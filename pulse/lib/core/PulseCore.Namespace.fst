(*
   Core-private namespace algebra over KnotInstantiation.address.
*)
module PulseCore.Namespace

module KI = PulseCore.KnotInstantiation
module GS = FStar.GhostSet
module M = FStar.Math.Lemmas
module LP = FStar.List.Tot.Properties

open FStar.List.Tot
open FStar.Ghost {erased, hide, reveal}

[@@ erasable]
let namespace = erased (list nat)

let root : namespace = hide []

let child (n:namespace) (x:nat) : namespace =
  hide (reveal n @ [x])

let pair (head tail:nat) : nat = pow2 tail * (2 * head + 1)

let rec decompose (z:nat) : Tot (nat & nat) (decreases z) =
  if z = 0 then (0, 0)
  else if z % 2 = 1 then ((z - 1) / 2, 0)
  else
    let h, t = decompose (z / 2) in
    (h, t + 1)

let rec decompose_spec (z:nat) : Lemma
  (requires z > 0)
  (ensures z == pair (fst (decompose z)) (snd (decompose z)))
  (decreases z)
= if z % 2 = 1 then (
    M.lemma_div_mod z 2;
    assert (pow2 0 == 1)
  ) else (
    assert (z % 2 == 0);
    assert (z / 2 > 0);
    decompose_spec (z / 2);
    M.lemma_div_mod z 2;
    let h, t = decompose (z / 2) in
    M.pow2_double_mult t
  )

let rec pow2_ge (n:nat) : Lemma
  (ensures pow2 n >= n)
  (decreases n)
= if n = 0 then (
    assert (pow2 0 == 1)
  ) else (
    pow2_ge (n - 1);
    assert (pow2 n == 2 * pow2 (n - 1))
  )

let rec pow2_gt (n:nat) : Lemma
  (ensures pow2 n > n)
  (decreases n)
= if n = 0 then (
    assert (pow2 0 == 1)
  ) else (
    pow2_gt (n - 1);
    assert (pow2 n == 2 * pow2 (n - 1))
  )

let pair_ge_tail (h t:nat) : Lemma
  (ensures pair h t >= t)
= pow2_ge t;
  assert (2 * h + 1 >= 1);
  M.lemma_mult_le_left (pow2 t) 1 (2 * h + 1)

let pair_ge_pow2 (h t:nat) : Lemma
  (ensures pair h t >= pow2 t)
= assert (2 * h + 1 >= 1);
  M.lemma_mult_le_left (pow2 t) 1 (2 * h + 1)

let pair_gt_tail (h t:nat) : Lemma
  (ensures pair h t > t)
= pair_ge_pow2 h t;
  pow2_gt t

let decompose_tail_lt (z:nat) : Lemma
  (requires z > 0)
  (ensures snd (decompose z) < z)
= decompose_spec z;
  pair_gt_tail (fst (decompose z)) (snd (decompose z))

let rec decompose_pair (h t:nat) : Lemma
  (ensures decompose (pair h t) == (h, t))
  (decreases t)
= if t = 0 then (
    assert (pair h 0 == 2 * h + 1);
    assert ((pair h 0) % 2 == 1)
  ) else (
    assert (pow2 t == 2 * pow2 (t - 1));
    assert (pair h t == pair h (t - 1) * 2);
    M.cancel_mul_mod (pair h (t - 1)) 2;
    M.cancel_mul_div (pair h (t - 1)) 2;
    decompose_pair h (t - 1)
  )

let rec decode (z:nat) : Tot (list nat) (decreases z) =
  if z = 0 then []
  else
    let h, t = decompose z in
    decompose_tail_lt z;
    h :: decode t

let rec encode (p:list nat) : nat =
  match p with
  | [] -> 0
  | h::t -> pair h (encode t)

let rec decode_encode (p:list nat) : Lemma
  (ensures decode (encode p) == p)
  (decreases p)
= match p with
  | [] -> ()
  | h::t ->
    decode_encode t;
    decompose_pair h (encode t)

let rec encode_decode (z:nat) : Lemma
  (ensures encode (decode z) == z)
  (decreases z)
= if z = 0 then ()
  else
    let h, t = decompose z in
    decompose_tail_lt z;
    encode_decode t;
    decompose_spec z

let encode_injective (p q:list nat) : Lemma
  (requires encode p == encode q)
  (ensures p == q)
= decode_encode p;
  decode_encode q

let rec prefix_b (p q:list nat) : Tot bool =
  match p, q with
  | [], _ -> true
  | _, [] -> false
  | hp::pt, hq::qt -> if hp = hq then prefix_b pt qt else false

let prefix (p q:list nat) : prop = exists suffix. q == p @ suffix

let rec prefix_b_spec (p q:list nat) : Lemma
  (ensures b2t (prefix_b p q) <==> prefix p q)
  (decreases p)
= match p, q with
  | [], _ -> ()
  | _, [] -> ()
  | hp::pt, hq::qt ->
    if hp = hq then prefix_b_spec pt qt else ()

let prefix_refl (p:list nat) : Lemma (prefix p p) =
  introduce exists suffix. p == p @ suffix with [] and ()

let prefix_append (p suffix:list nat) : Lemma (prefix p (p @ suffix)) =
  introduce exists rest. p @ suffix == p @ rest with suffix and ()

let prefix_child_weaken (p:list nat) (x:nat) (q:list nat) : Lemma
  (requires prefix (p @ [x]) q)
  (ensures prefix p q)
= eliminate exists suffix. q == (p @ [x]) @ suffix
  with (
    LP.append_assoc p [x] suffix
  )

let prefix_sibling_conflict (p:list nat) (x y:nat) (q:list nat) : Lemma
  (requires x <> y /\ prefix (p @ [x]) q /\ prefix (p @ [y]) q)
  (ensures False)
= eliminate exists sx. q == (p @ [x]) @ sx
  with eliminate exists sy. q == (p @ [y]) @ sy
    with (
      LP.append_assoc p [x] sx;
      LP.append_assoc p [y] sy;
      LP.append_inv_head p ([x] @ sx) ([y] @ sy);
      assert (x == y)
    )

let member_b (n:namespace) (i:KI.address) : GTot bool =
  prefix_b (reveal n) (decode (reveal i))

let member (n:namespace) (i:KI.address) : prop = b2t (member_b n i)

let inames (n:namespace) : GS.set KI.address = GS.comprehend (member_b n)

let all_inames : GS.set KI.address = GS.complement GS.empty
let all_inames_spec (_:unit) : Lemma
  (all_inames == GS.complement GS.empty)
= ()

let member_spec (n:namespace) (i:KI.address) : Lemma
  (ensures member n i <==> b2t (member_b n i))
= ()

let member_prefix_spec (n:namespace) (i:KI.address) : Lemma
  (ensures member n i <==> prefix (reveal n) (decode (reveal i)))
= prefix_b_spec (reveal n) (decode (reveal i))

let member_inames (n:namespace) (i:KI.address) : Lemma
  (ensures member n i <==> b2t (GS.mem i (inames n)))
= GS.comprehend_mem (member_b n) i

let root_member (i:KI.address) : Lemma (member root i) =
  member_prefix_spec root i;
  prefix_refl (decode (reveal i))

let child_member_parent (n:namespace) (x:nat) (i:KI.address) : Lemma
  (requires member (child n x) i)
  (ensures member n i)
= member_prefix_spec (child n x) i;
  member_prefix_spec n i;
  prefix_child_weaken (reveal n) x (decode (reveal i))

let child_members_disjoint (n:namespace) (x y:nat) (i:KI.address) : Lemma
  (requires x <> y /\ member (child n x) i /\ member (child n y) i)
  (ensures False)
= member_prefix_spec (child n x) i;
  member_prefix_spec (child n y) i;
  prefix_sibling_conflict (reveal n) x y (decode (reveal i))

let inames_root (_:unit) : Lemma (inames root == all_inames) =
  let pointwise (i:KI.address) : Lemma
    (ensures GS.mem i (inames root) == GS.mem i all_inames)
  = GS.comprehend_mem (member_b root) i;
    GS.mem_complement i GS.empty;
    GS.mem_empty i
  in
  FStar.Classical.forall_intro pointwise;
  GS.lemma_equal_intro (inames root) all_inames;
  GS.lemma_equal_elim (inames root) all_inames

let inames_child_subset (n:namespace) (x:nat) : Lemma
  (ensures GS.subset (inames (child n x)) (inames n))
= let pointwise (i:KI.address) : Lemma
    (ensures GS.mem i (inames (child n x)) ==> GS.mem i (inames n))
  = if GS.mem i (inames (child n x)) then (
      GS.comprehend_mem (member_b (child n x)) i;
      GS.comprehend_mem (member_b n) i;
      child_member_parent n x i
    ) else ()
  in
  FStar.Classical.forall_intro pointwise;
  GS.mem_subset (inames (child n x)) (inames n)

let inames_sibling_disjoint (n:namespace) (x y:nat) : Lemma
  (requires x <> y)
  (ensures GS.disjoint (inames (child n x)) (inames (child n y)))
= let pointwise (i:KI.address) : Lemma
    (ensures GS.mem i (GS.intersect (inames (child n x)) (inames (child n y))) ==
             GS.mem i GS.empty)
  = GS.mem_intersect i (inames (child n x)) (inames (child n y));
    GS.mem_empty i;
    GS.comprehend_mem (member_b (child n x)) i;
    GS.comprehend_mem (member_b (child n y)) i;
    if member_b (child n x) i && member_b (child n y) i then (
      child_members_disjoint n x y i
    ) else ()
  in
  FStar.Classical.forall_intro pointwise;
  GS.lemma_equal_intro
    (GS.intersect (inames (child n x)) (inames (child n y))) GS.empty;
  GS.lemma_equal_refl
    (GS.intersect (inames (child n x)) (inames (child n y))) GS.empty

let candidate_path (p:list nat) (suffix:nat) : nat = encode (p @ [suffix])

let rec candidate_path_gt (p:list nat) (suffix:nat) : Lemma
  (ensures candidate_path p suffix > suffix)
  (decreases p)
= match p with
  | [] ->
    assert (candidate_path [] suffix == pair suffix 0);
    assert (pair suffix 0 == 2 * suffix + 1)
  | h::t ->
    assert (candidate_path (h::t) suffix == pair h (candidate_path t suffix));
    pair_ge_tail h (candidate_path t suffix);
    candidate_path_gt t suffix

let candidate_path_decode (p:list nat) (suffix:nat) : Lemma
  (ensures decode (candidate_path p suffix) == p @ [suffix])
= decode_encode (p @ [suffix])

let candidate (n:namespace) (suffix:nat) : KI.address =
  hide (candidate_path (reveal n) suffix)

let candidate_gt (n:namespace) (suffix:nat) : Lemma
  (ensures reveal (candidate n suffix) > suffix)
= FStar.Ghost.reveal_hide (candidate_path (reveal n) suffix);
  candidate_path_gt (reveal n) suffix

let candidate_member (n:namespace) (suffix:nat) : Lemma
  (ensures member n (candidate n suffix))
= member_prefix_spec n (candidate n suffix);
  FStar.Ghost.reveal_hide (candidate_path (reveal n) suffix);
  candidate_path_decode (reveal n) suffix;
  prefix_append (reveal n) [suffix]
