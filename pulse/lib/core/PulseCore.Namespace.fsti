(*
   Core-private namespace algebra.
   The public namespace facade must not re-export this interface.
*)
module PulseCore.Namespace

module KI = PulseCore.KnotInstantiation
module GS = FStar.GhostSet
open FStar.List.Tot


[@@ erasable]
val namespace : Type0

val root : namespace
val child : namespace -> nat -> namespace

val pair : nat -> nat -> nat
val decompose : nat -> Tot (nat & nat)

val decompose_spec (z:nat) : Lemma
  (requires z > 0)
  (ensures z == pair (fst (decompose z)) (snd (decompose z)))

val pair_ge_tail (h t:nat) : Lemma
  (ensures pair h t >= t)

val decompose_tail_lt (z:nat) : Lemma
  (requires z > 0)
  (ensures snd (decompose z) < z)

val decompose_pair (h t:nat) : Lemma
  (ensures decompose (pair h t) == (h, t))

val decode : nat -> Tot (list nat)
val encode : list nat -> Tot nat

val decode_encode (p:list nat) : Lemma
  (ensures decode (encode p) == p)

val encode_decode (z:nat) : Lemma
  (ensures encode (decode z) == z)

val encode_injective (p q:list nat) : Lemma
  (requires encode p == encode q)
  (ensures p == q)

val prefix : list nat -> list nat -> prop

val prefix_refl (p:list nat) : Lemma (prefix p p)

val prefix_append (p suffix:list nat) : Lemma
  (prefix p (p @ suffix))

val prefix_child_weaken (p:list nat) (x:nat) (q:list nat) : Lemma
  (requires prefix (p @ [x]) q)
  (ensures prefix p q)

val prefix_sibling_conflict (p:list nat) (x y:nat) (q:list nat) : Lemma
  (requires x <> y /\ prefix (p @ [x]) q /\ prefix (p @ [y]) q)
  (ensures False)

val member_b : namespace -> KI.address -> GTot bool
val member : namespace -> KI.address -> prop
val inames : namespace -> GS.set KI.address
val all_inames : GS.set KI.address
val all_inames_spec (_:unit) : Lemma
  (all_inames == GS.complement GS.empty)

val member_spec (n:namespace) (i:KI.address) : Lemma
  (ensures member n i <==> b2t (member_b n i))

val member_inames (n:namespace) (i:KI.address) : Lemma
  (ensures member n i <==> b2t (GS.mem i (inames n)))

val inames_root (_:unit) : Lemma
  (inames root == all_inames)

val inames_child_subset (n:namespace) (x:nat) : Lemma
  (ensures GS.subset (inames (child n x)) (inames n))

val inames_sibling_disjoint (n:namespace) (x y:nat) : Lemma
  (requires x <> y)
  (ensures GS.disjoint (inames (child n x)) (inames (child n y)))

val candidate_path : list nat -> nat -> nat

val candidate_path_gt (p:list nat) (suffix:nat) : Lemma
  (ensures candidate_path p suffix > suffix)

val candidate_path_decode (p:list nat) (suffix:nat) : Lemma
  (ensures decode (candidate_path p suffix) == p @ [suffix])

val candidate : namespace -> nat -> KI.address

val candidate_gt (n:namespace) (suffix:nat) : Lemma
  (ensures FStar.Ghost.reveal (candidate n suffix) > suffix)

val candidate_member (n:namespace) (suffix:nat) : Lemma
  (ensures member n (candidate n suffix))
