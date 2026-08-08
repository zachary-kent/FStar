(*
   Positive public-facade clients for the mask algebra.
*)
module MaskAlgebraPositive

module Mask = Pulse.Lib.Mask
module Core = Pulse.Lib.Core

(* Finite masks are constructed only through the public operations. *)
let rec finite_mask (xs:list Core.iname) : Mask.mask =
  match xs with
  | [] -> Mask.empty
  | i :: tl -> Mask.union (Mask.singleton i) (finite_mask tl)

(* Exercise the public carrier, operations, and relations as client terms. *)
let operation_surface (i j k:Core.iname) : Lemma (True) =
  let e : Mask.mask = Mask.empty in
  let s : Mask.mask = Mask.singleton i in
  let u : Mask.mask = Mask.union s (Mask.singleton j) in
  let n : Mask.mask = Mask.inter u Mask.top in
  let d : Mask.mask = Mask.diff n (Mask.singleton k) in
  let c : Mask.mask = Mask.compl d in
  let _m : prop = Mask.mem i c in
  let _s : prop = Mask.subset e c in
  let _d : prop = Mask.disjoint e c in
  ()

(* Primitive public laws. *)
let client_mem_top (i:Core.iname) : Lemma (Mask.mem i Mask.top) =
  Mask.mem_top i

let client_mem_empty (i:Core.iname) : Lemma (not (Mask.mem i Mask.empty)) =
  Mask.mem_empty i

let client_mem_singleton (i j:Core.iname) : Lemma (
  Mask.mem i (Mask.singleton j) <==> i == j
) =
  Mask.mem_singleton i j

let client_mem_union (i:Core.iname) (e f:Mask.mask) : Lemma (
  Mask.mem i (Mask.union e f) <==> Mask.mem i e \/ Mask.mem i f
) =
  Mask.mem_union i e f

let client_mem_inter (i:Core.iname) (e f:Mask.mask) : Lemma (
  Mask.mem i (Mask.inter e f) <==> Mask.mem i e /\ Mask.mem i f
) =
  Mask.mem_inter i e f

let client_mem_diff (i:Core.iname) (e f:Mask.mask) : Lemma (
  Mask.mem i (Mask.diff e f) <==> Mask.mem i e /\ not (Mask.mem i f)
) =
  Mask.mem_diff i e f

let client_mem_compl (i:Core.iname) (e:Mask.mask) : Lemma (
  Mask.mem i (Mask.compl e) <==> not (Mask.mem i e)
) =
  Mask.mem_compl i e

let client_subset_spec (e f:Mask.mask) : Lemma (
  Mask.subset e f <==> forall (i:Core.iname). Mask.mem i e ==> Mask.mem i f
) =
  Mask.subset_spec e f

let client_disjoint_spec (e f:Mask.mask) : Lemma (
  Mask.disjoint e f <==> forall (i:Core.iname). not (Mask.mem i e /\ Mask.mem i f)
) =
  Mask.disjoint_spec e f

let client_ext (e f:Mask.mask) : Lemma (
  (e == f) <==> forall (i:Core.iname). (Mask.mem i e <==> Mask.mem i f)
) =
  Mask.ext e f

(* Symbolic singleton union, intersection, difference, and complement. *)
let symbolic_singleton_operations (i j k:Core.iname) : Lemma (
  (Mask.mem i (Mask.union (Mask.singleton j) (Mask.singleton k))
    <==> (i == j \/ i == k)) /\
  (Mask.mem i (Mask.inter (Mask.singleton j) (Mask.singleton k))
    <==> (i == j /\ i == k)) /\
  (Mask.mem i (Mask.diff (Mask.singleton j) (Mask.singleton k))
    <==> (i == j /\ not (i == k))) /\
  (Mask.mem i (Mask.compl (Mask.singleton j))
    <==> not (i == j))
) =
  Mask.mem_union i (Mask.singleton j) (Mask.singleton k);
  Mask.mem_inter i (Mask.singleton j) (Mask.singleton k);
  Mask.mem_diff i (Mask.singleton j) (Mask.singleton k);
  Mask.mem_compl i (Mask.singleton j);
  Mask.mem_singleton i j;
  Mask.mem_singleton i k;
  ()

(* Equality and order laws. *)
let client_subset_refl (e:Mask.mask) : Lemma (Mask.subset e e) =
  Mask.subset_refl e

let client_subset_trans (e f g:Mask.mask) : Lemma
  (requires (Mask.subset e f /\ Mask.subset f g))
  (ensures (Mask.subset e g)) =
  Mask.subset_trans e f g

let client_subset_antisym (e f:Mask.mask) : Lemma
  (requires (Mask.subset e f /\ Mask.subset f e))
  (ensures (e == f)) =
  Mask.subset_antisym e f

let client_eq_iff_subset (e f:Mask.mask) : Lemma (
  (e == f) <==> Mask.subset e f /\ Mask.subset f e
) =
  Mask.eq_iff_subset e f

let client_empty_subset (e:Mask.mask) : Lemma (Mask.subset Mask.empty e) =
  Mask.empty_subset e

let client_subset_top (e:Mask.mask) : Lemma (Mask.subset e Mask.top) =
  Mask.subset_top e

let client_subset_union_iff (e f:Mask.mask) : Lemma (
  Mask.subset e f <==> Mask.union e f == f
) =
  Mask.subset_union_iff e f

let client_subset_inter_iff (e f:Mask.mask) : Lemma (
  Mask.subset e f <==> Mask.inter e f == e
) =
  Mask.subset_inter_iff e f

let client_union_mono (e1 e2 f1 f2:Mask.mask) : Lemma
  (requires (Mask.subset e1 e2 /\ Mask.subset f1 f2))
  (ensures (Mask.subset (Mask.union e1 f1) (Mask.union e2 f2))) =
  Mask.union_mono e1 e2 f1 f2

let client_inter_mono (e1 e2 f1 f2:Mask.mask) : Lemma
  (requires (Mask.subset e1 e2 /\ Mask.subset f1 f2))
  (ensures (Mask.subset (Mask.inter e1 f1) (Mask.inter e2 f2))) =
  Mask.inter_mono e1 e2 f1 f2

(* Bounded distributive lattice laws. *)
let client_union_empty (e:Mask.mask) : Lemma (Mask.union e Mask.empty == e) =
  Mask.union_empty e

let client_union_top (e:Mask.mask) : Lemma (Mask.union e Mask.top == Mask.top) =
  Mask.union_top e

let client_union_idem (e:Mask.mask) : Lemma (Mask.union e e == e) =
  Mask.union_idem e

let client_union_comm (e f:Mask.mask) : Lemma (
  Mask.union e f == Mask.union f e
) =
  Mask.union_comm e f

let client_union_assoc (e f g:Mask.mask) : Lemma (
  Mask.union e (Mask.union f g) == Mask.union (Mask.union e f) g
) =
  Mask.union_assoc e f g

let client_inter_empty (e:Mask.mask) : Lemma (Mask.inter e Mask.empty == Mask.empty) =
  Mask.inter_empty e

let client_inter_top (e:Mask.mask) : Lemma (Mask.inter e Mask.top == e) =
  Mask.inter_top e

let client_inter_idem (e:Mask.mask) : Lemma (Mask.inter e e == e) =
  Mask.inter_idem e

let client_inter_comm (e f:Mask.mask) : Lemma (
  Mask.inter e f == Mask.inter f e
) =
  Mask.inter_comm e f

let client_inter_assoc (e f g:Mask.mask) : Lemma (
  Mask.inter e (Mask.inter f g) == Mask.inter (Mask.inter e f) g
) =
  Mask.inter_assoc e f g

let client_inter_union_absorb (e f:Mask.mask) : Lemma (
  Mask.inter e (Mask.union e f) == e
) =
  Mask.inter_union_absorb e f

let client_union_inter_absorb (e f:Mask.mask) : Lemma (
  Mask.union e (Mask.inter e f) == e
) =
  Mask.union_inter_absorb e f

let client_inter_union_distr (e f g:Mask.mask) : Lemma (
  Mask.inter e (Mask.union f g) == Mask.union (Mask.inter e f) (Mask.inter e g)
) =
  Mask.inter_union_distr e f g

let client_union_inter_distr (e f g:Mask.mask) : Lemma (
  Mask.union e (Mask.inter f g) == Mask.inter (Mask.union e f) (Mask.union e g)
) =
  Mask.union_inter_distr e f g

(* Complement and difference laws. *)
let client_compl_empty () : Lemma (Mask.compl Mask.empty == Mask.top) =
  Mask.compl_empty ()

let client_compl_top () : Lemma (Mask.compl Mask.top == Mask.empty) =
  Mask.compl_top ()

let client_compl_involutive (e:Mask.mask) : Lemma (
  Mask.compl (Mask.compl e) == e
) =
  Mask.compl_involutive e

let client_union_compl (e:Mask.mask) : Lemma (
  Mask.union e (Mask.compl e) == Mask.top
) =
  Mask.union_compl e

let client_inter_compl (e:Mask.mask) : Lemma (
  Mask.inter e (Mask.compl e) == Mask.empty
) =
  Mask.inter_compl e

let client_compl_union (e f:Mask.mask) : Lemma (
  Mask.compl (Mask.union e f) == Mask.inter (Mask.compl e) (Mask.compl f)
) =
  Mask.compl_union e f

let client_compl_inter (e f:Mask.mask) : Lemma (
  Mask.compl (Mask.inter e f) == Mask.union (Mask.compl e) (Mask.compl f)
) =
  Mask.compl_inter e f

let client_compl_antitone (e f:Mask.mask) : Lemma (
  Mask.subset e f <==> Mask.subset (Mask.compl f) (Mask.compl e)
) =
  Mask.compl_antitone e f

let client_diff_as_inter_compl (e f:Mask.mask) : Lemma (
  Mask.diff e f == Mask.inter e (Mask.compl f)
) =
  Mask.diff_as_inter_compl e f

let client_diff_empty (e:Mask.mask) : Lemma (Mask.diff e Mask.empty == e) =
  Mask.diff_empty e

let client_empty_diff (e:Mask.mask) : Lemma (Mask.diff Mask.empty e == Mask.empty) =
  Mask.empty_diff e

let client_diff_self (e:Mask.mask) : Lemma (Mask.diff e e == Mask.empty) =
  Mask.diff_self e

let client_diff_top (e:Mask.mask) : Lemma (Mask.diff e Mask.top == Mask.empty) =
  Mask.diff_top e

let client_top_diff (e:Mask.mask) : Lemma (Mask.diff Mask.top e == Mask.compl e) =
  Mask.top_diff e

let client_diff_twice (e f:Mask.mask) : Lemma (
  Mask.diff (Mask.diff e f) f == Mask.diff e f
) =
  Mask.diff_twice e f

let client_diff_diff_l (e f g:Mask.mask) : Lemma (
  Mask.diff (Mask.diff e f) g == Mask.diff e (Mask.union f g)
) =
  Mask.diff_diff_l e f g

let client_diff_union_l (e f g:Mask.mask) : Lemma (
  Mask.diff (Mask.union e f) g == Mask.union (Mask.diff e g) (Mask.diff f g)
) =
  Mask.diff_union_l e f g

let client_diff_union_r (e f g:Mask.mask) : Lemma (
  Mask.diff e (Mask.union f g) == Mask.inter (Mask.diff e f) (Mask.diff e g)
) =
  Mask.diff_union_r e f g

let client_diff_mono (e1 e2 f1 f2:Mask.mask) : Lemma
  (requires (Mask.subset e1 e2 /\ Mask.subset f2 f1))
  (ensures (Mask.subset (Mask.diff e1 f1) (Mask.diff e2 f2))) =
  Mask.diff_mono e1 e2 f1 f2

let client_subset_partition (e f:Mask.mask) : Lemma
  (requires (Mask.subset e f))
  (ensures (
    f == Mask.union e (Mask.diff f e) /\
    Mask.disjoint e (Mask.diff f e)
  )) =
  Mask.subset_partition e f

let client_diff_union_inter (e f:Mask.mask) : Lemma (
  Mask.union (Mask.diff e f) (Mask.inter e f) == e
) =
  Mask.diff_union_inter e f

(* Disjointness and singleton laws. *)
let client_disjoint_sym (e f:Mask.mask) : Lemma (
  Mask.disjoint e f <==> Mask.disjoint f e
) =
  Mask.disjoint_sym e f

let client_disjoint_empty (e:Mask.mask) : Lemma (Mask.disjoint e Mask.empty) =
  Mask.disjoint_empty e

let client_disjoint_inter_empty (e f:Mask.mask) : Lemma (
  Mask.disjoint e f <==> Mask.inter e f == Mask.empty
) =
  Mask.disjoint_inter_empty e f

let client_disjoint_compl_iff (e f:Mask.mask) : Lemma (
  Mask.disjoint e f <==> Mask.subset e (Mask.compl f)
) =
  Mask.disjoint_compl_iff e f

let client_disjoint_union (e f g:Mask.mask) : Lemma (
  Mask.disjoint e (Mask.union f g) <==> Mask.disjoint e f /\ Mask.disjoint e g
) =
  Mask.disjoint_union e f g

let client_disjoint_mono (e' e f' f:Mask.mask) : Lemma
  (requires (
    Mask.subset e' e /\
    Mask.subset f' f /\
    Mask.disjoint e f
  ))
  (ensures (Mask.disjoint e' f')) =
  Mask.disjoint_mono e' e f' f

let client_disjoint_diff (e f:Mask.mask) : Lemma (
  Mask.disjoint (Mask.diff e f) f
) =
  Mask.disjoint_diff e f

let client_disjoint_self_iff (e:Mask.mask) : Lemma (
  Mask.disjoint e e <==> e == Mask.empty
) =
  Mask.disjoint_self_iff e

let client_disjoint_top_iff (e:Mask.mask) : Lemma (
  Mask.disjoint Mask.top e <==> e == Mask.empty
) =
  Mask.disjoint_top_iff e

let client_singleton_subset_iff (i:Core.iname) (e:Mask.mask) : Lemma (
  Mask.subset (Mask.singleton i) e <==> Mask.mem i e
) =
  Mask.singleton_subset_iff i e

let client_singleton_disjoint_iff (i:Core.iname) (e:Mask.mask) : Lemma (
  Mask.disjoint (Mask.singleton i) e <==> not (Mask.mem i e)
) =
  Mask.singleton_disjoint_iff i e

(* The seven finite/cofinite matrix equations hold for arbitrary public masks. *)
let matrix_one (f g:Mask.mask) : Lemma (
  Mask.inter f (Mask.compl g) == Mask.diff f g
) =
  Mask.diff_as_inter_compl f g

let matrix_two (f g:Mask.mask) : Lemma (
  Mask.union f (Mask.compl g) == Mask.compl (Mask.diff g f)
) =
  Mask.diff_as_inter_compl g f;
  Mask.compl_inter g (Mask.compl f);
  Mask.compl_involutive f;
  Mask.union_comm f (Mask.compl g);
  ()

let matrix_three (f g:Mask.mask) : Lemma (
  Mask.diff f (Mask.compl g) == Mask.inter f g
) =
  Mask.diff_as_inter_compl f (Mask.compl g);
  Mask.compl_involutive g;
  ()

let matrix_four (f g:Mask.mask) : Lemma (
  Mask.inter (Mask.compl f) (Mask.compl g) == Mask.compl (Mask.union f g)
) =
  Mask.compl_union f g

let matrix_five (f g:Mask.mask) : Lemma (
  Mask.union (Mask.compl f) (Mask.compl g) == Mask.compl (Mask.inter f g)
) =
  Mask.compl_inter f g

let matrix_six (f g:Mask.mask) : Lemma (
  Mask.diff (Mask.compl f) g == Mask.compl (Mask.union f g)
) =
  Mask.diff_as_inter_compl (Mask.compl f) g;
  Mask.compl_union f g;
  Mask.compl_involutive f;
  ()

let matrix_seven (f g:Mask.mask) : Lemma (
  Mask.diff (Mask.compl f) (Mask.compl g) == Mask.diff g f
) =
  Mask.diff_as_inter_compl (Mask.compl f) (Mask.compl g);
  Mask.diff_as_inter_compl g f;
  Mask.compl_involutive f;
  Mask.compl_involutive g;
  Mask.inter_comm (Mask.compl f) g;
  ()

let finite_cofinite_matrix (i j k:Core.iname) : Lemma (
  let f = finite_mask [i; j] in
  let g = finite_mask [k] in
  Mask.inter f (Mask.compl g) == Mask.diff f g /\
  Mask.union f (Mask.compl g) == Mask.compl (Mask.diff g f) /\
  Mask.diff f (Mask.compl g) == Mask.inter f g /\
  Mask.inter (Mask.compl f) (Mask.compl g) == Mask.compl (Mask.union f g) /\
  Mask.union (Mask.compl f) (Mask.compl g) == Mask.compl (Mask.inter f g) /\
  Mask.diff (Mask.compl f) g == Mask.compl (Mask.union f g) /\
  Mask.diff (Mask.compl f) (Mask.compl g) == Mask.diff g f
) =
  let f = finite_mask [i; j] in
  let g = finite_mask [k] in
  matrix_one f g;
  matrix_two f g;
  matrix_three f g;
  matrix_four f g;
  matrix_five f g;
  matrix_six f g;
  matrix_seven f g;
  ()

(* Ei is Eo with i removed. *)
let ei_subset (i:Core.iname) (eo:Mask.mask) : Lemma (
  let ei = Mask.diff eo (Mask.singleton i) in
  Mask.subset ei eo
) =
  let ei = Mask.diff eo (Mask.singleton i) in
  Mask.subset_refl eo;
  Mask.empty_subset (Mask.singleton i);
  Mask.diff_mono eo eo (Mask.singleton i) Mask.empty;
  Mask.diff_empty eo;
  ()

let ei_disjoint (i:Core.iname) (eo:Mask.mask) : Lemma (
  let ei = Mask.diff eo (Mask.singleton i) in
  Mask.disjoint (Mask.singleton i) ei
) =
  let ei = Mask.diff eo (Mask.singleton i) in
  Mask.disjoint_diff eo (Mask.singleton i);
  Mask.disjoint_sym ei (Mask.singleton i);
  ()

let ei_partition (i:Core.iname) (eo:Mask.mask) : Lemma
  (requires (Mask.mem i eo))
  (ensures (
    let ei = Mask.diff eo (Mask.singleton i) in
    eo == Mask.union (Mask.singleton i) ei /\
    Mask.disjoint (Mask.singleton i) ei
  )) =
  let ei = Mask.diff eo (Mask.singleton i) in
  Mask.singleton_subset_iff i eo;
  Mask.subset_partition (Mask.singleton i) eo;
  Mask.disjoint_diff eo (Mask.singleton i);
  Mask.disjoint_sym ei (Mask.singleton i);
  ()

(* This symbolic client has no finite/cofinite premise. *)
let abstract_symbolic_client (e f g:Mask.mask) : Lemma
  (requires (Mask.subset e f))
  (ensures (
    Mask.subset (Mask.diff e g) (Mask.diff f g) /\
    Mask.disjoint (Mask.diff e g) g /\
    Mask.union (Mask.diff e f) (Mask.inter e f) == e /\
    Mask.subset (Mask.compl f) (Mask.compl e)
  )) =
  Mask.subset_refl g;
  Mask.diff_mono e f g g;
  Mask.disjoint_diff e g;
  Mask.diff_union_inter e f;
  Mask.compl_antitone e f;
  ()
