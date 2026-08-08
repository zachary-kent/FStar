(*
   Core-private primitive implementation boundary for Pulse.Lib.Mask.

   The interface keeps the carrier abstract.  This core-only implementation
   uses the legacy invariant-name set representation and proves its primitive
   characterization laws directly.
*)
module Pulse.Lib.Mask.PrimitiveContract

module Core = Pulse.Lib.Core
module GS = FStar.GhostSet

let mask = Core.inames

let top : mask = Core.all_inames
let empty : mask = Core.emp_inames
let singleton (i:Core.iname) : mask = Core.single i

let union (e f:mask) : mask = Core.join_inames e f
let inter (e f:mask) : mask = GS.intersect e f
let diff (e f:mask) : mask = GS.intersect e (GS.complement f)
let compl (e:mask) : mask = GS.complement e

let mem (i:Core.iname) (e:mask) : prop = b2t (GS.mem i e)
let subset (e f:mask) : prop =
  forall (i:Core.iname). mem i e ==> mem i f
let disjoint (e f:mask) : prop =
  forall (i:Core.iname). not (mem i e /\ mem i f)

let mem_top (i:Core.iname)
  : Lemma (mem i top)
  = ()

let mem_empty (i:Core.iname)
  : Lemma (not (mem i empty))
  = ()

let mem_singleton (i j:Core.iname)
  : Lemma (mem i (singleton j) <==> i == j)
  = ()

let mem_union (i:Core.iname) (e f:mask)
  : Lemma (mem i (union e f) <==> mem i e \/ mem i f)
  = ()

let mem_inter (i:Core.iname) (e f:mask)
  : Lemma (mem i (inter e f) <==> mem i e /\ mem i f)
  = GS.mem_intersect i e f

let mem_diff (i:Core.iname) (e f:mask)
  : Lemma (mem i (diff e f) <==> mem i e /\ not (mem i f))
  = GS.mem_intersect i e (compl f);
    GS.mem_complement i f

let mem_compl (i:Core.iname) (e:mask)
  : Lemma (mem i (compl e) <==> not (mem i e))
  = GS.mem_complement i e

let subset_spec (e f:mask)
  : Lemma (
      subset e f
      <==> forall (i:Core.iname). mem i e ==> mem i f
    )
  = ()

let disjoint_spec (e f:mask)
  : Lemma (
      disjoint e f
      <==> forall (i:Core.iname). not (mem i e /\ mem i f)
    )
  = ()

let raw_mem_eq_of_mem_iff (i:Core.iname) (e f:mask)
  : Lemma
      (requires (mem i e <==> mem i f))
      (ensures (GS.mem i e == GS.mem i f))
  = ()

let extensionality (e f:mask)
  : Lemma
      (requires (forall (i:Core.iname). GS.mem i e == GS.mem i f))
      (ensures (e == f))
  = GS.lemma_equal_intro e f;
    GS.lemma_equal_elim e f

let extensionality_prop (e f:mask)
  : Lemma
      (requires (forall (i:Core.iname). mem i e <==> mem i f))
      (ensures (e == f))
  = let raw_mem_eq (i:Core.iname) : Lemma (GS.mem i e == GS.mem i f) =
      raw_mem_eq_of_mem_iff i e f
    in
    FStar.Classical.forall_intro raw_mem_eq;
    extensionality e f

let ext (e f:mask)
  : Lemma (
      (e == f)
      <==> forall (i:Core.iname).
            (mem i e <==> mem i f)
    )
  = let reverse ()
      : Lemma
          (requires (forall (i:Core.iname). mem i e <==> mem i f))
          (ensures (e == f))
      = extensionality_prop e f
    in
    FStar.Classical.move_requires reverse ();
    ()
