(*
   Core-private primitive abstraction boundary for Pulse.Lib.Mask.

   Derived algebra modules receive only this abstract carrier and its ten
   primitive characterization laws.
*)
module Pulse.Lib.Mask.PrimitiveContract

module Core = Pulse.Lib.Core

[@@ erasable]
val mask : Type0

val top       : mask
val empty     : mask
val singleton : Core.iname -> mask

val union : mask -> mask -> mask
val inter : mask -> mask -> mask
val diff  : mask -> mask -> mask
val compl : mask -> mask

val mem      : Core.iname -> mask -> prop
val subset   : mask -> mask -> prop
val disjoint : mask -> mask -> prop

val mem_top (i:Core.iname)
  : Lemma (mem i top)

val mem_empty (i:Core.iname)
  : Lemma (not (mem i empty))

val mem_singleton (i j:Core.iname)
  : Lemma (mem i (singleton j) <==> i == j)

val mem_union (i:Core.iname) (e f:mask)
  : Lemma (mem i (union e f) <==> mem i e \/ mem i f)

val mem_inter (i:Core.iname) (e f:mask)
  : Lemma (mem i (inter e f) <==> mem i e /\ mem i f)

val mem_diff (i:Core.iname) (e f:mask)
  : Lemma (
      mem i (diff e f)
      <==> mem i e /\ not (mem i f)
    )

val mem_compl (i:Core.iname) (e:mask)
  : Lemma (mem i (compl e) <==> not (mem i e))

val subset_spec (e f:mask)
  : Lemma (
      subset e f
      <==> forall (i:Core.iname). mem i e ==> mem i f
    )

val disjoint_spec (e f:mask)
  : Lemma (
      disjoint e f
      <==> forall (i:Core.iname).
            not (mem i e /\ mem i f)
    )

val ext (e f:mask)
  : Lemma (
      (e == f)
      <==> forall (i:Core.iname).
            (mem i e <==> mem i f)
    )
