module Pulse.Lib.Namespace

module Core    = Pulse.Lib.Core
module CoreInv = Pulse.Lib.Core.Inv
module GS      = Pulse.Lib.GhostSet
module Mask    = Pulse.Lib.Mask

[@@ erasable]
val namespace : Type0

val root : namespace

val child : namespace -> nat -> namespace

val namespace_mask : namespace -> Mask.mask

val namespace_mask_root (_:unit)
  : Lemma (namespace_mask root == Mask.top)

val namespace_mask_child_subset
  (n:namespace)
  (x:nat)
  : Lemma (
      Mask.subset
        (namespace_mask (child n x))
        (namespace_mask n)
    )

val namespace_mask_sibling_disjoint
  (n:namespace)
  (x y:nat)
  : Lemma
      (requires (x <> y))
      (ensures (
        Mask.disjoint
          (namespace_mask (child n x))
          (namespace_mask (child n y))
      ))

val namespace_mask_fresh
  (n:namespace)
  (avoid:Core.fin_inames)
  : Lemma (
      ensures exists (i:Core.iname).
        Mask.mem i (namespace_mask n) /\
        ~(GS.mem i avoid)
    )

val fresh_invariant
  (n:namespace)
  (ctx:Core.fin_inames)
  (p:Core.slprop)
  : Core.stt_ghost
      (i:Core.iname {
        Mask.mem i (namespace_mask n) /\
        ~(GS.mem i ctx)
      })
      Core.emp_inames
      p
      (fun i -> CoreInv.inv i p)
