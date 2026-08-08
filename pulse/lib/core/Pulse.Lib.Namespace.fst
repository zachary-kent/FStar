module Pulse.Lib.Namespace
friend PulseCore.InstantiatedSemantics
friend Pulse.Lib.Core
friend Pulse.Lib.Core.Inv
friend Pulse.Lib.Mask
friend Pulse.Lib.Mask.PrimitiveContract

module Core     = Pulse.Lib.Core
module CoreInv  = Pulse.Lib.Core.Inv
module GS       = Pulse.Lib.GhostSet
module Mask     = Pulse.Lib.Mask
module Contract = Pulse.Lib.Mask.PrimitiveContract
module NS       = PulseCore.Namespace
module Atomic   = PulseCore.Atomic
module RawGS    = FStar.GhostSet

let namespace = NS.namespace

let root = NS.root

let child = NS.child

let namespace_mask (n:namespace) : Mask.mask = NS.inames n

let namespace_mask_root (_:unit)
  : Lemma (namespace_mask root == Mask.top)
  = Mask.ext (namespace_mask root) Mask.top;
    let pointwise (i:Core.iname)
      : Lemma (
          Mask.mem i (namespace_mask root)
          <==> Mask.mem i Mask.top
        )
      = assert (
          Mask.mem i (namespace_mask root)
          == Contract.mem i (NS.inames NS.root)
        );
        assert (
          Mask.mem i Mask.top
          == Contract.mem i Contract.top
        );
        assert (
          Contract.mem i (NS.inames NS.root)
          == b2t (RawGS.mem i (NS.inames NS.root))
        );
        assert (
          Contract.mem i Contract.top
          == b2t (RawGS.mem i (RawGS.complement RawGS.empty))
        );
        NS.inames_root ();
        NS.all_inames_spec ();
        RawGS.mem_complement i RawGS.empty;
        RawGS.mem_empty i;
        ()
    in
    FStar.Classical.forall_intro pointwise;
    ()

let namespace_mask_child_subset
  (n:namespace)
  (x:nat)
  : Lemma (
      Mask.subset
        (namespace_mask (child n x))
        (namespace_mask n)
    )
  = Mask.subset_spec
      (namespace_mask (child n x))
      (namespace_mask n);
    let pointwise (i:Core.iname)
      : Lemma (
          Mask.mem i (namespace_mask (child n x))
          ==> Mask.mem i (namespace_mask n)
        )
      = NS.inames_child_subset n x;
        RawGS.subset_mem
          (NS.inames (NS.child n x))
          (NS.inames n);
        ()
    in
    FStar.Classical.forall_intro pointwise

let namespace_mask_sibling_disjoint
  (n:namespace)
  (x y:nat)
  : Lemma
      (requires (x <> y))
      (ensures (
        Mask.disjoint
          (namespace_mask (child n x))
          (namespace_mask (child n y))
      ))
  = Mask.disjoint_spec
      (namespace_mask (child n x))
      (namespace_mask (child n y));
    let pointwise (i:Core.iname)
      : Lemma (
          not (
            Mask.mem i (namespace_mask (child n x)) /\
            Mask.mem i (namespace_mask (child n y))
          )
        )
      = NS.inames_sibling_disjoint n x y;
        RawGS.disjoint_not_in_both
          Core.iname
          (NS.inames (NS.child n x))
          (NS.inames (NS.child n y));
        ()
    in
    FStar.Classical.forall_intro pointwise

let namespace_mask_fresh
  (n:namespace)
  (avoid:Core.fin_inames)
  : Lemma (
      ensures exists (i:Core.iname).
        Mask.mem i (namespace_mask n) /\
        ~(GS.mem i avoid)
    )
  = let rec max_inames (xs:list Core.iname)
      : y:Core.iname {
          forall x. FStar.List.Tot.memP x xs ==>
            FStar.Ghost.reveal x <= y
        }
      = match xs with
        | [] -> 0
        | x::xs ->
          let y = max_inames xs in
          if FStar.Ghost.reveal x > FStar.Ghost.reveal y then x else y
    in
    let xs = GS.is_finite_elim avoid in
    let floor = max_inames xs in
    let suffix = FStar.Ghost.reveal floor + 1 in
    let i : Core.iname = NS.candidate n suffix in
    NS.candidate_member n suffix;
    NS.member_inames n i;
    assert (b2t (RawGS.mem i (NS.inames n)));
    assert (Contract.mem i (NS.inames n));
    assert (Mask.mem i (namespace_mask n));
    NS.candidate_gt n suffix;
    GS.mem_as_set' i xs;
    assert (~(GS.mem i avoid));
    introduce exists j.
      Mask.mem j (namespace_mask n) /\ ~(GS.mem j avoid)
    with i and ()

let fresh_invariant
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
  = let member_iff_mask (i:Core.iname) : Lemma
      (NS.member n i <==> Mask.mem i (namespace_mask n))
      = NS.member_inames n i;
        assert (
          Contract.mem i (NS.inames n)
          == b2t (RawGS.mem i (NS.inames n))
        );
        assert (
          Mask.mem i (namespace_mask n)
          == Contract.mem i (NS.inames n)
        );
        ()
    in
    FStar.Classical.forall_intro member_iff_mask;
    Atomic.fresh_invariant_in_namespace n ctx p
