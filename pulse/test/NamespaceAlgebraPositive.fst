(*
   Public-only positive clients for the F02 namespace algebra.

   This file deliberately names only the three public F02 client facades.
   In particular, hidden representation and implementation dependencies are not
   part of this client.
*)
module NamespaceAlgebraPositive

module Namespace = Pulse.Lib.Namespace
module Mask = Pulse.Lib.Mask
module Core = Pulse.Lib.Core

(* The carrier, constructors, and abstract mask are all usable directly. *)
let namespace_surface (x:nat) : Lemma (True) =
  let n0 : Namespace.namespace = Namespace.root in
  let n1 : Namespace.namespace = Namespace.child n0 x in
  let _m : Mask.mask = Namespace.namespace_mask n1 in
  ()

(* The four primitive namespace laws are called through their public names. *)
let root_mask_equality ()
  : Lemma (Namespace.namespace_mask Namespace.root == Mask.top) =
  Namespace.namespace_mask_root ()

let child_mask_subset (n:Namespace.namespace) (x:nat)
  : Lemma (
      Mask.subset
        (Namespace.namespace_mask (Namespace.child n x))
        (Namespace.namespace_mask n)
    ) =
  Namespace.namespace_mask_child_subset n x

let sibling_mask_disjoint
  (n:Namespace.namespace)
  (x y:nat)
  : Lemma
      (requires (x <> y))
      (ensures (
        Mask.disjoint
          (Namespace.namespace_mask (Namespace.child n x))
          (Namespace.namespace_mask (Namespace.child n y))
      )) =
  Namespace.namespace_mask_sibling_disjoint n x y

(* Finite avoidance is exercised with the empty context. *)
let finite_avoid_empty (n:Namespace.namespace)
  : Lemma (
      exists (i:Core.iname).
        Mask.mem i (Namespace.namespace_mask n) /\
        ~(FStar.GhostSet.mem i Core.emp_inames)
    ) =
  Namespace.namespace_mask_fresh n Core.emp_inames

(* And with a nonempty finite singleton context. *)
let finite_avoid_singleton
  (n:Namespace.namespace)
  (a:Core.iname)
  : Lemma (
      exists (i:Core.iname).
        Mask.mem i (Namespace.namespace_mask n) /\
        ~(FStar.GhostSet.mem i (Core.single a))
    ) =
  Namespace.namespace_mask_fresh n (Core.single a)

(* And with a finite list-backed context containing two existing names. *)
let finite_avoid_list_backed
  (n:Namespace.namespace)
  (a b:Core.iname)
  : Lemma (
      exists (i:Core.iname).
        Mask.mem i (Namespace.namespace_mask n) /\
        ~(FStar.GhostSet.mem i (Core.iname_list [a; b]))
    ) =
  Namespace.namespace_mask_fresh n (Core.iname_list [a; b])

(* This public computation ascription observes both result facts. *)
let fresh_invariant_exact_type
  (n:Namespace.namespace)
  (ctx:Core.fin_inames)
  (p:Core.slprop)
  : Core.stt_ghost
      (i:Core.iname {
        Mask.mem i (Namespace.namespace_mask n) /\
        ~(FStar.GhostSet.mem i ctx)
      })
      Core.emp_inames
      p
      _
  = Namespace.fresh_invariant n ctx p

(* Namespace nonemptiness is the empty-context instance of finite avoidance. *)
let namespace_nonempty (n:Namespace.namespace)
  : Lemma (
      exists (i:Core.iname).
        Mask.mem i (Namespace.namespace_mask n)
    ) =
  Namespace.namespace_mask_fresh n Core.emp_inames;
  ()

(* Two child steps compose by the public subset-transitivity law. *)
let descendant_inclusion
  (n:Namespace.namespace)
  (x y:nat)
  : Lemma (
      Mask.subset
        (Namespace.namespace_mask
          (Namespace.child (Namespace.child n x) y))
        (Namespace.namespace_mask n)
    ) =
  Namespace.namespace_mask_child_subset (Namespace.child n x) y;
  Namespace.namespace_mask_child_subset n x;
  Mask.subset_trans
    (Namespace.namespace_mask (Namespace.child (Namespace.child n x) y))
    (Namespace.namespace_mask (Namespace.child n x))
    (Namespace.namespace_mask n)

(* Children preserve any already-established disjointness of their parents. *)
let child_preserves_disjointness
  (n1 n2:Namespace.namespace)
  (x y:nat)
  : Lemma
      (requires (
        Mask.disjoint
          (Namespace.namespace_mask n1)
          (Namespace.namespace_mask n2)
      ))
      (ensures (
        Mask.disjoint
          (Namespace.namespace_mask (Namespace.child n1 x))
          (Namespace.namespace_mask (Namespace.child n2 y))
      )) =
  Namespace.namespace_mask_child_subset n1 x;
  Namespace.namespace_mask_child_subset n2 y;
  Mask.disjoint_mono
    (Namespace.namespace_mask (Namespace.child n1 x))
    (Namespace.namespace_mask n1)
    (Namespace.namespace_mask (Namespace.child n2 y))
    (Namespace.namespace_mask n2)

(* An allocator result has mask membership, hence contains its singleton. *)
let allocated_singleton_containment
  (n:Namespace.namespace)
  (ctx:Core.fin_inames)
  (i:Core.iname {
    Mask.mem i (Namespace.namespace_mask n) /\
    ~(FStar.GhostSet.mem i ctx)
  })
  : Lemma (
      Mask.subset (Mask.singleton i) (Namespace.namespace_mask n)
    ) =
  Mask.singleton_subset_iff i (Namespace.namespace_mask n);
  ()

(* The second finite-avoid result cannot equal the earlier allocated name. *)
let repeated_finite_avoid_distinctness
  (i1 i2:Core.iname)
  (h:~(FStar.GhostSet.mem i2 (Core.single i1)))
  : Lemma (~(i2 == i1)) =
  assert (FStar.GhostSet.mem i2 (Core.single i1) <==> i1 == i2);
  ()

(* The first allocator in the repeated scenario uses an empty finite context. *)
let repeated_finite_avoid_first_type
  (n:Namespace.namespace)
  (p:Core.slprop)
  : Core.stt_ghost
      (i1:Core.iname {
        Mask.mem i1 (Namespace.namespace_mask n) /\
        ~(FStar.GhostSet.mem i1 Core.emp_inames)
      })
      Core.emp_inames
      p
      _
  = Namespace.fresh_invariant n Core.emp_inames p

(* A second public allocator call can use the first result as its finite
   exclusion context; its exact type carries both refinements again. *)
let repeated_finite_avoid_second_type
  (n:Namespace.namespace)
  (i1:Core.iname)
  (p:Core.slprop)
  : Core.stt_ghost
      (i2:Core.iname {
        Mask.mem i2 (Namespace.namespace_mask n) /\
        ~(FStar.GhostSet.mem i2 (Core.single i1))
      })
      Core.emp_inames
      p
      _
  = Namespace.fresh_invariant n (Core.single i1) p
