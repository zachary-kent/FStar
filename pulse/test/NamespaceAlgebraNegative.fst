(*
   Negative public clients for the F02 namespace facade.

   Each marked declaration is intentionally rejected at its own boundary.  This
   file mentions only the public Namespace, Mask, Core, Core.Inv, and GhostSet
   facades; the one PulseCore reference checks that the raw allocator is not
   reachable through that public include topology.
*)
module NamespaceAlgebraNegative

module Namespace = Pulse.Lib.Namespace
module Mask = Pulse.Lib.Mask
module Core = Pulse.Lib.Core
module CoreInv = Pulse.Lib.Core.Inv
module GS = Pulse.Lib.GhostSet

(* Namespace paths remain abstract, even through Ghost.hide. *)
[@@expect_failure [54]]
let construct_namespace_path : Namespace.namespace = FStar.Ghost.hide [0]

[@@expect_failure [54]]
let reveal_namespace_path (n:Namespace.namespace) : GTot (list nat) =
  FStar.Ghost.reveal n

[@@expect_failure [189]]
let coerce_namespace_path (n:Namespace.namespace) : list nat = n

(* Raw invariant names remain abstract too, even through Ghost.hide. *)
[@@expect_failure [54]]
let construct_invariant_name : Core.iname = FStar.Ghost.hide 0

[@@expect_failure [54]]
let reveal_invariant_name (i:Core.iname) : GTot nat = FStar.Ghost.reveal i

[@@expect_failure [189]]
let coerce_invariant_name (i:Core.iname) : nat = i

(* A namespace closure is a Mask.mask, never a legacy inames carrier. *)
[@@expect_failure [12;34]]
let namespace_mask_to_inames (n:Namespace.namespace) : Core.inames =
  Namespace.namespace_mask n

[@@expect_failure [189]]
let inames_to_namespace_mask (is:Core.inames) : Mask.mask = is

(* Pulse opens still use raw inames, so a namespace mask cannot be passed. *)
[@@expect_failure [12]]
let namespace_mask_as_legacy_opens
  (n:Namespace.namespace)
  (f:Core.stt_ghost unit (Namespace.namespace_mask n) Core.emp (fun _ -> Core.emp)) =
  f

(* The public facade exports no raw allocator, codec, membership predicate,
   namespace-to-inames adapter, or primitive Mask backing.  The raw allocator
   cases intentionally reach toward core-private modules while the validation
   include path exposes none. *)
[@@expect_failure [72]]
let raw_namespace_allocator = PulseCore.Atomic.fresh_invariant_in_namespace

[@@expect_failure [72]]
let namespace_codec = Namespace.encode

[@@expect_failure [72]]
let namespace_decode = Namespace.decode

[@@expect_failure [72]]
let namespace_pair = Namespace.pair

[@@expect_failure [72]]
let namespace_prefix = Namespace.prefix

[@@expect_failure [72]]
let namespace_member = Namespace.member

[@@expect_failure [72]]
let namespace_member_b = Namespace.namespace_member_b

[@@expect_failure [72]]
let namespace_to_inames = Namespace.namespace_to_inames

[@@expect_failure [72]]
let raw_namespace_algebra = PulseCore.Namespace.root

[@@expect_failure [72]]
let raw_sep_namespace_allocator =
  PulseCore.IndirectionTheorySep.fresh_inv_in_namespace

[@@expect_failure [72]]
let raw_actions_namespace_allocator =
  PulseCore.IndirectionTheoryActions.fresh_invariant_in_namespace

[@@expect_failure [72]]
let raw_action_namespace_allocator =
  PulseCore.Action.fresh_invariant_in_namespace

[@@expect_failure [72]]
let primitive_mask_backing = Pulse.Lib.Mask.PrimitiveContract.mask

(* A child is contained in its parent, so their masks cannot be disjoint. *)
[@@expect_failure [19]]
let parent_child_disjoint (n:Namespace.namespace) (x:nat)
  : Lemma (Mask.disjoint
      (Namespace.namespace_mask n)
      (Namespace.namespace_mask (Namespace.child n x))) =
  Namespace.namespace_mask_fresh (Namespace.child n x) Core.emp_inames;
  Namespace.namespace_mask_child_subset n x;
  Mask.disjoint_spec
    (Namespace.namespace_mask n)
    (Namespace.namespace_mask (Namespace.child n x));
  Mask.subset_spec
    (Namespace.namespace_mask (Namespace.child n x))
    (Namespace.namespace_mask n);
  ()

(* Distinct namespace values need not have disjoint closures. *)
[@@expect_failure [19]]
let arbitrary_distinct_namespace_disjoint
  (n1 n2:Namespace.namespace)
  : Lemma
      (requires (not (n1 == n2)))
      (ensures (Mask.disjoint
        (Namespace.namespace_mask n1)
        (Namespace.namespace_mask n2))) =
  ()

(* The sibling theorem requires its x <> y premise. *)
[@@expect_failure [19]]
let sibling_disjoint_without_inequality (n:Namespace.namespace) (x:nat)
  : Lemma (Mask.disjoint
      (Namespace.namespace_mask (Namespace.child n x))
      (Namespace.namespace_mask (Namespace.child n x))) =
  Namespace.namespace_mask_sibling_disjoint n x x

(* A finite selection of children does not cover the entire parent closure. *)
[@@expect_failure [19]]
let children_cover_parent (n:Namespace.namespace) (x y:nat)
  : Lemma (Mask.subset
      (Namespace.namespace_mask n)
      (Mask.union
        (Namespace.namespace_mask (Namespace.child n x))
        (Namespace.namespace_mask (Namespace.child n y)))) =
  ()

(* No name can be fresh outside Mask.top. *)
[@@expect_failure [19]]
let fresh_outside_mask_top (n:Namespace.namespace)
  : Lemma (exists (i:Core.iname).
      Mask.mem i (Namespace.namespace_mask n) /\
      not (Mask.mem i Mask.top)) =
  ()

(* Finite avoidance takes a finite legacy set, not an arbitrary mask. *)
[@@expect_failure [189]]
let fresh_against_mask_top (n:Namespace.namespace) =
  Namespace.namespace_mask_fresh n Mask.top

(* The operational allocator likewise requires a finite raw exclusion set. *)
[@@expect_failure [19]]
let fresh_invariant_with_nonfinite_context
  (n:Namespace.namespace)
  (ctx:Core.inames)
  (p:Core.slprop) =
  Namespace.fresh_invariant n ctx p

(* stt_ghost's claimed result type is exact: neither returned fact is optional. *)
[@@expect_failure [19]]
let fresh_invariant_without_namespace_membership
  (n:Namespace.namespace)
  (ctx:Core.fin_inames)
  (p:Core.slprop)
  : Core.stt_ghost
      (i:Core.iname { ~(GS.mem i ctx) })
      Core.emp_inames
      p
      (fun i -> CoreInv.inv i p) =
  Namespace.fresh_invariant n ctx p

[@@expect_failure [19]]
let fresh_invariant_without_finite_exclusion
  (n:Namespace.namespace)
  (ctx:Core.fin_inames)
  (p:Core.slprop)
  : Core.stt_ghost
      (i:Core.iname { Mask.mem i (Namespace.namespace_mask n) })
      Core.emp_inames
      p
      (fun i -> CoreInv.inv i p) =
  Namespace.fresh_invariant n ctx p

(* F02 exports neither F03 authority nor F04/F07 transition/opening machinery. *)
[@@expect_failure [72]]
let namespace_ownE (n:Namespace.namespace) = Namespace.ownE n

[@@expect_failure [72]]
let namespace_fupd = Namespace.fupd

[@@expect_failure [72]]
let namespace_open_invariant = Namespace.open_invariant

(* Namespace-mask relations are propositions and cannot branch at runtime. *)

[@@expect_failure [12]]
let runtime_namespace_child_law (n:Namespace.namespace) (x:nat) : bool =
  if Namespace.namespace_mask_child_subset n x then true else false
[@@expect_failure [34]]
let runtime_namespace_child_subset (n:Namespace.namespace) (x:nat) : bool =
  if Mask.subset
       (Namespace.namespace_mask (Namespace.child n x))
       (Namespace.namespace_mask n)
  then true else false

[@@expect_failure [34]]
let runtime_namespace_sibling_disjoint
  (n:Namespace.namespace) (x y:nat) : bool =
  if Mask.disjoint
       (Namespace.namespace_mask (Namespace.child n x))
       (Namespace.namespace_mask (Namespace.child n y))
  then true else false
