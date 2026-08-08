(*
   Negative public-facade clients for the F01 mask abstraction boundary.

   Every declaration is expected to fail locally: these cases guard the
   representation boundary, reject unsupported operations, and keep proof-only
   relations out of runtime code.
*)
module MaskAlgebraNegative

module Core = Pulse.Lib.Core
module Mask = Pulse.Lib.Mask
module GhostSet = FStar.GhostSet

let needs_mask (_:Mask.mask) : unit = ()
let needs_authority (_:Core.slprop) : unit = ()

(* A public mask cannot be coerced to the raw legacy carrier. *)
[@@expect_failure [189]]
let mask_to_inames (m:Mask.mask) : Core.inames = m

(* A raw legacy carrier cannot be coerced to a public mask. *)
[@@expect_failure [189]]
let inames_to_mask (names:Core.inames) : Mask.mask = names

(* GhostSet.comprehend produces the private backing carrier, not a mask. *)
[@@expect_failure [12;34]]
let comprehend (p:Core.iname -> GTot bool) : Mask.mask = GhostSet.comprehend p

(* Backing-set destructors cannot inspect a public mask. *)
[@@expect_failure [189]]
let representation_inspect (i:Core.iname) (m:Mask.mask) : GTot bool =
  GhostSet.mem i m

(* The facade has no public representation reveal operation. *)
[@@expect_failure [72]]
let representation_reveal (m:Mask.mask) = Mask.reveal m

(* top is not a subset of empty in a context with an invariant name. *)
[@@expect_failure [19]]
let subset_top_empty (i:Core.iname) : Lemma (Mask.subset Mask.top Mask.empty) = ()

(* A singleton overlaps itself. *)
[@@expect_failure [19]]
let singleton_disjoint_self (i:Core.iname)
  : Lemma (Mask.disjoint (Mask.singleton i) (Mask.singleton i)) = ()

(* Removing top from a singleton cannot retain that singleton's member. *)
[@@expect_failure [19]]
let diff_singleton_top (i:Core.iname)
  : Lemma (Mask.mem i (Mask.diff (Mask.singleton i) Mask.top)) = ()

(* A singleton cannot equal empty. *)
[@@expect_failure [19]]
let singleton_empty (i:Core.iname) : Lemma (Mask.singleton i == Mask.empty) = ()

(* An action's opens index remains the raw legacy carrier. *)
[@@expect_failure [189]]
let opens_as_mask (opens:Core.inames) : unit = needs_mask opens

(* subset is proof-level and cannot drive executable control flow. *)
[@@expect_failure [34]]
let runtime_subset (e f:Mask.mask) : bool = if Mask.subset e f then true else false

(* disjoint is proof-level and cannot drive executable control flow. *)
[@@expect_failure [34]]
let runtime_disjoint (e f:Mask.mask) : bool = if Mask.disjoint e f then true else false

(* F01 has no namespace-aware allocator. *)
[@@expect_failure [72]]
let namespace_allocator (m:Mask.mask) = Mask.fresh_in_namespace m

(* F01 has no fancy-update or endpoint-transition operation. *)
[@@expect_failure [72]]
let fupd_transition = Mask.fupd

(* Membership is a pure fact, not invariant-authority resource. *)
[@@expect_failure [189]]
let mem_authority (i:Core.iname) (e:Mask.mask) (member:Mask.mem i e) : unit =
  needs_authority member

(* PulseCore's actual-open except context remains raw, not a mask. *)
[@@expect_failure [189]]
let except_as_mask (except:Core.inames) : unit = needs_mask except
