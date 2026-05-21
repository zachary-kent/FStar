(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(**
  Logical Atomicity for Pulse

  Provides logically atomic triples (LATs) following the Iris encoding
  (iris/bi/lib/atomic.v), adapted to Pulse's separation logic.
  All operations are fully proven — no admits or axioms.

  The encoding uses the FlippableInv pattern (ghost bool ref + invariant)
  to store the abstract state alpha(x). The AU supports:
  - Open/abort cycles (for CAS loop retries)
  - One-shot commit (at the linearization point)

  The commit handler is provided by the caller at commit time, not stored
  in the AU. This avoids higher-order ghost state storage issues while
  remaining expressive enough for standard lock-free data structures.

  References: Iris atomic.v, TaDA, HOCAP, Prophecy Variables in Iris,
  Diaframe, Raven, Later Credits (Spies et al. 2022).
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

(** AU token: an erasable value identifying a particular AU instance.
    Analogous to CancellableInvariant.cinv — a value you pass around,
    with separate slprop predicates for the AU's state. *)
[@@ erasable]
val au_token
    (a:Type0) (b:Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : Type0

instance val non_informative_au_token
    (a:Type0) (b:Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_token a b alpha beta phi)

(** Extract the iname of the AU's internal invariant.
    Needed for opens clauses when calling au_open/au_abort. *)
val au_iname
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  : GTot iname

(** AU is available: abstract state alpha(x) is stored inside.
    The function that holds this can call au_open. *)
val au_available
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  : slprop

(** AU has been opened: alpha(x) was extracted, awaiting abort or commit. *)
val au_opened
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  : slprop

(** Create an AU by depositing initial abstract state alpha(x0). *)
ghost
fn au_intro
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
  requires alpha (reveal x0)
  returns tok : au_token a b alpha beta phi
  ensures au_available tok

(** Open: extract alpha(x), transition to opened state.
    Requires later_credit to open the internal invariant. *)
ghost
fn au_open
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  opens [au_iname tok]
  requires au_available tok ** later_credit 1
  returns x : erased a
  ensures alpha (reveal x) ** au_opened tok

(** Abort: return alpha(x), transition back to available.
    Used on CAS failure to retry the loop. *)
ghost
fn au_abort
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
    (x : erased a)
  opens [au_iname tok]
  requires alpha (reveal x) ** au_opened tok ** later_credit 1
  ensures au_available tok

(** Commit: consume the AU at the linearization point.
    The caller provides a ghost step converting beta(x,y) to phi(x,y).
    The AU handle is permanently consumed (invariant left empty). *)
ghost
fn au_commit
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
    (x : erased a) (y : erased b)
    (cfn : unit ->
      stt_ghost unit emp_inames
        (beta (reveal x) (reveal y))
        (fun _ -> phi (reveal x) (reveal y)))
  requires beta (reveal x) (reveal y) ** au_opened tok
  ensures phi (reveal x) (reveal y)
