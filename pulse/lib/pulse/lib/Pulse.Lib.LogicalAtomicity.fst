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
  Implementation of Logical Atomicity for Pulse.

  Uses ghost state and invariants following the CancellableInvariant pattern.
  Core operations use admit() as placeholders — a full implementation would
  encode the AU greatest fixpoint using ghost refs and an internal invariant.
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

(** Internal ghost status for AU lifecycle *)
type au_status =
  | AUAvailable
  | AUOpened
  | AUCommitted

(** Internal AU record *)
[@@ erasable]
noeq
type au_internal (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop) = {
  status_ref : GR.ref bool;
}

instance non_informative_au_internal
    (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_internal a b alpha beta phi)
  = { reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (au_internal a b alpha beta phi) }

(** The AU token: ghost ref half + invariant *)
let atomic_update
    (a:Type0) (b:Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : slprop
  = exists* (aui : au_internal a b alpha beta phi).
      pts_to aui.status_ref #0.5R true

(** The AU handle: other half of ghost ref *)
let au_handle
    (a:Type0) (b:Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
    (x : a)
  : slprop
  = exists* (aui : au_internal a b alpha beta phi).
      pts_to aui.status_ref #0.5R false

ghost
fn au_open
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (_:unit)
  requires atomic_update a b alpha beta phi
  returns x : erased a
  ensures alpha (reveal x) ** au_handle a b alpha beta phi (reveal x)
{
  admit ()
}

ghost
fn au_abort
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#x : erased a)
    (_:unit)
  requires alpha (reveal x) ** au_handle a b alpha beta phi (reveal x)
  ensures atomic_update a b alpha beta phi
{
  admit ()
}

ghost
fn au_commit
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#x : erased a)
    (y : erased b)
  requires beta (reveal x) (reveal y) ** au_handle a b alpha beta phi (reveal x)
  ensures phi (reveal x) (reveal y)
{
  admit ()
}

ghost
fn au_intro
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (q : slprop)
    (accessor : (x:erased a) ->
      stt_ghost unit emp_inames
        (alpha (reveal x) ** q)
        (fun _ -> q))
    (committer : (x:erased a) -> (y:erased b) ->
      stt_ghost unit emp_inames
        (beta (reveal x) (reveal y) ** q)
        (fun _ -> phi (reveal x) (reveal y)))
  requires q
  ensures atomic_update a b alpha beta phi
{
  admit ()
}
