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

  This module provides logically atomic triples (LATs), adapting the
  Iris encoding (iris/bi/lib/atomic.v) to Pulse's separation logic.

  Key constructs:
  - `atomic_update a b alpha beta phi`: AU token
  - `au_handle`: opened AU handle (must be consumed by abort or commit)
  - `au_open`: decompose AU into alpha(x) + handle
  - `au_abort`: give back alpha(x), recover AU (retry)
  - `au_commit`: provide beta(x,y), receive phi(x,y) (linearization point)
  - `au_intro`: create AU from accessor/committer pair (coinduction)

  References:
  - Iris atomic.v (gitlab.mpi-sws.org/iris/iris)
  - TaDA (da Rocha Pinto et al., ECOOP 2014)
  - HOCAP (Svendsen et al., ICFP 2013)
  - Prophecy Variables in Iris (Jung et al., POPL 2020)
  - Diaframe (Mulder & Krebbers, POPL 2023)
  - Raven (Gupta et al., CAV 2025)
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

(** The atomic update token. Represents the client's offer to have their
    abstract state atomically transformed from alpha to beta.
    - a: type of abstract state witnesses
    - b: type of result witnesses
    - alpha: atomic precondition (abstract state before)
    - beta: atomic postcondition (abstract state after)
    - phi: committer's reward (what the function receives on commit)
*)
val atomic_update
    (a:Type0) (b:Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : slprop

(** Handle for an opened AU. Must be consumed by au_abort or au_commit.
    Witnesses the abstract state x observed when the AU was opened. *)
val au_handle
    (a:Type0) (b:Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
    (x : a)
  : slprop

(** Open an atomic update: get alpha(x) + handle.
    Corresponds to Iris aupd_aacc: AU |- atomic_acc alpha AU beta phi *)
ghost
fn au_open
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (_:unit)
  requires atomic_update a b alpha beta phi
  returns x : erased a
  ensures alpha (reveal x) ** au_handle a b alpha beta phi (reveal x)

(** Abort: give back alpha(x), recover AU (for CAS loop retry).
    Corresponds to Iris abort branch: alpha(x) ={Ei,Eo}=* AU *)
ghost
fn au_abort
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#x : erased a)
    (_:unit)
  requires alpha (reveal x) ** au_handle a b alpha beta phi (reveal x)
  ensures atomic_update a b alpha beta phi

(** Commit: provide beta(x,y), receive phi(x,y) (linearization point).
    Corresponds to Iris commit branch: beta(x,y) ={Ei,Eo}=* phi(x,y) *)
ghost
fn au_commit
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#x : erased a)
    (y : erased b)
  requires beta (reveal x) (reveal y) ** au_handle a b alpha beta phi (reveal x)
  ensures phi (reveal x) (reveal y)

(** Introduction rule (coinductive): create AU from accessor pattern.
    The accessor can be called repeatedly (open/abort/open/abort/...)
    because aborting restores q, from which the accessor can run again.

    Corresponds to Iris aupd_intro:
      (P /\ Q |- atomic_acc alpha Q beta phi) -> P /\ Q |- AU

    Parameters:
    - q: "fuel" state, consumed to access alpha, restored on abort
    - accessor: given alpha(x) ** q, restores q (abort handler)
    - committer: given beta(x,y) ** q, produces phi(x,y) (commit handler) *)
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
