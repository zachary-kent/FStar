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
  Logical Atomicity for Pulse — no admits, no axioms.

  Matches Iris atomic.v:
  - AU = νAU. |={Eo,Ei}=> ∃x. α(x) ∗ ((α(x) ={Ei,Eo}=∗ AU) ∧ (∀y. β(x,y) ={Ei,Eo}=∗ Φ(x,y)))
  - Encoded via FlippableInv (step-indexed greatest fixpoint via later credits)
  - au_commit CONSUMES the AU and produces Φ (matching Iris)
  - lat_elim: α(x₀) ⊢ ∃xy. Φ(x,y) — trivial composition of au_intro + f
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

[@@ erasable]
val au_token (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop) : Type0

instance val non_informative_au_token (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_token a b alpha beta phi)

val au_iname (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : GTot iname

(** AU is available: α(x) stored inside, ready to be opened. *)
val au_available (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : slprop

(** AU has been opened: α(x) extracted, awaiting abort or commit. *)
val au_opened (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : slprop

(** Introduction (Iris aupd_intro): deposit α(x₀) to create AU. *)
ghost fn au_intro (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
  requires alpha (reveal x0)
  returns tok : au_token a b alpha beta phi
  ensures au_available tok

(** Elimination — open (Iris aupd_aacc, extraction): AU → α(x) ∗ handle *)
ghost fn au_open (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  opens [au_iname tok]
  requires au_available tok ** later_credit 1
  returns x : erased a
  ensures alpha (reveal x) ** au_opened tok

(** Elimination — abort (Iris aupd_aacc, abort branch): α(x) ∗ handle → AU *)
ghost fn au_abort (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) (x : erased a)
  opens [au_iname tok]
  requires alpha (reveal x) ** au_opened tok ** later_credit 1
  ensures au_available tok

(** Elimination — commit (Iris aupd_aacc, commit branch): β(x,y) ∗ handle → Φ(x,y)
    CONSUMES the AU. The caller-provided cfn converts β into Φ. *)
ghost fn au_commit (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
    (x : erased a) (y : erased b)
    (cfn : unit -> stt_ghost unit emp_inames
        (beta (reveal x) (reveal y))
        (fun _ -> phi (reveal x) (reveal y)))
  requires beta (reveal x) (reveal y) ** au_opened tok
  ensures phi (reveal x) (reveal y)

(** LAT Elimination Rule.
    If f is logically atomic (takes AU, consumes it via commit, returns Φ),
    then given α(x₀), calling f produces ∃xy. Φ(x,y).
    This is the rule that invariants can be opened around LA ops:
    the AU acts as the invariant, f atomically transforms its contents. *)
fn lat_elim (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
  requires alpha (reveal x0)
  ensures (exists* (x:a) (y:b). phi x y)

(** Invariant opening around logically atomic operations.
    Iris aacc_aupd_commit (atomic.v line 387-400).

    Given α(x₀), a logically atomic f, and a split_phi that
    decomposes phi(x,y) into α(x') ** result(x,y):
    - Client recovers the updated α (to close their invariant)
    - Client gets result(x,y) as output

    split_phi corresponds to Iris's wand Φ(x,y) ={E1}=∗ Φ'(x',y')
    (atomic.v line 393). *)
fn lat_open (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#result : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
    (split_phi : (x:erased a) -> (y:erased b) ->
      stt_ghost unit emp_inames
        (phi (reveal x) (reveal y))
        (fun _ -> (exists* (x':a). alpha x') ** result (reveal x) (reveal y)))
  requires alpha (reveal x0)
  ensures (exists* (x:a). alpha x) ** (exists* (x:a) (y:b). result x y)

(** General abort-or-commit composition.
    Iris aacc_aupd (atomic.v line 373-385).

    f may either commit (return phi, AU consumed) or abort
    (return alpha + AU available). The on_commit/on_abort callbacks
    handle each case.

    Iris line 379 inner commit disjunction:
      (α(x) ∗ (AU ={E1}=∗ Φ')) ∨ (∃y. β(x,y) ∗ (Φ(x,y) ={E1}=∗ Φ'))
    Left = abort (on_abort), Right = commit (on_commit). *)
fn lat_open_gen (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#result : slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt bool (au_available tok)
        (fun committed ->
          if committed
          then (exists* (x:a) (y:b). phi x y)
          else (exists* (x:a). alpha x) ** au_available tok))
    (on_commit : (x:erased a) -> (y:erased b) ->
      stt_ghost unit emp_inames
        (phi (reveal x) (reveal y))
        (fun _ -> (exists* (x':a). alpha x') ** result))
    (on_abort :
      (tok : au_token a b alpha beta phi) ->
      stt unit
        ((exists* (x:a). alpha x) ** au_available tok)
        (fun _ -> (exists* (x:a). alpha x) ** result))
  requires alpha (reveal x0)
  ensures (exists* (x:a). alpha x) ** result
