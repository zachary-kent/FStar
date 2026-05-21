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

  Adapts Iris's atomic.v to Pulse using the FlippableInv pattern.
  The AU is a greatest fixpoint (step-indexed via later credits:
  each open/abort cycle costs credits, providing guardedness through
  Pulse's step-indexed invariant mechanism).

  ## Iris correspondence

  Iris `atomic_acc Eo Ei α P β Φ` =
    |={Eo,Ei}=> ∃ x. α(x) ∗ ((α(x) ={Ei,Eo}=∗ P) ∧ (∀ y. β(x,y) ={Ei,Eo}=∗ Φ(x,y)))

  Iris `atomic_update Eo Ei α β Φ` =
    νAU. atomic_acc Eo Ei α AU β Φ

  In Pulse:
  - atomic_acc is encoded operationally: au_open provides α(x) + handle,
    au_abort/au_commit consume the handle
  - atomic_update is the FlippableInv invariant containing ∃x. α(x)
  - The greatest fixpoint comes from the FlippableInv being reusable:
    abort restores the AU (= flips the inv back on)

  ## Rules proven

  - au_intro: create AU from α(x) — Iris aupd_intro (special case Q=α)
  - au_open: AU ⊢ α(x) ∗ handle — Iris aupd_aacc left component
  - au_abort: α(x) ∗ handle ⊢ AU — Iris aupd_aacc abort branch
  - au_commit: β(x,y) ∗ handle ⊢ Φ(x,y) ∗ AU — restoring commit
  - au_commit_consume: β(x,y) ∗ handle ⊢ Φ(x,y) — consuming commit
  - lat_elim: ∀f logically-atomic. α(x₀) ⊢ (∃x. α(x)) ∗ (∃xy. Φ(x,y))
    — the LAT elimination rule proving invariants can be opened around LA ops
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

(** ============================================================
    AU token and predicates
    ============================================================ *)

[@@ erasable]
val au_token
    (a:Type0) (b:Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : Type0

instance val non_informative_au_token
    (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_token a b alpha beta phi)

val au_iname
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  : GTot iname

val au_available
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  : slprop

val au_opened
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  : slprop

(** ============================================================
    Introduction (Iris aupd_intro, specialized to Q = α(x₀))
    ============================================================ *)

(** Create AU by depositing α(x₀).
    Corresponds to Iris aupd_intro with Q = α(x₀). *)
ghost
fn au_intro
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
  requires alpha (reveal x0)
  returns tok : au_token a b alpha beta phi
  ensures au_available tok

(** ============================================================
    Elimination (Iris aupd_aacc)

    AU unfolds to: ∃x. α(x) ∗ (abort: α(x) → AU) ∧ (commit: β(x,y) → Φ(x,y))
    Encoded as three operations: au_open, au_abort, au_commit.
    ============================================================ *)

(** Open: extract α(x) from the AU.
    Iris: left component of aupd_aacc. *)
ghost
fn au_open
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  opens [au_iname tok]
  requires au_available tok ** later_credit 1
  returns x : erased a
  ensures alpha (reveal x) ** au_opened tok

(** Abort: return α(x), recover AU.
    Iris: abort branch of aupd_aacc: α(x) ={Ei,Eo}=∗ AU. *)
ghost
fn au_abort
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
    (x : erased a)
  opens [au_iname tok]
  requires alpha (reveal x) ** au_opened tok ** later_credit 1
  ensures au_available tok

(** Commit (restoring): deposit α(new_x) back into AU + produce Φ.
    The cfn splits β(x,y) into α(new_x) ∗ Φ(x,y).
    Iris: commit branch of aupd_aacc: β(x,y) ={Ei,Eo}=∗ Φ(x,y),
    extended to also restore the AU with updated abstract state. *)
ghost
fn au_commit
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
    (x : erased a) (y : erased b)
    (new_x : erased a)
    (cfn : unit ->
      stt_ghost unit emp_inames
        (beta (reveal x) (reveal y))
        (fun _ -> alpha (reveal new_x) ** phi (reveal x) (reveal y)))
  opens [au_iname tok]
  requires beta (reveal x) (reveal y) ** au_opened tok ** later_credit 1
  ensures phi (reveal x) (reveal y) ** au_available tok

(** Commit (consuming): permanently consume the AU.
    Use when client does not need updated α back.
    Iris: commit branch of aupd_aacc: β(x,y) ={Ei,Eo}=∗ Φ(x,y). *)
ghost
fn au_commit_consume
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

(** ============================================================
    LAT Elimination Rule

    The key metatheoretic rule: if f is logically atomic
    (takes au_available, returns au_available + Φ after commit),
    and the client has α(x₀), then calling f yields the updated
    α(new_x) AND Φ(x,y).

    This demonstrates that the AU acts as an invariant containing α,
    and f atomically updates it — matching Iris's rule that invariants
    can be opened around logically atomic operations.
    ============================================================ *)

fn lat_elim
    (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt unit
        (au_available tok)
        (fun _ -> au_available tok ** (exists* (x:a) (y:b). phi x y)))
  requires alpha (reveal x0)
  ensures (exists* (x:a). alpha x) ** (exists* (x:a) (y:b). phi x y)
