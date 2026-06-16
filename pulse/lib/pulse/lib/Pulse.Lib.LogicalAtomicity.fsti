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
  Logical Atomicity for Pulse — adapted from Iris's atomic.v.
  
  Reference: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/bi/lib/atomic.v

  ═══════════════════════════════════════════════════════════════════
  IRIS CORRESPONDENCE TABLE
  ═══════════════════════════════════════════════════════════════════

  ┌──────────────────────┬─────────────────────────────────────────┬───────────────┐
  │ Pulse                │ Iris (atomic.v)                        │ Faithfulness  │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ au_token is a b α β Φ  │ atomic_update Eo Ei α β Φ : PROP       │ Reified token │
  │                      │   (line 25-27, greatest fixpoint ν)    │ vs BI prop    │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ au_available tok     │ AU Eo Ei α β Φ                         │ ✓ protocol    │
  │                      │   (the AU proposition itself)           │               │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ au_opened tok x      │ α(x) ∗ abort-cont ∗ commit-cont       │ ✓ protocol    │
  │                      │   (opened accessor state, line 16-20)  │ indexed by x  │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ au_intro             │ Not directly aupd_intro (line 276).    │ Concrete      │
  │                      │   Iris requires □(P -∗ atomic_acc ...) │ intro form    │
  │                      │   (persistent, coinductive accessor).   │               │
  │                      │   Pulse requires concrete α(x₀) + trade│               │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ au_open              │ aupd_aacc (line 253): unfold AU into   │ ✓ faithful    │
  │                      │   atomic_acc Eo Ei α AU β Φ            │               │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ au_abort             │ Abort branch: α(x) ={Ei,Eo}=∗ AU      │ ✓ faithful    │
  │                      │   (line 17, first conjunct)             │               │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ au_commit            │ Commit branch: ∀y. β(x,y) ={Ei,Eo}=∗  │ ✓ protocol    │
  │                      │   Φ(x,y) (line 25-27)                  │ trade not fupd│
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ trade (@==>)         │ ={Ei,Eo}=∗ (mask-changing fancy update)│ Same-mask     │
  │                      │   PulseCore paper: trade ≈ ={E}=∗      │ subset only   │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ lat_elim             │ Simple AU introduction + execution      │ ✓ faithful    │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ lat_open             │ aacc_aupd_commit (line 387): accessor  │ Restricted    │
  │                      │   composition with AU. Pulse captures   │ commit-only   │
  │                      │   commit+postprocess, not full accessor │ pattern       │
  │                      │   composition with mask choreography.   │               │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ opens [au_iname tok] │ Eo, Ei mask algebra                    │ Single-inv    │
  │                      │   (Iris: arbitrary mask sets)           │ approximation │
  ├──────────────────────┼─────────────────────────────────────────┼───────────────┤
  │ later_credit 1       │ ▷ from invariant opening               │ Explicit      │
  │                      │   (Iris: handled by fupd/step-index)   │ accounting    │
  └──────────────────────┴─────────────────────────────────────────┴───────────────┘

  ═══════════════════════════════════════════════════════════════════
  ENCODING DESIGN
  ═══════════════════════════════════════════════════════════════════

  Iris AU = ν AU. |={Eo,Ei}=> ∃x. α(x) ∗ ((α(x) ={Ei,Eo}=∗ AU) ∧ (∀y. β(x,y) ={Ei,Eo}=∗ Φ(x,y)))

  Pulse encoding (FlippableInv):
    ghost bool ref `gr` + invariant over:
      ∃flag. gr ↦{½} flag ∗ (if flag then ∃x. α(x) ∗ ∀*y. β(x,y) @==> Φ(x,y) else emp)
    
    au_available = gr ↦{½} true  ∗ inv(au_inv_p)
    au_opened(x) = gr ↦{½} false ∗ inv(au_inv_p) ∗ ∀*y. β(x,y) @==> Φ(x,y)

    open:   flip true→false, extract α(x) + trade
    abort:  flip false→true, re-deposit α(x) + trade
    commit: consume trade via elim_forall + elim_trade, drop remnants

  ═══════════════════════════════════════════════════════════════════
  KNOWN GAPS (from GPT-5.5 audit)
  ═══════════════════════════════════════════════════════════════════

  1. No greatest fixpoint: FlippableInv is a state machine, not ν.
     Iris aupd_intro requires □(P -∗ atomic_acc ...); ours requires
     concrete α(x₀) + trade. (Fundamental limitation of encoding.)

  2. No mask-changing fancy update: trade is same-mask (emp_inames).
     Iris commit can open invariants during ={Ei,Eo}=∗; ours cannot.
     (Addressable with richer Pulse trade parameterized over inames.)

  3. lat_open is not aacc_aupd_commit: captures commit+postprocess
     pattern only, not full accessor/AU composition with 4-mask
     choreography. (Addressable with more infrastructure.)

  4. au_opened indexed by x is sound under abstraction (.fsti hides
     the implementation). The stored trade carries x, preventing
     open-at-x₁ / commit-at-x₂ mismatch. (Faithfully captured.)

  5. au_commit drops ghost resources (half-permission + invariant).
     This is sound: matches Iris where commit produces only Φ.
     (Faithfully captured.)
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Forall
module GR = Pulse.Lib.GhostReference

(** AU token: reified representation of Iris's atomic_update Eo Ei α β Φ.
    Iris: atomic_update is a PROP (greatest fixpoint). Here: an allocated
    ghost object (ghost bool ref + invariant name). See atomic.v line 25-27. *)
[@@ erasable]
val au_token (is:inames) (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop) : Type0

instance val non_informative_au_token (is:inames) (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_token is a b alpha beta phi)

(** The iname backing the AU invariant.
    Iris: AU opening uses masks Eo→Ei. Pulse approximation: opens [au_iname tok]. *)
val au_iname (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) : GTot iname

(** AU is available (not currently opened). Iris: the AU proposition itself. *)
val au_available (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) : slprop

(** AU has been opened, witnessing abstract value x.
    Iris: the opened accessor state — α(x) is extracted, abort/commit branches available.
    The handle is indexed by x (phantom), preventing open-at-x₁/commit-at-x₂.
    See atomic.v line 16-20 (atomic_acc definition). *)
val au_opened (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) (x : a) : slprop

(** Introduction: deposit α(x₀) AND the commit contract ∀y. β(x₀,y) @==> Φ(x₀,y).
    
    Iris aupd_intro (line 276) requires □(P -∗ atomic_acc Eo Ei α P β Φ) — a
    persistent, coinductive accessor premise. Our concrete form requires
    concrete α(x₀) + trade instead. This is strictly more explicit: the client
    must provide the initial abstract state and commit contract upfront.
    Gap: no coinductive/persistent accessor. *)
ghost fn au_intro (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
  requires alpha (reveal x0) ** (forall* (y:b). trade #is (later_credit 1 ** beta (reveal x0) y) (phi (reveal x0) y))
  returns tok : au_token is a b alpha beta phi
  ensures au_available tok

(** Recommended API layering.

    Most clients should use [au_atomic_step] below: it brackets [au_open]
    around one atomic LP attempt and immediately closes with [au_commit]
    (success) or [au_abort] (retry/no-LP).  The raw [au_open], [au_commit],
    and [au_abort] primitives remain public for advanced helping protocols
    such as RDCSS, where an AU/accessor may be peeked, stored under another
    invariant, or committed by a helper. *)

(** Open: extract α(x). The commit contract stays in the handle.
    Iris aupd_aacc (line 253): unfolds AU into atomic_acc Eo Ei α AU β Φ.
    Faithfully captured: open extracts α(x), abort restores AU, commit yields Φ. *)
ghost fn au_open (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi)
  opens [au_iname tok]
  requires au_available tok ** later_credit 1
  returns x : erased a
  ensures alpha (reveal x) ** au_opened tok (reveal x)

(** Abort: return α(x), recover AU.
    Iris abort branch (line 17): α(x) ={Ei,Eo}=∗ AU.
    Faithfully captured: flips ghost bool false→true. *)
ghost fn au_abort (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) (x : erased a)
  opens [au_iname tok]
  requires alpha (reveal x) ** au_opened tok (reveal x) ** later_credit 1
  ensures au_available tok

(** Commit: provide β(x,y), get Φ(x,y). Uses stored trade — NO external cfn.
    Iris commit branch (line 25-27): ∀y. β(x,y) ={Ei,Eo}=∗ Φ(x,y).
    Gap: trade is same-mask (@==> with emp_inames), not mask-changing ={Ei,Eo}=∗.
    Iris commit can open invariants during the fancy update; ours cannot.
    Faithfully captured: protocol shape (β in, Φ out, AU consumed). *)
ghost fn au_commit (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi)
    (x : erased a) (y : b)
  opens is
  requires later_credit 1 ** beta (reveal x) y ** au_opened tok (reveal x)
  ensures phi (reveal x) y

(** Bracketed AU step: open the AU, run one atomic LP attempt, then close
    immediately.  [Some y] commits with [beta x y] and produces [phi x y];
    [None] aborts and restores [au_available tok].  The three later credits
    pay for AU open, the client's atomic body (typically an invariant-opened
    read/CAS), and AU close.  [body_inames] are the invariant names the
    one-step body may open in addition to the AU/trade names. *)
atomic fn au_atomic_step (#is : inames) (#body_inames : inames) (#a : Type0) (#b : Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#r_pre : slprop) (#r_post : b -> slprop)
    (tok : au_token is a b alpha beta phi)
    (body : (x : erased a) -> stt_atomic (option b) #Observable body_inames
       (r_pre ** later_credit 1 ** alpha (reveal x))
       (fun result -> match result with
         | Some y -> r_post y ** beta (reveal x) y
         | None -> r_pre ** alpha (reveal x)))
  opens add_inv (join_inames is body_inames) (au_iname tok)
  requires au_available tok ** r_pre ** later_credit 3
  returns result : option b
  ensures (match result with
    | Some y -> exists* (x:a). phi x y ** r_post y
    | None -> au_available tok ** r_pre)

(** Commit an outer AU by running an inner LAT as a black box.

    This advanced nested-LAT helper opens the outer AU, packages its α
    resource and commit continuation into an inner AU token, runs [f]
    (typically an inner LAT implementation whose own LP attempts use
    [au_atomic_step]), and closes the outer AU from the inner commit trade.
    User examples can therefore compose nested LATs without spelling raw
    [au_open]/[au_commit]/[au_abort] windows themselves. *)
fn au_commit_via_lat (#is:inames) (#a:Type0) (#b:Type0) (#c:Type0)
    (#alpha : a -> slprop)
    (#outer_beta : a -> b -> slprop) (#outer_phi : a -> b -> slprop)
    (#inner_beta : a -> c -> slprop)
    (#frame : slprop) (#result : slprop)
    (tok : au_token is a b alpha outer_beta outer_phi)
    (outer_y : b)
    (beta_to_outer : (x:erased a) -> (z:c) ->
      stt_ghost unit emp_inames
        (inner_beta (reveal x) z)
        (fun _ -> outer_beta (reveal x) outer_y))
    (post_commit : (x:erased a) ->
      stt_ghost unit emp_inames
        (outer_phi (reveal x) outer_y)
        (fun _ -> result))
    (f : (x:erased a) ->
      (inner_tok : au_token is a c alpha inner_beta (fun _ z -> result)) ->
      stt c (frame ** au_available inner_tok) (fun _ -> frame ** result))
  requires frame ** au_available tok ** later_credit 1
  returns z : c
  ensures frame ** result

(** lat_elim: simple AU introduction + execution.
    Iris: directly composing au_intro with an AU-consuming computation.
    Faithfully captured. *)

fn lat_elim (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token is a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
  requires alpha (reveal x0) ** (forall* (y:b). trade #is (later_credit 1 ** beta (reveal x0) y) (phi (reveal x0) y))
  ensures (exists* (x:a) (y:b). phi x y)

(** lat_open: restricted form of Iris aacc_aupd_commit (line 387).
    Iris: composes an outer AU with an inner atomic accessor, handling
    abort paths and 4-mask choreography (E1, E1', E2, E3).
    Pulse: captures commit+postprocess pattern only. Runs f(tok) to
    produce Φ, then uses split_phi to decompose Φ into restored α +
    result. Does NOT model abort-path composition or mask choreography.
    Gap: restricted to commit-only postprocessing; no inner accessor. *)
fn lat_open (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#result : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token is a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
    (split_phi : (x:erased a) -> (y:erased b) ->
      stt_ghost unit emp_inames
        (phi (reveal x) (reveal y))
        (fun _ -> (exists* (x':a). alpha x' ** (forall* (yy:b). trade #is (later_credit 1 ** beta x' yy) (phi x' yy))) ** result (reveal x) (reveal y)))
  requires alpha (reveal x0) ** (forall* (y:b). trade #is (later_credit 1 ** beta (reveal x0) y) (phi (reveal x0) y))
  ensures (exists* (x:a). alpha x ** (forall* (y:b). trade #is (later_credit 1 ** beta x y) (phi x y))) ** (exists* (x:a) (y:b). result x y)

(* ================================================================ *)
(* Logically Atomic Triple (LAT) type                               *)
(* ================================================================ *)

(** Direct Iris-style logically atomic triple.

    This is the Pulse analogue of the common Iris surface form

      <<{ ∀∀ x, α x }>> e @ E <<{ ∃∃ y, β x y | RET y }>>

    rather than the lower-level AU-consumer shape.  A client chooses an
    arbitrary ordinary postcondition [Phi] over the returned value.  The
    implementation receives only an AU token whose commit continuation is
    fixed to [fun x y -> Phi y].  Thus the implementation cannot choose,
    inspect, or hard-code the client's postcondition; it can obtain [Phi r]
    only by committing the AU with atomic postcondition [β x r].

    The post-state witness [b] is also the return type.  Unit-returning
    operations are ordinary instances with [b = unit]; no separate _void
    variant is needed. *)
let lat (is:inames) (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (frame : slprop) =
  phi:(b -> slprop) ->
  (tok : au_token is a b alpha beta (fun (_x:a) (y:b) -> phi y)) ->
  (_u : unit) ->
  stt b (frame ** au_available tok) (fun r -> frame ** phi r)
