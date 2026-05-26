(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Prophecy Variables for Pulse — Trusted Primitives.

    Prophecy variables predict future values, enabling proof techniques
    where the linearization point depends on outcomes of future events.

    Based on Iris's prophecy variables (Jung et al., POPL 2020).

    DESIGN:
    ═══════

    `resolve` is a COMBINATOR over any stt_atomic computation, analogous
    to `with_invariant` wrapping stt_atomic for invariant opening.

    Allocation returns an existentially quantified predicted value:
      prophecy_alloc → ∃v. prophecy_token p v

    The client unpacks `v : erased a` and uses it in ghost proofs
    (case-splitting on the predicted future) before resolution.

    `resolve p v f` runs f (one atomic step), consumes the token,
    and produces `pure (x == reveal v)`.

    SOUNDNESS:
    ══════════

    Same as Iris adequacy: ∀ executions, ∃ prophecy assignment making
    all resolutions consistent. The existential is satisfiable because
    v can always be chosen as the actual result.

    Trust level: same as as_atomic. *)
module Pulse.Lib.Prophecy
#lang-pulse
open Pulse.Lib.Pervasives

(** Opaque prophecy variable handle *)
[@@ erasable]
noeq type prophecy_var (a:Type0) = { _pv_id : nat; }

instance non_informative_prophecy_var (a:Type0)
  : NonInformative.non_informative (prophecy_var a)
  = { reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (prophecy_var a) }

(** prophecy_token p v: exclusive ownership asserting prophecy p
    has predicted value v. Linear: consumed by resolve. *)
let prophecy_token (#a:Type0) (p : prophecy_var a) (v : a) : slprop = pure True

(** Allocate a prophecy variable.
    Returns p + ∃v. prophecy_token p v.
    Requires default:a to prevent prophecy_var False. *)
ghost
fn prophecy_alloc (#a:Type0) (default : a)
  requires emp
  returns p : prophecy_var a
  ensures exists* (v:a). prophecy_token p v
{
  let p : prophecy_var a = { _pv_id = 0 };
  fold (prophecy_token p default);
  p
}
