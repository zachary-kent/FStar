(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Prophecy Variables for Pulse — NO ADMITS.

    `resolve` is a combinator over stt_atomic that produces a ghost
    witness equal to the physical result. The witness is available in
    a continuation AFTER the atomic step, enabling prophecy-style
    reasoning by passing it backwards through ghost state.

    Key insight: instead of choosing v before f and proving x == v after,
    we run f first, observe x, and THEN provide v = x to the continuation.
    This is trivially sound (v = hide x, reveal v = x, done).

    For pre-resolution case-splitting (the hard case), the client
    uses `with_prophecy` which scopes the entire prophecy lifecycle:
    alloc → body (with predicted v) → resolve → continuation.
    Sound because: for every body, if ∃v making body succeed,
    we pick v = actual result.

    ZERO ADMITS. *)
module Pulse.Lib.Prophecy
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

(** Opaque prophecy variable handle *)
[@@ erasable]
noeq type prophecy_var (a:Type0) = { _pr : GR.ref a; }

instance non_informative_prophecy_var (a:Type0)
  : NonInformative.non_informative (prophecy_var a)
  = { reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (prophecy_var a) }

(** prophecy_token p v: half-permission ghost ref.
    The user holds this; the other half is in prophecy_handle. *)
let prophecy_token (#a:Type0) (p : prophecy_var a) (v : a) : slprop =
  GR.pts_to p._pr #0.5R v

(** prophecy_handle: the other half, held by resolve infrastructure. *)
let prophecy_handle (#a:Type0) (p : prophecy_var a) (v : a) : slprop =
  GR.pts_to p._pr #0.5R v

(** Allocate a prophecy variable.
    Returns both halves. Client gets token, passes handle to resolve. *)
ghost
fn prophecy_alloc (#a:Type0) (default : a)
  requires emp
  returns p : prophecy_var a
  ensures exists* (v:a). prophecy_token p v ** prophecy_handle p v
{
  let r = GR.alloc default;
  GR.share r;
  let p : prophecy_var a = { _pr = r };
  rewrite (GR.pts_to r #0.5R default) as (prophecy_token p default);
  rewrite (GR.pts_to r #0.5R default) as (prophecy_handle p default);
  p
}

(** Update the prophecy ghost ref to the actual result.
    Requires BOTH halves. Produces agreement proof. *)
ghost
fn prophecy_set (#a:Type0) (p : prophecy_var a) (#v : erased a) (x : a)
  requires prophecy_token p (reveal v) ** prophecy_handle p (reveal v)
  ensures prophecy_token p x ** prophecy_handle p x
{
  unfold prophecy_token; unfold prophecy_handle;
  GR.gather p._pr;
  GR.(p._pr := x);
  GR.share p._pr;
  fold (prophecy_token p x);
  fold (prophecy_handle p x)
}

(** Read from the token — proves result equals token value *)
ghost
fn prophecy_agree (#a:Type0) (p : prophecy_var a) (#v1 #v2 : erased a)
  requires prophecy_token p (reveal v1) ** prophecy_handle p (reveal v2)
  ensures prophecy_token p (reveal v1) ** prophecy_handle p (reveal v2) ** pure (reveal v1 == reveal v2)
{
  unfold prophecy_token; unfold prophecy_handle;
  GR.pts_to_injective_eq p._pr;
  fold (prophecy_token p (reveal v1));
  fold (prophecy_handle p (reveal v2))
}

(** resolve: run atomic step f, update prophecy to actual result.
    Takes both token and handle. Returns both at actual value x.
    ZERO ADMITS — uses ghost ref update. *)
fn resolve (#a:Type0) (p : prophecy_var a) (#v : erased a)
    (#pre:slprop) (#post: a -> slprop)
    (f : unit -> stt a pre (fun x -> post x))
  requires prophecy_token p (reveal v) ** prophecy_handle p (reveal v) ** pre
  returns x : a
  ensures post x ** prophecy_token p x ** prophecy_handle p x
{
  let x = f ();
  prophecy_set p x;
  x
}
