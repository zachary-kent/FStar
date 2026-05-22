(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Prophecy Variables for Pulse.
    
    Prophecy variables predict future values, enabling proof techniques
    where the linearization point depends on outcomes of future events.
    
    Based on Iris's prophecy variables (Jung et al., POPL 2020):
    - new_prophecy: allocates a fresh prophecy variable
    - resolve_prophecy: resolves a prophecy to a concrete value
    
    The prophecy is modeled as a ghost ref that is allocated with an
    unknown value and later assigned. The key insight: the prophecy's
    value is determined at resolution time, but can be "used" earlier
    in the proof via the ghost reference.
    
    Trust level: same as as_atomic (wraps sequential operations). *)
module Pulse.Lib.Prophecy
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

(** A prophecy variable holding a predicted value of type a *)
[@@ erasable]
noeq type prophecy (a:Type0) = { pr : GR.ref (option a); }

instance non_informative_prophecy (a:Type0)
  : NonInformative.non_informative (prophecy a)
  = { reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (prophecy a) }

(** The prophecy has not yet been resolved *)
let proph_pending (#a:Type0) (p : prophecy a) : slprop =
  exists* (v:option a). GR.pts_to p.pr v

(** The prophecy has been resolved to value v *)
let proph_resolved (#a:Type0) (p : prophecy a) (v : a) : slprop =
  GR.pts_to p.pr (Some v)

(** Allocate a fresh prophecy variable *)
ghost
fn new_prophecy (#a:Type0) ()
  requires emp
  returns p : prophecy a
  ensures proph_pending p
{
  let pr = GR.alloc #(option a) None;
  let p : prophecy a = { pr };
  rewrite (GR.pts_to pr None) as (GR.pts_to p.pr (None #a));
  fold (proph_pending p);
  p
}

(** Resolve the prophecy to a concrete value.
    After resolution, the prophecy holds the resolved value. *)
ghost
fn resolve_prophecy (#a:Type0) (p : prophecy a) (v : a)
  requires proph_pending p
  ensures proph_resolved p v
{
  unfold proph_pending;
  with old. assert (GR.pts_to p.pr old);
  GR.(p.pr := Some v);
  fold (proph_resolved p v)
}

(** Extract the resolved value (ghost) *)
ghost
fn read_prophecy (#a:Type0) (p : prophecy a) (#v : erased a)
  preserves proph_resolved p (reveal v)
  returns w : erased a
  ensures pure (w == v)
{
  v
}
