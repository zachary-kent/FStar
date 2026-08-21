(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Untyped singleton prophecy-world resource.

    This is a low-level adapter over [PulseCore.ProphecyWorld] using the same
    ghost-table resource discipline as the current Pulse prophecy facade.  It is
    intentionally untyped: there is one nat-encoded prophecy world, not one
    authority per public [(result, payload)] projection.  Public typed
    NewProph/Resolve still need a dedicated semantic/runner rule before they can
    open this singleton from active adequacy, but this module fixes the concrete
    resource shape that rule must own and update. *)
module Pulse.Lib.ProphecyWorldResource
#lang-pulse

open Pulse.Lib.Pervasives
module GFT = Pulse.Lib.GhostFractionalTable
module PW = PulseCore.ProphecyWorld
module NST = PulseCore.NondeterministicHoareStateMonad

[@@erasable]
noeq type authority = {
  world_table: GFT.table PW.state_view;
  world_slot: nat;
}

let authority_state (auth:authority) (st:PW.state_view) : slprop =
  GFT.pts_to auth.world_table auth.world_slot #1.0R st

let active_world_interp
    (auth:authority)
    (st:PW.state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
  : slprop
= authority_state auth st ** pure (PW.state_interp st /\ PW.runtime_matches_ctr st ot c len)

let active_world_si
    (auth:authority)
    (ot:NST.obs_tape)
    (c:NST.ctr)
  : slprop
= exists* (st:PW.state_view) (len:nat).
    active_world_interp auth st ot c len

ghost
fn authority_init
    (#initial:erased PW.state_view)
    (#ot:erased NST.obs_tape)
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires pure (PW.state_interp (reveal initial) /\
    PW.runtime_matches_ctr (reveal initial) (reveal ot) (reveal c) (reveal len))
  returns auth:authority
  ensures active_world_interp auth (reveal initial) (reveal ot) (reveal c) (reveal len)
{
  let t = GFT.create #PW.state_view;
  let slot : nat = 0;
  GFT.alloc t (reveal initial) #slot;
  drop_ (GFT.is_table t (slot + 1));
  let auth = { world_table = t; world_slot = slot };
  assert_norm (auth.world_table == t);
  assert_norm (auth.world_slot == slot);
  rewrite (GFT.pts_to t slot #1.0R (reveal initial)) as
          (authority_state auth (reveal initial));
  fold (active_world_interp auth (reveal initial) (reveal ot) (reveal c) (reveal len));
  auth
}

ghost
fn alloc_current
    (auth:authority)
    (#st:erased PW.state_view)
    (#ot:erased NST.obs_tape)
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires active_world_interp auth (reveal st) (reveal ot) (reveal c) (reveal len)
  returns pid:erased PW.proph_id
  ensures (
    let pid0 = NST.prophecy_index (reveal c) in
    let st' = PW.alloc_view (reveal st) pid0 in
    active_world_interp auth st' (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len) **
    pure (reveal pid == pid0 /\
      PW.lookup pid0 st'.PW.world_token_map == Some (PW.list_resolves (reveal st).PW.world_decoder pid0 (reveal st).PW.world_future_trace)))
{
  unfold active_world_interp;
  unfold authority_state;
  PW.alloc_current_step (reveal st) (reveal ot) (reveal c) (reveal len);
  let pid0 = NST.prophecy_index (reveal c);
  let st' = PW.alloc_view (reveal st) (NST.prophecy_index (reveal c));
  GFT.update auth.world_table #auth.world_slot #(reveal st) st';
  fold (authority_state auth st');
  fold (active_world_interp auth st' (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len));
  rewrite (active_world_interp auth st' (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len)) as
          (active_world_interp auth (PW.alloc_view (reveal st) (NST.prophecy_index (reveal c)))
            (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len));
  hide pid0
}

ghost
fn active_world_si_alloc_current
    (auth:authority)
    (#ot:erased NST.obs_tape)
    (#c:erased NST.ctr)
  requires active_world_si auth (reveal ot) (reveal c)
  returns pid:erased PW.proph_id
  ensures active_world_si auth (reveal ot) (NST.bump_prophecy (reveal c)) **
    pure (reveal pid == NST.prophecy_index (reveal c))
{
  rewrite (active_world_si auth (reveal ot) (reveal c)) as
          (exists* (st:PW.state_view) (len:nat).
            active_world_interp auth st (reveal ot) (reveal c) len);
  with st len. assert (active_world_interp auth st (reveal ot) (reveal c) len);
  let pid = alloc_current auth #st #ot #c #len;
  let st' = PW.alloc_view st (NST.prophecy_index (reveal c));
  rewrite (active_world_interp auth (PW.alloc_view st (NST.prophecy_index (reveal c)))
            (reveal ot) (NST.bump_prophecy (reveal c)) len) as
          (active_world_interp auth st' (reveal ot) (NST.bump_prophecy (reveal c)) len);
  introduce exists* (st_out:PW.state_view) (len_out:nat).
    active_world_interp auth st_out (reveal ot) (NST.bump_prophecy (reveal c)) len_out with st' len;
  fold (active_world_si auth (reveal ot) (NST.bump_prophecy (reveal c)));
  pid
}

ghost
fn resolve_current
    (auth:authority)
    (#st:erased PW.state_view)
    (#ot:erased NST.obs_tape)
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (pid:PW.proph_id)
    (payload:nat)
    (#tail:erased PW.prediction_stream)
  requires active_world_interp auth (reveal st) (reveal ot) (reveal c) (reveal len) **
    pure (PW.current_observation_decodes_to (reveal st) (reveal ot) (reveal c) pid payload /\
      PW.lookup pid (reveal st).PW.world_token_map == Some (payload :: reveal tail))
  ensures (
    let ks = PW.trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let st' = PW.resolve_view (reveal st) pid (reveal tail) ks in
    active_world_interp auth st' (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1) **
    pure (PW.lookup pid st'.PW.world_token_map == Some (reveal tail)))
{
  unfold active_world_interp;
  unfold authority_state;
  PW.resolve_current_step (reveal st) (reveal ot) (reveal c) (reveal len) pid payload (reveal tail);
  let st' = PW.resolve_view (reveal st) pid (reveal tail)
    (PW.trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1));
  GFT.update auth.world_table #auth.world_slot #(reveal st) st';
  fold (authority_state auth st');
  fold (active_world_interp auth st' (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1));
  rewrite (active_world_interp auth st' (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1)) as
          (active_world_interp auth
            (PW.resolve_view (reveal st) pid (reveal tail)
              (PW.trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1)))
            (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1));
}

