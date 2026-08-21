(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Prophecy Variables for Pulse — Iris-style typed facade.

    This module exposes the typed client-facing wrapper around the trusted
    NewProph/Resolve boundary in [Pulse.Lib.AtomicPrimitives].  The trusted
    boundary is intentionally narrow and is shaped like Iris/HeapLang:

    * allocation consumes PulseCore's active prophecy-id cursor and returns a
      fresh prophecy id plus an existential client token fragment; the public
      token no longer owns the authoritative prophecy state, which is intended
      to live in the active semantics/adequacy state interpretation;
    * Resolve executes one observable atomic step and consumes the matching
      head observation in that same primitive step;
    * the equality between the physical result and the predicted head is
      obtained from the trusted trace coupling, not from a post-hoc ghost write.

    Pulse/F* does not have HeapLang's single untyped [val] universe.  The public
    representation is therefore typed per prophecy variable: a prophecy
    [prophecy_var result payload] observes atomic steps returning [result] and
    carrying attached payloads of type [payload].  The heterogeneous global
    observation list remains inside the trusted primitive boundary; the pure
    per-type projection model is in [Pulse.Lib.Prophecy.Trace], including the
    fresh-id discipline, the observation-index/runtime-cursor projection, and
    the remaining work to internalize the encoded witness as a first-class
    authoritative PulseCore state interpretation resource. *)
module Pulse.Lib.Prophecy
#lang-pulse

open Pulse.Lib.Pervasives
module AP = Pulse.Lib.AtomicPrimitives
module PT = Pulse.Lib.Prophecy.Trace
module NST = PulseCore.NondeterministicHoareStateMonad

let proph_id = PT.proph_id
let observation = PT.observation
let prediction_stream = PT.prediction_stream
let packed_observation = PT.packed_observation
let global_trace = PT.global_trace
let observation_decoder = PT.observation_decoder
let encoded_global_trace = PT.encoded_global_trace
let encoded_observation_decoder = PT.encoded_observation_decoder
let encoded_trace_of_tape = PT.encoded_trace_of_tape
let encoded_trace_of_tape_cons = PT.encoded_trace_of_tape_cons
let proph_map = PT.proph_map
let proph_list_resolves = PT.proph_list_resolves
let proph_list_resolves_global = PT.proph_list_resolves_global
let proph_list_resolves_encoded = PT.proph_list_resolves_encoded
let alloc_view = PT.alloc_view
let consume_prediction = PT.consume_prediction
let resolve_head = PT.resolve_head
let resolve_head_global = PT.resolve_head_global
let view_coupled = PT.view_coupled
let view_coupled_global = PT.view_coupled_global
let view_coupled_encoded = PT.view_coupled_encoded
let proph_map_interp = PT.proph_map_interp
let proph_map_interp_encoded = PT.proph_map_interp_encoded
let proph_map_contains = PT.proph_map_contains
let proph_map_lookup = PT.proph_map_lookup
let proph_map_update = PT.proph_map_update
let proph_map_fresh = PT.proph_map_fresh
let proph_map_unique = PT.proph_map_unique
let proph_map_update_fresh_noop = PT.proph_map_update_fresh_noop
let proph_map_contains_update = PT.proph_map_contains_update
let proph_map_lookup_alloc_same = PT.proph_map_lookup_alloc_same
let proph_map_lookup_alloc_other = PT.proph_map_lookup_alloc_other
let proph_map_lookup_update_same = PT.proph_map_lookup_update_same
let proph_map_lookup_update_other = PT.proph_map_lookup_update_other
let proph_map_lookup_some_contains = PT.proph_map_lookup_some_contains
let proph_map_lookup_update_same_from_lookup = PT.proph_map_lookup_update_same_from_lookup
let proph_map_update_preserves_unique = PT.proph_map_update_preserves_unique
let proph_map_bounded = PT.proph_map_bounded
let proph_map_bounded_fresh = PT.proph_map_bounded_fresh
let proph_map_bounded_monotone = PT.proph_map_bounded_monotone
let proph_map_update_preserves_bounded = PT.proph_map_update_preserves_bounded
let proph_map_alloc_fresh_preserves_bounded = PT.proph_map_alloc_fresh_preserves_bounded
let proph_map_alloc = PT.proph_map_alloc
let proph_map_alloc_lookup = PT.proph_map_alloc_lookup
let proph_map_alloc_encoded = PT.proph_map_alloc_encoded
let proph_map_alloc_encoded_lookup = PT.proph_map_alloc_encoded_lookup
let proph_map_alloc_preserves_interp = PT.proph_map_alloc_preserves_interp
let proph_map_alloc_encoded_preserves_interp = PT.proph_map_alloc_encoded_preserves_interp
let proph_map_alloc_preserves_unique = PT.proph_map_alloc_preserves_unique
let proph_map_alloc_encoded_preserves_unique = PT.proph_map_alloc_encoded_preserves_unique
let resolve_head_couples = PT.resolve_head_couples
let resolve_head_global_couples = PT.resolve_head_global_couples
let resolve_head_global_frames_other = PT.resolve_head_global_frames_other
let resolve_head_encoded = PT.resolve_head_encoded
let resolve_head_encoded_couples = PT.resolve_head_encoded_couples
let resolve_head_encoded_frames_other = PT.resolve_head_encoded_frames_other
let proph_map_resolve_preserves_interp = PT.proph_map_resolve_preserves_interp
let proph_map_resolve_encoded_frames_fresh = PT.proph_map_resolve_encoded_frames_fresh
let proph_map_resolve_encoded_preserves_interp = PT.proph_map_resolve_encoded_preserves_interp
let proph_state_view = PT.proph_state_view
let proph_state_view_encoded = PT.proph_state_view_encoded
let proph_state_interp = PT.proph_state_interp
let proph_state_alloc_view = PT.proph_state_alloc_view
let proph_state_alloc_fresh_view = PT.proph_state_alloc_fresh_view
let proph_state_resolve_view = PT.proph_state_resolve_view
let proph_state_alloc_view_lookup = PT.proph_state_alloc_view_lookup
let proph_state_alloc_fresh_view_lookup = PT.proph_state_alloc_fresh_view_lookup
let proph_state_resolve_view_lookup = PT.proph_state_resolve_view_lookup
let proph_state_next_fresh = PT.proph_state_next_fresh
let proph_state_interp_encoded = PT.proph_state_interp_encoded
let proph_state_alloc_view_encoded = PT.proph_state_alloc_view_encoded
let proph_state_alloc_fresh_view_encoded = PT.proph_state_alloc_fresh_view_encoded
let proph_state_resolve_view_encoded = PT.proph_state_resolve_view_encoded
let proph_state_future_matches_tape_encoded = PT.proph_state_future_matches_tape_encoded
let proph_state_resolve_advances_tape_encoded = PT.proph_state_resolve_advances_tape_encoded
let proph_state_runtime_matches_tape_encoded = PT.proph_state_runtime_matches_tape_encoded
let proph_state_runtime_matches_ctr_encoded = PT.proph_state_runtime_matches_ctr_encoded
let proph_state_alloc_runtime_preserves_tape_encoded = PT.proph_state_alloc_runtime_preserves_tape_encoded
let proph_state_alloc_fresh_runtime_preserves_tape_encoded = PT.proph_state_alloc_fresh_runtime_preserves_tape_encoded
let proph_state_alloc_fresh_runtime_advances_ctr_encoded = PT.proph_state_alloc_fresh_runtime_advances_ctr_encoded
let proph_state_resolve_observe_advances_tape_encoded = PT.proph_state_resolve_observe_advances_tape_encoded
let proph_state_resolve_observe_preserves_ctr_encoded = PT.proph_state_resolve_observe_preserves_ctr_encoded
let proph_map_observed_head_agrees_encoded = PT.proph_map_observed_head_agrees_encoded
let proph_map_lookup_projected_head_encoded = PT.proph_map_lookup_projected_head_encoded
let proph_state_observed_head_agrees_encoded = PT.proph_state_observed_head_agrees_encoded
let proph_state_lookup_projected_head_encoded = PT.proph_state_lookup_projected_head_encoded
let proph_state_lookup_projected_current_head_encoded = PT.proph_state_lookup_projected_current_head_encoded
let proph_state_observed_current_head_agrees_encoded = PT.proph_state_observed_current_head_agrees_encoded
let proph_state_resolve_observed_agree_preserves_interp = PT.proph_state_resolve_observed_agree_preserves_interp
let proph_state_resolve_observed_agree_preserves_ctr_encoded = PT.proph_state_resolve_observed_agree_preserves_ctr_encoded
let proph_state_alloc_view_encoded_lookup = PT.proph_state_alloc_view_encoded_lookup
let proph_state_alloc_fresh_view_encoded_lookup = PT.proph_state_alloc_fresh_view_encoded_lookup
let proph_state_alloc_view_encoded_lookup_other = PT.proph_state_alloc_view_encoded_lookup_other
let proph_state_alloc_fresh_view_encoded_lookup_other = PT.proph_state_alloc_fresh_view_encoded_lookup_other
let proph_state_alloc_fresh_view_encoded_preserves_lookup = PT.proph_state_alloc_fresh_view_encoded_preserves_lookup
let proph_state_resolve_view_encoded_lookup = PT.proph_state_resolve_view_encoded_lookup
let proph_state_resolve_view_encoded_lookup_other = PT.proph_state_resolve_view_encoded_lookup_other
let proph_state_resolve_view_encoded_preserves_lookup_other = PT.proph_state_resolve_view_encoded_preserves_lookup_other
let proph_state_next_fresh_encoded = PT.proph_state_next_fresh_encoded
let proph_state_alloc_preserves_interp = PT.proph_state_alloc_preserves_interp
let proph_state_alloc_fresh_preserves_interp = PT.proph_state_alloc_fresh_preserves_interp
let proph_state_resolve_preserves_interp = PT.proph_state_resolve_preserves_interp
let proph_state_alloc_encoded_preserves_interp = PT.proph_state_alloc_encoded_preserves_interp
let proph_state_alloc_fresh_encoded_preserves_interp = PT.proph_state_alloc_fresh_encoded_preserves_interp
let proph_state_resolve_encoded_preserves_interp = PT.proph_state_resolve_encoded_preserves_interp
let proph_state_resolve_observed_preserves_interp = PT.proph_state_resolve_observed_preserves_interp
let proph_state_alloc_fresh_authority_step_encoded = PT.proph_state_alloc_fresh_authority_step_encoded
let proph_state_alloc_fresh_authority_step_frames_lookup_encoded = PT.proph_state_alloc_fresh_authority_step_frames_lookup_encoded
let proph_state_resolve_authority_step_encoded = PT.proph_state_resolve_authority_step_encoded
let proph_state_resolve_authority_step_frames_lookup_encoded = PT.proph_state_resolve_authority_step_frames_lookup_encoded
let proph_state_alloc_fresh_authority_step_ctr_encoded = PT.proph_state_alloc_fresh_authority_step_ctr_encoded
let proph_state_resolve_authority_step_ctr_encoded = PT.proph_state_resolve_authority_step_ctr_encoded
let proph_state_resolve_authority_step_ctr_frames_lookup_encoded = PT.proph_state_resolve_authority_step_ctr_frames_lookup_encoded
let proph_state_alloc_fresh_repr_authority_step_encoded = PT.proph_state_alloc_fresh_repr_authority_step_encoded
let proph_state_alloc_fresh_repr_authority_step_frames_lookup_encoded = PT.proph_state_alloc_fresh_repr_authority_step_frames_lookup_encoded
let proph_state_alloc_fresh_repr_ctr_authority_step_encoded = PT.proph_state_alloc_fresh_repr_ctr_authority_step_encoded
let proph_state_alloc_fresh_repr_ctr_authority_step_frames_lookup_encoded = PT.proph_state_alloc_fresh_repr_ctr_authority_step_frames_lookup_encoded
let proph_state_alloc_fresh_repr_obs_ctr_authority_step_encoded = PT.proph_state_alloc_fresh_repr_obs_ctr_authority_step_encoded
let proph_state_alloc_fresh_repr_obs_ctr_authority_step_frames_lookup_encoded = PT.proph_state_alloc_fresh_repr_obs_ctr_authority_step_frames_lookup_encoded
let proph_state_resolve_observe_repr_authority_step_encoded = PT.proph_state_resolve_observe_repr_authority_step_encoded
let proph_state_resolve_observe_repr_authority_step_frames_lookup_encoded = PT.proph_state_resolve_observe_repr_authority_step_frames_lookup_encoded
let proph_state_resolve_observe_repr_current_authority_step_encoded = PT.proph_state_resolve_observe_repr_current_authority_step_encoded
let proph_state_resolve_observe_repr_current_authority_step_frames_lookup_encoded = PT.proph_state_resolve_observe_repr_current_authority_step_frames_lookup_encoded
let proph_state_resolve_observe_repr_ctr_current_authority_step_encoded = PT.proph_state_resolve_observe_repr_ctr_current_authority_step_encoded
let proph_state_resolve_observe_repr_ctr_current_authority_step_frames_lookup_encoded = PT.proph_state_resolve_observe_repr_ctr_current_authority_step_frames_lookup_encoded
let proph_state_resolve_observe_repr_obs_ctr_current_authority_step_encoded = PT.proph_state_resolve_observe_repr_obs_ctr_current_authority_step_encoded
let proph_state_resolve_observe_repr_obs_ctr_current_authority_step_frames_lookup_encoded = PT.proph_state_resolve_observe_repr_obs_ctr_current_authority_step_frames_lookup_encoded

(** Opaque typed prophecy variable handle. *)
type prophecy_var (result payload:Type0) = AP.prophecy_var result payload

(** [prophecy_token p pvs] is the linear client token for [p]: the public
    prediction slot plus the public half of the active token/world agreement.
    It no longer owns the authoritative prophecy-state runtime resource; that state is
    exposed separately through the active-component helpers for future adequacy
    plumbing.  Clients can only obtain it from [prophecy_alloc] and update it
    with [resolve] or [resolve_token]. *)
[@@pulse_unfold]
let prophecy_token (#result #payload:Type0)
    (p:prophecy_var result payload)
    (pvs:prediction_stream result payload)
  : slprop
= AP.prophecy_token p pvs

(** First-class shared-authority resource slice for future adequacy plumbing.
    [prophecy_authority_state] owns the authoritative encoded prophecy-state
    view, [prophecy_authority_runtime_state] additionally ties it to
    [NST.prophecy_index], [NST.observation_index], and the observation-tape
    suffix, while [prophecy_token_fragment] owns an individual token slot.  The
    allocation/Resolve helpers below are verified resource updates over that
    shared authority.  The active [prophecy_alloc] facade no longer returns that
    authority inside the token; [resolve] now derives the singleton erased
    lookup by gathering the public token's first-class agreement half at its
    deterministic projection-table slot with the active registry half and then
    using the projection invariant.  The former direct active-registry
    membership premise has been removed; the remaining trusted seam is the
    hidden consumed-nat decoder fact until Resolve is rewired to a first-class
    adequacy-owned active world. *)
type prophecy_authority (result payload:Type0) = AP.prophecy_authority result payload

let prophecy_id_of (#result #payload:Type0)
    (p:prophecy_var result payload)
  : GTot proph_id
= AP.prophecy_id_of p

let prophecy_bound_to_authority (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
  : GTot prop
= AP.prophecy_bound_to_authority auth p

[@@pulse_unfold]
let prophecy_authority_state (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:proph_state_view_encoded result payload)
  : slprop
= AP.prophecy_authority_state auth st

[@@pulse_unfold]
let prophecy_authority_runtime_state (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : slprop
= AP.prophecy_authority_runtime_state auth st ot c len

[@@pulse_unfold]
let prophecy_token_fragment (#result #payload:Type0)
    (p:prophecy_var result payload)
    (pvs:prediction_stream result payload)
  : slprop
= AP.prophecy_token_fragment p pvs

[@@pulse_unfold]
let prophecy_shared_state_interp (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : slprop
= AP.prophecy_shared_state_interp auth st ot c len

(** First-class package for the single adequacy-owned prophecy component.  The
    component-level wrappers below preserve the package across NewProph/Resolve
    updates, so the eventual active state interpretation can thread one value
    instead of reconstructing the authority/state/length triple after each
    step. *)
type prophecy_active_component (result payload:Type0) = AP.prophecy_active_component result payload

[@@pulse_unfold]
let prophecy_active_component_interp (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : slprop
= AP.prophecy_active_component_interp comp ot c

let prophecy_component_bound (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (p:prophecy_var result payload)
  : GTot prop
= AP.prophecy_component_bound comp p

let prophecy_component_lookup (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (p:prophecy_var result payload)
    (pvs:prediction_stream result payload)
  : GTot prop
= AP.prophecy_component_lookup comp p pvs

let prophecy_active_component_after_alloc (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
  : GTot (prophecy_active_component result payload)
= AP.prophecy_active_component_after_alloc comp

let prophecy_active_component_after_resolve (#result #payload:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : GTot (prophecy_active_component result payload)
= AP.prophecy_active_component_after_resolve comp p tail ot c

ghost
fn prophecy_active_component_init (#result #payload:Type0)
    (#initial:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires pure (proph_state_interp_encoded (reveal initial) /\
    proph_state_runtime_matches_ctr_encoded (reveal initial) (reveal ot) (reveal c) (reveal len))
  returns comp:prophecy_active_component result payload
  ensures prophecy_active_component_interp comp (reveal ot) (reveal c) **
    pure (comp.component_state_view == reveal initial /\ comp.component_len == reveal len)
{
  AP.prophecy_active_component_init #result #payload #initial #ot #c #len
}

ghost
fn prophecy_authority_init (#result #payload:Type0)
    (#initial:erased (proph_state_view_encoded result payload))
  requires pure (proph_state_interp_encoded (reveal initial))
  returns auth:prophecy_authority result payload
  ensures prophecy_authority_state auth (reveal initial)
{
  AP.prophecy_authority_init #result #payload #initial
}

ghost
fn prophecy_authority_alloc (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (proph_state_view_encoded result payload))
  requires prophecy_authority_state auth (reveal old_st)
  returns p:prophecy_var result payload
  ensures (
    let pid = (reveal old_st).encoded_next_proph_id in
    let pvs = proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_authority_state auth new_st **
    prophecy_token_fragment p pvs **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  AP.prophecy_authority_alloc #result #payload auth #old_st
}

ghost
fn prophecy_authority_alloc_runtime (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len)
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len) **
    prophecy_token_fragment p pvs **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  AP.prophecy_authority_alloc_runtime #result #payload auth #old_st #ot #c #len
}

ghost
fn prophecy_shared_state_interp_alloc (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len)
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_shared_state_interp auth new_st (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len) **
    prophecy_token_fragment p pvs **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  AP.prophecy_shared_state_interp_alloc #result #payload auth #old_st #ot #c #len
}

ghost
fn prophecy_shared_state_interp_alloc_obs_ctr_repr (#result #payload:Type0) (#s:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  requires prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len)
  returns p:prophecy_var result payload
  ensures (
    let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_shared_state_interp auth new_st (reveal ot) r._3 (reveal len) **
    prophecy_token_fragment p pvs **
    pure (r._1 == pid /\ r._2 == s0 /\ r._3 == NST.bump_prophecy (reveal c) /\
      prophecy_id_of p == pid /\ prophecy_bound_to_authority auth p /\
      proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  AP.prophecy_shared_state_interp_alloc_obs_ctr_repr #result #payload #s auth #old_st #ot #c #len s0 t at
}

ghost
fn prophecy_active_component_alloc_obs_ctr_component (#result #payload:Type0) (#s:Type0)
    (comp:prophecy_active_component result payload)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c)
  returns p:prophecy_var result payload
  ensures (
    let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) r._3 **
    prophecy_token_fragment p pvs **
    pure (r._1 == pid /\ r._2 == s0 /\ r._3 == NST.bump_prophecy (reveal c) /\
      comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs))
{
  AP.prophecy_active_component_alloc_obs_ctr_component #result #payload #s comp #ot #c s0 t at
}

ghost
fn prophecy_active_component_alloc_obs_ctr_component_frame (#result #payload:Type0) (#s:Type0)
    (comp:prophecy_active_component result payload)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (framed:prophecy_var result payload)
    (#framed_pvs:erased (prediction_stream result payload))
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (prophecy_component_bound comp framed /\
      prophecy_id_of framed <> NST.prophecy_index (reveal c) /\
      prophecy_component_lookup comp framed (reveal framed_pvs))
  returns p:prophecy_var result payload
  ensures (
    let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) r._3 **
    prophecy_token_fragment p pvs **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (r._1 == pid /\ r._2 == s0 /\ r._3 == NST.bump_prophecy (reveal c) /\
      comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs /\
      prophecy_component_bound comp' framed /\
      prophecy_component_lookup comp' framed (reveal framed_pvs)))
{
  AP.prophecy_active_component_alloc_obs_ctr_component_frame #result #payload #s comp #ot #c framed #framed_pvs s0 t at
}

fn prophecy_active_component_alloc_current_component (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (pid:proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    pure (pid == NST.prophecy_index (reveal c))
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) (NST.bump_prophecy (reveal c)) **
    prophecy_token_fragment p pvs **
    pure (comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs))
{
  AP.prophecy_active_component_alloc_current_component #result #payload comp pid #ot #c
}

ghost
fn prophecy_active_component_alloc_current_component_frame (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (pid:proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (framed:prophecy_var result payload)
    (#framed_pvs:erased (prediction_stream result payload))
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (pid == NST.prophecy_index (reveal c) /\
      prophecy_component_bound comp framed /\
      prophecy_id_of framed <> pid /\
      prophecy_component_lookup comp framed (reveal framed_pvs))
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) (NST.bump_prophecy (reveal c)) **
    prophecy_token_fragment p pvs **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs /\
      prophecy_component_bound comp' framed /\
      prophecy_component_lookup comp' framed (reveal framed_pvs)))
{
  AP.prophecy_active_component_alloc_current_component_frame #result #payload comp pid #ot #c framed #framed_pvs
}

ghost
fn prophecy_authority_alloc_runtime_frame (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
    (framed:prophecy_var result payload)
    (#framed_pvs:erased (prediction_stream result payload))
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (prophecy_bound_to_authority auth framed /\
      prophecy_id_of framed <> NST.prophecy_index (reveal c) /\
      proph_map_lookup (prophecy_id_of framed) (reveal old_st).encoded_token_map == Some (reveal framed_pvs))
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len) **
    prophecy_token_fragment p pvs **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      proph_map_lookup pid new_st.encoded_token_map == Some pvs /\
      proph_map_lookup (prophecy_id_of framed) new_st.encoded_token_map == Some (reveal framed_pvs)))
{
  AP.prophecy_authority_alloc_runtime_frame #result #payload auth #old_st #ot #c #len framed #framed_pvs
}

ghost
fn prophecy_authority_resolve_observed (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#pvs:erased (prediction_stream result payload))
    (observed_result:result)
    (observed_nat:nat)
    (#tail:erased (prediction_stream result payload))
    (#ks:erased encoded_global_trace)
  requires prophecy_authority_state auth (reveal old_st) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_future_trace == observed_nat :: reveal ks /\
      (reveal old_st).encoded_decoder observed_nat ==
        Some (prophecy_id_of p, (observed_result, payload_value)) /\
      reveal pvs == (observed_result, payload_value) :: reveal tail)
  returns u:unit
  ensures (
    let new_st = proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) (reveal ks) in
    prophecy_authority_state auth new_st **
    prophecy_token_fragment p (reveal tail) **
    pure (proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  AP.prophecy_authority_resolve_observed #result #payload auth p payload_value #old_st #pvs observed_result observed_nat #tail #ks
}

ghost
fn prophecy_authority_resolve_observed_runtime (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (prediction_stream result payload))
    (observed_result:result)
    (observed_nat:nat)
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      observed_nat == reveal ot (NST.observation_index (reveal c)) /\
      proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder observed_nat ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (prediction_stream result payload)
  ensures (
    let ks = encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (reveal pvs == (observed_result, payload_value) :: reveal tail /\
      proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  AP.prophecy_authority_resolve_observed_runtime #result #payload auth p payload_value #old_st #ot #c #len #pvs observed_result observed_nat
}

ghost
fn prophecy_authority_resolve_current (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (prediction_stream result payload))
    (observed_result:result)
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (prediction_stream result payload)
  ensures (
    let ks = encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (reveal pvs == (observed_result, payload_value) :: reveal tail /\
      proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  AP.prophecy_authority_resolve_current #result #payload auth p payload_value #old_st #ot #c #len #pvs observed_result
}

ghost
fn prophecy_shared_state_interp_resolve_current (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (prediction_stream result payload))
    (observed_result:result)
  requires prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (prediction_stream result payload)
  ensures (
    let ks = encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_shared_state_interp auth new_st (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (reveal pvs == (observed_result, payload_value) :: reveal tail /\
      proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  AP.prophecy_shared_state_interp_resolve_current #result #payload auth p payload_value #old_st #ot #c #len #pvs observed_result
}

ghost
fn prophecy_active_component_resolve_current_component (#result #payload:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (prediction_stream result payload))
    (observed_result:result)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment p (reveal pvs) **
    pure (comp.component_len > 0 /\ prophecy_component_bound comp p /\
      prophecy_component_lookup comp p (reveal pvs) /\
      comp.component_state_view.encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (prediction_stream result payload)
  ensures (
    let len_pos : (n:nat { n > 0 }) = comp.component_len in
    let comp' = prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c) in
    prophecy_active_component_interp comp' (reveal ot) (NST.bump_observation (reveal c)) **
    prophecy_token_fragment p (reveal tail) **
    pure (comp'.component_authority == comp.component_authority /\
      comp'.component_len == len_pos - 1 /\
      comp'.component_state_view.encoded_decoder == comp.component_state_view.encoded_decoder /\
      reveal pvs == (observed_result, payload_value) :: reveal tail /\
      prophecy_component_lookup comp' p (reveal tail)))
{
  AP.prophecy_active_component_resolve_current_component #result #payload comp p payload_value #pvs observed_result #ot #c
}

ghost
fn prophecy_active_component_resolve_obs_ctr_component (#result #payload:Type0) (#s:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (prediction_stream result payload))
    (observed_result:result)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment p (reveal pvs) **
    pure (comp.component_len > 0 /\ prophecy_component_bound comp p /\
      prophecy_component_lookup comp p (reveal pvs) /\
      comp.component_state_view.encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (prediction_stream result payload)
  ensures (
    let len_pos : (n:nat { n > 0 }) = comp.component_len in
    let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    let comp' = prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c) in
    prophecy_active_component_interp comp' (reveal ot) r._3 **
    prophecy_token_fragment p (reveal tail) **
    pure (r._1 == reveal ot (NST.observation_index (reveal c)) /\ r._2 == s0 /\
      r._3 == NST.bump_observation (reveal c) /\
      comp'.component_authority == comp.component_authority /\
      comp'.component_len == len_pos - 1 /\
      comp'.component_state_view.encoded_decoder == comp.component_state_view.encoded_decoder /\
      reveal pvs == (observed_result, payload_value) :: reveal tail /\
      prophecy_component_lookup comp' p (reveal tail)))
{
  AP.prophecy_active_component_resolve_obs_ctr_component #result #payload #s comp p payload_value #pvs observed_result s0 t at #ot #c
}

ghost
fn prophecy_shared_state_interp_resolve_obs_ctr_repr (#result #payload:Type0) (#s:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (prediction_stream result payload))
    (observed_result:result)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  requires prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (prediction_stream result payload)
  ensures (
    let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    let ks = encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_shared_state_interp auth new_st (reveal ot) r._3 (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (r._1 == reveal ot (NST.observation_index (reveal c)) /\ r._2 == s0 /\
      r._3 == NST.bump_observation (reveal c) /\
      reveal pvs == (observed_result, payload_value) :: reveal tail /\
      proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  AP.prophecy_shared_state_interp_resolve_obs_ctr_repr #result #payload #s auth p payload_value #old_st #ot #c #len #pvs observed_result s0 t at
}

(** Allocate a prophecy id through the active hidden-state NewProph path.

    This path consumes PulseCore's hidden-state prophecy-id cursor.  The
    allocation callback now opens the coherent hidden state used by
    [AP.new_proph_semantic]: a concrete untyped
    [Pulse.Lib.ProphecyWorldResource.active_world_interp] plus typed projection
    metadata at the same erased active observation tape/counter, related by
    decoder-domain, future-trace, token-key, erased stream
    projection/reflection, counter, and length coherence.  It allocates at
    [NST.prophecy_index], closes the singleton at [NST.bump_prophecy], and
    allocates a client token slot projected from the active future trace rather
    than a locally initialized empty stream.  The remaining NewProph-side gap is
    giving all instantiated runners non-vacuous support for the hidden-state
    constructor. *)
fn prophecy_alloc (#result #payload:Type0) ()
  requires emp
  returns p : prophecy_var result payload
  ensures exists* (pvs:prediction_stream result payload). prophecy_token p pvs
{
  AP.new_proph_semantic #result #payload ()
}

(** Resolve a prophecy around one observable atomic step.

    The precondition requires the caller's token to expose a head prediction
    [(pred, payload_value)].  Resolve performs [f] through the semantic
    hidden-state observed-result bridge, consumes one observation-tape entry in
    that same semantic step, opens the hidden active component, and updates the
    linear token fragment using the checked active Resolve helper.  The
    remaining core gap is wiring the p-specific hidden decoder facts to the
    singleton adequacy-owned state interpretation directly. *)
fn resolve (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pred:erased result)
    (#tail:erased (prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  requires prophecy_token p ((reveal pred, payload_value) :: reveal tail) ** pre
  returns x : result
  ensures post x ** prophecy_token p (reveal tail) ** pure (x == reveal pred)
{
  AP.resolve_proph_semantic #result #payload p payload_value #pred #tail #pre #post f
}

(** Resolve in the Iris-rule form used after allocation.

    The caller owns the whole current prediction stream [pvs] obtained from
    [prophecy_alloc].  The hidden-state observed-result bridge runs the physical
    step, consumes an observation, and supplies the active component/current
    decoder facts to the checked Resolve helper.  The map interpretation then
    establishes, without any executable case split on that erased stream, that
    [pvs]'s head was the observed result paired with [payload_value].  The
    concrete tail-token and encoded-state transition are verified in the
    primitive model. *)
fn resolve_token (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  requires prophecy_token p (reveal pvs) ** pre
  returns x : result
  ensures post x **
    (exists* (tail:prediction_stream result payload).
      prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail))
{
  AP.resolve_proph_token_semantic #result #payload p payload_value #pvs #pre #post f
}

(** Atomic-shaped Resolve-token rule for clients that must resolve while an
    invariant is open.  This exposes the same Iris-rule postcondition through
    the client-facing [Pulse.Lib.Prophecy] facade instead of requiring examples
    to depend directly on [Pulse.Lib.AtomicPrimitives]' prophecy internals.  Its
    implementation still factors through the trusted primitive-boundary
    observed-result atomic rule, so this does not hide the remaining
    singleton-runtime-authority/current-decode adequacy work. *)
let resolve_token_atomic (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : stt_atomic result #Observable emp_inames
      (prophecy_token p (reveal pvs) ** pre)
      (fun x -> post x **
        (exists* (tail:prediction_stream result payload).
          prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail)))
= AP.resolve_proph_token #result #payload p payload_value #pvs #pre #post f

(** Head-supplied atomic-shaped Resolve rule.  This is the open-invariant
    counterpart of [resolve]: callers that already decomposed the prediction
    stream get the equality between the physical result and the predicted head
    in an atomic postcondition. *)
let resolve_atomic (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pred:erased result)
    (#tail:erased (prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : stt_atomic result #Observable emp_inames
      (prophecy_token p ((reveal pred, payload_value) :: reveal tail) ** pre)
      (fun x -> post x ** prophecy_token p (reveal tail) ** pure (x == reveal pred))
= AP.resolve_proph #result #payload p payload_value #pred #tail #pre #post f
