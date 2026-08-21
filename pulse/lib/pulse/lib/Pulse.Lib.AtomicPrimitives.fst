(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Atomic Primitives — model implementation.

    This file provides a SEQUENTIAL MODEL of atomic operations using
    as_atomic. It is used only for F* type-checking.
    On real hardware, these operations are implemented by atomic
    machine instructions (LOCK CMPXCHG, LOCK XADD, etc.).

    The trusted interface is in .fsti — clients depend on those
    opaque specs, not on this implementation. *)
module Pulse.Lib.AtomicPrimitives
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U = Pulse.Lib.Raise
module U32 = FStar.UInt32
module C = Pulse.Lib.Core
module A = PulseCore.Action
module GFT = Pulse.Lib.GhostFractionalTable
module PT = Pulse.Lib.Prophecy.Trace
module PWR = Pulse.Lib.ProphecyWorldResource
module PW = PulseCore.ProphecyWorld
module NST = PulseCore.NondeterministicHoareStateMonad

(* ================================================================ *)
(* Load — atomic read from a box                                    *)
(* HeapLang: !l                                                     *)
(* ================================================================ *)

fn atomic_read_impl (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  preserves r |-> Frac p v
  returns x : a
  ensures rewrites_to x (reveal v)
{ B.op_Bang r }

let atomic_read (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_atomic a #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_read_impl r #v #p)

(* ================================================================ *)
(* Store — atomic write to a box                                    *)
(* HeapLang: l <- v                                                 *)
(* ================================================================ *)

fn atomic_write_impl (#a:Type0) (r : B.box a) (x : a) (#v : erased a)
  requires r |-> v
  ensures r |-> x
{ B.op_Colon_Equals r x }

let atomic_write (#a:Type0) (r : B.box a) (x : a) (#v : erased a)
  : stt_atomic unit #Observable emp_inames
    (B.pts_to r v) (fun _ -> B.pts_to r x)
  = Pulse.Lib.Core.as_atomic _ _ (atomic_write_impl r x #v)

(* ================================================================ *)
(* Alloc — atomic allocation of a box                               *)
(* HeapLang: ref v                                                  *)
(* ================================================================ *)

fn atomic_alloc_impl (#a:Type0) (x : a)
  requires emp
  returns r : B.box a
  ensures r |-> x
{ B.alloc x }

let atomic_alloc (#a:Type0) (x : a)
  : stt_atomic (B.box a) #Observable emp_inames
    emp (fun r -> B.pts_to r x)
  = Pulse.Lib.Core.as_atomic _ _ (atomic_alloc_impl x)

(* ================================================================ *)
(* CAS — compare-and-swap (eqtype, model implementation)            *)
(* ================================================================ *)

fn atomic_cas_impl (#a:eqtype) (r : B.box a) (expected new_val : a) (#cur : erased a)
  requires r |-> cur
  returns b : bool
  ensures cond b (r |-> new_val ** pure (reveal cur == expected))
                 (r |-> cur)
{
  let v = B.op_Bang r;
  if (v = expected) {
    B.op_Colon_Equals r new_val;
    fold (cond true (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    true
  } else {
    fold (cond false (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    false
  }
}

let atomic_cas (#a:eqtype) (r : B.box a) (expected new_val : a) (#cur : erased a)
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_cas_impl r expected new_val #cur)

(* ================================================================ *)
(* CAS — pointer equality variant (box_eq)                          *)
(* ================================================================ *)

fn atomic_cas_box_impl (#a:Type0) (r : B.box (B.box a))
    (expected new_val : B.box a) (#cur : erased (B.box a))
  requires r |-> cur
  returns b : bool
  ensures cond b (r |-> new_val ** pure (reveal cur == expected))
                 (r |-> cur)
{
  let v = B.op_Bang r;
  if (B.box_eq v expected) {
    B.op_Colon_Equals r new_val;
    fold (cond true (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    true
  } else {
    fold (cond false (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    false
  }
}

let atomic_cas_box (#a:Type0) (r : B.box (B.box a))
    (expected new_val : B.box a) (#cur : erased (B.box a))
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_cas_box_impl r expected new_val #cur)

(* ================================================================ *)
(* FAA — fetch-and-add on a box U32.t                               *)
(* HeapLang: FAA l delta                                            *)
(* ================================================================ *)

fn atomic_faa_impl (r : B.box U32.t) (delta : U32.t) (#cur : erased U32.t)
  requires r |-> cur
  returns old : U32.t
  ensures r |-> U32.add_mod old delta ** pure (old == reveal cur)
{
  let old = B.op_Bang r;
  B.op_Colon_Equals r (U32.add_mod old delta);
  old
}

let atomic_faa (r : B.box U32.t) (delta : U32.t) (#cur : erased U32.t)
  : stt_atomic U32.t #Observable emp_inames
    (B.pts_to r cur) (fun old -> B.pts_to r (U32.add_mod old delta) ** pure (old == reveal cur))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_faa_impl r delta #cur)

(* ================================================================ *)
(* Prophecy variables — model placeholder for trusted boundary      *)
(* ================================================================ *)

(** The interface treats prophecy variables as typed, opaque handles and keeps
    [prophecy_token] opaque.  The model body below is intentionally confined to
    the same trusted atomic primitive boundary as [as_atomic]: it stands for
    HeapLang NewProph/Resolve plus the adequacy-level global observation trace
    and proph_map_interp shape described in Pulse.Lib.Prophecy.Trace.

    The public token model is now deliberately only a client entry fragment in
    a ghost fractional table for the current prediction stream.  The
    authoritative nat-encoded prophecy state is represented by the explicit
    shared-authority/active-component slice below and must be owned by active
    semantics/adequacy, not by each public token.

    PulseCore now threads a dedicated observation oracle and has
    [ObservedAct]/[ObservedResultAct] nodes plus active hidden-state action
    support that consumes one observation and runs one action in the same
    semantic step.  The pure prophecy state view is also
    tied to [NST.observation_index]/[NST.bump_observation] by verified
    projection lemmas, and
    [PT.proph_state_resolve_observed_agree_preserves_interp] derives Resolve's
    result/prediction equality from the authoritative map/trace interpretation.
    The Resolve-token model below now uses the two-stage target-fixed
    [C.lift_targeted_post_result_observed_result_hidden_state_action], so the wrapped physical
    action, the post-result Resolve receipt, the observation-tape read, the public token pop, and the
    [PWR.resolve_current] update are semantically coupled inside the active
    observed-result action.  After the ownership split, public [prophecy_token]
    owns only an individual token fragment; it no longer carries
    [prophecy_shared_state_interp] or any equivalent authoritative runtime
    state.  NewProph therefore no longer has a runner-owned emp-to-authority
    projection helper.  This is only a NewProph ownership patch, not final Iris
    faithfulness: Resolve now opens a hidden active component through the
    active observed-result semantic rule and uses the checked active helper to
    derive the token-tail shape.  The hidden precondition no longer supplies
    the consumed-nat/current-cursor equality, the legacy component-bound fact, a
    typed projection-registry lookup, or a p-specific token/world stream
    agreement.  The consumed-nat equality is exposed by the active
    Ret-specialized [ObservedResultActWithHiddenStateReturnAction] callback; the
    previous stateful event witness has been deleted.  The remaining
    result-dependent event
    refinement is now a private active observed-result receipt threaded from the
    callback after the physical action returns [x] into the checked finisher.
    The finisher opens the token-indexed active singleton view, exposes its
    world/projection/checked projection-table binding, eliminates that receipt
    to the consumed-nat decoder fact, and then derives the current-cursor
    [PW.current_observation_decodes_to] fact by a checked lemma using the
    callback's consumed-nat equality.  Thus the
    authoritative world ownership stays in the active singleton predicate and
    there is no separate spatial
    observed-event-pre predicate.  The open-invariant Resolve path remains a
    temporary trusted
    [stt_atomic] presentation shim, but public Resolve now uses the two-stage target-fixed specialized core
    [lift_atomic_targeted_post_result_observed_result_hidden_state_action_atomic] rule for this
    active observed-result hidden-state action rather than a Resolve-local
    arbitrary local atomic coercion.  The public NewProph path is now
    [new_proph_semantic]: it consumes the
    active [Pulse.Lib.Core.fresh_prophecy_id_with_hidden_si_state_action]
    state-action cursor and runs allocation under the coherent hidden
    [active_prophecy_world_si] at the
    same erased [ot,c] with [pid == NST.prophecy_index c].  That hidden state
    opens the concrete untyped [Pulse.Lib.ProphecyWorldResource.active_world_interp]
    plus typed projection metadata at the same counter, tied by a pure relation
    covering decoder projection/reflection, future trace, token-map keys,
    value-level erased token-map streams, finite stream reflection, counters,
    and length.  The active path no longer owns
    [prophecy_active_component_interp] as a sibling authority: NewProph creates
    the public token slot directly from the singleton-derived typed stream, and
    Resolve derives the typed head/tail from the singleton projection before
    updating only that token slot, the token's agreement cell, and
    [PWR.active_world_interp].  The remaining Iris-faithfulness gaps are
    therefore: first, prove every public NewProph/Resolve adequacy path routes
    through the non-diverging active runners rather than the conservative
    counter-erased branches; second, replace the narrow Resolve event/decode
    boundary and specialized observed-result presentation shim with first-class
    PulseCore result-dependent active observed-result atomic support.  The
    head-supplied Resolve wrapper below now receives a target-fixed native event
    receipt; the remaining decoder bridge is still the private active-world-owned
    boundary below.  The legacy atomic-shaped Resolve reuses the same semantic
    hidden-state Resolve rule and the primitive kernel's specialized
    active-observed-result presentation boundary only for the open-invariant
    [stt_atomic] presentation. *)
[@@erasable]
noeq type prophecy_var (result payload:Type0) = {
  proph_id_refinement : PT.proph_id;
  proph_payload_pack : result -> payload -> nat;
  token_table : GFT.table (PT.prediction_stream result payload);
  token_slot : nat;
  agreement_table : GFT.table (PT.prediction_stream result payload);
  agreement_slot : nat;
  state_table : GFT.table (PT.proph_state_view_encoded result payload);
  state_slot : nat;
}

instance non_informative_prophecy_var (#result #payload:Type0)
  : NonInformative.non_informative (prophecy_var result payload) = {
  reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (prophecy_var result payload);
}

[@@erasable]
noeq type prophecy_authority (result payload:Type0) = {
  authority_table : GFT.table (PT.proph_state_view_encoded result payload);
  authority_slot : nat;
}

let prophecy_id_of (#result #payload:Type0)
    (p:prophecy_var result payload)
  : GTot PT.proph_id
= p.proph_id_refinement

let prophecy_bound_to_authority (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
  : GTot prop
= p.state_table == auth.authority_table /\ p.state_slot == auth.authority_slot

let prophecy_authority_of (#result #payload:Type0)
    (p:prophecy_var result payload)
  : GTot (prophecy_authority result payload)
= { authority_table = p.state_table; authority_slot = p.state_slot }

[@@pulse_unfold]
let prophecy_authority_state (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:PT.proph_state_view_encoded result payload)
  : slprop
= GFT.pts_to auth.authority_table auth.authority_slot #1.0R st **
  pure (PT.proph_state_interp_encoded st)

[@@pulse_unfold]
let prophecy_token_fragment (#result #payload:Type0)
    (p:prophecy_var result payload)
    (pvs:PT.prediction_stream result payload)
  : slprop
= GFT.pts_to p.token_table p.token_slot #1.0R pvs

noeq type prophecy_token_cell (result payload:Type0) = {
  agreement_cell_table : GFT.table (PT.prediction_stream result payload);
  agreement_cell_slot : nat;
}

let prophecy_token_cell_of (#result #payload:Type0)
    (p:prophecy_var result payload)
  : GTot (prophecy_token_cell result payload)
= { agreement_cell_table = p.agreement_table;
    agreement_cell_slot = p.agreement_slot }

let prophecy_token_cell_matches (#result #payload:Type0)
    (cell:prophecy_token_cell result payload)
    (p:prophecy_var result payload)
  : GTot prop
= cell.agreement_cell_table == p.agreement_table /\
  cell.agreement_cell_slot == p.agreement_slot

[@@pulse_unfold]
let prophecy_token_cell_fragment (#result #payload:Type0)
    (cell:prophecy_token_cell result payload)
    (pvs:PT.prediction_stream result payload)
  : slprop
= GFT.pts_to cell.agreement_cell_table cell.agreement_cell_slot #0.5R pvs

[@@pulse_unfold]
let prophecy_token_agreement (#result #payload:Type0)
    (p:prophecy_var result payload)
    (pvs:PT.prediction_stream result payload)
  : slprop
= prophecy_token_cell_fragment (prophecy_token_cell_of p) pvs **
  pure (p.agreement_slot == prophecy_id_of p)

(** First-class shared prophecy state-interpretation slice for one typed
    prophecy interface.  This is the resource that the active PulseCore
    adequacy/state interpretation must eventually own globally: a singleton
    authoritative prophecy map, tied to one observation tape and the current
    [NST.ctr].  The current resource-level helper keeps the concrete encoded
    state explicit so proofs can apply the checked Trace lemmas; the eventual
    PulseCore adequacy owner may existentially hide that field while preserving
    the same open/update/close rule.  NewProph/Resolve open it, update the
    authority, and close it at [NST.bump_prophecy] / [NST.bump_observation].

    This resource is intentionally no longer packed inside the opaque public
    token below.  The definitions and verified wrappers make the intended
    [proph_map_interp]-style ownership explicit for the active
    semantics/adequacy layer, while [prophecy_token] carries the client token
    slot plus the public half of the active token/world agreement cell.  Public
    NewProph has been reduced to fresh-id allocation plus a token/agreement
    return; the final foundational edit must connect that primitive to the
    hidden [active_prophecy_si] update in instantiated adequacy. *)
[@@pulse_unfold]
let prophecy_shared_state_interp (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:PT.proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : slprop
= prophecy_authority_runtime_state auth st ot c len

[@@pulse_unfold]
let prophecy_token (#result #payload:Type0)
    (p:prophecy_var result payload)
    (pvs:PT.prediction_stream result payload)
  : slprop
= prophecy_token_fragment p pvs ** prophecy_token_agreement p pvs

ghost
fn prophecy_authority_init (#result #payload:Type0)
    (#initial:erased (PT.proph_state_view_encoded result payload))
  requires pure (PT.proph_state_interp_encoded (reveal initial))
  returns auth:prophecy_authority result payload
  ensures prophecy_authority_state auth (reveal initial)
{
  let st_table = GFT.create #(PT.proph_state_view_encoded result payload);
  let slot : nat = 0;
  GFT.alloc st_table (reveal initial) #slot;
  drop_ (GFT.is_table st_table (slot + 1));
  let auth = { authority_table = st_table; authority_slot = slot };
  assert_norm (auth.authority_table == st_table);
  assert_norm (auth.authority_slot == slot);
  rewrite (GFT.pts_to st_table slot #1.0R (reveal initial)) as
          (GFT.pts_to auth.authority_table auth.authority_slot #1.0R (reveal initial));
  fold (prophecy_authority_state auth (reveal initial));
  auth
}

ghost
fn prophecy_authority_alloc (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
  requires prophecy_authority_state auth (reveal old_st)
  returns p:prophecy_var result payload
  ensures (
    let pid = (reveal old_st).encoded_next_proph_id in
    let pvs = PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_authority_state auth new_st **
    prophecy_token_fragment p pvs **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  unfold prophecy_authority_state;
  assert (GFT.pts_to auth.authority_table auth.authority_slot #1.0R (reveal old_st) **
          pure (PT.proph_state_interp_encoded (reveal old_st)));
  let pid = (reveal old_st).encoded_next_proph_id;
  let pvs = PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace;
  let new_st = snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st));
  PT.proph_state_alloc_fresh_authority_step_encoded (reveal old_st);
  let t = GFT.create #(PT.prediction_stream result payload);
  let slot : nat = 0;
  GFT.alloc t pvs #slot;
  drop_ (GFT.is_table t (slot + 1));
  GFT.update auth.authority_table #auth.authority_slot #(reveal old_st) new_st;
  let p = { proph_id_refinement = pid;
            proph_payload_pack = (fun (_:result) (_:payload) -> 0);
            token_table = t; token_slot = slot;
            agreement_table = t; agreement_slot = slot;
            state_table = auth.authority_table; state_slot = auth.authority_slot };
  assert_norm (p.proph_id_refinement == pid);
  assert_norm (p.token_table == t);
  assert_norm (p.token_slot == slot);
  assert_norm (p.agreement_table == t);
  assert_norm (p.agreement_slot == slot);
  assert_norm (p.state_table == auth.authority_table);
  assert_norm (p.state_slot == auth.authority_slot);
  rewrite (GFT.pts_to t slot #1.0R pvs) as
          (GFT.pts_to p.token_table p.token_slot #1.0R pvs);
  fold (prophecy_token_fragment p pvs);
  fold (prophecy_authority_state auth new_st);
  p
}

ghost
fn prophecy_authority_alloc_runtime (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len)
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len) **
    prophecy_token_fragment p pvs **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  rewrite (prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len)) as
          (prophecy_authority_state auth (reveal old_st) **
           pure (PT.proph_state_runtime_matches_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len)));
  assert (prophecy_authority_state auth (reveal old_st) **
    pure (PT.proph_state_runtime_matches_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len)));
  assert pure ((reveal old_st).encoded_next_proph_id == NST.prophecy_index (reveal c));
  PT.proph_state_alloc_fresh_authority_step_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len);
  let p = prophecy_authority_alloc #result #payload auth #old_st;
  rewrite each (PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder
    (reveal old_st).encoded_next_proph_id (reveal old_st).encoded_future_trace) as
    (PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder
      (NST.prophecy_index (reveal c)) (reveal old_st).encoded_future_trace);
  rewrite (prophecy_authority_state auth (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st))) **
           pure (PT.proph_state_runtime_matches_ctr_encoded
             (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)))
             (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len))) as
          (prophecy_authority_runtime_state auth (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)))
            (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len));
  p
}

ghost
fn prophecy_shared_state_interp_alloc (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len)
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_shared_state_interp auth new_st (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len) **
    prophecy_token_fragment p pvs **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  rewrite (prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len)) as
          (prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len));
  let p = prophecy_authority_alloc_runtime #result #payload auth #old_st #ot #c #len;
  rewrite (prophecy_authority_runtime_state auth (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)))
            (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len)) as
          (prophecy_shared_state_interp auth (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)))
            (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len));
  p
}

ghost
fn prophecy_shared_state_interp_alloc_obs_ctr_repr (#result #payload:Type0) (#s:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
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
    let pvs = PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_shared_state_interp auth new_st (reveal ot) r._3 (reveal len) **
    prophecy_token_fragment p pvs **
    pure (r._1 == pid /\ r._2 == s0 /\ r._3 == NST.bump_prophecy (reveal c) /\
      prophecy_id_of p == pid /\ prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup pid new_st.encoded_token_map == Some pvs))
{
  PT.proph_state_alloc_fresh_repr_obs_ctr_authority_step_encoded #result #payload #s
    (reveal old_st) (reveal ot) (reveal c) (reveal len) s0 t at;
  let p = prophecy_shared_state_interp_alloc #result #payload auth #old_st #ot #c #len;
  let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  assert pure (r._3 == NST.bump_prophecy (reveal c));
  p
}

ghost
fn prophecy_authority_alloc_runtime_frame (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
    (framed:prophecy_var result payload)
    (#framed_pvs:erased (PT.prediction_stream result payload))
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (prophecy_bound_to_authority auth framed /\
      prophecy_id_of framed <> NST.prophecy_index (reveal c) /\
      PT.proph_map_lookup (prophecy_id_of framed) (reveal old_st).encoded_token_map == Some (reveal framed_pvs))
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder pid (reveal old_st).encoded_future_trace in
    let new_st = snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)) in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len) **
    prophecy_token_fragment p pvs **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (prophecy_id_of p == pid /\
      prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup pid new_st.encoded_token_map == Some pvs /\
      PT.proph_map_lookup (prophecy_id_of framed) new_st.encoded_token_map == Some (reveal framed_pvs)))
{
  rewrite (prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len)) as
          (prophecy_authority_state auth (reveal old_st) **
           pure (PT.proph_state_runtime_matches_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len)));
  assert (prophecy_authority_state auth (reveal old_st) **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (PT.proph_state_runtime_matches_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len) /\
      prophecy_bound_to_authority auth framed /\
      prophecy_id_of framed <> NST.prophecy_index (reveal c) /\
      PT.proph_map_lookup (prophecy_id_of framed) (reveal old_st).encoded_token_map == Some (reveal framed_pvs)));
  assert pure ((reveal old_st).encoded_next_proph_id == NST.prophecy_index (reveal c));
  PT.proph_state_alloc_fresh_authority_step_frames_lookup_encoded (reveal old_st)
    (prophecy_id_of framed) (reveal framed_pvs);
  PT.proph_state_alloc_fresh_runtime_advances_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len);
  let p = prophecy_authority_alloc #result #payload auth #old_st;
  rewrite each (PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder
    (reveal old_st).encoded_next_proph_id (reveal old_st).encoded_future_trace) as
    (PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder
      (NST.prophecy_index (reveal c)) (reveal old_st).encoded_future_trace);
  rewrite (prophecy_authority_state auth (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st))) **
           pure (PT.proph_state_runtime_matches_ctr_encoded
             (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)))
             (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len))) as
          (prophecy_authority_runtime_state auth (snd (PT.proph_state_alloc_fresh_view_encoded (reveal old_st)))
            (reveal ot) (NST.bump_prophecy (reveal c)) (reveal len));
  p
}

ghost
fn prophecy_authority_resolve_observed (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
    (observed_nat:nat)
    (#tail:erased (PT.prediction_stream result payload))
    (#ks:erased PT.encoded_global_trace)
  requires prophecy_authority_state auth (reveal old_st) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_future_trace == observed_nat :: reveal ks /\
      (reveal old_st).encoded_decoder observed_nat ==
        Some (prophecy_id_of p, (observed_result, payload_value)) /\
      reveal pvs == (observed_result, payload_value) :: reveal tail)
  returns u:unit
  ensures (
    let new_st = PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) (reveal ks) in
    prophecy_authority_state auth new_st **
    prophecy_token_fragment p (reveal tail) **
    pure (PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  unfold prophecy_authority_state;
  unfold prophecy_token_fragment;
  assert (GFT.pts_to auth.authority_table auth.authority_slot #1.0R (reveal old_st) **
          GFT.pts_to p.token_table p.token_slot #1.0R (reveal pvs) **
          pure (PT.proph_state_interp_encoded (reveal old_st) /\
            prophecy_bound_to_authority auth p /\
            PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
            (reveal old_st).encoded_future_trace == observed_nat :: reveal ks /\
            (reveal old_st).encoded_decoder observed_nat ==
              Some (prophecy_id_of p, (observed_result, payload_value)) /\
            reveal pvs == (observed_result, payload_value) :: reveal tail));
  assert pure (PT.proph_state_interp_encoded (reveal old_st) /\
    prophecy_bound_to_authority auth p /\
    PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
    (reveal old_st).encoded_future_trace == observed_nat :: reveal ks /\
    (reveal old_st).encoded_decoder observed_nat ==
      Some (prophecy_id_of p, (observed_result, payload_value)) /\
    reveal pvs == (observed_result, payload_value) :: reveal tail);
  assert pure (PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map ==
          Some ((observed_result, payload_value) :: reveal tail));
  let new_st = PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) (reveal ks);
  PT.proph_state_resolve_authority_step_encoded (reveal old_st) (prophecy_id_of p)
    observed_result observed_result payload_value (reveal tail) observed_nat (reveal ks);
  GFT.update p.token_table #p.token_slot #(reveal pvs) (reveal tail);
  GFT.update auth.authority_table #auth.authority_slot #(reveal old_st) new_st;
  fold (prophecy_token_fragment p (reveal tail));
  fold (prophecy_authority_state auth new_st);
  ()
}

ghost
fn prophecy_authority_resolve_observed_runtime (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
    (observed_nat:nat)
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      observed_nat == reveal ot (NST.observation_index (reveal c)) /\
      PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder observed_nat ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (PT.prediction_stream result payload)
  ensures (
    let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (reveal pvs == (observed_result, payload_value) :: reveal tail /\
      PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  rewrite (prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len)) as
          (prophecy_authority_state auth (reveal old_st) **
           pure (PT.proph_state_runtime_matches_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len)));
  assert (prophecy_authority_state auth (reveal old_st) **
    prophecy_token_fragment p (reveal pvs) **
    pure (PT.proph_state_runtime_matches_ctr_encoded (reveal old_st) (reveal ot) (reveal c) (reveal len) /\
      prophecy_bound_to_authority auth p /\
      observed_nat == reveal ot (NST.observation_index (reveal c)) /\
      PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder observed_nat ==
        Some (prophecy_id_of p, (observed_result, payload_value))));
  let current_nat = reveal ot (NST.observation_index (reveal c));
  let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1);
  assert pure (observed_nat == current_nat);
  assert pure ((reveal old_st).encoded_decoder current_nat ==
    Some (prophecy_id_of p, (observed_result, payload_value)));
  let tail0 = PT.proph_list_resolves_encoded (reveal old_st).encoded_decoder (prophecy_id_of p) ks;
  PT.proph_state_lookup_projected_current_head_encoded (reveal old_st) (prophecy_id_of p)
    (observed_result, payload_value) (reveal pvs) (reveal ot) (reveal c) (reveal len);
  assert pure (reveal pvs == (observed_result, payload_value) :: tail0);
  PT.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) (reveal len);
  assert pure ((reveal old_st).encoded_future_trace == observed_nat :: ks);
  PT.proph_state_resolve_authority_step_ctr_encoded (reveal old_st) (prophecy_id_of p)
    observed_result observed_result payload_value tail0 observed_nat ks (reveal ot) (reveal c) (reveal len);
  prophecy_authority_resolve_observed #result #payload auth p payload_value #old_st #pvs
    observed_result observed_nat #tail0 #ks;
  rewrite (prophecy_authority_state auth
            (PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) tail0 ks) **
           pure (PT.proph_state_runtime_matches_ctr_encoded
            (PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) tail0 ks)
            (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1))) as
          (prophecy_authority_runtime_state auth
            (PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) tail0 ks)
            (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1));
  hide tail0
}

ghost
fn prophecy_authority_resolve_current (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
  requires prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (PT.prediction_stream result payload)
  ensures (
    let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_authority_runtime_state auth new_st (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (reveal pvs == (observed_result, payload_value) :: reveal tail /\
      PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  let observed_nat = reveal ot (NST.observation_index (reveal c));
  prophecy_authority_resolve_observed_runtime #result #payload auth p payload_value
    #old_st #ot #c #len #pvs observed_result observed_nat
}

ghost
fn prophecy_shared_state_interp_resolve_current (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
  requires prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (PT.prediction_stream result payload)
  ensures (
    let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_shared_state_interp auth new_st (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (reveal pvs == (observed_result, payload_value) :: reveal tail /\
      PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  rewrite (prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len)) as
          (prophecy_authority_runtime_state auth (reveal old_st) (reveal ot) (reveal c) (reveal len));
  let tail = prophecy_authority_resolve_current #result #payload auth p payload_value
    #old_st #ot #c #len #pvs observed_result;
  rewrite (prophecy_authority_runtime_state auth
            (PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail)
              (PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1)))
            (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1)) as
          (prophecy_shared_state_interp auth
            (PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail)
              (PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1)))
            (reveal ot) (NST.bump_observation (reveal c)) (reveal len - 1));
  tail
}

ghost
fn prophecy_shared_state_interp_resolve_obs_ctr_repr (#result #payload:Type0) (#s:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#old_st:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased (n:nat { n > 0 }))
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  requires prophecy_shared_state_interp auth (reveal old_st) (reveal ot) (reveal c) (reveal len) **
    prophecy_token_fragment p (reveal pvs) **
    pure (prophecy_bound_to_authority auth p /\
      PT.proph_map_lookup (prophecy_id_of p) (reveal old_st).encoded_token_map == Some (reveal pvs) /\
      (reveal old_st).encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (PT.prediction_stream result payload)
  ensures (
    let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (reveal len - 1) in
    let new_st = PT.proph_state_resolve_view_encoded (reveal old_st) (prophecy_id_of p) (reveal tail) ks in
    prophecy_shared_state_interp auth new_st (reveal ot) r._3 (reveal len - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (r._1 == reveal ot (NST.observation_index (reveal c)) /\ r._2 == s0 /\
      r._3 == NST.bump_observation (reveal c) /\
      reveal pvs == (observed_result, payload_value) :: reveal tail /\
      PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  let tail = prophecy_shared_state_interp_resolve_current #result #payload auth p payload_value
    #old_st #ot #c #len #pvs observed_result;
  NST.observe_obs_ctr_result #s s0 t at (reveal ot) (reveal c);
  let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  assert pure (r._3 == NST.bump_observation (reveal c));
  tail
}

(** Packaged adequacy-owned prophecy component.

    [prophecy_shared_state_interp] is the precise resource that an active
    adequacy/state interpretation must own.  The package below keeps the
    authoritative handle, current encoded state, and finite observation-suffix
    length together, so the NewProph and Resolve updates consume and return one
    first-class component rather than passing the fields independently.  This is
    still a ghost/resource-level component: public executable NewProph/Resolve
    will be able to delete the two remaining witnesses only once PulseCore's
    active semantics opens this component at the actual [ot,c] of
    [FreshProphId]/[ObservedResultAct]. *)
[@@pulse_unfold]
let prophecy_active_component_interp (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : slprop
= prophecy_shared_state_interp comp.component_authority comp.component_state_view ot c comp.component_len

let prophecy_component_bound (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (p:prophecy_var result payload)
  : GTot prop
= prophecy_bound_to_authority comp.component_authority p

let prophecy_component_lookup (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (p:prophecy_var result payload)
    (pvs:PT.prediction_stream result payload)
  : GTot prop
= PT.proph_map_lookup (prophecy_id_of p) comp.component_state_view.encoded_token_map == Some pvs

let prophecy_active_component_after_alloc (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
  : GTot (prophecy_active_component result payload)
= { component_authority = comp.component_authority;
    component_state_view = snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view);
    component_len = comp.component_len }

let prophecy_active_component_after_resolve (#result #payload:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (tail:PT.prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : GTot (prophecy_active_component result payload)
= { component_authority = comp.component_authority;
    component_state_view = PT.proph_state_resolve_view_encoded comp.component_state_view
      (prophecy_id_of p) tail
      (PT.encoded_trace_of_tape ot (NST.observation_index c + 1) (comp.component_len - 1));
    component_len = comp.component_len - 1 }

(** First-class singleton active-prophecy state interpretation for one typed
    projection of the nat-encoded prophecy world.  This predicate is the local
    Pulse resource shape that the active semantics/adequacy layer must own at
    the current observation tape and counter.  Opening it exposes exactly one
    [prophecy_active_component_interp]; allocation and resolution close the
    same singleton at the bumped counter rather than manufacturing a component
    from [emp]. *)
[@@pulse_unfold]
let active_prophecy_si (#result #payload:Type0)
    (ot:nat -> nat)
    (c:NST.ctr)
  : slprop
= exists* (comp:prophecy_active_component result payload).
    prophecy_active_component_interp comp ot c

let rec pw_map_keys
    (m:PW.proph_map)
  : Tot (list nat)
    (decreases m)
= match m with
  | [] -> []
  | (pid, _) :: m' -> pid :: pw_map_keys m'

let rec typed_map_keys (#result #payload:Type0)
    (m:PT.proph_map result payload)
  : Tot (list nat)
    (decreases m)
= match m with
  | [] -> []
  | (pid, _) :: m' -> pid :: typed_map_keys m'

let pw_map_keys_alloc
    (decode:PW.decoder)
    (pid:PW.proph_id)
    (ks:PW.encoded_trace)
    (m:PW.proph_map)
  : Lemma
    (ensures pw_map_keys (PW.alloc decode pid ks m) == pid :: pw_map_keys m)
= ()

let typed_map_keys_alloc (#result #payload:Type0)
    (decode:PT.encoded_observation_decoder result payload)
    (pid:PT.proph_id)
    (ks:PT.encoded_global_trace)
    (m:PT.proph_map result payload)
  : Lemma
    (ensures typed_map_keys (PT.proph_map_alloc_encoded decode pid ks m) == pid :: typed_map_keys m)
= ()

let rec pw_map_keys_update
    (pid:PW.proph_id)
    (tail:PW.prediction_stream)
    (m:PW.proph_map)
  : Lemma
    (ensures pw_map_keys (PW.update pid tail m) == pw_map_keys m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' -> if pid = pid' then () else pw_map_keys_update pid tail m'

let rec typed_map_keys_update (#result #payload:Type0)
    (pid:PT.proph_id)
    (tail:PT.prediction_stream result payload)
    (m:PT.proph_map result payload)
  : Lemma
    (ensures typed_map_keys (PT.proph_map_update pid tail m) == typed_map_keys m)
    (decreases m)
= match m with
  | [] -> ()
  | (_, _) :: m' -> typed_map_keys_update pid tail m'

(** Deterministic allocation order for typed projections.  Active NewProph
    allocates [NST.prophecy_index c] by consing it at the head, so a current
    token whose agreement slot is its prophecy id can recover its registry/map
    entry from the active next-id bound instead of relying on a hidden
    p-specific registry-membership witness. *)
let rec typed_map_descending_from (#result #payload:Type0)
    (next:PT.proph_id)
    (m:PT.proph_map result payload)
  : Tot prop
    (decreases m)
= match m with
  | [] -> next == 0
  | (pid, _) :: m' -> next == pid + 1 /\ typed_map_descending_from #result #payload pid m'

let typed_map_descending_alloc (#result #payload:Type0)
    (next:PT.proph_id)
    (pvs:PT.prediction_stream result payload)
    (m:PT.proph_map result payload)
  : Lemma
    (requires typed_map_descending_from #result #payload next m)
    (ensures typed_map_descending_from #result #payload (next + 1) ((next, pvs) :: m))
= ()

let rec typed_map_descending_update (#result #payload:Type0)
    (next:PT.proph_id)
    (pid:PT.proph_id)
    (tail:PT.prediction_stream result payload)
    (m:PT.proph_map result payload)
  : Lemma
    (requires typed_map_descending_from #result #payload next m)
    (ensures typed_map_descending_from #result #payload next (PT.proph_map_update pid tail m))
    (decreases m)
= match m with
  | [] -> ()
  | (pid0, pvs0) :: m' ->
    assert (next == pid0 + 1);
    assert (typed_map_descending_from #result #payload pid0 m');
    typed_map_descending_update pid0 pid tail m'

let rec trace_of_tape_agrees
    (ot:nat -> nat)
    (start:nat)
    (len:nat)
  : Lemma
    (ensures PW.trace_of_tape ot start len == PT.encoded_trace_of_tape ot start len)
    (decreases len)
= if len = 0 then () else trace_of_tape_agrees ot (start + 1) (len - 1)

let decoder_projects_world_pack (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (typed_decode:PT.encoded_observation_decoder result payload)
    (world_decode:PW.decoder)
  : GTot prop
= forall (n:nat). world_decode n == PT.erase_encoded_decoder pack typed_decode n

let decoder_reflects_world_pack (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (typed_decode:PT.encoded_observation_decoder result payload)
    (world_decode:PW.decoder)
  : GTot prop
= forall (n:nat) (pid:PT.proph_id) (r:result) (pl:payload).
    world_decode n == Some { PW.proph = pid; PW.payload = pack r pl } ==>
    typed_decode n == Some (pid, (r, pl))

let rec list_resolves_decoder_ext
    (d1 d2:PW.decoder)
    (pid:PW.proph_id)
    (ks:PW.encoded_trace)
  : Lemma
    (requires (forall (n:nat). d1 n == d2 n))
    (ensures PW.list_resolves d1 pid ks == PW.list_resolves d2 pid ks)
    (decreases ks)
= match ks with
  | [] -> ()
  | n :: ks' ->
    list_resolves_decoder_ext d1 d2 pid ks';
    assert (d1 n == d2 n)

let rec token_maps_project (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (typed_map:PT.proph_map result payload)
    (world_map:PW.proph_map)
  : Tot prop
    (decreases typed_map)
= match typed_map, world_map with
  | [], [] -> True
  | (pid_t, pvs_t) :: typed_tail, (pid_w, pvs_w) :: world_tail ->
    pid_w == pid_t /\
    pvs_w == PT.erase_prediction_stream pack pvs_t /\
    token_maps_project pack typed_tail world_tail
  | _, _ -> False

let rec prediction_stream_erasure_reflects (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (pvs:PT.prediction_stream result payload)
  : Tot prop
    (decreases pvs)
= match pvs with
  | [] -> True
  | (observed_result, payload_value) :: tail ->
    (forall (r:result) (pl:payload).
       pack r pl == pack observed_result payload_value ==> r == observed_result /\ pl == payload_value) /\
    prediction_stream_erasure_reflects #result #payload pack tail

let prediction_stream_erasure_reflects_tail (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (observed_result:result)
    (payload_value:payload)
    (tail:PT.prediction_stream result payload)
  : Lemma
    (requires prediction_stream_erasure_reflects #result #payload pack ((observed_result, payload_value) :: tail))
    (ensures prediction_stream_erasure_reflects #result #payload pack tail)
= ()

let prediction_stream_erasure_reflects_cons (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (observed_result:result)
    (payload_value:payload)
    (tail:PT.prediction_stream result payload)
  : Lemma
    (requires (forall (r:result) (pl:payload).
                 pack r pl == pack observed_result payload_value ==> r == observed_result /\ pl == payload_value) /\
              prediction_stream_erasure_reflects #result #payload pack tail)
    (ensures prediction_stream_erasure_reflects #result #payload pack ((observed_result, payload_value) :: tail))
= ()

let rec prediction_stream_erasure_reflects_injective (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (reflected:PT.prediction_stream result payload)
    (candidate:PT.prediction_stream result payload)
  : Lemma
    (requires prediction_stream_erasure_reflects #result #payload pack reflected /\
              PT.erase_prediction_stream pack candidate == PT.erase_prediction_stream pack reflected)
    (ensures candidate == reflected)
    (decreases reflected)
= match reflected, candidate with
  | [], [] -> ()
  | (observed_result, payload_value) :: reflected_tail, (r, pl) :: candidate_tail ->
    assert (pack r pl == pack observed_result payload_value);
    assert (r == observed_result /\ pl == payload_value);
    assert (PT.erase_prediction_stream pack candidate_tail == PT.erase_prediction_stream pack reflected_tail);
    prediction_stream_erasure_reflects_injective pack reflected_tail candidate_tail
  | _, _ -> ()

let prediction_stream_tail (#result #payload:Type0)
    (pvs:PT.prediction_stream result payload)
  : Tot (PT.prediction_stream result payload)
= match pvs with
  | [] -> []
  | _ :: tail -> tail

let prediction_stream_erasure_reflects_head (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (pvs:PT.prediction_stream result payload)
    (observed_result:result)
    (payload_value:payload)
    (world_tail:PW.prediction_stream)
  : Lemma
    (requires prediction_stream_erasure_reflects #result #payload pack pvs /\
              PT.erase_prediction_stream pack pvs == pack observed_result payload_value :: world_tail)
    (ensures pvs == (observed_result, payload_value) :: prediction_stream_tail pvs /\
             PT.erase_prediction_stream pack (prediction_stream_tail pvs) == world_tail)
= match pvs with
  | [] -> assert False
  | (r0, pl0) :: tail0 ->
    assert (PT.erase_prediction_stream pack pvs ==
      pack r0 pl0 :: PT.erase_prediction_stream pack tail0);
    assert (pack r0 pl0 == pack observed_result payload_value);
    assert (pack observed_result payload_value == pack r0 pl0);
    assert (observed_result == r0 /\ payload_value == pl0);
    assert (r0 == observed_result /\ pl0 == payload_value)

let rec list_resolves_encoded_erasure_reflects (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (typed_decode:PT.encoded_observation_decoder result payload)
    (world_decode:PW.decoder)
    (pid:PT.proph_id)
    (ks:PT.encoded_global_trace)
  : Lemma
    (requires decoder_projects_world_pack #result #payload pack typed_decode world_decode /\
              decoder_reflects_world_pack #result #payload pack typed_decode world_decode)
    (ensures prediction_stream_erasure_reflects #result #payload pack
      (PT.proph_list_resolves_encoded typed_decode pid ks))
    (decreases ks)
= match ks with
  | [] -> ()
  | n :: ks' ->
    list_resolves_encoded_erasure_reflects pack typed_decode world_decode pid ks';
    match typed_decode n with
    | None -> ()
    | Some (pid', (r, pl)) ->
      if pid' = pid then (
        assert (world_decode n == Some { PW.proph = pid'; PW.payload = pack r pl });
        assert (forall (r':result) (pl':payload).
          pack r' pl' == pack r pl ==> r' == r /\ pl' == pl);
        prediction_stream_erasure_reflects_cons pack r pl
          (PT.proph_list_resolves_encoded typed_decode pid ks')
      ) else ()

let rec token_maps_streams_reflect (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (typed_map:PT.proph_map result payload)
  : Tot prop
    (decreases typed_map)
= match typed_map with
  | [] -> True
  | (_, pvs) :: typed_tail ->
    prediction_stream_erasure_reflects #result #payload pack pvs /\
    token_maps_streams_reflect pack typed_tail

let rec token_maps_streams_reflect_lookup (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (pid:PT.proph_id)
    (typed_map:PT.proph_map result payload)
    (pvs:PT.prediction_stream result payload)
  : Lemma
    (requires token_maps_streams_reflect #result #payload pack typed_map /\
              PT.proph_map_lookup pid typed_map == Some pvs)
    (ensures prediction_stream_erasure_reflects #result #payload pack pvs)
    (decreases typed_map)
= match typed_map with
  | [] -> ()
  | (pid_t, pvs_t) :: typed_tail ->
    if pid = pid_t then () else token_maps_streams_reflect_lookup pack pid typed_tail pvs

let token_maps_streams_reflect_alloc (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (typed_decode:PT.encoded_observation_decoder result payload)
    (world_decode:PW.decoder)
    (pid:PT.proph_id)
    (typed_ks:PT.encoded_global_trace)
    (typed_map:PT.proph_map result payload)
  : Lemma
    (requires decoder_projects_world_pack #result #payload pack typed_decode world_decode /\
              decoder_reflects_world_pack #result #payload pack typed_decode world_decode /\
              token_maps_streams_reflect #result #payload pack typed_map)
    (ensures token_maps_streams_reflect #result #payload pack
      (PT.proph_map_alloc_encoded typed_decode pid typed_ks typed_map))
= list_resolves_encoded_erasure_reflects pack typed_decode world_decode pid typed_ks

let rec token_maps_streams_reflect_update (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (pid:PT.proph_id)
    (old_pvs:PT.prediction_stream result payload)
    (observed_result:result)
    (payload_value:payload)
    (tail:PT.prediction_stream result payload)
    (typed_map:PT.proph_map result payload)
  : Lemma
    (requires token_maps_streams_reflect #result #payload pack typed_map /\
              PT.proph_map_unique typed_map /\
              PT.proph_map_lookup pid typed_map == Some old_pvs /\
              old_pvs == (observed_result, payload_value) :: tail)
    (ensures token_maps_streams_reflect #result #payload pack
      (PT.proph_map_update pid tail typed_map))
    (decreases typed_map)
= match typed_map with
  | [] -> ()
  | (pid_t, pvs_t) :: typed_tail ->
    assert (PT.proph_map_unique typed_tail);
    if pid = pid_t then (
      assert (pvs_t == old_pvs);
      prediction_stream_erasure_reflects_tail pack observed_result payload_value tail;
      PT.proph_map_update_fresh_noop pid tail typed_tail;
      assert (PT.proph_map_update pid tail typed_tail == typed_tail)
    ) else (
      assert (token_maps_streams_reflect pack typed_tail);
      assert (PT.proph_map_lookup pid typed_tail == Some old_pvs);
      token_maps_streams_reflect_update pack pid old_pvs observed_result payload_value tail typed_tail
    )

let rec token_maps_project_lookup_back (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (pid:PT.proph_id)
    (typed_map:PT.proph_map result payload)
    (world_map:PW.proph_map)
    (pvs:PT.prediction_stream result payload)
  : Lemma
    (requires token_maps_project pack typed_map world_map /\
              token_maps_streams_reflect #result #payload pack typed_map /\
              PW.lookup pid world_map == Some (PT.erase_prediction_stream pack pvs))
    (ensures PT.proph_map_lookup pid typed_map == Some pvs)
    (decreases typed_map)
= match typed_map, world_map with
  | (pid_t, pvs_t) :: typed_tail, (pid_w, pvs_w) :: world_tail ->
    assert (pid_w == pid_t);
    assert (pvs_w == PT.erase_prediction_stream pack pvs_t);
    if pid = pid_t then (
      assert (PT.erase_prediction_stream pack pvs == PT.erase_prediction_stream pack pvs_t);
      assert (prediction_stream_erasure_reflects #result #payload pack pvs_t);
      prediction_stream_erasure_reflects_injective pack pvs_t pvs
    ) else (
      assert (token_maps_project pack typed_tail world_tail);
      assert (token_maps_streams_reflect pack typed_tail);
      assert (PW.lookup pid world_tail == Some (PT.erase_prediction_stream pack pvs));
      token_maps_project_lookup_back pack pid typed_tail world_tail pvs
    )
  | _, _ -> ()

let rec token_maps_project_lookup (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (pid:PT.proph_id)
    (typed_map:PT.proph_map result payload)
    (world_map:PW.proph_map)
    (pvs:PT.prediction_stream result payload)
  : Lemma
    (requires token_maps_project pack typed_map world_map /\
              PT.proph_map_lookup pid typed_map == Some pvs)
    (ensures PW.lookup pid world_map == Some (PT.erase_prediction_stream pack pvs))
    (decreases typed_map)
= match typed_map, world_map with
  | (pid_t, pvs_t) :: typed_tail, (pid_w, pvs_w) :: world_tail ->
    assert (pid_w == pid_t);
    if pid = pid_t then (
      assert (pvs_t == pvs)
    ) else (
      assert (token_maps_project pack typed_tail world_tail);
      assert (PT.proph_map_lookup pid typed_tail == Some pvs);
      token_maps_project_lookup pack pid typed_tail world_tail pvs
    )
  | _, _ -> ()

let rec world_interp_lookup_projected_head
    (decode:PW.decoder)
    (pid:PW.proph_id)
    (payload:nat)
    (pvs:PW.prediction_stream)
    (n:nat)
    (ks:PW.encoded_trace)
    (m:PW.proph_map)
  : Lemma
    (requires PW.interp decode (n :: ks) m /\
              PW.lookup pid m == Some pvs /\
              decode n == Some { PW.proph = pid; PW.payload = payload })
    (ensures pvs == payload :: PW.list_resolves decode pid ks)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', pvs') :: m' ->
    if pid = pid' then (
      assert (pvs' == pvs);
      PW.list_resolves_cons_current decode pid payload n ks
    ) else (
      assert (PW.interp decode (n :: ks) m');
      assert (PW.lookup pid m' == Some pvs);
      world_interp_lookup_projected_head decode pid payload pvs n ks m'
    )

let world_state_lookup_projected_current_head
    (st:PW.state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
    (pid:PW.proph_id)
    (payload:nat)
    (pvs:PW.prediction_stream)
  : Lemma
    (requires PW.state_interp st /\
              PW.runtime_matches_ctr st ot c len /\
              len > 0 /\
              PW.current_observation_decodes_to st ot c pid payload /\
              PW.lookup pid st.PW.world_token_map == Some pvs)
    (ensures pvs == payload ::
      PW.list_resolves st.PW.world_decoder pid
        (PW.trace_of_tape ot (NST.observation_index c + 1) (len - 1)))
= let n = ot (NST.observation_index c) in
  let ks = PW.trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  PW.trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.PW.world_future_trace == n :: ks);
  world_interp_lookup_projected_head st.PW.world_decoder pid payload pvs n ks st.PW.world_token_map

let token_maps_project_alloc (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (typed_decode:PT.encoded_observation_decoder result payload)
    (world_decode:PW.decoder)
    (pid:PT.proph_id)
    (typed_ks:PT.encoded_global_trace)
    (world_ks:PW.encoded_trace)
    (typed_map:PT.proph_map result payload)
    (world_map:PW.proph_map)
  : Lemma
    (requires decoder_projects_world_pack #result #payload pack typed_decode world_decode /\
              world_ks == typed_ks /\
              token_maps_project pack typed_map world_map)
    (ensures token_maps_project pack
      (PT.proph_map_alloc_encoded typed_decode pid typed_ks typed_map)
      (PW.alloc world_decode pid world_ks world_map))
= list_resolves_decoder_ext world_decode (PT.erase_encoded_decoder pack typed_decode) pid world_ks;
  PT.erase_list_resolves_encoded pack typed_decode pid typed_ks;
  assert (PW.list_resolves world_decode pid world_ks ==
    PT.erase_prediction_stream pack (PT.proph_list_resolves_encoded typed_decode pid typed_ks))

let rec token_maps_project_update (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (pid:PT.proph_id)
    (tail:PT.prediction_stream result payload)
    (world_tail_stream:PW.prediction_stream)
    (typed_map:PT.proph_map result payload)
    (world_map:PW.proph_map)
  : Lemma
    (requires token_maps_project pack typed_map world_map /\
              PT.proph_map_unique typed_map /\
              world_tail_stream == PT.erase_prediction_stream pack tail)
    (ensures token_maps_project pack
      (PT.proph_map_update pid tail typed_map)
      (PW.update pid world_tail_stream world_map))
    (decreases typed_map)
= match typed_map, world_map with
  | [], [] -> ()
  | (pid_t, pvs_t) :: typed_tail, (pid_w, pvs_w) :: world_tail ->
    assert (pid_w == pid_t);
    assert (PT.proph_map_unique typed_tail);
    if pid = pid_t then (
      assert (PT.proph_map_fresh pid_t typed_tail);
      PT.proph_map_update_fresh_noop pid tail typed_tail;
      assert (PT.proph_map_update pid tail typed_tail == typed_tail);
      assert (PW.update pid world_tail_stream ((pid_w, pvs_w) :: world_tail) ==
        (pid_w, world_tail_stream) :: world_tail)
    ) else (
      assert (token_maps_project pack typed_tail world_tail);
      token_maps_project_update pack pid tail world_tail_stream typed_tail world_tail
    )
  | _, _ -> ()

(** Pure coherence relation saying that the typed active component is a view of
    the singleton nat-encoded world currently owned by [PWR.active_world_interp].
    It relates exact typed-to-nat decoder projection and decoder reflection
    through the projection adapter carried by [active_prophecy_world_si], the
    shared future-trace suffix, token-map keys, value-level erasure of every
    typed token-map stream to the singleton map, finite-stream erasure
    reflection for those mapped streams, typed uniqueness/boundedness needed for
    updates, fresh-id/observation counters, and the finite suffix length.
    Consequently NewProph's freshly returned typed stream, and every previously
    allocated typed token stream in the component, is forced to erase to the
    corresponding singleton world stream under that active adapter; Resolve can
    now derive the singleton erased lookup from a typed projection-registry
    lookup plus this projection/reflection invariant instead of receiving the
    singleton lookup as a p-specific hidden precondition. *)
let active_component_projects_world (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (comp:prophecy_active_component result payload)
    (st:PW.state_view)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : GTot prop
= decoder_projects_world_pack #result #payload pack comp.component_state_view.encoded_decoder st.PW.world_decoder /\
  decoder_reflects_world_pack #result #payload pack comp.component_state_view.encoded_decoder st.PW.world_decoder /\
  st.PW.world_future_trace == comp.component_state_view.encoded_future_trace /\
  pw_map_keys st.PW.world_token_map == typed_map_keys comp.component_state_view.encoded_token_map /\
  token_maps_project pack
    comp.component_state_view.encoded_token_map st.PW.world_token_map /\
  token_maps_streams_reflect #result #payload pack comp.component_state_view.encoded_token_map /\
  PT.proph_map_unique comp.component_state_view.encoded_token_map /\
  PT.proph_map_bounded comp.component_state_view.encoded_next_proph_id
    comp.component_state_view.encoded_token_map /\
  typed_map_descending_from #result #payload comp.component_state_view.encoded_next_proph_id
    comp.component_state_view.encoded_token_map /\
  st.PW.world_next_proph_id == comp.component_state_view.encoded_next_proph_id /\
  st.PW.world_observation_index == comp.component_state_view.encoded_observation_index /\
  len == comp.component_len /\
  comp.component_state_view.encoded_next_proph_id == NST.prophecy_index c /\
  comp.component_state_view.encoded_observation_index == NST.observation_index c /\
  st.PW.world_next_proph_id == NST.prophecy_index c /\
  st.PW.world_observation_index == NST.observation_index c

let active_component_projects_world_after_alloc (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (comp:prophecy_active_component result payload)
    (st:PW.state_view)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (pid:PT.proph_id)
  : Lemma
    (requires active_component_projects_world #result #payload pack comp st ot c len /\
              pid == NST.prophecy_index c)
    (ensures active_component_projects_world #result #payload pack
      (prophecy_active_component_after_alloc comp)
      (PW.alloc_view st pid) ot (NST.bump_prophecy c) len)
= assert (pid == comp.component_state_view.encoded_next_proph_id);
  pw_map_keys_alloc st.PW.world_decoder pid st.PW.world_future_trace st.PW.world_token_map;
  typed_map_keys_alloc comp.component_state_view.encoded_decoder pid
    comp.component_state_view.encoded_future_trace comp.component_state_view.encoded_token_map;
  token_maps_project_alloc pack
    comp.component_state_view.encoded_decoder st.PW.world_decoder pid
    comp.component_state_view.encoded_future_trace st.PW.world_future_trace
    comp.component_state_view.encoded_token_map st.PW.world_token_map;
  token_maps_streams_reflect_alloc pack comp.component_state_view.encoded_decoder st.PW.world_decoder pid
    comp.component_state_view.encoded_future_trace comp.component_state_view.encoded_token_map;
  PT.proph_map_bounded_fresh comp.component_state_view.encoded_next_proph_id
    comp.component_state_view.encoded_token_map;
  PT.proph_map_alloc_encoded_preserves_unique comp.component_state_view.encoded_decoder pid
    comp.component_state_view.encoded_future_trace comp.component_state_view.encoded_token_map;
  PT.proph_map_alloc_fresh_preserves_bounded comp.component_state_view.encoded_next_proph_id
    (PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid
      comp.component_state_view.encoded_future_trace)
    comp.component_state_view.encoded_token_map;
  typed_map_descending_alloc comp.component_state_view.encoded_next_proph_id
    (PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid
      comp.component_state_view.encoded_future_trace)
    comp.component_state_view.encoded_token_map

let active_component_projects_world_after_resolve (#result #payload:Type0)
    (pack:result -> payload -> nat)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (st:PW.state_view)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat { len > 0 })
    (p:prophecy_var result payload)
    (old_pvs:PT.prediction_stream result payload)
    (observed_result:result)
    (payload_value:payload)
    (world_tail:PW.prediction_stream)
    (tail:PT.prediction_stream result payload)
  : Lemma
    (requires active_component_projects_world #result #payload pack comp st ot c len /\
              prophecy_component_lookup comp p old_pvs /\
              old_pvs == (observed_result, payload_value) :: tail /\
              world_tail == PT.erase_prediction_stream pack tail)
    (ensures active_component_projects_world #result #payload pack
      (prophecy_active_component_after_resolve comp p tail ot c)
      (PW.resolve_view st (prophecy_id_of p) world_tail
        (PW.trace_of_tape ot (NST.observation_index c + 1) (len - 1)))
      ot (NST.bump_observation c) (len - 1))
= trace_of_tape_agrees ot (NST.observation_index c + 1) (len - 1);
  pw_map_keys_update (prophecy_id_of p) world_tail st.PW.world_token_map;
  typed_map_keys_update (prophecy_id_of p) tail comp.component_state_view.encoded_token_map;
  token_maps_project_update pack
    (prophecy_id_of p) tail world_tail
    comp.component_state_view.encoded_token_map st.PW.world_token_map;
  token_maps_streams_reflect_update pack (prophecy_id_of p) old_pvs observed_result payload_value tail
    comp.component_state_view.encoded_token_map;
  PT.proph_map_update_preserves_unique (prophecy_id_of p) tail
    comp.component_state_view.encoded_token_map;
  PT.proph_map_update_preserves_bounded comp.component_state_view.encoded_next_proph_id
    (prophecy_id_of p) tail comp.component_state_view.encoded_token_map;
  typed_map_descending_update comp.component_state_view.encoded_next_proph_id
    (prophecy_id_of p) tail comp.component_state_view.encoded_token_map

let active_token_registry_entry (result payload:Type0)
  = PT.proph_id & prophecy_token_cell result payload

let rec active_token_registry (#result #payload:Type0)
    (agreement_table:GFT.table (PT.prediction_stream result payload))
    (registry:list (active_token_registry_entry result payload))
    (typed_map:PT.proph_map result payload)
  : Tot slprop
    (decreases registry)
= match registry, typed_map with
  | [], [] -> emp
  | (pid_r, cell) :: registry_tail, (pid_t, pvs_t) :: typed_tail ->
    GFT.pts_to agreement_table pid_t #0.5R pvs_t **
    pure (pid_r == pid_t /\
      cell.agreement_cell_table == agreement_table /\
      cell.agreement_cell_slot == pid_t) **
    active_token_registry #result #payload agreement_table registry_tail typed_tail
  | _, _ -> pure False

noeq type active_prophecy_projection (result payload:Type0) = {
  projection_component: prophecy_active_component result payload;
  projection_pack: result -> payload -> nat;
  projection_registry: list (active_token_registry_entry result payload);
  projection_agreement_table: GFT.table (PT.prediction_stream result payload);
}

let prophecy_token_bound_to_projection (#result #payload:Type0)
    (p:prophecy_var result payload)
    (projection:active_prophecy_projection result payload)
  : GTot prop
= p.agreement_table == projection.projection_agreement_table /\
  p.proph_payload_pack == projection.projection_pack /\
  p.agreement_slot == prophecy_id_of p /\
  prophecy_id_of p < projection.projection_component.component_state_view.encoded_next_proph_id

(** Spatial projection metadata carried by the singleton active state.
    It is still not typed authority: it owns only the active half of the
    first-class token/world agreement cells created by NewProph.  The paired
    public half lives in [prophecy_token].  The agreement halves now live in a
    deterministic projection table at slot [pid], so Resolve can recover the
    active entry from the public token's table/slot certificate and the active
    next-id/order invariant instead of a p-specific registry membership fact. *)
let active_prophecy_projection_view (#result #payload:Type0)
    (projection:active_prophecy_projection result payload)
  : slprop
= GFT.is_table projection.projection_agreement_table
    projection.projection_component.component_state_view.encoded_next_proph_id **
  active_token_registry #result #payload projection.projection_agreement_table
    projection.projection_registry
    projection.projection_component.component_state_view.encoded_token_map

ghost fn rec active_token_registry_lookup_agreement (#result #payload:Type0)
    (agreement_table:GFT.table (PT.prediction_stream result payload))
    (registry:list (active_token_registry_entry result payload))
    (typed_map:PT.proph_map result payload)
    (next:PT.proph_id)
    (target_pid:PT.proph_id)
    (p:prophecy_var result payload)
    (#pvs:erased (PT.prediction_stream result payload))
  requires active_token_registry #result #payload agreement_table registry typed_map **
    prophecy_token_agreement p (reveal pvs) **
    pure (target_pid == prophecy_id_of p /\
      p.agreement_table == agreement_table /\
      p.agreement_slot == target_pid /\
      target_pid < next /\
      typed_map_descending_from #result #payload next typed_map)
  ensures active_token_registry #result #payload agreement_table registry typed_map **
    prophecy_token_agreement p (reveal pvs) **
    pure (PT.proph_map_lookup (prophecy_id_of p) typed_map == Some (reveal pvs))
  decreases registry
{
  match registry {
    [] -> {
      match typed_map {
        [] -> {
          assert pure (typed_map_descending_from #result #payload next []);
          assert pure (next == 0);
          assert pure (target_pid < 0);
          unreachable ()
        }
        typed_entry :: typed_tail -> {
          rewrite (active_token_registry #result #payload agreement_table [] (typed_entry :: typed_tail)) as pure False;
          unreachable ()
        }
      }
    }
    registry_entry :: registry_tail -> {
      let pid_r = registry_entry._1;
      let cell = registry_entry._2;
      match typed_map {
        [] -> {
          rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail) []) as pure False;
          unreachable ()
        }
        typed_entry :: typed_tail -> {
          let pid_t = typed_entry._1;
          let pvs_t = typed_entry._2;
          rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail) (typed_entry :: typed_tail)) as
            (GFT.pts_to agreement_table pid_t #0.5R pvs_t **
            pure (pid_r == pid_t /\
              cell.agreement_cell_table == agreement_table /\
              cell.agreement_cell_slot == pid_t) **
            active_token_registry #result #payload agreement_table registry_tail typed_tail);
          assert (GFT.pts_to agreement_table pid_t #0.5R pvs_t **
            pure (pid_r == pid_t /\
              cell.agreement_cell_table == agreement_table /\
              cell.agreement_cell_slot == pid_t) **
            active_token_registry #result #payload agreement_table registry_tail typed_tail **
            prophecy_token_agreement p (reveal pvs));
          assert pure (typed_map_descending_from #result #payload next ((pid_t, pvs_t) :: typed_tail));
          assert pure (next == pid_t + 1);
          if (target_pid = pid_t) {
            rewrite (prophecy_token_agreement p (reveal pvs)) as
              (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal pvs) **
                pure (p.agreement_slot == prophecy_id_of p));
            assert pure ((prophecy_token_cell_of p).agreement_cell_table == agreement_table);
            assert pure ((prophecy_token_cell_of p).agreement_cell_slot == pid_t);
            rewrite each (prophecy_token_cell_of p).agreement_cell_table as agreement_table;
            rewrite each (prophecy_token_cell_of p).agreement_cell_slot as pid_t;
            GFT.gather #(PT.prediction_stream result payload) agreement_table pid_t #0.5R #0.5R #pvs_t #(reveal pvs);
            assert pure (pvs_t == reveal pvs);
            GFT.share #(PT.prediction_stream result payload) agreement_table pid_t 0.5R 0.5R #1.0R #pvs_t;
            rewrite (GFT.pts_to agreement_table pid_t #0.5R pvs_t) as
              (GFT.pts_to (prophecy_token_cell_of p).agreement_cell_table
                (prophecy_token_cell_of p).agreement_cell_slot #0.5R (reveal pvs));
            assert (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal pvs) **
              pure (p.agreement_slot == prophecy_id_of p));
            fold (prophecy_token_agreement p (reveal pvs));
            fold (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
              ((pid_t, pvs_t) :: typed_tail));
            rewrite (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
                ((pid_t, pvs_t) :: typed_tail)) as
              (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (typed_entry :: typed_tail));
            rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (typed_entry :: typed_tail)) as
              (active_token_registry #result #payload agreement_table registry typed_map);
            assert pure (PT.proph_map_lookup (prophecy_id_of p) (typed_entry :: typed_tail) == Some (reveal pvs))
          } else {
            assert pure (target_pid < pid_t);
            assert pure (typed_map_descending_from #result #payload pid_t typed_tail);
            active_token_registry_lookup_agreement #result #payload agreement_table registry_tail typed_tail pid_t target_pid p #pvs;
            fold (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
              ((pid_t, pvs_t) :: typed_tail));
            rewrite (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
                ((pid_t, pvs_t) :: typed_tail)) as
              (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (typed_entry :: typed_tail));
            rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (typed_entry :: typed_tail)) as
              (active_token_registry #result #payload agreement_table registry typed_map);
            assert pure (PT.proph_map_lookup (prophecy_id_of p) (typed_entry :: typed_tail) == Some (reveal pvs))
          }
        }
      }
    }
  }
}

ghost fn rec active_token_registry_resolve_agreement (#result #payload:Type0)
    (agreement_table:GFT.table (PT.prediction_stream result payload))
    (registry:list (active_token_registry_entry result payload))
    (typed_map:PT.proph_map result payload)
    (next:PT.proph_id)
    (target_pid:PT.proph_id)
    (p:prophecy_var result payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#tail:erased (PT.prediction_stream result payload))
  requires active_token_registry #result #payload agreement_table registry typed_map **
    prophecy_token_agreement p (reveal pvs) **
    pure (target_pid == prophecy_id_of p /\
      p.agreement_table == agreement_table /\
      p.agreement_slot == target_pid /\
      target_pid < next /\
      typed_map_descending_from #result #payload next typed_map /\
      PT.proph_map_unique typed_map)
  ensures active_token_registry #result #payload agreement_table registry
      (PT.proph_map_update (prophecy_id_of p) (reveal tail) typed_map) **
    prophecy_token_agreement p (reveal tail) **
    pure (PT.proph_map_lookup (prophecy_id_of p) typed_map == Some (reveal pvs))
  decreases registry
{
  match registry {
    [] -> {
      match typed_map {
        [] -> {
          assert pure (typed_map_descending_from #result #payload next []);
          assert pure (next == 0);
          assert pure (target_pid < 0);
          unreachable ()
        }
        typed_entry :: typed_tail -> {
          rewrite (active_token_registry #result #payload agreement_table [] (typed_entry :: typed_tail)) as pure False;
          unreachable ()
        }
      }
    }
    registry_entry :: registry_tail -> {
      let pid_r = registry_entry._1;
      let cell = registry_entry._2;
      match typed_map {
        [] -> {
          rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail) []) as pure False;
          unreachable ()
        }
        typed_entry :: typed_tail -> {
          let pid_t = typed_entry._1;
          let pvs_t = typed_entry._2;
          rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail) (typed_entry :: typed_tail)) as
            (GFT.pts_to agreement_table pid_t #0.5R pvs_t **
            pure (pid_r == pid_t /\
              cell.agreement_cell_table == agreement_table /\
              cell.agreement_cell_slot == pid_t) **
            active_token_registry #result #payload agreement_table registry_tail typed_tail);
          assert (GFT.pts_to agreement_table pid_t #0.5R pvs_t **
            pure (pid_r == pid_t /\
              cell.agreement_cell_table == agreement_table /\
              cell.agreement_cell_slot == pid_t) **
            active_token_registry #result #payload agreement_table registry_tail typed_tail **
            prophecy_token_agreement p (reveal pvs));
          assert pure (typed_map_descending_from #result #payload next ((pid_t, pvs_t) :: typed_tail));
          assert pure (next == pid_t + 1);
          assert pure (PT.proph_map_unique typed_tail);
          if (target_pid = pid_t) {
            rewrite (prophecy_token_agreement p (reveal pvs)) as
              (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal pvs) **
                pure (p.agreement_slot == prophecy_id_of p));
            assert pure ((prophecy_token_cell_of p).agreement_cell_table == agreement_table);
            assert pure ((prophecy_token_cell_of p).agreement_cell_slot == pid_t);
            rewrite each (prophecy_token_cell_of p).agreement_cell_table as agreement_table;
            rewrite each (prophecy_token_cell_of p).agreement_cell_slot as pid_t;
            GFT.gather #(PT.prediction_stream result payload) agreement_table pid_t #0.5R #0.5R #pvs_t #(reveal pvs);
            assert pure (pvs_t == reveal pvs);
            GFT.update #(PT.prediction_stream result payload) agreement_table #pid_t #pvs_t (reveal tail);
            GFT.share #(PT.prediction_stream result payload) agreement_table pid_t 0.5R 0.5R #1.0R #(reveal tail);
            rewrite (GFT.pts_to agreement_table pid_t #0.5R (reveal tail)) as
              (GFT.pts_to (prophecy_token_cell_of p).agreement_cell_table
                (prophecy_token_cell_of p).agreement_cell_slot #0.5R (reveal tail));
            assert (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal tail) **
              pure (p.agreement_slot == prophecy_id_of p));
            fold (prophecy_token_agreement p (reveal tail));
            assert pure (PT.proph_map_fresh pid_t typed_tail);
            PT.proph_map_update_fresh_noop pid_t (reveal tail) typed_tail;
            fold (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
              ((pid_t, reveal tail) :: typed_tail));
            rewrite (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
                ((pid_t, reveal tail) :: typed_tail)) as
              (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                ((pid_t, reveal tail) :: typed_tail));
            rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                ((pid_t, reveal tail) :: typed_tail)) as
              (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (PT.proph_map_update (prophecy_id_of p) (reveal tail) (typed_entry :: typed_tail)));
            rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (PT.proph_map_update (prophecy_id_of p) (reveal tail) (typed_entry :: typed_tail))) as
              (active_token_registry #result #payload agreement_table registry
                (PT.proph_map_update (prophecy_id_of p) (reveal tail) typed_map));
            assert pure (PT.proph_map_lookup (prophecy_id_of p) (typed_entry :: typed_tail) == Some (reveal pvs))
          } else {
            assert pure (target_pid < pid_t);
            assert pure (typed_map_descending_from #result #payload pid_t typed_tail);
            active_token_registry_resolve_agreement #result #payload agreement_table registry_tail typed_tail pid_t target_pid p #pvs #tail;
            fold (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
              ((pid_t, pvs_t) :: PT.proph_map_update (prophecy_id_of p) (reveal tail) typed_tail));
            rewrite (active_token_registry #result #payload agreement_table ((pid_r, cell) :: registry_tail)
                ((pid_t, pvs_t) :: PT.proph_map_update (prophecy_id_of p) (reveal tail) typed_tail)) as
              (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                ((pid_t, pvs_t) :: PT.proph_map_update (prophecy_id_of p) (reveal tail) typed_tail));
            rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                ((pid_t, pvs_t) :: PT.proph_map_update (prophecy_id_of p) (reveal tail) typed_tail)) as
              (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (PT.proph_map_update (prophecy_id_of p) (reveal tail) (typed_entry :: typed_tail)));
            rewrite (active_token_registry #result #payload agreement_table (registry_entry :: registry_tail)
                (PT.proph_map_update (prophecy_id_of p) (reveal tail) (typed_entry :: typed_tail))) as
              (active_token_registry #result #payload agreement_table registry
                (PT.proph_map_update (prophecy_id_of p) (reveal tail) typed_map));
            assert pure (PT.proph_map_lookup (prophecy_id_of p) (typed_entry :: typed_tail) == Some (reveal pvs))
          }
        }
      }
    }
  }
}

(** Coherent singleton/typed active prophecy state used by the public NewProph
    hidden-state cursor.

    Unlike the previous paired predicate, this shape owns only the concrete
    singleton [PWR.active_world_interp] state view.  The typed component is now
    carried as pure projection metadata rather than as a second spatial
    authority: decoder projection, decoder reflection for the active payload
    encoder, future trace, token-map keys, erased token-map stream values, typed
    map freshness facts, counters, and length must agree with the singleton
    through the same state-carried typed-to-nat projection adapter used to prove
    NewProph/Resolve token streams track the singleton [PW.list_resolves] /
    [PW.update] stream.  NewProph allocates the public token slot directly from
    the singleton-derived typed stream, and Resolve updates that slot directly
    after deriving the typed head/tail from the singleton map plus this pure
    projection/reflection boundary. *)
[@@pulse_unfold]
let active_prophecy_world_si (#result #payload:Type0)
    (ot:nat -> nat)
    (c:NST.ctr)
  : slprop
= exists* (auth:PWR.authority) (st:PW.state_view) (len:nat)
    (projection:active_prophecy_projection result payload).
    PWR.active_world_interp auth st ot c len **
    active_prophecy_projection_view projection **
    pure (active_component_projects_world #result #payload projection.projection_pack
      projection.projection_component st ot c len)

(** Token-indexed view of the same active singleton world.

    Resolve opens this strengthened view so the projection-table binding for the
    public token is carried by the active hidden-state resource itself, rather
    than by the remaining event/decode boundary.  It does not add a second
    authority: the spatial ownership is still exactly [PWR.active_world_interp]
    plus the non-authoritative projection/registry metadata. *)
[@@pulse_unfold]
let active_prophecy_world_si_for_token (#result #payload:Type0)
    (p:prophecy_var result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : slprop
= exists* (auth:PWR.authority) (st:PW.state_view) (len:nat)
    (projection:active_prophecy_projection result payload).
    PWR.active_world_interp auth st ot c len **
    active_prophecy_projection_view projection **
    pure (active_component_projects_world #result #payload projection.projection_pack
      projection.projection_component st ot c len /\
      p.agreement_table == projection.projection_agreement_table /\
      p.proph_payload_pack == projection.projection_pack)

ghost
fn prophecy_active_component_init (#result #payload:Type0)
    (#initial:erased (PT.proph_state_view_encoded result payload))
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (#len:erased nat)
  requires pure (PT.proph_state_interp_encoded (reveal initial) /\
    PT.proph_state_runtime_matches_ctr_encoded (reveal initial) (reveal ot) (reveal c) (reveal len))
  returns comp:prophecy_active_component result payload
  ensures prophecy_active_component_interp comp (reveal ot) (reveal c) **
    pure (comp.component_state_view == reveal initial /\ comp.component_len == reveal len)
{
  let len_v = reveal len;
  assert pure (PT.proph_state_interp_encoded (reveal initial));
  let auth = prophecy_authority_init #result #payload #initial;
  let comp = { component_authority = auth; component_state_view = reveal initial; component_len = len_v };
  assert_norm (comp.component_state_view == reveal initial);
  assert_norm (comp.component_len == len_v);
  assert (prophecy_authority_state auth (reveal initial) **
    pure (PT.proph_state_runtime_matches_ctr_encoded (reveal initial) (reveal ot) (reveal c) (reveal len)));
  rewrite (prophecy_authority_state auth (reveal initial) **
           pure (PT.proph_state_runtime_matches_ctr_encoded (reveal initial) (reveal ot) (reveal c) (reveal len))) as
          (prophecy_authority_runtime_state auth (reveal initial) (reveal ot) (reveal c) (reveal len));
  fold (prophecy_shared_state_interp auth (reveal initial) (reveal ot) (reveal c) (reveal len));
  rewrite (prophecy_shared_state_interp auth (reveal initial) (reveal ot) (reveal c) (reveal len)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view (reveal ot) (reveal c) comp.component_len);
  fold (prophecy_active_component_interp comp (reveal ot) (reveal c));
  comp
}

ghost
fn prophecy_active_component_alloc_obs_ctr_repr (#result #payload:Type0) (#s:Type0)
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
    let pvs = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let new_st = snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view) in
    prophecy_shared_state_interp comp.component_authority new_st (reveal ot) r._3 comp.component_len **
    prophecy_token_fragment p pvs **
    pure (r._1 == pid /\ r._2 == s0 /\ r._3 == NST.bump_prophecy (reveal c) /\
      prophecy_id_of p == pid /\ prophecy_bound_to_authority comp.component_authority p /\
      PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some pvs))
{
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  let p = prophecy_shared_state_interp_alloc_obs_ctr_repr #result #payload #s
    comp.component_authority #comp.component_state_view #ot #c #comp.component_len s0 t at;
  let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  let new_st = snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view);
  fold (prophecy_authority_state comp.component_authority new_st);
  fold (prophecy_authority_runtime_state comp.component_authority new_st (reveal ot) r._3 comp.component_len);
  fold (prophecy_shared_state_interp comp.component_authority new_st (reveal ot) r._3 comp.component_len);
  p
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
    let pvs = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) r._3 **
    prophecy_token_fragment p pvs **
    pure (r._1 == pid /\ r._2 == s0 /\ r._3 == NST.bump_prophecy (reveal c) /\
      comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs))
{
  let p = prophecy_active_component_alloc_obs_ctr_repr #result #payload #s comp #ot #c s0 t at;
  let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  assert_norm ((prophecy_active_component_after_alloc comp).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_alloc comp).component_len == comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority
            (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view))
            (reveal ot) r._3 comp.component_len) as
          (prophecy_shared_state_interp (prophecy_active_component_after_alloc comp).component_authority
            (prophecy_active_component_after_alloc comp).component_state_view
            (reveal ot) r._3 (prophecy_active_component_after_alloc comp).component_len);
  fold (prophecy_active_component_interp (prophecy_active_component_after_alloc comp) (reveal ot) r._3);
  assert_norm (prophecy_component_bound (prophecy_active_component_after_alloc comp) p == prophecy_bound_to_authority comp.component_authority p);
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_alloc comp) p
    (PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder
      (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace) ==
    (PT.proph_map_lookup (prophecy_id_of p)
      (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view)).encoded_token_map ==
      Some (PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder
        (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace)));
  p
}

ghost
fn prophecy_active_component_alloc_obs_ctr_component_frame (#result #payload:Type0) (#s:Type0)
    (comp:prophecy_active_component result payload)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (framed:prophecy_var result payload)
    (#framed_pvs:erased (PT.prediction_stream result payload))
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
    let pvs = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) r._3 **
    prophecy_token_fragment p pvs **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (r._1 == pid /\ r._2 == s0 /\ r._3 == NST.bump_prophecy (reveal c) /\
      comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs /\
      prophecy_component_bound comp' framed /\
      prophecy_component_lookup comp' framed (reveal framed_pvs)))
{
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len) as
          (prophecy_authority_runtime_state comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  let p = prophecy_authority_alloc_runtime_frame #result #payload comp.component_authority
    #comp.component_state_view #ot #c #comp.component_len framed #framed_pvs;
  PT.proph_state_alloc_fresh_repr_obs_ctr_authority_step_encoded #result #payload #s
    comp.component_state_view (reveal ot) (reveal c) comp.component_len s0 t at;
  let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  assert pure (r._3 == NST.bump_prophecy (reveal c));
  assert_norm ((prophecy_active_component_after_alloc comp).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_alloc comp).component_len == comp.component_len);
  rewrite (prophecy_authority_runtime_state comp.component_authority
            (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view))
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len) as
          (prophecy_shared_state_interp comp.component_authority
            (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view))
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority
            (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view))
            (reveal ot) r._3 comp.component_len) as
          (prophecy_shared_state_interp (prophecy_active_component_after_alloc comp).component_authority
            (prophecy_active_component_after_alloc comp).component_state_view
            (reveal ot) r._3 (prophecy_active_component_after_alloc comp).component_len);
  fold (prophecy_active_component_interp (prophecy_active_component_after_alloc comp) (reveal ot) r._3);
  assert_norm (prophecy_component_bound (prophecy_active_component_after_alloc comp) p == prophecy_bound_to_authority comp.component_authority p);
  assert_norm (prophecy_component_bound (prophecy_active_component_after_alloc comp) framed == prophecy_bound_to_authority comp.component_authority framed);
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_alloc comp) p
    (PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder
      (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace) ==
    (PT.proph_map_lookup (prophecy_id_of p)
      (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view)).encoded_token_map ==
      Some (PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder
        (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace)));
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_alloc comp) framed (reveal framed_pvs) ==
    (PT.proph_map_lookup (prophecy_id_of framed)
      (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view)).encoded_token_map == Some (reveal framed_pvs)));
  p
}

ghost
fn prophecy_active_component_resolve_obs_ctr_repr (#result #payload:Type0) (#s:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
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
  returns tail:erased (PT.prediction_stream result payload)
  ensures (
    let len_pos : (n:nat { n > 0 }) = comp.component_len in
    let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len_pos - 1) in
    let new_st = PT.proph_state_resolve_view_encoded comp.component_state_view (prophecy_id_of p) (reveal tail) ks in
    prophecy_shared_state_interp comp.component_authority new_st (reveal ot) r._3 (len_pos - 1) **
    prophecy_token_fragment p (reveal tail) **
    pure (r._1 == reveal ot (NST.observation_index (reveal c)) /\ r._2 == s0 /\
      r._3 == NST.bump_observation (reveal c) /\
      reveal pvs == (observed_result, payload_value) :: reveal tail /\
      PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)))
{
  assert pure (comp.component_len > 0);
  let len_pos : (n:nat { n > 0 }) = comp.component_len;
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  let tail = prophecy_shared_state_interp_resolve_obs_ctr_repr #result #payload #s
    comp.component_authority p payload_value #comp.component_state_view #ot #c #len_pos #pvs
    observed_result s0 t at;
  let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len_pos - 1);
  let new_st = PT.proph_state_resolve_view_encoded comp.component_state_view (prophecy_id_of p) (reveal tail) ks;
  fold (prophecy_authority_state comp.component_authority new_st);
  fold (prophecy_authority_runtime_state comp.component_authority new_st (reveal ot) r._3 (len_pos - 1));
  fold (prophecy_shared_state_interp comp.component_authority new_st (reveal ot) r._3 (len_pos - 1));
  tail
}

ghost
fn prophecy_active_component_resolve_current_component (#result #payload:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment p (reveal pvs) **
    pure (comp.component_len > 0 /\ prophecy_component_bound comp p /\
      prophecy_component_lookup comp p (reveal pvs) /\
      comp.component_state_view.encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (PT.prediction_stream result payload)
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
  assert pure (comp.component_len > 0);
  let len_pos : (n:nat { n > 0 }) = comp.component_len;
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  let tail = prophecy_shared_state_interp_resolve_current #result #payload
    comp.component_authority p payload_value #comp.component_state_view #ot #c #len_pos #pvs observed_result;
  let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len_pos - 1);
  let new_st = PT.proph_state_resolve_view_encoded comp.component_state_view (prophecy_id_of p) (reveal tail) ks;
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_state_view == new_st);
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_len == len_pos - 1);
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_state_view.encoded_decoder == comp.component_state_view.encoded_decoder);
  rewrite (prophecy_shared_state_interp comp.component_authority new_st (reveal ot) (NST.bump_observation (reveal c)) (len_pos - 1)) as
          (prophecy_shared_state_interp (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_authority
            (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_state_view
            (reveal ot) (NST.bump_observation (reveal c))
            (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_len);
  fold (prophecy_active_component_interp (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c))
    (reveal ot) (NST.bump_observation (reveal c)));
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)) p (reveal tail) ==
    (PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)));
  tail
}

(** Resolve helper used by the singleton-world public path.

    This is deliberately narrower than [prophecy_active_component_resolve_current_component]:
    [resolve_proph_token_finish_active] now uses the typed projection-registry
    lookup for the public token stream to derive the singleton erased lookup
    through the active projection/reflection invariant before calling this
    helper.  The actual token-table update and component authority update
    therefore do not need the legacy [prophecy_component_bound] fact tying the
    opaque handle's typed [state_table] fields to the component authority.  The
    singleton-world path already tracks the real authoritative world through
    [PWR.active_world_interp]; keeping [bound] and the direct singleton lookup
    out of the hidden precondition removes another p-specific witness while the
    remaining typed component exists only as the transitional token projection. *)
ghost
fn prophecy_active_component_resolve_current_component_projected (#result #payload:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment p (reveal pvs) **
    pure (comp.component_len > 0 /\
      prophecy_component_lookup comp p (reveal pvs) /\
      comp.component_state_view.encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value)))
  returns tail:erased (PT.prediction_stream result payload)
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
  assert pure (comp.component_len > 0);
  let len_pos : (n:nat { n > 0 }) = comp.component_len;
  let current_nat = reveal ot (NST.observation_index (reveal c));
  let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len_pos - 1);
  let tail0 = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder (prophecy_id_of p) ks;
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len) as
          (prophecy_authority_runtime_state comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  rewrite (prophecy_authority_runtime_state comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len) as
          (prophecy_authority_state comp.component_authority comp.component_state_view **
           pure (PT.proph_state_runtime_matches_ctr_encoded comp.component_state_view
             (reveal ot) (reveal c) comp.component_len));
  unfold prophecy_authority_state;
  unfold prophecy_token_fragment;
  assert_norm (prophecy_component_lookup comp p (reveal pvs) ==
    (PT.proph_map_lookup (prophecy_id_of p) comp.component_state_view.encoded_token_map == Some (reveal pvs)));
  assert (GFT.pts_to comp.component_authority.authority_table comp.component_authority.authority_slot #1.0R comp.component_state_view **
          GFT.pts_to p.token_table p.token_slot #1.0R (reveal pvs) **
          pure (PT.proph_state_interp_encoded comp.component_state_view /\
            PT.proph_state_runtime_matches_ctr_encoded comp.component_state_view (reveal ot) (reveal c) comp.component_len /\
            PT.proph_map_lookup (prophecy_id_of p) comp.component_state_view.encoded_token_map == Some (reveal pvs) /\
            comp.component_state_view.encoded_decoder current_nat ==
              Some (prophecy_id_of p, (observed_result, payload_value))));
  PT.proph_state_lookup_projected_current_head_encoded comp.component_state_view (prophecy_id_of p)
    (observed_result, payload_value) (reveal pvs) (reveal ot) (reveal c) len_pos;
  assert pure (reveal pvs == (observed_result, payload_value) :: tail0);
  PT.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) len_pos;
  assert pure (comp.component_state_view.encoded_future_trace == current_nat :: ks);
  PT.proph_state_resolve_authority_step_ctr_encoded comp.component_state_view (prophecy_id_of p)
    observed_result observed_result payload_value tail0 current_nat ks (reveal ot) (reveal c) len_pos;
  let new_st = PT.proph_state_resolve_view_encoded comp.component_state_view (prophecy_id_of p) tail0 ks;
  GFT.update p.token_table #p.token_slot #(reveal pvs) tail0;
  GFT.update comp.component_authority.authority_table #comp.component_authority.authority_slot #comp.component_state_view new_st;
  fold (prophecy_token_fragment p tail0);
  fold (prophecy_authority_state comp.component_authority new_st);
  rewrite (prophecy_authority_state comp.component_authority new_st **
           pure (PT.proph_state_runtime_matches_ctr_encoded new_st (reveal ot) (NST.bump_observation (reveal c)) (len_pos - 1))) as
          (prophecy_authority_runtime_state comp.component_authority new_st
            (reveal ot) (NST.bump_observation (reveal c)) (len_pos - 1));
  assert_norm ((prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)).component_state_view == new_st);
  assert_norm ((prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)).component_len == len_pos - 1);
  assert_norm ((prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)).component_state_view.encoded_decoder == comp.component_state_view.encoded_decoder);
  rewrite (prophecy_authority_runtime_state comp.component_authority new_st
            (reveal ot) (NST.bump_observation (reveal c)) (len_pos - 1)) as
          (prophecy_shared_state_interp comp.component_authority new_st
            (reveal ot) (NST.bump_observation (reveal c)) (len_pos - 1));
  rewrite (prophecy_shared_state_interp comp.component_authority new_st
            (reveal ot) (NST.bump_observation (reveal c)) (len_pos - 1)) as
          (prophecy_shared_state_interp (prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)).component_authority
            (prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)).component_state_view
            (reveal ot) (NST.bump_observation (reveal c))
            (prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)).component_len);
  fold (prophecy_active_component_interp (prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c))
    (reveal ot) (NST.bump_observation (reveal c)));
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_resolve comp p tail0 (reveal ot) (reveal c)) p tail0 ==
    (PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some tail0));
  hide tail0
}

ghost
fn active_prophecy_si_resolve_current_fragment (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (observed_result:result)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires (exists* (comp:prophecy_active_component result payload).
    prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment p (reveal pvs) **
    pure (comp.component_len > 0 /\ prophecy_component_bound comp p /\
      prophecy_component_lookup comp p (reveal pvs) /\
      comp.component_state_view.encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value))))
  returns tail:erased (PT.prediction_stream result payload)
  ensures active_prophecy_si #result #payload (reveal ot) (NST.bump_observation (reveal c)) **
    prophecy_token_fragment p (reveal tail) **
    pure (reveal pvs == (observed_result, payload_value) :: reveal tail)
{
  with comp. assert (prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment p (reveal pvs) **
    pure (comp.component_len > 0 /\ prophecy_component_bound comp p /\
      prophecy_component_lookup comp p (reveal pvs) /\
      comp.component_state_view.encoded_decoder (reveal ot (NST.observation_index (reveal c))) ==
        Some (prophecy_id_of p, (observed_result, payload_value))));
  assert pure (comp.component_len > 0);
  let tail = prophecy_active_component_resolve_current_component #result #payload comp p payload_value #pvs observed_result #ot #c;
  let comp' = prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c);
  rewrite (prophecy_active_component_interp (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c))
            (reveal ot) (NST.bump_observation (reveal c))) as
          (prophecy_active_component_interp comp' (reveal ot) (NST.bump_observation (reveal c)));
  introduce exists* (comp_out:prophecy_active_component result payload).
    prophecy_active_component_interp comp_out (reveal ot) (NST.bump_observation (reveal c)) with comp';
  rewrite (exists* (comp_out:prophecy_active_component result payload).
            prophecy_active_component_interp comp_out (reveal ot) (NST.bump_observation (reveal c))) as
          (active_prophecy_si #result #payload (reveal ot) (NST.bump_observation (reveal c)));
  tail
}

ghost
fn prophecy_active_component_resolve_obs_ctr_component (#result #payload:Type0) (#s:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
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
  returns tail:erased (PT.prediction_stream result payload)
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
  assert pure (comp.component_len > 0);
  let len_pos : (n:nat { n > 0 }) = comp.component_len;
  let tail = prophecy_active_component_resolve_obs_ctr_repr #result #payload #s comp p payload_value
    #pvs observed_result s0 t at #ot #c;
  let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  let ks = PT.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len_pos - 1);
  let new_st = PT.proph_state_resolve_view_encoded comp.component_state_view (prophecy_id_of p) (reveal tail) ks;
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_state_view == new_st);
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_len == len_pos - 1);
  assert_norm ((prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_state_view.encoded_decoder == comp.component_state_view.encoded_decoder);
  rewrite (prophecy_shared_state_interp comp.component_authority new_st (reveal ot) r._3 (len_pos - 1)) as
          (prophecy_shared_state_interp (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_authority
            (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_state_view
            (reveal ot) r._3 (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)).component_len);
  fold (prophecy_active_component_interp (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)) (reveal ot) r._3);
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_resolve comp p (reveal tail) (reveal ot) (reveal c)) p (reveal tail) ==
    (PT.proph_map_lookup (prophecy_id_of p) new_st.encoded_token_map == Some (reveal tail)));
  tail
}

(** NewProph allocation over an already-open active component.

    The checked helper below is the resource-level operation that a real
    state-interpretation/runner rule must perform after the executable
    [Pulse.Lib.Core.fresh_prophecy_id] cursor has returned the current
    [NST.prophecy_index].  It updates the active component with the verified
    counter-aware Trace lemma, returns the informative [prophecy_var] handle and
    a client token fragment, and closes the component at
    [NST.bump_prophecy c].

    Public [new_proph_semantic] no longer exposes an [emp ->
    prophecy_active_component_interp] opening and no longer calls a
    runner-owned projection primitive.  Until PulseCore owns [active_prophecy_si]
    in the instantiated adequacy state interpretation, public NewProph returns
    only the client fragment; this helper is the checked hidden-authority update
    that still needs to be wired into the active semantics. *)
fn prophecy_active_component_alloc_current_component (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    pure (pid == NST.prophecy_index (reveal c))
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) (NST.bump_prophecy (reveal c)) **
    prophecy_token_fragment p pvs **
    pure (comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs))
{
  assert pure (pid == NST.prophecy_index (reveal c));
  let pvs0 : PT.prediction_stream result payload =
    PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace;
  let new_st = snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view);
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len) as
          (prophecy_authority_runtime_state comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  rewrite (prophecy_authority_runtime_state comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len) as
          (prophecy_authority_state comp.component_authority comp.component_state_view **
           pure (PT.proph_state_runtime_matches_ctr_encoded comp.component_state_view
             (reveal ot) (reveal c) comp.component_len));
  unfold prophecy_authority_state;
  assert (GFT.pts_to comp.component_authority.authority_table comp.component_authority.authority_slot #1.0R comp.component_state_view **
          pure (PT.proph_state_interp_encoded comp.component_state_view /\
                PT.proph_state_runtime_matches_ctr_encoded comp.component_state_view (reveal ot) (reveal c) comp.component_len));
  PT.proph_state_alloc_fresh_authority_step_ctr_encoded comp.component_state_view (reveal ot) (reveal c) comp.component_len;
  let t = GFT.create #(PT.prediction_stream result payload);
  let slot : nat = 0;
  GFT.alloc t pvs0 #slot;
  drop_ (GFT.is_table t (slot + 1));
  GFT.update comp.component_authority.authority_table #comp.component_authority.authority_slot #comp.component_state_view new_st;
  let p = { proph_id_refinement = pid;
            proph_payload_pack = (fun (_:result) (_:payload) -> 0);
            token_table = t; token_slot = slot;
            agreement_table = t; agreement_slot = slot;
            state_table = comp.component_authority.authority_table;
            state_slot = comp.component_authority.authority_slot };
  assert_norm (p.proph_id_refinement == pid);
  assert_norm (p.token_table == t);
  assert_norm (p.token_slot == slot);
  assert_norm (p.agreement_table == t);
  assert_norm (p.agreement_slot == slot);
  assert_norm (p.state_table == comp.component_authority.authority_table);
  assert_norm (p.state_slot == comp.component_authority.authority_slot);
  rewrite (GFT.pts_to t slot #1.0R pvs0) as
          (GFT.pts_to p.token_table p.token_slot #1.0R pvs0);
  fold (prophecy_token_fragment p pvs0);
  fold (prophecy_authority_state comp.component_authority new_st);
  rewrite (prophecy_authority_state comp.component_authority new_st **
           pure (PT.proph_state_runtime_matches_ctr_encoded new_st (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len)) as
          (prophecy_authority_runtime_state comp.component_authority new_st
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len);
  rewrite (prophecy_authority_runtime_state comp.component_authority new_st
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len) as
          (prophecy_shared_state_interp comp.component_authority new_st
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len);
  assert_norm ((prophecy_active_component_after_alloc comp).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_alloc comp).component_state_view ==
    snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view));
  assert pure ((prophecy_active_component_after_alloc comp).component_state_view == new_st);
  assert_norm ((prophecy_active_component_after_alloc comp).component_len == comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority new_st
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len) as
          (prophecy_shared_state_interp (prophecy_active_component_after_alloc comp).component_authority
            (prophecy_active_component_after_alloc comp).component_state_view
            (reveal ot) (NST.bump_prophecy (reveal c))
            (prophecy_active_component_after_alloc comp).component_len);
  fold (prophecy_active_component_interp (prophecy_active_component_after_alloc comp)
    (reveal ot) (NST.bump_prophecy (reveal c)));
  assert_norm (prophecy_component_bound (prophecy_active_component_after_alloc comp) p ==
    prophecy_bound_to_authority comp.component_authority p);
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_alloc comp) p pvs0 ==
    (PT.proph_map_lookup (prophecy_id_of p)
      (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view)).encoded_token_map == Some pvs0));
  p
}

ghost
fn active_prophecy_si_alloc_obs_ctr_fragment (#result #payload:Type0) (#s:Type0)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  requires active_prophecy_si #result #payload (reveal ot) (reveal c)
  returns p:prophecy_var result payload
  ensures (
    let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c) in
    active_prophecy_si #result #payload (reveal ot) r._3 **
    (exists* (pvs:PT.prediction_stream result payload).
      prophecy_token_fragment p pvs **
      pure (r._1 == NST.prophecy_index (reveal c) /\
        r._3 == NST.bump_prophecy (reveal c) /\
        prophecy_id_of p == r._1)))
{
  rewrite (active_prophecy_si #result #payload (reveal ot) (reveal c)) as
          (exists* (comp:prophecy_active_component result payload).
            prophecy_active_component_interp comp (reveal ot) (reveal c));
  with comp. assert (prophecy_active_component_interp comp (reveal ot) (reveal c));
  let p = prophecy_active_component_alloc_obs_ctr_component #result #payload #s comp #ot #c s0 t at;
  let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at (reveal ot) (reveal c);
  let comp' = prophecy_active_component_after_alloc comp;
  let pvs0 = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder
    (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace;
  assert pure (r._1 == NST.prophecy_index (reveal c) /\
    r._3 == NST.bump_prophecy (reveal c) /\
    prophecy_id_of p == r._1);
  rewrite (prophecy_active_component_interp (prophecy_active_component_after_alloc comp)
            (reveal ot) r._3) as
          (prophecy_active_component_interp comp' (reveal ot) r._3);
  introduce exists* (comp_out:prophecy_active_component result payload).
    prophecy_active_component_interp comp_out (reveal ot) r._3 with comp';
  rewrite (exists* (comp_out:prophecy_active_component result payload).
            prophecy_active_component_interp comp_out (reveal ot) r._3) as
          (active_prophecy_si #result #payload (reveal ot) r._3);
  introduce exists* (pvs:PT.prediction_stream result payload).
    prophecy_token_fragment p pvs **
    pure (r._1 == NST.prophecy_index (reveal c) /\
      r._3 == NST.bump_prophecy (reveal c) /\
      prophecy_id_of p == r._1) with pvs0;
  p
}

ghost
fn active_prophecy_si_alloc_current_fragment (#result #payload:Type0)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires active_prophecy_si #result #payload (reveal ot) (reveal c) **
    pure (pid == NST.prophecy_index (reveal c))
  returns p:prophecy_var result payload
  ensures active_prophecy_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
    (exists* (pvs:PT.prediction_stream result payload).
      prophecy_token_fragment p pvs **
      pure (prophecy_id_of p == pid))
{
  rewrite (active_prophecy_si #result #payload (reveal ot) (reveal c)) as
          (exists* (comp:prophecy_active_component result payload).
            prophecy_active_component_interp comp (reveal ot) (reveal c));
  with comp. assert (prophecy_active_component_interp comp (reveal ot) (reveal c));
  assert pure (pid == NST.prophecy_index (reveal c));
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  let p = prophecy_shared_state_interp_alloc #result #payload comp.component_authority
    #comp.component_state_view #ot #c #comp.component_len;
  let comp' = prophecy_active_component_after_alloc comp;
  let pvs0 = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder
    (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace;
  assert pure (prophecy_id_of p == NST.prophecy_index (reveal c));
  assert pure (prophecy_id_of p == pid);
  assert_norm ((prophecy_active_component_after_alloc comp).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_alloc comp).component_state_view ==
    snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view));
  assert_norm ((prophecy_active_component_after_alloc comp).component_len == comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority
            (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view))
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len) as
          (prophecy_shared_state_interp comp'.component_authority comp'.component_state_view
            (reveal ot) (NST.bump_prophecy (reveal c)) comp'.component_len);
  fold (prophecy_active_component_interp comp' (reveal ot) (NST.bump_prophecy (reveal c)));
  introduce exists* (comp_out:prophecy_active_component result payload).
    prophecy_active_component_interp comp_out (reveal ot) (NST.bump_prophecy (reveal c)) with comp';
  rewrite (exists* (comp_out:prophecy_active_component result payload).
            prophecy_active_component_interp comp_out (reveal ot) (NST.bump_prophecy (reveal c))) as
          (active_prophecy_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)));
  introduce exists* (pvs:PT.prediction_stream result payload).
    prophecy_token_fragment p pvs ** pure (prophecy_id_of p == pid) with pvs0;
  p
}

ghost
fn active_prophecy_world_si_alloc_current_fragment (#result #payload:Type0)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires active_prophecy_world_si #result #payload (reveal ot) (reveal c) **
    pure (pid == NST.prophecy_index (reveal c))
  returns p:prophecy_var result payload
  ensures active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
    (exists* (pvs:PT.prediction_stream result payload).
      prophecy_token p pvs **
      pure (prophecy_id_of p == pid))
{
  rewrite (active_prophecy_world_si #result #payload (reveal ot) (reveal c)) as
          (exists* (auth:PWR.authority) (st:PW.state_view) (len:nat)
            (projection:active_prophecy_projection result payload).
            PWR.active_world_interp auth st (reveal ot) (reveal c) len **
            active_prophecy_projection_view projection **
            pure (active_component_projects_world #result #payload projection.projection_pack
              projection.projection_component st (reveal ot) (reveal c) len));
  with auth st len projection. assert (PWR.active_world_interp auth st (reveal ot) (reveal c) len **
    active_prophecy_projection_view projection);
  let comp = projection.projection_component;
  rewrite (active_prophecy_projection_view projection) as
    (GFT.is_table projection.projection_agreement_table
      comp.component_state_view.encoded_next_proph_id **
    active_token_registry #result #payload projection.projection_agreement_table
      projection.projection_registry comp.component_state_view.encoded_token_map);
  assert pure (active_component_projects_world #result #payload projection.projection_pack
    projection.projection_component st (reveal ot) (reveal c) len);
  assert pure (pid == NST.prophecy_index (reveal c));
  let pid_world = PWR.alloc_current auth #st #ot #c #len;
  assert pure (reveal pid_world == NST.prophecy_index (reveal c));
  assert pure (reveal pid_world == pid);
  let pvs0 = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder
    (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace;
  list_resolves_decoder_ext st.PW.world_decoder
    (PT.erase_encoded_decoder projection.projection_pack comp.component_state_view.encoded_decoder)
    (NST.prophecy_index (reveal c)) st.PW.world_future_trace;
  PT.erase_list_resolves_encoded projection.projection_pack comp.component_state_view.encoded_decoder
    (NST.prophecy_index (reveal c)) comp.component_state_view.encoded_future_trace;
  assert pure (PW.list_resolves st.PW.world_decoder (NST.prophecy_index (reveal c)) st.PW.world_future_trace ==
    PT.erase_prediction_stream projection.projection_pack pvs0);
  let t = GFT.create #(PT.prediction_stream result payload);
  let slot : nat = 0;
  GFT.alloc t pvs0 #slot;
  drop_ (GFT.is_table t (slot + 1));
  let agreement_slot : nat = pid;
  assert pure (agreement_slot == comp.component_state_view.encoded_next_proph_id);
  rewrite (GFT.is_table projection.projection_agreement_table comp.component_state_view.encoded_next_proph_id) as
    (GFT.is_table projection.projection_agreement_table agreement_slot);
  GFT.alloc projection.projection_agreement_table pvs0 #agreement_slot;
  GFT.share projection.projection_agreement_table agreement_slot 0.5R 0.5R #1.0R #pvs0;
  let agreement_t = projection.projection_agreement_table;
  let agreement_cell = { agreement_cell_table = agreement_t; agreement_cell_slot = agreement_slot };
  let p = { proph_id_refinement = pid;
            proph_payload_pack = projection.projection_pack;
            token_table = t; token_slot = slot;
            agreement_table = agreement_t; agreement_slot = agreement_slot;
            state_table = comp.component_authority.authority_table;
            state_slot = comp.component_authority.authority_slot };
  assert_norm (p.proph_id_refinement == pid);
  assert_norm (p.token_table == t);
  assert_norm (p.token_slot == slot);
  assert_norm (p.agreement_table == agreement_t);
  assert_norm (p.agreement_slot == agreement_slot);
  assert_norm (p.state_table == comp.component_authority.authority_table);
  assert_norm (p.state_slot == comp.component_authority.authority_slot);
  rewrite (GFT.pts_to t slot #1.0R pvs0) as
          (GFT.pts_to p.token_table p.token_slot #1.0R pvs0);
  fold (prophecy_token_fragment p pvs0);
  rewrite (GFT.pts_to projection.projection_agreement_table agreement_slot #0.5R pvs0) as
    (GFT.pts_to (prophecy_token_cell_of p).agreement_cell_table
      (prophecy_token_cell_of p).agreement_cell_slot #0.5R pvs0);
  assert pure (p.agreement_slot == prophecy_id_of p);
  fold (prophecy_token_agreement p pvs0);
  fold (prophecy_token p pvs0);
  assert pure (prophecy_id_of p == NST.prophecy_index (reveal c));
  assert pure (prophecy_id_of p == pid);
  let st' = PW.alloc_view st (NST.prophecy_index (reveal c));
  let comp' = prophecy_active_component_after_alloc comp;
  active_component_projects_world_after_alloc projection.projection_pack comp st (reveal ot) (reveal c) len pid;
  rewrite (PWR.active_world_interp auth (PW.alloc_view st (NST.prophecy_index (reveal c)))
            (reveal ot) (NST.bump_prophecy (reveal c)) len) as
          (PWR.active_world_interp auth st' (reveal ot) (NST.bump_prophecy (reveal c)) len);
  let projection' = hide ({ projection with
    projection_component = comp';
    projection_registry = (pid, agreement_cell) :: projection.projection_registry });
  assert_norm ((reveal projection').projection_component == comp');
  assert pure ((reveal projection').projection_registry == (pid, agreement_cell) :: projection.projection_registry);
  fold (active_token_registry #result #payload projection.projection_agreement_table ((pid, agreement_cell) :: projection.projection_registry)
    ((pid, pvs0) :: comp.component_state_view.encoded_token_map));
  rewrite (active_token_registry #result #payload projection.projection_agreement_table ((pid, agreement_cell) :: projection.projection_registry)
      ((pid, pvs0) :: comp.component_state_view.encoded_token_map)) as
    (active_token_registry #result #payload projection.projection_agreement_table ((pid, agreement_cell) :: projection.projection_registry)
      comp'.component_state_view.encoded_token_map);
  rewrite (active_token_registry #result #payload projection.projection_agreement_table ((pid, agreement_cell) :: projection.projection_registry)
      comp'.component_state_view.encoded_token_map) as
    (active_token_registry #result #payload (reveal projection').projection_agreement_table
      (reveal projection').projection_registry
      (reveal projection').projection_component.component_state_view.encoded_token_map);
  assert_norm ((reveal projection').projection_agreement_table == projection.projection_agreement_table);
  assert pure ((reveal projection').projection_component.component_state_view.encoded_next_proph_id == agreement_slot + 1);
  rewrite (GFT.is_table projection.projection_agreement_table (agreement_slot + 1)) as
    (GFT.is_table (reveal projection').projection_agreement_table
      (reveal projection').projection_component.component_state_view.encoded_next_proph_id);
  fold (active_prophecy_projection_view (reveal projection'));
  introduce exists* (auth_out:PWR.authority) (st_out:PW.state_view) (len_out:nat)
      (projection_out:active_prophecy_projection result payload).
    PWR.active_world_interp auth_out st_out (reveal ot) (NST.bump_prophecy (reveal c)) len_out **
    active_prophecy_projection_view projection_out **
    pure (active_component_projects_world #result #payload projection_out.projection_pack
      projection_out.projection_component st_out (reveal ot)
      (NST.bump_prophecy (reveal c)) len_out) with auth st' len (reveal projection');
  rewrite (exists* (auth_out:PWR.authority) (st_out:PW.state_view) (len_out:nat)
            (projection_out:active_prophecy_projection result payload).
            PWR.active_world_interp auth_out st_out (reveal ot) (NST.bump_prophecy (reveal c)) len_out **
            active_prophecy_projection_view projection_out **
            pure (active_component_projects_world #result #payload projection_out.projection_pack
              projection_out.projection_component st_out (reveal ot)
              (NST.bump_prophecy (reveal c)) len_out)) as
          (active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)));
  introduce exists* (pvs:PT.prediction_stream result payload).
    prophecy_token p pvs ** pure (prophecy_id_of p == pid) with pvs0;
  p
}

ghost
fn prophecy_active_component_alloc_current_component_frame (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
    (framed:prophecy_var result payload)
    (#framed_pvs:erased (PT.prediction_stream result payload))
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (pid == NST.prophecy_index (reveal c) /\
      prophecy_component_bound comp framed /\
      prophecy_id_of framed <> pid /\
      prophecy_component_lookup comp framed (reveal framed_pvs))
  returns p:prophecy_var result payload
  ensures (
    let pid = NST.prophecy_index (reveal c) in
    let pvs = PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace in
    let comp' = prophecy_active_component_after_alloc comp in
    prophecy_active_component_interp comp' (reveal ot) (NST.bump_prophecy (reveal c)) **
    prophecy_token_fragment p pvs **
    prophecy_token_fragment framed (reveal framed_pvs) **
    pure (comp'.component_authority == comp.component_authority /\
      comp'.component_state_view == snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view) /\
      comp'.component_len == comp.component_len /\
      prophecy_id_of p == pid /\ prophecy_component_bound comp' p /\
      prophecy_component_lookup comp' p pvs /\
      prophecy_component_bound comp' framed /\
      prophecy_component_lookup comp' framed (reveal framed_pvs)))
{
  assert pure (pid == NST.prophecy_index (reveal c));
  let pvs0 : PT.prediction_stream result payload =
    PT.proph_list_resolves_encoded comp.component_state_view.encoded_decoder pid comp.component_state_view.encoded_future_trace;
  let new_st = snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view);
  rewrite (prophecy_active_component_interp comp (reveal ot) (reveal c)) as
          (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len) as
          (prophecy_authority_runtime_state comp.component_authority comp.component_state_view
            (reveal ot) (reveal c) comp.component_len);
  assert_norm (prophecy_component_bound comp framed == prophecy_bound_to_authority comp.component_authority framed);
  assert_norm (prophecy_component_lookup comp framed (reveal framed_pvs) ==
    (PT.proph_map_lookup (prophecy_id_of framed) comp.component_state_view.encoded_token_map == Some (reveal framed_pvs)));
  let p = prophecy_authority_alloc_runtime_frame #result #payload comp.component_authority
    #comp.component_state_view #ot #c #comp.component_len framed #framed_pvs;
  assert_norm ((prophecy_active_component_after_alloc comp).component_authority == comp.component_authority);
  assert_norm ((prophecy_active_component_after_alloc comp).component_state_view ==
    snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view));
  assert pure ((prophecy_active_component_after_alloc comp).component_state_view == new_st);
  assert_norm ((prophecy_active_component_after_alloc comp).component_len == comp.component_len);
  rewrite (prophecy_authority_runtime_state comp.component_authority new_st
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len) as
          (prophecy_shared_state_interp comp.component_authority new_st
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len);
  rewrite (prophecy_shared_state_interp comp.component_authority new_st
            (reveal ot) (NST.bump_prophecy (reveal c)) comp.component_len) as
          (prophecy_shared_state_interp (prophecy_active_component_after_alloc comp).component_authority
            (prophecy_active_component_after_alloc comp).component_state_view
            (reveal ot) (NST.bump_prophecy (reveal c))
            (prophecy_active_component_after_alloc comp).component_len);
  fold (prophecy_active_component_interp (prophecy_active_component_after_alloc comp)
    (reveal ot) (NST.bump_prophecy (reveal c)));
  assert_norm (prophecy_component_bound (prophecy_active_component_after_alloc comp) p ==
    prophecy_bound_to_authority comp.component_authority p);
  assert_norm (prophecy_component_bound (prophecy_active_component_after_alloc comp) framed ==
    prophecy_bound_to_authority comp.component_authority framed);
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_alloc comp) p pvs0 ==
    (PT.proph_map_lookup (prophecy_id_of p)
      (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view)).encoded_token_map == Some pvs0));
  assert_norm (prophecy_component_lookup (prophecy_active_component_after_alloc comp) framed (reveal framed_pvs) ==
    (PT.proph_map_lookup (prophecy_id_of framed)
      (snd (PT.proph_state_alloc_fresh_view_encoded comp.component_state_view)).encoded_token_map == Some (reveal framed_pvs)));
  p
}

fn new_proph_semantic_active_component_after_cursor (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires prophecy_active_component_interp comp (reveal ot) (reveal c) **
    pure (pid == NST.prophecy_index (reveal c))
  returns p : prophecy_var result payload
  ensures prophecy_active_component_interp (prophecy_active_component_after_alloc comp)
      (reveal ot) (NST.bump_prophecy (reveal c)) **
    (exists* (pvs:PT.prediction_stream result payload). prophecy_token_fragment p pvs)
{
  prophecy_active_component_alloc_current_component #result #payload comp pid #ot #c
}

ghost
fn new_proph_semantic_hidden_state_alloc_core (#result #payload:Type0)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  requires active_prophecy_world_si #result #payload (reveal ot) (reveal c) **
    pure (pid == NST.prophecy_index (reveal c))
  returns p : prophecy_var result payload
  ensures active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
    (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs)
{
  assert pure (pid == NST.prophecy_index (reveal c));
  let p = active_prophecy_world_si_alloc_current_fragment #result #payload pid #ot #c;
  with pvs0. assert (prophecy_token p pvs0 ** pure (prophecy_id_of p == pid));
  introduce exists* (pvs_out:PT.prediction_stream result payload). prophecy_token p pvs_out with pvs0;
  p
}

ghost
fn new_proph_semantic_hidden_state_alloc_ghost (#result #payload:Type0)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased (c:NST.ctr{pid == NST.prophecy_index c}))
  requires active_prophecy_world_si #result #payload (reveal ot) (reveal c)
  returns p : prophecy_var result payload
  ensures active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
    (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs)
{
  assert pure (pid == NST.prophecy_index (reveal c));
  C.intro_pure (pid == NST.prophecy_index (reveal c)) ();
  assert (active_prophecy_world_si #result #payload (reveal ot) (reveal c) **
    pure (pid == NST.prophecy_index (reveal c)));
  let p = new_proph_semantic_hidden_state_alloc_core #result #payload pid #(hide (reveal ot)) #(hide (reveal c));
  p
}

let new_proph_semantic_hidden_state_alloc (#result #payload:Type0)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased (c:NST.ctr{pid == NST.prophecy_index c}))
  : stt (prophecy_var result payload)
      (active_prophecy_world_si #result #payload (reveal ot) (reveal c))
      (fun p -> active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
        (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs))
= C.lift_atomic
    (C.lift_ghost_neutral
      #(prophecy_var result payload)
      #emp_inames
      #(active_prophecy_world_si #result #payload (reveal ot) (reveal c))
      #(fun p -> active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
        (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs))
      (new_proph_semantic_hidden_state_alloc_ghost #result #payload pid #ot #c)
      (non_informative_prophecy_var #result #payload))

let new_proph_semantic_hidden_state_alloc_atomic (#result #payload:Type0)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased (c:NST.ctr{pid == NST.prophecy_index c}))
  : stt_atomic (prophecy_var result payload) #Neutral emp_inames
      (emp ** active_prophecy_world_si #result #payload (reveal ot) (reveal c))
      (fun p -> (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs) **
        active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)))
= C.sub_atomic
    #(prophecy_var result payload)
    #Neutral
    #emp_inames
    #(active_prophecy_world_si #result #payload (reveal ot) (reveal c))
    (emp ** active_prophecy_world_si #result #payload (reveal ot) (reveal c))
    #(fun p -> active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
      (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs))
    (fun p -> (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs) **
      active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)))
    (C.slprop_equiv_sym
      (emp ** active_prophecy_world_si #result #payload (reveal ot) (reveal c))
      (active_prophecy_world_si #result #payload (reveal ot) (reveal c))
      (C.slprop_equiv_unit (active_prophecy_world_si #result #payload (reveal ot) (reveal c))))
    (C.intro_slprop_post_equiv
      (fun p -> active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
        (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs))
      (fun p -> (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs) **
        active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)))
      (fun p -> C.slprop_equiv_comm
        (active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)))
        (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs)))
    (C.lift_ghost_neutral
      #(prophecy_var result payload)
      #emp_inames
      #(active_prophecy_world_si #result #payload (reveal ot) (reveal c))
      #(fun p -> active_prophecy_world_si #result #payload (reveal ot) (NST.bump_prophecy (reveal c)) **
        (exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs))
      (new_proph_semantic_hidden_state_alloc_ghost #result #payload pid #ot #c)
      (non_informative_prophecy_var #result #payload))

let new_proph_semantic_post (#result #payload:Type0)
    (p:prophecy_var result payload)
  : slprop
= exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs

let resolve_proph_token_semantic_post (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (pvs:PT.prediction_stream result payload)
    (post:result -> slprop)
    (x:result)
  : slprop
= post x **
  (exists* (tail:PT.prediction_stream result payload).
    prophecy_token p tail ** pure (pvs == (x, payload_value) :: tail))

let new_proph_semantic (#result #payload:Type0) ()
  : stt (prophecy_var result payload)
      emp
      (new_proph_semantic_post #result #payload)
= C.fresh_prophecy_id_with_hidden_si_state_action
    #(prophecy_var result payload)
    #(active_prophecy_world_si #result #payload)
    #(new_proph_semantic_post #result #payload)
    (fun pid #ot #c -> new_proph_semantic_hidden_state_alloc_atomic #result #payload pid #ot #c)

(** Adequacy-facing active execution certificate for the public
    [new_proph_semantic] lowering.

    This is the NewProph counterpart to
    [resolve_proph_token_semantic_active_run]: it reuses the exact allocation
    callback used by [new_proph_semantic] and dispatches it through the active
    FreshProph runner rather than through the ordinary counter-erased
    [FreshProphIdWithHiddenState*] branches, which remain conservative.  The
    checked callback opens [active_prophecy_world_si], calls
    [PWR.alloc_current] through [active_prophecy_world_si_alloc_current_fragment],
    allocates the public token from the singleton future suffix, and closes at
    [NST.bump_prophecy c]. *)
let new_proph_semantic_active_run (#result #payload:Type0) ()
  : C.fresh_prophecy_id_active_run_result
      #(prophecy_var result payload)
      (new_proph_semantic_post #result #payload)
      (active_prophecy_world_si #result #payload)
      emp
      1
= C.fresh_prophecy_id_with_hidden_si_state_action_active_run
    #(prophecy_var result payload)
    #(active_prophecy_world_si #result #payload)
    #(new_proph_semantic_post #result #payload)
    (fun pid #ot #c -> new_proph_semantic_hidden_state_alloc_atomic #result #payload pid #ot #c)
    emp
    1


(** Resolve target-fixed native event decoder fact is now exposed by
    [PulseCore.Action.observed_result_targeted_resolve_event_decoder_fact].
    The checked finisher below consumes that abstract active-runner receipt
    after opening [PWR.active_world_interp], then performs all token-tail and
    singleton-world updates locally. *)
let resolve_proph_token_current_observation_from_consumed_decoder (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (x:result)
    (consumed_nat:nat)
    (st:PW.state_view)
    (projection:active_prophecy_projection result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : Lemma
    (requires consumed_nat == ot (NST.observation_index c) /\
      st.PW.world_decoder consumed_nat ==
        Some { PW.proph = prophecy_id_of p; PW.payload = projection.projection_pack x payload_value })
    (ensures PW.current_observation_decodes_to st ot c
      (prophecy_id_of p) (projection.projection_pack x payload_value))
= ()

ghost
fn resolve_proph_token_finish_active_unit (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#post:result -> slprop)
    (x:result)
    (consumed_nat:nat)
    (#ot:erased (nat -> nat))
    (#c:erased (c:NST.ctr{consumed_nat == (reveal ot) (NST.observation_index c)}))
    (#event:erased (A.observed_result_targeted_resolve_event #result #payload consumed_nat (reveal ot) (reveal c) p.proph_payload_pack (prophecy_id_of p) payload_value x))
  : C.stt_ghost unit emp_inames
      ((post x ** prophecy_token p (reveal pvs)) **
        active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c))
      (fun _ -> (post x **
        (exists* (tail:PT.prediction_stream result payload).
          prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail))) **
        active_prophecy_world_si_for_token #result #payload p (reveal ot) (NST.bump_observation (reveal c)))
= {
  rewrite (active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c)) as
    (exists* (auth:PWR.authority) (st:PW.state_view) (len:nat)
      (projection:active_prophecy_projection result payload).
      PWR.active_world_interp auth st (reveal ot) (reveal c) len **
      active_prophecy_projection_view projection **
      pure (active_component_projects_world #result #payload projection.projection_pack
        projection.projection_component st (reveal ot) (reveal c) len /\
        p.agreement_table == projection.projection_agreement_table /\
        p.proph_payload_pack == projection.projection_pack));
  with auth st len projection. assert (PWR.active_world_interp auth st (reveal ot) (reveal c) len **
    active_prophecy_projection_view projection);
  rewrite (active_prophecy_projection_view projection) as
    (GFT.is_table projection.projection_agreement_table
      projection.projection_component.component_state_view.encoded_next_proph_id **
    active_token_registry #result #payload projection.projection_agreement_table
      projection.projection_registry
      projection.projection_component.component_state_view.encoded_token_map);
  unfold prophecy_token;
  assert (prophecy_token_fragment p (reveal pvs) ** prophecy_token_agreement p (reveal pvs));
  assert pure (active_component_projects_world #result #payload projection.projection_pack
    projection.projection_component st (reveal ot) (reveal c) len);
  assert pure (consumed_nat == (reveal ot) (NST.observation_index (reveal c)));
  assert pure (p.agreement_table == projection.projection_agreement_table);
  assert pure (p.proph_payload_pack == projection.projection_pack);
  assert pure (p.agreement_slot == prophecy_id_of p);
  rewrite (prophecy_token_agreement p (reveal pvs)) as
    (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal pvs) **
      pure (p.agreement_slot == prophecy_id_of p));
  rewrite (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal pvs)) as
    (GFT.pts_to p.agreement_table p.agreement_slot #0.5R (reveal pvs));
  rewrite (GFT.pts_to p.agreement_table p.agreement_slot #0.5R (reveal pvs)) as
    (GFT.pts_to projection.projection_agreement_table (prophecy_id_of p) #0.5R (reveal pvs));
  GFT.in_bounds #(PT.prediction_stream result payload) projection.projection_agreement_table
    #(prophecy_id_of p) #0.5R #(reveal pvs)
    #projection.projection_component.component_state_view.encoded_next_proph_id;
  assert pure (prophecy_id_of p < projection.projection_component.component_state_view.encoded_next_proph_id);
  rewrite (GFT.pts_to projection.projection_agreement_table (prophecy_id_of p) #0.5R (reveal pvs)) as
    (GFT.pts_to (prophecy_token_cell_of p).agreement_cell_table
      (prophecy_token_cell_of p).agreement_cell_slot #0.5R (reveal pvs));
  fold (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal pvs));
  assert (prophecy_token_cell_fragment (prophecy_token_cell_of p) (reveal pvs) **
    pure (p.agreement_slot == prophecy_id_of p));
  fold (prophecy_token_agreement p (reveal pvs));
  assert pure (prophecy_token_bound_to_projection #result #payload p projection);
  assert pure (typed_map_descending_from #result #payload
    projection.projection_component.component_state_view.encoded_next_proph_id
    projection.projection_component.component_state_view.encoded_token_map);
  active_token_registry_lookup_agreement #result #payload projection.projection_agreement_table
    projection.projection_registry
    projection.projection_component.component_state_view.encoded_token_map
    projection.projection_component.component_state_view.encoded_next_proph_id
    (prophecy_id_of p) p #pvs;
  assert pure (prophecy_component_lookup projection.projection_component p (reveal pvs));
  rewrite (PWR.active_world_interp auth st (reveal ot) (reveal c) len) as
          (PWR.authority_state auth st **
           pure (PW.state_interp st /\ PW.runtime_matches_ctr st (reveal ot) (reveal c) len));
  assert pure (PW.state_interp st /\ PW.runtime_matches_ctr st (reveal ot) (reveal c) len);
  A.observed_result_targeted_resolve_event_decoder_fact #result #payload
    consumed_nat (reveal ot) (reveal c) p.proph_payload_pack (prophecy_id_of p)
    payload_value x (reveal event) st len;
  assert pure (p.proph_payload_pack == projection.projection_pack);
  assert pure (p.proph_payload_pack x payload_value == projection.projection_pack x payload_value);
  assert pure (st.PW.world_decoder consumed_nat ==
    Some { PW.proph = prophecy_id_of p; PW.payload = projection.projection_pack x payload_value });
  fold (PWR.active_world_interp auth st (reveal ot) (reveal c) len);
  resolve_proph_token_current_observation_from_consumed_decoder #result #payload p payload_value x
    consumed_nat st projection (reveal ot) (reveal c);
  rewrite (PWR.active_world_interp auth st (reveal ot) (reveal c) len) as
          (PWR.authority_state auth st **
           pure (PW.state_interp st /\ PW.runtime_matches_ctr st (reveal ot) (reveal c) len));
  assert pure (PW.state_interp st /\ PW.runtime_matches_ctr st (reveal ot) (reveal c) len);
  assert pure (PW.current_observation_decodes_to st (reveal ot) (reveal c)
    (prophecy_id_of p) (projection.projection_pack x payload_value));
  PW.current_observation_decodes_to_implies_len_pos st (reveal ot) (reveal c) len
    (prophecy_id_of p) (projection.projection_pack x payload_value);
  assert pure (len > 0);
  fold (PWR.active_world_interp auth st (reveal ot) (reveal c) len);
  assert pure (consumed_nat == (reveal ot) (NST.observation_index (reveal c)));
  assert pure (PW.current_observation_decodes_to st (reveal ot) (reveal c)
    (prophecy_id_of p) (projection.projection_pack x payload_value));
  assert pure (st.PW.world_decoder ((reveal ot) (NST.observation_index (reveal c))) ==
    Some { PW.proph = prophecy_id_of p; PW.payload = projection.projection_pack x payload_value });
  assert pure (st.PW.world_decoder consumed_nat ==
    Some { PW.proph = prophecy_id_of p; PW.payload = projection.projection_pack x payload_value });
  assert pure (decoder_reflects_world_pack #result #payload projection.projection_pack
    projection.projection_component.component_state_view.encoded_decoder st.PW.world_decoder);
  assert pure (projection.projection_component.component_state_view.encoded_decoder consumed_nat ==
    Some (prophecy_id_of p, (x, payload_value)));
  assert pure (projection.projection_component.component_state_view.encoded_decoder ((reveal ot) (NST.observation_index (reveal c))) ==
    Some (prophecy_id_of p, (x, payload_value)));
  assert pure (decoder_projects_world_pack #result #payload projection.projection_pack
    projection.projection_component.component_state_view.encoded_decoder st.PW.world_decoder);
  assert pure (st.PW.world_decoder ((reveal ot) (NST.observation_index (reveal c))) ==
    PT.erase_encoded_decoder projection.projection_pack
      projection.projection_component.component_state_view.encoded_decoder
      ((reveal ot) (NST.observation_index (reveal c))));
  assert pure (PT.erase_encoded_decoder projection.projection_pack
      projection.projection_component.component_state_view.encoded_decoder
      ((reveal ot) (NST.observation_index (reveal c))) ==
    Some { PW.proph = prophecy_id_of p; PW.payload = projection.projection_pack x payload_value });
  assert pure (projection.projection_component.component_len == len);
  assert pure (projection.projection_component.component_len > 0);
  assert pure (p.agreement_table == projection.projection_agreement_table);
  assert pure (p.agreement_slot == prophecy_id_of p);
  assert pure (prophecy_id_of p < projection.projection_component.component_state_view.encoded_next_proph_id);
  assert pure (typed_map_descending_from #result #payload
    projection.projection_component.component_state_view.encoded_next_proph_id
    projection.projection_component.component_state_view.encoded_token_map);
  assert pure (prophecy_component_lookup projection.projection_component p (reveal pvs));
  assert pure (token_maps_project projection.projection_pack
    projection.projection_component.component_state_view.encoded_token_map st.PW.world_token_map);
  assert pure (token_maps_streams_reflect #result #payload projection.projection_pack
    projection.projection_component.component_state_view.encoded_token_map);
  token_maps_project_lookup projection.projection_pack (prophecy_id_of p)
    projection.projection_component.component_state_view.encoded_token_map st.PW.world_token_map (reveal pvs);
  assert pure (PW.lookup (prophecy_id_of p) st.PW.world_token_map ==
    Some (PT.erase_prediction_stream projection.projection_pack (reveal pvs)));
  token_maps_streams_reflect_lookup projection.projection_pack (prophecy_id_of p)
    projection.projection_component.component_state_view.encoded_token_map (reveal pvs);
  assert pure (prediction_stream_erasure_reflects #result #payload projection.projection_pack (reveal pvs));
  assert pure (PW.current_observation_decodes_to st (reveal ot) (reveal c)
    (prophecy_id_of p) (projection.projection_pack x payload_value));
  assert pure (PW.state_interp st /\ PW.runtime_matches_ctr st (reveal ot) (reveal c) len);
  assert pure (len > 0);
  world_state_lookup_projected_current_head st (reveal ot) (reveal c) len
    (prophecy_id_of p) (projection.projection_pack x payload_value)
    (PT.erase_prediction_stream projection.projection_pack (reveal pvs));
  let world_tail = hide (PW.list_resolves st.PW.world_decoder (prophecy_id_of p)
    (PW.trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len - 1)));
  assert pure (PT.erase_prediction_stream projection.projection_pack (reveal pvs) ==
    projection.projection_pack x payload_value :: reveal world_tail);
  prediction_stream_erasure_reflects_head projection.projection_pack (reveal pvs) x payload_value (reveal world_tail);
  let tail = hide (prediction_stream_tail (reveal pvs));
  assert pure (reveal pvs == (x, payload_value) :: reveal tail);
  assert pure (PT.erase_prediction_stream projection.projection_pack (reveal pvs) ==
    projection.projection_pack x payload_value :: PT.erase_prediction_stream projection.projection_pack (reveal tail));
  assert pure (PT.erase_prediction_stream projection.projection_pack (reveal tail) == reveal world_tail);
  assert pure (PW.lookup (prophecy_id_of p) st.PW.world_token_map ==
    Some (projection.projection_pack x payload_value :: PT.erase_prediction_stream projection.projection_pack (reveal tail)));
  active_token_registry_resolve_agreement #result #payload projection.projection_agreement_table
    projection.projection_registry
    projection.projection_component.component_state_view.encoded_token_map
    projection.projection_component.component_state_view.encoded_next_proph_id
    (prophecy_id_of p) p #pvs #tail;
  unfold prophecy_token_fragment;
  GFT.update p.token_table #p.token_slot #(reveal pvs) (reveal tail);
  fold (prophecy_token_fragment p (reveal tail));
  fold (prophecy_token p (reveal tail));
  let erased_tail = hide (PT.erase_prediction_stream projection.projection_pack (reveal tail));
  PWR.resolve_current auth #(hide st) #(hide (reveal ot)) #(hide (reveal c)) #(hide len)
    (prophecy_id_of p) (projection.projection_pack x payload_value) #erased_tail;
  assert pure (reveal erased_tail == PT.erase_prediction_stream projection.projection_pack (reveal tail));
  rewrite (PWR.active_world_interp auth
            (PW.resolve_view st (prophecy_id_of p) (reveal erased_tail)
              (PW.trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len - 1)))
            (reveal ot) (NST.bump_observation (reveal c)) (len - 1)) as
          (PWR.active_world_interp auth
            (PW.resolve_view st (prophecy_id_of p) (PT.erase_prediction_stream projection.projection_pack (reveal tail))
              (PW.trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len - 1)))
            (reveal ot) (NST.bump_observation (reveal c)) (len - 1));
  active_component_projects_world_after_resolve projection.projection_pack projection.projection_component st (reveal ot) (reveal c)
    len p (reveal pvs) x payload_value (PT.erase_prediction_stream projection.projection_pack (reveal tail)) (reveal tail);
  let projection' = hide ({ projection with projection_component = prophecy_active_component_after_resolve projection.projection_component p (reveal tail) (reveal ot) (reveal c) });
  assert_norm ((reveal projection').projection_registry == projection.projection_registry);
  rewrite (active_token_registry #result #payload projection.projection_agreement_table projection.projection_registry
      (PT.proph_map_update (prophecy_id_of p) (reveal tail) projection.projection_component.component_state_view.encoded_token_map)) as
    (active_token_registry #result #payload (reveal projection').projection_agreement_table
      (reveal projection').projection_registry
      (reveal projection').projection_component.component_state_view.encoded_token_map);
  assert_norm ((reveal projection').projection_agreement_table == projection.projection_agreement_table);
  assert_norm ((reveal projection').projection_pack == projection.projection_pack);
  assert pure (p.proph_payload_pack == (reveal projection').projection_pack);
  assert pure ((reveal projection').projection_component.component_state_view.encoded_next_proph_id ==
    projection.projection_component.component_state_view.encoded_next_proph_id);
  rewrite (GFT.is_table projection.projection_agreement_table
      projection.projection_component.component_state_view.encoded_next_proph_id) as
    (GFT.is_table (reveal projection').projection_agreement_table
      (reveal projection').projection_component.component_state_view.encoded_next_proph_id);
  fold (active_prophecy_projection_view (reveal projection'));
  introduce exists* (auth_out:PWR.authority) (st_out:PW.state_view) (len_out:nat)
      (projection_out:active_prophecy_projection result payload).
    PWR.active_world_interp auth_out st_out (reveal ot) (NST.bump_observation (reveal c)) len_out **
    active_prophecy_projection_view projection_out **
    pure (active_component_projects_world #result #payload projection_out.projection_pack
      projection_out.projection_component st_out (reveal ot)
      (NST.bump_observation (reveal c)) len_out /\
      p.agreement_table == projection_out.projection_agreement_table /\
      p.proph_payload_pack == projection_out.projection_pack) with auth
      (PW.resolve_view st (prophecy_id_of p) (PT.erase_prediction_stream projection.projection_pack (reveal tail))
        (PW.trace_of_tape (reveal ot) (NST.observation_index (reveal c) + 1) (len - 1)))
      (len - 1)
      (reveal projection');
  rewrite (exists* (auth_out:PWR.authority) (st_out:PW.state_view) (len_out:nat)
            (projection_out:active_prophecy_projection result payload).
            PWR.active_world_interp auth_out st_out (reveal ot) (NST.bump_observation (reveal c)) len_out **
            active_prophecy_projection_view projection_out **
            pure (active_component_projects_world #result #payload projection_out.projection_pack
              projection_out.projection_component st_out (reveal ot)
              (NST.bump_observation (reveal c)) len_out /\
              p.agreement_table == projection_out.projection_agreement_table /\
              p.proph_payload_pack == projection_out.projection_pack)) as
          (active_prophecy_world_si_for_token #result #payload p (reveal ot) (NST.bump_observation (reveal c)));
  ()
}

fn resolve_proph_token_finish_active (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#post:result -> slprop)
    (x:result)
    (consumed_nat:nat)
    (#ot:erased (nat -> nat))
    (#c:erased (c:NST.ctr{consumed_nat == (reveal ot) (NST.observation_index c)}))
    (#event:erased (A.observed_result_targeted_resolve_event #result #payload consumed_nat (reveal ot) (reveal c) p.proph_payload_pack (prophecy_id_of p) payload_value x))
  : stt result
      ((post x ** prophecy_token p (reveal pvs)) **
        active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c))
      (fun y -> (post y **
        (exists* (tail:PT.prediction_stream result payload).
          prophecy_token p tail ** pure (reveal pvs == (y, payload_value) :: tail))) **
        active_prophecy_world_si_for_token #result #payload p (reveal ot) (NST.bump_observation (reveal c)))
= {
  resolve_proph_token_finish_active_unit #result #payload p payload_value #pvs #post x consumed_nat #ot #c #event;
  x
}

let resolve_proph_token_finish_active_neutral (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#post:result -> slprop)
    (x:result)
    (consumed_nat:nat)
    (#ot:erased (nat -> nat))
    (#c:erased (c:NST.ctr{consumed_nat == (reveal ot) (NST.observation_index c)}))
    (#event:erased (A.observed_result_targeted_resolve_event #result #payload consumed_nat (reveal ot) (reveal c) p.proph_payload_pack (prophecy_id_of p) payload_value x))
  : stt_atomic unit #Neutral emp_inames
      ((post x ** prophecy_token p (reveal pvs)) **
        active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c))
      (fun _ -> (post x **
        (exists* (tail:PT.prediction_stream result payload).
          prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail))) **
        active_prophecy_world_si_for_token #result #payload p (reveal ot) (NST.bump_observation (reveal c)))
= C.lift_ghost_neutral
    #unit
    #emp_inames
    #((post x ** prophecy_token p (reveal pvs)) **
      active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c))
    #(fun _ -> (post x **
      (exists* (tail:PT.prediction_stream result payload).
        prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail))) **
      active_prophecy_world_si_for_token #result #payload p (reveal ot) (NST.bump_observation (reveal c)))
    (resolve_proph_token_finish_active_unit #result #payload p payload_value #pvs #post x consumed_nat #ot #c #event)
    NonInformative.non_informative_unit

let resolve_proph_token_semantic (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : stt result
      (prophecy_token p (reveal pvs) ** pre)
      (fun x -> post x **
        (exists* (tail:PT.prediction_stream result payload).
          prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail)))
= let framed = C.frame_atomic (prophecy_token p (reveal pvs)) (f ()) in
  let framed = C.sub_atomic (prophecy_token p (reveal pvs) ** pre)
    (fun x -> post x ** prophecy_token p (reveal pvs))
    (C.slprop_equiv_comm pre (prophecy_token p (reveal pvs)))
    (C.intro_slprop_post_equiv
       (fun x -> post x ** prophecy_token p (reveal pvs))
       (fun x -> post x ** prophecy_token p (reveal pvs))
       (fun x -> C.slprop_equiv_refl (post x ** prophecy_token p (reveal pvs))))
    framed
  in
  C.lift_targeted_post_result_observed_result_hidden_state_action
    #result #payload #(hide p.proph_payload_pack) #(hide (prophecy_id_of p)) #(hide payload_value)
    #(prophecy_token p (reveal pvs) ** pre)
    #(fun x -> post x **
      (exists* (tail:PT.prediction_stream result payload).
        prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail)))
    #(active_prophecy_world_si_for_token #result #payload p)
    (fun observed_nat #ot #c #receipt ->
      assert (observed_nat == (reveal ot) (NST.observation_index (reveal c)));
      let physical = C.frame_atomic
        (active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c))
        framed in
      (| (fun x -> post x ** prophecy_token p (reveal pvs)),
         physical,
         (fun x #event ->
           resolve_proph_token_finish_active_neutral #result #payload p payload_value
             #pvs #post x observed_nat #ot #c #event) |))

(** Adequacy-facing active execution certificate for the public
    [resolve_proph_token_semantic] lowering.

    This is not another public Resolve wrapper: it reuses the exact callback
    body used by [resolve_proph_token_semantic] and dispatches it through
    [C.observed_result_targeted_post_result_hidden_state_action_active_run].  Consequently
    adequacy proofs can package the public Resolve shape for the Ret-specialized
    active observed-result runner, whose counter postcondition is
    [NST.bump_observation c0] when concretely executed, rather than handing the constructor to ordinary
    [PulseCore.Semantics.run], whose hidden-state branches remain conservative.
    The remaining trusted slice is deliberately visible at the single
    conversion from the Action-level native Resolve certificate below: this
    certificate proves active-runner dispatch/unreachability while the checked
    finisher remains responsible for token-tail update and [PWR.resolve_current]. *)
let resolve_proph_token_semantic_active_run (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : C.observed_result_active_run_result
      #result
      (prophecy_token p (reveal pvs) ** pre)
      (resolve_proph_token_semantic_post #result #payload p payload_value (reveal pvs) post)
      (active_prophecy_world_si_for_token #result #payload p)
      emp
      1
= let framed = C.frame_atomic (prophecy_token p (reveal pvs)) (f ()) in
  let framed = C.sub_atomic (prophecy_token p (reveal pvs) ** pre)
    (fun x -> post x ** prophecy_token p (reveal pvs))
    (C.slprop_equiv_comm pre (prophecy_token p (reveal pvs)))
    (C.intro_slprop_post_equiv
       (fun x -> post x ** prophecy_token p (reveal pvs))
       (fun x -> post x ** prophecy_token p (reveal pvs))
       (fun x -> C.slprop_equiv_refl (post x ** prophecy_token p (reveal pvs))))
    framed
  in
  C.observed_result_targeted_post_result_hidden_state_action_active_run
    #result #payload #(hide p.proph_payload_pack) #(hide (prophecy_id_of p)) #(hide payload_value)
    #(prophecy_token p (reveal pvs) ** pre)
    #(resolve_proph_token_semantic_post #result #payload p payload_value (reveal pvs) post)
    #(active_prophecy_world_si_for_token #result #payload p)
    (fun observed_nat #ot #c #receipt ->
      assert (observed_nat == (reveal ot) (NST.observation_index (reveal c)));
      let physical = C.frame_atomic
        (active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c))
        framed in
      (| (fun x -> post x ** prophecy_token p (reveal pvs)),
         physical,
         (fun x #event ->
           resolve_proph_token_finish_active_neutral #result #payload p payload_value
             #pvs #post x observed_nat #ot #c #event) |))
    emp
    1


fn resolve_proph_semantic (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pred:erased result)
    (#tail:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  requires prophecy_token p ((reveal pred, payload_value) :: reveal tail) ** pre
  returns x : result
  ensures post x ** prophecy_token p (reveal tail) ** pure (x == reveal pred)
{
  let x = resolve_proph_token_semantic #result #payload p payload_value
            #((reveal pred, payload_value) :: reveal tail) #pre #post f;
  with tail'. assert (prophecy_token p tail' **
                      pure (((reveal pred, payload_value) :: reveal tail) ==
                            (x, payload_value) :: tail'));
  assert pure (x == reveal pred);
  assert pure (tail' == reveal tail);
  rewrite each tail' as (reveal tail);
  x
}

(** Narrow Resolve/open-invariant presentation boundary.

    The public atomic Resolve rule now presents the same active Ret-specialized
    [ObservedResultActWithHiddenStateReturnAction] shape directly through the
    core observed-result hidden-state presentation shim, rather than coercing an
    arbitrary [stt] proof with a local generic atomic coercion.  The remaining
    trusted scope is therefore only the atomic presentation of this one active
    observed-result action: the callback below still runs the physical
    observable action, calls the checked token-pop/[PWR.resolve_current]
    finisher (where the remaining opened-world event boundary is confined),
    and closes the token-indexed active singleton view at
    [NST.bump_observation c]. *)
let resolve_proph_token_active_atomic_presentation (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : stt_atomic result #Observable emp_inames
      (prophecy_token p (reveal pvs) ** pre)
      (fun x -> post x **
        (exists* (tail:PT.prediction_stream result payload).
          prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail)))
= let framed = C.frame_atomic (prophecy_token p (reveal pvs)) (f ()) in
  let framed = C.sub_atomic (prophecy_token p (reveal pvs) ** pre)
    (fun x -> post x ** prophecy_token p (reveal pvs))
    (C.slprop_equiv_comm pre (prophecy_token p (reveal pvs)))
    (C.intro_slprop_post_equiv
       (fun x -> post x ** prophecy_token p (reveal pvs))
       (fun x -> post x ** prophecy_token p (reveal pvs))
       (fun x -> C.slprop_equiv_refl (post x ** prophecy_token p (reveal pvs))))
    framed
  in
  C.lift_atomic_targeted_post_result_observed_result_hidden_state_action_atomic
    #result #payload #(hide p.proph_payload_pack) #(hide (prophecy_id_of p)) #(hide payload_value)
    #(prophecy_token p (reveal pvs) ** pre)
    #(fun x -> post x **
      (exists* (tail:PT.prediction_stream result payload).
        prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail)))
    #(active_prophecy_world_si_for_token #result #payload p)
    (fun observed_nat #ot #c #receipt ->
      assert (observed_nat == (reveal ot) (NST.observation_index (reveal c)));
      let physical = C.frame_atomic
        (active_prophecy_world_si_for_token #result #payload p (reveal ot) (reveal c))
        framed in
      (| (fun x -> post x ** prophecy_token p (reveal pvs)),
         physical,
         (fun x #event ->
           resolve_proph_token_finish_active_neutral #result #payload p payload_value
             #pvs #post x observed_nat #ot #c #event) |))

let resolve_proph_token (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pvs:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : stt_atomic result #Observable emp_inames
      (prophecy_token p (reveal pvs) ** pre)
      (fun x -> post x **
        (exists* (tail:PT.prediction_stream result payload).
          prophecy_token p tail ** pure (reveal pvs == (x, payload_value) :: tail)))
= resolve_proph_token_active_atomic_presentation #result #payload p payload_value #pvs #pre #post f

atomic fn resolve_proph (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pred:erased result)
    (#tail:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  requires prophecy_token p ((reveal pred, payload_value) :: reveal tail) ** pre
  returns x : result
  ensures post x ** prophecy_token p (reveal tail) ** pure (x == reveal pred)
{
  let x = resolve_proph_token #result #payload p payload_value
            #((reveal pred, payload_value) :: reveal tail) #pre #post f;
  with tail'. assert (prophecy_token p tail' **
                      pure (((reveal pred, payload_value) :: reveal tail) ==
                            (x, payload_value) :: tail'));
  assert pure (x == reveal pred);
  assert pure (tail' == reveal tail);
  rewrite each tail' as (reveal tail);
  x
}

(* ================================================================ *)
(* LL — load-linked (model: same as atomic read)                    *)
(* ================================================================ *)

fn ll_impl (#a:eqtype) (r : B.box a) (#v : erased a) (#p:perm)
  preserves r |-> Frac p v
  returns x : a
  ensures rewrites_to x (reveal v)
{ B.op_Bang r }

let ll (#a:eqtype) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_atomic a #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))
  = Pulse.Lib.Core.as_atomic _ _ (ll_impl r #v #p)

(* ================================================================ *)
(* SC — store-conditional (model: same as CAS)                      *)
(* ================================================================ *)

fn sc_impl (#a:eqtype) (r : B.box a) (new_val : a) (expected : a) (#cur : erased a)
  requires r |-> cur
  returns b : bool
  ensures cond b (r |-> new_val ** pure (reveal cur == expected))
                 (r |-> cur)
{
  let v = B.op_Bang r;
  if (v = expected) {
    B.op_Colon_Equals r new_val;
    fold (cond true (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    true
  } else {
    fold (cond false (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    false
  }
}

let sc (#a:eqtype) (r : B.box a) (new_val : a) (expected : a) (#cur : erased a)
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))
  = Pulse.Lib.Core.as_atomic _ _ (sc_impl r new_val expected #cur)

