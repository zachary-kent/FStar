(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Pure observation-trace model for Iris-style prophecy variables.

    This module is intentionally pure: it does not claim to provide the
    executable Pulse state interpretation or the trusted Resolve primitive.  It
    records the trace/state-interpretation shape that those foundational pieces
    must expose before the user-facing prophecy API can be fully Iris-faithful.
    PulseCore now has a nat-encoded observation oracle, ObservedAct and
    result-dependent ObservedResultAct nodes, and explicit observation-cursor
    bump facts; this file includes both the representation-agnostic packed model
    and the typed decoder/projection bridge for that core observation tape.

    Iris heap_lang observations have the shape
      prophecy id ↦ (result of the resolved atomic step, attached value).
    Allocation gives a prophecy token whose future stream is the projection
    of the global observation trace to the freshly allocated id.  The compact
    state-view models below carry the fresh-id counter, token map, future
    observation suffix, and (for the nat-encoded PulseCore bridge) observation
    index.  Resolving a prophecy is not a post-hoc ghost update: the
    operational step emits and consumes the next observation, and agreement
    comes from the coupled state interpretation.
 *)
module Pulse.Lib.Prophecy.Trace

module NST = PulseCore.NondeterministicHoareStateMonad
module PW = PulseCore.ProphecyWorld

open FStar.List.Tot

(** Prophecy identifiers.  The eventual operational allocation primitive must
    allocate a fresh identifier and seed its token from the global trace. *)
type proph_id = nat

(** One operational observation produced by a Resolve step.
    [result] is the value returned by the atomic step being wrapped; [payload]
    is the value supplied to Resolve to disambiguate success/failure branches
    (as in Iris's CmpXchg examples). *)
noeq
type observation (res_t:Type0) (payload_t:Type0) = {
  proph   : proph_id;
  result  : res_t;
  payload : payload_t;
}

let trace (result payload:Type0) = list (observation result payload)
let prediction_stream (result payload:Type0) = list (result & payload)

(** Pulse/F* lacks HeapLang's single untyped [val] universe.  A faithful global
    trace therefore has to store observations heterogeneously and expose typed
    projections through a trusted decoder for each typed prophecy interface.
    The decoder is the seam where a future foundational implementation can use
    type tags, dynamic boxes, or an indexed state interpretation; the pure model
    below is independent of that representation choice. *)
noeq
type packed_observation =
  | PackObservation : result:Type0 -> payload:Type0 -> proph_id -> result -> payload -> packed_observation

let global_trace = list packed_observation
let decoded_observation (result payload:Type0) = proph_id & (result & payload)
let observation_decoder (result payload:Type0) = packed_observation -> option (decoded_observation result payload)
let proph_map (result payload:Type0) = list (proph_id & prediction_stream result payload)

let obs_pair #result #payload (o:observation result payload) : result & payload =
  (o.result, o.payload)

(** [proph_list_resolves pid ks] is the Iris [proph_list_resolves] projection:
    all future observations in [ks] for [pid], preserving trace order. *)
let rec proph_list_resolves #result #payload
    (pid:proph_id)
    (ks:trace result payload)
  : Tot (prediction_stream result payload)
    (decreases ks)
= match ks with
  | [] -> []
  | o :: ks' ->
    if o.proph = pid
    then obs_pair o :: proph_list_resolves pid ks'
    else proph_list_resolves pid ks'

(** The allocation view that an Iris-faithful [NewProph] rule exposes. *)
let alloc_view #result #payload
    (pid:proph_id)
    (ks:trace result payload)
  : prediction_stream result payload
= proph_list_resolves pid ks

(** The local token update performed after the coupled operational Resolve
    consumes the head prediction.  If the stream is empty, Resolve cannot
    produce the required agreement. *)
let consume_prediction #result #payload
    (pvs:prediction_stream result payload)
  : option ((result & payload) & prediction_stream result payload)
= match pvs with
  | [] -> None
  | pv :: pvs' -> Some (pv, pvs')

(** The global trace step required for a Resolve of [pid].  The next global
    observation must be for the prophecy being resolved; the returned pair is
    the equality witness that clients may reason about before the step. *)
let resolve_head #result #payload
    (pid:proph_id)
    (ks:trace result payload)
  : option ((result & payload) & trace result payload)
= match ks with
  | [] -> None
  | o :: ks' ->
    if o.proph = pid
    then Some (obs_pair o, ks')
    else None

(** Coupling predicate expected of the future state interpretation: the token's
    prediction stream is exactly the projection of the global observation
    trace for its prophecy id. *)
let view_coupled #result #payload
    (pid:proph_id)
    (ks:trace result payload)
    (pvs:prediction_stream result payload)
  : prop
= pvs == proph_list_resolves pid ks

(** Typed projection from the heterogeneous global trace.  The trusted decoder
    returns [None] for observations belonging to other typed prophecy
    interfaces and [Some (pid, (result, payload))] for observations of this
    interface. *)
let rec proph_list_resolves_global #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (ks:global_trace)
  : Tot (prediction_stream result payload)
    (decreases ks)
= match ks with
  | [] -> []
  | o :: ks' ->
    match decode o with
    | None -> proph_list_resolves_global decode pid ks'
    | Some (pid', pv) ->
      if pid' = pid
      then pv :: proph_list_resolves_global decode pid ks'
      else proph_list_resolves_global decode pid ks'

let view_coupled_global #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (ks:global_trace)
    (pvs:prediction_stream result payload)
  : prop
= pvs == proph_list_resolves_global decode pid ks

(** Bridge to the PulseCore observation oracle.

    [PulseCore.NondeterministicHoareStateMonad.observe] and
    [PulseCore.Semantics.ObservedAct] keep the runtime observation tape
    nat-encoded so core semantics do not depend on a particular value universe.
    A typed prophecy interface supplies an encoded decoder, exactly analogous to
    the packed-observation decoder above.  The finite list model below is the
    per-type projection of a future suffix of that core observation tape. *)
let encoded_global_trace = list nat
let encoded_observation_decoder (result payload:Type0) = nat -> option (decoded_observation result payload)

let rec proph_list_resolves_encoded #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
  : Tot (prediction_stream result payload)
    (decreases ks)
= match ks with
  | [] -> []
  | n :: ks' ->
    match decode n with
    | None -> proph_list_resolves_encoded decode pid ks'
    | Some (pid', pv) ->
      if pid' = pid
      then pv :: proph_list_resolves_encoded decode pid ks'
      else proph_list_resolves_encoded decode pid ks'

(** Typed prophecy interfaces are projections of the core untyped singleton
    world.  A client-specific [pack] function erases a typed observed
    [(result, payload)] pair to the nat payload stored in
    [PulseCore.ProphecyWorld].  The lemma below is the representation bridge
    that lets future NewProph/Resolve rules allocate/update the core-owned
    singleton while exposing typed prediction streams as fragments. *)
let erase_encoded_decoder #result #payload
    (pack:result -> payload -> nat)
    (decode:encoded_observation_decoder result payload)
  : PW.decoder
= fun n ->
  match decode n with
  | None -> None
  | Some (pid, (r, p)) ->
    let o : PW.observation = { proph = pid; payload = pack r p } in
    Some o

let rec erase_prediction_stream #result #payload
    (pack:result -> payload -> nat)
    (pvs:prediction_stream result payload)
  : Tot PW.prediction_stream
    (decreases pvs)
= match pvs with
  | [] -> []
  | (r, p) :: pvs' -> pack r p :: erase_prediction_stream pack pvs'

let rec erase_list_resolves_encoded #result #payload
    (pack:result -> payload -> nat)
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
  : Lemma
    (ensures PW.list_resolves (erase_encoded_decoder pack decode) pid ks ==
             erase_prediction_stream pack (proph_list_resolves_encoded decode pid ks))
    (decreases ks)
= match ks with
  | [] -> ()
  | n :: ks' ->
    erase_list_resolves_encoded pack decode pid ks';
    match decode n with
    | None -> ()
    | Some (pid', (r, p)) -> ()

let view_coupled_encoded #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
    (pvs:prediction_stream result payload)
  : prop
= pvs == proph_list_resolves_encoded decode pid ks

let resolve_head_encoded #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
  : option ((result & payload) & encoded_global_trace)
= match ks with
  | [] -> None
  | n :: ks' ->
    match decode n with
    | Some (pid', pv) -> if pid' = pid then Some (pv, ks') else None
    | None -> None

let resolve_head_encoded_couples #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (pv:result & payload)
    (n:nat)
    (ks:encoded_global_trace)
  : Lemma
    (requires decode n == Some (pid, pv))
    (ensures proph_list_resolves_encoded decode pid (n :: ks) ==
             pv :: proph_list_resolves_encoded decode pid ks)
= ()

let resolve_head_encoded_frames_other #result #payload
    (decode:encoded_observation_decoder result payload)
    (resolved_pid:proph_id)
    (pid:proph_id)
    (pv:result & payload)
    (n:nat)
    (ks:encoded_global_trace)
  : Lemma
    (requires decode n == Some (resolved_pid, pv) /\ pid <> resolved_pid)
    (ensures proph_list_resolves_encoded decode pid (n :: ks) ==
             proph_list_resolves_encoded decode pid ks)
= ()

(** Encoded future suffix exposed by the PulseCore observation oracle.
    [encoded_trace_of_tape ot start len] is the finite prefix of the oracle
    suffix starting at [start].  Adequacy can quantify over [len] (or use a
    coinductive/infinite analogue) while the single-step Resolve rule below
    only needs the head/tail shape. *)
let rec encoded_trace_of_tape
    (ot:nat -> nat)
    (start:nat)
    (len:nat)
  : Tot encoded_global_trace
    (decreases len)
= if len = 0 then [] else ot start :: encoded_trace_of_tape ot (start + 1) (len - 1)

let encoded_trace_of_tape_cons
    (ot:nat -> nat)
    (start:nat)
    (len:nat)
  : Lemma
    (requires len > 0)
    (ensures encoded_trace_of_tape ot start len ==
             ot start :: encoded_trace_of_tape ot (start + 1) (len - 1))
= ()

(** A pure [proph_map_interp] analogue: every token stream recorded in the
    prophecy map is the typed projection of the same future global trace. *)
let rec proph_map_interp #result #payload
    (decode:observation_decoder result payload)
    (ks:global_trace)
    (m:proph_map result payload)
  : Tot prop
    (decreases m)
= match m with
  | [] -> True
  | (pid, pvs) :: m' ->
    view_coupled_global decode pid ks pvs /\ proph_map_interp decode ks m'

let rec proph_map_contains #result #payload
    (pid:proph_id)
    (m:proph_map result payload)
  : Tot bool
    (decreases m)
= match m with
  | [] -> false
  | (pid', _) :: m' -> pid = pid' || proph_map_contains pid m'

let rec proph_map_lookup #result #payload
    (pid:proph_id)
    (m:proph_map result payload)
  : Tot (option (prediction_stream result payload))
    (decreases m)
= match m with
  | [] -> None
  | (pid', pvs) :: m' -> if pid = pid' then Some pvs else proph_map_lookup pid m'

let rec proph_map_update #result #payload
    (pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Tot (proph_map result payload)
    (decreases m)
= match m with
  | [] -> []
  | (pid', pvs') :: m' ->
    if pid = pid'
    then (pid', pvs) :: proph_map_update pid pvs m'
    else (pid', pvs') :: proph_map_update pid pvs m'

let proph_map_fresh #result #payload
    (pid:proph_id)
    (m:proph_map result payload)
  : prop
= proph_map_contains pid m == false

let rec proph_map_unique #result #payload
    (m:proph_map result payload)
  : Tot prop
    (decreases m)
= match m with
  | [] -> True
  | (pid, _) :: m' -> proph_map_fresh pid m' /\ proph_map_unique m'

(** [proph_map_bounded next m] records the fresh-id discipline expected from
    a first-class runtime prophecy state: every allocated prophecy id in the
    authoritative map is strictly below [next].  Consequently [next] is fresh
    for allocation.  This is the pure counterpart of Iris's freshness side
    condition for [NewProph]. *)
let rec proph_map_bounded #result #payload
    (next:proph_id)
    (m:proph_map result payload)
  : Tot prop
    (decreases m)
= match m with
  | [] -> True
  | (pid, _) :: m' -> pid < next /\ proph_map_bounded next m'

let rec proph_map_bounded_fresh #result #payload
    (next:proph_id)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_bounded next m)
    (ensures proph_map_fresh next m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid, _) :: m' ->
    assert (pid <> next);
    proph_map_bounded_fresh next m'

let rec proph_map_bounded_monotone #result #payload
    (old_next:proph_id)
    (new_next:proph_id)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_bounded old_next m /\ old_next <= new_next)
    (ensures proph_map_bounded new_next m)
    (decreases m)
= match m with
  | [] -> ()
  | _ :: m' -> proph_map_bounded_monotone old_next new_next m'

let rec proph_map_update_preserves_bounded #result #payload
    (next:proph_id)
    (updated_pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_bounded next m)
    (ensures proph_map_bounded next (proph_map_update updated_pid pvs m))
    (decreases m)
= match m with
  | [] -> ()
  | _ :: m' -> proph_map_update_preserves_bounded next updated_pid pvs m'

let proph_map_alloc_fresh_preserves_bounded #result #payload
    (next:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_bounded next m)
    (ensures proph_map_bounded (next + 1) ((next, pvs) :: m))
= proph_map_bounded_monotone next (next + 1) m

let rec proph_map_update_fresh_noop #result #payload
    (pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_fresh pid m)
    (ensures proph_map_update pid pvs m == m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' ->
    assert (pid <> pid');
    assert (proph_map_fresh pid m');
    proph_map_update_fresh_noop pid pvs m'

let rec proph_map_contains_update #result #payload
    (updated_pid:proph_id)
    (pvs:prediction_stream result payload)
    (queried_pid:proph_id)
    (m:proph_map result payload)
  : Lemma
    (ensures proph_map_contains queried_pid (proph_map_update updated_pid pvs m) ==
             proph_map_contains queried_pid m)
    (decreases m)
= match m with
  | [] -> ()
  | _ :: m' -> proph_map_contains_update updated_pid pvs queried_pid m'

let proph_map_lookup_alloc_same #result #payload
    (pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (ensures proph_map_lookup pid ((pid, pvs) :: m) == Some pvs)
= ()

let proph_map_lookup_alloc_other #result #payload
    (fresh_pid:proph_id)
    (queried_pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires queried_pid <> fresh_pid)
    (ensures proph_map_lookup queried_pid ((fresh_pid, pvs) :: m) == proph_map_lookup queried_pid m)
= ()

let rec proph_map_lookup_update_same #result #payload
    (pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_contains pid m == true)
    (ensures proph_map_lookup pid (proph_map_update pid pvs m) == Some pvs)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' ->
    if pid = pid'
    then ()
    else proph_map_lookup_update_same pid pvs m'

let rec proph_map_lookup_update_other #result #payload
    (updated_pid:proph_id)
    (queried_pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires queried_pid <> updated_pid)
    (ensures proph_map_lookup queried_pid (proph_map_update updated_pid pvs m) ==
             proph_map_lookup queried_pid m)
    (decreases m)
= match m with
  | [] -> ()
  | _ :: m' -> proph_map_lookup_update_other updated_pid queried_pid pvs m'

let rec proph_map_lookup_some_contains #result #payload
    (pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_lookup pid m == Some pvs)
    (ensures proph_map_contains pid m == true)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' ->
    if pid = pid'
    then ()
    else proph_map_lookup_some_contains pid pvs m'

let proph_map_lookup_update_same_from_lookup #result #payload
    (pid:proph_id)
    (old_pvs pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_lookup pid m == Some old_pvs)
    (ensures proph_map_lookup pid (proph_map_update pid pvs m) == Some pvs)
= proph_map_lookup_some_contains pid old_pvs m;
  proph_map_lookup_update_same pid pvs m

let rec proph_map_update_preserves_unique #result #payload
    (updated_pid:proph_id)
    (pvs:prediction_stream result payload)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_unique m)
    (ensures proph_map_unique (proph_map_update updated_pid pvs m))
    (decreases m)
= match m with
  | [] -> ()
  | (pid, _) :: m' ->
    assert (proph_map_unique m');
    proph_map_update_preserves_unique updated_pid pvs m';
    proph_map_contains_update updated_pid pvs pid m'

(** Nat-encoded [proph_map_interp] analogue.  This is the representation that
    matches [PulseCore.NondeterministicHoareStateMonad.observe] and
    [PulseCore.Semantics.ObservedAct]: every typed prophecy token stream is a
    projection of the same shared future observation suffix. *)
let rec proph_map_interp_encoded #result #payload
    (decode:encoded_observation_decoder result payload)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Tot prop
    (decreases m)
= match m with
  | [] -> True
  | (pid, pvs) :: m' ->
    view_coupled_encoded decode pid ks pvs /\ proph_map_interp_encoded decode ks m'

let proph_map_alloc_encoded #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : proph_map result payload
= (pid, proph_list_resolves_encoded decode pid ks) :: m

let proph_map_alloc_encoded_lookup #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Lemma
    (ensures proph_map_lookup pid (proph_map_alloc_encoded decode pid ks m) ==
             Some (proph_list_resolves_encoded decode pid ks))
= proph_map_lookup_alloc_same pid (proph_list_resolves_encoded decode pid ks) m

let proph_map_alloc_encoded_preserves_interp #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp_encoded decode ks m /\ proph_map_fresh pid m)
    (ensures proph_map_interp_encoded decode ks (proph_map_alloc_encoded decode pid ks m))
= ()

let rec proph_map_resolve_encoded_frames_fresh #result #payload
    (decode:encoded_observation_decoder result payload)
    (resolved_pid:proph_id)
    (pv:result & payload)
    (n:nat)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp_encoded decode (n :: ks) m /\
              decode n == Some (resolved_pid, pv) /\
              proph_map_fresh resolved_pid m)
    (ensures proph_map_interp_encoded decode ks m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid, pvs) :: m' ->
    assert (pid <> resolved_pid);
    resolve_head_encoded_frames_other decode resolved_pid pid pv n ks;
    assert (proph_map_interp_encoded decode (n :: ks) m');
    assert (proph_map_fresh resolved_pid m');
    proph_map_resolve_encoded_frames_fresh decode resolved_pid pv n ks m';
    ()

let rec proph_map_resolve_encoded_preserves_interp #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (pv:result & payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp_encoded decode (n :: ks) m /\
              decode n == Some (pid, pv) /\
              proph_map_lookup pid m == Some (pv :: tail) /\
              proph_map_unique m)
    (ensures proph_map_interp_encoded decode ks (proph_map_update pid tail m))
    (decreases m)
= match m with
  | [] -> ()
  | (pid', pvs') :: m' ->
    if pid = pid'
    then (
      assert (pvs' == pv :: tail);
      resolve_head_encoded_couples decode pid pv n ks;
      assert (tail == proph_list_resolves_encoded decode pid ks);
      assert (proph_map_fresh pid m');
      assert (proph_map_interp_encoded decode (n :: ks) m');
      proph_map_resolve_encoded_frames_fresh decode pid pv n ks m';
      proph_map_update_fresh_noop pid tail m';
      assert (proph_map_update pid tail m' == m');
      ()
    )
    else (
      assert (pid' <> pid);
      assert (proph_map_interp_encoded decode (n :: ks) m');
      assert (proph_map_lookup pid m' == Some (pv :: tail));
      assert (proph_map_unique m');
      resolve_head_encoded_frames_other decode pid pid' pv n ks;
      proph_map_resolve_encoded_preserves_interp decode pid pv tail n ks m';
      ()
    )

(** Agreement fact for the public head-supplied Resolve rule.  If the active
    observation tape decodes the next observation as the physical result
    [(observed, payload_value)] for [pid], and the authoritative prophecy map
    says the client's token head is [(pred, payload_value)], then the result
    agrees with the prediction.  This is the pure equality proof used by the
    trusted Resolve boundary; no post-hoc ghost write is involved. *)
let rec proph_map_observed_head_agrees_encoded #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp_encoded decode (n :: ks) m /\
              decode n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid m == Some ((pred, payload_value) :: tail))
    (ensures observed == pred)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', pvs') :: m' ->
    if pid = pid'
    then (
      assert (pvs' == (pred, payload_value) :: tail);
      resolve_head_encoded_couples decode pid (observed, payload_value) n ks;
      assert (pvs' == proph_list_resolves_encoded decode pid (n :: ks));
      assert (proph_list_resolves_encoded decode pid (n :: ks) ==
              (observed, payload_value) :: proph_list_resolves_encoded decode pid ks);
      assert ((pred, payload_value) == (observed, payload_value));
      ()
    )
    else (
      assert (pid' <> pid);
      assert (proph_map_interp_encoded decode (n :: ks) m');
      assert (proph_map_lookup pid m' == Some ((pred, payload_value) :: tail));
      proph_map_observed_head_agrees_encoded decode pid observed pred payload_value tail n ks m'
    )

(** If the shared future suffix begins with an observation for [pid], then any
    authoritative map lookup for [pid] must expose that observation as the head
    of the looked-up token stream.  This lets the primitive boundary trust only
    the current observation head/decode fact; the token-tail shape follows from
    [proph_map_interp_encoded] rather than from a separate witness. *)
let rec proph_map_lookup_projected_head_encoded #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (pv:result & payload)
    (pvs:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp_encoded decode (n :: ks) m /\
              decode n == Some (pid, pv) /\
              proph_map_lookup pid m == Some pvs)
    (ensures pvs == pv :: proph_list_resolves_encoded decode pid ks)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', pvs') :: m' ->
    if pid = pid'
    then (
      assert (pvs' == pvs);
      resolve_head_encoded_couples decode pid pv n ks;
      assert (pvs' == proph_list_resolves_encoded decode pid (n :: ks));
      ()
    )
    else (
      assert (pid' <> pid);
      assert (proph_map_interp_encoded decode (n :: ks) m');
      assert (proph_map_lookup pid m' == Some pvs);
      proph_map_lookup_projected_head_encoded decode pid pv pvs n ks m'
    )

(** A compact state-interpretation slice using the same nat-encoded
    observation representation as PulseCore.  This is the preferred scaffold
    for closing the remaining trusted gap in [Pulse.Lib.AtomicPrimitives]: an
    instantiated semantic state can store [future_trace] as the suffix of the
    observation oracle, [encoded_next_proph_id] as the allocation counter, and
    [encoded_observation_index] as the oracle index consumed by [ObservedAct].
    Resolve consumes the suffix head while the token map is updated by
    [proph_map_resolve_encoded_preserves_interp]. *)
noeq
type proph_state_view_encoded (result payload:Type0) = {
  encoded_decoder : encoded_observation_decoder result payload;
  encoded_future_trace : encoded_global_trace;
  encoded_token_map : proph_map result payload;
  encoded_next_proph_id : proph_id;
  encoded_observation_index : nat;
}

let proph_state_interp_encoded #result #payload
    (st:proph_state_view_encoded result payload)
  : prop
= proph_map_interp_encoded st.encoded_decoder st.encoded_future_trace st.encoded_token_map /\
  proph_map_unique st.encoded_token_map /\
  proph_map_bounded st.encoded_next_proph_id st.encoded_token_map

let proph_state_next_fresh_encoded #result #payload
    (st:proph_state_view_encoded result payload)
  : Lemma
    (requires proph_state_interp_encoded st)
    (ensures proph_map_fresh st.encoded_next_proph_id st.encoded_token_map)
= proph_map_bounded_fresh st.encoded_next_proph_id st.encoded_token_map

let proph_state_alloc_view_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
  : proph_state_view_encoded result payload
= { encoded_decoder = st.encoded_decoder;
    encoded_future_trace = st.encoded_future_trace;
    encoded_token_map = proph_map_alloc_encoded st.encoded_decoder pid st.encoded_future_trace st.encoded_token_map;
    encoded_next_proph_id = pid + 1;
    encoded_observation_index = st.encoded_observation_index }

let proph_state_alloc_fresh_view_encoded #result #payload
    (st:proph_state_view_encoded result payload)
  : proph_id & proph_state_view_encoded result payload
= let pid = st.encoded_next_proph_id in
  (pid,
   { encoded_decoder = st.encoded_decoder;
     encoded_future_trace = st.encoded_future_trace;
     encoded_token_map = proph_map_alloc_encoded st.encoded_decoder pid st.encoded_future_trace st.encoded_token_map;
     encoded_next_proph_id = pid + 1;
     encoded_observation_index = st.encoded_observation_index })

let proph_state_resolve_view_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (tail:prediction_stream result payload)
    (ks:encoded_global_trace)
  : proph_state_view_encoded result payload
= { encoded_decoder = st.encoded_decoder;
    encoded_future_trace = ks;
    encoded_token_map = proph_map_update pid tail st.encoded_token_map;
    encoded_next_proph_id = st.encoded_next_proph_id;
    encoded_observation_index = st.encoded_observation_index + 1 }

let proph_state_future_matches_tape_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (len:nat)
  : prop
= st.encoded_future_trace == encoded_trace_of_tape ot st.encoded_observation_index len

let proph_state_resolve_advances_tape_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (len:nat)
  : Lemma
    (requires len > 0 /\
              proph_state_future_matches_tape_encoded st ot len /\
              st.encoded_future_trace == n :: ks)
    (ensures proph_state_future_matches_tape_encoded
               (proph_state_resolve_view_encoded st pid tail ks) ot (len - 1))
= encoded_trace_of_tape_cons ot st.encoded_observation_index len

(** Runtime projection to the active nondeterministic semantics.

    [NST.observe] consumes [ot (NST.observation_index c)] and advances exactly
    [NST.bump_observation c].  The encoded prophecy-state view carries the same
    observation index, so this predicate is the reviewed projection seam between
    the pure Iris prophecy map and the active PulseCore observation cursor. *)
let proph_state_runtime_matches_tape_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : prop
= st.encoded_observation_index == NST.observation_index c /\
  st.encoded_future_trace == encoded_trace_of_tape ot (NST.observation_index c) len

(** Full active-counter projection: the encoded state view agrees both with the
    Resolve observation cursor and with the NewProph fresh-id cursor. *)
let proph_state_runtime_matches_ctr_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : prop
= proph_state_runtime_matches_tape_encoded st ot c len /\
  st.encoded_next_proph_id == NST.prophecy_index c

let proph_state_alloc_runtime_preserves_tape_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_runtime_matches_tape_encoded st ot c len)
    (ensures proph_state_runtime_matches_tape_encoded
               (proph_state_alloc_view_encoded st pid) ot c len)
= ()

let proph_state_alloc_fresh_runtime_preserves_tape_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_runtime_matches_tape_encoded st ot c len)
    (ensures proph_state_runtime_matches_tape_encoded
               (snd (proph_state_alloc_fresh_view_encoded st)) ot c len)
= ()

let proph_state_alloc_fresh_runtime_advances_ctr_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_runtime_matches_ctr_encoded st ot c len)
    (ensures fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
             proph_state_runtime_matches_ctr_encoded
               (snd (proph_state_alloc_fresh_view_encoded st))
               ot (NST.bump_prophecy c) len)
= ()

let proph_state_resolve_observe_advances_tape_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires len > 0 /\
              proph_state_runtime_matches_tape_encoded st ot c len /\
              st.encoded_future_trace == n :: ks)
    (ensures proph_state_runtime_matches_tape_encoded
               (proph_state_resolve_view_encoded st pid tail ks)
               ot (NST.bump_observation c) (len - 1))
= encoded_trace_of_tape_cons ot (NST.observation_index c) len

let proph_state_resolve_observe_preserves_ctr_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_future_trace == n :: ks)
    (ensures proph_state_runtime_matches_ctr_encoded
               (proph_state_resolve_view_encoded st pid tail ks)
               ot (NST.bump_observation c) (len - 1))
= encoded_trace_of_tape_cons ot (NST.observation_index c) len


let proph_state_alloc_view_encoded_lookup #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
  : Lemma
    (ensures proph_map_lookup pid (proph_state_alloc_view_encoded st pid).encoded_token_map ==
             Some (proph_list_resolves_encoded st.encoded_decoder pid st.encoded_future_trace))
= proph_map_alloc_encoded_lookup st.encoded_decoder pid st.encoded_future_trace st.encoded_token_map

let proph_state_resolve_view_encoded_lookup #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (pv:result & payload)
    (tail:prediction_stream result payload)
    (ks:encoded_global_trace)
  : Lemma
    (requires proph_map_lookup pid st.encoded_token_map == Some (pv :: tail))
    (ensures proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail)
= proph_map_lookup_update_same_from_lookup pid (pv :: tail) tail st.encoded_token_map

(** Resolve updates only the resolved prophecy id and frames every other token
    stream in the shared prophecy map.  This is the pure counterpart of Iris's
    frame-preserving [proph_map_interp] update for helpers/clients owning
    different prophecy variables. *)
let proph_state_resolve_view_encoded_lookup_other #result #payload
    (st:proph_state_view_encoded result payload)
    (resolved_pid:proph_id)
    (queried_pid:proph_id)
    (tail:prediction_stream result payload)
    (ks:encoded_global_trace)
  : Lemma
    (requires queried_pid <> resolved_pid)
    (ensures proph_map_lookup queried_pid (proph_state_resolve_view_encoded st resolved_pid tail ks).encoded_token_map ==
             proph_map_lookup queried_pid st.encoded_token_map)
= proph_map_lookup_update_other resolved_pid queried_pid tail st.encoded_token_map

let proph_state_resolve_view_encoded_preserves_lookup_other #result #payload
    (st:proph_state_view_encoded result payload)
    (resolved_pid:proph_id)
    (queried_pid:proph_id)
    (pvs:prediction_stream result payload)
    (tail:prediction_stream result payload)
    (ks:encoded_global_trace)
  : Lemma
    (requires queried_pid <> resolved_pid /\
              proph_map_lookup queried_pid st.encoded_token_map == Some pvs)
    (ensures proph_map_lookup queried_pid (proph_state_resolve_view_encoded st resolved_pid tail ks).encoded_token_map == Some pvs)
= proph_state_resolve_view_encoded_lookup_other st resolved_pid queried_pid tail ks

let proph_map_alloc_encoded_preserves_unique #result #payload
    (decode:encoded_observation_decoder result payload)
    (pid:proph_id)
    (ks:encoded_global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_unique m /\ proph_map_fresh pid m)
    (ensures proph_map_unique (proph_map_alloc_encoded decode pid ks m))
= ()

let proph_state_alloc_encoded_preserves_interp #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
  : Lemma
    (requires proph_state_interp_encoded st /\ pid == st.encoded_next_proph_id)
    (ensures proph_state_interp_encoded (proph_state_alloc_view_encoded st pid))
= proph_state_next_fresh_encoded st;
  proph_map_alloc_encoded_preserves_interp st.encoded_decoder pid st.encoded_future_trace st.encoded_token_map;
  proph_map_alloc_encoded_preserves_unique st.encoded_decoder pid st.encoded_future_trace st.encoded_token_map;
  proph_map_alloc_fresh_preserves_bounded pid (proph_list_resolves_encoded st.encoded_decoder pid st.encoded_future_trace) st.encoded_token_map

let proph_state_alloc_fresh_view_encoded_lookup #result #payload
    (st:proph_state_view_encoded result payload)
  : Lemma
    (ensures proph_map_lookup (fst (proph_state_alloc_fresh_view_encoded st))
              (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
             Some (proph_list_resolves_encoded st.encoded_decoder st.encoded_next_proph_id st.encoded_future_trace))
= proph_map_alloc_encoded_lookup st.encoded_decoder st.encoded_next_proph_id st.encoded_future_trace st.encoded_token_map

(** Allocation frames every already-allocated prophecy id.  This is the pure
    map fact needed when a future shared authority contains tokens for several
    prophecy variables: allocating [encoded_next_proph_id] must add exactly one
    new projection and leave all other token streams unchanged. *)
let proph_state_alloc_view_encoded_lookup_other #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (queried_pid:proph_id)
  : Lemma
    (requires queried_pid <> pid)
    (ensures proph_map_lookup queried_pid (proph_state_alloc_view_encoded st pid).encoded_token_map ==
             proph_map_lookup queried_pid st.encoded_token_map)
= proph_map_lookup_alloc_other pid queried_pid
    (proph_list_resolves_encoded st.encoded_decoder pid st.encoded_future_trace)
    st.encoded_token_map

let proph_state_alloc_fresh_view_encoded_lookup_other #result #payload
    (st:proph_state_view_encoded result payload)
    (queried_pid:proph_id)
  : Lemma
    (requires queried_pid <> st.encoded_next_proph_id)
    (ensures proph_map_lookup queried_pid (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
             proph_map_lookup queried_pid st.encoded_token_map)
= proph_map_lookup_alloc_other st.encoded_next_proph_id queried_pid
    (proph_list_resolves_encoded st.encoded_decoder st.encoded_next_proph_id st.encoded_future_trace)
    st.encoded_token_map

let proph_state_alloc_fresh_view_encoded_preserves_lookup #result #payload
    (st:proph_state_view_encoded result payload)
    (queried_pid:proph_id)
    (pvs:prediction_stream result payload)
  : Lemma
    (requires queried_pid <> st.encoded_next_proph_id /\
              proph_map_lookup queried_pid st.encoded_token_map == Some pvs)
    (ensures proph_map_lookup queried_pid (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map == Some pvs)
= proph_state_alloc_fresh_view_encoded_lookup_other st queried_pid

let proph_state_alloc_fresh_encoded_preserves_interp #result #payload
    (st:proph_state_view_encoded result payload)
  : Lemma
    (requires proph_state_interp_encoded st)
    (ensures proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)))
= proph_state_next_fresh_encoded st;
  proph_map_alloc_encoded_preserves_interp st.encoded_decoder st.encoded_next_proph_id st.encoded_future_trace st.encoded_token_map;
  proph_map_alloc_encoded_preserves_unique st.encoded_decoder st.encoded_next_proph_id st.encoded_future_trace st.encoded_token_map;
  proph_map_alloc_fresh_preserves_bounded st.encoded_next_proph_id (proph_list_resolves_encoded st.encoded_decoder st.encoded_next_proph_id st.encoded_future_trace) st.encoded_token_map

let proph_state_resolve_encoded_preserves_interp #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (pv:result & payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
  : Lemma
    (requires proph_state_interp_encoded st /\
              st.encoded_future_trace == n :: ks /\
              st.encoded_decoder n == Some (pid, pv) /\
              proph_map_lookup pid st.encoded_token_map == Some (pv :: tail))
    (ensures proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks))
= proph_map_resolve_encoded_preserves_interp st.encoded_decoder pid pv tail n ks st.encoded_token_map;
  proph_map_update_preserves_unique pid tail st.encoded_token_map;
  proph_map_update_preserves_bounded st.encoded_next_proph_id pid tail st.encoded_token_map

let proph_state_resolve_observed_preserves_interp #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (pv:result & payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_tape_encoded st ot c len /\
              st.encoded_future_trace == n :: ks /\
              n == ot (NST.observation_index c) /\
              st.encoded_decoder n == Some (pid, pv) /\
              proph_map_lookup pid st.encoded_token_map == Some (pv :: tail))
    (ensures proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
             proph_state_runtime_matches_tape_encoded
               (proph_state_resolve_view_encoded st pid tail ks)
               ot (NST.bump_observation c) (len - 1))
= proph_state_resolve_encoded_preserves_interp st pid pv tail n ks;
  proph_state_resolve_observe_advances_tape_encoded st pid tail n ks ot c len

let proph_state_observed_head_agrees_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
  : Lemma
    (requires proph_state_interp_encoded st /\
              st.encoded_future_trace == n :: ks /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures observed == pred)
= proph_map_observed_head_agrees_encoded st.encoded_decoder pid observed pred payload_value tail n ks st.encoded_token_map

let proph_state_lookup_projected_head_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (pv:result & payload)
    (pvs:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
  : Lemma
    (requires proph_state_interp_encoded st /\
              st.encoded_future_trace == n :: ks /\
              st.encoded_decoder n == Some (pid, pv) /\
              proph_map_lookup pid st.encoded_token_map == Some pvs)
    (ensures pvs == pv :: proph_list_resolves_encoded st.encoded_decoder pid ks)
= proph_map_lookup_projected_head_encoded st.encoded_decoder pid pv pvs n ks st.encoded_token_map

(** Current-counter projection of [proph_state_lookup_projected_head_encoded].
    Once an active state interpretation owns a state view satisfying
    [proph_state_runtime_matches_ctr_encoded], the finite trace head and suffix
    are determined by the observation tape and [NST.observation_index c].  Thus
    the only Resolve-specific fact still needed from the future semantic rule is
    the typed decode of that current head for the prophecy being resolved; the
    token head/tail shape follows from the authoritative map interpretation. *)
let proph_state_lookup_projected_current_head_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (pv:result & payload)
    (pvs:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) == Some (pid, pv) /\
              proph_map_lookup pid st.encoded_token_map == Some pvs)
    (ensures pvs == pv ::
      proph_list_resolves_encoded st.encoded_decoder pid
        (encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1)))
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_lookup_projected_head_encoded st pid pv pvs n ks

(** Current-counter agreement without an explicit [n :: ks] premise.  This is
    the pure proof step that the old boundary-local current-decode witness should
    no longer need to manufacture once Resolve opens a real active component at
    the [ObservedResultAct] input counter. *)
let proph_state_observed_current_head_agrees_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) ==
                Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures observed == pred)
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_observed_head_agrees_encoded st pid observed pred payload_value tail n ks

let proph_state_resolve_observed_agree_preserves_interp #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_tape_encoded st ot c len /\
              st.encoded_future_trace == n :: ks /\
              n == ot (NST.observation_index c) /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures observed == pred /\
             proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
             proph_state_runtime_matches_tape_encoded
               (proph_state_resolve_view_encoded st pid tail ks)
               ot (NST.bump_observation c) (len - 1))
= proph_state_observed_head_agrees_encoded st pid observed pred payload_value tail n ks;
  assert ((observed, payload_value) == (pred, payload_value));
  assert (proph_map_lookup pid st.encoded_token_map == Some ((observed, payload_value) :: tail));
  proph_state_resolve_observed_preserves_interp st pid (observed, payload_value) tail n ks ot c len

let proph_state_resolve_observed_agree_preserves_ctr_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_future_trace == n :: ks /\
              n == ot (NST.observation_index c) /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures observed == pred /\
             proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
             proph_state_runtime_matches_ctr_encoded
               (proph_state_resolve_view_encoded st pid tail ks)
               ot (NST.bump_observation c) (len - 1))
= proph_state_observed_head_agrees_encoded st pid observed pred payload_value tail n ks;
  assert ((observed, payload_value) == (pred, payload_value));
  assert (proph_map_lookup pid st.encoded_token_map == Some ((observed, payload_value) :: tail));
  proph_state_resolve_observed_preserves_interp st pid (observed, payload_value) tail n ks ot c len;
  assert (st.encoded_next_proph_id == NST.prophecy_index c)

(** Compact, verified authority-transition facts for the future first-class
    shared prophecy resource.  They package the map/interp/tape-index facts
    that NewProph and Resolve need once the encoded state is stored in the
    instantiated state interpretation rather than in a per-handle table. *)
let proph_state_alloc_fresh_authority_step_encoded #result #payload
    (st:proph_state_view_encoded result payload)
  : Lemma
    (requires proph_state_interp_encoded st)
    (ensures fst (proph_state_alloc_fresh_view_encoded st) == st.encoded_next_proph_id /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_map_lookup (fst (proph_state_alloc_fresh_view_encoded st))
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder
          (fst (proph_state_alloc_fresh_view_encoded st)) st.encoded_future_trace))
= proph_state_alloc_fresh_encoded_preserves_interp st;
  proph_state_alloc_fresh_view_encoded_lookup st

let proph_state_alloc_fresh_authority_step_frames_lookup_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
  : Lemma
    (requires proph_state_interp_encoded st /\
              framed_pid <> st.encoded_next_proph_id /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_map_lookup st.encoded_next_proph_id
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder st.encoded_next_proph_id st.encoded_future_trace) /\
      proph_map_lookup framed_pid
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map == Some framed_pvs)
= proph_state_alloc_fresh_authority_step_encoded st;
  proph_state_alloc_fresh_view_encoded_preserves_lookup st framed_pid framed_pvs

let proph_state_resolve_authority_step_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
  : Lemma
    (requires proph_state_interp_encoded st /\
              st.encoded_future_trace == n :: ks /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures observed == pred /\
             proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
             proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail /\
             (proph_state_resolve_view_encoded st pid tail ks).encoded_next_proph_id == st.encoded_next_proph_id /\
             (proph_state_resolve_view_encoded st pid tail ks).encoded_observation_index == st.encoded_observation_index + 1)
= proph_state_observed_head_agrees_encoded st pid observed pred payload_value tail n ks;
  assert ((observed, payload_value) == (pred, payload_value));
  assert (proph_map_lookup pid st.encoded_token_map == Some ((observed, payload_value) :: tail));
  proph_state_resolve_encoded_preserves_interp st pid (observed, payload_value) tail n ks;
  proph_state_resolve_view_encoded_lookup st pid (observed, payload_value) tail ks

let proph_state_resolve_authority_step_frames_lookup_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
  : Lemma
    (requires proph_state_interp_encoded st /\
              st.encoded_future_trace == n :: ks /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail) /\
              framed_pid <> pid /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures observed == pred /\
             proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
             proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail /\
             proph_map_lookup framed_pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some framed_pvs)
= proph_state_resolve_authority_step_encoded st pid observed pred payload_value tail n ks;
  proph_state_resolve_view_encoded_preserves_lookup_other st pid framed_pid framed_pvs tail ks

let proph_state_alloc_fresh_authority_step_ctr_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              proph_state_runtime_matches_ctr_encoded st ot c len)
    (ensures fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_state_runtime_matches_ctr_encoded
        (snd (proph_state_alloc_fresh_view_encoded st)) ot (NST.bump_prophecy c) len /\
      proph_map_lookup (NST.prophecy_index c)
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder (NST.prophecy_index c) st.encoded_future_trace))
= proph_state_alloc_fresh_authority_step_encoded st;
  proph_state_alloc_fresh_runtime_advances_ctr_encoded st ot c len

let proph_state_resolve_authority_step_ctr_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_future_trace == n :: ks /\
              n == ot (NST.observation_index c) /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures observed == pred /\
             proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
             proph_state_runtime_matches_ctr_encoded
               (proph_state_resolve_view_encoded st pid tail ks)
               ot (NST.bump_observation c) (len - 1) /\
             proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail)
= proph_state_resolve_authority_step_encoded st pid observed pred payload_value tail n ks;
  proph_state_resolve_observed_agree_preserves_ctr_encoded st pid observed pred payload_value tail n ks ot c len

let proph_state_resolve_authority_step_ctr_frames_lookup_encoded #result #payload
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_future_trace == n :: ks /\
              n == ot (NST.observation_index c) /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail) /\
              framed_pid <> pid /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures observed == pred /\
             proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
             proph_state_runtime_matches_ctr_encoded
               (proph_state_resolve_view_encoded st pid tail ks)
               ot (NST.bump_observation c) (len - 1) /\
             proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail /\
             proph_map_lookup framed_pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some framed_pvs)
= proph_state_resolve_authority_step_ctr_encoded st pid observed pred payload_value tail n ks ot c len;
  proph_state_resolve_view_encoded_preserves_lookup_other st pid framed_pid framed_pvs tail ks

(** Repr-level authority facts tying the pure prophecy-state transitions to the
    actual nondeterministic interpreter primitives.  Earlier lemmas stated the
    counter relation in terms of [NST.bump_prophecy] and
    [NST.bump_observation]; these facts additionally use the checked
    [NST.repr] equations for [fresh_prophecy_id] and [observe].  They are the
    adequacy-facing shape needed to replace the remaining boundary-local
    NewProph/Resolve witnesses with a shared state interpretation: allocation
    uses exactly the id read by the interpreter, and Resolve consumes exactly
    the observation-head nat read by the interpreter. *)
let proph_state_alloc_fresh_repr_authority_step_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              proph_state_runtime_matches_ctr_encoded st ot c len)
    (ensures (let r = NST.repr (NST.fresh_prophecy_id #s ()) s0 t at ot c in
      r._1 == fst (proph_state_alloc_fresh_view_encoded st) /\
      r._2 == s0 /\
      r._3 == NST.bump_prophecy c /\
      fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_state_runtime_matches_ctr_encoded
        (snd (proph_state_alloc_fresh_view_encoded st)) ot r._3 len /\
      proph_map_lookup (NST.prophecy_index c)
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder (NST.prophecy_index c) st.encoded_future_trace)))
= NST.fresh_prophecy_id_result #s s0 t at ot c;
  proph_state_alloc_fresh_authority_step_ctr_encoded st ot c len

let proph_state_alloc_fresh_repr_authority_step_frames_lookup_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              framed_pid <> NST.prophecy_index c /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures (let r = NST.repr (NST.fresh_prophecy_id #s ()) s0 t at ot c in
      r._1 == fst (proph_state_alloc_fresh_view_encoded st) /\
      r._2 == s0 /\
      r._3 == NST.bump_prophecy c /\
      fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_state_runtime_matches_ctr_encoded
        (snd (proph_state_alloc_fresh_view_encoded st)) ot r._3 len /\
      proph_map_lookup (NST.prophecy_index c)
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder (NST.prophecy_index c) st.encoded_future_trace) /\
      proph_map_lookup framed_pid
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map == Some framed_pvs))
= NST.fresh_prophecy_id_result #s s0 t at ot c;
  assert (st.encoded_next_proph_id == NST.prophecy_index c);
  proph_state_alloc_fresh_authority_step_frames_lookup_encoded st framed_pid framed_pvs;
  proph_state_alloc_fresh_runtime_advances_ctr_encoded st ot c len

(** Counter-aware repr variants.

    The ordinary repr lemmas above are enough for historical [nst] clients.
    A first-class prophecy state interpretation, however, will be carried by
    counter-aware adequacy rules, so these variants package the same allocation
    facts using [NST.repr_ctr] and the checked [_ctr_result] equations.  They do
    not introduce new authority or trust; they simply make the already-verified
    resource update available in the shape needed by [nst_ctr]/[pnst_ctr]
    plumbing. *)
let proph_state_alloc_fresh_repr_ctr_authority_step_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              proph_state_runtime_matches_ctr_encoded st ot c len)
    (ensures (let r = NST.repr_ctr (NST.fresh_prophecy_id_ctr #s ()) s0 t at ot c in
      r._1 == fst (proph_state_alloc_fresh_view_encoded st) /\
      r._2 == s0 /\
      r._3 == NST.bump_prophecy c /\
      fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_state_runtime_matches_ctr_encoded
        (snd (proph_state_alloc_fresh_view_encoded st)) ot r._3 len /\
      proph_map_lookup (NST.prophecy_index c)
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder (NST.prophecy_index c) st.encoded_future_trace)))
= NST.fresh_prophecy_id_ctr_result #s s0 t at ot c;
  proph_state_alloc_fresh_authority_step_ctr_encoded st ot c len

let proph_state_alloc_fresh_repr_ctr_authority_step_frames_lookup_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              framed_pid <> NST.prophecy_index c /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures (let r = NST.repr_ctr (NST.fresh_prophecy_id_ctr #s ()) s0 t at ot c in
      r._1 == fst (proph_state_alloc_fresh_view_encoded st) /\
      r._2 == s0 /\
      r._3 == NST.bump_prophecy c /\
      fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_state_runtime_matches_ctr_encoded
        (snd (proph_state_alloc_fresh_view_encoded st)) ot r._3 len /\
      proph_map_lookup (NST.prophecy_index c)
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder (NST.prophecy_index c) st.encoded_future_trace) /\
      proph_map_lookup framed_pid
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map == Some framed_pvs))
= NST.fresh_prophecy_id_ctr_result #s s0 t at ot c;
  assert (st.encoded_next_proph_id == NST.prophecy_index c);
  proph_state_alloc_fresh_authority_step_frames_lookup_encoded st framed_pid framed_pvs;
  proph_state_alloc_fresh_runtime_advances_ctr_encoded st ot c len

(** Observation-tape/counter-aware repr variants.  These use [nst_obs_ctr],
    whose precondition can mention the active observation tape and counter, so
    they are the exact primitive facts needed by the shared state-interpretation
    seam rather than only post-hoc final-counter facts. *)
let proph_state_alloc_fresh_repr_obs_ctr_authority_step_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              proph_state_runtime_matches_ctr_encoded st ot c len)
    (ensures (let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at ot c in
      r._1 == fst (proph_state_alloc_fresh_view_encoded st) /\
      r._2 == s0 /\
      r._3 == NST.bump_prophecy c /\
      fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_state_runtime_matches_ctr_encoded
        (snd (proph_state_alloc_fresh_view_encoded st)) ot r._3 len /\
      proph_map_lookup (NST.prophecy_index c)
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder (NST.prophecy_index c) st.encoded_future_trace)))
= NST.fresh_prophecy_id_obs_ctr_result #s s0 t at ot c;
  proph_state_alloc_fresh_authority_step_ctr_encoded st ot c len

let proph_state_alloc_fresh_repr_obs_ctr_authority_step_frames_lookup_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              framed_pid <> NST.prophecy_index c /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures (let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at ot c in
      r._1 == fst (proph_state_alloc_fresh_view_encoded st) /\
      r._2 == s0 /\
      r._3 == NST.bump_prophecy c /\
      fst (proph_state_alloc_fresh_view_encoded st) == NST.prophecy_index c /\
      proph_state_interp_encoded (snd (proph_state_alloc_fresh_view_encoded st)) /\
      proph_state_runtime_matches_ctr_encoded
        (snd (proph_state_alloc_fresh_view_encoded st)) ot r._3 len /\
      proph_map_lookup (NST.prophecy_index c)
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map ==
        Some (proph_list_resolves_encoded st.encoded_decoder (NST.prophecy_index c) st.encoded_future_trace) /\
      proph_map_lookup framed_pid
        (snd (proph_state_alloc_fresh_view_encoded st)).encoded_token_map == Some framed_pvs))
= NST.fresh_prophecy_id_obs_ctr_result #s s0 t at ot c;
  assert (st.encoded_next_proph_id == NST.prophecy_index c);
  proph_state_alloc_fresh_authority_step_frames_lookup_encoded st framed_pid framed_pvs;
  proph_state_alloc_fresh_runtime_advances_ctr_encoded st ot c len

let proph_state_resolve_observe_repr_authority_step_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_future_trace == n :: ks /\
              n == ot (NST.observation_index c) /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures (let r = NST.repr (NST.observe #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail))
= NST.observe_result #s s0 t at ot c;
  proph_state_resolve_authority_step_ctr_encoded st pid observed pred payload_value tail n ks ot c len

let proph_state_resolve_observe_repr_authority_step_frames_lookup_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (n:nat)
    (ks:encoded_global_trace)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_future_trace == n :: ks /\
              n == ot (NST.observation_index c) /\
              st.encoded_decoder n == Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail) /\
              framed_pid <> pid /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures (let r = NST.repr (NST.observe #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail /\
      proph_map_lookup framed_pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some framed_pvs))
= NST.observe_result #s s0 t at ot c;
  proph_state_resolve_authority_step_ctr_frames_lookup_encoded st pid observed pred payload_value tail n ks ot c len framed_pid framed_pvs

(** Current-counter Resolve repr facts.

    The two repr lemmas above are intentionally close to the primitive Iris
    rule and take the consumed nat [n] plus suffix [ks] explicitly.  When the
    authoritative state is already tied to the active runtime cursor by
    [proph_state_runtime_matches_ctr_encoded], these wrappers derive that head
    and suffix from [NST.observation_index c] and the observation tape.  Thus a
    caller needs to supply only the typed decode fact for the current emitted
    observation; the list-head fact itself is no longer a separate premise.
    This is the exact pure shape expected from the future first-class
    state-interpretation resource that will replace the boundary-local
    current-decode witness. *)
let proph_state_resolve_observe_repr_current_authority_step_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) ==
                Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures (let n = ot (NST.observation_index c) in
      let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let r = NST.repr (NST.observe #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail))
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_resolve_observe_repr_authority_step_encoded st pid observed pred payload_value tail n ks ot c len s0 t at

let proph_state_resolve_observe_repr_current_authority_step_frames_lookup_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) ==
                Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail) /\
              framed_pid <> pid /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures (let n = ot (NST.observation_index c) in
      let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let r = NST.repr (NST.observe #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail /\
      proph_map_lookup framed_pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some framed_pvs))
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_resolve_observe_repr_authority_step_frames_lookup_encoded st pid observed pred payload_value tail n ks ot c len framed_pid framed_pvs s0 t at

let proph_state_resolve_observe_repr_ctr_current_authority_step_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) ==
                Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures (let n = ot (NST.observation_index c) in
      let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let r = NST.repr_ctr (NST.observe_ctr #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail))
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  NST.observe_ctr_result #s s0 t at ot c;
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_resolve_authority_step_ctr_encoded st pid observed pred payload_value tail n ks ot c len

let proph_state_resolve_observe_repr_ctr_current_authority_step_frames_lookup_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) ==
                Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail) /\
              framed_pid <> pid /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures (let n = ot (NST.observation_index c) in
      let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let r = NST.repr_ctr (NST.observe_ctr #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail /\
      proph_map_lookup framed_pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some framed_pvs))
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  NST.observe_ctr_result #s s0 t at ot c;
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_resolve_authority_step_ctr_frames_lookup_encoded st pid observed pred payload_value tail n ks ot c len framed_pid framed_pvs

let proph_state_resolve_observe_repr_obs_ctr_current_authority_step_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) ==
                Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail))
    (ensures (let n = ot (NST.observation_index c) in
      let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail))
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  NST.observe_obs_ctr_result #s s0 t at ot c;
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_resolve_authority_step_ctr_encoded st pid observed pred payload_value tail n ks ot c len

let proph_state_resolve_observe_repr_obs_ctr_current_authority_step_frames_lookup_encoded #result #payload (#s:Type0)
    (st:proph_state_view_encoded result payload)
    (pid:proph_id)
    (observed:result)
    (pred:result)
    (payload_value:payload)
    (tail:prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
    (framed_pid:proph_id)
    (framed_pvs:prediction_stream result payload)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires proph_state_interp_encoded st /\
              len > 0 /\
              proph_state_runtime_matches_ctr_encoded st ot c len /\
              st.encoded_decoder (ot (NST.observation_index c)) ==
                Some (pid, (observed, payload_value)) /\
              proph_map_lookup pid st.encoded_token_map == Some ((pred, payload_value) :: tail) /\
              framed_pid <> pid /\
              proph_map_lookup framed_pid st.encoded_token_map == Some framed_pvs)
    (ensures (let n = ot (NST.observation_index c) in
      let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at ot c in
      r._1 == n /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      observed == pred /\
      proph_state_interp_encoded (proph_state_resolve_view_encoded st pid tail ks) /\
      proph_state_runtime_matches_ctr_encoded
        (proph_state_resolve_view_encoded st pid tail ks) ot r._3 (len - 1) /\
      proph_map_lookup pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some tail /\
      proph_map_lookup framed_pid (proph_state_resolve_view_encoded st pid tail ks).encoded_token_map == Some framed_pvs))
= let n = ot (NST.observation_index c) in
  let ks = encoded_trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  NST.observe_obs_ctr_result #s s0 t at ot c;
  encoded_trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.encoded_future_trace == n :: ks);
  proph_state_resolve_authority_step_ctr_frames_lookup_encoded st pid observed pred payload_value tail n ks ot c len framed_pid framed_pvs


let proph_map_alloc #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (ks:global_trace)
    (m:proph_map result payload)
  : proph_map result payload
= (pid, proph_list_resolves_global decode pid ks) :: m

let proph_map_alloc_lookup #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (ks:global_trace)
    (m:proph_map result payload)
  : Lemma
    (ensures proph_map_lookup pid (proph_map_alloc decode pid ks m) ==
             Some (proph_list_resolves_global decode pid ks))
= proph_map_lookup_alloc_same pid (proph_list_resolves_global decode pid ks) m

let proph_map_alloc_preserves_interp #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (ks:global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp decode ks m /\ proph_map_fresh pid m)
    (ensures proph_map_interp decode ks (proph_map_alloc decode pid ks m))
= ()

(** Heterogeneous Resolve consumes the matching head of the global trace and
    exposes the typed head prediction plus the remaining global trace.  This is
    the pure counterpart of the future first-class Resolve action. *)
let resolve_head_global #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (ks:global_trace)
  : option ((result & payload) & global_trace)
= match ks with
  | [] -> None
  | o :: ks' ->
    match decode o with
    | Some (pid', pv) -> if pid' = pid then Some (pv, ks') else None
    | None -> None

(** For a matching head observation, the coupled token stream exposes that
    observation as its next prediction and leaves the tail projection behind. *)
let resolve_head_couples #result #payload
    (pid:proph_id)
    (o:observation result payload)
    (ks:trace result payload)
  : Lemma
    (requires o.proph == pid)
    (ensures proph_list_resolves pid (o :: ks) == obs_pair o :: proph_list_resolves pid ks)
= ()

(** Heterogeneous version of [resolve_head_couples].  If the global head decodes
    as an observation for [pid], then the [pid] projection begins with that
    observation and the tail is the projection of the remaining global trace. *)
let resolve_head_global_couples #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (pv:result & payload)
    (o:packed_observation)
    (ks:global_trace)
  : Lemma
    (requires decode o == Some (pid, pv))
    (ensures proph_list_resolves_global decode pid (o :: ks) ==
             pv :: proph_list_resolves_global decode pid ks)
= ()

(** Resolving another prophecy leaves this prophecy's typed projection
    unchanged.  This is the key frame-preservation fact needed by a global
    [proph_map_interp]: a Resolve step consumes only the head for the prophecy
    being resolved, while all other prophecy tokens keep the same stream. *)
let resolve_head_global_frames_other #result #payload
    (decode:observation_decoder result payload)
    (resolved_pid:proph_id)
    (pid:proph_id)
    (pv:result & payload)
    (o:packed_observation)
    (ks:global_trace)
  : Lemma
    (requires decode o == Some (resolved_pid, pv) /\ pid <> resolved_pid)
    (ensures proph_list_resolves_global decode pid (o :: ks) ==
             proph_list_resolves_global decode pid ks)
= ()

(** Frame-preservation for a whole prophecy map that does not contain the
    resolved id.  Consuming a global observation for [resolved_pid] leaves every
    other entry's projected stream unchanged. *)
let rec proph_map_resolve_frames_fresh #result #payload
    (decode:observation_decoder result payload)
    (resolved_pid:proph_id)
    (pv:result & payload)
    (o:packed_observation)
    (ks:global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp decode (o :: ks) m /\
              decode o == Some (resolved_pid, pv) /\
              proph_map_fresh resolved_pid m)
    (ensures proph_map_interp decode ks m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid, pvs) :: m' ->
    assert (pid <> resolved_pid);
    resolve_head_global_frames_other decode resolved_pid pid pv o ks;
    assert (proph_map_interp decode (o :: ks) m');
    assert (proph_map_fresh resolved_pid m');
    proph_map_resolve_frames_fresh decode resolved_pid pv o ks m';
    ()

(** Pure [proph_map_interp] Resolve update.  Suppose the next global observation
    decodes to [(pid, pv)] and the prophecy map contains the matching token
    stream [pv :: tail].  Updating that entry to [tail] preserves the map
    interpretation for the remaining global trace.  This is the pure analogue
    of Iris's [proph_map_resolve_proph] ghost update: agreement comes from the
    map/trace invariant, not from writing the observed value after the fact. *)
let rec proph_map_resolve_preserves_interp #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (pv:result & payload)
    (tail:prediction_stream result payload)
    (o:packed_observation)
    (ks:global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_interp decode (o :: ks) m /\
              decode o == Some (pid, pv) /\
              proph_map_lookup pid m == Some (pv :: tail) /\
              proph_map_unique m)
    (ensures proph_map_interp decode ks (proph_map_update pid tail m))
    (decreases m)
= match m with
  | [] -> ()
  | (pid', pvs') :: m' ->
    if pid = pid'
    then (
      assert (pvs' == pv :: tail);
      resolve_head_global_couples decode pid pv o ks;
      assert (tail == proph_list_resolves_global decode pid ks);
      assert (proph_map_fresh pid m');
      assert (proph_map_interp decode (o :: ks) m');
      proph_map_resolve_frames_fresh decode pid pv o ks m';
      proph_map_update_fresh_noop pid tail m';
      assert (proph_map_update pid tail m' == m');
      ()
    )
    else (
      assert (pid' <> pid);
      assert (proph_map_interp decode (o :: ks) m');
      assert (proph_map_lookup pid m' == Some (pv :: tail));
      assert (proph_map_unique m');
      resolve_head_global_frames_other decode pid pid' pv o ks;
      proph_map_resolve_preserves_interp decode pid pv tail o ks m';
      ()
    )

(** A compact pure state-interpretation slice for a single typed prophecy
    interface.  This is not a Pulse [slprop]; instead it is the total model that
    the eventual PulseCore instantiated state should internalize.  The view
    contains exactly the Iris ingredients: the future global observation trace,
    a prophecy-token map, and the decoder used to project the heterogeneous
    trace into this typed interface. *)
noeq
type proph_state_view (result payload:Type0) = {
  decoder      : observation_decoder result payload;
  future_trace : global_trace;
  token_map    : proph_map result payload;
  next_proph_id : proph_id;
}

let proph_state_interp #result #payload
    (st:proph_state_view result payload)
  : prop
= proph_map_interp st.decoder st.future_trace st.token_map /\
  proph_map_unique st.token_map /\
  proph_map_bounded st.next_proph_id st.token_map

let proph_state_next_fresh #result #payload
    (st:proph_state_view result payload)
  : Lemma
    (requires proph_state_interp st)
    (ensures proph_map_fresh st.next_proph_id st.token_map)
= proph_map_bounded_fresh st.next_proph_id st.token_map

let proph_state_alloc_view #result #payload
    (st:proph_state_view result payload)
    (pid:proph_id)
  : proph_state_view result payload
= { decoder = st.decoder;
    future_trace = st.future_trace;
    token_map = proph_map_alloc st.decoder pid st.future_trace st.token_map;
    next_proph_id = pid + 1 }

let proph_state_alloc_fresh_view #result #payload
    (st:proph_state_view result payload)
  : proph_id & proph_state_view result payload
= let pid = st.next_proph_id in
  (pid,
   { decoder = st.decoder;
     future_trace = st.future_trace;
     token_map = proph_map_alloc st.decoder pid st.future_trace st.token_map;
     next_proph_id = pid + 1 })

let proph_state_resolve_view #result #payload
    (st:proph_state_view result payload)
    (pid:proph_id)
    (tail:prediction_stream result payload)
    (ks:global_trace)
  : proph_state_view result payload
= { decoder = st.decoder;
    future_trace = ks;
    token_map = proph_map_update pid tail st.token_map;
    next_proph_id = st.next_proph_id }

let proph_state_alloc_view_lookup #result #payload
    (st:proph_state_view result payload)
    (pid:proph_id)
  : Lemma
    (ensures proph_map_lookup pid (proph_state_alloc_view st pid).token_map ==
             Some (proph_list_resolves_global st.decoder pid st.future_trace))
= proph_map_alloc_lookup st.decoder pid st.future_trace st.token_map

let proph_state_resolve_view_lookup #result #payload
    (st:proph_state_view result payload)
    (pid:proph_id)
    (pv:result & payload)
    (tail:prediction_stream result payload)
    (ks:global_trace)
  : Lemma
    (requires proph_map_lookup pid st.token_map == Some (pv :: tail))
    (ensures proph_map_lookup pid (proph_state_resolve_view st pid tail ks).token_map == Some tail)
= proph_map_lookup_update_same_from_lookup pid (pv :: tail) tail st.token_map

let proph_map_alloc_preserves_unique #result #payload
    (decode:observation_decoder result payload)
    (pid:proph_id)
    (ks:global_trace)
    (m:proph_map result payload)
  : Lemma
    (requires proph_map_unique m /\ proph_map_fresh pid m)
    (ensures proph_map_unique (proph_map_alloc decode pid ks m))
= ()

let proph_state_alloc_preserves_interp #result #payload
    (st:proph_state_view result payload)
    (pid:proph_id)
  : Lemma
    (requires proph_state_interp st /\ pid == st.next_proph_id)
    (ensures proph_state_interp (proph_state_alloc_view st pid))
= proph_state_next_fresh st;
  proph_map_alloc_preserves_interp st.decoder pid st.future_trace st.token_map;
  proph_map_alloc_preserves_unique st.decoder pid st.future_trace st.token_map;
  proph_map_alloc_fresh_preserves_bounded pid (proph_list_resolves_global st.decoder pid st.future_trace) st.token_map

let proph_state_alloc_fresh_view_lookup #result #payload
    (st:proph_state_view result payload)
  : Lemma
    (ensures proph_map_lookup (fst (proph_state_alloc_fresh_view st))
              (snd (proph_state_alloc_fresh_view st)).token_map ==
             Some (proph_list_resolves_global st.decoder st.next_proph_id st.future_trace))
= proph_map_alloc_lookup st.decoder st.next_proph_id st.future_trace st.token_map

let proph_state_alloc_fresh_preserves_interp #result #payload
    (st:proph_state_view result payload)
  : Lemma
    (requires proph_state_interp st)
    (ensures proph_state_interp (snd (proph_state_alloc_fresh_view st)))
= proph_state_next_fresh st;
  proph_map_alloc_preserves_interp st.decoder st.next_proph_id st.future_trace st.token_map;
  proph_map_alloc_preserves_unique st.decoder st.next_proph_id st.future_trace st.token_map;
  proph_map_alloc_fresh_preserves_bounded st.next_proph_id (proph_list_resolves_global st.decoder st.next_proph_id st.future_trace) st.token_map

let proph_state_resolve_preserves_interp #result #payload
    (st:proph_state_view result payload)
    (pid:proph_id)
    (pv:result & payload)
    (tail:prediction_stream result payload)
    (o:packed_observation)
    (ks:global_trace)
  : Lemma
    (requires proph_state_interp st /\
              st.future_trace == o :: ks /\
              st.decoder o == Some (pid, pv) /\
              proph_map_lookup pid st.token_map == Some (pv :: tail))
    (ensures proph_state_interp (proph_state_resolve_view st pid tail ks))
= proph_map_resolve_preserves_interp st.decoder pid pv tail o ks st.token_map;
  proph_map_update_preserves_unique pid tail st.token_map;
  proph_map_update_preserves_bounded st.next_proph_id pid tail st.token_map
