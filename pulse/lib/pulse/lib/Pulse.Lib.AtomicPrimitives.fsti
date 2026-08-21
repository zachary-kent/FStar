(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Atomic Primitives — the trusted kernel of atomic operations.

    This module is the ONLY place where as_atomic may appear.
    Each operation corresponds to a single Iris/HeapLang atomic step.

    HeapLang atomic steps (each individually atomic, no interleaving):
      - Load:  !l
      - Store: l <- v
      - Alloc: ref v
      - CAS:   CAS l expected new  (compare-and-swap)
      - FAA:   FAA l delta          (fetch-and-add, U32 only)

    These are OPAQUE axioms. The .fst provides a model implementation
    using as_atomic for type-checking, but clients depend only on
    the specs declared here. On real hardware, these map to:
      - Load/Store: MOV (aligned)
      - CAS:        LOCK CMPXCHG
      - FAA:        LOCK XADD
      - Alloc:      malloc

    All other files must compose these primitives rather than using
    as_atomic directly.

    Prophecy Resolve is currently the one non-hardware-shaped user of this
    boundary: the implementation keeps a non-exported, temporary observed-result
    `stt_atomic` presentation helper that is now specialized to the active
    Ret-specialized `ObservedResultActWithHiddenStateReturnAction` shape, so
    clients can resolve while invariants are open without a Resolve-local
    arbitrary `as_atomic` coercion.
    This is intentionally temporary and not final native Iris support;
    PulseCore still needs observed-result actions directly in the atomic
    representation.  See `PROPHECY_FOUNDATIONAL_CONSULTATION.md` for the
    concrete auditor-reviewable justification and remaining foundational work. *)
module Pulse.Lib.AtomicPrimitives
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32
module PT = Pulse.Lib.Prophecy.Trace
module NST = PulseCore.NondeterministicHoareStateMonad

(* ================================================================ *)
(* Conditional slprop (shared with Pulse.Lib.Primitives)            *)
(* ================================================================ *)

let cond b (p q:slprop) = if b then p else q

(* ================================================================ *)
(* Load — atomic read from a box                                    *)
(* HeapLang: !l                                                     *)
(* ================================================================ *)

val atomic_read (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_atomic a #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))

(* ================================================================ *)
(* Store — atomic write to a box                                    *)
(* HeapLang: l <- v                                                 *)
(* ================================================================ *)

val atomic_write (#a:Type0) (r : B.box a) (x : a) (#v : erased a)
  : stt_atomic unit #Observable emp_inames
    (B.pts_to r v) (fun _ -> B.pts_to r x)

(* ================================================================ *)
(* Alloc — atomic allocation of a box                               *)
(* HeapLang: ref v                                                  *)
(* ================================================================ *)

val atomic_alloc (#a:Type0) (x : a)
  : stt_atomic (B.box a) #Observable emp_inames
    emp (fun r -> B.pts_to r x)

(* ================================================================ *)
(* CAS — compare-and-swap (eqtype)                                  *)
(* HeapLang: CAS l expected new                                     *)
(* ================================================================ *)

val atomic_cas (#a:eqtype) (r : B.box a) (expected new_val : a) (#cur : erased a)
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))

(* ================================================================ *)
(* CAS — pointer equality variant (box_eq)                          *)
(* HeapLang: CAS l expected new  (on locations)                     *)
(* ================================================================ *)

val atomic_cas_box (#a:Type0) (r : B.box (B.box a))
    (expected new_val : B.box a) (#cur : erased (B.box a))
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))

(* ================================================================ *)
(* FAA — fetch-and-add on U32                                       *)
(* HeapLang: FAA l delta                                            *)
(* ================================================================ *)

val atomic_faa (r : B.box U32.t) (delta : U32.t) (#cur : erased U32.t)
  : stt_atomic U32.t #Observable emp_inames
    (B.pts_to r cur) (fun old -> B.pts_to r (U32.add_mod old delta) ** pure (old == reveal cur))

(* ================================================================ *)
(* Prophecy variables — trusted Iris-style operational boundary      *)
(*                                                                  *)
(* HeapLang has two prophecy constructs: NewProph and Resolve.       *)
(* Their soundness relies on adequacy/state interpretation threading *)
(* a global observation trace. PulseCore now has a dedicated         *)
(* observation oracle plus ObservedAct/ObservedResultAct semantic    *)
(* nodes, including active hidden-state action support for           *)
(* single-step action+observation coupling. The trace scaffold has   *)
(* verified projection lemmas for                                    *)
(* NST.observation_index/bump_observation and an agreement lemma     *)
(* deriving Resolve's result/prediction equality from proph_map      *)
(* interpretation. Resolve-token is now lowered through the active   *)
(* observed-result action path, so the wrapped physical atomic       *)
(* action, observation-tape consumption, token pop, and              *)
(* authoritative Resolve update occur in one semantic step. The      *)
(* public token model now owns the client token fragment plus the    *)
(* public half of the active token/world agreement cell; the         *)
(* authoritative encoded-state fragment is separated into the active *)
(* component/state-interpretation helpers. Resource-level NewProph   *)
(* helpers update that singleton component with verified             *)
(* counter-aware trace lemmas. The public NewProph path consumes the *)
(* active PulseCore prophecy-id cursor and returns the client token  *)
(* fragment without an emp-to-active-component opening. Resolve now  *)
(* consumes the observed-result nat in the active hidden-state action*)
(* callback while the hidden state is indexed only by active ot,c.   *)
(* The finish proof derives token/world agreement by gathering the   *)
(* public token's deterministic projection-table slot with the active*)
(* registry.  The direct active-registry membership premise has been *)
(* replaced by the token's projection-table/slot certificate.  The   *)
(* remaining named trusted prophecy slice is the opened-world        *)
(* event/decode boundary inside the finisher; the projection-table   *)
(* binding is now carried by the token-indexed active hidden state.  *)
(* The private observed-result atomic presentation shim remains. The *)
(* remaining gap is                                                *)
(* replacing those primitive-boundary facts with a first-class shared*)
(* state-interpretation/adequacy resource.                          *)
(* ================================================================ *)

(** An opaque prophecy handle for observations whose resolved step returns
    [result] and carries an attached [payload].  Internally the handle contains
    a uniform prophecy id plus a trusted prophecy-token table; the type
    parameters prevent clients from mixing incompatible projections. *)
[@@erasable]
val prophecy_var (result payload:Type0) : Type0

(** First-class shared prophecy authority, factored out from the legacy
    per-handle [prophecy_token] carrier.  This is a verified resource-level
    slice of the intended Iris [proph_map_interp]: [prophecy_authority_state]
    owns the authoritative encoded prophecy-state view, while
    [prophecy_token_fragment] owns only an individual prophecy's linear token
    slot.  The allocation/Resolve helpers below update the shared authority and
    token fragment together using the verified [Pulse.Lib.Prophecy.Trace]
    authority-step lemmas.  Public [new_proph_semantic] is now routed through a
    Ret-specialized active hidden-state runner; Resolve still needs the analogous
    first-class observed-result active runner and decoder derivation. *)
[@@erasable]
val prophecy_authority (result payload:Type0) : Type0

val prophecy_id_of (#result #payload:Type0)
    (p:prophecy_var result payload)
  : GTot PT.proph_id

val prophecy_bound_to_authority (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (p:prophecy_var result payload)
  : GTot prop

val prophecy_authority_state (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:PT.proph_state_view_encoded result payload)
  : slprop

(** Counter-aware singleton authority resource.  This is the smallest verified
    state-interpretation shape needed by adequacy-facing NewProph/Resolve:
    the authoritative encoded prophecy state is a resource, and its fresh-id
    and observation indices are tied to the active NST counters plus the
    observation tape suffix. *)
[@@pulse_unfold]
let prophecy_authority_runtime_state (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:PT.proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : slprop
= prophecy_authority_state auth st **
  pure (PT.proph_state_runtime_matches_ctr_encoded st ot c len)

val prophecy_token_fragment (#result #payload:Type0)
    (p:prophecy_var result payload)
    (pvs:PT.prediction_stream result payload)
  : slprop

(** Named state-interpretation slice for the same singleton runtime authority.
    This alias is intentionally exact (not existential): opening it exposes the
    authoritative encoded state at the same observation tape and [NST.ctr] that
    adequacy must thread through [FreshProphId] and [ObservedResultAct].  The
    allocation/Resolve wrappers below are resource-level rules; public NewProph
    now uses an informative active-component package built from this slice, but
    the package opening itself still needs a counter-aware executable rule whose
    specification exposes the [FreshProphId] input/output counter. *)
val prophecy_shared_state_interp (#result #payload:Type0)
    (auth:prophecy_authority result payload)
    (st:PT.proph_state_view_encoded result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
    (len:nat)
  : slprop

(** [prophecy_token p pvs] is now only the linear client fragment for [p].
    It deliberately does not own [prophecy_shared_state_interp] or any other
    authoritative runtime state; that authority is represented separately by
    [active_prophecy_si] / component helpers and must be owned by instantiated
    adequacy.  This split removes the NewProph token/authority duplication
    point.  Resolve now uses a hidden active observed-result precondition and
    the checked active helper for the token-tail equality; the remaining gap is
    wiring those p-specific hidden facts to the singleton adequacy state
    interpretation directly. *)
val prophecy_token (#result #payload:Type0)
    (p:prophecy_var result payload)
    (pvs:PT.prediction_stream result payload)
  : slprop

ghost
fn prophecy_authority_init (#result #payload:Type0)
    (#initial:erased (PT.proph_state_view_encoded result payload))
  requires pure (PT.proph_state_interp_encoded (reveal initial))
  returns auth:prophecy_authority result payload
  ensures prophecy_authority_state auth (reveal initial)

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

(** Resolve over a counter/tape-indexed runtime authority, deriving the consumed
    nat from [NST.observation_index c] instead of accepting it as a separate
    caller-supplied premise.  The remaining pure premise is exactly the typed
    decode fact for the current observation-tape head. *)
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

(** Packaged adequacy-owned prophecy component.

    This packages the exact [prophecy_shared_state_interp] resource that the
    active adequacy/state interpretation must own: a singleton authority, its
    current nat-encoded state view, and the remaining observation-suffix length.
    The allocation/Resolve rules below consume and return this one component at
    the exact [repr_obs_ctr] counter returned by [fresh_prophecy_id_obs_ctr] /
    [observe_obs_ctr].  The component is intentionally informative (not marked
    erasable), because public NewProph must construct and return a concrete
    [prophecy_var] handle whose authority fields are the active component's
    singleton authority.  Public NewProph no longer exposes this package or a
    runner-owned emp-to-authority projection; the remaining core gap is wiring
    public NewProph/Resolve to open this component from PulseCore's active state
    interpretation instead of returning an isolated fragment/update through
    primitive-boundary seams. *)
noeq type prophecy_active_component (result payload:Type0) = {
  component_authority: prophecy_authority result payload;
  component_state_view: PT.proph_state_view_encoded result payload;
  component_len: nat;
}

val prophecy_active_component_interp (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : slprop

val prophecy_component_bound (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (p:prophecy_var result payload)
  : GTot prop

val prophecy_component_lookup (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (p:prophecy_var result payload)
    (pvs:PT.prediction_stream result payload)
  : GTot prop

val prophecy_active_component_after_alloc (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
  : GTot (prophecy_active_component result payload)

val prophecy_active_component_after_resolve (#result #payload:Type0)
    (comp:prophecy_active_component result payload { comp.component_len > 0 })
    (p:prophecy_var result payload)
    (tail:PT.prediction_stream result payload)
    (ot:nat -> nat)
    (c:NST.ctr)
  : GTot (prophecy_active_component result payload)

(** First-class singleton active-prophecy state interpretation for one typed
    projection of the nat-encoded prophecy world.  This is the predicate that
    active semantics/adequacy must own at the current observation tape and
    counter; NewProph/Resolve rules open it, update the hidden component, and
    close it at the advanced counter. *)
val active_prophecy_si (#result #payload:Type0)
    (ot:nat -> nat)
    (c:NST.ctr)
  : slprop

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

(** Current-counter active-state allocation rule for the NewProph cursor.
    This is the small singleton-world ghost operation that the eventual active
    NewProph adequacy rule must call after [FreshProphId] has produced
    [pid == NST.prophecy_index c]: it opens the active [active_prophecy_si],
    updates the one hidden component, closes it at [NST.bump_prophecy c], and
    returns only the client token fragment.  The public [new_proph_semantic]
    boundary already returns only the opaque fragment token and no longer
    exposes an [emp -> prophecy_active_component_interp] witness; fully
    eliminating the remaining NewProph semantic gap requires wiring this helper
    into instantiated adequacy. *)
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

(** Allocation over an already-open active component at the current executable
    [FreshProphId] cursor.  This is the non-[repr] rule the future active
    NewProph adequacy path must call after the active component has been opened
    from adequacy-owned state interpretation; the map allocation/update itself
    is checked. *)
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

(** Framed version of the current-counter allocation rule.  It preserves an
    unrelated token lookup through the same singleton active component, which is
    the shape needed by future shared-prophecy adequacy/helper proofs. *)
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

(** Resolve by opening an active singleton component whose current-head facts are
    already known.  This is the resource-level shape used by the public
    hidden-state Resolve path: the observed-result semantic rule supplies the
    p-specific current decoder/bound/lookup facts as hidden state, and this
    helper derives the token-tail equality from the active component. *)
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

(** NewProph allocation after the active semantic fresh-id cursor.

    This is the blocker-deleting resource/runner shape for allocation once a
    prophecy-aware runner has exposed the executable [FreshProphId] fact
    [pid == NST.prophecy_index c].  The active singleton [active_prophecy_si ot
    c] is opened and updated by the checked current-counter allocation rule,
    and the returned public token is a projection from that singleton's future
    trace rather than a locally initialized empty stream.  Ordinary
    [new_proph_semantic] now performs the same allocation through the
    state-action hidden cursor [fresh_prophecy_id_with_hidden_si_state_action];
    this component rule remains the checked open-component form for
    adequacy/runner code that already exposes the active singleton explicitly. *)
val new_proph_semantic_active_component_after_cursor (#result #payload:Type0)
    (comp:prophecy_active_component result payload)
    (pid:PT.proph_id)
    (#ot:erased (nat -> nat))
    (#c:erased NST.ctr)
  : stt (prophecy_var result payload)
      (prophecy_active_component_interp comp (reveal ot) (reveal c) **
       pure (pid == NST.prophecy_index (reveal c)))
      (fun p -> prophecy_active_component_interp (prophecy_active_component_after_alloc comp)
          (reveal ot) (NST.bump_prophecy (reveal c)) **
        (exists* (pvs:PT.prediction_stream result payload). prophecy_token_fragment p pvs))

(** NewProph over the active semantic fresh-id cursor.

    The public facade now consumes the state-action hidden FreshProphId
    constructor: the allocation callback is a single neutral action that opens a
    coherent hidden state containing only the
    concrete untyped [Pulse.Lib.ProphecyWorldResource.active_world_interp] plus
    typed projection metadata at the same [ot,c], related by decoder-domain,
    future-trace, token-key, erased stream projection/reflection, counter, and
    length coherence.  It applies the checked current-counter allocation rule at
    [pid == NST.prophecy_index c], closes the hidden state at [NST.bump_prophecy
    c], and allocates only the projected client token slot from the
    singleton-derived typed stream.  This deletes the old compatibility path
    that locally initialized an empty prophecy-token stream and removes the typed active
    component as a spatial sibling of the singleton authority.  The generated
    primitive now lowers to a Ret-specialized hidden-state action constructor
    handled by the active NewProph runner that owns this
    [active_prophecy_world_si] authority; a fully general active runner for
    arbitrary post-NewProph continuations remains separate future work. *)
val new_proph_semantic (#result #payload:Type0) ()
  : stt (prophecy_var result payload)
      emp
      (fun p -> exists* (pvs:PT.prediction_stream result payload). prophecy_token p pvs)

(** Resolve in the Iris-rule form used immediately after [new_proph_semantic], lowered
    through the active hidden-state [ObservedResultAct] action.  The wrapped
    physical atomic action, observation-tape read, public token pop, and
    [PWR.resolve_current] update are coupled in one semantic step.  The
    consumed-nat/current-cursor equality is exposed by the active observed-result
    callback.  The active hidden resource is narrowed to active [ot,c] plus
    projection/registration state only: it does not supply either a hidden
    singleton [st.PW.world_decoder] premise or the transitional typed
    current-head decoder premise.  The previous stateful active-world event
    witness has been deleted from the public callback path; the Resolve finish
    step now consumes a private active observed-result receipt threaded from the
    callback after the physical action returns [x].  The finisher opens the
    actual active world, derives the token/projection binding, eliminates that
    receipt to the untyped singleton consumed-nat decoder fact, derives the
    current-observation fact from the callback equality, derives the typed
    decoder fact from opened projection reflection, and calls
    [PWR.resolve_current].  The former direct active-registry membership premise
    has been narrowed: the public token carries the deterministic agreement-slot
    certificate, and Resolve derives the slot/bounds part of the
    token/projection binding with [GFT.in_bounds].  The token-indexed active
    hidden state now supplies the active projection-table equality; Resolve
    derives the typed component lookup from the active registry/agreement cell
    before eliminating the event receipt.  The receipt boundary no longer
    supplies [PW.current_observation_decodes_to], positive length, typed decoder
    equality, token lookup, or token/world stream agreement.  The hidden state still
    does not supply a typed projection-registry lookup, singleton erased-token
    lookup, or token/world stream agreement. *)
val resolve_proph_token_semantic (#result #payload:Type0)
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

(** Resolve: execute one observable atomic step and consume the matching head
    prediction using the active observed-result action path.  The equality
    between [x] and [pred] is derived from [resolve_proph_token_semantic]'s
    Iris-rule postcondition. *)
val resolve_proph_semantic (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pred:erased result)
    (#tail:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : stt result
      (prophecy_token p ((reveal pred, payload_value) :: reveal tail) ** pre)
      (fun x -> post x ** prophecy_token p (reveal tail) ** pure (x == reveal pred))

(** Atomic-shaped Resolve-token rule for clients that must resolve while an
    invariant is open.  It has the same Iris-rule spec as the native semantic
    action above and reuses the active hidden-state Resolve implementation; the
    remaining trusted scope is the core
    [lift_atomic_targeted_post_result_observed_result_hidden_state_action_atomic]
    presentation shim, specialized to the target-fixed two-stage active
    observed-result hidden-state action.  That shim is guarded by the checked
    active-runner certificate for the same callback; it still is not the final
    PulseCore rule, because observed-result atomic actions should eventually be
    accepted directly by [with_invariants], or auditors must explicitly approve
    retaining this scoped boundary temporarily. *)
val resolve_proph_token (#result #payload:Type0)
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

val resolve_proph (#result #payload:Type0)
    (p:prophecy_var result payload)
    (payload_value:payload)
    (#pred:erased result)
    (#tail:erased (PT.prediction_stream result payload))
    (#pre:slprop)
    (#post:result -> slprop)
    (f:unit -> stt_atomic result #Observable emp_inames pre post)
  : stt_atomic result #Observable emp_inames
      (prophecy_token p ((reveal pred, payload_value) :: reveal tail) ** pre)
      (fun x -> post x ** prophecy_token p (reveal tail) ** pure (x == reveal pred))

(* ================================================================ *)
(* LL/SC — Load-Linked / Store-Conditional                          *)
(*                                                                  *)
(* Simplified model: SC succeeds iff current value == LL'd value.   *)
(* Real LL/SC may fail spuriously; we model the weaker guarantee:   *)
(*   - SC success ⟹ value unchanged since LL                       *)
(*   - SC failure ⟹ no information (may be spurious)               *)
(* This is sufficient to implement CAS, which is the use case.     *)
(*                                                                  *)
(* ARM: LDXR/STXR. RISC-V: LR/SC. MIPS: LL/SC.                    *)
(* ================================================================ *)

(** LL — load-linked: atomic read that returns a ghost token. *)
val ll (#a:eqtype) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_atomic a #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))

(** SC — store-conditional: attempts to write if value unchanged.
    Success means old value matched expected (from LL).
    Failure may be spurious — no information about current value. *)
val sc (#a:eqtype) (r : B.box a) (new_val : a) (expected : a) (#cur : erased a)
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))

