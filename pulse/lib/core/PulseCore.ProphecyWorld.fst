(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Low-level nat-encoded prophecy world for PulseCore.

    This module is intentionally below the typed Pulse prophecy facade.  It
    contains no [result]/[payload] type parameters and no high-level atomic
    primitive resources.  It is the pure core representation that the active
    instantiated semantics/adequacy layer can own as one singleton world:

      * observations are nat-encoded;
      * a decoder extracts an untyped prophecy id and nat payload from an
        observation when the observation belongs to the singleton prophecy
        protocol;
      * allocation seeds a token stream from the current future observation
        suffix;
      * Resolve consumes the current observation head and advances the suffix.

    Typed [Pulse.Lib.Prophecy.Trace] views are projections/adapters over this
    shape.  Keeping this module untyped is the first representation step needed
    to avoid one authoritative prophecy map per public [(result, payload)]
    interface. *)
module PulseCore.ProphecyWorld

module NST = PulseCore.NondeterministicHoareStateMonad
open FStar.List.Tot

(** Singleton-world prophecy identifiers are allocated from
    [NST.prophecy_index]. *)
type proph_id = nat

(** Untyped decoded observation.  The payload remains nat-encoded; typed
    prophecy interfaces decode/project it further. *)
noeq type observation = {
  proph: proph_id;
  payload: nat;
}

type encoded_trace = list nat
type prediction_stream = list nat
type decoder = nat -> option observation
type proph_map = list (proph_id & prediction_stream)

let obs_payload (o:observation) : nat = o.payload

(** Projection of the future trace for one prophecy id.  This is the untyped
    analogue of Iris [proph_list_resolves]. *)
let rec list_resolves
    (decode:decoder)
    (pid:proph_id)
    (ks:encoded_trace)
  : Tot prediction_stream
    (decreases ks)
= match ks with
  | [] -> []
  | n :: ks' ->
    match decode n with
    | None -> list_resolves decode pid ks'
    | Some o ->
      if o.proph = pid
      then o.payload :: list_resolves decode pid ks'
      else list_resolves decode pid ks'

let rec lookup
    (pid:proph_id)
    (m:proph_map)
  : Tot (option prediction_stream)
    (decreases m)
= match m with
  | [] -> None
  | (pid', pvs) :: m' -> if pid = pid' then Some pvs else lookup pid m'

let rec contains
    (pid:proph_id)
    (m:proph_map)
  : Tot bool
    (decreases m)
= match m with
  | [] -> false
  | (pid', _) :: m' -> pid = pid' || contains pid m'

let fresh (pid:proph_id) (m:proph_map) : prop = contains pid m == false

let rec unique
    (m:proph_map)
  : Tot prop
    (decreases m)
= match m with
  | [] -> True
  | (pid, _) :: m' -> fresh pid m' /\ unique m'

let rec bounded
    (next:proph_id)
    (m:proph_map)
  : Tot prop
    (decreases m)
= match m with
  | [] -> True
  | (pid, _) :: m' -> pid < next /\ bounded next m'

let rec interp
    (decode:decoder)
    (ks:encoded_trace)
    (m:proph_map)
  : Tot prop
    (decreases m)
= match m with
  | [] -> True
  | (pid, pvs) :: m' ->
    pvs == list_resolves decode pid ks /\ interp decode ks m'

let alloc
    (decode:decoder)
    (pid:proph_id)
    (ks:encoded_trace)
    (m:proph_map)
  : proph_map
= (pid, list_resolves decode pid ks) :: m

let rec update
    (pid:proph_id)
    (tail:prediction_stream)
    (m:proph_map)
  : Tot proph_map
    (decreases m)
= match m with
  | [] -> []
  | (pid', pvs) :: m' ->
    if pid = pid'
    then (pid', tail) :: m'
    else (pid', pvs) :: update pid tail m'

(** Finite suffix of the active observation tape. *)
let rec trace_of_tape
    (ot:NST.obs_tape)
    (start:nat)
    (len:nat)
  : Tot encoded_trace
    (decreases len)
= if len = 0 then [] else ot start :: trace_of_tape ot (start + 1) (len - 1)

let trace_of_tape_cons
    (ot:NST.obs_tape)
    (start:nat)
    (len:nat)
  : Lemma
    (requires len > 0)
    (ensures trace_of_tape ot start len == ot start :: trace_of_tape ot (start + 1) (len - 1))
= ()

(** Core singleton-world view, deliberately untyped. *)
noeq type state_view = {
  world_decoder: decoder;
  world_future_trace: encoded_trace;
  world_token_map: proph_map;
  world_next_proph_id: proph_id;
  world_observation_index: nat;
}

let state_interp (st:state_view) : prop =
  interp st.world_decoder st.world_future_trace st.world_token_map /\
  unique st.world_token_map /\
  bounded st.world_next_proph_id st.world_token_map

(** [len] is the finite active suffix of the observation tape that the
    singleton prophecy world is allowed to decode.  The future trace equality
    records the concrete nat suffix used to seed prediction streams; the
    decoder-bounded side condition rules out fabricating a current Resolve event
    from a tape position outside that suffix.  In particular, if the current
    tape head decodes to a prophecy observation, then [len > 0] follows from the
    active world itself rather than from a Resolve-local boundary premise. *)
let decoder_bounded_from
    (decode:decoder)
    (ot:NST.obs_tape)
    (start:nat)
    (len:nat)
  : prop
= forall (i:nat) (o:observation). decode (ot (start + i)) == Some o ==> i < len

let runtime_matches_tape
    (st:state_view)
    (ot:NST.obs_tape)
    (len:nat)
  : prop
= st.world_future_trace == trace_of_tape ot st.world_observation_index len /\
  decoder_bounded_from st.world_decoder ot st.world_observation_index len

let decoder_bounded_from_bump
    (decode:decoder)
    (ot:NST.obs_tape)
    (start:nat)
    (len:nat)
  : Lemma
    (requires len > 0 /\ decoder_bounded_from decode ot start len)
    (ensures decoder_bounded_from decode ot (start + 1) (len - 1))
= assert (forall (i:nat). (start + 1) + i == start + (i + 1));
  assert (forall (i:nat). i + 1 < len ==> i < len - 1);
  assert (forall (i:nat) (o:observation). decode (ot ((start + 1) + i)) == Some o ==> i < len - 1)

let runtime_matches_ctr
    (st:state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
  : prop
= runtime_matches_tape st ot len /\
  st.world_observation_index == NST.observation_index c /\
  st.world_next_proph_id == NST.prophecy_index c

let alloc_view
    (st:state_view)
    (pid:proph_id)
  : state_view
= { st with
    world_token_map = alloc st.world_decoder pid st.world_future_trace st.world_token_map;
    world_next_proph_id = pid + 1 }

let rec bounded_weaken
    (old_next:proph_id)
    (new_next:proph_id)
    (m:proph_map)
  : Lemma
    (requires bounded old_next m /\ old_next <= new_next)
    (ensures bounded new_next m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid, _) :: m' -> bounded_weaken old_next new_next m'

let rec bounded_implies_fresh
    (next:proph_id)
    (m:proph_map)
  : Lemma
    (requires bounded next m)
    (ensures fresh next m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid, _) :: m' ->
    bounded_implies_fresh next m';
    assert (pid < next);
    assert (next = pid == false)

let interp_alloc_current
    (decode:decoder)
    (pid:proph_id)
    (ks:encoded_trace)
    (m:proph_map)
  : Lemma
    (requires interp decode ks m)
    (ensures interp decode ks (alloc decode pid ks m))
= ()

let unique_alloc_current
    (decode:decoder)
    (pid:proph_id)
    (ks:encoded_trace)
    (m:proph_map)
  : Lemma
    (requires fresh pid m /\ unique m)
    (ensures unique (alloc decode pid ks m))
= ()

let bounded_alloc_current
    (decode:decoder)
    (pid:proph_id)
    (ks:encoded_trace)
    (m:proph_map)
  : Lemma
    (requires bounded pid m)
    (ensures bounded (pid + 1) (alloc decode pid ks m))
= bounded_weaken pid (pid + 1) m

let lookup_alloc_current
    (decode:decoder)
    (pid:proph_id)
    (ks:encoded_trace)
    (m:proph_map)
  : Lemma
    (ensures lookup pid (alloc decode pid ks m) == Some (list_resolves decode pid ks))
= ()

(** Checked pure core allocation step for the active NewProph cursor.

    This is the untyped/nat-encoded analogue of Iris [proph_map_new_proph]:
    if the singleton world is tied to the active [NST.prophecy_index c], then
    allocating at that cursor preserves the authoritative map interpretation,
    records exactly the projected future stream for the returned id, and moves
    the runtime match to [NST.bump_prophecy c].  It is pure representation
    evidence; the remaining executable work is to make ordinary Pulse
    NewProph open an adequacy-owned resource satisfying these premises. *)
let alloc_current_step
    (st:state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
  : Lemma
    (requires state_interp st /\ runtime_matches_ctr st ot c len)
    (ensures (let pid = NST.prophecy_index c in
      let st' = alloc_view st pid in
      state_interp st' /\
      runtime_matches_ctr st' ot (NST.bump_prophecy c) len /\
      lookup pid st'.world_token_map == Some (list_resolves st.world_decoder pid st.world_future_trace)))
= let pid = NST.prophecy_index c in
  let st' = alloc_view st pid in
  assert (pid == st.world_next_proph_id);
  assert (bounded pid st.world_token_map);
  bounded_implies_fresh pid st.world_token_map;
  interp_alloc_current st.world_decoder pid st.world_future_trace st.world_token_map;
  unique_alloc_current st.world_decoder pid st.world_future_trace st.world_token_map;
  bounded_alloc_current st.world_decoder pid st.world_future_trace st.world_token_map;
  lookup_alloc_current st.world_decoder pid st.world_future_trace st.world_token_map;
  assert (st'.world_observation_index == st.world_observation_index);
  assert (st'.world_future_trace == st.world_future_trace);
  assert (decoder_bounded_from st'.world_decoder ot st'.world_observation_index len);
  assert (st'.world_next_proph_id == pid + 1);
  assert (NST.prophecy_index (NST.bump_prophecy c) == pid + 1);
  assert (NST.observation_index (NST.bump_prophecy c) == NST.observation_index c)

(** Repr-indexed version of [alloc_current_step] for the active
    [fresh_prophecy_id_obs_ctr] transition.

    This is the exact low-level NewProph fact needed by the Design-A runner
    path: the returned id and output counter are those produced by the real
    observation-tape/counter primitive, not by a caller-supplied ghost cursor.
    It remains pure representation evidence; the public Pulse prophecy rule
    still has to open/update a linear singleton authority resource using this
    same [ot,c]. *)
let alloc_current_obs_ctr_step (#s:Type)
    (st:state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires state_interp st /\ runtime_matches_ctr st ot c len)
    (ensures (let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at ot c in
      let pid = r._1 in
      let st' = alloc_view st pid in
      r._1 == NST.prophecy_index c /\
      r._2 == s0 /\
      r._3 == NST.bump_prophecy c /\
      state_interp st' /\
      runtime_matches_ctr st' ot r._3 len /\
      lookup pid st'.world_token_map == Some (list_resolves st.world_decoder pid st.world_future_trace)))
= let r = NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #s ()) s0 t at ot c in
  NST.fresh_prophecy_id_obs_ctr_result #s s0 t at ot c;
  assert (r._1 == NST.prophecy_index c);
  assert (r._2 == s0);
  assert (r._3 == NST.bump_prophecy c);
  alloc_current_step st ot c len

let alloc_fresh_view
    (st:state_view)
  : proph_id & state_view
= let pid = st.world_next_proph_id in
  pid, alloc_view st pid

let resolve_view
    (st:state_view)
    (pid:proph_id)
    (tail:prediction_stream)
    (ks:encoded_trace)
  : state_view
= { st with
    world_future_trace = ks;
    world_token_map = update pid tail st.world_token_map;
    world_observation_index = st.world_observation_index + 1 }

let current_observation_decodes_to
    (st:state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (pid:proph_id)
    (payload:nat)
  : prop
= st.world_decoder (ot (NST.observation_index c)) == Some { proph = pid; payload = payload }

let current_observation_decodes_to_implies_len_pos
    (st:state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
    (pid:proph_id)
    (payload:nat)
  : Lemma
    (requires runtime_matches_ctr st ot c len /\
      current_observation_decodes_to st ot c pid payload)
    (ensures len > 0)
= assert (decoder_bounded_from st.world_decoder ot st.world_observation_index len);
  assert (st.world_observation_index == NST.observation_index c);
  assert (st.world_observation_index + 0 == NST.observation_index c);
  let o = { proph = pid; payload = payload } in
  assert (st.world_decoder (ot (st.world_observation_index + 0)) == Some o);
  assert (0 < len)

let resolve_lookup_head_without_current_decoder ()
  : Lemma
    (ensures
      (let decode (n:nat) : option observation =
         match n with
         | 0 -> Some { proph = 1; payload = 99 }
         | 1 -> Some { proph = 0; payload = 42 }
         | _ -> None in
       let ot (i:nat) : nat = i in
       let st = {
         world_decoder = decode;
         world_future_trace = 0 :: 1 :: [];
         world_token_map = (0, 42 :: []) :: (1, 99 :: []) :: [];
         world_next_proph_id = 2;
         world_observation_index = 0 } in
       state_interp st /\
       runtime_matches_tape st ot 2 /\
       lookup 0 st.world_token_map == Some (42 :: []) /\
       ~(st.world_decoder (ot st.world_observation_index) == Some { proph = 0; payload = 42 })))
= let decode (n:nat) : option observation =
    match n with
    | 0 -> Some { proph = 1; payload = 99 }
    | 1 -> Some { proph = 0; payload = 42 }
    | _ -> None in
  let ot (i:nat) : nat = i in
  let st = {
    world_decoder = decode;
    world_future_trace = 0 :: 1 :: [];
    world_token_map = (0, 42 :: []) :: (1, 99 :: []) :: [];
    world_next_proph_id = 2;
    world_observation_index = 0 } in
  assert (decode 0 == Some { proph = 1; payload = 99 });
  assert (decode 1 == Some { proph = 0; payload = 42 });
  assert (list_resolves decode 0 (0 :: 1 :: []) == 42 :: []);
  assert (list_resolves decode 1 (0 :: 1 :: []) == 99 :: []);
  assert (interp decode (0 :: 1 :: []) st.world_token_map);
  assert (unique st.world_token_map);
  assert (bounded st.world_next_proph_id st.world_token_map);
  assert (lookup 0 st.world_token_map == Some (42 :: []));
  assert (st.world_future_trace == trace_of_tape ot st.world_observation_index 2);
  assert (forall (i:nat) (o:observation). decode (ot (st.world_observation_index + i)) == Some o ==> i < 2);
  assert (decoder_bounded_from decode ot st.world_observation_index 2);
  assert (runtime_matches_tape st ot 2);
  assert (~(st.world_decoder (ot st.world_observation_index) == Some { proph = 0; payload = 42 }))

let list_resolves_cons_current
    (decode:decoder)
    (pid:proph_id)
    (payload:nat)
    (n:nat)
    (ks:encoded_trace)
  : Lemma
    (requires decode n == Some { proph = pid; payload = payload })
    (ensures list_resolves decode pid (n :: ks) == payload :: list_resolves decode pid ks)
= ()

let list_resolves_cons_other
    (decode:decoder)
    (resolved_pid:proph_id)
    (pid:proph_id)
    (payload:nat)
    (n:nat)
    (ks:encoded_trace)
  : Lemma
    (requires decode n == Some { proph = resolved_pid; payload = payload } /\ pid <> resolved_pid)
    (ensures list_resolves decode pid (n :: ks) == list_resolves decode pid ks)
= ()

let rec contains_update
    (updated_pid:proph_id)
    (tail:prediction_stream)
    (query_pid:proph_id)
    (m:proph_map)
  : Lemma
    (ensures contains query_pid (update updated_pid tail m) == contains query_pid m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' -> contains_update updated_pid tail query_pid m'

let rec unique_update
    (pid:proph_id)
    (tail:prediction_stream)
    (m:proph_map)
  : Lemma
    (requires unique m)
    (ensures unique (update pid tail m))
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' ->
    contains_update pid tail pid' m';
    unique_update pid tail m'

let rec bounded_update
    (next:proph_id)
    (pid:proph_id)
    (tail:prediction_stream)
    (m:proph_map)
  : Lemma
    (requires bounded next m)
    (ensures bounded next (update pid tail m))
    (decreases m)
= match m with
  | [] -> ()
  | (_, _) :: m' -> bounded_update next pid tail m'

let rec lookup_update_hit
    (pid:proph_id)
    (old:prediction_stream)
    (tail:prediction_stream)
    (m:proph_map)
  : Lemma
    (requires lookup pid m == Some old)
    (ensures lookup pid (update pid tail m) == Some tail)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' ->
    if pid = pid'
    then ()
    else lookup_update_hit pid old tail m'

let rec interp_drop_resolved_head_for_fresh
    (decode:decoder)
    (resolved_pid:proph_id)
    (payload:nat)
    (n:nat)
    (ks:encoded_trace)
    (m:proph_map)
  : Lemma
    (requires interp decode (n :: ks) m /\
              fresh resolved_pid m /\
              decode n == Some { proph = resolved_pid; payload = payload })
    (ensures interp decode ks m)
    (decreases m)
= match m with
  | [] -> ()
  | (pid', _) :: m' ->
    assert (pid' <> resolved_pid);
    list_resolves_cons_other decode resolved_pid pid' payload n ks;
    interp_drop_resolved_head_for_fresh decode resolved_pid payload n ks m'

let rec interp_update_resolved_head
    (decode:decoder)
    (pid:proph_id)
    (payload:nat)
    (tail:prediction_stream)
    (n:nat)
    (ks:encoded_trace)
    (m:proph_map)
  : Lemma
    (requires interp decode (n :: ks) m /\
              unique m /\
              decode n == Some { proph = pid; payload = payload } /\
              lookup pid m == Some (payload :: tail))
    (ensures interp decode ks (update pid tail m))
    (decreases m)
= match m with
  | [] -> ()
  | (pid', pvs) :: m' ->
    if pid = pid'
    then (
      assert (pvs == payload :: tail);
      list_resolves_cons_current decode pid payload n ks;
      assert (tail == list_resolves decode pid ks);
      interp_drop_resolved_head_for_fresh decode pid payload n ks m')
    else (
      assert (pid' <> pid);
      list_resolves_cons_other decode pid pid' payload n ks;
      interp_update_resolved_head decode pid payload tail n ks m')

(** Checked pure core Resolve step for the active observation cursor.

    This is the untyped/nat-encoded analogue of Iris
    [proph_map_resolve_proph] at the current observation head.  If the singleton
    world is tied to the active observation cursor, the current tape head
    decodes to the prophecy being resolved, and the authoritative map stores a
    stream whose head is that payload, then Resolve updates only that map entry,
    advances the observation suffix/cursor, preserves the authoritative
    invariant, and exposes the tail lookup for the client fragment.  Like
    [alloc_current_step], this is pure representation evidence; public Resolve
    still has to open the adequacy-owned singleton resource and obtain the
    current decode fact from the real [ObservedResultAct] step. *)
let resolve_current_step
    (st:state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
    (pid:proph_id)
    (payload:nat)
    (tail:prediction_stream)
  : Lemma
    (requires state_interp st /\
              runtime_matches_ctr st ot c len /\
              len > 0 /\
              current_observation_decodes_to st ot c pid payload /\
              lookup pid st.world_token_map == Some (payload :: tail))
    (ensures (let ks = trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let st' = resolve_view st pid tail ks in
      state_interp st' /\
      runtime_matches_ctr st' ot (NST.bump_observation c) (len - 1) /\
      lookup pid st'.world_token_map == Some tail))
= let n = ot (NST.observation_index c) in
  let ks = trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
  trace_of_tape_cons ot (NST.observation_index c) len;
  assert (st.world_future_trace == n :: ks);
  interp_update_resolved_head st.world_decoder pid payload tail n ks st.world_token_map;
  unique_update pid tail st.world_token_map;
  bounded_update st.world_next_proph_id pid tail st.world_token_map;
  lookup_update_hit pid (payload :: tail) tail st.world_token_map;
  let st' = resolve_view st pid tail ks in
  assert (st'.world_future_trace == ks);
  decoder_bounded_from_bump st.world_decoder ot st.world_observation_index len;
  assert (st'.world_observation_index == st.world_observation_index + 1);
  assert (decoder_bounded_from st'.world_decoder ot st'.world_observation_index (len - 1));
  assert (st.world_observation_index == NST.observation_index c);
  assert (NST.observation_index (NST.bump_observation c) == NST.observation_index c + 1);
  assert (st'.world_next_proph_id == st.world_next_proph_id);
  assert (NST.prophecy_index (NST.bump_observation c) == NST.prophecy_index c)

(** Repr-indexed version of [resolve_current_step] for the active
    [observe_obs_ctr] transition.

    This is the untyped event/counter fact that the final Resolve adequacy rule
    must use instead of a boundary-local current-head witness: the consumed
    observation is exactly [ot (NST.observation_index c)], the output counter is
    exactly [NST.bump_observation c], and the singleton world update is the
    checked current-head Resolve update above.  It does not manufacture the
    decoder fact; callers must still obtain [current_observation_decodes_to]
    from the active singleton state interpretation and the result-dependent
    observation decoder. *)
let resolve_current_obs_ctr_step (#s:Type)
    (st:state_view)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (len:nat)
    (pid:proph_id)
    (payload:nat)
    (tail:prediction_stream)
    (s0:s)
    (t:nat -> bool)
    (at:nat -> nat)
  : Lemma
    (requires state_interp st /\
              runtime_matches_ctr st ot c len /\
              len > 0 /\
              current_observation_decodes_to st ot c pid payload /\
              lookup pid st.world_token_map == Some (payload :: tail))
    (ensures (let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at ot c in
      let ks = trace_of_tape ot (NST.observation_index c + 1) (len - 1) in
      let st' = resolve_view st pid tail ks in
      r._1 == ot (NST.observation_index c) /\
      r._2 == s0 /\
      r._3 == NST.bump_observation c /\
      state_interp st' /\
      runtime_matches_ctr st' ot r._3 (len - 1) /\
      lookup pid st'.world_token_map == Some tail))
= let r = NST.repr_obs_ctr (NST.observe_obs_ctr #s ()) s0 t at ot c in
  NST.observe_obs_ctr_result #s s0 t at ot c;
  assert (r._1 == ot (NST.observation_index c));
  assert (r._2 == s0);
  assert (r._3 == NST.bump_observation c);
  resolve_current_step st ot c len pid payload tail
