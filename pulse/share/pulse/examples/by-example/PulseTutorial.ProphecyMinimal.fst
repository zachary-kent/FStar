(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Minimal client of the Iris-style prophecy facade.

    This is intentionally small: it demonstrates the end-to-end Resolve rule on
    a single atomic read before porting larger examples such as AtomicSnapshot
    and RDCSS.  The client starts from an explicit non-empty prophecy token,
    runs one observable atomic read, and receives both the tail token and the
    equality between the predicted head and the physical result.

    [alloc_prophecy] exercises the allocation rule itself, and
    [alloc_and_resolve_atomic_read] is the end-to-end allocation-to-resolution
    path: it opens the existential prediction stream from allocation and uses
    the Iris-rule Resolve form to learn the non-empty head without executable
    branching on the erased stream. *)
module PulseTutorial.ProphecyMinimal
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module AP = Pulse.Lib.AtomicPrimitives
module P = Pulse.Lib.Prophecy
module U32 = FStar.UInt32
module NST = PulseCore.NondeterministicHoareStateMonad

let zero_nat : nat = 0
let one_nat : nat = 1
let false_scheduler (_:nat) : bool = false
let zero_angel (_:nat) : nat = zero_nat

let single_u32_decoder (v:U32.t) (n:int)
  : option (P.proph_id & (U32.t & unit))
= if n = zero_nat then Some (zero_nat, (v, ())) else None

let single_u32_initial_state (v:U32.t)
  : P.proph_state_view_encoded U32.t unit
= { encoded_decoder = single_u32_decoder v;
    encoded_future_trace = zero_nat :: [];
    encoded_token_map = [];
    encoded_next_proph_id = zero_nat;
    encoded_observation_index = zero_nat }

let single_u32_initial_state_interp (v:U32.t)
  : Lemma (ensures P.proph_state_interp_encoded (single_u32_initial_state v))
= ()

let single_u32_initial_projection (v:U32.t)
  : Lemma
    (ensures P.proph_list_resolves_encoded
      (single_u32_decoder v) zero_nat (zero_nat :: []) == (v, ()) :: [])
= assert_norm (single_u32_decoder v zero_nat == Some (zero_nat, (v, ())));
  P.resolve_head_encoded_couples (single_u32_decoder v) zero_nat (v, ()) zero_nat []

let single_u32_current_repr_authority_step (v:U32.t)
    (#c:erased NST.ctr)
    (#ot:erased (nat -> nat))
  : Lemma
    (requires NST.prophecy_index (reveal c) == zero_nat /\
              NST.observation_index (reveal c) == zero_nat /\
              reveal ot (NST.observation_index (reveal c)) == zero_nat)
    (ensures True)
= let initial = single_u32_initial_state v in
  let allocated = snd (P.proph_state_alloc_fresh_view_encoded initial) in
  let sched (_:nat) = false in
  let angels (_:nat) = zero_nat in
  single_u32_initial_projection v;
  single_u32_initial_state_interp v;
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) one_nat;
  assert (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) one_nat);
  P.proph_state_alloc_fresh_repr_authority_step_encoded #U32.t #unit #unit initial
    (reveal ot) (reveal c) one_nat () sched angels;
  let alloc_r = NST.repr (NST.fresh_prophecy_id #unit ()) () sched angels (reveal ot) (reveal c) in
  assert (alloc_r._1 == zero_nat);
  assert (alloc_r._3 == NST.bump_prophecy (reveal c));
  assert (P.proph_state_interp_encoded allocated);
  assert (P.proph_state_runtime_matches_ctr_encoded allocated (reveal ot) alloc_r._3 one_nat);
  assert (P.proph_state_runtime_matches_ctr_encoded allocated (reveal ot) (NST.bump_prophecy (reveal c)) one_nat);
  assert (P.proph_map_lookup zero_nat allocated.encoded_token_map == Some ((v, ()) :: []));
  assert (allocated.encoded_decoder (reveal ot (NST.observation_index (NST.bump_prophecy (reveal c)))) ==
    Some (zero_nat, (v, ())));
  P.proph_state_resolve_observe_repr_current_authority_step_encoded #U32.t #unit #unit allocated zero_nat v v () []
    (reveal ot) (NST.bump_prophecy (reveal c)) one_nat () sched angels

let single_u32_current_repr_ctr_authority_step (v:U32.t)
    (#c:erased NST.ctr)
    (#ot:erased (nat -> nat))
  : Lemma
    (requires NST.prophecy_index (reveal c) == zero_nat /\
              NST.observation_index (reveal c) == zero_nat /\
              reveal ot (NST.observation_index (reveal c)) == zero_nat)
    (ensures True)
= let initial = single_u32_initial_state v in
  let allocated = snd (P.proph_state_alloc_fresh_view_encoded initial) in
  let sched (_:nat) = false in
  let angels (_:nat) = zero_nat in
  single_u32_initial_projection v;
  single_u32_initial_state_interp v;
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) one_nat;
  assert (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) one_nat);
  P.proph_state_alloc_fresh_repr_ctr_authority_step_encoded #U32.t #unit #unit initial
    (reveal ot) (reveal c) one_nat () sched angels;
  let alloc_r = NST.repr_ctr (NST.fresh_prophecy_id_ctr #unit ()) () sched angels (reveal ot) (reveal c) in
  assert (alloc_r._1 == zero_nat);
  assert (alloc_r._3 == NST.bump_prophecy (reveal c));
  assert (P.proph_state_interp_encoded allocated);
  assert (P.proph_state_runtime_matches_ctr_encoded allocated (reveal ot) alloc_r._3 one_nat);
  assert (P.proph_state_runtime_matches_ctr_encoded allocated (reveal ot) (NST.bump_prophecy (reveal c)) one_nat);
  assert (P.proph_map_lookup zero_nat allocated.encoded_token_map == Some ((v, ()) :: []));
  assert (allocated.encoded_decoder (reveal ot (NST.observation_index (NST.bump_prophecy (reveal c)))) ==
    Some (zero_nat, (v, ())));
  P.proph_state_resolve_observe_repr_ctr_current_authority_step_encoded #U32.t #unit #unit allocated zero_nat v v () []
    (reveal ot) (NST.bump_prophecy (reveal c)) one_nat () sched angels

(** Witness-free shared-authority resource slice.

    This ghost-only model does not allocate an operational NewProph or run a
    physical Resolve step.  It demonstrates the already verified resource path
    that the remaining foundational state-interpretation work must expose to
    the public primitive: one shared authoritative prophecy state allocates a
    fresh token fragment, the token stream is projected from the shared future
    observation suffix, and Resolve updates the same shared authority plus the
    token fragment using explicit observation-head facts rather than either of
    the boundary-local public witnesses. *)
ghost fn shared_authority_single_observation_model (v:U32.t)
  requires emp
  ensures emp
{
  single_u32_initial_projection v;
  single_u32_initial_state_interp v;
  let auth = P.prophecy_authority_init #U32.t #unit #(single_u32_initial_state v);
  let p = P.prophecy_authority_alloc #U32.t #unit auth #(single_u32_initial_state v);
  rewrite each (P.proph_list_resolves_encoded (single_u32_initial_state v).encoded_decoder
    (single_u32_initial_state v).encoded_next_proph_id
    (single_u32_initial_state v).encoded_future_trace) as ((v, ()) :: []);
  let allocated = snd (P.proph_state_alloc_fresh_view_encoded (single_u32_initial_state v));
  assert pure (P.prophecy_id_of p == (single_u32_initial_state v).encoded_next_proph_id /\
    P.prophecy_bound_to_authority auth p /\
    P.proph_map_lookup (single_u32_initial_state v).encoded_next_proph_id allocated.encoded_token_map == Some ((v, ()) :: []));
  assert_norm ((single_u32_initial_state v).encoded_next_proph_id == zero_nat);
  assert pure (P.prophecy_id_of p == zero_nat);
  assert pure (P.prophecy_bound_to_authority auth p);
  assert pure (P.proph_map_lookup (P.prophecy_id_of p) allocated.encoded_token_map == Some ((v, ()) :: []));
  assert pure (allocated.encoded_future_trace == zero_nat :: []);
  assert pure (allocated.encoded_decoder zero_nat == Some (zero_nat, (v, ())));
  assert pure (allocated.encoded_decoder zero_nat == Some (P.prophecy_id_of p, (v, ())));
  P.prophecy_authority_resolve_observed #U32.t #unit auth p ()
    #(snd (P.proph_state_alloc_fresh_view_encoded (single_u32_initial_state v)))
    #((v, ()) :: []) v zero_nat #[] #[];
  drop_ (P.prophecy_authority_state auth
    (P.proph_state_resolve_view_encoded
      (snd (P.proph_state_alloc_fresh_view_encoded (single_u32_initial_state v)))
      (P.prophecy_id_of p) [] []));
  drop_ (P.prophecy_token_fragment p []);
  ()
}

(** Counter-aware shared-authority slice.

    This variant is still ghost-only, but it uses the new runtime-state
    resource instead of passing the NewProph old-state cursor fact and Resolve
    observation-head/tail facts directly to the allocation/Resolve helpers.  The
    allocation id is obtained from [NST.prophecy_index c].  Resolve now uses
    [prophecy_authority_resolve_current], so the consumed nat is derived from
    the active observation tape at [NST.observation_index] rather than being
    passed as a separate boundary-style witness argument. *)
ghost fn shared_authority_runtime_single_observation_model
    (v:U32.t)
    (#c:erased NST.ctr)
    (#ot:erased (nat -> nat))
  requires pure (NST.prophecy_index (reveal c) == zero_nat /\
                  NST.observation_index (reveal c) == zero_nat /\
                  reveal ot (NST.observation_index (reveal c)) == zero_nat)
  ensures emp
{
  let initial = single_u32_initial_state v;
  single_u32_initial_projection v;
  single_u32_initial_state_interp v;
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) one_nat;
  assert pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) one_nat);
  let auth = P.prophecy_authority_init #U32.t #unit #initial;
  assert (P.prophecy_authority_state auth initial **
    pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) one_nat));
  rewrite (P.prophecy_authority_state auth initial **
           pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) one_nat)) as
          (P.prophecy_authority_runtime_state auth initial (reveal ot) (reveal c) one_nat);

  let p = P.prophecy_authority_alloc_runtime #U32.t #unit auth #initial #ot #c #one_nat;
  let allocated = snd (P.proph_state_alloc_fresh_view_encoded initial);
  rewrite (P.prophecy_authority_runtime_state auth (snd (P.proph_state_alloc_fresh_view_encoded initial))
            (reveal ot) (NST.bump_prophecy (reveal c)) one_nat) as
          (P.prophecy_authority_runtime_state auth allocated
            (reveal ot) (NST.bump_prophecy (reveal c)) one_nat);
  rewrite (P.prophecy_token_fragment p
    (P.proph_list_resolves_encoded initial.encoded_decoder (NST.prophecy_index (reveal c)) initial.encoded_future_trace)) as
          (P.prophecy_token_fragment p ((v, ()) :: []));
  assert pure (P.prophecy_id_of p == zero_nat);
  assert pure (P.prophecy_bound_to_authority auth p);
  assert pure (P.proph_map_lookup (P.prophecy_id_of p) allocated.encoded_token_map == Some ((v, ()) :: []));
  assert pure (allocated.encoded_decoder zero_nat == Some (P.prophecy_id_of p, (v, ())));
  assert pure (zero_nat == reveal ot (NST.observation_index (NST.bump_prophecy (reveal c))));
  let tail = P.prophecy_authority_resolve_current #U32.t #unit auth p ()
    #allocated #ot #(NST.bump_prophecy (reveal c)) #one_nat #((v, ()) :: []) v;
  assert pure (reveal tail == []);
  assert pure (P.encoded_trace_of_tape (reveal ot)
    (NST.observation_index (NST.bump_prophecy (reveal c)) + 1) (one_nat - 1) == []);
  rewrite each (reveal tail) as [];
  rewrite (P.prophecy_authority_runtime_state auth
            (P.proph_state_resolve_view_encoded allocated (P.prophecy_id_of p) []
              (P.encoded_trace_of_tape (reveal ot)
                (NST.observation_index (NST.bump_prophecy (reveal c)) + 1) (one_nat - 1)))
            (reveal ot) (NST.bump_observation (NST.bump_prophecy (reveal c))) (one_nat - 1)) as
          (P.prophecy_authority_runtime_state auth
            (P.proph_state_resolve_view_encoded allocated (P.prophecy_id_of p) [] [])
            (reveal ot) (NST.bump_observation (NST.bump_prophecy (reveal c))) zero_nat);
  drop_ (P.prophecy_authority_runtime_state auth
    (P.proph_state_resolve_view_encoded allocated (P.prophecy_id_of p) [] [])
    (reveal ot) (NST.bump_observation (NST.bump_prophecy (reveal c))) zero_nat);
  drop_ (P.prophecy_token_fragment p []);
  ()
}

(** Packaged active-component slice.

    This regression uses the Round 9 component-preserving wrappers: allocation
    and Resolve consume and return one packaged adequacy component instead of a
    loose authority/state/length triple.  It is still ghost-only, but it is the
    exact resource shape the active state interpretation should own when the two
    remaining public witnesses are removed. *)
ghost fn active_component_single_observation_model
    (v:U32.t)
    (#c:erased NST.ctr)
    (#ot:erased (nat -> nat))
  requires pure (NST.prophecy_index (reveal c) == zero_nat /\
                  NST.observation_index (reveal c) == zero_nat /\
                  reveal ot (NST.observation_index (reveal c)) == zero_nat)
  ensures emp
{
  let initial = single_u32_initial_state v;
  single_u32_initial_projection v;
  single_u32_initial_state_interp v;
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) one_nat;
  assert pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) one_nat);
  let comp0 = P.prophecy_active_component_init #U32.t #unit #initial #ot #c #one_nat;
  let p = P.prophecy_active_component_alloc_obs_ctr_component #U32.t #unit #unit
    comp0 #ot #c () false_scheduler zero_angel;
  let comp1 = P.prophecy_active_component_after_alloc comp0;
  assert pure (comp1.component_len == one_nat);
  assert pure (P.prophecy_id_of p == zero_nat);
  assert pure (P.prophecy_component_bound comp1 p);
  assert pure (comp0.component_state_view == initial);
  rewrite (P.prophecy_token_fragment p
    (P.proph_list_resolves_encoded comp0.component_state_view.encoded_decoder (NST.prophecy_index (reveal c)) comp0.component_state_view.encoded_future_trace)) as
          (P.prophecy_token_fragment p
            (P.proph_list_resolves_encoded initial.encoded_decoder (NST.prophecy_index (reveal c)) initial.encoded_future_trace));
  rewrite (P.prophecy_token_fragment p
    (P.proph_list_resolves_encoded initial.encoded_decoder (NST.prophecy_index (reveal c)) initial.encoded_future_trace)) as
          (P.prophecy_token_fragment p ((v, ()) :: []));
  assert pure (P.prophecy_component_lookup comp1 p ((v, ()) :: []));
  assert pure (comp1.component_state_view.encoded_decoder zero_nat == Some (P.prophecy_id_of p, (v, ())));
  assert pure (zero_nat == reveal ot (NST.observation_index (NST.bump_prophecy (reveal c))));
  assert pure ((NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #unit ()) () false_scheduler zero_angel (reveal ot) (reveal c))._3 == NST.bump_prophecy (reveal c));
  assert pure (comp1 == P.prophecy_active_component_after_alloc comp0);
  rewrite (P.prophecy_active_component_interp (P.prophecy_active_component_after_alloc comp0) (reveal ot)
            (NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #unit ()) () false_scheduler zero_angel (reveal ot) (reveal c))._3) as
          (P.prophecy_active_component_interp comp1 (reveal ot) (NST.bump_prophecy (reveal c)));
  let tail = P.prophecy_active_component_resolve_obs_ctr_component #U32.t #unit #unit
    comp1 p () #((v, ()) :: []) v () false_scheduler zero_angel #ot #(NST.bump_prophecy (reveal c));
  assert pure (reveal tail == []);
  let comp2 = P.prophecy_active_component_after_resolve comp1 p (reveal tail) (reveal ot) (NST.bump_prophecy (reveal c));
  assert pure (comp2.component_len == zero_nat);
  rewrite each (reveal tail) as [];
  assert pure ((NST.repr_obs_ctr (NST.observe_obs_ctr #unit ()) () false_scheduler zero_angel (reveal ot) (NST.bump_prophecy (reveal c)))._3 ==
    NST.bump_observation (NST.bump_prophecy (reveal c)));
  assert pure (comp2 == P.prophecy_active_component_after_resolve comp1 p [] (reveal ot) (NST.bump_prophecy (reveal c)));
  rewrite (P.prophecy_active_component_interp
            (P.prophecy_active_component_after_resolve comp1 p [] (reveal ot) (NST.bump_prophecy (reveal c)))
            (reveal ot)
            (NST.repr_obs_ctr (NST.observe_obs_ctr #unit ()) () false_scheduler zero_angel (reveal ot) (NST.bump_prophecy (reveal c)))._3) as
          (P.prophecy_active_component_interp comp2 (reveal ot)
            (NST.bump_observation (NST.bump_prophecy (reveal c))));
  drop_ (P.prophecy_active_component_interp comp2 (reveal ot)
    (NST.bump_observation (NST.bump_prophecy (reveal c))));
  drop_ (P.prophecy_token_fragment p []);
  ()
}

let two_u32_decoder (v0 v1:U32.t) (n:nat)
  : option (P.proph_id & (U32.t & unit))
= if n = zero_nat then Some (zero_nat, (v0, ()))
  else if n = one_nat then Some (one_nat, (v1, ()))
  else None

let two_u32_initial_state (v0 v1:U32.t)
  : P.proph_state_view_encoded U32.t unit
= { encoded_decoder = two_u32_decoder v0 v1;
    encoded_future_trace = zero_nat :: one_nat :: [];
    encoded_token_map = [];
    encoded_next_proph_id = zero_nat;
    encoded_observation_index = zero_nat }

let two_u32_initial_state_interp (v0 v1:U32.t)
  : Lemma (ensures P.proph_state_interp_encoded (two_u32_initial_state v0 v1))
= ()

let two_u32_initial_projection_first (v0 v1:U32.t)
  : Lemma
    (ensures P.proph_list_resolves_encoded
      (two_u32_decoder v0 v1) zero_nat (zero_nat :: one_nat :: []) == (v0, ()) :: [])
= assert_norm (two_u32_decoder v0 v1 zero_nat == Some (zero_nat, (v0, ())));
  P.resolve_head_encoded_couples (two_u32_decoder v0 v1) zero_nat (v0, ()) zero_nat (one_nat :: []);
  P.resolve_head_encoded_frames_other (two_u32_decoder v0 v1) zero_nat one_nat (v0, ()) zero_nat (one_nat :: [])

let two_u32_initial_projection_second (v0 v1:U32.t)
  : Lemma
    (ensures P.proph_list_resolves_encoded
      (two_u32_decoder v0 v1) one_nat (zero_nat :: one_nat :: []) == (v1, ()) :: [])
= assert_norm (two_u32_decoder v0 v1 zero_nat == Some (zero_nat, (v0, ())));
  assert_norm (two_u32_decoder v0 v1 one_nat == Some (one_nat, (v1, ())));
  P.resolve_head_encoded_frames_other (two_u32_decoder v0 v1) zero_nat one_nat (v0, ()) zero_nat (one_nat :: []);
  P.resolve_head_encoded_couples (two_u32_decoder v0 v1) one_nat (v1, ()) one_nat []

let two_u32_tail_projection_second (v0 v1:U32.t)
  : Lemma
    (ensures P.proph_list_resolves_encoded
      (two_u32_decoder v0 v1) one_nat (one_nat :: []) == (v1, ()) :: [])
= assert_norm (two_u32_decoder v0 v1 one_nat == Some (one_nat, (v1, ())));
  P.resolve_head_encoded_couples (two_u32_decoder v0 v1) one_nat (v1, ()) one_nat []

(** Current-counter active-component allocation framing model.

    This regression uses the executable-current component allocation rule, not
    the [repr_obs_ctr] wrapper: after one checked allocation at
    [NST.prophecy_index c], a second checked allocation at
    [NST.prophecy_index (NST.bump_prophecy c)] frames the first token through
    the same singleton active component.  This is the local resource shape that
    the remaining public NewProph opening seam must expose from adequacy. *)
ghost fn active_component_current_two_allocation_framing_model
    (v0 v1:U32.t)
    (#c:erased NST.ctr)
    (#ot:erased (nat -> nat))
  requires pure (NST.prophecy_index (reveal c) == zero_nat /\
                  NST.observation_index (reveal c) == zero_nat /\
                  reveal ot zero_nat == zero_nat /\
                  reveal ot one_nat == one_nat)
  ensures emp
{
  let initial = two_u32_initial_state v0 v1;
  two_u32_initial_projection_first v0 v1;
  two_u32_initial_projection_second v0 v1;
  two_u32_initial_state_interp v0 v1;
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) (one_nat + one_nat);
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c) + 1) one_nat;
  assert pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) (one_nat + one_nat));
  let comp0 = P.prophecy_active_component_init #U32.t #unit #initial #ot #c #(one_nat + one_nat);

  let p0 = P.prophecy_active_component_alloc_obs_ctr_component #U32.t #unit #unit
    comp0 #ot #c () false_scheduler zero_angel;
  let comp1 = P.prophecy_active_component_after_alloc comp0;
  assert pure ((NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #unit ()) () false_scheduler zero_angel (reveal ot) (reveal c))._3 ==
    NST.bump_prophecy (reveal c));
  rewrite (P.prophecy_active_component_interp (P.prophecy_active_component_after_alloc comp0)
            (reveal ot)
            (NST.repr_obs_ctr (NST.fresh_prophecy_id_obs_ctr #unit ()) () false_scheduler zero_angel (reveal ot) (reveal c))._3) as
          (P.prophecy_active_component_interp comp1 (reveal ot) (NST.bump_prophecy (reveal c)));
  rewrite (P.prophecy_token_fragment p0
    (P.proph_list_resolves_encoded comp0.component_state_view.encoded_decoder (NST.prophecy_index (reveal c)) comp0.component_state_view.encoded_future_trace)) as
          (P.prophecy_token_fragment p0 ((v0, ()) :: []));
  assert pure (P.prophecy_id_of p0 == zero_nat);
  assert pure (P.prophecy_component_bound comp1 p0);
  assert pure (P.prophecy_component_lookup comp1 p0 ((v0, ()) :: []));
  assert pure (P.prophecy_id_of p0 <> NST.prophecy_index (NST.bump_prophecy (reveal c)));

  let p1 = P.prophecy_active_component_alloc_current_component_frame #U32.t #unit
    comp1 one_nat #ot #(NST.bump_prophecy (reveal c)) p0 #((v0, ()) :: []);
  let comp2 = P.prophecy_active_component_after_alloc comp1;
  rewrite (P.prophecy_active_component_interp (P.prophecy_active_component_after_alloc comp1)
            (reveal ot) (NST.bump_prophecy (NST.bump_prophecy (reveal c)))) as
          (P.prophecy_active_component_interp comp2 (reveal ot)
            (NST.bump_prophecy (NST.bump_prophecy (reveal c))));
  rewrite (P.prophecy_token_fragment p1
    (P.proph_list_resolves_encoded comp1.component_state_view.encoded_decoder
      (NST.prophecy_index (NST.bump_prophecy (reveal c))) comp1.component_state_view.encoded_future_trace)) as
          (P.prophecy_token_fragment p1 ((v1, ()) :: []));
  assert pure (P.prophecy_id_of p1 == one_nat);
  assert pure (P.prophecy_component_bound comp2 p0);
  assert pure (P.prophecy_component_bound comp2 p1);
  assert pure (P.prophecy_component_lookup comp2 p0 ((v0, ()) :: []));
  assert pure (P.prophecy_component_lookup comp2 p1 ((v1, ()) :: []));
  drop_ (P.prophecy_active_component_interp comp2 (reveal ot)
    (NST.bump_prophecy (NST.bump_prophecy (reveal c))));
  drop_ (P.prophecy_token_fragment p0 ((v0, ()) :: []));
  drop_ (P.prophecy_token_fragment p1 ((v1, ()) :: []));
  ()
}

let two_u32_second_allocation_repr_frames_first (v0 v1:U32.t)
    (#c:erased NST.ctr)
    (#ot:erased (nat -> nat))
  : Lemma
    (requires NST.prophecy_index (reveal c) == zero_nat /\
              NST.observation_index (reveal c) == zero_nat /\
              reveal ot zero_nat == zero_nat /\
              reveal ot one_nat == one_nat)
    (ensures True)
= let initial = two_u32_initial_state v0 v1 in
  let sched (_:nat) = false in
  let angels (_:nat) = zero_nat in
  two_u32_initial_projection_first v0 v1;
  two_u32_initial_projection_second v0 v1;
  two_u32_initial_state_interp v0 v1;
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) (one_nat + one_nat);
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c) + 1) one_nat;
  assert (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) (one_nat + one_nat));
  P.proph_state_alloc_fresh_repr_authority_step_encoded #U32.t #unit #unit initial
    (reveal ot) (reveal c) (one_nat + one_nat) () sched angels;
  let st1 = snd (P.proph_state_alloc_fresh_view_encoded initial) in
  assert (P.proph_state_runtime_matches_ctr_encoded st1 (reveal ot) (NST.bump_prophecy (reveal c)) (one_nat + one_nat));
  assert (P.proph_map_lookup zero_nat st1.encoded_token_map == Some ((v0, ()) :: []));
  assert (NST.prophecy_index (NST.bump_prophecy (reveal c)) == one_nat);
  P.proph_state_alloc_fresh_repr_authority_step_frames_lookup_encoded #U32.t #unit #unit st1
    zero_nat ((v0, ()) :: []) (reveal ot) (NST.bump_prophecy (reveal c)) (one_nat + one_nat) () sched angels;
  let st2 = snd (P.proph_state_alloc_fresh_view_encoded st1) in
  assert (P.proph_map_lookup zero_nat st2.encoded_token_map == Some ((v0, ()) :: []));
  assert (P.proph_map_lookup one_nat st2.encoded_token_map == Some ((v1, ()) :: []))

(** Two-token shared-authority framing model.

    This is the smallest verified singleton-authority slice that involves more
    than one prophecy variable: both allocations update the same authoritative
    encoded prophecy state, resolving the first prophecy consumes only the
    global observation head for that id, and the second prophecy's token
    fragment is framed and remains resolvable from the same authority state.
    No boundary-local NewProph/Resolve witness is used here; all old-state,
    projection, lookup-preservation, and observed-head facts are explicit pure
    premises discharged by [Pulse.Lib.Prophecy.Trace] lemmas. *)
ghost fn shared_authority_two_observation_framing_model (v0 v1:U32.t)
  requires emp
  ensures emp
{
  let initial = two_u32_initial_state v0 v1;
  two_u32_initial_projection_first v0 v1;
  two_u32_initial_projection_second v0 v1;
  two_u32_tail_projection_second v0 v1;
  two_u32_initial_state_interp v0 v1;
  let auth = P.prophecy_authority_init #U32.t #unit #initial;

  let p0 = P.prophecy_authority_alloc #U32.t #unit auth #initial;
  let st1 = snd (P.proph_state_alloc_fresh_view_encoded initial);
  rewrite (P.prophecy_authority_state auth (snd (P.proph_state_alloc_fresh_view_encoded initial))) as
          (P.prophecy_authority_state auth st1);
  rewrite (P.prophecy_token_fragment p0
    (P.proph_list_resolves_encoded initial.encoded_decoder initial.encoded_next_proph_id initial.encoded_future_trace)) as
          (P.prophecy_token_fragment p0 ((v0, ()) :: []));
  assert pure (P.prophecy_id_of p0 == zero_nat);
  assert pure (P.prophecy_bound_to_authority auth p0);
  assert pure (P.proph_map_lookup zero_nat st1.encoded_token_map == Some ((v0, ()) :: []));

  let p1 = P.prophecy_authority_alloc #U32.t #unit auth #st1;
  let st2 = snd (P.proph_state_alloc_fresh_view_encoded st1);
  rewrite (P.prophecy_authority_state auth (snd (P.proph_state_alloc_fresh_view_encoded st1))) as
          (P.prophecy_authority_state auth st2);
  rewrite (P.prophecy_token_fragment p1
    (P.proph_list_resolves_encoded st1.encoded_decoder st1.encoded_next_proph_id st1.encoded_future_trace)) as
          (P.prophecy_token_fragment p1 ((v1, ()) :: []));
  assert pure (P.prophecy_id_of p1 == one_nat);
  assert pure (P.prophecy_bound_to_authority auth p1);
  assert pure (P.proph_map_lookup one_nat st2.encoded_token_map == Some ((v1, ()) :: []));

  P.proph_state_alloc_fresh_view_encoded_preserves_lookup st1 zero_nat ((v0, ()) :: []);
  assert pure (P.proph_map_lookup zero_nat st2.encoded_token_map == Some ((v0, ()) :: []));
  assert pure (st2.encoded_future_trace == zero_nat :: one_nat :: []);
  assert pure (st2.encoded_decoder zero_nat == Some (P.prophecy_id_of p0, (v0, ())));
  P.prophecy_authority_resolve_observed #U32.t #unit auth p0 ()
    #st2 #((v0, ()) :: []) v0 zero_nat #[] #(one_nat :: []);

  let st3 = P.proph_state_resolve_view_encoded st2 (P.prophecy_id_of p0) [] (one_nat :: []);
  rewrite (P.prophecy_authority_state auth
    (P.proph_state_resolve_view_encoded st2 (P.prophecy_id_of p0) [] (one_nat :: []))) as
          (P.prophecy_authority_state auth st3);
  P.proph_state_resolve_view_encoded_preserves_lookup_other st2 (P.prophecy_id_of p0) (P.prophecy_id_of p1) ((v1, ()) :: []) [] (one_nat :: []);
  assert pure (P.proph_map_lookup (P.prophecy_id_of p1) st3.encoded_token_map == Some ((v1, ()) :: []));
  assert pure (st3.encoded_future_trace == one_nat :: []);
  assert pure (st3.encoded_decoder one_nat == Some (P.prophecy_id_of p1, (v1, ())));
  P.prophecy_authority_resolve_observed #U32.t #unit auth p1 ()
    #st3 #((v1, ()) :: []) v1 one_nat #[] #[];

  let st4 = P.proph_state_resolve_view_encoded st3 (P.prophecy_id_of p1) [] [];
  rewrite (P.prophecy_authority_state auth
    (P.proph_state_resolve_view_encoded st3 (P.prophecy_id_of p1) [] [])) as
          (P.prophecy_authority_state auth st4);
  drop_ (P.prophecy_authority_state auth st4);
  drop_ (P.prophecy_token_fragment p0 []);
  drop_ (P.prophecy_token_fragment p1 []);
  ()
}

(** Counter-aware two-token shared-authority framing model.

    This combines the runtime-counter discipline from
    [shared_authority_runtime_single_observation_model] with the two-token
    framing fact above.  Both tokens are allocated by the same runtime
    authority using consecutive [NST.prophecy_index] values, resolving the
    first token consumes the concrete observation-tape head at the active
    [NST.observation_index], and the framed second token remains tied to the
    same authority so it can be resolved from the advanced runtime state.  This
    still avoids the public NewProph/Resolve boundary witnesses; the helper no
    longer accepts a standalone observed-nat argument, so counter advancement,
    tape-head selection, lookup, and decoder facts are derived from the
    explicit runtime authority resource and [Pulse.Lib.Prophecy.Trace] lemmas. *)
ghost fn shared_authority_runtime_two_observation_framing_model
    (v0 v1:U32.t)
    (#c:erased NST.ctr)
    (#ot:erased (nat -> nat))
  requires pure (NST.prophecy_index (reveal c) == zero_nat /\
                  NST.observation_index (reveal c) == zero_nat /\
                  reveal ot zero_nat == zero_nat /\
                  reveal ot one_nat == one_nat)
  ensures emp
{
  let initial = two_u32_initial_state v0 v1;
  two_u32_initial_projection_first v0 v1;
  two_u32_initial_projection_second v0 v1;
  two_u32_tail_projection_second v0 v1;
  two_u32_initial_state_interp v0 v1;
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c)) (one_nat + one_nat);
  P.encoded_trace_of_tape_cons (reveal ot) (NST.observation_index (reveal c) + 1) one_nat;
  assert pure (P.encoded_trace_of_tape (reveal ot) (NST.observation_index (reveal c)) (one_nat + one_nat) == zero_nat :: one_nat :: []);
  assert pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) (one_nat + one_nat));
  let auth = P.prophecy_authority_init #U32.t #unit #initial;
  assert (P.prophecy_authority_state auth initial **
    pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) (one_nat + one_nat)));
  rewrite (P.prophecy_authority_state auth initial **
           pure (P.proph_state_runtime_matches_ctr_encoded initial (reveal ot) (reveal c) (one_nat + one_nat))) as
          (P.prophecy_authority_runtime_state auth initial (reveal ot) (reveal c) (one_nat + one_nat));

  let p0 = P.prophecy_authority_alloc_runtime #U32.t #unit auth #initial #ot #c #(one_nat + one_nat);
  let st1 = snd (P.proph_state_alloc_fresh_view_encoded initial);
  rewrite (P.prophecy_authority_runtime_state auth (snd (P.proph_state_alloc_fresh_view_encoded initial))
            (reveal ot) (NST.bump_prophecy (reveal c)) (one_nat + one_nat)) as
          (P.prophecy_authority_runtime_state auth st1
            (reveal ot) (NST.bump_prophecy (reveal c)) (one_nat + one_nat));
  rewrite (P.prophecy_token_fragment p0
    (P.proph_list_resolves_encoded initial.encoded_decoder (NST.prophecy_index (reveal c)) initial.encoded_future_trace)) as
          (P.prophecy_token_fragment p0 ((v0, ()) :: []));
  assert pure (P.prophecy_id_of p0 == zero_nat);
  assert pure (P.prophecy_bound_to_authority auth p0);
  assert pure (P.proph_map_lookup zero_nat st1.encoded_token_map == Some ((v0, ()) :: []));

  assert pure (P.prophecy_id_of p0 <> NST.prophecy_index (NST.bump_prophecy (reveal c)));
  let p1 = P.prophecy_authority_alloc_runtime_frame #U32.t #unit auth #st1 #ot #(NST.bump_prophecy (reveal c)) #(one_nat + one_nat)
    p0 #((v0, ()) :: []);
  let st2 = snd (P.proph_state_alloc_fresh_view_encoded st1);
  rewrite (P.prophecy_authority_runtime_state auth (snd (P.proph_state_alloc_fresh_view_encoded st1))
            (reveal ot) (NST.bump_prophecy (NST.bump_prophecy (reveal c))) (one_nat + one_nat)) as
          (P.prophecy_authority_runtime_state auth st2
            (reveal ot) (NST.bump_prophecy (NST.bump_prophecy (reveal c))) (one_nat + one_nat));
  rewrite (P.prophecy_token_fragment p1
    (P.proph_list_resolves_encoded st1.encoded_decoder (NST.prophecy_index (NST.bump_prophecy (reveal c))) st1.encoded_future_trace)) as
          (P.prophecy_token_fragment p1 ((v1, ()) :: []));
  assert pure (P.prophecy_id_of p1 == one_nat);
  assert pure (P.prophecy_bound_to_authority auth p1);
  assert pure (P.proph_map_lookup one_nat st2.encoded_token_map == Some ((v1, ()) :: []));
  assert pure (P.proph_map_lookup zero_nat st2.encoded_token_map == Some ((v0, ()) :: []));
  assert pure (st2.encoded_decoder zero_nat == Some (P.prophecy_id_of p0, (v0, ())));
  assert pure (zero_nat == reveal ot (NST.observation_index (NST.bump_prophecy (NST.bump_prophecy (reveal c)))));

  let tail0 = P.prophecy_authority_resolve_current #U32.t #unit auth p0 ()
    #st2 #ot #(NST.bump_prophecy (NST.bump_prophecy (reveal c))) #(one_nat + one_nat) #((v0, ()) :: []) v0;
  assert pure (reveal tail0 == []);
  rewrite each (reveal tail0) as [];
  let st3 = P.proph_state_resolve_view_encoded st2 (P.prophecy_id_of p0) []
    (P.encoded_trace_of_tape (reveal ot)
      (NST.observation_index (NST.bump_prophecy (NST.bump_prophecy (reveal c))) + 1)
      ((one_nat + one_nat) - 1));
  rewrite (P.prophecy_authority_runtime_state auth
            (P.proph_state_resolve_view_encoded st2 (P.prophecy_id_of p0) []
              (P.encoded_trace_of_tape (reveal ot)
                (NST.observation_index (NST.bump_prophecy (NST.bump_prophecy (reveal c))) + 1)
                ((one_nat + one_nat) - 1)))
            (reveal ot) (NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c)))) ((one_nat + one_nat) - 1)) as
          (P.prophecy_authority_runtime_state auth st3
            (reveal ot) (NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c)))) one_nat);
  P.proph_state_resolve_view_encoded_preserves_lookup_other st2 (P.prophecy_id_of p0) (P.prophecy_id_of p1) ((v1, ()) :: []) [] (one_nat :: []);
  assert pure (P.proph_map_lookup (P.prophecy_id_of p1) st3.encoded_token_map == Some ((v1, ()) :: []));
  assert pure (st3.encoded_future_trace == one_nat :: []);
  assert pure (st3.encoded_decoder one_nat == Some (P.prophecy_id_of p1, (v1, ())));
  assert pure (one_nat == reveal ot (NST.observation_index (NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c))))));

  let tail1 = P.prophecy_authority_resolve_current #U32.t #unit auth p1 ()
    #st3 #ot #(NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c)))) #one_nat #((v1, ()) :: []) v1;
  assert pure (reveal tail1 == []);
  rewrite each (reveal tail1) as [];
  rewrite (P.prophecy_authority_runtime_state auth
            (P.proph_state_resolve_view_encoded st3 (P.prophecy_id_of p1) []
              (P.encoded_trace_of_tape (reveal ot)
                (NST.observation_index (NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c)))) + 1)
                (one_nat - 1)))
            (reveal ot) (NST.bump_observation (NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c))))) (one_nat - 1)) as
          (P.prophecy_authority_runtime_state auth
            (P.proph_state_resolve_view_encoded st3 (P.prophecy_id_of p1) [] [])
            (reveal ot) (NST.bump_observation (NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c))))) zero_nat);
  drop_ (P.prophecy_authority_runtime_state auth
    (P.proph_state_resolve_view_encoded st3 (P.prophecy_id_of p1) [] [])
    (reveal ot) (NST.bump_observation (NST.bump_observation (NST.bump_prophecy (NST.bump_prophecy (reveal c))))) zero_nat);
  drop_ (P.prophecy_token_fragment p0 []);
  drop_ (P.prophecy_token_fragment p1 []);
  ()
}

fn resolve_atomic_read
    (r:B.box U32.t)
    (p:P.prophecy_var U32.t unit)
    (#cur:erased U32.t)
    (#pred:erased U32.t)
    (#tail:erased (P.prediction_stream U32.t unit))
  requires B.pts_to r cur ** P.prophecy_token p ((reveal pred, ()) :: reveal tail)
  returns x:U32.t
  ensures B.pts_to r cur ** P.prophecy_token p (reveal tail) **
          pure (x == reveal cur) ** pure (x == reveal pred)
{
  let x = P.resolve #U32.t #unit p () #pred #tail
    #(B.pts_to r cur)
    #(fun y -> B.pts_to r cur ** pure (y == reveal cur))
    fn _ { AP.atomic_read r };
  x
}

fn alloc_prophecy ()
  requires emp
  returns p:P.prophecy_var U32.t unit
  ensures exists* (pvs:P.prediction_stream U32.t unit). P.prophecy_token p pvs
{
  P.prophecy_alloc #U32.t #unit ()
}

fn alloc_and_resolve_atomic_read
    (r:B.box U32.t)
    (#cur:erased U32.t)
  requires B.pts_to r cur
  returns x:U32.t
  ensures B.pts_to r cur ** pure (x == reveal cur)
{
  let p = P.prophecy_alloc #U32.t #unit ();
  with pvs. assert (P.prophecy_token p pvs);
  let x = P.resolve_token #U32.t #unit p () #pvs
    #(B.pts_to r cur)
    #(fun y -> B.pts_to r cur ** pure (y == reveal cur))
    fn _ { AP.atomic_read r };
  with tail. assert (P.prophecy_token p tail ** pure (pvs == (x, ()) :: tail));
  drop_ (P.prophecy_token p tail);
  x
}

(** Public-path two-token regression.  Unlike the ghost-only shared-authority
    models above, this function exercises the exported [prophecy_alloc] and
    [resolve_token] facade twice in one client computation.  It therefore
    protects the public allocation/Resolve path against regressions while the
    remaining primitive-boundary witnesses are being internalized into the
    singleton state-interpretation resource. *)
fn alloc_and_resolve_two_atomic_reads
    (r0 r1:B.box U32.t)
    (#cur0 #cur1:erased U32.t)
  requires B.pts_to r0 cur0 ** B.pts_to r1 cur1
  returns xy:(U32.t & U32.t)
  ensures B.pts_to r0 cur0 ** B.pts_to r1 cur1 **
          pure (fst xy == reveal cur0) ** pure (snd xy == reveal cur1)
{
  let p0 = P.prophecy_alloc #U32.t #unit ();
  with pvs0. assert (P.prophecy_token p0 pvs0);
  let p1 = P.prophecy_alloc #U32.t #unit ();
  with pvs1. assert (P.prophecy_token p1 pvs1);

  let x0 = P.resolve_token #U32.t #unit p0 () #pvs0
    #(B.pts_to r0 cur0)
    #(fun y -> B.pts_to r0 cur0 ** pure (y == reveal cur0))
    fn _ { AP.atomic_read r0 };
  with tail0. assert (P.prophecy_token p0 tail0 ** pure (pvs0 == (x0, ()) :: tail0));
  drop_ (P.prophecy_token p0 tail0);

  let x1 = P.resolve_token #U32.t #unit p1 () #pvs1
    #(B.pts_to r1 cur1)
    #(fun y -> B.pts_to r1 cur1 ** pure (y == reveal cur1))
    fn _ { AP.atomic_read r1 };
  with tail1. assert (P.prophecy_token p1 tail1 ** pure (pvs1 == (x1, ()) :: tail1));
  drop_ (P.prophecy_token p1 tail1);
  (x0, x1)
}

(** Public-path framing regression.

    This strengthens [alloc_and_resolve_two_atomic_reads] by resolving [p0]
    while the unrelated token for [p1] is part of the framed pre/post of the
    observed atomic read itself, not merely left in the surrounding context.
    It checks that the client-facing Resolve bridge preserves unrelated
    prophecy tokens across the coupled physical step/observation step, which is
    the client-visible analogue of the shared-authority framing lemmas above. *)
fn alloc_resolve_with_unrelated_token_in_atomic_frame
    (r0 r1:B.box U32.t)
    (#cur0 #cur1:erased U32.t)
  requires B.pts_to r0 cur0 ** B.pts_to r1 cur1
  returns xy:(U32.t & U32.t)
  ensures B.pts_to r0 cur0 ** B.pts_to r1 cur1 **
          pure (fst xy == reveal cur0) ** pure (snd xy == reveal cur1)
{
  let p0 = P.prophecy_alloc #U32.t #unit ();
  with pvs0. assert (P.prophecy_token p0 pvs0);
  let p1 = P.prophecy_alloc #U32.t #unit ();
  with pvs1. assert (P.prophecy_token p1 pvs1);

  let x0 = P.resolve_token #U32.t #unit p0 () #pvs0
    #(P.prophecy_token p1 pvs1 ** B.pts_to r0 cur0)
    #(fun y -> P.prophecy_token p1 pvs1 ** B.pts_to r0 cur0 ** pure (y == reveal cur0))
    fn _ {
      let y = AP.atomic_read r0;
      y
    };
  with tail0. assert (P.prophecy_token p1 pvs1 ** B.pts_to r0 cur0 ** pure (x0 == reveal cur0) **
    P.prophecy_token p0 tail0 ** pure (pvs0 == (x0, ()) :: tail0));
  drop_ (P.prophecy_token p0 tail0);

  let x1 = P.resolve_token #U32.t #unit p1 () #pvs1
    #(B.pts_to r1 cur1)
    #(fun y -> B.pts_to r1 cur1 ** pure (y == reveal cur1))
    fn _ { AP.atomic_read r1 };
  with tail1. assert (P.prophecy_token p1 tail1 ** pure (pvs1 == (x1, ()) :: tail1));
  drop_ (P.prophecy_token p1 tail1);
  (x0, x1)
}
