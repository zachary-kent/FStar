(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulseCore.NondeterministicHoareStateMonad
open PulseCore.HoareStateMonad

let req_t (s:Type) = s -> prop
let ens_t (s:Type) (a:Type) = s -> a -> s -> prop

(** Internal oracle cursors.  They are separate so prophecy observations are
    indexed only by prior observations, not by scheduler or angelic choices. *)
val ctr : Type0

(** Counter-aware postconditions.  The historical [ens_t] deliberately exposes
    only the physical state, which is enough for ordinary Pulse effects but not
    for adequacy facts about prophecy cursors.  [ens_ctr_t] is the minimal seam
    used by prophecy-state interpretation proofs: a postcondition can relate
    the input counter to the returned counter without changing existing [nst]
    clients. *)
let ens_ctr_t (s:Type) (a:Type) = s -> ctr -> a -> s -> ctr -> prop

val nst_ctr
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_t s)
    (post:ens_ctr_t s a)
: Type u#(max a s)

(** Observation-tape/counter-aware computations.  Unlike [nst_ctr], both the
    precondition and postcondition can mention the active observation tape and
    input counter.  This is a sibling effect for adequacy/state-interpretation
    plumbing; existing [nst] clients are unchanged. *)
let obs_tape = nat -> nat
let req_obs_ctr_t (s:Type) = s -> obs_tape -> ctr -> prop
let ens_obs_ctr_t (s:Type) (a:Type) = s -> obs_tape -> ctr -> a -> s -> ctr -> prop

val nst_obs_ctr
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_obs_ctr_t s)
    (post:ens_obs_ctr_t s a)
: Type u#(max a s)

val nst
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_t s)
    (post:ens_t s a)
: Type u#(max a s)

val initial_ctr : ctr
val scheduler_index : ctr -> nat
val angel_index : ctr -> nat
val observation_index : ctr -> nat
val prophecy_index : ctr -> nat

(** Cursor bump operations exposed for adequacy/projection lemmas.  They make
    the effects of [flip], [angel], [observe], and NewProph id allocation
    explicit while keeping the concrete counter representation abstract. *)
val bump_scheduler : c:ctr -> c':ctr{
  scheduler_index c' == scheduler_index c + 1 /\
  angel_index c' == angel_index c /\
  observation_index c' == observation_index c /\
  prophecy_index c' == prophecy_index c
}
val bump_angel : c:ctr -> c':ctr{
  scheduler_index c' == scheduler_index c /\
  angel_index c' == angel_index c + 1 /\
  observation_index c' == observation_index c /\
  prophecy_index c' == prophecy_index c
}
val bump_observation : c:ctr -> c':ctr{
  scheduler_index c' == scheduler_index c /\
  angel_index c' == angel_index c /\
  observation_index c' == observation_index c + 1 /\
  prophecy_index c' == prophecy_index c
}
val bump_prophecy : c:ctr -> c':ctr{
  scheduler_index c' == scheduler_index c /\
  angel_index c' == angel_index c /\
  observation_index c' == observation_index c /\
  prophecy_index c' == prophecy_index c + 1
}

val repr #s #a #pre #post (f:nst #s a pre post) :
  s0:s { pre s0 } ->
  (nat -> bool) ->
  (nat -> nat) ->  // angelic oracle
  (nat -> nat) ->  // observation oracle for prophecy/observable-step traces
  ctr ->
  (res:(a & s & ctr) {
    post s0 res._1 res._2
  })

val repr_ctr #s #a #pre #post (f:nst_ctr #s a pre post) :
  s0:s { pre s0 } ->
  (nat -> bool) ->
  (nat -> nat) ->  // angelic oracle
  (nat -> nat) ->  // observation oracle for prophecy/observable-step traces
  c0:ctr ->
  (res:(a & s & ctr) {
    post s0 c0 res._1 res._2 res._3
  })

val repr_obs_ctr #s #a #pre #post (f:nst_obs_ctr #s a pre post) :
  s0:s ->
  (nat -> bool) ->
  (nat -> nat) ->  // angelic oracle
  ot:obs_tape ->
  c0:ctr { pre s0 ot c0 } ->
  (res:(a & s & ctr) {
    post s0 ot c0 res._1 res._2 res._3
  })

val forget_ctr #s #a #pre #post (f:nst_ctr #s a pre post)
  : nst #s a pre (fun s0 x s1 -> exists c0 c1. post s0 c0 x s1 c1)

val lift_ctr #s #a #pre #post (f:nst #s a pre post)
  : nst_ctr #s a pre (fun s0 _ x s1 _ -> post s0 x s1)

val lift_ctr_to_obs_ctr #s #a #pre #post (f:nst_ctr #s a pre post)
  : nst_obs_ctr #s a (fun s0 _ _ -> pre s0)
      (fun s0 _ c0 x s1 c1 -> post s0 c0 x s1 c1)

val lift_to_obs_ctr #s #a #pre #post (f:nst #s a pre post)
  : nst_obs_ctr #s a (fun s0 _ _ -> pre s0)
      (fun s0 _ _ x s1 _ -> post s0 x s1)

val lift #s #a #pre #post (f:st a pre post) : nst #s a pre post

val return (#s:Type u#s)
           (#a:Type u#a)
           (x:a)
: nst #s a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)           

val bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:nst a req_f ens_f)
      (g:(x:a -> nst b (req_g x) (ens_g x)))
: nst b
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))

val weaken
      (#s:Type u#s)
      (#a:Type u#a)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      (f:nst a req_f ens_f)
    : Pure (nst a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)

val flip (#s:Type u#s) ()
  : nst #s bool (fun _ -> True) (fun s0 x s1 -> s0 == s1)

val flip_ctr (#s:Type u#s) ()
  : nst_ctr #s bool (fun _ -> True)
      (fun s0 c0 _ s1 c1 -> s0 == s1 /\ c1 == bump_scheduler c0)

(** Angelic choice: read a nat from the angel oracle.
    This supports existential nondeterminism.  It is not, by itself, an
    Iris-style prophecy mechanism; prophecy uses the separate observation
    oracle plus state-interpretation coupling. *)
val angel (#s:Type u#s) ()
  : nst #s nat (fun _ -> True) (fun s0 x s1 -> s0 == s1)

val angel_ctr (#s:Type u#s) ()
  : nst_ctr #s nat (fun _ -> True)
      (fun s0 c0 _ s1 c1 -> s0 == s1 /\ c1 == bump_angel c0)

(** Observation choice: consume the next nat from the observation oracle.
    Unlike [angel], this tape is reserved for observable-step traces such as
    prophecy Resolve observations.  The generic core keeps observations
    nat-encoded; typed prophecy decoders live above this layer. *)
val observe (#s:Type u#s) ()
  : nst #s nat (fun _ -> True) (fun s0 x s1 -> s0 == s1)

val observe_ctr (#s:Type u#s) ()
  : nst_ctr #s nat (fun _ -> True)
      (fun s0 c0 _ s1 c1 -> s0 == s1 /\ c1 == bump_observation c0)

val observe_obs_ctr (#s:Type u#s) ()
  : nst_obs_ctr #s nat (fun _ _ _ -> True)
      (fun s0 ot c0 n s1 c1 ->
        s0 == s1 /\ n == ot (observation_index c0) /\ c1 == bump_observation c0)

(** Allocate the next active prophecy identifier.  This is the core cursor that
    NewProph uses for global freshness; it is separate from the observation
    cursor consumed by Resolve. *)
val fresh_prophecy_id (#s:Type u#s) ()
  : nst #s nat (fun _ -> True) (fun s0 x s1 -> s0 == s1)

val fresh_prophecy_id_ctr (#s:Type u#s) ()
  : nst_ctr #s nat (fun _ -> True)
      (fun s0 c0 pid s1 c1 ->
        s0 == s1 /\ pid == prophecy_index c0 /\ c1 == bump_prophecy c0)

val fresh_prophecy_id_obs_ctr (#s:Type u#s) ()
  : nst_obs_ctr #s nat (fun _ _ _ -> True)
      (fun s0 _ c0 pid s1 c1 ->
        s0 == s1 /\ pid == prophecy_index c0 /\ c1 == bump_prophecy c0)

(** Exact repr facts for the primitive oracle reads.  These are used by
    adequacy/projection proofs to connect the abstract cursor operations above
    to the active interpreter. *)
val flip_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr (flip #s ()) s0 t at ot c ==
             (t (scheduler_index c), s0, bump_scheduler c))

val angel_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr (angel #s ()) s0 t at ot c ==
             (at (angel_index c), s0, bump_angel c))

val observe_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr (observe #s ()) s0 t at ot c ==
             (ot (observation_index c), s0, bump_observation c))

val fresh_prophecy_id_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr (fresh_prophecy_id #s ()) s0 t at ot c ==
             (prophecy_index c, s0, bump_prophecy c))

val flip_ctr_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr_ctr (flip_ctr #s ()) s0 t at ot c ==
             (t (scheduler_index c), s0, bump_scheduler c))

val angel_ctr_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr_ctr (angel_ctr #s ()) s0 t at ot c ==
             (at (angel_index c), s0, bump_angel c))

val observe_ctr_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr_ctr (observe_ctr #s ()) s0 t at ot c ==
             (ot (observation_index c), s0, bump_observation c))

val fresh_prophecy_id_ctr_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:nat -> nat) (c:ctr)
  : Lemma
    (ensures repr_ctr (fresh_prophecy_id_ctr #s ()) s0 t at ot c ==
             (prophecy_index c, s0, bump_prophecy c))

val observe_obs_ctr_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:obs_tape) (c:ctr)
  : Lemma
    (ensures repr_obs_ctr (observe_obs_ctr #s ()) s0 t at ot c ==
             (ot (observation_index c), s0, bump_observation c))

val fresh_prophecy_id_obs_ctr_result (#s:Type u#s)
    (s0:s) (t:nat -> bool) (at:nat -> nat) (ot:obs_tape) (c:ctr)
  : Lemma
    (ensures repr_obs_ctr (fresh_prophecy_id_obs_ctr #s ()) s0 t at ot c ==
             (prophecy_index c, s0, bump_prophecy c))
