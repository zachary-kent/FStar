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

module PulseCore.PartialNondeterministicHoareStateMonad
open FStar.Ghost
type level = n:erased nat & (unit -> Dv (k:nat { k == reveal n }))
let mk_level (n:nat) : level = (| hide n, fun () -> n |)

open PulseCore.HoareStateMonad
module NST = PulseCore.NondeterministicHoareStateMonad
let req_t (s:Type) = s -> prop
let ens_t (s:Type) (a:Type) = s -> a -> s -> prop

(** Internal oracle cursors, shared with NST. *)
type ctr = NST.ctr
let obs_tape = NST.obs_tape
let ens_ctr_t (s:Type) (a:Type) = s -> ctr -> a -> s -> ctr -> prop
let req_obs_ctr_t (s:Type) = s -> obs_tape -> ctr -> prop
let ens_obs_ctr_t (s:Type) (a:Type) = s -> obs_tape -> ctr -> a -> s -> ctr -> prop

val pnst
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_t s)
    (post:ens_t s a)
: Type0

(** Divergent partial computation.  This is used only when an older runner lacks
    the hidden state interpretation required by a newer semantic constructor;
    it preserves partial-correctness soundness by producing no result. *)
val diverge
    (#s:Type u#s)
    (#a:Type u#a)
    (#pre:req_t s)
    (#post:ens_t s a)
  : pnst #s a pre post

val pnst_ctr
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_t s)
    (post:ens_ctr_t s a)
: Type0

val pnst_obs_ctr
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_obs_ctr_t s)
    (post:ens_obs_ctr_t s a)
: Type0

val repr #s #a #pre #post (f:pnst #s a pre post) :
  s0:s { pre s0 } ->
  (nat -> bool) ->
  (nat -> nat) ->  // angelic oracle
  (nat -> nat) ->  // observation oracle for prophecy/observable-step traces
  ctr ->
  Dv (res:(a & s & ctr) {
    post s0 res._1 res._2
  })

val repr_ctr #s #a #pre #post (f:pnst_ctr #s a pre post) :
  s0:s { pre s0 } ->
  (nat -> bool) ->
  (nat -> nat) ->  // angelic oracle
  (nat -> nat) ->  // observation oracle for prophecy/observable-step traces
  c0:ctr ->
  Dv (res:(a & s & ctr) {
    post s0 c0 res._1 res._2 res._3
  })

val repr_obs_ctr #s #a #pre #post (f:pnst_obs_ctr #s a pre post) :
  s0:s ->
  (nat -> bool) ->
  (nat -> nat) ->  // angelic oracle
  ot:obs_tape ->
  c0:ctr { pre s0 ot c0 } ->
  Dv (res:(a & s & ctr) {
    post s0 ot c0 res._1 res._2 res._3
  })

val forget_ctr #s #a #pre #post (f:pnst_ctr #s a pre post)
  : pnst #s a pre (fun s0 x s1 -> exists c0 c1. post s0 c0 x s1 c1)

val lift_ctr #s #a #pre #post (f:NST.nst_ctr a pre post) : pnst_ctr #s a pre post

val lift_obs_ctr #s #a #pre #post (f:NST.nst_obs_ctr a pre post) : pnst_obs_ctr #s a pre post

(** Lift a total state computation whose specification may depend on the active
    observation tape and counter into the observation/counter-aware partial
    monad without changing the counter.  This is the small plumbing primitive
    needed by state-interpretation-aware observed-result adequacy rules: an
    atomic state action can be run with a frame [si ot c] chosen at the actual
    input tape/counter before the subsequent observation bump is interpreted. *)
val lift_st_obs_ctr
      (#s:Type u#s)
      (#a:Type u#a)
      (#pre:obs_tape -> ctr -> req_t s)
      (#post:obs_tape -> ctr -> ens_t s a)
      (f:(ot:obs_tape -> c:ctr -> st a (pre ot c) (post ot c)))
    : pnst_obs_ctr #s a
        (fun s0 ot c0 -> pre ot c0 s0)
        (fun s0 ot c0 x s1 c1 -> post ot c0 s0 x s1 /\ c1 == c0)

(** Run a state computation framed by the current observation/counter-indexed
    resource and then consume one observation.  The consumed nat is determined
    by [ot (NST.observation_index c0)]; callers that need the value can mention
    it in their weakening/closing proof. *)
val lift_st_then_observe_obs_ctr
      (#s:Type u#s)
      (#a:Type u#a)
      (#pre:obs_tape -> ctr -> req_t s)
      (#post:obs_tape -> ctr -> ens_t s a)
      (f:(ot:obs_tape -> c:ctr -> st a (pre ot c) (post ot c)))
    : pnst_obs_ctr #s a
        (fun s0 ot c0 -> pre ot c0 s0)
        (fun s0 ot c0 x s1 c1 -> post ot c0 s0 x s1 /\ c1 == NST.bump_observation c0)

(** Run a state computation framed by the current observation/counter-indexed
    resource and then consume the active prophecy-id cursor.  The returned id is
    [NST.prophecy_index c0], and the output counter is [NST.bump_prophecy c0]. *)
val lift_st_then_fresh_prophecy_obs_ctr
      (#s:Type u#s)
      (#a:Type u#a)
      (#pre:obs_tape -> ctr -> req_t s)
      (#post:obs_tape -> ctr -> nat -> ens_t s a)
      (f:(ot:obs_tape -> c:ctr -> pid:nat{pid == NST.prophecy_index c} ->
        st a (pre ot c) (post ot c pid)))
    : pnst_obs_ctr #s a
        (fun s0 ot c0 -> pre ot c0 s0)
        (fun s0 ot c0 x s1 c1 -> post ot c0 (NST.prophecy_index c0) s0 x s1 /\
          c1 == NST.bump_prophecy c0)

(** Dv-aware sibling of [lift_st_then_fresh_prophecy_obs_ctr].  This keeps the
    executable state update total once chosen, but permits the semantic layer to
    construct that state update from a divergent/coinductive continuation before
    the PNST representation is run.  It is the minimal plumbing needed by the
    active-prophecy state-interpretation runner, whose FreshProphId branch must
    both close [si ot (bump_prophecy c)] and build the next semantic reduct. *)
val lift_st_then_fresh_prophecy_obs_ctr_dv
      (#s:Type u#s)
      (#a:Type u#a)
      (#pre:obs_tape -> ctr -> req_t s)
      (#post:obs_tape -> ctr -> nat -> ens_t s a)
      (f:(ot:obs_tape -> c:ctr -> pid:nat{pid == NST.prophecy_index c} ->
        Dv (st a (pre ot c) (post ot c pid))))
    : pnst_obs_ctr #s a
        (fun s0 ot c0 -> pre ot c0 s0)
        (fun s0 ot c0 x s1 c1 -> post ot c0 (NST.prophecy_index c0) s0 x s1 /\
          c1 == NST.bump_prophecy c0)

(** Ordinary-[pnst] one-step prophecy-id cursor with ghost access to the active
    observation tape/counter.  The returned postcondition intentionally remains
    ordinary (counter-erased), but [make] is called at the real [ot,c] and the
    returned counter is [NST.bump_prophecy c].  This is the minimal primitive
    needed by [Sem.FreshProphIdWithObsCtr] without adding an unsound
    obs/counter-to-ordinary coercion. *)
val lift_fresh_prophecy_step
      (#s:Type u#s)
      (#a:Type u#a)
      (#pre:req_t s)
      (#post:ens_t s a)
      (make:(s0:s{pre s0} -> pid:nat -> ot:obs_tape -> c:ctr{pid == NST.prophecy_index c} ->
        Dv (x:a{post s0 x s0})))
    : pnst #s a pre post

val lift_to_ctr #s #a #pre #post (f:pnst #s a pre post)
  : pnst_ctr #s a pre (fun s0 _ x s1 _ -> post s0 x s1)

val lift_ctr_to_obs_ctr #s #a #pre #post (f:pnst_ctr #s a pre post)
  : pnst_obs_ctr #s a (fun s0 _ _ -> pre s0)
      (fun s0 _ c0 x s1 c1 -> post s0 c0 x s1 c1)

val lift_to_obs_ctr #s #a #pre #post (f:pnst #s a pre post)
  : pnst_obs_ctr #s a (fun s0 _ _ -> pre s0)
      (fun s0 _ _ x s1 _ -> post s0 x s1)

val lift #s #a #pre #post (f:NST.nst a pre post) : pnst #s a pre post

val return (#s:Type u#s)
           (#a:Type u#a)
           (x:a)
: pnst #s a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)           

val return_obs_ctr (#s:Type u#s)
           (#a:Type u#a)
           (x:a)
: pnst_obs_ctr #s a
    (fun _ _ _ -> True)
    (fun s0 _ c0 v s1 c1 -> x == v /\ s0 == s1 /\ c0 == c1)

val bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:pnst a req_f ens_f)
      (g:(x:a -> Dv (pnst b (req_g x) (ens_g x))))
: pnst b
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))

val weaken
      (#s:Type u#s)
      (#a:Type u#a)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      (f:pnst a req_f ens_f)
    : Pure (pnst a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)

val bind_obs_ctr
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#req_f:req_obs_ctr_t s)
      (#ens_f:ens_obs_ctr_t s a)
      (#req_g:a -> req_obs_ctr_t s)
      (#ens_g:a -> ens_obs_ctr_t s b)
      (f:pnst_obs_ctr a req_f ens_f)
      (g:(x:a -> pnst_obs_ctr b (req_g x) (ens_g x)))
: pnst_obs_ctr b
  (fun s0 ot c0 -> req_f s0 ot c0 /\
    (forall x s1 c1. ens_f s0 ot c0 x s1 c1 ==> (req_g x) s1 ot c1))
  (fun s0 ot c0 r s2 c2 -> req_f s0 ot c0 /\
    (exists x s1 c1. ens_f s0 ot c0 x s1 c1 /\ (req_g x) s1 ot c1 /\
      (ens_g x) s1 ot c1 r s2 c2))

(** Dv-aware observation/counter bind, matching ordinary [bind]'s ability to
    build the continuation after seeing the first result.  This is needed by
    active prophecy semantics: an atomic action returns [x], and the semantic
    reduct [k x] is a potentially divergent/coinductive value. *)
val bind_obs_ctr_dv
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#req_f:req_obs_ctr_t s)
      (#ens_f:ens_obs_ctr_t s a)
      (#req_g:a -> req_obs_ctr_t s)
      (#ens_g:a -> ens_obs_ctr_t s b)
      (f:pnst_obs_ctr a req_f ens_f)
      (g:(x:a -> Dv (pnst_obs_ctr b (req_g x) (ens_g x))))
: pnst_obs_ctr b
  (fun s0 ot c0 -> req_f s0 ot c0 /\
    (forall x s1 c1. ens_f s0 ot c0 x s1 c1 ==> (req_g x) s1 ot c1))
  (fun s0 ot c0 r s2 c2 -> req_f s0 ot c0 /\
    (exists x s1 c1. ens_f s0 ot c0 x s1 c1 /\ (req_g x) s1 ot c1 /\
      (ens_g x) s1 ot c1 r s2 c2))

val weaken_obs_ctr
      (#s:Type u#s)
      (#a:Type u#a)
      (#req_f:req_obs_ctr_t s)
      (#ens_f:ens_obs_ctr_t s a)
      (#req_g:req_obs_ctr_t s)
      (#ens_g:ens_obs_ctr_t s a)
      (f:pnst_obs_ctr a req_f ens_f)
    : Pure (pnst_obs_ctr a req_g ens_g)
      (requires
        (forall s ot c. req_g s ot c ==> req_f s ot c) /\
        (forall s0 ot c0 x s1 c1.
          (req_g s0 ot c0 /\ ens_f s0 ot c0 x s1 c1) ==> ens_g s0 ot c0 x s1 c1))
      (ensures fun _ -> True)

val weaken_obs_ctr_with
      (#s:Type u#s)
      (#a:Type u#a)
      (#req_f:req_obs_ctr_t s)
      (#ens_f:ens_obs_ctr_t s a)
      (#req_g:req_obs_ctr_t s)
      (#ens_g:ens_obs_ctr_t s a)
      (req_pf:(s0:s -> ot:obs_tape -> c:ctr ->
        Lemma (requires req_g s0 ot c) (ensures req_f s0 ot c)))
      (ens_pf:(s0:s -> ot:obs_tape -> c0:ctr -> x:a -> s1:s -> c1:ctr ->
        Lemma (requires req_g s0 ot c0 /\ ens_f s0 ot c0 x s1 c1)
              (ensures ens_g s0 ot c0 x s1 c1)))
      (f:pnst_obs_ctr a req_f ens_f)
    : pnst_obs_ctr a req_g ens_g
