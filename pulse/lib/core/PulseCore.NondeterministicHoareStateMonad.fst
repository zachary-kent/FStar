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

friend PulseCore.HoareStateMonad

type tape = nat -> bool
type angel_tape = nat -> nat  // angelic oracle: provides nat-encoded choices
type observation_tape = nat -> nat  // observable-step oracle: nat-encoded prophecy observations

(** Separate oracle cursors.

    Scheduler choices, angelic choices, and prophecy observations are logically
    distinct tapes.  In particular, a prophecy Resolve consumes the next
    observation independently of how many scheduler/angelic choices were used
    earlier in the execution.  Keeping a single counter for all three tapes
    would make the observation index depend on unrelated nondeterminism and
    would not match the [encoded_observation_index] discipline in the prophecy
    state-interpretation scaffold. *)
noeq
type ctr = {
  scheduler_ctr : nat;
  angel_ctr : nat;
  observation_ctr : nat;
  prophecy_ctr : nat;
}

type nst_ctr (#s:Type u#s)
           (a:Type u#a)
           (pre:req_t s)
           (post:ens_ctr_t s a) =
  s0:s { pre s0 } ->
  tape ->
  angel_tape ->  // angelic oracle
  observation_tape ->  // observable-step oracle
  c0:ctr ->
  (res:(a & s & ctr) {
    post s0 c0 res._1 res._2 res._3
  })

type nst_obs_ctr (#s:Type u#s)
           (a:Type u#a)
           (pre:req_obs_ctr_t s)
           (post:ens_obs_ctr_t s a) =
  s0:s ->
  tape ->
  angel_tape ->
  ot:observation_tape ->
  c0:ctr { pre s0 ot c0 } ->
  (res:(a & s & ctr) {
    post s0 ot c0 res._1 res._2 res._3
  })

type nst (#s:Type u#s)
           (a:Type u#a)
           (pre:req_t s)
           (post:ens_t s a) =
  s0:s { pre s0 } ->
  tape ->
  angel_tape ->  // angelic oracle
  observation_tape ->  // observable-step oracle
  ctr ->
  (res:(a & s & ctr) {
    post s0 res._1 res._2
  })

let initial_ctr = { scheduler_ctr = 0; angel_ctr = 0; observation_ctr = 0; prophecy_ctr = 0 }
let scheduler_index c = c.scheduler_ctr
let angel_index c = c.angel_ctr
let observation_index c = c.observation_ctr
let prophecy_index c = c.prophecy_ctr

let bump_scheduler c = { c with scheduler_ctr = c.scheduler_ctr + 1 }
let bump_angel c = { c with angel_ctr = c.angel_ctr + 1 }
let bump_observation c = { c with observation_ctr = c.observation_ctr + 1 }
let bump_prophecy c = { c with prophecy_ctr = c.prophecy_ctr + 1 }

let repr #s #a #pre #post f = f
let repr_ctr #s #a #pre #post f = f
let repr_obs_ctr #s #a #pre #post f = f

let forget_ctr #s #a #pre #post f =
  fun s0 t at ot c0 ->
    let x, s1, c1 = f s0 t at ot c0 in
    x, s1, c1

let lift_ctr #s #a #pre #post f =
  fun s0 t at ot c ->
    let x, s1, c1 = f s0 t at ot c in
    x, s1, c1

let lift_ctr_to_obs_ctr #s #a #pre #post f =
  fun s0 t at ot c ->
    let x, s1, c1 = f s0 t at ot c in
    x, s1, c1

let lift_to_obs_ctr #s #a #pre #post f =
  fun s0 t at ot c ->
    let x, s1, c1 = f s0 t at ot c in
    x, s1, c1

let lift #s #a #pre #post f =
  fun s0 t at ot c -> let x, s1 = f s0 in x, s1, c

let return #s #a x =
  fun s0 t at ot c -> x, s0, c

let bind #s #a #b #req_f #ens_f #req_g #ens_g f g =
  fun s0 t at ot c ->
  let x, s1, c = f s0 t at ot c in
  g x s1 t at ot c

let weaken #s #a #req_f #ens_f #req_g #ens_g f =
  fun s0 t at ot c -> f s0 t at ot c

let flip () = fun s0 t at ot c ->
  t c.scheduler_ctr, s0, bump_scheduler c

let flip_ctr () = fun s0 t at ot c ->
  t c.scheduler_ctr, s0, bump_scheduler c

(** Angelic choice: read a nat from the angel tape.
    The tape is threaded through the interpreter and can model existential
    choices.  It does not by itself provide Iris-style prophecy variables:
    prophecy uses the separate observation tape plus a Resolve step/state
    interpretation coupled to that trace. *)
let angel () = fun s0 t at ot c ->
  at c.angel_ctr, s0, bump_angel c

let angel_ctr () = fun s0 t at ot c ->
  at c.angel_ctr, s0, bump_angel c

(** Observation trace consumption for prophecy/observable-step semantics.
    The tape is separate from the angel oracle so proofs cannot confuse
    existential choices with observations emitted by operational steps. *)
let observe () = fun s0 t at ot c ->
  ot c.observation_ctr, s0, bump_observation c

let observe_ctr () = fun s0 t at ot c ->
  ot c.observation_ctr, s0, bump_observation c

let observe_obs_ctr () = fun s0 t at ot c ->
  ot c.observation_ctr, s0, bump_observation c

(** Fresh prophecy identifiers are tracked in the same active interpreter
    counter as scheduler/angel/observation cursors.  NewProph consumes this
    cursor; Resolve consumes [observe]. *)
let fresh_prophecy_id () = fun s0 t at ot c ->
  c.prophecy_ctr, s0, bump_prophecy c

let fresh_prophecy_id_ctr () = fun s0 t at ot c ->
  c.prophecy_ctr, s0, bump_prophecy c

let fresh_prophecy_id_obs_ctr () = fun s0 t at ot c ->
  c.prophecy_ctr, s0, bump_prophecy c

let flip_result #s s0 t at ot c = ()
let angel_result #s s0 t at ot c = ()
let observe_result #s s0 t at ot c = ()
let fresh_prophecy_id_result #s s0 t at ot c = ()
let flip_ctr_result #s s0 t at ot c = ()
let angel_ctr_result #s s0 t at ot c = ()
let observe_ctr_result #s s0 t at ot c = ()
let fresh_prophecy_id_ctr_result #s s0 t at ot c = ()
let observe_obs_ctr_result #s s0 t at ot c = ()
let fresh_prophecy_id_obs_ctr_result #s s0 t at ot c = ()
