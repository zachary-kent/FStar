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
type ctr = nat

type nst (#s:Type u#s)
           (a:Type u#a)
           (pre:req_t s)
           (post:ens_t s a) =
  s0:s { pre s0 } ->
  tape ->
  angel_tape ->  // angelic oracle
  ctr ->
  (res:(a & s & ctr) {
    post s0 res._1 res._2
  })


let repr #s #a #pre #post f = f
let lift #s #a #pre #post f =
  fun s0 t at c -> let x, s1 = f s0 in x, s1, c

let return #s #a x =
  fun s0 t at c -> x, s0, c

let bind #s #a #b #req_f #ens_f #req_g #ens_g f g =
  fun s0 t at c ->
  let x, s1, c = f s0 t at c in
  g x s1 t at c

let weaken #s #a #req_f #ens_f #req_g #ens_g f =
  fun s0 t at c -> f s0 t at c

let flip () = fun s0 t at c -> t c, s0, c+1

(** Angelic choice: read a nat from the angel tape.
    The angel tape is existentially quantified in adequacy:
    ∀ demonic_tape. ∃ angel_tape. execution succeeds.
    This provides the semantic foundation for prophecy variables. *)
let angel () = fun s0 t at c -> at c, s0, c+1
