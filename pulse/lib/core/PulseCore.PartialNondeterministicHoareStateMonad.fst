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

module NST = PulseCore.NondeterministicHoareStateMonad
type tape = nat -> bool
type angel_tape = nat -> nat
type observation_tape = nat -> nat

type pnst' (#s:Type u#s)
           (a:Type u#a)
           (pre:req_t s)
           (post:ens_t s a) =
  s0:s { pre s0 } ->
  tape ->
  angel_tape ->
  observation_tape ->
  ctr ->
  Dv (res:(a & s & ctr) {
    post s0 res._1 res._2
  })
let pnst #s a pre post = unit -> Dv (pnst' #s a pre post)

let rec diverge_loop #t () : Dv t = diverge_loop ()

let diverge #s #a #pre #post : pnst #s a pre post = fun () -> diverge_loop ()

type pnst_ctr' (#s:Type u#s)
           (a:Type u#a)
           (pre:req_t s)
           (post:ens_ctr_t s a) =
  s0:s { pre s0 } ->
  tape ->
  angel_tape ->
  observation_tape ->
  c0:ctr ->
  Dv (res:(a & s & ctr) {
    post s0 c0 res._1 res._2 res._3
  })
let pnst_ctr #s a pre post = unit -> Dv (pnst_ctr' #s a pre post)

type pnst_obs_ctr' (#s:Type u#s)
           (a:Type u#a)
           (pre:req_obs_ctr_t s)
           (post:ens_obs_ctr_t s a) =
  s0:s ->
  tape ->
  angel_tape ->
  ot:observation_tape ->
  c0:ctr { pre s0 ot c0 } ->
  Dv (res:(a & s & ctr) {
    post s0 ot c0 res._1 res._2 res._3
  })
let pnst_obs_ctr #s a pre post = unit -> Dv (pnst_obs_ctr' #s a pre post)

let repr #s #a #pre #post f = fun s0 t at ot c -> f () s0 t at ot c
let repr_ctr #s #a #pre #post f = fun s0 t at ot c -> f () s0 t at ot c
let repr_obs_ctr #s #a #pre #post f = fun s0 t at ot c -> f () s0 t at ot c

let forget_ctr #s #a #pre #post f =
  fun () s0 t at ot c0 ->
    let x, s1, c1 = f () s0 t at ot c0 in
    x, s1, c1

let lift_ctr #s #a #pre #post f =
  fun () s0 t at ot c -> let x, s1, c1 = NST.repr_ctr f s0 t at ot c in x, s1, c1

let lift_obs_ctr #s #a #pre #post f =
  fun () s0 t at ot c -> let x, s1, c1 = NST.repr_obs_ctr f s0 t at ot c in x, s1, c1

let lift_st_obs_ctr #s #a #pre #post f =
  fun () s0 t at ot c ->
    let x, s1 = f ot c s0 in
    x, s1, c

let lift_st_then_observe_obs_ctr #s #a #pre #post f =
  fun () s0 t at ot c ->
    let x, s1 = f ot c s0 in
    x, s1, NST.bump_observation c

let lift_st_then_fresh_prophecy_obs_ctr #s #a #pre #post f =
  fun () s0 t at ot c ->
    let pid = NST.prophecy_index c in
    let x, s1 = f ot c pid s0 in
    x, s1, NST.bump_prophecy c

let lift_st_then_fresh_prophecy_obs_ctr_dv #s #a #pre #post f =
  fun () s0 t at ot c ->
    let pid = NST.prophecy_index c in
    let state_step = f ot c pid in
    let x, s1 = state_step s0 in
    x, s1, NST.bump_prophecy c

let lift_fresh_prophecy_step #s #a #pre #post make =
  fun () s0 t at ot c ->
    let pid = NST.prophecy_index c in
    let x = make s0 pid ot c in
    x, s0, NST.bump_prophecy c

let lift_to_ctr #s #a #pre #post f =
  fun () s0 t at ot c -> let x, s1, c1 = f () s0 t at ot c in x, s1, c1

let lift_ctr_to_obs_ctr #s #a #pre #post f =
  fun () s0 t at ot c -> let x, s1, c1 = f () s0 t at ot c in x, s1, c1

let lift_to_obs_ctr #s #a #pre #post f =
  fun () s0 t at ot c -> let x, s1, c1 = f () s0 t at ot c in x, s1, c1

let lift #s #a #pre #post f =
  fun () s0 t at ot c -> let x, s1, c1 = NST.repr f s0 t at ot c in x, s1, c1

let return #s #a x =
  fun () s0 t at ot c -> x, s0, c

let return_obs_ctr #s #a x =
  fun () s0 t at ot c -> x, s0, c

let bind #s #a #b #req_f #ens_f #req_g #ens_g f g =
  fun () s0 t at ot c ->
  let x, s1, c = f () s0 t at ot c in
  g x () s1 t at ot c

let weaken #s #a #req_f #ens_f #req_g #ens_g f =
  fun () s0 t at ot c -> f () s0 t at ot c

let bind_obs_ctr #s #a #b #req_f #ens_f #req_g #ens_g f g =
  fun () s0 t at ot c ->
    let x, s1, c1 = f () s0 t at ot c in
    g x () s1 t at ot c1

let bind_obs_ctr_dv #s #a #b #req_f #ens_f #req_g #ens_g f g =
  fun () s0 t at ot c ->
    let x, s1, c1 = f () s0 t at ot c in
    let gx = g x in
    gx () s1 t at ot c1

let weaken_obs_ctr #s #a #req_f #ens_f #req_g #ens_g f =
  fun () s0 t at ot c -> f () s0 t at ot c

let weaken_obs_ctr_with #s #a #req_f #ens_f #req_g #ens_g req_pf ens_pf f =
  fun () s0 t at ot c ->
    req_pf s0 ot c;
    let x, s1, c1 = f () s0 t at ot c in
    ens_pf s0 ot c x s1 c1;
    x, s1, c1
