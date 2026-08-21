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
module PulseCore.InstantiatedSemantics

module Sem = PulseCore.Semantics
module Sep = PulseCore.IndirectionTheorySep
module F = FStar.FunctionalExtensionality

open FStar.Ghost
open PulseCore.IndirectionTheorySep

let laws ()
: squash (
    Sem.associative star /\
    Sem.commutative star /\
    Sem.is_unit emp star
  )
= Sep.sep_laws()

let state0 (e:inames) : Sem.state u#4 = {
    s = Sep.full_mem;
    budget = Sep.budget;
    pred = slprop;
    emp = emp;
    star = star;
    interp;
    invariant = mem_invariant e;
    laws = laws ();
}

let state : Sem.state = state0 GhostSet.empty

let _eq : squash (slprop == state.pred) = ()
let timeless p = Sep.timeless p
let emp = emp

let pure p = pure p
let op_Star_Star = star
let op_exists_Star #a p = op_exists_Star #a p
let implies = implies
let later_credit = later_credit
let later = later
let equiv = equiv
let later_credit_add n m = later_credit_add n m
let later_credit_zero () = later_credit_zero()
let iref = iref
let inv i p = inv i p

let slprop_equiv p q = p == q

let return_slprop_equiv (p q:slprop) (_:squash (p == q))
: slprop_equiv p q
= ()

let slprop_equiv_refl p = return_slprop_equiv p p ()
    
let slprop_equiv_elim p q = ()

let slprop_equiv_unit p = ()
let slprop_equiv_comm p1 p2 = ()
let slprop_equiv_assoc p1 p2 p3 = ()
let slprop_equiv_exists 
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. slprop_equiv (p x) (q x)))
= assert (F.feq p q);
  assert (F.feq (F.on_dom a p) (F.on_dom a q));
  Sep.exists_ext p q;
  return_slprop_equiv (op_exists_Star p) (op_exists_Star q) ()

(* The type of general-purpose computations *)
let lower (t:Type u#a) : Type0 = unit -> Dv t
let stt (a:Type u#a) 
        (pre:slprop)
        (post:a -> slprop)
: Type0
= lower (Sem.m u#4 u#a u#100 #state a pre (F.on_dom a post))

let return (#a:Type u#a) (x:a) (p:a -> slprop)
: stt a (p x) p
= fun _ -> Sem.ret x (F.on_dom a p)

let bind
    (#a:Type u#a) (#b:Type u#b)
    (#pre1:slprop) (#post1:a -> slprop) (#post2:b -> slprop)
    (e1:stt a pre1 post1)
    (e2:(x:a -> stt b (post1 x) post2))
: stt b pre1 post2
= fun _ -> Sem.mbind (e1()) (fun x -> e2 x ())

let frame
  (#a:Type u#a)
  (#pre:slprop) (#post:a -> slprop)
  (frame:slprop)
  (e:stt a pre post)
: stt a (pre `star` frame) (fun x -> post x `star` frame)
= fun _ -> Sem.frame frame (e())

let conv (#a:Type u#a)
         (pre1:slprop)
         (pre2:slprop)
         (post1:a -> slprop)
         (post2:a -> slprop)
         (pf1:squash (slprop_equiv pre1 pre2))
         (pf2:squash (slprop_post_equiv post1 post2))
: Lemma (stt a pre1 post1 == stt a pre2 post2)
= slprop_equiv_elim pre1 pre2;
  introduce forall (x:a). post1 x == post2 x
  with slprop_equiv_elim (post1 x) (post2 x);
  Sem.conv u#4 u#a u#100 #state a #pre1 #(F.on_dom _ post1) (F.on_dom _ post2);
  ()

let sub (#a:Type u#a)
        (#pre1:slprop)
        (pre2:slprop)
        (#post1:a -> slprop)
        (post2:a -> slprop)
        (pf1:squash (slprop_equiv pre1 pre2))
        (pf2:squash (slprop_post_equiv post1 post2))
        (e:stt a pre1 post1)
: stt a pre2 post2
= coerce_eq (conv pre1 pre2 post1 post2 pf1 pf2) e

let fork f0 = fun _ -> Sem.fork (f0 ())

let hide_div #a #pre #post (f:unit -> Dv (stt a pre post))
: stt a pre post
= fun _ -> f () ()

(** Adequacy-facing active NewProph runner for instantiated Pulse [stt]
    computations.

    This is the instantiated-semantics entry point for the Ret-specialized
    hidden-state NewProph lowering used by [Pulse.Lib.Core].  It unwraps the
    public [stt] thunk and dispatches to [Sem.run_active_new_proph_ret], so the
    public NewProph primitive can be validated through the active runner that
    owns the observation-tape/counter-indexed state interpretation rather than
    through the ordinary counter-erased [Sem.run] branch. *)
let run_active_new_proph_ret (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (e:stt a pre post)
    (frame:slprop)
    (fuel:pos)
  : Dv (option (Sem.active_run_result #state a (F.on_dom a post) frame fuel pre))
= let f = e () in
  Sem.run_active_new_proph_ret f frame fuel

(** Concrete instantiated execution of the Ret-specialized active NewProph
    constructor.  This is the adequacy-facing path used by the public
    hidden-state NewProph primitive after its syntax has been lowered: the
    caller starts with [si ot c0] in the state interpretation, the runner calls
    the active allocation action, and the returned counter is
    [NST.bump_prophecy c0]. *)
let run_active_new_proph_return_action_with_ctr (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (si:PulseCore.NondeterministicHoareStateMonad.obs_tape -> PulseCore.NondeterministicHoareStateMonad.ctr -> slprop)
    (alloc:(pid:nat -> ot:PulseCore.NondeterministicHoareStateMonad.obs_tape ->
      c:PulseCore.NondeterministicHoareStateMonad.ctr{pid == PulseCore.NondeterministicHoareStateMonad.prophecy_index c} ->
      (b:Type u#100 &
       ret:(b -> a) &
       mid:Sem.post state b &
       act:Sem.action state b {
         act.pre == pre `star` si ot c /\
         (forall x. act.post x == mid x `star` si ot (PulseCore.NondeterministicHoareStateMonad.bump_prophecy c)) /\
         (forall x. mid x == (F.on_dom a post) (ret x)) })))
    (frame:slprop)
    (t:Sem.tape)
    (at:Sem.angel_tape)
    (ot:Sem.observation_tape)
    (c0:PulseCore.NondeterministicHoareStateMonad.ctr)
    (fuel:pos)
    (s0:state.s { state.budget s0 >= fuel /\
      state.interp (((pre `star` frame) `star` si ot c0) `star` state.invariant s0) s0 })
  : Dv (res:(a & state.s & PulseCore.NondeterministicHoareStateMonad.ctr) {
      state.budget res._2 >= fuel - 1 /\
      state.interp ((((F.on_dom a post) res._1 `star` frame) `star` si ot res._3) `star` state.invariant res._2) res._2 /\
      res._3 == PulseCore.NondeterministicHoareStateMonad.bump_prophecy c0 })
= Sem.run_alt_active_new_proph_return_action_with_ctr #state #pre #a #(F.on_dom a post) si alloc frame t at ot c0 fuel s0

(** Adequacy-facing active observed-result runner for instantiated Pulse [stt]
    computations.

    This mirrors [run_active_new_proph_return_action_with_ctr] for Resolve-style
    observed-result events.  Callers that own the active observation/counter
    interpretation [si ot c0] can execute an
    [ObservedResultActWithHiddenStateAction] payload without falling back to the
    ordinary counter-erased [Sem.step] branch: the runner consumes exactly
    [ot (NST.observation_index c0)] and returns with [si] closed at
    [NST.bump_observation c0]. *)
let run_active_observed_result_action_with_ctr (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (si:PulseCore.PartialNondeterministicHoareStateMonad.obs_tape -> PulseCore.NondeterministicHoareStateMonad.ctr -> slprop)
    (k:(observed_nat:nat -> ot:PulseCore.PartialNondeterministicHoareStateMonad.obs_tape ->
      c:PulseCore.NondeterministicHoareStateMonad.ctr{observed_nat == ot (PulseCore.NondeterministicHoareStateMonad.observation_index c)} ->
      receipt:Sem.observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> Sem.observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:Sem.observed_result_current_event observed_nat ot c ->
        value_receipt:Sem.observed_result_value_event #result observed_nat ot c x ->
        Sem.observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#100 &
       mid:Sem.post state b &
       act:Sem.action state b {
         act.pre == state.star pre (si ot c) /\
         act.post == F.on_dom b (fun y -> state.star (mid y) (si ot (PulseCore.NondeterministicHoareStateMonad.bump_observation c))) } &
       (y:b -> Dv (Sem.m #state a (mid y) (F.on_dom a post))))))
    (frame:slprop)
    (t:Sem.tape)
    (at:Sem.angel_tape)
    (ot:Sem.observation_tape)
    (c0:PulseCore.NondeterministicHoareStateMonad.ctr)
    (fuel:pos)
    (s0:state.s { state.budget s0 >= fuel /\
      state.interp (((pre `star` frame) `star` si ot c0) `star` state.invariant s0) s0 })
  : Dv (res:(Sem.step_result a (F.on_dom a post) frame & state.s & PulseCore.NondeterministicHoareStateMonad.ctr) {
      state.budget res._2 >= fuel - 1 /\
      state.interp (((Sem.Step?.next res._1 `star` frame) `star` si ot res._3) `star` state.invariant res._2) res._2 /\
      res._3 == PulseCore.NondeterministicHoareStateMonad.bump_observation c0 })
= Sem.run_alt_active_observed_result_action_with_ctr #state #pre #a #(F.on_dom a post) si k frame t at ot c0 fuel s0

(** Adequacy-facing active observed-result value runner for the Ret-specialized
    public Resolve lowering.

    This is the instantiated counterpart of
    [Sem.run_alt_active_observed_result_return_action_with_ctr].  Unlike
    [run_active_observed_result_action_with_ctr], it executes the
    [ObservedResultActWithHiddenStateReturnAction] payload to the final public
    value under runner-owned [si ot c0] and returns with the observation cursor
    advanced to [NST.bump_observation c0], without handing any residual to the
    ordinary counter-erased [Sem.run] branch. *)
let run_active_observed_result_return_action_with_ctr (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (si:PulseCore.PartialNondeterministicHoareStateMonad.obs_tape -> PulseCore.NondeterministicHoareStateMonad.ctr -> slprop)
    (k:(observed_nat:nat -> ot:PulseCore.PartialNondeterministicHoareStateMonad.obs_tape ->
      c:PulseCore.NondeterministicHoareStateMonad.ctr{observed_nat == ot (PulseCore.NondeterministicHoareStateMonad.observation_index c)} ->
      receipt:Sem.observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> Sem.observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:Sem.observed_result_current_event observed_nat ot c ->
        value_receipt:Sem.observed_result_value_event #result observed_nat ot c x ->
        Sem.observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#100 &
       ret:(b -> a) &
       mid:Sem.post state b &
       act:Sem.action state b {
         act.pre == state.star pre (si ot c) /\
         act.post == F.on_dom b (fun y -> state.star (mid y) (si ot (PulseCore.NondeterministicHoareStateMonad.bump_observation c))) /\
         (forall y. mid y == (F.on_dom a post) (ret y)) })))
    (frame:slprop)
    (t:Sem.tape)
    (at:Sem.angel_tape)
    (ot:Sem.observation_tape)
    (c0:PulseCore.NondeterministicHoareStateMonad.ctr)
    (fuel:pos)
    (s0:state.s { state.budget s0 >= fuel /\
      state.interp (((pre `star` frame) `star` si ot c0) `star` state.invariant s0) s0 })
  : Dv (res:(a & state.s & PulseCore.NondeterministicHoareStateMonad.ctr) {
      state.budget res._2 >= fuel - 1 /\
      state.interp ((((F.on_dom a post) res._1 `star` frame) `star` si ot res._3) `star` state.invariant res._2) res._2 /\
      res._3 == PulseCore.NondeterministicHoareStateMonad.bump_observation c0 })
= Sem.run_alt_active_observed_result_return_action_with_ctr #state #pre #a #(F.on_dom a post) si k frame t at ot c0 fuel s0
