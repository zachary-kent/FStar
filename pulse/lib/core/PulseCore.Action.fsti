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

module PulseCore.Action

module I = PulseCore.InstantiatedSemantics
module Sem = PulseCore.Semantics
module Sep = PulseCore.IndirectionTheorySep
module NST = PulseCore.NondeterministicHoareStateMonad
module PW = PulseCore.ProphecyWorld
open FStar.PCM
open FStar.Ghost
open Pulse.Lib.Loc

open PulseCore.InstantiatedSemantics

type reifiability =
 | Ghost
 | Atomic

let ( ^^ ) (r1 r2 : reifiability) : reifiability =
  if r1 = r2 then r1
  else Atomic

[@@ erasable]
let iref : Type0 = Sep.iref
let inames = Sep.inames
let singleton (i:iref) : inames = Sep.single i

(** Resolve-specific active observed-result certificate.

    The constructor is hidden by this interface: clients can only receive this
    receipt from the active observed-result lowering callback, after the
    physical observable action has returned [x] and the runner has consumed the
    current observation cell [observed_nat].  The untyped prophecy id [pid] is
    part of the hidden receipt index, so public Resolve cannot retarget a
    receipt to another prophecy.  Higher-level prophecy code may tie this
    receipt to its singleton prophecy-world decoder boundary; ordinary callers
    cannot manufacture one through the public Core API. *)
[@@ erasable]
val observed_result_resolve_event
    (#result #payload:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (x:result)
    (payload_value:payload)
  : Type0

(** Target-fixed Resolve certificate for public prophecy lowering.

    Unlike the generic callback-local [observed_result_resolve_event]
    constructor capability, this receipt is indexed by the single prophecy id,
    payload packer, and payload value selected before the active observed-result
    action is built.  Public Resolve uses this narrower receipt so the checked
    finisher cannot be fed a certificate retargeted through the generic
    universally-quantified event capability. *)
[@@ erasable]
val observed_result_targeted_resolve_event
    (#result #payload:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (payload_value:payload)
    (x:result)
  : Type0

(** Decoder fact eliminator for a target-fixed active Resolve event.

    The receipt is abstract at the Action API and, via the Semantics private
    representation, can only be obtained from active observed-result runner
    callbacks.  Its private Semantics representation carries the runner-minted
    target-fixed observation adequacy certificate for the consumed current cell,
    fixed [pid], actual result [x], and [payload_value].  This eliminator only
    replays that certificate: it performs no token update and no world update;
    callers still have to prove the token head and call the checked
    [PWR.resolve_current] update. *)
val observed_result_targeted_resolve_event_decoder_fact
    (#result #payload:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (payload_value:payload)
    (x:result)
    (event:observed_result_targeted_resolve_event #result #payload observed_nat ot c pack pid payload_value x)
    (st:PW.state_view)
    (len:nat)
  : Lemma
      (requires PW.state_interp st /\ PW.runtime_matches_ctr st ot c len)
      (ensures st.PW.world_decoder observed_nat ==
        Some { PW.proph = pid; PW.payload = pack x payload_value })

let emp_inames : inames = GhostSet.empty

let join_inames (is1 is2 : inames) : inames =
  GhostSet.union is1 is2

let inames_subset (is1 is2 : inames) : prop =
  GhostSet.subset is1 is2

let (/!) (is1 is2 : inames) : prop =
  GhostSet.disjoint is1 is2

unfold
let inames_disj (ictx:inames) : Type = is:inames{is /! ictx}

val act 
    (a:Type u#a)
    (tag:reifiability)
    (opens:inames)
    (pre:slprop)
    (post:a -> slprop)
: Type u#(max a 5)

val return 
    (#a:Type u#a)
    (#r:_)
    #opens
    (#post:a -> slprop)
    (x:a)
: act a r opens (post x) post

val bind_ghost
     (#a:Type u#a)
     (#b:Type u#b)
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a Ghost opens pre1 post1)
     (g:(x:a -> act b Ghost opens (post1 x) post2))
: act b Ghost opens pre1 post2

val bind_atomic
     (#a:Type u#a)
     (#b:Type u#b)
     (#r1: reifiability)
     (#r2: reifiability { r1 == Ghost \/ r2 == Ghost })
     (#opens:inames)
     (#pre1 #post1 #post2:_)
     (f:act a r1 opens pre1 post1)
     (g:(x:a -> act b r2 opens (post1 x) post2))
: act b Atomic opens pre1 post2

val frame
     (#a:Type u#a)
     (#r:reifiability)
     (#opens:inames)
     (#pre #post #frame:_)
     (f:act a r opens pre post)
: act a r opens (pre ** frame) (fun x -> post x ** frame)

val lift_ghost_atomic
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (f:act a Ghost opens pre post)
: act a Atomic opens pre post

val weaken 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r0 #r1:reifiability)
    (#opens opens':inames)
    (f:act a r0 opens pre post)
: act a (r0 ^^ r1) (GhostSet.union opens opens') pre post

val sub 
    (#a:Type)
    (#pre:slprop)
    (#post:a -> slprop)
    (#r:reifiability)
    (#opens:inames)
    (pre':slprop { slprop_equiv pre pre' })
    (post':a -> slprop { forall x. slprop_equiv (post x) (post' x) })
    (f:act a r opens pre post)
: act a r opens pre' post'

val lift (#a:Type u#a) #r #opens (#pre:slprop) (#post:a -> slprop)
         (m:act a r opens pre post)
: I.stt a pre post

(** Lift an atomic action into the semantic [stt] monad through a
    result-dependent observation step, then continue with access to both the
    physical result and decoded observation. *)
val lift_observed_result_cont
    (#a:Type u#a)
    (#obs:a -> Type u#100)
    (#b:Type u#b)
    (decode_obs:(x:a -> nat -> obs x))
    (#opens:inames)
    (#pre:slprop)
    (#mid:a -> slprop)
    (#post:b -> slprop)
    (m:act a Atomic opens pre mid)
    (k:(x:a -> obs x -> I.stt b (mid x) post))
: I.stt b pre post

(** Hidden-state sibling of [lift_observed_result_cont].  The public pre/post
    remain ordinary, while prophecy-aware adequacy supplies the result-dependent
    hidden state [si_pre] at the consumed observation and receives [si_post] at
    [NST.bump_observation]. *)
val lift_observed_result_cont_hidden_state
    (#a:Type u#a)
    (#obs:a -> Type u#100)
    (#b:Type u#b)
    (decode_obs:(x:a -> nat -> obs x))
    (#opens:inames)
    (#pre:slprop)
    (#mid:a -> slprop)
    (#post:b -> slprop)
    (#si_pre:(x:a -> obs x -> NST.obs_tape -> NST.ctr -> slprop))
    (#si_post:(x:a -> obs x -> NST.obs_tape -> NST.ctr -> slprop))
    (m:act a Atomic opens pre mid)
    (k:(x:a -> observed_nat:nat -> o:obs x { o == decode_obs x observed_nat } ->
      #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      I.stt b (mid x ** si_pre x o (reveal ot) (reveal c))
        (fun y -> post y ** si_post x o (reveal ot) (NST.bump_observation (reveal c)))))
: I.stt b pre post

(** Native active observed-result hidden-state action.  The callback is the
    whole one-step action run under runner-owned [si ot c] and lowers to the
    Ret-specialized [ObservedResultActWithHiddenStateReturnAction]; the active
    runner consumes [ot (NST.observation_index c)] and closes [si] at
    [NST.bump_observation c] without going through the ordinary divergent
    [ObservedResultActWithHiddenState*] branches. *)
val lift_observed_result_hidden_state_action_invs
    (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (#opens:inames)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(observed_nat:nat -> #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      #receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
      #value_event:(#t:Type0 -> x:t -> erased (Sem.observed_result_value_event #t observed_nat (reveal ot) (reveal c) x)) ->
      #resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        #current_receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
        #value_receipt:erased (Sem.observed_result_value_event #result observed_nat (reveal ot) (reveal c) x) ->
        erased (observed_result_resolve_event #result #payload observed_nat (reveal ot) (reveal c) pack pid x payload_value)) ->
      act a Atomic opens
        (pre ** si (reveal ot) (reveal c))
        (fun x -> post x ** si (reveal ot) (NST.bump_observation (reveal c)))))
: I.stt a pre post

val lift_observed_result_hidden_state_action
    (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(observed_nat:nat -> #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      #receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
      #value_event:(#t:Type0 -> x:t -> erased (Sem.observed_result_value_event #t observed_nat (reveal ot) (reveal c) x)) ->
      #resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        #current_receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
        #value_receipt:erased (Sem.observed_result_value_event #result observed_nat (reveal ot) (reveal c) x) ->
        erased (observed_result_resolve_event #result #payload observed_nat (reveal ot) (reveal c) pack pid x payload_value)) ->
      act a Atomic emp_inames
        (pre ** si (reveal ot) (reveal c))
        (fun x -> post x ** si (reveal ot) (NST.bump_observation (reveal c)))))
: I.stt a pre post

val lift_targeted_post_result_observed_result_hidden_state_action
    (#resolve_result #resolve_payload:Type0)
    (#pack:erased (resolve_result -> resolve_payload -> nat))
    (#pid:erased nat)
    (#payload_value:erased resolve_payload)
    (#pre:slprop)
    (#post:resolve_result -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(observed_nat:nat -> #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      #receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
      (physical_post:(resolve_result -> slprop) &
       physical:act resolve_result Atomic emp_inames
         (pre ** si (reveal ot) (reveal c))
         (fun x -> physical_post x ** si (reveal ot) (reveal c)) &
       finish:(x:resolve_result ->
         #event:erased (observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat (reveal ot) (reveal c)
           (reveal pack) (reveal pid) (reveal payload_value) x) ->
         act unit Ghost emp_inames
           (physical_post x ** si (reveal ot) (reveal c))
           (fun _ -> post x ** si (reveal ot) (NST.bump_observation (reveal c)))))))
: I.stt resolve_result pre post

(** Checked active execution path for the Ret-specialized hidden-state
    observed-result lowering used by public Resolve.  The same callback used to
    build [lift_observed_result_hidden_state_action] is handed directly to the
    active observation runner, which consumes [ot (NST.observation_index c)] and
    returns the final value without passing through the ordinary divergent
    [ObservedResultActWithHiddenState*] branches. *)
val observed_result_hidden_state_action_active_run
    (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(observed_nat:nat -> #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      #receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
      #value_event:(#t:Type0 -> x:t -> erased (Sem.observed_result_value_event #t observed_nat (reveal ot) (reveal c) x)) ->
      #resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        #current_receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
        #value_receipt:erased (Sem.observed_result_value_event #result observed_nat (reveal ot) (reveal c) x) ->
        erased (observed_result_resolve_event #result #payload observed_nat (reveal ot) (reveal c) pack pid x payload_value)) ->
      act a Atomic emp_inames
        (pre ** si (reveal ot) (reveal c))
        (fun x -> post x ** si (reveal ot) (NST.bump_observation (reveal c)))))
    (frame:slprop)
    (fuel:pos)
  : PulseCore.Semantics.active_observed_run_result #state a (FStar.FunctionalExtensionality.on_dom a post) frame fuel pre

val observed_result_targeted_post_result_hidden_state_action_active_run
    (#resolve_result #resolve_payload:Type0)
    (#pack:erased (resolve_result -> resolve_payload -> nat))
    (#pid:erased nat)
    (#payload_value:erased resolve_payload)
    (#pre:slprop)
    (#post:resolve_result -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(observed_nat:nat -> #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      #receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
      (physical_post:(resolve_result -> slprop) &
       physical:act resolve_result Atomic emp_inames
         (pre ** si (reveal ot) (reveal c))
         (fun x -> physical_post x ** si (reveal ot) (reveal c)) &
       finish:(x:resolve_result ->
         #event:erased (observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat (reveal ot) (reveal c)
           (reveal pack) (reveal pid) (reveal payload_value) x) ->
         act unit Ghost emp_inames
           (physical_post x ** si (reveal ot) (reveal c))
           (fun _ -> post x ** si (reveal ot) (NST.bump_observation (reveal c)))))))
    (frame:slprop)
    (fuel:pos)
  : PulseCore.Semantics.active_observed_run_result #state resolve_result (FStar.FunctionalExtensionality.on_dom resolve_result post) frame fuel pre

(** Adequacy-facing checked execution path for the target-fixed two-stage
    observed-result lowering with explicit tapes/counter.  This is the concrete
    Resolve runner used when adequacy owns [si ot c0]: it runs the physical
    observable action, mints the target-fixed receipt for the actual result,
    executes the neutral finisher, and returns with [NST.bump_observation c0]
    without passing through the ordinary divergent hidden-state branches. *)
val observed_result_targeted_post_result_hidden_state_action_active_run_with_ctr
    (#resolve_result #resolve_payload:Type0)
    (#pack:erased (resolve_result -> resolve_payload -> nat))
    (#pid:erased nat)
    (#payload_value:erased resolve_payload)
    (#pre:slprop)
    (#post:resolve_result -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(observed_nat:nat -> #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      #receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
      (physical_post:(resolve_result -> slprop) &
       physical:act resolve_result Atomic emp_inames
         (pre ** si (reveal ot) (reveal c))
         (fun x -> physical_post x ** si (reveal ot) (reveal c)) &
       finish:(x:resolve_result ->
         #event:erased (observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat (reveal ot) (reveal c)
           (reveal pack) (reveal pid) (reveal payload_value) x) ->
         act unit Ghost emp_inames
           (physical_post x ** si (reveal ot) (reveal c))
           (fun _ -> post x ** si (reveal ot) (NST.bump_observation (reveal c)))))))
    (frame:slprop)
    (t:PulseCore.Semantics.tape)
    (at:PulseCore.Semantics.angel_tape)
    (ot:PulseCore.Semantics.observation_tape)
    (c0:NST.ctr)
    (fuel:pos)
    (s0:state.s { state.budget s0 >= fuel /\
      state.interp (((pre ** frame) ** si ot c0) ** state.invariant s0) s0 })
  : Dv (res:(resolve_result & state.s & NST.ctr) {
      state.budget res._2 >= fuel - 1 /\
      state.interp ((((FStar.FunctionalExtensionality.on_dom resolve_result post) res._1 ** frame) ** si ot res._3) ** state.invariant res._2) res._2 /\
      res._3 == NST.bump_observation c0 })

(** Adequacy-facing checked execution path for the same Ret-specialized
    observed-result lowering with explicit tapes/counter.  This is the public
    Resolve-side counterpart of [fresh_prophecy_id_hidden_state_action_active_run]
    when a top-level adequacy proof already owns [si ot c0]. *)
val observed_result_hidden_state_action_active_run_with_ctr
    (#a:Type u#a)
    (#pre:slprop)
    (#post:a -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(observed_nat:nat -> #ot:erased NST.obs_tape ->
      #c:erased (c:NST.ctr{observed_nat == (reveal ot) (NST.observation_index c)}) ->
      #receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
      #value_event:(#t:Type0 -> x:t -> erased (Sem.observed_result_value_event #t observed_nat (reveal ot) (reveal c) x)) ->
      #resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        #current_receipt:erased (Sem.observed_result_current_event observed_nat (reveal ot) (reveal c)) ->
        #value_receipt:erased (Sem.observed_result_value_event #result observed_nat (reveal ot) (reveal c) x) ->
        erased (observed_result_resolve_event #result #payload observed_nat (reveal ot) (reveal c) pack pid x payload_value)) ->
      act a Atomic emp_inames
        (pre ** si (reveal ot) (reveal c))
        (fun x -> post x ** si (reveal ot) (NST.bump_observation (reveal c)))))
    (frame:slprop)
    (t:PulseCore.Semantics.tape)
    (at:PulseCore.Semantics.angel_tape)
    (ot:PulseCore.Semantics.observation_tape)
    (c0:NST.ctr)
    (fuel:pos)
    (s0:state.s { state.budget s0 >= fuel /\
      state.interp (((pre ** frame) ** si ot c0) ** state.invariant s0) s0 })
  : Dv (res:(a & state.s & NST.ctr) {
      state.budget res._2 >= fuel - 1 /\
      state.interp ((((FStar.FunctionalExtensionality.on_dom a post) res._1 ** frame) ** si ot res._3) ** state.invariant res._2) res._2 /\
      res._3 == NST.bump_observation c0 })

(** Checked active execution path for the same Ret-specialized hidden-state
    NewProph lowering.  This entry point is the non-diverging runner used when
    adequacy owns [si ot c] as active hidden state. *)
val fresh_prophecy_id_hidden_state_action_active_run
    (#a:Type u#a)
    (#post:a -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(pid:nat -> #ot:erased NST.obs_tape -> #c:erased (c:NST.ctr{pid == NST.prophecy_index c}) ->
      act a Ghost emp_inames
        (emp ** si (reveal ot) (reveal c))
        (fun x -> post x ** si (reveal ot) (NST.bump_prophecy (reveal c)))))
    (frame:slprop)
    (fuel:pos)
  : PulseCore.Semantics.active_run_result #state a (FStar.FunctionalExtensionality.on_dom a post) frame fuel emp

(** Checked active execution path for the same Ret-specialized hidden-state
    NewProph lowering with explicit tapes/counter.  Adequacy code that owns
    [si ot c0] can execute the public NewProph shape directly and returns at
    [NST.bump_prophecy c0], without dispatching through the ordinary divergent
    hidden-state branch. *)
val fresh_prophecy_id_hidden_state_action_active_run_with_ctr
    (#a:Type u#a)
    (#post:a -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(pid:nat -> #ot:erased NST.obs_tape -> #c:erased (c:NST.ctr{pid == NST.prophecy_index c}) ->
      act a Ghost emp_inames
        (emp ** si (reveal ot) (reveal c))
        (fun x -> post x ** si (reveal ot) (NST.bump_prophecy (reveal c)))))
    (frame:slprop)
    (t:PulseCore.Semantics.tape)
    (at:PulseCore.Semantics.angel_tape)
    (ot:PulseCore.Semantics.observation_tape)
    (c0:NST.ctr)
    (fuel:pos)
    (s0:state.s { state.budget s0 >= fuel /\
      state.interp (((emp ** frame) ** si ot c0) ** state.invariant s0) s0 })
  : Dv (res:(a & state.s & NST.ctr) {
      state.budget res._2 >= fuel - 1 /\
      state.interp ((((FStar.FunctionalExtensionality.on_dom a post) res._1 ** frame) ** si ot res._3) ** state.invariant res._2) res._2 /\
      res._3 == NST.bump_prophecy c0 })

(** Lift a neutral/ghost allocation action through the active FreshProph cursor
    while a prophecy-aware runner owns [si ot c].  The action closes [si] at
    [NST.bump_prophecy c] in the same semantic NewProph step. *)
val lift_fresh_prophecy_id_hidden_state_action
    (#a:Type u#a)
    (#post:a -> slprop)
    (#si:NST.obs_tape -> NST.ctr -> slprop)
    (m:(pid:nat -> #ot:erased NST.obs_tape -> #c:erased (c:NST.ctr{pid == NST.prophecy_index c}) ->
      act a Ghost emp_inames
        (emp ** si (reveal ot) (reveal c))
        (fun x -> post x ** si (reveal ot) (NST.bump_prophecy (reveal c)))))
: I.stt a emp post


//////////////////////////////////////////////////////////////////////
// Invariants
//////////////////////////////////////////////////////////////////////

let add_inv (e:inames) (i:iref) : inames = GhostSet.union (singleton i) e
let mem_inv (e:inames) (i:iref) : GTot bool = GhostSet.mem i e

let inv : iref -> slprop -> slprop = Sep.inv

val dup_inv (i:iref) (p:slprop)
  : act unit Ghost emp_inames (inv i p) (fun _ -> (inv i p) ** (inv i p))

val new_invariant (p:slprop)
: act iref Ghost emp_inames p (fun i -> inv i p)

val fresh_invariant (ctx:inames { Pulse.Lib.GhostSet.is_finite ctx }) (p:slprop)
: act (i:iref { ~(GhostSet.mem i ctx) }) Ghost emp_inames p (fun i -> inv i p)

val inames_live_inv (i:iref) (p:slprop)
: act unit Ghost emp_inames (inv i p) (fun _ -> inv i p ** Sep.inames_live (singleton i))

val with_invariant
    (#a:Type)
    (#r:_)
    (#fp:slprop)
    (#fp':a -> slprop)
    (#f_opens:inames)
    (#p:slprop)
    (i:iref { not (mem_inv f_opens i) })
    (f:unit -> act a r f_opens (somewhere (later p) ** fp) (fun x -> somewhere (later p) ** fp' x))
: act a r (add_inv f_opens i) ((inv i p) ** fp) (fun x -> (inv i p) ** fp' x)

val invariant_name_identifies_invariant
      (p q:slprop)
      (i:iref)
: act unit
      Ghost
      emp_inames
      (inv i p ** inv i q)
      (fun _ -> inv i p ** inv i q ** later (equiv p q))

////////////////////////////////////////////////////////////////////////
// later and credits
////////////////////////////////////////////////////////////////////////
val later_intro (p:slprop)
: act unit Ghost emp_inames p (fun _ -> later p)

val later_elim (p:slprop)
: act unit Ghost emp_inames (later p ** later_credit 1) (fun _ -> p)

val implies_elim (p:slprop) (q:slprop { implies p q })
: act unit Ghost emp_inames p (fun _ -> q)

val buy1 ()
: stt unit emp (fun _ -> later_credit 1)

////////////////////////////////////////////////////////////////////////
// References
////////////////////////////////////////////////////////////////////////
val core_ref : Type u#0
val core_ref_null : core_ref
val is_core_ref_null (r:core_ref) : b:bool { b <==> r == core_ref_null }

let ref (a:Type u#3) (p:pcm a) : Type u#0 = core_ref
let ref_null #a (p:pcm a) : ref a p = core_ref_null

let is_ref_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p)
: b:bool { b <==> r == ref_null p }
= is_core_ref_null r

val pts_to (#a:Type) (#p:pcm a) (r:ref a p) (v:a) : slprop

val timeless_pts_to
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (v:a)
: Lemma (timeless (pts_to r v))

val on_pcm_pts_to_eq l #a #p r v : squash (Sep.on l (pts_to #a #p r v) == pts_to r v)

val pts_to_not_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ref a p) (v:a)
: act (squash (not (is_ref_null r)))
    Ghost
    emp_inames 
    (pts_to r v)
    (fun _ -> pts_to r v)

val alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act (ref a pcm)
      Atomic
      emp_inames
      emp
      (fun r -> pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (v:a{compatible p x v /\ p.refine v})
      Atomic
      emp_inames
      (pts_to r x)
      (fun v -> pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit
    Atomic
    emp_inames
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit
    Ghost
    emp_inames
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 ** pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1))
    Ghost
    emp_inames
    (pts_to r v0 ** pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

///////////////////////////////////////////////////////////////////
// pure
///////////////////////////////////////////////////////////////////
val pure_true ()
: slprop_equiv (pure True) emp

val intro_pure (p:prop) (pf:squash p)
: act unit Ghost emp_inames emp (fun _ -> pure p)

val elim_pure (p:prop)
: act (squash p) Ghost emp_inames (pure p) (fun _ -> emp)

///////////////////////////////////////////////////////////////////
// exists*
///////////////////////////////////////////////////////////////////
val intro_exists (#a:Type u#a) (p:a -> slprop) (x:erased a)
: act unit Ghost emp_inames (p x) (fun _ -> exists* x. p x)

val elim_exists (#a:Type u#a) (p:a -> slprop)
: act (erased a) Ghost emp_inames (exists* x. p x) (fun x -> p x)

///////////////////////////////////////////////////////////////////
// Other utils
///////////////////////////////////////////////////////////////////
val drop (p:slprop)
: act unit Ghost emp_inames p (fun _ -> emp)

val loc_get ()
: act loc_id Ghost emp_inames emp (fun l -> Sep.loc l)

////////////////////////////////////////////////////////////////////////
// Ghost References
////////////////////////////////////////////////////////////////////////
[@@erasable]
val core_ghost_ref : Type u#0
val core_ghost_ref_null : core_ghost_ref
let ghost_ref (#a:Type u#3) (p:pcm a) : Type u#0 = core_ghost_ref
val ghost_pts_to (#a:Type) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop

val timeless_ghost_pts_to
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (v:a)
: Lemma (timeless (ghost_pts_to r v))

val on_ghost_pcm_pts_to_eq l #a #p r v : squash (Sep.on l (ghost_pts_to #a #p r v) == ghost_pts_to r v)

val ghost_pts_to_not_null (#a:Type) (#p:FStar.PCM.pcm a) (r:ghost_ref p) (v:a)
: act (squash (r =!= core_ghost_ref_null))
    Ghost
    emp_inames 
    (ghost_pts_to r v)
    (fun _ -> ghost_pts_to r v)

val ghost_alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: act (ghost_ref pcm) Ghost emp_inames
    emp 
    (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act (erased (v:a{compatible p x v /\ p.refine v})) Ghost emp_inames
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act unit Ghost emp_inames 
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act unit Ghost emp_inames
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 ** ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act (squash (composable pcm v0 v1)) Ghost emp_inames
    (ghost_pts_to r v0 ** ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))


////////////////////////////////////////////////////////////////////////
let non_informative a = x:erased a -> y:a { reveal x == y}

val lift_erased 
    (#a:Type)
    (ni_a:non_informative a)
    (#opens:inames)
    (#pre:slprop)
    (#post:a -> slprop)
    (f:erased (act a Ghost opens pre post))
: act a Ghost opens pre post

val equiv_refl (a:slprop)
: act unit Ghost emp_inames emp (fun _ -> equiv a a)

val equiv_dup (a b:slprop)
: act unit Ghost emp_inames (equiv a b) (fun _ -> equiv a b ** equiv a b)

val equiv_trans (a b c:slprop)
: act unit Ghost emp_inames (equiv a b ** equiv b c) (fun _ -> equiv a c)

val equiv_elim (a b:slprop)
: act unit Ghost emp_inames (a ** equiv a b) (fun _ -> b)

/// slprop_refs
[@@erasable]
let slprop_ref : Type0 = Sep.slprop_ref

val null_slprop_ref : slprop_ref

let slprop_ref_pts_to (x: slprop_ref) (y: slprop) : slprop = Sep.slprop_ref_pts_to x y

val slprop_ref_alloc (y: slprop)
: act slprop_ref Ghost emp_inames emp fun x -> slprop_ref_pts_to x y

val slprop_ref_share (x:slprop_ref) (y:slprop)
: act unit Ghost emp_inames (slprop_ref_pts_to x y) fun _ -> slprop_ref_pts_to x y ** slprop_ref_pts_to x y

val slprop_ref_gather (x:slprop_ref) (y1 y2: slprop)
: act unit Ghost emp_inames (slprop_ref_pts_to x y1 ** slprop_ref_pts_to x y2) fun _ -> slprop_ref_pts_to x y1 ** later (I.equiv y1 y2)

val impersonate #a #r #is #pre #post l (k: act a r is pre post) :
    act a r is (Sep.on l pre) (fun r -> Sep.on l (post r))

val impersonate_stt #a #pre #post (l: loc_id) (k: stt a pre post) :
    stt a (Sep.on l pre) (fun x -> Sep.on l (post x))

val fork #p0 (l l': loc_id) (f0:stt unit (loc l' ** on l p0) (fun _ -> emp)) :
    stt unit (loc l ** p0) (fun _ -> emp)