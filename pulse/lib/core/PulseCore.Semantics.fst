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
module PulseCore.Semantics

module U = Pulse.Lib.Raise
module ST = PulseCore.HoareStateMonad
module NST = PulseCore.NondeterministicHoareStateMonad
module PNST = PulseCore.PartialNondeterministicHoareStateMonad
module PW = PulseCore.ProphecyWorld
module F = FStar.FunctionalExtensionality

open FStar.Ghost
open FStar.FunctionalExtensionality
open PulseCore.PartialNondeterministicHoareStateMonad

/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quantifiers is more convenient for the proof done here.

let associative #a (f: a -> a -> a) =
  forall x y z. f x (f y z) == f (f x y) z

let commutative #a (f: a -> a -> a) =
  forall x y. f x y == f y x

let is_unit #a (x:a) (f:a -> a -> a) =
  forall y. f x y == y /\ f y x == y

(**
 * A state typeclass:
 *  - [s] is the type of states
 *  - [budget] is the amount of fuel needed to run actions on [s]
 *  - [pred] is the type of state assertions
 *  - [emp] is the empty state assertion
 *  - [star] is the separating conjunction of state assertions
 *  - [interp p s] is the interpretation of a state assertion [p] in a state [s]
 *  - [invariant] is an internal invariant that a caller can instantiate and is maintained
 *                by every action and the semantics as a whole
 *  - [laws] state that {pred, emp, star} are a commutative monoid
 *)
noeq
type state : Type u#(s + 1)= {
  s:Type u#s;
  budget: s -> GTot int;
  pred:Type u#s;
  emp: pred;
  star: pred -> pred -> pred;
  interp: pred -> s -> prop;
  invariant: s -> pred;
  laws: squash (associative star /\ commutative star /\ is_unit emp star);
}

(** [post a c] is a postcondition on [a]-typed result *)
let post (s:state) a = a ^-> s.pred

(** We interpret computations into the npst monad,
    for partial, nondeterministic, preorder-state transfomers.
    npst_sep provides separation-logic specifications for those computations.
    pst_sep is analogous, except computation in pst_sep are also total
 **)
let st_sep_aux (st:state)
               (inv:st.s -> st.pred)
               (a:Type)
               (pre:st.pred)
               (post:a -> st.pred) =
  ST.st #(st.s) a
    (fun s0 -> st.budget s0 > 0 /\ st.interp (pre `st.star` inv s0) s0 )
    (fun s0 x s1 -> st.budget s0 - st.budget s1 <= 1 /\ st.interp (post x `st.star` inv s1) s1)
     
let st_sep st a pre post = st_sep_aux st st.invariant a pre post

let pnst_sep (st:state u#s) (a:Type u#a) (prefuel postfuel: nat) (pre:st.pred) (post:a -> st.pred) =
  PNST.pnst #(st.s) a
    (fun s0 -> st.budget s0 >= prefuel /\ st.interp (pre `st.star` st.invariant s0) s0 )
    (fun _ x s1 -> st.budget s1 >= postfuel /\ st.interp (post x `st.star` st.invariant s1) s1)

let star_rotate_right (st:state u#s) (x y z:st.pred)
  : Lemma (st.star (st.star x y) z == st.star (st.star x z) y)
= assert (associative st.star);
  assert (commutative st.star);
  assert (st.star (st.star x y) z == st.star x (st.star y z));
  assert (st.star y z == st.star z y);
  assert (st.star x (st.star y z) == st.star x (st.star z y));
  assert (st.star (st.star x z) y == st.star x (st.star z y))

(** Counter-aware sibling of [pnst_sep].  Existing Pulse semantics continue to
    use [pnst_sep]; this variant is the smallest adequacy-facing seam needed by
    the prophecy-state interpretation: a proof can additionally relate the
    initial oracle counter to the returned counter while keeping ordinary state
    assertions and clients unchanged. *)
let pnst_sep_ctr (st:state u#s) (a:Type u#a)
    (prefuel postfuel:nat)
    (pre:st.pred)
    (post:a -> st.pred)
    (ctr_post:st.s -> NST.ctr -> a -> st.s -> NST.ctr -> prop)
  = PNST.pnst_ctr #(st.s) a
    (fun s0 -> st.budget s0 >= prefuel /\ st.interp (pre `st.star` st.invariant s0) s0 )
    (fun s0 c0 x s1 c1 ->
      st.budget s1 >= postfuel /\
      st.interp (post x `st.star` st.invariant s1) s1 /\
      ctr_post s0 c0 x s1 c1)

(** Observation-tape/counter-indexed state-interpretation seam.

    This sibling of [pnst_sep] lets an adequacy proof own a resource indexed by
    the active observation tape and [NST.ctr] in both the pre- and
    postcondition.  It is deliberately additive: ordinary Pulse computations
    still use [pnst_sep], while prophecy adequacy can instantiate [si] with the
    shared [proph_map_interp]-style resource and close it at the returned
    counter. *)
let pnst_sep_obs_ctr_interp (st:state u#s) (a:Type u#a)
    (prefuel postfuel:nat)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (pre:st.pred)
    (post:a -> st.pred)
    (ctr_post:st.s -> PNST.obs_tape -> NST.ctr -> a -> st.s -> NST.ctr -> prop)
  = PNST.pnst_obs_ctr #(st.s) a
    (fun s0 ot c0 ->
      st.budget s0 >= prefuel /\
      st.interp ((pre `st.star` si ot c0) `st.star` st.invariant s0) s0)
    (fun s0 ot c0 x s1 c1 ->
      st.budget s1 >= postfuel /\
      st.interp ((post x `st.star` si ot c1) `st.star` st.invariant s1) s1 /\
      ctr_post s0 ot c0 x s1 c1)

(** Adequacy hook for state-interpretation-aware NewProph cursor steps.

    [pnst_sep_obs_ctr_interp] is intentionally generic in the state
    interpretation [si], so the core semantics cannot know how an arbitrary
    [si ot c] resource should advance when the active prophecy-id cursor is
    bumped.  This helper isolates that obligation: the caller supplies the
    resource-closing proof [close] for exactly the concrete cursor facts of
    [NST.fresh_prophecy_id_obs_ctr].  This helper is deliberately a pure,
    same-[s0] weakening hook: it can move an interpretation whose counter
    indexing changes without changing the underlying semantic state.  A real
    executable prophecy allocation rule still has to combine the cursor step
    with the state-changing ghost/resource update of the active component; that
    later rule, not this pure hook alone, is what can replace the current
    primitive-boundary NewProph opening. *)
let pnst_sep_obs_ctr_interp_fresh_prophecy_id (st:state u#s)
    (prefuel postfuel:nat)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (pre:st.pred)
    (post:nat -> st.pred)
    (ctr_post:st.s -> PNST.obs_tape -> NST.ctr -> nat -> st.s -> NST.ctr -> prop)
    (close:(s0:st.s -> ot:PNST.obs_tape -> c:NST.ctr ->
      Lemma
        (requires st.budget s0 >= prefuel /\
          st.interp ((pre `st.star` si ot c) `st.star` st.invariant s0) s0)
        (ensures st.budget s0 >= postfuel /\
          st.interp ((post (NST.prophecy_index c) `st.star` si ot (NST.bump_prophecy c))
            `st.star` st.invariant s0) s0 /\
          ctr_post s0 ot c (NST.prophecy_index c) s0 (NST.bump_prophecy c))))
  : pnst_sep_obs_ctr_interp st nat prefuel postfuel si pre post ctr_post
= let base = PNST.lift_obs_ctr (NST.fresh_prophecy_id_obs_ctr #st.s ()) in
  PNST.weaken_obs_ctr_with
    (fun _ _ _ -> ())
    (fun s0 ot c0 _ _ _ -> close s0 ot c0)
    base

(** Adequacy hook for state-interpretation-aware observation consumption.

    This is the observation-side sibling of
    [pnst_sep_obs_ctr_interp_fresh_prophecy_id].  The supplied [close] proof
    must update [si] from the input counter to [NST.bump_observation c] using
    the actual nat [ot (NST.observation_index c)] consumed by
    [NST.observe_obs_ctr].  As above, [close] is a same-state proof obligation.
    It records the exact counter/observation facts, but an Iris-faithful Resolve
    rule that updates the authoritative prophecy component must be a
    state-changing observed-result action/adequacy rule layered on top of this
    shape, rather than a mere weakening proof or primitive-boundary witness. *)
let pnst_sep_obs_ctr_interp_observe (st:state u#s)
    (prefuel postfuel:nat)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (pre:st.pred)
    (post:nat -> st.pred)
    (ctr_post:st.s -> PNST.obs_tape -> NST.ctr -> nat -> st.s -> NST.ctr -> prop)
    (close:(s0:st.s -> ot:PNST.obs_tape -> c:NST.ctr ->
      Lemma
        (requires st.budget s0 >= prefuel /\
          st.interp ((pre `st.star` si ot c) `st.star` st.invariant s0) s0)
        (ensures st.budget s0 >= postfuel /\
          st.interp ((post (ot (NST.observation_index c)) `st.star` si ot (NST.bump_observation c))
            `st.star` st.invariant s0) s0 /\
          ctr_post s0 ot c (ot (NST.observation_index c)) s0 (NST.bump_observation c))))
  : pnst_sep_obs_ctr_interp st nat prefuel postfuel si pre post ctr_post
= let base = PNST.lift_obs_ctr (NST.observe_obs_ctr #st.s ()) in
  PNST.weaken_obs_ctr_with
    (fun _ _ _ -> ())
    (fun s0 ot c0 _ _ _ -> close s0 ot c0)
    base

(** Runner-minted receipt that an active observed-result step consumed the
    current observation cell [observed_nat = ot (NST.observation_index c)].
    This is only the cursor/cell receipt; result-dependent physical-result and
    Resolve-payload receipts are represented by [observed_result_value_event]
    and [observed_result_resolve_event] below and are minted by the active
    runner capability for the actual value returned by the physical action. *)
[@@erasable]
private noeq type observed_result_current_event_repr
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
  = | ObservedResultCurrentEvent:
      observed_result_current_event_repr observed_nat ot c

type observed_result_current_event
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
  = observed_result_current_event_repr observed_nat ot c

(** Result-indexed active observed-result event receipt.

    The active runner passes a minting capability for this type to the
    observed-result callback.  It records that [x] is the physical result of the
    observed action at the consumed current cell; Resolve-specific payload
    evidence is represented separately by [observed_result_resolve_event].  The
    representation is private to this module so callers cannot forge current or
    value receipts outside the active runner. *)
[@@erasable]
private noeq type observed_result_value_event_repr
    (#a:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (x:a)
  = | ObservedResultValueEvent:
      observed_result_value_event_repr #a observed_nat ot c x

type observed_result_value_event
    (#a:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (x:a)
  = observed_result_value_event_repr #a observed_nat ot c x

(** Resolve-specific active observed-result event receipt.

    The active runner mints this receipt only at the current observation cell
    and only after the physical observable action result [x] is known; the
    attached [payload_value] and untyped prophecy id [pid] are part of the
    index so higher layers cannot reuse a result-only receipt for a different
    Resolve target or payload.  The core event is intentionally
    observation/presentation-only: it performs no token update and
    does not close or mutate any prophecy-world resource by itself.  Its
    representation is private to the semantic runner; clients can only receive
    it through runner-supplied capabilities. *)
[@@erasable]
private noeq type observed_result_resolve_event_repr
    (#result #payload:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (x:result)
    (payload_value:payload)
  = | ObservedResultResolveEvent:
      current_receipt:observed_result_current_event observed_nat ot c ->
      value_receipt:observed_result_value_event #result observed_nat ot c x ->
      observed_result_resolve_event_repr #result #payload observed_nat ot c pack pid x payload_value

type observed_result_resolve_event
    (#result #payload:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (x:result)
    (payload_value:payload)
  = observed_result_resolve_event_repr #result #payload observed_nat ot c pack pid x payload_value

(** Target-fixed Resolve receipt minted from the runner-owned current-cell
    receipt and the value receipt for the actual physical result [x].  Unlike
    [observed_result_resolve_event], the prophecy id, payload packer, and
    attached payload are not arguments to a callback-local universal capability:
    callers obtain this shape only after the target has already been fixed by
    the active observed-result lowering.  The receipt remains
    observation/presentation-only: it carries the target-fixed decoder
    adequacy certificate, but performs no prophecy-world or token update.
    Making the representation private keeps public code from constructing or
    decomposing a targeted receipt except through the active runner's
    target-fixed minting capability. *)
[@@erasable]
private noeq type observed_result_targeted_resolve_event_repr
    (#result #payload:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (payload_value:payload)
    (x:result)
  = | ObservedResultTargetedResolveEvent:
      current_receipt:observed_result_current_event observed_nat ot c ->
      value_receipt:observed_result_value_event #result observed_nat ot c x ->
      decoder_fact:(st:PW.state_view -> len:nat ->
        Lemma
          (requires PW.state_interp st /\ PW.runtime_matches_ctr st ot c len)
          (ensures st.PW.world_decoder observed_nat ==
            Some { PW.proph = pid; PW.payload = pack x payload_value })) ->
      observed_result_targeted_resolve_event_repr #result #payload observed_nat ot c pack pid payload_value x

type observed_result_targeted_resolve_event
    (#result #payload:Type0)
    (observed_nat:nat)
    (ot:NST.obs_tape)
    (c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (payload_value:payload)
    (x:result)
  = observed_result_targeted_resolve_event_repr #result #payload observed_nat ot c pack pid payload_value x

(** Source-level sanity check for the current receipt shape.

    The runner-owned current/value receipts by themselves do not constrain the
    opened prophecy-world decoder.  This verified counterexample keeps the
    remaining trusted obligation honest: any proof of the target-fixed decoder
    fact must come from a stronger native Resolve observation semantics (or an
    explicitly authorized adequacy primitive), not from [PW.state_interp],
    [PW.runtime_matches_ctr], or the current/value receipts alone. *)
private let observed_result_targeted_resolve_event_decoder_premises_counterexample ()
  : Lemma
      (ensures
        (let ot (i:nat) : nat = i in
         let c = NST.initial_ctr in
         let observed_nat = ot (NST.observation_index c) in
         let decode (n:nat) : option PW.observation =
           if n = observed_nat then Some { PW.proph = 1; PW.payload = 99 } else None in
         let st = {
           PW.world_decoder = decode;
           PW.world_future_trace = observed_nat :: [];
           PW.world_token_map = [];
           PW.world_next_proph_id = NST.prophecy_index c;
           PW.world_observation_index = NST.observation_index c } in
         let unit_star (_:unit) (_:unit) : unit = () in
         let runner_state : state = {
           s = unit;
           budget = (fun _ -> 1);
           pred = unit;
           emp = ();
           star = unit_star;
           interp = (fun _ _ -> True);
           invariant = (fun _ -> ());
           laws = () } in
         let runner_si (_:NST.obs_tape) (_:NST.ctr) : unit = () in
         runner_state.interp
           (runner_state.star (runner_state.star runner_state.emp (runner_si ot c))
             (runner_state.invariant ())) () /\
         PW.state_interp st /\
         PW.runtime_matches_ctr st ot c 1 /\
         ~(st.PW.world_decoder observed_nat == Some { PW.proph = 0; PW.payload = 42 })))
= let ot (i:nat) : nat = i in
  let c = NST.initial_ctr in
  let observed_nat = ot (NST.observation_index c) in
  let decode (n:nat) : option PW.observation =
    if n = observed_nat then Some { PW.proph = 1; PW.payload = 99 } else None in
  let st = {
    PW.world_decoder = decode;
    PW.world_future_trace = observed_nat :: [];
    PW.world_token_map = [];
    PW.world_next_proph_id = NST.prophecy_index c;
    PW.world_observation_index = NST.observation_index c } in
  let unit_star (_:unit) (_:unit) : unit = () in
  let runner_state : state = {
    s = unit;
    budget = (fun _ -> 1);
    pred = unit;
    emp = ();
    star = unit_star;
    interp = (fun _ _ -> True);
    invariant = (fun _ -> ());
    laws = () } in
  let runner_si (_:NST.obs_tape) (_:NST.ctr) : unit = () in
  let _current_receipt : observed_result_current_event observed_nat ot c = ObservedResultCurrentEvent in
  let _value_receipt : observed_result_value_event #unit observed_nat ot c () = ObservedResultValueEvent in
  assert (decode observed_nat == Some { PW.proph = 1; PW.payload = 99 });
  assert (~(decode observed_nat == Some { PW.proph = 0; PW.payload = 42 }));
  assert (PW.state_interp st);
  assert (st.PW.world_future_trace == PW.trace_of_tape ot st.PW.world_observation_index 1);
  assert (forall (i:nat) (o:PW.observation). decode (ot (st.PW.world_observation_index + i)) == Some o ==> i < 1);
  assert (PW.decoder_bounded_from st.PW.world_decoder ot st.PW.world_observation_index 1);
  assert (PW.runtime_matches_tape st ot 1);
  assert (st.PW.world_observation_index == NST.observation_index c);
  assert (st.PW.world_next_proph_id == NST.prophecy_index c);
  assert (PW.runtime_matches_ctr st ot c 1);
  assert (runner_state.interp
    (runner_state.star (runner_state.star runner_state.emp (runner_si ot c))
      (runner_state.invariant ())) ());
  assert (~(st.PW.world_decoder observed_nat == Some { PW.proph = 0; PW.payload = 42 }))

(** Current narrow prophecy-specific observed-result adequacy boundary.

    This proof is private to the semantic runner and is stored inside the
    target-fixed Resolve receipt minted after [observed_nat] and the physical
    result [x] are known.  It performs no token update, world update,
    allocation, active-world open/close, or atomic coercion.  Public prophecy
    code can only eliminate the resulting receipt.  The counterexample above
    shows this fact is not derivable from the current receipt/world premises
    alone; it is the exact remaining adequacy obligation for a native targeted
    Resolve event or for an explicitly authorized minimal primitive. *)
private let observed_result_targeted_resolve_event_decoder_adequacy
    (#result #payload:Type0)
    (#observed_nat:nat)
    (#ot:NST.obs_tape)
    (#c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (#pack:result -> payload -> nat)
    (#pid:nat)
    (#payload_value:payload)
    (x:result)
    (current_receipt:observed_result_current_event observed_nat ot c)
    (value_receipt:observed_result_value_event #result observed_nat ot c x)
    (st:PW.state_view)
    (len:nat)
  : Lemma
      (requires PW.state_interp st /\ PW.runtime_matches_ctr st ot c len)
      (ensures st.PW.world_decoder observed_nat ==
        Some { PW.proph = pid; PW.payload = pack x payload_value })
= admit () // intentional: exact target-fixed Resolve observation adequacy
           // boundary.  The trusted call is now receipt-indexed: it can only
           // be installed in a private target-fixed event when the active
           // runner has supplied both the current-cell receipt and the
           // value receipt for this exact physical result [x].

private let mk_observed_result_targeted_resolve_event
    (#result #payload:Type0)
    (#observed_nat:nat)
    (#ot:NST.obs_tape)
    (#c:NST.ctr{observed_nat == ot (NST.observation_index c)})
    (pack:result -> payload -> nat)
    (pid:nat)
    (payload_value:payload)
    (receipt:observed_result_current_event observed_nat ot c)
    (x:result)
    (value_receipt:observed_result_value_event #result observed_nat ot c x)
  : observed_result_targeted_resolve_event #result #payload observed_nat ot c pack pid payload_value x
= ObservedResultTargetedResolveEvent receipt value_receipt
    (fun st len ->
      observed_result_targeted_resolve_event_decoder_adequacy
        #result #payload #observed_nat #ot #c #pack #pid #payload_value x
        receipt value_receipt st len)

let observed_result_targeted_resolve_event_decoder_fact
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
= match event with
  | ObservedResultTargetedResolveEvent _ _ decoder_fact -> decoder_fact st len

(** State-changing adequacy hook for NewProph-style allocation.

    Unlike [pnst_sep_obs_ctr_interp_fresh_prophecy_id], this rule does not just
    weaken an already-closed state interpretation.  The supplied [alloc] step is
    a real state computation framed by [si ot c] at the active input counter; it
    receives the concrete fresh id [NST.prophecy_index c], updates the resource,
    and closes [si] at [NST.bump_prophecy c].  The callback is [Dv]-producing so
    a semantic runner can first construct the next divergent/coinductive reduct
    and only then package the total state transition that updates the active
    state interpretation.  This is the generic core shape needed to replace a
    primitive-boundary NewProph witness with an adequacy-owned proph-map
    component. *)
let pnst_sep_obs_ctr_interp_fresh_prophecy_id_state (st:state u#s)
    (#a:Type u#a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (pre:st.pred)
    (post:a -> st.pred)
    (ctr_post:st.s -> PNST.obs_tape -> NST.ctr -> a -> st.s -> NST.ctr -> prop)
    (alloc:(ot:PNST.obs_tape -> c:NST.ctr -> pid:nat{pid == NST.prophecy_index c} ->
      Dv (ST.st #(st.s) a
        (fun s0 -> st.budget s0 >= fuel /\
          st.interp ((pre `st.star` si ot c) `st.star` st.invariant s0) s0)
        (fun s0 x s1 -> st.budget s1 >= fuel - 1 /\
          st.interp ((post x `st.star` si ot (NST.bump_prophecy c))
            `st.star` st.invariant s1) s1 /\
          ctr_post s0 ot c x s1 (NST.bump_prophecy c)))))
  : pnst_sep_obs_ctr_interp st a fuel (fuel - 1) si pre post ctr_post
= let base = PNST.lift_st_then_fresh_prophecy_obs_ctr_dv
    #st.s #a
    #(fun ot c s0 -> st.budget s0 >= fuel /\
      st.interp ((pre `st.star` si ot c) `st.star` st.invariant s0) s0)
    #(fun ot c _pid s0 x s1 -> st.budget s1 >= fuel - 1 /\
      st.interp ((post x `st.star` si ot (NST.bump_prophecy c))
        `st.star` st.invariant s1) s1 /\
      ctr_post s0 ot c x s1 (NST.bump_prophecy c))
    alloc in
  PNST.weaken_obs_ctr_with
    (fun _ _ _ -> ())
    (fun s0 ot c0 x s1 c1 ->
      assert (c1 == NST.bump_prophecy c0);
      assert (si ot c1 == si ot (NST.bump_prophecy c0));
      assert (st.interp ((post x `st.star` si ot c1) `st.star` st.invariant s1) s1);
      assert (ctr_post s0 ot c0 x s1 c1))
    base

(** State-changing adequacy hook for observed-result Resolve-style steps.

    The supplied [step] runs the physical state action and the authoritative
    prophecy-resource update while framed by [si ot c].  The surrounding PNST
    primitive then consumes exactly the current observation head, advancing the
    counter to [NST.bump_observation c].  Consequently the returned
    postcondition owns [si] at the observation-advanced counter; the decode fact
    can be stated inside [step] using [ot (NST.observation_index c)] and the
    physical result [x]. *)
let pnst_sep_obs_ctr_interp_observed_result_state (st:state u#s)
    (#a:Type u#a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (pre:st.pred)
    (post:a -> st.pred)
    (ctr_post:st.s -> PNST.obs_tape -> NST.ctr -> a -> st.s -> NST.ctr -> prop)
    (step:(ot:PNST.obs_tape -> c:NST.ctr ->
      ST.st #(st.s) a
        (fun s0 -> st.budget s0 >= fuel /\
          st.interp ((pre `st.star` si ot c) `st.star` st.invariant s0) s0)
        (fun s0 x s1 -> st.budget s1 >= fuel - 1 /\
          st.interp ((post x `st.star` si ot (NST.bump_observation c))
            `st.star` st.invariant s1) s1 /\
          ctr_post s0 ot c x s1 (NST.bump_observation c))))
  : pnst_sep_obs_ctr_interp st a fuel (fuel - 1) si pre post ctr_post
= let base = PNST.lift_st_then_observe_obs_ctr
    #st.s #a
    #(fun ot c s0 -> st.budget s0 >= fuel /\
      st.interp ((pre `st.star` si ot c) `st.star` st.invariant s0) s0)
    #(fun ot c s0 x s1 -> st.budget s1 >= fuel - 1 /\
      st.interp ((post x `st.star` si ot (NST.bump_observation c))
        `st.star` st.invariant s1) s1 /\
      ctr_post s0 ot c x s1 (NST.bump_observation c))
    step in
  PNST.weaken_obs_ctr_with
    (fun _ _ _ -> ())
    (fun s0 ot c0 x s1 c1 ->
      assert (c1 == NST.bump_observation c0);
      assert (si ot c1 == si ot (NST.bump_observation c0));
      assert (st.interp ((post x `st.star` si ot c1) `st.star` st.invariant s1) s1);
      assert (ctr_post s0 ot c0 x s1 c1))
    base


(** [action c s]: atomic actions are, intuitively, single steps of
 *  state-transforming computations (in the nmst monad).
 *  However, we augment them with two features:
 *   1. they have pre-condition [pre] and post-condition [post]
 *   2. their type guarantees that they are frameable
 *  Thanks to Matt Parkinson for suggesting to set up atomic actions
 *  as frame-preserving steps.
 *  Also see: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/views.pdf
 *)
noeq
type action (st:state u#s) (a:Type u#a) : Type u#(max a s) = {
  pre: st.pred;
  post: post st a;
  step: (
    frame:st.pred ->
    st_sep st a (st.star pre frame) 
                (fun x -> st.star (post x) frame)
  )
 }
  
(** Two-stage target-fixed observed-result plan.

    The public Resolve lowering should not receive a freely callable
    [x -> event] capability before the physical action runs.  The public Core
    API therefore packages a physical observable action and a post-result
    finisher.  A fully native Semantics constructor for that plan would need to
    fix the result universe of [m] to the Type0 Resolve result; guarded probes
    show the current universe-polymorphic [m] family cannot express that
    specialization without a larger API redesign. *)
let as_post (#st:state u#s) (#a:Type u#a) (p:st.pred)
: post st a
= F.on_dom a (fun _ -> p)

(** [m #st a pre post]:
 *  A free monad for divergence, state and parallel composition
 *  with generic actions. The main idea:
 *
 *  Every continuation may be divergent. As such, [m] is indexed by
 *  pre- and post-conditions so that we can do proofs
 *  intrinsically.
 *
 *  Universe-polymorphic in both the state and result type
 *
 *)
noeq
type m (#st:state u#s) : (a:Type u#a) -> st.pred -> post st a -> Type u#(max (act + 1) s (a + 1)) =
  | Ret:
      #a:Type u#a ->
      #post:post st a ->
      x:a ->
      m a (post x) post
  | Act:
      #a:Type u#a ->
      #post:post st a ->
      #b:Type u#act ->
      f:action st b ->
      k:(x:b -> Dv (m a (f.post x) post)) ->
      m a f.pre post
  | ObservedAct:
      #a:Type u#a ->
      #post:post st a ->
      #b:Type u#act ->
      #obs:Type u#act ->
      decode_obs:(nat -> obs) ->
      f:action st b ->
      k:(o:obs -> x:b -> Dv (m a (f.post x) post)) ->
      m a f.pre post
  | ObservedResultAct:
      #a:Type u#a ->
      #post:post st a ->
      #b:Type u#act ->
      #obs:(b -> Type u#act) ->
      decode_obs:(x:b -> nat -> obs x) ->
      f:action st b ->
      k:(x:b -> o:obs x -> Dv (m a (f.post x) post)) ->
      m a f.pre post
  | ObservedResultActWithHiddenState:
      #a:Type u#a ->
      #post:post st a ->
      #b:Type u#act ->
      #obs:(b -> Type u#act) ->
      decode_obs:(x:b -> nat -> obs x) ->
      f:action st b ->
      si_pre:(x:b -> o:obs x -> NST.obs_tape -> NST.ctr -> st.pred) ->
      si_post:(x:b -> o:obs x -> NST.obs_tape -> NST.ctr -> st.pred) ->
      k:(x:b -> observed_nat:nat -> o:obs x { o == decode_obs x observed_nat } ->
        ot:NST.obs_tape -> c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
        Dv (m a (f.post x `st.star` si_pre x o ot c)
          (F.on_dom a (fun y -> post y `st.star` si_post x o ot (NST.bump_observation c))))) ->
      m a f.pre post
  | ObservedResultActWithHiddenStateAction:
      #a:Type u#a ->
      #pre:st.pred ->
      #q:post st a ->
      si:(NST.obs_tape -> NST.ctr -> st.pred) ->
      step:(observed_nat:nat -> ot:NST.obs_tape ->
        c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
        receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
        (b:Type u#act &
         mid:post st b &
         act:action st b {
           act.pre == pre `st.star` si ot c /\
           act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) } &
         (y:b -> Dv (m a (mid y) q)))) ->
      m a pre q
  | ObservedResultActWithHiddenStateReturnAction:
      #a:Type u#a ->
      #pre:st.pred ->
      #q:post st a ->
      si:(NST.obs_tape -> NST.ctr -> st.pred) ->
      step:(observed_nat:nat -> ot:NST.obs_tape ->
        c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
        receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
        (b:Type u#act &
         ret:(b -> a) &
         mid:post st b &
         act:action st b {
           act.pre == pre `st.star` si ot c /\
           act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
           (forall y. mid y == q (ret y)) })) ->
      m a pre q
  | ObservedResultTargetedActWithHiddenStateReturnAction:
      resolve_result:Type0 ->
      resolve_payload:Type0 ->
      pack:erased (resolve_result -> resolve_payload -> nat) ->
      pid:erased nat ->
      payload_value:erased resolve_payload ->
      #a:Type u#a ->
      #pre:st.pred ->
      #q:post st a ->
      si:(NST.obs_tape -> NST.ctr -> st.pred) ->
      step:(observed_nat:nat -> ot:NST.obs_tape ->
        c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
        receipt:observed_result_current_event observed_nat ot c ->
      resolve_event:(x:resolve_result ->
        observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x) ->
        (b:Type u#act &
         ret:(b -> a) &
         mid:post st b &
         act:action st b {
           act.pre == pre `st.star` si ot c /\
           act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
           (forall y. mid y == q (ret y)) })) ->
      m a pre q
  | ObservedResultTargetedActWithHiddenStateAction:
      resolve_result:Type0 ->
      resolve_payload:Type0 ->
      pack:erased (resolve_result -> resolve_payload -> nat) ->
      pid:erased nat ->
      payload_value:erased resolve_payload ->
      #a:Type u#a ->
      #pre:st.pred ->
      #q:post st a ->
      si:(NST.obs_tape -> NST.ctr -> st.pred) ->
      step:(observed_nat:nat -> ot:NST.obs_tape ->
        c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
        receipt:observed_result_current_event observed_nat ot c ->
      resolve_event:(x:resolve_result ->
        observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x) ->
        (b:Type u#act &
         mid:post st b &
         act:action st b {
           act.pre == pre `st.star` si ot c /\
           act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) } &
         (y:b -> Dv (m a (mid y) q)))) ->
      m a pre q
  | Par: // runs m0 concurrently without waiting for it
      #pre0:_ ->
      m0:m (U.raise_t unit) pre0 (as_post #st st.emp) ->
      #a:Type u#a ->
      #pre:_ ->
      #post:post st a ->
      k:m a pre post ->
      m a (pre0 `st.star` pre) post
  | Angel: // angelic (existential) choice — reads from angel oracle;
            // distinct from prophecy observations, which use ObservedAct
      #a:Type u#a ->
      #pre:st.pred ->
      #post:post st a ->
      #c:Type u#act ->
      decode:(nat -> c) ->  // decodes angel oracle nat to choice type
      k:(x:c -> Dv (m a pre post)) ->
      m a pre post
  | FreshProphId: // active NewProph id allocation cursor
      #a:Type u#a ->
      #pre:st.pred ->
      #post:post st a ->
      k:(pid:nat -> Dv (m a pre post)) ->
      m a pre post
  | FreshProphIdWithObsCtr: // cursor plus ghost access to the active tape/counter
      #a:Type u#a ->
      #pre:st.pred ->
      #post:post st a ->
      k:(pid:nat -> ot:NST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} -> Dv (m a pre post)) ->
      m a pre post
  | FreshProphIdWithHiddenState: // cursor interpreted by a hidden obs/counter-indexed state interpretation
      #a:Type u#a ->
      #pre:st.pred ->
      #post:post st a ->
      si:(NST.obs_tape -> NST.ctr -> st.pred) ->
      k:(pid:nat -> ot:NST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
        Dv (m a (pre `st.star` si ot c)
          (F.on_dom a (fun x -> post x `st.star` si ot (NST.bump_prophecy c))))) ->
      m a pre post
  | FreshProphIdWithHiddenStateAction: // one-step active NewProph action under hidden state
      #a:Type u#a ->
      #pre:st.pred ->
      #q:post st a ->
      si:(NST.obs_tape -> NST.ctr -> st.pred) ->
      alloc:(pid:nat -> ot:NST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
        (b:Type u#act &
         mid:post st b &
         act:action st b {
           act.pre == pre `st.star` si ot c /\
           (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) } &
         (x:b -> Dv (m a (mid x) q)))) ->
      m a pre q
  | FreshProphIdWithHiddenStateReturnAction: // active NewProph action with a Ret residual by construction
      #a:Type u#a ->
      #pre:st.pred ->
      #q:post st a ->
      si:(NST.obs_tape -> NST.ctr -> st.pred) ->
      alloc:(pid:nat -> ot:NST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
        (b:Type u#act &
         ret:(b -> a) &
         mid:post st b &
         act:action st b {
           act.pre == pre `st.star` si ot c /\
           (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) /\
           (forall x. mid x == q (ret x)) })) ->
      m a pre q

/// The semantics comes in two levels:
///
///   1. A single-step relation [step] which selects an atomic action to
///      execute in the tree of threads
///
///   2. A top-level driver [run] which repeatedly invokes [step]
///      until it returns with a result and final state.

(**
 * [step_result #st a q frame]:
 *    The result of evaluating a single step of a program
 *    - s, c: The state and its monoid
 *    - a : the result type
 *    - q : the postcondition to be satisfied after fully reducing the programs
 *    - frame: a framed assertion to carry through the proof
 *)
noeq
type step_result (#st:state u#s) (a:Type u#a) (q:post st a) (frame:st.pred) =
  | Step: next:_ -> //precondition of the reduct
          m:m a next q -> //the reduct
          step_result a q frame

#push-options "--z3rlimit 40"
let rec loop #t () : Dv t = loop ()

(**
 * [step f frame]: Reduces a single step of [f], while framing
 * the assertion [frame]
 *)
let rec step 
    (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (f:m a p q)
    (frame:st.pred)
    (fuel: erased pos)
: Tot (pnst_sep st
        (step_result a q frame)
        fuel (fuel - 1)
        (p `st.star` frame)
        (fun x -> Step?.next x `st.star` frame))
      (decreases f)
= match f with
  | Ret x -> 
    weaken <| return <| Step (q x) (Ret x)
  | Act f k ->
    let k (x:_) 
    : Dv (pnst_sep st (step_result a q frame) (fuel-1) (fuel-1)
                    (f.post x `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let n : m a (f.post x) q = k x in
      weaken (return (Step _ n))
    in
    weaken <| bind (PNST.lift <| (NST.lift <| f.step frame)) k
  | ObservedAct decode_obs f k ->
    // Consume one observation from the dedicated observation oracle and run
    // the physical action inside the same semantic step.  This is the generic
    // core shape needed by prophecy Resolve: the observation is not an
    // angelic proof choice, and continuations see both the decoded observation
    // and the actual result of the atomic action.
    let after_action (obs:_) (x:_)
    : Dv (pnst_sep st (step_result a q frame) (fuel-1) (fuel-1)
                    (f.post x `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let n : m a (f.post x) q = k obs x in
      weaken (return (Step _ n))
    in
    let after_observation (n:nat)
    : Dv (pnst_sep st (step_result a q frame) fuel (fuel-1)
                    (p `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let obs = decode_obs n in
      weaken <| bind (PNST.lift <| (NST.lift <| f.step frame)) (after_action obs)
    in
    weaken <| bind (lift <| NST.observe()) after_observation
  | ObservedResultAct decode_obs f k ->
    // Run the physical action and consume one observation from the dedicated
    // observation oracle inside the same semantic step.  Unlike [ObservedAct],
    // the decoder may depend on the physical result.  This is the shape needed
    // by Iris Resolve: the observation emitted by the step can record the
    // actual result, and the continuation can derive agreement from the
    // prophecy state interpretation rather than from a post-hoc ghost write.
    let after_observation (x:_) (n:nat)
    : Dv (pnst_sep st (step_result a q frame) (fuel-1) (fuel-1)
                    (f.post x `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let obs = decode_obs x n in
      let reduct = k x obs in
      weaken <| return <| (Step #st #a #q #frame (f.post x) reduct)
    in
    let after_action (x:_)
    : Dv (pnst_sep st (step_result a q frame) (fuel-1) (fuel-1)
                    (f.post x `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = weaken <| bind (lift <| NST.observe()) (after_observation x)
    in
    weaken <| bind (PNST.lift <| (NST.lift <| f.step frame)) after_action
  | ObservedResultActWithHiddenState decode_obs f si_pre si_post k ->
    // Hidden-state observed-result steps require an adequacy runner that owns
    // and advances the supplied observation/counter-indexed interpretation.
    // The historical runner cannot manufacture that hidden resource from the
    // public precondition, so it remains conservative by diverging.
    PNST.diverge
  | ObservedResultActWithHiddenStateAction si k ->
    // State-action observed-result constructor for the active prophecy runner.
    // The ordinary counter-erased runner still cannot create [si ot c] from the
    // public precondition.  Prophecy adequacy must dispatch through
    // [step_active_observed_result], whose action case consumes
    // [ot (NST.observation_index c)], runs the supplied observed-state action,
    // and closes [si] at [NST.bump_observation c].
    PNST.diverge
  | ObservedResultActWithHiddenStateReturnAction si k ->
    // Ret-specialized state-action observed-result constructor used by the
    // public Resolve lowering.  It is non-diverging only in the active observed
    // runner, which owns [si ot c] and consumes the current observation; the
    // ordinary counter-erased runner remains unable to manufacture [si].
    PNST.diverge
  | ObservedResultTargetedActWithHiddenStateReturnAction _ _ _ _ _ si k ->
    // Target-fixed Ret-specialized public Resolve constructor.  Like the
    // generic hidden-state return action, it is intentionally unreachable by
    // the ordinary counter-erased runner; public adequacy dispatches it through
    // [run_active_observed_result_ret], where the target-fixed receipt is
    // minted by the active observed-result runner after the physical result.
    PNST.diverge
  | ObservedResultTargetedActWithHiddenStateAction _ _ _ _ _ si k ->
    // Continuation-carrying target-fixed public Resolve constructor.  This is
    // produced by [mbind] from the Ret-specialized public Resolve shape, so the
    // Resolve target remains fixed across sequential composition instead of
    // degrading to the generic universally retargetable observed-result event.
    // The ordinary counter-erased runner still cannot manufacture [si ot c];
    // active observed-result dispatch handles this case explicitly.
    PNST.diverge
  | Par #_ #pre0 (Ret x0) #a #pre #post k ->
    weaken <| return <| Step pre k
  | Par #_ #pre0 m0 #a #prek #postk k ->
    let q : post st a = coerce_eq () q in
    let choose (b:bool)
    : pnst_sep st
        (step_result a q frame) fuel (fuel-1)
        (p `st.star` frame)
        (fun x -> (Step?.next x `st.star` frame))
    = if b
      then weaken <| 
           bind (step m0 (prek `st.star` frame) fuel)
                (fun x -> return <| Step _ <| Par (Step?.m x) k)
      else weaken <| 
           bind (step k (pre0 `st.star` frame) fuel)
                (fun x -> return <| Step _ <| Par m0 (Step?.m x))
    in
    weaken <| bind (lift <| NST.flip()) choose 
  | Angel #_ #pre' #post' #c decode k ->
    // Angelic choice: read from angel oracle, decode, continue.
    // This is ordinary existential nondeterminism.  Prophecy observations use
    // the separate observation oracle and [ObservedAct] so Resolve evidence is
    // not confused with proof search/nondeterministic choice.
    let k' (n:nat)
    : Dv (pnst_sep st (step_result a q frame) (fuel-1) (fuel-1)
                    (p `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let choice = decode n in
      let reduct = k choice in
      weaken <| return <| (Step #st #a #q #frame p reduct)
    in
    weaken <| bind (lift <| NST.angel()) k'
  | FreshProphId #_ #pre' #post' k ->
    // NewProph id allocation: consume the active prophecy-id cursor, leaving
    // scheduler/angel/observation cursors unchanged.  Resolve observations are
    // still consumed only by [ObservedAct]/[ObservedResultAct].
    let k' (pid:nat)
    : Dv (pnst_sep st (step_result a q frame) (fuel-1) (fuel-1)
                    (p `st.star` frame)
                    (fun v -> Step?.next v `st.star` frame))
    = let reduct = k pid in
      weaken <| return <| (Step #st #a #q #frame p reduct)
    in
    weaken <| bind (lift <| NST.fresh_prophecy_id()) k'
  | FreshProphIdWithObsCtr #_ #pre' #post' k ->
    // NewProph id allocation with the exact observation tape/counter exposed
    // to the ghost continuation.  This is the dedicated runner seam needed for
    // Iris-style allocation: the continuation receives the same [ot,c] whose
    // prophecy cursor is bumped by this step, so it can project the returned
    // token from the active future suffix instead of fabricating a local []
    // stream.  The tape/counter arguments must remain ghost-only at callers.
    PNST.lift_fresh_prophecy_step
      #st.s #(step_result a q frame)
      #(fun s0 -> st.budget s0 >= fuel /\
        st.interp ((p `st.star` frame) `st.star` st.invariant s0) s0)
      #(fun _ x s1 -> st.budget s1 >= fuel - 1 /\
        st.interp ((Step?.next x `st.star` frame) `st.star` st.invariant s1) s1)
      (fun s0 pid ot c0 ->
        let reduct = k pid ot c0 in
        assert (st.budget s0 >= fuel - 1);
        Step #st #a #q #frame p reduct)
  | FreshProphIdWithHiddenState #_ #pre' #post' si k ->
    // This constructor is for prophecy-aware adequacy runners that carry
    // [si ot c] as a hidden state interpretation.  The historical runner has
    // no such hidden resource, so its partial-correctness interpretation may
    // conservatively diverge rather than manufacture [si] from the public precondition.
    PNST.diverge
  | FreshProphIdWithHiddenStateAction si alloc ->
    // State-action NewProph constructor for the active prophecy runner.  The
    // ordinary counter-erased runner still cannot create [si ot c] from the
    // public precondition.  Prophecy adequacy must dispatch through
    // [step_active], whose [FreshProphIdWithHiddenStateAction] case calls
    // [pnst_sep_obs_ctr_interp_fresh_prophecy_id_action_step] and advances the
    // runner-owned hidden state to [NST.bump_prophecy c].
    PNST.diverge
  | FreshProphIdWithHiddenStateReturnAction si alloc ->
    // Ret-specialized public NewProph constructor.  It is non-diverging only in
    // the active runner [run_active_new_proph_ret], which owns [si ot c]; the
    // ordinary counter-erased runner remains unable to manufacture that hidden
    // active state from the public precondition.
    PNST.diverge
#pop-options

(** The main partial correctness result:
 *    m computations can be interpreted into nmst_sep computations 
 *)    
let rec run (#st:state u#s) 
            (#pre:st.pred)
            (#a:Type u#a) 
            (#post:post st a)
            (f:m a pre post)
            (fuel: nat)
: Dv (pnst_sep st a fuel 0 pre post)
= match f with
  | Ret x -> 
    weaken <| return x
  | _ ->
    if fuel = 0 then loop () else
    let k (s:step_result a post st.emp)
    : Dv (pnst_sep st a (fuel - 1) 0 (Step?.next s) post)
    = let Step _ f = s in
      run f _
    in
    weaken <| bind (step f st.emp fuel) k
    
let tape = nat -> bool
let angel_tape = nat -> nat
let observation_tape = nat -> nat
(** The main partial correctness result:
 *    m computations can be interpreted into nmst_sep computations 
 *)    
let run_alt_with_ctr (#st:state u#s)
            (#pre:st.pred)
            (#a:Type u#a)
            (#post:post st a)
            (f:m a pre post)
            (s0:st.s { st.interp (st.star pre (st.invariant s0)) s0 })
            (t:tape)
            (at:angel_tape)
            (ot:observation_tape)
            (fuel: nat { st.budget s0 >= fuel })
: Dv (res:(a & st.s & NST.ctr) { st.interp (st.star (post res._1) (st.invariant res._2)) res._2 })
= repr (run f fuel) s0 t at ot NST.initial_ctr

(** Adequacy-facing runner that preserves the historical result shape.  Use
    [run_alt_with_ctr] when reasoning about prophecy/observable-step adequacy:
    [NST.observation_index] of the returned counter records only observations
    consumed from [ot], independently of scheduler and angelic oracle
    consumption. *)
let run_alt (#st:state u#s) 
            (#pre:st.pred)
            (#a:Type u#a) 
            (#post:post st a)
            (f:m a pre post)
            (s0:st.s { st.interp (st.star pre (st.invariant s0)) s0 })
            (t:tape)
            (at:angel_tape)
            (ot:observation_tape)
            (fuel: nat { st.budget s0 >= fuel })
: Dv (res:(a & st.s) { st.interp (st.star (post res._1) (st.invariant res._2)) res._2 })
= let (x, s, _) = run_alt_with_ctr f s0 t at ot fuel in
  (x, s)


(** [return]: easy, just use Ret *)
let ret (#st:state) (#a:Type) (x:a) (post:post st a)
  : m a (post x) post
  = Ret x

let raise_action
    (#st:state u#s)
    (#t:Type u#a)
    (a:action st t)
 : action st (U.raise_t u#a u#(max a b) t)
 = {
      pre = a.pre;
      post = F.on_dom _ (fun (x:U.raise_t u#a u#(max a b) t) -> a.post (U.downgrade_val x));
      step = (fun frame ->
               ST.weaken <|
               ST.bind (a.step frame) <|
               (fun x -> ST.return <| U.raise_val u#a u#(max a b) #_ #U.raisable_inst x))
   }

let act
    (#st:state u#s)
    (#t:Type u#act)
    (a:action st t)
: m t a.pre a.post
= Act a Ret

(** One-step observable action wrapper.

    [ObservedAct] is the semantic constructor needed by prophecy Resolve: one
    nat is consumed from the observation tape, decoded by [decode_obs], and the
    physical action [a] is run in the same semantic step.  The continuation
    receives both values; this helper is the common case where the observation
    only justifies the step and the computation returns the physical action's
    result. *)
let observed_act
    (#st:state u#s)
    (#obs:Type u#act)
    (#t:Type u#act)
    (decode_obs:nat -> obs)
    (a:action st t)
: m t a.pre a.post
= ObservedAct decode_obs a (fun _ x -> Ret x)

(** Result-dependent observable action wrapper.

    The physical action is executed first, then one observation is consumed from
    the observation tape and decoded with access to the physical result.  This
    is the core semantic form needed by an Iris-faithful Resolve step: the
    emitted/consumed observation can be [(prophecy id, physical result,
    payload)], and the continuation can use the prophecy state interpretation
    to turn that observed result into the client's predicted-head equality. *)
let observed_result_act
    (#st:state u#s)
    (#t:Type u#act)
    (#obs:(t -> Type u#act))
    (decode_obs:(x:t -> nat -> obs x))
    (a:action st t)
: m t a.pre a.post
= ObservedResultAct decode_obs a (fun x _ -> Ret x)

(** Result-dependent observable action wrapper with an explicit semantic
    continuation.  This names the constructor shape used by the prophecy
    Resolve bridge: the physical action and observation-tape read are one
    semantic step, and the returned reduct is indexed by the physical action's
    postcondition so it can use both [x] and the decoded observation.  The
    continuation is still an ordinary semantic reduct; native open-invariant
    atomic Resolve support requires a separate atomic-action rule that accepts
    this observed-result continuation without coercing it through [as_atomic]. *)
let observed_result_act_cont
    (#st:state u#s)
    (#a:Type u#a)
    (#post:post st a)
    (#t:Type u#act)
    (#obs:(t -> Type u#act))
    (decode_obs:(x:t -> nat -> obs x))
    (act:action st t)
    (k:(x:t -> o:obs x -> Dv (m a (act.post x) post)))
: m a act.pre post
= ObservedResultAct decode_obs act k

(** Result-dependent observable action wrapper whose continuation also receives
    a hidden observation-tape/counter-indexed state interpretation.  The public
    computation keeps the ordinary [act.pre]/[post] shape; prophecy-aware
    adequacy runners are responsible for supplying [si_pre] at the consumed
    observation and closing [si_post] at [NST.bump_observation c].  The
    historical runner cannot supply these resources and therefore treats the
    constructor conservatively by divergence. *)
let observed_result_act_cont_hidden_state
    (#st:state u#s)
    (#a:Type u#a)
    (#post:post st a)
    (#t:Type u#act)
    (#obs:(t -> Type u#act))
    (decode_obs:(x:t -> nat -> obs x))
    (act:action st t)
    (si_pre:(x:t -> o:obs x -> NST.obs_tape -> NST.ctr -> st.pred))
    (si_post:(x:t -> o:obs x -> NST.obs_tape -> NST.ctr -> st.pred))
    (k:(x:t -> observed_nat:nat -> o:obs x { o == decode_obs x observed_nat } ->
      ot:NST.obs_tape -> c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      Dv (m a (act.post x `st.star` si_pre x o ot c)
        (F.on_dom a (fun y -> post y `st.star` si_post x o ot (NST.bump_observation c))))))
: m a act.pre post
= ObservedResultActWithHiddenState decode_obs act si_pre si_post k

let frame_action_for_mbind (#st:state u#s) (#a:Type u#act)
                 (f:action st a) (frame:st.pred)
: g:action st a { g.post == F.on_dom a (fun x -> f.post x `st.star` frame) /\
                  g.pre == f.pre `st.star` frame }
= let step (fr:st.pred)
    : st_sep st a
      ((f.pre `st.star` frame) `st.star` fr)
      (F.on_dom a (fun x -> (f.post x `st.star` frame) `st.star` fr))
    = f.step (frame `st.star` fr)
  in
  { pre = _;
    post = F.on_dom a (fun x -> f.post x `st.star` frame);
    step }

let frame_hidden_fresh_action (#st:state u#s) (#b:Type u#act)
    (#p:st.pred)
    (#mid:post st b)
    (si:NST.obs_tape -> NST.ctr -> st.pred)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (fr:st.pred)
    (act:action st b {
      act.pre == p `st.star` si ot c /\
      (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) })
  : g:action st b {
      g.pre == (p `st.star` fr) `st.star` si ot c /\
      (forall x. g.post x == (mid x `st.star` fr) `st.star` si ot (NST.bump_prophecy c)) }
= let step (fr':st.pred)
    : st_sep st b
      (((p `st.star` fr) `st.star` si ot c) `st.star` fr')
      (F.on_dom b (fun x -> ((mid x `st.star` fr) `st.star` si ot (NST.bump_prophecy c)) `st.star` fr'))
    = star_rotate_right st p (si ot c) fr;
      introduce forall (x:b). st.star (st.star (mid x) (si ot (NST.bump_prophecy c))) fr ==
        st.star (st.star (mid x) fr) (si ot (NST.bump_prophecy c))
      with star_rotate_right st (mid x) (si ot (NST.bump_prophecy c)) fr;
      ST.weaken (act.step (fr `st.star` fr'))
  in
  { pre = (p `st.star` fr) `st.star` si ot c;
    post = F.on_dom b (fun x -> (mid x `st.star` fr) `st.star` si ot (NST.bump_prophecy c));
    step }

let frame_hidden_observed_action (#st:state u#s) (#b:Type u#act)
    (#p:st.pred)
    (#mid:post st b)
    (si:NST.obs_tape -> NST.ctr -> st.pred)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (fr:st.pred)
    (act:action st b {
      act.pre == p `st.star` si ot c /\
      act.post == F.on_dom b (fun x -> mid x `st.star` si ot (NST.bump_observation c)) })
  : g:action st b {
      g.pre == (p `st.star` fr) `st.star` si ot c /\
      g.post == F.on_dom b (fun x -> (mid x `st.star` fr) `st.star` si ot (NST.bump_observation c)) }
= let step (fr':st.pred)
    : st_sep st b
      (((p `st.star` fr) `st.star` si ot c) `st.star` fr')
      (F.on_dom b (fun x -> ((mid x `st.star` fr) `st.star` si ot (NST.bump_observation c)) `st.star` fr'))
    = star_rotate_right st p (si ot c) fr;
      introduce forall (x:b). st.star (st.star (mid x) (si ot (NST.bump_observation c))) fr ==
        st.star (st.star (mid x) fr) (si ot (NST.bump_observation c))
      with star_rotate_right st (mid x) (si ot (NST.bump_observation c)) fr;
      assert (act.post == F.on_dom b (fun x -> mid x `st.star` si ot (NST.bump_observation c)));
      ST.weaken (act.step (fr `st.star` fr'))
  in
  { pre = (p `st.star` fr) `st.star` si ot c;
    post = F.on_dom b (fun x -> (mid x `st.star` fr) `st.star` si ot (NST.bump_observation c));
    step }

let pnst_sep_obs_ctr_interp_fresh_prophecy_id_action_value (st:state u#s)
    (#b:Type u#act)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (pre:st.pred)
    (mid:post st b)
    (frame:st.pred)
    (alloc:(pid:nat -> ot:PNST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
      act:action st b {
        act.pre == pre `st.star` si ot c /\
        (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) }))
  : pnst_sep_obs_ctr_interp st b fuel (fuel - 1) si (pre `st.star` frame)
      (fun x -> mid x `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0)
= pnst_sep_obs_ctr_interp_fresh_prophecy_id_state st #b fuel si (pre `st.star` frame)
    (fun x -> mid x `st.star` frame)
    (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0)
    (fun ot c pid ->
      let act = frame_hidden_fresh_action #st #b #pre #mid si ot c frame (alloc pid ot c) in
      ST.weaken (act.step st.emp))

(** Ret-specialized active NewProph runner step.

    This is the public [fresh_prophecy_id_with_hidden_si_state_action] lowering
    shape: the allocation action returns a value that is immediately returned by
    the semantic computation.  Unlike the older residual-finishing helper, this
    rule cannot fall back to divergence on an unsupported residual, because the
    residual [Ret] is represented in the constructor itself. *)
let pnst_sep_obs_ctr_interp_fresh_prophecy_id_return_action_value (st:state u#s)
    (#a:Type u#a)
    (#pre:st.pred)
    (#q:post st a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (frame:st.pred)
    (alloc:(pid:nat -> ot:PNST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == pre `st.star` si ot c /\
         (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) /\
         (forall x. mid x == q (ret x)) })))
  : pnst_sep_obs_ctr_interp st a fuel (fuel - 1) si (pre `st.star` frame)
      (fun x -> q x `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0)
= pnst_sep_obs_ctr_interp_fresh_prophecy_id_state st #a fuel si (pre `st.star` frame)
    (fun x -> q x `st.star` frame)
    (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0)
    (fun ot c pid ->
      let (| b, ret, mid, act |) = alloc pid ot c in
      let framed = frame_hidden_fresh_action #st #b #pre #mid si ot c frame act in
      ST.weaken (ST.bind (framed.step st.emp) (fun x -> ST.return (ret x))))

noeq
type fresh_action_step_payload (#st:state u#s) (#a:Type u#a) (q:post st a) =
  | FreshActionStepPayload:
      #b:Type u#act ->
      mid:post st b ->
      x:b ->
      k:(x:b -> Dv (m a (mid x) q)) ->
      fresh_action_step_payload #st #a q

(** Active-runner step for [FreshProphIdWithHiddenStateAction].

    The ordinary [step] result type is counter-erased and therefore cannot
    soundly manufacture an arbitrary hidden [si ot c] resource from the public
    precondition.  This adequacy-facing sibling is the non-diverging runner case
    for executions that already own [si] as runner hidden state: it consumes the
    active fresh-prophecy cursor, runs the supplied state action under
    [pre ** frame ** si ot c], builds the next semantic reduct from the action
    result, and closes [si] at [NST.bump_prophecy c]. *)
let pnst_sep_obs_ctr_interp_fresh_prophecy_id_action_step (st:state u#s)
    (#a:Type u#a)
    (#pre:st.pred)
    (#q:post st a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (frame:st.pred)
    (alloc:(pid:nat -> ot:PNST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
      (b:Type u#act &
       mid:post st b &
       act:action st b {
         act.pre == pre `st.star` si ot c /\
         (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) } &
       (x:b -> Dv (m a (mid x) q)))))
  : pnst_sep_obs_ctr_interp st (step_result a q frame) fuel (fuel - 1) si (pre `st.star` frame)
      (fun x -> Step?.next x `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0)
= let payload_next (payload:fresh_action_step_payload #st #a q) : st.pred =
    match payload with
    | FreshActionStepPayload mid x _ -> mid x in
  let base : pnst_sep_obs_ctr_interp st (fresh_action_step_payload #st #a q) fuel (fuel - 1) si (pre `st.star` frame)
      (fun payload -> payload_next payload `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0)
    = pnst_sep_obs_ctr_interp_fresh_prophecy_id_state st #(fresh_action_step_payload #st #a q) fuel si (pre `st.star` frame)
        (fun payload -> payload_next payload `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0)
        (fun ot c pid ->
          let (| b, mid, act, k |) = alloc pid ot c in
          let framed = frame_hidden_fresh_action #st #b #pre #mid si ot c frame act in
          ST.weaken (ST.bind (framed.step st.emp)
            (fun x -> ST.return (FreshActionStepPayload #st #a #q #b mid x k)))) in
  let continue (payload:fresh_action_step_payload #st #a q)
    : Dv (pnst_sep_obs_ctr_interp st (step_result a q frame) (fuel - 1) (fuel - 1) si
        (payload_next payload `st.star` frame)
        (fun step_value -> Step?.next step_value `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == c0))
    = match payload with
      | FreshActionStepPayload #_ mid x k ->
        let reduct : m a (mid x) q = k x in
        let step_value = Step #st #a #q #frame (mid x) reduct in
        assert (Step?.next step_value == payload_next payload);
        PNST.weaken_obs_ctr (PNST.return_obs_ctr step_value)
  in
  let both = PNST.bind_obs_ctr_dv base continue in
  PNST.weaken_obs_ctr_with
    (fun _ _ _ -> ())
    (fun s0 ot c0 step_value s1 c1 ->
      assert (c1 == NST.bump_prophecy c0);
      assert (si ot c1 == si ot (NST.bump_prophecy c0));
      assert (st.interp (((Step?.next step_value `st.star` frame) `st.star` si ot c1)
        `st.star` st.invariant s1) s1))
    both

noeq
type observed_result_action_step_payload (#st:state u#s) (#a:Type u#a) (q:post st a) =
  | ObservedResultActionStepPayload:
      #b:Type u#act ->
      mid:post st b ->
      x:b ->
      k:(x:b -> Dv (m a (mid x) q)) ->
      observed_result_action_step_payload #st #a q

(** Ret-specialized active observed-result value runner.

    This is the Resolve-side analogue of
    [pnst_sep_obs_ctr_interp_fresh_prophecy_id_return_action_value].  The
    public active observed-result lowering produced by [PulseCore.Action] has a
    [Ret] residual by construction, so adequacy can execute the hidden-state
    action directly to the final value instead of first returning a generic
    [step_result] that a later ordinary [run] could send through a conservative
    [PNST.diverge]/[loop] branch. *)
let pnst_sep_obs_ctr_interp_observed_result_return_action_value (st:state u#s)
    (#a:Type u#a)
    (#pre:st.pred)
    (#q:post st a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (frame:st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == pre `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
         (forall y. mid y == q (ret y)) })))
  : pnst_sep_obs_ctr_interp st a fuel (fuel - 1) si (pre `st.star` frame)
      (fun x -> q x `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
= pnst_sep_obs_ctr_interp_observed_result_state st #a fuel si (pre `st.star` frame)
    (fun x -> q x `st.star` frame)
    (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
    (fun ot c ->
      let observed_nat = ot (NST.observation_index c) in
      let receipt : observed_result_current_event observed_nat ot c = ObservedResultCurrentEvent in
      let value_event (#t:Type0) (x:t) : observed_result_value_event #t observed_nat ot c x =
        ObservedResultValueEvent in
      let resolve_event (#result:Type0) (#payload:Type0) (pack:result -> payload -> nat) (pid:nat) (x:result) (payload_value:payload)
          (current_receipt:observed_result_current_event observed_nat ot c)
          (value_receipt:observed_result_value_event #result observed_nat ot c x)
        : observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value =
        ObservedResultResolveEvent current_receipt value_receipt in
      let (| b, ret, mid, act |) = k observed_nat ot c receipt value_event resolve_event in
      let framed = frame_hidden_observed_action #st #b #pre #mid si ot c frame act in
      ST.weaken (ST.bind (framed.step st.emp) (fun x -> ST.return (ret x))))

(** Target-fixed Ret-specialized active observed-result value runner.

    This is the Resolve-specific sibling of
    [pnst_sep_obs_ctr_interp_observed_result_return_action_value].  The
    prophecy id, payload packer, and attached payload are fixed before the
    active runner consumes the observation and before the physical action is
    executed.  The callback receives only a target-fixed Resolve receipt
    capability, minted after the physical result [x] is known from the same
    runner-owned current-cell/value receipts; it is no longer handed the
    generic universally quantified [observed_result_resolve_event] capability
    on this public Resolve active-run path. *)
let pnst_sep_obs_ctr_interp_targeted_observed_result_return_action_value (st:state u#s)
    (#resolve_result #resolve_payload:Type0)
    (#pack:erased (resolve_result -> resolve_payload -> nat))
    (#pid:erased nat)
    (#payload_value:erased resolve_payload)
    (#a:Type u#a)
    (#pre:st.pred)
    (#q:post st a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (frame:st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      resolve_event:(x:resolve_result ->
        observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x) ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == pre `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
         (forall y. mid y == q (ret y)) })))
  : pnst_sep_obs_ctr_interp st a fuel (fuel - 1) si (pre `st.star` frame)
      (fun x -> q x `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
= pnst_sep_obs_ctr_interp_observed_result_state st #a fuel si (pre `st.star` frame)
    (fun x -> q x `st.star` frame)
    (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
    (fun ot c ->
      let observed_nat = ot (NST.observation_index c) in
      let receipt : observed_result_current_event observed_nat ot c = ObservedResultCurrentEvent in
      let resolve_event (x:resolve_result)
        : observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x =
        let value_receipt : observed_result_value_event #resolve_result observed_nat ot c x =
          ObservedResultValueEvent in
        mk_observed_result_targeted_resolve_event #resolve_result #resolve_payload #observed_nat #ot #c
          (reveal pack) (reveal pid) (reveal payload_value) receipt x value_receipt in
      let (| b, ret, mid, act |) = k observed_nat ot c receipt resolve_event in
      let framed = frame_hidden_observed_action #st #b #pre #mid si ot c frame act in
      ST.weaken (ST.bind (framed.step st.emp) (fun x -> ST.return (ret x))))

(** Target-fixed active observed-result action step.

    This is the continuation-carrying sibling of
    [pnst_sep_obs_ctr_interp_targeted_observed_result_return_action_value].  It
    preserves the Resolve target fixed by the public lowering even after
    semantic [mbind] introduces a continuation, rather than falling back to the
    generic [ObservedResultActWithHiddenStateAction] callback with its
    universally retargetable Resolve-event capability. *)
let pnst_sep_obs_ctr_interp_targeted_observed_result_action_step (st:state u#s)
    (#resolve_result #resolve_payload:Type0)
    (#pack:erased (resolve_result -> resolve_payload -> nat))
    (#pid:erased nat)
    (#payload_value:erased resolve_payload)
    (#a:Type u#a)
    (#pre:st.pred)
    (#q:post st a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (frame:st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      resolve_event:(x:resolve_result ->
        observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x) ->
      (b:Type u#act &
       mid:post st b &
       act:action st b {
         act.pre == pre `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) } &
       (y:b -> Dv (m a (mid y) q)))))
  : pnst_sep_obs_ctr_interp st (step_result a q frame) fuel (fuel - 1) si (pre `st.star` frame)
      (fun x -> Step?.next x `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
= let payload_next (payload:observed_result_action_step_payload #st #a q) : st.pred =
    match payload with
    | ObservedResultActionStepPayload mid x _ -> mid x in
  let base : pnst_sep_obs_ctr_interp st (observed_result_action_step_payload #st #a q) fuel (fuel - 1) si (pre `st.star` frame)
      (fun payload -> payload_next payload `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
    = pnst_sep_obs_ctr_interp_observed_result_state st #(observed_result_action_step_payload #st #a q) fuel si (pre `st.star` frame)
        (fun payload -> payload_next payload `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
        (fun ot c ->
          let observed_nat = ot (NST.observation_index c) in
          let receipt : observed_result_current_event observed_nat ot c = ObservedResultCurrentEvent in
          let resolve_event (x:resolve_result)
            : observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x =
            let value_receipt : observed_result_value_event #resolve_result observed_nat ot c x =
              ObservedResultValueEvent in
            mk_observed_result_targeted_resolve_event #resolve_result #resolve_payload #observed_nat #ot #c
              (reveal pack) (reveal pid) (reveal payload_value) receipt x value_receipt in
          let (| b, mid, act, cont |) = k observed_nat ot c receipt resolve_event in
          let framed = frame_hidden_observed_action #st #b #pre #mid si ot c frame act in
          ST.weaken (ST.bind (framed.step st.emp)
            (fun y -> ST.return (ObservedResultActionStepPayload #st #a #q #b mid y cont)))) in
  let continue (payload:observed_result_action_step_payload #st #a q)
    : Dv (pnst_sep_obs_ctr_interp st (step_result a q frame) (fuel - 1) (fuel - 1) si
        (payload_next payload `st.star` frame)
        (fun step_value -> Step?.next step_value `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == c0))
    = match payload with
      | ObservedResultActionStepPayload #_ mid x cont ->
        let reduct : m a (mid x) q = cont x in
        let step_value = Step #st #a #q #frame (mid x) reduct in
        assert (Step?.next step_value == payload_next payload);
        PNST.weaken_obs_ctr (PNST.return_obs_ctr step_value)
  in
  let both = PNST.bind_obs_ctr_dv base continue in
  PNST.weaken_obs_ctr_with
    (fun _ _ _ -> ())
    (fun s0 ot c0 step_value s1 c1 ->
      assert (c1 == NST.bump_observation c0);
      assert (si ot c1 == si ot (NST.bump_observation c0));
      assert (st.interp (((Step?.next step_value `st.star` frame) `st.star` si ot c1)
        `st.star` st.invariant s1) s1))
    both

(** Active-runner step for [ObservedResultActWithHiddenStateAction].

    This is the observation-side counterpart of
    [pnst_sep_obs_ctr_interp_fresh_prophecy_id_action_step].  It consumes
    exactly [ot (NST.observation_index c)] through
    [pnst_sep_obs_ctr_interp_observed_result_state], runs the supplied
    observed-state action under the runner-owned [si ot c], and returns the
    residual semantic computation while closing [si] at
    [NST.bump_observation c].  The ordinary [step] branch remains conservative;
    active prophecy adequacy code must dispatch through
    [step_active_observed_result]. *)
let pnst_sep_obs_ctr_interp_observed_result_action_step (st:state u#s)
    (#a:Type u#a)
    (#pre:st.pred)
    (#q:post st a)
    (fuel:pos)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (frame:st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#act &
       mid:post st b &
       act:action st b {
         act.pre == pre `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) } &
       (y:b -> Dv (m a (mid y) q)))))
  : pnst_sep_obs_ctr_interp st (step_result a q frame) fuel (fuel - 1) si (pre `st.star` frame)
      (fun x -> Step?.next x `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
= let payload_next (payload:observed_result_action_step_payload #st #a q) : st.pred =
    match payload with
    | ObservedResultActionStepPayload mid x _ -> mid x in
  let base : pnst_sep_obs_ctr_interp st (observed_result_action_step_payload #st #a q) fuel (fuel - 1) si (pre `st.star` frame)
      (fun payload -> payload_next payload `st.star` frame)
      (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
    = pnst_sep_obs_ctr_interp_observed_result_state st #(observed_result_action_step_payload #st #a q) fuel si (pre `st.star` frame)
        (fun payload -> payload_next payload `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0)
        (fun ot c ->
          let observed_nat = ot (NST.observation_index c) in
          let receipt : observed_result_current_event observed_nat ot c = ObservedResultCurrentEvent in
          let value_event (#t:Type0) (x:t) : observed_result_value_event #t observed_nat ot c x =
            ObservedResultValueEvent in
          let resolve_event (#result:Type0) (#payload:Type0) (pack:result -> payload -> nat) (pid:nat) (x:result) (payload_value:payload)
              (current_receipt:observed_result_current_event observed_nat ot c)
              (value_receipt:observed_result_value_event #result observed_nat ot c x)
            : observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value =
            ObservedResultResolveEvent current_receipt value_receipt in
          let (| b, mid, act, cont |) = k observed_nat ot c receipt value_event resolve_event in
          let framed = frame_hidden_observed_action #st #b #pre #mid si ot c frame act in
          ST.weaken (ST.bind (framed.step st.emp)
            (fun y -> ST.return (ObservedResultActionStepPayload #st #a #q #b mid y cont)))) in
  let continue (payload:observed_result_action_step_payload #st #a q)
    : Dv (pnst_sep_obs_ctr_interp st (step_result a q frame) (fuel - 1) (fuel - 1) si
        (payload_next payload `st.star` frame)
        (fun step_value -> Step?.next step_value `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == c0))
    = match payload with
      | ObservedResultActionStepPayload #_ mid x cont ->
        let reduct : m a (mid x) q = cont x in
        let step_value = Step #st #a #q #frame (mid x) reduct in
        assert (Step?.next step_value == payload_next payload);
        PNST.weaken_obs_ctr (PNST.return_obs_ctr step_value)
  in
  let both = PNST.bind_obs_ctr_dv base continue in
  PNST.weaken_obs_ctr_with
    (fun _ _ _ -> ())
    (fun s0 ot c0 step_value s1 c1 ->
      assert (c1 == NST.bump_observation c0);
      assert (si ot c1 == si ot (NST.bump_observation c0));
      assert (st.interp (((Step?.next step_value `st.star` frame) `st.star` si ot c1)
        `st.star` st.invariant s1) s1))
    both

(** Official active-step dispatcher for the dedicated NewProph hidden-state
    constructor.

    The historical [step] relation is intentionally counter-erased: it cannot
    soundly obtain [si ot c] from a public [pre] and therefore keeps the legacy
    [FreshProphIdWithHiddenStateAction] branch conservative.  Prophecy
    adequacy, however, owns the runner state interpretation explicitly.  This
    result packages exactly the [si]-indexed observation/counter step that such
    an active runner must use, so callers dispatching through [step_active]
    reach [pnst_sep_obs_ctr_interp_fresh_prophecy_id_action_step] rather than
    the legacy [PNST.diverge] branch. *)
noeq
type active_step_result (#st:state u#s)
    (a:Type u#a)
    (q:post st a)
    (frame:st.pred)
    (fuel:pos)
    (pre:st.pred)
  = | ActiveStepResult:
      si:(PNST.obs_tape -> NST.ctr -> st.pred) ->
      run_step:pnst_sep_obs_ctr_interp st (step_result a q frame) fuel (fuel - 1) si
        (pre `st.star` frame)
        (fun x -> Step?.next x `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0) ->
      active_step_result #st a q frame fuel pre

let step_active (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (f:m a p q)
    (frame:st.pred)
    (fuel:pos)
  : Tot (option (active_step_result #st a q frame fuel p))
= match f with
  | FreshProphIdWithHiddenStateAction si alloc ->
    Some (ActiveStepResult si
      (pnst_sep_obs_ctr_interp_fresh_prophecy_id_action_step st #a #p #q fuel si frame alloc))
  | _ -> None

(** Active-step result for observed-result hidden-state actions.  It is kept
    separate from [active_step_result] because this runner advances the
    observation cursor rather than the prophecy-id cursor. *)
noeq
type active_observed_step_result (#st:state u#s)
    (a:Type u#a)
    (q:post st a)
    (frame:st.pred)
    (fuel:pos)
    (pre:st.pred)
  = | ActiveObservedStepResult:
      si:(PNST.obs_tape -> NST.ctr -> st.pred) ->
      run_step:pnst_sep_obs_ctr_interp st (step_result a q frame) fuel (fuel - 1) si
        (pre `st.star` frame)
        (fun x -> Step?.next x `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0) ->
      active_observed_step_result #st a q frame fuel pre

(** Direct active-dispatch certificate for the hidden-state observed-result
    action constructor used by public Resolve.  This packages the exact
    non-diverging runner branch without going through the ordinary [step]
    interpreter, whose hidden-state action cases intentionally remain
    [PNST.diverge]. *)
let observed_result_hidden_state_action_active_step_result (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#act &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) } &
       (y:b -> Dv (m a (mid y) q)))))
    (frame:st.pred)
    (fuel:pos)
  : active_observed_step_result #st a q frame fuel p
= ActiveObservedStepResult si
    (pnst_sep_obs_ctr_interp_observed_result_action_step st #a #p #q fuel si frame k)

let step_active_observed_result (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (f:m a p q)
    (frame:st.pred)
    (fuel:pos)
  : Tot (option (active_observed_step_result #st a q frame fuel p))
= match f with
  | ObservedResultActWithHiddenStateAction si k ->
    Some (observed_result_hidden_state_action_active_step_result #st #p #a #q si k frame fuel)
  | ObservedResultTargetedActWithHiddenStateAction resolve_result resolve_payload pack pid payload_value si k ->
    Some (ActiveObservedStepResult si
      (pnst_sep_obs_ctr_interp_targeted_observed_result_action_step st
        #resolve_result #resolve_payload #pack #pid #payload_value #a #p #q fuel si frame k))
  | _ -> None

(** Concrete active observed-result execution with an explicit observation
    tape/counter.  This is the adequacy-facing runner counterpart to
    [run_alt_active_new_proph_return_action_with_ctr]: callers start with
    runner-owned [si ot c0], the runner consumes exactly the current
    observation, executes the supplied hidden-state action, and returns the next
    semantic reduct with the counter advanced to [NST.bump_observation c0]. *)
let run_alt_active_observed_result_action_with_ctr (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#act &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) } &
       (y:b -> Dv (m a (mid y) q)))))
    (frame:st.pred)
    (t:tape)
    (at:angel_tape)
    (ot:observation_tape)
    (c0:NST.ctr)
    (fuel:pos)
    (s0:st.s { st.budget s0 >= fuel /\
      st.interp (((p `st.star` frame) `st.star` si ot c0) `st.star` st.invariant s0) s0 })
  : Dv (res:(step_result a q frame & st.s & NST.ctr) {
      st.budget res._2 >= fuel - 1 /\
      st.interp (((Step?.next res._1 `st.star` frame) `st.star` si ot res._3) `st.star` st.invariant res._2) res._2 /\
      res._3 == NST.bump_observation c0 })
= let run_step = pnst_sep_obs_ctr_interp_observed_result_action_step st #a #p #q fuel si frame k in
  PNST.repr_obs_ctr run_step s0 t at ot c0

(** Resolve-only active runner used by adequacy proofs for the public
    [ObservedResultActWithHiddenStateReturnAction] lowering.

    This mirrors [active_run_result] for NewProph but advances the observation
    cursor.  Public Resolve lowerings that construct the Ret-specialized
    observed-result action can be executed directly by this runner, so the
    proof path need not hand the residual to ordinary [run], whose
    hidden-state branches intentionally remain conservative. *)
noeq
type active_observed_run_result (#st:state u#s)
    (a:Type u#a)
    (q:post st a)
    (frame:st.pred)
    (fuel:pos)
    (pre:st.pred)
  = | ActiveObservedRunResult:
      si:(PNST.obs_tape -> NST.ctr -> st.pred) ->
      run_value:pnst_sep_obs_ctr_interp st a fuel (fuel - 1) si
        (pre `st.star` frame)
        (fun x -> q x `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == NST.bump_observation c0) ->
      active_observed_run_result #st a q frame fuel pre

let run_active_observed_result_return_action (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
         (forall y. mid y == q (ret y)) })))
    (frame:st.pred)
    (fuel:pos)
  : active_observed_run_result #st a q frame fuel p
= ActiveObservedRunResult si
    (pnst_sep_obs_ctr_interp_observed_result_return_action_value st #a #p #q fuel si frame k)

let run_active_targeted_observed_result_return_action (#st:state u#s)
    (#resolve_result #resolve_payload:Type0)
    (#pack:erased (resolve_result -> resolve_payload -> nat))
    (#pid:erased nat)
    (#payload_value:erased resolve_payload)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      resolve_event:(x:resolve_result ->
        observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x) ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
         (forall y. mid y == q (ret y)) })))
    (frame:st.pred)
    (fuel:pos)
  : active_observed_run_result #st a q frame fuel p
= ActiveObservedRunResult si
    (pnst_sep_obs_ctr_interp_targeted_observed_result_return_action_value st
      #resolve_result #resolve_payload #pack #pid #payload_value #a #p #q fuel si frame k)


let run_active_observed_result_ret (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (f:m u#s u#a u#act a p q)
    (frame:st.pred)
    (fuel:pos)
  : Tot (option (active_observed_run_result #st a q frame fuel p))
= match f with
  | ObservedResultActWithHiddenStateReturnAction si k ->
    Some (run_active_observed_result_return_action #st #p #a #q si k frame fuel)
  | ObservedResultTargetedActWithHiddenStateReturnAction resolve_result resolve_payload pack pid payload_value si k ->
    Some (run_active_targeted_observed_result_return_action #st
      #resolve_result #resolve_payload #pack #pid #payload_value #p #a #q si k frame fuel)
  | _ -> None

let run_alt_active_observed_result_return_action_with_ctr (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      value_event:(#t:Type0 -> x:t -> observed_result_value_event #t observed_nat ot c x) ->
      resolve_event:(#result:Type0 -> #payload:Type0 -> pack:(result -> payload -> nat) -> pid:nat -> x:result -> payload_value:payload ->
        current_receipt:observed_result_current_event observed_nat ot c ->
        value_receipt:observed_result_value_event #result observed_nat ot c x ->
        observed_result_resolve_event #result #payload observed_nat ot c pack pid x payload_value) ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
         (forall y. mid y == q (ret y)) })))
    (frame:st.pred)
    (t:tape)
    (at:angel_tape)
    (ot:observation_tape)
    (c0:NST.ctr)
    (fuel:pos)
    (s0:st.s { st.budget s0 >= fuel /\
      st.interp (((p `st.star` frame) `st.star` si ot c0) `st.star` st.invariant s0) s0 })
  : Dv (res:(a & st.s & NST.ctr) {
      st.budget res._2 >= fuel - 1 /\
      st.interp (((q res._1 `st.star` frame) `st.star` si ot res._3) `st.star` st.invariant res._2) res._2 /\
      res._3 == NST.bump_observation c0 })
= let run_value = pnst_sep_obs_ctr_interp_observed_result_return_action_value st #a #p #q fuel si frame k in
  PNST.repr_obs_ctr run_value s0 t at ot c0

let run_alt_active_targeted_observed_result_return_action_with_ctr (#st:state u#s)
    (#resolve_result #resolve_payload:Type0)
    (#pack:erased (resolve_result -> resolve_payload -> nat))
    (#pid:erased nat)
    (#payload_value:erased resolve_payload)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (k:(observed_nat:nat -> ot:PNST.obs_tape ->
      c:NST.ctr{observed_nat == ot (NST.observation_index c)} ->
      receipt:observed_result_current_event observed_nat ot c ->
      resolve_event:(x:resolve_result ->
        observed_result_targeted_resolve_event #resolve_result #resolve_payload observed_nat ot c (reveal pack) (reveal pid) (reveal payload_value) x) ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         act.post == F.on_dom b (fun y -> mid y `st.star` si ot (NST.bump_observation c)) /\
         (forall y. mid y == q (ret y)) })))
    (frame:st.pred)
    (t:tape)
    (at:angel_tape)
    (ot:observation_tape)
    (c0:NST.ctr)
    (fuel:pos)
    (s0:st.s { st.budget s0 >= fuel /\
      st.interp (((p `st.star` frame) `st.star` si ot c0) `st.star` st.invariant s0) s0 })
  : Dv (res:(a & st.s & NST.ctr) {
      st.budget res._2 >= fuel - 1 /\
      st.interp (((q res._1 `st.star` frame) `st.star` si ot res._3) `st.star` st.invariant res._2) res._2 /\
      res._3 == NST.bump_observation c0 })
= let run_value = pnst_sep_obs_ctr_interp_targeted_observed_result_return_action_value st
    #resolve_result #resolve_payload #pack #pid #payload_value #a #p #q fuel si frame k in
  PNST.repr_obs_ctr run_value s0 t at ot c0

(** NewProph-only active runner used by adequacy proofs for the public
    [fresh_prophecy_id_with_hidden_si_state_action] shape.

    The public NewProph primitive generated by
    [PulseCore.Action.fresh_prophecy_id_hidden_state_action_semantic] now lowers
    to [FreshProphIdWithHiddenStateReturnAction], whose residual is [Ret] by
    construction.  This runner therefore executes the authoritative hidden-state
    allocation and returns the value directly; there is no fallback branch that
    can turn an unsupported residual into divergence on the public NewProph
    path.  More general post-NewProph continuations still use [step_active] and
    require a future multi-step active runner. *)
noeq
type active_run_result (#st:state u#s)
    (a:Type u#a)
    (q:post st a)
    (frame:st.pred)
    (fuel:pos)
    (pre:st.pred)
  = | ActiveRunResult:
      si:(PNST.obs_tape -> NST.ctr -> st.pred) ->
      run_value:pnst_sep_obs_ctr_interp st a fuel (fuel - 1) si
        (pre `st.star` frame)
        (fun x -> q x `st.star` frame)
        (fun _ _ c0 _ _ c1 -> c1 == NST.bump_prophecy c0) ->
      active_run_result #st a q frame fuel pre

let run_active_new_proph_return_action (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (alloc:(pid:nat -> ot:PNST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) /\
         (forall x. mid x == q (ret x)) })))
    (frame:st.pred)
    (fuel:pos)
  : active_run_result #st a q frame fuel p
= ActiveRunResult si
    (pnst_sep_obs_ctr_interp_fresh_prophecy_id_return_action_value st fuel si frame alloc)

let run_active_new_proph_ret (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (f:m u#s u#a u#act a p q)
    (frame:st.pred)
    (fuel:pos)
  : Tot (option (active_run_result #st a q frame fuel p))
= match f with
  | FreshProphIdWithHiddenStateReturnAction si alloc ->
    Some (run_active_new_proph_return_action #st #p #a #q si alloc frame fuel)
  | _ -> None

(** Execute the Ret-specialized active NewProph constructor all the way to the
    [PNST] result shape used by adequacy tests.  This is the concrete public
    path for the primitive lowering: callers pass the constructor payload,
    start with runner-owned [si ot c0], and the returned counter is exactly
    [NST.bump_prophecy c0]. *)
let run_alt_active_new_proph_return_action_with_ctr (#st:state u#s)
    (#p:st.pred)
    (#a:Type u#a)
    (#q:post st a)
    (si:PNST.obs_tape -> NST.ctr -> st.pred)
    (alloc:(pid:nat -> ot:PNST.obs_tape -> c:NST.ctr{pid == NST.prophecy_index c} ->
      (b:Type u#act &
       ret:(b -> a) &
       mid:post st b &
       act:action st b {
         act.pre == p `st.star` si ot c /\
         (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) /\
         (forall x. mid x == q (ret x)) })))
    (frame:st.pred)
    (t:tape)
    (at:angel_tape)
    (ot:observation_tape)
    (c0:NST.ctr)
    (fuel:pos)
    (s0:st.s { st.budget s0 >= fuel /\
      st.interp (((p `st.star` frame) `st.star` si ot c0) `st.star` st.invariant s0) s0 })
  : Dv (res:(a & st.s & NST.ctr) {
      st.budget res._2 >= fuel - 1 /\
      st.interp (((q res._1 `st.star` frame) `st.star` si ot res._3) `st.star` st.invariant res._2) res._2 /\
      res._3 == NST.bump_prophecy c0 })
= let run_value = pnst_sep_obs_ctr_interp_fresh_prophecy_id_return_action_value st fuel si frame alloc in
  PNST.repr_obs_ctr run_value s0 t at ot c0

let hom_hidden_fresh_action (#st:state u#s) (#b:Type u#act)
    (#p:st.pred)
    (#mid:post st b)
    (si:NST.obs_tape -> NST.ctr -> st.pred)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (hom: st.pred -> st.pred
      { hom st.emp == st.emp /\ (forall x y. hom (x `st.star` y) == hom x `st.star` hom y) })
    (hom_act: (#b:Type u#act -> act:action st b -> act':action st b
      { act'.pre == hom act.pre /\ (forall x. act'.post x == hom (act.post x)) }))
    (act:action st b {
      act.pre == p `st.star` si ot c /\
      (forall x. act.post x == mid x `st.star` si ot (NST.bump_prophecy c)) })
  : g:action st b {
      g.pre == hom p `st.star` hom (si ot c) /\
      (forall x. g.post x == hom (mid x) `st.star` hom (si ot (NST.bump_prophecy c))) }
= let act' = hom_act act in
  let step (fr:st.pred)
    : st_sep st b
      ((hom p `st.star` hom (si ot c)) `st.star` fr)
      (F.on_dom b (fun x -> (hom (mid x) `st.star` hom (si ot (NST.bump_prophecy c))) `st.star` fr))
    = assert (act'.pre == hom (p `st.star` si ot c));
      assert (hom (p `st.star` si ot c) == hom p `st.star` hom (si ot c));
      assert (forall x. act'.post x == hom (mid x `st.star` si ot (NST.bump_prophecy c)));
      assert (forall x. hom (mid x `st.star` si ot (NST.bump_prophecy c)) ==
        hom (mid x) `st.star` hom (si ot (NST.bump_prophecy c)));
      ST.weaken (act'.step fr)
  in
  { pre = hom p `st.star` hom (si ot c);
    post = F.on_dom b (fun x -> hom (mid x) `st.star` hom (si ot (NST.bump_prophecy c)));
    step }

let hom_hidden_observed_action (#st:state u#s) (#b:Type u#act)
    (#p:st.pred)
    (#mid:post st b)
    (si:NST.obs_tape -> NST.ctr -> st.pred)
    (ot:NST.obs_tape)
    (c:NST.ctr)
    (hom: st.pred -> st.pred
      { hom st.emp == st.emp /\ (forall x y. hom (x `st.star` y) == hom x `st.star` hom y) })
    (hom_act: (#b:Type u#act -> act:action st b -> act':action st b
      { act'.pre == hom act.pre /\ (forall x. act'.post x == hom (act.post x)) }))
    (act:action st b {
      act.pre == p `st.star` si ot c /\
      act.post == F.on_dom b (fun x -> mid x `st.star` si ot (NST.bump_observation c)) })
  : g:action st b {
      g.pre == hom p `st.star` hom (si ot c) /\
      g.post == F.on_dom b (fun x -> hom (mid x) `st.star` hom (si ot (NST.bump_observation c))) }
= let act' = hom_act act in
  let step (fr:st.pred)
    : st_sep st b
      ((hom p `st.star` hom (si ot c)) `st.star` fr)
      (F.on_dom b (fun x -> (hom (mid x) `st.star` hom (si ot (NST.bump_observation c))) `st.star` fr))
    = assert (act'.pre == hom (p `st.star` si ot c));
      assert (hom (p `st.star` si ot c) == hom p `st.star` hom (si ot c));
      assert (act.post == F.on_dom b (fun x -> mid x `st.star` si ot (NST.bump_observation c)));
      assert (forall x. act'.post x == hom (act.post x));
      assert (forall x. act'.post x == hom (mid x `st.star` si ot (NST.bump_observation c)));
      assert (forall x. hom (mid x `st.star` si ot (NST.bump_observation c)) ==
        hom (mid x) `st.star` hom (si ot (NST.bump_observation c)));
      ST.weaken (act'.step fr)
  in
  { pre = hom p `st.star` hom (si ot c);
    post = F.on_dom b (fun x -> hom (mid x) `st.star` hom (si ot (NST.bump_observation c)));
    step }

let rec frame_for_mbind (#st:state u#s)
              (#a:Type u#a)
              (#p:st.pred)
              (#q:post st a)
              (fr:st.pred)
              (f:m a p q)
   : Dv (m u#s u#a u#act a (p `st.star` fr) (F.on_dom a (fun x -> q x `st.star` fr)))
   = match f with
     | Ret x -> Ret x
     | Act f k ->
       Act (frame_action_for_mbind f fr) (fun x -> frame_for_mbind fr (k x))
     | ObservedAct decode_obs f k ->
       ObservedAct decode_obs (frame_action_for_mbind f fr) (fun obs x -> frame_for_mbind fr (k obs x))
     | ObservedResultAct decode_obs f k ->
       ObservedResultAct decode_obs (frame_action_for_mbind f fr) (fun x obs -> frame_for_mbind fr (k x obs))
     | ObservedResultActWithHiddenState decode_obs f si_pre si_post k ->
       ObservedResultActWithHiddenState decode_obs (frame_action_for_mbind f fr) si_pre si_post
         (fun x observed_nat obs ot c ->
           let framed = frame_for_mbind fr (k x observed_nat obs ot c) in
           star_rotate_right st (f.post x) (si_pre x obs ot c) fr;
           assert (forall y. st.star (st.star (q y) (si_post x obs ot (NST.bump_observation c))) fr ==
             st.star (st.star (q y) fr) (si_post x obs ot (NST.bump_observation c)));
           assert (F.feq
             (fun y -> st.star (st.star (q y) (si_post x obs ot (NST.bump_observation c))) fr)
             (fun y -> st.star (st.star (q y) fr) (si_post x obs ot (NST.bump_observation c))));
           F.extensionality a (fun _ -> st.pred)
             (fun y -> st.star (st.star (q y) (si_post x obs ot (NST.bump_observation c))) fr)
             (fun y -> st.star (st.star (q y) fr) (si_post x obs ot (NST.bump_observation c)));
           coerce_eq () framed)
     | ObservedResultActWithHiddenStateAction si k ->
       ObservedResultActWithHiddenStateAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt value_event resolve_event ->
           let (| b, mid, act, kont |) = k observed_nat ot c receipt value_event resolve_event in
           (| b,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act,
              (fun y -> frame_for_mbind fr (kont y)) |))
     | ObservedResultActWithHiddenStateReturnAction si k ->
       ObservedResultActWithHiddenStateReturnAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt value_event resolve_event ->
           let (| b, ret, mid, act |) = k observed_nat ot c receipt value_event resolve_event in
           (| b,
              ret,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act |))
     | ObservedResultTargetedActWithHiddenStateReturnAction resolve_result resolve_payload pack pid payload_value si k ->
       ObservedResultTargetedActWithHiddenStateReturnAction
         #st resolve_result resolve_payload pack pid payload_value
         #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt resolve_event ->
           let (| b, ret, mid, act |) = k observed_nat ot c receipt resolve_event in
           (| b,
              ret,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act |))
     | ObservedResultTargetedActWithHiddenStateAction resolve_result resolve_payload pack pid payload_value si k ->
       ObservedResultTargetedActWithHiddenStateAction
         #st resolve_result resolve_payload pack pid payload_value
         #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt resolve_event ->
           let (| b, mid, act, kont |) = k observed_nat ot c receipt resolve_event in
           (| b,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act,
              (fun y -> frame_for_mbind fr (kont y)) |))

     | Par #_ #pre0 m0 #_ #prek #postk k ->
       let k' = frame_for_mbind fr k in
       Par m0 k'
     | Angel #_ #pre #post #c decode k ->
       Angel decode (fun x -> frame_for_mbind fr (k x))
     | FreshProphId #_ #pre #post k ->
       FreshProphId (fun pid -> frame_for_mbind fr (k pid))
     | FreshProphIdWithObsCtr #_ #pre #post k ->
       FreshProphIdWithObsCtr (fun pid ot c -> frame_for_mbind fr (k pid ot c))
     | FreshProphIdWithHiddenState #_ #_ #_ si k ->
       FreshProphIdWithHiddenState
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun pid ot c ->
           let framed = frame_for_mbind fr (k pid ot c) in
           star_rotate_right st p (si ot c) fr;
           assert (forall x. st.star (st.star (q x) (si ot (NST.bump_prophecy c))) fr ==
             st.star (st.star (q x) fr) (si ot (NST.bump_prophecy c)));
           assert (F.feq
             (fun x -> st.star (st.star (q x) (si ot (NST.bump_prophecy c))) fr)
             (fun x -> st.star (st.star (q x) fr) (si ot (NST.bump_prophecy c))));
           F.extensionality a (fun _ -> st.pred)
             (fun x -> st.star (st.star (q x) (si ot (NST.bump_prophecy c))) fr)
             (fun x -> st.star (st.star (q x) fr) (si ot (NST.bump_prophecy c)));
           coerce_eq () framed)
     | FreshProphIdWithHiddenStateAction si alloc ->
       FreshProphIdWithHiddenStateAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun pid ot c ->
           let (| b, mid, act, k |) = alloc pid ot c in
           (| b,
              F.on_dom b (fun x -> mid x `st.star` fr),
              frame_hidden_fresh_action #st #b #p #mid si ot c fr act,
              (fun x -> frame_for_mbind fr (k x)) |))
     | FreshProphIdWithHiddenStateReturnAction si alloc ->
       FreshProphIdWithHiddenStateReturnAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun pid ot c ->
           let (| b, ret, mid, act |) = alloc pid ot c in
           (| b,
              ret,
              F.on_dom b (fun x -> mid x `st.star` fr),
              frame_hidden_fresh_action #st #b #p #mid si ot c fr act |))

(**
 * [bind]: sequential composition works by pushing `g` into the continuation
 * at each node, finally applying it at the terminal `Ret`
 *)
let rec mbind
     (#st:state u#s)
     (#a:Type u#a)
     (#b:Type u#b)
     (#p:st.pred)
     (#q:post st a)
     (#r:post st b)
     (f:m a p q)
     (g: (x:a -> Dv (m b (q x) r)))
  : Dv (m u#s u#b u#act b p r)
  = match f with
    | Ret x -> g x
    | Act act k ->
      Act act (fun x -> mbind (k x) g)
    | ObservedAct decode_obs act k ->
      ObservedAct decode_obs act (fun obs x -> mbind (k obs x) g)
    | ObservedResultAct decode_obs act k ->
      ObservedResultAct decode_obs act (fun x obs -> mbind (k x obs) g)
    | ObservedResultActWithHiddenState decode_obs act si_pre si_post k ->
      ObservedResultActWithHiddenState decode_obs act si_pre si_post
        (fun x observed_nat obs ot c ->
          mbind (k x observed_nat obs ot c)
            (fun y -> frame_for_mbind (si_post x obs ot (NST.bump_observation c)) (g y)))
    | ObservedResultActWithHiddenStateAction si k ->
      ObservedResultActWithHiddenStateAction #st #b #p #r si
        (fun observed_nat ot c receipt value_event resolve_event ->
          let (| b', mid, act', kont |) = k observed_nat ot c receipt value_event resolve_event in
          (| b', mid, act', (fun y -> mbind (kont y) g) |))
    | ObservedResultActWithHiddenStateReturnAction si k ->
      ObservedResultActWithHiddenStateAction #st #b #p #r si
        (fun observed_nat ot c receipt value_event resolve_event ->
          let (| b', ret, mid, act' |) = k observed_nat ot c receipt value_event resolve_event in
          (| b', mid, act', (fun y -> g (ret y)) |))
    | ObservedResultTargetedActWithHiddenStateReturnAction resolve_result resolve_payload pack pid payload_value si k ->
      ObservedResultTargetedActWithHiddenStateAction #st resolve_result resolve_payload pack pid payload_value #b #p #r si
        (fun observed_nat ot c receipt targeted_resolve_event ->
          let (| b', ret, mid, act' |) = k observed_nat ot c receipt targeted_resolve_event in
          (| b', mid, act', (fun y -> g (ret y)) |))
    | ObservedResultTargetedActWithHiddenStateAction resolve_result resolve_payload pack pid payload_value si k ->
      ObservedResultTargetedActWithHiddenStateAction #st resolve_result resolve_payload pack pid payload_value #b #p #r si
        (fun observed_nat ot c receipt targeted_resolve_event ->
          let (| b', mid, act', kont |) = k observed_nat ot c receipt targeted_resolve_event in
          (| b', mid, act', (fun y -> mbind (kont y) g) |))

    | Par #_ #pre0 ml #_ #prek #postk k ->
      let k : m b prek r = mbind k g in
      let ml' : m (U.raise_t u#0 u#b unit) pre0 (as_post st.emp) =
         mbind ml (fun _ -> Ret #_ #(U.raise_t u#0 u#b unit) #(as_post st.emp) (U.raise_val u#0 u#b ()))
      in
      Par ml' k
    | Angel #_ #pre #_ #c decode k ->
      Angel decode (fun x -> mbind (k x) g)
    | FreshProphId #_ #pre #_ k ->
      FreshProphId (fun pid -> mbind (k pid) g)
    | FreshProphIdWithObsCtr #_ #pre #_ k ->
      FreshProphIdWithObsCtr (fun pid ot c -> mbind (k pid ot c) g)
    | FreshProphIdWithHiddenState #_ #pre' #post' si k ->
      FreshProphIdWithHiddenState si
        (fun pid ot c ->
          mbind (k pid ot c)
            (fun x -> frame_for_mbind (si ot (NST.bump_prophecy c)) (g x)))
    | FreshProphIdWithHiddenStateAction si alloc ->
      FreshProphIdWithHiddenStateAction #st #b #p #r si
        (fun pid ot c ->
          let (| b', mid, act, k |) = alloc pid ot c in
          (| b', mid, act, (fun x -> mbind (k x) g) |))
    | FreshProphIdWithHiddenStateReturnAction si alloc ->
      FreshProphIdWithHiddenStateAction #st #b #p #r si
        (fun pid ot c ->
          let (| b', ret, mid, act |) = alloc pid ot c in
          (| b', mid, act, (fun x -> g (ret x)) |))

let act_as_m0
    (#st:state u#s)
    (#t:Type u#0)
    (a:action st t)
: Dv (m t a.pre a.post)
= let k (x:U.raise_t u#0 u#act t)
    : Dv (m t (a.post (U.downgrade_val x)) a.post) 
    = Ret (U.downgrade_val x)
  in
  mbind (act (raise_action a)) k

noeq
type liftable : Type u#(1 + (max a b)) = {
  downgrade_val : (t:Type u#a -> U.raise_t u#a u#(max a b) t -> t);
  laws : squash (forall (t:Type u#a) (x:t). downgrade_val t (U.raise_val x) == x)
}

let act_as_m_poly
    (#st:state u#s)
    (#t:Type u#a)
    (l:liftable u#a u#b)
    (a:action st t)
: Dv (m u#s u#a u#(max a b) t a.pre a.post)
= let k (x:U.raise_t u#a u#(max a b) t)
    : Dv (m t (a.post (l.downgrade_val _ x)) a.post) 
    = Ret (l.downgrade_val _ x)
  in
  mbind (act (raise_action a)) k

(* Next, a main property of this semantics is that it supports the
   frame rule. Here's a proof of it *)

/// First, we prove that individual actions can be framed
///
/// --- That's not so hard, since we specifically required actions to
///     be frameable
let frame_action (#st:state u#s) (#a:Type u#act) 
                 (f:action st a) (frame:st.pred)
: g:action st a { g.post == F.on_dom a (fun x -> f.post x `st.star` frame) /\
                  g.pre == f.pre `st.star` frame }
= let step (fr:st.pred) 
    : st_sep st a 
      ((f.pre `st.star` frame) `st.star` fr)
      (F.on_dom a (fun x -> (f.post x `st.star` frame) `st.star` fr))
    = f.step (frame `st.star` fr)
  in
  { pre = _;
    post = F.on_dom a (fun x -> f.post x `st.star` frame);
    step }

/// Now, to prove that computations can be framed, we'll just thread
/// the frame through the entire computation, passing it over every
/// frameable action
let rec frame (#st:state u#s)
              (#a:Type u#a)
              (#p:st.pred)
              (#q:post st a)
              (fr:st.pred)
              (f:m a p q)
   : Dv (m u#s u#a u#act a (p `st.star` fr) (F.on_dom a (fun x -> q x `st.star` fr)))
   = match f with
     | Ret x -> Ret x
     | Act f k ->
       Act (frame_action f fr) (fun x -> frame fr (k x))
     | ObservedAct decode_obs f k ->
       ObservedAct decode_obs (frame_action f fr) (fun obs x -> frame fr (k obs x))
     | ObservedResultAct decode_obs f k ->
       ObservedResultAct decode_obs (frame_action f fr) (fun x obs -> frame fr (k x obs))
     | ObservedResultActWithHiddenState decode_obs f si_pre si_post k ->
       ObservedResultActWithHiddenState decode_obs (frame_action f fr) si_pre si_post
         (fun x observed_nat obs ot c ->
           let framed = frame fr (k x observed_nat obs ot c) in
           star_rotate_right st (f.post x) (si_pre x obs ot c) fr;
           assert (forall y. st.star (st.star (q y) (si_post x obs ot (NST.bump_observation c))) fr ==
             st.star (st.star (q y) fr) (si_post x obs ot (NST.bump_observation c)));
           assert (F.feq
             (fun y -> st.star (st.star (q y) (si_post x obs ot (NST.bump_observation c))) fr)
             (fun y -> st.star (st.star (q y) fr) (si_post x obs ot (NST.bump_observation c))));
           F.extensionality a (fun _ -> st.pred)
             (fun y -> st.star (st.star (q y) (si_post x obs ot (NST.bump_observation c))) fr)
             (fun y -> st.star (st.star (q y) fr) (si_post x obs ot (NST.bump_observation c)));
           coerce_eq () framed)
     | ObservedResultActWithHiddenStateAction si k ->
       ObservedResultActWithHiddenStateAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt value_event resolve_event ->
           let (| b, mid, act, kont |) = k observed_nat ot c receipt value_event resolve_event in
           (| b,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act,
              (fun y -> frame fr (kont y)) |))
     | ObservedResultActWithHiddenStateReturnAction si k ->
       ObservedResultActWithHiddenStateReturnAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt value_event resolve_event ->
           let (| b, ret, mid, act |) = k observed_nat ot c receipt value_event resolve_event in
           (| b,
              ret,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act |))
     | ObservedResultTargetedActWithHiddenStateReturnAction resolve_result resolve_payload pack pid payload_value si k ->
       ObservedResultTargetedActWithHiddenStateReturnAction
         #st resolve_result resolve_payload pack pid payload_value
         #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt resolve_event ->
           let (| b, ret, mid, act |) = k observed_nat ot c receipt resolve_event in
           (| b,
              ret,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act |))
     | ObservedResultTargetedActWithHiddenStateAction resolve_result resolve_payload pack pid payload_value si k ->
       ObservedResultTargetedActWithHiddenStateAction
         #st resolve_result resolve_payload pack pid payload_value
         #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun observed_nat ot c receipt resolve_event ->
           let (| b, mid, act, kont |) = k observed_nat ot c receipt resolve_event in
           (| b,
              F.on_dom b (fun y -> mid y `st.star` fr),
              frame_hidden_observed_action #st #b #p #mid si ot c fr act,
              (fun y -> frame fr (kont y)) |))

     | Par #_ #pre0 m0 #_ #prek #postk k ->
       let k' = frame fr k in
       Par m0 k'
     | Angel #_ #pre #post #c decode k ->
       Angel decode (fun x -> frame fr (k x))
     | FreshProphId #_ #pre #post k ->
       FreshProphId (fun pid -> frame fr (k pid))
     | FreshProphIdWithObsCtr #_ #pre #post k ->
       FreshProphIdWithObsCtr (fun pid ot c -> frame fr (k pid ot c))
     | FreshProphIdWithHiddenState #_ #_ #_ si k ->
       FreshProphIdWithHiddenState
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun pid ot c ->
           let framed = frame fr (k pid ot c) in
           star_rotate_right st p (si ot c) fr;
           assert (forall x. st.star (st.star (q x) (si ot (NST.bump_prophecy c))) fr ==
             st.star (st.star (q x) fr) (si ot (NST.bump_prophecy c)));
           assert (F.feq
             (fun x -> st.star (st.star (q x) (si ot (NST.bump_prophecy c))) fr)
             (fun x -> st.star (st.star (q x) fr) (si ot (NST.bump_prophecy c))));
           F.extensionality a (fun _ -> st.pred)
             (fun x -> st.star (st.star (q x) (si ot (NST.bump_prophecy c))) fr)
             (fun x -> st.star (st.star (q x) fr) (si ot (NST.bump_prophecy c)));
           coerce_eq () framed)
     | FreshProphIdWithHiddenStateAction si alloc ->
       FreshProphIdWithHiddenStateAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun pid ot c ->
           let (| b, mid, act, k |) = alloc pid ot c in
           (| b,
              F.on_dom b (fun x -> mid x `st.star` fr),
              frame_hidden_fresh_action #st #b #p #mid si ot c fr act,
              (fun x -> frame fr (k x)) |))
     | FreshProphIdWithHiddenStateReturnAction si alloc ->
       FreshProphIdWithHiddenStateReturnAction
         #st #a #(p `st.star` fr) #(F.on_dom a (fun x -> q x `st.star` fr)) si
         (fun pid ot c ->
           let (| b, ret, mid, act |) = alloc pid ot c in
           (| b,
              ret,
              F.on_dom b (fun x -> mid x `st.star` fr),
              frame_hidden_fresh_action #st #b #p #mid si ot c fr act |))

let rec apply_hom (#st:state u#s)
              (hom: st.pred->st.pred
                { hom st.emp == st.emp /\ (forall x y. hom (x `st.star` y) == hom x `st.star` hom y) })
              (hom_act: (#b:Type u#act -> act:action st b -> act':action st b
                { act'.pre == hom act.pre /\ (forall x. act'.post x == hom (act.post x)) }))
              (#a:Type u#a)
              (#p:st.pred)
              (#q:post st a)
              (f:m a p q)
   : Dv (m u#s u#a u#act a (hom p) (F.on_dom a (fun x -> hom (q x))))
   = match f with
     | Ret x -> Ret x
     | Act f k ->
       Act (hom_act f) (fun x -> apply_hom hom hom_act (k x))
     | ObservedAct decode_obs f k ->
       ObservedAct decode_obs (hom_act f) (fun obs x -> apply_hom hom hom_act (k obs x))
     | ObservedResultAct decode_obs f k ->
       ObservedResultAct decode_obs (hom_act f) (fun x obs -> apply_hom hom hom_act (k x obs))
     | ObservedResultActWithHiddenState decode_obs f si_pre si_post k ->
       ObservedResultActWithHiddenState decode_obs (hom_act f)
         (fun x obs ot c -> hom (si_pre x obs ot c))
         (fun x obs ot c -> hom (si_post x obs ot c))
         (fun x observed_nat obs ot c -> apply_hom hom hom_act (k x observed_nat obs ot c))
     | ObservedResultActWithHiddenStateAction si k ->
       ObservedResultActWithHiddenStateAction
         #st #a #(hom p) #(F.on_dom a (fun x -> hom (q x)))
         (fun ot c -> hom (si ot c))
         (fun observed_nat ot c receipt value_event resolve_event ->
           let (| b, mid, act, kont |) = k observed_nat ot c receipt value_event resolve_event in
           (| b,
              F.on_dom b (fun y -> hom (mid y)),
              hom_hidden_observed_action #st #b #p #mid si ot c hom hom_act act,
              (fun y -> apply_hom hom hom_act (kont y)) |))
     | ObservedResultActWithHiddenStateReturnAction si k ->
       ObservedResultActWithHiddenStateReturnAction
         #st #a #(hom p) #(F.on_dom a (fun x -> hom (q x)))
         (fun ot c -> hom (si ot c))
         (fun observed_nat ot c receipt value_event resolve_event ->
           let (| b, ret, mid, act |) = k observed_nat ot c receipt value_event resolve_event in
           (| b,
              ret,
              F.on_dom b (fun y -> hom (mid y)),
              hom_hidden_observed_action #st #b #p #mid si ot c hom hom_act act |))
     | ObservedResultTargetedActWithHiddenStateReturnAction resolve_result resolve_payload pack pid payload_value si k ->
       ObservedResultTargetedActWithHiddenStateReturnAction
         #st resolve_result resolve_payload pack pid payload_value
         #a #(hom p) #(F.on_dom a (fun x -> hom (q x)))
         (fun ot c -> hom (si ot c))
         (fun observed_nat ot c receipt resolve_event ->
           let (| b, ret, mid, act |) = k observed_nat ot c receipt resolve_event in
           (| b,
              ret,
              F.on_dom b (fun y -> hom (mid y)),
              hom_hidden_observed_action #st #b #p #mid si ot c hom hom_act act |))
     | ObservedResultTargetedActWithHiddenStateAction resolve_result resolve_payload pack pid payload_value si k ->
       ObservedResultTargetedActWithHiddenStateAction
         #st resolve_result resolve_payload pack pid payload_value
         #a #(hom p) #(F.on_dom a (fun x -> hom (q x)))
         (fun ot c -> hom (si ot c))
         (fun observed_nat ot c receipt resolve_event ->
           let (| b, mid, act, kont |) = k observed_nat ot c receipt resolve_event in
           (| b,
              F.on_dom b (fun y -> hom (mid y)),
              hom_hidden_observed_action #st #b #p #mid si ot c hom hom_act act,
              (fun y -> apply_hom hom hom_act (kont y)) |))

     | Par #_ #pre0 m0 #_ #prek #postk k ->
       let m0' = apply_hom hom hom_act m0 in
       let k' = apply_hom hom hom_act k in
       assert as_post #st #(U.raise_t unit) st.emp == as_post (hom st.emp);
       Par m0' k'
     | Angel #_ #pre #post #c decode k ->
       Angel decode (fun x -> apply_hom hom hom_act (k x))
     | FreshProphId #_ #pre #post k ->
       FreshProphId (fun pid -> apply_hom hom hom_act (k pid))
     | FreshProphIdWithObsCtr #_ #pre #post k ->
       FreshProphIdWithObsCtr (fun pid ot c -> apply_hom hom hom_act (k pid ot c))
     | FreshProphIdWithHiddenState #_ #pre #post si k ->
       FreshProphIdWithHiddenState (fun ot c -> hom (si ot c))
         (fun pid ot c -> apply_hom hom hom_act (k pid ot c))
     | FreshProphIdWithHiddenStateAction si alloc ->
       FreshProphIdWithHiddenStateAction
         #st #a #(hom p) #(F.on_dom a (fun x -> hom (q x)))
         (fun ot c -> hom (si ot c))
         (fun pid ot c ->
           let (| b, mid, act, k |) = alloc pid ot c in
           (| b,
              F.on_dom b (fun x -> hom (mid x)),
              hom_hidden_fresh_action #st #b #p #mid si ot c hom hom_act act,
              (fun x -> apply_hom hom hom_act (k x)) |))
     | FreshProphIdWithHiddenStateReturnAction si alloc ->
       FreshProphIdWithHiddenStateReturnAction
         #st #a #(hom p) #(F.on_dom a (fun x -> hom (q x)))
         (fun ot c -> hom (si ot c))
         (fun pid ot c ->
           let (| b, ret, mid, act |) = alloc pid ot c in
           (| b,
              ret,
              F.on_dom b (fun x -> hom (mid x)),
              hom_hidden_fresh_action #st #b #p #mid si ot c hom hom_act act |))

(**
 * [fork]: Parallel execution using fork
 * Works by just using the `Par` node and `Ret` as its continuation
 **)
let fork (#st:state u#s)
        #p0 (m0:m unit p0 (as_post st.emp))
 : Dv (m u#s u#0 u#act unit p0 (as_post st.emp))
 = let m0' = mbind m0 (fun _ -> Ret #st #_ #(as_post st.emp) (U.raise_val ())) in
   Par m0' (Ret ())

let conv (#st:state u#s) (a:Type u#a)
         (#p:st.pred)
         (#q:post st a)
         (q':post st a { forall x. q x == q' x })
: Lemma (m u#s u#a u#act a p q == m u#s u#a u#act a p q')
= F.extensionality _ _ q q'
