(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

(**
  Demo: client-side composition of an atomic_update with a user-held
  invariant, without any cooperation from the AU's implementer.

  The Iris analog is [aacc_inv]: from [inv N P] and [atomic_acc E ...]
  derive an atomic_acc whose alpha is augmented by [|>P]. This requires
  fancy updates [|={E,E'}=>] in Iris.

  In Pulse the same pattern works directly: [au_open] is a pure ghost
  step with [emp_inames], so it composes with [with_invariants_g] for
  any [i] without iname conflict. The "linearization point" is the
  atomic-or-ghost continuation passed to [with_invariants_g], during
  which the client holds both [I] (from the inv) and [alpha x] (from
  the AU) as separating resources.
*)

module Pulse.Lib.AaccInvDemo
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Forall
open Pulse.Lib.CoinductiveAU

(** aacc_inv as a higher-order combinator.

    Given:
    - an invariant [inv i I] with timeless contents,
    - an [atomic_update alpha beta phi],
    - and a ghost continuation [k] that picks a commit-value [y]
      from any current state [x], using both [I] and [alpha x],

    fire one atomic step that opens the inv, opens the AU, runs [k],
    commits the AU with [y], and re-closes the inv. The client holds
    both pieces during [k] — full client-side composition without any
    primitive added to Pulse. *)
let call_g #t #is #req #ens (h : unit -> stt_ghost is t req (fun x -> ens x)) = h

ghost fn aacc_inv_demo
    (#a #b : Type0)
    (i : iname)
    (i_disj : squash (not (mem_inv emp_inames i)))
    (big_i : slprop { timeless big_i })
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (k : (x : erased a) -> unit -> stt_ghost b emp_inames
           (alpha x ** big_i)
           (fun y -> beta x y ** big_i))
  requires inv i big_i ** atomic_update emp_inames alpha beta phi ** later_credit 1
  opens add_inv emp_inames i
  returns y : b
  ensures (exists* (x : a). phi x y)
{
  with_invariants_g b emp_inames i big_i
    (atomic_update emp_inames alpha beta phi)
    (fun y -> exists* (x : a). phi x y)
  fn _ {
    let x = au_open emp_inames alpha beta phi;
    let y = call_g (k x) ();
    au_commit emp_inames alpha beta phi x y;
    drop_ (trade #emp_inames (alpha x) (atomic_update emp_inames alpha beta phi));
    intro_exists #a (fun x -> phi x y) x;
    y
  }
}
