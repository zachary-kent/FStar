(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

(**
  Coinductive atomic update / atomic accessor for Pulse, built on
  Pulse.Lib.GreatestFixpoint.

  Iris definition (atomic.v):
    atomic_acc Eo Ei alpha P beta Phi :=
      |={Eo,Ei}=> exists x, alpha x * (
        (alpha x ={Ei,Eo}=* P) /\
        (forall y, beta x y ={Ei,Eo}=* Phi x y))
    atomic_update Eo Ei alpha beta Phi :=
      bi_greatest_fixpoint (fun P. atomic_acc Eo Ei alpha P beta Phi) tt

  This module ports the gfp structure (not the masks/fupd yet). The
  functor [atomic_acc_pre] has [P] in covariant position (the abort
  branch returns it), making mono straightforward via [trade_compose].

  No client-side aacc_inv yet — first deliverable is just intro +
  unfold for atomic_update.
*)

module Pulse.Lib.CoinductiveAU
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Forall
open Pulse.Lib.GreatestFixpoint

(** The atomic-accessor functor, parameterized by the "AU slot" [p].
    A witness exhibits some [x] with [alpha x] currently held, a way
    to abort (returning [p] = the AU) and a way to commit (turning any
    [beta x y] into [phi x y]). *)
val atomic_acc_pre
    (#a #b : Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
    (p : slprop)
  : slprop

(** Monotonicity of [atomic_acc_pre _ _ _] in its [p] argument.
    Required to apply [bi_gfp_unfold]. *)
instance val mono_atomic_acc_pre
    (#a #b : Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : mono_slprop (atomic_acc_pre alpha beta phi)

(** The coinductive atomic update. *)
let atomic_update
    (#a #b : Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : slprop
  = bi_gfp (atomic_acc_pre alpha beta phi)

(** Introduction: any [p] with a meta-entailment to its atomic_acc form
    inhabits [atomic_update]. *)
ghost fn aupd_intro
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p : slprop)
  requires pure (implies p (atomic_acc_pre alpha beta phi p)) ** p
  ensures atomic_update alpha beta phi

(** Unfolding: an AU is a one-step access. *)
ghost fn aupd_unfold
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update alpha beta phi
  ensures atomic_acc_pre alpha beta phi (atomic_update alpha beta phi)

(***** Derived ops *****)

(** Open: extract the witness, the [alpha x], the abort-trade, and the
    commit-foralls from an AU. *)
ghost fn au_open
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update alpha beta phi
  returns x : erased a
  ensures alpha x **
          (alpha x @==> atomic_update alpha beta phi) **
          (forall* (y : b). beta x y @==> phi x y)

(** Commit: at linearization point, replace [beta x y] with [phi x y]. *)
ghost fn au_commit
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a) (y : b)
  requires beta x y ** (forall* (y' : b). beta x y' @==> phi x y')
  ensures phi x y

(** Abort: return [alpha x] to restore the AU for later use. *)
ghost fn au_abort
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a)
  requires alpha x ** (alpha x @==> atomic_update alpha beta phi)
  ensures atomic_update alpha beta phi
