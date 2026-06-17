(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

module Pulse.Lib.CoinductiveAU
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Forall
open Pulse.Lib.GreatestFixpoint

let atomic_acc_pre
    (#a #b : Type0)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
    (p : slprop)
  : slprop
  = exists* (x : a).
      alpha x **
      (alpha x @==> p) **
      (forall* (y : b). beta x y @==> phi x y)

(** Local helper for invoking stt_ghost-valued function fields. *)
let call #t #is #req #ens (h: unit -> stt_ghost is t req (fun x -> ens x)) = h

(** Monotonicity: given a trade [p @==> q], lift [atomic_acc_pre _ p]
    to [atomic_acc_pre _ q] by composing the abort branch's trade. *)
ghost fn mono_aap_lemma
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p q : slprop)
    (_ : unit)
  requires atomic_acc_pre alpha beta phi p ** trade p q
  ensures atomic_acc_pre alpha beta phi q
{
  unfold (atomic_acc_pre alpha beta phi p);
  with x. assert (
    alpha x **
    (alpha x @==> p) **
    (forall* (y : b). beta x y @==> phi x y));
  trade_compose #emp_inames (alpha x) p q;
  fold (atomic_acc_pre alpha beta phi q)
}

instance mono_atomic_acc_pre
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : mono_slprop (atomic_acc_pre alpha beta phi)
  = { mono_lemma = mono_aap_lemma alpha beta phi; }

ghost fn aupd_intro
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p : slprop)
  requires pure (implies p (atomic_acc_pre alpha beta phi p)) ** p
  ensures atomic_update alpha beta phi
{
  bi_gfp_intro (atomic_acc_pre alpha beta phi) p;
  fold (atomic_update alpha beta phi)
}

ghost fn aupd_unfold
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update alpha beta phi
  ensures atomic_acc_pre alpha beta phi (atomic_update alpha beta phi)
{
  unfold (atomic_update alpha beta phi);
  bi_gfp_unfold (atomic_acc_pre alpha beta phi)
    #(mono_atomic_acc_pre alpha beta phi);
  rewrite (atomic_acc_pre alpha beta phi (bi_gfp (atomic_acc_pre alpha beta phi)))
       as (atomic_acc_pre alpha beta phi (atomic_update alpha beta phi))
}

(***** Derived ops *****)

ghost fn au_open
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update alpha beta phi
  returns x : erased a
  ensures alpha x **
          (alpha x @==> atomic_update alpha beta phi) **
          (forall* (y : b). beta x y @==> phi x y)
{
  aupd_unfold alpha beta phi;
  unfold (atomic_acc_pre alpha beta phi (atomic_update alpha beta phi));
  with x. assert (
    alpha x **
    (alpha x @==> atomic_update alpha beta phi) **
    (forall* (y : b). beta x y @==> phi x y));
  hide x
}

ghost fn au_commit
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a) (y : b)
  requires beta x y ** (forall* (y' : b). beta x y' @==> phi x y')
  ensures phi x y
{
  elim_forall #b #(fun y' -> beta x y' @==> phi x y') y;
  elim_trade #emp_inames (beta x y) (phi x y)
}

ghost fn au_abort
    (#a #b : Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a)
  requires alpha x ** (alpha x @==> atomic_update alpha beta phi)
  ensures atomic_update alpha beta phi
{
  elim_trade #emp_inames (alpha x) (atomic_update alpha beta phi)
}
