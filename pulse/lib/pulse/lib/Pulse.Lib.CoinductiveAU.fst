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
    (is : inames)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
    (p : slprop)
  : slprop
  = exists* (x : a).
      alpha x **
      trade #is (alpha x) p **
      (forall* (y : b). trade #is (beta x y) (phi x y))

ghost fn atomic_acc_pre_intro
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
    (p : slprop)
    (x : a)
  requires alpha x **
          trade #is (alpha x) p **
          (forall* (y : b). trade #is (beta x y) (phi x y))
  ensures atomic_acc_pre is alpha beta phi p
{
  fold (atomic_acc_pre is alpha beta phi p)
}

let call #t #is #req #ens (h: unit -> stt_ghost is t req (fun x -> ens x)) = h

(** Monotonicity: lift [atomic_acc_pre is _ p] to [atomic_acc_pre is _ q]
    using a trade [p @==> q] (at emp_inames; lifted to is internally). *)
ghost fn mono_aap_lemma
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p q : slprop)
    (_ : unit)
  requires atomic_acc_pre is alpha beta phi p ** trade p q
  ensures atomic_acc_pre is alpha beta phi q
{
  unfold (atomic_acc_pre is alpha beta phi p);
  with x. assert (
    alpha x **
    trade #is (alpha x) p **
    (forall* (y : b). trade #is (beta x y) (phi x y)));
  trade_sub_inv #emp_inames #is p q;
  trade_compose #is (alpha x) p q;
  fold (atomic_acc_pre is alpha beta phi q)
}

instance mono_atomic_acc_pre
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : mono_slprop (atomic_acc_pre is alpha beta phi)
  = { mono_lemma = mono_aap_lemma is alpha beta phi; }

ghost fn aupd_intro
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p : slprop)
  requires pure (implies p (atomic_acc_pre is alpha beta phi p)) ** p
  ensures atomic_update is alpha beta phi
{
  bi_gfp_intro (atomic_acc_pre is alpha beta phi) p;
  fold (atomic_update is alpha beta phi)
}

ghost fn aupd_unfold
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update is alpha beta phi
  ensures atomic_acc_pre is alpha beta phi (atomic_update is alpha beta phi)
{
  unfold (atomic_update is alpha beta phi);
  bi_gfp_unfold (atomic_acc_pre is alpha beta phi)
    #(mono_atomic_acc_pre is alpha beta phi);
  rewrite (atomic_acc_pre is alpha beta phi (bi_gfp (atomic_acc_pre is alpha beta phi)))
       as (atomic_acc_pre is alpha beta phi (atomic_update is alpha beta phi))
}

ghost fn aupd_intro_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p : slprop)
  requires pers (trade p (atomic_acc_pre is alpha beta phi p)) ** p
  ensures atomic_update_pers is alpha beta phi
{
  bi_gfp_pers_intro (atomic_acc_pre is alpha beta phi) p;
  fold (atomic_update_pers is alpha beta phi)
}

ghost fn aupd_unfold_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update_pers is alpha beta phi
  ensures atomic_acc_pre is alpha beta phi (atomic_update_pers is alpha beta phi)
{
  unfold (atomic_update_pers is alpha beta phi);
  bi_gfp_pers_unfold (atomic_acc_pre is alpha beta phi)
    #(mono_atomic_acc_pre is alpha beta phi);
  rewrite (atomic_acc_pre is alpha beta phi (bi_gfp_pers (atomic_acc_pre is alpha beta phi)))
       as (atomic_acc_pre is alpha beta phi (atomic_update_pers is alpha beta phi))
}

(***** Derived ops *****)

ghost fn au_open
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update is alpha beta phi
  returns x : erased a
  ensures alpha x **
          trade #is (alpha x) (atomic_update is alpha beta phi) **
          (forall* (y : b). trade #is (beta x y) (phi x y))
{
  aupd_unfold is alpha beta phi;
  unfold (atomic_acc_pre is alpha beta phi (atomic_update is alpha beta phi));
  with x. assert (
    alpha x **
    trade #is (alpha x) (atomic_update is alpha beta phi) **
    (forall* (y : b). trade #is (beta x y) (phi x y)));
  hide x
}

ghost fn au_commit
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a) (y : b)
  requires beta x y ** (forall* (y' : b). trade #is (beta x y') (phi x y'))
  ensures phi x y
  opens is
{
  elim_forall #b #(fun y' -> trade #is (beta x y') (phi x y')) y;
  elim_trade #is (beta x y) (phi x y)
}

ghost fn au_abort
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a)
  requires alpha x ** trade #is (alpha x) (atomic_update is alpha beta phi)
  ensures atomic_update is alpha beta phi
  opens is
{
  elim_trade #is (alpha x) (atomic_update is alpha beta phi)
}

ghost fn au_open_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update_pers is alpha beta phi
  returns x : erased a
  ensures alpha x **
          trade #is (alpha x) (atomic_update_pers is alpha beta phi) **
          (forall* (y : b). trade #is (beta x y) (phi x y))
{
  aupd_unfold_pers is alpha beta phi;
  unfold (atomic_acc_pre is alpha beta phi (atomic_update_pers is alpha beta phi));
  with x. assert (
    alpha x **
    trade #is (alpha x) (atomic_update_pers is alpha beta phi) **
    (forall* (y : b). trade #is (beta x y) (phi x y)));
  hide x
}

ghost fn au_commit_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a) (y : b)
  requires beta x y ** (forall* (y' : b). trade #is (beta x y') (phi x y'))
  ensures phi x y
  opens is
{
  elim_forall #b #(fun y' -> trade #is (beta x y') (phi x y')) y;
  elim_trade #is (beta x y) (phi x y)
}

ghost fn au_abort_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a)
  requires alpha x ** trade #is (alpha x) (atomic_update_pers is alpha beta phi)
  ensures atomic_update_pers is alpha beta phi
  opens is
{
  elim_trade #is (alpha x) (atomic_update_pers is alpha beta phi)
}
