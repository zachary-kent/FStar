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

val atomic_acc_pre
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
    (p : slprop)
  : slprop

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

instance val mono_atomic_acc_pre
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : mono_slprop (atomic_acc_pre is alpha beta phi)

let atomic_update
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : slprop
  = bi_gfp (atomic_acc_pre is alpha beta phi)

let atomic_update_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop)
    (beta : a -> b -> slprop)
    (phi : a -> b -> slprop)
  : slprop
  = bi_gfp_pers (atomic_acc_pre is alpha beta phi)

ghost fn aupd_intro
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p : slprop)
  requires pure (implies p (atomic_acc_pre is alpha beta phi p)) ** p
  ensures atomic_update is alpha beta phi

ghost fn aupd_unfold
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update is alpha beta phi
  ensures atomic_acc_pre is alpha beta phi (atomic_update is alpha beta phi)

ghost fn aupd_intro_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (p : slprop)
  requires pers (trade p (atomic_acc_pre is alpha beta phi p)) ** p
  ensures atomic_update_pers is alpha beta phi

ghost fn aupd_unfold_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update_pers is alpha beta phi
  ensures atomic_acc_pre is alpha beta phi (atomic_update_pers is alpha beta phi)

ghost fn au_open
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update is alpha beta phi
  returns x : erased a
  ensures alpha x **
          trade #is (alpha x) (atomic_update is alpha beta phi) **
          (forall* (y : b). trade #is (beta x y) (phi x y))

ghost fn au_commit
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a) (y : b)
  requires beta x y ** (forall* (y' : b). trade #is (beta x y') (phi x y'))
  ensures phi x y
  opens is

ghost fn au_abort
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a)
  requires alpha x ** trade #is (alpha x) (atomic_update is alpha beta phi)
  ensures atomic_update is alpha beta phi
  opens is

ghost fn au_open_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  requires atomic_update_pers is alpha beta phi
  returns x : erased a
  ensures alpha x **
          trade #is (alpha x) (atomic_update_pers is alpha beta phi) **
          (forall* (y : b). trade #is (beta x y) (phi x y))

ghost fn au_commit_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a) (y : b)
  requires beta x y ** (forall* (y' : b). trade #is (beta x y') (phi x y'))
  ensures phi x y
  opens is

ghost fn au_abort_pers
    (#a #b : Type0)
    (is : inames)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
    (x : a)
  requires alpha x ** trade #is (alpha x) (atomic_update_pers is alpha beta phi)
  ensures atomic_update_pers is alpha beta phi
  opens is
