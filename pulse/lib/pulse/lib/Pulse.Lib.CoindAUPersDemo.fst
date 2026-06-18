(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

module Pulse.Lib.CoindAUPersDemo
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.CoinductiveAU

(** A tiny AU instance over unit resources.  The state token, commit token,
    and postcondition are all [emp], so the file isolates the additive
    pers/trade construction from any unrelated heap reasoning. *)
let toy_alpha (_ : unit) : slprop = emp
let toy_beta (x : unit) (_ : unit) : slprop = toy_alpha x
let toy_phi (x : unit) (y : unit) : slprop = toy_beta x y

(** Closed Pulse derivation of one atomic-access layer from [emp]. *)
ghost fn toy_acc_from_emp (_ : unit)
  requires emp
  ensures atomic_acc_pre emp_inames toy_alpha toy_beta toy_phi emp
{
  intro_trade #emp_inames (toy_alpha ()) emp emp fn _ {
    unfold (toy_alpha ())
  };
  intro_forall #unit #(fun y -> trade #emp_inames (toy_beta () y) (toy_phi () y)) emp fn y {
    intro_trade #emp_inames (toy_beta () y) (toy_phi () y) emp fn _ {
      unfold (toy_beta () y);
      fold (toy_beta () y);
      fold (toy_phi () y)
    }
  };
  fold (toy_alpha ());
  assert (
    toy_alpha () **
    trade #emp_inames (toy_alpha ()) emp **
    (forall* (y : unit). trade #emp_inames (toy_beta () y) (toy_phi () y)));
  atomic_acc_pre_intro emp_inames toy_alpha toy_beta toy_phi emp ()
}

(** Construct the persistent-wand AU witness intrinsically from [toy_acc_from_emp]. *)
ghost fn toy_au_intro_pers ()
  requires emp
  ensures atomic_update_pers emp_inames toy_alpha toy_beta toy_phi
{
  pers_intro_trade emp (atomic_acc_pre emp_inames toy_alpha toy_beta toy_phi emp) toy_acc_from_emp;
  aupd_intro_pers emp_inames toy_alpha toy_beta toy_phi emp
}

(** Full round-trip: construct the AU, open it, commit it, and discard the
    unused abort continuation. *)
ghost fn toy_au_pers_roundtrip ()
  requires emp
  ensures emp
{
  toy_au_intro_pers ();
  let x = au_open_pers emp_inames toy_alpha toy_beta toy_phi;
  fold (toy_beta (reveal x) ());
  au_commit_pers emp_inames toy_alpha toy_beta toy_phi (reveal x) ();
  drop_ (trade #emp_inames (toy_alpha (reveal x)) (atomic_update_pers emp_inames toy_alpha toy_beta toy_phi));
  unfold (toy_phi (reveal x) ());
  unfold (toy_beta (reveal x) ());
  unfold (toy_alpha (reveal x))
}
