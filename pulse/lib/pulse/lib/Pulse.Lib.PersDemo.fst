(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

module Pulse.Lib.PersDemo
#lang-pulse

open Pulse.Main
open Pulse.Lib.Core
open Pulse.Lib.Trade

(** Smoke-test the pure rule, duplication, elimination, and affine dropping. *)
ghost fn pers_pure_roundtrip ()
  requires pure True
  ensures pure True
{
  pers_intro_pure True;
  pers_dup (pure True);
  pers_elim (pure True);
  drop_ (pers (pure True))
}

(** A closed trade body can be introduced persistently, duplicated, eliminated,
    and then fired without ever using a model-level [pure (implies _ _)] fact. *)
ghost fn pers_trade_emp_roundtrip ()
  requires emp
  ensures emp
{
  pers_intro_trade emp emp fn _ {};
  pers_dup (trade #emp_inames emp emp);
  pers_elim (trade #emp_inames emp emp);
  elim_trade #emp_inames emp emp;
  drop_ (pers (trade #emp_inames emp emp))
}

(** A persistent invariant token can be introduced from a plain invariant token. *)
ghost fn pers_inv_survives (i: iname) (p: slprop)
  requires inv i p
  ensures pers (inv i p)
{
  pers_intro_inv i p
}

(** Duplicated persistent evidence can be eliminated back to the underlying token. *)
ghost fn pers_inv_dup_elim (i: iname) (p: slprop)
  requires pers (inv i p)
  ensures inv i p
{
  pers_dup (inv i p);
  pers_elim (inv i p);
  drop_ (pers (inv i p))
}

(** The slprop-ref persistence path supports intro, duplication, and elimination. *)
ghost fn pers_slprop_ref_dup_elim (r: slprop_ref) (p: slprop)
  requires slprop_ref_pts_to r p
  ensures slprop_ref_pts_to r p
{
  pers_intro_slprop_ref r p;
  pers_dup (slprop_ref_pts_to r p);
  pers_elim (slprop_ref_pts_to r p);
  drop_ (pers (slprop_ref_pts_to r p))
}

(** Persistent slprop-ref and invariant evidence can be recombined under [pers]. *)
ghost fn pers_slprop_ref_inv_star_intro (r: slprop_ref) (p: slprop) (i: iname) (q: slprop)
  requires pers (slprop_ref_pts_to r p) ** pers (inv i q)
  ensures pers (slprop_ref_pts_to r p ** inv i q)
{
  pers_intro_star (slprop_ref_pts_to r p) (inv i q)
}
