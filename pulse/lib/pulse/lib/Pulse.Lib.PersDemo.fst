(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

module Pulse.Lib.PersDemo
#lang-pulse

open Pulse.Main
open Pulse.Lib.Core

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
