(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

module Pulse.Lib.GreatestFixpoint
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

let call #t #is #req #ens (h: unit -> stt_ghost is t req (fun x -> ens x)) = h

let bi_gfp (f : slprop -> slprop) : slprop =
  exists* (p : slprop). equiv p (p ** f p) ** p

ghost fn bi_gfp_intro (f : slprop -> slprop) (p : slprop)
  requires equiv p (p ** f p) ** p
  ensures bi_gfp f
{
  fold (bi_gfp f)
}

(** Closure used as f_elim for intro_trade in bi_gfp_unfold:
    given [equiv p (p ** f p) ** p], produce [bi_gfp f]. *)
ghost fn cvt_phi_to_gfp (f : slprop -> slprop) (phi : slprop) (_ : unit)
  requires equiv phi (phi ** f phi) ** phi
  ensures bi_gfp f
{
  bi_gfp_intro f phi
}

ghost fn bi_gfp_unfold (f : slprop -> slprop) {| mono : mono_slprop f |}
  requires bi_gfp f
  ensures f (bi_gfp f)
{
  unfold (bi_gfp f);
  with phi. assert (equiv phi (phi ** f phi) ** phi);
  equiv_dup phi (phi ** f phi);
  equiv_elim phi (phi ** f phi);
  equiv_dup phi (phi ** f phi);
  intro_trade #emp_inames phi (bi_gfp f) (equiv phi (phi ** f phi)) (cvt_phi_to_gfp f phi);
  // Apply mono to convert f phi into f (bi_gfp f).
  call (mono.mono_lemma phi (bi_gfp f)) ();
  drop_ (equiv phi (phi ** f phi));
  drop_ phi
}

(** Identity functor + instance + demo. *)
let id_slprop (p : slprop) : slprop = p

ghost fn mono_id_lemma (p : slprop) (q : slprop) (_ : unit)
  requires id_slprop p ** trade p q
  ensures id_slprop q
{
  unfold (id_slprop p);
  elim_trade #emp_inames p q;
  fold (id_slprop q)
}

instance mono_id_slprop : mono_slprop id_slprop = {
  mono_lemma = mono_id_lemma;
}

ghost fn bi_gfp_id_unfold_demo (_ : unit)
  requires bi_gfp id_slprop
  ensures id_slprop (bi_gfp id_slprop)
{
  bi_gfp_unfold id_slprop #mono_id_slprop
}
