(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

module Pulse.Lib.GreatestFixpoint
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade



(** Local helper for invoking stt_ghost-valued function fields
    (private in Pulse.Lib.Trade). *)
let call #t #is #req #ens (h: unit -> stt_ghost is t req (fun x -> ens x)) = h

let post_fp_obligation (f : slprop -> slprop) (p : slprop) : slprop =
  pure (implies p (f p))

let bi_gfp (f : slprop -> slprop) : slprop =
  exists* (p : slprop). post_fp_obligation f p ** p

let post_fp_pers_obligation (f : slprop -> slprop) (p : slprop) : slprop =
  pers (trade p (f p))

let bi_gfp_pers (f : slprop -> slprop) : slprop =
  exists* (p : slprop). post_fp_pers_obligation f p ** p

ghost fn bi_gfp_intro (f : slprop -> slprop) (p : slprop)
  requires pure (implies p (f p)) ** p
  ensures bi_gfp f
{
  fold (post_fp_obligation f p);
  fold (exists* (q : slprop). post_fp_obligation f q ** q);
  fold (bi_gfp f)
}

ghost fn bi_gfp_pers_intro (f : slprop -> slprop) (p : slprop)
  requires pers (trade p (f p)) ** p
  ensures bi_gfp_pers f
{
  fold (post_fp_pers_obligation f p);
  fold (exists* (q : slprop). post_fp_pers_obligation f q ** q);
  fold (bi_gfp_pers f)
}

(** Closure used as f_elim for intro_trade in bi_gfp_unfold:
    given [pure (implies phi (f phi)) ** phi], produce [bi_gfp f]. *)
ghost fn cvt_phi_to_gfp (f : slprop -> slprop) (phi : slprop) (_ : unit)
  requires pure (implies phi (f phi)) ** phi
  ensures bi_gfp f
{
  bi_gfp_intro f phi
}

ghost fn bi_gfp_unfold (f : slprop -> slprop) {| mono : mono_slprop f |}
  requires bi_gfp f
  ensures f (bi_gfp f)
{
  unfold (bi_gfp f);
  with phi. assert (post_fp_obligation f phi ** phi);
  unfold (post_fp_obligation f phi);
  // Extract the meta-fact (consumes the pure slprop, produces emp + squash).
  let pf : squash (implies phi (f phi)) = elim_pure_explicit (implies phi (f phi));
  // Re-introduce two copies using the saved squash.
  intro_pure (implies phi (f phi)) pf;
  intro_pure (implies phi (f phi)) pf;
  // Have: pure_a ** pure_b ** phi
  // Build trade phi (bi_gfp f); intro_trade consumes pure_a as extra.
  intro_trade #emp_inames phi (bi_gfp f) (pure (implies phi (f phi))) (cvt_phi_to_gfp f phi);
  // Have: pure_b ** phi ** trade phi (bi_gfp f)
  // Use pure_b's meta-fact to invoke implies_elim, consuming phi.
  drop_ (pure (implies phi (f phi)));
  implies_elim phi (f phi);
  // Have: f phi ** trade phi (bi_gfp f)
  // Apply mono to lift f phi to f (bi_gfp f), consuming the trade.
  call (mono.mono_lemma phi (bi_gfp f)) ()
}

(** Closure used as f_elim for intro_trade in bi_gfp_pers_unfold:
    given a persistent copy of [phi -* f phi] plus [phi], repack [bi_gfp_pers f]. *)
ghost fn cvt_phi_to_gfp_pers (f : slprop -> slprop) (phi : slprop) (_ : unit)
  requires pers (trade phi (f phi)) ** phi
  ensures bi_gfp_pers f
{
  bi_gfp_pers_intro f phi
}

ghost fn bi_gfp_pers_unfold (f : slprop -> slprop) {| mono : mono_slprop f |}
  requires bi_gfp_pers f
  ensures f (bi_gfp_pers f)
{
  unfold (bi_gfp_pers f);
  with phi. assert (post_fp_pers_obligation f phi ** phi);
  unfold (post_fp_pers_obligation f phi);
  // Duplicate the persistent wand: one copy is captured to rebuild the gfp,
  // the other is eliminated and fired on [phi] to produce [f phi].
  pers_dup (trade phi (f phi));
  intro_trade #emp_inames phi (bi_gfp_pers f) (pers (trade phi (f phi))) (cvt_phi_to_gfp_pers f phi);
  pers_elim (trade phi (f phi));
  elim_trade #emp_inames phi (f phi);
  call (mono.mono_lemma phi (bi_gfp_pers f)) ()
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
