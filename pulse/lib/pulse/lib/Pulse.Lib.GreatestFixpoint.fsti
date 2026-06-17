(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

(**
  Greatest fixed point of a monotone slprop transformer.

  Iris encoding:
    bi_greatest_fixpoint F := exists Phi. (BOX) (Phi -* F Phi) /\ Phi
  where (BOX)(- -* -) is a persistent linear magic wand.

  Pulse encoding (this module):
    bi_gfp F := exists* Phi. pure (implies Phi (F Phi)) ** Phi
  where [implies : slprop -> slprop -> prop] is the meta-level entailment
  exposed by [PulseCore.InstantiatedSemantics] and [implies_elim] (from
  [PulseCore.Atomic]) consumes [Phi] to produce [F Phi]. The [pure]
  wrapping makes the obligation propositional, hence reusable via the
  [elim_pure]/[intro_pure] round-trip (the F* squash term can be applied
  many times). Linearity of [Phi] is preserved at firing time, matching
  Iris's [BOX]-wand exactly.
*)

module Pulse.Lib.GreatestFixpoint
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

(** The greatest fixed point of an slprop transformer [F]. *)
val bi_gfp (f : slprop -> slprop) : slprop

(** Iris-faithful additive encoding using the persistence modality:
      exists Phi. <pers> (Phi -* F Phi) ** Phi. *)
val bi_gfp_pers (f : slprop -> slprop) : slprop

(** Coinductive introduction: any [P] with a meta-level entailment
    [P |- F P] inhabits the gfp. The Pulse analog of Iris's coiter rule. *)
ghost fn bi_gfp_intro (f : slprop -> slprop) (p : slprop)
  requires pure (implies p (f p)) ** p
  ensures bi_gfp f

(** Additive coinductive introduction with a persistent Pulse trade. *)
ghost fn bi_gfp_pers_intro (f : slprop -> slprop) (p : slprop)
  requires pers (trade p (f p)) ** p
  ensures bi_gfp_pers f

(** Monotonicity of [F]: a one-shot conversion [p ~> q] (as a [trade])
    lifts to [F p ~> F q]. Iris's BiMonoPred via Pulse trades. *)
class mono_slprop (f : slprop -> slprop) = {
  mono_lemma :
    (p : slprop) -> (q : slprop) ->
    unit -> stt_ghost unit emp_inames (f p ** trade p q) (fun _ -> f q);
}

(** Coinductive elimination: for monotone [F],
      bi_gfp F |- F (bi_gfp F).
    [bi_gfp F] is consumed (linear): we extract one application of
    the entailment, weaken the result through [F]'s monotonicity. *)
ghost fn bi_gfp_unfold (f : slprop -> slprop) {| mono_slprop f |}
  requires bi_gfp f
  ensures f (bi_gfp f)

(** Coinductive elimination for the additive/persistent encoding. *)
ghost fn bi_gfp_pers_unfold (f : slprop -> slprop) {| mono_slprop f |}
  requires bi_gfp_pers f
  ensures f (bi_gfp_pers f)

(** Tiny instance + demo: identity functor. *)
val id_slprop (p : slprop) : slprop
instance val mono_id_slprop : mono_slprop id_slprop

ghost fn bi_gfp_id_unfold_demo (_ : unit)
  requires bi_gfp id_slprop
  ensures id_slprop (bi_gfp id_slprop)
