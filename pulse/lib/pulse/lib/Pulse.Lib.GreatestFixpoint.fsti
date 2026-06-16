(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
*)

(**
  Greatest fixed point of a monotone slprop transformer.

  Following Iris's iris/bi/lib/fixpoint_mono.v, define
      bi_gfp F := exists* Phi. <persistent: Phi entails Phi ** F Phi> ** Phi
  Pulse encoding uses the user-level [equiv] modality to express the
  post-fixed-point obligation persistently: [equiv Phi (Phi ** F Phi)] is
  duplicable and supports [equiv_elim] for repeated unfolding.
*)

module Pulse.Lib.GreatestFixpoint
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

(** The greatest fixed point of an slprop transformer [F]. *)
val bi_gfp (f : slprop -> slprop) : slprop

(** Coinductive introduction. *)
ghost fn bi_gfp_intro (f : slprop -> slprop) (p : slprop)
  requires equiv p (p ** f p) ** p
  ensures bi_gfp f

(** Monotonicity of an slprop transformer.

    [F] is monotone if any one-shot ghost conversion [p ~> q] (packaged
    as a [trade]) lifts to a conversion [F p ~> F q]. This matches Iris's
    [BiMonoPred] but uses [Pulse.Lib.Trade] one-shot wands instead of
    persistent magic wands, which is adequate because [bi_gfp_unfold]
    consumes the trade once per call. *)
class mono_slprop (f : slprop -> slprop) = {
  mono_lemma :
    (p : slprop) -> (q : slprop) ->
    unit -> stt_ghost unit emp_inames (f p ** trade p q) (fun _ -> f q);
}

(** Coinductive elimination / unfolding.

    For monotone [F], the gfp unfolds: [bi_gfp F |- F (bi_gfp F)]. *)
ghost fn bi_gfp_unfold (f : slprop -> slprop) {| mono_slprop f |}
  requires bi_gfp f
  ensures f (bi_gfp f)

(** Tiny instance: F P = P (identity). Validates that the [mono_slprop]
    class can be inhabited and [bi_gfp_unfold] used end-to-end. *)
val id_slprop (p : slprop) : slprop
instance val mono_id_slprop : mono_slprop id_slprop

ghost fn bi_gfp_id_unfold_demo (_ : unit)
  requires bi_gfp id_slprop
  ensures id_slprop (bi_gfp id_slprop)
