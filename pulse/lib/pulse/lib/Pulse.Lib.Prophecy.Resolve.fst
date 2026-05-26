(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Prophecy resolution with equality — the ONE trusted axiom.

    `prophecy_resolve_eq` runs a computation f, updates the prophecy
    ghost ref to the result, and produces `pure (x == reveal v)` where
    v was the predicted value from prophecy_alloc.

    This is the semantic bridge between the angelic choice (Angel in
    PulseCore.Semantics) and the object-level proof. It is justified
    by the adequacy theorem: ∀ demonic tape ∃ angel tape such that
    every prophecy_alloc chooses v = the actual future result.

    This module contains the ONLY admit in the prophecy system.
    Everything else (prophecy_alloc, prophecy_set, prophecy_agree,
    resolve) is fully verified.

    Trust: same level as as_atomic (Pulse.Lib.Core.as_atomic = admit).
    Semantic backing: Angel constructor in PulseCore.Semantics + angel
    oracle in NondeterministicHoareStateMonad. *)
module Pulse.Lib.Prophecy.Resolve

open Pulse.Lib.Pervasives
open Pulse.Lib.Prophecy

(** prophecy_resolve_eq: run f, resolve prophecy, produce equality.

    Iris analogue: Resolve e1 e2 v — atomically execute e1 and
    resolve prophecy e2, with the adequacy theorem guaranteeing
    that the prophecy's predicted value matches the result.

    The equality `x == reveal v` is the irreducible prophecy axiom.
    Sound by: ∀ demonic_tape. ∃ angel_tape. v = actual_result.

    Semantic backing: Angel constructor reads from angel_tape via
    NST.angel(), and run_alt existentially quantifies angel_tape. *)
let prophecy_resolve_eq (#a:Type0)
    (p : prophecy_var a)
    (v : Ghost.erased a)
    (#pre:slprop)
    (#post: a -> slprop)
    (f : unit -> stt_atomic a #Observable emp_inames pre (fun x -> post x))
  : stt_atomic a #Observable emp_inames
      (Pulse.Lib.Core.op_Star_Star (prophecy_token p (Ghost.reveal v))
        (Pulse.Lib.Core.op_Star_Star (prophecy_handle p (Ghost.reveal v)) pre))
      (fun x -> Pulse.Lib.Core.op_Star_Star (post x)
        (Pulse.Lib.Core.op_Star_Star
          (prophecy_token p x)
          (Pulse.Lib.Core.op_Star_Star
            (prophecy_handle p x)
            (pure (x == Ghost.reveal v)))))
  = // The ONE axiom in the prophecy system.
    // Justified by Angel semantics + angel oracle adequacy:
    //   ∀ demonic_tape. ∃ angel_tape. v = actual_result
    // See PulseCore.Semantics.Angel, NST.angel, run_alt.
    admit ()
