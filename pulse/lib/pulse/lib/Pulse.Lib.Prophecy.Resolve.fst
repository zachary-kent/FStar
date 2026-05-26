(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Prophecy resolve combinator — trusted axiom.
    Same trust level as as_atomic (Pulse.Lib.Core.as_atomic = admit()).
    Sound by prophecy adequacy: ∀ executions, ∃ prophecy assignment. *)
module Pulse.Lib.Prophecy.Resolve

open Pulse.Lib.Pervasives
open Pulse.Lib.Prophecy

(** resolve p v f: Run atomic step f, resolve prophecy p to the result.
    Consumes prophecy_token p v. Produces pure (x == reveal v).
    
    Iris analogue: Resolve e1 e2 ()
    Pulse analogue of with_invariant: wraps stt_atomic, adds ghost semantics. *)
let resolve (#a:Type0)
    (p : prophecy_var a)
    (v : Ghost.erased a)
    (#opens:inames)
    (#pre:slprop)
    (#post: a -> slprop)
    (f : unit -> stt_atomic a #Observable opens pre (fun x -> post x))
  : stt_atomic a #Observable opens
      (Pulse.Lib.Core.op_Star_Star (prophecy_token p (Ghost.reveal v)) pre)
      (fun x -> Pulse.Lib.Core.op_Star_Star (post x) (pure (x == Ghost.reveal v)))
  = admit () // Trusted axiom. Sound by prophecy adequacy.
