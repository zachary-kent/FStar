(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Generic atomic primitives needed by the Treiber-stack LAT example.

    Pulse.Lib.Primitives already provides the U32 box atomics used by the
    counter examples.  This module deliberately keeps only the generic box
    operations needed by Treiber: load, allocation, and pointer compare-and-swap.

    The pointer CAS is the primitive boundary: it specifies the single HeapLang
    CAS step on a location that stores a boxed pointer.  We do not expose a
    standalone decidable equality operation for boxes, since upstream boxes are
    intentionally [noeq]. *)
module Pulse.Lib.AtomicPrimitives
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module P = Pulse.Lib.Primitives

(* Generic box load: HeapLang !l. *)
val atomic_read (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_atomic a #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))

(* Generic box allocation: HeapLang ref v. *)
val atomic_alloc (#a:Type0) (x : a)
  : stt_atomic (B.box a) #Observable emp_inames
    emp (fun r -> B.pts_to r x)

(* Pointer CAS on boxed locations: HeapLang CAS l expected new. *)
val atomic_cas_box (#a:Type0) (r : B.box (B.box a))
    (expected new_val : B.box a) (#cur : erased (B.box a))
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> P.cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                       (B.pts_to r cur))
