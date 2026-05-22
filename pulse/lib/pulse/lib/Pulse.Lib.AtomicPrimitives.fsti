(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Atomic Primitives — the trusted kernel of atomic operations.

    This module is the ONLY place where as_atomic may appear.
    Each operation corresponds to a single Iris/HeapLang atomic step.

    HeapLang atomic steps (each individually atomic, no interleaving):
      - Load:  !l
      - Store: l <- v
      - Alloc: ref v
      - CAS:   CAS l expected new  (compare-and-swap)
      - FAA:   FAA l delta          (fetch-and-add, U32 only)

    These are OPAQUE axioms. The .fst provides a model implementation
    using as_atomic for type-checking, but clients depend only on
    the specs declared here. On real hardware, these map to:
      - Load/Store: MOV (aligned)
      - CAS:        LOCK CMPXCHG
      - FAA:        LOCK XADD
      - Alloc:      malloc

    All other files must compose these primitives rather than using
    as_atomic directly. *)
module Pulse.Lib.AtomicPrimitives
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32

(* ================================================================ *)
(* Conditional slprop (shared with Pulse.Lib.Primitives)            *)
(* ================================================================ *)

let cond b (p q:slprop) = if b then p else q

(* ================================================================ *)
(* Load — atomic read from a box                                    *)
(* HeapLang: !l                                                     *)
(* ================================================================ *)

val atomic_read (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_atomic a #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))

(* ================================================================ *)
(* Store — atomic write to a box                                    *)
(* HeapLang: l <- v                                                 *)
(* ================================================================ *)

val atomic_write (#a:Type0) (r : B.box a) (x : a) (#v : erased a)
  : stt_atomic unit #Observable emp_inames
    (B.pts_to r v) (fun _ -> B.pts_to r x)

(* ================================================================ *)
(* Alloc — atomic allocation of a box                               *)
(* HeapLang: ref v                                                  *)
(* ================================================================ *)

val atomic_alloc (#a:Type0) (x : a)
  : stt_atomic (B.box a) #Observable emp_inames
    emp (fun r -> B.pts_to r x)

(* ================================================================ *)
(* CAS — compare-and-swap (eqtype)                                  *)
(* HeapLang: CAS l expected new                                     *)
(* ================================================================ *)

val atomic_cas (#a:eqtype) (r : B.box a) (expected new_val : a) (#cur : erased a)
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))

(* ================================================================ *)
(* CAS — pointer equality variant (box_eq)                          *)
(* HeapLang: CAS l expected new  (on locations)                     *)
(* ================================================================ *)

val atomic_cas_box (#a:Type0) (r : B.box (B.box a))
    (expected new_val : B.box a) (#cur : erased (B.box a))
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))

(* ================================================================ *)
(* FAA — fetch-and-add on U32                                       *)
(* HeapLang: FAA l delta                                            *)
(* ================================================================ *)

val atomic_faa (r : B.box U32.t) (delta : U32.t) (#cur : erased U32.t)
  : stt_atomic U32.t #Observable emp_inames
    (B.pts_to r cur) (fun old -> B.pts_to r (U32.add_mod old delta) ** pure (old == reveal cur))

(* ================================================================ *)
(* Persistent read — load from a persistently-owned location        *)
(* HeapLang: !l  (where l ↦□ v)                                    *)
(* The proof requires ghost existential elimination, but the        *)
(* physical operation is a single load.                             *)
(* ================================================================ *)

let persistent_pts_to (#a:Type0) (r : B.box a) (v : a) : slprop =
  exists* (p:perm). B.pts_to r #p v

val atomic_read_persistent (#a:Type0) (r : B.box a) (#v : a)
  : stt_atomic a #Observable emp_inames
    (persistent_pts_to r v)
    (fun x -> persistent_pts_to r v ** pure (x == v))


val make_persistent (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_ghost unit emp_inames
    (B.pts_to r #p v) (fun _ -> persistent_pts_to r (reveal v))

val dup_persistent (#a:Type0) (r : B.box a) (#v : a)
  : stt_ghost unit emp_inames
    (persistent_pts_to r v) (fun _ -> persistent_pts_to r v ** persistent_pts_to r v)
