(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Atomic Primitives — model implementation.

    This file provides a SEQUENTIAL MODEL of atomic operations using
    as_atomic. It is used only for F* type-checking.
    On real hardware, these operations are implemented by atomic
    machine instructions (LOCK CMPXCHG, LOCK XADD, etc.).

    The trusted interface is in .fsti — clients depend on those
    opaque specs, not on this implementation. *)
module Pulse.Lib.AtomicPrimitives
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32

(* ================================================================ *)
(* Load — atomic read from a box                                    *)
(* HeapLang: !l                                                     *)
(* ================================================================ *)

fn atomic_read_impl (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  preserves r |-> Frac p v
  returns x : a
  ensures rewrites_to x (reveal v)
{ B.op_Bang r }

let atomic_read (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  : stt_atomic a #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_read_impl r #v #p)

(* ================================================================ *)
(* Store — atomic write to a box                                    *)
(* HeapLang: l <- v                                                 *)
(* ================================================================ *)

fn atomic_write_impl (#a:Type0) (r : B.box a) (x : a) (#v : erased a)
  requires r |-> v
  ensures r |-> x
{ B.op_Colon_Equals r x }

let atomic_write (#a:Type0) (r : B.box a) (x : a) (#v : erased a)
  : stt_atomic unit #Observable emp_inames
    (B.pts_to r v) (fun _ -> B.pts_to r x)
  = Pulse.Lib.Core.as_atomic _ _ (atomic_write_impl r x #v)

(* ================================================================ *)
(* Alloc — atomic allocation of a box                               *)
(* HeapLang: ref v                                                  *)
(* ================================================================ *)

fn atomic_alloc_impl (#a:Type0) (x : a)
  requires emp
  returns r : B.box a
  ensures r |-> x
{ B.alloc x }

let atomic_alloc (#a:Type0) (x : a)
  : stt_atomic (B.box a) #Observable emp_inames
    emp (fun r -> B.pts_to r x)
  = Pulse.Lib.Core.as_atomic _ _ (atomic_alloc_impl x)

(* ================================================================ *)
(* CAS — compare-and-swap (eqtype, model implementation)            *)
(* ================================================================ *)

fn atomic_cas_impl (#a:eqtype) (r : B.box a) (expected new_val : a) (#cur : erased a)
  requires r |-> cur
  returns b : bool
  ensures cond b (r |-> new_val ** pure (reveal cur == expected))
                 (r |-> cur)
{
  let v = B.op_Bang r;
  if (v = expected) {
    B.op_Colon_Equals r new_val;
    fold (cond true (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    true
  } else {
    fold (cond false (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    false
  }
}

let atomic_cas (#a:eqtype) (r : B.box a) (expected new_val : a) (#cur : erased a)
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_cas_impl r expected new_val #cur)

(* ================================================================ *)
(* CAS — pointer equality variant (box_eq)                          *)
(* ================================================================ *)

fn atomic_cas_box_impl (#a:Type0) (r : B.box (B.box a))
    (expected new_val : B.box a) (#cur : erased (B.box a))
  requires r |-> cur
  returns b : bool
  ensures cond b (r |-> new_val ** pure (reveal cur == expected))
                 (r |-> cur)
{
  let v = B.op_Bang r;
  if (B.box_eq v expected) {
    B.op_Colon_Equals r new_val;
    fold (cond true (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    true
  } else {
    fold (cond false (r |-> new_val ** pure (reveal cur == expected)) (r |-> cur));
    false
  }
}

let atomic_cas_box (#a:Type0) (r : B.box (B.box a))
    (expected new_val : B.box a) (#cur : erased (B.box a))
  : stt_atomic bool #Observable emp_inames
    (B.pts_to r cur)
    (fun b -> cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                     (B.pts_to r cur))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_cas_box_impl r expected new_val #cur)

(* ================================================================ *)
(* FAA — fetch-and-add on a box U32.t                               *)
(* HeapLang: FAA l delta                                            *)
(* ================================================================ *)

fn atomic_faa_impl (r : B.box U32.t) (delta : U32.t) (#cur : erased U32.t)
  requires r |-> cur
  returns old : U32.t
  ensures r |-> U32.add_mod old delta ** pure (old == reveal cur)
{
  let old = B.op_Bang r;
  B.op_Colon_Equals r (U32.add_mod old delta);
  old
}

let atomic_faa (r : B.box U32.t) (delta : U32.t) (#cur : erased U32.t)
  : stt_atomic U32.t #Observable emp_inames
    (B.pts_to r cur) (fun old -> B.pts_to r (U32.add_mod old delta) ** pure (old == reveal cur))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_faa_impl r delta #cur)

(* Persistent read: unfold existential, read, refold *)
fn atomic_read_persistent_impl (#a:Type0) (r : B.box a) (#v : a)
  requires persistent_pts_to r v
  returns x : a
  ensures persistent_pts_to r v ** pure (x == v)
{
  unfold persistent_pts_to;
  with p. assert (B.pts_to r #p v);
  B.share r;
  let x = B.op_Bang r;
  B.gather r;
  fold (persistent_pts_to r v);
  x
}

let atomic_read_persistent (#a:Type0) (r : B.box a) (#v : a)
  : stt_atomic a #Observable emp_inames
    (persistent_pts_to r v) (fun x -> persistent_pts_to r v ** pure (x == v))
  = Pulse.Lib.Core.as_atomic _ _ (atomic_read_persistent_impl r #v)
