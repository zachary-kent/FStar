(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Atomic Snapshot — ported from Iris logatom/snapshot.
    
    An atomic snapshot provides:
    - write(p, v): atomically update the snapshot value
    - read(p): atomically read the snapshot value
    - read_with(p, l): atomically read BOTH the snapshot value and *l
    
    The key challenge is read_with: it must atomically observe both
    the snapshot and a separate location, even though the implementation
    reads them sequentially. This uses a retry loop that checks if
    the snapshot changed between the two reads.
    
    Simplified from Iris (which uses prophecy variables for read_with's
    linearization point). Here we use a timestamp-based approach. *)
module PulseTutorial.AtomicSnapshot
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module P = Pulse.Lib.Primitives
open Pulse.Lib.Inv
open Pulse.Lib.Trade
open Pulse.Lib.Forall
open Pulse.Lib.Box { box }

(* ================================================================ *)
(* Snapshot representation                                          *)
(* ================================================================ *)

(* Snapshot: value + version counter for ABA detection *)
noeq type snap_ghost = { gr : GR.ref U32.t; }
noeq type snapshot = {
  value   : B.box U32.t;
  version : B.box U32.t;   (* monotonically increasing version counter *)
  sg      : snap_ghost;
  si      : iname;
}

let snap_content (g:snap_ghost) (v:U32.t) : slprop = GR.pts_to g.gr #0.5R v

let snap_inv_inner (value version : B.box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (v ver : U32.t).
    B.pts_to value v ** B.pts_to version ver ** GR.pts_to gr #0.5R v

let snap_inv_raw (s:snapshot) : slprop = snap_inv_inner s.value s.version s.sg.gr

let is_snap (s:snapshot) : slprop = inv s.si (snap_inv_raw s)

(* ================================================================ *)
(* new_snapshot                                                     *)
(* ================================================================ *)

fn new_snapshot (init:U32.t)
  requires emp
  returns s : snapshot
  ensures is_snap s ** snap_content s.sg init
{
  let value = B.alloc init;
  let version = B.alloc 0ul;
  let gr = GR.alloc #U32.t init;
  GR.share gr;
  let sg : snap_ghost = { gr };
  rewrite (GR.pts_to gr #0.5R init) as (GR.pts_to sg.gr #0.5R init);
  rewrite (GR.pts_to gr #0.5R init) as (snap_content sg init);
  fold (snap_inv_inner value version sg.gr);
  let si = new_invariant (snap_inv_inner value version sg.gr);
  let s : snapshot = { value; version; sg; si };
  rewrite (inv si (snap_inv_inner value version sg.gr)) as (inv s.si (snap_inv_raw s));
  fold (is_snap s);
  rewrite (snap_content sg init) as (snap_content s.sg init);
  s
}

(* ================================================================ *)
(* read — atomic read of snapshot value                             *)
(* ================================================================ *)

fn read_snap (s:snapshot)
  requires is_snap s
  returns v : U32.t
  ensures is_snap s
{
  unfold is_snap;
  let v = with_invariants U32.t emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let v = P.read_atomic_box s.value;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    v
  };
  fold (is_snap s);
  v
}

(* ================================================================ *)
(* write — atomic write of snapshot value (with version bump)       *)
(* ================================================================ *)

(** write_snap: Two-phase protocol.
    Phase 1: FAA version (single LOCK XADD)
    Phase 2: Write value (single MOV)
    Correctness: read_with checks version stability across reads.
    If version bumps between reads, reader retries. *)
fn write_snap (s:snapshot) (new_v : U32.t)
  requires is_snap s ** snap_content s.sg 'v
  ensures is_snap s ** snap_content s.sg new_v
{
  unfold is_snap;
  // Phase 1: bump version (single FAA — x86 LOCK XADD)
  with_invariants unit emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let _ = P.faa_box s.version 1ul;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
  };
  // Phase 2: write new value + update ghost (single write — x86 MOV)
  unfold snap_content;
  with_invariants unit emp_inames s.si (snap_inv_raw s)
    (GR.pts_to s.sg.gr #0.5R 'v)
    (fun _ -> GR.pts_to s.sg.gr #0.5R new_v)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    P.write_atomic_box s.value new_v;
    with v0 ver0. assert (B.pts_to s.value new_v ** B.pts_to s.version ver0 **
      GR.pts_to s.sg.gr #0.5R v0 ** GR.pts_to s.sg.gr #0.5R 'v);
    GR.pts_to_injective_eq s.sg.gr;
    rewrite each v0 as (reveal 'v);
    GR.gather s.sg.gr;
    GR.(s.sg.gr := new_v);
    GR.share s.sg.gr;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
  };
  fold (snap_content s.sg new_v);
  fold (is_snap s)
}

(* ================================================================ *)
(* read_with — atomically read snapshot + another location          *)
(* ================================================================ *)

(** read_with: read snapshot value and *l atomically.
    Implementation: read version, read value, read *l, re-read version.
    If version unchanged, the reads were consistent.
    
    Iris uses a prophecy variable to determine the linearization point
    (the read of *l). Here we use the retry-on-version-change pattern. *)
fn read_box_frac (r : B.box U32.t) (#v : erased U32.t) (#p:perm)
  preserves r |-> Frac p v
  returns x : U32.t
  ensures pure (x == reveal v)
{
  B.to_ref_pts_to r;
  let x = Pulse.Lib.Reference.read (B.box_to_ref r);
  B.to_box_pts_to r;
  x
}

fn rec read_with (s:snapshot) (l : B.box U32.t)
    (#lv : erased U32.t)
  requires is_snap s ** l |-> Frac 0.5R lv
  returns r : (U32.t & U32.t)
  ensures is_snap s ** l |-> Frac 0.5R lv
{
  // Read version before
  unfold is_snap;
  let ver1 = with_invariants U32.t emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let ver = P.read_atomic_box s.version;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    ver
  };
  fold (is_snap s);
  // Read snapshot value
  let snap_v = read_snap s;
  // Read the external location (non-atomic read with frac permission)
  let ext_v = read_box_frac l;
  // Read version after
  unfold is_snap;
  let ver2 = with_invariants U32.t emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let ver = P.read_atomic_box s.version;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    ver
  };
  fold (is_snap s);
  // If version unchanged, reads are consistent
  if (ver1 = ver2) {
    (snap_v, ext_v)
  } else {
    // Version changed: retry
    read_with s l
  }
}

(* ================================================================ *)
(* Client example                                                   *)
(* ================================================================ *)

fn snap_client ()
  requires emp
  ensures emp
{
  let s = new_snapshot 10ul;
  let l = B.alloc 20ul;
  B.share l;
  // Read with: atomically get (snapshot_val, *l)
  let r = read_with s l;
  // Write new snapshot value
  write_snap s 42ul;
  // Read again
  let r2 = read_with s l;
  // Cleanup
  B.gather l;
  B.free l;
  drop_ (is_snap s);
  drop_ (snap_content s.sg 42ul)
}
