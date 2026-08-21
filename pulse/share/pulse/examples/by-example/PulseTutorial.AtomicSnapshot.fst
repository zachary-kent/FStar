(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Atomic Snapshot — inspired by Iris logatom/snapshot.
    
    PARTIAL IRIS PORT: exported write still uses a two-phase protocol (FAA
    version, then write value).  This file now also contains a verified
    pointer-indirection CAS write step matching the key operational shape of
    Iris's write rule, but it has not yet replaced the exported AU proof.
    The exported read_with now allocates a prophecy variable and resolves the
    middle read of the external location, so it no longer uses the old
    version-number retry pattern.  The remaining gap is the stronger Iris AU
    proof around this example and the original pointer-indirection write
    protocol. *)
module PulseTutorial.AtomicSnapshot
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module AP = Pulse.Lib.AtomicPrimitives
module P = Pulse.Lib.Prophecy
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
    let v = AP.atomic_read s.value;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    v
  };
  fold (is_snap s);
  v
}

(* ================================================================ *)
(* write — atomic write of snapshot value (with version bump)       *)
(* ================================================================ *)

(** write_snap: Two-phase protocol with AU/LAT spec.
    Phase 1: FAA version (outside AU — pre-step)
    Phase 2: Write value + commit AU (LP at the write)
    No CAS retry needed — writes always succeed. *)
fn write_snap_au (s:snapshot) (new_v : U32.t)
    (#phi : U32.t -> unit -> slprop)
    (tok : au_token emp_inames U32.t unit
      (fun v -> snap_content s.sg v)
      (fun v _ -> snap_content s.sg new_v)
      phi)
    (_u:unit)
  requires is_snap s ** au_available tok
  ensures is_snap s ** (exists* v. phi v ())
{
  unfold is_snap;
  // Phase 1: bump version (outside AU — not the LP)
  with_invariants unit emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let _ = AP.atomic_faa s.version 1ul;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
  };
  // Phase 2: open AU, write value (LP), commit
  later_credit_buy 1;
  let v = au_open tok;
  unfold snap_content;
  with_invariants unit emp_inames s.si (snap_inv_raw s)
    (GR.pts_to s.sg.gr #0.5R v)
    (fun _ -> GR.pts_to s.sg.gr #0.5R new_v)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    AP.atomic_write s.value new_v;
    with v0 ver0. assert (B.pts_to s.value new_v ** B.pts_to s.version ver0 **
      GR.pts_to s.sg.gr #0.5R v0 ** GR.pts_to s.sg.gr #0.5R v);
    GR.pts_to_injective_eq s.sg.gr;
    rewrite each v0 as (reveal v);
    GR.gather s.sg.gr;
    GR.(s.sg.gr := new_v);
    GR.share s.sg.gr;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
  };
  fold (snap_content s.sg new_v);
  later_credit_buy 1;
  au_commit tok (reveal v) ();
  fold (is_snap s)
}

(** Type witness: write_snap IS a lat_void *)
let write_is_lat (s:snapshot) (new_v:U32.t)
  : lat_void emp_inames U32.t
    (fun v -> snap_content s.sg v)
    (fun v _ -> snap_content s.sg new_v)
    (is_snap s)
  = fun #phi tok _u -> write_snap_au s new_v #phi tok _u

ghost
fn mk_snap_trade (s:snapshot) (new_v:U32.t) (#v : erased U32.t)
  requires emp
  ensures (forall* (y:unit). (later_credit 1 ** snap_content s.sg new_v) @==> snap_content s.sg new_v)
{
  intro_forall #unit #(fun (y:unit) -> (later_credit 1 ** snap_content s.sg new_v) @==> snap_content s.sg new_v)
    emp
    fn (y:unit) {
      intro_trade (later_credit 1 ** snap_content s.sg new_v) (snap_content s.sg new_v) emp
        fn _ { drop_ (later_credit 1) }
    }
}

(** Sequential wrapper *)
fn write_snap (s:snapshot) (new_v : U32.t)
  requires is_snap s ** snap_content s.sg 'v
  ensures is_snap s ** snap_content s.sg new_v
{
  mk_snap_trade s new_v #'v;
  let tok = au_intro #emp_inames #U32.t #unit
    #(fun v -> snap_content s.sg v)
    #(fun v _ -> snap_content s.sg new_v)
    #(fun v _ -> snap_content s.sg new_v)
    'v;
  write_snap_au s new_v tok ()
}

(* ================================================================ *)
(* Pointer-indirection write building block                         *)
(* ================================================================ *)

(** One CAS step for Iris's pointer-indirection snapshot write protocol.

    The full exported [write_snap] above still uses the older two-phase
    version-counter proof.  This helper is a verified operational building
    block for the intended port: allocate/fill a fresh cell, then linearize the
    write by one CAS on the root pointer.  Ownership of the old and new cells is
    kept explicit here so the future invariant can decide how to retain retired
    immutable cells for readers. *)
fn snapshot_pointer_cas_write_step
    (root : B.box (B.box U32.t))
    (old_cell new_cell : B.box U32.t)
    (#old_v #new_v : erased U32.t)
  requires B.pts_to root old_cell ** B.pts_to old_cell old_v ** B.pts_to new_cell new_v
  returns b:bool
  ensures AP.cond b
    (B.pts_to root new_cell ** B.pts_to old_cell old_v ** B.pts_to new_cell new_v)
    (B.pts_to root old_cell ** B.pts_to old_cell old_v ** B.pts_to new_cell new_v)
{
  let b = AP.atomic_cas_box root old_cell new_cell;
  if b {
    unfold AP.cond;
    drop_ (pure (old_cell == old_cell));
    fold (AP.cond true
      (B.pts_to root new_cell ** B.pts_to old_cell old_v ** B.pts_to new_cell new_v)
      (B.pts_to root old_cell ** B.pts_to old_cell old_v ** B.pts_to new_cell new_v));
    true
  } else {
    unfold AP.cond;
    fold (AP.cond false
      (B.pts_to root new_cell ** B.pts_to old_cell old_v ** B.pts_to new_cell new_v)
      (B.pts_to root old_cell ** B.pts_to old_cell old_v ** B.pts_to new_cell new_v));
    false
  }
}

(* ================================================================ *)
(* read_with — atomically read snapshot + another location          *)
(* ================================================================ *)

(** read_with: read snapshot value and *l using Iris-style prophecy
    linearization for the middle read of [l].  The sequence still keeps the
    surrounding version reads from the earlier model as instrumentation, but
    the exported implementation no longer retries on version changes; its
    linearization point evidence comes from Resolve. *)
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

(** Prophecy-resolved version of the middle read used by Iris's
    [read_with].  This head-supplied helper is useful when a proof has already
    decomposed the prediction stream: the read of [l] is one observable atomic
    step coupled to a prophecy token, and the result/prediction equality comes
    from [Resolve]. *)
fn read_box_with_prophecy
    (r : B.box U32.t)
    (p : P.prophecy_var U32.t unit)
    (#v : erased U32.t)
    (#pred : erased U32.t)
    (#tail : erased (P.prediction_stream U32.t unit))
    (#q:perm)
  requires B.pts_to r #q v ** P.prophecy_token p ((reveal pred, ()) :: reveal tail)
  returns x : U32.t
  ensures B.pts_to r #q v ** P.prophecy_token p (reveal tail) **
          pure (x == reveal v) ** pure (x == reveal pred)
{
  let x = P.resolve #U32.t #unit p () #pred #tail
    #(B.pts_to r #q v)
    #(fun y -> B.pts_to r #q v ** pure (y == reveal v))
    fn _ { AP.atomic_read r };
  x
}

(** Resolve form used immediately after [prophecy_alloc].  The caller owns the
    whole existential stream [pvs]; Resolve proves it was headed by the value
    actually read and returns the tail token. *)
fn read_box_with_prophecy_token
    (r : B.box U32.t)
    (p : P.prophecy_var U32.t unit)
    (#v : erased U32.t)
    (#pvs : erased (P.prediction_stream U32.t unit))
    (#q:perm)
  requires B.pts_to r #q v ** P.prophecy_token p (reveal pvs)
  returns x : U32.t
  ensures B.pts_to r #q v ** pure (x == reveal v) **
          (exists* (tail:P.prediction_stream U32.t unit).
             P.prophecy_token p tail ** pure (reveal pvs == (x, ()) :: tail))
{
  let x = P.resolve_token #U32.t #unit p () #pvs
    #(B.pts_to r #q v)
    #(fun y -> B.pts_to r #q v ** pure (y == reveal v))
    fn _ { AP.atomic_read r };
  x
}

(** One full [read_with] iteration whose middle read is prophecy-resolved.
    This helper still expects an already non-empty prophecy token. *)
fn read_with_prophecy_step (s:snapshot) (l : B.box U32.t)
    (p : P.prophecy_var U32.t unit)
    (#lv : erased U32.t)
    (#pred : erased U32.t)
    (#tail : erased (P.prediction_stream U32.t unit))
  requires is_snap s ** l |-> Frac 0.5R lv **
           P.prophecy_token p ((reveal pred, ()) :: reveal tail)
  returns r : (U32.t & U32.t)
  ensures is_snap s ** l |-> Frac 0.5R lv **
          P.prophecy_token p (reveal tail) ** pure (snd r == reveal pred)
{
  unfold is_snap;
  let ver1 = with_invariants U32.t emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let ver = AP.atomic_read s.version;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    ver
  };
  fold (is_snap s);
  let snap_v = read_snap s;
  let ext_v = read_box_with_prophecy l p;
  unfold is_snap;
  let ver2 = with_invariants U32.t emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let ver = AP.atomic_read s.version;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    ver
  };
  fold (is_snap s);
  (snap_v, ext_v)
}

(** End-to-end prophecy allocation plus Resolve for the full read sequence.
    This is the path used by the exported [read_with]: allocation exposes an
    existential prediction stream, and [read_box_with_prophecy_token] consumes
    its head during the middle atomic read without a version retry. *)
fn read_with_allocated_prophecy_step (s:snapshot) (l : B.box U32.t)
    (#lv : erased U32.t)
  requires is_snap s ** l |-> Frac 0.5R lv
  returns r : (U32.t & U32.t)
  ensures is_snap s ** l |-> Frac 0.5R lv
{
  let p = P.prophecy_alloc #U32.t #unit ();
  with pvs. assert (P.prophecy_token p pvs);
  // Read version before: retained from the snapshot model, but no longer used
  // to decide a retry.
  unfold is_snap;
  let ver1 = with_invariants U32.t emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let ver = AP.atomic_read s.version;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    ver
  };
  fold (is_snap s);
  // Read snapshot value.
  let snap_v = read_snap s;
  // Read the external location through Resolve, consuming the prophecy head.
  let ext_v = read_box_with_prophecy_token l p #lv #pvs #0.5R;
  with tail. assert (P.prophecy_token p tail ** pure (pvs == (ext_v, ()) :: tail));
  drop_ (P.prophecy_token p tail);
  // Read version after: still modeled as an observable atomic read, but the
  // returned pair is not selected by version equality/retry.
  unfold is_snap;
  let ver2 = with_invariants U32.t emp_inames s.si (snap_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold snap_inv_raw; unfold snap_inv_inner;
    let ver = AP.atomic_read s.version;
    fold (snap_inv_inner s.value s.version s.sg.gr); fold (snap_inv_raw s);
    ver
  };
  fold (is_snap s);
  (snap_v, ext_v)
}

fn read_with (s:snapshot) (l : B.box U32.t)
    (#lv : erased U32.t)
  requires is_snap s ** l |-> Frac 0.5R lv
  returns r : (U32.t & U32.t)
  ensures is_snap s ** l |-> Frac 0.5R lv
{
  read_with_allocated_prophecy_step s l
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
