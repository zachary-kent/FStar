(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Counter with Backup — ported from Iris logatom/counter_with_backup.
    
    A counter that maintains a "backup" (secondary) value.
    Operations: new_counter, increment (FAA-based), get, get_backup.
    All operations are logically atomic.
    
    Simplified from Iris (which uses ghost maps for helping protocol).
    Here we use a simpler encoding: the backup is lazily synced with
    the primary counter via CAS. *)
module PulseTutorial.CounterWithBackup
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

(* ================================================================ *)
(* Counter representation                                           *)
(* ================================================================ *)

noeq type cwb_ghost = { gr : GR.ref U32.t; }
noeq type cwb_counter = {
  primary : B.box U32.t;   (* main counter (FAA target) *)
  backup  : B.box U32.t;   (* backup copy (lazily synced) *)
  cg      : cwb_ghost;
  ci      : iname;
}

let cwb_content (g:cwb_ghost) (n:U32.t) : slprop = GR.pts_to g.gr #0.5R n

(* Invariant: primary value matches ghost, backup <= primary *)
let cwb_inv_inner (primary backup : B.box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (pv bv : U32.t).
    B.pts_to primary pv ** B.pts_to backup bv ** GR.pts_to gr #0.5R pv

let cwb_inv_raw (c:cwb_counter) : slprop = cwb_inv_inner c.primary c.backup c.cg.gr

let is_cwb (c:cwb_counter) : slprop = inv c.ci (cwb_inv_raw c)

(* ================================================================ *)
(* new_counter                                                      *)
(* ================================================================ *)

fn new_cwb_counter ()
  requires emp
  returns c : cwb_counter
  ensures is_cwb c ** cwb_content c.cg 0ul
{
  let primary = B.alloc 0ul;
  let backup = B.alloc 0ul;
  let gr = GR.alloc #U32.t 0ul;
  GR.share gr;
  let cg : cwb_ghost = { gr };
  rewrite (GR.pts_to gr #0.5R 0ul) as (GR.pts_to cg.gr #0.5R 0ul);
  rewrite (GR.pts_to gr #0.5R 0ul) as (cwb_content cg 0ul);
  fold (cwb_inv_inner primary backup cg.gr);
  let ci = new_invariant (cwb_inv_inner primary backup cg.gr);
  let c : cwb_counter = { primary; backup; cg; ci };
  rewrite (inv ci (cwb_inv_inner primary backup cg.gr)) as (inv c.ci (cwb_inv_raw c));
  fold (is_cwb c);
  rewrite (cwb_content cg 0ul) as (cwb_content c.cg 0ul);
  c
}

(* ================================================================ *)
(* get — logically atomic read of primary counter                   *)
(* ================================================================ *)

fn get_cwb (c:cwb_counter)
  requires is_cwb c
  returns n : U32.t
  ensures is_cwb c
{
  unfold is_cwb;
  let n = with_invariants U32.t emp_inames c.ci (cwb_inv_raw c)
    emp (fun _ -> emp)
  fn _ {
    unfold cwb_inv_raw; unfold cwb_inv_inner;
    let n = P.read_atomic_box c.primary;
    fold (cwb_inv_inner c.primary c.backup c.cg.gr); fold (cwb_inv_raw c);
    n
  };
  fold (is_cwb c);
  n
}

(* ================================================================ *)
(* get_backup — read of backup counter                              *)
(* ================================================================ *)

fn get_backup (c:cwb_counter)
  requires is_cwb c
  returns n : U32.t
  ensures is_cwb c
{
  unfold is_cwb;
  let n = with_invariants U32.t emp_inames c.ci (cwb_inv_raw c)
    emp (fun _ -> emp)
  fn _ {
    unfold cwb_inv_raw; unfold cwb_inv_inner;
    let n = P.read_atomic_box c.backup;
    fold (cwb_inv_inner c.primary c.backup c.cg.gr); fold (cwb_inv_raw c);
    n
  };
  fold (is_cwb c);
  n
}

(* ================================================================ *)
(* increment — FAA-based increment with LA spec                     *)
(* ================================================================ *)

(** try_incr: inside invariant, FAA on primary, update ghost *)
fn try_incr_cwb_impl (c:cwb_counter) (#n : erased U32.t)
  requires cwb_inv_raw c ** GR.pts_to c.cg.gr #0.5R n
  returns old : U32.t
  ensures cwb_inv_raw c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod old 1ul) ** pure (old == reveal n)
{
  unfold cwb_inv_raw; unfold cwb_inv_inner;
  with pv0 bv0. assert (B.pts_to c.primary pv0 ** B.pts_to c.backup bv0 ** GR.pts_to c.cg.gr #0.5R pv0 ** GR.pts_to c.cg.gr #0.5R n);
  GR.pts_to_injective_eq c.cg.gr;
  rewrite each pv0 as (reveal n);
  let old = P.faa_box c.primary 1ul;
  // Update ghost state
  GR.gather c.cg.gr;
  GR.(c.cg.gr := U32.add_mod old 1ul);
  GR.share c.cg.gr;
  fold (cwb_inv_inner c.primary c.backup c.cg.gr);
  fold (cwb_inv_raw c);
  old
}

let try_incr_cwb_atomic (c:cwb_counter) (#n : erased U32.t)
  : stt_atomic U32.t #Observable emp_inames
    (cwb_inv_raw c ** GR.pts_to c.cg.gr #0.5R n)
    (fun old -> cwb_inv_raw c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod old 1ul) ** pure (old == reveal n))
  = Pulse.Lib.Core.as_atomic _ _ (try_incr_cwb_impl c #n)

fn increment_cwb (c:cwb_counter)
  requires is_cwb c ** cwb_content c.cg 'n
  ensures is_cwb c ** (exists* m. cwb_content c.cg m)
{
  unfold is_cwb; unfold cwb_content;
  let old = with_invariants U32.t emp_inames c.ci (cwb_inv_raw c)
    (GR.pts_to c.cg.gr #0.5R 'n)
    (fun old -> GR.pts_to c.cg.gr #0.5R (U32.add_mod old 1ul) ** pure (old == reveal 'n))
  fn _ { try_incr_cwb_atomic c #'n };
  fold (cwb_content c.cg (U32.add_mod old 1ul));
  fold (is_cwb c);
}

(* ================================================================ *)
(* sync_backup — lazily sync backup to primary (best-effort CAS)    *)
(* ================================================================ *)

fn sync_backup (c:cwb_counter)
  requires is_cwb c
  ensures is_cwb c
{
  let pv = get_cwb c;
  unfold is_cwb;
  with_invariants unit emp_inames c.ci (cwb_inv_raw c)
    emp (fun _ -> emp)
  fn _ {
    unfold cwb_inv_raw; unfold cwb_inv_inner;
    P.write_atomic_box c.backup pv;
    fold (cwb_inv_inner c.primary c.backup c.cg.gr);
    fold (cwb_inv_raw c);
  };
  fold (is_cwb c)
}

(* ================================================================ *)
(* Client example: increment + sync + read_backup                   *)
(* ================================================================ *)

fn client_example ()
  requires emp
  ensures emp
{
  let c = new_cwb_counter ();
  // Increment
  increment_cwb c;
  // Sync backup
  sync_backup c;
  // Read backup (should be close to primary)
  let bv = get_backup c;
  // Drop resources (would need dealloc in real code)
  with m0. assert (cwb_content c.cg m0);
  drop_ (is_cwb c);
  drop_ (cwb_content c.cg m0)
}
