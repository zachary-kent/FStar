(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Seqlock, ported from the Iris development in /tmp/pers-impl/seqlock.v.

    Phase 1 contains the shared state predicates and the non-atomic constructor.
    Later phases add snapshot_copy, write, and read with logically-atomic specs. *)
module PulseTutorial.Seqlock
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.SeqlockHistory
open Pulse.Lib.MonotonicGhostRef
module A = Pulse.Lib.Array.PtsTo
module Arr = Pulse.Lib.Array
module MGR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module List = FStar.List.Tot
module SZ = FStar.SizeT
open FStar.List.Tot { (@) }

(* The element type.  We keep it concrete in this port; the predicates below
   isolate the choice so later generalisation is mechanical. *)
type val_t = int

(* The big_atomic handle: (version_cell, data_array). *)
type big_atomic = ref nat & array val_t

(* Invariant namespace tag for documentation; the allocated invariant name is
   tracked separately by [is_seqlock]. *)
let seqlockN_tag : string = "PulseTutorial.Seqlock"

(* [history] is list-based, while Pulse array ownership is sequence-based. *)
let snapshot_of_seq (s:Seq.seq val_t) : list val_t = Seq.seq_to_list s
let seq_of_snapshot (vs:list val_t) : Seq.seq val_t = Seq.seq_of_list vs

let rec last_opt (#a:Type0) (xs:list a) : Tot (option a) =
  match xs with
  | [] -> None
  | x::[] -> Some x
  | _::tl -> last_opt tl

(* Monotone ghost reference for natural versions. *)
let mono_nat_increases : FStar.Preorder.preorder nat = fun (x:nat) (y:nat) -> b2t (x <= y)

[@@pulse_unfold]
let mono_nat_auth (gver:MGR.mref mono_nat_increases) (q:perm) (ver:nat) : slprop =
  MGR.pts_to gver #q ver

(* Value abstraction visible to clients: half of the history authority and a
   witness that the latest snapshot is [vs]. *)
let value (gh:gname val_t) (vs:list val_t) : slprop =
  exists* (h:history val_t).
    history_auth gh (1.0R /. 2.0R) h **
    pure (last_opt h == Some vs)

(* The big invariant content: conditional on parity of the physical version. *)
let seqlock_inv (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
                (version:ref nat) (data:array val_t) (len:nat)
  : slprop =
  exists* (ver:nat) (h:history val_t) (vs:list val_t).
    version |-> ver **
    pure (List.length vs == len /\ List.length h == 1 + ver / 2) **
    (if ver % 2 = 0 then
       history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver 1.0R ver **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs)
     else
       history_auth gh (1.0R /. 4.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) ver **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs))

(* Public predicate: holding an [is_seqlock] means the invariant has been
   allocated for the handle. *)
let is_seqlock (v:big_atomic) (gh:gname val_t) (n:nat) : slprop =
  exists* (gver:MGR.mref mono_nat_increases) (i:iname).
    inv i (seqlock_inv gver gh (fst v) (snd v) n)

fn new_big_atomic (n:SZ.t) (src:larray val_t (SZ.v n)) (#dq:perm)
    (#vs:erased (Seq.seq val_t))
  requires A.pts_to src #dq vs ** pure (Seq.length vs == SZ.v n /\ SZ.v n > 0)
  returns r : (big_atomic & gname val_t)
  ensures
    A.pts_to src #dq vs **
    is_seqlock (fst r) (snd r) (SZ.v n) **
    value (snd r) (snapshot_of_seq (reveal vs))
{
  let version = Pulse.Lib.Reference.alloc #nat 0;
  let data = A.alloc #val_t 0 n;
  Arr.memcpy n src data;

  let snap : erased (list val_t) = hide (snapshot_of_seq (reveal vs));
  let h0 : erased (history val_t) = hide [reveal snap];
  let gh = history_alloc (reveal h0);
  history_share gh;

  let gver = MGR.alloc #nat #mono_nat_increases 0;

  Seq.lemma_seq_of_seq_to_list (reveal vs);
  rewrite (A.pts_to data (reveal vs)) as (A.pts_to data (seq_of_snapshot (reveal snap)));

  fold (value gh (reveal snap));
  fold (mono_nat_auth gver 1.0R 0);
  fold (seqlock_inv gver gh version data (SZ.v n));
  let i = new_invariant (seqlock_inv gver gh version data (SZ.v n));
  let handle : big_atomic = (version, data);
  rewrite (inv i (seqlock_inv gver gh version data (SZ.v n)))
    as (inv i (seqlock_inv gver gh (fst handle) (snd handle) (SZ.v n)));
  fold (is_seqlock handle gh (SZ.v n));
  rewrite (value gh (reveal snap)) as (value gh (snapshot_of_seq (reveal vs)));
  (handle, gh)
}
