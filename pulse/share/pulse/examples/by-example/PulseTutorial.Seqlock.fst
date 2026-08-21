(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(**
  Ordinary multiword seqlock concrete baseline.

  This module exposes the ordinary non-helping seqlock implementation with
  allocation/length specs only.
*)
module PulseTutorial.Seqlock
#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module B = Pulse.Lib.Box
module V = Pulse.Lib.Vec
module AP = Pulse.Lib.AtomicPrimitives
module SM = Pulse.Lib.SeqMatch
module SMT = Pulse.Lib.SeqMatch.Util
module Trade = Pulse.Lib.Trade
module SZ = FStar.SizeT
module U32 = FStar.UInt32
open FStar.SizeT
module L = FStar.List.Tot
open Pulse.Lib.Inv
module GR = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
open FStar.Preorder

(*
 * History-ghost slice (additive, private; not yet wired into the seqlock
 * invariant).  This is the Pulse analogue of the Iris auth/fragment history
 * CMRA: an authoritative (version-index, current-values) pair carried at
 * fractional permission, plus persistent (duplicable) fragments at past
 * indices.  Backed by Pulse.Lib.MonotonicGhostRef with a preorder that says
 * either the index strictly grew or the index is unchanged and the value
 * sequence is identical.  Same-index two-fragment agreement falls out of
 * `snapshots_related`, since both disjuncts collapse to value equality.
 *
 * This is approach (A) of pulse-history-design.md: ~zero new PCM proofs.
 * If a more Iris-faithful gmap-of-agree(seq U32.t) PCM is later required,
 * these wrappers' signatures are the migration boundary.
 *)

let hist_state : Type0 = nat & Seq.seq U32.t

let hist_le (s0 s1:hist_state) : prop =
  fst s0 <= fst s1 /\ (fst s0 == fst s1 ==> snd s0 == snd s1)

let hist_le_is_preorder ()
  : Lemma ((forall x. hist_le x x) /\
           (forall x y z. hist_le x y /\ hist_le y z ==> hist_le x z))
  = ()

let hist_pre : preorder hist_state =
  hist_le_is_preorder ();
  hist_le

let hist_ref : Type0 = MR.mref hist_pre

let hist_auth (r:hist_ref) (q:perm) (i:nat) (vs:Seq.seq U32.t) : slprop =
  MR.pts_to r #q (i, vs)

let hist_frag (r:hist_ref) (i:nat) (vs:Seq.seq U32.t) : slprop =
  MR.snapshot r (i, vs)

ghost fn alloc_hist (vs0:Seq.seq U32.t)
  requires emp
  returns r : hist_ref
  ensures (exists* (i:nat). hist_auth r 1.0R i vs0 ** pure (i == 0))
{
  let z : nat = 0;
  let r = MR.alloc #hist_state #hist_pre (z, vs0);
  fold (hist_auth r 1.0R z vs0);
  r
}

ghost fn hist_auth_share (r:hist_ref) (#q #f #g:perm) (#i:nat) (#vs:erased (Seq.seq U32.t))
  requires hist_auth r q i vs ** pure (q == f +. g)
  ensures hist_auth r f i vs ** hist_auth r g i vs
{
  unfold (hist_auth r q i vs);
  MR.share #_ #_ r #_ #_ #f #g;
  fold (hist_auth r f i vs);
  fold (hist_auth r g i vs)
}

ghost fn hist_auth_gather (r:hist_ref) (#f #g:perm) (#i:nat) (#vs:erased (Seq.seq U32.t))
  requires hist_auth r f i vs ** hist_auth r g i vs
  ensures hist_auth r (f +. g) i vs
{
  unfold (hist_auth r f i vs);
  unfold (hist_auth r g i vs);
  MR.gather #_ #_ r #_ #f #g;
  fold (hist_auth r (f +. g) i vs)
}

ghost fn hist_take_frag (r:hist_ref) (#q:perm) (#i:nat) (#vs:erased (Seq.seq U32.t))
  preserves hist_auth r q i vs
  ensures hist_frag r i vs
{
  unfold (hist_auth r q i vs);
  MR.take_snapshot r (reveal i, reveal vs);
  fold (hist_auth r q i vs);
  fold (hist_frag r i vs)
}

ghost fn hist_dup_frag (r:hist_ref) (#i:nat) (#vs:erased (Seq.seq U32.t))
  preserves hist_frag r i vs
  ensures hist_frag r i vs
{
  unfold (hist_frag r i vs);
  dup (MR.snapshot r (reveal i, reveal vs)) ();
  fold (hist_frag r i vs);
  fold (hist_frag r i vs)
}

(* Two fragments at the same version index agree on the value sequence.
   This is the Iris `to_agree_op_inv_L` analogue used in §7 of the read proof. *)
ghost fn hist_frag_agree (r:hist_ref)
                         (#i:nat) (#vs0 #vs1:erased (Seq.seq U32.t))
  preserves hist_frag r i vs0 ** hist_frag r i vs1
  ensures pure (vs0 == vs1)
{
  unfold (hist_frag r i vs0);
  unfold (hist_frag r i vs1);
  MR.snapshots_related #_ #_ r #(reveal i, reveal vs0) #(reveal i, reveal vs1);
  fold (hist_frag r i vs0);
  fold (hist_frag r i vs1)
}

(* Auth+frag agreement / monotonicity:  a fragment's index never overtakes
   the authoritative index, and equal indices force equal contents.
   This is `history_auth_frag_agree` + version monotonicity in one shot. *)
ghost fn hist_frag_le (r:hist_ref)
                      (#q:perm) (#i #j:nat)
                      (#vs #ws:erased (Seq.seq U32.t))
  preserves hist_auth r q j ws ** hist_frag r i vs
  ensures pure (i <= j /\ (i == j ==> vs == ws))
{
  unfold (hist_auth r q j ws);
  unfold (hist_frag r i vs);
  MR.recall_snapshot r;
  fold (hist_auth r q j ws);
  fold (hist_frag r i vs)
}

(* Authoritative publish step: at full permission, advance the index and
   replace the value sequence (Iris `history_auth_update`).  The fresh
   fragment can be minted with `hist_take_frag` afterwards. *)
ghost fn hist_publish (r:hist_ref) (#i:nat) (#vs:erased (Seq.seq U32.t))
                      (ws:Seq.seq U32.t)
  requires hist_auth r 1.0R i vs
  ensures hist_auth r 1.0R (i + 1) ws
{
  unfold (hist_auth r 1.0R i vs);
  let j : nat = i + 1;
  MR.update r (j, ws);
  fold (hist_auth r 1.0R j ws);
  rewrite (hist_auth r 1.0R j ws) as (hist_auth r 1.0R (i + 1) ws)
}

(*
 * Write-first ghost substrate.
 *
 * The client-visible abstract content is now defined directly on top of
 * the history ghost: `seq_content sg vs` is the half-perm authoritative
 * history entry at some (existentially quantified) index whose value
 * sequence is `vs`.  This is the Pulse analogue of Iris `value γ vs`
 * defined as `own γ (◯E vs)` carved out of the history CMRA.  Folding
 * `hist_ref` into `seq_ghost` removes the separate `content_gr` ref
 * entirely; the writer LP will later mint the matching `hist_frag` at
 * publish time without a second ghost migration.
 *
 * `cur_gr` (ghost mirror of physical cells) and `writer_gr` (exclusion
 * token) are unchanged.
 *)

noeq type seq_ghost = {
  hist       : hist_ref;
  cur_gr     : GR.ref (Seq.seq U32.t);
  writer_gr  : GR.ref unit;
}

let seq_content (sg:seq_ghost) (vs:Seq.seq U32.t) : slprop =
  exists* (i:nat). hist_auth sg.hist 0.5R i vs

let seq_cur_half (sg:seq_ghost) (vs:Seq.seq U32.t) : slprop =
  GR.pts_to sg.cur_gr #0.5R vs

let writer_token (sg:seq_ghost) : slprop =
  GR.pts_to sg.writer_gr #1.0R ()

(* Resources the writer privately owns while holding the (future) CAS lock. *)
let writer_owned (sg:seq_ghost) (vs:Seq.seq U32.t) : slprop =
  writer_token sg ** seq_content sg vs ** seq_cur_half sg vs

(* Split a full-perm authoritative history into two `seq_content` halves. *)
ghost fn seq_content_share (sg:seq_ghost)
                           (#i:erased nat) (#vs:erased (Seq.seq U32.t))
  requires hist_auth sg.hist 1.0R i vs
  ensures seq_content sg vs ** seq_content sg vs
{
  hist_auth_share sg.hist #1.0R #0.5R #0.5R #i #vs;
  fold (seq_content sg vs);
  fold (seq_content sg vs)
}

ghost fn seq_content_agree (sg:seq_ghost)
                           (#vs0 #vs1:erased (Seq.seq U32.t))
  preserves seq_content sg vs0 ** seq_content sg vs1
  ensures pure (vs0 == vs1)
{
  unfold (seq_content sg vs0);
  unfold (seq_content sg vs1);
  with i0. assert (hist_auth sg.hist 0.5R i0 vs0);
  with i1. assert (hist_auth sg.hist 0.5R i1 vs1);
  hist_take_frag sg.hist #0.5R #i0 #vs0;
  hist_frag_le sg.hist #0.5R #i0 #i1 #vs0 #vs1;
  hist_take_frag sg.hist #0.5R #i1 #vs1;
  hist_frag_le sg.hist #0.5R #i1 #i0 #vs1 #vs0;
  drop_ (hist_frag sg.hist i0 vs0);
  drop_ (hist_frag sg.hist i1 vs1);
  fold (seq_content sg vs0);
  fold (seq_content sg vs1)
}

(* Gather two `seq_content` halves back into a full-perm authoritative
   history entry, simultaneously witnessing that the two value sequences
   agree (via the monotonic-ref snapshot trick). *)
ghost fn seq_content_gather (sg:seq_ghost)
                            (#vs0 #vs1:erased (Seq.seq U32.t))
  requires seq_content sg vs0 ** seq_content sg vs1
  ensures (exists* (i:nat). hist_auth sg.hist 1.0R i vs0) ** pure (vs0 == vs1)
{
  seq_content_agree sg #vs0 #vs1;
  unfold (seq_content sg vs0);
  unfold (seq_content sg vs1);
  with i0. assert (hist_auth sg.hist 0.5R i0 vs0);
  with i1. assert (hist_auth sg.hist 0.5R i1 vs1);
  (* Pin i0 == i1 by recalling each as a snapshot against the other auth. *)
  hist_take_frag sg.hist #0.5R #i0 #vs0;
  hist_frag_le sg.hist #0.5R #i0 #i1 #vs0 #vs1;
  hist_take_frag sg.hist #0.5R #i1 #vs1;
  hist_frag_le sg.hist #0.5R #i1 #i0 #vs1 #vs0;
  drop_ (hist_frag sg.hist i0 vs0);
  drop_ (hist_frag sg.hist i1 vs1);
  rewrite (hist_auth sg.hist 0.5R i1 vs1) as (hist_auth sg.hist 0.5R i0 vs0);
  hist_auth_gather sg.hist #0.5R #0.5R #i0 #vs0;
  rewrite (hist_auth sg.hist (0.5R +. 0.5R) i0 vs0) as (hist_auth sg.hist 1.0R i0 vs0)
}

ghost fn seq_cur_share (sg:seq_ghost) (#vs:erased (Seq.seq U32.t))
  requires GR.pts_to sg.cur_gr vs
  ensures seq_cur_half sg vs ** seq_cur_half sg vs
{
  GR.share sg.cur_gr;
  fold (seq_cur_half sg vs);
  fold (seq_cur_half sg vs)
}

ghost fn seq_cur_gather (sg:seq_ghost)
                        (#vs0 #vs1:erased (Seq.seq U32.t))
  requires seq_cur_half sg vs0 ** seq_cur_half sg vs1
  ensures GR.pts_to sg.cur_gr vs0 ** pure (vs0 == vs1)
{
  unfold (seq_cur_half sg vs0);
  unfold (seq_cur_half sg vs1);
  GR.gather sg.cur_gr
}

(*
 * Allocate the trio.  We hand the caller the full-perm authoritative
 * history entry (at index 0) plus the full-perm cur mirror and the
 * writer-exclusion token.  The caller is expected to `seq_content_share`
 * / `seq_cur_share` and route halves into the (future) parity-split
 * invariant and a `writer_owned` bundle via `writer_owned_intro`.
 *)
ghost fn alloc_seq_ghost (vs0:Seq.seq U32.t)
  requires emp
  returns sg : seq_ghost
  ensures hist_auth sg.hist 1.0R 0 vs0
       ** GR.pts_to sg.cur_gr vs0
       ** writer_token sg
{
  let hgr = alloc_hist vs0;
  let ugr = GR.alloc vs0;
  let wgr = GR.alloc ();
  let sg : seq_ghost = { hist = hgr; cur_gr = ugr; writer_gr = wgr };
  with i. assert (hist_auth hgr 1.0R i vs0 ** pure (i == 0));
  rewrite (hist_auth hgr 1.0R i vs0) as (hist_auth sg.hist 1.0R 0 vs0);
  rewrite (GR.pts_to ugr vs0) as (GR.pts_to sg.cur_gr vs0);
  rewrite (GR.pts_to wgr ()) as (GR.pts_to sg.writer_gr ());
  fold (writer_token sg);
  sg
}

ghost fn writer_owned_intro (sg:seq_ghost) (#vs:erased (Seq.seq U32.t))
  requires writer_token sg ** seq_content sg vs ** seq_cur_half sg vs
  ensures writer_owned sg vs
{
  fold (writer_owned sg vs)
}

ghost fn writer_owned_elim (sg:seq_ghost) (#vs:erased (Seq.seq U32.t))
  requires writer_owned sg vs
  ensures writer_token sg ** seq_content sg vs ** seq_cur_half sg vs
{
  unfold (writer_owned sg vs)
}

(*
 * Stage 3: write-first ghost-substrate publish step.
 *
 * Round-trips a `writer_owned` bundle through a single end-to-end
 * `hist_publish ws`, paired with the matching `GR.write ws` on the
 * `cur_gr` mirror.  Two-halves-in / two-halves-out: the writer-owned
 * bundle holds one half of each ghost (history + cur), and the caller
 * supplies the matching second halves separately so we can briefly
 * reach `1.0R` and re-split.  This is the first end-to-end exercise
 * of `hist_publish` through the new substrate.  Still substrate-private
 * with zero callers.
 *)
ghost fn seq_content_publish (sg:seq_ghost)
                             (#vs0 #vs1:erased (Seq.seq U32.t))
                             (ws:Seq.seq U32.t)
  requires writer_owned sg vs0
        ** seq_content sg vs1
        ** seq_cur_half sg vs1
  ensures  writer_owned sg ws
        ** seq_content sg ws
        ** seq_cur_half sg ws
{
  writer_owned_elim sg #vs0;
  seq_content_gather sg #vs0 #vs1;
  with i. assert (hist_auth sg.hist 1.0R i vs0);
  hist_publish sg.hist #i #vs0 ws;
  seq_content_share sg #(i + 1) #ws;
  unfold (seq_cur_half sg vs0);
  unfold (seq_cur_half sg vs1);
  GR.gather sg.cur_gr;
  GR.write sg.cur_gr ws;
  GR.share sg.cur_gr;
  fold (seq_cur_half sg ws);
  fold (seq_cur_half sg ws);
  writer_owned_intro sg #ws
}

ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q
  ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q
  ensures q
{ unfold AP.cond }

type payload_cells = Seq.seq (B.box U32.t)

type version_t = U32.t

let version_odd (v:version_t) : Tot bool = U32.eq (U32.rem v 2ul) 1ul
let version_lock (v:version_t) : Tot version_t = U32.add_mod v 1ul
let version_publish (v:version_t) : Tot version_t = U32.add_mod v 2ul

let payload_cell_allocated (cell:B.box U32.t) (_:unit) : slprop =
  exists* (v:U32.t). B.pts_to cell v

let payload_cells_allocated (cells:payload_cells) (marks:list unit) : slprop =
  SM.seq_list_match cells marks payload_cell_allocated

noeq type seqlock = {
  version : B.box version_t;
  cells   : payload_cells;
  len     : SZ.t;
  si      : iname;
  sw      : iname;
  sg      : FStar.Ghost.erased seq_ghost;
}

let seq_inv_inner (version:B.box version_t) (cells:payload_cells) (len:SZ.t)
                  (sg:seq_ghost) : slprop =
  exists* (ver:version_t) (marks:list unit) (vs:Seq.seq U32.t).
    B.pts_to version ver **
    payload_cells_allocated cells marks **
    seq_content sg vs **
    seq_cur_half sg vs **
    pure (L.length marks == SZ.v len) **
    pure (Seq.length cells == SZ.v len) **
    pure (Seq.length vs == SZ.v len)

let seq_inv_raw (l:seqlock) : slprop = seq_inv_inner l.version l.cells l.len (reveal l.sg)

let is_seqlock (l:seqlock) : slprop = inv l.si (seq_inv_raw l)

let seqlock_len (l:seqlock) : Tot SZ.t = l.len

fn rec alloc_payload_cells_zero (remaining:nat)
  requires emp
  returns cells : payload_cells
  ensures exists* (marks:list unit).
            payload_cells_allocated cells marks **
            pure (L.length marks == remaining) **
            pure (Seq.length cells == remaining)
  decreases remaining
{
  if (remaining = 0) {
    SM.seq_list_match_nil_intro Seq.empty [] payload_cell_allocated;
    fold (payload_cells_allocated Seq.empty []);
    Seq.empty
  } else {
    let head_cell = B.alloc 0ul;
    fold (payload_cell_allocated head_cell ());
    let rest_cells = alloc_payload_cells_zero (remaining - 1);
    with marks_rest. assert (
      payload_cells_allocated rest_cells marks_rest **
      pure (L.length marks_rest == remaining - 1) **
      pure (Seq.length rest_cells == remaining - 1));
    unfold payload_cells_allocated;
    SM.seq_list_match_cons_intro head_cell () rest_cells marks_rest payload_cell_allocated;
    fold (payload_cells_allocated (Seq.cons head_cell rest_cells) (() :: marks_rest));
    Seq.cons head_cell rest_cells
  }
}

fn read_version (l:seqlock)
  requires is_seqlock l
  returns v:version_t
  ensures is_seqlock l
{
  unfold is_seqlock;
  let v = with_invariants version_t emp_inames l.si (seq_inv_raw l)
    emp (fun _ -> emp)
  fn _ {
    unfold seq_inv_raw; unfold seq_inv_inner;
    let v = AP.atomic_read l.version;
    fold (seq_inv_inner l.version l.cells l.len (reveal l.sg));
    fold (seq_inv_raw l);
    v
  };
  fold (is_seqlock l);
  v
}

fn try_lock (l:seqlock) (sampled:version_t)
  requires is_seqlock l
  returns b:bool
  ensures is_seqlock l
{
  unfold is_seqlock;
  let b = with_invariants bool emp_inames l.si (seq_inv_raw l)
    emp (fun _ -> emp)
  fn _ {
    unfold seq_inv_raw; unfold seq_inv_inner;
    let b = AP.atomic_cas l.version sampled (version_lock sampled);
    if b {
      elim_cond_true _ _;
      fold (seq_inv_inner l.version l.cells l.len (reveal l.sg));
      fold (seq_inv_raw l);
      true
    } else {
      elim_cond_false _ _;
      fold (seq_inv_inner l.version l.cells l.len (reveal l.sg));
      fold (seq_inv_raw l);
      false
    }
  };
  fold (is_seqlock l);
  b
}

fn publish_unlock (l:seqlock) (base:version_t)
  requires is_seqlock l
  ensures is_seqlock l
{
  unfold is_seqlock;
  with_invariants unit emp_inames l.si (seq_inv_raw l)
    emp (fun _ -> emp)
  fn _ {
    unfold seq_inv_raw; unfold seq_inv_inner;
    AP.atomic_write l.version (version_publish base);
    fold (seq_inv_inner l.version l.cells l.len (reveal l.sg));
    fold (seq_inv_raw l)
  };
  fold (is_seqlock l)
}

fn read_cell (l:seqlock) (i:SZ.t { SZ.v i < SZ.v l.len })
  requires is_seqlock l
  returns x:U32.t
  ensures is_seqlock l
{
  unfold is_seqlock;
  let x = with_invariants U32.t emp_inames l.si (seq_inv_raw l)
    emp (fun _ -> emp)
  fn _ {
    unfold seq_inv_raw; unfold seq_inv_inner;
    with ver marks. assert (
      B.pts_to l.version ver **
      payload_cells_allocated l.cells marks **
      pure (L.length marks == SZ.v l.len) **
      pure (Seq.length l.cells == SZ.v l.len));
    unfold payload_cells_allocated;
    SMT.seq_list_match_index_trade payload_cell_allocated l.cells marks (SZ.v i);
    unfold payload_cell_allocated;
    with old. assert (B.pts_to (Seq.index l.cells (SZ.v i)) old);
    let x = AP.atomic_read (Seq.index l.cells (SZ.v i));
    fold (payload_cell_allocated (Seq.index l.cells (SZ.v i)) (L.index marks (SZ.v i)));
    Trade.elim_trade _ _;
    fold (payload_cells_allocated l.cells marks);
    fold (seq_inv_inner l.version l.cells l.len (reveal l.sg));
    fold (seq_inv_raw l);
    x
  };
  fold (is_seqlock l);
  x
}

fn write_cell (l:seqlock) (i:SZ.t { SZ.v i < SZ.v l.len }) (x:U32.t)
  requires is_seqlock l
  ensures is_seqlock l
{
  unfold is_seqlock;
  with_invariants unit emp_inames l.si (seq_inv_raw l)
    emp (fun _ -> emp)
  fn _ {
    unfold seq_inv_raw; unfold seq_inv_inner;
    with ver marks. assert (
      B.pts_to l.version ver **
      payload_cells_allocated l.cells marks **
      pure (L.length marks == SZ.v l.len) **
      pure (Seq.length l.cells == SZ.v l.len));
    unfold payload_cells_allocated;
    SMT.seq_list_match_index_trade payload_cell_allocated l.cells marks (SZ.v i);
    unfold payload_cell_allocated;
    with old. assert (B.pts_to (Seq.index l.cells (SZ.v i)) old);
    AP.atomic_write (Seq.index l.cells (SZ.v i)) x;
    fold (payload_cell_allocated (Seq.index l.cells (SZ.v i)) (L.index marks (SZ.v i)));
    Trade.elim_trade _ _;
    fold (payload_cells_allocated l.cells marks);
    fold (seq_inv_inner l.version l.cells l.len (reveal l.sg));
    fold (seq_inv_raw l)
  };
  fold (is_seqlock l)
}

fn rec write_cells_from_src
  (l:seqlock)
  (src:A.larray U32.t (SZ.v l.len))
  (i:SZ.t { SZ.v i <= SZ.v l.len })
  (#p:perm)
  (#src0:erased (Seq.seq U32.t))
  requires is_seqlock l ** A.pts_to src #p src0
  ensures is_seqlock l ** A.pts_to src #p src0
  decreases (SZ.v l.len - SZ.v i)
{
  if (i <^ l.len) {
    A.pts_to_len src #p #src0;
    let x = src.(i);
    write_cell l i x;
    write_cells_from_src l src (i +^ 1sz)
  }
}

fn rec copy_cells_to_result
  (l:seqlock)
  (dst:V.vec U32.t)
  (i:SZ.t { SZ.v i <= SZ.v l.len })
  (#dst0:erased (Seq.seq U32.t))
  requires is_seqlock l ** V.pts_to dst dst0 ** pure (Seq.length dst0 == SZ.v l.len)
  ensures is_seqlock l ** (exists* dst1. V.pts_to dst dst1 ** pure (Seq.length dst1 == SZ.v l.len))
  decreases (SZ.v l.len - SZ.v i)
{
  if (i <^ l.len) {
    let x = read_cell l i;
    with cur. assert (V.pts_to dst cur ** pure (Seq.length cur == SZ.v l.len));
    V.op_Array_Assignment dst i x;
    copy_cells_to_result l dst (i +^ 1sz)
  }
}

fn rec write_raw
  (l:seqlock)
  (src:A.larray U32.t (SZ.v l.len))
  (#p:perm)
  (#src0:erased (Seq.seq U32.t))
  requires is_seqlock l ** A.pts_to src #p src0
  ensures is_seqlock l ** A.pts_to src #p src0
{
  let sampled = read_version l;
  if (version_odd sampled) {
    write_raw l src
  } else {
    let locked = try_lock l sampled;
    if (locked) {
      write_cells_from_src l src 0sz;
      publish_unlock l sampled
    } else {
      write_raw l src
    }
  }
}

fn rec read_raw (l:seqlock)
  requires is_seqlock l
  returns dst:V.vec U32.t
  ensures is_seqlock l ** (exists* vals. V.pts_to dst vals ** pure (Seq.length vals == SZ.v l.len))
{
  let first = read_version l;
  if (version_odd first) {
    read_raw l
  } else {
    let dst = V.alloc 0ul l.len;
    copy_cells_to_result l dst 0sz;
    let second = read_version l;
    if (U32.eq first second) {
      dst
    } else {
      with vals. assert (V.pts_to dst vals ** pure (Seq.length vals == SZ.v l.len));
      V.free dst;
      read_raw l
    }
  }
}

fn write
  (l:seqlock)
  (src:A.larray U32.t (SZ.v l.len))
  (#p:perm)
  (#src0:erased (Seq.seq U32.t))
  requires is_seqlock l ** A.pts_to src #p src0
  ensures is_seqlock l ** A.pts_to src #p src0
{
  write_raw l src
}

fn read (l:seqlock)
  requires is_seqlock l
  returns dst:V.vec U32.t
  ensures is_seqlock l ** (exists* vals. V.pts_to dst vals ** pure (Seq.length vals == SZ.v l.len))
{
  read_raw l
}

(* Boxed allocator: returns the seq_ghost handle as an erased value so it can
   be bound in non-ghost (stt) contexts and stored in `seqlock.sg`.  The
   underlying resources are returned over `(reveal sg).*` so callers can share
   them and park them in the seqlock's invariants. *)
ghost fn alloc_seq_ghost_boxed (vs0:Seq.seq U32.t)
  requires emp
  returns sg : erased seq_ghost
  ensures hist_auth (reveal sg).hist 1.0R 0 vs0
       ** GR.pts_to (reveal sg).cur_gr vs0
       ** writer_token (reveal sg)
{
  let sg_c = alloc_seq_ghost vs0;
  let sg_e : erased seq_ghost = hide sg_c;
  rewrite (hist_auth sg_c.hist 1.0R 0 vs0) as (hist_auth (reveal sg_e).hist 1.0R 0 vs0);
  rewrite (GR.pts_to sg_c.cur_gr vs0) as (GR.pts_to (reveal sg_e).cur_gr vs0);
  rewrite (writer_token sg_c) as (writer_token (reveal sg_e));
  sg_e
}

fn new_big_atomic
  (n:SZ.t)
  (src:A.larray U32.t (SZ.v n))
  (#p:perm)
  (#src0:erased (Seq.seq U32.t))
  requires A.pts_to src #p src0
  returns l : seqlock
  ensures is_seqlock l ** A.pts_to src #p src0
{
  A.pts_to_len src #p #src0;
  let version = B.alloc 0ul;
  let init_vs : Seq.seq U32.t = Seq.create (SZ.v n) 0ul;
  let sg = alloc_seq_ghost_boxed init_vs;
  seq_content_share (reveal sg) #0 #init_vs;
  seq_cur_share (reveal sg) #init_vs;
  let cells = alloc_payload_cells_zero (SZ.v n);
  with marks. assert (
    payload_cells_allocated cells marks **
    pure (L.length marks == SZ.v n) **
    pure (Seq.length cells == SZ.v n));
  fold (seq_inv_inner version cells n (reveal sg));
  let si = new_invariant (seq_inv_inner version cells n (reveal sg));
  Seq.lemma_create_len (SZ.v n) 0ul;
  let sw = new_invariant (
    exists* (vs:Seq.seq U32.t).
      writer_token (reveal sg) **
      seq_content (reveal sg) vs **
      seq_cur_half (reveal sg) vs **
      pure (Seq.length vs == SZ.v n));
  let l : seqlock = { version; cells; len = n; si; sw; sg };
  rewrite (inv si (seq_inv_inner version cells n (reveal sg))) as (inv l.si (seq_inv_raw l));
  fold (is_seqlock l);
  write_raw l src;
  l
}
