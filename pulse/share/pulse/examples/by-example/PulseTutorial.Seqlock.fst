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
open Pulse.Lib.Inv
module A = Pulse.Lib.Array.PtsTo
module Arr = Pulse.Lib.Array
module MGR = Pulse.Lib.MonotonicGhostRef
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module List = FStar.List.Tot
module SZ = FStar.SizeT
module SM = Pulse.Lib.SeqMatch
open FStar.List.Tot { (@) }

let prop_as_bool = FStar.IndefiniteDescription.strong_excluded_middle

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

let mono_nat_auth (gver:MGR.mref mono_nat_increases) (q:perm) (ver:nat) : slprop =
  MGR.pts_to gver #q ver

let mono_nat_lb (gver:MGR.mref mono_nat_increases) (ver:nat) : slprop =
  MGR.snapshot #nat #mono_nat_increases gver ver

ghost fn mono_nat_lb_get (gver:MGR.mref mono_nat_increases) (#q:perm) (#ver:nat)
  preserves mono_nat_auth gver q ver
  ensures mono_nat_lb gver ver
{
  unfold (mono_nat_auth gver q ver);
  MGR.take_snapshot #nat #mono_nat_increases gver #q ver;
  fold (mono_nat_auth gver q ver);
  fold (mono_nat_lb gver ver)
}

ghost fn mono_nat_lb_valid (gver:MGR.mref mono_nat_increases) (#q:perm) (#ver #lb:nat)
  preserves mono_nat_auth gver q ver
  preserves mono_nat_lb gver lb
  ensures pure (lb <= ver)
{
  unfold (mono_nat_auth gver q ver);
  unfold (mono_nat_lb gver lb);
  MGR.recall_snapshot #nat #mono_nat_increases gver #q #ver #lb;
  fold (mono_nat_auth gver q ver);
  fold (mono_nat_lb gver lb)
}

let rec last_opt_nth_length (#a:Type0) (xs:list a)
  : Lemma
      (requires List.length xs > 0)
      (ensures List.nth xs (List.length xs - 1) == last_opt xs)
  = match xs with
    | [] -> ()
    | _::[] -> ()
    | _::tl -> last_opt_nth_length tl

let last_opt_nth (#a:Type0) (xs:list a) (i:nat) (v:a)
  : Lemma
      (requires List.length xs == 1 + i /\ last_opt xs == Some v)
      (ensures List.nth xs i == Some v)
  = last_opt_nth_length xs;
    assert (i == List.length xs - 1)

let rec nth_index_some (#a:Type0) (xs:list a) (i:nat{i < List.length xs})
  : Lemma (List.nth xs i == Some (List.index xs i))
  = match xs with
    | [] -> ()
    | _::tl -> if i = 0 then () else nth_index_some tl (i - 1)

let seq_of_snapshot_nth (vs:list val_t) (i:nat{i < List.length vs})
  : Lemma (List.nth vs i == Some (Seq.index (seq_of_snapshot vs) i))
  = SeqP.lemma_seq_of_list_index vs i;
    nth_index_some vs i

let t2b_true_of_prop (p:prop)
  : Lemma (requires p) (ensures Prims.t2b p == true)
  = ()

let t2b_false_of_not (p:prop)
  : Lemma (requires ~p) (ensures Prims.t2b p == false)
  = ()

ghost fn intro_cond_true_b (b:bool) (p q:slprop)
  requires p
  requires pure (b == true)
  ensures (if b then p else q)
{
  rewrite p as (if b then p else q)
}

ghost fn intro_cond_false_b (b:bool) (p q:slprop)
  requires q
  requires pure (b == false)
  ensures (if b then p else q)
{
  rewrite q as (if b then p else q)
}

ghost fn elim_if_true_b (b:bool) (p q:slprop)
  requires (if b then p else q)
  requires pure (b == true)
  ensures p
{
  rewrite (if b then p else q) as p
}

ghost fn elim_if_false_b (b:bool) (p q:slprop)
  requires (if b then p else q)
  requires pure (b == false)
  ensures q
{
  rewrite (if b then p else q) as q
}

(* Value abstraction visible to clients: half of the history authority and a
   witness that the latest snapshot is [vs]. *)
let value (gh:gname val_t) (vs:list val_t) : slprop =
  exists* (h:history val_t).
    history_auth gh (1.0R /. 2.0R) h **
    pure (last_opt h == Some vs)

(* The big invariant content: conditional on parity of the physical version. *)
let seqlock_inv_body (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
                (version:ref nat) (data:array val_t) (len:nat)
                (ver:nat) (h:history val_t) (vs:list val_t)
  : slprop =
  version |-> ver **
  pure (List.length vs == len /\ List.length h == 1 + ver / 2) **
  (if ver % 2 == 0 then
     history_auth gh (1.0R /. 2.0R) h **
     mono_nat_auth gver 1.0R ver **
     A.pts_to data (seq_of_snapshot vs) **
     pure (last_opt h == Some vs)
   else
     history_auth gh (1.0R /. 4.0R) h **
     mono_nat_auth gver (1.0R /. 2.0R) ver **
     A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs))

let seqlock_inv (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
                (version:ref nat) (data:array val_t) (len:nat)
  : slprop =
  exists* (ver:nat) (h:history val_t) (vs:list val_t).
    seqlock_inv_body gver gh version data len ver h vs

(* Public predicate: holding an [is_seqlock] means the invariant has been
   allocated for the handle. *)
let is_seqlock (v:big_atomic) (gh:gname val_t) (n:nat) : slprop =
  exists* (gver:MGR.mref mono_nat_increases) (i:iname).
    inv i (seqlock_inv gver gh (fst v) (snd v) n)

ghost fn pack_seqlock_inv_even (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t)
  requires
    pure (ver % 2 == 0) **
    version |-> ver **
    pure (List.length vs == n /\ List.length h == 1 + ver / 2) **
    history_auth gh (1.0R /. 2.0R) h **
    mono_nat_auth gver 1.0R ver **
    A.pts_to data (seq_of_snapshot vs) **
    pure (last_opt h == Some vs)
  ensures seqlock_inv gver gh version data n
{
  t2b_true_of_prop (ver % 2 == 0);
  assert (pure (Prims.t2b (ver % 2 == 0) == true));
  intro_pure (last_opt h == Some vs) ();
  intro_cond_true_b (Prims.t2b (ver % 2 == 0))
    (history_auth gh (1.0R /. 2.0R) h **
     mono_nat_auth gver 1.0R ver **
     A.pts_to data (seq_of_snapshot vs) **
     pure (last_opt h == Some vs))
    (history_auth gh (1.0R /. 4.0R) h **
     mono_nat_auth gver (1.0R /. 2.0R) ver **
     A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
  fold (seqlock_inv_body gver gh version data n ver h vs);
  fold (seqlock_inv gver gh version data n)
}

ghost fn pack_seqlock_inv_odd (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t)
  requires
    pure (ver % 2 <> 0) **
    version |-> ver **
    pure (List.length vs == n /\ List.length h == 1 + ver / 2) **
    history_auth gh (1.0R /. 4.0R) h **
    mono_nat_auth gver (1.0R /. 2.0R) ver **
    A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs)
  ensures seqlock_inv gver gh version data n
{
  t2b_false_of_not (ver % 2 == 0);
  assert (pure (Prims.t2b (ver % 2 == 0) == false));
  intro_cond_false_b (Prims.t2b (ver % 2 == 0))
    (history_auth gh (1.0R /. 2.0R) h **
     mono_nat_auth gver 1.0R ver **
     A.pts_to data (seq_of_snapshot vs) **
     pure (last_opt h == Some vs))
    (history_auth gh (1.0R /. 4.0R) h **
     mono_nat_auth gver (1.0R /. 2.0R) ver **
     A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
  fold (seqlock_inv_body gver gh version data n ver h vs);
  fold (seqlock_inv gver gh version data n)
}

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
  pack_seqlock_inv_even gver gh version data (SZ.v n) #0 #(reveal h0) #(reveal snap);
  let i = new_invariant (seqlock_inv gver gh version data (SZ.v n));
  let handle : big_atomic = (version, data);
  rewrite (inv i (seqlock_inv gver gh version data (SZ.v n)))
    as (inv i (seqlock_inv gver gh (fst handle) (snd handle) (SZ.v n)));
  fold (is_seqlock handle gh (SZ.v n));
  rewrite (value gh (reveal snap)) as (value gh (snapshot_of_seq (reveal vs)));
  (handle, gh)
}

(* Per-element evidence: the version observed while reading an element, plus
   a persistent history fragment for even (unlocked) versions. *)
let snapshot_even_evidence_payload (gh:gname val_t)
    (i:nat) (ver_i:nat) (v:val_t) : slprop =
  exists* (vs:list val_t) (h:history val_t).
    history_frag gh (ver_i / 2) vs #h **
    pure (List.nth vs i == Some v)

let snapshot_evidence (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (ver_i:nat) (v:val_t) : slprop =
  if ver_i % 2 == 0 then
    mono_nat_lb gver ver_i **
    snapshot_even_evidence_payload gh i ver_i v
  else
    mono_nat_lb gver ver_i **
    pure (ver_i % 2 <> 0)

(* A branch-free view of the invariant's read resources.  It lets the
   atomic body perform one physical read without branching on the erased
   invariant witness [ver]. *)
let seqlock_read_case (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (data:array val_t) (ver:nat) (h:history val_t) (vs:list val_t) : slprop =
  exists* (hp:perm) (vp:perm) (dp:perm).
    history_auth gh hp h **
    mono_nat_auth gver vp ver **
    A.pts_to data #dp (seq_of_snapshot vs) **
    pure (((ver % 2 == 0) /\ hp == (1.0R /. 2.0R) /\ vp == 1.0R /\
           dp == 1.0R /\ last_opt h == Some vs) \/
          ((ver % 2 <> 0) /\ hp == (1.0R /. 4.0R) /\
           vp == (1.0R /. 2.0R) /\ dp == (1.0R /. 2.0R)))

ghost fn seqlock_read_case_intro (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (data:array val_t) (#ver:nat) (#h:history val_t) (#vs:list val_t)
  requires
    (if ver % 2 == 0 then
       history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver 1.0R ver **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs)
     else
       history_auth gh (1.0R /. 4.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) ver **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs))
  ensures seqlock_read_case gver gh data ver h vs
{
  let b = prop_as_bool (ver % 2 == 0);
  if b {
    t2b_true_of_prop (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == true));
    elim_if_true_b (Prims.t2b (ver % 2 == 0))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver 1.0R ver **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 4.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) ver **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    fold (seqlock_read_case gver gh data ver h vs)
  } else {
    t2b_false_of_not (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == false));
    elim_if_false_b (Prims.t2b (ver % 2 == 0))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver 1.0R ver **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 4.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) ver **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    fold (seqlock_read_case gver gh data ver h vs)
  }
}

ghost fn dup_mono_nat_lb (gver:MGR.mref mono_nat_increases) (ver:nat)
  requires mono_nat_lb gver ver
  ensures mono_nat_lb gver ver ** mono_nat_lb gver ver
{
  unfold (mono_nat_lb gver ver);
  dup (MGR.snapshot #nat #mono_nat_increases gver ver) ();
  fold (mono_nat_lb gver ver);
  fold (mono_nat_lb gver ver)
}

ghost fn fold_seqlock_inv_even (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t)
  requires
    pure (ver % 2 == 0) **
    version |-> ver **
    pure (List.length vs == n /\ List.length h == 1 + ver / 2) **
    history_auth gh (1.0R /. 2.0R) h **
    mono_nat_auth gver 1.0R ver **
    A.pts_to data (seq_of_snapshot vs) **
    pure (last_opt h == Some vs)
  ensures seqlock_inv gver gh version data n
{
  pack_seqlock_inv_even gver gh version data n #ver #h #vs
}

ghost fn fold_seqlock_inv_odd (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t)
  requires
    pure (ver % 2 <> 0) **
    version |-> ver **
    pure (List.length vs == n /\ List.length h == 1 + ver / 2) **
    history_auth gh (1.0R /. 4.0R) h **
    mono_nat_auth gver (1.0R /. 2.0R) ver **
    A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs)
  ensures seqlock_inv gver gh version data n
{
  pack_seqlock_inv_odd gver gh version data n #ver #h #vs
}

ghost fn seqlock_read_case_close (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (version:ref nat) (data:array val_t) (n:nat) (i:SZ.t) (ver_lb:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t) (v_i:val_t)
  requires
    version |-> ver **
    pure (List.length vs == n /\ List.length h == 1 + ver / 2) **
    seqlock_read_case gver gh data ver h vs **
    mono_nat_lb gver ver_lb **
    pure (List.nth vs (SZ.v i) == Some v_i)
  ensures
    seqlock_inv gver gh version data n **
    snapshot_evidence gver gh (SZ.v i) ver v_i **
    mono_nat_lb gver ver **
    pure (ver >= ver_lb)
{
  unfold (seqlock_read_case gver gh data ver h vs);
  with hp vp dp. _;
  let b = prop_as_bool (ver % 2 == 0);
  if b {
    assert (pure (hp == (1.0R /. 2.0R) /\ vp == 1.0R /\ dp == 1.0R /\ last_opt h == Some vs));
    rewrite each hp as (1.0R /. 2.0R);
    rewrite each vp as 1.0R;
    rewrite each dp as 1.0R;
    mono_nat_lb_valid gver #1.0R #ver #ver_lb;
    mono_nat_lb_get gver #1.0R #ver;
    dup_mono_nat_lb gver ver;
    last_opt_nth h (ver / 2) vs;
    history_frag_alloc gh #(1.0R /. 2.0R) #h (ver / 2) vs;
    assert (pure (ver % 2 == 0));
    assert (pure (last_opt h == Some vs));
    intro_pure (List.length vs == n /\ List.length h == 1 + ver / 2) ();
    intro_pure (last_opt h == Some vs) ();
    fold_seqlock_inv_even gver gh version data n #ver #h #vs;
    t2b_true_of_prop (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == true));
    intro_pure (List.nth vs (SZ.v i) == Some v_i) ();
    fold (snapshot_even_evidence_payload gh (SZ.v i) ver v_i);
    intro_cond_true_b (Prims.t2b (ver % 2 == 0))
      (mono_nat_lb gver ver **
       snapshot_even_evidence_payload gh (SZ.v i) ver v_i)
      (mono_nat_lb gver ver ** pure (ver % 2 <> 0));
    fold (snapshot_evidence gver gh (SZ.v i) ver v_i);
    drop_ (mono_nat_lb gver ver_lb)
  } else {
    assert (pure (hp == (1.0R /. 4.0R) /\ vp == (1.0R /. 2.0R) /\ dp == (1.0R /. 2.0R)));
    rewrite each hp as (1.0R /. 4.0R);
    rewrite each vp as (1.0R /. 2.0R);
    rewrite each dp as (1.0R /. 2.0R);
    mono_nat_lb_valid gver #(1.0R /. 2.0R) #ver #ver_lb;
    mono_nat_lb_get gver #(1.0R /. 2.0R) #ver;
    dup_mono_nat_lb gver ver;
    assert (pure (ver % 2 <> 0));
    intro_pure (List.length vs == n /\ List.length h == 1 + ver / 2) ();
    fold_seqlock_inv_odd gver gh version data n #ver #h #vs;
    t2b_false_of_not (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == false));
    intro_pure (ver % 2 <> 0) ();
    intro_cond_false_b (Prims.t2b (ver % 2 == 0))
      (mono_nat_lb gver ver **
       snapshot_even_evidence_payload gh (SZ.v i) ver v_i)
      (mono_nat_lb gver ver ** pure (ver % 2 <> 0));
    fold (snapshot_evidence gver gh (SZ.v i) ver v_i);
    drop_ (mono_nat_lb gver ver_lb)
  }
}

let seq_index_or (#a:Type0) (d:a) (s:Seq.seq a) (i:nat) : Tot a =
  if i < Seq.length s then Seq.index s i else d

let seq_index_or_index (#a:Type0) (d:a) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (seq_index_or d s i == Seq.index s i)
  = ()

let versions_ge_from (lb:nat) (i:nat) (n:nat) (vers:Seq.seq nat) : prop =
  forall (k:nat). i <= k /\ k < n ==> lb <= seq_index_or #nat 0 vers k

let versions_strongly_sorted_from (i:nat) (n:nat) (vers:Seq.seq nat) : prop =
  forall (k:nat) (l:nat).
    i <= k /\ k < l /\ l < n ==> seq_index_or #nat 0 vers k <= seq_index_or #nat 0 vers l

let versions_ge_from_cons (lb:nat) (ver_i:nat) (i:nat) (n:nat) (vers:Seq.seq nat)
  : Lemma
      (requires lb <= ver_i /\ seq_index_or #nat 0 vers i == ver_i /\
                versions_ge_from ver_i (i + 1) n vers)
      (ensures versions_ge_from lb i n vers)
  = assert (forall (k:nat). i <= k /\ k < n ==> lb <= seq_index_or #nat 0 vers k)

let versions_strongly_sorted_from_cons (ver_i:nat) (i:nat) (n:nat) (vers:Seq.seq nat)
  : Lemma
      (requires seq_index_or #nat 0 vers i == ver_i /\
                versions_ge_from ver_i (i + 1) n vers /\
                versions_strongly_sorted_from (i + 1) n vers)
      (ensures versions_strongly_sorted_from i n vers)
  = assert (forall (k:nat) (l:nat).
              i <= k /\ k < l /\ l < n ==>
              seq_index_or #nat 0 vers k <= seq_index_or #nat 0 vers l)

let rec big_snapshot_evidence_from (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  : Tot slprop (decreases (n - i)) =
  if i < n then
    snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
    big_snapshot_evidence_from gver gh (i + 1) n vers vals
  else
    emp

let big_snapshot_evidence (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (ver_lb:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t) : slprop =
  big_snapshot_evidence_from gver gh 0 n vers vals **
  pure (Seq.length vers == n /\ Seq.length vals == n /\
        versions_strongly_sorted_from 0 n vers /\
        versions_ge_from ver_lb 0 n vers)

ghost fn pack_big_snapshot_evidence_nil (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires pure (i >= n)
  ensures big_snapshot_evidence_from gver gh i n vers vals
{
  assert (pure ((i < n) == false));
  intro_cond_false_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp;
  fold (big_snapshot_evidence_from gver gh i n vers vals)
}

ghost fn pack_big_snapshot_evidence_cons (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires pure (i < n)
  requires snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i)
  requires big_snapshot_evidence_from gver gh (i + 1) n vers vals
  ensures big_snapshot_evidence_from gver gh i n vers vals
{
  assert (pure ((i < n) == true));
  intro_cond_true_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp;
  fold (big_snapshot_evidence_from gver gh i n vers vals)
}

fn snapshot_read_slot_impl (data:array val_t) (i:SZ.t)
    (#p:perm)
    (#s:erased (Seq.seq val_t){SZ.v i < Seq.length s})
  preserves A.pts_to data #p s
  returns v_i:val_t
  ensures pure (v_i == Seq.index s (SZ.v i))
{
  data.(i)
}

let snapshot_read_slot_atomic (data:array val_t) (i:SZ.t)
    (#p:perm)
    (#s:erased (Seq.seq val_t){SZ.v i < Seq.length s}) =
  Pulse.Lib.Core.as_atomic _ _ (snapshot_read_slot_impl data i #p #s)

fn snapshot_copy_step
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat)
   (i:SZ.t) (#ver_lb:erased nat) (dst:array val_t)
   (#vdst:erased (s:Seq.seq val_t{SZ.v i < Seq.length s}))
  requires
       inv n_inv (seqlock_inv gver gh version data n)
    ** mono_nat_lb gver (reveal ver_lb)
    ** A.pts_to dst vdst
    ** pure (SZ.v i < n /\ Seq.length vdst == n)
  returns r : (erased nat & val_t)
  ensures
       A.pts_to dst (Seq.upd vdst (SZ.v i) (snd r))
    ** snapshot_evidence gver gh (SZ.v i) (reveal (fst r)) (snd r)
    ** mono_nat_lb gver (reveal (fst r))
    ** pure (reveal (fst r) >= reveal ver_lb)
{
  let r = with_invariants (erased nat & val_t) emp_inames n_inv (seqlock_inv gver gh version data n)
    (mono_nat_lb gver (reveal ver_lb))
    (fun r -> snapshot_evidence gver gh (SZ.v i) (reveal (fst r)) (snd r) **
              mono_nat_lb gver (reveal (fst r)) ** pure (reveal (fst r) >= reveal ver_lb))
  fn _ {
    unfold (seqlock_inv gver gh version data n);
    with ver h vs. _;
    unfold (seqlock_inv_body gver gh version data n ver h vs);
    seqlock_read_case_intro gver gh data #ver #h #vs;
    unfold (seqlock_read_case gver gh data ver h vs);
    with hp vp dp. _;
    let v_i = snapshot_read_slot_atomic data i #dp #(seq_of_snapshot vs);
    seq_of_snapshot_nth vs (SZ.v i);
    assert (pure (List.nth vs (SZ.v i) == Some v_i));
    fold (seqlock_read_case gver gh data ver h vs);
    seqlock_read_case_close gver gh version data n i (reveal ver_lb) #ver #h #vs v_i;
    (hide ver, v_i)
  };
  let v_i = snd r;
  dst.(i) <- v_i;
  with s'. assert (A.pts_to dst s' ** pure (s' == Seq.upd vdst (SZ.v i) v_i));
  rewrite each s' as (Seq.upd vdst (SZ.v i) v_i);
  r
}

fn rec snapshot_copy_aux
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (i:SZ.t) (#ver_lb:erased nat) (dst:array val_t)
   (#vdst:erased (Seq.seq val_t)) (#vers:erased (Seq.seq nat))
  requires
       inv n_inv (seqlock_inv gver gh version data (SZ.v n))
    ** mono_nat_lb gver (reveal ver_lb)
    ** A.pts_to dst vdst
    ** pure (SZ.v i <= SZ.v n /\ Seq.length vdst == SZ.v n /\ Seq.length vers == SZ.v n)
  ensures
    exists* (vout:Seq.seq val_t) (versout:Seq.seq nat).
       A.pts_to dst vout
    ** big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout
    ** pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
             versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
             versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
             (forall (k:nat). k < SZ.v i ==>
                seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))
  decreases (SZ.v n - SZ.v i)
{
  if (i = n) {
    assert (pure (SZ.v i == SZ.v n));
    assert (pure (versions_strongly_sorted_from (SZ.v i) (SZ.v n) vers));
    assert (pure (versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) vers));
    pack_big_snapshot_evidence_nil gver gh (SZ.v i) (SZ.v n) vers vdst;
    drop_ (mono_nat_lb gver (reveal ver_lb));
    intro_pure (Seq.length vdst == SZ.v n /\ Seq.length vers == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) vers /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) vers /\
                (forall (k:nat). k < SZ.v i ==>
                   seq_index_or #val_t 0 vdst k == seq_index_or #val_t 0 vdst k /\
                   seq_index_or #nat 0 vers k == seq_index_or #nat 0 vers k)) ();
    intro_exists #(Seq.seq nat)
      (fun versout -> A.pts_to dst vdst **
                      big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vdst **
                      pure (Seq.length vdst == SZ.v n /\ Seq.length versout == SZ.v n /\
                            versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                            versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                            (forall (k:nat). k < SZ.v i ==> 
                              seq_index_or #val_t 0 vdst k == seq_index_or #val_t 0 vdst k /\
                              seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) vers;
    intro_exists #(Seq.seq val_t)
      (fun vout -> exists* (versout:Seq.seq nat).
          A.pts_to dst vout **
          big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout **
          pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                (forall (k:nat). k < SZ.v i ==>
                  seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                  seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) vdst
  } else {
    assert (pure (SZ.v i < SZ.v n));
    SZ.fits_lte (SZ.v i + 1) (SZ.v n);
    let vdst_step : erased (s:Seq.seq val_t{SZ.v i < Seq.length s}) = hide (reveal vdst);
    rewrite (A.pts_to dst vdst) as (A.pts_to dst vdst_step);
    let r = snapshot_copy_step #gver #gh #n_inv version data (SZ.v n) i #ver_lb dst #vdst_step;
    let v_i = snd r;
    rewrite (A.pts_to dst (Seq.upd vdst_step (SZ.v i) v_i))
      as (A.pts_to dst (Seq.upd vdst (SZ.v i) v_i));
    let vdst1 : erased (Seq.seq val_t) = hide (Seq.upd vdst (SZ.v i) v_i);
    let vers1 : erased (Seq.seq nat) = hide (Seq.upd vers (SZ.v i) (reveal (fst r)));
    Seq.lemma_len_upd (SZ.v i) v_i vdst;
    Seq.lemma_len_upd (SZ.v i) (reveal (fst r)) vers;
    rewrite (A.pts_to dst (Seq.upd vdst (SZ.v i) v_i)) as (A.pts_to dst vdst1);
    let i1 = SZ.add i 1sz;
    assert (pure (SZ.v i1 == SZ.v i + 1));
    snapshot_copy_aux #gver #gh #n_inv version data n i1 #(fst r) dst #vdst1 #vers1;
    with vout versout. _;
    assert (pure (Seq.index vout (SZ.v i) == v_i));
    assert (pure (Seq.index versout (SZ.v i) == reveal (fst r)));
    seq_index_or_index #val_t 0 vout (SZ.v i);
    seq_index_or_index #nat 0 versout (SZ.v i);
    assert (pure (seq_index_or #nat 0 versout (SZ.v i) == reveal (fst r)));
    assert (pure (seq_index_or #val_t 0 vout (SZ.v i) == snd r));
    rewrite (snapshot_evidence gver gh (SZ.v i) (reveal (fst r)) (snd r))
      as (snapshot_evidence gver gh (SZ.v i)
            (seq_index_or #nat 0 versout (SZ.v i))
            (seq_index_or #val_t 0 vout (SZ.v i)));
    rewrite each (SZ.v i1) as (SZ.v i + 1);
    assert (pure (versions_ge_from (reveal (fst r)) (SZ.v i + 1) (SZ.v n) versout));
    assert (pure (versions_strongly_sorted_from (SZ.v i + 1) (SZ.v n) versout));
    versions_ge_from_cons (reveal ver_lb) (reveal (fst r)) (SZ.v i) (SZ.v n) versout;
    versions_strongly_sorted_from_cons (reveal (fst r)) (SZ.v i) (SZ.v n) versout;
    pack_big_snapshot_evidence_cons gver gh (SZ.v i) (SZ.v n) versout vout;
    assert (pure (forall (k:nat). k < SZ.v i ==>
             seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
             seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k));
    intro_pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                (forall (k:nat). k < SZ.v i ==>
                   seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                   seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k)) ();
    intro_exists #(Seq.seq nat)
      (fun versout -> A.pts_to dst vout **
                      big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout **
                      pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                            versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                            versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                            (forall (k:nat). k < SZ.v i ==> 
                              seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                              seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) versout;
    intro_exists #(Seq.seq val_t)
      (fun vout -> exists* (versout:Seq.seq nat).
          A.pts_to dst vout **
          big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout **
          pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                (forall (k:nat). k < SZ.v i ==>
                  seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                  seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) vout
  }
}

fn snapshot_copy
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (ver_lb:nat) (dst:array val_t)
   (#vdst0:erased (Seq.seq val_t))
  requires
       inv n_inv (seqlock_inv gver gh version data (SZ.v n))
    ** mono_nat_lb gver ver_lb
    ** A.pts_to dst vdst0
    ** pure (Seq.length vdst0 == SZ.v n)
  returns vdst' : erased (Seq.seq val_t)
  ensures
       A.pts_to dst vdst'
    ** pure (Seq.length vdst' == SZ.v n)
    ** (exists* (vers:Seq.seq nat).
          big_snapshot_evidence gver gh ver_lb (SZ.v n) vers vdst')
{
  let vers0 : erased (Seq.seq nat) = hide (Seq.create (SZ.v n) 0);
  assert (pure (Seq.length vers0 == SZ.v n));
  snapshot_copy_aux #gver #gh #n_inv version data n 0sz #(hide ver_lb) dst #vdst0 #vers0;
  with vout versout. _;
  fold (big_snapshot_evidence gver gh ver_lb (SZ.v n) versout vout);
  intro_exists #(Seq.seq nat)
    (fun vers -> big_snapshot_evidence gver gh ver_lb (SZ.v n) vers vout) versout;
  hide vout
}
