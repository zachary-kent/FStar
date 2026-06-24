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
module AP = Pulse.Lib.Primitives
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
let history_len_for_version (ver:nat) : nat = 1 + (ver + ver % 2) / 2

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

ghost fn elim_ap_cond_true (p q:slprop)
  requires AP.cond true p q
  ensures p
{
  unfold AP.cond
}

ghost fn elim_ap_cond_false (p q:slprop)
  requires AP.cond false p q
  ensures q
{
  unfold AP.cond
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
  pure (List.length vs == len /\ List.length h == history_len_for_version ver) **
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
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
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
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
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
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
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
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
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
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
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
    intro_pure (List.length vs == n /\ List.length h == history_len_for_version ver) ();
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
    intro_pure (List.length vs == n /\ List.length h == history_len_for_version ver) ();
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

(* -------------------------------------------------------------------------- *)
(* Writer-side helpers                                                        *)
(* -------------------------------------------------------------------------- *)

let rec last_opt_snoc (#a:Type0) (xs:list a) (x:a)
  : Lemma (last_opt (xs @ [x]) == Some x)
  = match xs with
    | [] -> ()
    | _::tl -> last_opt_snoc tl x

let seq_prefix_eq (i:nat) (s t:Seq.seq val_t) : prop =
  forall (k:nat). k < i /\ k < Seq.length s /\ k < Seq.length t ==>
    Seq.index s k == Seq.index t k

let seq_prefix_eq_succ (i:nat) (s t:Seq.seq val_t)
  : Lemma
      (requires i < Seq.length s /\ Seq.length s == Seq.length t /\ seq_prefix_eq i s t)
      (ensures seq_prefix_eq (i + 1) (Seq.upd s i (Seq.index t i)) t)
  = Seq.lemma_index_upd1 s i (Seq.index t i);
    assert (forall (k:nat). k < i + 1 /\ k < Seq.length (Seq.upd s i (Seq.index t i)) /\ k < Seq.length t ==>
              Seq.index (Seq.upd s i (Seq.index t i)) k == Seq.index t k)

let seq_prefix_eq_all (s t:Seq.seq val_t)
  : Lemma
      (requires Seq.length s == Seq.length t /\ seq_prefix_eq (Seq.length s) s t)
      (ensures s == t)
  = Seq.lemma_eq_intro s t;
    Seq.lemma_eq_elim s t

ghost fn mono_nat_auth_auth_agree (gver:MGR.mref mono_nat_increases)
    (#q1 #q2:perm) (#v1 #v2:nat)
  preserves mono_nat_auth gver q1 v1 ** mono_nat_auth gver q2 v2
  ensures pure (v1 == v2)
{
  unfold (mono_nat_auth gver q1 v1);
  unfold (mono_nat_auth gver q2 v2);
  MGR.take_snapshot #nat #mono_nat_increases gver #q1 v1;
  MGR.take_snapshot #nat #mono_nat_increases gver #q2 v2;
  MGR.recall_snapshot #nat #mono_nat_increases gver #q2 #v2 #v1;
  MGR.recall_snapshot #nat #mono_nat_increases gver #q1 #v1 #v2;
  assert (pure (v1 <= v2));
  assert (pure (v2 <= v1));
  assert (pure (v1 == v2));
  fold (mono_nat_auth gver q1 v1);
  fold (mono_nat_auth gver q2 v2)
}

ghost fn mono_nat_update (gver:MGR.mref mono_nat_increases) (#old:nat) (newv:nat)
  requires mono_nat_auth gver 1.0R old ** pure (old <= newv)
  ensures mono_nat_auth gver 1.0R newv
{
  unfold (mono_nat_auth gver 1.0R old);
  MGR.update #nat #mono_nat_increases gver #old newv;
  fold (mono_nat_auth gver 1.0R newv)
}

ghost fn mono_nat_gather (gver:MGR.mref mono_nat_increases)
    (#q1 #q2:perm) (#v1 #v2:nat)
  requires mono_nat_auth gver q1 v1 ** mono_nat_auth gver q2 v2
  ensures mono_nat_auth gver (q1 +. q2) v1 ** pure (v1 == v2)
{
  mono_nat_auth_auth_agree gver #q1 #q2 #v1 #v2;
  rewrite each v2 as v1;
  unfold (mono_nat_auth gver q1 v1);
  unfold (mono_nat_auth gver q2 v1);
  MGR.gather #nat #mono_nat_increases gver #v1 #q1 #q2;
  fold (mono_nat_auth gver (q1 +. q2) v1)
}

fn version_read_impl (version:ref nat) (#p:perm) (#ver:erased nat)
  preserves version |-> Frac p ver
  returns r:nat
  ensures pure (r == reveal ver)
{
  !version
}

let version_read_atomic (version:ref nat) (#p:perm) (#ver:erased nat) =
  Pulse.Lib.Core.as_atomic _ _ (version_read_impl version #p #ver)

fn version_store_impl (version:ref nat) (newv:nat) (#old:erased nat)
  requires version |-> old
  ensures version |-> newv
{
  version := newv
}

let version_store_atomic (version:ref nat) (newv:nat) (#old:erased nat) =
  Pulse.Lib.Core.as_atomic _ _ (version_store_impl version newv #old)

fn version_store_bool_impl (version:ref nat) (newv:nat) (#old:erased nat)
  requires version |-> old
  returns b:bool
  ensures version |-> newv ** pure (b == true)
{
  version := newv;
  intro_pure (true == true) ();
  true
}

let version_store_bool_atomic (version:ref nat) (newv:nat) (#old:erased nat) =
  Pulse.Lib.Core.as_atomic _ _ (version_store_bool_impl version newv #old)

fn data_write_slot_impl (data:array val_t) (i:SZ.t) (v_i:val_t)
    (#s:erased (Seq.seq val_t){SZ.v i < Seq.length s})
  requires A.pts_to data s
  ensures A.pts_to data (Seq.upd s (SZ.v i) v_i)
{
  data.(i) <- v_i
}

let data_write_slot_atomic (data:array val_t) (i:SZ.t) (v_i:val_t)
    (#s:erased (Seq.seq val_t){SZ.v i < Seq.length s}) =
  Pulse.Lib.Core.as_atomic _ _ (data_write_slot_impl data i v_i #s)

let writer_locked (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (data:array val_t) (n:nat) (start_ver:nat)
    (h:history val_t) (old_vs:list val_t) (new_vs:list val_t)
    (cur:Seq.seq val_t) : slprop =
  history_auth gh (1.0R /. 4.0R) h **
  mono_nat_auth gver (1.0R /. 2.0R) (start_ver + 1) **
  A.pts_to data #(1.0R /. 2.0R) cur **
  pure (start_ver % 2 == 0 /\ List.length old_vs == n /\
        List.length new_vs == n /\
        List.length h == history_len_for_version (start_ver + 1) /\
        last_opt h == Some new_vs /\ Seq.length cur == n)

ghost fn writer_locked_cur_length (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (data:array val_t) (n:nat) (start_ver:nat)
    (#h:erased (history val_t)) (#old_vs:erased (list val_t)) (#new_vs:erased (list val_t))
    (#cur:erased (Seq.seq val_t))
  preserves writer_locked gver gh data n start_ver (reveal h) (reveal old_vs) (reveal new_vs) cur
  ensures pure (Seq.length cur == n)
{
  unfold (writer_locked gver gh data n start_ver (reveal h) (reveal old_vs) (reveal new_vs) cur);
  assert (pure (Seq.length cur == n));
  intro_pure (Seq.length cur == n) ();
  fold (writer_locked gver gh data n start_ver (reveal h) (reveal old_vs) (reveal new_vs) cur)
}

ghost fn write_read_version_close (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#curr:nat) (#h:history val_t) (#vs:list val_t)
  requires seqlock_inv_body gver gh version data n curr h vs
  ensures seqlock_inv gver gh version data n ** mono_nat_lb gver curr
{
  unfold (seqlock_inv_body gver gh version data n curr h vs);
  let b = prop_as_bool (curr % 2 == 0);
  if b {
    t2b_true_of_prop (curr % 2 == 0);
    assert (pure (Prims.t2b (curr % 2 == 0) == true));
    elim_if_true_b (Prims.t2b (curr % 2 == 0))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver 1.0R curr **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 4.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) curr **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    mono_nat_lb_get gver #1.0R #curr;
    intro_pure (last_opt h == Some vs) ();
    pack_seqlock_inv_even gver gh version data n #curr #h #vs
  } else {
    t2b_false_of_not (curr % 2 == 0);
    assert (pure (Prims.t2b (curr % 2 == 0) == false));
    elim_if_false_b (Prims.t2b (curr % 2 == 0))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver 1.0R curr **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 4.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) curr **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    mono_nat_lb_get gver #(1.0R /. 2.0R) #curr;
    pack_seqlock_inv_odd gver gh version data n #curr #h #vs
  }
}

fn write_read_version
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat)
  requires inv n_inv (seqlock_inv gver gh version data n)
  returns ver:nat
  ensures inv n_inv (seqlock_inv gver gh version data n) ** mono_nat_lb gver ver
{
  let ver = with_invariants nat emp_inames n_inv (seqlock_inv gver gh version data n)
    emp (fun r -> mono_nat_lb gver r)
  fn _ {
    unfold (seqlock_inv gver gh version data n);
    with curr h vs. _;
    unfold (seqlock_inv_body gver gh version data n curr h vs);
    let r = version_read_atomic version #1.0R #(hide curr);
    assert (pure (r == curr));
    fold (seqlock_inv_body gver gh version data n curr h vs);
    write_read_version_close gver gh version data n #curr #h #vs;
    rewrite (mono_nat_lb gver curr) as (mono_nat_lb gver r);
    r
  };
  ver
}

fn write_try_lock
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat) (start_ver:nat)
   (#new_vs:erased (list val_t))
   (#is:inames) (phi:unit -> slprop)
   (tok : au_token is (list val_t) unit
      (fun vs -> value gh vs)
      (fun _ _ -> value gh (reveal new_vs))
      (fun _ r -> phi r))
  requires
    inv n_inv (seqlock_inv gver gh version data n) **
    au_available tok **
    pure (start_ver % 2 == 0 /\ List.length (reveal new_vs) == n)
  returns r:option (erased (history val_t & list val_t))
  ensures inv n_inv (seqlock_inv gver gh version data n) **
          (match r with
           | None -> au_available tok
           | Some info ->
             writer_locked gver gh data n start_ver
               (fst (reveal info)) (snd (reveal info)) (reveal new_vs)
               (seq_of_snapshot (snd (reveal info))) **
             phi ())
{
  later_credit_buy 3;
  let attempt = au_atomic_step
    #is #(add_inv emp_inames n_inv) #(list val_t) #unit
    #(fun vs -> value gh vs)
    #(fun _ _ -> value gh (reveal new_vs))
    #(fun _ r -> phi r)
    #(inv n_inv (seqlock_inv gver gh version data n))
    #(fun _ -> exists* (info:erased (history val_t & list val_t)).
        writer_locked gver gh data n start_ver
          (fst (reveal info)) (snd (reveal info)) (reveal new_vs)
          (seq_of_snapshot (snd (reveal info))))
    tok
  fn x {
    unfold (value gh (reveal x));
    with h_au. _;
    let r = with_invariants_a (option (erased (history val_t & list val_t))) emp_inames
      n_inv (seqlock_inv gver gh version data n)
      (history_auth gh (1.0R /. 2.0R) h_au **
       pure (last_opt h_au == Some (reveal x)))
      (fun r -> match r with
        | None -> value gh (reveal x)
        | Some info ->
          writer_locked gver gh data n start_ver
            (fst (reveal info)) (snd (reveal info)) (reveal new_vs)
            (seq_of_snapshot (snd (reveal info))) **
          value gh (reveal new_vs))
    fn _ {
      unfold (seqlock_inv gver gh version data n);
      with curr h vs. _;
      unfold (seqlock_inv_body gver gh version data n curr h vs);
      let next_ver : nat = start_ver + 1;
      let b = AP.cas_nat version start_ver next_ver #(hide curr);
      if b {
        elim_ap_cond_true
          (version |-> next_ver ** pure (curr == start_ver))
          (version |-> curr ** pure (~ (curr == start_ver)));
        assert (pure (curr == start_ver));
        rewrite each curr as start_ver;
        t2b_true_of_prop (start_ver % 2 == 0);
        assert (pure (Prims.t2b (start_ver % 2 == 0) == true));
        elim_if_true_b (Prims.t2b (start_ver % 2 == 0))
          (history_auth gh (1.0R /. 2.0R) h **
           mono_nat_auth gver 1.0R start_ver **
           A.pts_to data (seq_of_snapshot vs) **
           pure (last_opt h == Some vs))
          (history_auth gh (1.0R /. 4.0R) h **
           mono_nat_auth gver (1.0R /. 2.0R) start_ver **
           A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));

        history_auth_auth_agree gh #(1.0R /. 2.0R) #(1.0R /. 2.0R) #h #h_au;
        rewrite each h_au as h;
        assert (pure (reveal x == vs));
        history_gather gh #(1.0R /. 2.0R) #(1.0R /. 2.0R) #h #h;
        assert (pure ((1.0R /. 2.0R) +. (1.0R /. 2.0R) == 1.0R));
        rewrite (history_auth gh ((1.0R /. 2.0R) +. (1.0R /. 2.0R)) h)
          as (history_auth gh 1.0R h);
        history_extend gh #h (reveal new_vs);
        drop_ (history_frag gh (List.length h) (reveal new_vs) #(h @ [reveal new_vs]));
        last_opt_snoc h (reveal new_vs);
        history_share gh #1.0R #(h @ [reveal new_vs]);
        intro_pure (last_opt (h @ [reveal new_vs]) == Some (reveal new_vs)) ();
        fold (value gh (reveal new_vs));
        history_share gh #(1.0R /. 2.0R) #(h @ [reveal new_vs]);
        assert (pure (1.0R /. 2.0R /. 2.0R == 1.0R /. 4.0R));
        rewrite each (1.0R /. 2.0R /. 2.0R) as (1.0R /. 4.0R);

        A.share data #(seq_of_snapshot vs) #1.0R;
        mono_nat_update gver #start_ver (start_ver + 1);
        unfold (mono_nat_auth gver 1.0R (start_ver + 1));
        MGR.share #nat #mono_nat_increases gver #(start_ver + 1) #1.0R
          #(1.0R /. 2.0R) #(1.0R /. 2.0R);
        fold (mono_nat_auth gver (1.0R /. 2.0R) (start_ver + 1));
        fold (mono_nat_auth gver (1.0R /. 2.0R) (start_ver + 1));

        assert (pure ((start_ver + 1) % 2 <> 0));
        List.Tot.append_length h [reveal new_vs];
        assert (pure (List.length [reveal new_vs] == 1));
        assert (pure (List.length (h @ [reveal new_vs]) == List.length h + 1));
        assert (pure (List.length (h @ [reveal new_vs]) == history_len_for_version (start_ver + 1)));
        intro_pure (List.length vs == n /\
                    List.length (h @ [reveal new_vs]) == history_len_for_version (start_ver + 1)) ();
        pack_seqlock_inv_odd gver gh version data n #(start_ver + 1) #(h @ [reveal new_vs]) #vs;
        intro_pure (start_ver % 2 == 0 /\ List.length vs == n /\
                    List.length (reveal new_vs) == n /\
                    List.length (h @ [reveal new_vs]) == history_len_for_version (start_ver + 1) /\
                    last_opt (h @ [reveal new_vs]) == Some (reveal new_vs) /\
                    Seq.length (seq_of_snapshot vs) == n) ();
        fold (writer_locked gver gh data n start_ver (h @ [reveal new_vs]) vs (reveal new_vs)
          (seq_of_snapshot vs));
        Some (hide (h @ [reveal new_vs], vs))
      } else {
        elim_ap_cond_false
          (version |-> next_ver ** pure (curr == start_ver))
          (version |-> curr ** pure (~ (curr == start_ver)));
        drop_ (pure (~ (curr == start_ver)));
        fold (seqlock_inv_body gver gh version data n curr h vs);
        fold (seqlock_inv gver gh version data n);
        intro_pure (last_opt h_au == Some (reveal x)) ();
        fold (value gh (reveal x));
        None #(erased (history val_t & list val_t))
      }
    };
    match r {
    None -> {
      None #unit
    }
    Some info -> {
      intro_exists #(erased (history val_t & list val_t))
        (fun info -> writer_locked gver gh data n start_ver
          (fst (reveal info)) (snd (reveal info)) (reveal new_vs)
          (seq_of_snapshot (snd (reveal info)))) info;
      Some ()
    }
    }
  };
  match attempt {
  None -> {
    None #(erased (history val_t & list val_t))
  }
  Some y -> {
    with _x. assert (phi y ** (exists* (info:erased (history val_t & list val_t)).
      writer_locked gver gh data n start_ver
        (fst (reveal info)) (snd (reveal info)) (reveal new_vs)
        (seq_of_snapshot (snd (reveal info)))));
    with info. _;
    rewrite (phi y) as (phi ());
    Some info
  }
  }
}

fn write_copy_step
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat)
   (src:array val_t) (#dq:perm)
   (#srcs:erased (Seq.seq val_t))
   (#start_ver:erased nat) (#h:erased (history val_t))
   (#old_vs:erased (list val_t)) (#new_vs:erased (list val_t))
   (#cur:erased (Seq.seq val_t))
   (i:SZ.t{SZ.v i < n /\ SZ.v i < Seq.length srcs /\ SZ.v i < Seq.length cur})
  requires
       inv n_inv (seqlock_inv gver gh version data n)
    ** writer_locked gver gh data n (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur
    ** A.pts_to src #dq srcs
    ** pure (SZ.v i < n /\ Seq.length srcs == n /\ Seq.length cur == n /\
             seq_prefix_eq (SZ.v i) cur srcs)
  returns cur1:erased (Seq.seq val_t)
  ensures
       inv n_inv (seqlock_inv gver gh version data n)
    ** writer_locked gver gh data n (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur1
    ** A.pts_to src #dq srcs
    ** pure (reveal cur1 == Seq.upd cur (SZ.v i) (Seq.index srcs (SZ.v i)) /\
             Seq.length (reveal cur1) == n /\
             seq_prefix_eq (SZ.v i + 1) cur1 srcs)
{
  let v_i = src.(i);
  Seq.lemma_len_upd (SZ.v i) v_i cur;
  let cur1 : erased (Seq.seq val_t) = hide (Seq.upd cur (SZ.v i) v_i);
  let _ = with_invariants unit emp_inames n_inv (seqlock_inv gver gh version data n)
    (writer_locked gver gh data n (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur)
    (fun _ -> writer_locked gver gh data n (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur1)
  fn _ {
    unfold (writer_locked gver gh data n (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur);
    unfold (seqlock_inv gver gh version data n);
    with curr h_inv vs_inv. _;
    unfold (seqlock_inv_body gver gh version data n curr h_inv vs_inv);
    seqlock_read_case_intro gver gh data #curr #h_inv #vs_inv;
    unfold (seqlock_read_case gver gh data curr h_inv vs_inv);
    with hp vp dp. _;
    mono_nat_auth_auth_agree gver #(1.0R /. 2.0R) #vp #(reveal start_ver + 1) #curr;
    assert (pure (curr == reveal start_ver + 1));
    rewrite each curr as (reveal start_ver + 1);
    assert (pure ((reveal start_ver + 1) % 2 <> 0));
    assert (pure (hp == (1.0R /. 4.0R) /\ vp == (1.0R /. 2.0R) /\ dp == (1.0R /. 2.0R)));
    rewrite each hp as (1.0R /. 4.0R);
    rewrite each vp as (1.0R /. 2.0R);
    rewrite each dp as (1.0R /. 2.0R);
    history_auth_auth_agree gh;
    rewrite each h_inv as (reveal h);
    A.pts_to_injective_eq data;
    A.gather data;
    data_write_slot_atomic data i v_i #cur;
    Seq.lemma_len_upd (SZ.v i) v_i cur;
    A.share data #(Seq.upd cur (SZ.v i) v_i) #1.0R;
    Seq.lemma_seq_of_seq_to_list (reveal cur1);
    rewrite (A.pts_to data #(1.0R /. 2.0R) (reveal cur1))
      as (A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot (snapshot_of_seq (reveal cur1))));
    assert (pure (List.length (snapshot_of_seq (reveal cur1)) == n));
    assert (pure (List.length (reveal h) == history_len_for_version (reveal start_ver + 1)));
    intro_pure (List.length (snapshot_of_seq (reveal cur1)) == n /\
                List.length (reveal h) == history_len_for_version (reveal start_ver + 1)) ();
    pack_seqlock_inv_odd gver gh version data n #(reveal start_ver + 1)
      #(reveal h) #(snapshot_of_seq (reveal cur1));
    intro_pure (reveal start_ver % 2 == 0 /\ List.length (reveal old_vs) == n /\
                List.length (reveal new_vs) == n /\
                List.length (reveal h) == history_len_for_version (reveal start_ver + 1) /\
                last_opt (reveal h) == Some (reveal new_vs) /\
                Seq.length (reveal cur1) == n) ();
    fold (writer_locked gver gh data n (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur1)
  };
  seq_prefix_eq_succ (SZ.v i) cur srcs;
  assert (pure (reveal cur1 == Seq.upd cur (SZ.v i) (Seq.index srcs (SZ.v i))));
  intro_pure (reveal cur1 == Seq.upd cur (SZ.v i) (Seq.index srcs (SZ.v i)) /\
              Seq.length (reveal cur1) == n /\
              seq_prefix_eq (SZ.v i + 1) cur1 srcs) ();
  cur1
}

fn rec write_copy_aux
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (i:SZ.t) (src:array val_t) (#dq:perm)
   (#srcs:erased (Seq.seq val_t))
   (#start_ver:erased nat) (#h:erased (history val_t))
   (#old_vs:erased (list val_t)) (#new_vs:erased (list val_t))
   (#cur:erased (Seq.seq val_t))
  requires
       inv n_inv (seqlock_inv gver gh version data (SZ.v n))
    ** writer_locked gver gh data (SZ.v n) (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur
    ** A.pts_to src #dq srcs
    ** pure (SZ.v i <= SZ.v n /\ Seq.length srcs == SZ.v n /\ Seq.length cur == SZ.v n /\
             seq_prefix_eq (SZ.v i) cur srcs)
  ensures
       inv n_inv (seqlock_inv gver gh version data (SZ.v n))
    ** writer_locked gver gh data (SZ.v n) (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) srcs
    ** A.pts_to src #dq srcs
  decreases (SZ.v n - SZ.v i)
{
  if (i = n) {
    assert (pure (SZ.v i == SZ.v n));
    seq_prefix_eq_all cur srcs;
    rewrite (writer_locked gver gh data (SZ.v n) (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) cur)
      as (writer_locked gver gh data (SZ.v n) (reveal start_ver) (reveal h) (reveal old_vs) (reveal new_vs) srcs)
  } else {
    assert (pure (SZ.v i < SZ.v n));
    SZ.fits_lte (SZ.v i + 1) (SZ.v n);
    let cur1 = write_copy_step #gver #gh #n_inv version data (SZ.v n) src #dq #srcs
      #start_ver #h #old_vs #new_vs #cur i;
    let i1 = SZ.add i 1sz;
    assert (pure (SZ.v i1 == SZ.v i + 1));
    write_copy_aux #gver #gh #n_inv version data n i1 src #dq #srcs
      #start_ver #h #old_vs #new_vs #cur1
  }
}

fn write_unlock
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (start_ver:nat) (#h:erased (history val_t))
   (#old_vs:erased (list val_t)) (#new_vs:erased (list val_t))
  requires
       inv n_inv (seqlock_inv gver gh version data (SZ.v n))
    ** writer_locked gver gh data (SZ.v n) start_ver (reveal h) (reveal old_vs)
         (reveal new_vs) (seq_of_snapshot (reveal new_vs))
    ** pure (List.length (reveal new_vs) == SZ.v n)
  ensures
       inv n_inv (seqlock_inv gver gh version data (SZ.v n))
    ** pure (List.length (reveal new_vs) == SZ.v n)
{
  let stored = with_invariants bool emp_inames
    n_inv (seqlock_inv gver gh version data (SZ.v n))
    (writer_locked gver gh data (SZ.v n) start_ver (reveal h) (reveal old_vs)
       (reveal new_vs) (seq_of_snapshot (reveal new_vs)))
    (fun b -> pure (b == true))
  fn _ {
    unfold (writer_locked gver gh data (SZ.v n) start_ver (reveal h) (reveal old_vs)
      (reveal new_vs) (seq_of_snapshot (reveal new_vs)));
    unfold (seqlock_inv gver gh version data (SZ.v n));
    with curr h_inv vs_inv. _;
    unfold (seqlock_inv_body gver gh version data (SZ.v n) curr h_inv vs_inv);
    seqlock_read_case_intro gver gh data #curr #h_inv #vs_inv;
    unfold (seqlock_read_case gver gh data curr h_inv vs_inv);
    with hp vp dp. _;
    mono_nat_auth_auth_agree gver #(1.0R /. 2.0R) #vp #(start_ver + 1) #curr;
    assert (pure (curr == start_ver + 1));
    rewrite each curr as (start_ver + 1);
    assert (pure ((start_ver + 1) % 2 <> 0));
    assert (pure (hp == (1.0R /. 4.0R) /\ vp == (1.0R /. 2.0R) /\ dp == (1.0R /. 2.0R)));
    rewrite each hp as (1.0R /. 4.0R);
    rewrite each vp as (1.0R /. 2.0R);
    rewrite each dp as (1.0R /. 2.0R);
    let stored = version_store_bool_atomic version (start_ver + 2) #(hide (start_ver + 1));

    history_auth_auth_agree gh #(1.0R /. 4.0R) #(1.0R /. 4.0R) #(reveal h) #h_inv;
    rewrite each h_inv as (reveal h);
    A.pts_to_injective_eq data;
    A.gather data;
    mono_nat_gather gver #(1.0R /. 2.0R) #(1.0R /. 2.0R)
      #(start_ver + 1) #(start_ver + 1);
    assert (pure ((1.0R /. 2.0R) +. (1.0R /. 2.0R) == 1.0R));
    rewrite (mono_nat_auth gver ((1.0R /. 2.0R) +. (1.0R /. 2.0R)) (start_ver + 1))
      as (mono_nat_auth gver 1.0R (start_ver + 1));
    mono_nat_update gver #(start_ver + 1) (start_ver + 2);

    history_gather gh #(1.0R /. 4.0R) #(1.0R /. 4.0R) #(reveal h) #(reveal h);
    assert (pure ((1.0R /. 4.0R) +. (1.0R /. 4.0R) == (1.0R /. 2.0R)));
    rewrite (history_auth gh ((1.0R /. 4.0R) +. (1.0R /. 4.0R)) (reveal h))
      as (history_auth gh (1.0R /. 2.0R) (reveal h));
    assert (pure (start_ver % 2 == 0));
    assert (pure ((start_ver + 2) % 2 == 0));
    assert (pure (List.length (reveal h) == history_len_for_version (start_ver + 2)));
    intro_pure (List.length (reveal new_vs) == SZ.v n /\
                List.length (reveal h) == history_len_for_version (start_ver + 2)) ();
    intro_pure (last_opt (reveal h) == Some (reveal new_vs)) ();
    pack_seqlock_inv_even gver gh version data (SZ.v n) #(start_ver + 2)
      #(reveal h) #(reveal new_vs);
    stored
  };
  drop_ (pure (stored == true));
  intro_pure (List.length (reveal new_vs) == SZ.v n) ()
}

let write_frame (gh:gname val_t) (n:SZ.t) (v:big_atomic) (src:array val_t)
    (#dq:perm) (#vs:erased (list val_t)) : slprop =
  is_seqlock v gh (SZ.v n) **
  A.pts_to src #dq (seq_of_snapshot (reveal vs)) **
  pure (List.length (reveal vs) == SZ.v n)

fn rec write (#gh:gname val_t) (n:SZ.t) (v:big_atomic) (src:array val_t)
    (#dq:perm) (#vs':erased (list val_t))
    (#is:inames) (phi:unit -> slprop)
    (tok : au_token is (list val_t) unit
      (fun vs -> value gh vs)
      (fun _ _ -> value gh (reveal vs'))
      (fun _ r -> phi r))
    (_u:unit)
  requires
       write_frame gh n v src #dq #vs'
    ** au_available tok
  returns r:unit
  ensures
       write_frame gh n v src #dq #vs'
    ** phi r
{
  unfold (write_frame gh n v src #dq #vs');
  unfold (is_seqlock v gh (SZ.v n));
  with gver n_inv. _;
  let version = fst v;
  let data = snd v;
  rewrite (inv n_inv (seqlock_inv gver gh (fst v) (snd v) (SZ.v n)))
    as (inv n_inv (seqlock_inv gver gh version data (SZ.v n)));
  let ver = write_read_version #gver #gh #n_inv version data (SZ.v n);
  if (ver % 2 = 0) {
    let locked = write_try_lock #gver #gh #n_inv version data (SZ.v n) ver #vs' #is phi tok;
    drop_ (mono_nat_lb gver ver);
    match locked {
    None -> {
      fold (is_seqlock v gh (SZ.v n));
      fold (write_frame gh n v src #dq #vs');
      write #gh n v src #dq #vs' #is phi tok ()
    }
    Some info -> {
      let locked_h : erased (history val_t) = hide (fst (reveal info));
      let old_vs : erased (list val_t) = hide (snd (reveal info));
      let srcs : erased (Seq.seq val_t) = hide (seq_of_snapshot (reveal vs'));
      let cur0 : erased (Seq.seq val_t) = hide (seq_of_snapshot (reveal old_vs));
      assert (pure (Seq.length srcs == SZ.v n));
      rewrite (writer_locked gver gh data (SZ.v n) ver (fst (reveal info)) (snd (reveal info))
                 (reveal vs') (seq_of_snapshot (snd (reveal info))))
        as (writer_locked gver gh data (SZ.v n) ver (reveal locked_h) (reveal old_vs) (reveal vs') cur0);
      writer_locked_cur_length gver gh data (SZ.v n) ver #locked_h #old_vs #vs' #cur0;
      assert (pure (seq_prefix_eq 0 cur0 srcs));
      write_copy_aux #gver #gh #n_inv version data n 0sz src #dq #srcs
        #(hide ver) #locked_h #old_vs #vs' #cur0;
      rewrite (writer_locked gver gh data (SZ.v n) ver (reveal locked_h) (reveal old_vs) (reveal vs') srcs)
        as (writer_locked gver gh data (SZ.v n) (reveal (hide ver)) (reveal locked_h) (reveal old_vs)
              (reveal vs') (seq_of_snapshot (reveal vs')));
      write_unlock #gver #gh #n_inv version data n ver #locked_h #old_vs #vs';
      fold (is_seqlock v gh (SZ.v n));
      fold (write_frame gh n v src #dq #vs')
    }
    }
  } else {
    drop_ (mono_nat_lb gver ver);
    fold (is_seqlock v gh (SZ.v n));
    fold (write_frame gh n v src #dq #vs');
    write #gh n v src #dq #vs' #is phi tok ()
  }
}

let write_is_lat (#gh:gname val_t) (n:SZ.t) (v:big_atomic) (src:array val_t)
    (#dq:perm) (#vs':erased (list val_t)) (#is:inames)
  : lat is (list val_t) unit
      (fun vs -> value gh vs)
      (fun _ _ -> value gh (reveal vs'))
      (write_frame gh n v src #dq #vs')
  = write #gh n v src #dq #vs'

(* -------------------------------------------------------------------------- *)
(* Reader-side helpers                                                        *)
(* -------------------------------------------------------------------------- *)

let read_start_frag (gh:gname val_t) (ver:nat) (n:nat) : slprop =
  exists* (h:history val_t) (vs:list val_t).
    history_frag gh (ver / 2) vs #h **
    pure (ver % 2 == 0 /\ List.length vs == n)

let read_start_evidence (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (ver:nat) (n:nat) : slprop =
  mono_nat_lb gver ver ** read_start_frag gh ver n

let snapshot_values_match_from (i:nat) (n:nat)
    (vals:Seq.seq val_t) (vs:list val_t) : prop =
  forall (k:nat). i <= k /\ k < n ==>
    seq_index_or #val_t 0 vals k == seq_index_or #val_t 0 (seq_of_snapshot vs) k

ghost fn snapshot_evidence_dup_lb (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (ver_i:nat) (v_i:val_t)
  requires snapshot_evidence gver gh i ver_i v_i
  ensures snapshot_evidence gver gh i ver_i v_i ** mono_nat_lb gver ver_i
{
  unfold (snapshot_evidence gver gh i ver_i v_i);
  let b = prop_as_bool (ver_i % 2 == 0);
  if b {
    t2b_true_of_prop (ver_i % 2 == 0);
    assert (pure (Prims.t2b (ver_i % 2 == 0) == true));
    elim_if_true_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    dup_mono_nat_lb gver ver_i;
    intro_cond_true_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    fold (snapshot_evidence gver gh i ver_i v_i)
  } else {
    t2b_false_of_not (ver_i % 2 == 0);
    assert (pure (Prims.t2b (ver_i % 2 == 0) == false));
    elim_if_false_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    dup_mono_nat_lb gver ver_i;
    intro_cond_false_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    fold (snapshot_evidence gver gh i ver_i v_i)
  }
}

ghost fn snapshot_evidence_open_even (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (ver_i:nat) (v_i:val_t)
  requires snapshot_evidence gver gh i ver_i v_i
  requires pure (ver_i % 2 == 0)
  ensures mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i
{
  unfold (snapshot_evidence gver gh i ver_i v_i);
  t2b_true_of_prop (ver_i % 2 == 0);
  assert (pure (Prims.t2b (ver_i % 2 == 0) == true));
  elim_if_true_b (Prims.t2b (ver_i % 2 == 0))
    (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
    (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0))
}

ghost fn unpack_big_snapshot_evidence_nil (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires big_snapshot_evidence_from gver gh i n vers vals
  requires pure (i >= n)
  ensures emp
{
  unfold (big_snapshot_evidence_from gver gh i n vers vals);
  assert (pure ((i < n) == false));
  elim_if_false_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp
}

ghost fn unpack_big_snapshot_evidence_cons (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires big_snapshot_evidence_from gver gh i n vers vals
  requires pure (i < n)
  ensures snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
          big_snapshot_evidence_from gver gh (i + 1) n vers vals
{
  unfold (big_snapshot_evidence_from gver gh i n vers vals);
  assert (pure ((i < n) == true));
  elim_if_true_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp
}

ghost fn rec read_snapshot_consistent_from
    (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (ver:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
    (hcur:history val_t) (vs0:list val_t)
  requires big_snapshot_evidence_from gver gh i n vers vals
  preserves mono_nat_auth gver 1.0R ver
  preserves history_auth gh (1.0R /. 2.0R) hcur
  requires pure (i <= n /\ ver % 2 == 0 /\ Seq.length vals == n /\
                 List.length vs0 == n /\ versions_ge_from ver i n vers /\
                 List.nth hcur (ver / 2) == Some vs0)
  ensures pure (snapshot_values_match_from i n vals vs0)
  decreases (n - i)
{
  if (i < n) {
    unpack_big_snapshot_evidence_cons gver gh i n vers vals;
    let ver_i = seq_index_or #nat 0 vers i;
    let v_i = seq_index_or #val_t 0 vals i;
    rewrite (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i))
      as (snapshot_evidence gver gh i ver_i v_i);
    snapshot_evidence_dup_lb gver gh i ver_i v_i;
    mono_nat_lb_valid gver #1.0R #ver #ver_i;
    assert (pure (ver <= ver_i));
    assert (pure (ver_i <= ver));
    assert (pure (ver_i == ver));
    rewrite each ver_i as ver;
    snapshot_evidence_open_even gver gh i ver v_i;
    drop_ (mono_nat_lb gver ver);
    drop_ (mono_nat_lb gver ver);
    unfold (snapshot_even_evidence_payload gh i ver v_i);
    with vsi hi. _;
    history_auth_frag_agree gh #(1.0R /. 2.0R) #hcur (ver / 2) vsi #hi;
    assert (pure (vsi == vs0));
    rewrite each vsi as vs0;
    assert (pure (List.nth vs0 i == Some v_i));
    seq_of_snapshot_nth vs0 i;
    seq_index_or_index #val_t 0 vals i;
    assert (pure (seq_index_or #val_t 0 vals i == seq_index_or #val_t 0 (seq_of_snapshot vs0) i));
    assert (pure (versions_ge_from ver (i + 1) n vers));
    read_snapshot_consistent_from gver gh (i + 1) n ver vers vals hcur vs0;
    assert (pure (snapshot_values_match_from (i + 1) n vals vs0));
    assert (pure (snapshot_values_match_from i n vals vs0))
  } else {
    unpack_big_snapshot_evidence_nil gver gh i n vers vals;
    assert (pure (snapshot_values_match_from i n vals vs0))
  }
}

ghost fn read_snapshot_consistent (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (n:nat) (ver:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
    (hcur:history val_t) (vs0:list val_t)
  requires big_snapshot_evidence gver gh ver n vers vals
  preserves mono_nat_auth gver 1.0R ver
  preserves history_auth gh (1.0R /. 2.0R) hcur
  requires pure (ver % 2 == 0 /\ List.length vs0 == n /\
                 List.nth hcur (ver / 2) == Some vs0)
  ensures pure (vals == seq_of_snapshot vs0)
{
  unfold (big_snapshot_evidence gver gh ver n vers vals);
  assert (pure (Seq.length vals == n));
  assert (pure (versions_ge_from ver 0 n vers));
  read_snapshot_consistent_from gver gh 0 n ver vers vals hcur vs0;
  assert (pure (snapshot_values_match_from 0 n vals vs0));
  assert (pure (Seq.length (seq_of_snapshot vs0) == n));
  Seq.lemma_eq_intro vals (seq_of_snapshot vs0);
  Seq.lemma_eq_elim vals (seq_of_snapshot vs0);
  assert (pure (vals == seq_of_snapshot vs0))
}

fn read_first_even
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat)
  requires inv n_inv (seqlock_inv gver gh version data n)
  returns r:option nat
  ensures inv n_inv (seqlock_inv gver gh version data n) **
          (match r with
           | None -> emp
           | Some ver -> read_start_evidence gver gh ver n)
{
  let r = with_invariants (option nat) emp_inames n_inv (seqlock_inv gver gh version data n)
    emp
    (fun r -> match r with
      | None -> emp
      | Some ver -> read_start_evidence gver gh ver n)
  fn _ {
    unfold (seqlock_inv gver gh version data n);
    with curr h vs. _;
    unfold (seqlock_inv_body gver gh version data n curr h vs);
    let observed = version_read_atomic version #1.0R #(hide curr);
    assert (pure (observed == curr));
    if (observed % 2 = 0) {
      rewrite each curr as observed;
      t2b_true_of_prop (observed % 2 == 0);
      assert (pure (Prims.t2b (observed % 2 == 0) == true));
      elim_if_true_b (Prims.t2b (observed % 2 == 0))
        (history_auth gh (1.0R /. 2.0R) h **
         mono_nat_auth gver 1.0R observed **
         A.pts_to data (seq_of_snapshot vs) **
         pure (last_opt h == Some vs))
        (history_auth gh (1.0R /. 4.0R) h **
         mono_nat_auth gver (1.0R /. 2.0R) observed **
         A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
      mono_nat_lb_get gver #1.0R #observed;
      last_opt_nth h (observed / 2) vs;
      history_frag_alloc gh #(1.0R /. 2.0R) #h (observed / 2) vs;
      intro_pure (last_opt h == Some vs) ();
      intro_pure (List.length vs == n /\ List.length h == history_len_for_version observed) ();
      pack_seqlock_inv_even gver gh version data n #observed #h #vs;
      intro_pure (observed % 2 == 0 /\ List.length vs == n) ();
      fold (read_start_frag gh observed n);
      fold (read_start_evidence gver gh observed n);
      Some observed
    } else {
      rewrite each curr as observed;
      t2b_false_of_not (observed % 2 == 0);
      assert (pure (Prims.t2b (observed % 2 == 0) == false));
      elim_if_false_b (Prims.t2b (observed % 2 == 0))
        (history_auth gh (1.0R /. 2.0R) h **
         mono_nat_auth gver 1.0R observed **
         A.pts_to data (seq_of_snapshot vs) **
         pure (last_opt h == Some vs))
        (history_auth gh (1.0R /. 4.0R) h **
         mono_nat_auth gver (1.0R /. 2.0R) observed **
         A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
      intro_pure (List.length vs == n /\ List.length h == history_len_for_version observed) ();
      pack_seqlock_inv_odd gver gh version data n #observed #h #vs;
      None #nat
    }
  };
  r
}

let read_attempt_frame (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (n_inv:iname) (version:ref nat) (data:array val_t) (n:SZ.t)
    (ver:nat) (dst:array val_t) (vdst:Seq.seq val_t) (vers:Seq.seq nat) : slprop =
  inv n_inv (seqlock_inv gver gh version data (SZ.v n)) **
  A.pts_to dst vdst **
  read_start_frag gh ver (SZ.v n) **
  big_snapshot_evidence gver gh ver (SZ.v n) vers vdst **
  pure (Seq.length vdst == SZ.v n /\ is_full_array dst)

fn read_try_commit
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (ver:nat) (dst:array val_t)
   (#vdst:erased (Seq.seq val_t)) (#vers:erased (Seq.seq nat))
   (#is:inames) (phi:array val_t -> slprop)
   (tok : au_token is (list val_t) (array val_t)
      (fun vs -> value gh vs)
      (fun vs copy -> value gh vs ** A.pts_to copy (seq_of_snapshot vs))
      (fun _ copy -> phi copy))
  requires read_attempt_frame gver gh n_inv version data n ver dst vdst vers **
           au_available tok
  returns r:option (array val_t)
  ensures (match r with
    | None -> read_attempt_frame gver gh n_inv version data n ver dst vdst vers **
              au_available tok
    | Some copy -> inv n_inv (seqlock_inv gver gh version data (SZ.v n)) **
                   phi copy)
{
  later_credit_buy 3;
  let attempt = au_atomic_step
    #is #(add_inv emp_inames n_inv) #(list val_t) #(array val_t)
    #(fun vs -> value gh vs)
    #(fun vs copy -> value gh vs ** A.pts_to copy (seq_of_snapshot vs))
    #(fun _ copy -> phi copy)
    #(read_attempt_frame gver gh n_inv version data n ver dst (reveal vdst) (reveal vers))
    #(fun _ -> inv n_inv (seqlock_inv gver gh version data (SZ.v n)))
    tok
  fn x {
    unfold (read_attempt_frame gver gh n_inv version data n ver dst (reveal vdst) (reveal vers));
    unfold (value gh (reveal x));
    with h_au. _;
    let res = with_invariants_a (option (array val_t)) emp_inames
      n_inv (seqlock_inv gver gh version data (SZ.v n))
      (A.pts_to dst (reveal vdst) **
       read_start_frag gh ver (SZ.v n) **
       big_snapshot_evidence gver gh ver (SZ.v n) (reveal vers) (reveal vdst) **
       pure (Seq.length (reveal vdst) == SZ.v n /\ is_full_array dst) **
       history_auth gh (1.0R /. 2.0R) h_au **
       pure (last_opt h_au == Some (reveal x)))
      (fun res -> match res with
        | None -> A.pts_to dst (reveal vdst) **
                  read_start_frag gh ver (SZ.v n) **
                  big_snapshot_evidence gver gh ver (SZ.v n) (reveal vers) (reveal vdst) **
                  pure (Seq.length (reveal vdst) == SZ.v n /\ is_full_array dst) **
                  value gh (reveal x)
        | Some copy -> value gh (reveal x) ** A.pts_to copy (seq_of_snapshot (reveal x)))
    fn _ {
      unfold (seqlock_inv gver gh version data (SZ.v n));
      with curr hcur vscur. _;
      unfold (seqlock_inv_body gver gh version data (SZ.v n) curr hcur vscur);
      let observed = version_read_atomic version #1.0R #(hide curr);
      assert (pure (observed == curr));
      if (observed = ver) {
        rewrite each curr as ver;
        unfold (read_start_frag gh ver (SZ.v n));
        with h0 vs0. _;
        assert (pure (ver % 2 == 0));
        t2b_true_of_prop (ver % 2 == 0);
        assert (pure (Prims.t2b (ver % 2 == 0) == true));
        elim_if_true_b (Prims.t2b (ver % 2 == 0))
          (history_auth gh (1.0R /. 2.0R) hcur **
           mono_nat_auth gver 1.0R ver **
           A.pts_to data (seq_of_snapshot vscur) **
           pure (last_opt hcur == Some vscur))
          (history_auth gh (1.0R /. 4.0R) hcur **
           mono_nat_auth gver (1.0R /. 2.0R) ver **
           A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vscur));
        history_auth_frag_agree gh #(1.0R /. 2.0R) #hcur (ver / 2) vs0 #h0;
        last_opt_nth hcur (ver / 2) vscur;
        assert (pure (vs0 == vscur));
        history_auth_auth_agree gh #(1.0R /. 2.0R) #(1.0R /. 2.0R) #hcur #h_au;
        rewrite each h_au as hcur;
        assert (pure (reveal x == vscur));
        read_snapshot_consistent gver gh (SZ.v n) ver (reveal vers) (reveal vdst) hcur vs0;
        rewrite each (reveal vdst) as (seq_of_snapshot vs0);
        rewrite each vs0 as (reveal x);
        intro_pure (List.length vscur == SZ.v n /\ List.length hcur == history_len_for_version ver) ();
        intro_pure (last_opt hcur == Some vscur) ();
        pack_seqlock_inv_even gver gh version data (SZ.v n) #ver #hcur #vscur;
        intro_pure (last_opt hcur == Some (reveal x)) ();
        fold (value gh (reveal x));
        Some dst
      } else {
        fold (seqlock_inv_body gver gh version data (SZ.v n) curr hcur vscur);
        fold (seqlock_inv gver gh version data (SZ.v n));
        intro_pure (last_opt h_au == Some (reveal x)) ();
        fold (value gh (reveal x));
        None #(array val_t)
      }
    };
    match res {
    None -> {
      fold (read_attempt_frame gver gh n_inv version data n ver dst (reveal vdst) (reveal vers));
      None #(array val_t)
    }
    Some copy -> {
      Some copy
    }
    }
  };
  match attempt {
  None -> {
    None #(array val_t)
  }
  Some copy -> {
    with _x. assert (phi copy ** inv n_inv (seqlock_inv gver gh version data (SZ.v n)));
    Some copy
  }
  }
}

let read_frame (gh:gname val_t) (n:SZ.t) (v:big_atomic) : slprop =
  is_seqlock v gh (SZ.v n) ** pure (SZ.v n > 0)

fn rec read (#gh:gname val_t) (n:SZ.t) (v:big_atomic)
    (#is:inames) (phi:array val_t -> slprop)
    (tok : au_token is (list val_t) (array val_t)
      (fun vs -> value gh vs)
      (fun vs copy -> value gh vs ** A.pts_to copy (seq_of_snapshot vs))
      (fun _ copy -> phi copy))
    (_u:unit)
  requires read_frame gh n v ** au_available tok
  returns copy:array val_t
  ensures read_frame gh n v ** phi copy
{
  unfold (read_frame gh n v);
  unfold (is_seqlock v gh (SZ.v n));
  with gver n_inv. _;
  let version = fst v;
  let data = snd v;
  rewrite (inv n_inv (seqlock_inv gver gh (fst v) (snd v) (SZ.v n)))
    as (inv n_inv (seqlock_inv gver gh version data (SZ.v n)));
  let first = read_first_even #gver #gh #n_inv version data (SZ.v n);
  match first {
  None -> {
    fold (is_seqlock v gh (SZ.v n));
    fold (read_frame gh n v);
    read #gh n v #is phi tok ()
  }
  Some ver -> {
    unfold (read_start_evidence gver gh ver (SZ.v n));
    let dst = A.alloc #val_t 0 n;
    let vdst0 : erased (Seq.seq val_t) = hide (Seq.create (SZ.v n) 0);
    rewrite (A.pts_to dst (Seq.create (SZ.v n) 0)) as (A.pts_to dst vdst0);
    let vdst' = snapshot_copy #gver #gh #n_inv version data n ver dst #vdst0;
    with vers. _;
    fold (read_attempt_frame gver gh n_inv version data n ver dst (reveal vdst') vers);
    let committed = read_try_commit #gver #gh #n_inv version data n ver dst #vdst' #(hide vers) #is phi tok;
    match committed {
    Some copy -> {
      rewrite (inv n_inv (seqlock_inv gver gh version data (SZ.v n)))
        as (inv n_inv (seqlock_inv gver gh (fst v) (snd v) (SZ.v n)));
      fold (is_seqlock v gh (SZ.v n));
      fold (read_frame gh n v);
      copy
    }
    None -> {
      unfold (read_attempt_frame gver gh n_inv version data n ver dst (reveal vdst') vers);
      A.free dst #vdst';
      drop_ (read_start_frag gh ver (SZ.v n));
      drop_ (big_snapshot_evidence gver gh ver (SZ.v n) vers (reveal vdst'));
      drop_ (pure (Seq.length (reveal vdst') == SZ.v n /\ is_full_array dst));
      rewrite (inv n_inv (seqlock_inv gver gh version data (SZ.v n)))
        as (inv n_inv (seqlock_inv gver gh (fst v) (snd v) (SZ.v n)));
      fold (is_seqlock v gh (SZ.v n));
      fold (read_frame gh n v);
      read #gh n v #is phi tok ()
    }
    }
  }
  }
}

let read_is_lat (#gh:gname val_t) (n:SZ.t) (v:big_atomic) (#is:inames)
  : lat is (list val_t) (array val_t)
      (fun vs -> value gh vs)
      (fun vs copy -> value gh vs ** A.pts_to copy (seq_of_snapshot vs))
      (read_frame gh n v)
  = read #gh n v
