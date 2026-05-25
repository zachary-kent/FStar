(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Treiber Stack v2 — faithful to Iris/HeapLang atomicity model.
    
    Uses only Pulse.Lib.AtomicPrimitives (single-step atomic ops).
    No as_atomic outside the kernel.
    
    Key differences from v1:
    - Nodes are raw boxes (not LinkedList), matching Iris's HeapLang encoding
    - Allocation happens OUTSIDE the invariant
    - Only CAS on the head pointer is inside the invariant
    - Ghost state tracks abstract list contents
    - Persistent is_list predicate (∃q. l↦{q}v) — duplicable, Iris-faithful *)
module PulseTutorial.TreiberStack2
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.AtomicPrimitives
open Pulse.Lib.PersistentPtsTo
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
open Pulse.Lib.Inv
open Pulse.Lib.Trade
open Pulse.Lib.Forall
module AP = Pulse.Lib.AtomicPrimitives

(* Use AtomicPrimitives.cond for consistency *)
ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q
  ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q
  ensures q
{ unfold AP.cond }

ghost fn intro_cond_true (p q : slprop)
  requires p
  ensures AP.cond true p q
{ fold (AP.cond true p q) }

ghost fn intro_cond_false (p q : slprop)
  requires q
  ensures AP.cond false p q
{ fold (AP.cond false p q) }

(* ================================================================ *)
(* Node representation — raw boxes, no LinkedList                   *)
(* ================================================================ *)

(* A node is a (value, next) pair. next is a box pointer; null = empty *)
noeq type node (t:Type0) = { value : t; nd_next : B.box (node t); }

(* Null sentinel — using B.null *)
let is_null_node (#t:Type0) (n : B.box (node t)) : bool = B.is_null n

(* ================================================================ *)
(* Persistent is_list: uses persistent_pts_to for node contents     *)
(* Duplicable — can be used outside the invariant                   *)
(* ================================================================ *)

let rec is_list (#t:Type0) (hd : B.box (node t)) (xs : list t)
  : Tot slprop (decreases xs) =
  match xs with
  | [] -> pure (hd == B.null)
  | x :: rest -> exists* (nd : node t).
      persistent_pts_to hd nd ** pure (nd.value == x) ** is_list nd.nd_next rest

ghost fn rec dup_is_list (#t:Type0) (hd : B.box (node t)) (xs : list t)
  requires is_list hd xs
  ensures is_list hd xs ** is_list hd xs
  decreases xs
{
  match xs {
    Nil -> {
      unfold is_list;
      fold (is_list #t hd []);
      rewrite (is_list #t hd []) as (is_list hd xs);
      fold (is_list #t hd []);
      rewrite (is_list #t hd []) as (is_list hd xs)
    }
    Cons x rest -> {
      unfold is_list;
      with nd. assert (persistent_pts_to hd nd ** pure (nd.value == x) ** is_list nd.nd_next rest);
      dup_persistent hd #nd;
      dup_is_list nd.nd_next rest;
      fold (is_list hd (x :: rest));
      rewrite (is_list hd (x :: rest)) as (is_list hd xs);
      fold (is_list hd (x :: rest));
      rewrite (is_list hd (x :: rest)) as (is_list hd xs)
    }
  }
}

(* Stack invariant: uses persistent is_list directly.
   Nodes are immutable after allocation — persistent ownership suffices.
   is_list is duplicable, so we can extract copies outside the invariant. *)

noeq type ts_ghost (t:Type0) = { gr : GR.ref (list t); }

noeq type tstack2 (t:Type0) = {
  head : B.box (B.box (node t));
  nm   : ts_ghost t;
  inm  : iname;
}

let scont2 (#t:Type0) (g:ts_ghost t) (xs:list t) : slprop = GR.pts_to g.gr #0.5R xs

let sinv_inner (#t:Type0) (head : B.box (B.box (node t))) (gr : GR.ref (list t)) : slprop =
  exists* (hd : B.box (node t)) (xs : list t).
    B.pts_to head hd ** is_list hd xs ** GR.pts_to gr #0.5R xs

let sinv (#t:Type0) (s:tstack2 t) : slprop = sinv_inner s.head s.nm.gr
let is_ts2 (#t:Type0) (s:tstack2 t) : slprop = inv s.inm (sinv s)

(* ================================================================ *)
(* new_stack                                                        *)
(* ================================================================ *)

fn new_stack2 (#t:Type0) ()
  requires emp
  returns s : tstack2 t
  ensures is_ts2 s ** scont2 s.nm []
{
  let head = B.alloc (B.null #(node t));
  let gr = GR.alloc #(list t) [];
  GR.share gr;
  let nm : ts_ghost t = { gr };
  rewrite (GR.pts_to gr #0.5R []) as (GR.pts_to nm.gr #0.5R []);
  rewrite (GR.pts_to gr #0.5R []) as (scont2 nm []);
  fold (is_list #t (B.null #(node t)) []);
  fold (sinv_inner head nm.gr);
  let inm = new_invariant (sinv_inner head nm.gr);
  let s : tstack2 t = { head; nm; inm };
  rewrite (inv inm (sinv_inner head nm.gr)) as (inv s.inm (sinv s));
  fold (is_ts2 s);
  rewrite (scont2 nm []) as (scont2 s.nm []);
  s
}

(* ================================================================ *)
(* push — alloc outside invariant, CAS inside                       *)
(* ================================================================ *)

(** read_head: atomic read of head pointer (single atomic_read inside invariant) *)
fn read_head2 (#t:Type0) (s:tstack2 t)
  requires is_ts2 s
  returns cur : B.box (node t)
  ensures is_ts2 s
{
  unfold is_ts2;
  let cur = with_invariants (B.box (node t)) emp_inames s.inm (sinv s)
    emp (fun _ -> emp)
  fn _ {
    unfold sinv; unfold sinv_inner;
    let c = atomic_read s.head;
    fold (sinv_inner s.head s.nm.gr); fold (sinv s);
    c
  };
  fold (is_ts2 s);
  cur
}

(** try_push2: CAS head from old_hd to new_node.
    is_list (persistent) stays in the invariant — duplicable.
    The new_node's pts_to is made persistent before linking.
    Faithful to Iris: one atomic CAS per invariant opening. *)
fn try_push2 (#t:Type0) (s:tstack2 t) (v:t) (old_hd new_node : B.box (node t))
    (#xs : erased (list t))
  requires is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs **
           persistent_pts_to new_node ({ value = v; nd_next = old_hd })
  returns b : bool
  ensures AP.cond b
    (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (v :: xs))
    (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs)
{
  unfold is_ts2;
  let b = with_invariants bool emp_inames s.inm (sinv s)
    (GR.pts_to s.nm.gr #0.5R xs **
     persistent_pts_to new_node ({ value = v; nd_next = old_hd }))
    (fun b -> AP.cond b
      (GR.pts_to s.nm.gr #0.5R (v :: xs))
      (GR.pts_to s.nm.gr #0.5R xs))
  fn _ {
    unfold sinv; unfold sinv_inner;
    let b = atomic_cas_box s.head old_hd new_node;
    if b {
      elim_cond_true _ _;
      with hd0 xs0. assert (
        B.pts_to s.head new_node ** pure (reveal (hide hd0) == old_hd) **
        is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 **
        GR.pts_to s.nm.gr #0.5R xs **
        persistent_pts_to new_node ({ value = v; nd_next = old_hd }));
      GR.pts_to_injective_eq s.nm.gr;
      rewrite each xs0 as (reveal xs);
      rewrite each hd0 as old_hd;
      // Build is_list new_node (v :: xs) from:
      //   persistent_pts_to new_node {value=v, next=old_hd}
      //   is_list old_hd xs (from invariant, persistent)
      fold (is_list new_node (v :: reveal xs));
      // Update ghost
      GR.gather s.nm.gr;
      GR.(s.nm.gr := v :: (reveal xs));
      GR.share s.nm.gr;
      fold (sinv_inner s.head s.nm.gr); fold (sinv s);
      fold (AP.cond true
        (GR.pts_to s.nm.gr #0.5R (v :: xs))
        (GR.pts_to s.nm.gr #0.5R xs));
      true
    } else {
      elim_cond_false _ _;
      // Drop the persistent_pts_to (it's duplicable, safe to drop)
      drop_ (persistent_pts_to new_node ({ value = v; nd_next = old_hd }));
      fold (sinv_inner s.head s.nm.gr); fold (sinv s);
      fold (AP.cond false
        (GR.pts_to s.nm.gr #0.5R (v :: xs))
        (GR.pts_to s.nm.gr #0.5R xs));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_ts2 s);
    intro_cond_true
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (v :: xs))
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs);
    true
  } else {
    elim_cond_false _ _;
    fold (is_ts2 s);
    intro_cond_false
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (v :: xs))
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs);
    false
  }
}

(** push_loop: CAS retry loop, parametric in the client's postcondition.
    Alloc happens HERE (outside invariant). On failure, node is dropped. *)
fn rec push_loop2 (#t:Type0) (s:tstack2 t) (v:t)
    (#phi : list t -> unit -> slprop)
    (tok : au_token emp_inames (list t) unit
      (fun xs -> scont2 s.nm xs)
      (fun xs _ -> scont2 s.nm (v :: xs))
      phi)
    (_u:unit)
  requires is_ts2 s ** au_available tok
  ensures is_ts2 s ** (exists* xs. phi xs ())
{
  // Step 1: Read head (single atomic read inside invariant)
  let old_hd = read_head2 s;
  // Step 2: Allocate new node (OUTSIDE invariant)
  let new_node = atomic_alloc ({ value = v; nd_next = old_hd } <: node t);
  // Make node persistent (Iris: pointsto_persist)
  make_persistent new_node;
  // Step 3: Open AU
  later_credit_buy 1;
  let xs = au_open tok;
  unfold scont2;
  // Step 4: CAS (single atomic CAS inside invariant)
  let b = try_push2 s v old_hd new_node;
  if b {
    elim_cond_true _ _;
    fold (scont2 s.nm (v :: xs));
    later_credit_buy 1;
    au_commit tok (reveal xs) ();
  } else {
    elim_cond_false _ _;
    fold (scont2 s.nm xs);
    later_credit_buy 1;
    au_abort tok (reveal xs);
    push_loop2 s v tok ()
  }
}

(** Type witness: push_loop2 IS a lat_void *)
let push_is_lat (#t:Type0) (s:tstack2 t) (v:t)
  : lat_void emp_inames (list t)
    (fun xs -> scont2 s.nm xs)
    (fun xs _ -> scont2 s.nm (v :: xs))
    (is_ts2 s)
  = fun #phi tok _u -> push_loop2 s v #phi tok _u

ghost
fn mk_id_trade2 (#t:Type0) (s : tstack2 t) (v : t) (#xs : erased (list t))
  requires emp
  ensures (forall* (y:unit). (later_credit 1 ** scont2 s.nm (v :: xs)) @==> scont2 s.nm (v :: xs))
{
  intro_forall #unit #(fun (y:unit) -> (later_credit 1 ** scont2 s.nm (v :: xs)) @==> scont2 s.nm (v :: xs))
    emp
    fn (y:unit) {
      intro_trade (later_credit 1 ** scont2 s.nm (v :: xs)) (scont2 s.nm (v :: xs)) emp
        fn _ { drop_ (later_credit 1) }
    }
}

(** Sequential wrapper: uses the identity trade (β = Φ).
    The logically atomic parametricity lives in push_loop2. *)
fn push2 (#t:Type0) (s:tstack2 t) (v:t)
  requires is_ts2 s ** scont2 s.nm 'xs
  ensures is_ts2 s ** (exists* ys. scont2 s.nm ys)
{
  mk_id_trade2 s v #'xs;
  let tok = au_intro #emp_inames #(list t) #unit
    #(fun xs -> scont2 s.nm xs)
    #(fun xs _ -> scont2 s.nm (v :: xs))
    #(fun xs _ -> scont2 s.nm (v :: xs))
    'xs;
  push_loop2 s v tok ()
}

(* ================================================================ *)
(* pop — read node outside invariant using persistent is_list       *)
(* ================================================================ *)

let list_hd_opt (#t:Type0) (xs:list t) : option t = match xs with | [] -> None | v::_ -> Some v
let list_tl (#t:Type0) (xs:list t) : list t = match xs with | [] -> [] | _::rest -> rest
let list_hd_val (#t:Type0) (xs:list t{Cons? xs}) : t = match xs with | v::_ -> v

let pop_post2 (#t:Type0) (g:ts_ghost t) (xs:list t) (ov:option t) : slprop =
  scont2 g (list_tl xs) ** pure (ov == list_hd_opt xs)

ghost fn is_list_unfold_non_null (#t:Type0) (hd : B.box (node t)) (xs : list t)
  requires is_list hd xs ** pure (not (B.is_null hd))
  returns nd : erased (node t)
  ensures persistent_pts_to hd (reveal nd) **
          pure (Cons? xs /\ (reveal nd).value == List.Tot.hd xs) **
          is_list (reveal nd).nd_next (list_tl xs)
{
  match xs {
    Nil -> {
      unfold is_list;
      unreachable ()
    }
    Cons x rest -> {
      unfold is_list;
      with nd0. assert (persistent_pts_to hd nd0 ** pure (nd0.value == x) ** is_list nd0.nd_next rest);
      rewrite (is_list nd0.nd_next rest) as (is_list nd0.nd_next (list_tl xs));
      hide nd0
    }
  }
}

ghost fn is_list_unfold_null (#t:Type0) (hd : B.box (node t)) (xs : list t)
  requires is_list hd xs ** pure (B.is_null hd)
  ensures pure (xs == [])
{
  match xs {
    Nil -> {
      unfold is_list
    }
    Cons x rest -> {
      unfold is_list;
      with nd. assert (persistent_pts_to hd nd ** pure (nd.value == x) ** is_list nd.nd_next rest);
      unfold (persistent_pts_to hd nd);
      with p. assert (B.pts_to hd #p nd);
      B.pts_to_not_null hd;
      unreachable ()
    }
  }
}


(** read_is_list_head: read node contents from persistent is_list.
    Wraps ghost unfold + physical read in a single fn boundary,
    avoiding the ghost-scope issue in callers. *)
fn read_is_list_head (#t:Type0) (hd : B.box (node t)) (#xs : erased (list t))
  requires is_list hd (reveal xs) ** pure (not (B.is_null hd))
  returns nd : node t
  ensures persistent_pts_to hd nd **
          pure (Cons? (reveal xs) /\ nd.value == List.Tot.hd (reveal xs)) **
          is_list nd.nd_next (list_tl (reveal xs))
{
  let _nd_e = is_list_unfold_non_null hd (reveal xs);
  let nd = read_persistent hd;
  rewrite each (reveal _nd_e) as nd;
  nd
}

(** read_head_snap: read head AND get a persistent is_list snapshot. *)
fn read_head_snap (#t:Type0) (s:tstack2 t)
  requires is_ts2 s
  returns hd : B.box (node t)
  ensures is_ts2 s ** (exists* xs. is_list hd xs)
{
  unfold is_ts2;
  let hd = with_invariants (B.box (node t)) emp_inames s.inm (sinv s)
    emp (fun hd -> exists* xs. is_list hd xs)
  fn _ {
    unfold sinv; unfold sinv_inner;
    with hd0 xs0. assert (B.pts_to s.head hd0 ** is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0);
    dup_is_list hd0 xs0;
    let c = atomic_read s.head;
    rewrite (is_list hd0 xs0) as (is_list c xs0);
    fold (sinv_inner s.head s.nm.gr); fold (sinv s);
    c
  };
  fold (is_ts2 s);
  hd
}

fn read_head_for_xs (#t:Type0) (s:tstack2 t) (#xs : erased (list t))
  requires is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs
  returns hd : B.box (node t)
  ensures is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs ** is_list hd (reveal xs)
{
  unfold is_ts2;
  let hd = with_invariants (B.box (node t)) emp_inames s.inm (sinv s)
    (GR.pts_to s.nm.gr #0.5R xs)
    (fun hd -> GR.pts_to s.nm.gr #0.5R xs ** is_list hd (reveal xs))
  fn _ {
    unfold sinv; unfold sinv_inner;
    with hd0 xs0. assert (B.pts_to s.head hd0 ** is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 ** GR.pts_to s.nm.gr #0.5R xs);
    GR.pts_to_injective_eq s.nm.gr;
    rewrite each xs0 as (reveal xs);
    dup_is_list hd0 (reveal xs);
    let c = atomic_read s.head;
    rewrite (is_list hd0 (reveal xs)) as (is_list c (reveal xs));
    fold (sinv_inner s.head s.nm.gr); fold (sinv s);
    c
  };
  fold (is_ts2 s);
  hd
}

(** try_pop2: CAS head from old_hd to next_hd.
    Faithful to Iris: single atomic CAS inside with_invariants.
    Node contents (v, next_hd) were read OUTSIDE the invariant using
    persistent is_list. The persistent_pts_to witnesses that the node
    contains {value=v, nd_next=next_hd}. *)
fn try_pop2 (#t:Type0) (s:tstack2 t) (old_hd next_hd : B.box (node t))
    (v : t) (#xs : erased (list t))
  requires is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs **
           persistent_pts_to old_hd ({ value = v; nd_next = next_hd }) **
           pure (not (B.is_null old_hd))
  returns b : bool
  ensures AP.cond b
    (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (list_tl (reveal xs)))
    (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs)
{
  unfold is_ts2;
  let b = with_invariants bool emp_inames s.inm (sinv s)
    (GR.pts_to s.nm.gr #0.5R xs **
     persistent_pts_to old_hd ({ value = v; nd_next = next_hd }))
    (fun b -> AP.cond b
      (GR.pts_to s.nm.gr #0.5R (list_tl (reveal xs)))
      (GR.pts_to s.nm.gr #0.5R xs))
  fn _ {
    unfold sinv; unfold sinv_inner;
    // Single atomic step: CAS head from old_hd to next_hd
    let b = atomic_cas_box s.head old_hd next_hd;
    if b {
      elim_cond_true _ _;
      with hd0 xs0. assert (
        B.pts_to s.head next_hd ** pure (reveal (hide hd0) == old_hd) **
        is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 **
        GR.pts_to s.nm.gr #0.5R xs **
        persistent_pts_to old_hd ({ value = v; nd_next = next_hd }));
      GR.pts_to_injective_eq s.nm.gr;
      rewrite each xs0 as (reveal xs);
      rewrite each hd0 as old_hd;
      // old_hd is non-null, so xs is Cons
      let nd_e = is_list_unfold_non_null old_hd (reveal xs);
      // Prove reveal nd_e == {value=v, nd_next=next_hd} via pts_to agreement
      unfold (persistent_pts_to old_hd (reveal nd_e));
      with p1. assert (B.pts_to old_hd #p1 (reveal nd_e));
      unfold (persistent_pts_to old_hd ({ value = v; nd_next = next_hd }));
      with p2. assert (B.pts_to old_hd #p2 ({ value = v; nd_next = next_hd }));
      B.pts_to_injective_eq old_hd;
      rewrite each (reveal nd_e) as ({ value = v; nd_next = next_hd } <: node t);
      // Drop fractional pts_to remnants
      drop_ (B.pts_to old_hd #p1 ({ value = v; nd_next = next_hd }));
      drop_ (B.pts_to old_hd #p2 ({ value = v; nd_next = next_hd }));
      // Now: is_list next_hd (list_tl xs)
      // Update ghost
      GR.gather s.nm.gr;
      GR.(s.nm.gr := list_tl (reveal xs));
      GR.share s.nm.gr;
      fold (sinv_inner s.head s.nm.gr); fold (sinv s);
      fold (AP.cond true
        (GR.pts_to s.nm.gr #0.5R (list_tl (reveal xs)))
        (GR.pts_to s.nm.gr #0.5R xs));
      true
    } else {
      elim_cond_false _ _;
      drop_ (persistent_pts_to old_hd ({ value = v; nd_next = next_hd }));
      fold (sinv_inner s.head s.nm.gr); fold (sinv s);
      fold (AP.cond false
        (GR.pts_to s.nm.gr #0.5R (list_tl (reveal xs)))
        (GR.pts_to s.nm.gr #0.5R xs));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_ts2 s);
    intro_cond_true
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (list_tl (reveal xs)))
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs);
    true
  } else {
    elim_cond_false _ _;
    fold (is_ts2 s);
    intro_cond_false
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (list_tl (reveal xs)))
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs);
    false
  }
}

fn rec pop_loop2 (#t:Type0) (s:tstack2 t)
    (#phi : list t -> option t -> slprop)
    (tok : au_token emp_inames (list t) (option t)
      (fun xs -> scont2 s.nm xs)
      (fun xs ov -> pop_post2 s.nm xs ov)
      phi)
    (_u:unit)
  requires is_ts2 s ** au_available tok
  returns ov : option t
  ensures is_ts2 s ** (exists* xs. phi xs ov)
{
  later_credit_buy 1;
  let xs = au_open tok;
  unfold scont2;
  let old_hd = read_head_for_xs s;
  if (B.is_null old_hd) {
    is_list_unfold_null old_hd (reveal xs);
    fold (scont2 s.nm (list_tl (reveal xs)));
    fold (pop_post2 s.nm (reveal xs) (None #t));
    later_credit_buy 1;
    au_commit tok (reveal xs) (None #t);
    (None #t)
  } else {
    let nd = read_is_list_head old_hd;
    let v = nd.value;
    let next_hd = nd.nd_next;
    drop_ (is_list nd.nd_next (list_tl (reveal xs)));
    rewrite (persistent_pts_to old_hd nd) as
            (persistent_pts_to old_hd ({ value = v; nd_next = next_hd }));
    let b = try_pop2 s old_hd next_hd v;
    if b {
      elim_cond_true _ _;
      fold (scont2 s.nm (list_tl (reveal xs)));
      fold (pop_post2 s.nm (reveal xs) (Some v));
      later_credit_buy 1;
      au_commit tok (reveal xs) (Some v);
      (Some v)
    } else {
      elim_cond_false _ _;
      fold (scont2 s.nm xs);
      later_credit_buy 1;
      au_abort tok (reveal xs);
      pop_loop2 s #phi tok ()
    }
  }
}

(** Type witness: pop_loop2 IS a lat *)
let pop_is_lat (#t:Type0) (s:tstack2 t)
  : lat emp_inames (list t) (option t)
    (fun xs -> scont2 s.nm xs)
    (fun xs ov -> pop_post2 s.nm xs ov)
    (is_ts2 s)
  = fun #phi tok _u -> pop_loop2 s #phi tok _u

ghost
fn mk_id_trade_pop (#t:Type0) (s : tstack2 t) (#xs : erased (list t))
  requires emp
  ensures (forall* (ov:option t). (later_credit 1 ** pop_post2 s.nm (reveal xs) ov) @==> pop_post2 s.nm (reveal xs) ov)
{
  intro_forall #(option t) #(fun (ov:option t) -> (later_credit 1 ** pop_post2 s.nm (reveal xs) ov) @==> pop_post2 s.nm (reveal xs) ov)
    emp
    fn (ov:option t) {
      intro_trade (later_credit 1 ** pop_post2 s.nm (reveal xs) ov) (pop_post2 s.nm (reveal xs) ov) emp
        fn _ { drop_ (later_credit 1) }
    }
}

(** Sequential pop wrapper *)
fn pop2 (#t:Type0) (s:tstack2 t)
  requires is_ts2 s ** scont2 s.nm 'xs
  returns ov : option t
  ensures is_ts2 s ** (exists* ys. scont2 s.nm ys)
{
  mk_id_trade_pop s #'xs;
  let tok = au_intro #emp_inames #(list t) #(option t)
    #(fun xs -> scont2 s.nm xs)
    #(fun xs ov -> pop_post2 s.nm xs ov)
    #(fun xs ov -> pop_post2 s.nm xs ov)
    'xs;
  let ov = pop_loop2 s tok ();
  with xs0. assert (pop_post2 s.nm xs0 ov);
  unfold pop_post2;
  ov
}
