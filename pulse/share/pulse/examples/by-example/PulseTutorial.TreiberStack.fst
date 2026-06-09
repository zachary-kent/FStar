(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Treiber Stack — faithful to Iris/HeapLang atomicity model.
    
    Uses only Pulse.Lib.AtomicPrimitives (single-step atomic ops).
    No as_atomic outside the kernel.
    
    Key design choices:
    - Nodes are raw boxes (not LinkedList), matching Iris's HeapLang encoding
    - Allocation happens OUTSIDE the invariant
    - Only CAS on the head pointer is inside the invariant
    - Ghost state tracks abstract list contents
    - Persistent is_list predicate (∃q. l↦{q}v) — duplicable, Iris-faithful *)
module PulseTutorial.TreiberStack
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.AtomicPrimitives
open Pulse.Lib.PersistentPtsTo
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module AP = Pulse.Lib.Primitives
open Pulse.Lib.Inv

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

(* Null sentinel — using B.null directly. *)
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

ghost fn rec is_list_dup (#t:Type0) (hd : B.box (node t)) (xs : list t)
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
      dup (persistent_pts_to hd nd) ();
      is_list_dup nd.nd_next rest;
      fold (is_list hd (x :: rest));
      rewrite (is_list hd (x :: rest)) as (is_list hd xs);
      fold (is_list hd (x :: rest));
      rewrite (is_list hd (x :: rest)) as (is_list hd xs)
    }
  }
}

instance duplicable_is_list #t hd xs : duplicable (is_list #t hd xs) =
  { dup_f = fun _ -> is_list_dup hd xs }

(* Stack invariant: uses persistent is_list directly.
   Nodes are immutable after allocation — persistent ownership suffices.
   is_list is duplicable, so we can extract copies outside the invariant. *)

noeq type stack_ghost (t:Type0) = { gr : GR.ref (list t); }

noeq type stack (t:Type0) = {
  head : B.box (B.box (node t));
  contents   : stack_ghost t;
  inv_name  : iname;
}

let stack_content (#t:Type0) (g:stack_ghost t) (xs:list t) : slprop = GR.pts_to g.gr #0.5R xs

let is_stack (#t:Type0) (s:stack t) (xs:list t) : slprop = stack_content s.contents xs

let stack_inv_inner (#t:Type0) (head : B.box (B.box (node t))) (gr : GR.ref (list t)) : slprop =
  exists* (hd : B.box (node t)) (xs : list t).
    B.pts_to head hd ** is_list hd xs ** GR.pts_to gr #0.5R xs

let stack_inv (#t:Type0) (s:stack t) : slprop = stack_inv_inner s.head s.contents.gr
let is_stack_handle (#t:Type0) (s:stack t) : slprop = inv s.inv_name (stack_inv s)

(* ================================================================ *)
(* new_stack                                                        *)
(* ================================================================ *)

fn new_stack (#t:Type0) ()
  requires emp
  returns s : stack t
  ensures is_stack_handle s ** is_stack s []
{
  let head = B.alloc (B.null #(node t));
  let gr = GR.alloc #(list t) [];
  GR.share gr;
  let contents : stack_ghost t = { gr };
  rewrite (GR.pts_to gr #0.5R []) as (GR.pts_to contents.gr #0.5R []);
  rewrite (GR.pts_to gr #0.5R []) as (stack_content contents []);
  fold (is_list #t (B.null #(node t)) []);
  fold (stack_inv_inner head contents.gr);
  let inv_name = new_invariant (stack_inv_inner head contents.gr);
  let s : stack t = { head; contents; inv_name };
  rewrite (inv inv_name (stack_inv_inner head contents.gr)) as (inv s.inv_name (stack_inv s));
  fold (is_stack_handle s);
  rewrite (stack_content contents []) as (is_stack s []);
  s
}

(* ================================================================ *)
(* push — alloc outside invariant, CAS inside                       *)
(* ================================================================ *)

(** read_head: atomic read of head pointer (single atomic_read inside invariant) *)
fn read_head (#t:Type0) (s:stack t)
  requires is_stack_handle s
  returns cur : B.box (node t)
  ensures is_stack_handle s
{
  unfold is_stack_handle;
  let cur = with_invariants (B.box (node t)) emp_inames s.inv_name (stack_inv s)
    emp (fun _ -> emp)
  fn _ {
    unfold stack_inv; unfold stack_inv_inner;
    let c = atomic_read s.head;
    fold (stack_inv_inner s.head s.contents.gr); fold (stack_inv s);
    c
  };
  fold (is_stack_handle s);
  cur
}

(** try_push: CAS head from old_hd to new_node.
    is_list (persistent) stays in the invariant — duplicable.
    The new_node's pts_to is made persistent before linking.
    Faithful to Iris: one atomic CAS per invariant opening. *)
fn try_push (#t:Type0) (s:stack t) (v:t) (old_hd new_node : B.box (node t))
    (#xs : erased (list t))
  requires is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs **
           persistent_pts_to new_node ({ value = v; nd_next = old_hd })
  returns b : bool
  ensures AP.cond b
    (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R (v :: xs))
    (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs)
{
  unfold is_stack_handle;
  let b = with_invariants bool emp_inames s.inv_name (stack_inv s)
    (GR.pts_to s.contents.gr #0.5R xs **
     persistent_pts_to new_node ({ value = v; nd_next = old_hd }))
    (fun b -> AP.cond b
      (GR.pts_to s.contents.gr #0.5R (v :: xs))
      (GR.pts_to s.contents.gr #0.5R xs))
  fn _ {
    unfold stack_inv; unfold stack_inv_inner;
    let b = atomic_cas_box s.head old_hd new_node;
    if b {
      elim_cond_true _ _;
      with hd0 xs0. assert (
        B.pts_to s.head new_node ** pure (reveal (hide hd0) == old_hd) **
        is_list hd0 xs0 ** GR.pts_to s.contents.gr #0.5R xs0 **
        GR.pts_to s.contents.gr #0.5R xs **
        persistent_pts_to new_node ({ value = v; nd_next = old_hd }));
      GR.pts_to_injective_eq s.contents.gr;
      rewrite each xs0 as (reveal xs);
      rewrite each hd0 as old_hd;
      // Build is_list new_node (v :: xs) from:
      //   persistent_pts_to new_node {value=v, next=old_hd}
      //   is_list old_hd xs (from invariant, persistent)
      fold (is_list new_node (v :: reveal xs));
      // Update ghost
      GR.gather s.contents.gr;
      GR.(s.contents.gr := v :: (reveal xs));
      GR.share s.contents.gr;
      fold (stack_inv_inner s.head s.contents.gr); fold (stack_inv s);
      fold (AP.cond true
        (GR.pts_to s.contents.gr #0.5R (v :: xs))
        (GR.pts_to s.contents.gr #0.5R xs));
      true
    } else {
      elim_cond_false _ _;
      // Drop the persistent_pts_to (it's duplicable, safe to drop)
      drop_ (persistent_pts_to new_node ({ value = v; nd_next = old_hd }));
      fold (stack_inv_inner s.head s.contents.gr); fold (stack_inv s);
      fold (AP.cond false
        (GR.pts_to s.contents.gr #0.5R (v :: xs))
        (GR.pts_to s.contents.gr #0.5R xs));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_stack_handle s);
    intro_cond_true
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R (v :: xs))
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs);
    true
  } else {
    elim_cond_false _ _;
    fold (is_stack_handle s);
    intro_cond_false
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R (v :: xs))
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs);
    false
  }
}

(** push_loop: CAS retry loop, parametric in the client's postcondition.
    Allocation happens here (outside the invariant). On CAS failure the
    persistent witness is discarded and the operation retries with a fresh node. *)
fn rec push_loop (#t:Type0) (s:stack t) (v:t)
    (phi : unit -> slprop)
    (tok : au_token emp_inames (list t) unit
      (fun xs -> is_stack s xs)
      (fun xs _ -> is_stack s (v :: xs))
      (fun _ r -> phi r))
    (_u:unit)
  requires is_stack_handle s ** au_available tok
  ensures is_stack_handle s ** phi ()
{
  // Read head (single atomic read inside invariant)
  let old_hd = read_head s;
  // Allocate new node (OUTSIDE invariant)
  let new_node = atomic_alloc ({ value = v; nd_next = old_hd } <: node t);
  // Make node persistent (Iris: pointsto_persist)
  make_persistent new_node;
  // Open AU
  later_credit_buy 1;
  let xs = au_open tok;
  unfold is_stack; unfold stack_content;
  // CAS (single atomic CAS inside invariant)
  let b = try_push s v old_hd new_node;
  if b {
    elim_cond_true _ _;
    fold (stack_content s.contents (v :: xs));
    fold (is_stack s (v :: xs));
    later_credit_buy 1;
    au_commit tok (reveal xs) ();
  } else {
    elim_cond_false _ _;
    fold (stack_content s.contents xs);
    fold (is_stack s xs);
    later_credit_buy 1;
    au_abort tok (reveal xs);
    push_loop s v phi tok ()
  }
}

(** Direct logically atomic triple witness for push. *)
let push_is_lat (#t:Type0) (s:stack t) (v:t)
  : lat emp_inames (list t) unit
    (fun xs -> is_stack s xs)
    (fun xs _ -> is_stack s (v :: xs))
    (is_stack_handle s)
  = push_loop s v

(* ================================================================ *)
(* pop — read node outside invariant using persistent is_list       *)
(* ================================================================ *)

let list_hd_opt (#t:Type0) (xs:list t) : option t = match xs with | [] -> None | v::_ -> Some v
let list_tl (#t:Type0) (xs:list t) : list t = match xs with | [] -> [] | _::rest -> rest

let pop_post (#t:Type0) (s:stack t) (xs:list t) (ov:option t) : slprop =
  is_stack s (list_tl xs) ** pure (ov == list_hd_opt xs)

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

fn read_head_for_xs (#t:Type0) (s:stack t) (#xs : erased (list t))
  requires is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs
  returns hd : B.box (node t)
  ensures is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs ** is_list hd (reveal xs)
{
  unfold is_stack_handle;
  let hd = with_invariants (B.box (node t)) emp_inames s.inv_name (stack_inv s)
    (GR.pts_to s.contents.gr #0.5R xs)
    (fun hd -> GR.pts_to s.contents.gr #0.5R xs ** is_list hd (reveal xs))
  fn _ {
    unfold stack_inv; unfold stack_inv_inner;
    with hd0 xs0. assert (B.pts_to s.head hd0 ** is_list hd0 xs0 ** GR.pts_to s.contents.gr #0.5R xs0 ** GR.pts_to s.contents.gr #0.5R xs);
    GR.pts_to_injective_eq s.contents.gr;
    rewrite each xs0 as (reveal xs);
    dup (is_list hd0 (reveal xs)) ();
    let c = atomic_read s.head;
    rewrite (is_list hd0 (reveal xs)) as (is_list c (reveal xs));
    fold (stack_inv_inner s.head s.contents.gr); fold (stack_inv s);
    c
  };
  fold (is_stack_handle s);
  hd
}

(** try_pop: CAS head from old_hd to next_hd.
    Faithful to Iris: single atomic CAS inside with_invariants.
    Node contents (v, next_hd) were read OUTSIDE the invariant using
    persistent is_list. The persistent_pts_to witnesses that the node
    contains {value=v, nd_next=next_hd}. *)
fn try_pop (#t:Type0) (s:stack t) (old_hd next_hd : B.box (node t))
    (v : t) (#xs : erased (list t))
  requires is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs **
           persistent_pts_to old_hd ({ value = v; nd_next = next_hd }) **
           pure (not (B.is_null old_hd))
  returns b : bool
  ensures AP.cond b
    (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R (list_tl (reveal xs)))
    (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs)
{
  unfold is_stack_handle;
  let b = with_invariants bool emp_inames s.inv_name (stack_inv s)
    (GR.pts_to s.contents.gr #0.5R xs **
     persistent_pts_to old_hd ({ value = v; nd_next = next_hd }))
    (fun b -> AP.cond b
      (GR.pts_to s.contents.gr #0.5R (list_tl (reveal xs)))
      (GR.pts_to s.contents.gr #0.5R xs))
  fn _ {
    unfold stack_inv; unfold stack_inv_inner;
    // Single atomic step: CAS head from old_hd to next_hd
    let b = atomic_cas_box s.head old_hd next_hd;
    if b {
      elim_cond_true _ _;
      with hd0 xs0. assert (
        B.pts_to s.head next_hd ** pure (reveal (hide hd0) == old_hd) **
        is_list hd0 xs0 ** GR.pts_to s.contents.gr #0.5R xs0 **
        GR.pts_to s.contents.gr #0.5R xs **
        persistent_pts_to old_hd ({ value = v; nd_next = next_hd }));
      GR.pts_to_injective_eq s.contents.gr;
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
      GR.gather s.contents.gr;
      GR.(s.contents.gr := list_tl (reveal xs));
      GR.share s.contents.gr;
      fold (stack_inv_inner s.head s.contents.gr); fold (stack_inv s);
      fold (AP.cond true
        (GR.pts_to s.contents.gr #0.5R (list_tl (reveal xs)))
        (GR.pts_to s.contents.gr #0.5R xs));
      true
    } else {
      elim_cond_false _ _;
      drop_ (persistent_pts_to old_hd ({ value = v; nd_next = next_hd }));
      fold (stack_inv_inner s.head s.contents.gr); fold (stack_inv s);
      fold (AP.cond false
        (GR.pts_to s.contents.gr #0.5R (list_tl (reveal xs)))
        (GR.pts_to s.contents.gr #0.5R xs));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_stack_handle s);
    intro_cond_true
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R (list_tl (reveal xs)))
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs);
    true
  } else {
    elim_cond_false _ _;
    fold (is_stack_handle s);
    intro_cond_false
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R (list_tl (reveal xs)))
      (is_stack_handle s ** GR.pts_to s.contents.gr #0.5R xs);
    false
  }
}

fn rec pop_loop (#t:Type0) (s:stack t)
    (phi : option t -> slprop)
    (tok : au_token emp_inames (list t) (option t)
      (fun xs -> is_stack s xs)
      (fun xs ov -> pop_post s xs ov)
      (fun _ ov -> phi ov))
    (_u:unit)
  requires is_stack_handle s ** au_available tok
  returns ov : option t
  ensures is_stack_handle s ** phi ov
{
  later_credit_buy 1;
  let xs = au_open tok;
  unfold is_stack; unfold stack_content;
  let old_hd = read_head_for_xs s;
  if (B.is_null old_hd) {
    is_list_unfold_null old_hd (reveal xs);
    fold (stack_content s.contents (list_tl (reveal xs)));
    fold (is_stack s (list_tl (reveal xs)));
    fold (pop_post s (reveal xs) (None #t));
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
    let b = try_pop s old_hd next_hd v;
    if b {
      elim_cond_true _ _;
      fold (stack_content s.contents (list_tl (reveal xs)));
      fold (is_stack s (list_tl (reveal xs)));
      fold (pop_post s (reveal xs) (Some v));
      later_credit_buy 1;
      au_commit tok (reveal xs) (Some v);
      (Some v)
    } else {
      elim_cond_false _ _;
      fold (stack_content s.contents xs);
      fold (is_stack s xs);
      later_credit_buy 1;
      au_abort tok (reveal xs);
      pop_loop s phi tok ()
    }
  }
}

(** Direct logically atomic triple witness for pop. *)
let pop_is_lat (#t:Type0) (s:stack t)
  : lat emp_inames (list t) (option t)
    (fun xs -> is_stack s xs)
    (fun xs ov -> pop_post s xs ov)
    (is_stack_handle s)
  = pop_loop s

