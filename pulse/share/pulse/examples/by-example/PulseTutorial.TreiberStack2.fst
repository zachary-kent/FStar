(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Treiber Stack v2 — faithful to Iris/HeapLang atomicity model.
    
    Uses only Pulse.Lib.AtomicPrimitives (single-step atomic ops).
    No as_atomic outside the kernel.
    
    Key differences from v1:
    - Nodes are raw boxes (not LinkedList), matching Iris's HeapLang encoding
    - Allocation happens OUTSIDE the invariant
    - Only CAS on the head pointer is inside the invariant
    - Ghost state tracks abstract list contents
    - Recursive phys_list predicate owned by the invariant *)
module PulseTutorial.TreiberStack2
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.AtomicPrimitives
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

(* Physical list: recursive predicate owned by the invariant.
   phys_list null [] = emp
   phys_list p (x::xs) = p |-> {value=x; nd_next=tl} ** phys_list tl xs *)
let rec phys_list (#t:Type0) (hd : B.box (node t)) (xs : list t)
  : Tot slprop (decreases xs) =
  match xs with
  | [] -> pure (hd == B.null)
  | x :: rest -> exists* (nd : node t).
      B.pts_to hd nd ** pure (nd.value == x) ** phys_list nd.nd_next rest

(* ================================================================ *)
(* Stack representation                                             *)
(* ================================================================ *)

noeq type ts_ghost (t:Type0) = { gr : GR.ref (list t); }

(* The head is a box (box (node t)) — a mutable pointer to the first node *)
noeq type tstack2 (t:Type0) = {
  head : B.box (B.box (node t));
  nm   : ts_ghost t;
  inm  : iname;
}

let scont2 (#t:Type0) (g:ts_ghost t) (xs:list t) : slprop = GR.pts_to g.gr #0.5R xs

(* Stack invariant: head points to a physical list matching ghost state *)
let sinv_inner (#t:Type0) (head : B.box (B.box (node t))) (gr : GR.ref (list t)) : slprop =
  exists* (hd : B.box (node t)) (xs : list t).
    B.pts_to head hd ** phys_list hd xs ** GR.pts_to gr #0.5R xs

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
  fold (phys_list #t (B.null #(node t)) []);
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
    phys_list stays INSIDE the invariant — never leaves.
    The new_node is passed in (allocated outside).
    On CAS success: new_node is linked into phys_list inside invariant.
    On CAS failure: new_node is returned to caller.
    Faithful to Iris: one atomic CAS per invariant opening. *)
fn try_push2 (#t:Type0) (s:tstack2 t) (v:t) (old_hd new_node : B.box (node t))
    (#xs : erased (list t))
  requires is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs **
           new_node |-> ({ value = v; nd_next = old_hd })
  returns b : bool
  ensures AP.cond b
    (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (v :: xs))
    (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs **
     new_node |-> ({ value = v; nd_next = old_hd }))
{
  unfold is_ts2;
  let b = with_invariants bool emp_inames s.inm (sinv s)
    (GR.pts_to s.nm.gr #0.5R xs **
     new_node |-> ({ value = v; nd_next = old_hd }))
    (fun b -> AP.cond b
      (GR.pts_to s.nm.gr #0.5R (v :: xs))
      (GR.pts_to s.nm.gr #0.5R xs **
       new_node |-> ({ value = v; nd_next = old_hd })))
  fn _ {
    unfold sinv; unfold sinv_inner;
    // Single atomic step: CAS head from old_hd to new_node
    let b = atomic_cas_box s.head old_hd new_node;
    if b {
      elim_cond_true _ _;
      // CAS succeeded: old_hd was the head, now head = new_node
      with hd0 xs0. assert (
        B.pts_to s.head new_node ** pure (reveal (hide hd0) == old_hd) **
        phys_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 **
        GR.pts_to s.nm.gr #0.5R xs **
        new_node |-> ({ value = v; nd_next = old_hd }));
      GR.pts_to_injective_eq s.nm.gr;
      rewrite each xs0 as (reveal xs);
      rewrite each hd0 as old_hd;
      // Build phys_list new_node (v :: xs):
      // new_node |-> {value=v, next=old_hd} ** phys_list old_hd xs
      fold (phys_list new_node (v :: reveal xs));
      // Update ghost
      GR.gather s.nm.gr;
      GR.(s.nm.gr := v :: (reveal xs));
      GR.share s.nm.gr;
      fold (sinv_inner s.head s.nm.gr); fold (sinv s);
      fold (AP.cond true
        (GR.pts_to s.nm.gr #0.5R (v :: xs))
        (GR.pts_to s.nm.gr #0.5R xs **
         new_node |-> ({ value = v; nd_next = old_hd })));
      true
    } else {
      elim_cond_false _ _;
      fold (sinv_inner s.head s.nm.gr); fold (sinv s);
      fold (AP.cond false
        (GR.pts_to s.nm.gr #0.5R (v :: xs))
        (GR.pts_to s.nm.gr #0.5R xs **
         new_node |-> ({ value = v; nd_next = old_hd })));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_ts2 s);
    intro_cond_true
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (v :: xs))
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs **
       new_node |-> ({ value = v; nd_next = old_hd }));
    true
  } else {
    elim_cond_false _ _;
    fold (is_ts2 s);
    intro_cond_false
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R (v :: xs))
      (is_ts2 s ** GR.pts_to s.nm.gr #0.5R xs **
       new_node |-> ({ value = v; nd_next = old_hd }));
    false
  }
}

(** push_loop: CAS retry loop.
    Alloc happens HERE (outside invariant). On failure, node is dropped. *)
fn rec push_loop2 (#t:Type0) (s:tstack2 t) (v:t)
    (tok : au_token (list t) unit
      (fun xs -> scont2 s.nm xs)
      (fun xs _ -> scont2 s.nm (v :: xs))
      (fun xs _ -> scont2 s.nm (v :: xs)))
    (_u:unit)
  requires is_ts2 s ** au_available tok
  ensures is_ts2 s ** (exists* xs. scont2 s.nm xs)
{
  // Step 1: Read head (single atomic read inside invariant)
  let old_hd = read_head2 s;
  // Step 2: Allocate new node (OUTSIDE invariant)
  let new_node = atomic_alloc ({ value = v; nd_next = old_hd } <: node t);
  // Step 3: Open AU
  later_credit_buy 1;
  let xs = au_open tok;
  unfold scont2;
  // Step 4: CAS (single atomic CAS inside invariant)
  let b = try_push2 s v old_hd new_node;
  if b {
    elim_cond_true _ _;
    fold (scont2 s.nm (v :: xs));
    au_commit tok (reveal xs) ();
  } else {
    elim_cond_false _ _;
    fold (scont2 s.nm xs);
    later_credit_buy 1;
    au_abort tok (reveal xs);
    // Drop the failed node (affine/GC)
    drop_ (B.pts_to new_node ({ value = v; nd_next = old_hd }));
    push_loop2 s v tok ()
  }
}

ghost
fn mk_id_trade2 (#t:Type0) (s : tstack2 t) (v : t) (#xs : erased (list t))
  requires emp
  ensures (forall* (y:unit). scont2 s.nm (v :: xs) @==> scont2 s.nm (v :: xs))
{
  intro_forall #unit #(fun (y:unit) -> scont2 s.nm (v :: xs) @==> scont2 s.nm (v :: xs))
    emp
    fn (y:unit) {
      intro_trade (scont2 s.nm (v :: xs)) (scont2 s.nm (v :: xs)) emp
        fn _ { () }
    }
}

fn push2 (#t:Type0) (s:tstack2 t) (v:t)
  requires is_ts2 s ** scont2 s.nm 'xs
  ensures is_ts2 s ** (exists* ys. scont2 s.nm ys)
{
  mk_id_trade2 s v #'xs;
  let tok = au_intro #(list t) #unit
    #(fun xs -> scont2 s.nm xs)
    #(fun xs _ -> scont2 s.nm (v :: xs))
    #(fun xs _ -> scont2 s.nm (v :: xs))
    'xs;
  push_loop2 s v tok ()
}
