(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Treiber Stack — concrete nodes, pointer CAS on llist, LA push. *)
module PulseTutorial.TreiberStack
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module P = Pulse.Lib.Primitives
open Pulse.Lib.Inv
open Pulse.Lib.LinkedList
open Pulse.Lib.Trade
open Pulse.Lib.Forall
open Pulse.Lib.Box { box, (:=), (!) }

(** CAS on llist pointer: read + llist_eq + write, lifted to atomic *)
fn cas_llist_impl (#t:Type0) (r : box (llist t)) (u v : llist t) (#i : erased (llist t))
  requires r |-> i
  returns b : bool
  ensures P.cond b ((r |-> v) ** pure (reveal i == u)) (r |-> i)
{
  let cur = !r;
  if (llist_eq cur u) {
    r := v;
    fold (P.cond true ((r |-> v) ** pure (reveal i == u)) (r |-> i));
    true
  } else {
    fold (P.cond false ((r |-> v) ** pure (reveal i == u)) (r |-> i));
    false
  }
}

let cas_llist (#t:Type0) (r : box (llist t)) (u v : llist t) (#i : erased (llist t))
  : stt_atomic bool #Observable emp_inames
      (r |-> i) (fun b -> P.cond b ((r |-> v) ** pure (reveal i == u)) (r |-> i))
  = Pulse.Lib.Core.as_atomic _ _ (cas_llist_impl r u v #i)

(** Atomic read of box (llist t) — same trust as read_atomic_box *)
fn read_llist_impl (#t:Type0) (r : box (llist t)) (#v : erased (llist t)) (#p:perm)
  preserves r |-> Frac p v
  returns x : llist t
  ensures rewrites_to x (reveal v)
{ !r }

let read_llist_atomic (#t:Type0) (r : box (llist t)) (#v : erased (llist t)) (#p:perm)
  : stt_atomic (llist t) #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))
  = Pulse.Lib.Core.as_atomic _ _ (read_llist_impl r #v #p)

noeq type sn (t:Type0) = { gr : GR.ref (list t); }
noeq type tstack (t:Type0) = {
  head : box (llist t);
  nm : sn t;
  inm : iname;
}

let scont (#t:Type0) (g:sn t) (xs:list t) : slprop = GR.pts_to g.gr #0.5R xs

let sinv_raw (#t:Type0) (head_box : box (llist t)) (gr : GR.ref (list t)) : slprop =
  exists* (hd:llist t) (xs:list t).
    B.pts_to head_box hd ** is_list hd xs ** GR.pts_to gr #0.5R xs

let is_ts (#t:Type0) (s:tstack t) : slprop = inv s.inm (sinv_raw s.head s.nm.gr)

fn new_stack (#t:Type0) ()
  requires emp
  returns s : tstack t
  ensures is_ts s ** scont s.nm []
{
  let hd0 = Pulse.Lib.LinkedList.create t;
  let head_box = B.alloc hd0;
  let gr = GR.alloc #(list t) [];
  GR.share gr;
  let g : sn t = { gr };
  rewrite (GR.pts_to gr #0.5R []) as (GR.pts_to g.gr #0.5R []);
  rewrite (GR.pts_to gr #0.5R []) as (scont g []);
  fold (sinv_raw head_box g.gr);
  let i = new_invariant (sinv_raw head_box g.gr);
  let s : tstack t = { head = head_box; nm = g; inm = i };
  rewrite (inv i (sinv_raw head_box g.gr)) as (inv s.inm (sinv_raw s.head s.nm.gr));
  fold (is_ts s);
  rewrite (scont g []) as (scont s.nm []);
  s
}

fn read_head (#t:Type0) (s:tstack t)
  requires is_ts s
  returns cur : llist t
  ensures is_ts s
{
  unfold is_ts;
  let cur = with_invariants (llist t) emp_inames s.inm (sinv_raw s.head s.nm.gr)
    emp (fun _ -> emp)
  fn _ { unfold sinv_raw; let c = read_llist_atomic s.head; fold (sinv_raw s.head s.nm.gr); c };
  fold (is_ts s); cur
}

(** try_push_impl: CAS head + cons + ghost update in one fn (lifted to atomic).
    old_hd: the previously-read head pointer (concrete, may be stale).
    On CAS success: cons v onto current head, update ghost state.
    On CAS failure: nothing changes. *)
fn try_push_impl (#t:Type0) (s:tstack t) (v:t) (old_hd : llist t)
    (#xs : erased (list t))
  requires sinv_raw s.head s.nm.gr ** GR.pts_to s.nm.gr #0.5R xs
  returns b : bool
  ensures sinv_raw s.head s.nm.gr **
          P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs)
{
  unfold sinv_raw;
  // Read current head (concrete)
  let cur_hd = !s.head;
  // Compare with old_hd (pointer equality via llist_eq)
  if (llist_eq cur_hd old_hd) {
    // "CAS" succeeds: head hasn't changed since we read it
    // Cons new node using cur_hd (is_list cur_hd xs is available from invariant)
    with hd0 xs0.
      assert (B.pts_to s.head hd0 ** is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 ** GR.pts_to s.nm.gr #0.5R xs);
    GR.pts_to_injective_eq s.nm.gr;
    rewrite each xs0 as (reveal xs);
    // hd0 == cur_hd (read from same box), cur_hd == old_hd (llist_eq)
    let new_hd = Pulse.Lib.LinkedList.cons v cur_hd;
    s.head := new_hd;
    GR.gather s.nm.gr;
    GR.(s.nm.gr := Cons v (reveal xs));
    GR.share s.nm.gr;
    fold (sinv_raw s.head s.nm.gr);
    fold (P.cond true (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs));
    true
  } else {
    // "CAS" fails
    fold (sinv_raw s.head s.nm.gr);
    fold (P.cond false (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs));
    false
  }
}

let try_push_atomic (#t:Type0) (s:tstack t) (v:t) (old_hd : llist t) (#xs : erased (list t))
  : stt_atomic bool #Observable emp_inames
    (sinv_raw s.head s.nm.gr ** GR.pts_to s.nm.gr #0.5R xs)
    (fun b -> sinv_raw s.head s.nm.gr **
              P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs))
  = Pulse.Lib.Core.as_atomic _ _ (try_push_impl s v old_hd #xs)

fn try_push (#t:Type0) (s:tstack t) (v:t) (old_hd : llist t) (#xs : erased (list t))
  requires is_ts s ** GR.pts_to s.nm.gr #0.5R xs
  returns b : bool
  ensures P.cond b (is_ts s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                   (is_ts s ** GR.pts_to s.nm.gr #0.5R xs)
{
  unfold is_ts;
  let b = with_invariants bool emp_inames s.inm (sinv_raw s.head s.nm.gr)
    (GR.pts_to s.nm.gr #0.5R xs)
    (fun b -> P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs))
  fn _ { try_push_atomic s v old_hd #xs };
  if b {
    elim_cond_true _ _ _;
    fold (is_ts s);
    intro_cond_true (is_ts s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                    (is_ts s ** GR.pts_to s.nm.gr #0.5R xs); true
  } else {
    elim_cond_false _ _ _;
    fold (is_ts s);
    intro_cond_false (is_ts s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                     (is_ts s ** GR.pts_to s.nm.gr #0.5R xs); false
  }
}

fn rec push_loop (#t:Type0) (s:tstack t) (v:t)
    (tok : au_token (list t) unit
      (fun xs -> scont s.nm xs)
      (fun xs _ -> scont s.nm (Cons v xs))
      (fun xs _ -> scont s.nm (Cons v xs)))
    (_u:unit)
  requires is_ts s ** au_available tok
  ensures is_ts s ** (exists* (xs_out : list t). scont s.nm xs_out)
{
  let old_hd = read_head s;
  later_credit_buy 1;
  let xs = au_open tok;
  unfold scont;
  let b = try_push s v old_hd;
  if b {
    elim_cond_true _ _ _;
    fold (scont s.nm (Cons v xs));
    au_commit tok (reveal xs) ();
  } else {
    elim_cond_false _ _ _;
    fold (scont s.nm xs);
    later_credit_buy 1;
    au_abort tok (reveal xs);
    push_loop s v tok ()
  }
}

ghost
fn id_trade_body (#t:Type0) (s : tstack t) (v : t) (#xs : erased (list t)) (y : unit)
  requires scont s.nm (Cons v xs)
  ensures scont s.nm (Cons v xs)
{ () }

ghost
fn mk_id_trade (#t:Type0) (s : tstack t) (v : t) (#xs : erased (list t))
  requires emp
  ensures (forall* (y:unit). scont s.nm (Cons v xs) @==> scont s.nm (Cons v xs))
{
  intro_forall #unit #(fun (y:unit) -> scont s.nm (Cons v xs) @==> scont s.nm (Cons v xs))
    emp
    fn (y:unit) {
      intro_trade (scont s.nm (Cons v xs)) (scont s.nm (Cons v xs)) emp
        fn _ { () }
    }
}

fn push (#t:Type0) (s:tstack t) (v:t)
  requires is_ts s ** scont s.nm 'xs
  ensures is_ts s ** (exists* ys. scont s.nm ys)
{
  mk_id_trade s v #'xs;
  // Now have: forall* y. beta(xs,y) @==> phi(xs,y) where beta=phi
  let tok = au_intro #(list t) #unit
                     #(fun xs -> scont s.nm xs)
                     #(fun xs _ -> scont s.nm (Cons v xs))
                     #(fun xs _ -> scont s.nm (Cons v xs))
                     'xs;
  push_loop s v tok ()
}
