(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Treiber Stack — concrete nodes + version CAS + LA. No admits. *)
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
open Pulse.Lib.Box { box, (:=), (!) }

noeq type sn (t:Type0) = { gr : GR.ref (list t); }
noeq type tstack (t:Type0) = {
  ver : box U32.t;
  head : box (llist t);
  nm : sn t;
  inm : iname;
}
let scont (#t:Type0) (g:sn t) (xs:list t) : slprop = GR.pts_to g.gr #0.5R xs

let sinv_raw (#t:Type0) (ver_box : box U32.t) (head_box : box (llist t))
    (gr : GR.ref (list t)) : slprop =
  exists* (v:U32.t) (hd:llist t) (xs:list t).
    B.pts_to ver_box v ** B.pts_to head_box hd ** is_list hd xs ** GR.pts_to gr #0.5R xs

let is_ts (#t:Type0) (s:tstack t) : slprop = inv s.inm (sinv_raw s.ver s.head s.nm.gr)

fn new_stack (#t:Type0) ()
  requires emp
  returns s : tstack t
  ensures is_ts s ** scont s.nm []
{
  let ver_box = B.alloc 0ul;
  let hd0 = Pulse.Lib.LinkedList.create t;
  let head_box = B.alloc hd0;
  let gr = GR.alloc #(list t) [];
  GR.share gr;
  let g : sn t = { gr };
  rewrite (GR.pts_to gr #0.5R []) as (GR.pts_to g.gr #0.5R []);
  rewrite (GR.pts_to gr #0.5R []) as (scont g []);
  fold (sinv_raw ver_box head_box g.gr);
  let i = new_invariant (sinv_raw ver_box head_box g.gr);
  let s : tstack t = { ver = ver_box; head = head_box; nm = g; inm = i };
  rewrite (inv i (sinv_raw ver_box head_box g.gr))
       as (inv s.inm (sinv_raw s.ver s.head s.nm.gr));
  fold (is_ts s);
  rewrite (scont g []) as (scont s.nm []);
  s
}

fn read_ver (#t:Type0) (s:tstack t)
  requires is_ts s
  returns cur : U32.t
  ensures is_ts s
{
  unfold is_ts;
  let cur = with_invariants U32.t emp_inames s.inm (sinv_raw s.ver s.head s.nm.gr)
    emp (fun _ -> emp)
  fn _ { unfold sinv_raw; let c = P.read_atomic_box s.ver; fold (sinv_raw s.ver s.head s.nm.gr); c };
  fold (is_ts s); cur
}

(** try_push_impl: read ver + compare + cons + write ver + write head + ghost.
    All concrete stt operations. Lifted to atomic via as_atomic. *)
fn try_push_impl (#t:Type0) (s:tstack t) (v:t) (old_ver new_ver : U32.t)
    (#xs : erased (list t))
  requires sinv_raw s.ver s.head s.nm.gr ** GR.pts_to s.nm.gr #0.5R xs
  returns b : bool
  ensures sinv_raw s.ver s.head s.nm.gr **
          P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs)
{
  unfold sinv_raw;
  // Read CONCRETE values before existential elimination
  let cur_ver = !s.ver;
  let cur_head = !s.head;
  // Now unfold existentials for ghost agreement
  with v0 hd0 xs0.
    assert (B.pts_to s.ver v0 ** B.pts_to s.head hd0 **
            is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 **
            GR.pts_to s.nm.gr #0.5R xs);
  GR.pts_to_injective_eq s.nm.gr;
  rewrite each xs0 as (reveal xs);
  if (cur_ver = old_ver) {
    // CAS succeeds: update version
    s.ver := new_ver;
    // Cons concrete node using cur_head (concrete, not erased)
    let new_hd = Pulse.Lib.LinkedList.cons v cur_head;
    // Write head
    s.head := new_hd;
    // is_list: new_hd represents (v :: xs)
    // We have is_list hd0 xs from the invariant.
    // hd0 == cur_head (both read from same box).
    // So is_list cur_head xs, and cons gives is_list new_hd (v::xs).
    // But we already consumed is_list hd0 xs to build new_hd via cons.
    // Good — cons consumed is_list cur_head xs and produced is_list new_hd (v::xs).
    // Ghost update
    GR.gather s.nm.gr;
    GR.(s.nm.gr := Cons v (reveal xs));
    GR.share s.nm.gr;
    fold (sinv_raw s.ver s.head s.nm.gr);
    fold (P.cond true (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs));
    true
  } else {
    // CAS fails
    fold (sinv_raw s.ver s.head s.nm.gr);
    fold (P.cond false (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs));
    false
  }
}

let try_push_atomic (#t:Type0) (s:tstack t) (v:t) (old_ver new_ver : U32.t) (#xs : erased (list t))
  : stt_atomic bool #Observable emp_inames
    (sinv_raw s.ver s.head s.nm.gr ** GR.pts_to s.nm.gr #0.5R xs)
    (fun b -> sinv_raw s.ver s.head s.nm.gr **
              P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs))
  = Pulse.Lib.Core.as_atomic _ _ (try_push_impl s v old_ver new_ver #xs)

fn try_push (#t:Type0) (s:tstack t) (v:t) (old_ver new_ver : U32.t) (#xs : erased (list t))
  requires is_ts s ** GR.pts_to s.nm.gr #0.5R xs
  returns b : bool
  ensures P.cond b (is_ts s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                   (is_ts s ** GR.pts_to s.nm.gr #0.5R xs)
{
  unfold is_ts;
  let b = with_invariants bool emp_inames s.inm (sinv_raw s.ver s.head s.nm.gr)
    (GR.pts_to s.nm.gr #0.5R xs)
    (fun b -> P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs))
  fn _ { try_push_atomic s v old_ver new_ver #xs };
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
  let cur = read_ver s;
  let new_ver = U32.add_mod cur 1ul;
  later_credit_buy 1;
  let xs = au_open tok;
  unfold scont;
  let b = try_push s v cur new_ver;
  if b {
    elim_cond_true _ _ _;
    fold (scont s.nm (Cons v xs));
    au_commit tok (reveal xs) (hide ()) fn _ { () };
  } else {
    elim_cond_false _ _ _;
    fold (scont s.nm xs);
    later_credit_buy 1;
    au_abort tok (reveal xs);
    push_loop s v tok ()
  }
}

fn push (#t:Type0) (s:tstack t) (v:t)
  requires is_ts s ** scont s.nm 'xs
  ensures is_ts s ** (exists* ys. scont s.nm ys)
{
  let tok = au_intro #(list t) #unit
                     #(fun xs -> scont s.nm xs)
                     #(fun xs _ -> scont s.nm (Cons v xs))
                     #(fun xs _ -> scont s.nm (Cons v xs))
                     'xs;
  push_loop s v tok ()
}
