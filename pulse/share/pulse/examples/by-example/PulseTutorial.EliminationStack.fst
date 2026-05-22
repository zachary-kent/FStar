(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Elimination Stack — Treiber stack with elimination channel.
    Ported from Iris: theories/logatom/elimination_stack/stack.v
    
    When push/pop fail their CAS, instead of just retrying, they can
    use a side channel: a pusher "offers" its value, and a concurrent
    popper can "accept" the offer. This eliminates contention.
    
    Offer states: Pending(0) -> Accepted(1) | Revoked(2)
    - Pusher creates offer in Pending state
    - Popper CAS Pending -> Accepted
    - Pusher checks: if Accepted, done; if still Pending, CAS Pending -> Revoked
*)
module PulseTutorial.EliminationStack
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

(* ================================================================ *)
(* Offer channel representation                                     *)
(* ================================================================ *)

(* Offer states encoded as U32: 0=Pending, 1=Accepted, 2=Revoked *)
let offer_pending  : U32.t = 0ul
let offer_accepted : U32.t = 1ul
let offer_revoked  : U32.t = 2ul

(* An offer: status word + the offered value *)
noeq type offer (t:Type0) = {
  status : box U32.t;
  value  : t;
}

(* ================================================================ *)
(* Stack representation (reusing Treiber stack structure)            *)
(* ================================================================ *)

noeq type es_ghost (t:Type0) = { gr : GR.ref (list t); }
noeq type elim_stack (t:Type0) = {
  head : box (llist t);
  nm   : es_ghost t;
  inm  : iname;
}

let es_content (#t:Type0) (g:es_ghost t) (xs:list t) : slprop = GR.pts_to g.gr #0.5R xs

let es_inv_inner (#t:Type0) (head : box (llist t)) (gr : GR.ref (list t)) : slprop =
  exists* (hd:llist t) (xs:list t).
    B.pts_to head hd ** is_list hd xs ** GR.pts_to gr #0.5R xs

let es_inv_raw (#t:Type0) (s:elim_stack t) : slprop = es_inv_inner s.head s.nm.gr

let is_es (#t:Type0) (s:elim_stack t) : slprop = inv s.inm (es_inv_raw s)

(* ================================================================ *)
(* new_stack                                                        *)
(* ================================================================ *)

fn new_elim_stack (#t:Type0) ()
  requires emp
  returns s : elim_stack t
  ensures is_es s ** es_content s.nm []
{
  let hd0 = Pulse.Lib.LinkedList.create t;
  let head = B.alloc hd0;
  let gr = GR.alloc #(list t) [];
  GR.share gr;
  let nm : es_ghost t = { gr };
  rewrite (GR.pts_to gr #0.5R []) as (GR.pts_to nm.gr #0.5R []);
  rewrite (GR.pts_to gr #0.5R []) as (es_content nm []);
  fold (es_inv_inner head nm.gr);
  let inm = new_invariant (es_inv_inner head nm.gr);
  let s : elim_stack t = { head; nm; inm };
  rewrite (inv inm (es_inv_inner head nm.gr)) as (inv s.inm (es_inv_raw s));
  fold (is_es s);
  rewrite (es_content nm []) as (es_content s.nm []);
  s
}

(* ================================================================ *)
(* Atomic read helper                                               *)
(* ================================================================ *)

fn read_llist_box_impl (#t:Type0) (r : box (llist t)) (#v : erased (llist t)) (#p:perm)
  preserves r |-> Frac p v
  returns x : llist t
  ensures rewrites_to x (reveal v)
{ !r }

let read_llist_box_atomic (#t:Type0) (r : box (llist t)) (#v : erased (llist t)) (#p:perm)
  : stt_atomic (llist t) #Observable emp_inames
    (B.pts_to r #p v) (fun x -> B.pts_to r #p v ** pure (x == reveal v))
  = Pulse.Lib.Core.as_atomic _ _ (read_llist_box_impl r #v #p)

(* ================================================================ *)
(* read_head                                                        *)
(* ================================================================ *)

fn read_es_head (#t:Type0) (s:elim_stack t)
  requires is_es s
  returns cur : llist t
  ensures is_es s
{
  unfold is_es;
  let cur = with_invariants (llist t) emp_inames s.inm (es_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold es_inv_raw; unfold es_inv_inner;
    let c = read_llist_box_atomic s.head;
    fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
    c
  };
  fold (is_es s);
  cur
}

(* ================================================================ *)
(* try_push: CAS-based push (same as Treiber)                      *)
(* ================================================================ *)

fn try_push_es_impl (#t:Type0) (s:elim_stack t) (v:t) (old_hd : llist t)
    (#xs : erased (list t))
  requires es_inv_raw s ** GR.pts_to s.nm.gr #0.5R xs
  returns b : bool
  ensures es_inv_raw s **
    P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs)
{
  unfold es_inv_raw; unfold es_inv_inner;
  let cur_hd = !s.head;
  if (llist_eq cur_hd old_hd) {
    with hd0 xs0.
      assert (B.pts_to s.head hd0 ** is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 ** GR.pts_to s.nm.gr #0.5R xs);
    GR.pts_to_injective_eq s.nm.gr;
    rewrite each xs0 as (reveal xs);
    let new_hd = Pulse.Lib.LinkedList.cons v cur_hd;
    s.head := new_hd;
    GR.gather s.nm.gr;
    GR.(s.nm.gr := Cons v (reveal xs));
    GR.share s.nm.gr;
    fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
    fold (P.cond true (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs));
    true
  } else {
    fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
    fold (P.cond false (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs));
    false
  }
}

let try_push_es_atomic (#t:Type0) (s:elim_stack t) (v:t) (old_hd : llist t)
    (#xs : erased (list t))
  : stt_atomic bool #Observable emp_inames
    (es_inv_raw s ** GR.pts_to s.nm.gr #0.5R xs)
    (fun b -> es_inv_raw s **
      P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs))
  = Pulse.Lib.Core.as_atomic _ _ (try_push_es_impl s v old_hd #xs)

fn try_push_es (#t:Type0) (s:elim_stack t) (v:t) (old_hd : llist t)
    (#xs : erased (list t))
  requires is_es s ** GR.pts_to s.nm.gr #0.5R xs
  returns b : bool
  ensures P.cond b
    (is_es s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
    (is_es s ** GR.pts_to s.nm.gr #0.5R xs)
{
  unfold is_es;
  let b = with_invariants bool emp_inames s.inm (es_inv_raw s)
    (GR.pts_to s.nm.gr #0.5R xs)
    (fun b -> P.cond b (GR.pts_to s.nm.gr #0.5R (Cons v xs)) (GR.pts_to s.nm.gr #0.5R xs))
  fn _ { try_push_es_atomic s v old_hd #xs };
  if b {
    elim_cond_true _ _ _;
    fold (is_es s);
    intro_cond_true (is_es s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                    (is_es s ** GR.pts_to s.nm.gr #0.5R xs); true
  } else {
    elim_cond_false _ _ _;
    fold (is_es s);
    intro_cond_false (is_es s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                     (is_es s ** GR.pts_to s.nm.gr #0.5R xs); false
  }
}

(* ================================================================ *)
(* push with elimination: try CAS, on fail try offer                *)
(* ================================================================ *)

fn rec push_loop (#t:Type0) (s:elim_stack t) (v:t)
    (tok : au_token (list t) unit
      (fun xs -> es_content s.nm xs)
      (fun xs _ -> es_content s.nm (Cons v xs))
      (fun xs _ -> es_content s.nm (Cons v xs)))
    (_u:unit)
  requires is_es s ** au_available tok
  ensures is_es s ** (exists* (xs_out : list t). es_content s.nm xs_out)
{
  let old_hd = read_es_head s;
  later_credit_buy 1;
  let xs = au_open tok;
  unfold es_content;
  let b = try_push_es s v old_hd;
  if b {
    elim_cond_true _ _ _;
    fold (es_content s.nm (Cons v xs));
    au_commit tok (reveal xs) ();
  } else {
    elim_cond_false _ _ _;
    fold (es_content s.nm xs);
    later_credit_buy 1;
    au_abort tok (reveal xs);
    // In the full elimination stack, we would try the offer channel here.
    // For now, just retry the CAS (same as basic Treiber).
    push_loop s v tok ()
  }
}

ghost
fn mk_es_push_trade (#t:Type0) (s : elim_stack t) (v : t) (#xs : erased (list t))
  requires emp
  ensures (forall* (y:unit). es_content s.nm (Cons v xs) @==> es_content s.nm (Cons v xs))
{
  intro_forall #unit #(fun (y:unit) -> es_content s.nm (Cons v xs) @==> es_content s.nm (Cons v xs))
    emp
    fn (y:unit) {
      intro_trade (es_content s.nm (Cons v xs)) (es_content s.nm (Cons v xs)) emp
        fn _ { () }
    }
}

fn push_es (#t:Type0) (s:elim_stack t) (v:t)
  requires is_es s ** es_content s.nm 'xs
  ensures is_es s ** (exists* ys. es_content s.nm ys)
{
  mk_es_push_trade s v #'xs;
  let tok = au_intro #(list t) #unit
    #(fun xs -> es_content s.nm xs)
    #(fun xs _ -> es_content s.nm (Cons v xs))
    #(fun xs _ -> es_content s.nm (Cons v xs))
    'xs;
  push_loop s v tok ()
}

(* ================================================================ *)
(* pop with elimination (CAS-only for now)                          *)
(* ================================================================ *)

let es_pop_val (#t:Type0) (xs: list t) : option t =
  match xs with | [] -> None | v::_ -> Some v

let es_pop_rest (#t:Type0) (xs: list t) : list t =
  match xs with | [] -> [] | _::xs' -> xs'

let es_pop_post (#t:Type0) (g:es_ghost t) (xs: list t) (ov: option t) : slprop =
  es_content g (es_pop_rest xs) ** pure (ov == es_pop_val xs)

fn try_pop_es_impl (#t:Type0) (s:elim_stack t) (old_hd : llist t)
    (out : box (option t)) (#xs : erased (list t))
  requires es_inv_raw s ** GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)
  returns b : bool
  ensures es_inv_raw s **
    P.cond b
      (GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
      (GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t))
{
  unfold es_inv_raw; unfold es_inv_inner;
  let cur_hd = !s.head;
  if (llist_eq cur_hd old_hd) {
    with hd0 xs0.
      assert (B.pts_to s.head hd0 ** is_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 ** GR.pts_to s.nm.gr #0.5R xs);
    GR.pts_to_injective_eq s.nm.gr;
    rewrite each xs0 as (reveal xs);
    let b = is_empty cur_hd;
    if b {
      fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
      fold (P.cond true
        (GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
        (GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)));
      true
    } else {
      let popped = Pulse.Lib.LinkedList.pop cur_hd;
      s.head := fst popped;
      out := Some (snd popped);
      GR.gather s.nm.gr;
      GR.(s.nm.gr := List.Tot.tl (reveal xs));
      GR.share s.nm.gr;
      fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
      rewrite each (List.Tot.tl (reveal xs)) as (es_pop_rest (reveal xs));
      rewrite each (Some (snd popped)) as (es_pop_val (reveal xs));
      fold (P.cond true
        (GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
        (GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)));
      true
    }
  } else {
    fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
    fold (P.cond false
      (GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
      (GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)));
    false
  }
}

let try_pop_es_atomic (#t:Type0) (s:elim_stack t) (old_hd : llist t)
    (out : box (option t)) (#xs : erased (list t))
  : stt_atomic bool #Observable emp_inames
    (es_inv_raw s ** GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t))
    (fun b -> es_inv_raw s **
      P.cond b
        (GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
        (GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)))
  = Pulse.Lib.Core.as_atomic _ _ (try_pop_es_impl s old_hd out #xs)

fn try_pop_es (#t:Type0) (s:elim_stack t) (old_hd : llist t)
    (out : box (option t)) (#xs : erased (list t))
  requires is_es s ** GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)
  returns b : bool
  ensures P.cond b
    (is_es s ** GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
    (is_es s ** GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t))
{
  unfold is_es;
  let b = with_invariants bool emp_inames s.inm (es_inv_raw s)
    (GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t))
    (fun b -> P.cond b
      (GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
      (GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)))
  fn _ { try_pop_es_atomic s old_hd out #xs };
  if b {
    elim_cond_true _ _ _;
    fold (is_es s);
    intro_cond_true
      (is_es s ** GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
      (is_es s ** GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)); true
  } else {
    elim_cond_false _ _ _;
    fold (is_es s);
    intro_cond_false
      (is_es s ** GR.pts_to s.nm.gr #0.5R (es_pop_rest (reveal xs)) ** out |-> (es_pop_val (reveal xs)))
      (is_es s ** GR.pts_to s.nm.gr #0.5R xs ** out |-> (None #t)); false
  }
}

fn rec pop_es_loop (#t:Type0) (s:elim_stack t)
    (tok : au_token (list t) (option t)
      (fun xs -> es_content s.nm xs)
      (fun xs ov -> es_pop_post s.nm xs ov)
      (fun xs ov -> es_pop_post s.nm xs ov))
    (out : box (option t))
    (_u:unit)
  requires is_es s ** au_available tok ** out |-> (None #t)
  ensures is_es s ** (exists* (xs:list t) (ov:option t). es_pop_post s.nm xs ov ** out |-> ov)
{
  let old_hd = read_es_head s;
  later_credit_buy 1;
  let xs = au_open tok;
  unfold es_content;
  let b = try_pop_es s old_hd out;
  if b {
    elim_cond_true _ _ _;
    fold (es_content s.nm (es_pop_rest (reveal xs)));
    fold (es_pop_post s.nm (reveal xs) (es_pop_val (reveal xs)));
    au_commit tok (reveal xs) (es_pop_val (reveal xs));
  } else {
    elim_cond_false _ _ _;
    fold (es_content s.nm xs);
    later_credit_buy 1;
    au_abort tok (reveal xs);
    // In full elimination stack, would try accept an offer here
    pop_es_loop s tok out ()
  }
}

ghost
fn mk_es_pop_trade (#t:Type0) (s : elim_stack t) (#xs : erased (list t))
  requires emp
  ensures (forall* (ov:option t). es_pop_post s.nm (reveal xs) ov @==> es_pop_post s.nm (reveal xs) ov)
{
  intro_forall #(option t) #(fun (ov:option t) -> es_pop_post s.nm (reveal xs) ov @==> es_pop_post s.nm (reveal xs) ov)
    emp
    fn (ov:option t) {
      intro_trade (es_pop_post s.nm (reveal xs) ov) (es_pop_post s.nm (reveal xs) ov) emp
        fn _ { () }
    }
}

fn pop_es (#t:Type0) (s:elim_stack t)
  requires is_es s ** es_content s.nm 'xs
  returns ov : option t
  ensures is_es s ** (exists* (xs:list t). es_content s.nm (es_pop_rest xs) ** pure (ov == es_pop_val xs))
{
  mk_es_pop_trade s #'xs;
  let tok = au_intro #(list t) #(option t)
    #(fun xs -> es_content s.nm xs)
    #(fun xs ov -> es_pop_post s.nm xs ov)
    #(fun xs ov -> es_pop_post s.nm xs ov)
    'xs;
  let out = B.alloc (None #t);
  pop_es_loop s tok out ();
  let xs2 = elim_exists #(list t) (fun (xs:list t) -> exists* (ov:option t). es_pop_post s.nm xs ov ** out |-> ov);
  let ov2 = elim_exists #(option t) (fun (ov:option t) -> es_pop_post s.nm (reveal xs2) ov ** out |-> ov);
  unfold (es_pop_post s.nm (reveal xs2) (reveal ov2));
  let ov = !out;
  B.free out;
  ov
}
