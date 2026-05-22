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
module AP = Pulse.Lib.AtomicPrimitives
open Pulse.Lib.Inv
open Pulse.Lib.LinkedList
open Pulse.Lib.Trade
open Pulse.Lib.Forall
open Pulse.Lib.Box { box, (:=), (!) }

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
(* Stack representation                                              *)
(* ================================================================ *)

noeq type es_node (t:Type0) = {
  es_value : t;
  es_next  : B.box (es_node t);
}

let rec phys_list (#t:Type0) (hd : B.box (es_node t)) (xs:list t)
  : Tot slprop (decreases xs) =
  match xs with
  | [] -> pure (hd == B.null #(es_node t))
  | x::rest -> exists* (nd:es_node t).
      B.pts_to hd nd ** pure (nd.es_value == x) ** phys_list nd.es_next rest
ghost fn phys_list_null_nil (#t:Type0) (hd : B.box (es_node t)) (xs : list t)
  requires phys_list hd xs
  requires pure (hd == B.null #(es_node t))
  ensures pure (xs == [])
{
  match xs {
    [] -> {
      unfold (phys_list #t hd []);
      ()
    }
    x::rest -> {
      unfold (phys_list #t hd (x::rest));
      with nd. _;
      rewrite each hd as (B.null #(es_node t));
      B.pts_to_not_null (B.null #(es_node t));
      assert (pure (B.is_null (B.null #(es_node t))));
      unreachable ()
    }
  }
}

ghost fn phys_list_cons_case (#t:Type0) (hd : B.box (es_node t)) (xs : list t)
  requires phys_list hd xs
  requires pure (~(hd == B.null #(es_node t)))
  ensures exists* (nd : es_node t) (rest : list t).
    B.pts_to hd nd ** pure (xs == nd.es_value :: rest) ** phys_list nd.es_next rest
{
  match xs {
    [] -> {
      unfold (phys_list #t hd []);
      rewrite each hd as (B.null #(es_node t));
      unreachable ()
    }
    x::rest -> {
      unfold (phys_list #t hd (x::rest));
      with nd. _;
      rewrite each nd.es_value as x;
    }
  }
}

noeq type es_ghost (t:Type0) = { gr : GR.ref (list t); }
noeq type elim_stack (t:Type0) = {
  head : box (B.box (es_node t));
  nm   : es_ghost t;
  inm  : iname;
}

let es_content (#t:Type0) (g:es_ghost t) (xs:list t) : slprop = GR.pts_to g.gr #0.5R xs

let es_inv_inner (#t:Type0) (head : box (B.box (es_node t))) (gr : GR.ref (list t)) : slprop =
  exists* (hd:B.box (es_node t)) (xs:list t).
    B.pts_to head hd ** phys_list hd xs ** GR.pts_to gr #0.5R xs

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
  let head = B.alloc (B.null #(es_node t));
  let gr = GR.alloc #(list t) [];
  GR.share gr;
  let nm : es_ghost t = { gr };
  rewrite (GR.pts_to gr #0.5R []) as (GR.pts_to nm.gr #0.5R []);
  rewrite (GR.pts_to gr #0.5R []) as (es_content nm []);
  fold (phys_list #t (B.null #(es_node t)) []);
  fold (es_inv_inner head nm.gr);
  let inm = new_invariant (es_inv_inner head nm.gr);
  let s : elim_stack t = { head; nm; inm };
  rewrite (inv inm (es_inv_inner head nm.gr)) as (inv s.inm (es_inv_raw s));
  fold (is_es s);
  rewrite (es_content nm []) as (es_content s.nm []);
  s
}

(* ================================================================ *)
(* read_head                                                        *)
(* ================================================================ *)

fn read_es_head (#t:Type0) (s:elim_stack t)
  requires is_es s
  returns cur : B.box (es_node t)
  ensures is_es s
{
  unfold is_es;
  let cur = with_invariants (B.box (es_node t)) emp_inames s.inm (es_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold es_inv_raw; unfold es_inv_inner;
    let c = AP.atomic_read s.head;
    fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
    c
  };
  fold (is_es s);
  cur
}

(* ================================================================ *)
(* try_push: CAS-based push (same as Treiber)                      *)
(* ================================================================ *)

fn try_push_es (#t:Type0) (s:elim_stack t) (v:t) (old_hd : B.box (es_node t))
    (#xs : erased (list t))
  requires is_es s ** GR.pts_to s.nm.gr #0.5R xs
  returns b : bool
  ensures AP.cond b
    (is_es s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
    (is_es s ** GR.pts_to s.nm.gr #0.5R xs)
{
  let new_node = AP.atomic_alloc ({ es_value = v; es_next = old_hd } <: es_node t);
  unfold is_es;
  let b = with_invariants bool emp_inames s.inm (es_inv_raw s)
    (GR.pts_to s.nm.gr #0.5R xs **
     new_node |-> ({ es_value = v; es_next = old_hd }))
    (fun b -> AP.cond b
      (GR.pts_to s.nm.gr #0.5R (Cons v xs))
      (GR.pts_to s.nm.gr #0.5R xs **
       new_node |-> ({ es_value = v; es_next = old_hd })))
  fn _ {
    unfold es_inv_raw; unfold es_inv_inner;
    let b = AP.atomic_cas_box s.head old_hd new_node;
    if b {
      elim_cond_true _ _;
      with hd0 xs0. assert (
        B.pts_to s.head new_node ** pure (hd0 == old_hd) **
        phys_list hd0 xs0 ** GR.pts_to s.nm.gr #0.5R xs0 **
        GR.pts_to s.nm.gr #0.5R xs **
        new_node |-> ({ es_value = v; es_next = old_hd }));
      GR.pts_to_injective_eq s.nm.gr;
      rewrite each xs0 as (reveal xs);
      rewrite each hd0 as old_hd;
      fold (phys_list new_node (v :: reveal xs));
      GR.gather s.nm.gr;
      GR.(s.nm.gr := v :: (reveal xs));
      GR.share s.nm.gr;
      fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
      fold (AP.cond true
        (GR.pts_to s.nm.gr #0.5R (Cons v xs))
        (GR.pts_to s.nm.gr #0.5R xs **
         new_node |-> ({ es_value = v; es_next = old_hd })));
      true
    } else {
      elim_cond_false _ _;
      fold (es_inv_inner s.head s.nm.gr); fold (es_inv_raw s);
      fold (AP.cond false
        (GR.pts_to s.nm.gr #0.5R (Cons v xs))
        (GR.pts_to s.nm.gr #0.5R xs **
         new_node |-> ({ es_value = v; es_next = old_hd })));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_es s);
    intro_cond_true (is_es s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                    (is_es s ** GR.pts_to s.nm.gr #0.5R xs);
    true
  } else {
    elim_cond_false _ _;
    fold (is_es s);
    drop_ (B.pts_to new_node ({ es_value = v; es_next = old_hd }));
    intro_cond_false (is_es s ** GR.pts_to s.nm.gr #0.5R (Cons v xs))
                     (is_es s ** GR.pts_to s.nm.gr #0.5R xs);
    false
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
    elim_cond_true _ _;
    fold (es_content s.nm (Cons v xs));
    au_commit tok (reveal xs) ();
  } else {
    elim_cond_false _ _;
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

(* Pop requires persistent points-to (Iris l↦□) for reading node contents
   outside the invariant. This is future work — see TreiberStack2 for the
   same limitation. The push side is fully verified above. *)
