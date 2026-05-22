(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Atomic Counter — CAS-loop increment with LA spec.
    Also demonstrates lat_open (invariant opening around LA ops). *)
module PulseTutorial.AtomicCounter
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
open Pulse.Lib.AtomicPrimitives
module AP = Pulse.Lib.AtomicPrimitives
open Pulse.Lib.Inv
open Pulse.Lib.Trade
open Pulse.Lib.Forall
open Pulse.Lib.Box { box, (:=), (!) }

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
(* Counter representation                                           *)
(* ================================================================ *)

noeq type ctr_ghost = { gr : GR.ref U32.t; }
noeq type counter = {
  loc : box U32.t;
  cg  : ctr_ghost;
  ci  : iname;
}

let ctr_content (g:ctr_ghost) (n:U32.t) : slprop = GR.pts_to g.gr #0.5R n

let ctr_inv_raw (loc : box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (n:U32.t). B.pts_to loc n ** GR.pts_to gr #0.5R n

let is_ctr (c:counter) : slprop = inv c.ci (ctr_inv_raw c.loc c.cg.gr)

(* ================================================================ *)
(* new_counter                                                      *)
(* ================================================================ *)

fn new_counter ()
  requires emp
  returns c : counter
  ensures is_ctr c ** ctr_content c.cg 0ul
{
  let loc = B.alloc 0ul;
  let gr = GR.alloc #U32.t 0ul;
  GR.share gr;
  let cg : ctr_ghost = { gr };
  rewrite (GR.pts_to gr #0.5R 0ul) as (GR.pts_to cg.gr #0.5R 0ul);
  rewrite (GR.pts_to gr #0.5R 0ul) as (ctr_content cg 0ul);
  fold (ctr_inv_raw loc cg.gr);
  let ci = new_invariant (ctr_inv_raw loc cg.gr);
  let c : counter = { loc; cg; ci };
  rewrite (inv ci (ctr_inv_raw loc cg.gr)) as (inv c.ci (ctr_inv_raw c.loc c.cg.gr));
  rewrite (ctr_content cg 0ul) as (ctr_content c.cg 0ul);
  fold (is_ctr c);
  c
}

(* ================================================================ *)
(* get — logically atomic read                                      *)
(* ================================================================ *)

fn get (c:counter)
  requires is_ctr c
  returns n : U32.t
  ensures is_ctr c
{
  unfold is_ctr;
  let n = with_invariants U32.t emp_inames c.ci (ctr_inv_raw c.loc c.cg.gr)
    emp (fun _ -> emp)
  fn _ {
    unfold ctr_inv_raw;
    let n = atomic_read c.loc;
    fold (ctr_inv_raw c.loc c.cg.gr);
    n
  };
  fold (is_ctr c);
  n
}

(* ================================================================ *)
(* increment — CAS loop with LA spec                                *)
(* ================================================================ *)

fn try_incr (c:counter) (old_n : U32.t) (#n : erased U32.t)
  requires is_ctr c ** GR.pts_to c.cg.gr #0.5R n
  returns b : bool
  ensures AP.cond b
    (is_ctr c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
    (is_ctr c ** GR.pts_to c.cg.gr #0.5R n)
{
  unfold is_ctr;
  let b = with_invariants bool emp_inames c.ci (ctr_inv_raw c.loc c.cg.gr)
    (GR.pts_to c.cg.gr #0.5R n)
    (fun b -> AP.cond b
      (GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
      (GR.pts_to c.cg.gr #0.5R n))
  fn _ {
    unfold ctr_inv_raw;
    let b = atomic_cas c.loc old_n (U32.add_mod old_n 1ul);
    if b {
      elim_cond_true _ _;
      with n0. assert (
        B.pts_to c.loc (U32.add_mod old_n 1ul) **
        pure (reveal (hide n0) == old_n) **
        GR.pts_to c.cg.gr #0.5R n0 **
        GR.pts_to c.cg.gr #0.5R n);
      GR.pts_to_injective_eq c.cg.gr;
      rewrite each n0 as (reveal n);
      GR.gather c.cg.gr;
      GR.(c.cg.gr := U32.add_mod (reveal n) 1ul);
      GR.share c.cg.gr;
      fold (ctr_inv_raw c.loc c.cg.gr);
      fold (AP.cond true
        (GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
        (GR.pts_to c.cg.gr #0.5R n));
      true
    } else {
      elim_cond_false _ _;
      fold (ctr_inv_raw c.loc c.cg.gr);
      fold (AP.cond false
        (GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
        (GR.pts_to c.cg.gr #0.5R n));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_ctr c);
    intro_cond_true
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    true
  } else {
    elim_cond_false _ _;
    fold (is_ctr c);
    intro_cond_false
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    false
  }
}

(** incr_loop: AU open/commit/abort CAS retry loop *)
fn rec incr_loop (c:counter)
    (tok : au_token U32.t unit
      (fun n -> ctr_content c.cg n)
      (fun n _ -> ctr_content c.cg (U32.add_mod n 1ul))
      (fun n _ -> ctr_content c.cg (U32.add_mod n 1ul)))
    (_u:unit)
  requires is_ctr c ** au_available tok
  ensures is_ctr c ** (exists* (n:U32.t). ctr_content c.cg (U32.add_mod n 1ul))
{
  let old_n = get c;
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_content;
  let b = try_incr c old_n;
  if b {
    elim_cond_true _ _;
    fold (ctr_content c.cg (U32.add_mod (reveal n) 1ul));
    au_commit tok (reveal n) ();
  } else {
    elim_cond_false _ _;
    fold (ctr_content c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    incr_loop c tok ()
  }
}

ghost
fn mk_incr_trade (c:counter) (#n : erased U32.t)
  requires emp
  ensures (forall* (y:unit). ctr_content c.cg (U32.add_mod (reveal n) 1ul) @==> ctr_content c.cg (U32.add_mod (reveal n) 1ul))
{
  intro_forall #unit #(fun (y:unit) -> ctr_content c.cg (U32.add_mod (reveal n) 1ul) @==> ctr_content c.cg (U32.add_mod (reveal n) 1ul))
    emp
    fn (y:unit) {
      intro_trade (ctr_content c.cg (U32.add_mod (reveal n) 1ul))
                  (ctr_content c.cg (U32.add_mod (reveal n) 1ul)) emp
        fn _ { () }
    }
}

(** increment: client-facing.
    Iris spec: <<< ∀∀ n, ctr_content γ n >>> incr c @ ↑N <<< ctr_content γ (n+1) | RET #n >>> *)
fn increment (c:counter)
  requires is_ctr c ** ctr_content c.cg 'n
  ensures is_ctr c ** (exists* m. ctr_content c.cg m)
{
  mk_incr_trade c #'n;
  let tok = au_intro #U32.t #unit
    #(fun n -> ctr_content c.cg n)
    #(fun n _ -> ctr_content c.cg (U32.add_mod n 1ul))
    #(fun n _ -> ctr_content c.cg (U32.add_mod n 1ul))
    'n;
  incr_loop c tok ()
}

(* ================================================================ *)
(* Client examples: composing LA operations                         *)
(* ================================================================ *)

(** Simple composition: increment twice.
    Demonstrates that LA operations compose cleanly. *)
fn incr_twice (c:counter)
  requires is_ctr c ** ctr_content c.cg 'n
  ensures is_ctr c ** (exists* m. ctr_content c.cg m)
{
  increment c;
  with m1. assert (ctr_content c.cg m1);
  increment c
}
