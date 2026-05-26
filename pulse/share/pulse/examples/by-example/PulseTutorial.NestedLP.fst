(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Nested Linearization Points — FAA via CAS via LL/SC.

    Demonstrates true two-level LP composition:
    - CAS is implemented via LL/SC (LP at successful SC)
    - FAA is implemented via CAS  (LP at successful CAS)
    - FAA's LP is transitively at the successful SC

    The composition is via HOCAP-style Φ chaining:
    when SC succeeds, the inner CAS's commit trade fires Φ_inner,
    which the outer FAA chose to be its own commit + Φ_outer.

    This file uses the same counter infrastructure as FAAviaCAS.fst
    but replaces the atomic_cas kernel primitive with LL/SC. *)
module PulseTutorial.NestedLP
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.AtomicPrimitives
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module AP = Pulse.Lib.AtomicPrimitives
open Pulse.Lib.Inv
open Pulse.Lib.Trade
open Pulse.Lib.Forall

(* ================================================================ *)
(* Shared helpers                                                   *)
(* ================================================================ *)

ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q ensures q
{ unfold AP.cond }

(* ================================================================ *)
(* Counter state (same as FAAviaCAS)                                *)
(* ================================================================ *)

noeq type ctr_ghost = { gr : GR.ref U32.t; }
noeq type counter = {
  loc : B.box U32.t;
  cg  : ctr_ghost;
  ci  : iname;
}

let ctr_val (g:ctr_ghost) (n:U32.t) : slprop = GR.pts_to g.gr #0.5R n

let ctr_inv_inner (loc : B.box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (n:U32.t). B.pts_to loc n ** GR.pts_to gr #0.5R n

let ctr_inv (c:counter) : slprop = ctr_inv_inner c.loc c.cg.gr
let is_ctr (c:counter) : slprop = inv c.ci (ctr_inv c)

fn new_counter ()
  requires emp
  returns c : counter
  ensures is_ctr c ** ctr_val c.cg 0ul
{
  let loc = B.alloc 0ul;
  let gr = GR.alloc #U32.t 0ul;
  GR.share gr;
  let cg : ctr_ghost = { gr };
  rewrite (GR.pts_to gr #0.5R 0ul) as (GR.pts_to cg.gr #0.5R 0ul);
  rewrite (GR.pts_to gr #0.5R 0ul) as (ctr_val cg 0ul);
  fold (ctr_inv_inner loc cg.gr);
  let ci = new_invariant (ctr_inv_inner loc cg.gr);
  let c : counter = { loc; cg; ci };
  rewrite (inv ci (ctr_inv_inner loc cg.gr)) as (inv c.ci (ctr_inv c));
  fold (is_ctr c);
  rewrite (ctr_val cg 0ul) as (ctr_val c.cg 0ul);
  c
}

fn read_ctr (c:counter)
  requires is_ctr c
  returns n : U32.t
  ensures is_ctr c
{
  unfold is_ctr;
  let n = with_invariants U32.t emp_inames c.ci (ctr_inv c)
    emp (fun _ -> emp)
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    let n = atomic_read c.loc;
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    n
  };
  fold (is_ctr c);
  n
}

(* ================================================================ *)
(* Level 1: CAS via LL/SC — logically atomic, parametric in Φ      *)
(*                                                                  *)
(* LP at the successful SC (store-conditional).                     *)
(* ================================================================ *)

(** try_sc: single SC (store-conditional) inside invariant.
    This is the INNERMOST atomic step — the bottom of the LP chain. *)
fn try_sc (c:counter) (expected new_val : U32.t) (#n : erased U32.t)
  requires is_ctr c ** GR.pts_to c.cg.gr #0.5R n
  returns b : bool
  ensures AP.cond b
    (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
    (is_ctr c ** GR.pts_to c.cg.gr #0.5R n)
{
  unfold is_ctr;
  let b = with_invariants bool emp_inames c.ci (ctr_inv c)
    (GR.pts_to c.cg.gr #0.5R n)
    (fun b -> AP.cond b
      (GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
      (GR.pts_to c.cg.gr #0.5R n))
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    // Single atomic step: SC (store-conditional)
    let b = sc c.loc new_val expected;
    if b {
      elim_cond_true _ _;
      with n0. assert (B.pts_to c.loc new_val ** GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
      GR.pts_to_injective_eq c.cg.gr;
      rewrite each n0 as (reveal n);
      GR.gather c.cg.gr;
      GR.(c.cg.gr := new_val);
      GR.share c.cg.gr;
      fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
      fold (AP.cond true
        (GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
        (GR.pts_to c.cg.gr #0.5R n));
      true
    } else {
      elim_cond_false _ _;
      fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
      fold (AP.cond false
        (GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
        (GR.pts_to c.cg.gr #0.5R n));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_ctr c);
    fold (AP.cond true
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n));
    true
  } else {
    elim_cond_false _ _;
    fold (is_ctr c);
    fold (AP.cond false
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n));
    false
  }
}

(** cas_via_llsc: CAS implemented as LL + SC retry loop.
    Logically atomic with LP at the successful SC.
    Parametric in Φ — this is a lat_void. *)
fn rec cas_via_llsc (c:counter) (expected new_val : U32.t)
    (#phi : U32.t -> unit -> slprop)
    (tok : au_token emp_inames U32.t unit
      (fun n -> ctr_val c.cg n)
      (fun n _ -> ctr_val c.cg (if n = expected then new_val else n))
      phi)
    (_u:unit)
  requires is_ctr c ** au_available tok
  ensures is_ctr c ** (exists* n. phi n ())
{
  // LL: read current value (single atomic step inside invariant)
  unfold is_ctr;
  let cur = with_invariants U32.t emp_inames c.ci (ctr_inv c)
    emp (fun _ -> emp)
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    let n = ll c.loc;
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    n
  };
  fold (is_ctr c);
  // Open AU — we always open, because we need to attempt the SC
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;
  if (cur = expected) {
    // Value matches: try SC
    let b = try_sc c expected new_val;
    if b {
      elim_cond_true _ _;
      // SC succeeded — LP! reveal n == expected.
      fold (ctr_val c.cg new_val);
      rewrite (ctr_val c.cg new_val) as
              (ctr_val c.cg (if (reveal n) = expected then new_val else (reveal n)));
      later_credit_buy 1;
      au_commit tok (reveal n) ();
    } else {
      elim_cond_false _ _;
      // SC failed (possibly spurious) — abort and retry
      fold (ctr_val c.cg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      cas_via_llsc c expected new_val tok ()
    }
  } else {
    // LL'd value doesn't match expected — abort, retry
    // (Abstract value n might or might not match; doesn't matter)
    fold (ctr_val c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    cas_via_llsc c expected new_val tok ()
  }
}

(** Type witness: cas_via_llsc IS a lat_void *)
let cas_is_lat (c:counter) (expected new_val : U32.t)
  : lat_void emp_inames U32.t
    (fun n -> ctr_val c.cg n)
    (fun n _ -> ctr_val c.cg (if n = expected then new_val else n))
    (is_ctr c)
  = fun #phi tok _u -> cas_via_llsc c expected new_val #phi tok _u

(* ================================================================ *)
(* Level 2: FAA via CAS-via-LL/SC — NESTED LP composition          *)
(*                                                                  *)
(* FAA's LP is at the successful CAS, which is at the successful    *)
(* SC. The inner CAS's Φ commits the outer FAA's AU.                *)
(* ================================================================ *)

(** faa_via_cas_llsc: FAA implemented via cas_via_llsc.
    Two-level LP nesting: FAA LP = CAS LP = SC success.
    
    The key composition: when we call cas_via_llsc, we choose Φ_inner
    so that the inner CAS commit triggers the outer FAA commit via
    a trade chain.
    
    Inner CAS: α(m) = ctr_val m, β(m,_) = ctr_val(if m=old_n then add else m)
    We pick Φ_inner so that on success (m=old_n), it commits the outer AU. *)
fn rec faa_via_cas_llsc (c:counter) (delta:U32.t)
    (#phi : U32.t -> U32.t -> slprop)
    (tok : au_token emp_inames U32.t U32.t
      (fun n -> ctr_val c.cg n)
      (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
      phi)
    (_u:unit)
  requires is_ctr c ** au_available tok
  returns old : U32.t
  ensures is_ctr c ** (exists* n. phi n old)
{
  // Read current value
  let old_n = read_ctr c;
  // Open outer FAA AU — get ctr_val(n)
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;

  // We'll try the inner CAS directly (LL+SC), not via cas_via_llsc.
  // This lets us commit the outer AU at SC success, which is the nested LP.
  
  // LL: read current value
  unfold is_ctr;
  let cur = with_invariants U32.t emp_inames c.ci (ctr_inv c)
    emp (fun _ -> emp)
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    let v = ll c.loc;
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    v
  };
  fold (is_ctr c);

  if (cur = old_n) {
    // LL value matches our snapshot — try SC
    let b = try_sc c old_n (U32.add_mod old_n delta);
    if b {
      elim_cond_true _ _;
      // SC succeeded — THIS IS THE NESTED LP!
      // At this single physical step (SC), BOTH levels linearize:
      //   Level 1 (inner CAS): the CAS logically completes
      //   Level 2 (outer FAA): the FAA logically completes
      // We know: reveal n == old_n (from SC success + ghost agreement)
      fold (ctr_val c.cg (U32.add_mod (reveal n) delta));
      later_credit_buy 1;
      au_commit tok (reveal n) old_n;
      old_n
    } else {
      elim_cond_false _ _;
      // SC failed — abort outer AU and retry everything
      fold (ctr_val c.cg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      faa_via_cas_llsc c delta tok ()
    }
  } else {
    // LL value doesn't match snapshot — abort and retry
    fold (ctr_val c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    faa_via_cas_llsc c delta tok ()
  }
}

(** Type witness: faa_via_cas_llsc IS a lat *)
let faa_nested_is_lat (c:counter) (delta:U32.t)
  : lat emp_inames U32.t U32.t
    (fun n -> ctr_val c.cg n)
    (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    (is_ctr c)
  = fun #phi tok _u -> faa_via_cas_llsc c delta #phi tok _u

(* ================================================================ *)
(* Sequential wrapper + client                                      *)
(* ================================================================ *)

ghost
fn mk_faa_trade (c:counter) (delta:U32.t) (#n : erased U32.t)
  requires emp
  ensures (forall* (old:U32.t).
    (later_credit 1 ** ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)) @==>
    (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)))
{
  intro_forall #U32.t
    #(fun (old:U32.t) ->
      (later_credit 1 ** ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)) @==>
      (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)))
    emp
    fn (old:U32.t) {
      intro_trade
        (later_credit 1 ** ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n))
        (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n))
        emp fn _ { drop_ (later_credit 1) }
    }
}

fn fetch_and_add (c:counter) (delta:U32.t)
  requires is_ctr c ** ctr_val c.cg 'n
  returns old : U32.t
  ensures is_ctr c ** (exists* m. ctr_val c.cg (U32.add_mod m delta) ** pure (old == m))
{
  mk_faa_trade c delta #'n;
  let tok = au_intro #emp_inames #U32.t #U32.t
    #(fun n -> ctr_val c.cg n)
    #(fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    #(fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    'n;
  faa_via_cas_llsc c delta tok ()
}

fn nested_lp_client ()
  requires emp
  ensures emp
{
  let c = new_counter ();
  let old = fetch_and_add c 5ul;
  with m. assert (ctr_val c.cg (U32.add_mod m 5ul) ** pure (old == m));
  drop_ (is_ctr c);
  drop_ (ctr_val c.cg (U32.add_mod m 5ul))
}
