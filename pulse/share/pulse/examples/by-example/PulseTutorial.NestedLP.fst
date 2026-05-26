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
(* Level 2b: MODULAR FAA via cas_via_llsc as BLACK BOX              *)
(*                                                                  *)
(* This version calls cas_via_llsc modularly, choosing Φ_inner so   *)
(* that when the inner CAS commits, it commits the outer FAA AU     *)
(* through the trade chain.                                         *)
(*                                                                  *)
(* Key insight: cas_via_llsc is a lat_void. We choose:              *)
(*   Φ_inner(m, _) = phi_outer(n, old_n) ** pure (m == old_n)      *)
(* The inner trade captures au_opened outer_tok and commits the     *)
(* outer AU inside. For the m≠old_n branch, the trade has False     *)
(* in hypothesis (pure (m == old_n) when m ≠ old_n), so it fires    *)
(* vacuously. In practice, cas_via_llsc only commits at SC success  *)
(* where m == old_n == n, so this branch is never reached.          *)
(* ================================================================ *)

(* ================================================================ *)
(* Level 2b: MODULAR FAA via cas_via_llsc as BLACK BOX              *)
(*                                                                  *)
(* This version calls cas_via_llsc modularly. The inner CAS's Φ     *)
(* commits the outer FAA's AU at the successful SC.                 *)
(*                                                                  *)
(* Design: The inner CAS AU has:                                    *)
(*   α_inner(m) = ctr_val m ** au_opened outer_tok n ** pure(m==n)  *)
(*   β_inner(m,_) = ctr_val(add(m,delta)) ** au_opened outer_tok n *)
(*                  ** pure(m==n)                                   *)
(* Only when m = old_n does SC succeed.                             *)
(* Φ_inner(m,_) = phi(n, old_n)                                    *)
(*                                                                  *)
(* The trade converts β_inner → Φ_inner by committing the outer AU.*)
(* Since β_inner carries pure(m==n), the trade can rewrite m→n.    *)
(* ================================================================ *)

(* ================================================================ *)
(* Level 2b: MODULAR FAA via cas_via_llsc as BLACK BOX              *)
(*                                                                  *)
(* The inner CAS commits the outer FAA AU through a trade chain.    *)
(*                                                                  *)
(* Key trick: use a DIFFERENT inner CAS spec where β_inner carries  *)
(* pure(m == old_n). try_sc already proves this on SC success.      *)
(* The trade hypothesis then has this proof, enabling the rewrite   *)
(* from ctr_val(add(old_n,delta)) to ctr_val(add(n,delta)).         *)
(*                                                                  *)
(* Inner CAS spec:                                                  *)
(*   α(m) = ctr_val m                                               *)
(*   β(m,_) = ctr_val(add(old_n,delta)) ** pure(m == old_n)        *)
(*     (only the success case; failure aborts+retries inside CAS)   *)
(*   Φ(m,_) = phi_outer(n, old_n)                                  *)
(*                                                                  *)
(* The trade: lc 1 ** ctr_val(add(old_n,d)) ** pure(m==old_n)      *)
(*   @==> phi_outer(n, old_n)                                       *)
(* Body: rewrite m→n (since m==old_n and n==old_n from ghost),      *)
(*   fold β_outer, au_commit outer → phi_outer.                     *)
(* ================================================================ *)

(** cas_commit_only: variant of cas_via_llsc that only commits on success.
    β always carries the full post-CAS state + success proof.
    On LL mismatch or SC failure, aborts and retries. *)
fn rec cas_commit_only (c:counter) (expected new_val : U32.t)
    (#phi : U32.t -> unit -> slprop)
    (tok : au_token emp_inames U32.t unit
      (fun n -> ctr_val c.cg n)
      (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
      phi)
    (_u:unit)
  requires is_ctr c ** au_available tok
  ensures is_ctr c ** (exists* n. phi n ())
{
  // LL: read current value
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
  // Open AU
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;
  if (cur = expected) {
    // Value matches: try SC
    let b = try_sc c expected new_val;
    if b {
      elim_cond_true _ _;
      // SC succeeded: n == expected (from ghost agreement + SC proof)
      fold (ctr_val c.cg new_val);
      later_credit_buy 1;
      au_commit tok (reveal n) ();
    } else {
      elim_cond_false _ _;
      fold (ctr_val c.cg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      cas_commit_only c expected new_val tok ()
    }
  } else {
    // LL mismatch — abort and retry
    fold (ctr_val c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    cas_commit_only c expected new_val tok ()
  }
}

(** Type witness *)
let cas_commit_is_lat (c:counter) (expected new_val : U32.t)
  : lat_void emp_inames U32.t
    (fun n -> ctr_val c.cg n)
    (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
    (is_ctr c)
  = fun #phi tok _u -> cas_commit_only c expected new_val #phi tok _u

(** Modular FAA: calls cas_commit_only as a BLACK BOX.
    The inner CAS's Φ commits the outer FAA's AU at the SC LP.
    True nested LP via trade chain. *)
fn rec faa_modular (c:counter) (delta:U32.t)
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
  // Read current value (outside AU)
  let old_n = read_ctr c;
  // Open outer FAA AU
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;

  // Build inner CAS trade: β_inner @==> Φ_inner
  // β_inner(m,_) = ctr_val(add(old_n,delta)) ** pure(m == old_n)
  // Φ_inner(m,_) = phi(n, old_n)
  //
  // Trade captures: au_opened tok n
  // Trade body:
  //   1. From pure(m == old_n), we know the CAS succeeded at value old_n
  //   2. The inner AU's m == old_n, and ghost agreement gives n == m == old_n
  //   3. Rewrite ctr_val(add(old_n,delta)) as ctr_val(add(n,delta))
  //   4. Fold β_outer(n, old_n)
  //   5. au_commit tok → phi(n, old_n)

  intro_forall #unit
    #(fun (_:unit) ->
      (later_credit 1 ** ctr_val c.cg (U32.add_mod old_n delta) ** pure (reveal n == old_n))
      @==> phi (reveal n) old_n)
    (au_opened tok (reveal n))
    fn (_y:unit) {
      intro_trade
        (later_credit 1 ** ctr_val c.cg (U32.add_mod old_n delta) ** pure (reveal n == old_n))
        (phi (reveal n) old_n)
        (au_opened tok (reveal n))
        fn _ {
          // Inside trade: we have
          //   later_credit 1
          //   ctr_val c.cg (add(old_n, delta))
          //   pure (reveal n == old_n)     ← from β_inner
          //   au_opened tok (reveal n)     ← from trade frame
          //
          // Since n == old_n:
          //   ctr_val(add(old_n, delta)) = ctr_val(add(n, delta))
          rewrite (ctr_val c.cg (U32.add_mod old_n delta))
               as (ctr_val c.cg (U32.add_mod (reveal n) delta));
          // Commit outer AU: β_outer(n, old_n) = ctr_val(add(n,delta)) ** pure(old_n == n)
          au_commit tok (reveal n) old_n
        }
    };

  // Create inner AU
  fold (ctr_val c.cg (reveal n));
  let inner_tok = au_intro #emp_inames #U32.t #unit
    #(fun m -> ctr_val c.cg m)
    #(fun m _ -> ctr_val c.cg (U32.add_mod old_n delta) ** pure (m == old_n))
    #(fun m _ -> phi (reveal n) old_n)
    (reveal n);

  // Call inner CAS as BLACK BOX — at SC success, inner commit fires
  // trade, which commits outer AU. TRUE NESTED LP!
  cas_commit_only c old_n (U32.add_mod old_n delta) inner_tok ();
  with m. assert (phi (reveal n) old_n);
  old_n
}

(** Type witness for modular FAA *)
let faa_modular_is_lat (c:counter) (delta:U32.t)
  : lat emp_inames U32.t U32.t
    (fun n -> ctr_val c.cg n)
    (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    (is_ctr c)
  = fun #phi tok _u -> faa_modular c delta #phi tok _u
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
