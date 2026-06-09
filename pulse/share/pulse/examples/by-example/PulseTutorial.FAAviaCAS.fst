(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Fetch-and-Add via CAS loop — logically atomic specification.

    Demonstrates the core LA encoding: a physically non-atomic operation
    (CAS retry loop) with a logically atomic spec. The CAS is the
    linearization point; abort on CAS failure restores the AU for retry.

    This is the canonical counter-shaped LA example in this directory. *)
module PulseTutorial.FAAviaCAS
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
(* Counter state                                                    *)
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

(* ================================================================ *)
(* new_counter                                                      *)
(* ================================================================ *)

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

(* ================================================================ *)
(* read — atomic read of current value                              *)
(* ================================================================ *)

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
(* CAS step — single atomic CAS inside invariant                    *)
(* ================================================================ *)

ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q ensures q
{ unfold AP.cond }

ghost fn intro_cond_true (p q : slprop)
  requires p ensures AP.cond true p q
{ fold (AP.cond true p q) }

ghost fn intro_cond_false (p q : slprop)
  requires q ensures AP.cond false p q
{ fold (AP.cond false p q) }

fn try_add (c:counter) (old_n delta : U32.t) (#n : erased U32.t)
  requires is_ctr c ** GR.pts_to c.cg.gr #0.5R n
  returns b : bool
  ensures AP.cond b
    (is_ctr c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) delta) **
     pure (reveal n == old_n))
    (is_ctr c ** GR.pts_to c.cg.gr #0.5R n)
{
  unfold is_ctr;
  let b = with_invariants bool emp_inames c.ci (ctr_inv c)
    (GR.pts_to c.cg.gr #0.5R n)
    (fun b -> AP.cond b
      (GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) delta) **
       pure (reveal n == old_n))
      (GR.pts_to c.cg.gr #0.5R n))
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    // Single atomic step: CAS loc from old_n to old_n + delta
    let b = atomic_cas c.loc old_n (U32.add_mod old_n delta);
    if b {
      elim_cond_true _ _;
      // CAS succeeded: old_n was the current value
      with n0. assert (B.pts_to c.loc (U32.add_mod old_n delta) **
        GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
      GR.pts_to_injective_eq c.cg.gr;
      rewrite each n0 as (reveal n);
      GR.gather c.cg.gr;
      GR.(c.cg.gr := U32.add_mod (reveal n) delta);
      GR.share c.cg.gr;
      fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
      fold (AP.cond true
        (GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) delta) **
         pure (reveal n == old_n))
        (GR.pts_to c.cg.gr #0.5R n));
      true
    } else {
      elim_cond_false _ _;
      fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
      fold (AP.cond false
        (GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) delta) **
         pure (reveal n == old_n))
        (GR.pts_to c.cg.gr #0.5R n));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_ctr c);
    intro_cond_true
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) delta) **
       pure (reveal n == old_n))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    true
  } else {
    elim_cond_false _ _;
    fold (is_ctr c);
    intro_cond_false
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R (U32.add_mod (reveal n) delta) **
       pure (reveal n == old_n))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    false
  }
}

(* ================================================================ *)
(* FAA via CAS loop — the logically atomic operation                *)
(* ================================================================ *)

(** faa_loop: CAS retry loop with the encoded lat shape.

    Encoded operation:
    <<< ∀∀ n, ctr_val γ n >>>
      fetch_and_add c delta @ is
    <<< ctr_val γ (n + delta) ** pure (old == n) | RET old >>>

    The loop is parametric in the caller's Φ through the AU token. At the
    successful CAS linearization point it provides β; the token's stored
    trade (β @==> Φ) supplies the caller-selected postcondition. *)
fn rec faa_loop (c:counter) (delta:U32.t)
    (#is : inames)
    (#phi : U32.t -> U32.t -> slprop)
    (tok : au_token is U32.t U32.t
      (fun n -> ctr_val c.cg n)
      (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
      phi)
    (_u:unit)
  requires is_ctr c ** au_available tok
  returns old : U32.t
  ensures is_ctr c ** (exists* n. phi n old)
{
  // Step 1: Read current value (single atomic_read)
  let old_n = read_ctr c;
  // Step 2: AU open — get ctr_val(n)
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;
  // Step 3: CAS (single atomic CAS inside invariant)
  let b = try_add c old_n delta;
  if b {
    elim_cond_true _ _;
    // Step 4: CAS succeeded — this is the linearization point!
    // Provide β(n, old_n) to au_commit. The stored trade β @==> Φ
    // (created by the caller) transforms it into Φ(n, old_n).
    fold (ctr_val c.cg (U32.add_mod (reveal n) delta));
    later_credit_buy 1;
    au_commit tok (reveal n) old_n;
    // Now we have: phi (reveal n) old_n
    old_n
  } else {
    elim_cond_false _ _;
    // Step 5: CAS failed — abort and retry
    fold (ctr_val c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    faa_loop c delta tok ()
  }
}

(** Type witness: faa_loop IS a lat.
    This proves the CAS loop satisfies the logically atomic triple type,
    which structurally enforces universal Φ. *)
let faa_is_lat (c:counter) (delta:U32.t) (#is:inames)
  : lat is U32.t U32.t
    (fun n -> ctr_val c.cg n)
    (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    (is_ctr c)
  = faa_loop c delta

(* ================================================================ *)
(* Client 1: sequential owner (creates AU with identity trade)      *)
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

(** Sequential client: owns ctr_val directly, uses identity trade (β = Φ).
    This is the "easy" API — not the interesting concurrent use case. *)
fn fetch_and_add_seq (c:counter) (delta:U32.t)
  requires is_ctr c ** ctr_val c.cg 'n
  returns old : U32.t
  ensures is_ctr c ** (exists* n. ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
{
  mk_faa_trade c delta #'n;
  let tok = au_intro #emp_inames #U32.t #U32.t
    #(fun n -> ctr_val c.cg n)
    #(fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    #(fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    'n;
  faa_loop c delta #emp_inames tok ()
}

(* ================================================================ *)
(* Client 2: non-trivial Φ — demonstrates universal quantification *)
(* ================================================================ *)

(** Composed client: one non-identity Φ instantiation.
    β = ctr_val(n+delta) ** pure(old==n)  (the counter update)
    Φ = pure(old==n)                      (just the return-value fact)
    The trade drops ctr_val and keeps only the pure receipt, illustrating
    that faa_loop is not limited to the sequential identity postcondition. *)
fn composed_faa (c:counter) (delta:U32.t)
  requires is_ctr c ** ctr_val c.cg 'n
  returns old : U32.t
  ensures is_ctr c ** (exists* m. pure (old == m))
{
  intro_forall #U32.t
    #(fun (old:U32.t) ->
      (later_credit 1 ** ctr_val c.cg (U32.add_mod (reveal 'n) delta) ** pure (old == reveal 'n)) @==>
      pure (old == reveal 'n))
    emp
    fn (old:U32.t) {
      intro_trade
        (later_credit 1 ** ctr_val c.cg (U32.add_mod (reveal 'n) delta) ** pure (old == reveal 'n))
        (pure (old == reveal 'n))
        emp fn _ {
          drop_ (later_credit 1);
          drop_ (ctr_val c.cg (U32.add_mod (reveal 'n) delta))
        }
    };
  let tok = au_intro #emp_inames #U32.t #U32.t
    #(fun n -> ctr_val c.cg n)
    #(fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    #(fun n old -> pure (old == n))
    'n;
  let old = faa_loop c delta #emp_inames tok ();
  with m. assert (pure (old == m));
  old
}

(* ================================================================ *)
(* Client 3: simple sequential demo                                 *)
(* ================================================================ *)

fn simple_client ()
  requires emp
  ensures emp
{
  let c = new_counter ();
  let old1 = fetch_and_add_seq c 3ul;
  with n1. assert (ctr_val c.cg (U32.add_mod n1 3ul) ** pure (old1 == n1));
  let old2 = fetch_and_add_seq c 5ul;
  with n2. assert (ctr_val c.cg (U32.add_mod n2 5ul) ** pure (old2 == n2));
  drop_ (is_ctr c);
  drop_ (ctr_val c.cg (U32.add_mod n2 5ul))
}
