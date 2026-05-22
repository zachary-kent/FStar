(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Fetch-and-Add via CAS loop — logically atomic specification.

    Demonstrates the core LA encoding: a physically non-atomic operation
    (CAS retry loop) with a logically atomic spec. The CAS is the
    linearization point; abort on CAS failure restores the AU for retry.

    This is the canonical LA example: Iris treiber2.v style. *)
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

(** The CAS retry loop, universally quantified over Φ.

    Iris spec:
    <<< ∀∀ n, ctr_val γ n >>>
      fetch_and_add c delta @ ↑N
    <<< ∀∀ Φ, ctr_val γ (n + delta) | RET n >>>

    The loop does NOT mention Φ — it provides β at the linearization
    point and the stored trade (β @==> Φ, supplied by the caller
    when creating the AU) does the rest. This is the key insight:
    the CAS loop is parametric in the client's postcondition. *)
fn rec faa_loop (c:counter) (delta:U32.t)
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

(* ================================================================ *)
(* Client 1: sequential owner (creates AU with identity trade)      *)
(* ================================================================ *)

ghost
fn mk_faa_trade (c:counter) (delta:U32.t) (#n : erased U32.t)
  requires emp
  ensures (forall* (old:U32.t).
    (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)) @==>
    (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)))
{
  intro_forall #U32.t
    #(fun (old:U32.t) ->
      (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)) @==>
      (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)))
    emp
    fn (old:U32.t) {
      intro_trade
        (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n))
        (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n))
        emp fn _ { () }
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
  faa_loop c delta tok ()
}

(* ================================================================ *)
(* Client 2: concurrent client with ctr_val inside an invariant     *)
(* Shows the real power of ∀Φ: client chooses their own Φ.         *)
(* ================================================================ *)

(** A concurrent client that holds ctr_val inside their own invariant,
    alongside a ghost "total" tracking the sum of all increments.
    
    The client creates an AU where Φ updates their ghost total.
    This demonstrates the universally-quantified Φ: the CAS loop
    (faa_loop) never knows about the client's ghost state, but at
    the linearization point the stored trade transforms β into the
    client's custom Φ which updates their ghost total. *)
let client_inv_p (c:counter) (total_gr : GR.ref U32.t) : slprop =
  exists* (n:U32.t). ctr_val c.cg n ** GR.pts_to total_gr n

fn concurrent_client ()
  requires emp
  ensures emp
{
  let c = new_counter ();
  // Client's private ghost state: tracks the counter value
  let total_gr = GR.alloc #U32.t 0ul;
  // Move ctr_val into client invariant
  fold (client_inv_p c total_gr);
  let cli_inv = new_invariant (client_inv_p c total_gr);
  // To call faa_loop, client must:
  // 1. Open their invariant to extract ctr_val (providing α)
  // 2. Create a trade β @==> Φ where Φ updates their ghost total
  // 3. Create the AU and pass it to faa_loop
  // This is left as a proof exercise — the key point is that
  // faa_loop is polymorphic in Φ, so it works for any client.
  drop_ (inv cli_inv (client_inv_p c total_gr));
  drop_ (is_ctr c)
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
