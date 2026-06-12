(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Nested logically-atomic triples — FAA implemented as a *black-box*
    call to an inner CAS LAT.

    Both the inner (CAS) and the outer (FAA) operations are logically —
    not physically — atomic.  Each is built from a CAS-retry loop, each
    has its own LAT spec, and the outer's body never touches the box
    directly: it only calls the inner LAT.  On a successful inner CAS
    step the inner LAT commits its AU, which fires a captured trade
    that commits the outer LAT's AU at the same physical step.

    Outer.LP coincides with inner.LP.

    No new primitives are introduced — only the existing kernel
    [cas_box]/[read_atomic_box] are used, indirectly, via the inner LAT.

    Adapted from a previously-pruned [PulseTutorial.NestedLP] which had
    used a non-faithful LL/SC kernel.  Here the bottom layer is the
    faithful single-step [cas_box]. *)
module PulseTutorial.NestedAU
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.Primitives
open Pulse.Lib.Trade
open Pulse.Lib.Forall
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module AP = Pulse.Lib.Primitives
open Pulse.Lib.Inv

(* ================================================================ *)
(* Counter state — same shape as PulseTutorial.FAAviaCAS            *)
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

(* ================================================================ *)
(* AP.cond helpers — same as FAAviaCAS                              *)
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

(* ================================================================ *)
(* Read the box (used by faa to pick an expected value)             *)
(* ================================================================ *)

fn read_ctr (c:counter)
  requires is_ctr c
  returns v : U32.t
  ensures is_ctr c
{
  unfold is_ctr;
  let v = with_invariants U32.t emp_inames c.ci (ctr_inv c)
    emp (fun _ -> emp)
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    let v = read_atomic_box c.loc;
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    v
  };
  fold (is_ctr c);
  v
}

(* ================================================================ *)
(* Single-CAS attempt: swap the box from [expected] to [new_val].   *)
(* Same shape as [try_add] in FAAviaCAS but with a fixed new_val.   *)
(* ================================================================ *)

fn try_cas (c:counter) (expected new_val : U32.t) (#n : erased U32.t)
  requires is_ctr c ** GR.pts_to c.cg.gr #0.5R n
  returns b : bool
  ensures AP.cond b
    (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val **
     pure (reveal n == expected))
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
    // The single physical CAS step.  This is the LP for the inner LAT
    // (and, on a successful trade-fire, for the outer LAT too).
    let b = cas_box c.loc expected new_val;
    if b {
      elim_cond_true _ _;
      with n0. assert (B.pts_to c.loc new_val **
        GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
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
    intro_cond_true
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val **
       pure (reveal n == expected))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    true
  } else {
    elim_cond_false _ _;
    fold (is_ctr c);
    intro_cond_false
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val **
       pure (reveal n == expected))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    false
  }
}

(* ================================================================ *)
(* INNER LAT — cas_loop                                             *)
(*                                                                  *)
(*   <<< ∀∀ n, ctr_val γ n >>>                                      *)
(*     cas_loop c expected new_val @ is                             *)
(*   <<< ctr_val γ new_val ** pure(n == expected) | RET () >>>      *)
(*                                                                  *)
(* This LAT only commits on a successful CAS at value [expected].   *)
(* On any retry (read mismatch or losing the CAS race) it [au_abort]s *)
(* and loops.  Internal livelock if the value is never [expected]; *)
(* the LAT spec is purely partial.                                  *)
(* ================================================================ *)

fn rec cas_loop (c:counter) (expected new_val : U32.t)
    (#is : inames)
    (phi : unit -> slprop)
    (tok : au_token is U32.t unit
      (fun n -> ctr_val c.cg n)
      (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
      (fun _ y -> phi y))
    (_u:unit)
  requires is_ctr c ** au_available tok
  returns _r : unit
  ensures is_ctr c ** phi _r
{
  // Cheap read to pick the CAS guess; carries no abstract claim.
  let cur = read_ctr c;
  // Open the AU regardless — we will au_commit on success or
  // au_abort on failure.
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;
  if (cur = expected) {
    let b = try_cas c expected new_val;
    if b {
      elim_cond_true _ _;
      // SUCCESS: ctr_val c.cg new_val ** pure(reveal n == expected).
      // This is the inner LAT's LP.
      fold (ctr_val c.cg new_val);
      later_credit_buy 1;
      au_commit tok (reveal n) ();
      ()
    } else {
      elim_cond_false _ _;
      // CAS lost the race — abort and retry from scratch.
      fold (ctr_val c.cg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      cas_loop c expected new_val phi tok ()
    }
  } else {
    // Read said value ≠ expected; nothing to CAS — abort and retry.
    fold (ctr_val c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    cas_loop c expected new_val phi tok ()
  }
}

(** Inner LAT type witness. *)
let cas_is_lat (c:counter) (expected new_val : U32.t) (#is:inames)
  : lat is U32.t unit
    (fun n -> ctr_val c.cg n)
    (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
    (is_ctr c)
  = cas_loop c expected new_val

(* ================================================================ *)
(* OUTER LAT — fetch-and-add, implemented by calling cas_loop       *)
(* as a black-box LAT.                                              *)
(*                                                                  *)
(*   <<< ∀∀ n, ctr_val γ n >>>                                      *)
(*     faa_via_cas c delta @ is                                     *)
(*   <<< ctr_val γ (n + delta) ** pure(old == n) | RET old >>>      *)
(*                                                                  *)
(* The body never touches the box directly.  It opens its outer AU, *)
(* constructs an inner trade family that captures au_opened_outer + *)
(* commits the outer AU when the inner LAT's β fires, then au_intros *)
(* an inner AU and forwards to cas_loop as a black-box LAT call.    *)
(*                                                                  *)
(* When cas_loop hits its LP (a successful CAS), it au_commits the  *)
(* inner AU; the captured trade fires and au_commits the outer AU. *)
(* Outer.LP = inner.LP = the physical CAS step.                     *)
(* ================================================================ *)

fn rec faa_via_cas (c:counter) (delta:U32.t)
    (#is : inames)
    (phi : U32.t -> slprop)
    (tok : au_token is U32.t U32.t
      (fun n -> ctr_val c.cg n)
      (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
      (fun _ old -> phi old))
    (_u:unit)
  requires is_ctr c ** au_available tok
  returns old : U32.t
  ensures is_ctr c ** phi old
{
  // Cheap read to pick the CAS witness we will offer to the inner LAT.
  let old_n = read_ctr c;
  // Open the outer FAA AU.  Now we hold ctr_val c.cg (reveal n) and
  // au_opened tok (reveal n).
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;

  // Build the inner trade family.  The inner LAT we will call has:
  //
  //   inner.a       = U32.t
  //   inner.b       = unit
  //   inner.α m     = ctr_val c.cg m
  //   inner.β m _   = ctr_val c.cg (U32.add_mod old_n delta)
  //                ** pure (m == old_n)
  //
  // We fix the inner AU's witness to x_in = reveal n via au_intro.
  // So β instantiated at this fixed witness becomes:
  //   β (reveal n) _ = ctr_val c.cg (U32.add_mod old_n delta)
  //                 ** pure (reveal n == old_n)
  //
  // The trade family au_intro asks for is:
  //   forall* (y:unit).
  //     trade (later_credit 1 ** β (reveal n) y)
  //           ((fun _x y -> phi old_n) (reveal n) y)
  //   = forall* (y:unit).
  //     trade (later_credit 1
  //           ** ctr_val c.cg (U32.add_mod old_n delta)
  //           ** pure (reveal n == old_n))
  //           (phi old_n)
  //
  // The trade's "extra" captures au_opened tok (reveal n).
  intro_forall #unit
    #(fun (_y:unit) ->
        trade #is
          (later_credit 1
           ** ctr_val c.cg (U32.add_mod old_n delta)
           ** pure (reveal n == old_n))
          (phi old_n))
    (au_opened tok (reveal n))
    fn _y {
      intro_trade #is
        (later_credit 1
         ** ctr_val c.cg (U32.add_mod old_n delta)
         ** pure (reveal n == old_n))
        (phi old_n)
        (au_opened tok (reveal n))
        fn _ {
          // Inside the trade body we now hold:
          //   later_credit 1
          //   ctr_val c.cg (U32.add_mod old_n delta)
          //   pure (reveal n == old_n)
          //   au_opened tok (reveal n)
          //
          // We need to commit the outer AU at witness (reveal n)
          // and return value old_n.  Outer.β (reveal n) old_n =
          //   ctr_val c.cg (U32.add_mod (reveal n) delta)
          //   ** pure (old_n == reveal n)
          //
          // Use the pure equality to rewrite the ctr_val.
          rewrite (ctr_val c.cg (U32.add_mod old_n delta))
               as (ctr_val c.cg (U32.add_mod (reveal n) delta));
          au_commit tok (reveal n) old_n;
          ()
        }
    };

  // Re-fold the outer α we got from au_open back into ctr_val shape so
  // au_intro can consume it for the inner AU.
  fold (ctr_val c.cg (reveal n));
  let inner_tok = au_intro
    #is #U32.t #unit
    #(fun m -> ctr_val c.cg m)
    #(fun m _ -> ctr_val c.cg (U32.add_mod old_n delta) ** pure (m == old_n))
    #(fun _x y -> phi old_n)
    (hide (reveal n));

  // Forward to the inner LAT as a black box.  When cas_loop hits a
  // successful CAS, it au_commits inner_tok; that fires our captured
  // trade, which au_commits tok (the outer AU) and yields phi old_n.
  cas_loop c old_n (U32.add_mod old_n delta) (fun _ -> phi old_n) inner_tok ();
  old_n
}

(** Outer LAT type witness. *)
let faa_is_lat (c:counter) (delta:U32.t) (#is:inames)
  : lat is U32.t U32.t
    (fun n -> ctr_val c.cg n)
    (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    (is_ctr c)
  = faa_via_cas c delta
