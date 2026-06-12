(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Nested logically-atomic linearization points via LL/SC.

    Two-level LP composition.  Both [cas_via_llsc] and [faa_via_cas_llsc]
    are logically (not physically) atomic.  Each is a retry loop built
    from LL (load-linked) followed by SC (store-conditional).  At a
    single successful SC step:

      Level 1 — the inner [cas_via_llsc] LAT linearizes there.
      Level 2 — the outer [faa_via_cas_llsc] LAT linearizes there too.

    Outer.LP coincides with inner.LP coincides with the SC step.

    Provenance.  This file is the surviving form of the previously-pruned
    [PulseTutorial.NestedLP], which had injected [ll]/[sc] into the
    trusted kernel [Pulse.Lib.AtomicPrimitives].  That injection was
    rejected as non-faithful, because the simplified [sc] model below
    (SC succeeds iff value unchanged) is operationally identical to
    [cas_box] and elides real LL/SC quirks (spurious failure, monitor
    invalidation, ABA windows, etc.).  In this file the [ll]/[sc]
    declarations are SCOPED LOCALLY at the top of the example.  They
    are unsafe-by-the-same-standard, but their use stays inside this
    module and does not contaminate the kernel. *)
module PulseTutorial.NestedLP
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
(* LOCAL LL/SC — scoped to this example                             *)
(*                                                                  *)
(* Simplified model:                                                *)
(*   ll r        : read the current value, returning it as a pure  *)
(*                 witness.  Models ARM LDXR / RISC-V LR / MIPS LL. *)
(*   sc r v exp  : conditionally write v if the current value is   *)
(*                 still exp; bool result.  Models ARM STXR /      *)
(*                 RISC-V SC / MIPS SC.                            *)
(*                                                                  *)
(* The implementations bottom out in the trusted [read_atomic_box]  *)
(* and [cas_box] primitives from [Pulse.Lib.Primitives], so they   *)
(* introduce NO new axioms.  But the SPEC of [sc] elides           *)
(* spurious-failure / monitor-invalidation behaviour of real LL/SC, *)
(* so this remains a SIMPLIFIED, non-faithful façade — fine for    *)
(* demonstrating nested LPs in this single example file but not    *)
(* something that belongs in the trusted kernel.                   *)
(* ================================================================ *)

atomic fn ll (r : B.box U32.t) (#v : erased U32.t) (#p : perm)
  preserves r |-> Frac p v
  returns x : U32.t
  ensures pure (x == reveal v)
{
  let x = AP.read_atomic_box r;
  x
}

atomic fn sc (r : B.box U32.t) (new_val expected : U32.t) (#cur : erased U32.t)
  requires r |-> cur
  returns b : bool
  ensures AP.cond b (r |-> new_val ** pure (reveal cur == expected))
                    (r |-> cur)
{
  let b = AP.cas_box r expected new_val;
  b
}

(* ================================================================ *)
(* AP.cond helpers                                                  *)
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
(* Counter state — same shape as FAAviaCAS / NestedAU              *)
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
    let n = AP.read_atomic_box c.loc;
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    n
  };
  fold (is_ctr c);
  n
}

(* ================================================================ *)
(* try_sc: a single SC step inside the invariant                    *)
(*                                                                  *)
(* This is the INNERMOST atomic step — the bottom of the LP chain. *)
(* ================================================================ *)

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
    // The single SC step — this is the LP.
    let b = sc c.loc new_val expected;
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
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    true
  } else {
    elim_cond_false _ _;
    fold (is_ctr c);
    intro_cond_false
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
      (is_ctr c ** GR.pts_to c.cg.gr #0.5R n);
    false
  }
}

(* ================================================================ *)
(* Level 1: cas_via_llsc — CAS as a LL+SC retry loop                *)
(*                                                                  *)
(*   <<< ∀∀ n, ctr_val γ n >>>                                      *)
(*     cas_via_llsc c expected new_val @ is                         *)
(*   <<< ctr_val γ (if n = expected then new_val else n)            *)
(*       | RET () >>>                                               *)
(*                                                                  *)
(* LP at the successful SC.  Loops (livelocks) until the counter   *)
(* observes value [expected].                                       *)
(* ================================================================ *)

fn rec cas_via_llsc (c:counter) (expected new_val : U32.t)
    (#is : inames)
    (phi : unit -> slprop)
    (tok : au_token is U32.t unit
      (fun n -> ctr_val c.cg n)
      (fun n _ -> ctr_val c.cg (if n = expected then new_val else n))
      (fun _ y -> phi y))
    (_u:unit)
  requires is_ctr c ** au_available tok
  returns _r : unit
  ensures is_ctr c ** phi _r
{
  // LL: read current value (single atomic load inside invariant).
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
  // Open AU; on retry we abort.
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;
  if (cur = expected) {
    let b = try_sc c expected new_val;
    if b {
      elim_cond_true _ _;
      // SC succeeded — this is the LP.  reveal n == expected, so
      //   ctr_val new_val = ctr_val (if reveal n = expected then new_val else reveal n).
      fold (ctr_val c.cg new_val);
      rewrite (ctr_val c.cg new_val)
           as (ctr_val c.cg (if (reveal n) = expected then new_val else (reveal n)));
      later_credit_buy 1;
      au_commit tok (reveal n) ();
      ()
    } else {
      elim_cond_false _ _;
      fold (ctr_val c.cg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      cas_via_llsc c expected new_val phi tok ()
    }
  } else {
    fold (ctr_val c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    cas_via_llsc c expected new_val phi tok ()
  }
}

(** Level-1 LAT type witness. *)
let cas_is_lat (c:counter) (expected new_val : U32.t) (#is:inames)
  : lat is U32.t unit
    (fun n -> ctr_val c.cg n)
    (fun n _ -> ctr_val c.cg (if n = expected then new_val else n))
    (is_ctr c)
  = cas_via_llsc c expected new_val

(* ================================================================ *)
(* Level 2: faa_via_cas_llsc — FAA built directly on LL/SC          *)
(*                                                                  *)
(*   <<< ∀∀ n, ctr_val γ n >>>                                      *)
(*     faa_via_cas_llsc c delta @ is                                *)
(*   <<< ctr_val γ (n + delta) ** pure (old == n) | RET old >>>     *)
(*                                                                  *)
(* The body inlines the LL+SC sequence rather than calling          *)
(* [cas_via_llsc].  This makes the nested-LP structure visible in   *)
(* a single function: the SC step is simultaneously the inner LP    *)
(* (if you read the body as a CAS-via-LL/SC) and the outer LP (the *)
(* FAA's logical step).                                             *)
(*                                                                  *)
(* For a BLACK-BOX LAT-calling-LAT version of this composition see  *)
(* [PulseTutorial.NestedAU] (faa_via_cas calls cas_loop as a LAT). *)
(* ================================================================ *)

fn rec faa_via_cas_llsc (c:counter) (delta:U32.t)
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
  // Snapshot the current value to use as the SC's expected.
  let old_n = read_ctr c;
  // Open outer FAA AU.
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;

  // LL: re-read the value inside the invariant.
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
    let b = try_sc c old_n (U32.add_mod old_n delta);
    if b {
      elim_cond_true _ _;
      // SC succeeded — this is the NESTED LP.  At this single
      // physical step BOTH the inner CAS-via-LL/SC view and the
      // outer FAA view linearize.  From the try_sc post we have
      // reveal n == old_n, hence:
      //   ctr_val (add old_n delta) = ctr_val (add (reveal n) delta).
      fold (ctr_val c.cg (U32.add_mod (reveal n) delta));
      later_credit_buy 1;
      au_commit tok (reveal n) old_n;
      old_n
    } else {
      elim_cond_false _ _;
      fold (ctr_val c.cg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      faa_via_cas_llsc c delta phi tok ()
    }
  } else {
    fold (ctr_val c.cg n);
    later_credit_buy 1;
    au_abort tok (reveal n);
    faa_via_cas_llsc c delta phi tok ()
  }
}

(** Level-2 LAT type witness. *)
let faa_nested_is_lat (c:counter) (delta:U32.t) (#is:inames)
  : lat is U32.t U32.t
    (fun n -> ctr_val c.cg n)
    (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    (is_ctr c)
  = faa_via_cas_llsc c delta

(* ================================================================ *)
(* Sequential client wrapper                                        *)
(* ================================================================ *)

(** Build the identity trade family used by the sequential wrapper.
    Each instance is β @==> β, which just drops the [later_credit]. *)
ghost
fn mk_faa_trade (c:counter) (delta:U32.t) (#n : erased U32.t)
  requires emp
  ensures (forall* (old:U32.t).
    trade #emp_inames
      (later_credit 1
       ** ctr_val c.cg (U32.add_mod (reveal n) delta)
       ** pure (old == reveal n))
      (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)))
{
  intro_forall #U32.t
    #(fun (old:U32.t) ->
        trade #emp_inames
          (later_credit 1
           ** ctr_val c.cg (U32.add_mod (reveal n) delta)
           ** pure (old == reveal n))
          (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n)))
    emp
    fn old {
      intro_trade #emp_inames
        (later_credit 1
         ** ctr_val c.cg (U32.add_mod (reveal n) delta)
         ** pure (old == reveal n))
        (ctr_val c.cg (U32.add_mod (reveal n) delta) ** pure (old == reveal n))
        emp
        fn _ { drop_ (later_credit 1) }
    }
}

(** Sequential fetch-and-add: construct an AU with Φ = β (identity trade)
    and run the level-2 LAT against it. *)
fn fetch_and_add (c:counter) (delta:U32.t)
  requires is_ctr c ** ctr_val c.cg 'n
  returns old : U32.t
  ensures is_ctr c
       ** ctr_val c.cg (U32.add_mod (reveal 'n) delta)
       ** pure (old == reveal 'n)
{
  mk_faa_trade c delta #'n;
  let tok = au_intro
    #emp_inames #U32.t #U32.t
    #(fun n -> ctr_val c.cg n)
    #(fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    #(fun _x old -> ctr_val c.cg (U32.add_mod (reveal 'n) delta) ** pure (old == reveal 'n))
    'n;
  let old = faa_via_cas_llsc c delta
              (fun old -> ctr_val c.cg (U32.add_mod (reveal 'n) delta)
                       ** pure (old == reveal 'n))
              tok ();
  old
}

fn nested_lp_client ()
  requires emp
  ensures emp
{
  let c = new_counter ();
  let old = fetch_and_add c 5ul;
  drop_ (is_ctr c);
  drop_ (ctr_val c.cg (U32.add_mod 0ul 5ul))
}
