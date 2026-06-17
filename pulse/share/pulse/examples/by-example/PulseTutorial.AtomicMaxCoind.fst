(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Migration of PulseTutorial.AtomicMax to coinductive AU.

    Demonstrates the same pattern as PulseTutorial.NestedAUCoind, but
    for a multi-LP outer LAT: each iteration may commit at one of two
    locations (CAS-success when guess<v, or read when guess>=v).
    Both LPs sit inside the same with_invariants_a window and call
    au_commit; the abort path drops the abort trade and retries. *)
module PulseTutorial.AtomicMaxCoind
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.CoinductiveAU
open Pulse.Lib.Primitives
open Pulse.Lib.Trade
open Pulse.Lib.Forall
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module AP = Pulse.Lib.Primitives
open Pulse.Lib.Inv

let u32_max (a b : U32.t) : U32.t = if U32.lt a b then b else a

ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q ensures q
{ unfold AP.cond }

(* ============ Counter (same as AtomicMax) ============ *)

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
    let v = AP.read_atomic_box c.loc;
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    v
  };
  fold (is_ctr c);
  v
}

(* ============ atomic_max — coinductive AU version ============ *)

fn rec atomic_max_c (c:counter) (v:U32.t)
    (#is : inames { not (mem_inv is c.ci) })
    (phi : U32.t -> slprop)
    (_u : unit)
  requires
    is_ctr c **
    atomic_update is
      (fun n -> ctr_val c.cg n)
      (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
      (fun _ result -> phi result)
  returns result : U32.t
  ensures is_ctr c ** phi result
{
  let guess = read_ctr c;
  unfold is_ctr;
  later_credit_buy 1;
  let attempt = with_invariants_a (option U32.t) is c.ci (ctr_inv c)
    (atomic_update is
       (fun n -> ctr_val c.cg n)
       (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
       (fun _ result -> phi result))
    (fun r -> match r with
      | Some result -> phi result
      | None -> atomic_update is
                  (fun n -> ctr_val c.cg n)
                  (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
                  (fun _ result -> phi result))
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    with n0. assert (B.pts_to c.loc n0 ** GR.pts_to c.cg.gr #0.5R n0);
    let x = au_open is
              (fun n -> ctr_val c.cg n)
              (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
              (fun _ result -> phi result);
    unfold (ctr_val c.cg (reveal x));
    GR.pts_to_injective_eq c.cg.gr;
    rewrite each n0 as (reveal x);
    if U32.lt guess v {
      // LP A: try a CAS guess->v.
      let b = AP.cas_box c.loc guess v;
      if b {
        elim_cond_true _ _;
        GR.gather c.cg.gr;
        GR.(c.cg.gr := v);
        GR.share c.cg.gr;
        // beta x v needs ctr_val c.cg (u32_max x v) ** pure(v == u32_max x v).
        // CAS succeeded => x == guess < v => u32_max x v == v.
        fold (ctr_val c.cg v);
        rewrite (ctr_val c.cg v) as (ctr_val c.cg (u32_max (reveal x) v));
        au_commit is
          (fun n -> ctr_val c.cg n)
          (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
          (fun _ result -> phi result)
          (reveal x) v;
        drop_ (trade #is (ctr_val c.cg (reveal x))
                 (atomic_update is
                    (fun n -> ctr_val c.cg n)
                    (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
                    (fun _ result -> phi result)));
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        Some v
      } else {
        elim_cond_false _ _;
        fold (ctr_val c.cg (reveal x));
        au_abort is
          (fun n -> ctr_val c.cg n)
          (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
          (fun _ result -> phi result)
          (reveal x);
        drop_ (forall* (y' : U32.t). trade #is
                 (ctr_val c.cg (u32_max (reveal x) v) ** pure (y' == u32_max (reveal x) v))
                 (phi y'));
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        None #U32.t
      }
    } else {
      // LP B: read-only commit when guess >= v.  Already-true: x reflects current.
      // Need beta x x' for some x' = u32_max x v.  Since guess >= v, we OPT to commit
      // at x (the current state) iff x >= v.  We don't know x's value; we only know
      // n0 == x and we observed n0 == box value via inv.  Re-read box for safety.
      let observed = AP.read_atomic_box c.loc;
      // Box read after CAS-not-attempted: observed == reveal x.
      assert (pure (observed == reveal x));
      if U32.lt observed v {
        // Witness changed since cheap read; abort.
        fold (ctr_val c.cg (reveal x));
        au_abort is
          (fun n -> ctr_val c.cg n)
          (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
          (fun _ result -> phi result)
          (reveal x);
        drop_ (forall* (y' : U32.t). trade #is
                 (ctr_val c.cg (u32_max (reveal x) v) ** pure (y' == u32_max (reveal x) v))
                 (phi y'));
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        None #U32.t
      } else {
        // observed >= v, so u32_max x v == x == observed.  Commit at observed.
        fold (ctr_val c.cg (reveal x));
        rewrite (ctr_val c.cg (reveal x)) as (ctr_val c.cg (u32_max (reveal x) v));
        au_commit is
          (fun n -> ctr_val c.cg n)
          (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
          (fun _ result -> phi result)
          (reveal x) observed;
        drop_ (trade #is (ctr_val c.cg (reveal x))
                 (atomic_update is
                    (fun n -> ctr_val c.cg n)
                    (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
                    (fun _ result -> phi result)));
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        Some observed
      }
    }
  };
  fold (is_ctr c);
  match attempt {
    Some result -> { result }
    None -> { atomic_max_c c v phi () }
  }
}
