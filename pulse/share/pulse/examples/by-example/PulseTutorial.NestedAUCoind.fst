(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Migration of NestedAU's inner LAT (cas_loop) to the coinductive AU.

    Demonstrates that [Pulse.Lib.CoinductiveAU.atomic_update] is a
    drop-in replacement for the [au_token]-based LAT API for a single,
    single-CAS-loop LAT.  Only the inner LAT is migrated here; the
    outer faa_via_cas migration (which uses au_commit_via_lat) is
    deferred to a follow-up.

    Compared to PulseTutorial.NestedAU.cas_loop:
      - [au_token is ...]                  --> [atomic_update is ...]
      - [au_available tok]                 --> just have the AU slprop
      - [au_atomic_step tok fn x { body }] --> with_invariants_a + manual
                                              au_open / au_commit / au_abort
*)
module PulseTutorial.NestedAUCoind
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

(* ============ Counter — copied from NestedAU ============ *)

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

(* ============ Cheap read used for the witness ============ *)

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

(* ============ AP.cond helpers ============ *)

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

(* ============ Inner LAT — coinductive version ============ *)

(** The same inner LAT as PulseTutorial.NestedAU.cas_loop, but with the
    AU expressed as a coinductive [atomic_update] slprop instead of an
    [au_token].  The body opens both the counter inv and the AU inside
    a single atomic CAS step. *)
fn rec cas_loop_c (c:counter) (expected new_val : U32.t)
    (#is : inames { not (mem_inv is c.ci) })
    (phi : unit -> slprop)
    (_u : unit)
  requires
    is_ctr c **
    atomic_update is
      (fun n -> ctr_val c.cg n)
      (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
      (fun _ y -> phi y)
  returns _r : unit
  ensures is_ctr c ** phi _r
{
  // Pre-read picks the iteration's chosen witness.
  let cur = read_ctr c;
  if (cur = expected) {
    // LP attempt: open inv + AU inside one atomic step.
    unfold is_ctr;
    later_credit_buy 1;
    let result = with_invariants_a (option unit) is c.ci (ctr_inv c)
      (atomic_update is
         (fun n -> ctr_val c.cg n)
         (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
         (fun _ y -> phi y))
      (fun r -> match r with
        | Some () -> phi ()
        | None -> atomic_update is
                    (fun n -> ctr_val c.cg n)
                    (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
                    (fun _ y -> phi y))
    fn _ {
      unfold ctr_inv; unfold ctr_inv_inner;
      with n0. assert (B.pts_to c.loc n0 ** GR.pts_to c.cg.gr #0.5R n0);
      // Open the AU.  alpha n = ctr_val c.cg n = GR.pts_to c.cg.gr #0.5R n.
      let x = au_open is
                (fun n -> ctr_val c.cg n)
                (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
                (fun _ y -> phi y);
      // alpha x = ctr_val c.cg x; we hold ctr_val c.cg n0 from inv too.
      unfold (ctr_val c.cg (reveal x));
      GR.pts_to_injective_eq c.cg.gr;
      rewrite each n0 as (reveal x);
      // Physical CAS.
      let b = cas_box c.loc expected new_val;
      if b {
        elim_cond_true _ _;
        // CAS succeeded — beta-witness is (), pure (x == expected) holds.
        GR.gather c.cg.gr;
        GR.(c.cg.gr := new_val);
        GR.share c.cg.gr;
        // Build the beta slprop and commit.
        fold (ctr_val c.cg new_val);
        au_commit is
          (fun n -> ctr_val c.cg n)
          (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
          (fun _ y -> phi y)
          (reveal x) ();
        drop_ (trade #is (ctr_val c.cg (reveal x))
                 (atomic_update is
                    (fun n -> ctr_val c.cg n)
                    (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
                    (fun _ y -> phi y)));
        // Restore inv contents.
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        Some ()
      } else {
        elim_cond_false _ _;
        // CAS failed — abort the AU, restore inv.
        fold (ctr_val c.cg (reveal x));
        au_abort is
          (fun n -> ctr_val c.cg n)
          (fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
          (fun _ y -> phi y)
          (reveal x);
        drop_ (forall* (y' : unit). trade #is
                 (ctr_val c.cg new_val ** pure (reveal x == expected))
                 (phi y'));
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        None #unit
      }
    };
    fold (is_ctr c);
    match result {
      Some r -> { rewrite each r as (); () }
      None -> { cas_loop_c c expected new_val phi () }
    }
  } else {
    // No LP this iteration.
    cas_loop_c c expected new_val phi ()
  }
}
