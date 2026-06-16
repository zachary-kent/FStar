(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Nested logically-atomic triples with bracketed AU steps.

    Both the inner (CAS) and the outer (FAA) operations are logically —
    not physically — atomic.  Each has its own LAT spec and each retry
    loop uses [au_atomic_step] to open its AU only around one LP attempt:
    success commits immediately, while a failed attempt aborts and retries
    with a fresh AU witness.

    The inner LAT exposes a CAS-from-[expected]-to-[new_val] spec.  The
    outer FAA LAT uses the same faithful [cas_box] LP shape to update the
    counter from [n] to [n + delta] and return [n], so both examples show
    the bracketed pattern at distinct LAT levels without exposing raw
    [au_open]/[au_commit]/[au_abort] in user-facing code.

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
(* Each loop iteration brackets one LP attempt with [au_atomic_step]:*)
(* success commits, while a mismatch or lost CAS returns [None] and  *)
(* retries with a fresh AU witness. Internal livelock is possible if *)
(* the value is never [expected]; the LAT spec is purely partial.    *)
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
  // Cheap read to choose whether this iteration will try the CAS.
  let cur = read_ctr c;
  later_credit_buy 3;
  let attempt = au_atomic_step
    #is #(add_inv emp_inames c.ci) #U32.t #unit
    #(fun n -> ctr_val c.cg n)
    #(fun n _ -> ctr_val c.cg new_val ** pure (n == expected))
    #(fun _ y -> phi y)
    #(is_ctr c)
    #(fun _ -> is_ctr c)
    tok
    fn n {
      unfold ctr_val;
      if (cur = expected) {
        unfold is_ctr;
        let b = with_invariants_a bool emp_inames c.ci (ctr_inv c)
          (GR.pts_to c.cg.gr #0.5R n)
          (fun b -> AP.cond b
            (GR.pts_to c.cg.gr #0.5R new_val ** pure (reveal n == expected))
            (GR.pts_to c.cg.gr #0.5R n))
        fn _ {
          unfold ctr_inv; unfold ctr_inv_inner;
          // LP: successful CAS inside au_atomic_step changes [expected] to [new_val].
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
        fold (is_ctr c);
        if b {
          elim_cond_true _ _;
          fold (ctr_val c.cg new_val);
          Some ()
        } else {
          elim_cond_false _ _;
          fold (ctr_val c.cg n);
          None #unit
        }
      } else {
        // No LP this iteration: consume the step credit with an invariant read,
        // then abort the bracket by returning [None].
        unfold is_ctr;
        let _observed = with_invariants_a U32.t emp_inames c.ci (ctr_inv c)
          (GR.pts_to c.cg.gr #0.5R n)
          (fun _ -> GR.pts_to c.cg.gr #0.5R n)
        fn _ {
          unfold ctr_inv; unfold ctr_inv_inner;
          let observed = read_atomic_box c.loc;
          fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
          observed
        };
        fold (is_ctr c);
        fold (ctr_val c.cg n);
        None #unit
      }
    };
  match attempt {
    Some r -> {
      with _x. assert (phi r ** is_ctr c);
      rewrite each r as ();
      ()
    }
    None -> { cas_loop c expected new_val phi tok () }
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
(* OUTER LAT — fetch-and-add via a bracketed FAA CAS attempt.       *)
(*                                                                  *)
(*   <<< ∀∀ n, ctr_val γ n >>>                                      *)
(*     faa_via_cas c delta @ is                                     *)
(*   <<< ctr_val γ (n + delta) ** pure(old == n) | RET old >>>      *)
(*                                                                  *)
(* The outer operation is also written in the bracketed style: each  *)
(* iteration samples a candidate value, then [au_atomic_step] opens  *)
(* the outer AU only around the successful-CAS LP attempt. CAS loss  *)
(* returns [None] and retries with a fresh outer AU witness.         *)
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
  // Cheap read to pick the CAS witness for this outer FAA iteration.
  let old_n = read_ctr c;
  let new_n = U32.add_mod old_n delta;
  later_credit_buy 3;
  let attempt = au_atomic_step
    #is #(add_inv emp_inames c.ci) #U32.t #U32.t
    #(fun n -> ctr_val c.cg n)
    #(fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    #(fun _ old -> phi old)
    #(is_ctr c)
    #(fun _ -> is_ctr c)
    tok
    fn n {
      unfold ctr_val;
      unfold is_ctr;
      let b = with_invariants_a bool emp_inames c.ci (ctr_inv c)
        (GR.pts_to c.cg.gr #0.5R n)
        (fun b -> AP.cond b
          (GR.pts_to c.cg.gr #0.5R new_n ** pure (reveal n == old_n))
          (GR.pts_to c.cg.gr #0.5R n))
      fn _ {
        unfold ctr_inv; unfold ctr_inv_inner;
        // LP: successful CAS inside au_atomic_step implements the FAA update.
        let b = cas_box c.loc old_n new_n;
        if b {
          elim_cond_true _ _;
          with n0. assert (B.pts_to c.loc new_n **
            GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
          GR.pts_to_injective_eq c.cg.gr;
          rewrite each n0 as (reveal n);
          GR.gather c.cg.gr;
          GR.(c.cg.gr := new_n);
          GR.share c.cg.gr;
          fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
          fold (AP.cond true
            (GR.pts_to c.cg.gr #0.5R new_n ** pure (reveal n == old_n))
            (GR.pts_to c.cg.gr #0.5R n));
          true
        } else {
          elim_cond_false _ _;
          fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
          fold (AP.cond false
            (GR.pts_to c.cg.gr #0.5R new_n ** pure (reveal n == old_n))
            (GR.pts_to c.cg.gr #0.5R n));
          false
        }
      };
      fold (is_ctr c);
      if b {
        elim_cond_true _ _;
        fold (ctr_val c.cg new_n);
        rewrite (ctr_val c.cg new_n) as (ctr_val c.cg (U32.add_mod (reveal n) delta));
        Some old_n
      } else {
        elim_cond_false _ _;
        fold (ctr_val c.cg n);
        None #U32.t
      }
    };
  match attempt {
    Some old -> {
      with _x. assert (phi old ** is_ctr c);
      old
    }
    None -> { faa_via_cas c delta phi tok () }
  }
}

(** Outer LAT type witness. *)
let faa_is_lat (c:counter) (delta:U32.t) (#is:inames)
  : lat is U32.t U32.t
    (fun n -> ctr_val c.cg n)
    (fun n old -> ctr_val c.cg (U32.add_mod n delta) ** pure (old == n))
    (is_ctr c)
  = faa_via_cas c delta
