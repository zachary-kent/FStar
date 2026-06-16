(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Multi-LP outer LAT — atomic_max linearizing at one of two distinct
    physical inner LATs.

    [atomic_max c v] replaces the counter c with [max c v] and returns
    the resulting value.  The outer LAT has a CONDITIONAL postcondition
    that depends on the abstract witness n:

      α n          = ctr_val c n
      β n result   = ctr_val c (max n v) ** pure (result == max n v)

    The implementation has TWO physical primitives at TWO distinct LP
    loci, one for each abstract branch:

      - n >= v branch (no state change):
          LP at an internal atomic_read.
          β at LP gives ctr_val c n ** pure (result == n).

      - n < v branch (state change n -> v):
          LP at an internal cas_box.
          β at LP gives ctr_val c v ** pure (result == v).

    Both branches share the same outer α and the same outer β shape
    (modulo the abstract conditional).  Same outer LAT, two LP loci,
    two genuinely-different physical inner primitives.

    Earlier versions opened the outer AU across both a read and a CAS,
    which froze the counter and ruled out CAS failure.  The current
    version uses au_atomic_step for one LP attempt at a time; CAS failure is
    live again and retries recursively with a fresh abstract witness.

    Alongside [PulseTutorial.NestedAU] (FAA via inner CAS LAT, single
    LP at one primitive type) and [PulseTutorial.NestedLP] (LL/SC,
    archived as a faithful-LL/SC limitation demo), this file is the
    multi-LP variant: outer LAT, two LP loci, two inner primitive
    types. *)
module PulseTutorial.AtomicMax
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
(* Pure max on U32                                                  *)
(* ================================================================ *)

let u32_max (a b : U32.t) : U32.t = if U32.lt a b then b else a

(* ================================================================ *)
(* AP.cond helpers                                                  *)
(* ================================================================ *)

ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q ensures q
{ unfold AP.cond }

(* ================================================================ *)
(* Counter state — same as FAAviaCAS / NestedAU                    *)
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
  returns observed : U32.t
  ensures is_ctr c
{
  unfold is_ctr;
  let observed = with_invariants U32.t emp_inames c.ci (ctr_inv c)
    emp (fun _ -> emp)
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    let observed = AP.read_atomic_box c.loc;
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    observed
  };
  fold (is_ctr c);
  observed
}

(* ================================================================ *)
(* atomic_max c v — multi-LP outer LAT                              *)
(*                                                                  *)
(*   <<< ∀∀ n. ctr_val c n >>>                                      *)
(*     atomic_max c v                                               *)
(*   <<< ctr_val c (max n v) ** pure (result == max n v)            *)
(*       | RET result : U32.t >>>                                   *)
(*                                                                  *)
(* Implementation:                                                  *)
(*   Each loop iteration first performs an ordinary read to choose   *)
(*   an LP attempt.  The AU is opened only by au_atomic_step, whose  *)
(*   body performs exactly one physical atomic LP attempt and then   *)
(*   immediately commits (Some) or aborts (None).                   *)
(*      - guess >= v: LP at read inside au_atomic_step.             *)
(*      - guess <  v: LP at successful CAS inside au_atomic_step;   *)
(*                    failed CAS aborts and retries recursively.    *)
(* ================================================================ *)

fn rec atomic_max (c:counter) (v:U32.t)
    (#is : inames)
    (phi : U32.t -> slprop)
    (tok : au_token is U32.t U32.t
      (fun n -> ctr_val c.cg n)
      (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
      (fun _ result -> phi result))
    (_u:unit)
  requires is_ctr c ** au_available tok
  returns result : U32.t
  ensures is_ctr c ** phi result
{
  let guess = read_ctr c;
  later_credit_buy 3;
  let attempt = au_atomic_step
    #is #(add_inv emp_inames c.ci) #U32.t #U32.t
    #(fun n -> ctr_val c.cg n)
    #(fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
    #(fun _ result -> phi result)
    #(is_ctr c)
    #(fun _ -> is_ctr c)
    tok
    fn n {
      unfold ctr_val;
      if U32.lt guess v {
        // LP: successful CAS inside au_atomic_step when the guessed value is below v.
        unfold is_ctr;
        let b = with_invariants_a bool emp_inames c.ci (ctr_inv c)
          (GR.pts_to c.cg.gr #0.5R n)
          (fun b -> AP.cond b
            (GR.pts_to c.cg.gr #0.5R v ** pure (reveal n == guess))
            (GR.pts_to c.cg.gr #0.5R n))
        fn _ {
          unfold ctr_inv; unfold ctr_inv_inner;
          with n0. assert (B.pts_to c.loc n0 **
            GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
          GR.pts_to_injective_eq c.cg.gr;
          rewrite each n0 as (reveal n);
          let b = AP.cas_box c.loc guess v;
          if b {
            elim_cond_true _ _;
            GR.gather c.cg.gr;
            GR.(c.cg.gr := v);
            GR.share c.cg.gr;
            fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
            fold (AP.cond true
              (GR.pts_to c.cg.gr #0.5R v ** pure (reveal n == guess))
              (GR.pts_to c.cg.gr #0.5R n));
            true
          } else {
            elim_cond_false _ _;
            fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
            fold (AP.cond false
              (GR.pts_to c.cg.gr #0.5R v ** pure (reveal n == guess))
              (GR.pts_to c.cg.gr #0.5R n));
            false
          }
        };
        fold (is_ctr c);
        if b {
          elim_cond_true _ _;
          fold (ctr_val c.cg v);
          rewrite (ctr_val c.cg v) as (ctr_val c.cg (u32_max (reveal n) v));
          Some v
        } else {
          elim_cond_false _ _;
          fold (ctr_val c.cg n);
          None #U32.t
        }
      } else {
        // LP: read inside au_atomic_step when the guessed value is at least v.
        unfold is_ctr;
        let observed = with_invariants_a U32.t emp_inames c.ci (ctr_inv c)
          (GR.pts_to c.cg.gr #0.5R n)
          (fun observed -> GR.pts_to c.cg.gr #0.5R n ** pure (observed == reveal n))
        fn _ {
          unfold ctr_inv; unfold ctr_inv_inner;
          with n0. assert (B.pts_to c.loc n0 **
            GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
          GR.pts_to_injective_eq c.cg.gr;
          rewrite each n0 as (reveal n);
          let observed = AP.read_atomic_box c.loc;
          fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
          observed
        };
        fold (is_ctr c);
        if U32.lt observed v {
          fold (ctr_val c.cg n);
          None #U32.t
        } else {
          fold (ctr_val c.cg n);
          rewrite (ctr_val c.cg n) as (ctr_val c.cg (u32_max (reveal n) v));
          Some observed
        }
      }
    };
  match attempt {
    Some result -> {
      with _x. assert (phi result ** is_ctr c);
      result
    }
    None -> {
      atomic_max c v phi tok ()
    }
  }
}

(** Outer LAT type witness. *)
let atomic_max_is_lat (c:counter) (v:U32.t) (#is:inames)
  : lat is U32.t U32.t
    (fun n -> ctr_val c.cg n)
    (fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
    (is_ctr c)
  = atomic_max c v

(* ================================================================ *)
(* Sequential client wrapper                                        *)
(* ================================================================ *)

ghost
fn mk_max_trade (c:counter) (v:U32.t) (#n : erased U32.t)
  requires emp
  ensures (forall* (result:U32.t).
    trade #emp_inames
      (later_credit 1
       ** ctr_val c.cg (u32_max (reveal n) v)
       ** pure (result == u32_max (reveal n) v))
      (ctr_val c.cg (u32_max (reveal n) v) ** pure (result == u32_max (reveal n) v)))
{
  intro_forall #U32.t
    #(fun (result:U32.t) ->
        trade #emp_inames
          (later_credit 1
           ** ctr_val c.cg (u32_max (reveal n) v)
           ** pure (result == u32_max (reveal n) v))
          (ctr_val c.cg (u32_max (reveal n) v) ** pure (result == u32_max (reveal n) v)))
    emp
    fn result {
      intro_trade #emp_inames
        (later_credit 1
         ** ctr_val c.cg (u32_max (reveal n) v)
         ** pure (result == u32_max (reveal n) v))
        (ctr_val c.cg (u32_max (reveal n) v) ** pure (result == u32_max (reveal n) v))
        emp
        fn _ { drop_ (later_credit 1) }
    }
}

fn atomic_max_seq (c:counter) (v:U32.t)
  requires is_ctr c ** ctr_val c.cg 'n
  returns result : U32.t
  ensures is_ctr c
       ** ctr_val c.cg (u32_max (reveal 'n) v)
       ** pure (result == u32_max (reveal 'n) v)
{
  mk_max_trade c v #'n;
  let tok = au_intro
    #emp_inames #U32.t #U32.t
    #(fun n -> ctr_val c.cg n)
    #(fun n result -> ctr_val c.cg (u32_max n v) ** pure (result == u32_max n v))
    #(fun _x result -> ctr_val c.cg (u32_max (reveal 'n) v)
                    ** pure (result == u32_max (reveal 'n) v))
    'n;
  let result = atomic_max c v
    (fun result -> ctr_val c.cg (u32_max (reveal 'n) v)
                ** pure (result == u32_max (reveal 'n) v))
    tok ();
  result
}

fn atomic_max_client ()
  requires emp
  ensures emp
{
  let c = new_counter ();
  // c starts at 0.  atomic_max c 5 should set it to 5.
  let r1 = atomic_max_seq c 5ul;
  // Now at 5.  atomic_max c 3 should leave it at 5 and return 5.
  let r2 = atomic_max_seq c 3ul;
  drop_ (is_ctr c);
  drop_ (ctr_val c.cg (u32_max (u32_max 0ul 5ul) 3ul))
}
