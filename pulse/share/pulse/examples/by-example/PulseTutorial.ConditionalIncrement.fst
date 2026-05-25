(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Conditional Increment — adapted from Iris logatom/conditional_increment.
    
    Flag is persistent (persistent_pts_to, Iris flag ↦□ b) — immutable
    after initialization. Since the flag can't change, no prophecy
    is needed: LP is at the CAS (flag=true) or trivially at the
    flag read (flag=false).
    
    AU spec: <<< cinc_content γ n >>> cinc s flag_val <<< cinc_content γ (if flag_val then n+1 else n) >>>
    The flag_val is read from persistent ownership before opening the AU. *)
module PulseTutorial.ConditionalIncrement
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.PersistentPtsTo
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module AP = Pulse.Lib.AtomicPrimitives
open Pulse.Lib.Inv
open Pulse.Lib.Trade
open Pulse.Lib.Forall

ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q
  ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q
  ensures q
{ unfold AP.cond }

(* ================================================================ *)
(* Counter representation (same as AtomicCounter)                   *)
(* ================================================================ *)

noeq type cinc_ghost = { gr : GR.ref U32.t; }
noeq type cinc_state = {
  counter : B.box U32.t;
  cg      : cinc_ghost;
  ci      : iname;
}

let cinc_content (g:cinc_ghost) (n:U32.t) : slprop = GR.pts_to g.gr #0.5R n

let cinc_inv_inner (counter : B.box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (n:U32.t). B.pts_to counter n ** GR.pts_to gr #0.5R n

let cinc_inv_raw (s:cinc_state) : slprop = cinc_inv_inner s.counter s.cg.gr
let is_cinc (s:cinc_state) : slprop = inv s.ci (cinc_inv_raw s)

fn new_cinc ()
  requires emp
  returns s : cinc_state
  ensures is_cinc s ** cinc_content s.cg 0ul
{
  let counter = B.alloc 0ul;
  let gr = GR.alloc #U32.t 0ul;
  GR.share gr;
  let cg : cinc_ghost = { gr };
  rewrite (GR.pts_to gr #0.5R 0ul) as (GR.pts_to cg.gr #0.5R 0ul);
  rewrite (GR.pts_to gr #0.5R 0ul) as (cinc_content cg 0ul);
  fold (cinc_inv_inner counter cg.gr);
  let ci = new_invariant (cinc_inv_inner counter cg.gr);
  let s : cinc_state = { counter; cg; ci };
  rewrite (inv ci (cinc_inv_inner counter cg.gr)) as (inv s.ci (cinc_inv_raw s));
  fold (is_cinc s);
  rewrite (cinc_content cg 0ul) as (cinc_content s.cg 0ul);
  s
}

(* ================================================================ *)
(* Helper: atomic read of counter                                   *)
(* ================================================================ *)

fn get_counter (s:cinc_state)
  requires is_cinc s
  returns n : U32.t
  ensures is_cinc s
{
  unfold is_cinc;
  let n = with_invariants U32.t emp_inames s.ci (cinc_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold cinc_inv_raw; unfold cinc_inv_inner;
    let n = AP.atomic_read s.counter;
    fold (cinc_inv_inner s.counter s.cg.gr); fold (cinc_inv_raw s);
    n
  };
  fold (is_cinc s);
  n
}

(* ================================================================ *)
(* Helper: try CAS increment (one atomic step inside invariant)     *)
(* ================================================================ *)

fn try_cinc (s:cinc_state) (old_n : U32.t) (#n : erased U32.t)
  requires is_cinc s ** GR.pts_to s.cg.gr #0.5R n
  returns b : bool
  ensures AP.cond b
    (is_cinc s ** GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
    (is_cinc s ** GR.pts_to s.cg.gr #0.5R n)
{
  unfold is_cinc;
  let b = with_invariants bool emp_inames s.ci (cinc_inv_raw s)
    (GR.pts_to s.cg.gr #0.5R n)
    (fun b -> AP.cond b
      (GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
      (GR.pts_to s.cg.gr #0.5R n))
  fn _ {
    unfold cinc_inv_raw; unfold cinc_inv_inner;
    let b = AP.atomic_cas s.counter old_n (U32.add_mod old_n 1ul);
    if b {
      elim_cond_true _ _;
      with n0. assert (B.pts_to s.counter (U32.add_mod old_n 1ul) ** GR.pts_to s.cg.gr #0.5R n0 ** GR.pts_to s.cg.gr #0.5R n);
      GR.pts_to_injective_eq s.cg.gr;
      rewrite each n0 as (reveal n);
      GR.gather s.cg.gr;
      GR.(s.cg.gr := U32.add_mod (reveal n) 1ul);
      GR.share s.cg.gr;
      fold (cinc_inv_inner s.counter s.cg.gr); fold (cinc_inv_raw s);
      fold (AP.cond true
        (GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
        (GR.pts_to s.cg.gr #0.5R n));
      true
    } else {
      elim_cond_false _ _;
      fold (cinc_inv_inner s.counter s.cg.gr); fold (cinc_inv_raw s);
      fold (AP.cond false
        (GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
        (GR.pts_to s.cg.gr #0.5R n));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_cinc s);
    fold (AP.cond true
      (is_cinc s ** GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
      (is_cinc s ** GR.pts_to s.cg.gr #0.5R n));
    true
  } else {
    elim_cond_false _ _;
    fold (is_cinc s);
    fold (AP.cond false
      (is_cinc s ** GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal n) 1ul))
      (is_cinc s ** GR.pts_to s.cg.gr #0.5R n));
    false
  }
}

(* ================================================================ *)
(* cinc — conditional increment with AU/LAT spec                    *)
(* ================================================================ *)

(** cinc_result: computes the counter value after conditional increment *)
let cinc_result (flag_val:bool) (n:U32.t) : U32.t =
  if flag_val then U32.add_mod n 1ul else n

(** cinc_loop: the core CAS-retry loop with AU spec.
    flag_val is the concrete flag value (read from persistent outside).
    Parametric in Φ — structurally prevents spec hacking. *)
fn rec cinc_loop (s:cinc_state) (flag_val:bool)
    (#phi : U32.t -> unit -> slprop)
    (tok : au_token emp_inames U32.t unit
      (fun n -> cinc_content s.cg n)
      (fun n _ -> cinc_content s.cg (cinc_result flag_val n))
      phi)
    (_u:unit)
  requires is_cinc s ** au_available tok
  ensures is_cinc s ** (exists* n. phi n ())
{
  if flag_val {
    // Flag is true: CAS loop to increment (same as AtomicCounter)
    let old_n = get_counter s;
    later_credit_buy 1;
    let n = au_open tok;
    unfold cinc_content;
    let b = try_cinc s old_n;
    if b {
      elim_cond_true _ _;
      fold (cinc_content s.cg (U32.add_mod (reveal n) 1ul));
      rewrite (cinc_content s.cg (U32.add_mod (reveal n) 1ul)) as
              (cinc_content s.cg (cinc_result flag_val (reveal n)));
      later_credit_buy 1;
      au_commit tok (reveal n) ();
    } else {
      elim_cond_false _ _;
      fold (cinc_content s.cg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      cinc_loop s flag_val tok ()
    }
  } else {
    // Flag is false: commit immediately (β = α when flag=false)
    later_credit_buy 1;
    let n = au_open tok;
    // cinc_result false n = n, so β(n,()) = cinc_content g n = α(n)
    later_credit_buy 1;
    au_commit tok (reveal n) ();
  }
}

(** Type witness: cinc_loop IS a lat_void *)
let cinc_is_lat (s:cinc_state) (flag_val:bool)
  : lat_void emp_inames U32.t
    (fun n -> cinc_content s.cg n)
    (fun n _ -> cinc_content s.cg (cinc_result flag_val n))
    (is_cinc s)
  = fun #phi tok _u -> cinc_loop s flag_val #phi tok _u

(* ================================================================ *)
(* Sequential wrapper with persistent flag                          *)
(* ================================================================ *)

ghost
fn mk_cinc_trade (s:cinc_state) (flag_val:bool) (#n : erased U32.t)
  requires emp
  ensures (forall* (y:unit). (later_credit 1 ** cinc_content s.cg (cinc_result flag_val (reveal n))) @==> cinc_content s.cg (cinc_result flag_val (reveal n)))
{
  intro_forall #unit #(fun (y:unit) -> (later_credit 1 ** cinc_content s.cg (cinc_result flag_val (reveal n))) @==> cinc_content s.cg (cinc_result flag_val (reveal n)))
    emp
    fn (y:unit) {
      intro_trade (later_credit 1 ** cinc_content s.cg (cinc_result flag_val (reveal n)))
                  (cinc_content s.cg (cinc_result flag_val (reveal n))) emp
        fn _ { drop_ (later_credit 1) }
    }
}

(** cinc: read persistent flag, then conditionally increment. *)
fn cinc (s:cinc_state) (flag : B.box bool)
  requires is_cinc s ** cinc_content s.cg 'n ** persistent_pts_to flag 'b
  ensures is_cinc s ** persistent_pts_to flag 'b **
          (exists* m. cinc_content s.cg m)
{
  let b = read_persistent flag;
  mk_cinc_trade s b #'n;
  let tok = au_intro #emp_inames #U32.t #unit
    #(fun n -> cinc_content s.cg n)
    #(fun n _ -> cinc_content s.cg (cinc_result b n))
    #(fun n _ -> cinc_content s.cg (cinc_result b n))
    'n;
  cinc_loop s b tok ()
}

(* ================================================================ *)
(* Client example                                                   *)
(* ================================================================ *)

fn cinc_client ()
  requires emp
  ensures emp
{
  let s = new_cinc ();
  let flag = B.alloc true;
  make_persistent flag;
  // Conditional increment with flag=true
  cinc s flag;
  // Cleanup
  drop_ (is_cinc s);
  drop_ (persistent_pts_to flag true);
  with m0. assert (cinc_content s.cg m0);
  drop_ (cinc_content s.cg m0)
}
