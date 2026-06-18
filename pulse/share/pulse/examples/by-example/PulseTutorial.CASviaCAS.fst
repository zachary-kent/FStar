(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Nested-LAT motivating example: logically atomic CAS, then FAA via CAS.

    Step 2 starts with [cas_lat], a direct logically atomic wrapper around a
    single physical [cas_box] on a boxed U32 cell paired with a ghost half.
    Step 3 extends this file with an FAA loop that calls [cas_lat] as its
    inner logically atomic operation. *)
module PulseTutorial.CASviaCAS
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.Primitives
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module AP = Pulse.Lib.Primitives
open Pulse.Lib.Inv

(* ================================================================ *)
(* Atomic cell state                                                *)
(* ================================================================ *)

noeq type cell_ghost = { gr : GR.ref U32.t; }
noeq type atomic_cell = {
  loc : B.box U32.t;
  cg  : cell_ghost;
  ci  : iname;
}

let cell_val (g : cell_ghost) (n : U32.t) : slprop = GR.pts_to g.gr #0.5R n

let cell_inv_inner (loc : B.box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (n : U32.t). B.pts_to loc n ** GR.pts_to gr #0.5R n

let cell_inv (c : atomic_cell) : slprop = cell_inv_inner c.loc c.cg.gr
let is_cell (c : atomic_cell) : slprop = inv c.ci (cell_inv c)

fn new_atomic_cell ()
  requires emp
  returns c : atomic_cell
  ensures is_cell c ** cell_val c.cg 0ul
{
  let loc = B.alloc 0ul;
  let gr = GR.alloc #U32.t 0ul;
  GR.share gr;
  let cg : cell_ghost = { gr };
  rewrite (GR.pts_to gr #0.5R 0ul) as (GR.pts_to cg.gr #0.5R 0ul);
  rewrite (GR.pts_to gr #0.5R 0ul) as (cell_val cg 0ul);
  fold (cell_inv_inner loc cg.gr);
  let ci = new_invariant (cell_inv_inner loc cg.gr);
  let c : atomic_cell = { loc; cg; ci };
  rewrite (inv ci (cell_inv_inner loc cg.gr)) as (inv c.ci (cell_inv c));
  fold (is_cell c);
  rewrite (cell_val cg 0ul) as (cell_val c.cg 0ul);
  c
}

(* ================================================================ *)
(* AP.cond helpers for primitive CAS                                *)
(* ================================================================ *)

ghost fn elim_cond_true (p q : slprop)
  requires AP.cond true p q ensures p
{ unfold AP.cond }

ghost fn elim_cond_false (p q : slprop)
  requires AP.cond false p q ensures q
{ unfold AP.cond }

(* ================================================================ *)
(* CAS LAT                                                         *)
(* ================================================================ *)

let cas_beta (c : atomic_cell) (old_n new_n : U32.t) (n : U32.t) (b : bool) : slprop =
  if b then cell_val c.cg new_n ** pure (n == old_n)
       else cell_val c.cg n     ** pure (~ (n == old_n))

fn cas_lat_impl (c : atomic_cell) (old_n new_n : U32.t) (#is : inames)
    (phi : bool -> slprop)
    (tok : au_token is U32.t bool
      (fun n -> cell_val c.cg n)
      (cas_beta c old_n new_n)
      (fun _ b -> phi b))
    (_u : unit)
  requires is_cell c ** au_available tok
  returns b : bool
  ensures is_cell c ** phi b
{
  // Open the caller's AU to obtain the abstract ghost half for this cell.
  later_credit_buy 1;
  let n = au_open tok;
  unfold cell_val;

  // The physical linearization point: one atomic CAS inside the cell invariant.
  unfold is_cell;
  let b = with_invariants bool emp_inames c.ci (cell_inv c)
    (GR.pts_to c.cg.gr #0.5R n)
    (fun b -> AP.cond b
      (GR.pts_to c.cg.gr #0.5R new_n ** pure (reveal n == old_n))
      (GR.pts_to c.cg.gr #0.5R n     ** pure (~ (reveal n == old_n))))
  fn _ {
    unfold cell_inv; unfold cell_inv_inner;
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
      fold (cell_inv_inner c.loc c.cg.gr); fold (cell_inv c);
      fold (AP.cond true
        (GR.pts_to c.cg.gr #0.5R new_n ** pure (reveal n == old_n))
        (GR.pts_to c.cg.gr #0.5R n     ** pure (~ (reveal n == old_n))));
      true
    } else {
      elim_cond_false _ _;
      with n0. assert (B.pts_to c.loc n0 **
        GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
      GR.pts_to_injective_eq c.cg.gr;
      rewrite each n0 as (reveal n);
      fold (cell_inv_inner c.loc c.cg.gr); fold (cell_inv c);
      fold (AP.cond false
        (GR.pts_to c.cg.gr #0.5R new_n ** pure (reveal n == old_n))
        (GR.pts_to c.cg.gr #0.5R n     ** pure (~ (reveal n == old_n))));
      false
    }
  };
  fold (is_cell c);

  // Commit the AU with the boolean-indexed CAS postcondition.
  if b {
    elim_cond_true _ _;
    fold (cell_val c.cg new_n);
    intro_pure (reveal n == old_n) ();
    fold (cas_beta c old_n new_n (reveal n) true);
    later_credit_buy 1;
    au_commit tok (reveal n) true;
    true
  } else {
    elim_cond_false _ _;
    fold (cell_val c.cg n);
    intro_pure (~ (reveal n == old_n)) ();
    fold (cas_beta c old_n new_n (reveal n) false);
    later_credit_buy 1;
    au_commit tok (reveal n) false;
    false
  }
}

(** Direct logically atomic triple witness for compare-and-swap.

    Public spec:
      <<< ∀∀ n. cell_val γ n >>>
        CAS c old_n new_n @ is
      <<< if b then cell_val γ new_n ** pure(n == old_n)
                else cell_val γ n     ** pure(n != old_n)
          | RET b >>> *)
let cas_lat (c : atomic_cell) (old_n new_n : U32.t) (#is : inames)
  : lat is U32.t bool
      (fun n -> cell_val c.cg n)
      (cas_beta c old_n new_n)
      (is_cell c)
  = cas_lat_impl c old_n new_n
