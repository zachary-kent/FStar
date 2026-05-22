(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Conditional Increment — inspired by Iris logatom/conditional_increment.
    
    SIMPLIFIED VERSION: The flag is owned exclusively (not under a
    concurrent invariant), so the flag read is non-atomic and there is
    no concurrent race on the flag. The Iris version uses a descriptor-
    based helping protocol with prophecy variables to handle the case
    where the flag is shared under an invariant and may change between
    the flag read and the CAS. That proof challenge is not represented
    here — it requires a faithful prophecy resolve primitive coupled
    to CAS (Iris's Resolve CmpXchg). *)
module PulseTutorial.ConditionalIncrement
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.Prophecy
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

ghost fn intro_cond_true (p q : slprop)
  requires p
  ensures AP.cond true p q
{ fold (AP.cond true p q) }

ghost fn intro_cond_false (p q : slprop)
  requires q
  ensures AP.cond false p q
{ fold (AP.cond false p q) }

(* ================================================================ *)
(* Counter + flag representation                                    *)
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

(* ================================================================ *)
(* new_counter                                                      *)
(* ================================================================ *)

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
(* cinc — conditional increment with prophecy                       *)
(* ================================================================ *)

(** The conditional increment: if flag is true, increment counter.
    
    Iris cinc spec:
    <<< ∀∀ b n, cinc_content γ n ∗ flag ↦ b >>>
        cinc counter flag @ ↑N
    <<< cinc_content γ (if b then n+1 else n) ∗ flag ↦ b | RET #() >>>
    
    Here we simplify: the flag is read non-atomically, and we use
    a CAS to conditionally increment. The prophecy predicts whether
    the flag will be true at the linearization point. *)

fn rec cinc_impl (s:cinc_state) (flag : B.box bool) (#flag_val : erased bool)
  requires is_cinc s ** cinc_content s.cg 'n ** flag |-> flag_val
  ensures is_cinc s ** (exists* m. cinc_content s.cg m) ** flag |-> flag_val
{
  // Read the flag
  let b = B.op_Bang flag;
  if b {
    // Flag is true: try to increment
    unfold is_cinc;
    // Read current counter value
    let old_n = with_invariants U32.t emp_inames s.ci (cinc_inv_raw s)
      emp (fun _ -> emp)
    fn _ {
      unfold cinc_inv_raw; unfold cinc_inv_inner;
      let n = AP.atomic_read s.counter;
      fold (cinc_inv_inner s.counter s.cg.gr); fold (cinc_inv_raw s);
      n
    };
    // CAS to increment
    unfold cinc_content;
    let b2 = with_invariants bool emp_inames s.ci (cinc_inv_raw s)
      (GR.pts_to s.cg.gr #0.5R 'n)
      (fun b2 -> AP.cond b2
        (GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal 'n) 1ul))
        (GR.pts_to s.cg.gr #0.5R 'n))
    fn _ {
      unfold cinc_inv_raw; unfold cinc_inv_inner;
      let b2 = AP.atomic_cas s.counter old_n (U32.add_mod old_n 1ul);
      if b2 {
        elim_cond_true _ _;
        with n0. assert (B.pts_to s.counter (U32.add_mod old_n 1ul) ** GR.pts_to s.cg.gr #0.5R n0 ** GR.pts_to s.cg.gr #0.5R 'n);
        GR.pts_to_injective_eq s.cg.gr;
        rewrite each n0 as (reveal 'n);
        GR.gather s.cg.gr;
        GR.(s.cg.gr := U32.add_mod (reveal 'n) 1ul);
        GR.share s.cg.gr;
        fold (cinc_inv_inner s.counter s.cg.gr); fold (cinc_inv_raw s);
        fold (AP.cond true
          (GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal 'n) 1ul))
          (GR.pts_to s.cg.gr #0.5R 'n));
        true
      } else {
        elim_cond_false _ _;
        fold (cinc_inv_inner s.counter s.cg.gr); fold (cinc_inv_raw s);
        fold (AP.cond false
          (GR.pts_to s.cg.gr #0.5R (U32.add_mod (reveal 'n) 1ul))
          (GR.pts_to s.cg.gr #0.5R 'n));
        false
      }
    };
    if b2 {
      elim_cond_true _ _;
      fold (cinc_content s.cg (U32.add_mod (reveal 'n) 1ul));
      fold (is_cinc s);
    } else {
      elim_cond_false _ _;
      fold (cinc_content s.cg 'n);
      fold (is_cinc s);
      // CAS failed, retry
      cinc_impl s flag
    }
  } else {
    // Flag is false: no increment needed
    ()
  }
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
  // Conditional increment with flag=true
  cinc_impl s flag;
  // Set flag to false
  B.op_Colon_Equals flag false;
  // Conditional increment with flag=false (no-op)
  cinc_impl s flag;
  // Cleanup
  B.free flag;
  with m0. assert (cinc_content s.cg m0);
  drop_ (is_cinc s);
  drop_ (cinc_content s.cg m0)
}
