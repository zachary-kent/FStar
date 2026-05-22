(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** RDCSS — Restricted Double-Compare Single-Swap.
    Ported from Iris logatom/rdcss.
    
    rdcss(l_m, l_n, m1, n1, n2):
      atomically: if *l_m == m1 && *l_n == n1 then *l_n := n2
      returns the old value of *l_n
    
    Simplified from Iris (which uses descriptor-based helping).
    Here we use a direct CAS-loop approach. *)
module PulseTutorial.RDCSS
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
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
(* RDCSS state                                                      *)
(* ================================================================ *)

noeq type rdcss_ghost = { gr : GR.ref U32.t; }
noeq type rdcss_state = {
  l_n : B.box U32.t;   (* target location — atomically read/modified *)
  rg  : rdcss_ghost;
  ri  : iname;
}

let rdcss_content (g:rdcss_ghost) (n:U32.t) : slprop = GR.pts_to g.gr #0.5R n

let rdcss_inv_inner (l_n : B.box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (n:U32.t). B.pts_to l_n n ** GR.pts_to gr #0.5R n

let rdcss_inv_raw (s:rdcss_state) : slprop = rdcss_inv_inner s.l_n s.rg.gr

let is_rdcss (s:rdcss_state) : slprop = inv s.ri (rdcss_inv_raw s)

(* ================================================================ *)
(* new_rdcss                                                        *)
(* ================================================================ *)

fn new_rdcss (init:U32.t)
  requires emp
  returns s : rdcss_state
  ensures is_rdcss s ** rdcss_content s.rg init
{
  let l_n = B.alloc init;
  let gr = GR.alloc #U32.t init;
  GR.share gr;
  let rg : rdcss_ghost = { gr };
  rewrite (GR.pts_to gr #0.5R init) as (GR.pts_to rg.gr #0.5R init);
  rewrite (GR.pts_to gr #0.5R init) as (rdcss_content rg init);
  fold (rdcss_inv_inner l_n rg.gr);
  let ri = new_invariant (rdcss_inv_inner l_n rg.gr);
  let s : rdcss_state = { l_n; rg; ri };
  rewrite (inv ri (rdcss_inv_inner l_n rg.gr)) as (inv s.ri (rdcss_inv_raw s));
  fold (is_rdcss s);
  rewrite (rdcss_content rg init) as (rdcss_content s.rg init);
  s
}

(* ================================================================ *)
(* get — atomic read                                                *)
(* ================================================================ *)

fn get_rdcss (s:rdcss_state)
  requires is_rdcss s
  returns n : U32.t
  ensures is_rdcss s
{
  unfold is_rdcss;
  let n = with_invariants U32.t emp_inames s.ri (rdcss_inv_raw s)
    emp (fun _ -> emp)
  fn _ {
    unfold rdcss_inv_raw; unfold rdcss_inv_inner;
    let n = AP.atomic_read s.l_n;
    fold (rdcss_inv_inner s.l_n s.rg.gr); fold (rdcss_inv_raw s);
    n
  };
  fold (is_rdcss s);
  n
}

(* ================================================================ *)
(* rdcss — the main operation                                       *)
(* ================================================================ *)

(** rdcss_impl: read l_m, if it matches m1, CAS l_n from n1 to n2.
    Returns old value of l_n.
    
    In the full Iris proof, l_m is under a separate invariant and the
    linearization point uses a prophecy variable. Here we simplify:
    l_m is passed as a concrete value (snapshot). *)
fn rec rdcss_loop (s:rdcss_state) (m_val : U32.t) (m1 n1 n2 : U32.t)
  requires is_rdcss s ** rdcss_content s.rg 'n
  returns old : U32.t
  ensures is_rdcss s ** (exists* n'. rdcss_content s.rg n')
{
  // Read current l_n value
  let cur_n = get_rdcss s;
  // Check: does m_val == m1 && cur_n == n1?
  if (m_val = m1 && cur_n = n1) {
    // Try CAS: l_n from n1 to n2
    unfold is_rdcss; unfold rdcss_content;
    let b = with_invariants bool emp_inames s.ri (rdcss_inv_raw s)
      (GR.pts_to s.rg.gr #0.5R 'n)
      (fun b -> AP.cond b
        (GR.pts_to s.rg.gr #0.5R n2)
        (GR.pts_to s.rg.gr #0.5R 'n))
    fn _ {
      unfold rdcss_inv_raw; unfold rdcss_inv_inner;
      let b = AP.atomic_cas s.l_n n1 n2;
      if b {
        elim_cond_true _ _;
        with n0. assert (B.pts_to s.l_n n2 ** GR.pts_to s.rg.gr #0.5R n0 ** GR.pts_to s.rg.gr #0.5R 'n);
        GR.pts_to_injective_eq s.rg.gr;
        rewrite each n0 as (reveal 'n);
        GR.gather s.rg.gr;
        GR.(s.rg.gr := n2);
        GR.share s.rg.gr;
        fold (rdcss_inv_inner s.l_n s.rg.gr); fold (rdcss_inv_raw s);
        fold (AP.cond true (GR.pts_to s.rg.gr #0.5R n2) (GR.pts_to s.rg.gr #0.5R 'n));
        true
      } else {
        elim_cond_false _ _;
        fold (rdcss_inv_inner s.l_n s.rg.gr); fold (rdcss_inv_raw s);
        fold (AP.cond false (GR.pts_to s.rg.gr #0.5R n2) (GR.pts_to s.rg.gr #0.5R 'n));
        false
      }
    };
    if b {
      elim_cond_true _ _;
      fold (rdcss_content s.rg n2);
      fold (is_rdcss s);
      cur_n  // return old value
    } else {
      elim_cond_false _ _;
      fold (rdcss_content s.rg 'n);
      fold (is_rdcss s);
      // CAS failed, retry
      rdcss_loop s m_val m1 n1 n2
    }
  } else {
    // Condition not met: return current value without modification
    cur_n
  }
}

(* ================================================================ *)
(* Client example                                                   *)
(* ================================================================ *)

fn rdcss_client ()
  requires emp
  ensures emp
{
  let s = new_rdcss 42ul;
  // RDCSS: if m_val==10 && *l_n==42 then *l_n := 99
  let old = rdcss_loop s 10ul 10ul 42ul 99ul;
  // old should be 42, and *l_n is now 99
  // Read to verify
  let cur = get_rdcss s;
  // Cleanup
  with n'. assert (rdcss_content s.rg n');
  drop_ (is_rdcss s);
  drop_ (rdcss_content s.rg n')
}
