(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** RDCSS — inspired by Iris logatom/rdcss.
    
    SIMPLIFIED: l_m's value is passed as a parameter (m_val) rather than
    read from a concurrent location. The descriptor/helping protocol is
    not implemented. However, the operation IS logically atomic wrt l_n:
    it has an AU/LAT spec parametric in Φ.
    
    Full Iris version would need: shared l_m under invariant, descriptor
    heap cell, helping protocol, and prophecy-based LP identification. *)
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

(* ================================================================ *)
(* RDCSS state                                                      *)
(* ================================================================ *)

noeq type rdcss_ghost = { gr : GR.ref U32.t; }
noeq type rdcss_state = {
  l_n : B.box U32.t;
  rg  : rdcss_ghost;
  ri  : iname;
}

let rdcss_content (g:rdcss_ghost) (n:U32.t) : slprop = GR.pts_to g.gr #0.5R n

let rdcss_inv_inner (l_n : B.box U32.t) (gr : GR.ref U32.t) : slprop =
  exists* (n:U32.t). B.pts_to l_n n ** GR.pts_to gr #0.5R n

let rdcss_inv_raw (s:rdcss_state) : slprop = rdcss_inv_inner s.l_n s.rg.gr
let is_rdcss (s:rdcss_state) : slprop = inv s.ri (rdcss_inv_raw s)

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
(* try_rdcss — single atomic CAS inside invariant                   *)
(* ================================================================ *)

fn try_rdcss (s:rdcss_state) (n1 n2 : U32.t) (#n : erased U32.t)
  requires is_rdcss s ** GR.pts_to s.rg.gr #0.5R n
  returns b : bool
  ensures AP.cond b
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1))
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n)
{
  unfold is_rdcss;
  let b = with_invariants bool emp_inames s.ri (rdcss_inv_raw s)
    (GR.pts_to s.rg.gr #0.5R n)
    (fun b -> AP.cond b
      (GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1))
      (GR.pts_to s.rg.gr #0.5R n))
  fn _ {
    unfold rdcss_inv_raw; unfold rdcss_inv_inner;
    let b = AP.atomic_cas s.l_n n1 n2;
    if b {
      elim_cond_true _ _;
      with n0. assert (B.pts_to s.l_n n2 ** GR.pts_to s.rg.gr #0.5R n0 ** GR.pts_to s.rg.gr #0.5R n);
      GR.pts_to_injective_eq s.rg.gr;
      rewrite each n0 as (reveal n);
      GR.gather s.rg.gr;
      GR.(s.rg.gr := n2);
      GR.share s.rg.gr;
      fold (rdcss_inv_inner s.l_n s.rg.gr); fold (rdcss_inv_raw s);
      fold (AP.cond true (GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1)) (GR.pts_to s.rg.gr #0.5R n));
      true
    } else {
      elim_cond_false _ _;
      fold (rdcss_inv_inner s.l_n s.rg.gr); fold (rdcss_inv_raw s);
      fold (AP.cond false (GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1)) (GR.pts_to s.rg.gr #0.5R n));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_rdcss s);
    fold (AP.cond true (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1)) (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n));
    true
  } else {
    elim_cond_false _ _;
    fold (is_rdcss s);
    fold (AP.cond false (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1)) (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n));
    false
  }
}

(* ================================================================ *)
(* rdcss — the main operation with AU/LAT spec                      *)
(* ================================================================ *)

(** rdcss_result: what l_n becomes after rdcss *)
let rdcss_result (m_val m1 n1 n2 n : U32.t) : U32.t =
  if m_val = m1 && n = n1 then n2 else n

(** rdcss_loop: CAS-retry loop with AU spec.
    m_val is the snapshot of l_m (read before AU).
    Logically atomic wrt l_n: parametric in Φ. *)
fn rec rdcss_loop (s:rdcss_state) (m_val m1 n1 n2 : U32.t)
    (#phi : U32.t -> unit -> slprop)
    (tok : au_token emp_inames U32.t unit
      (fun n -> rdcss_content s.rg n)
      (fun n _ -> rdcss_content s.rg (rdcss_result m_val m1 n1 n2 n))
      phi)
    (_u:unit)
  requires is_rdcss s ** au_available tok
  ensures is_rdcss s ** (exists* n. phi n ())
{
  later_credit_buy 1;
  let n = au_open tok;
  unfold rdcss_content;
  if (m_val = m1) {
    // m condition met: try CAS on l_n
    let b = try_rdcss s n1 n2;
    if b {
      elim_cond_true _ _;
      // CAS succeeded: reveal n == n1 (from try_rdcss)
      // rdcss_result m_val m1 n1 n2 n = n2
      fold (rdcss_content s.rg n2);
      rewrite (rdcss_content s.rg n2) as
              (rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n)));
      later_credit_buy 1;
      au_commit tok (reveal n) ();
    } else {
      elim_cond_false _ _;
      fold (rdcss_content s.rg n);
      later_credit_buy 1;
      au_abort tok (reveal n);
      rdcss_loop s m_val m1 n1 n2 tok ()
    }
  } else {
    // m condition not met: no modification, commit immediately
    // rdcss_result m_val m1 n1 n2 n = n (since m_val != m1)
    fold (rdcss_content s.rg n);
    rewrite (rdcss_content s.rg (reveal n)) as
            (rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n)));
    later_credit_buy 1;
    au_commit tok (reveal n) ();
  }
}

(** Type witness: rdcss_loop IS a lat_void *)
let rdcss_is_lat (s:rdcss_state) (m_val m1 n1 n2 : U32.t)
  : lat_void emp_inames U32.t
    (fun n -> rdcss_content s.rg n)
    (fun n _ -> rdcss_content s.rg (rdcss_result m_val m1 n1 n2 n))
    (is_rdcss s)
  = fun #phi tok _u -> rdcss_loop s m_val m1 n1 n2 #phi tok _u

(* ================================================================ *)
(* Sequential wrapper                                               *)
(* ================================================================ *)

ghost
fn mk_rdcss_trade (s:rdcss_state) (m_val m1 n1 n2 : U32.t) (#n : erased U32.t)
  requires emp
  ensures (forall* (y:unit). (later_credit 1 ** rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n))) @==> rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n)))
{
  intro_forall #unit #(fun (y:unit) -> (later_credit 1 ** rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n))) @==> rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n)))
    emp
    fn (y:unit) {
      intro_trade (later_credit 1 ** rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n)))
                  (rdcss_content s.rg (rdcss_result m_val m1 n1 n2 (reveal n))) emp
        fn _ { drop_ (later_credit 1) }
    }
}

fn rdcss (s:rdcss_state) (m_val m1 n1 n2 : U32.t)
  requires is_rdcss s ** rdcss_content s.rg 'n
  ensures is_rdcss s ** (exists* n'. rdcss_content s.rg n')
{
  mk_rdcss_trade s m_val m1 n1 n2 #'n;
  let tok = au_intro #emp_inames #U32.t #unit
    #(fun n -> rdcss_content s.rg n)
    #(fun n _ -> rdcss_content s.rg (rdcss_result m_val m1 n1 n2 n))
    #(fun n _ -> rdcss_content s.rg (rdcss_result m_val m1 n1 n2 n))
    'n;
  rdcss_loop s m_val m1 n1 n2 tok ()
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
  rdcss s 10ul 10ul 42ul 99ul;
  // Read to verify
  let cur = get_rdcss s;
  // Cleanup
  with n'. assert (rdcss_content s.rg n');
  drop_ (is_rdcss s);
  drop_ (rdcss_content s.rg n')
}
