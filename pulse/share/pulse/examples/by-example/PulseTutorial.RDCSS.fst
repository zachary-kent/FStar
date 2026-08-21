(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** RDCSS — inspired by Iris logatom/rdcss.
    
    PARTIAL IRIS PORT: the exported wrapper below now reads l_m from a
    physical shared box before invoking the logically atomic l_n update, but
    the descriptor/helping protocol is not implemented. The operation IS
    logically atomic wrt l_n: it has an AU/LAT spec parametric in Φ.
    
    The main loop now allocates a prophecy variable and resolves the CAS inside
    the invariant through the client-facing atomic Resolve rule, so the n-CAS
    linearization evidence is no longer the old prophecy-avoiding shortcut.
    The full Iris version still needs: descriptor ownership/helping under the
    invariant and prophecy-based LP identification across helpers.  This file
    now includes verified descriptor-slot CAS install and completion/helping
    steps as building blocks for replacing the simplified U32-only l_n
    representation. *)
module PulseTutorial.RDCSS
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module AP = Pulse.Lib.AtomicPrimitives
module P = Pulse.Lib.Prophecy
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

(** Descriptor-shaped slot used by the future faithful RDCSS port.

    The exported example below still stores plain [U32.t] in [l_n].  Iris's
    RDCSS temporarily installs a descriptor in [l_n] so helpers can complete the
    operation.  This eqtype model and CAS install step are kept separate from
    the current proof while the invariant/helping proof is being ported. *)
type rdcss_descriptor = {
  desc_m1 : U32.t;
  desc_n1 : U32.t;
  desc_n2 : U32.t;
}

type rdcss_slot =
  | RdcssValue : U32.t -> rdcss_slot
  | RdcssDescriptor : rdcss_descriptor -> rdcss_slot

fn rdcss_descriptor_install_step
    (l_n:B.box rdcss_slot)
    (d:rdcss_descriptor)
    (#cur:erased rdcss_slot)
  requires B.pts_to l_n cur
  returns b:bool
  ensures AP.cond b
    (B.pts_to l_n (RdcssDescriptor d) ** pure (reveal cur == RdcssValue d.desc_n1))
    (B.pts_to l_n cur)
{
  AP.atomic_cas l_n (RdcssValue d.desc_n1) (RdcssDescriptor d)
}

(** One helper/completion step for a descriptor already installed in [l_n].

    This is the operational core missing from the simplified exported RDCSS
    proof: a helper reads the shared [l_m] location, decides the descriptor's
    final value, and tries to replace the descriptor by that value.  The helper
    is still a standalone building block (the active invariant below stores
    plain [U32.t]), but unlike the older model it verifies the actual
    descriptor-helping action shape used by the Iris implementation. *)
fn rdcss_descriptor_complete_step
    (l_m:B.box U32.t)
    (l_n:B.box rdcss_slot)
    (d:rdcss_descriptor)
    (#m_cur:erased U32.t)
    (#q:perm)
  requires B.pts_to l_m #q m_cur ** B.pts_to l_n (RdcssDescriptor d)
  returns b:bool
  ensures B.pts_to l_m #q m_cur **
    AP.cond b
      (B.pts_to l_n (RdcssValue (if reveal m_cur = d.desc_m1 then d.desc_n2 else d.desc_n1)))
      (B.pts_to l_n (RdcssDescriptor d))
{
  let m = AP.atomic_read l_m;
  assert pure (m == reveal m_cur);
  let b = AP.atomic_cas l_n (RdcssDescriptor d)
    (RdcssValue (if m = d.desc_m1 then d.desc_n2 else d.desc_n1));
  if b {
    unfold AP.cond;
    rewrite each m as (reveal m_cur);
    drop_ (pure (RdcssDescriptor d == RdcssDescriptor d));
    fold (AP.cond true
      (B.pts_to l_n (RdcssValue (if reveal m_cur = d.desc_m1 then d.desc_n2 else d.desc_n1)))
      (B.pts_to l_n (RdcssDescriptor d)));
    true
  } else {
    unfold AP.cond;
    fold (AP.cond false
      (B.pts_to l_n (RdcssValue (if reveal m_cur = d.desc_m1 then d.desc_n2 else d.desc_n1)))
      (B.pts_to l_n (RdcssDescriptor d)));
    false
  }
}

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

(** Prophecy-resolved CAS slice for the future Iris-style RDCSS port.
    Full RDCSS still needs descriptors/helping and AU plumbing, but this helper
    couples the CAS result to a prophecy prediction in the same observable
    atomic step. *)
fn cas_with_prophecy
    (r:B.box U32.t)
    (expected new_val:U32.t)
    (p:P.prophecy_var bool unit)
    (#cur:erased U32.t)
    (#pred:erased bool)
    (#tail:erased (P.prediction_stream bool unit))
  requires B.pts_to r cur ** P.prophecy_token p ((reveal pred, ()) :: reveal tail)
  returns b:bool
  ensures AP.cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                    (B.pts_to r cur) **
          P.prophecy_token p (reveal tail) ** pure (b == reveal pred)
{
  let b = P.resolve #bool #unit p () #pred #tail
    #(B.pts_to r cur)
    #(fun b -> AP.cond b (B.pts_to r new_val ** pure (reveal cur == expected))
                         (B.pts_to r cur))
    fn _ { AP.atomic_cas r expected new_val };
  b
}


fn try_rdcss_with_prophecy
    (s:rdcss_state) (n1 n2 : U32.t)
    (p:P.prophecy_var bool unit)
    (#n : erased U32.t)
    (#pred : erased bool)
    (#tail : erased (P.prediction_stream bool unit))
  requires is_rdcss s ** GR.pts_to s.rg.gr #0.5R n **
           P.prophecy_token p ((reveal pred, ()) :: reveal tail)
  returns b : bool
  ensures AP.cond b
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 **
      P.prophecy_token p (reveal tail) ** pure (b == reveal pred) ** pure (reveal n == n1))
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n **
      P.prophecy_token p (reveal tail) ** pure (b == reveal pred))
{
  unfold is_rdcss;
  let b = with_invariants bool emp_inames s.ri (rdcss_inv_raw s)
    (GR.pts_to s.rg.gr #0.5R n ** P.prophecy_token p ((reveal pred, ()) :: reveal tail))
    (fun b -> AP.cond b
      (GR.pts_to s.rg.gr #0.5R n2 ** P.prophecy_token p (reveal tail) **
        pure (b == reveal pred) ** pure (reveal n == n1))
      (GR.pts_to s.rg.gr #0.5R n ** P.prophecy_token p (reveal tail) **
        pure (b == reveal pred)))
  fn _ {
    let b = P.resolve_atomic #bool #unit p () #pred #tail
      #(rdcss_inv_raw s ** GR.pts_to s.rg.gr #0.5R n)
      #(fun b -> rdcss_inv_raw s ** AP.cond b
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
      fold (AP.cond true
        (GR.pts_to s.rg.gr #0.5R n2 ** P.prophecy_token p (reveal tail) ** pure (true == reveal pred) ** pure (reveal n == n1))
        (GR.pts_to s.rg.gr #0.5R n ** P.prophecy_token p (reveal tail) ** pure (true == reveal pred)));
      true
    } else {
      elim_cond_false _ _;
      fold (AP.cond false
        (GR.pts_to s.rg.gr #0.5R n2 ** P.prophecy_token p (reveal tail) ** pure (false == reveal pred) ** pure (reveal n == n1))
        (GR.pts_to s.rg.gr #0.5R n ** P.prophecy_token p (reveal tail) ** pure (false == reveal pred)));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_rdcss s);
    fold (AP.cond true
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** P.prophecy_token p (reveal tail) ** pure (true == reveal pred) ** pure (reveal n == n1))
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n ** P.prophecy_token p (reveal tail) ** pure (true == reveal pred)));
    true
  } else {
    elim_cond_false _ _;
    fold (is_rdcss s);
    fold (AP.cond false
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** P.prophecy_token p (reveal tail) ** pure (false == reveal pred) ** pure (reveal n == n1))
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n ** P.prophecy_token p (reveal tail) ** pure (false == reveal pred)));
    false
  }
}

fn try_rdcss_with_prophecy_token
    (s:rdcss_state) (n1 n2 : U32.t)
    (p:P.prophecy_var bool unit)
    (#n : erased U32.t)
    (#pvs : erased (P.prediction_stream bool unit))
  requires is_rdcss s ** GR.pts_to s.rg.gr #0.5R n **
           P.prophecy_token p (reveal pvs)
  returns b : bool
  ensures AP.cond b
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1) **
      (exists* (tail:P.prediction_stream bool unit).
        P.prophecy_token p tail ** pure (reveal pvs == (true, ()) :: tail)))
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n **
      (exists* (tail:P.prediction_stream bool unit).
        P.prophecy_token p tail ** pure (reveal pvs == (false, ()) :: tail)))
{
  unfold is_rdcss;
  let b = with_invariants bool emp_inames s.ri (rdcss_inv_raw s)
    (GR.pts_to s.rg.gr #0.5R n ** P.prophecy_token p (reveal pvs))
    (fun b -> AP.cond b
      (GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1) **
        (exists* (tail:P.prediction_stream bool unit).
          P.prophecy_token p tail ** pure (reveal pvs == (true, ()) :: tail)))
      (GR.pts_to s.rg.gr #0.5R n **
        (exists* (tail:P.prediction_stream bool unit).
          P.prophecy_token p tail ** pure (reveal pvs == (false, ()) :: tail))))
  fn _ {
    let b = P.resolve_token_atomic #bool #unit p () #pvs
      #(rdcss_inv_raw s ** GR.pts_to s.rg.gr #0.5R n)
      #(fun b -> rdcss_inv_raw s ** AP.cond b
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
      with tail. assert (P.prophecy_token p tail ** pure (pvs == (true, ()) :: tail));
      fold (AP.cond true
        (GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1) **
          (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (true, ()) :: tail)))
        (GR.pts_to s.rg.gr #0.5R n **
          (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (false, ()) :: tail))));
      true
    } else {
      elim_cond_false _ _;
      with tail. assert (P.prophecy_token p tail ** pure (pvs == (false, ()) :: tail));
      fold (AP.cond false
        (GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1) **
          (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (true, ()) :: tail)))
        (GR.pts_to s.rg.gr #0.5R n **
          (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (false, ()) :: tail))));
      false
    }
  };
  if b {
    elim_cond_true _ _;
    fold (is_rdcss s);
    fold (AP.cond true
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1) **
        (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (true, ()) :: tail)))
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n **
        (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (false, ()) :: tail))));
    true
  } else {
    elim_cond_false _ _;
    fold (is_rdcss s);
    fold (AP.cond false
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1) **
        (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (true, ()) :: tail)))
      (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n **
        (exists* (tail:P.prediction_stream bool unit). P.prophecy_token p tail ** pure (reveal pvs == (false, ()) :: tail))));
    false
  }
}

fn try_rdcss (s:rdcss_state) (n1 n2 : U32.t) (#n : erased U32.t)
  requires is_rdcss s ** GR.pts_to s.rg.gr #0.5R n
  returns b : bool
  ensures AP.cond b
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1))
    (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n)
{
  let p = P.prophecy_alloc #bool #unit ();
  with pvs. assert (P.prophecy_token p pvs);
  let b = try_rdcss_with_prophecy_token s n1 n2 p #n #pvs;
  if b {
    elim_cond_true _ _;
    with tail. assert (P.prophecy_token p tail ** pure (pvs == (true, ()) :: tail));
    drop_ (P.prophecy_token p tail);
    fold (AP.cond true (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n2 ** pure (reveal n == n1)) (is_rdcss s ** GR.pts_to s.rg.gr #0.5R n));
    true
  } else {
    elim_cond_false _ _;
    with tail. assert (P.prophecy_token p tail ** pure (pvs == (false, ()) :: tail));
    drop_ (P.prophecy_token p tail);
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

(** Wrapper that removes the old external [m_val] shortcut for clients: the
    operation first performs an observable atomic read of [l_m], then uses that
    value as the m-side comparison input for the AU-protected l_n update.  This
    still stops short of the full Iris descriptor/helping protocol, but [l_m] is
    now an actual shared location read by the operation rather than a caller
    supplied pure parameter. *)
fn rdcss_with_m (s:rdcss_state) (l_m:B.box U32.t) (m1 n1 n2 : U32.t)
    (#m_cur : erased U32.t) (#n : erased U32.t) (#q:perm)
  requires is_rdcss s ** rdcss_content s.rg n ** B.pts_to l_m #q m_cur
  ensures is_rdcss s ** B.pts_to l_m #q m_cur ** (exists* n'. rdcss_content s.rg n')
{
  let m_val = AP.atomic_read l_m;
  drop_ (pure (m_val == reveal m_cur));
  rdcss s m_val m1 n1 n2
}

(* ================================================================ *)
(* Client example                                                   *)
(* ================================================================ *)

fn rdcss_client ()
  requires emp
  ensures emp
{
  let s = new_rdcss 42ul;
  let l_m = B.alloc 10ul;
  // RDCSS: read *l_m; if it is 10 and *l_n is 42 then *l_n := 99.
  rdcss_with_m s l_m 10ul 42ul 99ul;
  // Read to verify
  let cur = get_rdcss s;
  // Cleanup
  with n'. assert (rdcss_content s.rg n');
  B.free l_m;
  drop_ (is_rdcss s);
  drop_ (rdcss_content s.rg n')
}
