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

    Why this works without a retry loop.  Once we au_open the outer
    AU, we hold ctr_val c.cg n (one ghost half).  The other half lives
    in c.ci's invariant.  No other thread can modify the counter while
    we hold our half, because mutating the counter requires updating
    the invariant's ghost half too, and that requires gathering with
    our half.  So inside the AU window the counter is FROZEN — the
    internal read sees n, and a CAS at expected=n cannot fail.

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

(* ================================================================ *)
(* atomic_max c v — multi-LP outer LAT                              *)
(*                                                                  *)
(*   <<< ∀∀ n. ctr_val c n >>>                                      *)
(*     atomic_max c v                                               *)
(*   <<< ctr_val c (max n v) ** pure (result == max n v)            *)
(*       | RET result : U32.t >>>                                   *)
(*                                                                  *)
(* Implementation:                                                  *)
(*   1. au_open — get erased witness n + ctr_val c.cg n.            *)
(*   2. Internal atomic_read inside c.ci → observed; prove          *)
(*      observed == reveal n via GR.pts_to_injective_eq.            *)
(*   3. Branch on observed vs v:                                    *)
(*      - observed >= v:   LP at the read.   au_commit at result=n. *)
(*      - observed <  v:   internal cas_box at expected=n new=v;    *)
(*                         CAS cannot fail (state frozen);          *)
(*                         LP at the CAS.   au_commit at result=v.  *)
(* ================================================================ *)

fn atomic_max (c:counter) (v:U32.t)
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
  // Step 1: open outer AU.  Get erased witness n + ctr_val c.cg n + au_opened.
  later_credit_buy 1;
  let n = au_open tok;
  unfold ctr_val;
  // We now hold: GR.pts_to c.cg.gr #0.5R n, au_opened tok (reveal n).

  // Step 2: internal atomic_read inside the invariant.  Prove observed = n.
  unfold is_ctr;
  let observed = with_invariants U32.t emp_inames c.ci (ctr_inv c)
    (GR.pts_to c.cg.gr #0.5R n)
    (fun observed -> GR.pts_to c.cg.gr #0.5R n ** pure (observed == reveal n))
  fn _ {
    unfold ctr_inv; unfold ctr_inv_inner;
    with n0. assert (B.pts_to c.loc n0 **
      GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
    GR.pts_to_injective_eq c.cg.gr;
    rewrite each n0 as (reveal n);
    let observed = AP.read_atomic_box c.loc;
    // From read_atomic_box's spec: pure (reveal n == observed).
    fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
    observed
  };
  fold (is_ctr c);
  // Have: GR.pts_to c.cg.gr #0.5R n, observed:U32.t, pure (observed == reveal n).

  // Step 3: branch on observed vs v.
  if U32.lt observed v {
    // n < v branch.  observed = n, so n < v, hence u32_max n v = v.
    // Internal CAS at expected=n new=v — cannot fail (state frozen at n).
    // Inner cond's failure case carries the strengthened cas_box inequality
    // witness; combined outside with `pure (observed == reveal n)` (still in
    // scope from the read step), the SMT derives False and the failure
    // branch becomes provably unreachable.
    unfold is_ctr;
    let b = with_invariants bool emp_inames c.ci (ctr_inv c)
      (GR.pts_to c.cg.gr #0.5R n)
      (fun b -> AP.cond b
        (GR.pts_to c.cg.gr #0.5R v)
        (GR.pts_to c.cg.gr #0.5R n ** pure (~ (reveal n == observed))))
    fn _ {
      unfold ctr_inv; unfold ctr_inv_inner;
      with n0. assert (B.pts_to c.loc n0 **
        GR.pts_to c.cg.gr #0.5R n0 ** GR.pts_to c.cg.gr #0.5R n);
      GR.pts_to_injective_eq c.cg.gr;
      rewrite each n0 as (reveal n);
      let b = AP.cas_box c.loc observed v;
      if b {
        elim_cond_true _ _;
        GR.gather c.cg.gr;
        GR.(c.cg.gr := v);
        GR.share c.cg.gr;
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        fold (AP.cond true
          (GR.pts_to c.cg.gr #0.5R v)
          (GR.pts_to c.cg.gr #0.5R n ** pure (~ (reveal n == observed))));
        true
      } else {
        elim_cond_false _ _;
        // Have B.pts_to c.loc (reveal n) ** pure (~(reveal n == observed)).
        fold (ctr_inv_inner c.loc c.cg.gr); fold (ctr_inv c);
        fold (AP.cond false
          (GR.pts_to c.cg.gr #0.5R v)
          (GR.pts_to c.cg.gr #0.5R n ** pure (~ (reveal n == observed))));
        false
      }
    };
    fold (is_ctr c);
    if b {
      elim_cond_true _ _;
      fold (ctr_val c.cg v);
      rewrite (ctr_val c.cg v) as (ctr_val c.cg (u32_max (reveal n) v));
      later_credit_buy 1;
      au_commit tok (reveal n) v;
      v
    } else {
      // pure (~(reveal n == observed)) (from CAS-failure cond) plus
      // pure (observed == reveal n) (from the read step) gives pure False.
      elim_cond_false _ _;
      unreachable ()
    }
  } else {
    // n >= v branch.  observed = n, so n >= v, hence u32_max n v = n.
    // LP at the internal atomic_read above.
    fold (ctr_val c.cg n);
    rewrite (ctr_val c.cg n) as (ctr_val c.cg (u32_max (reveal n) v));
    later_credit_buy 1;
    au_commit tok (reveal n) observed;
    observed
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
