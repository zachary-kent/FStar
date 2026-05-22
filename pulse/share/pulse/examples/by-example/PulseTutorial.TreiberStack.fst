(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Treiber Stack — CAS-based push with logically atomic spec. No admits. *)
module PulseTutorial.TreiberStack
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module P = Pulse.Lib.Primitives
open Pulse.Lib.Inv

noeq type sn = { gr : GR.ref (list U32.t); }
noeq type tstack = { hd : B.box U32.t; nm : sn; inm : iname; }

let scont (g:sn) (xs:list U32.t) : slprop = pts_to g.gr #0.5R xs

let inv_inner (hd : B.box U32.t) (g : sn) (ver : U32.t) : slprop =
  exists* (xs : list U32.t). B.pts_to hd ver ** pts_to g.gr #0.5R xs

let sinv (hd : B.box U32.t) (g : sn) : slprop =
  exists* (ver : U32.t). inv_inner hd g ver

let is_ts (s:tstack) : slprop = inv s.inm (sinv s.hd s.nm)

fn new_stack ()
  requires emp
  returns s : tstack
  ensures is_ts s ** scont s.nm []
{
  let hd = B.alloc 0ul;
  let gr = GR.alloc #(list U32.t) [];
  GR.share gr;
  let g : sn = { gr };
  rewrite (GR.pts_to gr #0.5R []) as (pts_to g.gr #0.5R []);
  rewrite (GR.pts_to gr #0.5R []) as (scont g []);
  fold (inv_inner hd g 0ul);
  fold (sinv hd g);
  let i = new_invariant (sinv hd g);
  let s : tstack = { hd; nm = g; inm = i };
  rewrite (inv i (sinv hd g)) as (inv s.inm (sinv s.hd s.nm));
  fold (is_ts s);
  rewrite (scont g []) as (scont s.nm []);
  s
}

fn rec push_loop
    (s : tstack) (v : U32.t)
    (tok : au_token (list U32.t) unit
      (fun xs -> scont s.nm xs)
      (fun xs _ -> scont s.nm (Cons v xs))
      (fun xs _ -> scont s.nm (Cons v xs)))
    (_u:unit)
  requires is_ts s ** au_available tok
  ensures is_ts s ** (exists* (xs_out : list U32.t). scont s.nm xs_out)
{
  later_credit_buy 1;

  unfold is_ts;
  dup_inv s.inm _;
  let xs = au_open tok;
  unfold scont;

  let success =
    with_invariants bool emp_inames s.inm (sinv s.hd s.nm)
      (pts_to s.nm.gr #0.5R xs ** au_opened tok)
      (fun b -> P.cond b
        (pts_to s.nm.gr #0.5R (Cons v xs) ** au_opened tok)
        (pts_to s.nm.gr #0.5R xs ** au_opened tok))
    fn _ {
      unfold sinv;
      with ver0. unfold (inv_inner s.hd s.nm ver0);
      with xs0.
        assert (B.pts_to s.hd ver0 ** pts_to s.nm.gr #0.5R xs0 **
                pts_to s.nm.gr #0.5R xs ** au_opened tok);
      GR.pts_to_injective_eq s.nm.gr;
      rewrite each xs0 as (reveal xs);
      let b = P.cas_box s.hd 0ul 1ul;
      if b {
        elim_cond_true _ _ _;
        drop_ (pure (ver0 == 0ul));
        GR.gather s.nm.gr;
        GR.(s.nm.gr := Cons v (reveal xs));
        GR.share s.nm.gr;
        fold (inv_inner s.hd s.nm 1ul);
        fold (sinv s.hd s.nm);
        intro_cond_true (pts_to s.nm.gr #0.5R (Cons v xs) ** au_opened tok)
                        (pts_to s.nm.gr #0.5R xs ** au_opened tok);
        true
      } else {
        elim_cond_false _ _ _;
        fold (inv_inner s.hd s.nm ver0);
        fold (sinv s.hd s.nm);
        intro_cond_false (pts_to s.nm.gr #0.5R (Cons v xs) ** au_opened tok)
                         (pts_to s.nm.gr #0.5R xs ** au_opened tok);
        false
      }
    };

  if (success) {
    elim_cond_true _ _ _;
    drop_ (inv s.inm (sinv s.hd s.nm));
    fold (scont s.nm (Cons v xs));
    au_commit tok xs (hide ()) fn _ { () };
    // phi produced: scont s.nm (Cons v xs)
    rewrite (inv s.inm (sinv s.hd s.nm)) as (is_ts s);
  } else {
    elim_cond_false _ _ _;
    fold (scont s.nm xs);
    later_credit_buy 1;
    au_abort tok xs;
    drop_ (inv s.inm (sinv s.hd s.nm));
    rewrite (inv s.inm (sinv s.hd s.nm)) as (is_ts s);
    push_loop s v tok ()
  }
}

fn push (s:tstack) (v:U32.t)
  requires is_ts s ** scont s.nm 'xs
  ensures is_ts s ** (exists* ys. scont s.nm ys)
{
  let tok = au_intro #(list U32.t) #unit
                     #(fun xs -> scont s.nm xs)
                     #(fun xs _ -> scont s.nm (Cons v xs))
                     #(fun xs _ -> scont s.nm (Cons v xs))
                     'xs;
  push_loop s v tok ()
}
