(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Treiber Stack — CAS push with LA. No admits. *)
module PulseTutorial.TreiberStack
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
module B = Pulse.Lib.Box
module GR = Pulse.Lib.GhostReference
module U32 = FStar.UInt32
module P = Pulse.Lib.Primitives
open Pulse.Lib.Inv

[@@ erasable]
noeq type sn = { gr : GR.ref (list U32.t); }
instance ni_sn : Pulse.Lib.NonInformative.non_informative sn
  = { reveal = (fun r -> FStar.Ghost.reveal r) <: Pulse.Lib.NonInformative.revealer sn }

let scont (g:sn) (xs:list U32.t) : slprop = pts_to g.gr #0.5R xs

[@@ erasable]
noeq type tstack = { hd : B.box U32.t; nm : sn; inm : iname; }
instance ni_ts : Pulse.Lib.NonInformative.non_informative tstack
  = { reveal = (fun r -> FStar.Ghost.reveal r) <: Pulse.Lib.NonInformative.revealer tstack }

(** Invariant content is raw — no wrapper definition to unfold *)
let is_ts (s:tstack) (v:U32.t) (xs:list U32.t) : slprop =
  inv s.inm (B.pts_to s.hd v ** pts_to s.nm.gr #0.5R xs)

fn new_stack ()
  requires emp
  returns s : tstack
  ensures (exists* v xs. is_ts s v xs) ** scont s.nm []
{
  let hd = B.alloc 0ul;
  let gr = GR.alloc #(list U32.t) [];
  GR.share gr;
  let g : sn = { gr };
  let i = new_invariant (B.pts_to hd 0ul ** pts_to gr #0.5R []);
  let s : tstack = { hd; nm = g; inm = i };
  rewrite (inv i (B.pts_to hd 0ul ** pts_to gr #0.5R []))
       as (inv s.inm (B.pts_to s.hd 0ul ** pts_to s.nm.gr #0.5R []));
  fold (is_ts s 0ul []);
  rewrite (GR.pts_to gr #0.5R []) as (scont s.nm []);
  s
}

fn rec push_loop
    (s:tstack) (v:U32.t)
    (tok : au_token (list U32.t) unit
      (fun xs -> scont s.nm xs)
      (fun xs _ -> scont s.nm (Cons v xs))
      (fun xs _ -> scont s.nm (Cons v xs)))
    (cur_v:U32.t) (new_v:U32.t) (cur_xs:list U32.t)
  requires is_ts s cur_v (cur_xs) ** au_available tok
  ensures (exists* vv xxs. is_ts s vv xxs) **
          (exists* (xs:list U32.t) (_y:unit). scont s.nm (Cons v xs))
{
  later_credit_buy 1;
  later_credit_buy 1;

  let xs = au_open tok;
  unfold scont;

  unfold is_ts;
  // Now: inv s.inm (B.pts_to s.hd cur_v ** pts_to s.nm.gr #0.5R cur_xs)
  // No unfold needed inside with_invariants!

  let success =
    with_invariants bool emp_inames s.inm
      (B.pts_to s.hd cur_v ** pts_to s.nm.gr #0.5R (cur_xs))
      (pts_to s.nm.gr #0.5R (reveal xs) ** au_opened tok)
      (fun b -> P.cond b
        (pts_to s.nm.gr #0.5R (Cons v (reveal xs)) ** au_opened tok)
        (pts_to s.nm.gr #0.5R (reveal xs) ** au_opened tok))
    fn _ {
      // CAS first — no ghost steps before it
      let b = P.cas_box s.hd cur_v new_v;
      if b {
        elim_cond_true _ _ _;
        drop_ (pure (cur_v == cur_v));
        // Ghost steps after CAS
        GR.pts_to_injective_eq s.nm.gr;
        GR.gather s.nm.gr;
        GR.(s.nm.gr := Cons v (reveal xs));
        GR.share s.nm.gr;
        let ret = true;
        rewrite (pts_to s.nm.gr #0.5R (Cons v (reveal xs)) ** au_opened tok)
             as P.cond ret
                  (pts_to s.nm.gr #0.5R (Cons v (reveal xs)) ** au_opened tok)
                  (pts_to s.nm.gr #0.5R (reveal xs) ** au_opened tok);
        ret
      } else {
        elim_cond_false _ _ _;
        let ret = false;
        rewrite (pts_to s.nm.gr #0.5R (reveal xs) ** au_opened tok)
             as P.cond ret
                  (pts_to s.nm.gr #0.5R (Cons v (reveal xs)) ** au_opened tok)
                  (pts_to s.nm.gr #0.5R (reveal xs) ** au_opened tok);
        ret
      }
    };

  if (success) {
    elim_cond_true _ _ _;
    fold (scont s.nm (Cons v (reveal xs)));
    au_commit tok (reveal xs) (hide ()) fn _ { () };
    fold (is_ts s new_v (Cons v (cur_xs)));
  } else {
    elim_cond_false _ _ _;
    fold (scont s.nm (reveal xs));
    later_credit_buy 1;
    au_abort tok (reveal xs);
    fold (is_ts s cur_v (cur_xs));
    push_loop s v tok cur_v new_v #cur_xs
  }
}

fn push (s:tstack) (v:U32.t)
  requires (exists* vv xxs. is_ts s vv xxs) ** scont s.nm 'xs
  ensures (exists* vv xxs. is_ts s vv xxs) ** (exists* ys. scont s.nm ys)
{
  lat_elim #_ #_ #(fun xs -> scont s.nm xs)
           #(fun xs _ -> scont s.nm (Cons v xs))
           #(fun xs _ -> scont s.nm (Cons v xs))
           (hide 'xs)
    (fun tok -> push_loop s v tok 0ul 1ul)
}
