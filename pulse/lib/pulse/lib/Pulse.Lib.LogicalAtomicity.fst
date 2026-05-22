(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Inv
module GR = Pulse.Lib.GhostReference

let au_inv_p (a:Type0) (alpha : a -> slprop) (gr : GR.ref bool) : slprop =
  exists* (b:bool). pts_to gr #0.5R b ** (if b then (exists* (x:a). alpha x) else emp)

ghost fn fold_au_inv_p (a:Type0) (alpha : a -> slprop) (gr : GR.ref bool) (#b:bool)
  requires pts_to gr #0.5R b ** (if b then (exists* (x:a). alpha x) else emp)
  ensures au_inv_p a alpha gr
{ fold (au_inv_p a alpha gr) }

noeq type au_token (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop) = {
  gr : GR.ref bool;
  i : iname;
}

instance non_informative_au_token (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_token a b alpha beta phi)
  = { reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (au_token a b alpha beta phi) }

let au_iname (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : GTot iname = tok.i

let au_available (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : slprop =
  pts_to tok.gr #0.5R true ** inv tok.i (au_inv_p a alpha tok.gr)

let au_opened (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : slprop =
  pts_to tok.gr #0.5R false ** inv tok.i (au_inv_p a alpha tok.gr)

ghost fn au_intro (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
  requires alpha (reveal x0)
  returns tok : au_token a b alpha beta phi
  ensures au_available tok
{
  let gr = GR.alloc true;
  GR.share gr;
  fold (exists* (x:a). alpha x);
  rewrite (exists* (x:a). alpha x) as (if true then (exists* (x:a). alpha x) else emp);
  fold_au_inv_p a alpha gr;
  let i = new_invariant (au_inv_p a alpha gr);
  let tok : au_token a b alpha beta phi = { gr; i };
  rewrite (pts_to gr #0.5R true) as (pts_to tok.gr #0.5R true);
  rewrite (inv i (au_inv_p a alpha gr)) as (inv tok.i (au_inv_p a alpha tok.gr));
  fold (au_available tok);
  tok
}

ghost fn au_open (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  opens [au_iname tok]
  requires au_available tok ** later_credit 1
  returns x : erased a
  ensures alpha (reveal x) ** au_opened tok
{
  open GR;
  unfold au_available;
  with_invariants_g unit emp_inames tok.i (au_inv_p a alpha tok.gr)
    (pts_to tok.gr #0.5R true)
    (fun _ -> (exists* (x:a). alpha x) ** pts_to tok.gr #0.5R false)
  fn _ {
    unfold au_inv_p;
    with bv. assert (pts_to tok.gr #0.5R bv ** pts_to tok.gr #0.5R true);
    GR.gather tok.gr #true #_;
    rewrite each bv as true;
    rewrite (if true then (exists* (x:a). alpha x) else emp) as (exists* (x:a). alpha x);
    tok.gr := false;
    GR.share tok.gr;
    rewrite emp as (if false then (exists* (x:a). alpha x) else emp);
    fold_au_inv_p a alpha tok.gr;
  };
  let x = elim_exists #a (fun (x:a) -> alpha x);
  fold (au_opened tok);
  x
}

ghost fn au_abort (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) (x : erased a)
  opens [au_iname tok]
  requires alpha (reveal x) ** au_opened tok ** later_credit 1
  ensures au_available tok
{
  open GR;
  unfold au_opened;
  with_invariants_g unit emp_inames tok.i (au_inv_p a alpha tok.gr)
    (alpha (reveal x) ** pts_to tok.gr #0.5R false)
    (fun _ -> pts_to tok.gr #0.5R true)
  fn _ {
    unfold au_inv_p;
    with bv. assert (pts_to tok.gr #0.5R bv ** pts_to tok.gr #0.5R false);
    GR.gather tok.gr #false #_;
    rewrite each bv as false;
    rewrite (if false then (exists* (x:a). alpha x) else emp) as emp;
    drop_ emp;
    tok.gr := true;
    GR.share tok.gr;
    fold (exists* (xx:a). alpha xx);
    rewrite (exists* (x:a). alpha x) as (if true then (exists* (x:a). alpha x) else emp);
    fold_au_inv_p a alpha tok.gr;
  };
  fold (au_available tok)
}

ghost fn au_commit (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
    (x : erased a) (y : erased b)
    (cfn : unit -> stt_ghost unit emp_inames
        (beta (reveal x) (reveal y))
        (fun _ -> phi (reveal x) (reveal y)))
  requires beta (reveal x) (reveal y) ** au_opened tok
  ensures phi (reveal x) (reveal y)
{
  cfn ();
  unfold au_opened;
  drop_ (pts_to tok.gr #0.5R false);
  drop_ (inv tok.i (au_inv_p a alpha tok.gr))
}

fn lat_elim (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
  requires alpha (reveal x0)
  ensures (exists* (x:a) (y:b). phi x y)
{
  let tok = au_intro #a #b #alpha #beta #phi x0;
  f tok
}

(** Iris aacc_aupd_commit (atomic.v line 387-400) *)
fn lat_open (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#result : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
    (split_phi : (x:erased a) -> (y:erased b) ->
      stt_ghost unit emp_inames
        (phi (reveal x) (reveal y))
        (fun _ -> (exists* (x':a). alpha x') ** result (reveal x) (reveal y)))
  requires alpha (reveal x0)
  ensures (exists* (x:a). alpha x) ** (exists* (x:a) (y:b). result x y)
{
  // Step 1: au_intro (Iris aupd_intro, atomic.v line 276)
  let tok = au_intro #a #b #alpha #beta #phi x0;

  // Step 2: Call f (Iris: inner aacc, atomic.v line 311)
  f tok;

  // Step 3: Split phi (Iris: commit wand Φ→Φ', atomic.v line 321-322)
  let x = elim_exists #a (fun (x:a) -> exists* (y:b). phi x y);
  let y = elim_exists #b (fun (y:b) -> phi (reveal x) y);
  split_phi x y;
}
