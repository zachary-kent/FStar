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
open Pulse.Lib.Trade
open Pulse.Lib.Forall
module GR = Pulse.Lib.GhostReference

(** Invariant content: when flag=true, holds α(x) AND the commit trade *)
let au_inv_p (is:inames) (a:Type0) (b:Type0) (alpha : a -> slprop) (beta : a -> b -> slprop)
    (phi : a -> b -> slprop) (gr : GR.ref bool) : slprop =
  exists* (flag:bool). pts_to gr #0.5R flag **
    (if flag then
       (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y)))
     else emp)

ghost fn fold_au_inv_p (is:inames) (a:Type0) (b:Type0) (alpha : a -> slprop) (beta : a -> b -> slprop)
    (phi : a -> b -> slprop) (gr : GR.ref bool) (#flag:bool)
  requires pts_to gr #0.5R flag **
    (if flag then (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) else emp)
  ensures au_inv_p is a b alpha beta phi gr
{ fold (au_inv_p is a b alpha beta phi gr) }

noeq type au_token (is:inames) (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop) = {
  gr : GR.ref bool;
  i : iname;
}

instance non_informative_au_token (is:inames) (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_token is a b alpha beta phi)
  = { reveal = (fun r -> Ghost.reveal r) <: NonInformative.revealer (au_token is a b alpha beta phi) }

let au_iname (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) : GTot iname = tok.i

let au_available (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) : slprop =
  pts_to tok.gr #0.5R true ** inv tok.i (au_inv_p is a b alpha beta phi tok.gr)

(** Handle carries the commit trade via the invariant *)
let au_opened (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) (x : a) : slprop =
  pts_to tok.gr #0.5R false **
  inv tok.i (au_inv_p is a b alpha beta phi tok.gr) **
  (forall* (y:b). trade #is (beta x y) (phi x y))

ghost fn au_intro (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
  requires alpha (reveal x0) ** (forall* (y:b). trade #is (beta (reveal x0) y) (phi (reveal x0) y))
  returns tok : au_token is a b alpha beta phi
  ensures au_available tok
{
  let gr = GR.alloc true;
  GR.share gr;
  fold (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y)));
  rewrite (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y)))
       as (if true then (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) else emp);
  fold_au_inv_p is a b alpha beta phi gr;
  let i = new_invariant (au_inv_p is a b alpha beta phi gr);
  let tok : au_token is a b alpha beta phi = { gr; i };
  rewrite (pts_to gr #0.5R true) as (pts_to tok.gr #0.5R true);
  rewrite (inv i (au_inv_p is a b alpha beta phi gr))
       as (inv tok.i (au_inv_p is a b alpha beta phi tok.gr));
  fold (au_available tok);
  tok
}

ghost fn au_open (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi)
  opens [au_iname tok]
  requires au_available tok ** later_credit 1
  returns x : erased a
  ensures alpha (reveal x) ** au_opened tok (reveal x)
{
  open GR;
  unfold au_available;
  with_invariants_g unit emp_inames tok.i (au_inv_p is a b alpha beta phi tok.gr)
    (pts_to tok.gr #0.5R true)
    (fun _ -> (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) ** pts_to tok.gr #0.5R false)
  fn _ {
    unfold au_inv_p;
    with bv. assert (pts_to tok.gr #0.5R bv ** pts_to tok.gr #0.5R true);
    GR.gather tok.gr #true #_;
    rewrite each bv as true;
    rewrite (if true then (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) else emp)
         as (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y)));
    tok.gr := false;
    GR.share tok.gr;
    rewrite emp as (if false then (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) else emp);
    fold_au_inv_p is a b alpha beta phi tok.gr;
  };
  // Unpack: ∃x. alpha x ** forall* y. trade
  let x = elim_exists #a (fun (x:a) -> alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y)));
  fold (au_opened tok (reveal x));
  x
}

ghost fn au_abort (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi) (x : erased a)
  opens [au_iname tok]
  requires alpha (reveal x) ** au_opened tok (reveal x) ** later_credit 1
  ensures au_available tok
{
  open GR;
  unfold (au_opened tok (reveal x));
  // Repack alpha + trade into existential
  fold (exists* (xx:a). alpha xx ** (forall* (y:b). trade #is (beta xx y) (phi xx y)));
  with_invariants_g unit emp_inames tok.i (au_inv_p is a b alpha beta phi tok.gr)
    ((exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) ** pts_to tok.gr #0.5R false)
    (fun _ -> pts_to tok.gr #0.5R true)
  fn _ {
    unfold au_inv_p;
    with bv. assert (pts_to tok.gr #0.5R bv ** pts_to tok.gr #0.5R false);
    GR.gather tok.gr #false #_;
    rewrite each bv as false;
    rewrite (if false then (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) else emp) as emp;
    drop_ emp;
    tok.gr := true;
    GR.share tok.gr;
    rewrite (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y)))
         as (if true then (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) else emp);
    fold_au_inv_p is a b alpha beta phi tok.gr;
  };
  fold (au_available tok)
}

ghost fn au_commit (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token is a b alpha beta phi)
    (x : erased a) (y : b)
  opens is
  requires beta (reveal x) y ** au_opened tok (reveal x)
  ensures phi (reveal x) y
{
  unfold (au_opened tok (reveal x));
  // Use the stored trade: elim_forall y, then elim_trade
  elim_forall y;
  elim_trade #is (beta (reveal x) y) (phi (reveal x) y);
  // Drop the AU remnants
  drop_ (pts_to tok.gr #0.5R false);
  drop_ (inv tok.i (au_inv_p is a b alpha beta phi tok.gr))
}

fn lat_elim (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token is a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
  requires alpha (reveal x0) ** (forall* (y:b). trade #is (beta (reveal x0) y) (phi (reveal x0) y))
  ensures (exists* (x:a) (y:b). phi x y)
{
  let tok = au_intro #is #a #b #alpha #beta #phi x0;
  f tok
}

fn lat_open (#is:inames) (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#result : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token is a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
    (split_phi : (x:erased a) -> (y:erased b) ->
      stt_ghost unit emp_inames
        (phi (reveal x) (reveal y))
        (fun _ -> (exists* (x':a). alpha x' ** (forall* (yy:b). trade #is (beta x' yy) (phi x' yy))) ** result (reveal x) (reveal y)))
  requires alpha (reveal x0) ** (forall* (y:b). trade #is (beta (reveal x0) y) (phi (reveal x0) y))
  ensures (exists* (x:a). alpha x ** (forall* (y:b). trade #is (beta x y) (phi x y))) ** (exists* (x:a) (y:b). result x y)
{
  let tok = au_intro #is #a #b #alpha #beta #phi x0;
  f tok;
  let x = elim_exists #a (fun (x:a) -> exists* (y:b). phi x y);
  let y = elim_exists #b (fun (y:b) -> phi (reveal x) y);
  split_phi x y;
}
