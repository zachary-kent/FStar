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

(**
  Logical Atomicity for Pulse.

  The AU stores its commit continuation internally as a trade (magic wand):
    forall* y. beta(x,y) @==> phi(x,y)
  This matches Iris's AU definition where the commit branch
    ∀y. β(x,y) ={Ei,Eo}=∗ Φ(x,y)
  is part of the AU itself (atomic.v line 25-27).

  au_commit needs NO external cfn — it uses the stored trade.
*)

module Pulse.Lib.LogicalAtomicity
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
open Pulse.Lib.Forall
module GR = Pulse.Lib.GhostReference

[@@ erasable]
val au_token (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop) : Type0

instance val non_informative_au_token (a:Type0) (b:Type0)
    (alpha : a -> slprop) (beta : a -> b -> slprop) (phi : a -> b -> slprop)
  : NonInformative.non_informative (au_token a b alpha beta phi)

val au_iname (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : GTot iname

val au_available (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) : slprop

val au_opened (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) (x : a) : slprop

(** Introduction: deposit α(x₀) AND the commit contract ∀y. β(x₀,y) @==> Φ(x₀,y).
    Iris aupd_intro (line 276): the AU stores its postcondition contract. *)
ghost fn au_intro (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
  requires alpha (reveal x0) ** (forall* (y:b). beta (reveal x0) y @==> phi (reveal x0) y)
  returns tok : au_token a b alpha beta phi
  ensures au_available tok

(** Open: extract α(x). The commit contract stays in the handle.
    Iris aupd_aacc (line 253). *)
ghost fn au_open (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
  opens [au_iname tok]
  requires au_available tok ** later_credit 1
  returns x : erased a
  ensures alpha (reveal x) ** au_opened tok (reveal x)

(** Abort: return α(x), recover AU. Iris aupd_aacc abort branch. *)
ghost fn au_abort (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi) (x : erased a)
  opens [au_iname tok]
  requires alpha (reveal x) ** au_opened tok (reveal x) ** later_credit 1
  ensures au_available tok

(** Commit: provide β(x,y), get Φ(x,y). NO cfn needed — uses stored trade.
    Iris aupd_aacc commit branch (line 25): ∀y. β(x,y) ={Ei,Eo}=∗ Φ(x,y). *)
ghost fn au_commit (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (tok : au_token a b alpha beta phi)
    (x : erased a) (y : b)
  requires beta (reveal x) y ** au_opened tok (reveal x)
  ensures phi (reveal x) y

(** lat_elim, lat_open, lat_open_gen as before *)

fn lat_elim (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
  requires alpha (reveal x0) ** (forall* (y:b). beta (reveal x0) y @==> phi (reveal x0) y)
  ensures (exists* (x:a) (y:b). phi x y)

fn lat_open (#a:Type0) (#b:Type0)
    (#alpha : a -> slprop) (#beta : a -> b -> slprop) (#phi : a -> b -> slprop)
    (#result : a -> b -> slprop)
    (x0 : erased a)
    (f : (tok : au_token a b alpha beta phi) ->
      stt unit (au_available tok) (fun _ -> exists* (x:a) (y:b). phi x y))
    (split_phi : (x:erased a) -> (y:erased b) ->
      stt_ghost unit emp_inames
        (phi (reveal x) (reveal y))
        (fun _ -> (exists* (x':a). alpha x' ** (forall* (yy:b). beta x' yy @==> phi x' yy)) ** result (reveal x) (reveal y)))
  requires alpha (reveal x0) ** (forall* (y:b). beta (reveal x0) y @==> phi (reveal x0) y)
  ensures (exists* (x:a). alpha x ** (forall* (y:b). beta x y @==> phi x y)) ** (exists* (x:a) (y:b). result x y)
