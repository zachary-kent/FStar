(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** PulseTutorial.SeqlockWf — phase-1 skeleton for the wait-free seqlock port. *)
module PulseTutorial.SeqlockWf
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.SeqlockHistory
open Pulse.Lib.MonotonicGhostRef
open Pulse.Lib.Inv
module A = Pulse.Lib.Array.PtsTo
module Arr = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module MGR = Pulse.Lib.MonotonicGhostRef
module Reg = Pulse.Lib.SeqlockWfRegistry
module Trade = Pulse.Lib.Trade
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module List = FStar.List.Tot
module SZ = FStar.SizeT
open FStar.List.Tot { (@) }

let prop_as_bool = FStar.IndefiniteDescription.strong_excluded_middle

(* The element type.  We keep it concrete in this tutorial port. *)
type val_t = int

(* The big_atomic handle: (version_cell, data_array). *)
type big_atomic = ref nat & array val_t

(* Public value ghost name, mirroring Iris's ghost_var γ over list val. *)
type gamma_value_t = GR.ref (list val_t)

(* Invariant namespace tags for documentation. *)
let seqlockN_tag : string = "PulseTutorial.SeqlockWf.seqlock"
let writeN_tag : string = "PulseTutorial.SeqlockWf.write"

(* [history] is list-based, while Pulse array ownership is sequence-based. *)
let snapshot_of_seq (s:Seq.seq val_t) : list val_t = Seq.seq_to_list s
let seq_of_snapshot (vs:list val_t) : Seq.seq val_t = Seq.seq_of_list vs

(* The wait-free port follows Iris's final-store write LP, so the committed
   history length is uniformly 1 + ver/2, including the odd locked state. *)
let history_len_for_version (ver:nat) : nat = 1 + ver / 2

let rec last_opt (#a:Type0) (xs:list a) : Tot (option a) =
  match xs with
  | [] -> None
  | x::[] -> Some x
  | _::tl -> last_opt tl

let rec last_opt_snoc (#a:Type0) (xs:list a) (x:a)
  : Lemma (last_opt (xs @ [x]) == Some x)
  = match xs with
    | [] -> ()
    | _::tl -> last_opt_snoc tl x

(* Monotone ghost reference for natural versions. *)
let mono_nat_increases : FStar.Preorder.preorder nat = fun (x:nat) (y:nat) -> b2t (x <= y)

let mono_nat_auth (gver:MGR.mref mono_nat_increases) (q:perm) (ver:nat) : slprop =
  MGR.pts_to gver #q ver

let mono_nat_lb (gver:MGR.mref mono_nat_increases) (ver:nat) : slprop =
  MGR.snapshot #nat #mono_nat_increases gver ver

ghost fn mono_nat_lb_get (gver:MGR.mref mono_nat_increases) (#q:perm) (#ver:nat)
  preserves mono_nat_auth gver q ver
  ensures mono_nat_lb gver ver
{
  unfold (mono_nat_auth gver q ver);
  MGR.take_snapshot #nat #mono_nat_increases gver #q ver;
  fold (mono_nat_auth gver q ver);
  fold (mono_nat_lb gver ver)
}

ghost fn mono_nat_lb_valid (gver:MGR.mref mono_nat_increases) (#q:perm) (#ver #lb:nat)
  preserves mono_nat_auth gver q ver
  preserves mono_nat_lb gver lb
  ensures pure (lb <= ver)
{
  unfold (mono_nat_auth gver q ver);
  unfold (mono_nat_lb gver lb);
  MGR.recall_snapshot #nat #mono_nat_increases gver #q #ver #lb;
  fold (mono_nat_auth gver q ver);
  fold (mono_nat_lb gver lb)
}

ghost fn mono_nat_auth_auth_agree (gver:MGR.mref mono_nat_increases)
    (#q1 #q2:perm) (#v1 #v2:nat)
  preserves mono_nat_auth gver q1 v1 ** mono_nat_auth gver q2 v2
  ensures pure (v1 == v2)
{
  unfold (mono_nat_auth gver q1 v1);
  unfold (mono_nat_auth gver q2 v2);
  MGR.take_snapshot #nat #mono_nat_increases gver #q1 v1;
  MGR.take_snapshot #nat #mono_nat_increases gver #q2 v2;
  MGR.recall_snapshot #nat #mono_nat_increases gver #q2 #v2 #v1;
  MGR.recall_snapshot #nat #mono_nat_increases gver #q1 #v1 #v2;
  assert (pure (v1 <= v2));
  assert (pure (v2 <= v1));
  assert (pure (v1 == v2));
  fold (mono_nat_auth gver q1 v1);
  fold (mono_nat_auth gver q2 v2)
}

ghost fn mono_nat_update (gver:MGR.mref mono_nat_increases) (#old:nat) (newv:nat)
  requires mono_nat_auth gver 1.0R old ** pure (old <= newv)
  ensures mono_nat_auth gver 1.0R newv
{
  unfold (mono_nat_auth gver 1.0R old);
  MGR.update #nat #mono_nat_increases gver #old newv;
  fold (mono_nat_auth gver 1.0R newv)
}

ghost fn mono_nat_gather (gver:MGR.mref mono_nat_increases)
    (#q1 #q2:perm) (#v1 #v2:nat)
  requires mono_nat_auth gver q1 v1 ** mono_nat_auth gver q2 v2
  ensures mono_nat_auth gver (q1 +. q2) v1 ** pure (v1 == v2)
{
  mono_nat_auth_auth_agree gver #q1 #q2 #v1 #v2;
  rewrite each v2 as v1;
  unfold (mono_nat_auth gver q1 v1);
  unfold (mono_nat_auth gver q2 v1);
  MGR.gather #nat #mono_nat_increases gver #v1 #q1 #q2;
  fold (mono_nat_auth gver (q1 +. q2) v1)
}

let rec last_opt_nth_length (#a:Type0) (xs:list a)
  : Lemma
      (requires List.length xs > 0)
      (ensures List.nth xs (List.length xs - 1) == last_opt xs)
  = match xs with
    | [] -> ()
    | _::[] -> ()
    | _::tl -> last_opt_nth_length tl

let last_opt_nth (#a:Type0) (xs:list a) (i:nat) (v:a)
  : Lemma
      (requires List.length xs == 1 + i /\ last_opt xs == Some v)
      (ensures List.nth xs i == Some v)
  = last_opt_nth_length xs;
    assert (i == List.length xs - 1)

let rec nth_index_some (#a:Type0) (xs:list a) (i:nat{i < List.length xs})
  : Lemma (List.nth xs i == Some (List.index xs i))
  = match xs with
    | [] -> ()
    | _::tl -> if i = 0 then () else nth_index_some tl (i - 1)

let seq_of_snapshot_nth (vs:list val_t) (i:nat{i < List.length vs})
  : Lemma (List.nth vs i == Some (Seq.index (seq_of_snapshot vs) i))
  = SeqP.lemma_seq_of_list_index vs i;
    nth_index_some vs i

let t2b_true_of_prop (p:prop)
  : Lemma (requires p) (ensures Prims.t2b p == true)
  = ()

let t2b_false_of_not (p:prop)
  : Lemma (requires ~p) (ensures Prims.t2b p == false)
  = ()

ghost fn intro_cond_true_b (b:bool) (p q:slprop)
  requires p
  requires pure (b == true)
  ensures (if b then p else q)
{
  rewrite p as (if b then p else q)
}

ghost fn intro_cond_false_b (b:bool) (p q:slprop)
  requires q
  requires pure (b == false)
  ensures (if b then p else q)
{
  rewrite q as (if b then p else q)
}

ghost fn elim_if_true_b (b:bool) (p q:slprop)
  requires (if b then p else q)
  requires pure (b == true)
  ensures p
{
  rewrite (if b then p else q) as p
}

ghost fn elim_if_false_b (b:bool) (p q:slprop)
  requires (if b then p else q)
  requires pure (b == false)
  ensures q
{
  rewrite (if b then p else q) as q
}

(* Client-visible abstract value: half of the ghost variable. *)
let value_auth (g:gamma_value_t) (vs:list val_t) : slprop =
  GR.pts_to g #(1.0R /. 2.0R) vs

let value (g:gamma_value_t) (vs:list val_t) : slprop =
  value_auth g vs

(* Per-request linearization ghost: the registry stores the actual
   half-fractional boolean ghost variable name used by request_inv/write_inv. *)
let lin_ghost_var (gamma_l:Reg.lin_gname) (b:bool) : slprop =
  GR.pts_to gamma_l #(1.0R /. 2.0R) b

let request_live_bit (tracked_ver:nat) (request_ver:nat) : GTot bool =
  prop_as_bool (tracked_ver < request_ver)

type write_post_t = unit -> slprop

let source_points_to (src:array val_t) (dq:perm) (vs:list val_t) : slprop =
  A.pts_to src #dq (seq_of_snapshot vs)

let write_commit_cont (src:array val_t) (dq:perm) (vs:list val_t)
                      (phi:write_post_t) : slprop =
  Trade.trade #emp_inames (source_points_to src dq vs) (phi ())

let au_write (phi:write_post_t) (g:gamma_value_t) (vs_new:list val_t)
             (src:array val_t) (dq:perm) : slprop =
  exists* (tok:au_token emp_inames (list val_t) unit
            (fun (vs_old:list val_t) -> value g vs_old)
            (fun (_old:list val_t) (_u:unit) -> value g vs_new)
            (fun (_old:list val_t) (_u:unit) -> write_commit_cont src dq vs_new phi)).
    au_available tok

type write_lifecycle =
  | WriteLinearized
  | WritePending
  | WriteReturned

type request_token_t = GR.ref bool

let request_token (gamma_t:request_token_t) : slprop =
  GR.pts_to gamma_t #1.0R true

let write_inv_state (phi:write_post_t) (g:gamma_value_t) (gamma_l:Reg.lin_gname)
                    (gamma_t:request_token_t) (src:array val_t) (dq:perm)
                    (vs_new:list val_t) (state:write_lifecycle) : slprop =
  match state with
  | WriteLinearized ->
      write_commit_cont src dq vs_new phi ** lin_ghost_var gamma_l false
  | WritePending ->
      later_credit 1 ** au_write phi g vs_new src dq ** lin_ghost_var gamma_l true
  | WriteReturned ->
      request_token gamma_t ** exists* (b:bool). lin_ghost_var gamma_l b

let write_inv (phi:write_post_t) (g:gamma_value_t) (gamma_l:Reg.lin_gname)
              (gamma_t:request_token_t) (src:array val_t) (dq:perm)
              (vs_new:list val_t) : slprop =
  exists* (state:write_lifecycle).
    write_inv_state phi g gamma_l gamma_t src dq vs_new state

let request_inv (g:gamma_value_t) (tracked_ver:nat) (request:Reg.request) : slprop =
  let gamma_l = fst request in
  let request_ver = snd request in
  lin_ghost_var gamma_l (request_live_bit tracked_ver request_ver) **
  exists* (phi:write_post_t) (gamma_t:request_token_t) (src:array val_t)
          (dq:perm) (vs_new:list val_t) (i:iname).
    inv i (write_inv phi g gamma_l gamma_t src dq vs_new)

let rec registry_inv (g:gamma_value_t) (tracked_ver:nat) (requests:Reg.registry) : slprop =
  match requests with
  | [] -> emp
  | request::tl -> request_inv g tracked_ver request ** registry_inv g tracked_ver tl

(* The big invariant content: conditional on parity of the physical version. *)
let seqlock_inv_body (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
                (gr:Reg.reg_gname) (g:gamma_value_t)
                (version:ref nat) (data:array val_t) (len:nat)
                (ver:nat) (h:history val_t) (vs:list val_t) (requests:Reg.registry)
  : slprop =
  version |-> ver **
  Reg.registry_auth gr 1.0R requests **
  registry_inv g (ver / 2) requests **
  pure (List.length vs == len /\ List.length h == history_len_for_version ver) **
  (if ver % 2 == 0 then
     value_auth g vs **
     history_auth gh 1.0R h **
     mono_nat_auth gver 1.0R ver **
     A.pts_to data (seq_of_snapshot vs) **
     pure (last_opt h == Some vs)
   else
     history_auth gh (1.0R /. 2.0R) h **
     mono_nat_auth gver (1.0R /. 2.0R) ver **
     A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs))

let seqlock_inv (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
                (gr:Reg.reg_gname) (g:gamma_value_t)
                (version:ref nat) (data:array val_t) (len:nat)
  : slprop =
  exists* (ver:nat) (h:history val_t) (vs:list val_t) (requests:Reg.registry).
    seqlock_inv_body gver gh gr g version data len ver h vs requests

(* Public predicate: hides the version, history, registry, and invariant names. *)
let is_seqlock (v:big_atomic) (g:gamma_value_t) (n:nat) : slprop =
  exists* (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
          (gr:Reg.reg_gname) (i:iname).
    inv i (seqlock_inv gver gh gr g (fst v) (snd v) n)

ghost fn pack_seqlock_inv_even (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (gr:Reg.reg_gname) (g:gamma_value_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t) (#requests:Reg.registry)
  requires
    pure (ver % 2 == 0) **
    version |-> ver **
    Reg.registry_auth gr 1.0R requests **
    registry_inv g (ver / 2) requests **
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
    value_auth g vs **
    history_auth gh 1.0R h **
    mono_nat_auth gver 1.0R ver **
    A.pts_to data (seq_of_snapshot vs) **
    pure (last_opt h == Some vs)
  ensures seqlock_inv gver gh gr g version data n
{
  t2b_true_of_prop (ver % 2 == 0);
  assert (pure (Prims.t2b (ver % 2 == 0) == true));
  intro_pure (last_opt h == Some vs) ();
  intro_cond_true_b (Prims.t2b (ver % 2 == 0))
    (value_auth g vs **
     history_auth gh 1.0R h **
     mono_nat_auth gver 1.0R ver **
     A.pts_to data (seq_of_snapshot vs) **
     pure (last_opt h == Some vs))
    (history_auth gh (1.0R /. 2.0R) h **
     mono_nat_auth gver (1.0R /. 2.0R) ver **
     A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
  fold (seqlock_inv_body gver gh gr g version data n ver h vs requests);
  fold (seqlock_inv gver gh gr g version data n)
}

ghost fn pack_seqlock_inv_odd (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (gr:Reg.reg_gname) (g:gamma_value_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t) (#requests:Reg.registry)
  requires
    pure (ver % 2 <> 0) **
    version |-> ver **
    Reg.registry_auth gr 1.0R requests **
    registry_inv g (ver / 2) requests **
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
    history_auth gh (1.0R /. 2.0R) h **
    mono_nat_auth gver (1.0R /. 2.0R) ver **
    A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs)
  ensures seqlock_inv gver gh gr g version data n
{
  t2b_false_of_not (ver % 2 == 0);
  assert (pure (Prims.t2b (ver % 2 == 0) == false));
  intro_cond_false_b (Prims.t2b (ver % 2 == 0))
    (value_auth g vs **
     history_auth gh 1.0R h **
     mono_nat_auth gver 1.0R ver **
     A.pts_to data (seq_of_snapshot vs) **
     pure (last_opt h == Some vs))
    (history_auth gh (1.0R /. 2.0R) h **
     mono_nat_auth gver (1.0R /. 2.0R) ver **
     A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
  fold (seqlock_inv_body gver gh gr g version data n ver h vs requests);
  fold (seqlock_inv gver gh gr g version data n)
}

fn new_big_atomic (n:SZ.t) (src:larray val_t (SZ.v n)) (#dq:perm)
    (#vs:erased (Seq.seq val_t))
  requires A.pts_to src #dq vs ** pure (Seq.length vs == SZ.v n /\ SZ.v n > 0)
  returns r : (big_atomic & gamma_value_t)
  ensures
    A.pts_to src #dq vs **
    is_seqlock (fst r) (snd r) (SZ.v n) **
    value (snd r) (snapshot_of_seq (reveal vs))
{
  let version = Pulse.Lib.Reference.alloc #nat 0;
  let data = A.alloc #val_t 0 n;
  Arr.memcpy n src data;

  let snap : erased (list val_t) = hide (snapshot_of_seq (reveal vs));
  let h0 : erased (history val_t) = hide [reveal snap];
  let gh = history_alloc (reveal h0);

  let g = GR.alloc #(list val_t) (reveal snap);
  GR.share g;

  let gr = Reg.registry_alloc ();
  let gver = MGR.alloc #nat #mono_nat_increases 0;

  Seq.lemma_seq_of_seq_to_list (reveal vs);
  rewrite (A.pts_to data (reveal vs)) as (A.pts_to data (seq_of_snapshot (reveal snap)));

  fold (value_auth g (reveal snap));
  fold (value g (reveal snap));
  fold (value_auth g (reveal snap));
  fold (mono_nat_auth gver 1.0R 0);
  fold (registry_inv g 0 []);
  pack_seqlock_inv_even gver gh gr g version data (SZ.v n) #0 #(reveal h0) #(reveal snap) #[];
  let i = new_invariant (seqlock_inv gver gh gr g version data (SZ.v n));
  let handle : big_atomic = (version, data);
  rewrite (inv i (seqlock_inv gver gh gr g version data (SZ.v n)))
    as (inv i (seqlock_inv gver gh gr g (fst handle) (snd handle) (SZ.v n)));
  fold (is_seqlock handle g (SZ.v n));
  rewrite (value g (reveal snap)) as (value g (snapshot_of_seq (reveal vs)));
  (handle, g)
}

fn version_read_impl (version:ref nat) (#p:perm) (#ver:erased nat)
  preserves version |-> Frac p ver
  returns r:nat
  ensures pure (r == reveal ver)
{
  !version
}

let version_read_atomic (version:ref nat) (#p:perm) (#ver:erased nat) =
  Pulse.Lib.Core.as_atomic _ _ (version_read_impl version #p #ver)

ghost fn loop_read_close (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (gr:Reg.reg_gname) (g:gamma_value_t)
    (version:ref nat) (data:array val_t) (n:nat)
    (#lb:nat) (#curr:nat) (#h:history val_t) (#vs:list val_t) (#requests:Reg.registry)
  requires seqlock_inv_body gver gh gr g version data n curr h vs requests **
           mono_nat_lb gver lb
  ensures seqlock_inv gver gh gr g version data n **
          mono_nat_lb gver lb ** mono_nat_lb gver curr ** pure (lb <= curr)
{
  unfold (seqlock_inv_body gver gh gr g version data n curr h vs requests);
  let b = prop_as_bool (curr % 2 == 0);
  if b {
    t2b_true_of_prop (curr % 2 == 0);
    assert (pure (Prims.t2b (curr % 2 == 0) == true));
    elim_if_true_b (Prims.t2b (curr % 2 == 0))
      (value_auth g vs **
       history_auth gh 1.0R h **
       mono_nat_auth gver 1.0R curr **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) curr **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    mono_nat_lb_valid gver #1.0R #curr #lb;
    mono_nat_lb_get gver #1.0R #curr;
    intro_pure (last_opt h == Some vs) ();
    pack_seqlock_inv_even gver gh gr g version data n #curr #h #vs #requests
  } else {
    t2b_false_of_not (curr % 2 == 0);
    assert (pure (Prims.t2b (curr % 2 == 0) == false));
    elim_if_false_b (Prims.t2b (curr % 2 == 0))
      (value_auth g vs **
       history_auth gh 1.0R h **
       mono_nat_auth gver 1.0R curr **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) curr **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    mono_nat_lb_valid gver #(1.0R /. 2.0R) #curr #lb;
    mono_nat_lb_get gver #(1.0R /. 2.0R) #curr;
    pack_seqlock_inv_odd gver gh gr g version data n #curr #h #vs #requests
  }
}

fn loop_read_step
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat) (lb:nat)
  requires inv n_inv (seqlock_inv gver gh gr g version data n) ** mono_nat_lb gver lb
  returns curr:nat
  ensures inv n_inv (seqlock_inv gver gh gr g version data n) **
          mono_nat_lb gver lb ** mono_nat_lb gver curr ** pure (lb <= curr)
{
  let curr = with_invariants nat emp_inames n_inv (seqlock_inv gver gh gr g version data n)
    (mono_nat_lb gver lb)
    (fun r -> mono_nat_lb gver lb ** mono_nat_lb gver r ** pure (lb <= r))
  fn _ {
    unfold (seqlock_inv gver gh gr g version data n);
    with curr h vs requests. _;
    unfold (seqlock_inv_body gver gh gr g version data n curr h vs requests);
    let r = version_read_atomic version #1.0R #(hide curr);
    assert (pure (r == curr));
    fold (seqlock_inv_body gver gh gr g version data n curr h vs requests);
    loop_read_close gver gh gr g version data n #lb #curr #h #vs #requests;
    rewrite (mono_nat_lb gver curr) as (mono_nat_lb gver r);
    r
  };
  curr
}

fn rec loop_while
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat) (v:nat)
  requires inv n_inv (seqlock_inv gver gh gr g version data n) ** mono_nat_lb gver v
  ensures inv n_inv (seqlock_inv gver gh gr g version data n) **
          (exists* (ver':nat). pure (v < ver') ** mono_nat_lb gver ver')
{
  let curr = loop_read_step #gver #gh #gr #g #n_inv version data n v;
  if (curr = v) {
    rewrite each curr as v;
    drop_ (mono_nat_lb gver v);
    loop_while #gver #gh #gr #g #n_inv version data n v
  } else {
    assert (pure (v < curr));
    drop_ (mono_nat_lb gver v);
    intro_pure (v < curr) ();
    intro_exists #nat (fun ver' -> pure (v < ver') ** mono_nat_lb gver ver') curr
  }
}
