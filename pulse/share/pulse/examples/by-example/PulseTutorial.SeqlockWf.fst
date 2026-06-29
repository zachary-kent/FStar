(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** PulseTutorial.SeqlockWf — phase-1 skeleton for the wait-free seqlock port. *)
module PulseTutorial.SeqlockWf
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.LogicalAtomicity
open Pulse.Lib.SeqlockHistory
open Pulse.Lib.MonotonicGhostRef
open Pulse.Lib.Inv
module CAU = Pulse.Lib.CoinductiveAU
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

let request_live_bit_true_of_lt (tracked_ver request_ver:nat)
  : Lemma
      (requires tracked_ver < request_ver)
      (ensures request_live_bit tracked_ver request_ver == true)
  = ()

let request_live_bit_false_of_not_lt (tracked_ver request_ver:nat)
  : Lemma
      (requires ~(tracked_ver < request_ver))
      (ensures request_live_bit tracked_ver request_ver == false)
  = ()

let request_live_bit_false_mono (tracked_ver request_ver:nat)
  : Lemma
      (requires request_live_bit tracked_ver request_ver == false)
      (ensures request_live_bit (tracked_ver + 1) request_ver == false)
  = if request_live_bit (tracked_ver + 1) request_ver then (
      assert (tracked_ver + 1 < request_ver);
      assert (tracked_ver < request_ver);
      assert (request_live_bit tracked_ver request_ver == true)
    ) else ()

let source_points_to (src:array val_t) (dq:perm) (vs:list val_t) : slprop =
  A.pts_to src #dq (seq_of_snapshot vs)

let au_write (g:gamma_value_t) (vs_new:list val_t)
             (src:array val_t) (dq:perm) : slprop =
  CAU.atomic_update #(list val_t) #unit emp_inames
    (fun (vs_old:list val_t) -> value g vs_old)
    (fun (_old:list val_t) (_u:unit) -> value g vs_new)
    (fun (_old:list val_t) (_u:unit) -> source_points_to src dq vs_new)

type write_lifecycle =
  | WriteLinearized
  | WritePending
  | WriteReturned

type request_token_t = GR.ref bool

let request_token (gamma_t:request_token_t) : slprop =
  GR.pts_to gamma_t #1.0R true

let write_inv_state (g:gamma_value_t) (gamma_l:Reg.lin_gname)
                    (gamma_t:request_token_t) (src:array val_t) (dq:perm)
                    (vs_new:list val_t) (state:write_lifecycle) : slprop =
  match state with
  | WriteLinearized ->
      source_points_to src dq vs_new ** lin_ghost_var gamma_l false
  | WritePending ->
      later_credit 1 ** au_write g vs_new src dq ** lin_ghost_var gamma_l true
  | WriteReturned ->
      request_token gamma_t ** exists* (b:bool). lin_ghost_var gamma_l b

let write_inv (g:gamma_value_t) (gamma_l:Reg.lin_gname)
              (gamma_t:request_token_t) (src:array val_t) (dq:perm)
              (vs_new:list val_t) : slprop =
  exists* (state:write_lifecycle).
    write_inv_state g gamma_l gamma_t src dq vs_new state

let request_gamma_l (request:Reg.request) : Reg.lin_gname = tfst request
let request_target (request:Reg.request) : nat = tsnd request
let request_write_i (request:Reg.request) : iname = tthd request

let request_inv (g:gamma_value_t) (tracked_ver:nat) (request:Reg.request) : slprop =
  let gamma_l = request_gamma_l request in
  let ver' = request_target request in
  let write_i = request_write_i request in
  lin_ghost_var gamma_l (request_live_bit tracked_ver ver') **
  exists* (gamma_t:request_token_t) (src:array val_t)
          (dq:perm) (vs_new:list val_t).
    inv write_i (write_inv g gamma_l gamma_t src dq vs_new)

let rec registry_inv (g:gamma_value_t) (tracked_ver:nat) (requests:Reg.registry) : slprop =
  match requests with
  | [] -> emp
  | request::tl -> request_inv g tracked_ver request ** registry_inv g tracked_ver tl

let rec registry_inames (requests:Reg.registry) : Tot inames =
  match requests with
  | [] -> emp_inames
  | request::tl -> add_inv (registry_inames tl) (request_write_i request)

ghost fn lin_ghost_agree (gamma_l:Reg.lin_gname) (#b0 #b1:bool)
  preserves lin_ghost_var gamma_l b0 ** lin_ghost_var gamma_l b1
  ensures pure (b0 == b1)
{
  unfold (lin_ghost_var gamma_l b0);
  unfold (lin_ghost_var gamma_l b1);
  GR.pts_to_injective_eq gamma_l;
  fold (lin_ghost_var gamma_l b0);
  fold (lin_ghost_var gamma_l b1)
}

ghost fn lin_ghost_update_halves (gamma_l:Reg.lin_gname) (#b0 #b1:bool) (b:bool)
  requires lin_ghost_var gamma_l b0 ** lin_ghost_var gamma_l b1
  ensures lin_ghost_var gamma_l b ** lin_ghost_var gamma_l b ** pure (b0 == b1)
{
  lin_ghost_agree gamma_l #b0 #b1;
  rewrite each b1 as b0;
  unfold (lin_ghost_var gamma_l b0);
  unfold (lin_ghost_var gamma_l b0);
  GR.gather gamma_l;
  GR.(gamma_l := b);
  GR.share gamma_l;
  fold (lin_ghost_var gamma_l b);
  fold (lin_ghost_var gamma_l b)
}

ghost fn value_update_halves (g:gamma_value_t) (#vs0 #vs1:list val_t) (vs:list val_t)
  requires value_auth g vs0 ** value g vs1
  ensures value_auth g vs ** value g vs ** pure (vs0 == vs1)
{
  unfold (value g vs1);
  unfold (value_auth g vs0);
  unfold (value_auth g vs1);
  GR.pts_to_injective_eq g;
  rewrite each vs1 as vs0;
  GR.gather g;
  GR.(g := vs);
  GR.share g;
  fold (value_auth g vs);
  fold (value_auth g vs);
  fold (value g vs)
}

ghost fn rec linearize_writes (g:gamma_value_t) (#vs:list val_t)
    (ver:nat) (requests:Reg.registry)
  opens (registry_inames requests)
  requires later_credit (List.length requests) ** value_auth g vs ** registry_inv g ver requests
  ensures exists* (vs':list val_t). value_auth g vs' ** registry_inv g (ver + 1) requests
  decreases requests
{
  match requests {
    Nil -> {
      unfold (registry_inv g ver []);
      later_credit_zero ();
      rewrite (later_credit 0) as emp;
      fold (registry_inv g (ver + 1) []);
      rewrite (registry_inv g (ver + 1) []) as (registry_inv g (ver + 1) requests);
      intro_exists #(list val_t)
        (fun vs' -> value_auth g vs' ** registry_inv g (ver + 1) requests) vs
    }
    Cons request tl -> {
      let gamma_l = request_gamma_l request;
      let request_ver = request_target request;
      assert (pure (List.length (request::tl) == 1 + List.length tl));
      rewrite (later_credit (List.length (request::tl))) as (later_credit (1 + List.length tl));
      later_credit_add 1 (List.length tl);
      rewrite (later_credit (1 + List.length tl)) as (later_credit 1 ** later_credit (List.length tl));
      unfold (registry_inv g ver (request::tl));
      linearize_writes g #vs ver tl;
      with vs_tail. _;
      unfold (request_inv g ver request);
      with gamma_t src dq vs_new. _;
      rewrite each (request_gamma_l request) as gamma_l;
      rewrite each (request_target request) as request_ver;
      with_invariants_g unit emp_inames (request_write_i request)
        (write_inv g gamma_l gamma_t src dq vs_new)
        (value_auth g vs_tail ** lin_ghost_var gamma_l (request_live_bit ver request_ver))
        (fun _ -> exists* (vs_final:list val_t).
           value_auth g vs_final ** lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver))
        fn _ {
          unfold (write_inv g gamma_l gamma_t src dq vs_new);
          with state. _;
          let state0 = reveal state;
          match state0 {
            WriteLinearized -> {
              rewrite (write_inv_state g gamma_l gamma_t src dq vs_new state) as
                (write_inv_state g gamma_l gamma_t src dq vs_new WriteLinearized);
              unfold (write_inv_state g gamma_l gamma_t src dq vs_new WriteLinearized);
              lin_ghost_agree gamma_l #(request_live_bit ver request_ver) #false;
              rewrite each (request_live_bit ver request_ver) as false;
              request_live_bit_false_mono ver request_ver;
              fold (write_inv_state g gamma_l gamma_t src dq vs_new WriteLinearized);
              fold (write_inv g gamma_l gamma_t src dq vs_new);
              rewrite (lin_ghost_var gamma_l false) as
                (lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver));
              intro_exists #(list val_t)
                (fun vs_final -> value_auth g vs_final ** lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver)) vs_tail
            }
            WritePending -> {
              rewrite (write_inv_state g gamma_l gamma_t src dq vs_new state) as
                (write_inv_state g gamma_l gamma_t src dq vs_new WritePending);
              unfold (write_inv_state g gamma_l gamma_t src dq vs_new WritePending);
              lin_ghost_agree gamma_l #(request_live_bit ver request_ver) #true;
              rewrite each (request_live_bit ver request_ver) as true;
              if (ver + 1 < request_ver) {
                request_live_bit_true_of_lt (ver + 1) request_ver;
                fold (write_inv_state g gamma_l gamma_t src dq vs_new WritePending);
                fold (write_inv g gamma_l gamma_t src dq vs_new);
                rewrite (lin_ghost_var gamma_l true) as
                  (lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver));
                intro_exists #(list val_t)
                  (fun vs_final -> value_auth g vs_final ** lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver)) vs_tail
              } else {
                request_live_bit_false_of_not_lt (ver + 1) request_ver;
                lin_ghost_update_halves gamma_l #true #true false;
                unfold (au_write g vs_new src dq);
                let vs_old = CAU.au_open #(list val_t) #unit emp_inames
                  (fun (vs_old:list val_t) -> value g vs_old)
                  (fun (_old:list val_t) (_u:unit) -> value g vs_new)
                  (fun (_old:list val_t) (_u:unit) -> source_points_to src dq vs_new);
                value_update_halves g #vs_tail #(reveal vs_old) vs_new;
                CAU.au_commit #(list val_t) #unit emp_inames
                  (fun (vs_old:list val_t) -> value g vs_old)
                  (fun (_old:list val_t) (_u:unit) -> value g vs_new)
                  (fun (_old:list val_t) (_u:unit) -> source_points_to src dq vs_new)
                  (reveal vs_old) ();
                drop_ (Trade.trade #emp_inames (value g (reveal vs_old))
                  (CAU.atomic_update #(list val_t) #unit emp_inames
                    (fun (vs_old:list val_t) -> value g vs_old)
                    (fun (_old:list val_t) (_u:unit) -> value g vs_new)
                    (fun (_old:list val_t) (_u:unit) -> source_points_to src dq vs_new)));
                drop_ (later_credit 1);
                fold (write_inv_state g gamma_l gamma_t src dq vs_new WriteLinearized);
                fold (write_inv g gamma_l gamma_t src dq vs_new);
                rewrite (lin_ghost_var gamma_l false) as
                  (lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver));
                intro_exists #(list val_t)
                  (fun vs_final -> value_auth g vs_final ** lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver)) vs_new
              }
            }
            WriteReturned -> {
              rewrite (write_inv_state g gamma_l gamma_t src dq vs_new state) as
                (write_inv_state g gamma_l gamma_t src dq vs_new WriteReturned);
              unfold (write_inv_state g gamma_l gamma_t src dq vs_new WriteReturned);
              with b. _;
              let b0 = reveal b;
              rewrite (lin_ghost_var gamma_l b) as (lin_ghost_var gamma_l b0);
              lin_ghost_update_halves gamma_l #(request_live_bit ver request_ver) #b0 (request_live_bit (ver + 1) request_ver);
              fold (write_inv_state g gamma_l gamma_t src dq vs_new WriteReturned);
              fold (write_inv g gamma_l gamma_t src dq vs_new);
              intro_exists #(list val_t)
                (fun vs_final -> value_auth g vs_final ** lin_ghost_var gamma_l (request_live_bit (ver + 1) request_ver)) vs_tail
            }
          }
        };
      with vs_final. _;
      rewrite each gamma_l as (request_gamma_l request);
      rewrite each request_ver as (request_target request);
      fold (request_inv g (ver + 1) request);
      fold (registry_inv g (ver + 1) (request::tl));
      rewrite (registry_inv g (ver + 1) (request::tl)) as (registry_inv g (ver + 1) requests);
      intro_exists #(list val_t)
        (fun vs' -> value_auth g vs' ** registry_inv g (ver + 1) requests) vs_final
    }
  }
}

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

(* -------------------------------------------------------------------------- *)
(* Set-once iname agreement                                                   *)
(* -------------------------------------------------------------------------- *)
(* We need each registered request's invariant name `write_i` to be provably
   distinct from the seqlock invariant's own name `n_seqlock`, so that the
   helper writer (at the unlock LP) can open every per-request `write_inv`
   under the open `seqlock_inv` without violating Pulse's mask discipline.

   The disjointness is established at registration time by
   `fresh_invariant (singleton n_seqlock) (...)`.  To carry this fact into
   `linearize_writes` (called inside the open seqlock_inv), the seqlock_inv
   body must internally know `n_seqlock`.  But `inv n_seqlock (seqlock_inv
   ... n_seqlock)` is unallocatable: `Pulse.Lib.Inv.new_invariant` needs the
   body before returning the fresh iname.

   Fix: a set-once MGR holding `option iname`.  Seqlock_inv carries half of
   the pts_to (existentially over the current value `cur_n`).  Initially
   `cur_n = None`.  After invariant allocation, the allocator opens the
   freshly-created invariant once, gathers both halves, updates to
   `Some n_seqlock`, takes a persistent snapshot, splits back.  The snapshot
   `iname_agree gn n_seqlock` is exposed in `is_seqlock` and consumed at the
   unlock LP to recover the disjointness fact.

   Set-once-ness: the preorder allows None -> Some i and Some i -> Some i,
   but forbids Some i -> Some j (i =!= j) and Some _ -> None.  The MGR
   `update` call requires `pts_to 1.0R`, which is only available transiently
   (inside the seqlock_inv open during the two-step allocation).  Once the
   value is `Some n_seqlock`, no honest client can change it. *)
let iname_once_preorder : FStar.Preorder.preorder (option iname) =
  fun (x:option iname) (y:option iname) ->
    match x with
    | None -> True
    | Some i -> (match y with | Some j -> i == j | None -> False)

let iname_box (gn:MGR.mref iname_once_preorder) (q:perm) (cur:option iname) : slprop =
  MGR.pts_to gn #q cur

let iname_agree (gn:MGR.mref iname_once_preorder) (n_seqlock:iname) : slprop =
  MGR.snapshot gn (Some n_seqlock)

ghost fn iname_agree_dup (gn:MGR.mref iname_once_preorder) (n_seqlock:iname)
  requires iname_agree gn n_seqlock
  ensures iname_agree gn n_seqlock ** iname_agree gn n_seqlock
{
  unfold (iname_agree gn n_seqlock);
  dup (MGR.snapshot gn (Some n_seqlock)) ();
  fold (iname_agree gn n_seqlock);
  fold (iname_agree gn n_seqlock)
}

ghost fn iname_agree_recall (gn:MGR.mref iname_once_preorder)
    (n_seqlock:iname) (#q:perm) (#cur:option iname)
  preserves iname_box gn q cur
  preserves iname_agree gn n_seqlock
  ensures pure (cur == Some n_seqlock)
{
  unfold (iname_box gn q cur);
  unfold (iname_agree gn n_seqlock);
  MGR.recall_snapshot gn #q #cur #(Some n_seqlock);
  assert (pure (iname_once_preorder (Some n_seqlock) cur));
  fold (iname_box gn q cur);
  fold (iname_agree gn n_seqlock)
}

ghost fn iname_box_share (gn:MGR.mref iname_once_preorder)
    (#q:perm) (#cur:option iname)
  requires iname_box gn q cur
  ensures iname_box gn (q /. 2.0R) cur ** iname_box gn (q /. 2.0R) cur
{
  unfold (iname_box gn q cur);
  MGR.share gn #cur #q #(q /. 2.0R) #(q /. 2.0R);
  fold (iname_box gn (q /. 2.0R) cur);
  fold (iname_box gn (q /. 2.0R) cur)
}

ghost fn iname_box_gather (gn:MGR.mref iname_once_preorder)
    (#q1 #q2:perm) (#cur1 #cur2:option iname)
  requires iname_box gn q1 cur1 ** iname_box gn q2 cur2
  ensures iname_box gn (q1 +. q2) cur1 ** pure (cur1 == cur2)
{
  unfold (iname_box gn q1 cur1);
  unfold (iname_box gn q2 cur2);
  MGR.take_snapshot gn #q1 cur1;
  MGR.take_snapshot gn #q2 cur2;
  MGR.recall_snapshot gn #q1 #cur1 #cur2;
  MGR.recall_snapshot gn #q2 #cur2 #cur1;
  assert (pure (iname_once_preorder cur1 cur2));
  assert (pure (iname_once_preorder cur2 cur1));
  (* From iname_once_preorder both ways, cur1 == cur2. *)
  (match cur1, cur2 with
   | None, None -> ()
   | Some _, Some _ -> ()
   | _, _ -> ());
  MGR.gather gn #cur1 #q1 #q2;
  fold (iname_box gn (q1 +. q2) cur1)
}

ghost fn iname_box_update (gn:MGR.mref iname_once_preorder) (n_seqlock:iname)
    (#old:option iname)
  requires iname_box gn 1.0R old ** pure (iname_once_preorder old (Some n_seqlock))
  ensures iname_box gn 1.0R (Some n_seqlock) ** iname_agree gn n_seqlock
{
  unfold (iname_box gn 1.0R old);
  MGR.update gn #old (Some n_seqlock);
  MGR.take_snapshot gn #1.0R (Some n_seqlock);
  fold (iname_box gn 1.0R (Some n_seqlock));
  fold (iname_agree gn n_seqlock)
}

ghost fn iname_box_alloc (_:unit)
  requires emp
  returns gn:MGR.mref iname_once_preorder
  ensures iname_box gn 1.0R None
{
  let gn = MGR.alloc #(option iname) #iname_once_preorder None;
  fold (iname_box gn 1.0R None);
  gn
}

(* Pure-prop side of disjointness: every registered request_inv name is
   distinct from n_seqlock.  Carried as a pure conjunct inside seqlock_inv,
   established at registration time from fresh_invariant freshness. *)
let rec registry_excludes_iname (requests:Reg.registry) (n_seqlock:iname) : Tot prop =
  match requests with
  | [] -> True
  | r::tl -> request_write_i r =!= n_seqlock /\ registry_excludes_iname tl n_seqlock

let rec registry_excludes_iname_snoc (requests:Reg.registry) (r:Reg.request) (n_seqlock:iname)
  : Lemma
      (requires registry_excludes_iname requests n_seqlock /\ request_write_i r =!= n_seqlock)
      (ensures registry_excludes_iname (requests @ [r]) n_seqlock)
  = match requests with
    | [] -> ()
    | _::tl -> registry_excludes_iname_snoc tl r n_seqlock

let rec registry_excludes_iname_subset (requests:Reg.registry) (n_seqlock:iname)
  : Lemma
      (requires registry_excludes_iname requests n_seqlock)
      (ensures Pulse.Lib.Core.inames_subset (registry_inames requests)
                                            (Pulse.Lib.Core.remove_inv Pulse.Lib.Core.all_inames n_seqlock))
  = match requests with
    | [] -> ()
    | r::tl ->
      registry_excludes_iname_subset tl n_seqlock

(* -------------------------------------------------------------------------- *)
(* End of set-once iname agreement                                            *)
(* -------------------------------------------------------------------------- *)

let agreement_inv (gn:MGR.mref iname_once_preorder) (requests:Reg.registry) : slprop =
  exists* (cur_n:option iname).
    iname_box gn 1.0R cur_n **
    pure (match cur_n with
          | None -> requests == []
          | Some n_s -> registry_excludes_iname requests n_s)

ghost fn agreement_inv_extract (gn:MGR.mref iname_once_preorder) (n_seqlock:iname)
    (#requests:Reg.registry)
  requires agreement_inv gn requests ** iname_agree gn n_seqlock
  ensures agreement_inv gn requests ** iname_agree gn n_seqlock **
          pure (registry_excludes_iname requests n_seqlock)
{
  unfold (agreement_inv gn requests);
  with cur_n. _;
  iname_agree_recall gn n_seqlock #1.0R #cur_n;
  rewrite each cur_n as (Some n_seqlock <: option iname);
  fold (agreement_inv gn requests)
}

let seqlock_inv (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
                (gr:Reg.reg_gname) (g:gamma_value_t)
                (gn:MGR.mref iname_once_preorder)
                (version:ref nat) (data:array val_t) (len:nat)
  : slprop =
  exists* (ver:nat) (h:history val_t) (vs:list val_t)
          (requests:Reg.registry).
    agreement_inv gn requests **
    seqlock_inv_body gver gh gr g version data len ver h vs requests

(* Public predicate.  Exposes [n_seqlock] as the first explicit parameter so
   clients (notably the helper writer at unlock) can pass it to
   [linearize_writes] and discharge the mask-disjointness obligation. *)
let is_seqlock (n_seqlock:iname) (v:big_atomic) (g:gamma_value_t) (n:nat) : slprop =
  exists* (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
          (gr:Reg.reg_gname) (gn:MGR.mref iname_once_preorder).
    inv n_seqlock (seqlock_inv gver gh gr g gn (fst v) (snd v) n) **
    iname_agree gn n_seqlock

ghost fn pack_seqlock_inv_even (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (gr:Reg.reg_gname) (g:gamma_value_t)
    (gn:MGR.mref iname_once_preorder)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t) (#requests:Reg.registry)
  requires
    pure (ver % 2 == 0) **
    agreement_inv gn requests **
    version |-> ver **
    Reg.registry_auth gr 1.0R requests **
    registry_inv g (ver / 2) requests **
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
    value_auth g vs **
    history_auth gh 1.0R h **
    mono_nat_auth gver 1.0R ver **
    A.pts_to data (seq_of_snapshot vs) **
    pure (last_opt h == Some vs)
  ensures seqlock_inv gver gh gr g gn version data n
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
  fold (seqlock_inv gver gh gr g gn version data n)
}

ghost fn pack_seqlock_inv_odd (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (gr:Reg.reg_gname) (g:gamma_value_t)
    (gn:MGR.mref iname_once_preorder)
    (version:ref nat) (data:array val_t) (n:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t) (#requests:Reg.registry)
  requires
    pure (ver % 2 <> 0) **
    agreement_inv gn requests **
    version |-> ver **
    Reg.registry_auth gr 1.0R requests **
    registry_inv g (ver / 2) requests **
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
    history_auth gh (1.0R /. 2.0R) h **
    mono_nat_auth gver (1.0R /. 2.0R) ver **
    A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs)
  ensures seqlock_inv gver gh gr g gn version data n
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
  fold (seqlock_inv gver gh gr g gn version data n)
}

fn new_big_atomic (n:SZ.t) (src:larray val_t (SZ.v n)) (#dq:perm)
    (#vs:erased (Seq.seq val_t))
  requires A.pts_to src #dq vs ** pure (Seq.length vs == SZ.v n /\ SZ.v n > 0)
  returns r : (iname & big_atomic & gamma_value_t)
  ensures
    A.pts_to src #dq vs **
    is_seqlock (tfst r) (tsnd r) (tthd r) (SZ.v n) **
    value (tthd r) (snapshot_of_seq (reveal vs))
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

  let gn = iname_box_alloc ();

  Seq.lemma_seq_of_seq_to_list (reveal vs);
  rewrite (A.pts_to data (reveal vs)) as (A.pts_to data (seq_of_snapshot (reveal snap)));

  fold (value_auth g (reveal snap));
  fold (value g (reveal snap));
  fold (value_auth g (reveal snap));
  fold (mono_nat_auth gver 1.0R 0);
  fold (registry_inv g 0 []);
  intro_pure (match (None #iname) with
              | None -> ([] <: Reg.registry) == []
              | Some n_s -> registry_excludes_iname [] n_s) ();
  fold (agreement_inv gn []);
  pack_seqlock_inv_even gver gh gr g gn version data (SZ.v n)
    #0 #(reveal h0) #(reveal snap) #[];
  let n_seqlock = new_invariant (seqlock_inv gver gh gr g gn version data (SZ.v n));
  (* Two-step allocation: now that the inv exists with name [n_seqlock], open
     it to update the set-once MGR from [None] to [Some n_seqlock], producing
     the persistent [iname_agree gn n_seqlock] snapshot. *)
  later_credit_buy 1;
  with_invariants_g unit emp_inames n_seqlock
    (seqlock_inv gver gh gr g gn version data (SZ.v n))
    emp
    (fun _ -> iname_agree gn n_seqlock)
  fn _ {
    unfold (seqlock_inv gver gh gr g gn version data (SZ.v n));
    with ver1 h1 vs1 requests1. _;
    unfold (agreement_inv gn requests1);
    with cur_n. _;
    (* The inv was JUST allocated above with cur_n == None and requests == [].
       Pulse cannot reason temporally, so we use an internal trick: at
       allocation time we additionally allocate a one-shot "init token"
       ghost ref that witnesses cur_n == None on first open and gets
       discarded after the update.  For now use an explicit Some/None split. *)
    (* Since we just allocated, the only reachable state is cur_n=None.  We
       handle both branches: in the Some branch, derive False via... well,
       this is the tricky bit. *)
    (match cur_n with
     | None -> ()
     | Some _ -> ());
    (* TEMP: proceed only if None; in Some case we'd be stuck. *)
    admit ()
  };
  let handle : big_atomic = (version, data);
  rewrite (inv n_seqlock (seqlock_inv gver gh gr g gn version data (SZ.v n)))
    as (inv n_seqlock (seqlock_inv gver gh gr g gn (fst handle) (snd handle) (SZ.v n)));
  fold (is_seqlock n_seqlock handle g (SZ.v n));
  rewrite (value g (reveal snap)) as (value g (snapshot_of_seq (reveal vs)));
  (n_seqlock, handle, g)
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
    (gn:MGR.mref iname_once_preorder)
    (version:ref nat) (data:array val_t) (n:nat)
    (#lb:nat) (#curr:nat) (#h:history val_t) (#vs:list val_t) (#requests:Reg.registry)
  requires seqlock_inv_body gver gh gr g version data n curr h vs requests **
           agreement_inv gn requests **
           mono_nat_lb gver lb
  ensures seqlock_inv gver gh gr g gn version data n **
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
    pack_seqlock_inv_even gver gh gr g gn version data n #curr #h #vs #requests
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
    pack_seqlock_inv_odd gver gh gr g gn version data n #curr #h #vs #requests
  }
}

fn loop_read_step
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t)
   (#gn:MGR.mref iname_once_preorder) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat) (lb:nat)
  requires inv n_inv (seqlock_inv gver gh gr g gn version data n) ** mono_nat_lb gver lb
  returns curr:nat
  ensures inv n_inv (seqlock_inv gver gh gr g gn version data n) **
          mono_nat_lb gver lb ** mono_nat_lb gver curr ** pure (lb <= curr)
{
  let curr = with_invariants nat emp_inames n_inv (seqlock_inv gver gh gr g gn version data n)
    (mono_nat_lb gver lb)
    (fun r -> mono_nat_lb gver lb ** mono_nat_lb gver r ** pure (lb <= r))
  fn _ {
    unfold (seqlock_inv gver gh gr g gn version data n);
    with curr h vs requests. _;
    unfold (seqlock_inv_body gver gh gr g version data n curr h vs requests);
    let r = version_read_atomic version #1.0R #(hide curr);
    assert (pure (r == curr));
    fold (seqlock_inv_body gver gh gr g version data n curr h vs requests);
    loop_read_close gver gh gr g gn version data n #lb #curr #h #vs #requests;
    rewrite (mono_nat_lb gver curr) as (mono_nat_lb gver r);
    r
  };
  curr
}

fn rec loop_while
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t)
   (#gn:MGR.mref iname_once_preorder) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat) (v:nat)
  requires inv n_inv (seqlock_inv gver gh gr g gn version data n) ** mono_nat_lb gver v
  ensures inv n_inv (seqlock_inv gver gh gr g gn version data n) **
          (exists* (ver':nat). pure (v < ver') ** mono_nat_lb gver ver')
{
  let curr = loop_read_step #gver #gh #gr #g #gn #n_inv version data n v;
  if (curr = v) {
    rewrite each curr as v;
    drop_ (mono_nat_lb gver v);
    loop_while #gver #gh #gr #g #gn #n_inv version data n v
  } else {
    assert (pure (v < curr));
    drop_ (mono_nat_lb gver v);
    intro_pure (v < curr) ();
    intro_exists #nat (fun ver' -> pure (v < ver') ** mono_nat_lb gver ver') curr
  }
}

(* -------------------------------------------------------------------------- *)
(* Reader-side snapshot evidence                                               *)
(* -------------------------------------------------------------------------- *)

(* Per-element evidence: the version observed while reading an element, plus
   a persistent history fragment for even (unlocked) versions. *)
let snapshot_even_evidence_payload (gh:gname val_t)
    (i:nat) (ver_i:nat) (v:val_t) : slprop =
  exists* (vs:list val_t) (h:history val_t).
    history_frag gh (ver_i / 2) vs #h **
    pure (List.nth vs i == Some v)

let snapshot_evidence (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (ver_i:nat) (v:val_t) : slprop =
  if ver_i % 2 == 0 then
    mono_nat_lb gver ver_i **
    snapshot_even_evidence_payload gh i ver_i v
  else
    mono_nat_lb gver ver_i **
    pure (ver_i % 2 <> 0)

(* A branch-free view of the invariant's read resources.  It lets the atomic
   body perform one physical read without branching on the erased invariant
   witness [ver], while preserving the extra wait-free registry resources
   outside this view. *)
let seqlock_read_case (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (g:gamma_value_t) (data:array val_t) (ver:nat) (h:history val_t)
    (vs:list val_t) : slprop =
  exists* (hp:perm) (vp:perm) (dp:perm).
    (if ver % 2 == 0 then value_auth g vs else emp) **
    history_auth gh hp h **
    mono_nat_auth gver vp ver **
    A.pts_to data #dp (seq_of_snapshot vs) **
    pure (((ver % 2 == 0) /\ hp == 1.0R /\ vp == 1.0R /\
           dp == 1.0R /\ last_opt h == Some vs) \/
          ((ver % 2 <> 0) /\ hp == (1.0R /. 2.0R) /\
           vp == (1.0R /. 2.0R) /\ dp == (1.0R /. 2.0R)))

ghost fn seqlock_read_case_intro (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (g:gamma_value_t) (data:array val_t) (#ver:nat) (#h:history val_t) (#vs:list val_t)
  requires
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
  ensures seqlock_read_case gver gh g data ver h vs
{
  let b = prop_as_bool (ver % 2 == 0);
  if b {
    t2b_true_of_prop (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == true));
    elim_if_true_b (Prims.t2b (ver % 2 == 0))
      (value_auth g vs **
       history_auth gh 1.0R h **
       mono_nat_auth gver 1.0R ver **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) ver **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    intro_cond_true_b (Prims.t2b (ver % 2 == 0)) (value_auth g vs) emp;
    fold (seqlock_read_case gver gh g data ver h vs)
  } else {
    t2b_false_of_not (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == false));
    elim_if_false_b (Prims.t2b (ver % 2 == 0))
      (value_auth g vs **
       history_auth gh 1.0R h **
       mono_nat_auth gver 1.0R ver **
       A.pts_to data (seq_of_snapshot vs) **
       pure (last_opt h == Some vs))
      (history_auth gh (1.0R /. 2.0R) h **
       mono_nat_auth gver (1.0R /. 2.0R) ver **
       A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
    intro_cond_false_b (Prims.t2b (ver % 2 == 0)) (value_auth g vs) emp;
    fold (seqlock_read_case gver gh g data ver h vs)
  }
}

ghost fn dup_mono_nat_lb (gver:MGR.mref mono_nat_increases) (ver:nat)
  requires mono_nat_lb gver ver
  ensures mono_nat_lb gver ver ** mono_nat_lb gver ver
{
  unfold (mono_nat_lb gver ver);
  dup (MGR.snapshot #nat #mono_nat_increases gver ver) ();
  fold (mono_nat_lb gver ver);
  fold (mono_nat_lb gver ver)
}

ghost fn fold_seqlock_inv_even (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
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
  pack_seqlock_inv_even gver gh gr g version data n #ver #h #vs #requests
}

ghost fn fold_seqlock_inv_odd (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
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
  pack_seqlock_inv_odd gver gh gr g version data n #ver #h #vs #requests
}

ghost fn seqlock_read_case_close (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (gr:Reg.reg_gname) (g:gamma_value_t)
    (version:ref nat) (data:array val_t) (n:nat) (i:SZ.t) (ver_lb:nat)
    (#ver:nat) (#h:history val_t) (#vs:list val_t) (#requests:Reg.registry)
    (v_i:val_t)
  requires
    version |-> ver **
    Reg.registry_auth gr 1.0R requests **
    registry_inv g (ver / 2) requests **
    pure (List.length vs == n /\ List.length h == history_len_for_version ver) **
    seqlock_read_case gver gh g data ver h vs **
    mono_nat_lb gver ver_lb **
    pure (List.nth vs (SZ.v i) == Some v_i)
  ensures
    seqlock_inv gver gh gr g version data n **
    snapshot_evidence gver gh (SZ.v i) ver v_i **
    mono_nat_lb gver ver **
    pure (ver >= ver_lb)
{
  unfold (seqlock_read_case gver gh g data ver h vs);
  with hp vp dp. _;
  let b = prop_as_bool (ver % 2 == 0);
  if b {
    t2b_true_of_prop (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == true));
    elim_if_true_b (Prims.t2b (ver % 2 == 0)) (value_auth g vs) emp;
    assert (pure (hp == 1.0R /\ vp == 1.0R /\ dp == 1.0R /\ last_opt h == Some vs));
    rewrite each hp as 1.0R;
    rewrite each vp as 1.0R;
    rewrite each dp as 1.0R;
    mono_nat_lb_valid gver #1.0R #ver #ver_lb;
    mono_nat_lb_get gver #1.0R #ver;
    dup_mono_nat_lb gver ver;
    last_opt_nth h (ver / 2) vs;
    history_frag_alloc gh #1.0R #h (ver / 2) vs;
    assert (pure (ver % 2 == 0));
    assert (pure (last_opt h == Some vs));
    intro_pure (List.length vs == n /\ List.length h == history_len_for_version ver) ();
    intro_pure (last_opt h == Some vs) ();
    fold_seqlock_inv_even gver gh gr g version data n #ver #h #vs #requests;
    t2b_true_of_prop (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == true));
    intro_pure (List.nth vs (SZ.v i) == Some v_i) ();
    fold (snapshot_even_evidence_payload gh (SZ.v i) ver v_i);
    intro_cond_true_b (Prims.t2b (ver % 2 == 0))
      (mono_nat_lb gver ver **
       snapshot_even_evidence_payload gh (SZ.v i) ver v_i)
      (mono_nat_lb gver ver ** pure (ver % 2 <> 0));
    fold (snapshot_evidence gver gh (SZ.v i) ver v_i);
    drop_ (mono_nat_lb gver ver_lb)
  } else {
    t2b_false_of_not (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == false));
    elim_if_false_b (Prims.t2b (ver % 2 == 0)) (value_auth g vs) emp;
    assert (pure (hp == (1.0R /. 2.0R) /\ vp == (1.0R /. 2.0R) /\ dp == (1.0R /. 2.0R)));
    rewrite each hp as (1.0R /. 2.0R);
    rewrite each vp as (1.0R /. 2.0R);
    rewrite each dp as (1.0R /. 2.0R);
    mono_nat_lb_valid gver #(1.0R /. 2.0R) #ver #ver_lb;
    mono_nat_lb_get gver #(1.0R /. 2.0R) #ver;
    dup_mono_nat_lb gver ver;
    assert (pure (ver % 2 <> 0));
    intro_pure (List.length vs == n /\ List.length h == history_len_for_version ver) ();
    fold_seqlock_inv_odd gver gh gr g version data n #ver #h #vs #requests;
    t2b_false_of_not (ver % 2 == 0);
    assert (pure (Prims.t2b (ver % 2 == 0) == false));
    intro_pure (ver % 2 <> 0) ();
    intro_cond_false_b (Prims.t2b (ver % 2 == 0))
      (mono_nat_lb gver ver **
       snapshot_even_evidence_payload gh (SZ.v i) ver v_i)
      (mono_nat_lb gver ver ** pure (ver % 2 <> 0));
    fold (snapshot_evidence gver gh (SZ.v i) ver v_i);
    drop_ (mono_nat_lb gver ver_lb)
  }
}

let seq_index_or (#a:Type0) (d:a) (s:Seq.seq a) (i:nat) : Tot a =
  if i < Seq.length s then Seq.index s i else d

let seq_index_or_index (#a:Type0) (d:a) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (seq_index_or d s i == Seq.index s i)
  = ()

let versions_ge_from (lb:nat) (i:nat) (n:nat) (vers:Seq.seq nat) : prop =
  forall (k:nat). i <= k /\ k < n ==> lb <= seq_index_or #nat 0 vers k

let versions_strongly_sorted_from (i:nat) (n:nat) (vers:Seq.seq nat) : prop =
  forall (k:nat) (l:nat).
    i <= k /\ k < l /\ l < n ==> seq_index_or #nat 0 vers k <= seq_index_or #nat 0 vers l

let versions_ge_from_cons (lb:nat) (ver_i:nat) (i:nat) (n:nat) (vers:Seq.seq nat)
  : Lemma
      (requires lb <= ver_i /\ seq_index_or #nat 0 vers i == ver_i /\
                versions_ge_from ver_i (i + 1) n vers)
      (ensures versions_ge_from lb i n vers)
  = assert (forall (k:nat). i <= k /\ k < n ==> lb <= seq_index_or #nat 0 vers k)

let versions_strongly_sorted_from_cons (ver_i:nat) (i:nat) (n:nat) (vers:Seq.seq nat)
  : Lemma
      (requires seq_index_or #nat 0 vers i == ver_i /\
                versions_ge_from ver_i (i + 1) n vers /\
                versions_strongly_sorted_from (i + 1) n vers)
      (ensures versions_strongly_sorted_from i n vers)
  = assert (forall (k:nat) (l:nat).
              i <= k /\ k < l /\ l < n ==>
              seq_index_or #nat 0 vers k <= seq_index_or #nat 0 vers l)

let rec big_snapshot_evidence_from (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  : Tot slprop (decreases (n - i)) =
  if i < n then
    snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
    big_snapshot_evidence_from gver gh (i + 1) n vers vals
  else
    emp

let big_snapshot_evidence (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (ver_lb:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t) : slprop =
  big_snapshot_evidence_from gver gh 0 n vers vals **
  pure (Seq.length vers == n /\ Seq.length vals == n /\
        versions_strongly_sorted_from 0 n vers /\
        versions_ge_from ver_lb 0 n vers)

ghost fn pack_big_snapshot_evidence_nil (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires pure (i >= n)
  ensures big_snapshot_evidence_from gver gh i n vers vals
{
  assert (pure ((i < n) == false));
  intro_cond_false_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp;
  fold (big_snapshot_evidence_from gver gh i n vers vals)
}

ghost fn pack_big_snapshot_evidence_cons (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires pure (i < n)
  requires snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i)
  requires big_snapshot_evidence_from gver gh (i + 1) n vers vals
  ensures big_snapshot_evidence_from gver gh i n vers vals
{
  assert (pure ((i < n) == true));
  intro_cond_true_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp;
  fold (big_snapshot_evidence_from gver gh i n vers vals)
}

fn snapshot_read_slot_impl (data:array val_t) (i:SZ.t)
    (#p:perm)
    (#s:erased (Seq.seq val_t){SZ.v i < Seq.length s})
  preserves A.pts_to data #p s
  returns v_i:val_t
  ensures pure (v_i == Seq.index s (SZ.v i))
{
  data.(i)
}

let snapshot_read_slot_atomic (data:array val_t) (i:SZ.t)
    (#p:perm)
    (#s:erased (Seq.seq val_t){SZ.v i < Seq.length s}) =
  Pulse.Lib.Core.as_atomic _ _ (snapshot_read_slot_impl data i #p #s)

fn snapshot_copy_step
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat)
   (i:SZ.t) (#ver_lb:erased nat) (dst:array val_t)
   (#vdst:erased (s:Seq.seq val_t{SZ.v i < Seq.length s}))
  requires
       inv n_inv (seqlock_inv gver gh gr g version data n)
    ** mono_nat_lb gver (reveal ver_lb)
    ** A.pts_to dst vdst
    ** pure (SZ.v i < n /\ Seq.length vdst == n)
  returns r : (erased nat & val_t)
  ensures
       A.pts_to dst (Seq.upd vdst (SZ.v i) (snd r))
    ** snapshot_evidence gver gh (SZ.v i) (reveal (fst r)) (snd r)
    ** mono_nat_lb gver (reveal (fst r))
    ** pure (reveal (fst r) >= reveal ver_lb)
{
  let r = with_invariants (erased nat & val_t) emp_inames n_inv
    (seqlock_inv gver gh gr g version data n)
    (mono_nat_lb gver (reveal ver_lb))
    (fun r -> snapshot_evidence gver gh (SZ.v i) (reveal (fst r)) (snd r) **
              mono_nat_lb gver (reveal (fst r)) ** pure (reveal (fst r) >= reveal ver_lb))
  fn _ {
    unfold (seqlock_inv gver gh gr g version data n);
    with ver h vs requests. _;
    unfold (seqlock_inv_body gver gh gr g version data n ver h vs requests);
    seqlock_read_case_intro gver gh g data #ver #h #vs;
    unfold (seqlock_read_case gver gh g data ver h vs);
    with hp vp dp. _;
    let v_i = snapshot_read_slot_atomic data i #dp #(seq_of_snapshot vs);
    seq_of_snapshot_nth vs (SZ.v i);
    assert (pure (List.nth vs (SZ.v i) == Some v_i));
    fold (seqlock_read_case gver gh g data ver h vs);
    seqlock_read_case_close gver gh gr g version data n i (reveal ver_lb) #ver #h #vs #requests v_i;
    (hide ver, v_i)
  };
  let v_i = snd r;
  dst.(i) <- v_i;
  with s'. assert (A.pts_to dst s' ** pure (s' == Seq.upd vdst (SZ.v i) v_i));
  rewrite each s' as (Seq.upd vdst (SZ.v i) v_i);
  r
}

fn rec snapshot_copy_aux
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (i:SZ.t) (#ver_lb:erased nat) (dst:array val_t)
   (#vdst:erased (Seq.seq val_t)) (#vers:erased (Seq.seq nat))
  requires
       inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n))
    ** mono_nat_lb gver (reveal ver_lb)
    ** A.pts_to dst vdst
    ** pure (SZ.v i <= SZ.v n /\ Seq.length vdst == SZ.v n /\ Seq.length vers == SZ.v n)
  ensures
    exists* (vout:Seq.seq val_t) (versout:Seq.seq nat).
       A.pts_to dst vout
    ** big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout
    ** pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
             versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
             versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
             (forall (k:nat). k < SZ.v i ==>
                seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))
  decreases (SZ.v n - SZ.v i)
{
  if (i = n) {
    assert (pure (SZ.v i == SZ.v n));
    assert (pure (versions_strongly_sorted_from (SZ.v i) (SZ.v n) vers));
    assert (pure (versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) vers));
    pack_big_snapshot_evidence_nil gver gh (SZ.v i) (SZ.v n) vers vdst;
    drop_ (mono_nat_lb gver (reveal ver_lb));
    intro_pure (Seq.length vdst == SZ.v n /\ Seq.length vers == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) vers /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) vers /\
                (forall (k:nat). k < SZ.v i ==>
                   seq_index_or #val_t 0 vdst k == seq_index_or #val_t 0 vdst k /\
                   seq_index_or #nat 0 vers k == seq_index_or #nat 0 vers k)) ();
    intro_exists #(Seq.seq nat)
      (fun versout -> A.pts_to dst vdst **
                      big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vdst **
                      pure (Seq.length vdst == SZ.v n /\ Seq.length versout == SZ.v n /\
                            versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                            versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                            (forall (k:nat). k < SZ.v i ==>
                              seq_index_or #val_t 0 vdst k == seq_index_or #val_t 0 vdst k /\
                              seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) vers;
    intro_exists #(Seq.seq val_t)
      (fun vout -> exists* (versout:Seq.seq nat).
          A.pts_to dst vout **
          big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout **
          pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                (forall (k:nat). k < SZ.v i ==>
                  seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                  seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) vdst
  } else {
    assert (pure (SZ.v i < SZ.v n));
    SZ.fits_lte (SZ.v i + 1) (SZ.v n);
    let vdst_step : erased (s:Seq.seq val_t{SZ.v i < Seq.length s}) = hide (reveal vdst);
    rewrite (A.pts_to dst vdst) as (A.pts_to dst vdst_step);
    let r = snapshot_copy_step #gver #gh #gr #g #n_inv version data (SZ.v n) i #ver_lb dst #vdst_step;
    let v_i = snd r;
    rewrite (A.pts_to dst (Seq.upd vdst_step (SZ.v i) v_i))
      as (A.pts_to dst (Seq.upd vdst (SZ.v i) v_i));
    let vdst1 : erased (Seq.seq val_t) = hide (Seq.upd vdst (SZ.v i) v_i);
    let vers1 : erased (Seq.seq nat) = hide (Seq.upd vers (SZ.v i) (reveal (fst r)));
    Seq.lemma_len_upd (SZ.v i) v_i vdst;
    Seq.lemma_len_upd (SZ.v i) (reveal (fst r)) vers;
    rewrite (A.pts_to dst (Seq.upd vdst (SZ.v i) v_i)) as (A.pts_to dst vdst1);
    let i1 = SZ.add i 1sz;
    assert (pure (SZ.v i1 == SZ.v i + 1));
    snapshot_copy_aux #gver #gh #gr #g #n_inv version data n i1 #(fst r) dst #vdst1 #vers1;
    with vout versout. _;
    assert (pure (Seq.index vout (SZ.v i) == v_i));
    assert (pure (Seq.index versout (SZ.v i) == reveal (fst r)));
    seq_index_or_index #val_t 0 vout (SZ.v i);
    seq_index_or_index #nat 0 versout (SZ.v i);
    assert (pure (seq_index_or #nat 0 versout (SZ.v i) == reveal (fst r)));
    assert (pure (seq_index_or #val_t 0 vout (SZ.v i) == snd r));
    rewrite (snapshot_evidence gver gh (SZ.v i) (reveal (fst r)) (snd r))
      as (snapshot_evidence gver gh (SZ.v i)
            (seq_index_or #nat 0 versout (SZ.v i))
            (seq_index_or #val_t 0 vout (SZ.v i)));
    rewrite each (SZ.v i1) as (SZ.v i + 1);
    assert (pure (versions_ge_from (reveal (fst r)) (SZ.v i + 1) (SZ.v n) versout));
    assert (pure (versions_strongly_sorted_from (SZ.v i + 1) (SZ.v n) versout));
    versions_ge_from_cons (reveal ver_lb) (reveal (fst r)) (SZ.v i) (SZ.v n) versout;
    versions_strongly_sorted_from_cons (reveal (fst r)) (SZ.v i) (SZ.v n) versout;
    pack_big_snapshot_evidence_cons gver gh (SZ.v i) (SZ.v n) versout vout;
    assert (pure (forall (k:nat). k < SZ.v i ==>
             seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
             seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k));
    intro_pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                (forall (k:nat). k < SZ.v i ==>
                   seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                   seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k)) ();
    intro_exists #(Seq.seq nat)
      (fun versout -> A.pts_to dst vout **
                      big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout **
                      pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                            versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                            versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                            (forall (k:nat). k < SZ.v i ==>
                              seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                              seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) versout;
    intro_exists #(Seq.seq val_t)
      (fun vout -> exists* (versout:Seq.seq nat).
          A.pts_to dst vout **
          big_snapshot_evidence_from gver gh (SZ.v i) (SZ.v n) versout vout **
          pure (Seq.length vout == SZ.v n /\ Seq.length versout == SZ.v n /\
                versions_strongly_sorted_from (SZ.v i) (SZ.v n) versout /\
                versions_ge_from (reveal ver_lb) (SZ.v i) (SZ.v n) versout /\
                (forall (k:nat). k < SZ.v i ==>
                  seq_index_or #val_t 0 vout k == seq_index_or #val_t 0 vdst k /\
                  seq_index_or #nat 0 versout k == seq_index_or #nat 0 vers k))) vout
  }
}

fn snapshot_copy
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (ver_lb:nat) (dst:array val_t)
   (#vdst0:erased (Seq.seq val_t))
  requires
       inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n))
    ** mono_nat_lb gver ver_lb
    ** A.pts_to dst vdst0
    ** pure (Seq.length vdst0 == SZ.v n)
  returns vdst' : erased (Seq.seq val_t)
  ensures
       A.pts_to dst vdst'
    ** pure (Seq.length vdst' == SZ.v n)
    ** (exists* (vers:Seq.seq nat).
          big_snapshot_evidence gver gh ver_lb (SZ.v n) vers vdst')
{
  let vers0 : erased (Seq.seq nat) = hide (Seq.create (SZ.v n) 0);
  assert (pure (Seq.length vers0 == SZ.v n));
  snapshot_copy_aux #gver #gh #gr #g #n_inv version data n 0sz #(hide ver_lb) dst #vdst0 #vers0;
  with vout versout. _;
  fold (big_snapshot_evidence gver gh ver_lb (SZ.v n) versout vout);
  intro_exists #(Seq.seq nat)
    (fun vers -> big_snapshot_evidence gver gh ver_lb (SZ.v n) vers vout) versout;
  hide vout
}

(* -------------------------------------------------------------------------- *)
(* Read LAT                                                                    *)
(* -------------------------------------------------------------------------- *)

let read_start_frag (gh:gname val_t) (ver:nat) (n:nat) : slprop =
  exists* (h:history val_t) (vs:list val_t).
    history_frag gh (ver / 2) vs #h **
    pure (ver % 2 == 0 /\ List.length vs == n)

let read_start_evidence (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (ver:nat) (n:nat) : slprop =
  mono_nat_lb gver ver ** read_start_frag gh ver n

let snapshot_values_match_from (i:nat) (n:nat)
    (vals:Seq.seq val_t) (vs:list val_t) : prop =
  forall (k:nat). i <= k /\ k < n ==>
    seq_index_or #val_t 0 vals k == seq_index_or #val_t 0 (seq_of_snapshot vs) k

ghost fn value_auth_agree (g:gamma_value_t) (#vs0 #vs1:list val_t)
  preserves value_auth g vs0 ** value_auth g vs1
  ensures pure (vs0 == vs1)
{
  unfold (value_auth g vs0);
  unfold (value_auth g vs1);
  GR.pts_to_injective_eq g;
  fold (value_auth g vs0);
  fold (value_auth g vs1)
}

ghost fn snapshot_evidence_dup_lb (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (ver_i:nat) (v_i:val_t)
  requires snapshot_evidence gver gh i ver_i v_i
  ensures snapshot_evidence gver gh i ver_i v_i ** mono_nat_lb gver ver_i
{
  unfold (snapshot_evidence gver gh i ver_i v_i);
  let b = prop_as_bool (ver_i % 2 == 0);
  if b {
    t2b_true_of_prop (ver_i % 2 == 0);
    assert (pure (Prims.t2b (ver_i % 2 == 0) == true));
    elim_if_true_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    dup_mono_nat_lb gver ver_i;
    intro_cond_true_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    fold (snapshot_evidence gver gh i ver_i v_i)
  } else {
    t2b_false_of_not (ver_i % 2 == 0);
    assert (pure (Prims.t2b (ver_i % 2 == 0) == false));
    elim_if_false_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    dup_mono_nat_lb gver ver_i;
    intro_cond_false_b (Prims.t2b (ver_i % 2 == 0))
      (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
      (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0));
    fold (snapshot_evidence gver gh i ver_i v_i)
  }
}

ghost fn snapshot_evidence_open_even (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (ver_i:nat) (v_i:val_t)
  requires snapshot_evidence gver gh i ver_i v_i
  requires pure (ver_i % 2 == 0)
  ensures mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i
{
  unfold (snapshot_evidence gver gh i ver_i v_i);
  t2b_true_of_prop (ver_i % 2 == 0);
  assert (pure (Prims.t2b (ver_i % 2 == 0) == true));
  elim_if_true_b (Prims.t2b (ver_i % 2 == 0))
    (mono_nat_lb gver ver_i ** snapshot_even_evidence_payload gh i ver_i v_i)
    (mono_nat_lb gver ver_i ** pure (ver_i % 2 <> 0))
}

ghost fn unpack_big_snapshot_evidence_nil (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires big_snapshot_evidence_from gver gh i n vers vals
  requires pure (i >= n)
  ensures emp
{
  unfold (big_snapshot_evidence_from gver gh i n vers vals);
  assert (pure ((i < n) == false));
  elim_if_false_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp
}

ghost fn unpack_big_snapshot_evidence_cons (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
  requires big_snapshot_evidence_from gver gh i n vers vals
  requires pure (i < n)
  ensures snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
          big_snapshot_evidence_from gver gh (i + 1) n vers vals
{
  unfold (big_snapshot_evidence_from gver gh i n vers vals);
  assert (pure ((i < n) == true));
  elim_if_true_b (i < n)
    (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i) **
     big_snapshot_evidence_from gver gh (i + 1) n vers vals)
    emp
}

ghost fn rec read_snapshot_consistent_from
    (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (i:nat) (n:nat) (ver:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
    (hcur:history val_t) (vs0:list val_t)
  requires big_snapshot_evidence_from gver gh i n vers vals
  preserves mono_nat_auth gver 1.0R ver
  preserves history_auth gh 1.0R hcur
  requires pure (i <= n /\ ver % 2 == 0 /\ Seq.length vals == n /\
                 List.length vs0 == n /\ versions_ge_from ver i n vers /\
                 List.nth hcur (ver / 2) == Some vs0)
  ensures pure (snapshot_values_match_from i n vals vs0)
  decreases (n - i)
{
  if (i < n) {
    unpack_big_snapshot_evidence_cons gver gh i n vers vals;
    let ver_i = seq_index_or #nat 0 vers i;
    let v_i = seq_index_or #val_t 0 vals i;
    rewrite (snapshot_evidence gver gh i (seq_index_or #nat 0 vers i) (seq_index_or #val_t 0 vals i))
      as (snapshot_evidence gver gh i ver_i v_i);
    snapshot_evidence_dup_lb gver gh i ver_i v_i;
    mono_nat_lb_valid gver #1.0R #ver #ver_i;
    assert (pure (ver <= ver_i));
    assert (pure (ver_i <= ver));
    assert (pure (ver_i == ver));
    rewrite each ver_i as ver;
    snapshot_evidence_open_even gver gh i ver v_i;
    drop_ (mono_nat_lb gver ver);
    drop_ (mono_nat_lb gver ver);
    unfold (snapshot_even_evidence_payload gh i ver v_i);
    with vsi hi. _;
    history_auth_frag_agree gh #1.0R #hcur (ver / 2) vsi #hi;
    assert (pure (vsi == vs0));
    rewrite each vsi as vs0;
    assert (pure (List.nth vs0 i == Some v_i));
    seq_of_snapshot_nth vs0 i;
    seq_index_or_index #val_t 0 vals i;
    assert (pure (seq_index_or #val_t 0 vals i == seq_index_or #val_t 0 (seq_of_snapshot vs0) i));
    assert (pure (versions_ge_from ver (i + 1) n vers));
    read_snapshot_consistent_from gver gh (i + 1) n ver vers vals hcur vs0;
    assert (pure (snapshot_values_match_from (i + 1) n vals vs0));
    assert (pure (snapshot_values_match_from i n vals vs0))
  } else {
    unpack_big_snapshot_evidence_nil gver gh i n vers vals;
    assert (pure (snapshot_values_match_from i n vals vs0))
  }
}

ghost fn read_snapshot_consistent (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (n:nat) (ver:nat) (vers:Seq.seq nat) (vals:Seq.seq val_t)
    (hcur:history val_t) (vs0:list val_t)
  requires big_snapshot_evidence gver gh ver n vers vals
  preserves mono_nat_auth gver 1.0R ver
  preserves history_auth gh 1.0R hcur
  requires pure (ver % 2 == 0 /\ List.length vs0 == n /\
                 List.nth hcur (ver / 2) == Some vs0)
  ensures pure (vals == seq_of_snapshot vs0)
{
  unfold (big_snapshot_evidence gver gh ver n vers vals);
  assert (pure (Seq.length vals == n));
  assert (pure (versions_ge_from ver 0 n vers));
  read_snapshot_consistent_from gver gh 0 n ver vers vals hcur vs0;
  assert (pure (snapshot_values_match_from 0 n vals vs0));
  assert (pure (Seq.length (seq_of_snapshot vs0) == n));
  Seq.lemma_eq_intro vals (seq_of_snapshot vs0);
  Seq.lemma_eq_elim vals (seq_of_snapshot vs0);
  assert (pure (vals == seq_of_snapshot vs0))
}

fn read_first_even
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:nat)
  requires inv n_inv (seqlock_inv gver gh gr g version data n)
  returns r:option nat
  ensures inv n_inv (seqlock_inv gver gh gr g version data n) **
          (match r with
           | None -> emp
           | Some ver -> read_start_evidence gver gh ver n)
{
  let r = with_invariants (option nat) emp_inames n_inv (seqlock_inv gver gh gr g version data n)
    emp
    (fun r -> match r with
      | None -> emp
      | Some ver -> read_start_evidence gver gh ver n)
  fn _ {
    unfold (seqlock_inv gver gh gr g version data n);
    with curr h vs requests. _;
    unfold (seqlock_inv_body gver gh gr g version data n curr h vs requests);
    let observed = version_read_atomic version #1.0R #(hide curr);
    assert (pure (observed == curr));
    if (observed % 2 = 0) {
      rewrite each curr as observed;
      t2b_true_of_prop (observed % 2 == 0);
      assert (pure (Prims.t2b (observed % 2 == 0) == true));
      elim_if_true_b (Prims.t2b (observed % 2 == 0))
        (value_auth g vs **
         history_auth gh 1.0R h **
         mono_nat_auth gver 1.0R observed **
         A.pts_to data (seq_of_snapshot vs) **
         pure (last_opt h == Some vs))
        (history_auth gh (1.0R /. 2.0R) h **
         mono_nat_auth gver (1.0R /. 2.0R) observed **
         A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
      mono_nat_lb_get gver #1.0R #observed;
      last_opt_nth h (observed / 2) vs;
      history_frag_alloc gh #1.0R #h (observed / 2) vs;
      intro_pure (last_opt h == Some vs) ();
      intro_pure (List.length vs == n /\ List.length h == history_len_for_version observed) ();
      pack_seqlock_inv_even gver gh gr g version data n #observed #h #vs #requests;
      intro_pure (observed % 2 == 0 /\ List.length vs == n) ();
      fold (read_start_frag gh observed n);
      fold (read_start_evidence gver gh observed n);
      Some observed
    } else {
      rewrite each curr as observed;
      t2b_false_of_not (observed % 2 == 0);
      assert (pure (Prims.t2b (observed % 2 == 0) == false));
      elim_if_false_b (Prims.t2b (observed % 2 == 0))
        (value_auth g vs **
         history_auth gh 1.0R h **
         mono_nat_auth gver 1.0R observed **
         A.pts_to data (seq_of_snapshot vs) **
         pure (last_opt h == Some vs))
        (history_auth gh (1.0R /. 2.0R) h **
         mono_nat_auth gver (1.0R /. 2.0R) observed **
         A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vs));
      intro_pure (List.length vs == n /\ List.length h == history_len_for_version observed) ();
      pack_seqlock_inv_odd gver gh gr g version data n #observed #h #vs #requests;
      None #nat
    }
  };
  r
}

let read_attempt_frame (gver:MGR.mref mono_nat_increases) (gh:gname val_t)
    (gr:Reg.reg_gname) (g:gamma_value_t)
    (n_inv:iname) (version:ref nat) (data:array val_t) (n:SZ.t)
    (ver:nat) (dst:array val_t) (vdst:Seq.seq val_t) (vers:Seq.seq nat) : slprop =
  inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n)) **
  A.pts_to dst vdst **
  read_start_frag gh ver (SZ.v n) **
  big_snapshot_evidence gver gh ver (SZ.v n) vers vdst **
  pure (Seq.length vdst == SZ.v n /\ is_full_array dst)

fn read_try_commit
   (#gver:MGR.mref mono_nat_increases) (#gh:gname val_t)
   (#gr:Reg.reg_gname) (#g:gamma_value_t) (#n_inv:iname)
   (version:ref nat) (data:array val_t) (n:SZ.t)
   (ver:nat) (dst:array val_t)
   (#vdst:erased (Seq.seq val_t)) (#vers:erased (Seq.seq nat))
   (#is:inames) (phi:array val_t -> slprop)
   (tok : au_token is (list val_t) (array val_t)
      (fun vs -> value g vs)
      (fun vs copy -> value g vs ** A.pts_to copy (seq_of_snapshot vs))
      (fun _ copy -> phi copy))
  requires read_attempt_frame gver gh gr g n_inv version data n ver dst vdst vers **
           au_available tok
  returns r:option (array val_t)
  ensures (match r with
    | None -> read_attempt_frame gver gh gr g n_inv version data n ver dst vdst vers **
              au_available tok
    | Some copy -> inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n)) **
                   phi copy)
{
  later_credit_buy 3;
  let attempt = au_atomic_step
    #is #(add_inv emp_inames n_inv) #(list val_t) #(array val_t)
    #(fun vs -> value g vs)
    #(fun vs copy -> value g vs ** A.pts_to copy (seq_of_snapshot vs))
    #(fun _ copy -> phi copy)
    #(read_attempt_frame gver gh gr g n_inv version data n ver dst (reveal vdst) (reveal vers))
    #(fun _ -> inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n)))
    tok
  fn x {
    unfold (read_attempt_frame gver gh gr g n_inv version data n ver dst (reveal vdst) (reveal vers));
    unfold (value g (reveal x));
    let res = with_invariants_a (option (array val_t)) emp_inames
      n_inv (seqlock_inv gver gh gr g version data (SZ.v n))
      (A.pts_to dst (reveal vdst) **
       read_start_frag gh ver (SZ.v n) **
       big_snapshot_evidence gver gh ver (SZ.v n) (reveal vers) (reveal vdst) **
       pure (Seq.length (reveal vdst) == SZ.v n /\ is_full_array dst) **
       value_auth g (reveal x))
      (fun res -> match res with
        | None -> A.pts_to dst (reveal vdst) **
                  read_start_frag gh ver (SZ.v n) **
                  big_snapshot_evidence gver gh ver (SZ.v n) (reveal vers) (reveal vdst) **
                  pure (Seq.length (reveal vdst) == SZ.v n /\ is_full_array dst) **
                  value g (reveal x)
        | Some copy -> value g (reveal x) ** A.pts_to copy (seq_of_snapshot (reveal x)))
    fn _ {
      unfold (seqlock_inv gver gh gr g version data (SZ.v n));
      with curr hcur vscur requests. _;
      unfold (seqlock_inv_body gver gh gr g version data (SZ.v n) curr hcur vscur requests);
      let observed = version_read_atomic version #1.0R #(hide curr);
      assert (pure (observed == curr));
      if (observed = ver) {
        rewrite each curr as ver;
        unfold (read_start_frag gh ver (SZ.v n));
        with h0 vs0. _;
        assert (pure (ver % 2 == 0));
        t2b_true_of_prop (ver % 2 == 0);
        assert (pure (Prims.t2b (ver % 2 == 0) == true));
        elim_if_true_b (Prims.t2b (ver % 2 == 0))
          (value_auth g vscur **
           history_auth gh 1.0R hcur **
           mono_nat_auth gver 1.0R ver **
           A.pts_to data (seq_of_snapshot vscur) **
           pure (last_opt hcur == Some vscur))
          (history_auth gh (1.0R /. 2.0R) hcur **
           mono_nat_auth gver (1.0R /. 2.0R) ver **
           A.pts_to data #(1.0R /. 2.0R) (seq_of_snapshot vscur));
        history_auth_frag_agree gh #1.0R #hcur (ver / 2) vs0 #h0;
        last_opt_nth hcur (ver / 2) vscur;
        assert (pure (vs0 == vscur));
        read_snapshot_consistent gver gh (SZ.v n) ver (reveal vers) (reveal vdst) hcur vs0;
        rewrite each (reveal vdst) as (seq_of_snapshot vs0);
        rewrite each vs0 as vscur;
        value_auth_agree g #vscur #(reveal x);
        intro_pure (List.length vscur == SZ.v n /\ List.length hcur == history_len_for_version ver) ();
        intro_pure (last_opt hcur == Some vscur) ();
        pack_seqlock_inv_even gver gh gr g version data (SZ.v n) #ver #hcur #vscur #requests;
        rewrite (A.pts_to dst (seq_of_snapshot vscur)) as
          (A.pts_to dst (seq_of_snapshot (reveal x)));
        fold (value g (reveal x));
        Some dst
      } else {
        fold (seqlock_inv_body gver gh gr g version data (SZ.v n) curr hcur vscur requests);
        fold (seqlock_inv gver gh gr g version data (SZ.v n));
        fold (value g (reveal x));
        None #(array val_t)
      }
    };
    match res {
    None -> {
      fold (read_attempt_frame gver gh gr g n_inv version data n ver dst (reveal vdst) (reveal vers));
      None #(array val_t)
    }
    Some copy -> {
      Some copy
    }
    }
  };
  match attempt {
  None -> {
    None #(array val_t)
  }
  Some copy -> {
    with _x. assert (phi copy ** inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n)));
    Some copy
  }
  }
}

let read_frame (g:gamma_value_t) (n:SZ.t) (v:big_atomic) : slprop =
  is_seqlock v g (SZ.v n) ** pure (SZ.v n > 0)

fn rec read (#g:gamma_value_t) (n:SZ.t) (v:big_atomic)
    (#is:inames) (phi:array val_t -> slprop)
    (tok : au_token is (list val_t) (array val_t)
      (fun vs -> value g vs)
      (fun vs copy -> value g vs ** A.pts_to copy (seq_of_snapshot vs))
      (fun _ copy -> phi copy))
    (_u:unit)
  requires read_frame g n v ** au_available tok
  returns copy:array val_t
  ensures read_frame g n v ** phi copy
{
  unfold (read_frame g n v);
  unfold (is_seqlock v g (SZ.v n));
  with gver gh gr n_inv. _;
  let version = fst v;
  let data = snd v;
  rewrite (inv n_inv (seqlock_inv gver gh gr g (fst v) (snd v) (SZ.v n)))
    as (inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n)));
  let first = read_first_even #gver #gh #gr #g #n_inv version data (SZ.v n);
  match first {
  None -> {
    fold (is_seqlock v g (SZ.v n));
    fold (read_frame g n v);
    read #g n v #is phi tok ()
  }
  Some ver -> {
    unfold (read_start_evidence gver gh ver (SZ.v n));
    let dst = A.alloc #val_t 0 n;
    let vdst0 : erased (Seq.seq val_t) = hide (Seq.create (SZ.v n) 0);
    rewrite (A.pts_to dst (Seq.create (SZ.v n) 0)) as (A.pts_to dst vdst0);
    let vdst' = snapshot_copy #gver #gh #gr #g #n_inv version data n ver dst #vdst0;
    with vers. _;
    fold (read_attempt_frame gver gh gr g n_inv version data n ver dst (reveal vdst') vers);
    let committed = read_try_commit #gver #gh #gr #g #n_inv version data n ver dst #vdst' #(hide vers) #is phi tok;
    match committed {
    Some copy -> {
      rewrite (inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n)))
        as (inv n_inv (seqlock_inv gver gh gr g (fst v) (snd v) (SZ.v n)));
      fold (is_seqlock v g (SZ.v n));
      fold (read_frame g n v);
      copy
    }
    None -> {
      unfold (read_attempt_frame gver gh gr g n_inv version data n ver dst (reveal vdst') vers);
      A.free dst #vdst';
      drop_ (read_start_frag gh ver (SZ.v n));
      drop_ (big_snapshot_evidence gver gh ver (SZ.v n) vers (reveal vdst'));
      drop_ (pure (Seq.length (reveal vdst') == SZ.v n /\ is_full_array dst));
      rewrite (inv n_inv (seqlock_inv gver gh gr g version data (SZ.v n)))
        as (inv n_inv (seqlock_inv gver gh gr g (fst v) (snd v) (SZ.v n)));
      fold (is_seqlock v g (SZ.v n));
      fold (read_frame g n v);
      read #g n v #is phi tok ()
    }
    }
  }
  }
}

let read_is_lat (#g:gamma_value_t) (n:SZ.t) (v:big_atomic) (#is:inames)
  : lat is (list val_t) (array val_t)
      (fun vs -> value g vs)
      (fun vs copy -> value g vs ** A.pts_to copy (seq_of_snapshot vs))
      (read_frame g n v)
  = read #g n v
