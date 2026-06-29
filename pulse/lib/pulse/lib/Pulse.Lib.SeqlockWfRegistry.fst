module Pulse.Lib.SeqlockWfRegistry
#lang-pulse
open Pulse.Lib.Pervasives
module List = FStar.List.Tot
open FStar.List.Tot { (@) }
module GR = Pulse.Lib.GhostReference
module MGR = Pulse.Lib.MonotonicGhostRef

let rec prefix (#a:Type0) (xs ys:list a) : Tot prop =
  match xs, ys with
  | [], _ -> True
  | _::_, [] -> False
  | x::xt, y::yt -> x == y /\ prefix xt yt

let rec prefix_refl (#a:Type0) (xs:list a)
  : Lemma (prefix xs xs)
  = match xs with
    | [] -> ()
    | _::xt -> prefix_refl xt

let rec prefix_trans (#a:Type0) (xs ys zs:list a)
  : Lemma
      (requires prefix xs ys /\ prefix ys zs)
      (ensures prefix xs zs)
  = match xs, ys, zs with
    | [], _, _ -> ()
    | _::_, [], _ -> ()
    | _::_, _::_, [] -> ()
    | _::xt, _::yt, _::zt -> prefix_trans xt yt zt

let rec prefix_antisym (#a:Type0) (xs ys:list a)
  : Lemma
      (requires prefix xs ys /\ prefix ys xs)
      (ensures xs == ys)
  = match xs, ys with
    | [], [] -> ()
    | [], _::_ -> ()
    | _::_, [] -> ()
    | _::xt, _::yt -> prefix_antisym xt yt

let prefix_preorder (#a:Type0)
  : Lemma (FStar.Preorder.preorder_rel (prefix #a))
  = introduce forall x. prefix #a x x with (prefix_refl #a x);
    introduce forall x y z. (prefix #a x y /\ prefix #a y z) ==> prefix #a x z with
      introduce _ ==> _ with _. (prefix_trans #a x y z)

let registry_preorder : FStar.Preorder.preorder registry =
  prefix_preorder #request;
  prefix #request

let rec prefix_append (#a:Type0) (xs ys:list a)
  : Lemma (prefix xs (xs @ ys))
  = match xs with
    | [] -> ()
    | _::xt -> prefix_append xt ys

let rec prefix_nth (#a:Type0) (xs ys:list a) (i:nat) (v:a)
  : Lemma
      (requires prefix xs ys /\ List.nth xs i == Some v)
      (ensures List.nth ys i == Some v)
  = match xs, ys with
    | [], _ -> ()
    | _::_, [] -> ()
    | _::xt, _::yt ->
      if i = 0 then () else prefix_nth xt yt (i - 1) v

let rec nth_append_length (#a:Type0) (xs:list a) (v:a)
  : Lemma (List.nth (xs @ [v]) (List.length xs) == Some v)
  = match xs with
    | [] -> ()
    | _::xt -> nth_append_length xt v

[@@erasable]
let reg_gname : Type0 = MGR.mref #registry registry_preorder

instance non_informative_reg_gname : NonInformative.non_informative reg_gname =
  MGR.non_informative_mref registry registry_preorder

[@@pulse_unfold]
let registry_auth (g:reg_gname) (q:perm) (requests:registry) : slprop =
  MGR.pts_to #registry #registry_preorder g #q requests

[@@pulse_unfold]
let registered (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (write_i:iname) (#snap:registry) : slprop =
  MGR.snapshot #registry #registry_preorder g snap **
  pure (List.nth snap i == Some (gamma_l, ver, write_i))

ghost fn registered_dup (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (write_i:iname) (#snap:registry)
  requires registered g i gamma_l ver write_i #snap
  ensures registered g i gamma_l ver write_i #snap ** registered g i gamma_l ver write_i #snap
{
  unfold (registered g i gamma_l ver write_i #snap);
  dup (MGR.snapshot #registry #registry_preorder g snap) ();
  fold (registered g i gamma_l ver write_i #snap);
  fold (registered g i gamma_l ver write_i #snap)
}

instance duplicable_registered (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (write_i:iname) (#snap:registry)
  : duplicable (registered g i gamma_l ver write_i #snap) =
  { dup_f = fun _ -> registered_dup g i gamma_l ver write_i #snap }

ghost fn registry_alloc (_:unit)
  requires emp
  returns g:reg_gname
  ensures registry_auth g 1.0R []
{
  let g = MGR.alloc #registry #registry_preorder [];
  fold (registry_auth g 1.0R []);
  g
}

ghost fn registry_share (g:reg_gname) (#q:perm) (#requests:registry)
  requires registry_auth g q requests
  ensures registry_auth g (q /. 2.0R) requests ** registry_auth g (q /. 2.0R) requests
{
  unfold (registry_auth g q requests);
  assert pure (q == (q /. 2.0R) +. (q /. 2.0R));
  MGR.share #registry #registry_preorder g #requests #q #(q /. 2.0R) #(q /. 2.0R);
  fold (registry_auth g (q /. 2.0R) requests);
  fold (registry_auth g (q /. 2.0R) requests)
}

[@@allow_ambiguous]
ghost fn registry_auth_auth_agree_core (g:reg_gname) (#q1 #q2:perm) (#r1 #r2:registry)
  preserves registry_auth g q1 r1 ** registry_auth g q2 r2
  ensures pure (r1 == r2)
{
  unfold (registry_auth g q1 r1);
  unfold (registry_auth g q2 r2);
  MGR.take_snapshot #registry #registry_preorder g #q1 r1;
  MGR.take_snapshot #registry #registry_preorder g #q2 r2;
  MGR.recall_snapshot #registry #registry_preorder g #q2 #r2 #r1;
  MGR.recall_snapshot #registry #registry_preorder g #q1 #r1 #r2;
  prefix_antisym r1 r2;
  fold (registry_auth g q1 r1);
  fold (registry_auth g q2 r2)
}

[@@allow_ambiguous]
ghost fn registry_gather (g:reg_gname) (#q1 #q2:perm) (#r1 #r2:registry)
  requires registry_auth g q1 r1 ** registry_auth g q2 r2
  ensures registry_auth g (q1 +. q2) r1 ** pure (r1 == r2)
{
  registry_auth_auth_agree_core g;
  rewrite each r2 as r1;
  unfold (registry_auth g q1 r1);
  unfold (registry_auth g q2 r1);
  MGR.gather #registry #registry_preorder g #r1 #q1 #q2;
  fold (registry_auth g (q1 +. q2) r1)
}

[@@allow_ambiguous]
ghost fn registry_auth_auth_agree (g:reg_gname) (#q1 #q2:perm) (#r1 #r2:registry)
  preserves registry_auth g q1 r1 ** registry_auth g q2 r2
  ensures pure (r1 == r2)
{
  registry_auth_auth_agree_core g
}

ghost fn registry_extend (g:reg_gname) (#requests:registry) (gamma_l:lin_gname) (ver:nat) (write_i:iname)
  requires registry_auth g 1.0R requests
  ensures registry_auth g 1.0R (requests @ [(gamma_l, ver, write_i)]) **
          registered g (List.length requests) gamma_l ver write_i #(requests @ [(gamma_l, ver, write_i)])
{
  unfold (registry_auth g 1.0R requests);
  let request = (gamma_l, ver, write_i);
  let requests' = requests @ [request];
  prefix_append requests [request];
  assert pure (registry_preorder requests requests');
  MGR.update #registry #registry_preorder g #requests requests';
  MGR.take_snapshot #registry #registry_preorder g #1.0R requests';
  nth_append_length requests request;
  rewrite each request as (gamma_l, ver, write_i);
  rewrite each requests' as (requests @ [(gamma_l, ver, write_i)]);
  fold (registry_auth g 1.0R (requests @ [(gamma_l, ver, write_i)]));
  fold (registered g (List.length requests) gamma_l ver write_i #(requests @ [(gamma_l, ver, write_i)]))
}

ghost fn registered_alloc (g:reg_gname) (#q:perm) (#requests:registry)
    (i:nat) (gamma_l:lin_gname) (ver:nat) (write_i:iname)
  requires registry_auth g q requests ** pure (List.nth requests i == Some (gamma_l, ver, write_i))
  ensures registry_auth g q requests ** registered g i gamma_l ver write_i #requests
{
  unfold (registry_auth g q requests);
  MGR.take_snapshot #registry #registry_preorder g #q requests;
  fold (registry_auth g q requests);
  fold (registered g i gamma_l ver write_i #requests)
}

ghost fn registry_auth_frag_agree (g:reg_gname) (#q:perm) (#requests:registry)
    (i:nat) (gamma_l:lin_gname) (ver:nat) (write_i:iname) (#snap:registry)
  requires registry_auth g q requests ** registered g i gamma_l ver write_i #snap
  ensures registry_auth g q requests ** registered g i gamma_l ver write_i #snap **
          pure (List.nth requests i == Some (gamma_l, ver, write_i))
{
  unfold (registry_auth g q requests);
  unfold (registered g i gamma_l ver write_i #snap);
  MGR.recall_snapshot #registry #registry_preorder g #q #requests #snap;
  prefix_nth snap requests i (gamma_l, ver, write_i);
  fold (registry_auth g q requests);
  fold (registered g i gamma_l ver write_i #snap)
}
