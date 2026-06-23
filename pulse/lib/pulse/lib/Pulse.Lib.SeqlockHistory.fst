module Pulse.Lib.SeqlockHistory
#lang-pulse
open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module List = FStar.List.Tot
open FStar.List.Tot { (@) }
module MGR = Pulse.Lib.MonotonicGhostRef

(* The public interface exposes history as list (list a). *)
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

let history_preorder (#a:Type0) : FStar.Preorder.preorder (history a) =
  prefix_preorder #(list a);
  prefix #(list a)

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
let gname (a:Type0) : Type0 = MGR.mref #(history a) (history_preorder #a)

instance non_informative_gname (a:Type0) : NonInformative.non_informative (gname a) =
  MGR.non_informative_mref (history a) (history_preorder #a)

[@@pulse_unfold]
let history_auth (#a:Type0) (gh:gname a) (q:perm) (h:history a) : slprop =
  MGR.pts_to #(history a) #(history_preorder #a) gh #q h

[@@pulse_unfold]
let history_frag (#a:Type0) (gh:gname a) (i:nat) (vs:list a) (#snap:history a) : slprop =
  MGR.snapshot #(history a) #(history_preorder #a) gh snap **
  pure (List.nth snap i == Some vs)

ghost fn dup_history_frag (#a:Type0) (gh:gname a) (i:nat) (vs:list a) (#snap:history a)
  requires history_frag gh i vs #snap
  ensures history_frag gh i vs #snap ** history_frag gh i vs #snap
{
  unfold (history_frag gh i vs #snap);
  dup (MGR.snapshot #(history a) #(history_preorder #a) gh snap) ();
  fold (history_frag gh i vs #snap);
  fold (history_frag gh i vs #snap)
}

instance duplicable_history_frag (#a:Type0) (gh:gname a) (i:nat) (vs:list a) (#snap:history a)
  : duplicable (history_frag gh i vs #snap) =
  { dup_f = fun _ -> dup_history_frag gh i vs #snap }

ghost fn history_alloc (#a:Type0) (h0:history a)
  requires emp
  returns gh:gname a
  ensures history_auth gh 1.0R h0
{
  let gh = MGR.alloc #(history a) #(history_preorder #a) h0;
  fold (history_auth gh 1.0R h0);
  gh
}

ghost fn history_share (#a:Type0) (gh:gname a) (#q:perm) (#h:history a)
  requires history_auth gh q h
  ensures history_auth gh (q /. 2.0R) h ** history_auth gh (q /. 2.0R) h
{
  unfold (history_auth gh q h);
  assert pure (q == (q /. 2.0R) +. (q /. 2.0R));
  MGR.share #(history a) #(history_preorder #a) gh #h #q #(q /. 2.0R) #(q /. 2.0R);
  fold (history_auth gh (q /. 2.0R) h);
  fold (history_auth gh (q /. 2.0R) h)
}

[@@allow_ambiguous]
ghost fn history_auth_auth_agree_core (#a:Type0) (gh:gname a) (#q1 #q2:perm) (#h1 #h2:history a)
  preserves history_auth gh q1 h1 ** history_auth gh q2 h2
  ensures pure (h1 == h2)
{
  unfold (history_auth gh q1 h1);
  unfold (history_auth gh q2 h2);
  MGR.take_snapshot #(history a) #(history_preorder #a) gh #q1 h1;
  MGR.take_snapshot #(history a) #(history_preorder #a) gh #q2 h2;
  MGR.recall_snapshot #(history a) #(history_preorder #a) gh #q2 #h2 #h1;
  MGR.recall_snapshot #(history a) #(history_preorder #a) gh #q1 #h1 #h2;
  prefix_antisym h1 h2;
  fold (history_auth gh q1 h1);
  fold (history_auth gh q2 h2)
}

[@@allow_ambiguous]
ghost fn history_gather (#a:Type0) (gh:gname a) (#q1 #q2:perm) (#h1 #h2:history a)
  requires history_auth gh q1 h1 ** history_auth gh q2 h2
  ensures history_auth gh (q1 +. q2) h1 ** pure (h1 == h2)
{
  history_auth_auth_agree_core gh;
  rewrite each h2 as h1;
  unfold (history_auth gh q1 h1);
  unfold (history_auth gh q2 h1);
  MGR.gather #(history a) #(history_preorder #a) gh #h1 #q1 #q2;
  fold (history_auth gh (q1 +. q2) h1)
}

ghost fn history_extend (#a:Type0) (gh:gname a) (#h:history a) (vs:list a)
  requires history_auth gh 1.0R h
  ensures history_auth gh 1.0R (h @ [vs]) ** history_frag gh (List.length h) vs #(h @ [vs])
{
  unfold (history_auth gh 1.0R h);
  let h' = h @ [vs];
  prefix_append h [vs];
  assert pure ((history_preorder #a) h h');
  MGR.update #(history a) #(history_preorder #a) gh #h h';
  MGR.take_snapshot #(history a) #(history_preorder #a) gh #1.0R h';
  nth_append_length h vs;
  rewrite each h' as (h @ [vs]);
  fold (history_auth gh 1.0R (h @ [vs]));
  fold (history_frag gh (List.length h) vs #(h @ [vs]))
}

ghost fn history_frag_alloc (#a:Type0) (gh:gname a) (#q:perm) (#h:history a)
    (i:nat) (vs:list a)
  requires history_auth gh q h ** pure (List.nth h i == Some vs)
  ensures history_auth gh q h ** history_frag gh i vs #h
{
  unfold (history_auth gh q h);
  MGR.take_snapshot #(history a) #(history_preorder #a) gh #q h;
  fold (history_auth gh q h);
  fold (history_frag gh i vs #h)
}

ghost fn history_auth_frag_agree (#a:Type0) (gh:gname a) (#q:perm) (#h:history a)
    (i:nat) (vs:list a) (#snap:history a)
  requires history_auth gh q h ** history_frag gh i vs #snap
  ensures history_auth gh q h ** history_frag gh i vs #snap ** pure (List.nth h i == Some vs)
{
  unfold (history_auth gh q h);
  unfold (history_frag gh i vs #snap);
  MGR.recall_snapshot #(history a) #(history_preorder #a) gh #q #h #snap;
  prefix_nth snap h i vs;
  fold (history_auth gh q h);
  fold (history_frag gh i vs #snap)
}

[@@allow_ambiguous]
ghost fn history_auth_auth_agree (#a:Type0) (gh:gname a) (#q1 #q2:perm) (#h1 #h2:history a)
  preserves history_auth gh q1 h1 ** history_auth gh q2 h2
  ensures pure (h1 == h2)
{
  history_auth_auth_agree_core gh
}
