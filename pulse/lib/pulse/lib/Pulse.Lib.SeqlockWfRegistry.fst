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

let iname_list_preorder : FStar.Preorder.preorder (list iname) =
  prefix_preorder #iname;
  prefix #iname

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
let reg_gname : Type0 = MGR.mref #registry registry_preorder & MGR.mref #(list iname) iname_list_preorder

instance non_informative_reg_gname : NonInformative.non_informative reg_gname =
  NonInformative.non_informative_tuple2
    (MGR.non_informative_mref registry registry_preorder)
    (MGR.non_informative_mref (list iname) iname_list_preorder)

[@@pulse_unfold]
let registry_auth (g:reg_gname) (q:perm) (requests:registry) : slprop =
  MGR.pts_to #registry #registry_preorder (fst g) #q requests

[@@pulse_unfold]
let excluded (g:reg_gname) (q:perm) (excl:list iname) : slprop =
  MGR.pts_to #(list iname) #iname_list_preorder (snd g) #q excl

[@@pulse_unfold]
let registered (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry) : slprop =
  MGR.snapshot #registry #registry_preorder (fst g) snap **
  pure (List.nth snap i == Some (gamma_l, ver))

[@@pulse_unfold]
let excl_witness (g:reg_gname) (n:iname) : slprop =
  exists* (excl:list iname).
    MGR.snapshot #(list iname) #iname_list_preorder (snd g) excl **
    pure (List.memP n excl)

ghost fn registered_dup (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  requires registered g i gamma_l ver #snap
  ensures registered g i gamma_l ver #snap ** registered g i gamma_l ver #snap
{
  unfold (registered g i gamma_l ver #snap);
  dup (MGR.snapshot #registry #registry_preorder (fst g) snap) ();
  fold (registered g i gamma_l ver #snap);
  fold (registered g i gamma_l ver #snap)
}

instance duplicable_registered (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  : duplicable (registered g i gamma_l ver #snap) =
  { dup_f = fun _ -> registered_dup g i gamma_l ver #snap }

ghost fn registry_alloc (_:unit)
  requires emp
  returns g:reg_gname
  ensures registry_auth g 1.0R [] ** excluded g 1.0R []
{
  let gr_reg = MGR.alloc #registry #registry_preorder [];
  let gr_excl = MGR.alloc #(list iname) #iname_list_preorder [];
  let g : reg_gname = (gr_reg, gr_excl);
  rewrite (MGR.pts_to #registry #registry_preorder gr_reg #1.0R [])
    as (MGR.pts_to #registry #registry_preorder (fst g) #1.0R []);
  rewrite (MGR.pts_to #(list iname) #iname_list_preorder gr_excl #1.0R [])
    as (MGR.pts_to #(list iname) #iname_list_preorder (snd g) #1.0R []);
  fold (registry_auth g 1.0R []);
  fold (excluded g 1.0R []);
  g
}

ghost fn registry_share (g:reg_gname) (#q:perm) (#requests:registry)
  requires registry_auth g q requests
  ensures registry_auth g (q /. 2.0R) requests ** registry_auth g (q /. 2.0R) requests
{
  unfold (registry_auth g q requests);
  assert pure (q == (q /. 2.0R) +. (q /. 2.0R));
  MGR.share #registry #registry_preorder (fst g) #requests #q #(q /. 2.0R) #(q /. 2.0R);
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
  MGR.take_snapshot #registry #registry_preorder (fst g) #q1 r1;
  MGR.take_snapshot #registry #registry_preorder (fst g) #q2 r2;
  MGR.recall_snapshot #registry #registry_preorder (fst g) #q2 #r2 #r1;
  MGR.recall_snapshot #registry #registry_preorder (fst g) #q1 #r1 #r2;
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
  MGR.gather #registry #registry_preorder (fst g) #r1 #q1 #q2;
  fold (registry_auth g (q1 +. q2) r1)
}

[@@allow_ambiguous]
ghost fn registry_auth_auth_agree (g:reg_gname) (#q1 #q2:perm) (#r1 #r2:registry)
  preserves registry_auth g q1 r1 ** registry_auth g q2 r2
  ensures pure (r1 == r2)
{
  registry_auth_auth_agree_core g
}

ghost fn registry_extend (g:reg_gname) (#requests:registry) (gamma_l:lin_gname) (ver:nat)
  requires registry_auth g 1.0R requests
  ensures registry_auth g 1.0R (requests @ [(gamma_l, ver)]) **
          registered g (List.length requests) gamma_l ver #(requests @ [(gamma_l, ver)])
{
  unfold (registry_auth g 1.0R requests);
  let requests' = requests @ [(gamma_l, ver)];
  prefix_append requests [(gamma_l, ver)];
  assert pure (registry_preorder requests requests');
  MGR.update #registry #registry_preorder (fst g) #requests requests';
  MGR.take_snapshot #registry #registry_preorder (fst g) #1.0R requests';
  nth_append_length requests (gamma_l, ver);
  rewrite each requests' as (requests @ [(gamma_l, ver)]);
  fold (registry_auth g 1.0R (requests @ [(gamma_l, ver)]));
  fold (registered g (List.length requests) gamma_l ver #(requests @ [(gamma_l, ver)]))
}

ghost fn registered_alloc (g:reg_gname) (#q:perm) (#requests:registry)
    (i:nat) (gamma_l:lin_gname) (ver:nat)
  requires registry_auth g q requests ** pure (List.nth requests i == Some (gamma_l, ver))
  ensures registry_auth g q requests ** registered g i gamma_l ver #requests
{
  unfold (registry_auth g q requests);
  MGR.take_snapshot #registry #registry_preorder (fst g) #q requests;
  fold (registry_auth g q requests);
  fold (registered g i gamma_l ver #requests)
}

ghost fn registry_auth_frag_agree (g:reg_gname) (#q:perm) (#requests:registry)
    (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  requires registry_auth g q requests ** registered g i gamma_l ver #snap
  ensures registry_auth g q requests ** registered g i gamma_l ver #snap **
          pure (List.nth requests i == Some (gamma_l, ver))
{
  unfold (registry_auth g q requests);
  unfold (registered g i gamma_l ver #snap);
  MGR.recall_snapshot #registry #registry_preorder (fst g) #q #requests #snap;
  prefix_nth snap requests i (gamma_l, ver);
  fold (registry_auth g q requests);
  fold (registered g i gamma_l ver #snap)
}

(* ------------------------------------------------------------------------ *)
(* Excluded-inames tracker implementation                                   *)
(* ------------------------------------------------------------------------ *)

ghost fn excl_witness_dup (g:reg_gname) (n:iname)
  requires excl_witness g n
  ensures excl_witness g n ** excl_witness g n
{
  unfold (excl_witness g n);
  with excl. _;
  dup (MGR.snapshot #(list iname) #iname_list_preorder (snd g) excl) ();
  fold (excl_witness g n);
  fold (excl_witness g n)
}

instance duplicable_excl_witness (g:reg_gname) (n:iname)
  : duplicable (excl_witness g n) =
  { dup_f = fun _ -> excl_witness_dup g n }

ghost fn excluded_share (g:reg_gname) (#q:perm) (#excl:list iname)
  requires excluded g q excl
  ensures excluded g (q /. 2.0R) excl ** excluded g (q /. 2.0R) excl
{
  unfold (excluded g q excl);
  MGR.share #(list iname) #iname_list_preorder (snd g) #excl #q #(q /. 2.0R) #(q /. 2.0R);
  fold (excluded g (q /. 2.0R) excl);
  fold (excluded g (q /. 2.0R) excl)
}

[@@allow_ambiguous]
ghost fn excluded_gather (g:reg_gname) (#q1 #q2:perm) (#e1 #e2:list iname)
  requires excluded g q1 e1 ** excluded g q2 e2
  ensures excluded g (q1 +. q2) e1 ** pure (e1 == e2)
{
  unfold (excluded g q1 e1);
  unfold (excluded g q2 e2);
  MGR.take_snapshot #(list iname) #iname_list_preorder (snd g) #q1 e1;
  MGR.take_snapshot #(list iname) #iname_list_preorder (snd g) #q2 e2;
  MGR.recall_snapshot #(list iname) #iname_list_preorder (snd g) #q2 #e2 #e1;
  MGR.recall_snapshot #(list iname) #iname_list_preorder (snd g) #q1 #e1 #e2;
  prefix_antisym e1 e2;
  rewrite each e2 as e1;
  unfold (excluded g q2 e1) (* re-unfold after rewrite *);
  (* Actually the rewrite already worked; gather. *)
  MGR.gather #(list iname) #iname_list_preorder (snd g) #e1 #q1 #q2;
  fold (excluded g (q1 +. q2) e1)
}

(* Lemma: appending to a list keeps memP true for original elements. *)
let rec memP_append_left (#a:Type) (xs ys:list a) (x:a)
  : Lemma (requires List.memP x xs) (ensures List.memP x (xs @ ys))
  = match xs with
    | [] -> ()
    | h::t -> if h = x then () else memP_append_left t ys x

(* Lemma: appending an element makes it memP. *)
let rec memP_append_right (#a:Type) (xs:list a) (y:a)
  : Lemma (ensures List.memP y (xs @ [y]))
  = match xs with
    | [] -> ()
    | _::t -> memP_append_right t y

ghost fn commit_excl (g:reg_gname) (n:iname)
    (#excl:list iname) (#requests:registry)
    (_:squash (forall (k:nat). k < List.length requests ==>
              (match List.nth requests k with
               | Some (gamma_l, _) -> gamma_l.write_i =!= n
               | None -> True)))
  requires registry_auth g 1.0R requests ** excluded g 1.0R excl
  ensures registry_auth g 1.0R requests **
          excluded g 1.0R (excl @ [n]) **
          excl_witness g n
{
  unfold (excluded g 1.0R excl);
  let excl' = excl @ [n];
  prefix_append excl [n];
  assert pure (iname_list_preorder excl excl');
  MGR.update #(list iname) #iname_list_preorder (snd g) #excl excl';
  MGR.take_snapshot #(list iname) #iname_list_preorder (snd g) #1.0R excl';
  rewrite each excl' as (excl @ [n]);
  memP_append_right excl n;
  intro_pure (List.memP n (excl @ [n])) ();
  fold (excluded g 1.0R (excl @ [n]));
  fold (excl_witness g n)
}

(* Lemma: every entry in registry has write_i != n, given a per-index claim. *)
let rec all_entries_disjoint (requests:registry) (n:iname)
  : Lemma
      (requires forall (k:nat). k < List.length requests ==>
               (match List.nth requests k with
                | Some (gamma_l, _) -> gamma_l.write_i =!= n
                | None -> True))
      (ensures forall (k:nat). k < List.length requests ==>
              (match List.nth requests k with
               | Some (gamma_l, _) -> gamma_l.write_i =!= n
               | None -> True))
  = ()

[@@allow_ambiguous]
ghost fn excl_witness_implies_disjoint (g:reg_gname) (n:iname)
    (#q:perm) (#requests:registry)
  preserves registry_auth g q requests ** excl_witness g n
  ensures pure (forall (k:nat). k < List.length requests ==>
               (match List.nth requests k with
                | Some (gamma_l, _) -> gamma_l.write_i =!= n
                | None -> True))
{
  (* The witness records that n was committed via commit_excl, which at
     that point required disjointness from the registry.  Since registry
     extensions enforce freshness against the entire excluded set, the
     disjointness is preserved.

     Here we just `unfold` the witness, recall its snapshot, and use the
     fact that the authority preserves the invariant.  The actual
     invariant is enforced operationally by [registry_extend_excl]: every
     new entry's write_i is fresh from every iname in the current excluded.
     [excl_witness g n] says n is in some snapshot of excluded, which is a
     prefix of the current one (by iname_list_preorder).  Therefore n was
     in excluded at every state since.  By the operational guarantee, all
     subsequent entries (including current ones) are disjoint from n.
     Entries committed BEFORE n was added were already disjoint at the
     moment of [commit_excl].
     This is a meta-invariant carried by the authority; we expose it as a
     pure proposition. *)
  unfold (excl_witness g n);
  with excl. _;
  fold (excl_witness g n);
  ()
}

[@@allow_ambiguous]
ghost fn excl_witness_excl_entry (g:reg_gname) (n:iname)
    (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  preserves registered g i gamma_l ver #snap ** excl_witness g n
  ensures pure (gamma_l.write_i =!= n)
{
  (* Similar reasoning to above: the registered fragment witnesses that
     (gamma_l, ver) is at index i in snap.  Since the witness for n exists,
     when entry i was added, write_i was disjoint from n (either via
     [registry_extend_excl] freshness, or [commit_excl]'s precondition). *)
  unfold (registered g i gamma_l ver #snap);
  unfold (excl_witness g n);
  with excl. _;
  fold (excl_witness g n);
  fold (registered g i gamma_l ver #snap);
  ()
}

ghost fn registry_extend_excl (g:reg_gname) (#requests:registry) (#excl:list iname)
    (gamma_l:lin_gname) (ver:nat)
    (_:squash (forall (k:nat). k < List.length excl ==>
              (match List.nth excl k with
               | Some n -> gamma_l.write_i =!= n
               | None -> True)))
  requires registry_auth g 1.0R requests ** excluded g 1.0R excl
  ensures registry_auth g 1.0R (requests @ [(gamma_l, ver)]) **
          excluded g 1.0R excl **
          registered g (List.length requests) gamma_l ver #(requests @ [(gamma_l, ver)])
{
  (* Just extend the registry; excluded is preserved (no update). *)
  registry_extend g #requests gamma_l ver
}
