module Pulse.Lib.SeqlockHistory
#lang-pulse
open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module List = FStar.List.Tot
open FStar.List.Tot { (@) }

(* Type abbreviation for clarity. The history is a (logical) ordered list of
   list-of-values snapshots; index = number of completed writes. *)
type history (a:Type0) = list (list a)

[@@erasable]
val gname (a:Type0) : Type0

instance val non_informative_gname (a:Type0) : NonInformative.non_informative (gname a)

(* Abstract slprops. *)
val history_auth (#a:Type0) (gh:gname a) (q:perm) (h:history a) : slprop

(* Persistent fragment: at index i, the snapshot was vs.  The hidden
   snapshot parameter is inferred from the producing operation. *)
[@@allow_ambiguous]
val history_frag (#a:Type0) (gh:gname a) (i:nat) (vs:list a) (#snap:history a) : slprop

(* history_frag is duplicable. *)
[@@erasable]
instance val duplicable_history_frag (#a:Type0) (gh:gname a) (i:nat) (vs:list a) (#snap:history a)
  : duplicable (history_frag gh i vs #snap)

(* Allocate a new history, returning the auth full-fraction. *)
ghost fn history_alloc (#a:Type0) (h0:history a)
  requires emp
  returns gh:gname a
  ensures history_auth gh 1.0R h0

(* Split / re-gather fractions. *)
ghost fn history_share (#a:Type0) (gh:gname a) (#q:perm) (#h:history a)
  requires history_auth gh q h
  ensures history_auth gh (q /. 2.0R) h ** history_auth gh (q /. 2.0R) h

[@@allow_ambiguous]
ghost fn history_gather (#a:Type0) (gh:gname a) (#q1 #q2:perm) (#h1 #h2:history a)
  requires history_auth gh q1 h1 ** history_auth gh q2 h2
  ensures history_auth gh (q1 +. q2) h1 ** pure (h1 == h2)

(* Update at full fraction: extend by one snapshot, get the fragment. *)
ghost fn history_extend (#a:Type0) (gh:gname a) (#h:history a) (vs:list a)
  requires history_auth gh 1.0R h
  ensures history_auth gh 1.0R (h @ [vs]) ** history_frag gh (List.length h) vs #(h @ [vs])

(* From auth at any fraction: derive a frag for an existing index. *)
ghost fn history_frag_alloc (#a:Type0) (gh:gname a) (#q:perm) (#h:history a)
    (i:nat) (vs:list a)
  requires history_auth gh q h ** pure (List.nth h i == Some vs)
  ensures history_auth gh q h ** history_frag gh i vs #h

(* Frag-auth agreement. *)
ghost fn history_auth_frag_agree (#a:Type0) (gh:gname a) (#q:perm) (#h:history a)
    (i:nat) (vs:list a) (#snap:history a)
  requires history_auth gh q h ** history_frag gh i vs #snap
  ensures history_auth gh q h ** history_frag gh i vs #snap ** pure (List.nth h i == Some vs)

(* Two auths at any fractions agree on the history. *)
[@@allow_ambiguous]
ghost fn history_auth_auth_agree (#a:Type0) (gh:gname a) (#q1 #q2:perm) (#h1 #h2:history a)
  preserves history_auth gh q1 h1 ** history_auth gh q2 h2
  ensures pure (h1 == h2)
