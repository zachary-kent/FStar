(* Copyright 2026 Microsoft Research. Apache 2.0. *)
(** Persistent points-to: ∃ q, l ↦{q} v  (Iris l ↦□ v)
    
    Duplicable because any fraction can be split: q → q/2 + q/2.
    Used for immutable heap data (e.g., Treiber stack nodes).
    
    This is NOT an atomic primitive — it's a derived concept built
    from fractional permissions. Only the read operation needs
    atomic support (a single load). *)
module Pulse.Lib.PersistentPtsTo
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box

(** ∃ q, l ↦{q} v — persistent/duplicable points-to. *)
let persistent_pts_to (#a:Type0) (r : B.box a) (v : a) : slprop =
  exists* (p:perm). B.pts_to r #p v

(** Convert full/fractional ownership to persistent. *)
ghost fn make_persistent (#a:Type0) (r : B.box a) (#v : erased a) (#p:perm)
  requires B.pts_to r #p v
  ensures persistent_pts_to r (reveal v)
{
  fold (persistent_pts_to r (reveal v))
}

(** Duplicate persistent ownership. *)
ghost fn dup_persistent (#a:Type0) (r : B.box a) (#v : a)
  requires persistent_pts_to r v
  ensures persistent_pts_to r v ** persistent_pts_to r v
{
  unfold persistent_pts_to;
  B.share r;
  fold (persistent_pts_to r v);
  fold (persistent_pts_to r v)
}

(** Read from persistent ownership — a non-atomic read.
    For use OUTSIDE invariants (no atomic step needed). *)
fn read_persistent (#a:Type0) (r : B.box a) (#v : erased a)
  preserves persistent_pts_to r (reveal v)
  returns x : a
  ensures pure (x == reveal v)
{
  dup_persistent r #(reveal v);
  unfold (persistent_pts_to r (reveal v));
  with p. assert (B.pts_to r #p (reveal v));
  let x = B.op_Bang r;
  drop_ (B.pts_to r #p (reveal v));
  x
}
