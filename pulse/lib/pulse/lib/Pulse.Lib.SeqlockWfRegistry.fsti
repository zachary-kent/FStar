module Pulse.Lib.SeqlockWfRegistry
#lang-pulse
open Pulse.Lib.Pervasives
module List = FStar.List.Tot
open FStar.List.Tot { (@) }
module GR = Pulse.Lib.GhostReference

(* Per-request linearization ghost name.  The registry stores the actual
   half-fractional bool ghost reference used by request_inv/write_inv, plus
   the concrete Pulse invariant name for this request's write_inv. *)
unopteq
type lin_gname = {
  lin_ref : GR.ref bool;
  write_i : iname;
}

type request = lin_gname & nat

type registry = list request

(* Ghost name for a registry instance. *)
[@@erasable]
val reg_gname : Type0

instance val non_informative_reg_gname : NonInformative.non_informative reg_gname

(* Authoritative ownership of the registry at fractional permission q. *)
val registry_auth (g:reg_gname) (q:perm) (requests:registry) : slprop

(* Persistent fragment witnessing that index i contains (gamma_l, ver).
   The hidden snapshot parameter is inferred from the operation that produced
   the fragment; agreement with current authority follows from prefix monotonicity. *)
[@@allow_ambiguous]
val registered (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry) : slprop

(* Explicit duplicability operation for clients that prefer not to use dup. *)
ghost fn registered_dup (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  requires registered g i gamma_l ver #snap
  ensures registered g i gamma_l ver #snap ** registered g i gamma_l ver #snap

(* registered fragments are duplicable. *)
[@@erasable]
instance val duplicable_registered (g:reg_gname) (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  : duplicable (registered g i gamma_l ver #snap)

(* Allocate an empty registry AND empty excluded set; return full authority on both. *)
ghost fn registry_alloc (_:unit)
  requires emp
  returns g:reg_gname
  ensures registry_auth g 1.0R [] ** excluded g 1.0R []

(* Fractional split/gather. *)
ghost fn registry_share (g:reg_gname) (#q:perm) (#requests:registry)
  requires registry_auth g q requests
  ensures registry_auth g (q /. 2.0R) requests ** registry_auth g (q /. 2.0R) requests

[@@allow_ambiguous]
ghost fn registry_gather (g:reg_gname) (#q1 #q2:perm) (#r1 #r2:registry)
  requires registry_auth g q1 r1 ** registry_auth g q2 r2
  ensures registry_auth g (q1 +. q2) r1 ** pure (r1 == r2)

(* Auth/auth agreement. *)
[@@allow_ambiguous]
ghost fn registry_auth_auth_agree (g:reg_gname) (#q1 #q2:perm) (#r1 #r2:registry)
  preserves registry_auth g q1 r1 ** registry_auth g q2 r2
  ensures pure (r1 == r2)

(* Extend: append a new request. Returns a fragment at the new index. *)
ghost fn registry_extend (g:reg_gname) (#requests:registry) (gamma_l:lin_gname) (ver:nat)
  requires registry_auth g 1.0R requests
  ensures registry_auth g 1.0R (requests @ [(gamma_l, ver)]) **
          registered g (List.length requests) gamma_l ver #(requests @ [(gamma_l, ver)])

(* From auth at any fraction: derive a fragment for an existing index. *)
ghost fn registered_alloc (g:reg_gname) (#q:perm) (#requests:registry)
    (i:nat) (gamma_l:lin_gname) (ver:nat)
  requires registry_auth g q requests ** pure (List.nth requests i == Some (gamma_l, ver))
  ensures registry_auth g q requests ** registered g i gamma_l ver #requests

(* Frag/auth agreement: index i lookup matches the fragment. *)
ghost fn registry_auth_frag_agree (g:reg_gname) (#q:perm) (#requests:registry)
    (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  requires registry_auth g q requests ** registered g i gamma_l ver #snap
  ensures registry_auth g q requests ** registered g i gamma_l ver #snap **
          pure (List.nth requests i == Some (gamma_l, ver))

(* ------------------------------------------------------------------------ *)
(* Excluded-inames tracker                                                  *)
(* ------------------------------------------------------------------------ *)
(* A monotonic list of inames that every (current and future) entry's
   [write_i] is guaranteed to be disjoint from.  Established by [commit_excl]
   when the caller proves disjointness against the current registry; preserved
   by [registry_extend_excl] which requires the new write_i to be fresh
   against the current excluded set.

   This is the mechanism used by helping protocols (such as SeqlockWf's
   final-store linearization) to discharge the Pulse mask-discipline
   obligation [write_i =!= n_seqlock] when opening many per-request
   invariants under an open seqlock_inv. *)

(* List of excluded inames; conceptually a set, ordered by insertion. *)
val excluded (g:reg_gname) (q:perm) (excl:list iname) : slprop

(* Persistent witness that a particular iname has been committed to the
   excluded set. *)
[@@allow_ambiguous]
val excl_witness (g:reg_gname) (n:iname) : slprop

ghost fn excl_witness_dup (g:reg_gname) (n:iname)
  requires excl_witness g n
  ensures excl_witness g n ** excl_witness g n

[@@erasable]
instance val duplicable_excl_witness (g:reg_gname) (n:iname)
  : duplicable (excl_witness g n)

(* Fractional split/gather on the excluded authority. *)
ghost fn excluded_share (g:reg_gname) (#q:perm) (#excl:list iname)
  requires excluded g q excl
  ensures excluded g (q /. 2.0R) excl ** excluded g (q /. 2.0R) excl

[@@allow_ambiguous]
ghost fn excluded_gather (g:reg_gname) (#q1 #q2:perm) (#e1 #e2:list iname)
  requires excluded g q1 e1 ** excluded g q2 e2
  ensures excluded g (q1 +. q2) e1 ** pure (e1 == e2)

(* Commit a new excluded iname.  Requires the caller to prove that every
   currently registered entry's write_i differs from n.  This is the
   bootstrapping step performed once per seqlock invariant at allocation
   time. *)
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

(* Persistent witness + authority ⇒ every current entry excludes n. *)
[@@allow_ambiguous]
ghost fn excl_witness_implies_disjoint (g:reg_gname) (n:iname)
    (#q:perm) (#requests:registry)
  preserves registry_auth g q requests ** excl_witness g n
  ensures pure (forall (k:nat). k < List.length requests ==>
               (match List.nth requests k with
                | Some (gamma_l, _) -> gamma_l.write_i =!= n
                | None -> True))

(* Persistent witness + registered fragment ⇒ that specific entry excludes n. *)
[@@allow_ambiguous]
ghost fn excl_witness_excl_entry (g:reg_gname) (n:iname)
    (i:nat) (gamma_l:lin_gname) (ver:nat) (#snap:registry)
  preserves registered g i gamma_l ver #snap ** excl_witness g n
  ensures pure (gamma_l.write_i =!= n)

(* registry_extend with explicit freshness against the excluded set.  The
   caller (a writer at registration) obtains the freshness from a
   [fresh_invariant ctx ...] call where [ctx] contains the current excluded
   inames. *)
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

