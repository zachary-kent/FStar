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

(* Allocate an empty registry; return full authority. *)
ghost fn registry_alloc (_:unit)
  requires emp
  returns g:reg_gname
  ensures registry_auth g 1.0R []

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
