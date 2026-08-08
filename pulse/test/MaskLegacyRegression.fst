module MaskLegacyRegression

#lang-pulse

open Pulse.Lib.Pervasives

module Inv = Pulse.Lib.Inv
module CInv = Pulse.Lib.CancellableInvariant
module CV = Pulse.Lib.ConditionVar
module FInv = Pulse.Lib.FlippableInv
module Pledge = Pulse.Lib.Pledge

(* Raw compatibility terms remain in the legacy inames vocabulary. *)
let raw_inames_identity (i:iname) = assert (
  add_inv emp_inames i
  ==
  join_inames (single i) emp_inames
)

let raw_inames_list_identity (i:iname) = assert (
  iname_list [i]
  ==
  add_inv emp_inames i
)

type raw_inames_footprint (is:inames) (i:iname) =
  (mem_iname (add_inv (remove_inv (join_inames is emp_inames) i) i) i,
   mem_inv (remove_inv all_inames i),
   inames_subset emp_inames (join_inames is (single i)),
   emp_inames /! all_inames)

(* Reproduce the type-level forms exercised by PulseFnTerms. *)
type atomic_action_with_opens (is:inames) =
  atomic fn (_u:unit) opens is requires emp ensures emp

type ghost_action_with_opens (is:inames) =
  ghost fn (_u:unit) opens is requires emp ensures emp

fn call_atomic_action_with_opens
  (is:inames)
  (f: atomic fn (_u:unit) opens is requires emp ensures emp)
  requires emp
  ensures emp
{
  f ()
}

fn call_ghost_action_with_opens
  (is:inames)
  (f: ghost fn (_u:unit) opens is requires emp ensures emp)
  requires emp
  ensures emp
{
  f ()
}

unobservable fn legacy_with_inv_unobs (i:iname)
  requires Inv.inv i emp
  requires later_credit 1
  ensures emp
  opens [i]
{
  Inv.with_inv_unobs unit emp_inames i emp emp (fun _ -> emp) fn _ {
    ()
  }
}

ghost fn legacy_with_invariants_g (i:iname)
  requires Inv.inv i emp
  requires later_credit 1
  ensures Inv.inv i emp
  opens [i]
{
  Inv.with_invariants_g unit emp_inames i emp emp (fun _ -> emp) fn _ {
    ()
  }
}

atomic fn legacy_with_invariants_a (i:iname)
  requires Inv.inv i emp
  requires later_credit 1
  ensures Inv.inv i emp
  opens [i]
{
  Inv.with_invariants_a unit emp_inames i emp emp (fun _ -> emp) fn _ {
    ()
  }
}

fn legacy_with_invariants (i:iname)
  requires Inv.inv i emp
  ensures Inv.inv i emp
{
  Inv.with_invariants unit emp_inames i emp emp (fun _ -> emp) fn _ {
    ()
  }
}

ghost fn legacy_fresh_invariant (ctx:fin_inames)
  requires emp
  returns i:iname
  ensures Inv.inv i emp
  ensures pure (~(Pulse.Lib.GhostSet.mem i ctx))
{
  Inv.fresh_invariant ctx emp
}

ghost fn legacy_new_invariant ()
  requires emp
  returns i:iname
  ensures Inv.inv i emp
{
  Inv.new_invariant emp
}

ghost fn legacy_cancellable_cancel (c:CInv.cinv)
  requires Inv.inv (CInv.iname_of c) (CInv.cinv_vp c emp)
  requires CInv.active c 1.0R
  requires later_credit 1
  ensures emp
  opens [CInv.iname_of c]
{
  CInv.cancel c
}

atomic fn legacy_condition_signal_atomic (c:CV.cvar_t)
  requires CV.send c emp
  requires emp
  requires later_credit 1
  ensures emp
  opens [CV.inv_name c]
{
  CV.signal_atomic c #emp
}

fn legacy_condition_signal (c:CV.cvar_t)
  requires CV.send c emp
  requires emp
  ensures emp
{
  CV.signal c #emp
}

ghost fn legacy_condition_split (c:CV.cvar_t)
  requires CV.recv c (emp ** emp)
  requires later_credit 2
  ensures CV.recv c emp
  ensures CV.recv c emp
  opens [CV.inv_name c]
{
  CV.split c #emp #emp #_ #_;
  ()
}

ghost fn legacy_flip_cycle (fi:FInv.finv emp)
  requires FInv.off fi
  requires later_credit 2
  ensures FInv.off fi
  opens [FInv.iname_of fi]
{
  later_credit_add 1 1;
  rewrite (later_credit 2) as (later_credit 1 ** later_credit 1);
  FInv.flip_on fi;
  FInv.flip_off fi;
}

ghost fn legacy_pledge_finite (is:inames)
  requires Pledge.pledge is emp emp
  ensures Pledge.pledge is emp emp
  ensures pure (Pulse.Lib.GhostSet.is_finite is)
{
  Pledge.pledge_inames_finite is emp emp
}

ghost fn legacy_pledge_subset
  (is1:inames)
  (is2:fin_inames {inames_subset is1 is2})
  requires Pledge.pledge is1 emp emp
  ensures Pledge.pledge is2 emp emp
{
  Pledge.pledge_sub_inv is1 is2 emp emp
}

ghost fn legacy_make_pledge (is:fin_inames)
  requires emp
  ensures Pledge.pledge is emp emp
{
  Pledge.make_pledge is emp emp emp #_ fn _ {
    ()
  }
}

ghost fn legacy_redeem_pledge (is:inames)
  requires Pledge.pledge is emp emp
  ensures emp
  ensures pure (Pulse.Lib.GhostSet.is_finite is)
  opens is
{
  Pledge.redeem_pledge is emp emp
}
