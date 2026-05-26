module Test_nested_inv
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Inv
open Pulse.Lib.AtomicPrimitives
module B = Pulse.Lib.Box

(* Nested with correct inames: outer accounts for inner opening *)
fn test_nested (r1 r2 : B.box int) (i1 i2 : iname)
  requires inv i1 (exists* v. B.pts_to r1 v) **
           inv i2 (exists* v. B.pts_to r2 v) **
           pure (i1 =!= i2)
  ensures  inv i1 (exists* v. B.pts_to r1 v) **
           inv i2 (exists* v. B.pts_to r2 v)
{
  later_credit_buy 1;
  later_credit_buy 1;
  (* Outer opens i1, but the body will also open i2.
     So body's inames = add_inv emp_inames i2 (it opens i2).
     Outer result inames = add_inv (add_inv emp_inames i2) i1. *)
  with_invariants_a unit (add_inv emp_inames i2) i1 (exists* v. B.pts_to r1 v)
    (inv i2 (exists* v. B.pts_to r2 v) ** later_credit 1)
    (fun _ -> inv i2 (exists* v. B.pts_to r2 v))
  fn _ {
    with_invariants_a unit emp_inames i2 (exists* v. B.pts_to r2 v)
      (exists* v. B.pts_to r1 v)
      (fun _ -> exists* v. B.pts_to r1 v)
    fn _ {
      atomic_write r2 42;
      fold (exists* v. B.pts_to r2 v)
    }
  }
}
