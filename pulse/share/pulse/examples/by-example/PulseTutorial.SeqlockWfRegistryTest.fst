module PulseTutorial.SeqlockWfRegistryTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Inv
module List = FStar.List.Tot
open FStar.List.Tot { (@) }
module GR = Pulse.Lib.GhostReference
module Reg = Pulse.Lib.SeqlockWfRegistry

let gamma0_name : Reg.lin_gname = GR.null #bool
let gamma1_name : Reg.lin_gname = GR.null #bool
let ver0 : nat = 7
let ver1 : nat = 9
let requests0 : Reg.registry = []
let req0 (write0_name:iname) : Reg.request = (gamma0_name, ver0, write0_name)
let req1 (write1_name:iname) : Reg.request = (gamma1_name, ver1, write1_name)
let requests1 (write0_name:iname) : Reg.registry = requests0 @ [req0 write0_name]
let requests2 (write0_name:iname) (write1_name:iname) : Reg.registry =
  requests1 write0_name @ [req1 write1_name]

ghost fn dispose_empty_inv (i:iname)
  requires inv i emp
  ensures emp
{
  drop_ (inv i emp)
}

let test_post (g:Reg.reg_gname) (write0_name:iname) (write1_name:iname) : slprop =
  Reg.registry_auth g 1.0R (requests2 write0_name write1_name) **
  Reg.registered g 0 gamma0_name ver0 write0_name #(requests1 write0_name) **
  Reg.registered g 1 gamma1_name ver1 write1_name #(requests2 write0_name write1_name)

ghost fn seqlock_wf_registry_test ()
  requires emp
  returns g:Reg.reg_gname
  ensures exists* (write0_name:iname) (write1_name:iname). test_post g write0_name write1_name
{
  let write0_name = new_invariant emp;
  dispose_empty_inv write0_name;
  let write1_name = new_invariant emp;
  dispose_empty_inv write1_name;

  let g = Reg.registry_alloc ();
  rewrite (Reg.registry_auth g 1.0R []) as (Reg.registry_auth g 1.0R requests0);

  Reg.registry_extend g #requests0 gamma0_name ver0 write0_name;
  rewrite (Reg.registry_auth g 1.0R (requests0 @ [(gamma0_name, ver0, write0_name)]))
    as (Reg.registry_auth g 1.0R (requests1 write0_name));
  rewrite (Reg.registered g (List.length requests0) gamma0_name ver0 write0_name #(requests0 @ [(gamma0_name, ver0, write0_name)]))
    as (Reg.registered g (List.length requests0) gamma0_name ver0 write0_name #(requests1 write0_name));

  Reg.registry_extend g #(requests1 write0_name) gamma1_name ver1 write1_name;
  rewrite (Reg.registry_auth g 1.0R ((requests1 write0_name) @ [(gamma1_name, ver1, write1_name)]))
    as (Reg.registry_auth g 1.0R (requests2 write0_name write1_name));
  rewrite (Reg.registered g (List.length (requests1 write0_name)) gamma1_name ver1 write1_name #((requests1 write0_name) @ [(gamma1_name, ver1, write1_name)]))
    as (Reg.registered g (List.length (requests1 write0_name)) gamma1_name ver1 write1_name #(requests2 write0_name write1_name));
  assert (pure (List.length requests0 == 0));
  assert (pure (List.length (requests1 write0_name) == 1));
  rewrite (Reg.registered g (List.length requests0) gamma0_name ver0 write0_name #(requests1 write0_name))
    as (Reg.registered g 0 gamma0_name ver0 write0_name #(requests1 write0_name));
  rewrite (Reg.registered g (List.length (requests1 write0_name)) gamma1_name ver1 write1_name #(requests2 write0_name write1_name))
    as (Reg.registered g 1 gamma1_name ver1 write1_name #(requests2 write0_name write1_name));

  Reg.registered_dup g 0 gamma0_name ver0 write0_name #(requests1 write0_name);
  Reg.registry_auth_frag_agree g 0 gamma0_name ver0 write0_name #(requests1 write0_name);
  Reg.registry_auth_frag_agree g 0 gamma0_name ver0 write0_name #(requests1 write0_name);
  Reg.registry_auth_frag_agree g 1 gamma1_name ver1 write1_name #(requests2 write0_name write1_name);

  fold (test_post g write0_name write1_name);
  intro_exists #iname (fun write1_name -> test_post g write0_name write1_name) write1_name;
  intro_exists #iname (fun write0_name -> exists* (write1_name:iname). test_post g write0_name write1_name) write0_name;
  g
}
