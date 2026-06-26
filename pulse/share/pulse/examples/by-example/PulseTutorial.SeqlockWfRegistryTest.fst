module PulseTutorial.SeqlockWfRegistryTest
#lang-pulse
open Pulse.Lib.Pervasives
module List = FStar.List.Tot
open FStar.List.Tot { (@) }
module Reg = Pulse.Lib.SeqlockWfRegistry

let gamma0_name : Reg.lin_gname = hide 100
let gamma1_name : Reg.lin_gname = hide 200
let req0 : Reg.request = (gamma0_name, 7)
let req1 : Reg.request = (gamma1_name, 9)
let requests0 : Reg.registry = []
let requests1 : Reg.registry = [req0]
let requests2 : Reg.registry = [req0; req1]

ghost fn seqlock_wf_registry_test ()
  requires emp
  returns g:Reg.reg_gname
  ensures
    Reg.registry_auth g 1.0R requests2 **
    Reg.registered g 0 gamma0_name 7 #requests1 **
    Reg.registered g 1 gamma1_name 9 #requests2
{
  let g = Reg.registry_alloc ();

  Reg.registry_extend g gamma0_name 7;
  Reg.registry_extend g gamma1_name 9;

  Reg.registered_dup g 0 gamma0_name 7 #requests1;
  Reg.registry_auth_frag_agree g 0 gamma0_name 7 #requests1;
  Reg.registry_auth_frag_agree g 0 gamma0_name 7 #requests1;
  Reg.registry_auth_frag_agree g 1 gamma1_name 9 #requests2;

  g
}
