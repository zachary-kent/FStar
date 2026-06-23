module PulseTutorial.SeqlockHistoryTest
#lang-pulse
open Pulse.Lib.Pervasives
module List = FStar.List.Tot
open FStar.List.Tot { (@) }
module Hist = Pulse.Lib.SeqlockHistory

ghost fn seqlock_history_test ()
  requires emp
  returns gh:Hist.gname int
  ensures
    Hist.history_auth gh 1.0R [[1; 2; 3]; [4; 5; 6]] **
    Hist.history_frag gh 0 [1; 2; 3] #[[1; 2; 3]; [4; 5; 6]] **
    Hist.history_frag gh 1 [4; 5; 6] #[[1; 2; 3]; [4; 5; 6]]
{
  let h0 = [[1; 2; 3]];
  let h1 = [[1; 2; 3]; [4; 5; 6]];
  let gh = Hist.history_alloc h0;

  Hist.history_share gh;
  Hist.history_auth_auth_agree gh #(1.0R /. 2.0R) #(1.0R /. 2.0R) #h0 #h0;
  Hist.history_gather gh #(1.0R /. 2.0R) #(1.0R /. 2.0R) #h0 #h0;
  assert pure (((1.0R /. 2.0R) +. (1.0R /. 2.0R)) == 1.0R);
  rewrite each ((1.0R /. 2.0R) +. (1.0R /. 2.0R)) as 1.0R;

  Hist.history_extend gh [4; 5; 6];
  assert pure (h0 @ [[4; 5; 6]] == h1);
  rewrite each (h0 @ [[4; 5; 6]]) as h1;
  assert pure (List.length h0 == 1);
  rewrite each List.length h0 as 1;

  assert pure (List.nth h1 0 == Some [1; 2; 3]);
  Hist.history_frag_alloc gh 0 [1; 2; 3];

  assert pure (List.nth h1 1 == Some [4; 5; 6]);
  Hist.history_auth_frag_agree gh 1 [4; 5; 6] #h1;

  dup (Hist.history_frag gh 0 [1; 2; 3] #h1) ();
  Hist.history_auth_frag_agree gh 0 [1; 2; 3] #h1;
  Hist.history_auth_frag_agree gh 0 [1; 2; 3] #h1;
  rewrite each h1 as [[1; 2; 3]; [4; 5; 6]];
  gh
}
