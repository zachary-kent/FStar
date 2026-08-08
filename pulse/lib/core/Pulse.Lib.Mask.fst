(*
   Public implementation of the abstract Pulse.Lib.Mask contract.

   All derived algebraic proofs below use only its primitive laws.
*)
module Pulse.Lib.Mask

module Core = Pulse.Lib.Core
module Contract = Pulse.Lib.Mask.PrimitiveContract

let mask = Contract.mask

let top = Contract.top
let empty = Contract.empty
let singleton = Contract.singleton

let union = Contract.union
let inter = Contract.inter
let diff = Contract.diff
let compl = Contract.compl

let mem = Contract.mem
let subset = Contract.subset
let disjoint = Contract.disjoint

let mem_top = Contract.mem_top
let mem_empty = Contract.mem_empty
let mem_singleton = Contract.mem_singleton
let mem_union = Contract.mem_union
let mem_inter = Contract.mem_inter
let mem_diff = Contract.mem_diff
let mem_compl = Contract.mem_compl
let subset_spec = Contract.subset_spec
let disjoint_spec = Contract.disjoint_spec
let ext = Contract.ext

(* Derived algebraic proof bodies. *)

let subset_refl (e:Contract.mask)
  : Lemma (Contract.subset e e)
  = Contract.subset_spec e e;
    let pointwise (i:Core.iname)
      : Lemma (Contract.mem i e ==> Contract.mem i e)
      = ()
    in
    FStar.Classical.forall_intro pointwise

let subset_trans (e f g:Contract.mask)
  : Lemma
      (requires (Contract.subset e f /\ Contract.subset f g))
      (ensures  (Contract.subset e g))
  = Contract.subset_spec e f;
    Contract.subset_spec f g;
    Contract.subset_spec e g;
    let pointwise (i:Core.iname)
      : Lemma (Contract.mem i e ==> Contract.mem i g)
      = ()
    in
    FStar.Classical.forall_intro pointwise

let subset_antisym (e f:Contract.mask)
  : Lemma
      (requires (Contract.subset e f /\ Contract.subset f e))
      (ensures  (e == f))
  = Contract.subset_spec e f;
    Contract.subset_spec f e;
    let pointwise (i:Core.iname)
      : Lemma (Contract.mem i e <==> Contract.mem i f)
      = ()
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext e f;
    ()

let eq_iff_subset (e f:Contract.mask)
  : Lemma (
      (e == f)
      <==> Contract.subset e f /\ Contract.subset f e
    )
  = let forward ()
      : Lemma
          (requires (e == f))
          (ensures  (Contract.subset e f /\ Contract.subset f e))
      = subset_refl e;
        subset_refl f;
        ()
    in
    let backward ()
      : Lemma
          (requires (Contract.subset e f /\ Contract.subset f e))
          (ensures  (e == f))
      = subset_antisym e f
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let empty_subset (e:Contract.mask)
  : Lemma (Contract.subset Contract.empty e)
  = Contract.subset_spec Contract.empty e;
    let pointwise (i:Core.iname)
      : Lemma (Contract.mem i Contract.empty ==> Contract.mem i e)
      = Contract.mem_empty i;
        ()
    in
    FStar.Classical.forall_intro pointwise

let subset_top (e:Contract.mask)
  : Lemma (Contract.subset e Contract.top)
  = Contract.subset_spec e Contract.top;
    let pointwise (i:Core.iname)
      : Lemma (Contract.mem i e ==> Contract.mem i Contract.top)
      = Contract.mem_top i;
        ()
    in
    FStar.Classical.forall_intro pointwise

let subset_union_iff (e f:Contract.mask)
  : Lemma (
      Contract.subset e f
      <==> Contract.union e f == f
    )
  = let forward ()
      : Lemma
          (requires (Contract.subset e f))
          (ensures  (Contract.union e f == f))
      = Contract.subset_spec e f;
        let pointwise (i:Core.iname)
          : Lemma (
              Contract.mem i (Contract.union e f)
              <==> Contract.mem i f
            )
          = Contract.mem_union i e f;
            ()
        in
        FStar.Classical.forall_intro pointwise;
        Contract.ext (Contract.union e f) f;
        ()
    in
    let backward ()
      : Lemma
          (requires (Contract.union e f == f))
          (ensures  (Contract.subset e f))
      = Contract.subset_spec e f;
        let pointwise (i:Core.iname)
          : Lemma (Contract.mem i e ==> Contract.mem i f)
          = Contract.mem_union i e f;
            ()
        in
        FStar.Classical.forall_intro pointwise;
        ()
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let subset_inter_iff (e f:Contract.mask)
  : Lemma (
      Contract.subset e f
      <==> Contract.inter e f == e
    )
  = let forward ()
      : Lemma
          (requires (Contract.subset e f))
          (ensures  (Contract.inter e f == e))
      = Contract.subset_spec e f;
        let pointwise (i:Core.iname)
          : Lemma (
              Contract.mem i (Contract.inter e f)
              <==> Contract.mem i e
            )
          = Contract.mem_inter i e f;
            ()
        in
        FStar.Classical.forall_intro pointwise;
        Contract.ext (Contract.inter e f) e;
        ()
    in
    let backward ()
      : Lemma
          (requires (Contract.inter e f == e))
          (ensures  (Contract.subset e f))
      = Contract.subset_spec e f;
        let pointwise (i:Core.iname)
          : Lemma (Contract.mem i e ==> Contract.mem i f)
          = Contract.mem_inter i e f;
            ()
        in
        FStar.Classical.forall_intro pointwise;
        ()
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let union_mono (e1 e2 f1 f2:Contract.mask)
  : Lemma
      (requires (Contract.subset e1 e2 /\ Contract.subset f1 f2))
      (ensures  (Contract.subset (Contract.union e1 f1) (Contract.union e2 f2)))
  = Contract.subset_spec e1 e2;
    Contract.subset_spec f1 f2;
    Contract.subset_spec (Contract.union e1 f1) (Contract.union e2 f2);
    let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e1 f1)
          ==> Contract.mem i (Contract.union e2 f2)
        )
      = Contract.mem_union i e1 f1;
        Contract.mem_union i e2 f2;
        ()
    in
    FStar.Classical.forall_intro pointwise

let inter_mono (e1 e2 f1 f2:Contract.mask)
  : Lemma
      (requires (Contract.subset e1 e2 /\ Contract.subset f1 f2))
      (ensures  (Contract.subset (Contract.inter e1 f1) (Contract.inter e2 f2)))
  = Contract.subset_spec e1 e2;
    Contract.subset_spec f1 f2;
    Contract.subset_spec (Contract.inter e1 f1) (Contract.inter e2 f2);
    let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e1 f1)
          ==> Contract.mem i (Contract.inter e2 f2)
        )
      = Contract.mem_inter i e1 f1;
        Contract.mem_inter i e2 f2;
        ()
    in
    FStar.Classical.forall_intro pointwise

let union_empty (e:Contract.mask)
  : Lemma (Contract.union e Contract.empty == e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e Contract.empty)
          <==> Contract.mem i e
        )
      = Contract.mem_union i e Contract.empty;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.union e Contract.empty) e

let union_top (e:Contract.mask)
  : Lemma (Contract.union e Contract.top == Contract.top)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e Contract.top)
          <==> Contract.mem i Contract.top
        )
      = Contract.mem_union i e Contract.top;
        Contract.mem_top i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.union e Contract.top) Contract.top

let union_idem (e:Contract.mask)
  : Lemma (Contract.union e e == e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e e)
          <==> Contract.mem i e
        )
      = Contract.mem_union i e e
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.union e e) e

let union_comm (e f:Contract.mask)
  : Lemma (Contract.union e f == Contract.union f e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e f)
          <==> Contract.mem i (Contract.union f e)
        )
      = Contract.mem_union i e f;
        Contract.mem_union i f e
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.union e f) (Contract.union f e)

let union_assoc (e f g:Contract.mask)
  : Lemma (
      Contract.union e (Contract.union f g)
      == Contract.union (Contract.union e f) g
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e (Contract.union f g))
          <==> Contract.mem i (Contract.union (Contract.union e f) g)
        )
      = Contract.mem_union i e (Contract.union f g);
        Contract.mem_union i f g;
        Contract.mem_union i (Contract.union e f) g;
        Contract.mem_union i e f
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.union e (Contract.union f g))
      (Contract.union (Contract.union e f) g)

let inter_empty (e:Contract.mask)
  : Lemma (Contract.inter e Contract.empty == Contract.empty)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e Contract.empty)
          <==> Contract.mem i Contract.empty
        )
      = Contract.mem_inter i e Contract.empty;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.inter e Contract.empty) Contract.empty;
    ()

let inter_top (e:Contract.mask)
  : Lemma (Contract.inter e Contract.top == e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e Contract.top)
          <==> Contract.mem i e
        )
      = Contract.mem_inter i e Contract.top;
        Contract.mem_top i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.inter e Contract.top) e;
    ()

let inter_idem (e:Contract.mask)
  : Lemma (Contract.inter e e == e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e e)
          <==> Contract.mem i e
        )
      = Contract.mem_inter i e e
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.inter e e) e;
    ()

let inter_comm (e f:Contract.mask)
  : Lemma (Contract.inter e f == Contract.inter f e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e f)
          <==> Contract.mem i (Contract.inter f e)
        )
      = Contract.mem_inter i e f;
        Contract.mem_inter i f e
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.inter e f) (Contract.inter f e);
    ()

let inter_assoc (e f g:Contract.mask)
  : Lemma (
      Contract.inter e (Contract.inter f g)
      == Contract.inter (Contract.inter e f) g
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e (Contract.inter f g))
          <==> Contract.mem i (Contract.inter (Contract.inter e f) g)
        )
      = Contract.mem_inter i e (Contract.inter f g);
        Contract.mem_inter i f g;
        Contract.mem_inter i (Contract.inter e f) g;
        Contract.mem_inter i e f
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.inter e (Contract.inter f g))
      (Contract.inter (Contract.inter e f) g);
    ()

let inter_union_absorb (e f:Contract.mask)
  : Lemma (Contract.inter e (Contract.union e f) == e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e (Contract.union e f))
          <==> Contract.mem i e
        )
      = Contract.mem_inter i e (Contract.union e f);
        Contract.mem_union i e f
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.inter e (Contract.union e f)) e;
    ()

let union_inter_absorb (e f:Contract.mask)
  : Lemma (Contract.union e (Contract.inter e f) == e)
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e (Contract.inter e f))
          <==> Contract.mem i e
        )
      = Contract.mem_union i e (Contract.inter e f);
        Contract.mem_inter i e f
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.union e (Contract.inter e f)) e;
    ()

let inter_union_distr (e f g:Contract.mask)
  : Lemma (
      Contract.inter e (Contract.union f g)
      == Contract.union (Contract.inter e f) (Contract.inter e g)
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.inter e (Contract.union f g))
          <==> Contract.mem i (Contract.union (Contract.inter e f) (Contract.inter e g))
        )
      = Contract.mem_inter i e (Contract.union f g);
        Contract.mem_union i f g;
        Contract.mem_union i (Contract.inter e f) (Contract.inter e g);
        Contract.mem_inter i e f;
        Contract.mem_inter i e g
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.inter e (Contract.union f g))
      (Contract.union (Contract.inter e f) (Contract.inter e g));
    ()

let union_inter_distr (e f g:Contract.mask)
  : Lemma (
      Contract.union e (Contract.inter f g)
      == Contract.inter (Contract.union e f) (Contract.union e g)
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union e (Contract.inter f g))
          <==> Contract.mem i (Contract.inter (Contract.union e f) (Contract.union e g))
        )
      = Contract.mem_union i e (Contract.inter f g);
        Contract.mem_inter i f g;
        Contract.mem_inter i (Contract.union e f) (Contract.union e g);
        Contract.mem_union i e f;
        Contract.mem_union i e g
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.union e (Contract.inter f g))
      (Contract.inter (Contract.union e f) (Contract.union e g));
    ()

let compl_empty (_:unit)
  : Lemma (Contract.compl Contract.empty == Contract.top)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.compl Contract.empty) <==> Contract.mem i Contract.top)
      = Contract.mem_compl i Contract.empty;
        Contract.mem_empty i;
        Contract.mem_top i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.compl Contract.empty) Contract.top;
    ()

let compl_top (_:unit)
  : Lemma (Contract.compl Contract.top == Contract.empty)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.compl Contract.top) <==> Contract.mem i Contract.empty)
      = Contract.mem_compl i Contract.top;
        Contract.mem_top i;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.compl Contract.top) Contract.empty;
    ()

let compl_involutive (e:Contract.mask)
  : Lemma (Contract.compl (Contract.compl e) == e)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.compl (Contract.compl e)) <==> Contract.mem i e)
      = Contract.mem_compl i (Contract.compl e);
        Contract.mem_compl i e;
        FStar.Classical.excluded_middle (Contract.mem i e)
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.compl (Contract.compl e)) e;
    ()

let union_compl (e:Contract.mask)
  : Lemma (Contract.union e (Contract.compl e) == Contract.top)
  = let pointwise i
      : Lemma (
          Contract.mem i (Contract.union e (Contract.compl e))
          <==> Contract.mem i Contract.top
        )
      = Contract.mem_union i e (Contract.compl e);
        Contract.mem_compl i e;
        Contract.mem_top i;
        FStar.Classical.excluded_middle (Contract.mem i e)
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.union e (Contract.compl e)) Contract.top;
    ()

let inter_compl (e:Contract.mask)
  : Lemma (Contract.inter e (Contract.compl e) == Contract.empty)
  = let pointwise i
      : Lemma (
          Contract.mem i (Contract.inter e (Contract.compl e))
          <==> Contract.mem i Contract.empty
        )
      = Contract.mem_inter i e (Contract.compl e);
        Contract.mem_compl i e;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.inter e (Contract.compl e)) Contract.empty;
    ()

let compl_union (e f:Contract.mask)
  : Lemma (
      Contract.compl (Contract.union e f)
      == Contract.inter (Contract.compl e) (Contract.compl f)
    )
  = let pointwise i
      : Lemma (
          Contract.mem i (Contract.compl (Contract.union e f))
          <==> Contract.mem i (Contract.inter (Contract.compl e) (Contract.compl f))
        )
      = Contract.mem_compl i (Contract.union e f);
        Contract.mem_union i e f;
        Contract.mem_inter i (Contract.compl e) (Contract.compl f);
        Contract.mem_compl i e;
        Contract.mem_compl i f
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.compl (Contract.union e f))
      (Contract.inter (Contract.compl e) (Contract.compl f));
    ()

let compl_inter (e f:Contract.mask)
  : Lemma (
      Contract.compl (Contract.inter e f)
      == Contract.union (Contract.compl e) (Contract.compl f)
    )
  = let pointwise i
      : Lemma (
          Contract.mem i (Contract.compl (Contract.inter e f))
          <==> Contract.mem i (Contract.union (Contract.compl e) (Contract.compl f))
        )
      = Contract.mem_compl i (Contract.inter e f);
        Contract.mem_inter i e f;
        Contract.mem_union i (Contract.compl e) (Contract.compl f);
        Contract.mem_compl i e;
        Contract.mem_compl i f;
        FStar.Classical.excluded_middle (Contract.mem i e);
        FStar.Classical.excluded_middle (Contract.mem i f)
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.compl (Contract.inter e f))
      (Contract.union (Contract.compl e) (Contract.compl f));
    ()

let compl_antitone (e f:Contract.mask)
  : Lemma (
      Contract.subset e f
      <==> Contract.subset (Contract.compl f) (Contract.compl e)
    )
  = let forward ()
      : Lemma
          (requires (Contract.subset e f))
          (ensures (Contract.subset (Contract.compl f) (Contract.compl e)))
      = Contract.subset_spec e f;
        Contract.subset_spec (Contract.compl f) (Contract.compl e);
        let pointwise i
          : Lemma (
              Contract.mem i (Contract.compl f)
              ==> Contract.mem i (Contract.compl e)
            )
          = Contract.mem_compl i f;
            Contract.mem_compl i e;
            ()
        in
        FStar.Classical.forall_intro pointwise
    in
    let backward ()
      : Lemma
          (requires (Contract.subset (Contract.compl f) (Contract.compl e)))
          (ensures (Contract.subset e f))
      = Contract.subset_spec (Contract.compl f) (Contract.compl e);
        Contract.subset_spec e f;
        let pointwise i
          : Lemma (Contract.mem i e ==> Contract.mem i f)
          = Contract.mem_compl i f;
            Contract.mem_compl i e;
            FStar.Classical.excluded_middle (Contract.mem i f)
        in
        FStar.Classical.forall_intro pointwise
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let diff_as_inter_compl (e f:Contract.mask)
  : Lemma (Contract.diff e f == Contract.inter e (Contract.compl f))
  = let pointwise i
      : Lemma (
          Contract.mem i (Contract.diff e f)
          <==> Contract.mem i (Contract.inter e (Contract.compl f))
        )
      = Contract.mem_diff i e f;
        Contract.mem_inter i e (Contract.compl f);
        Contract.mem_compl i f
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.diff e f) (Contract.inter e (Contract.compl f));
    ()

let diff_empty (e:Contract.mask)
  : Lemma (Contract.diff e Contract.empty == e)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.diff e Contract.empty) <==> Contract.mem i e)
      = Contract.mem_diff i e Contract.empty;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.diff e Contract.empty) e;
    ()

let empty_diff (e:Contract.mask)
  : Lemma (Contract.diff Contract.empty e == Contract.empty)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.diff Contract.empty e) <==> Contract.mem i Contract.empty)
      = Contract.mem_diff i Contract.empty e;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.diff Contract.empty e) Contract.empty;
    ()

let diff_self (e:Contract.mask)
  : Lemma (Contract.diff e e == Contract.empty)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.diff e e) <==> Contract.mem i Contract.empty)
      = Contract.mem_diff i e e;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.diff e e) Contract.empty;
    ()

let diff_top (e:Contract.mask)
  : Lemma (Contract.diff e Contract.top == Contract.empty)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.diff e Contract.top) <==> Contract.mem i Contract.empty)
      = Contract.mem_diff i e Contract.top;
        Contract.mem_top i;
        Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.diff e Contract.top) Contract.empty;
    ()

let top_diff (e:Contract.mask)
  : Lemma (Contract.diff Contract.top e == Contract.compl e)
  = let pointwise i
      : Lemma (Contract.mem i (Contract.diff Contract.top e) <==> Contract.mem i (Contract.compl e))
      = Contract.mem_diff i Contract.top e;
        Contract.mem_top i;
        Contract.mem_compl i e
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.diff Contract.top e) (Contract.compl e);
    ()

let diff_twice (e f:Contract.mask)
  : Lemma (Contract.diff (Contract.diff e f) f == Contract.diff e f)
  = let pointwise i
      : Lemma (
          Contract.mem i (Contract.diff (Contract.diff e f) f)
          <==> Contract.mem i (Contract.diff e f)
        )
      = Contract.mem_diff i (Contract.diff e f) f;
        Contract.mem_diff i e f
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.diff (Contract.diff e f) f) (Contract.diff e f);
    ()

let diff_diff_l (e f g:Contract.mask)
  : Lemma (
      Contract.diff (Contract.diff e f) g
      == Contract.diff e (Contract.union f g)
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.diff (Contract.diff e f) g)
          <==> Contract.mem i (Contract.diff e (Contract.union f g))
        )
      = Contract.mem_diff i (Contract.diff e f) g;
        Contract.mem_diff i e f;
        Contract.mem_diff i e (Contract.union f g);
        Contract.mem_union i f g
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.diff (Contract.diff e f) g)
      (Contract.diff e (Contract.union f g));
    ()

let diff_union_l (e f g:Contract.mask)
  : Lemma (
      Contract.diff (Contract.union e f) g
      == Contract.union (Contract.diff e g) (Contract.diff f g)
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.diff (Contract.union e f) g)
          <==> Contract.mem i (Contract.union (Contract.diff e g) (Contract.diff f g))
        )
      = Contract.mem_diff i (Contract.union e f) g;
        Contract.mem_union i e f;
        Contract.mem_union i (Contract.diff e g) (Contract.diff f g);
        Contract.mem_diff i e g;
        Contract.mem_diff i f g
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.diff (Contract.union e f) g)
      (Contract.union (Contract.diff e g) (Contract.diff f g));
    ()

let diff_union_r (e f g:Contract.mask)
  : Lemma (
      Contract.diff e (Contract.union f g)
      == Contract.inter (Contract.diff e f) (Contract.diff e g)
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.diff e (Contract.union f g))
          <==> Contract.mem i (Contract.inter (Contract.diff e f) (Contract.diff e g))
        )
      = Contract.mem_diff i e (Contract.union f g);
        Contract.mem_union i f g;
        Contract.mem_inter i (Contract.diff e f) (Contract.diff e g);
        Contract.mem_diff i e f;
        Contract.mem_diff i e g
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext
      (Contract.diff e (Contract.union f g))
      (Contract.inter (Contract.diff e f) (Contract.diff e g));
    ()

let diff_mono (e1 e2 f1 f2:Contract.mask)
  : Lemma
      (requires (Contract.subset e1 e2 /\ Contract.subset f2 f1))
      (ensures  (Contract.subset (Contract.diff e1 f1) (Contract.diff e2 f2)))
  = Contract.subset_spec e1 e2;
    Contract.subset_spec f2 f1;
    Contract.subset_spec (Contract.diff e1 f1) (Contract.diff e2 f2);
    let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.diff e1 f1)
          ==> Contract.mem i (Contract.diff e2 f2)
        )
      = Contract.mem_diff i e1 f1;
        Contract.mem_diff i e2 f2;
        ()
    in
    FStar.Classical.forall_intro pointwise

let subset_partition (e f:Contract.mask)
  : Lemma
      (requires (Contract.subset e f))
      (ensures (
        f == Contract.union e (Contract.diff f e) /\
        Contract.disjoint e (Contract.diff f e)
      ))
  = let recompose ()
      : Lemma (f == Contract.union e (Contract.diff f e))
      = Contract.subset_spec e f;
        let pointwise (i:Core.iname)
          : Lemma (
              Contract.mem i f
              <==> Contract.mem i (Contract.union e (Contract.diff f e))
            )
          = Contract.mem_union i e (Contract.diff f e);
            Contract.mem_diff i f e;
            FStar.Classical.excluded_middle (Contract.mem i e)
        in
        FStar.Classical.forall_intro pointwise;
        Contract.ext f (Contract.union e (Contract.diff f e));
        ()
    in
    let separate ()
      : Lemma (Contract.disjoint e (Contract.diff f e))
      = Contract.disjoint_spec e (Contract.diff f e);
        let pointwise (i:Core.iname)
          : Lemma (
              not (Contract.mem i e /\ Contract.mem i (Contract.diff f e))
            )
          = Contract.mem_diff i f e;
            ()
        in
        FStar.Classical.forall_intro pointwise
    in
    recompose ();
    separate ();
    ()

let diff_union_inter (e f:Contract.mask)
  : Lemma (
      Contract.union (Contract.diff e f) (Contract.inter e f) == e
    )
  = let pointwise (i:Core.iname)
      : Lemma (
          Contract.mem i (Contract.union (Contract.diff e f) (Contract.inter e f))
          <==> Contract.mem i e
        )
      = Contract.mem_union i (Contract.diff e f) (Contract.inter e f);
        Contract.mem_diff i e f;
        Contract.mem_inter i e f;
        FStar.Classical.excluded_middle (Contract.mem i f)
    in
    FStar.Classical.forall_intro pointwise;
    Contract.ext (Contract.union (Contract.diff e f) (Contract.inter e f)) e;
    ()

let disjoint_sym (e f:Contract.mask)
  : Lemma (Contract.disjoint e f <==> Contract.disjoint f e)
  = Contract.disjoint_spec e f;
    Contract.disjoint_spec f e;
    ()

let disjoint_empty (e:Contract.mask)
  : Lemma (Contract.disjoint e Contract.empty)
  = Contract.disjoint_spec e Contract.empty;
    let pointwise (i:Core.iname)
      : Lemma (not (Contract.mem i e /\ Contract.mem i Contract.empty))
      = Contract.mem_empty i
    in
    FStar.Classical.forall_intro pointwise;
    ()

let disjoint_inter_empty (e f:Contract.mask)
  : Lemma (Contract.disjoint e f <==> Contract.inter e f == Contract.empty)
  = let forward ()
      : Lemma
          (requires (Contract.disjoint e f))
          (ensures (Contract.inter e f == Contract.empty))
      = Contract.disjoint_spec e f;
        Contract.ext (Contract.inter e f) Contract.empty;
        let pointwise (i:Core.iname)
          : Lemma (
              Contract.mem i (Contract.inter e f)
              <==> Contract.mem i Contract.empty
            )
          = Contract.mem_inter i e f;
            Contract.mem_empty i;
            ()
        in
        FStar.Classical.forall_intro pointwise;
        ()
    in
    let backward ()
      : Lemma
          (requires (Contract.inter e f == Contract.empty))
          (ensures (Contract.disjoint e f))
      = Contract.disjoint_spec e f;
        let pointwise (i:Core.iname)
          : Lemma (not (Contract.mem i e /\ Contract.mem i f))
          = Contract.mem_inter i e f;
            Contract.mem_empty i;
            ()
        in
        FStar.Classical.forall_intro pointwise;
        ()
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let disjoint_compl_iff (e f:Contract.mask)
  : Lemma (
      Contract.disjoint e f
      <==> Contract.subset e (Contract.compl f)
    )
  = let forward ()
      : Lemma
          (requires (Contract.disjoint e f))
          (ensures (Contract.subset e (Contract.compl f)))
      = Contract.disjoint_spec e f;
        Contract.subset_spec e (Contract.compl f);
        let pointwise (i:Core.iname)
          : Lemma (Contract.mem i e ==> Contract.mem i (Contract.compl f))
          = Contract.mem_compl i f;
            ()
        in
        FStar.Classical.forall_intro pointwise
    in
    let backward ()
      : Lemma
          (requires (Contract.subset e (Contract.compl f)))
          (ensures (Contract.disjoint e f))
      = Contract.subset_spec e (Contract.compl f);
        Contract.disjoint_spec e f;
        let pointwise (i:Core.iname)
          : Lemma (not (Contract.mem i e /\ Contract.mem i f))
          = Contract.mem_compl i f;
            ()
        in
        FStar.Classical.forall_intro pointwise
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let disjoint_union (e f g:Contract.mask)
  : Lemma (
      Contract.disjoint e (Contract.union f g)
      <==> Contract.disjoint e f /\ Contract.disjoint e g
    )
  = let forward ()
      : Lemma
          (requires (Contract.disjoint e (Contract.union f g)))
          (ensures (Contract.disjoint e f /\ Contract.disjoint e g))
      = Contract.disjoint_spec e (Contract.union f g);
        Contract.disjoint_spec e f;
        let left (i:Core.iname)
          : Lemma (not (Contract.mem i e /\ Contract.mem i f))
          = Contract.mem_union i f g;
            ()
        in
        FStar.Classical.forall_intro left;
        Contract.disjoint_spec e g;
        let right (i:Core.iname)
          : Lemma (not (Contract.mem i e /\ Contract.mem i g))
          = Contract.mem_union i f g;
            ()
        in
        FStar.Classical.forall_intro right;
        ()
    in
    let backward ()
      : Lemma
          (requires (Contract.disjoint e f /\ Contract.disjoint e g))
          (ensures (Contract.disjoint e (Contract.union f g)))
      = Contract.disjoint_spec e f;
        Contract.disjoint_spec e g;
        Contract.disjoint_spec e (Contract.union f g);
        let pointwise (i:Core.iname)
          : Lemma (not (Contract.mem i e /\ Contract.mem i (Contract.union f g)))
          = Contract.mem_union i f g;
            ()
        in
        FStar.Classical.forall_intro pointwise
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let disjoint_mono (e' e f' f:Contract.mask)
  : Lemma
      (requires (
        Contract.subset e' e /\
        Contract.subset f' f /\
        Contract.disjoint e f
      ))
      (ensures (Contract.disjoint e' f'))
  = Contract.subset_spec e' e;
    Contract.subset_spec f' f;
    Contract.disjoint_spec e f;
    Contract.disjoint_spec e' f';
    let pointwise (i:Core.iname)
      : Lemma (not (Contract.mem i e' /\ Contract.mem i f'))
      = ()
    in
    FStar.Classical.forall_intro pointwise

let disjoint_diff (e f:Contract.mask)
  : Lemma (Contract.disjoint (Contract.diff e f) f)
  = Contract.disjoint_spec (Contract.diff e f) f;
    let pointwise (i:Core.iname)
      : Lemma (not (Contract.mem i (Contract.diff e f) /\ Contract.mem i f))
      = Contract.mem_diff i e f;
        ()
    in
    FStar.Classical.forall_intro pointwise

let disjoint_self_iff (e:Contract.mask)
  : Lemma (
      Contract.disjoint e e
      <==> e == Contract.empty
    )
  = let forward ()
      : Lemma
          (requires (Contract.disjoint e e))
          (ensures (e == Contract.empty))
      = Contract.disjoint_spec e e;
        let left ()
          : Lemma (Contract.subset e Contract.empty)
          = Contract.subset_spec e Contract.empty;
            let pointwise (i:Core.iname)
              : Lemma (Contract.mem i e ==> Contract.mem i Contract.empty)
              = Contract.mem_empty i;
                ()
            in
            FStar.Classical.forall_intro pointwise
        in
        let right ()
          : Lemma (Contract.subset Contract.empty e)
          = Contract.subset_spec Contract.empty e;
            let pointwise (i:Core.iname)
              : Lemma (Contract.mem i Contract.empty ==> Contract.mem i e)
              = Contract.mem_empty i;
                ()
            in
            FStar.Classical.forall_intro pointwise
        in
        left ();
        right ();
        subset_antisym e Contract.empty
    in
    let backward ()
      : Lemma
          (requires (e == Contract.empty))
          (ensures (Contract.disjoint e e))
      = disjoint_empty e
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let disjoint_top_iff (e:Contract.mask)
  : Lemma (
      Contract.disjoint Contract.top e
      <==> e == Contract.empty
    )
  = let forward ()
      : Lemma
          (requires (Contract.disjoint Contract.top e))
          (ensures (e == Contract.empty))
      = Contract.disjoint_spec Contract.top e;
        let left ()
          : Lemma (Contract.subset e Contract.empty)
          = Contract.subset_spec e Contract.empty;
            let pointwise (i:Core.iname)
              : Lemma (Contract.mem i e ==> Contract.mem i Contract.empty)
              = Contract.mem_top i;
                Contract.mem_empty i;
                ()
            in
            FStar.Classical.forall_intro pointwise
        in
        let right ()
          : Lemma (Contract.subset Contract.empty e)
          = Contract.subset_spec Contract.empty e;
            let pointwise (i:Core.iname)
              : Lemma (Contract.mem i Contract.empty ==> Contract.mem i e)
              = Contract.mem_empty i;
                ()
            in
            FStar.Classical.forall_intro pointwise
        in
        left ();
        right ();
        subset_antisym e Contract.empty
    in
    let backward ()
      : Lemma
          (requires (e == Contract.empty))
          (ensures (Contract.disjoint Contract.top e))
      = disjoint_empty Contract.top
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let singleton_subset_iff (i:Core.iname) (e:Contract.mask)
  : Lemma (
      Contract.subset (Contract.singleton i) e
      <==> Contract.mem i e
    )
  = let forward ()
      : Lemma
          (requires (Contract.subset (Contract.singleton i) e))
          (ensures (Contract.mem i e))
      = Contract.subset_spec (Contract.singleton i) e;
        Contract.mem_singleton i i;
        ()
    in
    let backward ()
      : Lemma
          (requires (Contract.mem i e))
          (ensures (Contract.subset (Contract.singleton i) e))
      = Contract.subset_spec (Contract.singleton i) e;
        let pointwise (j:Core.iname)
          : Lemma (
              Contract.mem j (Contract.singleton i)
              ==> Contract.mem j e
            )
          = Contract.mem_singleton j i;
            ()
        in
        FStar.Classical.forall_intro pointwise
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()

let singleton_disjoint_iff (i:Core.iname) (e:Contract.mask)
  : Lemma (
      Contract.disjoint (Contract.singleton i) e
      <==> not (Contract.mem i e)
    )
  = let forward ()
      : Lemma
          (requires (Contract.disjoint (Contract.singleton i) e))
          (ensures (not (Contract.mem i e)))
      = Contract.disjoint_spec (Contract.singleton i) e;
        Contract.mem_singleton i i;
        ()
    in
    let backward ()
      : Lemma
          (requires (not (Contract.mem i e)))
          (ensures (Contract.disjoint (Contract.singleton i) e))
      = Contract.disjoint_spec (Contract.singleton i) e;
        let pointwise (j:Core.iname)
          : Lemma (
              not (Contract.mem j (Contract.singleton i) /\ Contract.mem j e)
            )
          = Contract.mem_singleton j i;
            ()
        in
        FStar.Classical.forall_intro pointwise
    in
    FStar.Classical.move_requires forward ();
    FStar.Classical.move_requires backward ();
    ()
