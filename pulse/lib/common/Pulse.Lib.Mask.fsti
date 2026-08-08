(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.Mask

module Core = Pulse.Lib.Core

[@@ erasable]
val mask : Type0

val top       : mask
val empty     : mask
val singleton : Core.iname -> mask

val union : mask -> mask -> mask
val inter : mask -> mask -> mask
val diff  : mask -> mask -> mask
val compl : mask -> mask

val mem      : Core.iname -> mask -> prop
val subset   : mask -> mask -> prop
val disjoint : mask -> mask -> prop

val mem_top (i:Core.iname)
  : Lemma (mem i top)

val mem_empty (i:Core.iname)
  : Lemma (not (mem i empty))

val mem_singleton (i j:Core.iname)
  : Lemma (mem i (singleton j) <==> i == j)

val mem_union (i:Core.iname) (e f:mask)
  : Lemma (mem i (union e f) <==> mem i e \/ mem i f)

val mem_inter (i:Core.iname) (e f:mask)
  : Lemma (mem i (inter e f) <==> mem i e /\ mem i f)

val mem_diff (i:Core.iname) (e f:mask)
  : Lemma (
      mem i (diff e f)
      <==> mem i e /\ not (mem i f)
    )

val mem_compl (i:Core.iname) (e:mask)
  : Lemma (mem i (compl e) <==> not (mem i e))

val subset_spec (e f:mask)
  : Lemma (
      subset e f
      <==> forall (i:Core.iname). mem i e ==> mem i f
    )

val disjoint_spec (e f:mask)
  : Lemma (
      disjoint e f
      <==> forall (i:Core.iname).
            not (mem i e /\ mem i f)
    )

val ext (e f:mask)
  : Lemma (
      (e == f)
      <==> forall (i:Core.iname).
            (mem i e <==> mem i f)
    )

val subset_refl (e:mask)
  : Lemma (subset e e)

val subset_trans (e f g:mask)
  : Lemma
      (requires (subset e f /\ subset f g))
      (ensures  (subset e g))

val subset_antisym (e f:mask)
  : Lemma
      (requires (subset e f /\ subset f e))
      (ensures  (e == f))

val eq_iff_subset (e f:mask)
  : Lemma (
      (e == f)
      <==> subset e f /\ subset f e
    )

val empty_subset (e:mask)
  : Lemma (subset empty e)

val subset_top (e:mask)
  : Lemma (subset e top)

val subset_union_iff (e f:mask)
  : Lemma (
      subset e f
      <==> union e f == f
    )

val subset_inter_iff (e f:mask)
  : Lemma (
      subset e f
      <==> inter e f == e
    )

val union_mono (e1 e2 f1 f2:mask)
  : Lemma
      (requires (subset e1 e2 /\ subset f1 f2))
      (ensures  (subset (union e1 f1) (union e2 f2)))

val inter_mono (e1 e2 f1 f2:mask)
  : Lemma
      (requires (subset e1 e2 /\ subset f1 f2))
      (ensures  (subset (inter e1 f1) (inter e2 f2)))

val union_empty (e:mask)
  : Lemma (union e empty == e)

val union_top (e:mask)
  : Lemma (union e top == top)

val union_idem (e:mask)
  : Lemma (union e e == e)

val union_comm (e f:mask)
  : Lemma (union e f == union f e)

val union_assoc (e f g:mask)
  : Lemma (
      union e (union f g)
      == union (union e f) g
    )

val inter_empty (e:mask)
  : Lemma (inter e empty == empty)

val inter_top (e:mask)
  : Lemma (inter e top == e)

val inter_idem (e:mask)
  : Lemma (inter e e == e)

val inter_comm (e f:mask)
  : Lemma (inter e f == inter f e)

val inter_assoc (e f g:mask)
  : Lemma (
      inter e (inter f g)
      == inter (inter e f) g
    )

val inter_union_absorb (e f:mask)
  : Lemma (
      inter e (union e f) == e
    )

val union_inter_absorb (e f:mask)
  : Lemma (
      union e (inter e f) == e
    )

val inter_union_distr (e f g:mask)
  : Lemma (
      inter e (union f g)
      == union (inter e f) (inter e g)
    )

val union_inter_distr (e f g:mask)
  : Lemma (
      union e (inter f g)
      == inter (union e f) (union e g)
    )

val compl_empty (_:unit)
  : Lemma (compl empty == top)

val compl_top (_:unit)
  : Lemma (compl top == empty)

val compl_involutive (e:mask)
  : Lemma (compl (compl e) == e)

val union_compl (e:mask)
  : Lemma (union e (compl e) == top)

val inter_compl (e:mask)
  : Lemma (inter e (compl e) == empty)

val compl_union (e f:mask)
  : Lemma (
      compl (union e f)
      == inter (compl e) (compl f)
    )

val compl_inter (e f:mask)
  : Lemma (
      compl (inter e f)
      == union (compl e) (compl f)
    )

val compl_antitone (e f:mask)
  : Lemma (
      subset e f
      <==> subset (compl f) (compl e)
    )

val diff_as_inter_compl (e f:mask)
  : Lemma (
      diff e f == inter e (compl f)
    )

val diff_empty (e:mask)
  : Lemma (diff e empty == e)

val empty_diff (e:mask)
  : Lemma (diff empty e == empty)

val diff_self (e:mask)
  : Lemma (diff e e == empty)

val diff_top (e:mask)
  : Lemma (diff e top == empty)

val top_diff (e:mask)
  : Lemma (diff top e == compl e)

val diff_twice (e f:mask)
  : Lemma (
      diff (diff e f) f == diff e f
    )

val diff_diff_l (e f g:mask)
  : Lemma (
      diff (diff e f) g
      == diff e (union f g)
    )

val diff_union_l (e f g:mask)
  : Lemma (
      diff (union e f) g
      == union (diff e g) (diff f g)
    )

val diff_union_r (e f g:mask)
  : Lemma (
      diff e (union f g)
      == inter (diff e f) (diff e g)
    )

val diff_mono (e1 e2 f1 f2:mask)
  : Lemma
      (requires (subset e1 e2 /\ subset f2 f1))
      (ensures  (subset (diff e1 f1) (diff e2 f2)))

val subset_partition (e f:mask)
  : Lemma
      (requires (subset e f))
      (ensures (
        f == union e (diff f e) /\
        disjoint e (diff f e)
      ))

val diff_union_inter (e f:mask)
  : Lemma (
      union (diff e f) (inter e f) == e
    )

val disjoint_sym (e f:mask)
  : Lemma (
      disjoint e f <==> disjoint f e
    )

val disjoint_empty (e:mask)
  : Lemma (disjoint e empty)

val disjoint_inter_empty (e f:mask)
  : Lemma (
      disjoint e f
      <==> inter e f == empty
    )

val disjoint_compl_iff (e f:mask)
  : Lemma (
      disjoint e f
      <==> subset e (compl f)
    )

val disjoint_union (e f g:mask)
  : Lemma (
      disjoint e (union f g)
      <==> disjoint e f /\ disjoint e g
    )

val disjoint_mono (e' e f' f:mask)
  : Lemma
      (requires (
        subset e' e /\
        subset f' f /\
        disjoint e f
      ))
      (ensures (disjoint e' f'))

val disjoint_diff (e f:mask)
  : Lemma (disjoint (diff e f) f)

val disjoint_self_iff (e:mask)
  : Lemma (
      disjoint e e
      <==> e == empty
    )

val disjoint_top_iff (e:mask)
  : Lemma (
      disjoint top e
      <==> e == empty
    )

val singleton_subset_iff (i:Core.iname) (e:mask)
  : Lemma (
      subset (singleton i) e
      <==> mem i e
    )

val singleton_disjoint_iff (i:Core.iname) (e:mask)
  : Lemma (
      disjoint (singleton i) e
      <==> not (mem i e)
    )
