Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope sets.
Local Open Scope Z.

(** 本次作业共有4题。后两题是关于无穷并集的。无穷并集的运算性质与普通并集运算的性质是类
    似的，请你阅读课程附件材料后完成。评分时，后两题记为附加分。*)

(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact Sets_ex1:
  forall {A: Type} (x y z: A -> Prop),
    x ⊆ y ->
    x ∪ z ⊆ z ∪ y.
Proof.
  intros A x y z Hxy.
  apply Sets_union_included.
  - transitivity y.
    + exact Hxy.
    + apply Sets_included_union2.
  - apply Sets_included_union1.
Qed.


(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)


Fact Sets_ex2:
  forall {A: Type} (x1 x2 y1 y2: A -> Prop),
    (x1 ∩ x2) ∪ (y1 ∩ y2) ⊆
    (x1 ∪ y1) ∩ (x2 ∪ y2).
Proof.
  intros A x1 x2 y1 y2.
  apply Sets_included_intersect.
  - apply Sets_union_included.
    + transitivity x1.
      * rewrite Sets_intersect_included1.
        reflexivity.
      * apply Sets_included_union1.
    + transitivity y1.
      * rewrite Sets_intersect_included1.
        reflexivity.
      * apply Sets_included_union2.
  - apply Sets_union_included.
    + transitivity x2.
      * rewrite Sets_intersect_included2.
        reflexivity.
      * apply Sets_included_union1.
    + transitivity y2.
      * rewrite Sets_intersect_included2.
        reflexivity.
      * apply Sets_included_union2.
Qed.




(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact IndexUnion_ex1:
  forall {A: Type} (xs: nat -> A -> Prop),
    ⋃ (fun n => xs (2 * n)%nat) ⊆ ⋃ xs.
Proof.
    intros A xs.
    apply Sets_indexed_union_included.
    intros.
    apply Sets_included_indexed_union.
Qed.






(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)



Fact IndexUnion_ex2:
  forall {A: Type} (xs: nat -> A -> Prop),
    (forall n m, (n <= m)%nat -> xs n ⊆ xs m) ->
    ⋃ (fun n => xs (2 * n)%nat) == ⋃ xs.
Proof.
    intros A xs H.
    apply Sets_equiv_Sets_included; split.
    - apply IndexUnion_ex1.
    - intros a Ha.
    (** 这里老是apply不成功，不知道为啥，于是摆了，手动写一遍*)
      cbv [Sets.indexed_union Sets.lift_indexed_union] in Ha |- *.
      destruct Ha as [k Hk].
      assert (Hle : (k <= 2 * k)%nat) by lia.
      specialize (H k (2 * k)%nat Hle) as Hinc.
      specialize (Hinc a) as Hinca.
      exists k.
      exact (Hinca Hk).
Qed.
