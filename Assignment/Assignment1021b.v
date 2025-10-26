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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact Sets_ex2:
  forall {A: Type} (x1 x2 y1 y2: A -> Prop),
    (x1 ∩ x2) ∪ (y1 ∩ y2) ⊆
    (x1 ∪ y1) ∩ (x2 ∪ y2).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact IndexUnion_ex1:
  forall {A: Type} (xs: nat -> A -> Prop),
    ⋃ (fun n => xs (2 * n)%nat) ⊆ ⋃ xs.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请试着在不使用_[sets_unfold]_或_[Sets_unfold]_的情况下证明下面集合运算的性质。*)

Fact IndexUnion_ex2:
  forall {A: Type} (xs: nat -> A -> Prop),
    (forall n m, (n <= m)%nat -> xs n ⊆ xs m) ->
    ⋃ (fun n => xs (2 * n)%nat) == ⋃ xs.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


