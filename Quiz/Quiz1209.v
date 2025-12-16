Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List. Import ListNotations.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
Require Import PL.Monad.
Require Import PL.Kleene.
Require Import PL.FixedPoint.
Require Import PL.MonadHoare.
Local Open Scope Z.
Local Open Scope list.

Import Monad
       MonadNotation
       SetMonadExamples0
       SetMonadExamples2
       SetMonadExamples3
       SetMonadHoare
       KleeneFix Sets_CPO.
Local Open Scope monad.

(************)
(** 习题：  *)
(************)

(** 请证明下面程序的性质。*)

Definition body_count (n: Z) (x: Z): SetMonad.M (ContinueOrBreak Z Z) :=
  choice
    (assume (x < n);; continue (x + 1))
    (assume (~ (x < n));; break x).

Definition count (n: Z): SetMonad.M Z :=
  repeat_break (body_count n) 0.

Theorem functional_correctness_count:
  forall n,
    0 < n ->
    Hoare (count n) (fun x => x = n).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请证明下面程序的性质。*)

Definition body_slow_div (n m: Z):
  Z * Z -> SetMonad.M (ContinueOrBreak (Z * Z) (Z * Z)) :=
  fun '(x, y) =>
    choice
      (assume (x < n);; break (x, y))
      (assume (~ (x < n));; continue (x - n, y + 1)).

Definition slow_div (n m: Z): SetMonad.M (Z * Z) :=
  repeat_break (body_slow_div n m) (m, 0).

Theorem functional_correctness_slow_div:
  forall n m,
    0 < n ->
    0 <= m ->
    Hoare (slow_div n m)
          (fun '(x, y) => x + n * y = m /\ 0 <= x < n).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

Definition insertion_body (x: Z):
  list Z * list Z -> SetMonad.M (ContinueOrBreak (list Z * list Z) (list Z)) :=
  fun '(l1, l2) =>
    match l2 with
    | nil => break (l1 ++ [x])
    | cons y l2' =>
        choice
          (assume (x <= y);; break (l1 ++ [x] ++ l2))
          (assume (y <= x);; continue (l1 ++ [y], l2'))
    end.

Definition insertion (x: Z) (l: list Z): SetMonad.M (list Z) :=
  repeat_break (insertion_body x) (nil, l).

Theorem insertion_perm:
  forall x l,
    Hoare
      (insertion x l)
      (fun l0 => Permutation (l ++ [x]) l0).
Proof.
  intros x l.
  unfold insertion.
  apply (Hoare_repeat_break _
           (fun '(l1, l2) => Permutation l (l1 ++ l2))).
  2: { simpl. change (Permutation l l). apply Permutation_refl. }
  intros [l1 l2] Hperm.
  unfold insertion_body.
  destruct l2 as [| y l2'].
  - apply Hoare_ret.
    rewrite app_nil_r in Hperm.
    apply Permutation_app; [exact Hperm | reflexivity].
  - apply Hoare_choice; apply Hoare_assume_bind; intros.
    + apply Hoare_ret.
      assert (Permutation (l ++ [x]) ((l1 ++ y :: l2') ++ [x]))
        by (apply Permutation_app_tail, Hperm).
      assert (Permutation ((l1 ++ y :: l2') ++ [x]) (l1 ++ [x] ++ y :: l2')).
      { rewrite <- app_assoc.
        apply Permutation_app_head.
        apply Permutation_app_comm.
      }
      eapply Permutation_trans; eauto.
    + apply Hoare_ret.
      simpl.
      replace ((l1 ++ [y]) ++ l2') with (l1 ++ y :: l2') by (rewrite <- app_assoc; simpl; reflexivity).
      exact Hperm.
Qed.

Lemma incr_app_le: forall l x,
  incr l ->
  (forall z, In z l -> z <= x) ->
  incr (l ++ [x]).
Proof.
  induction l as [| a l IH]; intros; simpl in *.
  - tauto.
  - destruct l as [| b l].
    + split; [apply H0; simpl; auto | tauto].
    + destruct H as [? ?].
      split; [tauto |].
      apply IH; [tauto |].
      intros z ?.
      apply H0.
      simpl; right; tauto.
Qed.


Theorem insertion_incr:
  forall x l,
    incr l ->
    Hoare
      (insertion x l)
      (fun l0 => incr l0).
Proof.
  intros x l Hincr.
  unfold insertion.
  apply (Hoare_repeat_break _
           (fun '(l1, l2) =>
              incr (l1 ++ l2) /\
              incr l1 /\
              (forall z, In z l1 -> z <= x))).
  2: { simpl. repeat split; auto. intros; tauto. }
  intros [l1 l2] [Hsorted [Hsorted1 Hle]].
  unfold insertion_body.
  destruct l2 as [| y l2'].
  - apply Hoare_ret.
    apply incr_app_le; assumption.
  - apply Hoare_choice; apply Hoare_assume_bind; intros.
    + apply Hoare_ret.
      pose proof (incr_app_cons_inv2 l1 y l2' Hsorted) as Hy_tail.
      apply incr_app_cons.
      * apply incr_app_le; assumption.
      * simpl. split; [assumption | exact Hy_tail].
    + apply Hoare_ret.
      split; [| split].
      * rewrite <- app_assoc. simpl. exact Hsorted.
      * pose proof (incr_app_cons_inv1 l1 y l2' Hsorted) as Hprefix.
        exact Hprefix.
      * intros z Hz.
        apply in_app_or in Hz.
        destruct Hz as [Hz | Hz].
        { apply Hle in Hz. exact Hz. }
        { simpl in Hz. destruct Hz as [Hz | ?]; [subst; assumption | tauto]. }
Qed.

(** 列表迭代辅助定义与引理。 *)

Fixpoint list_iter
           {A B: Type}
           (f: A -> B -> SetMonad.M B)
           (l: list A)
           (b: B):
  SetMonad.M B :=
  match l with
  | nil => ret b
  | a :: l0 => b0 <- f a b;; list_iter f l0 b0
  end.

Lemma Hoare_list_iter_aux {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall l2 b l1,
       P l1 b ->
       Hoare (list_iter f l2 b) (fun b0 => P (l1 ++ l2) b0)).
Proof.
  intros f P H l2.
  induction l2; intros; simpl.
  + apply Hoare_ret.
    rewrite app_nil_r.
    tauto.
  + apply (Hoare_bind _ _ (fun b0 : B => P (l1 ++ [a]) b0)).
    - apply H.
      apply H0.
    - intros b0 H1.
      pose proof IHl2 b0 (l1 ++ [a]) H1.
      rewrite <- app_assoc in H2.
      simpl in H2.
      apply H2.
Qed.

Theorem Hoare_list_iter {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall b l, P nil b -> Hoare (list_iter f l b) (fun b0 => P l b0)).
Proof.
  intros.
  pose proof Hoare_list_iter_aux f P H l b nil.
  tauto.
Qed.

(************)
(** 习题：  *)
(************)

Definition ins_sort (l: list Z) :=
  list_iter insertion l nil.

Theorem ins_sort_perm:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l).
Proof.
  intros L.
  unfold ins_sort.
  apply (Hoare_list_iter
           insertion
           (fun l acc => Permutation l acc)).
  - intros b l a Hperm.
    eapply Hoare_conseq.
    2: { apply insertion_perm. }
    intros b0 Hb0.
    eapply Permutation_trans; [| exact Hb0 ].
    apply Permutation_app; [exact Hperm | reflexivity].
  - simpl. apply Permutation_refl.
Qed.

Theorem ins_sort_incr:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => incr l).
Proof.
  intros L.
  unfold ins_sort.
  apply (Hoare_list_iter
           insertion
    (fun _ acc => incr acc)).
  - intros b l a Hincr.
    eapply Hoare_conseq; [| apply insertion_incr; exact Hincr ].
    intros; tauto.
  - simpl. tauto.
Qed.

Theorem functional_correctness_ins_sort:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l /\ incr l).
Proof.
  intros.
  apply Hoare_conjunct.
  + apply ins_sort_perm.
  + apply ins_sort_incr.
Qed.


Module AssocUnit.

(** 下面我们结合先前所学，来证明一些关于结合律、单位元和幂运算的性质。在数学上，
    如果一个二元运算有结合律，那么在书写时就可以省略括号，忽略结合顺序。更进一
    步，在结合律的基础上可以引入幂运算。例如，_[a ∘ (a ∘ a) = (a ∘ a) ∘ a]_，所
    以我们可以用_[a]_的立方来表示这个等式两边的值。下面我们在Coq中定义这些概念并
    且证明一些性质。*)

Class AssocUnitOperator (A: Type): Type := {
  unit: A;
  op: A -> A -> A
}.

(** 我们同样引入一些Notation来表示此处我们讨论的单位元与二元运算。*)

Notation "1" := (unit).
Notation "x * y" := (op x y) (left associativity, at level 40).

(** 我们假设该二元运算符合结合律、左单位元性质与右单位元性质。*)

Class AssocUnitProperties (A: Type) {AU: AssocUnitOperator A}: Prop := {
  assoc: forall (x y z: A), (x * y) * z = x * (y * z);
  left_unit: forall (x: A), 1 * x = x;
  right_unit: forall (x: A), x * 1 = x
}.

(** 在Coq中，可以用Section与Context关键字统一引入一下假设与前提，这些假设与前提
    会在End处失效。*)

Section AssocUnit.

Context {A: Type}
        {AU: AssocUnitOperator A}
        {AUP: AssocUnitProperties A}.

(** 幂运算可以在Coq中对自然数归纳定义：*)

Fixpoint power (x: A) (n: nat): A :=
  match n with
  | O => unit
  | S n' => power x n' * x
  end.

(** 根据上面定义，_[x]_就是_[x]_本身的一次幂。*)

Lemma power_1: forall x, x = power x 1.
Proof.
  intros.
  simpl.
  rewrite left_unit.
  reflexivity.
Qed.

(** _[x ∘ x]_就是_[x]_本身的二次幂。*)

Lemma power_2: forall x, x * x = power x 2.
Proof.
  intros.
  simpl.
  rewrite left_unit.
  reflexivity.
Qed.

(** 下面证明幂运算的性质：*)

Lemma power_mul_power:
  forall x n m, power x n * power x m = power x (n + m).
Proof.
  intros x n m.
  induction m as [| m IH]; simpl.
  - rewrite right_unit.
    rewrite Nat.add_0_r.
    reflexivity.
  - rewrite <- assoc.
    rewrite IH.
    rewrite Nat.add_succ_r.
    simpl. reflexivity.
Qed.

Lemma power_power: 
  forall x n m, power (power x m) n = power x (n * m).
Proof.
    intros.
    induction n.
    +simpl.
    reflexivity.
    +simpl.
    assert (m+n*m=n*m + m)%nat.
    lia.
    rewrite H.
    rewrite <-power_mul_power.
    rewrite IHn.
    reflexivity.
Qed.

End AssocUnit.
End AssocUnit.

Module FastPower.
Import AssocUnit.
Local Open Scope sets.

Section FastPower.

(** 快速幂算法的伪代码非常简单：

result = unit;
while (n > 0) {
  if (n % 2 == 1) {
    result = result * base;
  }
  n = n / 2;
  base = base * base;
}

    它适用于一切具有结合律与单位元的二元运算。在刻画该算法并证明其正确性时，我们
    可以引用先前定义的相关假设。*)

Context {A: Type}
        {AU: AssocUnitOperator A}
        {AUP: AssocUnitProperties A}.

Definition body_fast_power:
  nat * A * A -> SetMonad.M (ContinueOrBreak (nat * A * A) A) :=
  fun '(exp, base, res) =>
    choice
      (assume (exp = 0%nat);; break res)
      (choice
         (assume(Nat.Even exp);;
          continue ((exp/2)%nat, base * base, res))
         (assume(Nat.Odd exp);;
          continue ((exp/2)%nat, base * base, res * base))).

Definition fast_power (n: nat) (a: A): SetMonad.M A :=
  repeat_break body_fast_power (n, a, 1).


Lemma Nat_Even_fact: forall n,
  Nat.Even n ->
  (n = 2 * (n / 2))%nat.
Proof.
  intros.
  pose proof Nat.Even_double n H.
  pose proof Nat.double_twice (n / 2).
  pose proof Nat.div2_div n.
  lia.
Qed.

Lemma Nat_Odd_fact: forall n,
  Nat.Odd n ->
  (n = 1 + 2 * (n / 2))%nat.
Proof.
  intros.
  pose proof Nat.Odd_double n H.
  pose proof Nat.double_twice (n / 2).
  pose proof Nat.div2_div n.
  lia.
Qed.

Theorem body_fast_power_sound:
  forall (exp: nat) (base: A),
    Hoare
      (fast_power exp base)
      (fun res => res = power base exp).
Proof.
    intros.
    unfold fast_power.
    apply (Hoare_repeat_break _ (fun '(exp', base', res') => res' * power base' exp' = power base exp)).
    2: {
        rewrite <-left_unit.
        tauto.
    }
    intros [[exp' base'] res'] Hinv.
    unfold body_fast_power.
    repeat apply Hoare_choice.
    - apply Hoare_assume_bind.
      intros.
      assert (exp' = 0%nat).
      + lia.
      + apply Hoare_ret.
        subst.
        rewrite 