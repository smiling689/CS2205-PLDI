Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.AlgebraicStructure.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 布尔表达式的指称语义 *)

Module DntSem_SimpleWhile3.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2.

(** 在Coq中可以如下定义：*)

Definition true_sem: state -> Prop := Sets.full.

Definition false_sem: state -> Prop := ∅.

Definition lt_sem (D1 D2: state -> Z):
  state -> Prop :=
  fun s => D1 s < D2 s.

Definition and_sem (D1 D2: state -> Prop):
  state -> Prop :=
  D1 ∩ D2.

Definition not_sem (D: state -> Prop):
  state -> Prop :=
  Sets.complement D.

Fixpoint eval_expr_bool (e: expr_bool): state -> Prop :=
  match e with
  | ETrue =>
      true_sem
  | EFalse =>
      false_sem
  | ELt e1 e2 =>
      lt_sem (eval_expr_int e1) (eval_expr_int e2)
  | EAnd e1 e2 =>
      and_sem (eval_expr_bool e1) (eval_expr_bool e2)
  | ENot e1 =>
      not_sem (eval_expr_bool e1)
  end.

Notation "⟦ e ⟧" := (eval_expr_bool e)
  (at level 0, only printing, e custom prog_lang_entry at level 99).

Ltac get_prog_syntax x ::=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  | expr_bool => constr:(x)
  end.

Ltac any_eval' x ::=
  match goal with
  | |- _ -> Z    => exact (eval_expr_int x)
  | |- _ -> Prop => exact (eval_expr_bool x)
  | _            =>
    match type of x with
    | expr_int  => exact (eval_expr_int x)
    | expr_bool => exact (eval_expr_bool x)
    end
  end.

(** 与整数类型表达式的行为等价定义一样，我们也可以用函数相等定义布尔表达式行为等价。*)

Definition bequiv (e1 e2: expr_bool): Prop :=
  ⟦ e1 ⟧ == ⟦ e2 ⟧.

Notation "e1 '~=~' e2" := (bequiv e1 e2)
  (at level 69, no associativity, only printing).

Ltac any_equiv' x y ::=
  match type of x with
  | expr_int  => exact (iequiv x y)
  | expr_bool => exact (bequiv x y)
  | _         =>
      match type of y with
      | expr_int  => exact (iequiv x y)
      | expr_bool => exact (bequiv x y)
      end
  end.


(** 下面先证明三个语义算子_[lt_sem]_、_[and_sem]_与_[not_sem]_能保持函数相等，再利用
    函数相等的性质证明布尔表达式行为等价的性质。*)

#[export] Instance lt_sem_congr:
  Proper (func_equiv _ _ ==>
          func_equiv _ _ ==>
          Sets.equiv) lt_sem.
Proof.
  unfold Proper, respectful, lt_sem.
  unfold func_equiv, pointwise_relation.
  sets_unfold.
  intros D11 D12 H1 D21 D22 H2 s.
  rewrite H1, H2.
  tauto.
Qed.

#[export] Instance and_sem_congr:
  Proper (Sets.equiv ==>
          Sets.equiv ==>
          Sets.equiv) and_sem.
Proof.
  unfold Proper, respectful, and_sem.
  intros D11 D12 H1 D21 D22 H2.
  rewrite H1, H2.
  reflexivity.
Qed.

#[export] Instance not_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv) not_sem.
Proof.
  unfold Proper, respectful, not_sem.
  intros D1 D2 H.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance bequiv_equiv: Equivalence bequiv.
Proof.
  unfold bequiv.
  apply equiv_in_domain.
  apply Sets_equiv_equiv.
Qed.

#[export] Instance ELt_congr:
  Proper (iequiv ==> iequiv ==> bequiv) ELt.
Proof.
  unfold Proper, respectful, bequiv, iequiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance EAnd_congr:
  Proper (bequiv ==> bequiv ==> bequiv) EAnd.
Proof.
  unfold Proper, respectful, bequiv.
  intros; simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance ENot_congr:
  Proper (bequiv ==> bequiv) ENot.
Proof.
  unfold Proper, respectful, bequiv.
  intros; simpl.
  rewrite H.
  reflexivity.
Qed.

End DntSem_SimpleWhile3.

(** * 程序语句的指称语义定义 *)



(** * Coq中定义程序语句的指称语义 *)

Module DntSem_SimpleWhile4.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3.

Definition asgn_sem
             (X: var_name)
             (D: state -> Z)
             (s1 s2: state): Prop :=
  s2 X = D s1 /\ forall Y, X <> Y -> s2 Y = s1 Y.

Definition skip_sem: state -> state -> Prop :=
  Rels.id.

Definition seq_sem (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  D1 ∘ D2.

Definition test_true
             (D: state -> Prop):
  state -> state -> Prop :=
  Rels.test D.

Definition test_false
             (D: state -> Prop):
  state -> state -> Prop :=
  Rels.test (Sets.complement D).

Definition if_sem
             (D0: state -> Prop)
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  (test_true D0 ∘ D1) ∪ (test_false D0 ∘ D2).

Fixpoint iterLB
           (D0: state -> Prop)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => test_false D0
  | S n0 => test_true D0 ∘ D1 ∘ iterLB D0 D1 n0
  end.

Module WhileSem1.

(** 第一种定义方式 *)
Definition while_sem
             (D0: state -> Prop)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (iterLB D0 D1).

End WhileSem1.

Fixpoint boundedLB
           (D0: state -> Prop)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1 ∘ boundedLB D0 D1 n0) ∪
      (test_false D0)
  end.

Module WhileSem2.

(** 第二种定义方式 *)
Definition while_sem
             (D0: state -> Prop)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (boundedLB D0 D1).

End WhileSem2.

(** 我们选择第二种定义。*)

Export WhileSem2.


(** 下面是程序语句指称语义的递归定义。*)

Fixpoint eval_com (c: com): state -> state -> Prop :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr_int e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr_bool e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr_bool e) (eval_com c1)
  end.

Notation "⟦ c ⟧" := (eval_com c)
  (at level 0, only printing, c custom prog_lang_entry at level 99).

Ltac get_prog_syntax x ::=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  | expr_bool => constr:(x)
  | com => constr:(x)
  end.

Ltac any_eval' x ::=
  match goal with
  | |- _ -> Z    => exact (eval_expr_int x)
  | |- _ -> bool => exact (eval_expr_bool x)
  | |- _ -> Prop => exact (eval_com x)
  | _            =>
    match type of x with
    | expr_int  => exact (eval_expr_int x)
    | expr_bool => exact (eval_expr_bool x)
    | com       => exact (eval_com x)
    end
  end.

(** * 程序语句的行为等价 *)

(** 下面定义程序语句的行为等价。*)

Definition cequiv (c1 c2: com): Prop :=
  ⟦ c1 ⟧ == ⟦ c2 ⟧.

Notation "c1 '~=~' c2" := (cequiv c1 c2)
  (at level 69, no associativity, only printing).

Ltac any_equiv' x y ::=
  match type of x with
  | expr_int  => exact (iequiv x y)
  | expr_bool => exact (bequiv x y)
  | com       => exact (cequiv x y)
  | _         =>
      match type of y with
      | expr_int  => exact (iequiv x y)
      | expr_bool => exact (bequiv x y)
      | com       => exact (cequiv x y)
      end
  end.

(** 可以证明，赋值语句、顺序执行、if语句和while语句对应的语义算子_[asgn_sem]_、
    _[seq_sem]_、_[if_sem]_与_[while_sem]_能由相同的函数及集合计算得到相同的集合。其
    中，证明if语句和while语句性质时，需要先证明_[test_true]_和_[test_false]_能够由相
    同的函数计算得到相同的集合。*)

#[export] Instance asgn_sem_congr:
  Proper (eq ==> func_equiv _ _ ==> Sets.equiv) asgn_sem.
Proof.
  unfold Proper, respectful.
  intros x x' Hx D1 D2 H; subst x'.
  sets_unfold; intros s1 s2.
  unfold asgn_sem.
  rewrite H.
  tauto.
Qed.

#[export] Instance seq_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) seq_sem.
Proof. apply Rels_concat_congr. Qed.

#[export] Instance test_true_congr:
  Proper (Sets.equiv ==> Sets.equiv) test_true.
Proof.
  unfold Proper, respectful, test_true.
  intros.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance test_false_congr:
  Proper (Sets.equiv ==> Sets.equiv) test_false.
Proof.
  unfold Proper, respectful, test_false.
  intros.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance if_sem_congr:
  Proper (Sets.equiv ==>
          Sets.equiv ==>
          Sets.equiv ==>
          Sets.equiv) if_sem.
Proof.
  unfold Proper, respectful, if_sem.
  intros D01 D02 H0 D11 D12 H1 D21 D22 H2.
  rewrite H0, H1, H2.
  reflexivity.
Qed.

(** 下面证明Simplewhile程序语句行为等价的代数性质。*)

#[export] Instance cequiv_equiv: Equivalence cequiv.
Proof.
  unfold cequiv.
  apply equiv_in_domain.
  apply Sets_equiv_equiv.
Qed.

#[export] Instance CAsgn_congr:
  Proper (eq ==> iequiv ==> cequiv) CAsgn.
Proof.
  unfold Proper, respectful, cequiv, iequiv.
  intros; simpl.
  apply asgn_sem_congr; tauto.
Qed.

#[export] Instance CSeq_congr:
  Proper (cequiv ==> cequiv ==> cequiv) CSeq.
Proof.
  unfold Proper, respectful, cequiv.
  intros; simpl.
  apply seq_sem_congr; tauto.
Qed.

#[export] Instance CIf_congr:
  Proper (bequiv ==> cequiv ==> cequiv ==> cequiv) CIf.
Proof.
  unfold Proper, respectful, bequiv, cequiv; intros.
  intros; simpl.
  apply if_sem_congr; tauto.
Qed.

(** 更多关于程序行为的有用性质可以使用集合与关系的运算性质完成证明，_[seq_skip]_与
    _[skip_seq]_表明了删除顺序执行中多余的空语句不改变程序行为。*)

Lemma seq_skip:
  forall c, [[ c; skip ]] ~=~ c.
Proof.
  intros.
  unfold cequiv.
  simpl.
  unfold seq_sem, skip_sem.
  apply Rels_concat_id_r.
Qed.

Lemma skip_seq:
  forall c, [[ skip; c ]] ~=~ c.
Proof.
  intros.
  unfold cequiv.
  simpl.
  unfold seq_sem, skip_sem.
  apply Rels_concat_id_l.
Qed.

(** 类似的，_[seq_assoc]_表明顺序执行的结合顺序是不影响程序行为的，因此，所有实际的编
    程中都不需要在程序开发的过程中额外标明顺序执行的结合方式。*)

Lemma seq_assoc: forall c1 c2 c3,
  [[ (c1; c2); c3 ]] ~=~ [[ c1; (c2; c3) ]].
Proof.
  intros.
  unfold cequiv.
  simpl.
  unfold seq_sem.
  apply Rels_concat_assoc.
Qed.


(** * 复杂程序语句语义性质的证明 *)

(** 下面证明几条程序语句语义的一般性性质。我们首先可以证明，两种while语句语义的定义方式
    是等价的。*)

Lemma while_sem1_while_sem2_equiv:
  forall D0 D1,
    WhileSem1.while_sem D0 D1 ==
    WhileSem2.while_sem D0 D1.
Proof.
  intros.
  unfold WhileSem1.while_sem, while_sem.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_indexed_union_included.
    intros n.
    rewrite <- (Sets_included_indexed_union (S n)).
    induction n; simpl.
    - Sets_unfold; intros; tauto.
    - rewrite IHn; simpl.
      Sets_unfold; intros; tauto.
  + apply Sets_indexed_union_included.
    intros n.
    induction n; simpl.
    - apply Sets_empty_included.
    - rewrite IHn.
      clear n IHn.
      apply Sets_union_included.
      * rewrite Rels_concat_indexed_union_distr_l.
        rewrite Rels_concat_indexed_union_distr_l.
        apply Sets_indexed_union_included.
        intros n.
        rewrite <- (Sets_included_indexed_union (S n)).
        simpl.
        reflexivity.
      * rewrite <- (Sets_included_indexed_union O).
        simpl.
        reflexivity.
Qed.

(** 还可以证明，_[boundedLB]_是递增的。*)

Lemma boundedLB_inc1: forall D0 D1 n,
  boundedLB D0 D1 n ⊆ boundedLB D0 D1 (S n).
Proof.
  intros.
  induction n; simpl.
  + apply Sets_empty_included.
  + rewrite IHn at 1.
    reflexivity.
Qed.

Theorem boundedLB_inc: forall D0 D1 n m,
  boundedLB D0 D1 m ⊆ boundedLB D0 D1 (n + m).
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn.
    rewrite (boundedLB_inc1 D0 D1 (n + m)) at 1.
    simpl.
    reflexivity.
Qed.

#[export] Instance while_sem_congr:
  Proper (Sets.equiv ==>
          Sets.equiv ==>
          Sets.equiv) while_sem.
Proof.
  unfold Proper, respectful, while_sem.
  intros D01 D02 H0 D11 D12 H1.
  apply Sets_indexed_union_congr.
  intros n.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn, H0, H1.
    reflexivity.
Qed.

#[export] Instance CWhile_congr:
  Proper (bequiv ==> cequiv ==> cequiv) CWhile.
Proof.
  unfold Proper, respectful, bequiv, cequiv; intros.
  intros; simpl.
  apply while_sem_congr; tauto.
Qed.

(** 前面提到，while循环语句的行为也可以描述为：只要循环条件成立，就先执行循环体再重新执
    行循环。我们可以证明，我们目前定义的程序语义符合这一性质。*)

Lemma while_unroll1: forall e c,
  [[ while (e) do {c} ]] ~=~
  [[ if (e) then { c; while (e) do {c} } else {skip} ]].
Proof.
  unfold cequiv.
  intros; simpl.
  unfold while_sem, if_sem, seq_sem, skip_sem.
  rewrite Rels_concat_id_r.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_indexed_union_included.
    intros n.
    destruct n; simpl.
    - apply Sets_empty_included.
    - rewrite <- (Sets_included_indexed_union n).
      reflexivity.
  + apply Sets_union_included.
    - rewrite Rels_concat_indexed_union_distr_l.
      rewrite Rels_concat_indexed_union_distr_l.
      apply Sets_indexed_union_included; intros.
      rewrite <- (Sets_included_indexed_union (S n)).
      simpl.
      apply Sets_included_union1.
    - rewrite <- (Sets_included_indexed_union (S O)).
      simpl boundedLB.
      apply Sets_included_union2.
Qed.



End DntSem_SimpleWhile4.
