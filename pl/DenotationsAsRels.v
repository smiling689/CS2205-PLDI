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


