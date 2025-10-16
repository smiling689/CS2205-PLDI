Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import PL.AlgebraicStructure.
Require Import PL.Syntax.
Local Open Scope string.
Local Open Scope Z.

(** * SimpleWhile整数类型表达式的指称语义 *)

Module StateModel_SimpleWhile1.
Import Lang_SimpleWhile.

(** 程序状态的定义：*)

(** 状态是一个变量名到整数的映射。*)
Definition state: Type := var_name -> Z.

End StateModel_SimpleWhile1.

Module DntSem_SimpleWhile1.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1.

(** 整数类型表达式的行为：*)

Fixpoint eval_expr_int (e: expr_int) (s: state) : Z :=
  match e with
  | EConst n => n
  | EVar X => s X
  | EAdd e1 e2 => eval_expr_int e1 s + eval_expr_int e2 s
  | ESub e1 e2 => eval_expr_int e1 s - eval_expr_int e2 s
  | EMul e1 e2 => eval_expr_int e1 s * eval_expr_int e2 s
  end.

Notation "⟦ e ⟧" := (eval_expr_int e)
  (at level 0, e custom prog_lang_entry at level 99).

(** 下面是两个具体的例子。*)

Example eval_example1: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  ⟦ "x" + "y" ⟧ s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Example eval_example2: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  ⟦ "x" * "y" + 1 ⟧ s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.


End DntSem_SimpleWhile1.

(** * 定义有符号64位运算的表达式语义 *)

(** 在表达式的指称语义中表示表达式求值错误（有符号64位整数的运算越界的情况）这一概
    念，数学上有两种常见方案。其一是将求值结果由“整数”改为“整数或求值失败”。*)


(** * 变量初始化与表达式语义 *)


(** * 行为等价 *)

Module DntSem_SimpleWhile1_Properties.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile1.

(** 基于整数类型表达式的语义定义_[eval_expr_int]_，我们可以定义整数类型表达式之
    间的行为等价（亦称语义等价）：两个表达式_[e1]_与_[e2]_是等价的当且仅当它们在
    任何程序状态上的求值结果都相同。*)

Definition iequiv (e1 e2: expr_int): Prop :=
  forall s, ⟦ e1 ⟧ s = ⟦ e2 ⟧ s.

(** 之后我们将在Coq中用_[e1 ~=~ e2]_表示_[iequiv e1 e2]_。*)

Notation "e1 '~=~' e2" := (iequiv e1 e2)
  (at level 69, no associativity).

Example iequiv_sample:
  [["x" + "x"]] ~=~ [["x" * 2]].
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

(** 下面罗列的都是整数类型表达式语义等价的例子。*)

Lemma zero_plus_equiv: forall (a: expr_int),
  [[0 + a]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma plus_zero_equiv: forall (a: expr_int),
  [[a + 0]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma minus_zero_equiv: forall (a: expr_int),
  [[a - 0]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma zero_mult_equiv: forall (a: expr_int),
  [[0 * a]] ~=~ 0.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma mult_zero_equiv: forall (a: expr_int),
  [[a * 0]] ~=~ 0.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma const_plus_const: forall n m: Z,
  [[EConst n + EConst m]] ~=~ EConst (n + m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_minus_const: forall n m: Z,
  [[EConst n - EConst m]] ~=~ EConst (n - m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_mult_const: forall n m: Z,
  [[EConst n * EConst m]] ~=~ EConst (n * m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面SimpleWhile中整数类型表达式的行为等价。*)

Lemma plus_plus_assoc:
  forall a b c: expr_int,
    [[ a + (b + c) ]] ~=~ [[ a + b + c ]].
Proof.
    intros.
    unfold iequiv.
    intros.
    simpl.
    lia.
Qed.

Lemma plus_minus_assoc:
  forall a b c: expr_int,
    [[ a + (b - c) ]] ~=~ [[ a + b - c ]].
Proof.
    intros.
    unfold iequiv.
    intros.
    simpl.
    lia.
Qed.

Lemma minus_plus_assoc:
  forall a b c: expr_int,
    [[ a - (b + c) ]] ~=~ [[ a - b - c ]].
Proof.
    intros.
    unfold iequiv.
    intros.
    simpl.
    lia.
Qed.

Lemma minus_minus_assoc:
  forall a b c: expr_int,
    [[ a - (b - c) ]] ~=~ [[ a - b + c ]].
Proof.
    intros.
    unfold iequiv.
    intros.
    simpl.
    lia.
Qed.


(** * 行为等价的性质 *)

(** 整数类型表达式之间的行为等价符合下面几条重要的代数性质。*)

(** 下面要证明的是，行为等价是自反的。*)

#[export] Instance iequiv_refl: Reflexive iequiv.
Proof.
    unfold iequiv.
  unfold Reflexive, iequiv.
  intros.
  reflexivity.
Qed.

#[export] Instance iequiv_symm: Symmetric iequiv.
Proof.
  unfold Symmetric, iequiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance iequiv_trans: Transitive iequiv.
Proof.
  unfold Transitive, iequiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

(** 这个的意思是，行为等价是自反的。*)
#[export] Instance iequiv_equiv: Equivalence iequiv.
Proof.
  split.
  + apply iequiv_refl.
  + apply iequiv_symm.
  + apply iequiv_trans.
Qed.

#[export] Instance EAdd_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) EAdd.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance ESub_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) ESub.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance EMul_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) EMul.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

(** 利用这些代数性质，我们可以重新证明证明以下命题。*)

Fact iequiv_ex0:
  forall (a: expr_int) (n m: Z),
    [[ a + (EConst n) + (EConst m) ]] ~=~
    EAdd a (EConst (n + m)).
Proof.
  intros.
  rewrite <- plus_plus_assoc.
  rewrite const_plus_const.
  reflexivity.
Qed.


End DntSem_SimpleWhile1_Properties.

(** * 利用高阶函数定义指称语义 *)

Module DntSem_SimpleWhile2.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1.

Definition add_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s + D2 s.

Definition sub_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s - D2 s.

Definition mul_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s * D2 s.


Check add_sem.

(** 可以看到_[add_sem]_的类型是_[(state -> Z) -> (state -> Z) -> state -> Z]_，
    这既可以被看做一个三元函数，也可以被看做一个二元函数，即函数之间的二元函数。

    基于上面这三个用高阶函数定义的语义算子，可以重新定义整数类型表达式的指称语义。*)

Definition const_sem (n: Z): state -> Z := 
  fun s => n.

Definition var_sem (X: var_name): state -> Z :=
  fun s => s X.

Fixpoint eval_expr_int (e: expr_int): state -> Z :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      add_sem (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      sub_sem (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      mul_sem (eval_expr_int e1) (eval_expr_int e2)
  end.

(** 下面我们同样引入_[⟦ e ⟧]_这个Notation，并且_[unfold_sem]_这个证明指令用于展开
    语义相关的定义。*)

Notation "⟦ e ⟧" := (eval_expr_int e)
  (at level 0, only printing, e custom prog_lang_entry at level 99).

Ltac get_prog_syntax x :=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  end.

Ltac any_eval' x :=
  match goal with
  | |- _ -> Z => exact (eval_expr_int x)
  | _         => 
    match type of x with
    | expr_int => exact (eval_expr_int x)
    end
  end.

Ltac any_eval x :=
  let x' := get_prog_syntax x in
  any_eval' x'.

Notation "⟦ x ⟧" := (ltac:(any_eval x))
  (at level 0, only parsing, x custom prog_lang_entry at level 99).

(** 可以证明，前面定义的三个语义函数都能保持函数相等。*)

#[export] Instance add_sem_congr:
  Proper (func_equiv _ _ ==>
          func_equiv _ _ ==>
          func_equiv _ _) add_sem.
Proof.
  unfold Proper, respectful,
         func_equiv, pointwise_relation.
  intros D11 D12 H1 D21 D22 H2.
  unfold add_sem.
  intros s.
  rewrite H1, H2.
  reflexivity.
Qed.

#[export] Instance sub_sem_congr:
  Proper (func_equiv _ _ ==>
          func_equiv _ _ ==>
          func_equiv _ _) sub_sem.
Proof.
  unfold Proper, respectful,
         func_equiv, pointwise_relation.
  intros D11 D12 H1 D21 D22 H2.
  unfold sub_sem.
  intros s.
  rewrite H1, H2.
  reflexivity.
Qed.

#[export] Instance mul_sem_congr:
  Proper (func_equiv _ _ ==>
          func_equiv _ _ ==>
          func_equiv _ _) mul_sem.
Proof.
  unfold Proper, respectful,
         func_equiv, pointwise_relation.
  intros D11 D12 H1 D21 D22 H2.
  unfold mul_sem.
  intros s.
  rewrite H1, H2.
  reflexivity.
Qed.


(** 同时，我们也可以用函数相等来定义表达式行为等价和并利用函数相等的代数性质来证明行为
    等价的代数性质。*)

Definition iequiv (e1 e2: expr_int): Prop :=
  (⟦ e1 ⟧ == ⟦ e2 ⟧)%func.

Notation "e1 '~=~' e2" := (iequiv e1 e2)
  (at level 69, no associativity, only printing).

Ltac any_equiv' x y :=
  exact (iequiv x y).

Ltac any_equiv x y :=
  let x' := get_prog_syntax x in
  let y' := get_prog_syntax y in
  any_equiv' x' y'.

Notation "e1 '~=~' e2" := (ltac:(any_equiv e1 e2))
  (at level 69, no associativity, only parsing).

#[export] Instance iequiv_equiv: Equivalence iequiv.
Proof.
  unfold iequiv.
  apply equiv_in_domain.
  apply func_equiv_equiv.
Qed.

#[export] Instance EAdd_congr:
  Proper (iequiv ==> iequiv ==> iequiv) EAdd.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply add_sem_congr; tauto.
Qed.

#[export] Instance ESub_congr:
  Proper (iequiv ==> iequiv ==> iequiv) ESub.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply sub_sem_congr; tauto.
Qed.

#[export] Instance EMul_congr:
  Proper (iequiv ==> iequiv ==> iequiv) EMul.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply mul_sem_congr; tauto.
Qed.



End DntSem_SimpleWhile2.
