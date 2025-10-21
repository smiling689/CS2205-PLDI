Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import PL.AlgebraicStructure.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Import StateModel_SimpleWhile1.
Local Open Scope string.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 下面我们考虑将SimpleWhile语言中整数类型表达式的语法稍作拓展，增加“负号”和取绝对值
    这两个一元运算。请你定义它的指称语义，并证明它的基本性质。其中，定义取绝对值的语义
    时，你可能需要用到标准库中的这个绝对值函数：_[Z.abs: Z -> Z -> Z]_。

    下面是新的整数类型表达式语法。*)

Inductive expr_int : Type :=
  | EConst (n: Z): expr_int
  | EVar (x: var_name): expr_int
  | EAdd (e1 e2: expr_int): expr_int
  | ESub (e1 e2: expr_int): expr_int
  | EMul (e1 e2: expr_int): expr_int
  | ENeg (e: expr_int): expr_int
  | EAbs (e: expr_int): expr_int.

(** 下面是Notation的规定，你可以跳过这一段代码。*)

Definition EVar': string -> expr_int := EVar.
Coercion EConst: Z >-> expr_int.
Coercion EVar: var_name >-> expr_int.
Coercion EVar': string >-> expr_int.
Notation "[[ e ]]" := e
  (at level 0, e custom prog_lang_entry at level 99).
Notation "( x )" := x
  (in custom prog_lang_entry, x custom prog_lang_entry at level 99).
Notation "x" := x
  (in custom prog_lang_entry at level 0, x constr at level 0).
Notation "f x" := (f x)
  (in custom prog_lang_entry at level 1, only parsing,
   f custom prog_lang_entry,
   x custom prog_lang_entry at level 0).
Notation "'ABS' ( x )" := (EAbs x)
  (in custom prog_lang_entry at level 3).
Notation "- x" := (ENeg x)
  (in custom prog_lang_entry at level 11).
Notation "x * y" := (EMul x y)
  (in custom prog_lang_entry at level 10, left associativity).
Notation "x + y" := (EAdd x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x - y" := (ESub x y)
  (in custom prog_lang_entry at level 12, left associativity).

(** 基于这些Notation，你可以在后续定义或者例子中写出以下的表达式。*)

Check [[ - "x"]].
Check [[ - "x" + 3]].
Check [[ - ("x" + 3) * 2]].
Check [[ ABS ("x")]].
Check [[ - "y" * ABS ("x")]].
Check [[ "x" - (- (- (- (- "y")))) ]].
(** 下面是你的任务。

    第一步：请你定义新的语义算子。以下代码是我们之前定义的语义算子，你可以直接使用，也
    供你在定义“负号”与“取绝对值”对应的语义算子时用作参考。*)

Definition add_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s + D2 s.

Definition sub_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s - D2 s.

Definition mul_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s * D2 s.

Definition const_sem (n: Z): state -> Z := 
  fun s => n.

Definition var_sem (X: var_name): state -> Z :=
  fun s => s X.

Definition neg_sem (D: state -> Z) (s: state): Z :=
  - D s.

Definition abs_sem (D: state -> Z) (s: state): Z :=
  Z.abs (D s).

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
  | ENeg e1 =>
      neg_sem (eval_expr_int e1)
  | EAbs e1 =>
      abs_sem (eval_expr_int e1)
  end.

Notation "⟦ e ⟧" := (eval_expr_int e)
  (at level 0, e custom prog_lang_entry at level 99).

Definition iequiv (e1 e2: expr_int): Prop :=
  (⟦ e1 ⟧ == ⟦ e2 ⟧)%func.

Notation "e1 '~=~' e2" := (iequiv e1 e2)
  (at level 69, no associativity).


(** 第二步：请你基于上述语义算子（包括提供给你的算子以及你自己定义的算子）定义新的整数
    类型表达式指称语义。以下是SimpleWhile语义的整数类型表达式指称语义定义，供你参考。

   
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
      



    以下代码可以用于引入“⟦ ⟧”这个记号。你需要的话可以加上这行代码，或者做必要修改后加上
    这段代码。

   
      Notation "⟦ e ⟧" := (eval_expr_int e)
        (at level 0, e custom prog_lang_entry at level 99).
      


    第三步：请你定义行为等价。这是我们原先为SimpleWhile语言做的定义，供你参考。

   
      Definition iequiv (e1 e2: expr_int): Prop :=
        (⟦ e1 ⟧ == ⟦ e2 ⟧)%func.
      


    以下代码可以用于引入“~=~”这个记号。你需要的话可以加上这行代码，或者做必要修改后加上
    这段代码。

   
      Notation "e1 '~=~' e2" := (iequiv e1 e2)
        (at level 69, no associativity).
      


    第四步：请你证明，所有语义算子都能保持函数相等。以下代码是我们之前对_[add_sem]_等
    三个语义算子做得证明。供你参考。你还需要针对“负号”与“取绝对值”相关的语义算子做证
    明。*)

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

#[export] Instance neg_sem_congr:
  Proper (func_equiv _ _ ==> func_equiv _ _) neg_sem.
Proof.
  unfold Proper, respectful,
         func_equiv, pointwise_relation.
  intros D1 D2 H.
  unfold neg_sem.
  intros s.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance abs_sem_congr:
  Proper (func_equiv _ _ ==> func_equiv _ _) abs_sem.
Proof.
  unfold Proper, respectful,
         func_equiv, pointwise_relation.
  intros D1 D2 H.
  unfold abs_sem.
  intros s.
  rewrite H.
  reflexivity.
Qed.

(** 第五步，请你证明行为等价是等价关系，并且所有语法算子都能保持行为等价。在
    SimpleWhile语言中，我们证明了以下结论，供你参考。

   
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
        intros.
        simpl.
        rewrite H, H0.
        reflexivity.
      Qed.
      
      #[export] Instance ESub_congr:
        Proper (iequiv ==> iequiv ==> iequiv) ESub.
      Proof.
        unfold Proper, respectful, iequiv.
        intros.
        simpl.
        rewrite H, H0.
        reflexivity.
      Qed.
      
      #[export] Instance EMul_congr:
        Proper (iequiv ==> iequiv ==> iequiv) EMul.
      Proof.
        unfold Proper, respectful, iequiv.
        intros.
        simpl.
        rewrite H, H0.
        reflexivity.
      Qed.
      


    第六步，请使用“指称语义”、“行为等价”、_[func_equiv]_以及_[pointwise_relation]_
    的定义证明以下结论。

   
      [[e1 + (- e2)]] ~=~ [[e1 - e2]]
      [[e1 - (- e2)]] ~=~ [[e1 + e2]]
      [[- (- e)]] ~=~ e
      


    第七步，请使用上面结论证明：
   
      [[ "x" - (- (- (- (- "y")))) ]] ~=~ [[ "x" - "y" ]]
      *)

#[export] Instance iequiv_equiv: Equivalence iequiv.
Proof.
  unfold iequiv.
  apply equiv_in_domain.
  apply func_equiv_equiv.
Qed.

#[export] Instance EConst_congr:
  Proper (eq ==> iequiv) EConst.
Proof.
  unfold Proper, respectful, iequiv.
  intros n1 n2 Hn.
  subst.
  reflexivity.
Qed.

#[export] Instance EVar_congr:
  Proper (eq ==> iequiv) EVar.
Proof.
  unfold Proper, respectful, iequiv.
  intros x1 x2 Hx.
  subst.
  reflexivity.
Qed.

#[export] Instance EAdd_congr:
  Proper (iequiv ==> iequiv ==> iequiv) EAdd.
Proof.
  unfold Proper, respectful, iequiv.
  intros e1 e1' He e2 e2' He'.
  simpl.
  rewrite He, He'.
  reflexivity.
Qed.

#[export] Instance ESub_congr:
  Proper (iequiv ==> iequiv ==> iequiv) ESub.
Proof.
  unfold Proper, respectful, iequiv.
  intros e1 e1' He e2 e2' He'.
  simpl.
  rewrite He, He'.
  reflexivity.
Qed.

#[export] Instance EMul_congr:
  Proper (iequiv ==> iequiv ==> iequiv) EMul.
Proof.
  unfold Proper, respectful, iequiv.
  intros e1 e1' He e2 e2' He'.
  simpl.
  rewrite He, He'.
  reflexivity.
Qed.

#[export] Instance ENeg_congr:
  Proper (iequiv ==> iequiv) ENeg.
Proof.
  unfold Proper, respectful, iequiv.
  intros e1 e2 He.
  simpl.
  rewrite He.
  reflexivity.
Qed.

#[export] Instance EAbs_congr:
  Proper (iequiv ==> iequiv) EAbs.
Proof.
  unfold Proper, respectful, iequiv.
  intros e1 e2 He.
  simpl.
  rewrite He.
  reflexivity.
Qed.

Lemma add_neg_equiv_sub:
  forall e1 e2,
    [[ e1 + (- e2) ]] ~=~ [[ e1 - e2 ]].
Proof.
  unfold iequiv.
  intros e1 e2.
  simpl.
  unfold func_equiv, pointwise_relation.
  intros s.
  simpl.
  unfold add_sem, neg_sem, sub_sem.
  lia.
Qed.

Lemma sub_neg_equiv_add:
  forall e1 e2,
    [[ e1 - (- e2) ]] ~=~ [[ e1 + e2 ]].
Proof.
  unfold iequiv.
  intros e1 e2.
  simpl.
  unfold func_equiv, pointwise_relation.
  intros s.
  simpl.
  unfold sub_sem, neg_sem, add_sem.
  lia.
Qed.

Lemma neg_neg_equiv:
  forall e,
    [[ - (- e) ]] ~=~ e.
Proof.
  unfold iequiv.
  intros e.
  simpl.
  unfold func_equiv, pointwise_relation.
  intros s.
  simpl.
  unfold neg_sem.
  lia.
Qed.

Lemma nested_neg_example:
  [[ "x" - (- (- (- (- "y")))) ]] ~=~ [[ "x" - "y" ]].
Proof.
    unfold iequiv.
    intros.
    simpl.
    unfold sub_sem, var_sem.
    intros s.
    simpl.
    unfold neg_sem.
    lia.
Qed.