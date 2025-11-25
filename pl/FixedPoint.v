Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
Require Import PL.Monad.
Require Import PL.Kleene.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.



(** * While语言的指称语义 *)

Module DntSem_While2.
Import Lang_While
       StateModel_SimpleWhile2
       DntSem_SimpleWhile7
       SetMonadEExamples
       SetMonadE.Notations
       DntSem_While
       KleeneFix Sets_CPO StateRels_Funcs.

(** 下面定义程序语句的语义。程序语句的语义包含两种情况：正常运行终止和运行出错。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop
}.

End CDenote.

(** 以下为_[Notation]_声明，细节可以忽略。*)

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | SetMonadE.M _ => exact (SetMonadE.nrm _ x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | SetMonadE.M _ => exact (SetMonadE.err _ x)
  | CDenote => exact (CDenote.err x)
  end.

(** 空语句的语义：*)

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
  |}.

(** 赋值语句的语义：*)

Definition asgn_sem
             (X: var_name)
             (D: state -> SetMonadE.M Z): CDenote :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        i ∈ (D s1).(nrm) /\ s2 X = Var_I i /\
        (forall Y, X <> Y -> s2 Y = s1 Y);
    err := fun s1 => (D s1).(err);
  |}.

(** 顺序执行语句的语义：*)

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
  |}.

(** 条件分支语句的语义：*)

Definition test_true (D: state -> SetMonadE.M Z):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, i ∈ (D s).(nrm) /\ i <> 0).

Definition test_false (D: state -> SetMonadE.M Z):
  state -> state -> Prop :=
  Rels.test (fun s => 0 ∈ (D s).(nrm)).

Definition err_set (D: state -> SetMonadE.M Z):
  state -> Prop :=
  fun s => (D s).(err).

Definition if_sem
             (D0: state -> SetMonadE.M Z)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := err_set D0 ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err))
  |}.

Definition while_sem
             (D0: state -> SetMonadE.M Z)
             (D1: CDenote): CDenote :=
  {|
    nrm := Kleene_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_false D0);
    err := Kleene_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_true D0 ∘ D1.(err) ∪
                err_set D0);
  |}.

(** 程序语句的语义可以最后表示成下面递归函数。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr e) (eval_com c1)
  end.





End DntSem_While2.

(** * 加入break、continue语句的指称语义 *)

Module DntSem_WhileBC.
Import Lang_While
       StateModel_SimpleWhile2
       DntSem_SimpleWhile7
       SetMonadEExamples
       SetMonadE.Notations
       DntSem_While
       KleeneFix Sets_CPO StateRels_Funcs.

(** 考虑以下While程序语言的拓展 *)

Inductive com : Type :=
  | CSkip: com
  | CAsgn (X: var_name) (e: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CContinue: com
  | CBreak: com.

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  brk: state -> state -> Prop;
  cnt: state -> state -> Prop;
  err: state -> Prop
}.

End CDenote.

(** 以下为_[Notation]_声明，细节可以忽略。*)

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | SetMonadE.M _ => exact (SetMonadE.nrm _ x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | SetMonadE.M _ => exact (SetMonadE.err _ x)
  | CDenote => exact (CDenote.err x)
  end.

Notation "x '.(brk)'" := (CDenote.brk x)
  (at level 1).

Notation "x '.(cnt)'" := (CDenote.cnt x)
  (at level 1).


(** 空语句的语义：*)

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    brk := ∅;
    cnt := ∅;
    err := ∅;
  |}.

(** Break语句的语义 *)

Definition brk_sem: CDenote :=
  {|
    nrm := ∅;
    brk := Rels.id;
    cnt := ∅;
    err := ∅;
  |}.

(** Continue语句的语义 *)

Definition cnt_sem: CDenote :=
  {|
    nrm := ∅;
    brk := ∅;
    cnt := Rels.id;
    err := ∅;
  |}.

(** 顺序执行语句的语义 *)

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    brk := D1.(brk) ∪ (D1.(nrm) ∘ D2.(brk));
    cnt := D1.(cnt) ∪ (D1.(nrm) ∘ D2.(cnt));
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
  |}.

(** 赋值语句的语义：*)

Definition asgn_sem
             (X: var_name)
             (D: state -> SetMonadE.M Z): CDenote :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        i ∈ (D s1).(nrm) /\ s2 X = Var_I i /\
        (forall Y, X <> Y -> s2 Y = s1 Y);
    brk := ∅;
    cnt := ∅;
    err := fun s1 => (D s1).(err);
  |}.

(** 以下定义沿用 *)

Definition test_true (D: state -> SetMonadE.M Z):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, i ∈ (D s).(nrm) /\ i <> 0).

Definition test_false (D: state -> SetMonadE.M Z):
  state -> state -> Prop :=
  Rels.test (fun s => 0 ∈ (D s).(nrm)).

Definition err_set (D: state -> SetMonadE.M Z):
  state -> Prop :=
  fun s => (D s).(err).

(** If语句的语义 *)

Definition if_sem
             (D0: state -> SetMonadE.M Z)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    brk := (test_true D0 ∘ D1.(brk)) ∪
           (test_false D0 ∘ D2.(brk));
    cnt := (test_true D0 ∘ D1.(cnt)) ∪
           (test_false D0 ∘ D2.(cnt));
    err := err_set D0 ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
  |}.

Definition while_sem
             (D0: state -> SetMonadE.M Z)
             (D1: CDenote): CDenote :=
  {|
    nrm := Kleene_LFix
             (fun X =>
               test_true D0 ∘ D1.(nrm) ∘ X ∪
               test_true D0 ∘ D1.(cnt) ∘ X ∪
               test_true D0 ∘ D1.(brk) ∪
               test_false D0);
    brk := ∅;
    cnt := ∅;
    err := Kleene_LFix
             (fun X =>
               test_true D0 ∘ D1.(nrm) ∘ X ∪
               test_true D0 ∘ D1.(cnt) ∘ X ∪
               test_true D0 ∘ D1.(err) ∪
               err_set D0);
  |}.

(** 程序语句的语义可以最后表示成下面递归函数。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr e) (eval_com c1)
  | CBreak =>
      brk_sem
  | CContinue =>
      cnt_sem
  end.

End DntSem_WhileBC.

(** * SetMonad中加入循环 *)

Module SetMonadExamples3.
Import Monad
       MonadNotation
       SetMonadExamples0
       SetMonadExamples2
       KleeneFix Sets_CPO.
Local Open Scope monad.

(** 如果要用单子表示带循环的计算过程，那就需要引入新的循环算子。

    首先定义循环体的计算结果，其结果要么是continue终止，要么是break终止。*)

Inductive ContinueOrBreak (A B: Type): Type :=
| by_continue (a: A)
| by_break (b: B).

Arguments by_continue {_} {_} (_).
Arguments by_break {_} {_} (_).

(** 下面用不动点定义repeat循环。*)

Definition repeat_break_f
             {A B: Type}
             (body: A -> SetMonad.M (ContinueOrBreak A B))
             (W: A -> SetMonad.M B)
             (a: A): SetMonad.M B :=
  x <- body a;;
  match x with
  | by_continue a' => W a'
  | by_break b => ret b
  end.

Definition repeat_break
             {A B: Type}
             (body: A -> SetMonad.M (ContinueOrBreak A B)):
  A -> SetMonad.M B :=
  Kleene_LFix (repeat_break_f body).

(** 下面还可以定义循环体中的continue语句和break语句。*)

Definition continue {A B: Type} (a: A):
  SetMonad.M (ContinueOrBreak A B) :=
  ret (by_continue a).

Definition break {A B: Type} (b: B):
  SetMonad.M (ContinueOrBreak A B) :=
  ret (by_break b).

Definition body_3x1 (x: Z): SetMonad.M (ContinueOrBreak Z Z) :=
  choice
    (assume (x <= 1);; break x)
    (choice
      (assume (exists k, x = 2 * k);;
       continue (x / 2))
      (assume (exists k, k <> 0 /\ x = 2 * k + 1);;
       continue (3 * x + 1))).

Definition run_3x1: Z -> SetMonad.M Z :=
  repeat_break body_3x1.

Definition body_binary_search (P: Z -> Prop):
  Z * Z -> SetMonad.M (ContinueOrBreak (Z * Z) Z) :=
  fun '(lo, hi) =>
  choice
    (assume (lo + 1 = hi);; break lo)
    (assume (lo + 1 < hi);;
     let mid := (lo + hi) / 2 in
     choice
       (assume (P mid);; continue (mid, hi))
       (assume (~ P mid);; continue (lo, mid))).

Definition binary_search (P: Z -> Prop) (lo hi: Z):
  SetMonad.M Z :=
  repeat_break (body_binary_search P) (lo, hi).

Import ListNotations.
Local Open Scope list.

Definition body_merge:
  list Z * list Z * list Z ->
  SetMonad.M (ContinueOrBreak (list Z * list Z * list Z) (list Z)) :=
  fun '(l1, l2, l3) =>
    match l1, l2 with 
    | nil, _ => break (l3 ++ l2)
    | _, nil => break (l3 ++ l1)
    | x :: l1', y :: l2' =>
        choice
          (assume (x <= y);; continue (l1', l2, l3 ++ x :: nil))
          (assume (y <= x);; continue (l1, l2', l3 ++ y :: nil))
  end.

Definition merge l l0 :=
  repeat_break body_merge (l, l0, nil).

End SetMonadExamples3.
