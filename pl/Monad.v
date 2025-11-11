Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope Z.


(** * 在Coq中定义单子结构 *)

(** 单子可以这样在Coq中定义为一类代数结构。*)

Module Monad.

Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

End Monad.

Import Monad.

(** 我们之后最常常用到的将是集合单子（set monad）如下定义。*)

Module SetMonad.

Definition M (A: Type): Type := A -> Prop.

Definition bind: forall (A B: Type) (f: M A) (g: A -> M B), M B :=
  fun (A B: Type) (f: M A) (g: A -> M B) =>
    fun b: B => exists a: A, a ∈ f /\ b ∈ g a.

Definition ret: forall (A: Type) (a: A), M A :=
  fun (A: Type) (a: A) => Sets.singleton a.

End SetMonad.

#[export] Instance set_monad: Monad SetMonad.M := {|
  bind := SetMonad.bind;
  ret := SetMonad.ret;
|}.

(** 下面是另一个例子状态单子的定义：*)

Module StateMonad.

Definition M (Σ A: Type): Type := Σ -> Σ * A.

Definition bind (Σ: Type):
  forall (A B: Type) (f: M Σ A) (g: A -> M Σ B), M Σ B :=
  fun A B f g s1 =>
    match f s1 with
    | (s2, a) => g a s2
    end.

Definition ret (Σ: Type):
  forall (A: Type) (a: A), M Σ A :=
  fun A a s => (s, a).

End StateMonad.

#[export] Instance state_monad (Σ: Type): Monad (StateMonad.M Σ) := {|
  bind := StateMonad.bind Σ;
  ret := StateMonad.ret Σ;
|}.

(** * bind算子的记号 *)

Import Monad.

Module SetMonadExamples0.

(** 任取一个整数：*)

Definition any_Z: SetMonad.M Z := Sets.full.

(** 整数乘二：*)

Definition multi_two: Z -> SetMonad.M Z :=
  fun x => ret (x * 2).

(** 整数加一：*)

Definition plus_one: Z -> SetMonad.M Z :=
  fun x => ret (x + 1).

(** 任取整数再乘二：*)

Definition bind_ex0: SetMonad.M Z :=
  bind any_Z multi_two.

(** 任取整数乘二再加一：*)

Definition bind_ex1: SetMonad.M Z :=
  bind (bind any_Z multi_two) plus_one.

Definition bind_ex2: SetMonad.M Z :=
  bind any_Z (fun x => bind (multi_two x) plus_one).


End SetMonadExamples0.

(** 下面是用单子描述计算时常用的记号：*)

Module MonadNotation.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation " x : T <- c1 ;; c2" :=(bind c1 (fun x : T => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
  (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (bind e1 (fun _: unit => e2))
  (at level 61, right associativity) : monad_scope.

End MonadNotation.
Import MonadNotation.
Local Open Scope monad.

(** 用这些Notation可以重写前面的一些例子。*)

Module SetMonadExamples1.
Import SetMonadExamples0.

(** 任取整数再乘二：*)

Definition bind_ex0': SetMonad.M Z :=
  x <- any_Z;; ret (x * 2).

(** 任取整数乘二再加一：*)

Definition bind_ex1': SetMonad.M Z :=
  x <- any_Z;; y <- multi_two x;; ret (y + 1).

(** 注意，在上述定义中，

   
      x <- any_Z;; y <- multi_two x;; ret (y + 1)
      
    等价于说 
   
      bind any_Z
           (fun x => bind (multi_two x) (fun y => ret (y + 1))
      *)

(************)
(** 习题：  *)
(************)

(** 请写出下面标记背后表达的单子定义。*)

Definition  bind_ex2': SetMonad.M Z :=
  x <- any_Z;;
  y <- any_Z;;
  z1 <- multi_two y;;
  z2 <- plus_one y;;
  ret (x + y + z1 + z2).



End SetMonadExamples1.

(** * 集合单子 *)

(** ** 集合单子的简单例子 *)

Definition choice {A: Type} (f g: SetMonad.M A):
  SetMonad.M A :=
  f ∪ g.

Definition assume (P: Prop): SetMonad.M unit :=
  fun _ => P.

Definition compute_abs (z: Z): SetMonad.M Z :=
  choice
    (assume (z >= 0);; ret z)
    (assume (z <= 0);; ret (-z)).

(** ** 用集合单子定义表达式指称语义 *)

Import StateModel_SimpleWhile1
       SetMonadExamples0
       SetMonadExamples1.


(** 在整数类型表达式中添加_[ANY]_：
    _[ANY + 1]_表示任取一个整数再加一；
    _[ANY * 2]_表示任取一个整数再乘二。*)

Inductive expr_int : Type :=
  | EConst (n: Z): expr_int
  | EVar (x: var_name): expr_int
  | EAdd (e1 e2: expr_int): expr_int
  | ESub (e1 e2: expr_int): expr_int
  | EMul (e1 e2: expr_int): expr_int
  | EAny: expr_int.


(** 下面定义语义算子：*)

Definition any_sem: state -> SetMonad.M Z :=
  fun s => any_Z.

Definition const_sem (n: Z): state -> SetMonad.M Z :=
  fun s => ret n.

Definition var_sem (X: var_name): state -> SetMonad.M Z :=
  fun s => ret (s X).

Definition add_sem (D1 D2: state -> SetMonad.M Z):
  state -> SetMonad.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;; ret (x + y).

Definition sub_sem (D1 D2: state -> SetMonad.M Z):
  state -> SetMonad.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;; ret (x - y).

Definition mul_sem (D1 D2: state -> SetMonad.M Z):
  state -> SetMonad.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;; ret (x * y).

Fixpoint eval_expr_int (e: expr_int): state -> SetMonad.M Z :=
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
  | EAny =>
      any_sem
  end.
