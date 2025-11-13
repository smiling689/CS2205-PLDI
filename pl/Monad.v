Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import compcert.lib.Integers.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
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

Module SetMonadExamples2.

Definition choice {A: Type} (f g: SetMonad.M A):
  SetMonad.M A :=
  f ∪ g.

Definition assume (P: Prop): SetMonad.M unit :=
  fun _ => P.

Definition compute_abs (z: Z): SetMonad.M Z :=
  choice
    (assume (z >= 0);; ret z)
    (assume (z <= 0);; ret (-z)).

End SetMonadExamples2.

(** ** 用集合单子定义表达式指称语义 *)

Module DntSem_SimpleWhile5.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       SetMonadExamples0
       SetMonadExamples2.


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

End DntSem_SimpleWhile5.

(** * 非确定性 + 计算异常退出 *)

(** ** 单子定义 *)


Module SetMonadE.

Record M (A: Type): Type := {
  nrm: A -> Prop;
  err: Prop;
}.

Module Notations.

Notation "x '.(nrm)'" := (nrm _ x) (at level 1).

Notation "x '.(err)'" := (err _ x) (at level 1).

End Notations.

Import Notations.

Definition ret (A: Type) (a: A): M A := {|
  nrm := Sets.singleton a;
  err := ∅;
|}.

Definition bind (A B: Type) (f: M A) (g: A -> M B):
  M B :=
  {|
    nrm := fun b => exists a, a ∈ f.(nrm) /\ b ∈ (g a).(nrm);
    err := f.(err) \/ exists a, a ∈ f.(nrm) /\ (g a).(err);
  |}.

End SetMonadE.

Import SetMonadE.Notations.

#[export] Instance err_monad: Monad SetMonadE.M := {|
  bind := SetMonadE.bind;
  ret := SetMonadE.ret;
|}.

(** ** 基本算子与简单示例 *)

Module SetMonadEExamples.

Definition abort {A: Type}: SetMonadE.M A :=
  {|
    SetMonadE.nrm := ∅;
    SetMonadE.err := True;
  |}.

Definition assume (P: Prop):
  SetMonadE.M unit :=
  {|
    SetMonadE.nrm := fun _ => P;
    SetMonadE.err := False;
  |}.

Definition assert (P: Prop):
  SetMonadE.M unit :=
  {|
    SetMonadE.nrm := fun _ => P;
    SetMonadE.err := ~ P;
  |}.

Definition choice {A: Type} (f g: SetMonadE.M A):
  SetMonadE.M A :=
  {|
    SetMonadE.nrm := f.(nrm) ∪ g.(nrm);
    SetMonadE.err := f.(err) \/ g.(err);
  |}.

Definition compute_abs (z: Z): SetMonadE.M Z :=
  choice
    (assume (z >= 0);; ret z)
    (assume (z <= 0);; ret (-z)).

Definition compute_div (a b: Z): SetMonadE.M Z :=
  assert (b <> 0);;
  ret (a / b).

Definition compute_mod (a b: Z): SetMonadE.M Z :=
  assert (b <> 0);;
  ret (a mod b).

End SetMonadEExamples.

(** ** SimpleWhile的整数类型表达式指称语义（有符号64位计算） *)

Module DntSem_SimpleWhile6.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       SetMonadEExamples.


(** 下面定义语义算子：*)

Definition const_sem (n: Z):
  state -> SetMonadE.M Z :=
  fun s =>
    assert (Int64.min_signed <= n <= Int64.max_signed);;
    ret n.

Definition var_sem (X: var_name):
  state -> SetMonadE.M Z :=
  fun s =>
    ret (s X).

Definition add_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x + y <= Int64.max_signed);;
    ret (x + y).

Definition sub_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x - y <= Int64.max_signed);;
    ret (x - y).

Definition mul_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x * y <= Int64.max_signed);;
    ret (x * y).

Fixpoint eval_expr_int (e: expr_int):
  state -> SetMonadE.M Z :=
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

End DntSem_SimpleWhile6.

(** ** SimpleWhile的整数类型表达式指称语义（考虑变量初始化） *)


Inductive val: Type :=
| Var_U: val
| Var_I (i: Z): val.

(** 这里，如果一个变量的值用_[Var_U]_表示，那么一个变量没有初始化；如果一个变量的值用
    _[Var_I]_表示，那么这个变量已经初始化了。*)

Module StateModel_SimpleWhile2.
Import Lang_SimpleWhile.

(** 这样，程序状态就可以如下定义。*)

Definition state: Type := var_name -> val.


End StateModel_SimpleWhile2.

Module DntSem_SimpleWhile7.
Import Lang_SimpleWhile
       StateModel_SimpleWhile2
       SetMonadEExamples.

(** 下面定义语义算子：*)

Definition var_sem (X: var_name):
  state -> SetMonadE.M Z :=
  fun s =>
    match s X with
    | Var_U => abort
    | Var_I n => ret n
    end.

(** 其他语义算子的定义代码都不需要修改。*)

Definition const_sem (n: Z):
  state -> SetMonadE.M Z :=
  fun s =>
    assert (Int64.min_signed <= n <= Int64.max_signed);;
    ret n.

Definition add_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x + y <= Int64.max_signed);;
    ret (x + y).

Definition sub_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x - y <= Int64.max_signed);;
    ret (x - y).

Definition mul_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x * y <= Int64.max_signed);;
    ret (x * y).

End DntSem_SimpleWhile7.

Module DntSem_SimpleWhile8.
Import Lang_SimpleWhile
       StateModel_SimpleWhile2
       DntSem_SimpleWhile7.

Fixpoint eval_expr_int (e: expr_int):
  state -> SetMonadE.M Z :=
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

End DntSem_SimpleWhile8.

(** * While语言表达式的指称语义 *)

Module DntSem_While.
Import Lang_While
       StateModel_SimpleWhile2
       DntSem_SimpleWhile7
       SetMonadEExamples.


(**
        E :: = N | V | -E | E+E | E-E | E*E | E/E | E%E |
               E<E | E<=E | E==E | E!=E | E>=E | E>E |
               E&&E | E||E | !E 

   
      Inductive unop : Type :=
        | ONot | ONeg.
      

   
      Inductive binop : Type :=
        | OOr | OAnd
        | OLt | OLe | OGt | OGe | OEq | ONe
        | OPlus | OMinus | OMul | ODiv | OMod.
      

   
      Inductive expr : Type :=
        | EConst (n: Z): expr
        | EVar (x: var_name): expr
        | EBinop (op: binop) (e1 e2: expr): expr
        | EUnop (op: unop) (e: expr): expr.
      

    常量、变量、加、减、乘对应的语义算子都可以沿用先前的定义。下面先定义除法和取余对应
    的语义算子，具体规定细节参考了C标准。*)

Definition div_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (y <> 0);;
    assert (y <> -1 \/ x <> Int64.min_signed);;
    ret (Z.quot x y).

Definition mod_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (y <> 0);;
    assert (y <> -1 \/ x <> Int64.min_signed);;
    ret (Z.rem x y).

(** C标准规定：

    在任何情况下，整数运算中的C表达式_[a / b]_与_[a % b]_永远满足以下式子

    _[a = b * (a / b) + a % b]_。

    同时，如果前者的计算是未定义行为，那么后者的也是。

    如果除法运算不整除，那么_[a % b]_与_[a]_同号。


    下面再定义整数大小比较的语义算子。*)

Definition eq_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x = y);; ret 1)
      (assume (x <> y);; ret 0).

Definition neq_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x <> y);; ret 1)
      (assume (x = y);; ret 0).

Definition lt_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x < y);; ret 1)
      (assume (x >= y);; ret 0).

Definition le_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x <= y);; ret 1)
      (assume (x > y);; ret 0).

Definition gt_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x > y);; ret 1)
      (assume (x <= y);; ret 0).

Definition ge_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x >= y);; ret 1)
      (assume (x < y);; ret 0).

(** 最后两个语义算子是关于逻辑运算的语义算子。*)

Definition and_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;;
    choice
      (assume (x <> 0);; 
       y <- D2 s;;
       choice
         (assume (y <> 0);; ret 1)
         (assume (y = 0);; ret 0))
      (assume (x = 0);; ret 0).

Definition or_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;;
    choice
      (assume (x <> 0);; ret 1)
      (assume (x = 0);; 
       y <- D2 s;;
       choice
         (assume (y <> 0);; ret 1)
         (assume (y = 0);; ret 0)).

(** 除了定义二元运算符的语义算子之外，还有两个一元运算符需要定义其语义算子。*)

Definition not_sem (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D s;;
    choice
      (assume (x <> 0);; ret 0)
      (assume (x = 0);; ret 1).

Definition neg_sem (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D s;;
    assert (x <> Int64.min_signed);;
    ret (- x).

(** 将上面这些语义算子集成起来 *)

Definition binop_sem (op: binop) (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  match op with
  | OPlus => add_sem D1 D2
  | OMinus => sub_sem D1 D2
  | OMul => mul_sem D1 D2
  | ODiv => div_sem D1 D2
  | OMod => mod_sem D1 D2
  | OLt => lt_sem D1 D2
  | OLe => le_sem D1 D2
  | OGt => gt_sem D1 D2
  | OGe => ge_sem D1 D2
  | OEq => eq_sem D1 D2
  | ONe => neq_sem D1 D2
  | OAnd => and_sem D1 D2
  | OOr => or_sem D1 D2
  end.

Definition unop_sem (op: unop) (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

(** 最终的递归定义：*)

Fixpoint eval_expr (e: expr): state -> SetMonadE.M Z :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EBinop op e1 e2 =>
      binop_sem op (eval_expr e1) (eval_expr e2)
  | EUnop op e1 =>
      unop_sem op (eval_expr e1)
  end.



End DntSem_While.

(** * WhileDeref语言表达式的指称语义 *)

Module DntSem_WhileDeref.
Import Lang_WhileDeref
       SetMonadEExamples.


Inductive mem_val: Type :=
| Mem_HasPerm (v: val): mem_val (** 有内存读写权限 *)
| Mem_NoPerm: mem_val.          (** 无内存读写权限 *)

Record state: Type := {
  var: var_name -> val; (** 变量的值 *)
  mem: Z -> mem_val;    (** 额外内存空间上存储的值 *)
}.

(** 首先，每个程序状态_[s]_中除了包含每个变量的值_[s.(var)]_还包含内存地址上存储的
    值_[s.(mem)]_，这些内存地址是指存储变量数值之外的额外内存存储空间。而对于每个内存
    地址而言，又要首先定义是否有该地址的读写权限。据此，可以重新定义_[var_sem]_。 *)

Definition var_sem (X: var_name):
  state -> SetMonadE.M Z :=
  fun s =>
    match s.(var) X with
    | Var_U => abort
    | Var_I n => ret n
    end.

(** 接下去定义解引用的语义算子。*)

Definition deref_sem (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D s;;
    match s.(mem) x with
    | Mem_NoPerm => abort
    | Mem_HasPerm Var_U => abort
    | Mem_HasPerm (Var_I n) => ret n
    end.

(** 其他语义算子保持不变。*)

Definition const_sem (n: Z):
  state -> SetMonadE.M Z :=
  fun s =>
    assert (Int64.min_signed <= n <= Int64.max_signed);;
    ret n.

Definition add_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x + y <= Int64.max_signed);;
    ret (x + y).

Definition sub_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x - y <= Int64.max_signed);;
    ret (x - y).

Definition mul_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (Int64.min_signed <= x * y <= Int64.max_signed);;
    ret (x * y).

Definition div_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (y <> 0);;
    assert (y <> -1 \/ x <> Int64.min_signed);;
    ret (Z.quot x y).

Definition mod_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    assert (y <> 0);;
    assert (y <> -1 \/ x <> Int64.min_signed);;
    ret (Z.rem x y).

Definition eq_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x = y);; ret 1)
      (assume (x <> y);; ret 0).

Definition neq_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x <> y);; ret 1)
      (assume (x = y);; ret 0).

Definition lt_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x < y);; ret 1)
      (assume (x >= y);; ret 0).

Definition le_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x <= y);; ret 1)
      (assume (x > y);; ret 0).

Definition gt_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x > y);; ret 1)
      (assume (x <= y);; ret 0).

Definition ge_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;; y <- D2 s;;
    choice
      (assume (x >= y);; ret 1)
      (assume (x < y);; ret 0).

Definition and_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;;
    choice
      (assume (x <> 0);; 
       y <- D2 s;;
       choice
         (assume (y <> 0);; ret 1)
         (assume (y = 0);; ret 0))
      (assume (x = 0);; ret 0).

Definition or_sem (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D1 s;;
    choice
      (assume (x <> 0);; ret 1)
      (assume (x = 0);; 
       y <- D2 s;;
       choice
         (assume (y <> 0);; ret 1)
         (assume (y = 0);; ret 0)).

Definition not_sem (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D s;;
    choice
      (assume (x <> 0);; ret 0)
      (assume (x = 0);; ret 1).

Definition neg_sem (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D s;;
    assert (x <> Int64.min_signed);;
    ret (- x).

Definition binop_sem (op: binop) (D1 D2: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  match op with
  | OPlus => add_sem D1 D2
  | OMinus => sub_sem D1 D2
  | OMul => mul_sem D1 D2
  | ODiv => div_sem D1 D2
  | OMod => mod_sem D1 D2
  | OLt => lt_sem D1 D2
  | OLe => le_sem D1 D2
  | OGt => gt_sem D1 D2
  | OGe => ge_sem D1 D2
  | OEq => eq_sem D1 D2
  | ONe => neq_sem D1 D2
  | OAnd => and_sem D1 D2
  | OOr => or_sem D1 D2
  end.

Definition unop_sem (op: unop) (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

(** 最终的递归定义：*)

Fixpoint eval_expr (e: expr): state -> SetMonadE.M Z :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EBinop op e1 e2 =>
      binop_sem op (eval_expr e1) (eval_expr e2)
  | EUnop op e1 =>
      unop_sem op (eval_expr e1)
  | EDeref e1 =>
      deref_sem (eval_expr e1)
  end.



End DntSem_WhileDeref.
