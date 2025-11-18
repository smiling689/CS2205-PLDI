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
Require Import PL.Monad.
Import SetsNotation.
Import Monad.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

Module DntSem_WhileD.
Import Lang_WhileD
       SetMonadEExamples.


Inductive mem_val: Type :=
| Mem_HasPerm (v: val): mem_val
| Mem_NoPerm: mem_val.

Record state: Type := {
  var: var_name -> Z; (** 表示每个变量的存储地址 *)
  mem: Z -> mem_val;  (** 既包含变量存储的内存空间也包含其他内存空间 *)
}.

Definition deref_sem (D: state -> SetMonadE.M Z):
  state -> SetMonadE.M Z :=
  fun s =>
    x <- D s;;
    match s.(mem) x with
    | Mem_NoPerm => abort
    | Mem_HasPerm Var_U => abort
    | Mem_HasPerm (Var_I n) => ret n
    end.

Definition var_addr_sem (X: var_name):
  state -> SetMonadE.M Z :=
  fun s => ret (s.(var) X).

Definition var_sem (X: var_name):
  state -> SetMonadE.M Z :=
  fun s =>
    y <- ret (s.(var) X);;
    match s.(mem) y with
    | Mem_NoPerm => abort
    | Mem_HasPerm Var_U => abort
    | Mem_HasPerm (Var_I n) => ret n
    end.

(** 其他语义算子可以沿用原先定义。*)

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

(** 表达式的指称语义要分左值和右值定义。*)

Record EDenote: Type := {
  lvalue: state -> SetMonadE.M Z;
  rvalue: state -> SetMonadE.M Z;
}.

(** 最终的递归定义：*)

Fixpoint eval_expr (e: expr): EDenote :=
  match e with
  | EConst n =>
      {| lvalue := fun _ => abort;
         rvalue := const_sem n |}
  | EVar X =>
      {| lvalue := var_addr_sem X;
         rvalue := var_sem X |}
  | EBinop op e1 e2 =>
      {| lvalue := fun _ => abort;
         rvalue := binop_sem op
                             (eval_expr e1).(rvalue)
                             (eval_expr e2).(rvalue) |}
  | EUnop op e1 =>
      {| lvalue := fun _ => abort;
         rvalue := unop_sem op (eval_expr e1).(rvalue) |}
  | EDeref e1 =>
      {| lvalue := (eval_expr e1).(rvalue);
         rvalue := deref_sem (eval_expr e1).(rvalue) |}
  | EAddrOf e1 =>
      {| lvalue := fun _ => abort;
         rvalue := (eval_expr e1).(lvalue) |}
  end.


End DntSem_WhileD.
