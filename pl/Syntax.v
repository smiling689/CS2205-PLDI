Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope Z.

(** * 一个极简的指令式程序语言：SimpleWhile *)

(** 在Coq中，我们就用字符串表示变量名，*)

Definition var_name: Type := string.

Declare Custom Entry prog_lang_entry.

Module Lang_SimpleWhile.

(** 并且使用Coq归纳类型定义表达式和语句的语法树。*)

Inductive expr_int : Type :=
  | EConst (n: Z): expr_int
  | EVar (x: var_name): expr_int
  | EAdd (e1 e2: expr_int): expr_int
  | ESub (e1 e2: expr_int): expr_int
  | EMul (e1 e2: expr_int): expr_int.

Inductive expr_bool: Type :=
  | ETrue: expr_bool
  | EFalse: expr_bool
  | ELt (e1 e2: expr_int): expr_bool
  | EAnd (e1 e2: expr_bool): expr_bool
  | ENot (e: expr_bool): expr_bool.

Inductive com : Type :=
  | CSkip: com
  | CAsgn (x: var_name) (e: expr_int): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr_bool) (c1 c2: com): com
  | CWhile (e: expr_bool) (c: com): com.

(** 在Coq中，可以利用_[Notation]_使得这些表达式和程序语句更加易读。*)

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
Notation "x * y" := (EMul x y)
  (in custom prog_lang_entry at level 11, left associativity).
Notation "x + y" := (EAdd x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x - y" := (ESub x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x < y" := (ELt x y)
  (in custom prog_lang_entry at level 13, no associativity).
Notation "x && y" := (EAnd x y)
  (in custom prog_lang_entry at level 14, left associativity).
Notation "! x" := (ENot x)
  (in custom prog_lang_entry at level 10).
Notation "x = e" := (CAsgn x e)
  (in custom prog_lang_entry at level 18, no associativity).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom prog_lang_entry at level 20, right associativity).
Notation "'skip'" := (CSkip)
  (in custom prog_lang_entry at level 10).
Notation "'if' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (CIf e c1 c2)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99,
   c2 custom prog_lang_entry at level 99,
   format  "'if'  e  'then'  '{'  c1  '}'  'else'  '{'  c2  '}'").
Notation "'while' e 'do' '{' c1 '}'" := (CWhile e c1)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99).

(** 使用_[Notation]_的效果如下：*)

Check [[1 + "x"]].
Check [["x" * ("a" + "b" + 1)]].
Check [[1 + "x" < "x"]].
Check [["x" < 0 && 0 < "y"]].
Check [["x" = "x" + 1]].
Check [[while (0 < "x") do { "x" = "x" - 1}]].


End Lang_SimpleWhile.

(** * 更多的程序语言：While语言 *)

(** 在许多以C语言为代表的常用程序语言中，往往不区分整数类型表达式与布尔类型表达
    式，同时表达式中也包含更多运算符。例如，我们可以如下规定一种程序语言的语法。

    下面依次在Coq中定义该语言中的二元运算符和一元运算符。*)

Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

Module Lang_While.

(** 然后再定义表达式的抽象语法树。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr.

(** 最后是程序语句的抽象语法树。*)

Inductive com : Type :=
  | CSkip: com
  | CAsgn (x: var_name) (e: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.


End Lang_While.

(** * 更多的程序语言：WhileDeref *)

Module Lang_WhileDeref.

(** 下面在While程序语言中增加取地址上的值_[EDeref]_操作。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr.

(** 相应的，赋值语句也可以分为两种情况。*)

Inductive com : Type :=
  | CSkip: com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

End Lang_WhileDeref.

(** * 更多的程序语言：WhileD *)

Module Lang_WhileD.

(** 在大多数程序语言中，会同时支持或不支持取地址_[EAddrOf]_与取地址上的值
    _[EDeref]_两类操作，我们也可以在WhileDeref语言中再加入取地址操作。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr.

(** 程序语句的语法树不变。*)

Inductive com : Type :=
  | CSkip: com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

End Lang_WhileD.

(** * 更多的程序语言：WhileDC *)

Module Lang_WhileDC.

(** 下面在程序语句中增加控制流语句continue与break，并增加多种循环语句。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr.

Inductive com : Type :=
  | CSkip: com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CFor (c1: com) (e: expr) (c2: com) (c3: com): com
  | CDoWhile (c: com) (e: expr): com
  | CContinue: com
  | CBreak: com.

End Lang_WhileDC.


(** * 更多的程序语言：WhileDL *)

Module Lang_WhileDL.
Import Lang_While.

(** 下面在程序语句中增加局部变量声明。*)

Inductive com : Type :=
  | CSkip: com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CLocalVar (x: var_name) (c: com): com.

End Lang_WhileDL.

(** * 带类型标注的表达式 *)

Module Lang_TypedExpr.


(** 下面先定义整数类型，每个整数类型由其所需比特数（_[sz]_）和其有无符号（_[sg]_）两部
    分构成。*)

Inductive Signedness : Type :=
  | Signed: Signedness
  | Unsigned: Signedness.

Inductive IntType : Type :=
  | Build_IntType (sz: Z) (sg: Signedness): IntType.

(** 基于此，可以定义带类型标注的While语言表达式。*)

Inductive expr : Type :=
  | EConst (n: Z) (t: IntType): expr
  | EVar (x: var_name) (t: IntType): expr
  | EBinop (op: binop) (e1 e2: expr) (t: IntType): expr
  | EUnop (op: unop) (e: expr) (t: IntType): expr.


End Lang_TypedExpr.

(** * 基于语法树递归定义的例子 *)

(** ** 表达式中包含的计算次数 *)

Module RecurExample1.
Import Lang_SimpleWhile.

(** 下面定义SimpleWhile语言中一个整数类型表达式中包含的算数运算数量。*)

Fixpoint number_of_comp (ei: expr_int): Z :=
  match ei with
  | EAdd e1 e2 => number_of_comp e1 + number_of_comp e2 + 1
  | ESub e1 e2 => number_of_comp e1 + number_of_comp e2 + 1
  | EMul e1 e2 => number_of_comp e1 + number_of_comp e2 + 1
  | EVar v => 0
  | EConst n => 0
  end.

Fact number_of_comp_example1:
  number_of_comp [[1 + "x"]] = 1.
Proof. reflexivity. Qed.

Fact number_of_comp_example2:
  number_of_comp [[(1 + "x") * "y" * "z"]] = 3.
Proof. reflexivity. Qed.



End RecurExample1.

(** ** 带类型表达式的几个基本合法性条件 *)

Module RecurExample2.
Import Lang_TypedExpr.


(** 下面我们定义两种带类型表达式的合法性条件。其一是表达式中常数的合法性条件，即每个常
    数都落在其类型规定的范围之内。 

    我们可以首先定义每个整数类型对应的数值范围。*)

Definition const_in_range (n: Z) (t: IntType): Prop :=
  match t with
  | Build_IntType sz Signed =>
      - Z.pow 2 (sz - 1) <= n < Z.pow 2 (sz - 1)
  | Build_IntType sz Unsigned =>
      0 <= n < Z.pow 2 sz
  end.

(** 之后就可以定义“表达式中所有常数全都满足类型范围要求”的合法性条件。*)

Fixpoint consts_in_range (e: expr): Prop :=
  match e with
  | EConst n t =>        const_in_range n t
  | EVar v t =>          True
  | EBinop op e1 e2 t => consts_in_range e1 /\
                         consts_in_range e2
  | EUnop op e1 t =>     consts_in_range e1
  end.

(** 其二是定义表达式中变量的合法性条件，即表达式中的每个变量类型都与当前环境规定的变量
    类型吻合。 *)

Definition var_types: Type := var_name -> IntType.

Fixpoint vars_well_typed (env: var_types) (e: expr): Prop :=
  match e with
  | EConst n t =>        True
  | EVar v t =>          env v = t
  | EBinop op e1 e2 t => vars_well_typed env e1 /\
                         vars_well_typed env e2
  | EUnop op e1 t =>     vars_well_typed env e1
  end.


End RecurExample2.

