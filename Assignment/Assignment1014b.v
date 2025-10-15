Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile1
       DntSem_SimpleWhile1_Properties.
Local Open Scope string.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 请在不展开“行为等价”之定义的情况下证明以下结论。提示：你可以在证明中使用已经证明过
    的引理以及_[rewrite]_证明脚本。*)

Fact iequiv_ex1: forall e1 e2: expr_int,
  [[e1 + e2 * 0]] ~=~ e1.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请在不展开“行为等价”之定义的情况下证明以下结论。提示：你可以在证明中使用已经证明过
    的引理以及_[rewrite]_证明脚本。*)

Fact iequiv_ex2: forall e1 e2 e3 e4: expr_int,
  [[((e1 + e2) + e3) + e4]] ~=~
  [[e1 + (e2 + (e3 + e4))]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


