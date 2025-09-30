Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import PL.SimpleProofsAndDefs.
Require Import PL.HighOrder.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact logic_ex8: forall {A B: Type} (P Q: A -> B -> Prop),
  (forall (a: A) (b: B), P a b -> Q a b) ->
  (forall (a: A) (b: B), ~ P a b \/ Q a b).
Proof.
    intros A B P Q HP a b.
    pose proof HP a b.
    unfold not.
    tauto.
Qed.



(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact logic_ex9: forall {A B: Type} (P Q: A -> B -> Prop),
  (forall (a: A) (b: B), ~ P a b \/ Q a b) ->
  (forall (a: A) (b: B), P a b -> Q a b).
Proof.
    intros A B P Q H a b HP.
    pose proof H a b.
    unfold not in H0.
    tauto.
Qed.



(************)
(** 习题：  *)
(************)

(** 请证明下面命题。*)

Fact shift_up1_eq: forall f,
  shift_up1 f = func_plus f (fun x => 1).
Proof.
    unfold shift_up1.
    unfold func_plus.
    intros.
    assert (forall x, f x + 1 = f x + 1) as H by lia.
    reflexivity.
Qed.
    


(************)
(** 习题：  *)
(************)

(** 请证明常值函数都是单调的。*)

Lemma const_mono: forall a: Z,
  mono (fun x => a).
Proof.
    unfold mono.
    intros a x y Hxy.
    lia.
Qed.


(************)
(** 习题：  *)
(************)

(** 请证明立方函数是单调的。*)

Example cube_mono: mono (fun x => x * x * x).
Proof.
    unfold mono.
    intros n m Hnm.
    replace (n * n * n) with (m * m * m - (m - n) * (m * m + n * m + n * n)) by nia.
    assert (m * m + n * m + n * n >= 0) by nia.
    nia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明函数加法能保持单调性。*)

Lemma mono_func_plus: forall f g,
  mono f ->
  mono g ->
  mono (func_plus f g).
Proof.
    unfold mono, func_plus.
    intros f g Hf Hg n m.
    pose proof Hf n m as Hf1.
    pose proof Hg n m as Hg1.
    lia.
Qed.

(************)
(** 习题：  *)
(************)


(** 正则表达式分为5种，分别是单个字符、空字符串、字符串的连接、字符串结合的并集和字符串
    的重复，即 

        _[r ::= c  |  empty-string  |  r | r  |  rr  |  r *]_ 

    请在Coq中定义正则表达式的语法树。*)


Inductive regex: Type :=
  | Char (c: ascii)
  | EmptyString
  | Union (r1 r2: regex)
  | Concat (r1 r2: regex)
  | Star (r: regex).
