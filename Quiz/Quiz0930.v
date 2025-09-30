Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.SimpleProofsAndDefs.
Require Import PL.Syntax.
Local Open Scope Z.


(** 下面是一个小测验。请在Coq中证明下面结论。*)


(************)
(** 习题：  *)
(************)

(** 我们可以使用乘法运算定义“正负号不同”这个二元谓词。请基于这一定义完成相关性质的Coq证
    明。*)

Definition opposite_sgn (x y: Z): Prop := x * y < 0.

Fact opposite_sgn_plus_2: forall x,
  opposite_sgn (x + 2) x ->
  x = -1.
Proof.
    unfold opposite_sgn.
    intros.
    nia.
Qed.

Fact opposite_sgn_odds: forall x,
  opposite_sgn (square x) x ->
  x < 0.
Proof.
    unfold opposite_sgn, square.
    intros.
    nia.
Qed.


(************)
(** 习题：  *)
(************)

(** 下面定义的谓词_[quad_nonneg a b c]_表示：以_[a]_、_[b]_、_[c]_为系数的二次式在
    自变量去一切整数的时候都恒为非负。请基于这一定义完成相关性质的Coq证明。*)

Definition quad_nonneg (a b c: Z): Prop :=
  forall x: Z, a * x * x + b * x + c >= 0.

Lemma scale_quad_nonneg: forall a b c k: Z,
  k > 0 ->
  quad_nonneg a b c ->
  quad_nonneg (k * a) (k * b) (k * c).
Proof.
    intros a b c k Hk Hq x.
    unfold quad_nonneg in Hq.
    specialize (Hq x).
    nia.
Qed.

Lemma descale_quad_nonneg: forall a b c k: Z,
  k > 0 ->
  quad_nonneg (k * a) (k * b) (k * c) ->
  quad_nonneg a b c.
Proof.
    intros a b c k Hk Hq x.
    unfold quad_nonneg in Hq.
    specialize (Hq x).
    nia.
Qed.

Lemma plus_quad_nonneg: forall a1 b1 c1 a2 b2 c2: Z,
  quad_nonneg a1 b1 c1 ->
  quad_nonneg a2 b2 c2 ->
  quad_nonneg (a1 + a2) (b1 + b2) (c1 + c2).
Proof.
    intros a1 b1 c1 a2 b2 c2 Hq1 Hq2 x.
    unfold quad_nonneg in Hq1, Hq2.
    specialize (Hq1 x).
    specialize (Hq2 x).
    nia.
Qed.

(** 我们知道，如果二次式的二次项系数为正且判别式不为正，那么这个二次式在自变量取遍一切
    实数的时候都恒为正。相应的性质在自变量取遍一切整数的时候自然也成立。请证明这一结
    论。【选做】*)

Lemma plus_quad_discriminant: forall a b c,
  a > 0 ->
  b * b - 4 * a * c <= 0 ->
  quad_nonneg a b c.
Proof.
    intros.
    unfold quad_nonneg.
    pose proof sqr_pos (2 * a * x + b).
    nia.
Qed.


(** 然而，判别式不为正并不是_[quad_nonneg]_的必要条件。下面命题是一个简单的反例。*)

Example quad_nonneg_1_1_0: quad_nonneg 1 1 0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact logic_ex6: forall {A: Type} (P Q: A -> Prop) (a0: A),
  P a0 ->
  (forall a: A, P a -> Q a) ->
  Q a0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact logic_ex7: forall {A: Type} (P Q: A -> Prop) (a0: A),
  (forall a: A, P a -> Q a -> False) ->
  Q a0 -> 
  ~ P a0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)


(** 在WhileDeref语言的基础上，加上
      - malloc
      - read_int
      - read_char
      - write_int
      - write_char
    这几个内置函数之后，程序中就可以包含内存动态分配以及IO。下面请写出这个新语言的表达
    式与程序语句的语法定义。*)



(************)
(** 习题：  *)
(************)


(** SimpleWhile语言的整数类型表达式只包含加、减、乘三种运算以及整数常数和变量，之前我
    们也依次为依据在Coq中定义了它们的抽象语法树。在抽象语法树中，是没有“括号”这一语法元
    素的。其实，我们可以修改语法树，把“括号”这一语法元素也添加到语法树中，使得我们可以描述以下这些树结构。

   
                      +                -
                    /   \            /   \
                ( )       ( )      x     ( )
                 |         |            /   \
                 *         +           y     z
               /   \     /   \
              z     x   p     1
      

    请根据上述要求在Coq中定义带括号的SimpleWhile整数类型表达式语法树，类型名称请依旧使
    用_[expr_int]_。*)


