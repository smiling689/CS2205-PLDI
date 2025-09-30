Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.SimpleProofsAndDefs.
Local Open Scope Z.

(** * 高阶函数 *)


(** 在Coq中，函数的参数也可以是函数。下面定义的_[shift_left1]_是一个二元函数，它的第
    一个参数_[f: Z -> Z]_是一个从整数到整数的一元函数，第二个参数_[x: Z]_是一个整数，这个函数依据两个参数计算出的函数值是_[f (x + 1)]_。*)

Definition shift_left1 (f: Z -> Z) (x: Z): Z :=
  f (x + 1).

(** 下面是两个_[shift_left1]_的例子。*)

Example shift_left1_square: forall x,
  shift_left1 square x = (x + 1) * (x + 1).
Proof. unfold shift_left1, square. lia. Qed.

Example shift_left1_plus_one: forall x,
  shift_left1 plus_one x = x + 2.
Proof. unfold shift_left1, plus_one. lia. Qed.

(** 从这两个例子可以看出，_[shift_left1]_作为一个二元函数，也可以被看作一个一元函数，
    这个一元函数的参数是一个整数到整数的函数，这个一元函数的计算结果也是一个整数到整数
    的函数。例如，_[shift_left1 square]_的计算结果在数学上可以写作函数 
        f(x) = (x + 1) * (x + 1)。
    更一般的，_[shift_left1 f]_可以看作将函数_[f]_在坐标平面中的图像左移一个单位的结
    果。这样的观点也可以在Coq中更直白地表达出来，下面定义的_[shift_left1']_实际上是与
    _[shift_left1]_完全相同的函数，但是这一定义在形式上是一个一元函数。*)

Definition shift_left1' (f: Z -> Z): Z -> Z :=
  fun x => f (x + 1).

(** 与_[shift_left1]_类似，我们还可以定义将一元函数图像向上移动一个单位的结果。*)

Definition shift_up1 (f: Z -> Z) (x: Z): Z :=
  f x + 1.

Example shift_up1_square: forall x,
  shift_up1 square x = x * x + 1.
Proof. unfold shift_up1, square. lia. Qed.

Example shift_up1_plus_one: forall x,
  shift_up1 plus_one x = x + 2.
Proof. unfold shift_up1, plus_one. lia. Qed.

(** 像_[shift_left1]_和_[shift_up1]_这样以函数为参数的函数称为高阶函数。高阶函数也可
    以是多元函数。例如下面的_[func_plus]_与_[func_mult]_定义了函数的加法和乘法。*)

Definition func_plus (f g: Z -> Z): Z -> Z :=
  fun x => f x + g x.

Definition func_mult (f g: Z -> Z): Z -> Z :=
  fun x => f x * g x.

(** 下面证明几条关于高阶函数的简单性质。首先我们证明，对于任意函数_[f]_，对它先左移再上
    移和先上移再左移的结果是一样的。*)

Lemma shift_up1_shift_left1_comm: forall f,
  shift_up1 (shift_left1 f) = shift_left1 (shift_up1 f).
Proof.
  intros.
  unfold shift_left1, shift_up1.
  reflexivity.
Qed.

(** 在上面证明中，在展开“左移”与“上移”的定义后，需要证明的结论是：

        _[(fun x : Z => f (x + 1) + 1) = (fun x : Z => f (x + 1) + 1)]_ 

    这个等式两边的表达式字面上完全相同，因此该结论显然成立。证明指令_[reflexivity]_
    表示利用“自反性”完成证明，所谓等式的自反性就是“任意一个数学对象都等于它自身”。下面
    我们还可以证明，将_[f]_与_[g]_两个函数先相加再图像左移，与先图像左移再函数相加得到
    的结果是一样的。*)

Lemma shift_left1_func_plus: forall f g,
  shift_left1 (func_plus f g) =
  func_plus (shift_left1 f) (shift_left1 g).
Proof.
  intros.
  unfold shift_left1, func_plus.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面命题。*)
(** 这里fun x => 1是一个常值函数，它的值在所有自变量下都为1。*)

Fact shift_up1_eq: forall f,
  shift_up1 f = func_plus f (fun x => 1).
Proof.
    unfold shift_up1, func_plus.
    reflexivity.
Qed.


(** * 高阶谓词 *)


(** 类似于高阶函数，如果一个谓词的参数中有函数（或谓词），那它就是一个高阶谓词。其实，
    许多常见数学概念都是高阶谓词。例如，函数的单调性就是一个高阶谓词。*)

Definition mono (f: Z -> Z): Prop :=
  forall n m, n <= m -> f n <= f m.

(** 有许多函数都是单调的。前面我们定义的_[plus_one]_函数就是个单调函数。*)

Example plus_one_mono: mono plus_one.
Proof.
  unfold mono, plus_one.
  intros.
  lia.
Qed.

(** 我们还可以定义整数函数的复合，然后证明复合函数能保持单调性。*)

Definition Zcomp (f g: Z -> Z): Z -> Z :=
  fun x => f (g x).

Lemma mono_compose: forall f g,
  mono f ->
  mono g ->
  mono (Zcomp f g).
Proof.
  unfold mono, Zcomp.
  intros f g Hf Hg n m Hnm.
  pose proof Hg n m Hnm as Hgnm.
  pose proof Hf (g n) (g m) Hgnm.
  lia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明常值函数都是单调的。*)

Lemma const_mono: forall a: Z,
  mono (fun x => a).
Proof.
    unfold mono.
    intros.
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

(** “结合律”也是一个常用的数学概念。如下面定义所示，一个二元函数_[f]_具有结合律，当且
    仅当它满足_[f x (f y z) = f (f x y) z]_。*)

Definition assoc (f: Z -> Z -> Z): Prop :=
  forall x y z,
    f x (f y z) = f (f x y) z.

(** 我们熟知整数的加法于乘法都满足结合律。下面是加法结合律与乘法结合律的Coq证明。*)

Lemma plus_assoc: assoc (fun x y => x + y).
Proof. unfold assoc. lia. Qed.

Lemma mult_assoc: assoc (fun x y => x * y).
Proof. unfold assoc. nia. Qed.

(************)
(** 习题：  *)
(************)

(** 请证明，我们先前定义的_[smul]_函数也符合结合律。*)
Lemma smul_assoc: assoc smul.
Proof.
    unfold assoc, smul.
    intros x y z.
    nia.
Qed.

(** 上面例子中的两个高阶谓词都是以函数为参数的高阶谓词，下面两个例子都是以谓词为参数的
    高阶谓词，甚至它们的参数本身也是高阶谓词。它们分别说的是，函数的性质_[P]_能被图像上
    移变换（_[shift_up1]_）保持以及能被图像左移变换（_[shift_left1]_）保持。*)

Definition preserved_by_shifting_up (P: (Z -> Z) -> Prop): Prop :=
  forall f, P f -> P (shift_up1 f).

Definition preserved_by_shifting_left (P: (Z -> Z) -> Prop): Prop :=
  forall f, P f -> P (shift_left1 f).

(** 不难发现，单调性就能被这两种图像平移变换保持。*)

Lemma mono_pu: preserved_by_shifting_up mono.
Proof.
  unfold preserved_by_shifting_up, mono, shift_up1.
  intros.
  pose proof H _ _ H0.
  lia.
Qed.

Lemma mono_pl: preserved_by_shifting_left mono.
Proof.
  unfold preserved_by_shifting_left, mono, shift_left1.
  intros.
  pose proof H (n + 1) (m + 1) ltac:(lia).
  lia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明“恒为非负”这一性质（见下面Coq定义）也被图像上移与图像左移变换保持。*)

Definition univ_nonneg {A: Type} (f: A -> Z): Prop :=
  forall a: A, f a >= 0.

Lemma univ_nonneg_pu: preserved_by_shifting_up univ_nonneg.
Proof.
    unfold preserved_by_shifting_up, univ_nonneg, shift_up1.
    intros.
    pose proof H a.
    lia.
Qed.

Lemma univ_nonneg_pl: preserved_by_shifting_left univ_nonneg.
Proof.
    unfold preserved_by_shifting_left, univ_nonneg, shift_left1.
    intros.
    pose proof H (a+1).
    lia.
Qed.

(** 在数学证明中，我们往往会先证明一些具有一般性的定理或引理，并后续的证明中使用这些定
    理或引理。站在编写Coq证明脚本的角度看，使用先前已经证明的定理也可以看作对定理本身证
    明代码的复用。反过来，如果一系列数学对象具有相似的性质，这些性质的证明方式上也是相似的，那么我们在Coq编码时就可以利用函数与谓词（特别是高阶函数和高阶谓词）概括性地描述这些数学对象之间的关系，并给出统一的证明。例如，当我们要证明

        _[fun x => x * x * x - 3 * x * x + 3 * x]_ 

    具备单调性时，可以基于下面代数变换并多次使用复合函数保持单调性这一引理完成证明。

        _[x * x * x - 3 * x * x + 3 * x = (x - 1)^3 + 1]_ *)

Example mono_ex1: mono (fun x => x * x * x - 3 * x * x + 3 * x).

(** 具体而言，下面在Coq中证明这一单调性性质的时候，将分两步进行。第一步先证明
    _[fun x => x - 1]_、_[fun x => x + 1]_与_[fun x => x * x * x]_这三个简单函数
    都是单调的；第二步则利用复合函数的单调性性质将这三个结论组合起来完成证明。*)

Proof.
  assert (mono (fun x => x - 1)) as H_minus.
  (** 这里的_[assert]_指令表示：声明_[mono (fun x => x - 1)]_这一命题成立。逻辑上
      看，一个合理的逻辑系统不应当允许我们凭空声明一条性质。因此，我们在完成声明后需要
      首先证明“为什么这一命题成立”，再基于此进行后续证明。在执行完这一条指令后，Coq系
      统显示目前有两个证明目标需要证明，它们分别对应这里所说的“为什么这一命题成立”与后
      续证明两部分。*)
  { unfold mono. lia. }
  (** 在有多个证明目标需要证明的时候，证明脚本中的左大括号表示进入其中的第一个证明目标
      的证明。这里的第一个证明目标就是要证明_[fun x => x - 1]_是一个单调函数。该证明
      结束后，证明脚本中的右大括号表示返回其余证明目标。返回后可以看到，证明目标中增加
      了一条前提：_[H_minus: fun x => x - 1]_。这一前提的名称_[H_minus]_是先前的
      _[assert]_指令选定的。*)
  assert (mono (fun x => x + 1)) as H_plus.
  { unfold mono. lia. }
  (** 类似的，这里可以使用声明+证明的方式证明_[fun x => x + 1]_也是一个单调函数。*)
  pose proof cube_mono as H_cube.
  (** 先前已经证明过，立方函数是单调的，这里直接_[pose proof]_这一结论。至此，我们已
      经完成了三个子命题的证明，下面的将通过复合函数的形式把它们组合起来。*)
  pose proof mono_compose _ _ H_plus (mono_compose _ _ H_cube H_minus).
  unfold mono.
  intros n m Hnm.
  unfold mono, Zcomp, plus_one in H.
  pose proof H n m Hnm.
  nia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面Coq命题。*)

Example mono_ex2: mono (fun x => x * x * x + 3 * x * x + 3 * x).
Proof.
    unfold mono.
    intros.
    pose proof cube_mono as H_cube.
    intros.
    unfold mono in H_cube.
    pose proof H_cube (n+1) (m+1).
    assert (n + 1 <= m + 1) by lia.
    pose proof H0 H1.
    assert (n * n * n + 3 * n * n + 3 * n + 1 <= m * m * m + 3 * m * m + 3 * m + 1) by nia.
    lia.
Qed.