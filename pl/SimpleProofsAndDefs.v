Require Import Coq.Logic.Classical_Prop.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.

(** * 整数算数运算与大小比较 *)


(** 算术与数量之间的大小关系是日常生活中最常见的数学概念。我们可以用数描述物体的数量、
    几何图形的长度与面积、人的年龄等等。作为Coq验证工具的入门篇，这一章将介绍如何使用
    Coq表达一些简单的数量关系，并证明一些简单的性质。

    大约在1500年前，《孙子算经》一书中记载了这样一个有趣的问题：今有雉兔同笼，上有三十 
    五头，下有九十四足，问雉兔各几何？这就是著名的鸡兔同笼问题。我们都知道，如果用C表示
    鸡（Chicken）的数量，用R表示兔（Rabbit）的数量，那么这一问题中的数量关系就可以表示
    为：

        _[C + R = 35]_ 

        _[2 * C + 4 * R = 94]_ 

    进而可以求解得知_[C = 23]_（也可以求解得到_[R = 12]_）。这一推理过程可以在Coq中表
    示成为下面命题。*)

Fact chickens_and_rabbits: forall C R: Z,
  C + R = 35 ->
  2 * C + 4 * R = 94 ->
  C = 23.

(** 字面意思上，这个命题说的是：对于任意整数_[C]_与_[R]_，如果_[C + R = 35]_并且
    _[2 * C + 4 * R = 94]_，那么_[C = 23]_。其中，_[forall]_与_[->]_是Coq中描述数
    学命题的常用符号。

    在Fact指令之后，我们可以在Coq中证明这个数学命题成立。如果要用中学数学知识完成这一
    证明，恐怕要使用加减消元法、代入消元法等代数技巧。Coq并不需要我们掌握这些数学技巧，
    Coq系统可以自动完成整数线性运算性质（linear integer arithmetic，简称lia）的证
    明，_[chickens_and_rabbits]_这一命题在Coq中的证明只需一行：*)

Proof. lia. Qed.

(** 在这一行代码中，Proof和Qed表示一段证明的开头与结尾，在它们之间的_[lia]_指令是证明
    脚本。

    一般而言，编写Coq证明的过程是交互式的——“交互式”的意思是：在编写证明代码的同时，我
    们可以在Coq定理证明环境中运行证明脚本，获得反馈，让定理证明系统告诉我们“已经证明了
    哪些结论”、“还需要证明哪些结论”等等，并以此为依据编写后续的证明代码。安装VSCoq插
    件的VSCode编辑器、安装proof-general插件的emacs编辑器以及CoqIDE都是成熟易用的Coq
    定理证明环境。
    
    以上面的证明为例，执行_[lia]_指令前，证明窗口显示了当前还需证明的性质（亦称为证明
    目标，proof goal）：
   
        ------------------------------------------
        (1/1)
        forall C R : Z,
        C + R = 35 -> 2 * C + 4 * R = 94 -> C = 23
      
    这里横线上方的是目前可以使用的前提，横线下方的是目前要证明的结论，目前，前提集合为
    空。横线下方的(1/1)表示总共还有1个证明目标需要证明，当前显示的是其中的第一个证明目
    标。利用证明脚本证明的过程中，每一条证明指令可以将一个证明目标规约为0个，1个或者更
    多的证明目标。执行_[lia]_指令之后，证明窗口显示：Proof finished。表示证明已经完
    成。一般情况下，Coq证明往往是不能只靠一条证明指令完成证明的。

    Coq证明指令_[lia]_除了能够证明关于线性运算的等式，也可以证明关于线性运算的不等式。
    下面这个例子选自熊斌教授所著《奥数教程》的小学部分：幼儿园的小朋友去春游，有男孩、
    女孩、男老师与女老师共16人，已知小朋友比老师人数多，但是女老师比女孩人数多，女孩又
    比男孩人数多，男孩比男老师人数多，请证明幼儿园只有一位男老师。*)

Fact teachers_and_children: forall MT FT MC FC: Z,
  MT > 0 ->
  FT > 0 ->
  MC > 0 ->
  FC > 0 ->
  MT + FT + MC + FC = 16 ->
  MC + FC > MT + FT ->
  FT > FC ->
  FC > MC ->
  MC > MT ->
  MT = 1.
Proof. lia. Qed.

(************)
(** 习题：  *)
(************)

(** 请在Coq中描述下面结论并证明：如果今年甲的年龄是乙5倍，并且5年后甲的年龄是乙的3倍，
    那么今年甲的年龄是25岁。*)


(** 除了线性性质之外，Coq中还可以证明的一些更复杂的性质。例如下面就可以证明，任意两个整
    数的平方和总是大于它们的乘积。证明中使用的指令_[nia]_表示的是非线性整数运算
    （nonlinear integer arithmetic）求解。*)

Fact sum_of_sqr1: forall x y: Z,
  x * x + y * y >= x * y.
Proof. nia. Qed.

(** 不过，_[nia]_与_[lia]_不同，后者能够保证关于线性运算的真命题总能被自动证明（规模过
    大的除外），但是有不少非线性的算数运算性质是_[nia]_无法自动求解的。例如，下面例子说明，一些很简单的命题_[nia]_都无法完成自动验证。*)

Fact sum_of_sqr2: forall x y: Z,
  x * x + y * y >= 2 * x * y.
Proof. Fail nia. Abort.

(** 这时，我们就需要编写证明脚本，给出中间证明步骤。证明过程中，可以使用Coq标准库中的结
    论，也可以使用我们自己实现证明的结论。例如，Coq标准库中，_[sqr_pos]_定理证明了任意
    一个整数_[x]_的平方都是非负数，即：

       _[sqr_pos: forall x: Z, x * x >= 0]_ 

    我们可以借助这一性质完成上面_[sum_of_sqr2]_的证明。*)

Fact sum_of_sqr2: forall x y: Z,
  x * x + y * y >= 2 * x * y.
Proof.
  intros.
  pose proof sqr_pos (x - y).
  nia.
Qed.

(** 这段证明有三个证明步骤。证明指令_[intros]_将待证明结论中的逻辑结构“对于任意整数x与
    y”移除，并在前提中假如“x与y是整数”这两条假设。第二条指令_[pose proof]_表示对x-y使
    用标准库中的定理_[sqr_pos]_。从Coq定理证明界面中可以看到，使用该定理得到的命题会被
    添加到证明目标的前提中去，Coq系统将这个新命题自动命名为H（表示Hypothesis）。最后，
    _[nia]_可以自动根据当前证明目标中的前提证明结论。

    下面证明演示了如何使用我们刚刚证明的性质_[sum_of_sqr1]_。*)

Example quad_ex1: forall x y: Z,
  x * x + 2 * x * y + y * y + x + y + 1 >= 0.
Proof.
  intros.
  pose proof sum_of_sqr1 (x + y) (-1).
  nia.
Qed.

(** 下面这个例子说的是：如果_[x < y]_，那么_[x * x + x * y + y * y]_一定大于零。*)

Fact sum_of_sqr_lt: forall x y: Z,
  x < y ->
  x * x + x * y + y * y > 0.

(** 在我们学习数学知识时，我们知道_[x * x + x * y + y * y]_是恒为非负的，而且只有在
    _[x]_与_[y]_都为0的时候，这个式子才能取到0，因此，在_[x < y]_的前提下，这个式子恒
    为正。在进一步学习Coq定理证明器的使用之后，我们完全可以在Coq中表达上述证明过程。不
    过，如果仅仅使用目前所介绍的几条Coq证明指令，其实也是可以完成上面命题的Coq证明的。
    不过，此处就需要换一条证明思路。

    我们可以利用下面两式相等证明：

        _[4 * (x * x + x * y + y * y)]_ 

        _[3 * (x + y) * (x + y) + (x - y) * (x - y)]_ 

    于是，在_[x < y]_的假设下，等式右边的两个平方式一个恒为非负，一个恒为正。因此，等
    式的左边也恒为正。将这一思路写成Coq证明如下：*)

Proof.
  intros.
  pose proof sqr_pos (x + y).
  nia.
Qed.

(** 可以看到，在_[x < y]_的前提下，Coq的_[nia]_指令可以自动推断得知_[(x - y)]_的平方
    恒为正。不过，我们仍然需要手动提示Coq，_[(x + y)]_的平方恒为非负。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面结论。提示：可以利用以下代数变换完成证明 

        _[4 * (x * x + 3 * x + 4) = (2 * x + 3) * (2 * x + 3) + 7]_ *)

Example quad_ex2: forall x: Z,
  x * x + 3 * x + 4 > 0.
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** * 函数与谓词 *)

(** 函数是一类重要的数学对象。例如，“加一”这个函数往往可以写作：f(x) = x + 1。
    在Coq中，我们可以用以下代码将其定义为_[plus_one]_函数。*)

Definition plus_one (x: Z): Z := x + 1.

(** 在类型方面，_[plus_one (x: Z): Z]_表示这个函数的自变量和值都是整数，而_[:=]_符号
    右侧的表达式_[x + 1]_也描述了函数值的计算方法。

    我们知道，“在1的基础上加一”结果是2，“在1的基础上加一再加一”结果是3。这些简单论断都
    可以用Coq命题表达出来并在Coq中证明。*)

Example One_plus_one: plus_one 1 = 2.
Proof. unfold plus_one. lia. Qed.

Example One_plus_one_plus_one: plus_one (plus_one 1) = 3.
Proof. unfold plus_one. lia. Qed.

(** 下面是更多函数的例子。我们可以采用类似于定义“加一”的方法定义“平方”函数。*)

Definition square (x: Z): Z := x * x.

Example square_5: square 5 = 25.
Proof. unfold square. lia. Qed.

(** Coq中也可以定义多元函数。*)

Definition smul (x y: Z): Z := x * y + x + y.

Example smul_ex1: smul 1 1 = 3.
Proof. unfold smul. lia. Qed.

Example smul_ex2: smul 2 3 = 11.
Proof. unfold smul. lia. Qed.

(** 下面Coq代码定义了“非负”这一概念。在Coq中，可以通过定义类型为_[Prop]_的函数来定义
    谓词。以下面定义为例，对于每个整数_[x]_，_[:=]_符号右侧表达式_[x >= 0]_是真还是假
    决定了_[x]_是否满足性质_[nonneg]_（即，非负）。 *)

Definition nonneg (x: Z): Prop := x >= 0.

Fact nonneg_plus_one: forall x: Z,
  nonneg x -> nonneg (plus_one x).
Proof. unfold nonneg, plus_one. lia. Qed.

Fact nonneg_square: forall x: Z,
  nonneg (square x).
Proof. unfold nonneg, square. nia. Qed.

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact nonneg_smul: forall x y: Z,
  nonneg x -> nonneg y -> nonneg (smul x y).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 我们可以使用乘法运算定义“正负号不同”这个二元谓词。请基于这一定义完成相关性质的Coq证
    明。*)

Definition opposite_sgn (x y: Z): Prop := x * y < 0.

Fact opposite_sgn_plus_2: forall x,
  opposite_sgn (x + 2) x ->
  x = -1.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Fact opposite_sgn_odds: forall x,
  opposite_sgn (square x) x ->
  x < 0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma descale_quad_nonneg: forall a b c k: Z,
  k > 0 ->
  quad_nonneg (k * a) (k * b) (k * c) ->
  quad_nonneg a b c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma plus_quad_nonneg: forall a1 b1 c1 a2 b2 c2: Z,
  quad_nonneg a1 b1 c1 ->
  quad_nonneg a2 b2 c2 ->
  quad_nonneg (a1 + a2) (b1 + b2) (c1 + c2).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 我们知道，如果二次式的二次项系数为正且判别式不为正，那么这个二次式在自变量取遍一切
    实数的时候都恒为正。相应的性质在自变量取遍一切整数的时候自然也成立。请证明这一结
    论。【选做】*)

Lemma plus_quad_discriminant: forall a b c,
  a > 0 ->
  b * b - 4 * a * c <= 0 ->
  quad_nonneg a b c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 然而，判别式不为正并不是_[quad_nonneg]_的必要条件。下面命题是一个简单的反例。*)

Example quad_nonneg_1_1_0: quad_nonneg 1 1 0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** * 逻辑连接词与逻辑命题 *)

(** 数学中可以用“并且”、“或”、“非”、“如果-那么”、“存在”以及“任意”把简单性质组合起来构
    成复杂性质或复杂命题，例如“单调且连续”与“无限且不循环”这两个常用数学概念的定义中就
    用到了逻辑连接词“并且”，又例如“有零点”这一数学概念的定义就要用到“存在”这个逻辑中的
    量词（quantifier）。Coq中也允许用户使用这些常用的逻辑符号。

    下面是一个使用逻辑符号定义复合命题的例子。前面我们已经定义过_[nonneg]_表示一个整数
    非负，Coq标准库中还提供了谓词_[Z.Odd]_和_[Z.Even]_表示一个整数是奇数/偶数。因此，
    我们就可以用_[nonneg n /\ Z.Even n]_表示整数_[n]_是一个非负偶数。

    下面性质说的是，如果一个函数_[f]_能保持非负性，也能保持奇偶性，那么它也能保持“非负
    偶数”这个性质。*)

Fact logic_ex1: forall f: Z -> Z,
  (forall n, nonneg n -> nonneg (f n)) ->
  (forall n, Z.Odd n -> Z.Odd (f n)) ->
  (forall n, Z.Even n -> Z.Even (f n)) ->
  (forall n, nonneg n /\ Z.Even n -> nonneg (f n) /\ Z.Even (f n)).

(** 不难发现，这一性质的证明“非负”的定义无关，也和奇偶性的定义无关，这一性质的证明只需
    用到其中各个逻辑符号的性质。下面是Coq证明。*)

Proof.
  intros.
  (** 在_[intros]_指令执行后，Coq证明目标中共有四条前提：
      - H: forall n: Z, nonneg n -> nonneg (f n)
      - H0: forall n: Z, Z.Odd n -> Z.Odd (f n)
      - H1: forall n: Z, Z.Even n -> Z.Even (f n)
      - H2: nonneg n /\ Z.Even n *)
  pose proof H n.
  (** 获得一个新的前提
      - H3: nonneg n -> nonneg (f n) *)
  pose proof H1 n.
  (** 获得一个新的前提
      - H3: Z.Even n -> Z.Even (f n) *)
  (** 而_[H0]_这个关于奇数的前提没有用 *)
  tauto.
Qed.

(** 最后一条证明指令_[tauto]_是英文单词“tautology”的缩写，表示当前证明目标是一个命题
    逻辑永真式，可以自动证明。在上面证明中，如果把命题_[nonneg n]_与_[Z.Even n]_记作
    命题_[P1]_与_[Q1]_，将命题_[nonneg (f n)]_看作一个整体记作_[P2]_，将命题
    _[Z.Even (f n)]_也看作一个整体记为_[Q2]_，那么证明指令_[tauto]_在此处证明的结论
    就可以概括为：如果

        _[P1]_成立并且_[Q1]_成立（前提_[H1]_）

        _[P1]_能推出_[P2]_（前提_[H2]_） 

        _[Q1]_能推出_[Q2]_（前提_[H3]_） 

    那么_[P2]_成立并且_[Q2]_成立。不难看出，无论_[P1]_、_[Q1]_、_[P2]_与_[Q2]_这四
    个命题中的每一个是真是假，上述推导都成立。因此，这一推导过程可以用一个命题逻辑永真
    式刻画，_[tauto]_能够自动完成它的证明。Coq中也可以把这一原理单独地表述出来：*)

Fact logic_ex2: forall P1 Q1 P2 Q2: Prop,
  P1 /\ Q1 ->
  (P1 -> P2) ->
  (Q1 -> Q2) ->
  P2 /\ Q2.
Proof.
  intros P1 Q1 P2 Q2 H1 H2 H3.
  tauto.
Qed.

(** 仅仅利用_[tauto]_指令就已经能够证明不少关于逻辑的结论了。下面两个例子刻画了一个命
    题与其逆否命题的关系。*)

Fact logic_ex3: forall {A: Type} (P Q: A -> Prop),
  (forall a: A, P a -> Q a) ->
  (forall a: A, ~ Q a -> ~ P a).
Proof. intros A P Q H a. pose proof H a. tauto. Qed.

Fact logic_ex4: forall {A: Type} (P Q: A -> Prop),
  (forall a: A, ~ Q a -> ~ P a) ->
  (forall a: A, P a -> Q a).
Proof. intros A P Q H a. pose proof H a. tauto. Qed.

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact logic_ex5: forall {A: Type} (P Q: A -> Prop),
  (forall a: A, P a -> Q a) ->
  (forall a: A, P a) ->
  (forall a: A, Q a).
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

(** 请在Coq中证明下面结论。*)

Fact logic_ex8: forall {A B: Type} (P Q: A -> B -> Prop),
  (forall (a: A) (b: B), P a b -> Q a b) ->
  (forall (a: A) (b: B), ~ P a b \/ Q a b).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact logic_ex9: forall {A B: Type} (P Q: A -> B -> Prop),
  (forall (a: A) (b: B), ~ P a b \/ Q a b) ->
  (forall (a: A) (b: B), P a b -> Q a b).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

