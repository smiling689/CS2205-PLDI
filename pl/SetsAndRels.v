Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.



(** * 在Coq中表示集合与二元关系 *)

(** SetsClass拓展库中提供了有关集合的一系列定义。例如：
   
    - 空集：用 _[∅]_ 或者一堆方括号表示，定义为_[Sets.empty]_；

    - 全集：定义为_[Sets.full]_（全集没有专门的表示符号）；

    - 单元集：用一对方括号表示，定义为_[Sets.singleton]_；

    - 补集：定义为_[Sets.complement]_（补集没有专门的表示符号）；

    - 并集：用_[∪]_表示，定义为_[Sets.union]_；

    - 交集：用_[∩]_表示，定义为_[Sets.intersect]_；

    - 集合相等：用_[==]_表示，定义为_[Sets.equiv]_；

    - 元素与集合关系：用_[∈]_表示，定义为_[Sets.In]_；

    - 子集关系：用_[⊆]_表示，定义为_[Sets.included]_；

    在这些符号中，补集以及其他Coq函数的优先级最高，交集的优先级其次，并集的优先级再次，
    集合相等、集合包含与属于号的优先级最低。例如，下面是两个关于集合的命题，并且其中第
    二个命题中的括号可以省略：*)

Check forall A (X: A -> Prop), X ∪ ∅ == X.

Check forall A B (X Y: A -> B -> Prop), X ∪ (Y ∩ X) ⊆ X.

(** 在CoqIDE中，你可以利用CoqIDE对于unicode的支持打出特殊字符：
   
    - 首先，打出特殊字符的latex表示法；

    - 再按shift+空格键；

    - latex表示法就自动转化为了相应的特殊字符。

    例如，如果你需要打出符号_[∈]_，请先在输入框中输入_[\in]_，当光标紧跟在_[n]_
    这个字符之后的时候，按shift+空格键即可。
    
    在VSCode中，你可以使用Unicode Latex Input拓展包从而方便地打出这些特殊字符。安装该
    拓展包后，只需要输入_[\in]_就会出现提示框显示_[∈]_符号。

    值得一提的是，使用SetsClass拓展库中的集合时一定要使用双等号_[==]_而不是普通等号
    _[=]_表示集合相等，SetsClass拓展库已经为其用户证明了_[==]_是一个等价关系。

    SetsClass拓展库中提供了这些关于二元关系的定义：
   
    - 二元关系的连接：用 _[∘]_表示，定义为_[Rels.concat]_；

    - 相等关系：定义为_[Rels.id]_（没有专门的表示符号）；

    - 测试：定义为_[Rels.test]_（没有专门的表示符号）。

    基于此，我们可以将一些二元关系运算的例子写作Coq命题，下面就是一个这样的例子。*)

Fact plus_1_concat_plus_1:
  forall S1 S2: Z -> Z -> Prop,
    (forall n m, (n, m) ∈ S1 <-> m = n + 1) ->
    (forall n m, (n, m) ∈ S2 <-> m = n + 2) ->
    S1 ∘ S1 == S2.
Proof.
  intros S1 S2 H_S1 H_S2.
  Sets_unfold.
  intros x z.
  (** _[Sets_unfold]_指令将_[∘]_的定义展开，现在需要证明：
        - exists y, (x, y) ∈ S1 /\ (y, z) ∈ S1
      当且仅当
        - (x, z) ∈ S2]_。*)
  rewrite H_S2.
  setoid_rewrite H_S1.
  (** 根据_[S1]_与_[S2]_的定义，就只需要证明：
        - (exists y, y = x + 1 /\ z = y + 1) <-> z = x + 2 *)
  split.
  + intros [y [? ?]].
  (** [y [? ?]] 的意思是：存在一个y，使得x与y的关系在S1中成立，并且y与z的关系在S1中成立。
        这里的_[?]_表示存在一个命题，但我们并不关心它具体是什么，因此用_[?]_代替。*)
    lia.
  + intros.
    exists (x + 1).
    lia.
Qed.

(** * 集合与二元关系Coq证明 *)

(** ** 集合命题的基本证明方法 *)

(** SetsClass拓展库中的集合运算符都是基于Coq中的命题进行定义的。例如，
    当_[X Y: A -> Prop]_时，_[X ∩ Y]_就可以被定义为：

        _[fun a => X a /\ Y a]_。 

    这与我们对“交”运算的朴素理解是一致的，即，_[a ∈ X ∩ Y]_当且仅当_[a ∈ X]_并且
    _[a ∈ Y]_。类似的，_[a ∈ X ∪ Y]_当且仅当_[a ∈ X]_或者_[a ∈ Y]_。在证明中，也可
    以据此将集合间的运算性质规约为集合与元素之间的逻辑命题。例如，下面在Coq中证明了，与
    另一个集合做交集运算的结果是原集合的子集。*)

Theorem Sets1_intersect_included1: forall A (X Y: A -> Prop),
  X ∩ Y ⊆ X.
Proof.
  intros.
  (** 下面一条命令_[Sets_unfold]_是SetsClass库提供的自动证明指令，它可以将有关
      集合的性质转化为有关命题的性质。*)
  Sets_unfold.
  (** 原本要证明的关于交集的性质现在就转化为了：
        _[forall a : A, a ∈ X /\ a ∈ Y -> a ∈ X]_
      这个关于逻辑的命题在Coq中是容易证明的。*)
  intros.
  tauto.
Qed.

(** 下面是一条关于并集运算的性质。*)

Lemma Sets1_included_union1: forall A (X Y: A -> Prop),
  X ⊆ X ∪ Y.
Proof.
  intros.
  Sets_unfold.
  (** 经过转化，要证明的结论是：_[forall a : A, a ∈ X -> a ∈ X \/ a ∈ Y]_。*)
  intros.
  tauto.
Qed.

(** 我们也可以利用集合运算相关的前提进行证明。*)

Example Sets2_proof_sample1: forall A B (X Y Z: A -> B -> Prop),
  X ∪ Y ⊆ Z ->
  Y ⊆ Z.
Proof.
  intros.
  Sets_unfold in H.
  Sets_unfold.
  intros a b.
  specialize (H a b).
  tauto.
Qed.

(** 当所需证明性质较为简单的时候，将集合相关的Coq命题展开为逻辑相关的命题是一种有效的自
    动证明方法。然而，需要证明的结论有时也会比较复杂，例如，哪怕下面这条性质“交集运算对
    有穷多个集合的并具有分配律”的证明也需要我们对有穷长的集合序列做归纳证明。 

        _[A ∩ (B1 ∪ B2 ∪ ... ∪ Bn) == (A ∩ B1) ∪ ... ∪ (A ∩ Bn)]_ 

    这时，在集合层面基于集合运算的基本性质表述证明就变得更为直观简便了。从下一节开始，
    我们将介绍这样的证明方法。

    我们熟知，集合相等是一个等价关系，集合包含具有自反性和传递性。在Coq中，这些性质即是
    说：
   
        Equivalence Sets.equiv
        Reflexive Sets.included
        Transitive Sets.included
      
    SetsClass拓展库已经证明了这些定理，因此我们就可以把_[rewrite]_、
    _[reflexivity]_等证明指令用在集合相关的证明中。下面就是两个简单的例子。 *)

Example Sets1_proof_sample2: forall (A: Type) (X Y Z: A -> Prop),
  X == Y -> X == Z -> Y == Z.
Proof.
  intros.
  rewrite <- H, <- H0.
  reflexivity.
Qed.

Example Sets1_proof_sample3: forall (A: Type) (F: (A -> Prop) -> (A -> Prop)),
  (forall X: A -> Prop, X ⊆ F X) ->
  (forall X: A -> Prop, X ⊆ F (F X)).
Proof.
  intros.
  rewrite <- H, <- H.
  reflexivity.
Qed.

(** 另外，集合间的交集、并集和补集运算会保持“包含”与“被包含”关系，也会保持集合相等关
    系。在SetsClass拓展库中，已经证明了：
   
        Sets_union_mono:
          Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.union
        Sets_intersect_mono:
          Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.intersect
        Sets_union_congr:
          Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.union
        Sets_intersect_mono:
          Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.intersect
        Sets_complement_congr:
          Proper (Sets.equiv ==> Sets.equiv) Sets.complement
        Sets_complement_mono:
          Proper (Sets.included --> Sets.included) Sets.complement 
    当然，_[Sets.equiv]_与_[Sets.included]_也满足一些基于_[Proper]_描述的性质。
   
        Proper (Sets.included --> Sets.included ==> Basics.impl) Sets.included
        Proper (Sets.equiv ==> Sets.equiv ==> iff) Sets.equiv
        Proper (Sets.equiv ==> Sets.equiv ==> iff) Sets.included 
    上面这三条性质中，前两条是由_[Sets.included]_与_[Sets.equiv]_的传递性自动推导得
    到的，而第三条性质是SetsClass拓展库额外证明并提供给用户的。这些性质结合在一起，使
    得我们在许多时候都可以用Coq的rewrite指令较为方便地完成证明。下面是一个简单的例子。*)

Example Sets1_proof_sample4: forall (A: Type) (X1 X2 Y1 Y2: A -> Prop),
  X1 == X2 -> Y1 ⊆ Y2 -> X1 ∪ Y1 ⊆ X2 ∪ Y2.
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.


(** ** 交集与并集性质的Coq证明 *)

(** 相应的，要证明两个集合相等，就只需要证明它们相互包含。在Coq中只需要_[apply]_下面引
    理来实现这个证明步骤。
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
      
    要证明某两个集合的交集包含第三个集合，或者证明某两个集合的交集被第三个集合包含，又
    可以采取以下方法。

        _[x ⊆ y ∩ z]_可以被规约为_[x ⊆ y]_与_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_可以被规约为_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_也可以被规约为_[y ⊆ z]_。 

    在Coq中，前一种证明可以通过_[apply]_下面引理实现。
   
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
      
    而后两种证明可以通过_[rewrite]_下面引理实现。
   
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
      
    例如，我们可以如下证明集合交具有交换律和结合律。*)

Theorem Sets1_intersect_comm:
  forall {A: Type} (x y: A -> Prop),
    x ∩ y == y ∩ x.
Proof.
  intros.
  (** 首先，要证明两个集合相等只需要证明它们互为子集。*)
  apply Sets_equiv_Sets_included; split.
  + (** 第一个分支需要证明_[x ∩ y ⊆ y ∩ x]_，右边是两个集合的交集，因此这两个集合都包
        含左边集合即可。*)
    apply Sets_included_intersect.
    - (** 现在需要证明_[x ∩ y ⊆ y]_，形式上，是要证明左侧两个集合的交集是右侧集合的子
          集，这只需要证明左侧的第二个集合是右侧集合的子集就够了。 *)
      rewrite Sets_intersect_included2.
      reflexivity.
    - (** 类似的，这个子分支需要证明_[x ∩ y ⊆ x]_，我们可以选择将其归结为证明左边的一
          个集合是右边集合的子集。。 *)
      rewrite Sets_intersect_included1.
      reflexivity.
  + (** 第二个分支的证明是类似的。*)
    apply Sets_included_intersect.
    - rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included1.
      reflexivity.
Qed.

Theorem Sets1_intersect_assoc:
  forall {A: Type} (x y z: A -> Prop),
    (x ∩ y) ∩ z == x ∩ (y ∩ z).
Proof.
  intros.
  (** 与证明交集交换律的时候类似，我们将两个集合相等的证明归于为证明它们互为子集。*)
  apply Sets_equiv_Sets_included; split.
  + (** 第一个分支需要证明_[(x ∩ y) ∩ z ⊆ x ∩ (y ∩ z)]_。要证明左侧是右侧三个集合交集
        的子集，就需要证明左侧是右侧每一个集合的子集。*)
    apply Sets_included_intersect; [| apply Sets_included_intersect].
    (** 现在三个证明目标分别是：
        - (x ∩ y) ∩ z ⊆ x
        - (x ∩ y) ∩ z ⊆ y
        - (x ∩ y) ∩ z ⊆ z
        证明时只需要指明左边三个集合中哪一个是右边的子集即可。*)
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included2.
      reflexivity.
  + (** 第二个分支的证明是类似的。*)
    apply Sets_included_intersect; [apply Sets_included_intersect |].
    - rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included2.
      reflexivity.
Qed.

(** 对于并集运算而言，要证明某两个集合的并集包含第三个集合，或者证明某两个集合的并集被
    第三个集合包含，就类似于要证明形如_[P -> Q \/ R]_或_[P \/ Q -> R]_的命题。具体
    地，

        _[x ⊆ y ∪ z]_可以被规约为_[x ⊆ y]_; 

        _[x ⊆ y ∪ z]_也可以被规约为_[x ⊆ z]_; 

        _[x ∪ y ⊆ z]_可以被规约为_[x ⊆ z]_与_[y ⊆ z]_。 

    在Coq中，前两种证明可以通过从右向左_[rewrite]_下面引理实现。
   
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
      
    而后一种证明则可以通过_[apply]_下面引理实现。
   
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z;
      
    有时，包含号_[⊆]_左侧的集合不是一个并集，需要先使用交集对于并集的分配律才能使用
    _[Sets_union_included]_。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于集合的性质。 *)

Fact sets_fact_ex: forall (A: Type) (X Y: A -> Prop),
  X ⊆ Y ->
  X ∩ Y == X.
Proof.
    intros.
    apply Sets_equiv_Sets_included; split.
    + rewrite Sets_intersect_included1.
      reflexivity.
    + apply Sets_included_intersect.
        - reflexivity.
        - apply H.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_intersect_absorb_union:
  forall {A: Type} (x y: A -> Prop),
    x ∩ (x ∪ y) == x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + rewrite Sets_intersect_included1.
    reflexivity.
  + Sets_unfold.
    intros.
    split.
    - apply H.
    - tauto.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_union_absorb_intersect:
  forall {A: Type} (x y: A -> Prop),
    x ∪ (x ∩ y) == x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + Sets_unfold.
    intros.
    tauto.
  + Sets_unfold.
    intros.
    tauto.
Qed.


(** 总而言之，以下这些SetsClass拓展库中的引理，构成了供我们手动证明集合运算性质的基本
    方法。
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z
        Sets_intersect_union_distr_r:
          forall x y z, (x ∪ y) ∩ z == x ∩ z ∪ y ∩ z
        Sets_intersect_union_distr_l:
          forall x y z, x ∩ (y ∪ z) == x ∩ y ∪ x ∩ z
      
    基于这些引理，我们前面已经证明集合交的交换律与结合律。这些我们演示过的证明都已经包
    含在SetsClass拓展库中了，除此之外，SetsClass拓展库还提供了集合并的交换律与结合
    律以及集合并对集合交左右分配律。SetsClass拓展库中的证明也不限于形如_[A -> Prop]_
    类型的Coq集合，而一并考虑了_[A -> B -> Prop]_、_[A -> B -> C -> Prop]_等所有可
    能的情形。
   
        Sets_intersect_comm:
          forall x y, x ∩ y == y ∩ x
        Sets_intersect_assoc:
          forall x y z, (x ∩ y) ∩ z == x ∩ (y ∩ z)
        Sets_union_comm:
          forall x y, x ∪ y == y ∪ x
        Sets_union_assoc:
          forall x y z, (x ∪ y) ∪ z == x ∪ (y ∪ z)
        Sets_union_intersect_distr_l:
          forall x y z, x ∪ (y ∩ z) == (x ∪ y) ∩ (x ∪ z)
        Sets_union_intersect_distr_r:
          forall x y z, (x ∩ y) ∪ z == (x ∪ z) ∩ (y ∪ z)
      *)

(** ** 空集、补集、全集、无穷交与无穷并性质的Coq证明 *)

(** SetsClass拓展库对于空集的支持主要是通过以下性质：空集是一切集合的子集。
   
        Sets_empty_included: forall x, ∅ ⊆ x
      
    相对应的，一切集合都是全集的子集。 
   
        Sets_included_full: forall x, x ⊆ Sets.full
      
    基于这两条性质，可以证明许多有用的导出性质。SetsClass提供的导出性质有：
   
        Sets_union_empty_l: forall x, ∅ ∪ x == x
        Sets_union_empty_r: forall x, x ∪ ∅ == x
        Sets_intersect_empty_l: forall x, ∅ ∩ x == ∅
        Sets_intersect_empty_r: forall x, x ∩ ∅ == ∅
        Sets_union_full_l: forall x, Sets.full ∪ x == Sets.full
        Sets_union_full_r: forall x, x ∪ Sets.full == Sets.full
        Sets_intersect_full_l: forall x, Sets.full ∩ x == x
        Sets_intersect_full_r: forall x, x ∩ Sets.full == x
        Sets_equiv_empty_fact: forall x, x ⊆ ∅ <-> x == ∅
        Sets_equiv_full_fact: forall x, Sets.full ⊆ x <-> x == Sets.full
      *)

(************)
(** 习题：  *)
(************)

(** 前面已经提到，SetsClass拓展库已经证明了_[Sets_intersect_empty_l]_。请你只使用
    _[Sets_empty_included]_以及交集的性质证明它。*)

Lemma Sets1_intersect_empty_l:
  forall (A: Type) (x: A -> Prop), ∅ ∩ x == ∅.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
    + rewrite Sets_intersect_included1.
      reflexivity.
    + apply Sets_included_intersect.
        reflexivity.
        apply Sets_empty_included.
Qed.

(** SetsClass库中提供的关于补集的性质有下面四组。(1) 一个集合与自己的补集求交或求并会
    得到空集或全集。 
   
        Sets_intersect_complement_self
          forall x, x ∩ Sets.complement x == ∅
        Sets_complement_self_intersect
          forall x, Sets.complement x ∩ x == ∅
        Sets_union_complement_self:
          forall x, x ∪ Sets.complement x == Sets.full
        Sets_complement_self_union
          forall x, Sets.complement x ∪ x == Sets.full
      
    (2) 补集的补集是原集合。 
   
        Sets_complement_complement
          forall x, Sets.complement (Sets.complement x) == x
      
    (3) 交集或并集的补集满足德摩根律。 
   
        Sets_complement_union
          forall x y,
            Sets.complement (x ∪ y) ==
            Sets.complement x ∩ Sets.complement y
        Sets_complement_intersect
          forall x y,
            Sets.complement (x ∩ y) ==
            Sets.complement x ∪ Sets.complement y
      
    (4) 补集与包含关系之间满足类似逆否命题之间的性质。 
   
        Sets_contrapositive_PP:
          forall x y, x ⊆ y -> Sets.complement y ⊆ Sets.complement x
        Sets_contrapositive_CC:
          forall x y, Sets.complement y ⊆ Sets.complement x -> x ⊆ y
        Sets_contrapositive_PC:
          forall x y, y ⊆ Sets.complement x -> x ⊆ Sets.complement y
        Sets_contrapositive_CC:
          forall x y, Sets.complement x ⊆ y -> Sets.complement y ⊆ x
      

    SetsClass拓展库提供了两种支持无穷交集和无穷并集的定义。它们的证明方式与普通的并集
    与交集的证明方式是类似的。

    - 基于指标集的集合并：_[⋃ X]_，_[Sets.indexed_union X]_
    
    - 基于指标集的集合交：_[⋂ X]_，_[Sets.indexed_intersect X]_
    
    - 广义并：_[⨆ U]_，_[Sets.general_union U]_
    
    - 广义交：_[⨅ U]_，_[Sets.general_intersect U]_


    它们相关性质的证明方式与普通并集与交集的证明方式是类似的。下面是一个简单的例子。*)

Example Sets1_union_indexed_intersect_fact:
  forall {A: Type} (x: nat -> A -> Prop) (y: A -> Prop),
    (⋂ x) ∪ y ⊆ ⋂ (fun n => x n ∪ y).
Proof.
  intros.
  (** 要证明左边集合是右边这无穷多个集合交集的子集，就需要证明左边集合是右边每一个集合
      的子集。 *)
  apply Sets_included_indexed_intersect.
  intros n.
  (** 现在只需要证明_[⋂ x ∪ y ⊆ x n ∪ y]_。 *)
  rewrite (Sets_indexed_intersect_included n).
  reflexivity.
Qed.

(** ** 二元关系运算性质的Coq证明 *)

(** 二元关系除了满足普通集合的运算性质之外，还有几条额外的重要运算性质。

   

    - 结合律：_[(x ∘ y) ∘ z == x ∘ (y ∘ z)]_
    
    - 左单位元：_[Rels.id ∘ x == x]_
    
    - 右单位元：_[x ∘ Rels.id == x]_
    
    - 左分配律：_[x ∘ (y ∪ z) == x ∘ y ∪ x ∘ z]_

    - 右分配律：_[(x ∪ y) ∘ z == x ∘ z ∪ y ∘ z]_


    另外，二元关系对并集的分配律对于无穷并集也成立。这些性质对应了SetsClass库中的下面
    这些定理。*)
(************)
(** 习题：  *)
(************)

(** 请根据二元关系连接的定义证明下面性质。*)

Lemma plus_n_plus_m:
  forall (plus_rel: Z -> Z -> Z -> Prop),
    (forall n m1 m2, (m1, m2) ∈ plus_rel n <-> m1 + n = m2) ->
    (forall n m, plus_rel n ∘ plus_rel m == plus_rel (n + m)).
Proof.
    intros.
    Sets_unfold.
    intros x z.
    rewrite H.
    setoid_rewrite H.
    split.
    + intros [y [? ?]].
        lia.
    + intros.
        exists (x + n).
        lia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请根据二元关系连接的定义证明下面性质。*)

Lemma Rels22_concat_assoc:
  forall {A: Type} (x y z: A -> A -> Prop),
    (x ∘ y) ∘ z == x ∘ (y ∘ z).
Proof.
  intros.
  Sets_unfold.
  intros a d.
  split.
  - intros [b [[c [Hxc Hycb]] Hbd]].
    exists c. split; [exact Hxc|].
    exists b. split; assumption.
  - intros [c [Hac [b [Hcb Hbd]]]].
    exists b. split.
    + exists c. split; assumption.
    + exact Hbd.
Qed.

Lemma Rels22_concat_id_l:
  forall {A: Type} (x: A -> A -> Prop),
    Rels.id ∘ x == x.
Proof.
  intros.
  Sets_unfold.
  intros a b.
  split.
  - intros [c [Hac Hcb]].
    subst c.
    exact Hcb.
  - intros Hxab.
    exists a. split; [reflexivity | exact Hxab].
Qed.

Lemma Rels22_concat_union_distr_r:
  forall {A: Type} (x y z: A -> A -> Prop),
    (x ∪ y) ∘ z == x ∘ z ∪ y ∘ z.
Proof.
  intros.
  Sets_unfold.
  intros a c.
  split.
  - intros [b [Hunion Hzb]].
    destruct Hunion as [Hxb | Hyb].
    + left. exists b. split; assumption.
    + right. exists b. split; assumption.
  - intros [[b [Hxb Hzb]] | [b [Hyb Hzb]]].
    + exists b. split; [left; exact Hxb | exact Hzb].
    + exists b. split; [right; exact Hyb | exact Hzb].
Qed.
