Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.AlgebraicStructure.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
Local Open Scope list.
Local Open Scope Z.
Local Open Scope sets.

(**    本次测试各题分值如下（100分记满分）：                 
                                                          
       + 第一题 rotate                                    
         - rotate_refl 10                                 
         - rotate_sym 10                                  
         - app_split3 35                                  
         - rotate_trans 25                                
       + 第二题 power_rel                                 
         - power_rel_add 25                               
         - power_rel_trans 25                             
       + 第三题 semantics                                 
         - Rels_test_concat_comm 25                       
         - if_if 25                                       **)

(************)
(** 习题：  *)
(************)

(** 如果把一个序列（_[list]_）看作环状的，那么 

        _[[1; 2; 3; 4]]_ 

        _[[2; 3; 4; 1]]_ 

        _[[3; 4; 1; 2]]_ 

        _[[4; 1; 2; 3]]_ 

    表示的是同一个环。下面定义的_[rotate]_就表示，可以通过轮转变换由一个序列得到另一个
    序列，换言之，这两个序列表示的是同一个环。*)

Definition rotate {A: Type} (l1 l2: list A): Prop :=
  exists lx ly, l1 = lx ++ ly /\ l2 = ly ++ lx.

(** 首先，请证明_[rotate]_具有自反性：*)

#[export] Instance rotate_refl {A: Type}: Reflexive (@rotate A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 其次，请证明_[rotate]_具有对称性。*)

#[export] Instance rotate_symm {A: Type}: Symmetric (@rotate A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 要证明_[rotate]_具有传递性要复杂一些。根据定义，

        _[rotate l1 l2]_ 

        _[rotate l2 l3]_ 

    这两个条件等价于存在_[lx]_、_[ly]_、_[lu]_与_[lv]_使得：

        _[l1 = lx ++ ly]_ 

        _[l2 = ly ++ lx]_ 

        _[l2 = lu ++ lv]_ 

        _[l3 = lv ++ lu]_ 

    观察中间两条性质，我们立即知道_[ly ++ lx = lu ++ v]_。这意味着，要么_[l2]_可以写
    成_[ly ++ l ++ lv]_的形式，并且 

        _[lx = l ++ lv]_ 

        _[lu = ly ++ l]_； 

    要么_[l2]_可以写成_[lu ++ l ++ lx]_的形式，并且 

        _[ly = lu ++ l]_ 

        _[lv = l ++ lx]_。 

    无论是两种情况中的哪一种成立，都足以帮助我们证明_[rotate l1 l3]_。下面，请首先证
    明这条证明传递性时需要用到的重要引理，请注意恰当选择归纳证明的对象，也要恰当选择加
    强归纳的方法。*)

Lemma app_split3: forall {A: Type} (lx ly lu lv: list A),
  ly ++ lx = lu ++ lv ->
  (exists l, ly = lu ++ l /\ lv = l ++ lx) \/
  (exists l, lu = ly ++ l /\ lx = l ++ lv).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 接下去，请用上面的引理_[app_split3]_证明_[rotate]_有传递性。*)

#[export] Instance rotate_trans {A: Type}: Transitive (@rotate A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 现在我们已经证明了_[rotate]_是一个等价关系，因此就可以在Coq中写如下证明了。*)

Example rotate_ex: forall {A: Type} (l1 l2 l3 l4: list A),
  rotate l1 l2 ->
  rotate l3 l2 ->
  rotate l3 l4 ->
  rotate l1 l4.
Proof.
  intros A l1 l2 l3 l4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.



(************)
(** 习题：  *)
(************)

(** 下面是二元关系的幂运算。*)

Fixpoint power_rel {A: Type} (R: A -> A -> Prop) (n: nat): A -> A -> Prop :=
  match n with
  | O => Rels.id
  | S n0 => R ∘ power_rel R n0
  end.

(** 请证明下面二元关系幂运算的性质。*)

Lemma power_rel_add: forall {A: Type} (R: A -> A -> Prop) (n m: nat),
  power_rel R n ∘ power_rel R m == power_rel R (n + m)%nat.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem power_rel_trans: forall {A: Type} (R: A -> A -> Prop),
  ⋃ (power_rel R) ∘ ⋃ (power_rel R) == ⋃ (power_rel R).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4.

(************)
(** 习题：  *)
(************)

(** 请使用集合运算的定义以及_[Sets_unfold]_（或_[sets_unfold]_指令）证明下面关于测试
    关系的性质：*)

Theorem Rels_test_concat_comm:
  forall D1 D2: state -> Prop,
    Rels.test D1 ∘ Rels.test D2 ==
    Rels.test D2 ∘ Rels.test D1.
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 请证明下面关于行为等价的性质，证明中可以用到上面的结论。*)

Theorem if_if:
  forall e1 e2 c1 c2 c3 c4,
    [[ if (e1)
       then { if (e2) then {c1} else {c2} }
       else { if (e2) then {c3} else {c4} } ]] ~=~
    [[ if (e2)
       then { if (e1) then {c1} else {c3} }
       else { if (e1) then {c2} else {c4} } ]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


