Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.AlgebraicStructure.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)

(** 请证明下面二元关系的运算性质。*)

Example Rels_concat_ex1:
  forall (A: Type) (R1 R2: A -> A -> Prop),
    R1 ∘ R1 == ∅ ->
    R2 ∘ R2 == ∅ ->
    (R1 ∪ R2) ∘ (R1 ∪ R2) == R1 ∘ R2 ∪ R2 ∘ R1.
Proof.
    intros.
    Sets_unfold in H.
    Sets_unfold in H0.
    Sets_unfold.
    intros.
    specialize (H a a0) as [HR1 _].
    specialize (H0 a a0) as [HR2 _].
    split.
    - intro Hex.
        destruct Hex as [i [ [H1 | H2] [H3 | H4] ] ].
        + exfalso. 
            apply HR1. 
            exists i. 
            split; assumption.
        + left.  
            exists i. 
            split; assumption.
        + right. 
            exists i.
            split; assumption.
        + exfalso. 
            apply HR2. 
            exists i. 
            split; assumption.
    - intro Hex.
        destruct Hex as [ [i [H1 H2] ] | [i [H3 H4] ] ].
        + exists i.
            split.
            * left.
                assumption.
            * right.
                assumption. 
        + exists i.
            split.
            * right.
                assumption.
            * left.
                assumption.
Qed.


(************)
(** 习题：  *)
(************)

(** 请证明下面二元关系的性质。*)

Example Rels_concat_ex2:
  forall (A: Type) (T R1 R2 R3: A -> A -> Prop),
    T ∘ R1 ⊆ R2 ->
    T ∘ R2 ⊆ R3 ->
    T ∘ R3 ⊆ R1 ->
    T ∘ (R1 ∪ R2 ∪ R3) ⊆ R1 ∪ R2 ∪ R3.
Proof.
    intros.
    Sets_unfold.
    Sets_unfold in H.
    Sets_unfold in H0.
    Sets_unfold in H1.
    intros a a0 Hcomp.
    destruct Hcomp as [i [HT HR] ].
    destruct HR as [ [HR1 | HR2] | HR3].
    - pose proof (H a a0) as H2.
      assert ((a, a0) ∈ R2) as HR2'.
      { apply H2. exists i. split; assumption. }
      left. right. exact HR2'.
    - pose proof (H0 a a0) as H2.
      assert ((a, a0) ∈ R3) as HR3'.
      { apply H2. exists i. split; assumption. }
      right.  exact HR3'.
    - pose proof (H1 a a0) as H2.
      assert ((a, a0) ∈ R1) as HR1'.
      { apply H2. exists i. split; assumption. }
      left. left. exact HR1'.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面关于行为等价的性质。*)

Theorem if_seq:
  forall e c1 c2 c3,
    [[ if (e) then { c1 } else { c2 }; c3 ]] ~=~
    [[ if (e) then { c1; c3 } else { c2; c3 } ]].
Proof.
    unfold cequiv.
    intros.
    simpl.
    unfold if_sem, seq_sem.
    rewrite Rels_concat_union_distr_r.
    rewrite Rels_concat_assoc.
    rewrite Rels_concat_assoc.
    reflexivity.
Qed.
       


(************)
(** 习题：  *)
(************)

(** 请证明下面关于行为等价的性质。*)

Theorem if_not:
  forall e c1 c2,
    [[ if (! e) then { c1 } else { c2 } ]] ~=~
    [[ if (e) then { c2 } else { c1 } ]].
Proof.
    unfold cequiv.
    intros.
    simpl.
    unfold if_sem, not_sem.
    assert (test_true (Sets.complement ⟦ e ⟧) == test_false ⟦ e ⟧) as H.
    { reflexivity. }
    assert (test_false (Sets.complement ⟦ e ⟧) == test_true ⟦ e ⟧) as H1.
    { 
    unfold test_false.
    rewrite Sets_complement_complement.
    reflexivity.
   }
    rewrite H.
    rewrite H1.
    apply Sets_union_comm.
Qed.

(************)
(** 习题：  *)
(************)

(** 我们知道_[while (b) do { c }]_的语义满足一下等式：
   
          ⟦ while (b) do { c } ⟧ ==
          test_true ⟦ e ⟧ ∘ ⟦ c ⟧ ∘ ⟦ while (b) do { c } ⟧ ∪ test_false ⟦ e ⟧
      
    那么是否有其他程序状态上的二元关系_[R]_满足以下性质呢？
   
          R == test_true ⟦ e ⟧ ∘ ⟦ c ⟧ ∘ R ∪ test_false ⟦ e ⟧
      
    尽管下面的要你证明的这个结论并不能给出一个肯定或者否定的答案，但是至少也给出这样的
    _[R]_应当满足的一些基本性质。*)

Lemma while_sem_fact0:
  forall (e: expr_bool) (c: com) (R: state -> state -> Prop),
    test_true ⟦ e ⟧ ∘ ⟦ c ⟧ ∘ R ∪ test_false ⟦ e ⟧ ⊆ R ->
    while_sem ⟦ e ⟧ ⟦ c ⟧ ⊆ R.
Proof.
    intros.
    unfold while_sem.
    apply Sets_indexed_union_included.
    intros n.
    induction n.
    - simpl.
        unfold seq_sem, skip_sem.
        apply Sets_empty_included.
    - simpl.
        rewrite IHn.
        apply H.
Qed.


