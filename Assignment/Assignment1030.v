Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List. Import ListNotations.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.AlgebraicStructure.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope list.

(** 本次作业中最后三题_[app_sem_assoc1]_、_[app_sem_assoc2]_与_[RE_App_assoc]_的证
    明为附加题。*)

(************)
(** 习题：  *)
(************)

Theorem rev_app_distr:
  forall A (l1 l2: list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros.
    induction l1 as [| h t IH].
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

Theorem rev_involutive:
  forall A (l: list A), rev (rev l) = l.
Proof.
    intros.
    induction l as [| h t IH].
    - simpl. reflexivity.
    - simpl. rewrite rev_app_distr. simpl. rewrite IH. reflexivity.
Qed.



(************)
(** 习题：  *)
(************)


(** 指称语义是一种定义语义的通用方法。下面我们将利用指称语义的思想定义正则表达式的含
    义。下面是正则表达式的定义： *)

Inductive reg_exp (A: Type): Type :=
| RE_EmptyStr: reg_exp A                 (** empty string *)
| RE_Single (a: A): reg_exp A            (** single char *)
| RE_Union (r1 r2: reg_exp A): reg_exp A (** r1 | r2 *)
| RE_App (r1 r2: reg_exp A): reg_exp A   (** r1 r2 *)
| RE_Star (r: reg_exp A): reg_exp A      (** r * *)
.

Arguments RE_EmptyStr {A}.
Arguments RE_Single {A} (a).
Arguments RE_Union {A} (r1) (r2).
Arguments RE_App {A} (r1) (r2).
Arguments RE_Star {A} (r).

(** 我们可以将一个正则表达式的指称语义定义为其表示的字符串集合。下面是五种正则表达式对
    应的语义算子。*)

Definition empty_str_sem {A: Type}: list A -> Prop :=
  fun l => l = nil.

Definition single_sem {A: Type} (a: A): list A -> Prop :=
  fun l => l = a :: nil.

Definition union_sem {A: Type} (D1 D2: list A -> Prop): list A -> Prop :=
  D1 ∪ D2.

Definition app_sem {A: Type} (D1 D2: list A -> Prop): list A -> Prop :=
  fun l => exists l1 l2, l1 ∈ D1 /\ l2 ∈ D2 /\ l = l1 ++ l2.

(** NOTE power的语义是递归定义的，表示的是对于任意自然数n，D的n次幂的语义。*)
Fixpoint power_sem {A: Type} (D: list A -> Prop) (n: nat): list A -> Prop :=
  match n with
  | O => empty_str_sem
  | S n0 => app_sem D (power_sem D n0)
  end.

Definition star_sem {A: Type} (D: list A -> Prop): list A -> Prop :=
  ⋃ (power_sem D).

(** 据此，就可以递归定义正则表达式的指称语义以及行为等价。*)

Fixpoint eval_reg_expr {A: Type} (r: reg_exp A): list A -> Prop :=
  match r with
  | RE_EmptyStr => empty_str_sem
  | RE_Single a => single_sem a
  | RE_Union r1 r2 => union_sem (eval_reg_expr r1) (eval_reg_expr r2)
  | RE_App r1 r2 => app_sem (eval_reg_expr r1) (eval_reg_expr r2)
  | RE_Star r => star_sem (eval_reg_expr r)
  end.

Notation "⟦ r ⟧" := (eval_reg_expr r)
  (at level 0, r at level 99).

Definition requiv {A: Type} (r1 r2: reg_exp A): Prop :=
  ⟦ r1 ⟧ == ⟦ r2 ⟧.

Notation "r1 '~=~' r2" := (requiv r1 r2)
  (at level 69, no associativity).

(** 下面请你证明一些正则表达式的等价性质。*)

#[export] Instance requiv_equiv: forall {A: Type},
  Equivalence (@requiv A).
Proof. 
    intros A. 
    unfold requiv. 
    apply equiv_in_domain. 
    apply Sets_equiv_equiv. 
Qed.
    
    
Theorem RE_Union_comm: forall {A: Type} (r1 r2: reg_exp A),
  RE_Union r1 r2 ~=~ RE_Union r2 r1.
Proof.
    intros.
    unfold requiv.
    simpl.
    unfold union_sem.
    Sets_unfold.
    tauto.
Qed.

Lemma app_sem_id_l: forall {A: Type} (D: list A -> Prop),
  app_sem empty_str_sem D == D.
Proof.
    intros.
    unfold app_sem, empty_str_sem; Sets_unfold.
    intros l.
    split; intros H.
    - destruct H as [l1 [l2 [H1 [H2 H3] ] ] ].
      rewrite H1 in H3.
      rewrite app_nil_l in H3.
      rewrite H3.
        assumption.
    - exists nil, l.
      split.
      + simpl. reflexivity.
      + split.
        * assumption.
        * simpl. reflexivity.
Qed.


Theorem RE_App_id_l: forall {A: Type} (r: reg_exp A),
  RE_App RE_EmptyStr r ~=~ r.
Proof.
    intros.
    unfold requiv.
    simpl.
    rewrite app_sem_id_l.
    reflexivity.
Qed.

(**NOTE 附加题 *)

Lemma app_sem_assoc1: forall {A: Type} (D1 D2 D3: list A -> Prop),
  app_sem D1 (app_sem D2 D3) ⊆ app_sem (app_sem D1 D2) D3.
Proof.
    intros.
    unfold app_sem; Sets_unfold.
    intros l H.
    destruct H as [l1 [l23 [H1 [H2 H3] ] ] ].
    destruct H2 as [l2 [l3 [H21 [H22 H23] ] ] ].
    exists (l1 ++ l2), l3.
    split.
    - exists l1, l2.
      split.
        + assumption.
        + split.
          * assumption.
          * reflexivity.
    - split.
      + assumption.
      + rewrite H3.
      rewrite H23.
       rewrite app_assoc. reflexivity.
Qed.


Lemma app_sem_assoc2: forall {A: Type} (D1 D2 D3: list A -> Prop),
  app_sem (app_sem D1 D2) D3 ⊆ app_sem D1 (app_sem D2 D3).
Proof.
    intros.
    unfold app_sem; Sets_unfold.
    intros l H.
    destruct H as [l12 [l3 [H12 [H3 H] ] ] ].
    destruct H12 as [l1 [l2 [H1 [H2 H12] ] ] ].
    exists l1, (l2 ++ l3).
    split.
    - assumption.
    - split.
      + exists l2, l3.
        split.
        * assumption.
        * split.
          -- assumption.
          -- reflexivity.
        + rewrite H.
            rewrite H12.
            rewrite app_assoc. reflexivity.
Qed.    

  

Theorem RE_App_assoc: forall {A: Type} (r1 r2 r3: reg_exp A),
  RE_App r1 (RE_App r2 r3) ~=~ RE_App (RE_App r1 r2) r3.
Proof.
    intros.
    unfold requiv.
    simpl.
    split; apply app_sem_assoc1 || apply app_sem_assoc2.
Qed.


