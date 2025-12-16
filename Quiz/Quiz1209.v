Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List. Import ListNotations.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.Syntax.
Require Import PL.DenotationsOfExpr.
Require Import PL.DenotationsAsRels.
Require Import PL.Monad.
Require Import PL.Kleene.
Require Import PL.FixedPoint.
Require Import PL.MonadHoare.
Local Open Scope Z.
Local Open Scope list.

Import Monad
       MonadNotation
       SetMonadExamples0
       SetMonadExamples2
       SetMonadExamples3
       SetMonadHoare
       KleeneFix Sets_CPO.
Local Open Scope monad.

(************)
(** 习题：  *)
(************)

Definition insertion_body (x: Z):
  list Z * list Z -> SetMonad.M (ContinueOrBreak (list Z * list Z) (list Z)) :=
  fun '(l1, l2) =>
    match l2 with
    | nil => break (l1 ++ [x])
    | cons y l2' =>
        choice
          (assume (x <= y);; break (l1 ++ [x] ++ l2))
          (assume (y <= x);; continue (l1 ++ [y], l2'))
    end.

Definition insertion (x: Z) (l: list Z): SetMonad.M (list Z) :=
  repeat_break (insertion_body x) (nil, l).

Theorem insertion_perm:
  forall x l,
    Hoare
      (insertion x l)
      (fun l0 => Permutation (l ++ [x]) l0).
Proof. 
  intros.
  unfold insertion.
  apply (Hoare_repeat_break _ (fun '(l1, l2) => l = l1 ++ l2)). 
  - intros. 
    unfold insertion_body. 
    destruct a.
    destruct l1. 
    + apply Hoare_ret.
      rewrite H. 
      rewrite <- app_assoc.
      reflexivity.
    + apply Hoare_choice. 
      * apply Hoare_assume_bind. 
        intros. 
        apply Hoare_ret. 
        rewrite H.
        rewrite <- !app_assoc.
        apply Permutation_app.
        reflexivity.
        apply Permutation_app_comm.
      * apply Hoare_assume_bind. 
        intros. 
        apply Hoare_ret.
        subst. 
        rewrite <- app_assoc. 
        reflexivity. 
  - reflexivity.
Qed.

Lemma snoc_destruct: forall {A: Type} (l: list A),
  l = nil \/
  exists a l', l = l' ++ [a].
Proof.
  intros.
  revert l; apply rev_ind.
  + left; reflexivity.
  + intros.
    right.
    eauto.
Qed.

Lemma incr_app_inv1: forall l1 l2,
  incr (l1 ++ l2) ->
  incr l1.
Proof.
  intros.
  destruct (snoc_destruct l1).
  + subst; simpl; tauto.
  + destruct H0 as [? [? ?]]; subst.
    rewrite <-app_assoc in H. 
    apply incr_app_cons_inv1 in H.
    tauto.
Qed.

Lemma incr_app_inv2: forall l1 l2,
  incr (l1 ++ l2) ->
  incr l2.
Proof.
  intros.
  destruct l2.
  + subst; simpl; tauto.
  + apply incr_app_cons_inv2 in H.
    tauto.
Qed.

Theorem insertion_incr:
  forall x l,
    incr l ->
    Hoare
      (insertion x l)
      (fun l0 => incr l0).
Proof.
  intros.
  unfold insertion.
  apply (Hoare_repeat_break _ (fun '(l1, l2) => incr (l1 ++ [x]) /\ incr l2 /\ l = l1 ++ l2)). 
  - intros.
    unfold insertion_body.
    destruct a.
    destruct l1.
    + apply Hoare_ret. 
      tauto.
    + apply Hoare_choice. 
      * apply Hoare_assume_bind. 
        intros. 
        apply Hoare_ret.
        apply incr_app_cons; [tauto|]. 
        simpl; tauto.
      * apply Hoare_assume_bind. 
        intros. 
        apply Hoare_ret.
        destruct H0 as [? []]. 
        split; [|split]. 
        ** subst.
           rewrite <- app_assoc.
           apply incr_app_cons. 
           { apply incr_app_cons_inv1 in H; auto. }
           { simpl; tauto. } 
        ** subst. 
           replace (z :: l1) with ([z] ++ l1) in H2 
           by reflexivity.
           apply incr_app_inv2 in H2. 
           auto. 
        ** subst. 
           rewrite <- app_assoc. 
           reflexivity. 
  - split; [|split]. 
    ** simpl; tauto. 
    ** apply H. 
    ** reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

Definition ins_sort (l: list Z) :=
  list_iter insertion l nil.

Theorem ins_sort_perm:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l).
Proof.
  intros.
  unfold ins_sort.
  apply Hoare_list_iter; [|reflexivity].
  intros.
  eapply Hoare_conseq. 
  2:{ apply insertion_perm. }
  simpl; intros. 
  eapply Permutation_trans.
  2:{ apply H0. }
  apply Permutation_app;
  [apply H | reflexivity].
Qed.

Theorem ins_sort_incr:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => incr l).
Proof.
  intros.
  unfold ins_sort.
  apply Hoare_list_iter with (P:= fun _ l => incr l). 
  intros; apply insertion_incr; auto. 
  simpl; tauto.
Qed.

Theorem functional_correctness_ins_sort:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l /\ incr l).
Proof.
  intros.
  apply Hoare_conjunct.
  + apply ins_sort_perm.
  + apply ins_sort_incr.
Qed.

