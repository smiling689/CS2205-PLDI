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
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.


Module SetMonadHoare.
Import Monad
       MonadNotation
       SetMonadExamples0
       SetMonadExamples2
       SetMonadExamples3
       KleeneFix Sets_CPO.
Local Open Scope monad.

Definition d1 (x: Z): SetMonad.M (ContinueOrBreak Z Z) :=
  choice
    (assume (x >= 1);; continue (x- 1))
    (assume (x = 0);; break x).

Ltac unfold_d1 := unfold repeat_break_f, d1 in *.
Ltac unfold_monad := unfold bind, choice, assume, continue, break, ret, set_monad, SetMonad.bind, SetMonad.ret in *.

Lemma Hoare_d1_step1:
  repeat_break_f d1 (fun _ => ∅) ==
  (fun x => if x =? 0 
            then [0]%sets 
            else ∅).
Proof.
    split; unfold_d1; unfold_monad; intros. 
    - sets_unfold in H. 
      destruct H as [x0 [H_d1 H_match]].
      destruct H_d1 as [H_continue | H_break].
      + destruct H_continue as [_ [H_ge H_val]].
        subst x0.
        contradiction.
      + destruct H_break as [_ [H_eq H_val]].
        subst.
        rewrite Z.eqb_refl. 
        reflexivity. 
    - destruct (Z.eq_dec a 0) as [H_a_eq | H_a_neq].
      + subst a.
        rewrite Z.eqb_refl in H; sets_unfold in H; subst.
        exists (by_break 0); split; [right|reflexivity]; simpl.
        exists tt; split; reflexivity. 
      + rewrite <- Z.eqb_neq in H_a_neq.
        rewrite H_a_neq in H; sets_unfold in H; contradiction.
Qed.

#[export] Instance repeat_break_f_d1_Proper:
  Proper (Sets.equiv ==> Sets.equiv) (repeat_break_f d1).
Proof.
    unfold Proper, respectful; intros; split; 
    unfold_d1; unfold_monad; intros;
    destruct H0 as [x0 [H_d1 H_match]];
    exists x0; split; auto; 
    destruct x0; auto; 
    apply H; auto.
Qed.

Lemma Hoare_d1_step2:
  repeat_break_f d1 (repeat_break_f d1 (fun _ => ∅)) ==
  (fun x => if ((x =? 0) || (x =? 1))%bool
            then [0]%sets 
            else ∅).
Proof.
    rewrite Hoare_d1_step1. 
    split; unfold_d1; unfold_monad; intros. 
    - sets_unfold in H. 
      destruct H as [x0 [H_d1 H_match]].
      destruct H_d1 as [H_continue | H_break].
      + destruct H_continue as [_ [H_ge H_val]].
      subst x0.
      destruct (Z.eqb_spec (a - 1) 0). 
      * assert (a = 1) by lia; subst. 
        reflexivity.
      * contradiction. 
    + destruct H_break as [_ [H_eq H_val]].
      subst.
      rewrite Z.eqb_refl. 
      reflexivity.
    - destruct (Z.eq_dec a 0) as [H_a_eq | H_a_neq].
      + subst a.
        rewrite Z.eqb_refl in H; sets_unfold in H; simpl in H; subst.
        exists (by_break 0); split; [right|reflexivity]; simpl.
        exists tt; split; reflexivity. 
      + destruct (Z.eqb_spec a 1). 
        * rewrite <- Z.eqb_neq in H_a_neq. 
          rewrite H_a_neq in H; sets_unfold in H; simpl in H. 
          subst.
          exists (by_continue 0); split; [left|reflexivity]; simpl.
          exists tt; split; [sets_unfold; lia|reflexivity]. 
        * rewrite <- Z.eqb_neq in H_a_neq. 
          rewrite H_a_neq in H; sets_unfold in H; simpl in H. 
          contradiction.
Qed.

Lemma Hoare_d1_step3:
  repeat_break_f d1 (repeat_break_f d1 (repeat_break_f d1 (fun _ => ∅))) ==
  (fun x => if ((x =? 0) || (x =? 1) || (x =? 2))%bool
            then [0]%sets 
            else ∅).
Proof.
    rewrite Hoare_d1_step2. 
    split; unfold_d1; unfold_monad; intros.
    - sets_unfold in H. 
      destruct H as [x0 [H_d1 H_match]].
      destruct H_d1 as [H_continue | H_break].
      + destruct H_continue as [_ [H_ge H_val]].
        subst x0.
        destruct ((a - 1 =? 0) || (a - 1 =? 1))%bool eqn:E.
        * apply Bool.orb_prop in E. destruct E as [E|E]; apply Z.eqb_eq in E; subst. 
          { assert (a = 1) by lia; subst. reflexivity. }
          { assert (a = 2) by lia; subst. reflexivity. }
        * contradiction. 
      + destruct H_break as [_ [H_eq H_val]].
        subst.
        reflexivity.
    - destruct ((a =? 0) || (a =? 1) || (a =? 2))%bool eqn:E.
      + sets_unfold in H; subst.
        apply Bool.orb_prop in E; destruct E as [E|E]; 
        [apply Bool.orb_prop in E; destruct E as [E|E] |]; 
        apply Z.eqb_eq in E; subst. 
        * sets_unfold. 
          exists (by_break 0).
          split; [right; split; [|split]; reflexivity |reflexivity]. 
        * sets_unfold. 
          exists (by_continue 0).
          split; [left; split; [|split]; try lia; reflexivity | reflexivity]. 
        * sets_unfold. 
          exists (by_continue 1).
          split; [left; split; [|split]; try lia; reflexivity | reflexivity].
      + contradiction. 
Qed.

Lemma Hoare_d1_final:
  repeat_break d1 ==
  (fun x => if x >=? 0
            then [0]%sets 
            else ∅).
Proof.
  intros a.
  apply Sets_equiv_Sets_included; split; intros y H.

  - unfold repeat_break, Kleene_LFix, omega_lub, oLub_sets in H.
    sets_unfold in H. destruct H as [n H].
    revert a y H.
    induction n; intros.
    + simpl in H; contradiction.
    + simpl in H.
      unfold_d1. unfold_monad.
      sets_unfold in H.
      destruct H as [x0 [[H_cont | H_break] H_match]].
      * destruct H_cont as [_ [H_ge H_val]]; subst x0.
        simpl in H_match.
        specialize (IHn (a - 1) y H_match).
        destruct (a - 1 >=? 0) eqn:H_cond; [| contradiction].
        sets_unfold in IHn; subst y.
        rewrite Z.ge_le_iff in *.
        replace (a >=? 0) with true; [reflexivity |].
        symmetry; apply Z.geb_le; lia.
      * destruct H_break as [_ [H_eq H_val]]; subst x0.
        simpl in H_match; subst.
        simpl; reflexivity.
  - destruct (a >=? 0) eqn:H_ge.
    + sets_unfold in H; subst.
      apply Z.geb_le in H_ge.
      unfold repeat_break, Kleene_LFix, omega_lub, oLub_sets.
      sets_unfold.
      exists (S (Z.to_nat a)).
      remember (Z.to_nat a) as n.
      revert a H_ge Heqn.
      induction n; intros.
      * assert (a = 0) by lia; subst.
        apply Hoare_d1_step1.
        reflexivity. 
      * remember (S n) as m; simpl.  
        exists (by_continue (a - 1)).
        split.
        { unfold_d1; unfold_monad; left; exists tt; split; 
        [sets_unfold; lia|reflexivity].  }
        { apply IHn; lia. }
    + contradiction.
Qed.


End SetMonadHoare.
