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
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 单子程序上的霍尔逻辑 *)

Module SetMonadHoare.
Import Monad
       MonadNotation
       SetMonadExamples0
       SetMonadExamples2
       SetMonadExamples3
       KleeneFix Sets_CPO.
Local Open Scope monad.


(** 集合单子上，霍尔三元组会退化为霍尔二元组。*)

Definition Hoare {A: Type} (c: SetMonad.M A) (P: A -> Prop): Prop :=
  forall a, a ∈ c -> P a.

(** 可以证明，各个单子算子满足下面性质。*)

Theorem Hoare_bind {A B: Type}:
  forall (f: SetMonad.M A)
         (g: A -> SetMonad.M B)
         (P: A -> Prop)
         (Q: B -> Prop),
    Hoare f P ->
    (forall a, P a -> Hoare (g a) Q) ->
    Hoare (bind f g) Q.
Proof.
  intros.
  unfold Hoare; sets_unfold;
  unfold bind, set_monad, SetMonad.bind.
  intros b [a [? ?]].
  specialize (H _ H1).
  specialize (H0 _ H _ H2).
  tauto.
Qed.

Theorem Hoare_ret {A: Type}:
  forall (a: A) (P: A -> Prop),
    P a -> Hoare (ret a) P.
Proof.
  intros.
  unfold Hoare, ret, set_monad, SetMonad.ret; sets_unfold.
  intros.
  rewrite <- H0; tauto.
Qed.

Theorem Hoare_conseq {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    (forall a, P a -> Q a) ->
    Hoare f P ->
    Hoare f Q.
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_conjunct {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    Hoare f P ->
    Hoare f Q ->
    Hoare f (fun a => P a /\ Q a).
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_choice {A: Type}:
  forall (f g: SetMonad.M A)
         (P: A -> Prop),
    Hoare f P ->
    Hoare g P ->
    Hoare (choice f g) P.
Proof.
  intros.
  unfold Hoare; sets_unfold; unfold choice; Sets_unfold.
  intros.
  destruct H1; [apply H | apply H0]; tauto.
Qed.

Theorem Hoare_assume_bind {A: Type}:
  forall (P: Prop)
         (f: SetMonad.M A)
         (Q: A -> Prop),
    (P -> Hoare f Q) ->
    (Hoare (assume P;; f) Q).
Proof.
  intros.
  apply (Hoare_bind _ _ (fun _ => P)).
  + unfold Hoare, assume; sets_unfold.
    tauto.
  + tauto.
Qed.

Lemma Hoare_Kleene_LFix {A B: Type}:
  forall (a: A)
         (Q: B -> Prop)
         (f: (A -> SetMonad.M B) -> (A -> SetMonad.M B)),
    (forall n, Hoare (Nat.iter n f ∅ a) Q) ->
    Hoare (Kleene_LFix f a) Q.
Proof.
  intros.
  unfold Hoare.
  intros b HFix.
  change (b ∈ (⋃ (fun n => Nat.iter n f ∅ a))) in HFix.
  change (exists n, b ∈ Nat.iter n f ∅ a) in HFix.
  destruct HFix as [n ?].
  unfold Hoare in H.
  pose proof H n b H0.
  tauto.
Qed.

Lemma Hoare_repeat_break_aux {A B: Type}:
  forall (body: A -> SetMonad.M (ContinueOrBreak A B))
         (P: A -> Prop)
         (Q: B -> Prop),
    (forall a, P a ->
               Hoare (body a) (fun x => match x with
                                        | by_continue a => P a
                                        | by_break b => Q b
                                        end)) ->
    (forall n a, P a ->
                 Hoare (Nat.iter n (repeat_break_f body) ∅ a) Q).
Proof.
  intros body P Q H n.
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold repeat_break_f at 1.
    eapply Hoare_bind.
    - apply H, H0.
    - intros [a0 | b0].
      * apply IHn.
      * apply Hoare_ret.
Qed.

Theorem Hoare_repeat_break {A B: Type}:
  forall (body: A -> SetMonad.M (ContinueOrBreak A B))
         (P: A -> Prop)
         (Q: B -> Prop),
    (forall a, P a ->
               Hoare (body a) (fun x => match x with
                                        | by_continue a => P a
                                        | by_break b => Q b
                                        end)) ->
    (forall a, P a -> Hoare (repeat_break body a) Q).
Proof.
  intros.
  change (Hoare (Kleene_LFix (repeat_break_f body) a) Q).
  apply Hoare_Kleene_LFix.
  intros.
  pose proof Hoare_repeat_break_aux body P Q H.
  pose proof H1 n a H0.
  tauto.
Qed.

(** * 霍尔逻辑证明 *)

(** ** 3x + 1 *)

Theorem functional_correctness_3x1:
  forall n: Z,
    n >= 1 ->
    Hoare (run_3x1 n) (fun m => m = 1).
Proof.
  apply Hoare_repeat_break.
  intros.
  unfold body_3x1.
  repeat apply Hoare_choice.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    lia.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    destruct H0 as [? ?].
    subst a.
    rewrite Z.mul_comm, Z_div_mult_full by lia.
    lia.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    lia.
Qed.

(** ** 二分查找 *)

Theorem functional_correctness_binary_search:
  forall (P: Z -> Prop) lo hi,
    (forall n m, n <= m -> P m -> P n) ->
    P lo ->
    ~ P hi ->
    Hoare (binary_search P lo hi)
          (fun x => P x /\ ~ P (x + 1)).
Proof.
  intros.
  apply (Hoare_repeat_break _
           (fun '(lo, hi) => P lo /\ ~ P hi)); [| tauto].
  clear lo hi H0 H1.
  intros [lo hi] [? ?].
  unfold body_binary_search.
  apply Hoare_choice.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_ret.
    subst hi; tauto.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_choice; apply Hoare_assume_bind; intros.
    - apply Hoare_ret.
      tauto.
    - apply Hoare_ret.
      tauto.
Qed.

(** ** 归并 *)

Local Close Scope sets.
Local Open Scope list.

Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ incr_aux l0 y
  end.

Definition incr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => incr_aux l0 x
  end.

Lemma incr_app_cons: forall l1 x l2,
  incr (l1 ++ [x]) ->
  incr (x :: l2) ->
  incr (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv1: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv2: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.

Theorem merge_perm:
  forall l1 l2,
    Hoare (merge l1 l2) (Permutation (l1 ++ l2)).
Proof.
  intros.
  unfold merge.
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') =>
              Permutation (l1 ++ l2) (l1' ++ l2' ++ l3'))).
  2: {
    rewrite app_nil_r.
    reflexivity.
  }
  intros [[l1' l2'] l3'] ?.
  unfold body_merge.
  destruct l1' as [ | x l1']; [| destruct l2' as [| y l2']].
  + apply Hoare_ret.
    rewrite H; simpl.
    apply Permutation_app_comm.x
  + apply Hoare_ret.
    rewrite H.
    rewrite Permutation_app_comm.
    reflexivity.
  + apply Hoare_choice; apply Hoare_assume_bind; intros.
    - apply Hoare_ret.
      rewrite H.
      rewrite ! app_assoc.
      rewrite (Permutation_app_comm _ [x]).
      reflexivity.
    - apply Hoare_ret.
      rewrite H.
      apply Permutation_app; [reflexivity |].
      rewrite ! app_assoc.
      rewrite (Permutation_app_comm _ [y]).
      reflexivity.
Qed.

Theorem merge_incr:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (merge l1 l2) incr.
Proof.
  intros.
  unfold merge.
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') => 
              incr (l3' ++ l1') /\
              incr (l3' ++ l2'))).
  2: {
    tauto.
  }
  clear l1 l2 H H0.
  intros [[l1 l2] l3] [? ?].
  destruct l1 as [ | x l1]; [| destruct l2 as [| y l2]].
  + apply Hoare_ret; tauto.
  + apply Hoare_ret; tauto.
  + apply Hoare_choice; apply Hoare_assume_bind; intros.
    - apply Hoare_ret.
      split.
      * rewrite <- app_assoc.
        exact H.
      * rewrite <- app_assoc.
        simpl.
        apply incr_app_cons_inv1 in H.
        apply incr_app_cons_inv2 in H0.
        apply incr_app_cons; simpl in *; tauto.
    - apply Hoare_ret.
      split.
      * rewrite <- app_assoc.
        simpl.
        apply incr_app_cons_inv1 in H0.
        apply incr_app_cons_inv2 in H.
        apply incr_app_cons; simpl in *; tauto.
      * rewrite <- app_assoc.
        exact H0.
Qed.

Theorem functional_correctness_merge:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (merge l1 l2)
          (fun l3 => Permutation (l1 ++ l2) l3 /\ incr l3).
Proof.
  intros.
  apply Hoare_conjunct.
  + apply merge_perm.
  + apply merge_incr; tauto.
Qed.

(** ** 拓展欧几里得 *)

Local Close Scope list.
Local Open Scope sets.

Definition any (A: Type): SetMonad.M A := Sets.full.

Definition body_ext_euclid
             (W: Z -> Z -> SetMonad.M (Z * Z))
             (a b: Z): SetMonad.M (Z * Z) :=
  choice
    (assume (b = 0);; 
     choice
       (assume (a >= 0);; ret (1, 0))
       (assume (a <= 0);; ret (-1, 0)))
    (assume (b <> 0);;
     q <- any Z;;
     r <- any Z;;
     assume (a = r + q * b);;
     '(x, y) <- W b r;;
     ret (y, x - q * y)).

Definition ext_euclid (a b: Z): SetMonad.M (Z * Z) :=
  Kleene_LFix body_ext_euclid a b.


Lemma Hoare_Kleene_LFix2 {A1 A2 B: Type}:
  forall (a1: A1) (a2: A2)
         (Q: B -> Prop)
         (f: (A1 -> A2 -> SetMonad.M B) ->
             (A1 -> A2 -> SetMonad.M B)),
    (forall n, Hoare (Nat.iter n f ∅ a1 a2) Q) ->
    Hoare (Kleene_LFix f a1 a2) Q.
Proof.
  intros.
  unfold Hoare.
  intros b HFix.
  change (b ∈ (⋃ (fun n => Nat.iter n f ∅ a1 a2))) in HFix.
  change (exists n, b ∈ Nat.iter n f ∅ a1 a2) in HFix.
  destruct HFix as [n ?].
  unfold Hoare in H.
  pose proof H n b H0.
  tauto.
Qed.

Theorem Hoare_any_bind {A B: Type}:
  forall (f: A -> SetMonad.M B) (Q: B -> Prop),
    (forall a, Hoare (f a) Q) ->
    Hoare (bind (any A) f) Q.
Proof.
  intros.
  apply (Hoare_bind _ _ (fun _ => True)).
  + unfold Hoare, any.
    intros. tauto.
  + intros.
    apply H.
Qed.

Lemma functional_correctness_ext_euclid_aux:
  forall W,
    (forall a b, Hoare
                   (W a b)
                   (fun '(x, y) => a * x + b * y = Z.gcd a b)) ->
    (forall a b, Hoare
                   (body_ext_euclid W a b)
                   (fun '(x, y) => a * x + b * y = Z.gcd a b)).
Proof.
  intros.
  unfold body_ext_euclid.
  apply Hoare_choice.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_choice.
    - apply Hoare_assume_bind.
      intros.
      apply Hoare_ret.
      rewrite H0.
      rewrite Z.gcd_0_r.
      lia.
    - apply Hoare_assume_bind.
      intros.
      apply Hoare_ret.
      rewrite H0.
      rewrite Z.gcd_0_r.
      lia.
  + apply Hoare_assume_bind.
    intros.
    apply Hoare_any_bind.
    intros q.
    apply Hoare_any_bind.
    intros r.
    apply Hoare_assume_bind.
    intros.
    eapply Hoare_bind.
    1: { apply H. }
    intros [y x] ?.
    apply Hoare_ret.
    pose proof Z.gcd_comm a b.
    pose proof Z.gcd_add_mult_diag_r b r q.
    rewrite <- H1 in H4.
    nia.
Qed.

Theorem functional_correctness_ext_euclid:
  forall a b,
    Hoare (ext_euclid a b)
          (fun '(x, y) => a * x + b * y = Z.gcd a b).
Proof.
  intros.
  revert a b.
  unfold ext_euclid.
  intros.
  apply Hoare_Kleene_LFix2.
  intros n.
  revert a b.
  induction n; simpl; intros.
  + unfold Hoare; sets_unfold; intros; tauto.
  + apply functional_correctness_ext_euclid_aux.
    apply IHn.
Qed.

(** ** 归并排序 *)

Local Open Scope list.

Definition ext_sort (l: list Z): SetMonad.M (list Z) :=
  fun l' => Permutation l l' /\ incr l'.

Definition ext_split (l: list Z): SetMonad.M (list Z * list Z) :=
  fun '(l0, l1) => Permutation l (l0 ++ l1).

Definition gmergesort_f (W: list Z -> SetMonad.M (list Z)):
  list Z -> SetMonad.M (list Z) :=
  fun x => 
    choice
      (ext_sort x)
      (assume(length x >= 2)%nat;;
       '(p1, q1) <- ext_split x ;; 
       p2 <- W (p1) ;; 
       q2 <- W (q1) ;; 
       merge p2 q2).

Definition gmergesort := Kleene_LFix gmergesort_f.
Lemma ext_sort_fact:
  forall l,
    Hoare (ext_sort l) (fun l0 => Permutation l l0 /\ incr l0).
Proof.
  unfold Hoare, ext_sort; sets_unfold.
  intros.
  tauto.
Qed.

Lemma ext_split_fact:
  forall l,
    Hoare (ext_split l) (fun '(l1, l2) => Permutation l (l1 ++ l2)).
Proof.
  unfold Hoare, ext_split; sets_unfold.
  intros.
  tauto.
Qed.

Theorem functional_correctness_mergesort:
  forall l,
    Hoare (gmergesort l) (fun l0 => Permutation l l0 /\ incr l0).
Proof.
  intros.
  unfold Hoare, gmergesort, Kleene_LFix; unfold_CPO_defs.
  intros.
  destruct H as [n ?].
  revert l a H.
  change (forall l,
          Hoare (Nat.iter n gmergesort_f ∅ l)
                (fun l0 => Permutation l l0 /\ incr l0)).
  induction n; simpl; intros.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold gmergesort_f at 1.
    apply Hoare_choice; [apply ext_sort_fact |].
    apply Hoare_assume_bind.
    intros.
    eapply Hoare_bind; [apply ext_split_fact |].
    intros [l1 l2] ?.
    eapply Hoare_bind; [apply IHn |].
    intros l1' [? ?].
    eapply Hoare_bind; [apply IHn |].
    intros l2' [? ?].
    eapply Hoare_conseq; [| apply functional_correctness_merge; tauto].
    intros l3 [? ?].
    rewrite <- H5 at 1.
    rewrite <- H1, <- H3.
    tauto.
Qed.

Arguments bind: simpl never.
Arguments ret: simpl never.

Fixpoint list_iter
           {A B: Type}
           (f: A -> B -> SetMonad.M B)
           (l: list A)
           (b: B):
  SetMonad.M B :=
  match l with
  | nil => ret b
  | a :: l0 => b0 <- f a b;; list_iter f l0 b0
  end.

Lemma Hoare_list_iter_aux {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall l2 b l1,
       P l1 b ->
       Hoare (list_iter f l2 b) (fun b0 => P (l1 ++ l2) b0)).
Proof.
  intros f P H l2.
  induction l2; intros; simpl.
  + apply Hoare_ret.
    rewrite app_nil_r.
    tauto.
  + apply (Hoare_bind _ _ (fun b0 : B => P (l1 ++ [a]) b0)).
    - apply H.
      apply H0.
    - intros b0 H1.
      pose proof IHl2 b0 (l1 ++ [a]) H1.
      rewrite <- app_assoc in H2.
      simpl in H2.
      apply H2.
Qed.

Theorem Hoare_list_iter {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall b l, P nil b -> Hoare (list_iter f l b) (fun b0 => P l b0)).
Proof.
  intros.
  pose proof Hoare_list_iter_aux f P H l b nil.
  tauto.
Qed.


End SetMonadHoare.
