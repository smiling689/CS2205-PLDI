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

(** * 状态关系单子程序 *)

Module StateRelMonad.
Import Monad SetMonadExamples3
       MonadNotation
       KleeneFix Sets_CPO.
Local Open Scope monad.


(** 下面用StateRelMonad表示带有程序状态的非确定性计算。*)

Module StateRelMonad.

Definition M (Σ A: Type): Type :=
  Σ -> A -> Σ -> Prop.

Definition bind (Σ A B: Type) (f: M Σ A) (g: A -> M Σ B): M Σ B :=
  fun (s1: Σ) (b: B) (s3: Σ) =>
    exists (a: A) (s2: Σ),
      (s1, a, s2) ∈ f /\ (s2, b, s3) ∈ g a.

Definition ret (Σ A: Type) (a0: A): M Σ A :=
  fun (s1: Σ) (a: A) (s2: Σ) => a = a0 /\ s1 = s2.

End StateRelMonad.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := StateRelMonad.bind Σ;
  ret := StateRelMonad.ret Σ;
|}.


(** 以下可以再定义一些额外的算子。*)

Definition assume {Σ: Type} (P: Σ -> Prop): StateRelMonad.M Σ unit :=
  fun s1 _ s2 => P s1 /\ s1 = s2.

Definition choice {Σ A: Type} (f g: StateRelMonad.M Σ A): StateRelMonad.M Σ A :=
  f ∪ g.

Definition any {Σ: Type} (A: Type): StateRelMonad.M Σ A :=
  fun s1 _ s2 => s1 = s2.

Definition repeat_break_f
             {Σ A B: Type}
             (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B))
             (W: A -> StateRelMonad.M Σ B)
             (a: A): StateRelMonad.M Σ B :=
  x <- body a;;
  match x with
  | by_continue a' => W a'
  | by_break b => ret b
  end.

Definition repeat_break
             {Σ A B: Type}
             (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B)):
  A -> StateRelMonad.M Σ B :=
  Kleene_LFix (repeat_break_f body).

Definition continue {Σ A B: Type} (a: A):
  StateRelMonad.M Σ (ContinueOrBreak A B) :=
  ret (by_continue a).

Definition break {Σ A B: Type} (b: B):
  StateRelMonad.M Σ (ContinueOrBreak A B) :=
  ret (by_break b).

(** * 霍尔逻辑 *)


(** 在StateRelMonad上的霍尔逻辑是一个关于霍尔三元组的逻辑。*)

Definition Hoare {Σ A: Type}
                 (P: Σ -> Prop)
                 (c: StateRelMonad.M Σ A)
                 (Q: A -> Σ -> Prop): Prop :=
  forall s1 a s2, P s1 -> (s1, a, s2) ∈ c -> Q a s2.

Theorem Hoare_bind {Σ A B: Type}:
  forall (P: Σ -> Prop)
         (f: StateRelMonad.M Σ A)
         (Q: A -> Σ -> Prop)
         (g: A -> StateRelMonad.M Σ B)
         (R: B -> Σ -> Prop),
  Hoare P f Q ->
  (forall a, Hoare (Q a) (g a) R) ->
  Hoare P (bind f g) R.
Proof.
  intros.
  unfold Hoare, bind; simpl; sets_unfold; unfold StateRelMonad.bind.
  intros s1 b s3 ? [a [s2 [? ?]]].
  pose proof H _ _ _ H1 H2.
  pose proof H0 a _ _ _ H4 H3.
  tauto.
Qed.

Theorem Hoare_ret {Σ A: Type}:
  forall (P: A -> Σ -> Prop) (a0: A),
    Hoare (P a0) (ret a0) P.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H0; subst; tauto.
Qed.

Theorem Hoare_choice {Σ A: Type}:
  forall P (f g: StateRelMonad.M Σ A) Q,
    Hoare P f Q -> 
    Hoare P g Q ->
    Hoare P (choice f g) Q.
Proof.
  intros.
  unfold Hoare, choice; sets_unfold.
  intros ? ? ? ? [? | ?].
  + pose proof H _ _ _ H1 H2.
    tauto.
  + pose proof H0 _ _ _ H1 H2.
    tauto.
Qed.

Theorem Hoare_assume_bind {Σ A: Type}:
  forall P (Q: Σ -> Prop) (f: StateRelMonad.M Σ A) R,
    Hoare (fun s => Q s /\ P s) f R -> 
    Hoare P (assume Q;; f) R.
Proof.
  intros.
  eapply Hoare_bind; [| intros; apply H].
  unfold Hoare, assume; sets_unfold.
  intros s1 _ s2 ? [? ?].
  subst; tauto.
Qed.

Theorem Hoare_any_bind {Σ A B: Type}:
  forall P Q (f: A -> StateRelMonad.M Σ B),
    (forall a, Hoare P (f a) Q) ->
    (Hoare P (bind (any A) f) Q).
Proof.
  intros.
  apply (Hoare_bind _ _ (fun _ => P)).
  + unfold Hoare, any; sets_unfold.
    intros.
    subst; tauto.
  + apply H.
Qed.

Theorem Hoare_conseq {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P2 f Q2 ->
    Hoare P1 f Q1.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply H0.
  apply (H1 s1 a s2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_pre {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    Hoare P2 f Q ->
    Hoare P1 f Q.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply (H0 s1 a s2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_post {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    (forall b s, Q2 b s -> Q1 b s) ->
    Hoare P f Q2 ->
    Hoare P f Q1.
Proof.
  intros.
  unfold Hoare.
  intros.
  apply H.
  apply (H0 s1 a s2); tauto.
Qed.

Theorem Hoare_conj {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q1 Q2: A -> Σ -> Prop),
    Hoare P f Q1 ->
    Hoare P f Q2 ->
    Hoare P f (fun a s => Q1 a s /\ Q2 a s).
Proof.
  intros.
  unfold Hoare; intros.
  split.
  + apply (H _ _ _ H1 H2).
  + apply (H0 _ _ _ H1 H2).
Qed.  

Theorem Hoare_forall {Σ A: Type}:
  forall (X: Type) (P: Σ -> Prop) f (Q: X -> A -> Σ -> Prop),
    (forall x, Hoare P f (Q x)) ->
    Hoare P f (fun a s => forall x, Q x a s).
Proof.
  intros.
  unfold Hoare.
  intros.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall x, Hoare (P x) f Q) ->
    Hoare (fun s => exists x, P x s) f Q.
Proof.
  intros.
  unfold Hoare.
  intros s1 a s2 [x ?] ?.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_ret' {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a0: A),
    (forall s, P s -> Q a0 s) ->
    Hoare P (ret a0) Q.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H1; subst.
  apply H. tauto.
Qed.

Theorem Hoare_repeat_break {Σ A B: Type}:
  forall (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B))
         (P: A -> Σ -> Prop)
         (Q: B -> Σ -> Prop),
    (forall a, Hoare (P a) (body a) (fun x s => match x with
                                                | by_continue a => P a s
                                                | by_break b => Q b s
                                                end)) ->
    (forall a, Hoare (P a) (repeat_break body a) Q).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold repeat_break, Kleene_LFix; unfold_CPO_defs.
  intros [n ?].
  revert a s1 b s2 H0 H1.
  change (forall a, Hoare (P a) (Nat.iter n (repeat_break_f body) ∅ a) Q).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold repeat_break_f at 1.
    eapply Hoare_bind.
    - apply H.
    - intros [a0 | b0].
      * apply IHn.
      * apply Hoare_ret.
Qed.

(** * 定义有向图和图上的程序 *)

(** 可以如下定义有向图。*)

Record PreGraph (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex
}.

Notation "pg '.(vvalid)'" := (vvalid _ _ pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).

(** 基于此就能定义“从x点经过一条边可以到达y点”。*)

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y.

(** 进一步，单步可达关系的自反传递闭包就是多步可达关系。*)

Definition reachable {V E: Type} (pg: PreGraph V E) :=
  clos_refl_trans (step pg).


(** 自反传递闭包_[clos_refl_trans]_是SetsClass库提供的定义。*)


End StateRelMonad.
