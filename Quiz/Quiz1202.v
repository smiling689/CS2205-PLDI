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

(** 请证明下面程序的性质。*)

Definition body_count (n: Z) (x: Z): SetMonad.M (ContinueOrBreak Z Z) :=
  choice
    (assume (x < n);; continue (x + 1))
    (assume (~ (x < n));; break x).

Definition count (n: Z): SetMonad.M Z :=
  repeat_break (body_count n) 0.

Theorem functional_correctness_count:
  forall n,
    0 < n ->
    Hoare (count n) (fun x => x = n).
Proof. 
  intros. 
  unfold count. 
  apply (Hoare_repeat_break _ (fun x => x <= n)). 
  - intros. 
    unfold body_count. 
    apply Hoare_choice. 
    * apply Hoare_assume_bind. 
      intros. 
      apply Hoare_ret.
      lia. 
    * apply Hoare_assume_bind. 
      intros. 
      apply Hoare_ret.
      lia. 
  - lia.
Qed.


(************)
(** 习题：  *)
(************)

(** 请证明下面程序的性质。*)

Definition body_slow_div (n m: Z):
  Z * Z -> SetMonad.M (ContinueOrBreak (Z * Z) (Z * Z)) :=
  fun '(x, y) =>
    choice
      (assume (x < n);; break (x, y))
      (assume (~ (x < n));; continue (x - n, y + 1)).

Definition slow_div (n m: Z): SetMonad.M (Z * Z) :=
  repeat_break (body_slow_div n m) (m, 0).

Theorem functional_correctness_slow_div:
  forall n m,
    0 < n ->
    0 <= m ->
    Hoare (slow_div n m)
          (fun '(x, y) => x + n * y = m /\ 0 <= x < n).
Proof. 
  intros. 
  unfold slow_div. 
  apply (Hoare_repeat_break _ (fun '(x, y) => x + n * y = m /\ 0 <= x)). 
  - intros. 
    unfold body_slow_div. 
    destruct a as [x y].
    destruct H1. 
    apply Hoare_choice. 
    * apply Hoare_assume_bind. 
      intros. 
      apply Hoare_ret. 
      split; lia.
    * apply Hoare_assume_bind. 
      intros. 
      apply Hoare_ret. 
      split; lia.
  - split; lia.
Qed.

(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

