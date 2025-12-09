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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem insertion_incr:
  forall x l,
    incr l ->
    Hoare
      (insertion x l)
      (fun l0 => incr l0).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem ins_sort_incr:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => incr l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

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

