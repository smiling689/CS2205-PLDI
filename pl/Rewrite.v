Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.SimpleProofsAndDefs.
Require Import PL.HighOrder.
Local Open Scope Z.


(** 在先前证明单调函数性质的过程中，我们经常会要通过参数之间的大小关系推导出函数值之间
    的大小关系。例如，当_[f]_是一个单调函数时，可以由_[x <= y]_推出_[f x <= f y]_。
    对于一般的函数，我们也可以由参数相等，推出函数值相等，即由_[x = y]_推出
    _[f x = f y]_。下面的证明中就要用到这一性质。
*)

Definition is_fixpoint (f: Z -> Z) (x: Z): Prop :=
  f x = x.

Theorem fixpoint_self_comp: forall f x,
  is_fixpoint f x ->
  is_fixpoint (Zcomp f f) x.
Proof.
  unfold is_fixpoint, Zcomp.
  intros.
  (** 此时需要利用前提_[H: f x = x]_证明_[f (f x) = x]_。*)
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

(** 在数学上，如果_[f x = x]_，那么我们就称_[x]_是函数_[f]_的一个不动点。上面的定理证
    明了，如果_[x]_是_[f]_的不动点，那么_[x]_也是_[f]_与自身复合结果的不动点。在这一
    证明中，前提_[H]_是命题_[f x = x]_。证明指令_[rewrite H]_的效果是将结论中的
    _[f x]_替换为_[x]_，因此，第一次使用该指令后，原先需要证明的_[f (f x) = x]_规约
    为了_[f x = x]_。这一步背后的证明实际就用到了“只要函数_[f]_的参数不变，那么函数值
    也不变”这条性质。

    下面关于不动点简单性质的证明需要我们灵活使用rewrite指令。*)

Example fixpoint_self_comp23: forall f x,
  is_fixpoint (Zcomp f f) x ->
  is_fixpoint (Zcomp f (Zcomp f f)) x ->
  is_fixpoint f x.
Proof.
  unfold is_fixpoint, Zcomp.
  intros.
  rewrite H in H0.
  rewrite H0.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面关于结合律的性质。*)

Definition power2 (f: Z -> Z -> Z) (x: Z): Z :=
  f x x.

Definition power4 (f: Z -> Z -> Z) (x: Z): Z :=
  f x (f x (f x x)).

Fact power2_power2: forall f a,
  assoc f ->
  power2 f (power2 f a) = power4 f a.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面关于群的性质。提示：_[f x (g x) = f 1 (f x (g x))]_而
    _[f (g (g x)) (g x) = 1]_。*)

Fact group_basic: forall (f: Z -> Z -> Z) (g: Z -> Z),
  assoc f ->
  (forall x, f 1 x = x) ->
  (forall x, f (g x) x = 1) ->
  (forall x, f x (g x) = 1).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


