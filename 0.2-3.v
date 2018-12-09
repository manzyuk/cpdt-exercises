Require Import Arith Cpdt.CpdtTactics.

Inductive multiple_of_6 : nat -> Prop :=
| O_multiple_of_6 : multiple_of_6 0
| S6_multiple_of_6 : forall n, multiple_of_6 n -> multiple_of_6 (6 + n).

Inductive multiple_of_10 : nat -> Prop :=
| O_multiple_of_10 : multiple_of_10 0
| S10_multiple_of_10 : forall n, multiple_of_10 n -> multiple_of_10 (10 + n).

Inductive multiple_of_6_or_10 : nat -> Prop :=
| Multiple_of_6 : forall n, multiple_of_6 n -> multiple_of_6_or_10 n
| Multiple_of_10 : forall n, multiple_of_10 n -> multiple_of_6_or_10 n.

Theorem not_multiple_of_6_or_10_13 : ~(multiple_of_6_or_10 13).
  unfold not.
  inversion 1.
  inversion H0. inversion H3. inversion H5.
  inversion H0. inversion H3.
Qed.

Definition odd (n : nat) : Prop := exists m : nat, n = S (m + m).

Lemma even_plus_odd : forall m n : nat, odd ((m + m) + n) -> odd n.
  induction m.
  simpl. trivial.
  destruct 1. apply (IHm n). unfold odd. exists (pred x). crush.
Qed.

Lemma six_plus_odd : forall n : nat, odd (6 + n) -> odd n.
  intro. apply (even_plus_odd 3 n).
Qed.

Lemma ten_plus_odd : forall n : nat, odd (10 + n) -> odd n.
  intro. apply (even_plus_odd 5 n).
Qed.

Definition is_zero (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Lemma O_neq_S : forall n : nat, O <> S n.
  unfold not. intros. change (is_zero (S n)). rewrite <- H. simpl. constructor.
Qed.

Lemma multiple_of_6_not_odd : forall n : nat, multiple_of_6 n -> ~(odd n).
  unfold not. induction 1.
  intro. destruct H. apply (O_neq_S (x + x) H).
  intro. apply (IHmultiple_of_6 (six_plus_odd n H0)).
Qed.

Lemma multiple_of_10_not_odd : forall n : nat, multiple_of_10 n -> ~(odd n).
  unfold not. induction 1.
  intro. destruct H. apply (O_neq_S (x + x) H).
  intro. apply (IHmultiple_of_10 (ten_plus_odd n H0)).
Qed.

Theorem multiple_of_6_or_10_not_odd : forall n : nat,
    multiple_of_6_or_10 n -> ~(odd n).
  intros. destruct H.
  apply (multiple_of_6_not_odd n H).
  apply (multiple_of_10_not_odd n H).
Qed.
