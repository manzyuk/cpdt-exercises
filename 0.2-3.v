Require Import Arith Cpdt.CpdtTactics.
Set Implicit Arguments.

Inductive multiple (m : nat) : nat -> Prop :=
| MultipleO : multiple m 0
| MultipleS : forall n : nat, multiple m n -> multiple m (m + n).

Theorem thirteen_not_multiple_of_six_or_ten : ~(multiple 6 13 \/ multiple 10 13).
  unfold not. inversion 1.
  inversion H0. inversion H2. inversion H4.
  inversion H0. inversion H2.
Qed.

Definition odd (n : nat) : Prop := exists m : nat, n = S (m + m).

Definition is_zero (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Lemma O_neq_S : forall n : nat, O <> S n.
  unfold not. intros. change (is_zero (S n)). rewrite <- H. simpl. constructor.
Qed.

Lemma even_plus_odd : forall m n : nat, odd ((m + m) + n) -> odd n.
  induction m.
  simpl. trivial.
  destruct 1. apply IHm. unfold odd. exists (pred x). crush.
Qed.

Lemma multiple_of_even_not_odd : forall m n : nat, multiple (m + m) n -> ~(odd n).
  unfold not. intros m n. induction 1.
  intro. destruct H. apply (O_neq_S H).
  intro. apply IHmultiple. apply (even_plus_odd m n H0).
Qed.

Theorem multiple_of_six_or_ten_not_odd : forall n : nat,
    multiple 6 n \/ multiple 10 n -> ~(odd n).
  intros. destruct H.
  apply (multiple_of_even_not_odd 3). simpl. assumption.
  apply (multiple_of_even_not_odd 5). simpl. assumption.
Qed.
