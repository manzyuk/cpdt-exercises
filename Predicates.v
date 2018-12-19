Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Print unit.

Print True.

(* Propositional Logic *)

Section Propositional.
  Variables P Q R : Prop.

  Theorem obvious : True.
    apply I.
  Qed.

  Theorem obvious' : True.
    constructor.
  Qed.

  Theorem False_imp : False -> 2 + 2 = 5.
    destruct 1.
  Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro.
    elimtype False.
    crush.
  Qed.

  Print not.

  Theorem arith_neq' : ~ (2 + 2 = 5).
    unfold not.
    crush.
  Qed.

  Print and.

  Theorem and_comm : P /\ Q -> Q /\ P.
    destruct 1.
    split.
    assumption.
    assumption.
  Qed.

  Print or.

  Theorem or_comm : P \/ Q -> Q \/ P.
    destruct 1.
    right; assumption.
    left; assumption.
  Qed.

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
      length ls1 = length ls2 \/ length ls1 + length ls2 = 6
      -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.
    crush.
  Qed.
End Propositional.

(* First Order Logic *)

Print ex.

Theorem exist1 : exists x : nat, x + 1 = 2.
  exists 1.
  reflexivity.
Qed.

Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
  destruct 1.
  crush.
Qed.

(* Predicates with Implicit Equality *)

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

Print eq.

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
  destruct 1.
  crush.
Qed.

Theorem isZero_contra : isZero 1 -> False.
  inversion 1.
Qed.

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  destruct 1.
Abort.

Check isZero_ind.

(* Recursive Predicates *)

Inductive even : nat -> Prop :=
| EvenO : even 0
| EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0 : even 0.
  constructor.
Qed.

Theorem even_4 : even 4.
  constructor; constructor; constructor.
Qed.

Hint Constructors even.

Theorem even_4' : even 4.
  auto.
Qed.

Theorem even_1_contra : even 1 -> False.
  inversion 1.
Qed.

Theorem even_3_contra : even 3 -> False.
  inversion 1.
  inversion H1.
Qed.

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
  induction 1; crush.
Qed.

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush.
  match goal with
  | [H : S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
  end; crush.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra'; eauto.
Qed.

Lemma even_contra'' : forall n' n, even n' -> n' = S (n + n) -> False.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush.
  match goal with
  | [H : S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
  end; crush.
Abort.
