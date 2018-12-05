Require Import List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive slist (T : Type) : Type :=
| Nil : slist T
| Singleton : T -> slist T
| Append : slist T -> slist T -> slist T.

Fixpoint flatten T (sl : slist T) : list T :=
  match sl with
  | Nil => nil
  | Singleton x => x :: nil
  | Append sl1 sl2 => app (flatten sl1) (flatten sl2)
  end.

Definition slist_app T (sl1 : slist T) (sl2 : slist T) : slist T :=
  Append sl1 sl2.

Theorem flatten_distributes_over_app : forall T (sl1 sl2 : slist T),
    flatten (slist_app sl1 sl2) = app (flatten sl1) (flatten sl2).
  crush.
Qed.

Fixpoint flatten_acc T (sl : slist T) (acc : list T) : list T :=
  match sl with
  | Nil => acc
  | Singleton x => x :: acc
  | Append sl1 sl2 => flatten_acc sl1 (flatten_acc sl2 acc)
  end.

Lemma flatten_acc_correct : forall T (sl : slist T) (acc : list T),
    flatten_acc sl acc = app (flatten sl) acc.
  induction sl; crush.
Qed.

Definition flatten' T (sl : slist T) : list T :=
  flatten_acc sl nil.

Theorem flatten'_equals_flatten : forall T (sl : slist T),
    flatten' sl = flatten sl.
  intros.
  rewrite (app_nil_end (flatten sl)).
  rewrite <- flatten_acc_correct.
  trivial.
Qed.
