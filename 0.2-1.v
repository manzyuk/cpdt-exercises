Theorem a : (True \/ False) /\ (False \/ True).
  split. left. constructor. right. constructor.
Qed.

Theorem b : forall (P : Prop), P -> ~~P.
  intros P proof. unfold not. intro contra. apply (contra proof).
Qed.

Theorem c : forall (P Q R : Prop), P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
  intros P Q R. destruct 1. destruct H0.
  left; split; assumption.
  right; split; assumption.
Qed.
