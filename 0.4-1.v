Require Import Bool Arith List Cpdt.CpdtTactics.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Definition compare : forall n m : nat, {n <= m} + {n > m}.
  refine (fix f (n m : nat) : {n <= m} + {n > m} :=
            match n, m with
            | O, _ => Yes
            | _, O => No
            | S n', S m' => Reduce (f n' m')
            end); crush.
Defined.
