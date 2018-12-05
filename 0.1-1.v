Inductive truth : Set := Yes | No | Maybe.

Definition not (t : truth): truth :=
  match t with
  | Yes => No
  | No => Yes
  | Maybe => Maybe
  end.

Definition and (t1 : truth) (t2 : truth) : truth :=
  match t1 with
  | Yes => t2
  | No => No
  | Maybe =>
    match t2 with
    | Yes => Maybe
    | No => No
    | Maybe => Maybe
    end
  end.

Definition or (t1 : truth) (t2 : truth) : truth :=
  match t1 with
  | Yes => Yes
  | No => t2
  | Maybe =>
    match t2 with
    | Yes => Yes
    | No => Maybe
    | Maybe => Maybe
    end
  end.

Theorem and_commutative : forall t1 t2 : truth, and t1 t2 = and t2 t1.
  destruct t1; destruct t2; reflexivity.
Qed.

Theorem and_distributes_over_or : forall t1 t2 t3 : truth,
    and t1 (or t2 t3) = or (and t1 t2) (and t1 t3).
  destruct t1; destruct t2; destruct t3; reflexivity.
Qed.
