Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Definition var := nat.

Inductive prop : Set :=
| Var : var -> prop
| Neg : prop -> prop
| Conj : prop -> prop -> prop
| Disj : prop -> prop -> prop.

Fixpoint propDenote (truth : var -> bool) (p : prop) : Prop :=
  match p with
  | Var v => if truth v then True else False
  | Neg p' => ~ propDenote truth p'
  | Conj p1 p2 => propDenote truth p1 /\ propDenote truth p2
  | Disj p1 p2 => propDenote truth p1 \/ propDenote truth p2
  end.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).

Definition bool_true_dec : forall b, {b = true} + {b = true -> False}.
  refine (fun b =>
            match b with
            | true => Yes
            | false => No
            end). reflexivity. discriminate.
Defined.

Definition decide : forall (truth : var -> bool) (p : prop),
    {propDenote truth p} + {~ propDenote truth p}.
  intros. induction p; crush. destruct (truth v); crush.
Defined.

Notation "[ e ]" := (exist _ e _).
Notation "x <- e1 ; e2" :=
  (match e1 with exist x _ => e2 end)
  (right associativity, at level 60).

Definition negate : forall p : prop,
    {p' : prop | forall truth, propDenote truth p <-> ~ propDenote truth p'}.
  refine (fix F (p : prop) : {p' : prop | forall truth, propDenote truth p <-> ~ propDenote truth p'} :=
            match p with
            | Var v => [Neg (Var v)]
            | Neg p => [p]
            | Conj p1 p2 =>
              p1' <- F p1;
              p2' <- F p2;
              [Disj p1' p2']
            | Disj p1 p2 =>
              p1' <- F p1;
              p2' <- F p2;
              [Conj p1' p2']
            end); crush;
    repeat (match goal with
            | [i : forall truth : var -> bool, _ <-> _ |- _] =>
              destruct (i truth); clear i
            | [|- context[if ?E then _ else _]] =>
              destruct E
            end); crush.
  destruct (decide truth p1'); crush.
Defined.
