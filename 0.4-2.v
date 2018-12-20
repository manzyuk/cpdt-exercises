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
            end); crush.
  destruct (truth v). constructor. apply (H (fun f => f)).
  set (Hp1 := i truth). unfold iff in Hp1. destruct Hp1. apply (H0 H1 H).
  set (Hp2 := i0 truth). unfold iff in Hp2. destruct Hp2. apply (H0 H2 H).
  set (Hp1 := i truth). unfold iff in Hp1. destruct Hp1. apply (H H0 H1).
  set (Hp2 := i0 truth). unfold iff in Hp2. destruct Hp2. apply (H H0 H2).
  destruct (decide truth p1'). right; apply (H0 p0). left. assumption.
Defined.
