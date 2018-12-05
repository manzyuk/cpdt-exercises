Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set := Plus | Times.

Definition var := nat.

Definition vars := var -> nat.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote (vs : vars) (e : exp) : nat :=
  match e with
  | Const n => n
  | Var v => vs v
  | Binop b e1 e2 => binopDenote b (expDenote vs e1) (expDenote vs e2)
  end.

Definition binopFoldConsts (b : binop) (e1 e2 : exp) : exp :=
  match e1, e2 with
  | Const n1, Const n2 => Const (binopDenote b n1 n2)
  | _, _ => Binop b e1 e2
  end.

Fixpoint expFoldConsts (e : exp) : exp :=
  match e with
  | Binop b e1 e2 => binopFoldConsts b (expFoldConsts e1) (expFoldConsts e2)
  | _ => e
  end.

Eval simpl in expFoldConsts (Binop Plus (Binop Times (Const 1) (Const 2)) (Binop Plus (Const 3) (Const 4))).

Lemma binopFoldConsts_preserves_meaning :
  forall (vs : vars) (b : binop) (e1 e2 : exp),
    expDenote vs (binopFoldConsts b e1 e2) = binopDenote b (expDenote vs e1) (expDenote vs e2).
  destruct e1; destruct e2; crush.
Qed.

Hint Rewrite binopFoldConsts_preserves_meaning.

Theorem expFoldConsts_preserves_meaning : forall (vs : vars) (e : exp),
    expDenote vs (expFoldConsts e) = expDenote vs e.
  induction e; crush.
Qed.
