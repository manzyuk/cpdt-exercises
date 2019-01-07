Require Import Bool Arith List Omega Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Section plist.
  Variable A : Set.
  Variable P : A -> Prop.
  Variable dec : forall x, {P x} + {~ P x}.

  Inductive plist : nat -> Set :=
  | Nil : plist O
  | UCons : forall n, A -> plist n -> plist n
  | TCons : forall n x, P x -> plist n -> plist (S n).

  Fixpoint append n1 (ls1 : plist n1) n2 (ls2 : plist n2) : plist (n1 + n2) :=
    match ls1 in (plist n1) return plist (n1 + n2) with
    | Nil => ls2
    | UCons _ x ls1' => UCons x (append ls1' ls2)
    | TCons _ _ pf ls1' => TCons pf (append ls1' ls2)
    end.

  Fixpoint plistOut n (ls : plist n): list A :=
    match ls with
    | Nil => nil
    | UCons _ x ls' => x :: plistOut ls'
    | TCons _ x _ ls' => x :: plistOut ls'
    end.

  Notation "{< x >}" := (existT _ _ x).

  Fixpoint plistIn' (ls : list A) : {n : nat & plist n} :=
    match ls with
    | nil => {<Nil>}
    | h :: t =>
      match dec h with
      | left p => {<TCons p (projT2 (plistIn' t))>}
      | right _ => {<UCons h (projT2 (plistIn' t))>}
      end
    end.

  Definition plistIn (ls : list A) := projT2 (plistIn' ls).

  Check plistIn.

  Fixpoint count (ls : list A) : nat :=
    match ls with
    | nil => O
    | h :: t => if dec h then S (count t) else count t
    end.

  Ltac plistIn :=
    crush;
    match goal with
    | [ |- context[dec ?A]] => destruct (dec A)
    end; crush.

  Theorem plistIn_bound : forall ls, projT1 (plistIn' ls) = count ls.
    intro; induction ls; plistIn.
  Qed.

  Theorem out_in : forall ls, plistOut (plistIn ls) = ls.
    intro; induction ls; crush; unfold plistIn in *; plistIn.
  Qed.
