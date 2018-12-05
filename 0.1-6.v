Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive nat_tree : Set :=
| NTLeaf : nat -> nat_tree
| NTNode : (nat -> nat_tree) -> nat_tree.

Fixpoint increment (nt : nat_tree) : nat_tree :=
  match nt with
  | NTLeaf n => NTLeaf (S n)
  | NTNode children => NTNode (fun n => increment (children n))
  end.

Fixpoint leapfrog (i : nat) (nt : nat_tree) : nat :=
  match nt with
  | NTLeaf n => n
  | NTNode children => leapfrog (S i) (children i)
  end.

Theorem leapfrog_increment : forall (nt : nat_tree) (i : nat),
    leapfrog i (increment nt) = S (leapfrog i nt).
  induction nt; crush.
Qed.
