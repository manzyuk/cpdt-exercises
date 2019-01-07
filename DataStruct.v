Require Import Arith List.
Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* More Length-Indexed Lists *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
    | Nil => fun idx =>
               match idx in fin n' return (match n' with
                                           | O => A
                                           | S _ => unit
                                           end) with
               | First _ => tt
               | Next _ _ => tt
               end
    | Cons _ x ls' => fun idx =>
                        match idx in fin n' return (fin (pred n') -> A) -> A with
                        | First _ => fun _ => x
                        | Next _ idx' => fun get_ls' => get_ls' idx'
                        end (get ls')
    end.
End ilist.

Implicit Arguments Nil [A].
Implicit Arguments First [n].

Section ilist_map.
  Variable A B : Set.
  Variable f : A -> B.

  Fixpoint imap n (ls : ilist A n) : ilist B n :=
    match ls with
    | Nil => Nil
    | Cons _ x ls' => Cons (f x) (imap ls')
    end.

  Theorem get_imap : forall n (idx : fin n) (ls : ilist A n),
      get (imap ls) idx = f (get ls idx).
    induction ls; dep_destruct idx; crush.
  Qed.
End ilist_map.
