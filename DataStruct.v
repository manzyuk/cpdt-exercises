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

(* Heterogeneous Lists *)

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
    | HNil => fun mem =>
                match mem in member ls' return (match ls' with
                                                | nil => B elm
                                                | _ :: _ => unit
                                                end) with
                | HFirst _ => tt
                | HNext _ _ _ => tt
                end
    | HCons _ _ x mls' => fun mem =>
                            match mem in member ls' return (match ls' with
                                                            | nil => Empty_set
                                                            | x' :: ls'' =>
                                                              B x' -> (member ls'' -> B elm) -> B elm
                                                            end) with
                            | HFirst _ => fun x _ => x
                            | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
                            end x (hget mls')
    end.
End hlist.

Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].
Implicit Arguments HFirst [A elm ls].
Implicit Arguments HNext [A elm x ls].

Definition someTypes : list Set := nat :: bool :: nil.

Example someValues : hlist (fun T : Set => T) someTypes :=
  HCons 5 (HCons true HNil).

Eval simpl in hget someValues HFirst.

Eval simpl in hget someValues (HNext HFirst).

Example somePairs : hlist (fun T : Set => T * T)%type someTypes :=
  HCons (1, 2) (HCons (true, false) HNil).
