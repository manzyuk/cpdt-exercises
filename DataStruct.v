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

(* A Lambda Calculus Interpreter *)

Inductive type : Set :=
| Unit : type
| Arrow : type -> type -> type.

Inductive exp : list type -> type -> Set :=
| Const : forall ts, exp ts Unit
| Var : forall ts t, member t ts -> exp ts t
| App : forall ts dom ran, exp ts (Arrow dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (Arrow dom ran).

Implicit Arguments Const [ts].

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Unit => unit
  | Arrow t1 t2 => typeDenote t1 -> typeDenote t2
  end.

Fixpoint expDenote ts t (e : exp ts t) : hlist typeDenote ts -> typeDenote t :=
  match e with
  | Const _ => fun _ => tt
  | Var _ _ mem => fun s => hget s mem
  | App _ _ _ e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
  | Abs _ _ _ e' => fun s => fun x => expDenote e' (HCons x s)
  end.

Eval simpl in expDenote Const HNil.

Eval simpl in expDenote (Abs (dom := Unit) (Var HFirst)) HNil.

Eval simpl in expDenote (Abs (dom := Unit) (Abs (dom := Unit) (Var (HNext HFirst)))) HNil.

Eval simpl in expDenote (Abs (dom := Unit) (Abs (dom := Unit) (Var HFirst))) HNil.

Eval simpl in expDenote (App (Abs (Var HFirst)) Const) HNil.

(* Recursive Type Definitions *)

Section filist.
  Variable A : Set.

  Fixpoint filist (n : nat) : Set :=
    match n with
    | O => unit
    | S n' => A * filist n'
    end%type.

  Fixpoint ffin (n : nat) : Set :=
    match n with
    | O => Empty_set
    | S n' => option (ffin n')
    end.

  Fixpoint fget (n : nat) : filist n -> ffin n -> A :=
    match n with
    | O => fun _ idx => match idx with end
    | S n' => fun ls idx =>
                match idx with
                | None => fst ls
                | Some idx' => fget n' (snd ls) idx'
                end
    end.
End filist.

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

  Fixpoint fhlist (ls : list A) : Type :=
    match ls with
    | nil => unit
    | x :: ls' => B x * fhlist ls'
    end%type.

  Variable elm : A.

  Fixpoint fmember (ls : list A) : Type :=
    match ls with
    | nil => Empty_set
    | x :: ls' => (x = elm) + fmember ls'
    end%type.

  Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
    match ls with
    | nil => fun _ idx => match idx with end
    | _ :: ls' => fun mls idx =>
                    match idx with
                    | inl pf => match pf with
                                | eq_refl => fst mls
                                end
                    | inr idx' => fhget ls' (snd mls) idx'
                    end
    end.
End fhlist.

Implicit Arguments fhget [A B elm ls].

(* Data Structures as Index Functions *)

Section tree.
  Variable A : Set.

  Inductive tree : Set :=
  | Leaf : A -> tree
  | Node : forall n, (ffin n -> tree) -> tree.
End tree.

Implicit Arguments Node [A n].

Section rifoldr.
  Variables A B : Set.
  Variable f : A -> B -> B.
  Variable i : B.

  Fixpoint rifoldr (n : nat) : (ffin n -> A) -> B :=
    match n with
    | O => fun _ => i
    | S n' => fun get => f (get None) (rifoldr n' (fun idx => get (Some idx)))
    end.
End rifoldr.

Implicit Arguments rifoldr [A B n].

Fixpoint sum (t : tree nat) : nat :=
  match t with
  | Leaf n => n
  | Node _ f => rifoldr plus O (fun idx => sum (f idx))
  end.

Fixpoint inc (t : tree nat) : tree nat :=
  match t with
  | Leaf n => Leaf (S n)
  | Node _ f => Node (fun idx => inc (f idx))
  end.

Lemma plus_ge : forall x1 y1 x2 y2,
    x1 >= x2 -> y1 >= y2 -> x1 + y1 >= x2 + y2.
  crush.
Qed.

Lemma sum_inc' : forall n (f1 f2 : ffin n -> nat),
    (forall idx, f1 idx >= f2 idx)
    -> rifoldr plus O f1 >= rifoldr plus O f2.
  Hint Resolve plus_ge.

  induction n; crush.
Qed.

Theorem sum_inc : forall t, sum (inc t) >= sum t.
  Hint Resolve sum_inc'.

  induction t; crush.
Qed.

(* Another Interpreter Example *)

Inductive type' : Type := Nat | Bool.

Inductive exp' : type' -> Type :=
| NConst : nat -> exp' Nat
| Plus : exp' Nat -> exp' Nat -> exp' Nat
| Eq : exp' Nat -> exp' Nat -> exp' Bool
| BConst : bool -> exp' Bool
| Cond : forall n t, (ffin n -> exp' Bool) -> (ffin n -> exp' t) -> exp' t -> exp' t.

Example ex1 := Cond 2
  (fun f => match f with
            | None => Eq (Plus (NConst 2) (NConst 2)) (NConst 5)
            | Some None => Eq (Plus (NConst 1) (NConst 1)) (NConst 2)
            | Some (Some v) => match v with end
            end)
  (fun f => match f with
            | None => NConst 0
            | Some None => NConst 1
            | Some (Some v) => match v with end
            end)
  (NConst 2).

Definition type'Denote (t : type') : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

Section cond.
  Variable A : Set.
  Variable default : A.

  Fixpoint cond (n : nat) : (ffin n -> bool) -> (ffin n -> A) -> A :=
    match n with
    | O => fun _ _ => default
    | S n' => fun tests bodies =>
      if tests None
      then bodies None
      else cond n'
                (fun idx => tests (Some idx))
                (fun idx => bodies (Some idx))
    end.
End cond.

Implicit Arguments cond [A n].

Fixpoint exp'Denote t (e : exp' t) : type'Denote t :=
  match e with
  | NConst n => n
  | Plus e1 e2 => exp'Denote e1 + exp'Denote e2
  | Eq e1 e2 =>
    if eq_nat_dec (exp'Denote e1) (exp'Denote e2) then true else false
  | BConst b => b
  | Cond _ _ tests bodies default =>
    cond
      (exp'Denote default)
      (fun idx => exp'Denote (tests idx))
      (fun idx => exp'Denote (bodies idx))
  end.

Section cfoldCond.
  Variable t : type'.
  Variable default : exp' t.

  Fixpoint cfoldCond (n : nat)
    : (ffin n -> exp' Bool) -> (ffin n -> exp' t) -> exp' t :=
    match n with
    | O => fun _ _ => default
    | S n' => fun tests bodies =>
      match tests None return _ with
      | BConst true => bodies None
      | BConst false => cfoldCond n'
          (fun idx => tests (Some idx))
          (fun idx => bodies (Some idx))
      | _ =>
        let e := cfoldCond n'
          (fun idx => tests (Some idx))
          (fun idx => bodies (Some idx)) in
        match e in exp' t return exp' t -> exp' t with
        | Cond n _ tests' bodies' default' => fun body =>
            Cond
              (S n)
              (fun idx => match idx with
                          | None => tests None
                          | Some idx => tests' idx
                          end)
              (fun idx => match idx with
                          | None => body
                          | Some idx => bodies' idx
                          end)
              default'
        | e => fun body =>
            Cond
              1
              (fun _ => tests None)
              (fun _ => body)
              e
        end (bodies None)
      end
    end.
End cfoldCond.

Implicit Arguments cfoldCond [t n].

Fixpoint cfold t (e : exp' t) : exp' t :=
  match e with
  | NConst n => NConst n
  | Plus e1 e2 =>
    let e1' := cfold e1 in
    let e2' := cfold e2 in
    match e1', e2' return exp' Nat with
    | NConst n1, NConst n2 => NConst (n1 + n2)
    | _, _ => Plus e1' e2'
    end
  | Eq e1 e2 =>
    let e1' := cfold e1 in
    let e2' := cfold e2 in
    match e1', e2' return exp' Bool with
    | NConst n1, NConst n2 => BConst (if eq_nat_dec n1 n2 then true else false)
    | _, _ => Eq e1' e2'
    end
  | BConst b => BConst b
  | Cond _ _ tests bodies default =>
    cfoldCond
      (cfold default)
      (fun idx => cfold (tests idx))
      (fun idx => cfold (bodies idx))
  end.

Lemma cfoldCond_correct : forall t (default : exp' t) n (tests : ffin n -> exp' Bool) (bodies : ffin n -> exp' t),
    exp'Denote (cfoldCond default tests bodies)
    = exp'Denote (Cond n tests bodies default).
  induction n; crush;
    match goal with
    | [IHn : forall tests bodies, _, tests : _ -> _, bodies : _ -> _ |- _] =>
      specialize (IHn (fun idx => tests (Some idx)) (fun idx => bodies (Some idx)))
    end;
    repeat (match goal with
            | [ |- context[match ?E with NConst _ => _ | _ => _ end]] =>
              dep_destruct E
            | [ |- context[if ?B then _ else _]] => destruct B
            end; crush).
Qed.

Lemma cond_ext : forall (A : Set) (default : A) n (tests tests' : ffin n -> bool) (bodies bodies' : ffin n -> A),
    (forall idx, tests idx = tests' idx)
    -> (forall idx, bodies idx = bodies' idx)
    -> cond default tests bodies = cond default tests' bodies'.
  induction n; crush;
    match goal with
    | [ |- context[if ?E then _ else _]] => destruct E
    end; crush.
Qed.

Theorem cfold_correct : forall t (e : exp' t),
    exp'Denote (cfold e) = exp'Denote e.
  Hint Rewrite cfoldCond_correct.
  Hint Resolve cond_ext.

  induction e; crush;
    repeat (match goal with
            | [ |- context[cfold ?E]] => dep_destruct (cfold E)
            end; crush).
Qed.
