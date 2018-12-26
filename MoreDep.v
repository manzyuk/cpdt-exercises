Require Import Arith Bool List Omega.

Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif.

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Length-Indexed Lists *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app ls1' ls2)
    end.

  Fixpoint app' n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
    | Nil => ls2
    | Cons _ x ls1' => Cons x (app' ls1' ls2)
    end.

  Fixpoint inject (ls : list A) : ilist (length ls) :=
    match ls with
    | nil => Nil
    | h :: t => Cons h (inject t)
    end.

  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
    | Nil => nil
    | Cons _ h t => h :: unject t
    end.

  Theorem inject_inverse : forall ls, unject (inject ls) = ls.
    induction ls; crush.
  Qed.

  Definition hd' n (ls : ilist n) :=
    match ls in (ilist n) return (match n with O => unit | S _ => A end) with
    | Nil => tt
    | Cons _ h _ => h
    end.

  Check hd'.

  Definition hd n (ls : ilist (S n)) : A := hd' ls.
End ilist.

(* A Tagless Interpreter *)

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool

| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall t, exp Bool -> exp t -> exp t -> exp t

| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
| Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end%type.

Fixpoint expDenote t (e : exp t) : typeDenote t :=
  match e with
  | NConst n => n
  | Plus e1 e2 => expDenote e1 + expDenote e2
  | Eq e1 e2 => if eq_nat_dec (expDenote e1) (expDenote e2) then true else false

  | BConst b => b
  | And e1 e2 => expDenote e1 && expDenote e2
  | If _ e' e1 e2 => if expDenote e' then expDenote e1 else expDenote e2

  | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
  | Fst _ _ e' => fst (expDenote e')
  | Snd _ _ e' => snd (expDenote e')
  end.

Definition pairOutType (t : type) := option (match t with
                                             | Prod t1 t2 => exp t1 * exp t2
                                             | _ => unit
                                            end).

Definition pairOut t (e : exp t) :=
  match e in (exp t) return pairOutType t with
  | Pair _ _ e1 e2 => Some (e1, e2)
  | _ => None
  end.

Fixpoint cfold t (e : exp t) : exp t :=
  match e with
  | NConst n => NConst n
  | Plus e1 e2 =>
    let e1' := cfold e1 in
    let e2' := cfold e2 in
    match e1', e2' return exp Nat with
    | NConst n1, NConst n2 => NConst (n1 + n2)
    | _, _ => Plus e1' e2'
    end
  | Eq e1 e2 =>
    let e1' := cfold e1 in
    let e2' := cfold e2 in
    match e1', e2' return exp Bool with
    | NConst n1, NConst n2 => BConst (if eq_nat_dec n1 n2 then true else false)
    | _, _ => Eq e1' e2'
    end

  | BConst b => BConst b
  | And e1 e2 =>
    let e1' := cfold e1 in
    let e2' := cfold e2 in
    match e1', e2' return exp Bool with
    | BConst b1, BConst b2 => BConst (b1 && b2)
    | _, _ => And e1' e2'
    end
  | If _ e e1 e2 =>
    let e' := cfold e in
    match e' with
    | BConst true => cfold e1
    | BConst false => cfold e2
    | _ => If e' (cfold e1) (cfold e2)
    end

  | Pair _ _ e1 e2 => Pair (cfold e1) (cfold e2)
  | Fst _ _ e =>
    let e' := cfold e in
    match pairOut e' with
    | Some p => fst p
    | None => Fst e'
    end
  | Snd _ _ e =>
    let e' := cfold e in
    match pairOut e' with
    | Some p => snd p
    | None => Snd e'
    end
  end.

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
  induction e; crush;
    repeat (match goal with
            | [ |- context[match cfold ?E with NConst _ => _ | _ => _ end]] =>
              dep_destruct (cfold E)
            | [ |- context[match pairOut (cfold ?E) with Some _ => _ | None => _ end]] =>
              dep_destruct (cfold E)
            | [ |- (if ?E then _ else _) = _] => destruct E
            end; crush).
Qed.
