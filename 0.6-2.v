Require Import Arith Bool List.
Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Fixpoint happend ls1 ls2 (mls1 : hlist ls1) (mls2 : hlist ls2) : hlist (ls1 ++ ls2) :=
    match mls1 with
    | HNil => mls2
    | HCons _ _ x mls1' => HCons x (happend mls1' mls2)
    end.

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

Section hmap.
  Variable A : Type.
  Variables B C : A -> Type.
  Variable f : forall x, B x -> C x.

  Fixpoint hmap ls (mls : hlist B ls) : hlist C ls :=
    match mls with
    | HNil => HNil
    | HCons _ _ x mls' => HCons (f x) (hmap mls')
    end.
End hmap.

Implicit Arguments hmap [A B C ls].

Inductive type : Type :=
| Bool : type
| Sum : type -> type -> type.

Fixpoint typeDenote (t : type) : Set :=
  match t with
  | Bool => bool
  | Sum t1 t2 => typeDenote t1 + typeDenote t2
  end%type.

(* pat ts t is a pattern that contains variables of types ts and that
can be used to pattern-match values of type t *)
Inductive pat : list type -> type -> Type :=
| PConst : bool -> pat nil Bool
| PVar : forall t, pat (t :: nil) t
| PInl : forall ts t1 t2, pat ts t1 -> pat ts (Sum t1 t2)
| PInr : forall ts t1 t2, pat ts t2 -> pat ts (Sum t1 t2).

Inductive exp : list type -> type -> Type :=
| Const : forall ts, bool -> exp ts Bool
| Var : forall ts t, member t ts -> exp ts t
| Inl : forall ts t1 t2, exp ts t1 -> exp ts (Sum t1 t2)
| Inr : forall ts t1 t2, exp ts t2 -> exp ts (Sum t1 t2)
| Case : forall ts tin tout tss,
    exp ts tin
    -> hlist
         (* case expression can refer to the variables from the
         enclosing scope as well as to the variables brought into
         scope by pattern-matching *)
         (fun ts' => (pat ts' tin * exp (ts' ++ ts) tout)%type)
         tss
    -> exp ts tout
    -> exp ts tout.

Fixpoint patDenote ts t (p : pat ts t) : typeDenote t -> option (hlist typeDenote ts) :=
  match p with
  | PConst b => fun v =>
      if Bool.bool_dec b v then Some HNil else None
  | PVar _ => fun v =>
      Some (HCons v HNil)
  | PInl _ _ _ p' => fun v =>
      match v with
      | inl v' => patDenote p' v'
      | inr _ => None
      end
  | PInr _ _ _ p' => fun v =>
      match v with
      | inl _ => None
      | inr v' => patDenote p' v'
      end
  end.

Fixpoint case t tss A (v : typeDenote t) (cases : hlist (fun ts' => (pat ts' t * (hlist typeDenote ts' -> A))%type) tss) (default : A) : A :=
  match cases with
  | HNil => default
  | HCons _ _ (p, f) cases' =>
    match patDenote p v with
    | None => case v cases' default
    | Some s => f s
    end
  end.

Fixpoint expDenote ts t (e : exp ts t) : hlist typeDenote ts -> typeDenote t :=
  match e with
  | Const _ b => fun _ => b
  | Var _ _ mem => fun s => hget s mem
  | Inl _ _ _ e => fun s => inl (expDenote e s)
  | Inr _ _ _ e => fun s => inr (expDenote e s)
  | Case _ _ _ _ scrutinee cases default => fun s =>
      case
        (expDenote scrutinee s)
        (hmap
           (fun _ case =>
              (fst case,
               fun s' => expDenote (snd case) (happend s' s)))
           cases)
        (expDenote default s)
  end.

Example ex1 :=
  Case
    (Var (HFirst (ls := nil)))
    (HCons
       (PInl Bool (PVar Bool), Inr Bool (Var HFirst))
       (HCons
          (PInr Bool (PVar Bool), Inl Bool (Var HFirst))
          HNil))
    (Var HFirst).

Print ex.

Eval simpl in expDenote ex1 (HCons (x := Sum Bool Bool) (inl true) HNil).
Eval simpl in expDenote ex1 (HCons (x := Sum Bool Bool) (inr false) HNil).

Example ex2 :=
  Case
    (Var (HFirst (ls := nil)))
    (HCons
       (PInl Bool (PVar Bool), Inr (Sum Bool Bool) (Var (HNext HFirst)))
       (HCons
          (PInr Bool (PVar Bool), Inr (Sum Bool Bool) (Inl Bool (Var HFirst)))
          HNil))
    (Inl (Sum Bool Bool) (Var HFirst)).

Eval simpl in expDenote ex2 (HCons (x := Sum Bool Bool) (inl true) HNil).
Eval simpl in expDenote ex2 (HCons (x := Sum Bool Bool) (inr false) HNil).
