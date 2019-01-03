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

(* Dependently Typed Red-Black Trees *)

Inductive color : Set := Red | Black.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).

Require Import Max Min.

Section depth.
  Variable f : nat -> nat -> nat.

  Fixpoint depth c n (t : rbtree c n) : nat :=
    match t with
    | Leaf => 0
    | RedNode _ t1 _ t2 => S (f (depth t1) (depth t2))
    | BlackNode _ _ _ t1 _ t2 => S (f (depth t1) (depth t2))
    end.
End depth.

Check min_dec.

Theorem depth_min : forall c n (t : rbtree c n), depth min t >= n.
  induction t; crush;
    match goal with
    | [ |- context[min ?X ?Y]] => destruct (min_dec X Y)
    end; crush.
Qed.

Lemma depth_max' : forall c n (t : rbtree c n),
    match c with
    | Red => depth max t <= 2 * n + 1
    | Black => depth max t <= 2 * n
    end.
  induction t; crush;
    match goal with
    | [ |- context[max ?X ?Y]] => destruct (max_dec X Y)
    end; crush;
      repeat (match goal with
              | [H : context[match ?C with Red => _ | Black => _ end] |- _] =>
                destruct C
              end; crush).
Qed.

Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 2 * n + 1.
  intros; generalize (depth_max' t); destruct c; crush.
Qed.

Theorem balanced : forall c n (t : rbtree c n),
    2 * depth min t + 1 >= depth max t.
  intros; generalize (depth_min t); generalize (depth_max t); crush.
Qed.

Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.

Section present.
  Variable x : nat.

  Fixpoint present c n (t : rbtree c n) : Prop :=
    match t with
    | Leaf => False
    | RedNode _ a y b => present a \/ x = y \/ present b
    | BlackNode _ _ _ a y b => present a \/ x = y \/ present b
    end.

  Definition rpresent n (t : rtree n) : Prop :=
    match t with
    | RedNode' _ _ _ a y b => present a \/ x = y \/ present b
    end.
End present.

Locate "{ _ : _ & _ }".

Print sigT.

Notation "{< x >}" := (existT _ _ x).

Definition balance1 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n -> {c : color & rbtree c (S n)} with
  | RedNode' _ c0 _ t1 y t2 =>
    match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n -> {c : color & rbtree c (S n)} with
    | RedNode _ a x b => fun c d => {<RedNode (BlackNode a x b) y (BlackNode c data d)>}
    | t1' => fun t2 =>
               match t2 in rbtree c n return rbtree Black n -> rbtree c2 n -> {c : color & rbtree c (S n)} with
               | RedNode _ b x c => fun a d => {<RedNode (BlackNode a y b) x (BlackNode c data d)>}
               | b => fun a t => {<BlackNode (RedNode a y b) data t>}
               end t1'
    end t2
  end.

Definition balance2 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n -> {c : color & rbtree c (S n)} with
  | RedNode' _ c0 _ t1 z t2 =>
    match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n -> {c : color & rbtree c (S n)} with
    | RedNode _ b y c => fun d a => {<RedNode (BlackNode a data b) y (BlackNode c z d)>}
    | t1' => fun t2 =>
               match t2 in rbtree c n return rbtree Black n -> rbtree c2 n -> {c : color & rbtree c (S n)} with
               | RedNode _ c z' d => fun b a => {<RedNode (BlackNode a data b) z (BlackNode c z' d)>}
               | b => fun a t => {<BlackNode t data (RedNode a z b)>}
               end t1'
    end t2
  end.

Section insert.
  Variable x : nat.

  Definition insResult c n :=
    match c with
    | Red => rtree n
    | Black => {c' : color & rbtree c' n}
    end.

  Fixpoint ins c n (t : rbtree c n) : insResult c n :=
    match t with
    | Leaf => {<RedNode Leaf x Leaf>}
    | RedNode _ a y b =>
      if le_lt_dec x y
      then RedNode' (projT2 (ins a)) y b
      else RedNode' a y (projT2 (ins b))
    | BlackNode c1 c2 _ a y b =>
      if le_lt_dec x y
      then
        match c1 return insResult c1 _ -> _ with
        | Red => fun ins_a => balance1 ins_a y b
        | _ => fun ins_a => {<BlackNode (projT2 ins_a) y b>}
        end (ins a)
      else
        match c2 return insResult c2 _ -> _ with
        | Red => fun ins_b => balance2 ins_b y a
        | _ => fun ins_b => {<BlackNode a y (projT2 ins_b)>}
        end (ins b)
    end.

  Definition insertResult c n :=
    match c with
    | Red => rbtree Black (S n)
    | Black => {c' : color & rbtree c' n}
    end.

  Definition makeRbtree c n : insResult c n -> insertResult c n :=
    match c with
    | Red => fun r =>
               match r with
               | RedNode' _ _ _ a x b => BlackNode a x b
               end
    | Black => fun r => r
    end.

  Implicit Arguments makeRbtree [c n].

  Definition insert c n (t : rbtree c n) : insertResult c n :=
    makeRbtree (ins t).

  Section present.
    Variable z : nat.

    Ltac present_balance :=
      crush;
      repeat (match goal with
              | [_ : context[match ?T with Leaf => _ | _ => _ end] |- _] =>
                dep_destruct T
              | [ |- context[match ?T with Leaf => _ | _ => _ end]] =>
                dep_destruct T
              end; crush).

    Lemma present_balance1 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
        present z (projT2 (balance1 a y b))
        <-> rpresent z a \/ z = y \/ present z b.
      destruct a; present_balance.
    Qed.

    Lemma present_balance2 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
        present z (projT2 (balance2 a y b))
        <-> rpresent z a \/ z = y \/ present z b.
      destruct a; present_balance.
    Qed.

    Definition present_insResult c n :=
      match c return (rbtree c n -> insResult c n -> Prop) with
      | Red => fun t r => rpresent z r <-> z = x \/ present z t
      | Black => fun t r => present z (projT2 r) <-> z = x \/ present z t
      end.

    Theorem present_ins : forall c n (t : rbtree c n),
        present_insResult t (ins t).
      induction t; crush;
        repeat (match goal with
                | [_ : context[if ?E then _ else _] |- _] => destruct E
                | [ |- context[if ?E then _ else _]] => destruct E
                | [_ : context[match ?C with Red => _ | Black => _ end] |- _] =>
                  destruct C
                end; crush);
        try match goal with
            | [_ : context[balance1 ?A ?B ?C] |- _] =>
              generalize (present_balance1 A B C)
            end;
        try match goal with
            | [_ : context[balance2 ?A ?B ?C] |- _] =>
              generalize (present_balance2 A B C)
            end;
        try match goal with
            | [ |- context[balance1 ?A ?B ?C]] =>
              generalize (present_balance1 A B C)
            end;
        try match goal with
            | [ |- context[balance2 ?A ?B ?C]] =>
              generalize (present_balance2 A B C)
            end;
        crush;
        match goal with
        | [z : nat, x : nat |- _] =>
          match goal with
          | [H : z = x |- _] => rewrite H in *; clear H
          end
        end;
        tauto.
    Qed.

    Ltac present_insert :=
      unfold insert; intros n t; inversion t;
      generalize (present_ins t); simpl;
      dep_destruct (ins t); tauto.

    Theorem present_insert_Red : forall n (t : rbtree Red n),
        present z (insert t)
        <-> (z = x \/ present z t).
      present_insert.
    Qed.

    Theorem present_insert_Black : forall n (t : rbtree Black n),
        present z (projT2 (insert t))
        <-> (z = x \/ present z t).
      present_insert.
    Qed.
  End present.
End insert.

Recursive Extraction insert.
