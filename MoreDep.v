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

(* A Certified Regular Expression Matcher *)

Require Import Ascii String.

Open Scope string_scope.

Section star.
  Variable P : string -> Prop.

  Inductive star : string -> Prop :=
  | Empty : star ""
  | Iter : forall s1 s2, P s1 -> star s2 -> star (s1 ++ s2).
End star.

Inductive regexp : (string -> Prop) -> Type :=
| Char : forall ch : ascii,
    regexp (fun s => s = String ch "")
| Concat : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
    regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2)
| Or : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
    regexp (fun s => P1 s \/ P2 s)
| Star : forall P (r : regexp P),
    regexp (star P).

Open Scope specif_scope.

Lemma length_emp : length "" <= 0.
  crush.
Qed.

Lemma append_emp : forall s, s = "" ++ s.
  crush.
Qed.

Ltac substring :=
  crush;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] => destruct N; crush
         end.

Lemma substring_le : forall s n m,
  length (substring n m s) <= m.
  induction s; substring.
Qed.

Lemma substring_all : forall s,
  substring 0 (length s) s = s.
  induction s; substring.
Qed.

Lemma substring_none : forall s n,
  substring n 0 s = "".
  induction s; substring.
Qed.

Hint Rewrite substring_all substring_none.

Lemma substring_split : forall s m,
  substring 0 m s ++ substring m (length s - m) s = s.
  induction s; substring.
Qed.

Lemma length_app1 : forall s1 s2,
  length s1 <= length (s1 ++ s2).
  induction s1; crush.
Qed.

Hint Resolve length_emp append_emp substring_le substring_split length_app1.

Lemma substring_app_fst : forall s2 s1 n,
  length s1 = n
  -> substring 0 n (s1 ++ s2) = s1.
  induction s1; crush.
Qed.

Lemma substring_app_snd : forall s2 s1 n,
  length s1 = n
  -> substring n (length (s1 ++ s2) - n) (s1 ++ s2) = s2.
  Hint Rewrite <- minus_n_O.

  induction s1; crush.
Qed.

Hint Rewrite substring_app_fst substring_app_snd using solve [trivial].

Section split.
  Variables P1 P2 : string -> Prop.
  Variable P1_dec : forall s, {P1 s} + {~ P1 s}.
  Variable P2_dec : forall s, {P2 s} + {~ P2 s}.
  Variable s : string.

  Definition split' : forall n : nat,
      n <= length s ->
      {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2} +
      {forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2}.
    refine (fix F (n : nat) :
              n <= length s ->
              {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2} +
              {forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2} :=
              match n with
              | O => fun _ => Reduce (P1_dec "" && P2_dec s)
              | S n' => fun _ =>
                          (P1_dec (substring 0 (S n') s) && P2_dec (substring (S n') (length s - S n') s)) || F n' _
              end); clear F; crush; eauto 7;
      match goal with
      | [_ : length ?S <= 0 |- _] => destruct S
      | [_ : length ?S' <= S ?N |- _] => destruct (eq_nat_dec (length S') (S N))
      end; crush.
  Defined.

  Definition split :
    {exists s1, exists s2, s1 ++ s2 = s /\ P1 s1 /\ P2 s2} +
    {forall s1 s2, s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2}.
    refine (Reduce (split' (n := length s) _)); crush; eauto.
  Defined.
End split.

Implicit Arguments split [P1 P2].

Lemma app_empty_end : forall s, s ++ "" = s.
  induction s; crush.
Qed.

Hint Rewrite app_empty_end.

Lemma substring_self : forall s n,
  n <= 0
  -> substring n (length s - n) s = s.
  induction s; substring.
Qed.

Lemma substring_empty : forall s n m,
  m <= 0
  -> substring n m s = "".
  induction s; substring.
Qed.

Hint Rewrite substring_self substring_empty using omega.

Lemma substring_split' : forall s n m,
  substring n m s ++ substring (n + m) (length s - (n + m)) s
  = substring n (length s - n) s.
  Hint Rewrite substring_split.

  induction s; substring.
Qed.

Lemma substring_stack : forall s n2 m1 m2,
  m1 <= m2
  -> substring 0 m1 (substring n2 m2 s)
  = substring n2 m1 s.
  induction s; substring.
Qed.

Ltac substring' :=
  crush;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] => case_eq N; crush
         end.

Lemma substring_stack' : forall s n1 n2 m1 m2,
  n1 + m1 <= m2
  -> substring n1 m1 (substring n2 m2 s)
  = substring (n1 + n2) m1 s.
  induction s; substring';
    match goal with
      | [ |- substring ?N1 _ _ = substring ?N2 _ _ ] =>
        replace N1 with N2; crush
    end.
Qed.

Lemma substring_suffix : forall s n,
  n <= length s
  -> length (substring n (length s - n) s) = length s - n.
  induction s; substring.
Qed.

Lemma substring_suffix_emp' : forall s n m,
  substring n (S m) s = ""
  -> n >= length s.
  induction s; crush;
    match goal with
      | [ |- ?N >= _ ] => destruct N; crush
    end;
    match goal with
      [ |- S ?N >= S ?E ] => assert (N >= E); [ eauto | omega ]
    end.
Qed.

Lemma substring_suffix_emp : forall s n m,
  substring n m s = ""
  -> m > 0
  -> n >= length s.
  destruct m as [ | m]; [crush | intros; apply substring_suffix_emp' with m; assumption].
Qed.

Hint Rewrite substring_stack substring_stack' substring_suffix
  using omega.

Lemma minus_minus : forall n m1 m2,
  m1 + m2 <= n
  -> n - m1 - m2 = n - (m1 + m2).
  intros; omega.
Qed.

Lemma plus_n_Sm' : forall n m : nat, S (n + m) = m + S n.
  intros; omega.
Qed.

Hint Rewrite minus_minus using omega.

Section dec_star.
  Variable P : string -> Prop.
  Variable P_dec : forall s, {P s} + {~ P s}.

  Hint Constructors star.

  Lemma star_empty : forall s,
    length s = 0
    -> star P s.
    destruct s; crush.
  Qed.

  Lemma star_singleton : forall s, P s -> star P s.
    intros; rewrite <- (app_empty_end s); auto.
  Qed.

  Lemma star_app : forall s n m,
    P (substring n m s)
    -> star P (substring (n + m) (length s - (n + m)) s)
    -> star P (substring n (length s - n) s).
    induction n; substring;
      match goal with
        | [ H : P (substring ?N ?M ?S) |- _ ] =>
          solve [ rewrite <- (substring_split S M); auto
            | rewrite <- (substring_split' S N M); auto ]
      end.
  Qed.

  Hint Resolve star_empty star_singleton star_app.

  Variable s : string.

  Lemma star_inv : forall s,
    star P s
    -> s = ""
    \/ exists i, i < length s
      /\ P (substring 0 (S i) s)
      /\ star P (substring (S i) (length s - S i) s).
    Hint Extern 1 (exists i : nat, _) =>
      match goal with
        | [ H : P (String _ ?S) |- _ ] => exists (length S); crush
      end.

    induction 1; [
      crush
      | match goal with
          | [ _ : P ?S |- _ ] => destruct S; crush
        end
    ].
  Qed.

  Lemma star_substring_inv : forall n,
    n <= length s
    -> star P (substring n (length s - n) s)
    -> substring n (length s - n) s = ""
    \/ exists l, l < length s - n
      /\ P (substring n (S l) s)
      /\ star P (substring (n + S l) (length s - (n + S l)) s).
    Hint Rewrite plus_n_Sm'.

    intros;
      match goal with
        | [ H : star _ _ |- _ ] => generalize (star_inv H); do 3 crush; eauto
      end.
  Qed.

  Section dec_star''.
    Variable n : nat.
    Variable P' : string -> Prop.
    Variable P'_dec : forall n' : nat, n' > n
      -> {P' (substring n' (length s - n') s)} +
         {~ P' (substring n' (length s - n') s)}.

    Definition dec_star'' : forall l : nat,
        {exists l', S l' <= l
                    /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)} +
        {forall l', S l' <= l
                    -> ~ P (substring n (S l') s) \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)}.
      refine (fix F (l : nat) :
        {exists l', S l' <= l
                    /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)} +
        {forall l', S l' <= l
                    -> ~ P (substring n (S l') s) \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)} :=
                match l with
                | O => _
                | S l' =>
                  (P_dec (substring n (S l') s) && P'_dec (n' := n + S l') _) || F l'
                end); clear F; crush; eauto 7;
        match goal with
        | [H : ?X <= S ?Y |- _] => destruct (eq_nat_dec X (S Y)); crush
        end.
    Defined.
  End dec_star''.

  Lemma star_length_contra : forall n,
    length s > n
    -> n >= length s
    -> False.
    crush.
  Qed.

  Lemma star_length_flip : forall n n',
    length s - n <= S n'
    -> length s > n
    -> length s - n > 0.
    crush.
  Qed.

  Hint Resolve star_length_contra star_length_flip substring_suffix_emp.

  Definition dec_star' : forall n n' : nat, length s - n' <= n
    -> {star P (substring n' (length s - n') s)} +
       {~ star P (substring n' (length s - n') s)}.
    refine (fix F (n n' : nat) : length s - n' <= n
      -> {star P (substring n' (length s - n') s)} +
         {~ star P (substring n' (length s - n') s)} :=
              match n with
              | O =>
                fun _ => Yes
              | S n'' =>
                fun _ =>
                  le_gt_dec (length s) n'
                  || dec_star'' (n := n') (star P)
                                (fun n0 _ => Reduce (F n'' n0 _)) (length s - n')
              end); clear F; crush; eauto;
    match goal with
    | [H : star _ _ |- _] =>
      apply star_substring_inv in H; crush; eauto
    end;
    match goal with
    | [H1 : _ < _ - _, H2 : forall l' : nat, _ <= _ - _ -> _ |- _] =>
      generalize (H2 _ (lt_le_S _ _ H1)); tauto
    end.
  Defined.

  Definition dec_star : {star P s} + {~ star P s}.
    refine (Reduce (dec_star' (n := length s) 0 _)); crush.
  Defined.
End dec_star.

Lemma app_cong : forall x1 y1 x2 y2,
  x1 = x2
  -> y1 = y2
  -> x1 ++ y1 = x2 ++ y2.
  congruence.
Qed.

Hint Resolve app_cong.

Definition matches : forall P (r : regexp P) s, {P s} + {~ P s}.
  refine (fix F P (r : regexp P) s : {P s} + {~ P s} :=
            match r with
            | Char ch => string_dec s (String ch "")
            | Concat _ _ r1 r2 => Reduce (split (F _ r1) (F _ r2) s)
            | Or _ _ r1 r2 => F _ r1 s || F _ r2 s
            | Star _ r => dec_star _ _ _
            end); crush;
    (* Not sure why crush fails to handle it, but without
       this extra eauto I can't discharge the goal

       - x1, x2 : string
       - H1 : P1 x1
       - H2 : P2 x2
         ============================
         exists s1 s2, x1 ++ x2 = s1 ++ s2 /\ P1 s1 /\ P2 s2
     *)
    eauto;
    match goal with
    | [H : _ |- _] => generalize (H _ _ (eq_refl _))
    end; tauto.
Defined.

Example a_star := Star (Char "a"%char).
Eval hnf in matches a_star "".
Eval hnf in matches a_star "a".
Eval hnf in matches a_star "b".
Eval hnf in matches a_star "aa".
