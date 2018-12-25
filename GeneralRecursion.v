Require Import Bool Arith List Omega Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.
Require Import Extraction.

(* Well-Founded Recursion *)

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons: A -> stream -> stream.
End stream.

CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) : stream A -> Prop :=
| ChainCons : forall x y s,
    infiniteDecreasingChain R (Cons y s)
    -> R y x
    -> infiniteDecreasingChain R (Cons x (Cons y s)).

Lemma noBadChains' : forall A (R : A -> A -> Prop) x,
    Acc R x -> forall s, ~ infiniteDecreasingChain R (Cons x s).
  induction 1; crush;
    match goal with
    | [H : infiniteDecreasingChain _ _ |- _] => inversion H; eauto
    end.
Qed.

Theorem noBadChains : forall A (R : A -> A -> Prop),
    well_founded R -> forall s, ~ infiniteDecreasingChain R s.
  destruct s; apply noBadChains'; auto.
Qed.

Check Fix.

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
    | nil => x :: nil
    | h :: ls' =>
      if le x h
      then x :: ls
      else h :: insert x ls'
    end.

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
    | nil => ls2
    | h :: ls' => insert h (merge ls' ls2)
    end.

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil, nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
      (h1 :: ls1, h2 :: ls2)
    end.

  Definition lengthOrder (ls1 ls2 : list A) : Prop :=
    length ls1 < length ls2.

  Hint Constructors Acc.

  Lemma lengthOrder_wf' :
    forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red; intro; eapply lengthOrder_wf'; eauto.
  Defined.

  Lemma split_wf : forall len ls,
      2 <= length ls <= len ->
      let (ls1, ls2) := split ls in
      lengthOrder ls1 ls /\ lengthOrder ls2 ls.
    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
    destruct (le_lt_dec 2 (length ls));
    repeat (match goal with
            | [_ : length ?E < 2 |- _] => destruct E
            | [_ : S (length ?E) < 2 |- _] => destruct E
            | [IH : _ |- context[split ?L]] =>
              specialize (IH L); destruct (split L); destruct IH
            end; crush).
  Defined.

  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls); destruct (split ls); destruct 1; crush.

  Lemma split_wf1 : forall ls,
      2 <= length ls -> lengthOrder (fst (split ls)) ls.
    split_wf.
  Defined.

  Lemma split_wf2 : forall ls,
      2 <= length ls -> lengthOrder (snd (split ls)) ls.
    split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2.

  Definition mergeSort : list A -> list A.
    refine (Fix lengthOrder_wf (fun _ => list A)
                (fun (ls : list A)
                     (mergeSort : forall ls' : list A, lengthOrder ls' ls -> list A) =>
                   if le_lt_dec 2 (length ls)
                   then let lss := split ls in
                        merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
                   else  ls)); subst lss; crush.
  Defined.
End mergeSort.

Eval compute in mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).

Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls,
    mergeSort le ls = if le_lt_dec 2 (length ls)
                      then let lss := split ls in
                           merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
                      else ls.
  intros. apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)); intros.
  match goal with
  | [|- context[match ?E with left _ => _ | right _ => _ end]] =>
    destruct E
  end; simpl; f_equal; auto.
Qed.

Extraction mergeSort.

Check well_founded_induction.

(* A Non-Termination Monad Inspired by Domain Theory *)

Section computation.
  Variable A : Type.

  Definition computation :=
    {f : nat -> option A
    | forall (n : nat) (v : A),
        f n = Some v
        -> forall (n' : nat), n' >= n -> f n' = Some v}.

  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
End computation.

Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] => rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run'; repeat (match goal with
                            | [ H : forall n v, ?E n = Some v -> _
                                |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
                              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
                          end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
  exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Theorem max_spec_le : forall n m, n <= m /\ max n m = m \/ m <= n /\ max n m = n.
  induction n; destruct m; simpl; intuition;
    specialize (IHn m); intuition.
Qed.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.

Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    exists (fun _ : nat => @None A); abstract run.
  Defined.

  Theorem run_Bottom : forall v, ~ run Bottom v.
    run.
  Qed.
End Bottom.

Section Return.
  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
    exists (fun _ : nat => Some v); abstract run.
  Defined.

  Theorem run_Return : run Return v.
    run.
  Qed.
End Return.

Section Bind.
  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
    exists (fun n =>
              let (f1, _) := m1 in
              match f1 n with
              | None => None
              | Some v =>
                let (f2, _) := m2 v in
                f2 n
              end); abstract run.
  Defined.

  Theorem run_Bind : forall (v1 : A) (v2 : B),
      run m1 v1 -> run (m2 v1) v2 -> run Bind v2.
    run; match goal with
         | [x : nat, y : nat |- _] => exists (max x y)
         end; run.
  Qed.
End Bind.

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

Definition meq A (m1 m2 : computation A) :=
  forall n, proj1_sig m1 n = proj1_sig m2 n.

Theorem left_identity : forall A B (a : A) (f : A -> computation B),
    meq (Bind (Return a) f) (f a).
  run.
Qed.

Theorem right_identity : forall A (m : computation A),
    meq (Bind m (@Return _)) m.
  run.
Qed.

Theorem associativity :
  forall A B C
         (m : computation A)
         (f : A -> computation B)
         (g : B -> computation C),
    meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
  run.
Qed.

Section lattice.
  Variable A : Type.

  Definition leq (x y : option A) :=
    forall v, x = Some v -> y = Some v.
End lattice.

Section Fix.
  Variables A B : Type.
  Variable f : (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous : forall n v v1 x,
      runTo (f v1 x) n v
      -> forall (v2 : A -> computation B),
        (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n))
        -> runTo (f v2 x) n v.

  Fixpoint Fix' (n : nat) (x : A) : computation B :=
    match n with
    | O => Bottom _
    | S n' => f (Fix' n') x
    end.

  Hint Extern 1 (_ >= _) => omega.
  Hint Unfold leq.

  Lemma Fix'_ok : forall steps n x v,
      proj1_sig (Fix' n x) steps = Some v
      -> forall n', n' >= n
                    -> proj1_sig (Fix' n' x) steps = Some v.
    unfold runTo in *; induction n; crush;
      match goal with
      | [H : _ >= _ |- _] => inversion H; crush; eauto
      end.
  Qed.

  Hint Resolve Fix'_ok.
  Hint Extern 1 (proj1_sig _ _ = _) =>
  simpl; match goal with
         | [|- proj1_sig ?E _ = _] => eapply (proj2_sig E)
         end.

  Definition Fix : A -> computation B.
    intro x; exists (fun n => proj1_sig (Fix' n x) n); abstract run.
  Defined.

  Theorem run_Fix : forall x v,
      run (f Fix x) v -> run (Fix x) v.
    run; match goal with
         | [n : nat |- _] => exists (S n); eauto
         end.
  Qed.
End Fix.

Lemma leq_Some : forall A (x y : A), leq (Some x) (Some y)
  -> x = y.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Lemma leq_None : forall A (x y : A), leq (Some x) None
  -> False.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Ltac mergeSort' := run;
  repeat (match goal with
            | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
          end; run);
  repeat match goal with
           | [ H : forall x, leq (proj1_sig (?f x) _) (proj1_sig (?g x) _) |- _ ] =>
             match goal with
               | [ H1 : f ?arg = _, H2 : g ?arg = _ |- _ ] =>
                 generalize (H arg); rewrite H1; rewrite H2; clear H1 H2; simpl; intro
             end
         end; run; repeat match goal with
                            | [ H : _ |- _ ] => (apply leq_None in H; tauto) || (apply leq_Some in H; subst)
                          end; auto.

Definition mergeSort' : forall A, (A -> A -> bool) -> list A -> computation (list A).
  refine (fun A le => Fix
    (fun (mergeSort : list A -> computation (list A))
         (ls : list A) =>
       if le_lt_dec 2 (length ls)
       then let lss := split ls in
            ls1 <- mergeSort (fst lss);
            ls2 <- mergeSort (snd lss);
            Return (merge le ls1 ls2)
       else Return ls) _); abstract mergeSort'.
Defined.

Lemma test_mergeSort' : run (mergeSort' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil)) (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  exists 4; reflexivity.
Qed.

Ltac looper := unfold leq in *; run;
  repeat match goal with
           | [ x : unit |- _ ] => destruct x
           | [ x : bool |- _ ] => destruct x
         end; auto.

Definition looper : bool -> computation unit.
  refine (Fix (fun looper (b : bool) =>
                 if b then Return tt else looper b) _); abstract looper.
Defined.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.

(* Co-Inductive Non-Termination Monads *)

CoInductive thunk (A : Type) : Type :=
| Answer : A -> thunk A
| Think : thunk A -> thunk A.

CoFixpoint TBind A B (m1 : thunk A) (m2 : A -> thunk B) : thunk B :=
  match m1 with
  | Answer x => m2 x
  | Think m1' => Think (TBind m1' m2)
  end.

Definition frob A (m : thunk A) : thunk A :=
  match m with
  | Answer x => Answer x
  | Think m' => Think m'
  end.

Theorem frob_eq : forall A (m : thunk A), frob m = m.
  destruct m; reflexivity.
Qed.

CoFixpoint fact (n acc : nat) : thunk nat :=
  match n with
  | O => Answer acc
  | S n' => Think (fact n' (S n' * acc))
  end.

Inductive eval A : thunk A -> A -> Prop :=
| EvalAnswer : forall x, eval (Answer x) x
| EvalThink : forall m x, eval m x -> eval (Think m) x.

Hint Rewrite frob_eq.

Lemma eval_frob : forall A (c : thunk A) x,
    eval (frob c) x -> eval c x.
  crush.
Qed.

Theorem eval_fact : eval (fact 5 1) 120.
  repeat (apply eval_frob; simpl; constructor).
Qed.

Notation "x <- m1 ; m2" :=
  (TBind m1 (fun x => m2)) (right associativity, at level 70).

(*
CoFixpoint fib (n : nat) : thunk nat :=
  match n with
  | 0 => Answer 1
  | 1 => Answer 1
  | _ =>
    n1 <- fib (pred n);
    n2 <- fib (pred (pred n));
    Answer (n1 + n2)
  end.
 *)

CoInductive comp (A : Type) : Type :=
| Ret : A -> comp A
| Bnd : forall B, comp B -> (B -> comp A) -> comp A.

Inductive exec A : comp A -> A -> Prop :=
| ExecRet : forall x, exec (Ret x) x
| ExecBnd : forall B (c : comp B) (f : B -> comp A) x1 x2,
    exec (A := B) c x1 -> exec (f x1) x2 -> exec (Bnd c f) x2.

Notation "x <- m1 ; m2" := (Bnd m1 (fun x => m2)).

CoFixpoint mergeSort'' A (le : A -> A -> bool) (ls : list A) : comp (list A) :=
  if le_lt_dec 2 (length ls)
  then let lss := split ls in
       ls1 <- mergeSort'' le (fst lss);
       ls2 <- mergeSort'' le (snd lss);
       Ret (merge le ls1 ls2)
  else Ret ls.

Definition frob' A (c : comp A) :=
  match c with
  | Ret x => Ret x
  | Bnd _ c' f => Bnd c' f
  end.

Lemma exec_frob : forall A (c : comp A) x,
    exec (frob' c) x -> exec c x.
  destruct c; crush.
Qed.

Lemma test_mergeSort'' : exec (mergeSort'' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil)) (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  repeat (apply exec_frob; simpl; econstructor).
Qed.
