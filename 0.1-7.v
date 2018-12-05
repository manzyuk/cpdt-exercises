Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive btree (T : Set) : Set :=
| BTLeaf : btree T
| BTNode : btree T -> T -> btree T -> btree T.

Section btree_map.
  Variables A B : Set.
  Variable f : A -> B.

  Fixpoint btree_map (bt : btree A) : btree B :=
    match bt with
    | BTLeaf => BTLeaf B
    | BTNode bt1 a bt2 => BTNode (btree_map bt1) (f a) (btree_map bt2)
    end.
End btree_map.

Section btree_fold.
  Variable A B : Set.
  Variable leaf : B.
  Variable node : B -> A -> B -> B.

  Fixpoint btree_fold (bt : btree A) : B :=
    match bt with
    | BTLeaf => leaf
    | BTNode bt1 a bt2 => node (btree_fold bt1) a (btree_fold bt2)
    end.
End btree_fold.

Definition btree_sum (bt : btree nat) : nat :=
  btree_fold O (fun left x right => plus left (plus x right)) bt.

Section btree_all.
  Variable T : Set.
  Variable P : T -> Prop.
  Fixpoint btree_all (bt : btree T) : Prop :=
    match bt with
    | BTLeaf => True
    | BTNode bt1 x bt2 => btree_all bt1 /\ P x /\ btree_all bt2
    end.
End btree_all.

Inductive trexp : Set :=
| TEBase : nat -> trexp
| TETree : btree trexp -> trexp.

Fixpoint total (tr : trexp) : nat :=
  match tr with
  | TEBase n => n
  | TETree bt => btree_sum (btree_map total bt)
  end.

Fixpoint trexp_increment (tr : trexp) : trexp :=
  match tr with
  | TEBase n => TEBase (S n)
  | TETree bt => TETree (btree_map trexp_increment bt)
  end.

Lemma btree_map_compose :
  forall (A B C : Set) (f : A -> B) (g : B -> C) (bt : btree A),
    btree_map g (btree_map f bt) = btree_map (fun a => g (f a)) bt.
  induction bt; crush.
Qed.

Lemma plus_monotone : forall (n m n' m' : nat),
    n >= n' -> m >= m' -> plus n m >= plus n' m'.
  crush.
Qed.

Hint Resolve plus_monotone.

Lemma btree_fold_monotone :
  forall (A : Set) (f : A -> nat) (g : A -> nat) (bt : btree A),
    btree_all (fun a => f a >= g a) bt ->
    btree_sum (btree_map f bt) >= btree_sum (btree_map g bt).
  induction bt; crush.
Qed.

Section trexp_ind'.
  Variable P : trexp -> Prop.
  Hypothesis TEBase_case : forall n, P (TEBase n).
  Hypothesis TETree_case : forall (bt : btree trexp),
      btree_all P bt -> P (TETree bt).
  Fixpoint trexp_ind' (tr : trexp) : P tr :=
    match tr with
    | TEBase n => TEBase_case n
    | TETree bt =>
      TETree_case bt ((fix btree_ind (bt : btree trexp) : btree_all P bt :=
                         match bt with
                         | BTLeaf => I
                         | BTNode bt1 tr bt2 =>
                           conj (btree_ind bt1)
                                (conj (trexp_ind' tr) (btree_ind bt2))
                         end) bt)
    end.
End trexp_ind'.

Hint Rewrite btree_map_compose.
Hint Resolve btree_fold_monotone.

Theorem total_increment : forall (tr : trexp),
    total (trexp_increment tr) >= total tr.
  induction tr using trexp_ind'; crush.
Qed.
