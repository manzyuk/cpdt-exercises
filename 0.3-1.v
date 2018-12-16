Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

CoInductive tree T :=
| Node : tree T -> T -> tree T -> tree T.

CoFixpoint everywhere T (x : T) : tree T :=
  Node (everywhere x) x (everywhere x).

CoFixpoint map A B C (f : A -> B -> C) (ta : tree A) (tb : tree B) :=
  match ta, tb with
  | Node la a ra, Node lb b rb => Node (map f la lb) (f a b) (map f ra rb)
  end.

Definition falses : tree bool := everywhere false.

CoFixpoint true_false : tree bool := Node false_true true false_true
with false_true : tree bool := Node true_false false true_false.

CoInductive tree_eq T : tree T -> tree T -> Prop :=
| Tree_eq : forall x l1 r1 l2 r2,
    tree_eq l1 l2 -> tree_eq r1 r2 -> tree_eq (Node l1 x r1) (Node l2 x r2).

Definition value T (t : tree T) : T :=
  match t with
  | Node _ x _ => x
  end.

Definition left T (t : tree T) : tree T :=
  match t with
  | Node l _ _ => l
  end.

Definition right T (t : tree T) : tree T :=
  match t with
  | Node _ _ r => r
  end.

Section tree_eq_coind.
  Variable T : Type.
  Variable R : tree T -> tree T -> Prop.

  Hypothesis Node_case_value : forall t1 t2, R t1 t2 -> value t1 = value t2.
  Hypothesis Node_case_left : forall t1 t2, R t1 t2 -> R (left t1) (left t2).
  Hypothesis Node_case_right : forall t1 t2, R t1 t2 -> R (right t1) (right t2).

  Theorem tree_eq_coind : forall t1 t2, R t1 t2 -> tree_eq t1 t2.
    cofix; destruct t1; destruct t2; intro.
    generalize (Node_case_value H); intro Heq; simpl in Heq; rewrite Heq.
    constructor; apply tree_eq_coind.
    apply (Node_case_left H).
    apply (Node_case_right H).
  Qed.
End tree_eq_coind.

Theorem true_false_eq : tree_eq true_false (map orb true_false falses).
  apply (tree_eq_coind (fun t1 t2 =>
                          (t1 = true_false /\ t2 = map orb true_false falses) \/
                          (t1 = false_true /\ t2 = map orb false_true falses))); crush.
Qed.
