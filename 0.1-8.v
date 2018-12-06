Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Definition is_leaf (t : nat_btree) : Prop :=
  match t with
  | NLeaf => True
  | NNode _ _ _ => False
  end.

Theorem leaf_neq_node : forall (n : nat) (l r : nat_btree), NLeaf <> NNode l n r.
  intros.
  red.
  intro H.
  change (is_leaf (NNode l n r)).
  rewrite <- H.
  simpl.
  trivial.
Qed.

Definition node_number (t : nat_btree) : nat :=
  match t with
  | NLeaf => O
  | NNode _ n _ => n
  end.

Theorem node_inj : forall (n1 n2 : nat) (l1 r1 l2 r2 : nat_btree),
    NNode l1 n1 r1 = NNode l2 n2 r2 -> n1 = n2.
  intros n1 n2 l1 r1 l2 r2 H.
  change (node_number (NNode l1 n1 r1) = node_number (NNode l2 n2 r2)).
  rewrite H.
  reflexivity.
Qed.
