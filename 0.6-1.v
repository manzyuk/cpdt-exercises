Require Import Arith List.
Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Section tree.
  Variable A : Type.

  Inductive tree : Type :=
  | Leaf : A -> tree
  | Node : tree -> tree -> tree.
End tree.


Section htree.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive htree : tree A -> Type :=
  | HLeaf : forall (x : A), B x -> htree (Leaf x)
  | HNode : forall l r, htree l -> htree r -> htree (Node l r).

  Variable elm : A.

  Inductive path : tree A -> Type :=
  | Finish : path (Leaf elm)
  | Left : forall l r, path l -> path (Node l r)
  | Right : forall l r, path r -> path (Node l r).

  Fixpoint tget t (ht : htree t) : path t -> B elm :=
    match ht with
    | HLeaf _ b => fun p =>
        match p in path t' return (match t' with
                                   | Leaf x => B x -> B elm
                                   | Node _ _ => unit
                                   end) with
        | Finish => fun b => b
        | Left _ _ _ => tt
        | Right _ _ _ => tt
        end b
    | HNode _ _ hl hr => fun p =>
        match p in path t' return (match t' with
                                   | Leaf _ => unit
                                   | Node l r => (path l -> B elm) -> (path r -> B elm) -> B elm
                                   end) with
        | Finish => tt
        | Left _ _ p' => fun tget_l _ => tget_l p'
        | Right _ _ p' => fun _ tget_r => tget_r p'
        end (tget hl) (tget hr)
    end.
End htree.

Implicit Arguments HLeaf [A B x].
Implicit Arguments HNode [A B l r].
Implicit Arguments Finish [A elm].
Implicit Arguments Left [A elm l r].
Implicit Arguments Right [A elm l r].

Example someTypes : tree Set :=
  Node (Node (Leaf nat) (Leaf unit)) (Leaf bool).
Example someValues : htree (fun T : Set => T) someTypes :=
  HNode (HNode (HLeaf 42) (HLeaf tt)) (HLeaf true).

Eval simpl in tget someValues (Right Finish).
Eval simpl in tget someValues (Left (Right Finish)).
Eval simpl in tget someValues (Left (Left Finish)).
