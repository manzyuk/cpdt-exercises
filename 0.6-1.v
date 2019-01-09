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

(* Inductive *)

Section htree.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive htree : tree A -> Type :=
  | HLeaf : forall (x : A), B x -> htree (Leaf x)
  | HNode : forall l r, htree l -> htree r -> htree (Node l r).

  Variable elm : A.

  Inductive path : tree A -> Type :=
  | Stop : path (Leaf elm)
  | Left : forall l r, path l -> path (Node l r)
  | Right : forall l r, path r -> path (Node l r).

  Fixpoint tget t (ht : htree t) : path t -> B elm :=
    match ht with
    | HLeaf _ b => fun p =>
        match p in path t' return (match t' with
                                   | Leaf x => B x -> B elm
                                   | Node _ _ => unit
                                   end) with
        | Stop => fun b => b
        | Left _ _ _ => tt
        | Right _ _ _ => tt
        end b
    | HNode _ _ hl hr => fun p =>
        match p in path t' return (match t' with
                                   | Leaf _ => unit
                                   | Node l r => (path l -> B elm) -> (path r -> B elm) -> B elm
                                   end) with
        | Stop => tt
        | Left _ _ p' => fun tget_l _ => tget_l p'
        | Right _ _ p' => fun _ tget_r => tget_r p'
        end (tget hl) (tget hr)
    end.
End htree.

Implicit Arguments HLeaf [A B x].
Implicit Arguments HNode [A B l r].
Implicit Arguments Stop [A elm].
Implicit Arguments Left [A elm l r].
Implicit Arguments Right [A elm l r].

Example someTypes : tree Set :=
  Node (Node (Leaf nat) (Leaf unit)) (Leaf bool).
Example someValues : htree (fun T : Set => T) someTypes :=
  HNode (HNode (HLeaf 42) (HLeaf tt)) (HLeaf true).

Eval simpl in tget someValues (Right Stop).
Eval simpl in tget someValues (Left (Right Stop)).
Eval simpl in tget someValues (Left (Left Stop)).

Section htmap2.
  Variable A : Type.
  Variables B1 B2 C : A -> Type.
  Variable f : forall x, B1 x -> B2 x -> C x.

  Fixpoint htmap2 t (ht1 : htree B1 t) (ht2 : htree B2 t) : htree C t :=
    match ht1 in htree _ t return htree _ t -> htree _ t with
    | HLeaf x b1 => fun ht2 =>
      match ht2
            in htree _ t'
            return
            match t' with
            | Leaf x' => B1 x' -> htree _ t'
            | Node _ _ => B1 x -> unit
            end
      with
      | HLeaf _ b2 => fun b1 => HLeaf (f b1 b2)
      | HNode _ _ _ _ => fun _ => tt
      end b1
    | HNode l r hl1 hr1 => fun ht2 =>
      match ht2
            in htree _ t'
            return
            match t' with
            | Leaf _ =>
              (htree B2 l -> htree C l) ->
              (htree B2 r -> htree C r) ->
              unit
            | Node l r =>
              (htree B2 l -> htree C l) ->
              (htree B2 r -> htree C r) ->
              htree C (Node l r)
            end
      with
      | HLeaf _ _ => fun _ _ => tt
      | HNode _ _ hl2 hr2 =>
        fun htmap2_l htmap2_r => HNode (htmap2_l hl2) (htmap2_r hr2)
      end (htmap2 hl1) (htmap2 hr1)
    end ht2.
End htmap2.

(* Recursive *)

Section fhtree.
  Variable A : Type.
  Variable B : A -> Type.

  Fixpoint fhtree (t : tree A) : Type :=
    match t with
    | Leaf x => B x
    | Node l r => fhtree l * fhtree r
    end%type.

  Variable elm : A.

  Fixpoint fpath (t : tree A) : Type :=
    match t with
    | Leaf x => x = elm
    | Node l r => fpath l + fpath r
    end%type.

  Fixpoint ftget (t : tree A) : fhtree t -> fpath t -> B elm :=
    match t with
    | Leaf x => fun b p =>
      match p with eq_refl => b end
    | Node l r => fun b p =>
      match p with
      | inl p' => ftget l (fst b) p'
      | inr p' => ftget r (snd b) p'
      end
    end.
End fhtree.

Section fhtmap2.
  Variable A : Type.
  Variables B1 B2 C : A -> Type.
  Variable f : forall x, B1 x -> B2 x -> C x.

  Fixpoint fhtmap2 (t : tree A) : fhtree B1 t -> fhtree B2 t -> fhtree C t :=
    match t with
    | Leaf x => fun b1 b2 => f b1 b2
    | Node l r => fun ht1 ht2 =>
      (fhtmap2 l (fst ht1) (fst ht2), fhtmap2 r (snd ht1) (snd ht2))
    end.
End fhtmap2.

(* Index Function *)

Section fhtree'.
  Variable A : Type.
  Variable B : A -> Type.

  Definition fhtree' (t : tree A) := forall elm, fpath elm t -> B elm.
  Variable elm : A.

  Definition ftget' (t : tree A) : fhtree' t -> fpath elm t -> B elm :=
    fun f p => f elm p.
End fhtree'.

Section fhtmap2'.
  Variable A : Type.
  Variables B1 B2 C : A -> Type.
  Variable f : forall x, B1 x -> B2 x -> C x.

  Definition fhtmap2' (t : tree A) : fhtree' B1 t -> fhtree' B2 t -> fhtree' C t :=
    fun f1 f2 => fun elm p => f (f1 elm p) (f2 elm p).
End fhtmap2'.
