Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive nat_binop := NPlus | NTimes.

Inductive bool_binop := BEq | BLt.

Definition var := nat.

Definition vars := var -> nat.

Inductive nat_exp : Set :=
| NConst : nat -> nat_exp
| NVar : var -> nat_exp
| NBinop : nat_binop -> nat_exp -> nat_exp -> nat_exp
| NIf : bool_exp -> nat_exp -> nat_exp -> nat_exp
with bool_exp : Set :=
| BConst : bool -> bool_exp
| BBinop : bool_binop -> nat_exp -> nat_exp -> bool_exp.

Definition nat_binop_denote (binop : nat_binop) : nat -> nat -> nat :=
  match binop with
  | NPlus => plus
  | NTimes => mult
  end.

Definition if_denote (b : bool) (n1 : nat) (n2 : nat) : nat :=
  if b then n1 else n2.

Definition bool_binop_denote (binop : bool_binop) : nat -> nat -> bool :=
  match binop with
  | BEq => beq_nat
  | BLt => leb
  end.

Fixpoint nat_exp_denote (vs : vars) (ne : nat_exp) : nat :=
  match ne with
  | NConst n => n
  | NVar v => vs v
  | NBinop binop ne1 ne2 =>
    nat_binop_denote
      binop
      (nat_exp_denote vs ne1)
      (nat_exp_denote vs ne2)
  | NIf be ne1 ne2 =>
    if_denote
      (bool_exp_denote vs be)
      (nat_exp_denote vs ne1)
      (nat_exp_denote vs ne2)
  end
with bool_exp_denote (vs : vars) (be : bool_exp) : bool :=
  match be with
  | BConst b => b
  | BBinop binop ne1 ne2 =>
    bool_binop_denote
      binop
      (nat_exp_denote vs ne1)
      (nat_exp_denote vs ne2)
  end.

Definition nat_binop_fold_consts (binop : nat_binop) (ne1 ne2 : nat_exp) : nat_exp :=
  match ne1, ne2 with
  | NConst n1, NConst n2 => NConst (nat_binop_denote binop n1 n2)
  | _, _ => NBinop binop ne1 ne2
  end.

Definition if_fold_consts (be : bool_exp) (ne1 ne2 : nat_exp) : nat_exp :=
  match be with
  | BConst b => if b then ne1 else ne2
  | _ => NIf be ne1 ne2
  end.

Definition bool_binop_fold_consts (binop : bool_binop) (ne1 ne2 : nat_exp) : bool_exp :=
  match ne1, ne2 with
  | NConst n1, NConst n2 => BConst (bool_binop_denote binop n1 n2)
  | _, _ => BBinop binop ne1 ne2
  end.

Fixpoint nat_exp_fold_consts (ne : nat_exp) : nat_exp :=
  match ne with
  | NBinop binop ne1 ne2 =>
    nat_binop_fold_consts
      binop
      (nat_exp_fold_consts ne1)
      (nat_exp_fold_consts ne2)
  | NIf be ne1 ne2 =>
    if_fold_consts
      (bool_exp_fold_consts be)
      (nat_exp_fold_consts ne1)
      (nat_exp_fold_consts ne2)
  | _ => ne
  end
with bool_exp_fold_consts (be : bool_exp) : bool_exp :=
  match be with
  | BBinop binop ne1 ne2 =>
    bool_binop_fold_consts
      binop
      (nat_exp_fold_consts ne1)
      (nat_exp_fold_consts ne2)
  | _ => be
  end.

Lemma nat_binop_fold_consts_preserves_meaning :
  forall (vs : vars) (binop : nat_binop) (ne1 ne2 : nat_exp),
    nat_exp_denote vs (nat_binop_fold_consts binop ne1 ne2) =
    nat_binop_denote binop (nat_exp_denote vs ne1) (nat_exp_denote vs ne2).
  destruct ne1; destruct ne2; crush.
Qed.

Lemma if_fold_consts_preserves_meaning :
  forall (vs : vars) (be : bool_exp) (ne1 ne2 : nat_exp),
    nat_exp_denote vs (if_fold_consts be ne1 ne2) =
    if_denote (bool_exp_denote vs be) (nat_exp_denote vs ne1) (nat_exp_denote vs ne2).
  destruct be; crush.
  destruct b; crush.
Qed.

Lemma bool_binop_fold_consts_preserves_meaning :
  forall (vs : vars) (binop : bool_binop) (ne1 ne2 : nat_exp),
    bool_exp_denote vs (bool_binop_fold_consts binop ne1 ne2) =
    bool_binop_denote binop (nat_exp_denote vs ne1) (nat_exp_denote vs ne2).
  destruct ne1; destruct ne2; crush.
Qed.

Hint Rewrite nat_binop_fold_consts_preserves_meaning.
Hint Rewrite if_fold_consts_preserves_meaning.
Hint Rewrite bool_binop_fold_consts_preserves_meaning.

Scheme nat_exp_mut := Induction for nat_exp Sort Prop
  with bool_exp_mut := Induction for bool_exp Sort Prop.

Check nat_exp_mut.

Theorem nat_exp_fold_consts_preserves_meaning : forall (ne : nat_exp) (vs : vars),
      nat_exp_denote vs (nat_exp_fold_consts ne) = nat_exp_denote vs ne.
  apply (nat_exp_mut
           (fun ne : nat_exp => forall (vs : vars),
                nat_exp_denote vs (nat_exp_fold_consts ne) = nat_exp_denote vs ne)
           (fun be : bool_exp => forall (vs : vars),
                bool_exp_denote vs (bool_exp_fold_consts be) = bool_exp_denote vs be)); crush.
Qed.
