Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Definition var := nat.

Inductive exp : Set :=
| EConst : nat -> exp
| EAdd : exp -> exp -> exp
| EPair : exp -> exp -> exp
| EFst : exp -> exp
| ESnd : exp -> exp
| EVar : var -> exp.

Inductive cmd : Set :=
| CExp : exp -> cmd
| CAssign : var -> exp -> cmd -> cmd.

Inductive val : Set :=
| VConst : nat -> val
| VPair : val -> val -> val.

Definition env (T : Set) := var -> T.

Definition evalAdd (ov1 : option val) (ov2 : option val) : option val :=
  match ov1, ov2 with
  | Some (VConst n1), Some (VConst n2) => Some (VConst (n1 + n2))
  | _, _ => None
  end.

Definition evalPair (ov1 : option val) (ov2 : option val) : option val :=
  match ov1, ov2 with
  | Some v1, Some v2 => Some (VPair v1 v2)
  | _, _ => None
  end.

Definition evalFst (ov : option val) : option val :=
  match ov with
  | Some (VPair v _) => Some v
  | _ => None
  end.

Definition evalSnd (ov : option val) : option val :=
  match ov with
  | Some (VPair _ v) => Some v
  | _ => None
  end.

Fixpoint eval (e : exp) (vs : env val) : option val :=
  match e with
  | EConst n => Some (VConst n)
  | EAdd e1 e2 => evalAdd (eval e1 vs) (eval e2 vs)
  | EPair e1 e2 => evalPair (eval e1 vs) (eval e2 vs)
  | EFst e => evalFst (eval e vs)
  | ESnd e => evalSnd (eval e vs)
  | EVar x => Some (vs x)
  end.

Definition assign (T : Set) (x : var) (t : T) (ts : env T) : env T :=
  fun x' => if eq_nat_dec x x' then t else ts x'.

Fixpoint run (c : cmd) (vs : env val) : option val :=
  match c with
  | CExp e => eval e vs
  | CAssign x e c' =>
    match eval e vs with
    | Some v => run c' (assign x v vs)
    | None => None
    end
  end.

Inductive type : Set :=
| TNat : type
| TPair : type -> type -> type.

Definition addType (ot1 : option type) (ot2 : option type) : option type :=
  match ot1, ot2 with
  | Some TNat, Some TNat => Some TNat
  | _, _ => None
  end.

Definition pairType (ot1 : option type) (ot2 : option type) : option type :=
  match ot1, ot2 with
  | Some t1, Some t2 => Some (TPair t1 t2)
  | _, _ => None
  end.

Definition fstType (ot : option type) : option type :=
  match ot with
  | Some (TPair t _) => Some t
  | _ => None
  end.

Definition sndType (ot : option type) : option type :=
  match ot with
  | Some (TPair _ t) => Some t
  | _ => None
  end.

Fixpoint expType (e : exp) (ts : env type) : option type :=
  match e with
  | EConst _ => Some TNat
  | EAdd e1 e2 => addType (expType e1 ts) (expType e2 ts)
  | EPair e1 e2 => pairType (expType e1 ts) (expType e2 ts)
  | EFst e => fstType (expType e ts)
  | ESnd e => sndType (expType e ts)
  | EVar x => Some (ts x)
  end.

Fixpoint cmdType (c : cmd) (ts : env type): option type :=
  match c with
  | CExp e => expType e ts
  | CAssign x e c' =>
    match expType e ts with
    | Some t => cmdType c' (assign x t ts)
    | _ => None
    end
  end.

Fixpoint valType (v : val) : type :=
  match v with
  | VConst _ => TNat
  | VPair v1 v2 => TPair (valType v1) (valType v2)
  end.

Definition varsType (vs : env val) (ts : env type) :=
  forall x : var, valType (vs x) = ts x.

Lemma add_type_inversion : forall (ot1 ot2 : option type) (t : type),
    addType ot1 ot2 = Some t -> ot1 = Some TNat /\ ot2 = Some TNat /\ t = TNat.
  intros; destruct ot1; destruct ot2;
    match goal with
      | [ H : addType (Some ?T1) (Some ?T2) = _ |- _ ] =>
        destruct T1; destruct T2
      | [ H : addType (Some ?T) None = _ |- _ ] =>
        destruct T
      | [ H : addType None (Some ?T) = _ |- _ ] =>
        destruct T
      | [ H : addType None None = _ |- _ ] =>
        simpl in H
    end; crush.
Qed.

Lemma pair_type_inversion : forall (ot1 ot2 : option type) (t : type),
    pairType ot1 ot2 = Some t ->
    exists t1 t2 : type, ot1 = Some t1 /\ ot2 = Some t2 /\ t = TPair t1 t2.
  intros; destruct ot1 as [t1|]; destruct ot2 as [t2|]; crush.
  exists t1. exists t2. auto.
Qed.

Lemma fst_type_inversion : forall (ot : option type) (t1 : type),
    fstType ot = Some t1 -> exists t2 : type, ot = Some (TPair t1 t2).
  intros. destruct ot as [t|].
  destruct t as [|t1' t2']; crush. exists t2'. auto.
  crush.
Qed.

Lemma snd_type_inversion : forall (ot : option type) (t2 : type),
    sndType ot = Some t2 -> exists t1 : type, ot = Some (TPair t1 t2).
  intros. destruct ot as [t|].
  destruct t as [|t1' t2']; crush. exists t1'. auto.
  crush.
Qed.

Theorem exp_type_sound :
  forall (e : exp) (t : type) (vs : env val) (ts : env type),
    expType e ts = Some t /\ varsType vs ts ->
    exists v : val, eval e vs = Some v /\ valType v = t.
  induction e.
  (* EConst n *)
  intros. exists (VConst n). crush.
  (* EAdd e1 e2 *)
  intros. destruct H as [Hadd_type Hvs].
  simpl in Hadd_type.
  set (H := add_type_inversion (expType e1 ts) (expType e2 ts) Hadd_type).
  destruct H as [He1_type [He2_type Ht]].
  set (H1 := IHe1 TNat vs ts (conj He1_type Hvs)).
  destruct H1 as [v1 [He1_val Hv1_type]].
  set (H2 := IHe2 TNat vs ts (conj He2_type Hvs)).
  destruct H2 as [v2 [He2_val Hv2_type]].
  destruct v1 as [n1 | v11 v12].
  destruct v2 as [n2 | v21 v22].
  exists (VConst (plus n1 n2)). crush.
  simpl in Hv2_type. discriminate Hv2_type.
  simpl in Hv1_type. discriminate Hv1_type.
  (* EPair e1 e2 *)
  intros. destruct H as [Hpair_type Hvs].
  simpl in Hpair_type.
  set (H := pair_type_inversion (expType e1 ts) (expType e2 ts) Hpair_type).
  destruct H as [t1 [t2 [He1_type [He2_type Ht]]]].
  set (H1 := IHe1 t1 vs ts (conj He1_type Hvs)).
  destruct H1 as [v1 [He1_val Hv1_type]].
  set (H2 := IHe2 t2 vs ts (conj He2_type Hvs)).
  destruct H2 as [v2 [He2_val Hv2_type]].
  exists (VPair v1 v2). crush.
  (* EFst e *)
  intros t1 vs ts H. destruct H as [Hfst_type Hvs].
  simpl in Hfst_type.
  set (H := fst_type_inversion (expType e ts) Hfst_type).
  destruct H as [t2 He_type].
  set (H := IHe (TPair t1 t2) vs ts (conj He_type Hvs)).
  destruct H as [v [He_val Hv_type]].
  destruct v as [n |v1 v2].
  simpl in Hv_type. discriminate Hv_type.
  exists v1. crush.
  (* ESnd e *)
  intros t2 vs ts H. destruct H as [Hsnd_type Hvs].
  simpl in Hsnd_type.
  set (H := snd_type_inversion (expType e ts) Hsnd_type).
  destruct H as [t1 He_type].
  set (H := IHe (TPair t1 t2) vs ts (conj He_type Hvs)).
  destruct H as [v [He_val Hv_type]].
  destruct v as [n |v1 v2].
  simpl in Hv_type. discriminate Hv_type.
  exists v2. crush.
