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

Definition runAssign (x : var) (ov : option val) (k : env val -> option val) (vs : env val) :=
  match ov with
  | Some v => k (assign x v vs)
  | None => None
  end.

Fixpoint run (c : cmd) (vs : env val) : option val :=
  match c with
  | CExp e => eval e vs
  | CAssign x e c' => runAssign x (eval e vs) (fun vs => run c' vs) vs
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

Definition assignType (x : var) (ot : option type) (k : env type -> option type) (ts : env type) :=
  match ot with
  | Some t => k (assign x t ts)
  | None => None
  end.

Fixpoint cmdType (c : cmd) (ts : env type): option type :=
  match c with
  | CExp e => expType e ts
  | CAssign x e c' => assignType x (expType e ts) (fun ts => cmdType c' ts) ts
  end.

Fixpoint valType (v : val) : type :=
  match v with
  | VConst _ => TNat
  | VPair v1 v2 => TPair (valType v1) (valType v2)
  end.

Definition varsType (vs : env val) (ts : env type) :=
  forall x : var, valType (vs x) = ts x.

Lemma vars_type_assign : forall (vs : env val) (ts : env type) (x : var) (v : val) (t : type),
    varsType vs ts /\ valType v = t -> varsType (assign x v vs) (assign x t ts).
  intros. red. intro x'. destruct H as [Hvs_ts Hv_t].
  unfold assign. destruct (eq_nat_dec x x').
  assumption.
  red in Hvs_ts. apply (Hvs_ts x').
Qed.

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
  induction e as [n|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2|e IHe|e IHe|x].
  (* EConst n *)
  intros. exists (VConst n). crush.
  (* EAdd e1 e2 *)
  intros. destruct H as [Hadd_type Hvs]. simpl in Hadd_type.
  destruct (add_type_inversion (expType e1 ts) (expType e2 ts) Hadd_type)
    as [He1_type [He2_type Ht]].
  destruct (IHe1 TNat vs ts (conj He1_type Hvs)) as [v1 [He1_val Hv1]].
  destruct (IHe2 TNat vs ts (conj He2_type Hvs)) as [v2 [He2_val Hv2]].
  destruct v1 as [n1 | v11 v12].
  destruct v2 as [n2 | v21 v22].
  exists (VConst (plus n1 n2)). crush.
  simpl in Hv2. discriminate Hv2.
  simpl in Hv1. discriminate Hv1.
  (* EPair e1 e2 *)
  intros. destruct H as [Hpair_type Hvs]. simpl in Hpair_type.
  destruct (pair_type_inversion (expType e1 ts) (expType e2 ts) Hpair_type)
    as [t1 [t2 [He1_type [He2_type Ht]]]].
  destruct (IHe1 t1 vs ts (conj He1_type Hvs)) as [v1].
  destruct (IHe2 t2 vs ts (conj He2_type Hvs)) as [v2].
  exists (VPair v1 v2). crush.
  (* EFst e *)
  intros t1 vs ts H. destruct H as [Hfst_type Hvs]. simpl in Hfst_type.
  destruct (fst_type_inversion (expType e ts) Hfst_type) as [t2 He_type].
  destruct (IHe (TPair t1 t2) vs ts (conj He_type Hvs)) as [v [He_val Hv]].
  destruct v as [n |v1 v2].
  simpl in Hv. discriminate Hv.
  exists v1. crush.
  (* ESnd e *)
  intros t2 vs ts H. destruct H as [Hsnd_type Hvs]. simpl in Hsnd_type.
  destruct (snd_type_inversion (expType e ts) Hsnd_type) as [t1 He_type].
  destruct (IHe (TPair t1 t2) vs ts (conj He_type Hvs)) as [v [He_val Hv]].
  destruct v as [n |v1 v2].
  simpl in Hv. discriminate Hv.
  exists v2. crush.
  (* EVar v *)
  intros. exists (vs x). crush.
Qed.

Lemma assign_type_inversion :
  forall (x : var) (ot : option type) (k : env type -> option type) (ts : env type) (t : type),
    assignType x ot k ts = Some t ->
    exists t' : type, ot = Some t' /\ k (assign x t' ts) = Some t.
  intros. destruct ot as [t'|]. exists t'. crush.
  simpl in H. discriminate H.
Qed.

Theorem cmd_type_sound :
  forall (c : cmd) (t : type) (vs : env val) (ts : env type),
    cmdType c ts = Some t /\ varsType vs ts ->
    exists v : val, run c vs = Some v /\ valType v = t.
  induction c as [e|x e c].
  (* CExp e *)
  intros. simpl in H. destruct (exp_type_sound e H) as [v]. exists v. crush.
  (* CAssign v e c *)
  intros. destruct H as [Hassign_type Hvs]. simpl in Hassign_type.
  destruct (assign_type_inversion x (expType e ts) (fun ts => cmdType c ts) ts Hassign_type)
    as [t' [He_type Hc_type]].
  destruct (exp_type_sound e (conj He_type Hvs)) as [v' [He_val Hv']].
  set (Hvs' := vars_type_assign x v' (conj Hvs Hv')).
  destruct (IHc t (assign x v' vs) (assign x t' ts) (conj Hc_type Hvs')) as [v''].
  exists v''. crush.
Qed.
