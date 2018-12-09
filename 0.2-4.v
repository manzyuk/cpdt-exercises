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

Theorem exp_type_sound :
  forall (e : exp) (t : type) (vs : env val) (ts : env type),
    expType e ts = Some t /\ varsType vs ts ->
    exists v : val, eval e vs = Some v /\ valType v = t.
