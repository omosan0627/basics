Require Import List.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Inductive type: Type :=
    | TVar: nat -> type
    | Func: type -> type -> type
    | Forall: type -> type.

Inductive term : Type :=
    | O: term
    | Succ: term -> term
    | Abst: type -> term -> term
    | App: term -> term -> term
    | Var: nat -> term
    | TAbst: term -> term
    | TApp: term -> type -> term.

Notation "t [ T ] " := (TApp t) (at level 62).
Notation "'Λ' t " := (TAbst t) (at level 61).
Notation "'λ' T , t " := (Abst T t) (at level 60, T at level 99).
Notation "t1 ◦ t2" := (App t1 t2) (at level 59, left associativity).

Inductive nvalue: term -> Prop :=
    | nv_O: nvalue O
    | nv_Succ: forall nv, nvalue nv -> nvalue (Succ nv).

Inductive value: term -> Prop :=
    | v_nvalue: forall nv, nvalue nv -> value nv
    | v_Abst: forall T t, value (λ T , t)
    | v_TAbst: forall t, value (Λ t).


Inductive eval_step: term -> term -> Prop :=
    | EApp1: forall t1 t1' t2, eval_step t1 t1' -> eval_step (t1 ◦ t2) (t1' ◦ t2)
    | EApp2: forall v1 t2 t2', value v1 -> eval_step t2 t2' -> eval_step (v1 ◦ t2) (v1 ◦ t2').
    | EAppAbs: forall T t12 v2, value v2 ->
    eval_step ((λ T , t12) ◦ v2) (reverse_shift 0 ([ 0 |→ shift 0 1 v2 ] t12)).

Inductive type_step: list type -> term -> type -> Prop :=
    | TVar: forall k T Γ, get_var_type k Γ = Some T -> type_step Γ (Var k) T
    | TAbs: forall T1 Γ t2 T2, type_step (T1 :: Γ) t2 T2
    -> type_step Γ (λ T1 , t2) (T1 → T2)
    | TApp: forall Γ t1 T11 T12 t2, type_step Γ t1 (T11 → T12) -> type_step Γ t2 T11
    -> type_step Γ (t1 ◦ t2) T12.


(* No Symbol *)
