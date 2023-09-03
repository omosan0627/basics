Require Import List.
Require Import Nat.

Inductive symbol : Type := 
| Symb: nat -> symbol.

Fixpoint eq_nat (n:nat) (m:nat) : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

Definition eq_symbol (x: symbol) (y: symbol): bool :=
    match x, y with
    | Symb v, Symb w => eq_nat v w
    end.

Definition succ_symbol (x: symbol): symbol :=
    match x with
    | Symb v => Symb (S v)
    end.

Inductive term : Type :=
  | Var: symbol -> term
  | Abst: symbol -> term -> term
  | App: term -> term -> term.

Inductive index: Type :=
  | IndVar: nat -> index
  | IndAbst: index -> index
  | IndApp: index -> index -> index.

Definition VA: symbol := Symb 0.
Definition VB: symbol := Symb 1.
Definition VC: symbol := Symb 2.
Definition VD: symbol := Symb 3.
Definition VE: symbol := Symb 4.

Definition tru: term := Abst VA (Abst VB (Var VA)).
Definition fls: term := Abst VA (Abst VB (Var VB)).
Definition test: term := Abst VA (Abst VB (Abst VC (App (App (Var VA) (Var VB)) (Var VD)))).


Fixpoint symbol_find (l: list symbol) (v: nat): nat :=
  match l with
  | nil => v
  | t :: l => if eq_symbol (Symb v) t then 0 else (S (symbol_find l v))
  end.

Fixpoint to_index (t:term) (l: list symbol) : index :=
  match t with
  | Var (Symb v) => IndVar (symbol_find l v)
  | Abst x t => IndAbst (to_index t (x :: l))
  | App t1 t2 => IndApp (to_index t1 l) (to_index t2 l)
  end.

Fixpoint is_free_var (x: symbol) (t:term): bool :=
  match t with
  | Var y => eq_symbol x y
  | Abst y t1 => if eq_symbol x y then false else is_free_var x t1
  | App t1 t2 => is_free_var x t1 || is_free_var x t2
  end.

Definition is_false (b:bool): bool :=
  match b with
  | true => false
  | false => true
  end.

Fixpoint subst (x: symbol) (s:term) (t: term): option term :=
match t with
| Var y => if eq_symbol x y then Some s else Some (Var y)
| Abst y t1 => if eq_symbol x y then Some (Abst y t1) else if 
  is_false (is_free_var y s) then (match (subst x s t1) with 
  | None => None
  | Some t1' => Some (Abst y t1')
  end
  ) else None
| App t1 t2 => (match (subst x s t1), (subst x s t2) with
  | None, _ => None
  | _, None => None
  | Some t1', Some t2' => Some (App t1' t2')
end
)
end.

Inductive value: term -> Prop :=
  | v_Abst: forall x t1, value (Abst x t1).

Inductive term_step: term -> term -> Prop :=
  | EApp1: forall t1 t1' t2, term_step t1 t1' -> term_step (App t1 t2) (App t1' t2)
  | EApp2: forall v1 t2 t2', value v1 -> term_step t2 t2' -> term_step (App v1 t2) (App v1 t2')
  | EAppAbs: forall x t12 v2 s, value v2 -> subst x v2 t12 = Some s ->
    term_step (App (Abst x t12) v2) s.

Inductive index_step: index -> index -> Prop :=
  | TermRev: forall i1 i2, (exists t1 t2, (to_index t1 nil) = i1 /\ (to_index t2 nil) = i2 /\ term_step t1 t2) 
  -> index_step i1 i2.

Fixpoint eval (t:term): term :=
  match t with
  | App t1 t2 => (
    match t1 with
    | Abst x t12 => (
      match t2 with
      | Abst _ _ => (
        match subst x t2 t12 with
        | None => Var (Symb 1919)
        | Some s => s
        end
      )
      | _ => App t1 (eval t2)
      end
    )
    | _ => App (eval t1) t2
    end
  )
  | _ => Var (Symb 1919)
  end.

Lemma step_match_eval: forall t1 t2, term_step t1 t2 -> t2 = eval t1.
intros. induction H. 
subst. destruct t1. inversion H. inversion H. simpl. reflexivity.
subst. inversion H. destruct t2. inversion H0. inversion H0. simpl. reflexivity.
simpl. inversion H. subst. remember (subst x (Abst x0 t1) t12) as tt. revert Heqtt. subst. 
intros. reflexivity. Qed.

(* d: None-> means -1 *)
Fixpoint shift (t: index) (d: option nat) (c: nat): index :=
match t with
| IndVar k => if (k <? c) then IndVar k else
  (match d with
  | Some d' => IndVar (k + d')
  | None => IndVar (pred k)
  end)
| IndAbst t1 => IndAbst (shift t1 d (S c))
| IndApp t1 t2 => IndApp (shift t1 d c) (shift t2 d c)
end.

Fixpoint index_subst (j: nat) (s:index) (t: index): index :=
  match t with
  | IndVar k => if k =? j then s else IndVar k
  | IndAbst t1 => IndAbst (index_subst (S j) (shift s (Some 1) 0) t1)
  | IndApp t1 t2 => IndApp (index_subst j s t1) (index_subst j s t2)
  end.

Inductive index_value: index -> Prop :=
  | iv_Abst: forall t1, index_value (IndAbst t1).

Inductive shift_step: index -> index -> Prop :=
  | IEApp1: forall i1 i1' i2, shift_step i1 i1' -> shift_step (IndApp i1 i2) (IndApp i1' i2)
  | IEApp2: forall v1 i2 i2', index_value v1 -> shift_step i2 i2' -> shift_step (IndApp v1 i2) (IndApp v1 i2')
  | IEAppAbs: forall i12 v2, index_value v2 -> 
  shift_step (IndApp (IndAbst i12) v2) (shift (index_subst 0 (shift v2 (Some 1) 0) i12) None 0).

Theorem index_equals_shift: forall i1 i2, shift_step i1 i2 <-> index_step i1 i2.
intros. split. intros. apply TermRev. induction H.  destruct IHshift_step. destruct H0.
admit. admit. destruct H. generalize dependent t1. induction i12. intros. admit.
intros. admit. admit. intros. destruct H. destruct H. destruct H.  destruct H.
destruct H0.

Fixpoint max_symbol_impl (t: term): nat :=
    match t with
    | Var (Symb v) => v
    | Abst (Symb v) t => max v (max_symbol_impl t)
    | App t1 t2 => max (max_symbol_impl t1) (max_symbol_impl t2)
    end.

Definition max_symbol (t:term): symbol := Symb (max_symbol_impl t).

(* [x \mapsto s] t. If it need alpha trans, return None*)



Inductive equiv: term -> term -> Prop :=
| EqVar: forall x, equiv (Var x) (Var x)
| EqAbst: forall x y t1, is_free_var y t1 = false -> equiv (Abst x t1) (Abst y (subst x (Var y) t1))
| EqApp: forall t1 t1' t2 t2', equiv t1 t1' -> equiv t2 t2' -> equiv (App t1 t2) (App t1' t2').


Eval compute in App (App (App test fls) (Abst VD (Var VD))) (Abst VE (Var VE)).