Require Import List.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Inductive type: Type :=
    | Bool: type
    | Func: type -> type -> type.

Inductive symbol : Type := 
    | Symb: nat -> symbol.

Inductive term : Type :=
    | True: term
    | False: term
    | IfThenElse: term -> term-> term-> term
    | Var: symbol -> term
    | Abst: symbol -> type -> term -> term
    | App: term -> term -> term.

Notation "'If' A 'Then' B 'Else' C" := (IfThenElse A B C) (at level 57, A at level 99, B at level 99).

Notation "'λ' x : T , t " := (Abst x T t) (at level 60, x at level 99, T at level 99).

Notation "t1 ◦ t2" := (App t1 t2) (at level 59, left associativity).

Inductive value: term -> Prop :=
  | v_Abst: forall x T t, value (λ x : T , t).

Notation "A → B" := (Func A B) (at level 58, right associativity).

Definition eq_symbol (x: symbol) (y: symbol): bool :=
    match x, y with
    | Symb v, Symb w => v =? w
    end.

Lemma eq_symbol_refl: forall x, eq_symbol x x = true.
destruct x. apply Nat.eqb_refl. Qed.

Fixpoint FV (x: symbol) (t:term): bool :=
  match t with
  | Var y => eq_symbol x y
  | λ y : T , t1 => if eq_symbol x y then false else FV x t1
  | App t1 t2 => FV x t1 || FV x t2
  | If t1 Then t2 Else t3 => FV x t1 || FV x t2 || FV x t3
  | _ => true
  end.

Fixpoint subst (x: symbol) (s:term) (t: term): option term :=
match t with
| Var y => if eq_symbol x y then Some s else Some (Var y)
| λ y : T , t1 => if eq_symbol x y then Some (Abst y T t1) else if 
  Bool.eqb (FV y s) false then (match (subst x s t1) with 
  | None => None
  | Some t1' => Some (Abst y T t1')
  end
  ) else None
| App t1 t2 => (match (subst x s t1), (subst x s t2) with
  | None, _ => None
  | _, None => None
  | Some t1', Some t2' => Some (App t1' t2')
end)
| If t1 Then t2 Else t3 => (match (subst x s t1), (subst x s t2), (subst x s t3) with
  | None, _, _ => None
  | _, None, _ => None
  | _, _, None => None
  | Some t1', Some t2', Some t3' => Some (If t1' Then t2' Else t3')
end)
| b => Some b
end.

Notation "[ x |→ v2 ] t1" := (subst x v2 t1) (at level 61, x at level 99, v2 at level 99).

Inductive term_step: term -> term -> Prop :=
    | EIfTrue: forall t2 t3, term_step (If True Then t2 Else t3) t2
    | EIfFalse: forall t2 t3, term_step (If False Then t2 Else t3) t3
    | EIf: forall t1 t1' t2 t3, (term_step t1 t1') 
    -> (term_step (If t1 Then t2 Else t3) (If t1' Then t2 Else t3))
    | EApp1: forall t1 t1' t2, term_step t1 t1' -> term_step (App t1 t2) (App t1' t2)
    | EApp2: forall v1 t2 t2', value v1 -> term_step t2 t2' -> term_step (App v1 t2) (App v1 t2')
    | EAppAbs: forall x T t12 v2 s, value v2 -> [x |→ v2] t12 = Some s ->
    term_step ((λ x : T , t12) ◦ v2) s.

Notation "t1 -→ t2" := (term_step t1 t2) (at level 61).

Notation "{ x : T }" := (x, T) (x at level 99).

Fixpoint get_var_type (x: symbol) (Γ: list (symbol * type)): option type :=
    match Γ with
    | nil => None
    | { y : T } :: Γ' => if eq_symbol x y then Some T else get_var_type x Γ'
    end.

Inductive type_step: list (symbol * type) -> term -> type -> Prop :=
    | TTrue: forall Γ, type_step Γ True Bool
    | TFalse: forall Γ, type_step Γ False Bool
    | TIf: forall Γ t1 t2 t3 T, type_step Γ t1 Bool -> type_step Γ t2 T -> type_step Γ t3 T
    -> type_step Γ (If t1 Then t2 Else t3) T
    | TVar: forall x T Γ, get_var_type x Γ = Some T -> type_step Γ (Var x) T
    | TAbs: forall x T1 Γ t2 T2, type_step ( {x : T1} :: Γ) t2 T2
    -> type_step Γ (λ x : T1 , t2) (T1 → T2)
    | TApp: forall Γ t1 T11 T12 t2, type_step Γ t1 (T11 → T12) -> type_step Γ t2 T11
    -> type_step Γ (t1 ◦ t2) T12.

Notation "Γ |- t : T" := (type_step Γ t T) (at level 61, t at level 99).

Theorem just_testing_notations: forall x t1 t Γ, 
    [x |→ (λ x : (Bool → Bool) , If (Var x) Then t ◦ t Else t ◦ (Var x) ◦ (Var x))] t1 = Some t ->
((x, Bool → Bool → Bool) :: Γ) |- λ x : (Bool → Bool) , t : (Bool → Bool → Bool).
Admitted.

Lemma ex9_2_2_1: forall f, {f : Bool → Bool} :: nil |- Var f ◦ If False Then True Else False : Bool.
intros. refine (TApp _ _ Bool _ _ _ _). constructor. simpl.
rewrite eq_symbol_refl. reflexivity. constructor. constructor. constructor. constructor. Qed.

Lemma ex9_2_2_2: forall x f, eq_symbol f x = false -> {f : Bool → Bool} :: nil |- 
λ x : Bool , Var f ◦ (If Var x Then False Else Var x) : Bool → Bool.
intros. constructor. refine (TApp _ _ Bool _ _ _ _).
constructor. simpl. rewrite H. rewrite eq_symbol_refl. reflexivity.
constructor. constructor. simpl. rewrite eq_symbol_refl. reflexivity.
constructor. constructor. simpl. rewrite eq_symbol_refl. reflexivity. Qed.

Lemma lem9_3_1_TVar: forall Γ x R, Γ |- (Var x) : R -> get_var_type x Γ = Some R.
intros. inversion H. apply H2. Qed.
Lemma lem9_3_1_TAbs: forall Γ x T1 t2 R, Γ |- λ x : T1 , t2 : R -> exists R2,
{x : T1} :: Γ |- t2 : R2 /\ R = T1 → R2.
intros. inversion H. exists T2. auto. Qed.
Lemma lem9_3_1_TApp: forall Γ t1 t2 R, Γ |- t1 ◦ t2 : R -> exists T11,
(Γ |- t1 : T11 → R /\ Γ |- t2 : T11).
intros. inversion H. exists T11. auto. Qed.
Lemma lem9_3_1_TTrue: forall Γ R, Γ |- True : R -> R = Bool.
intros. inversion H. auto. Qed.
Lemma lem9_3_1_TFalse: forall Γ R, Γ |- False : R -> R = Bool.
intros. inversion H. auto. Qed.
Lemma lem9_3_1_TIf: forall Γ t1 t2 t3 R, Γ |- If t1 Then t2 Else t3 : R ->
Γ |- t1 : Bool /\ Γ |- t2 : R /\ Γ |- t3 : R.
intros. inversion H. auto. Qed.