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
  | v_True: value True
  | v_False: value False
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
  | _ => false
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
    | EAppAbs: forall x y T t12 v2 s1 s2, value v2 -> [x |→ Var y] t12 = Some s1 
    -> [y |→ v2] s1 = Some s2 -> term_step ((λ x : T , t12) ◦ v2) s2. (* アルファ変換を許す*)

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

Theorem thm9_3_3: forall Γ t T1 T2, Γ |- t : T1 -> Γ |- t : T2 -> T1 = T2.
intros. generalize dependent T2. induction H.
- intros. apply lem9_3_1_TTrue in H0. auto.
- intros. apply lem9_3_1_TFalse in H0. auto.
- intros. apply lem9_3_1_TIf in H2. destruct H2. destruct H3. now apply IHtype_step2 in H3.
- intros. apply lem9_3_1_TVar in H0. rewrite H in H0. now inversion H0.
- intros. apply lem9_3_1_TAbs in H0. destruct H0. destruct H0. apply IHtype_step in H0.
subst. reflexivity.
- intros. apply lem9_3_1_TApp in H1. destruct H1. destruct H1. apply IHtype_step1 in H1.
apply IHtype_step2 in H2. subst. now inversion H1. Qed.

Lemma lem9_3_4_1: forall v Γ, value v -> Γ |- v : Bool -> v = True \/ v = False.
intros. inversion H. auto. auto. subst. inversion H0. Qed.
Lemma lem9_3_4_2: forall v T1 T2 Γ, value v -> Γ |- v : T1 → T2 -> exists x t2, v = λ x : T1 , t2.
intros. destruct H. inversion H0. inversion H0. inversion H0. subst.
exists x, t. reflexivity. Qed.

Lemma subst_alpha_exists: forall t1 t2 x, exists y s1 s2, 
[x |→ Var y] t1 = Some s1 /\ [y |→ t2] s1 = Some s2.

(* Lemma subst_alpha_unique: forall t1 t2 x y y' s1 s2 s1' s2',
Some s1 = [x |→ Var y] t1 -> Some s2 = [y |→ t2] s1 ->
Some s1' = [x |→ Var y'] t1 -> Some s2' = [y' |→ t2] s1' -> s2 = s2'.
induction t1.
- intros. simpl in H. inversion H. subst. inversion H0. simpl in H1. inversion H1.
  subst. simpl in H2. inversion H2. reflexivity.
- intros. simpl in H. inversion H. subst. inversion H0. simpl in H1. inversion H1.
  subst. simpl in H2. inversion H2. reflexivity.
- intros. simpl in H. 
  remember ([x |→ Var y] t1_1) as o1.
  remember ([x |→ Var y] t1_2) as o2.
  remember ([x |→ Var y] t1_3) as o3.
  destruct o1. destruct o2. destruct o3. inversion H. subst. simpl in H0.
  remember ([y |→ t2] t) as p1.
  remember ([y |→ t2] t0) as p2.
  remember ([y |→ t2] t1) as p3.
  destruct p1. destruct p2. destruct p3. inversion H0. simpl in H1.
  remember ([x |→ Var y'] t1_1) as o1'.
  remember ([x |→ Var y'] t1_2) as o2'.
  remember ([x |→ Var y'] t1_3) as o3'.
  destruct o1'. destruct o2'. destruct o3'. inversion H1. subst. simpl in H2.
  remember ([y' |→ t2] t6) as p1'.
  remember ([y' |→ t2] t7) as p2'.
  remember ([y' |→ t2] t8) as p3'.
  destruct p1'. destruct p2'. destruct p3'. inversion H2.
  pose proof (IHt1_1 _ _ _ _ _ _ _ _ Heqo1 Heqp1 Heqo1' Heqp1').
  pose proof (IHt1_2 _ _ _ _ _ _ _ _ Heqo2 Heqp2 Heqo2' Heqp2').
  pose proof (IHt1_3 _ _ _ _ _ _ _ _ Heqo3 Heqp3 Heqo3' Heqp3').
  now subst.
  inversion H2. inversion H2. inversion H2. inversion H1. inversion H1. inversion H1.
  inversion H0. inversion H0. inversion H0. inversion H. inversion H. inversion H.
- intros. simpl in H. remember (eq_symbol x s). destruct b.
  + inversion H. subst. simpl in H0. remember (eq_symbol y y). destruct b.
  inversion H0. simpl in H1. symmetry in Heqb. rewrite Heqb in H1. inversion H1.
  subst. simpl in H2. remember (eq_symbol y' y'). destruct b. now inversion H2.
  pose proof (eq_symbol_refl y'). rewrite H3 in Heqb1. inversion Heqb1.
  pose proof (eq_symbol_refl y). rewrite H3 in Heqb0. inversion Heqb0.
  + admit.
- intros. admit.
- admit. Admitted. *)

Theorem thm9_3_5: forall t T , nil |- t : T -> value t \/ exists t', t -→ t'.
intros. remember nil as Γ. induction H.
- left. constructor.
- left. constructor.
- right. destruct IHtype_step1. apply HeqΓ. inversion H2.
  + exists t2. constructor.
  + exists t3. constructor.
  + subst. inversion H.
  + destruct H2. exists (If x Then t2 Else t3). now constructor.
- rewrite HeqΓ in H. simpl in H. inversion H.
- left. constructor.
- pose proof (IHtype_step1 HeqΓ). pose proof (IHtype_step2 HeqΓ). destruct H1. inversion H1.
  + subst. inversion H.
  + subst. inversion H.
  + right. subst. destruct H2.
    * pose proof (subst_alpha_exists x t t2). destruct H3. destruct H3. destruct H3.
      destruct H3. exists x2. refine (EAppAbs _ _ _ _ _ _ _ H2 H3 H4).
    * destruct H2. remember (λ x : T, t) as t'. exists (t' ◦ x0). now constructor.
  + destruct H1. right. exists (x ◦ t2). now constructor. Qed.

Lemma lem9_3_8: forall Γ x y s S t T t1' t2', {x : S} :: Γ |- t : T -> Γ |- s : S 
-> [x |→ Var y] t = Some t1' -> [y |→ s] t1' = Some t2' -> Γ |- t2' : T.
Admitted.

Theorem thm9_3_9: forall Γ t t' T, Γ |- t : T -> t -→ t' -> Γ |- t' : T.
intros. generalize dependent t'. induction H.
- intros. inversion H0.
- intros. inversion H0.
- intros. inversion H2.
  + subst. auto.
  + subst. auto.
  + subst. constructor. refine (IHtype_step1 _ H7). auto. auto.
- intros. inversion H0.
- intros. inversion H0.
- intros. inversion H1.
  + subst. pose proof (IHtype_step1 _ H5). refine (TApp _ _ _ _ _ H2 H0).
  + subst. pose proof (IHtype_step2 _ H6). refine (TApp _ _ _ _ _ H H2).
  + subst. inversion H. subst. refine (lem9_3_8 _ _ _ _ _ _ _ _ _ H6 H0 H5 H7). Qed.