Require Import List.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Inductive type: Type :=
    | Bool: type
    | Func: type -> type -> type.

(* No Symbol *)
Inductive term : Type :=
    | True: term
    | False: term
    | IfThenElse: term -> term-> term-> term
    | Var: nat -> term
    | Abst: type -> term -> term
    | App: term -> term -> term.

Notation "'If' A 'Then' B 'Else' C" := (IfThenElse A B C) (at level 57, A at level 99, B at level 99).

Notation "'λ' T , t " := (Abst T t) (at level 60, T at level 99).

Notation "t1 ◦ t2" := (App t1 t2) (at level 59, left associativity).

Inductive value: term -> Prop :=
  | v_True: value True
  | v_False: value False
  | v_Abst: forall T t, value (λ T , t).

Notation "A → B" := (Func A B) (at level 58, right associativity).

Fixpoint shift (c d: nat) (t: term): term :=
  match t with
  | Var k => if c <=? k then Var (k + d) else Var k
  | λ T , t => λ T , shift (S c) d t
  | t1 ◦ t2 => (shift c d t1) ◦ (shift c d t2)
  | IfThenElse t1 t2 t3 => If (shift c d t1) Then (shift c d t2) Else (shift c d t3)
  | b => b
  end.

Fixpoint reverse_shift (c: nat) (t: term): term :=
  match t with
  | Var k => if c <=? k then Var (pred k) else Var k
  | λ T , t => λ T , reverse_shift (S c) t
  | t1 ◦ t2 => (reverse_shift c t1) ◦ (reverse_shift c t2)
  | IfThenElse t1 t2 t3 => If (reverse_shift c t1) Then (reverse_shift c t2) 
  Else (reverse_shift c t3)
  | b => b
  end.

Fixpoint subst (j: nat) (s t: term) :=
  match t with
  | Var k => if k =? j then s else Var k
  | λ T , t => λ T , subst (S j) (shift 0 1 s) t
  | t1 ◦ t2 => (subst j s t1) ◦ (subst j s t2)
  | IfThenElse t1 t2 t3 => If (subst j s t1) Then (subst j s t2) Else (subst j s t3)
  | b => b
  end.

Notation "[ j |→ v ] t" := (subst j v t) (at level 62, j at level 99, v at level 99).

Inductive term_step: term -> term -> Prop :=
    | EIfTrue: forall t2 t3, term_step (If True Then t2 Else t3) t2
    | EIfFalse: forall t2 t3, term_step (If False Then t2 Else t3) t3
    | EIf: forall t1 t1' t2 t3, (term_step t1 t1') 
    -> (term_step (If t1 Then t2 Else t3) (If t1' Then t2 Else t3))
    | EApp1: forall t1 t1' t2, term_step t1 t1' -> term_step (App t1 t2) (App t1' t2)
    | EApp2: forall v1 t2 t2', value v1 -> term_step t2 t2' -> term_step (App v1 t2) (App v1 t2')
    | EAppAbs: forall T t12 v2, value v2 ->
    term_step ((λ T , t12) ◦ v2) (reverse_shift 0 ([ 0 |→ shift 0 1 v2 ] t12)).

Notation "t1 -→ t2" := (term_step t1 t2) (at level 62).

Fixpoint get_var_type (k: nat) (Γ: list type): option type :=
    match Γ with
    | nil => None
    | T :: Γ' => if k =? 0 then Some T else get_var_type (pred k) Γ'
    end.

Inductive type_step: list type -> term -> type -> Prop :=
    | TTrue: forall Γ, type_step Γ True Bool
    | TFalse: forall Γ, type_step Γ False Bool
    | TIf: forall Γ t1 t2 t3 T, type_step Γ t1 Bool -> type_step Γ t2 T -> type_step Γ t3 T
    -> type_step Γ (If t1 Then t2 Else t3) T
    | TVar: forall k T Γ, get_var_type k Γ = Some T -> type_step Γ (Var k) T
    | TAbs: forall T1 Γ t2 T2, type_step (T1 :: Γ) t2 T2
    -> type_step Γ (λ T1 , t2) (T1 → T2)
    | TApp: forall Γ t1 T11 T12 t2, type_step Γ t1 (T11 → T12) -> type_step Γ t2 T11
    -> type_step Γ (t1 ◦ t2) T12.

Notation "Γ |- t : T" := (type_step Γ t T) (at level 62, t at level 99).

Lemma ex9_2_2_1: (Bool → Bool) :: nil |- Var 0 ◦ If False Then True Else False : Bool.
refine (TApp _ _ Bool _ _ _ _). constructor. now simpl.
constructor. constructor. constructor. constructor. Qed.

Lemma ex9_2_2_2: (Bool → Bool) :: nil |- 
λ Bool , Var 1 ◦ (If Var 0 Then False Else Var 0) : Bool → Bool.
constructor. refine (TApp _ _ Bool _ _ _ _).
constructor. simpl. reflexivity. constructor. constructor. simpl. reflexivity.
constructor. constructor. simpl. reflexivity. Qed.

Lemma lem9_3_1_TVar: forall Γ x R, Γ |- (Var x) : R -> get_var_type x Γ = Some R.
intros. inversion H. apply H2. Qed.
Lemma lem9_3_1_TAbs: forall Γ T1 t2 R, Γ |- λ T1 , t2 : R -> exists R2,
T1 :: Γ |- t2 : R2 /\ R = T1 → R2.
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
Lemma lem9_3_4_2: forall v T1 T2 Γ, value v -> Γ |- v : T1 → T2 -> exists t2, v = λ T1 , t2.
intros. destruct H. inversion H0. inversion H0. inversion H0. subst.
exists t. reflexivity. Qed.

(* 以降名前付けの話 *)
(* 深さでやらないといけないかも. アルファ変換絡むものは大体そうですね。*)
(* 代入前に先頭のλのみを変えるのがよさそう->無理。やっぱり全部変える必要アリ *)

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
    * exists (reverse_shift 0 ([0 |→ shift 0 1 t2] t)). constructor. apply H2.
    * destruct H2. remember (λ T, t) as t'. exists (t' ◦ x). now constructor.
  + destruct H1. right. exists (x ◦ t2). now constructor. Qed.

Lemma lem9_3_8: forall S Γ Γ' t T, Γ' ++ S :: Γ |- t : T -> forall n s, Γ' ++ Γ |- s : S 
-> length Γ' = n ->  Γ' ++ Γ |- reverse_shift 0 ([n |→ shift 0 (S n) s] (shift 0 n t)) : T.
intros ? ? ? ? ? ?. remember (Γ' ++ S :: Γ) as Γ''. generalize dependent S. generalize dependent Γ.
generalize dependent Γ'. 
induction H.
- intros. simpl. constructor.
- intros. simpl. constructor.
- intros. admit.
  (* + refine (IHtype_step1 Γ0 S HeqΓ'' s H2).
  + refine (IHtype_step2 Γ0 S HeqΓ'' s H2).
  + refine (IHtype_step3 Γ0 S HeqΓ'' s H2). *)
- intros. admit.
- intros. simpl. constructor. replace (T1 :: Γ' ++ Γ0) with ((T1 :: Γ') ++ Γ0).
  pose proof (IHtype_step (T1 :: Γ') Γ0 S).
  assert (T1 :: Γ = (T1 :: Γ') ++ S :: Γ0). rewrite HeqΓ''. simpl.
  reflexivity. pose proof (H2 H3 (n + 1) s). simpl in H4.

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
  + subst. inversion H. subst. refine (lem9_3_8 _ _ _ _ _ H4 H0). Qed.