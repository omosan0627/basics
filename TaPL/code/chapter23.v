Require Import List.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Inductive type: Type :=
    | Nat: type
    | TVar: nat -> type
    | Func: type -> type -> type
    | Forall: type -> type.

Notation "'∀' T" := (Forall T) (at level 62).
Notation "T1 → T2" := (Func T1 T2) (at level 62).

Inductive term : Type :=
    | O: term
    | Succ: term -> term
    | Abst: type -> term -> term
    | App: term -> term -> term
    | Var: nat -> term
    | TAbst: term -> term
    | TApp: term -> type -> term.

Notation "'Λ' t " := (TAbst t) (at level 62).
Notation "'λ' T , t " := (Abst T t) (at level 61, T at level 99).
Notation "t [ T ] " := (TApp t T) (at level 60).
Notation "t1 ◦ t2" := (App t1 t2) (at level 59, left associativity).

Inductive nvalue: term -> Prop :=
    | nv_O: nvalue O
    | nv_Succ: forall nv, nvalue nv -> nvalue (Succ nv).

Inductive value: term -> Prop :=
    | v_nvalue: forall nv, nvalue nv -> value nv
    | v_Abst: forall T t, value (λ T , t)
    | v_TAbst: forall t, value (Λ t).

Inductive env_elem: Type :=
    | env_var_bind: type -> env_elem
    | env_type_bind: env_elem.

Fixpoint is_type_var_bind (T: type) (n: nat): bool :=
    match T with
    | Nat => true
    | TVar k => if k <? n then true else false
    | T1' → T2' => (is_type_var_bind T1' n) && (is_type_var_bind T2' n)
    | ∀ T' => is_type_var_bind T' (n + 1)
    end.

Fixpoint count_env_type_bind (Γ: list env_elem): nat :=
    match Γ with
    | nil => 0
    | (env_var_bind T) :: Γ' => count_env_type_bind Γ'
    | env_type_bind :: Γ' => (count_env_type_bind Γ') + 1
    end.

Fixpoint count_env_var_bind (Γ: list env_elem): nat :=
    match Γ with
    | nil => 0
    | (env_var_bind T) :: Γ' => (count_env_var_bind Γ') + 1
    | env_type_bind :: Γ' => count_env_var_bind Γ'
    end.

Fixpoint shift (c d: nat) (t: term): term :=
    match t with
    | O => O
    | Succ t' => Succ (shift c d t')
    | Var k => if c <=? k then Var (k + d) else Var k
    | λ T , t => λ T , shift (S c) d t
    | t1 ◦ t2 => (shift c d t1) ◦ (shift c d t2)
    | Λ t' => Λ (shift c d t')
    | t' [T] => (shift c d t') [T]
end.
      
Fixpoint reverse_shift (c: nat) (t: term): term :=
    match t with
    | O => O
    | Succ t' => Succ (reverse_shift c t')
    | Var k => if c <=? k then Var (pred k) else Var k
    | λ T , t => λ T , reverse_shift (S c) t
    | t1 ◦ t2 => (reverse_shift c t1) ◦ (reverse_shift c t2)
    | Λ t' => Λ (reverse_shift c t')
    | t' [T] => (reverse_shift c t') [T]
end.
      
Fixpoint subst (j: nat) (s t: term) :=
    match t with 
    | O => O
    | Succ t' => Succ (subst j s t')
    | Var k => if k =? j then s else Var k
    | λ T , t => λ T , subst (S j) (shift 0 1 s) t
    | t1 ◦ t2 => (subst j s t1) ◦ (subst j s t2)
    | Λ t' => Λ (subst j s t')
    | t' [T] => (subst j s t') [T]
end.
      
Notation "[ j |→ v ] t" := (subst j v t) (at level 62, j at level 99, v at level 99).

Fixpoint type_shift (c d: nat) (T: type): type :=
    match T with
    | Nat => Nat
    | TVar k => if c <=? k then TVar (k + d) else TVar k
    | T1 → T2 => type_shift c d T1 → type_shift c d T2
    | ∀ T' => ∀ (type_shift (c + 1) d T')
end.
      
Fixpoint type_reverse_shift (c: nat) (T: type): type :=
    match T with
    | Nat => Nat
    | TVar k => if c <=? k then TVar (pred k) else TVar k
    | T1 → T2 => type_reverse_shift c T1 → type_reverse_shift c T2
    | ∀ T' => ∀ (type_reverse_shift (c + 1) T')
end.

      
Fixpoint type_subst (j: nat) (T1 T2: type) :=
    match T2 with
    | Nat => Nat
    | TVar k => if k =? j then T1 else TVar k
    | T1' → T2' => (type_subst j T1 T1') → (type_subst j T1 T2')
    | ∀ T' => ∀ type_subst (S j) (type_shift 0 1 T1) T'
end.
      
Notation "[[[ j |→ T1 ]]] T2" := (type_subst j T1 T2) (at level 62, j at level 99, T1 at level 99).

Fixpoint env_shift (c d: nat) (Γ: list env_elem): list env_elem :=
    match Γ with
    | nil => nil
    | env_var_bind T :: Γ' => env_var_bind (type_shift c d T) :: env_shift c d Γ'
    | env_type_bind :: Γ' => env_type_bind :: Γ'
    end.

Fixpoint env_reverse_shift (c: nat) (Γ: list env_elem): list env_elem :=
    match Γ with
    | nil => nil
    | env_var_bind T :: Γ' => env_var_bind (type_reverse_shift c T) :: env_reverse_shift c Γ'
    | env_type_bind :: Γ' => env_type_bind :: env_reverse_shift c Γ'
    end.


Inductive env: list env_elem -> Prop :=
    | env_empty: env nil
    | env_type_bind_cons: forall Γ, env Γ -> env (env_type_bind :: env_shift 0 1 Γ)
    | env_var_bind_cons: forall T Γ, env Γ -> env ((env_var_bind T) :: Γ).

Fixpoint type_term_subst (j: nat) (T: type) (t: term): term :=
    match t with
    | O => O
    | Succ t' => Succ (type_term_subst j T t')
    | Var k => Var k
    | λ T' , t' => λ [[[j |→ T]]] T' , type_term_subst j T t'
    | t1 ◦ t2 => (type_term_subst j T t1) ◦ (type_term_subst j T t2)
    | Λ t' => Λ (type_term_subst (j + 1) (type_shift 0 1 T) t')
    | t' [T'] => (type_term_subst j T t') [(type_subst j T T')]
end.

Notation "[[ j |→ T ]] t" := (type_term_subst j T t) (at level 62, j at level 99, T at level 99).

Fixpoint type_term_shift (c d: nat) (t: term): term :=
    match t with
    | O => O
    | Succ t' => Succ (type_term_shift c d t')
    | Var k => Var k
    | λ T , t' => λ type_shift c d T, type_term_shift c d t'
    | t1 ◦ t2 => (type_term_shift c d t1) ◦ (type_term_shift c d t2)
    | Λ t' => Λ type_term_shift (c + 1) d t'
    | t' [T] => ((type_term_shift c d t') [type_shift c d T])
end.

Fixpoint type_term_reverse_shift (c: nat) (t: term): term :=
    match t with
    | O => O
    | Succ t' => Succ (type_term_reverse_shift c t')
    | Var k => Var k
    | λ T , t' => λ type_reverse_shift c T, type_term_reverse_shift c t'
    | t1 ◦ t2 => (type_term_reverse_shift c t1) ◦ (type_term_reverse_shift c t2)
    | Λ t' => Λ type_term_reverse_shift (c + 1) t'
    | t' [T] => ((type_term_reverse_shift c t') [type_reverse_shift c T])
end.

Inductive eval_step: term -> term -> Prop :=
    | EApp1: forall t1 t1' t2, eval_step t1 t1' -> eval_step (t1 ◦ t2) (t1' ◦ t2)
    | EApp2: forall v1 t2 t2', value v1 -> eval_step t2 t2' -> eval_step (v1 ◦ t2) (v1 ◦ t2')
    | EAppAbs: forall T t12 v2, value v2 ->
    eval_step ((λ T , t12) ◦ v2) (reverse_shift 0 ([ 0 |→ shift 0 1 v2 ] t12))
    | ESucc: forall t1 t1', eval_step t1 t1' -> eval_step (Succ t1) (Succ t1')
    | ETApp: forall t1 t1' T, eval_step t1 t1' -> eval_step (t1 [T]) (t1' [T])
    | ETAppTAbs: forall t T, eval_step ((Λ t) [T]) (type_term_reverse_shift 0 ([[0 |→ type_shift 0 1 T]] t)).

Notation "A -→ B" := (eval_step A B) (at level 65).

Inductive multi_eval_step: term->term->Prop:=
  | Refl: forall t, multi_eval_step t t
  | Trans: forall t1 t2 t3, eval_step t1 t2 -> multi_eval_step t2 t3 -> multi_eval_step t1 t3.

Notation "A -→* B" := (multi_eval_step A B) (at level 65).

Fixpoint get_var_type (k: nat) (Γ: list env_elem): option type :=
    match Γ with
    | nil => None
    | (env_var_bind T) :: Γ' => if k =? 0 then Some T else get_var_type (pred k) Γ'
    | env_type_bind :: Γ' => get_var_type k Γ'
    end.

(* Γ = x:X, X, f:X→X みたいなときに上手くいかない。Xがどこで束縛されたかわからないため。*)
(* 初期のfree varfiableありまくりの状態が上手く行くかが謎。->やっぱりこういうのを弾くルールが必要です*)
(* 本文ではなく注釈に書いてあるうーん*)
Inductive type_bind: list env_elem -> term -> type -> Prop :=
    | TZero: forall Γ, env Γ -> type_bind Γ O Nat
    | TSucc: forall Γ t1, env Γ -> type_bind Γ t1 Nat -> type_bind Γ (Succ t1) Nat
    | TVar': forall k T Γ, env Γ -> get_var_type k Γ = Some T -> type_bind Γ (Var k) T
    | TAbs: forall T1 Γ t2 T2, env Γ -> type_bind (env_var_bind T1 :: Γ) t2 T2
    -> type_bind Γ (λ T1 , t2) (T1 → T2)
    | TApp': forall Γ t1 T11 T12 t2, env Γ -> type_bind Γ t1 (T11 → T12) -> type_bind Γ t2 T11
    -> type_bind Γ (t1 ◦ t2) T12
    | TTAbs: forall Γ t T, env Γ -> type_bind (env_type_bind :: env_shift 0 1 Γ) t T 
    -> type_bind Γ (Λ t) (∀ T)
    | TTApp: forall Γ t T T', env Γ -> type_bind Γ t (∀ T) 
    -> type_bind Γ (t [T']) (type_reverse_shift 0 ([[[0 |→ type_shift 0 1 T']]] T)).

Notation "Γ |- t : T" := (type_bind Γ t T) (at level 65, t at level 99).

Lemma ex1: TApp (Λ (Abst (TVar 0) (Var 0))) (Nat) ◦ O -→* O.
apply (Trans _ ((Abst Nat (Var 0)) ◦ O) _).
+ constructor. constructor.
+ apply (Trans _ O _).
    - constructor. constructor. constructor.
    - constructor. Qed.

Lemma ex1_type: type_bind nil (TApp (Λ (Abst (TVar 0) (Var 0))) (Nat) ◦ O) Nat.
apply TApp' with (T11:=Nat).
+ constructor.
+ apply TTApp with (T:= TVar 0 → TVar 0). constructor. constructor. constructor. constructor.
constructor. constructor. constructor. constructor. constructor. constructor. simpl. reflexivity.
+ constructor. constructor.
Qed.

Definition double:= Λ λ (TVar 0 → TVar 0), λ (TVar 0), ((Var 1) ◦ ((Var 1) ◦ (Var 0))).
Definition doubleNat:= λ Nat → Nat, λ Nat, ((Var 1) ◦ ((Var 1) ◦ (Var 0))).

Definition five:= (double [Nat] ◦ (λ Nat, Succ (Succ (Var 0)))) ◦ (Succ O).
Lemma ex2: five -→* (Succ (Succ (Succ (Succ (Succ O))))).
unfold five.
apply (Trans _ ((doubleNat ◦ (λ Nat, Succ (Succ (Var 0)))) ◦ (Succ O)) _).
+ constructor. constructor. constructor.
+ apply (Trans _ ((λ Nat, (λ Nat, (Succ (Succ (Var 0)))) ◦ ((λ Nat, (Succ (Succ (Var 0)))) ◦ (Var 0))) ◦ (Succ O)) _).
    - constructor. constructor. apply v_Abst.
    - apply (Trans _ ((λ Nat, (Succ (Succ (Var 0)))) ◦ ((λ Nat, (Succ (Succ (Var 0)))) ◦ (Succ O))) _).
        * constructor. constructor. constructor. constructor.
        * apply (Trans _ ((λ Nat, Succ (Succ (Var 0))) ◦ (Succ (Succ (Succ O)))) _).
            constructor. apply v_Abst. constructor. constructor. constructor. constructor.
            apply (Trans _ (Succ (Succ (Succ (Succ (Succ O))))) _).
            constructor. constructor. constructor. constructor. constructor. constructor.
            constructor. Qed.

Lemma natIsNValueLeft: forall Γ t, Γ |- t : Nat /\ value t -> nvalue t.
intros. destruct H. remember Nat as T. induction H.
+ constructor.
+ constructor. apply IHtype_bind. auto. inversion H0. constructor. inversion H2. auto.
+ subst. inversion H0. apply H2.
+ inversion HeqT.
+ subst. inversion H0. apply H3.
+ inversion HeqT.
+ inversion H0. apply H2.
Qed.

Theorem th23_5_2: forall t T, nil |- t : T -> (value t) \/ (exists t', t -→ t').
intros. remember nil as Γ. induction H.
+ left. constructor. constructor.
+ apply IHtype_bind in HeqΓ. destruct HeqΓ.
    - left. constructor. constructor. inversion H1. apply H2. subst. inversion H0. subst. inversion H0.
    - right. destruct H1. exists (Succ x). constructor. apply H1.
+ subst. simpl in H0. inversion H0.
+ left. apply v_Abst.
+ assert (Γ = nil); auto. apply IHtype_bind1 in HeqΓ. apply IHtype_bind2 in H2.
destruct HeqΓ. 
    - inversion H0. subst. inversion H3. inversion H6. subst. inversion H3. inversion H4. 
    subst. destruct H2. right. exists (reverse_shift 0 ([0 |→ shift 0 1 t2] t0)). constructor. apply H2.
    destruct H2. right. exists ((λ T11, t0) ◦ x). constructor. apply H3. apply H2.
    subst. inversion H3. inversion H7. subst. inversion H3. inversion H6.
    - destruct H3. right. exists (x ◦ t2). constructor. auto.
+ left. apply v_TAbst.
+ apply IHtype_bind in HeqΓ. destruct HeqΓ.
    - inversion H0.
        * subst. inversion H1. subst. inversion H4.
        * subst. inversion H1. subst. inversion H5.
        * subst. right. exists (type_term_reverse_shift 0 ([[0 |→ type_shift 0 1 T']] t0)). constructor.
        * subst. inversion H1. subst. inversion H4.
    - destruct H1. right. exists (x [T']). constructor. auto.
Qed.

Fixpoint type_subst_in_list (n: nat) (S: type) (Γ: list env_elem) : list env_elem :=
match Γ with
    | nil => nil
    | (env_var_bind X) :: Γ' 
    => env_var_bind ([[[n |→ S]]] X) :: type_subst_in_list n S Γ'
    | env_type_bind :: Γ' => env_type_bind :: (type_subst_in_list n S Γ')
end.

Lemma env_with_one_less_type_var: forall Γ' Γ Γ0 m S U, Γ = Γ' ++ env_type_bind :: Γ0
-> env Γ -> m = count_env_type_bind Γ'
-> U = type_shift 0 (m + 1) S -> env (env_reverse_shift m (type_subst_in_list m U Γ' ++ Γ0)).
induction Γ'.
- intros. simpl. simpl in H. rewrite H in H0. inversion H0.  admit.
- intros. destruct a.
    + simpl. rewrite H in H0. simpl in H0. inversion H0. constructor.
    apply IHΓ' with (Γ:=Γ'++env_type_bind::Γ0)(S:=S). auto. auto. auto. auto.
    + simpl. rewrite H in H0. simpl in H0. inversion H0. admit.
Admitted.

Lemma get_var_type_and_subst: forall Γ' k m Γ0 S T U, get_var_type k (Γ' ++ env_type_bind :: Γ0) = Some T 
-> env (Γ' ++ env_type_bind :: Γ0)
-> m = count_env_type_bind Γ' 
-> U = type_shift 0 (m + 1) S
-> get_var_type k (env_reverse_shift m (type_subst_in_list m U Γ' ++ Γ0)) = 
Some (type_reverse_shift m ([[[m |→ U]]] T)).
induction Γ'.
- intros. simpl. admit.
- intros. destruct a.
    + simpl. admit.
    + simpl. simpl in H. apply IHΓ' with (S:=S). auto. admit. admit. apply H2.
Admitted.

Lemma th23_5_1_type_prep: forall Γ Γ' m t T S U, Γ' ++ env_type_bind :: Γ |- t : T ->
m = count_env_type_bind Γ' ->
U = type_shift 0 (m + 1) S ->
env_reverse_shift m ((type_subst_in_list m U Γ') ++ Γ) |- (type_term_reverse_shift m ([[m |→ U]] t))
: (type_reverse_shift m ([[[m |→ U]]] T)).
intros ? ? ? ? ? ? ? ?. remember (Γ' ++ env_type_bind :: Γ) as Γ''.
generalize dependent Γ'. generalize dependent Γ. generalize dependent m. generalize dependent S. generalize dependent U. 
induction H.
- intros. simpl. constructor. apply env_with_one_less_type_var with (Γ:=Γ)(S:=S). auto. auto.
  auto. auto.
- intros. simpl. constructor. apply env_with_one_less_type_var with (Γ:=Γ)(S:=S). auto. auto.
  auto. auto. auto. pose proof (IHtype_bind U S). apply H3 with (Γ':=Γ') (Γ:=Γ0). auto. auto. auto.
- intros. simpl. constructor. apply env_with_one_less_type_var with (Γ:=Γ)(S:=S). auto. auto.
  auto. auto. apply get_var_type_and_subst with(S:=S). rewrite HeqΓ'' in H0.
  auto. rewrite HeqΓ'' in H. auto. auto. auto.
- intros. simpl. apply TAbs. apply env_with_one_less_type_var with (Γ:=Γ)(S:=S). auto. auto.
  auto. auto. pose proof (IHtype_bind U S m Γ0 (env_var_bind T1 :: Γ')).
simpl in H3. apply H3. rewrite HeqΓ''. auto. auto. auto.
- intros. simpl. apply TApp' with (T11:=type_reverse_shift m ([[[m |→ U]]] T11)).
  apply env_with_one_less_type_var with (Γ:=Γ)(S:=S). auto. auto. auto. auto.
 simpl in IHtype_bind1. refine (IHtype_bind1 U S m _ _ _ _ _). auto. auto. auto.
 simpl in IHtype_bind2. refine (IHtype_bind2 U S m _ _ _ _ _). auto. auto. auto.
- intros. simpl. constructor. apply env_with_one_less_type_var with (Γ:=Γ)(S:=S).
  auto. auto. auto. auto.
  pose proof (IHtype_bind (type_shift 0 1 U) S (m + 1) (env_shift 0 1 Γ0) (env_type_bind :: (env_shift 0 1 Γ'))). assert (m + 1 + 1 = m + 2).
  lia. rewrite H4 in H3. assert (Datatypes.S m = m + 1). lia. rewrite H5. simpl in H3.
  assert (env_reverse_shift (m + 1) (type_subst_in_list (m + 1) (type_shift 0 1 U) (env_shift 0 1 Γ') ++ env_shift 0 1 Γ0)
  = env_shift 0 1 (env_reverse_shift m (type_subst_in_list m U Γ' ++ Γ0))).
  admit. rewrite H6 in H3. apply H3. rewrite HeqΓ''. admit. admit. admit.
- intros. simpl. simpl in IHtype_bind. pose proof (TTApp (env_reverse_shift m (type_subst_in_list m U Γ' ++ Γ0)) 
(type_term_reverse_shift m
([[m |→ U]] t)) (type_reverse_shift (m + 1)
([[[(m + 1)
 |→ type_shift 0 1 U]]] T)) (type_reverse_shift m
([[[m |→ U]]] T'))). assert (env (env_reverse_shift m (type_subst_in_list m U Γ' ++ Γ0))).
 apply env_with_one_less_type_var with (Γ:=Γ)(S:=S). auto. auto. auto. auto.
 assert (env_reverse_shift m (type_subst_in_list m U Γ' ++ Γ0)
 |- type_term_reverse_shift m
      ([[m |→ U]] t) : ∀ type_reverse_shift (m + 1)
      ([[[(m + 1)
       |→ type_shift 0 1 U]]] T)). 
pose proof (IHtype_bind U S m Γ0 Γ'). assert (Datatypes.S m = m + 1). lia. rewrite H6 in H5.
apply H5. auto. auto. auto. pose proof (H3 H4 H5). admit.
Admitted.

Lemma th23_5_1_var_prep: forall S Γ Γ' t T n m s, 
Γ |- s : S ->
n = count_env_var_bind Γ' ->
m = count_env_type_bind Γ' ->
Γ' ++ env_var_bind S :: (env_shift 0 m Γ) |- t : T ->
Γ' ++ (env_shift 0 m Γ) |- reverse_shift n ([n |→ shift 0 (n + 1) s] t) : T.
intros. remember (Γ' ++ env_var_bind S :: env_shift 0 m Γ) as Γ''. generalize dependent Γ'.
generalize dependent s. generalize dependent S. generalize dependent Γ. 
generalize dependent n. generalize dependent m. induction H2.
- intros. simpl. constructor. admit.
- intros. simpl. constructor. admit. apply IHtype_bind with (S:=S)(m:=m). auto. auto. auto. auto.
- intros. admit.
- intros. simpl. constructor. admit. rewrite HeqΓ'' in IHtype_bind.
 pose proof (IHtype_bind m (n + 1) Γ0 S s H0 (env_var_bind T1 :: Γ')).
 assert (Datatypes.S n = n + 1). lia. rewrite H5. simpl in H4.
 assert (shift 0 1 (shift 0 (n + 1) s) = shift 0 (n + 1 + 1) s).
 admit. rewrite H6. apply H4. auto. auto. auto. 
- intros. simpl. admit.
- intros. simpl. constructor. admit. 
  pose proof (IHtype_bind (m + 1) n Γ0 S s H0 (env_type_bind :: (env_shift 0 1 Γ'))).
  simpl in H4. assert (env_shift 0 1 Γ' ++ env_shift 0 (m + 1) Γ0 = env_shift 0 1 (Γ' ++ env_shift 0 m Γ0)).
  admit. rewrite H5 in H4. apply H4. admit. admit. admit.
- intros. simpl. constructor. admit. apply IHtype_bind with (S:=S). auto.
  auto. auto. auto.
Admitted.

Theorem th23_5_1: forall Γ t T t', Γ |- t : T -> t -→ t' -> Γ |- t' : T.
intros. generalize dependent t'. induction H.
intros.
+ inversion H0.
+ intros. inversion H1. constructor. apply H. apply IHtype_bind. apply H3.
+ intros. inversion H1.
+ intros. inversion H1.
+ intros. inversion H2. subst.
    - apply IHtype_bind1 in H6. apply TApp' with (T11:=T11). auto. auto. auto.
    - subst. apply TApp' with (T11:=T11). auto. auto. apply IHtype_bind2. apply H7.
    - subst. inversion H0. subst. inversion H0. subst. 
    pose proof (th23_5_1_var_prep T11 Γ nil t12 T12). simpl in H3. 
    pose proof (H3 0 0 t2 H1). simpl in H4. assert (env_shift 0 0 Γ = Γ). admit.
    rewrite H5 in H4. apply H4. auto. auto. auto.
+ intros. inversion H1.
+ intros. inversion H1.
    - subst. apply IHtype_bind in H5. apply TTApp. auto. auto.
    - subst. inversion H0. subst. 
    pose proof (th23_5_1_type_prep (env_shift 0 1 Γ) nil 0 t0 T T' (type_shift 0 1 T') H6).
    simpl in H2. assert (0 = 0). auto. assert (type_shift 0 1 T' = type_shift 0 1 T'). auto.
    apply H2 in H3. assert (env_reverse_shift 0 (env_shift 0 1 Γ) = Γ). admit. rewrite H7 in H3.
    apply H3. apply H4.
Admitted.