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
    | Λ t' => Λ (subst j (type_term_shift 0 1 s) t')
    | t' [T] => (subst j s t') [T]
end.
      
Notation "[ j |→ v ] t" := (subst j v t) (at level 62, j at level 99, v at level 99).


Fixpoint env_shift (c d: nat) (Γ: list env_elem): list env_elem :=
    match Γ with
    | nil => nil
    | env_var_bind T :: Γ' => env_var_bind (type_shift c d T) :: env_shift c d Γ'
    | env_type_bind :: Γ' => env_type_bind :: env_shift c d Γ'
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

Fixpoint env_subst (n: nat) (S: type) (Γ: list env_elem) : list env_elem :=
match Γ with
    | nil => nil
    | (env_var_bind X) :: Γ' 
    => env_var_bind ([[[n |→ S]]] X) :: env_subst n S Γ'
    | env_type_bind :: Γ' => env_type_bind :: (env_subst n S Γ')
end.


Lemma type_shift_double: forall T m n d, m >= n -> type_shift (m+1) d (type_shift n 1 T)
= type_shift n 1 (type_shift m d T). induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (n0 <=? n) as b. destruct b.
    + simpl. remember (m <=? n) as b. destruct b. assert ((m+1<=?n+1)=true).
    rewrite Nat.leb_le. symmetry in Heqb0. rewrite Nat.leb_le in Heqb0. lia. rewrite H0.
    simpl. assert ((n0 <=? n + d) = true). apply Nat.leb_le. symmetry in Heqb.
    apply Nat.leb_le in Heqb. lia. rewrite H1. assert (n+1+d=n+d+1). lia. rewrite H2.
    reflexivity. simpl. symmetry in Heqb. rewrite Heqb. assert ((m+1<=?n+1)=false).
    rewrite Nat.leb_gt. symmetry in Heqb0. rewrite Nat.leb_gt in Heqb0. lia. rewrite H0.
    reflexivity.
    + simpl. assert (n0 > n). symmetry in Heqb. apply Nat.leb_gt in Heqb. lia.
    assert ((m+1<=?n)=false). apply Nat.leb_gt. lia. rewrite H1. assert ((m<=?n)=false).
    apply Nat.leb_gt. lia. rewrite H2. simpl. assert ((n0<=?n)=false). apply Nat.leb_gt.
    lia. rewrite H3. auto.
- intros. simpl. rewrite IHT1. rewrite IHT2. reflexivity. lia. lia.
- intros. simpl. pose proof (IHT (m+1) (n+1) d). assert (m + 1 >= n + 1). lia.
  apply H0 in H1. rewrite H1. reflexivity. 
Qed.

Lemma type_subst_dist_m: forall T m n U, m >= n -> type_shift (m+1) 1 ([[[n |→ U]]] T)
= [[[n |→ type_shift (m+1) 1 U]]] (type_shift (m+1) 1 T). induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (n=?n0) as b. destruct b. symmetry in Heqb. apply Nat.eqb_eq in Heqb.
  subst. assert ((m+1 <=?n0) = false). apply Nat.leb_gt. lia. rewrite H0. simpl. 
  assert ((n0=?n0) = true). apply Nat.eqb_eq. reflexivity. rewrite H1. reflexivity.
  remember (m+1 <=?n) as b. destruct b. symmetry in Heqb0. apply Nat.leb_le in Heqb0. simpl.
  assert ((m+1 <=?n) = true). apply Nat.leb_le. auto. rewrite H0. assert ((n+1 =? n0) = false).
  apply Nat.eqb_neq. lia. rewrite H1. reflexivity.
  symmetry in Heqb0. apply Nat.leb_gt in Heqb0. symmetry in Heqb. apply Nat.eqb_neq in Heqb.
  simpl. assert ((m+1 <=? n) = false). apply Nat.leb_gt. auto. assert ((n=?n0)=false). apply Nat.eqb_neq.
  lia. rewrite H0. rewrite H1. reflexivity.
- intros. simpl. rewrite IHT1. rewrite IHT2. reflexivity. auto. auto.
- intros. simpl. pose proof (IHT (m+1) (n+1) (type_shift 0 1 U)).
  pose proof (type_shift_double U (m+1) 0 1). assert (m+1>=0). lia. apply H1 in H2.
  symmetry in H2. rewrite H2. assert (S n = n + 1). lia. rewrite H3. assert (m + 1 >= n + 1). lia.
  apply H0 in H4. rewrite H4. reflexivity.
Qed.

Lemma type_subst_dist_zero: forall T n m U, m >= n ->
type_shift n 1 ([[[m |→ U]]] T)
= [[[m + 1 |→ type_shift n 1 U]]] (type_shift n 1 T).
induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (n0 <=? n) as b. destruct b. symmetry in Heqb. simpl.
  remember (n =? m) as b. destruct b. assert ((n+1 =?m+1) = true). apply Nat.eqb_eq.
  symmetry in Heqb0. apply Nat.eqb_eq in Heqb0. lia. rewrite H0. reflexivity.
  assert ((n+1=?m+1) = false). apply Nat.eqb_neq. symmetry in Heqb0. apply Nat.eqb_neq in Heqb0.
  lia. rewrite H0. simpl. rewrite Heqb. reflexivity.
  simpl. symmetry in Heqb. apply Nat.leb_gt in Heqb. assert ((n=?m)=false). apply Nat.eqb_neq. lia.
  assert ((n=?m+1)=false). apply Nat.eqb_neq. lia. rewrite H0. rewrite H1. simpl.
  apply Nat.leb_gt in Heqb. rewrite Heqb. reflexivity.
- intros. simpl. rewrite IHT1. rewrite IHT2. reflexivity. auto. auto.
- intros. simpl. pose proof (IHT (n+1) (m+1) (type_shift 0 1 U)). 
  pose proof (type_shift_double U n 0 1). assert (n >= 0). lia. apply H1 in H2. symmetry in H2.
  rewrite H2. assert (S m = m + 1). lia. rewrite H3. assert (S (m+1) = m + 1 + 1).
  lia. rewrite H4. assert (m + 1 >= n + 1). lia. apply H0 in H5. rewrite H5. reflexivity.
Qed.

Lemma type_shift_inversion: forall T c, type_reverse_shift c (type_shift c 1 T) = T.
induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (c<=?n) as b. destruct b. simpl. assert ((c<=?n+1)=true).
  apply Nat.leb_le. symmetry in Heqb. apply Nat.leb_le in Heqb. lia. rewrite H.
  assert (Init.Nat.pred (n+1) = n). lia. rewrite H0. reflexivity. simpl.
  symmetry in Heqb. rewrite Heqb. reflexivity.
- intros. simpl. rewrite IHT1. rewrite IHT2. reflexivity.
- intros. simpl. pose proof IHT (c+1). rewrite H. auto.
Qed.

Fixpoint has_free_var_in_type (m: nat) (T: type): bool :=
  match T with
  | Nat => false
  | TVar k => if m =? k then true else false
  | T1 → T2 => (has_free_var_in_type m T1) || (has_free_var_in_type m T2)
  | ∀ T' => has_free_var_in_type (m + 1) T'
end.

Lemma free_var_in_type_shift_prep: forall T m n l, m >= l -> 
(forall k, m > k -> k >= l -> has_free_var_in_type k T = false) ->
(forall c, m + n > c -> c >= l -> has_free_var_in_type c (type_shift m n T) = false).
induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (m <=? n) as b. destruct b. symmetry in Heqb. apply Nat.leb_le in Heqb.
  simpl. assert ((c =? n + n0) = false). apply Nat.eqb_neq. lia. rewrite H3. reflexivity.
  symmetry in Heqb. apply Nat.leb_gt in Heqb. assert (m > n). lia. simpl. remember (c =? n) as b. 
  destruct b. symmetry in Heqb0. apply Nat.eqb_eq in Heqb0. subst. pose proof (H0 n H3 H2).
  simpl in H4. assert ((n =? n)= true). apply Nat.eqb_eq. lia. rewrite H5 in H4. inversion H4.
  reflexivity.
- intros. simpl. rewrite IHT1 with (l:=l). rewrite IHT2 with (l:=l). simpl. reflexivity.
  auto. intros. pose proof (H0 k H3 H4). simpl in H5. apply Bool.orb_false_elim in H5. destruct H5.
  apply H6. auto. auto. auto. intros. pose proof (H0 k H3 H4). simpl in H5.
  apply Bool.orb_false_elim in H5. destruct H5. auto. auto. auto.
- intros. simpl. pose proof (IHT (m+1) n). simpl in H0. 
assert (forall k, m + 1 > k -> k >= l + 1 -> has_free_var_in_type k T = false).
intros. remember (k - 1) as k'. assert (k = k' + 1). lia. rewrite H6.
pose proof (H0 k'). apply H7. lia. lia. assert (m + 1 >= l + 1). lia.
pose proof (H3 (l+1) H5 H4 (c + 1)). apply H6. lia. lia.
Qed.

Lemma free_var_in_type_shift_prep_2: forall T l m n, m >= l ->
has_free_var_in_type m T = false -> has_free_var_in_type (m + n) (type_shift l n T) = false.
induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (l <=? n) as b. destruct b. simpl. assert ((m + n0 =? n + n0) = false).
  simpl in H0. remember (m =? n) as b. destruct b. inversion H0. symmetry in Heqb0.
  apply Nat.eqb_neq in Heqb0. apply Nat.eqb_neq. lia. rewrite H1. reflexivity.
  symmetry in Heqb. apply Nat.leb_gt in Heqb. simpl. assert ((m + n0 =? n) = false).
  apply Nat.eqb_neq. lia. rewrite H1. reflexivity.
- intros. simpl. simpl in H0. rewrite IHT1. rewrite IHT2. simpl. reflexivity. auto.
  apply Bool.orb_false_elim in H0. destruct H0. apply H1. auto. apply Bool.orb_false_elim in H0.
  destruct H0. apply H0.
- intros. simpl. simpl in H0. pose proof (IHT (l+1) (m+1) n). assert (m+1>=l+1).
  lia. pose proof (H1 H2 H0). assert (m + 1 + n = m + n + 1). lia. rewrite H4 in H3.
  apply H3.
Qed.

Lemma type_shift_zero: forall T c, type_shift c 0 T = T.
induction T.
- intros. simpl. auto.
- intros. simpl. remember (c <=? n) as b. destruct b. assert (n + 0 = n). lia.
  rewrite H. reflexivity. reflexivity.
- intros. simpl. rewrite IHT1. rewrite IHT2. reflexivity.
- intros. simpl. pose proof (IHT (c+1)). rewrite H. reflexivity.
Qed.

Lemma type_term_shift_zero: forall t c, type_term_shift c 0 t = t.
induction t.
- intros. simpl. auto.
- intros. simpl. rewrite IHt. auto.
- intros. simpl. rewrite IHt. rewrite type_shift_zero. auto.
- intros. simpl. rewrite IHt1. rewrite IHt2. auto.
- intros. simpl. auto.
- intros. simpl. rewrite IHt. auto.
- intros. simpl. rewrite IHt. rewrite type_shift_zero. auto.
Qed.


Lemma free_var_in_type_shift: forall c m T, 
m > 0 -> has_free_var_in_type c (type_shift c m T) = false.
intros. pose proof (free_var_in_type_shift_prep T c m c).
apply H0. lia. intros. lia. lia. lia.
Qed.

Lemma free_var_in_type_shift_zero: forall m T, 
has_free_var_in_type m (type_shift 0 (m+1) T) = false.
intros. pose proof (free_var_in_type_shift_prep T 0 (m + 1) 0).
apply H. lia. intros. lia. lia. lia. Qed.

Lemma type_shift_inversion_reverse: forall T m, has_free_var_in_type m T = false ->
type_shift m 1 (type_reverse_shift m T) = T.
induction T.
- intros. simpl. reflexivity.
- intros. simpl in H. remember (m =? n) as b. destruct b. inversion H. symmetry in Heqb.
  simpl. remember (m <=? n) as b. destruct b. symmetry in Heqb0. apply Nat.eqb_neq in Heqb.
  apply Nat.leb_le in Heqb0. simpl. assert ((m <=? Init.Nat.pred n) = true).
  apply Nat.leb_le. lia. rewrite H0. assert (Init.Nat.pred n + 1 = n). lia. rewrite H1. auto.
  symmetry in Heqb0. apply Nat.leb_gt in Heqb0. simpl. assert ((m <=? n) = false).
  apply Nat.leb_gt. auto. rewrite H0. reflexivity.
- intros. simpl in H. apply Bool.orb_false_elim in H. destruct H. simpl.
  rewrite IHT1. rewrite IHT2. reflexivity. auto. auto.
- intros. simpl. simpl in H. pose proof (IHT (m + 1) H). rewrite H0. reflexivity.
Qed.

Lemma free_var_in_type_subst: forall T U m,
has_free_var_in_type m U = false -> has_free_var_in_type m ([[[m |→ U]]] T) = false.
induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (n =? m) as b. destruct b. symmetry in Heqb. apply Nat.eqb_eq in Heqb.
  subst. auto. symmetry in Heqb. simpl. assert ((m =? n) = false).
  apply Nat.eqb_neq in Heqb. apply Nat.eqb_neq. lia. rewrite H0. reflexivity.
- intros. simpl. rewrite IHT1. rewrite IHT2. simpl. reflexivity. apply H. apply H.
- intros. simpl. pose proof (IHT (type_shift 0 1 U) (m+1)). assert (S m = m + 1). lia.
  rewrite H1. apply H0. pose proof (free_var_in_type_shift_prep_2 U 0 m 1). assert (m >= 0).
  lia. apply H2. auto. auto.
Qed.

Lemma type_subst_no_free_var: forall T a U,
has_free_var_in_type a T = false -> [[[a |→ U]]] T = T.
induction T.
- intros. simpl. auto.
- intros. simpl. simpl in H. remember (a =? n) as b. destruct b. inversion H.
  assert ((n =? a) = false). apply Nat.eqb_neq. symmetry in Heqb. apply Nat.eqb_neq in Heqb.
  lia. rewrite H0. auto.
- intros. simpl in H. apply Bool.orb_false_elim in H. destruct H. simpl.
  rewrite IHT1. rewrite IHT2. auto. auto. auto.
- intros. simpl. simpl in H. rewrite IHT. auto. assert (S a = a + 1). lia. rewrite H0. auto.
Qed.

Lemma type_subst_dist_subs: forall V a b T U, b > a
-> has_free_var_in_type a T = false -> has_free_var_in_type a U = false
-> [[[b |→ T]]] ([[[a |→ U]]] V) = [[[a |→ ([[[b |→ T]]] U)]]] ([[[b |→ T]]] V).
induction V. 
- intros. simpl. reflexivity.
- intros. simpl. remember (n =? a) as c0. remember (n =? b) as c1. destruct c0, c1.
  symmetry in Heqc0. symmetry in Heqc1. apply Nat.eqb_eq in Heqc0, Heqc1. lia.
  simpl. symmetry in Heqc0. rewrite Heqc0. auto. simpl. symmetry in Heqc1.
  rewrite Heqc1. rewrite type_subst_no_free_var. auto. auto.
  simpl. symmetry in Heqc0. rewrite Heqc0. symmetry in Heqc1. rewrite Heqc1. auto. 
- intros. simpl. rewrite IHV1. rewrite IHV2. auto. auto. auto. auto. auto. auto. auto.
- intros. simpl. pose proof (IHV (S a) (S b) (type_shift 0 1 T) (type_shift 0 1 U)).
  assert (type_shift 0 1 ([[[b |→ T]]] U) = [[[S b |→ type_shift 0 1 T]]] type_shift 0 1 U).
  assert (S b = b + 1). lia. rewrite H3. apply type_subst_dist_zero. lia.
  rewrite H3. rewrite H2. reflexivity. lia. assert (S a = a + 1). lia. rewrite H4.
  apply free_var_in_type_shift_prep_2. lia. auto. assert (S a = a + 1). lia. rewrite H4.
  apply free_var_in_type_shift_prep_2. lia. auto.
Qed.

Lemma type_shift_swap_m: forall T m n, m >= n -> has_free_var_in_type n T = false ->
type_shift m 1 (type_reverse_shift n T) = type_reverse_shift n (type_shift (m+1) 1 T).
induction T.
- intros. simpl. reflexivity.
- intros. simpl. remember (n0<=?n) as b. destruct b.
    + simpl. symmetry in Heqb. apply Nat.leb_le in Heqb.
    remember (m+1<=?n) as b. destruct b. symmetry in Heqb0. apply Nat.leb_le in Heqb0.
    simpl. assert ((n0 <=? n+1)=true). apply Nat.leb_le. lia. rewrite H1.
    assert ((m <=? Init.Nat.pred n) = true). apply Nat.leb_le. lia. rewrite H2.
    assert (Init.Nat.pred n + 1 = Init.Nat.pred (n+1)). lia. rewrite H3. reflexivity.
    simpl in H0. remember (n0 =? n) as b. destruct b. inversion H0. symmetry in Heqb1.
    apply Nat.eqb_neq in Heqb1. simpl. assert ((n0 <=? n) = true). apply Nat.leb_le. lia.
    rewrite H1. assert ((m <=? Init.Nat.pred n) = false). apply Nat.leb_gt.
    symmetry in Heqb0. apply Nat.leb_gt in Heqb0. lia. rewrite H2. reflexivity.
    + simpl. symmetry in Heqb. apply Nat.leb_gt in Heqb. assert ((m <=? n) = false).
    apply Nat.leb_gt. lia. assert ((m+1<=?n)=false). apply Nat.leb_gt. lia. rewrite H1.
    rewrite H2. simpl. assert ((n0 <=? n) = false). apply Nat.leb_gt. auto. rewrite H3.
    reflexivity.
- intros. simpl. rewrite IHT1. rewrite IHT2. reflexivity. auto. simpl in H0. 
  apply Bool.orb_false_elim in H0. destruct H0. apply H1. auto.
  simpl in H0. apply Bool.orb_false_elim in H0. destruct H0. apply H0.
- intros. simpl. pose proof (IHT (m+1) (n+1)). rewrite H1. reflexivity. lia. simpl in H0. apply H0.
Qed.

Lemma type_shift_swap_zero: forall T m n, m >= n -> has_free_var_in_type m T = false ->
type_shift n 1 (type_reverse_shift m T) = type_reverse_shift (m+1) (type_shift n 1 T).
induction T.
- intros. simpl. reflexivity.
- intros. simpl in H0. remember (m =? n) as b. destruct b. inversion H0. symmetry in Heqb.
  simpl. remember (n0 <=? n) as b. destruct b. symmetry in Heqb0. apply Nat.leb_le in Heqb0.
  simpl. remember (m <=? n) as b. destruct b. symmetry in Heqb1. apply Nat.leb_le in Heqb1.
  simpl. assert ((m + 1 <=? n + 1) = true). apply Nat.leb_le. lia. rewrite H1.
  assert ((n0 <=? Init.Nat.pred n) = true). apply Nat.leb_le. apply Nat.eqb_neq in Heqb.
  lia. rewrite H2. apply Nat.eqb_neq in Heqb. assert (Init.Nat.pred n + 1 = Init.Nat.pred (n + 1)).
  lia. rewrite H3. reflexivity. simpl. symmetry in Heqb1. apply Nat.leb_gt in Heqb1.
  assert ((m + 1 <=? n + 1) = false). apply Nat.leb_gt. lia. rewrite H1. assert ((n0 <=? n) = true).
  apply Nat.leb_le. lia. rewrite H2. reflexivity. simpl. symmetry in Heqb0.
  apply Nat.leb_gt in Heqb0. assert ((m <=? n) = false). apply Nat.leb_gt. lia.
  assert ((m +1 <=? n) = false). apply Nat.leb_gt. lia. rewrite H1. rewrite H2. simpl.
  assert ((n0 <=? n) = false). apply Nat.leb_gt. auto. rewrite H3. reflexivity.
- intros. simpl in H0. apply Bool.orb_false_elim in H0. destruct H0. simpl. rewrite IHT1.
  rewrite IHT2. reflexivity. apply H. apply H1. apply H. apply H0.
- intros. simpl. pose proof (IHT (m+1) (n+1)). assert (m+1 >= n + 1). lia. apply H1 in H2.
  rewrite H2. reflexivity. simpl in H0. apply H0.
Qed.

Lemma env_shift_zero: forall Γ, env_shift 0 0 Γ = Γ.
induction Γ.
- simpl. reflexivity.
- destruct a. simpl. pose proof (type_shift_zero t 0). rewrite H. rewrite IHΓ. reflexivity.
  simpl. rewrite IHΓ. reflexivity.
Qed.

Lemma env_shift_inversion: forall Γ, env_reverse_shift 0 (env_shift 0 1 Γ) = Γ.
induction Γ.
- simpl. reflexivity.
- destruct a. simpl. rewrite IHΓ. pose proof (type_shift_inversion t 0). rewrite H.
  reflexivity. simpl. rewrite IHΓ. reflexivity.
Qed.

Lemma env_shift_inversion_reverse: forall Γ, env_shift 0 1 (env_reverse_shift 0 Γ) = Γ.
induction Γ.
- simpl. reflexivity.
- destruct a. simpl. rewrite IHΓ. rewrite type_shift_inversion_reverse. auto. admit.
  simpl. rewrite IHΓ. auto.
Admitted.

Lemma shift_combine: forall T c d e, shift c d (shift c e T) =
shift c (d + e) T.
induction T.
- intros. simpl. auto.
- intros. simpl. rewrite IHT. auto.
- intros. simpl. rewrite IHT. auto.
- intros. simpl. rewrite IHT1. rewrite IHT2. auto.
- intros. simpl. remember (c <=? n) as b. destruct b. simpl. symmetry in Heqb.
  apply Nat.leb_le in Heqb. assert ((c <=? n+e) = true). apply Nat.leb_le. lia.
  rewrite H. assert (n + e + d = n + (d + e)). lia. rewrite H0. auto.
  simpl. symmetry in Heqb. rewrite Heqb. auto.
- intros. simpl. rewrite IHT. auto.
- intros. simpl. rewrite IHT. auto.
Qed.

Lemma type_shift_combine: forall T c d e, type_shift c d (type_shift c e T) =
type_shift c (d + e) T.
induction T.
- intros. simpl. auto.
- intros. simpl. remember (c <=? n) as b. destruct b. simpl. assert ((c <=? n + e) = true).
  apply Nat.leb_le. symmetry in Heqb. apply Nat.leb_le in Heqb. lia. rewrite H.
  assert (n + e + d = (n + (d + e))). lia. rewrite H0. auto. simpl. symmetry in Heqb. rewrite Heqb.
  auto.
- intros. simpl. rewrite IHT1. rewrite IHT2. auto.
- intros. simpl. rewrite IHT. auto.
Qed.

Lemma type_term_shift_combine: forall t c d e, type_term_shift c d (type_term_shift c e t)
= type_term_shift c (d + e) t. induction t.
- intros. simpl. auto.
- intros. simpl. rewrite IHt. auto.
- intros. simpl. rewrite IHt. rewrite type_shift_combine. auto.
- intros. simpl. rewrite IHt1. rewrite IHt2. auto.
- intros. simpl. auto.
- intros. simpl. rewrite IHt. auto.
- intros. simpl. rewrite IHt. rewrite type_shift_combine. auto.
Qed.

Lemma env_reverse_shift_split: forall m Γ Γ', env_reverse_shift m (Γ ++ Γ') =
env_reverse_shift m Γ ++ env_reverse_shift m Γ'.
intros ? ?. generalize dependent m. induction Γ.
- intros. simpl. auto.
- intros. destruct a. simpl. rewrite IHΓ. auto. simpl. rewrite IHΓ. auto.
Qed.

Lemma env_shift_split: forall c d Γ Γ', env_shift c d (Γ ++ Γ') =
env_shift c d Γ ++ env_shift c d Γ'.
intros ? ? ?.  generalize dependent c. generalize dependent d. induction Γ.
- intros. simpl. auto.
- intros. destruct a. simpl. rewrite IHΓ. auto. simpl. rewrite IHΓ. auto.
Qed.

Lemma env_shift_swap_zero: forall m Γ, env_shift 0 1 (env_reverse_shift m Γ) =
env_reverse_shift (m+1) (env_shift 0 1 Γ).
intros ? ?. generalize dependent m. induction Γ.
- intros. simpl. auto.
- intros. destruct a. simpl. rewrite IHΓ. rewrite type_shift_swap_zero. auto.
  lia. admit. simpl. rewrite IHΓ. auto.
Admitted.

Lemma env_type_subst_zero: forall m U Γ, env_shift 0 1 (env_subst m U Γ)
= env_subst (m+1) (type_shift 0 1 U) (env_shift 0 1 Γ).
intros ? ? ?. generalize dependent m. generalize dependent U. induction Γ.
- intros. simpl. auto.
- intros. destruct a. simpl. rewrite type_subst_dist_zero. rewrite IHΓ. auto. lia. 
  simpl. rewrite IHΓ. auto.
Qed.

Lemma count_env_type_bind_shift: forall c d Γ, count_env_type_bind Γ =
count_env_type_bind (env_shift c d Γ). intros ? ? ?. generalize dependent d. 
generalize dependent c. induction Γ. intros. simpl. auto. intros. destruct a. simpl. apply IHΓ.
simpl. symmetry in IHΓ. rewrite IHΓ. auto. Qed.

Lemma count_env_type_bind_reverse: forall m Γ, count_env_type_bind Γ =
count_env_type_bind (env_reverse_shift m Γ). intros ? ?. generalize dependent m.
induction Γ. intros. simpl. auto. intros. destruct a. simpl. apply IHΓ.
simpl. symmetry in IHΓ. rewrite IHΓ. auto. Qed.

Lemma count_env_var_bind_shift: forall c d Γ, count_env_var_bind Γ =
count_env_var_bind (env_shift c d Γ). intros ? ? ?. generalize dependent d.
generalize dependent c. induction Γ. intros. simpl. auto.
intros. destruct a. simpl. rewrite IHΓ with (c:=c) (d:=d). auto. simpl. 
rewrite IHΓ with (c:=c) (d:=d). auto. Qed. 

Lemma env_shift_combine: forall c d e Γ, env_shift c d (env_shift c e Γ) =
env_shift c (d + e) Γ. intros ? ? ? ?. generalize dependent e. generalize dependent d. 
generalize dependent c. induction Γ.
- intros. simpl. auto.
- intros. destruct a. simpl. rewrite IHΓ. rewrite type_shift_combine. auto.
  simpl. rewrite IHΓ. auto.
Qed.

Lemma env_with_one_less_type_var: forall Γ' Γ Γ0 m S U, 
env Γ -> Γ = Γ' ++ env_type_bind :: Γ0 -> m = count_env_type_bind Γ'
-> U = type_shift 0 (m + 1) S -> env (env_reverse_shift m (env_subst m U Γ' ++ Γ0)).
intros ? ? ? ? ? ? ?. generalize dependent Γ'. generalize dependent Γ0.
generalize dependent m. generalize dependent S. generalize dependent U. induction H.
- intros. destruct Γ'. inversion H. simpl in H. inversion H.
- intros. destruct Γ'. inversion H0. simpl. simpl in H1. rewrite H1.
  rewrite env_shift_inversion. apply H. destruct e. simpl in H0. inversion H0. 
  simpl in H0. simpl in H1. inversion H0. simpl. remember (count_env_type_bind Γ') as m'.
  assert (env_reverse_shift 0 (env_shift 0 1 Γ) 
  = env_reverse_shift 0 (Γ' ++ env_type_bind :: Γ0)). rewrite H4. auto.
  rewrite env_shift_inversion in H3. rewrite env_reverse_shift_split in H3. simpl in H3.
  pose proof (IHenv (type_shift 0 (m' + 1) S) S m' 
  (env_reverse_shift 0 Γ0) (env_reverse_shift 0 Γ') H3).
  assert (m' = count_env_type_bind (env_reverse_shift 0 Γ')). 
  rewrite count_env_type_bind_reverse with (m:=0) in Heqm'. apply Heqm'.
  assert (type_shift 0 (m' + 1) S = type_shift 0 (m' + 1) S). auto.
  pose proof (H5 H6 H7). remember (env_reverse_shift m' (env_subst m' (type_shift 0 (m' + 1) S)
  (env_reverse_shift 0 Γ') ++ env_reverse_shift 0 Γ0)) as Γ0'. assert (env (env_type_bind :: env_shift 0 1 Γ0')).
  constructor. apply H8. rewrite HeqΓ0' in H9. rewrite env_shift_swap_zero in H9. rewrite env_shift_split in H9.
  rewrite env_type_subst_zero in H9. symmetry in H1. rewrite H1 in H9. rewrite type_shift_combine in H9.
  assert (1 + m = m + 1). lia. rewrite H10 in H9.
  symmetry in H2. rewrite H2 in H9. rewrite env_shift_inversion_reverse in H9. rewrite env_shift_inversion_reverse in H9.
  apply H9.
- intros. destruct Γ'. inversion H0. destruct e. simpl in H0. inversion H0. simpl.
  constructor. apply IHenv with (S:=S). auto. simpl in H1. auto. auto. simpl in H0. inversion H0.
Qed.

Lemma shift_equal: forall T U c d, type_shift c d T = type_shift c d U -> T = U.
induction T.
- intros. simpl in H. destruct U. reflexivity. simpl in H. destruct (c <=? n).
  inversion H. inversion H. simpl in H. inversion H. simpl in H. inversion H.
- intros. simpl in H. destruct U. simpl in H. destruct (c <=? n). inversion H. inversion H.
  simpl in H. remember (c <=? n) as b1. remember (c <=? n0) as b2. destruct b1, b2.
  inversion H. assert (n = n0). lia. subst. auto. symmetry in Heqb1. apply Nat.leb_le in Heqb1.
  symmetry in Heqb2. apply Nat.leb_gt in Heqb2. inversion H. lia. symmetry in Heqb1. 
  apply Nat.leb_gt in Heqb1. symmetry in Heqb2. apply Nat.leb_le in Heqb2. inversion H. lia.
  auto. destruct (c <=? n). simpl in H. inversion H. simpl in H. inversion H.
  destruct (c <=? n). simpl in H. inversion H. simpl in H. inversion H.
- intros. simpl in H. destruct U. simpl in H. inversion H. simpl in H. destruct (c <=? n).
  inversion H. inversion H. simpl in H. inversion H. rewrite IHT1 with (U:=U1)(c:=c)(d:=d).
  rewrite IHT2 with (U:=U2)(c:=c)(d:=d). auto. auto. auto. simpl in H. inversion H.
- intros. simpl in H. destruct U. simpl in H. inversion H. simpl in H. destruct (c <=? n).
  inversion H. inversion H. simpl in H. inversion H. simpl in H. inversion H.
  rewrite IHT with (U:=U)(c:=c+1)(d:=d). auto. auto.
Qed.

Lemma get_var_type_and_shift: forall c d k Γ T, get_var_type k Γ = Some T <->
get_var_type k (env_shift c d Γ) = Some (type_shift c d T).
split. intros. generalize dependent c. generalize dependent d. generalize dependent k.
generalize dependent T. induction Γ. intros.
- simpl. simpl in H. inversion H.
- intros. destruct a. simpl in H. simpl. remember (k =? 0) as b. destruct b. inversion H.
  subst. auto. apply IHΓ. apply H. simpl. simpl in H. apply IHΓ. apply H.
- intros. generalize dependent c. generalize dependent d. generalize dependent k.
generalize dependent T. induction Γ. intros. simpl. simpl in H. inversion H.
intros. destruct a. simpl in H. simpl. remember (k =? 0) as b. destruct b. inversion H.
apply shift_equal in H1. subst. auto. apply IHΓ with (d:=d) (c:=c). apply H. simpl. apply IHΓ with (d:=d) (c:=c).
apply H.
Qed.

Lemma get_var_type_and_subst_func: forall Γ k T m U, get_var_type k Γ = Some T
-> get_var_type k (env_subst m U Γ) = Some ([[[m |→ U]]] T). induction Γ.
- intros. simpl in H. inversion H.
- intros. destruct a. simpl. simpl in H. remember (k=?0) as b. destruct b.
  symmetry in Heqb. inversion H. subst. auto. apply IHΓ. auto.
  simpl. simpl in H. apply IHΓ. auto.
Qed.

Lemma get_var_type_and_subst_prep: forall T Γ' k m Γ0 S U, get_var_type k (Γ' ++ env_type_bind :: Γ0) = Some T 
-> env (Γ' ++ env_type_bind :: Γ0)
-> m = count_env_type_bind Γ' 
-> U = type_shift 0 (m + 1) S
-> get_var_type k (env_reverse_shift m (env_subst m U (Γ' ++ Γ0))) = 
Some (type_reverse_shift m ([[[m |→ U]]] T)).
intros. remember (Γ' ++ env_type_bind :: Γ0) as Γ''. generalize dependent Γ'.
generalize dependent U. generalize dependent S. generalize dependent Γ0. generalize dependent m.
generalize dependent k. generalize dependent T. induction H0.
- intros. simpl in HeqΓ''. destruct Γ'. simpl in HeqΓ''. inversion HeqΓ''.
simpl in HeqΓ''. inversion HeqΓ''.
- intros. destruct Γ'. simpl in HeqΓ''. inversion HeqΓ''. simpl in H1. rewrite H1.
  simpl in H. simpl. apply (get_var_type_and_shift 0 1 k). rewrite env_shift_inversion_reverse.
  rewrite type_shift_inversion_reverse. rewrite H4. rewrite H4 in H.
  apply get_var_type_and_subst_func. apply H. rewrite free_var_in_type_subst. auto. rewrite H2. rewrite free_var_in_type_shift. auto.
  lia.
  simpl in HeqΓ''. inversion HeqΓ''. simpl.
  simpl in H. assert (get_var_type k Γ = Some (type_reverse_shift 0 T)).
  assert (T = type_shift 0 1 (type_reverse_shift 0 T)). rewrite type_shift_inversion_reverse.
  auto. admit. rewrite H3 in H.
  apply (get_var_type_and_shift 0 1 k). auto.
  pose proof (IHenv (type_reverse_shift 0 T) k H3).
  pose proof (H6 (m-1) (env_reverse_shift 0 Γ0) S (type_reverse_shift 0 U)).
  symmetry in H4. rewrite H4 in H1. simpl in H1. 
  assert (type_reverse_shift 0 U = type_shift 0 (m - 1 + 1) S).
  assert (U = type_shift 0 1 (type_shift 0 m S)). rewrite H2. rewrite type_shift_combine.
  assert (m+1=1+m). lia. rewrite H8. auto. rewrite H8. rewrite type_shift_inversion.
  assert (m-1+1=m). lia. rewrite H9. auto.
  assert (env_reverse_shift 0 (env_shift 0 1 Γ) = Γ). rewrite env_shift_inversion. auto.
  rewrite H5 in H9. rewrite env_reverse_shift_split in H9. simpl in H9. symmetry in H7.
  assert (m - 1 = count_env_type_bind (env_reverse_shift 0 Γ')).
  rewrite count_env_type_bind_reverse with (m:=0) in H1. lia. symmetry in H9.
  pose proof (H7 H8 _ H9 H10). symmetry in H11. apply (get_var_type_and_shift 0 1) in H11.
  rewrite env_shift_swap_zero in H11. rewrite type_shift_swap_zero in H11.
  pose proof env_reverse_shift_split. symmetry in H12. rewrite H12 in H11.
  rewrite env_type_subst_zero in H11. rewrite type_subst_dist_zero in H11.
  rewrite type_shift_inversion_reverse in H11.
  rewrite type_shift_inversion_reverse in H11.
  rewrite env_shift_inversion_reverse in H11. assert (m - 1 + 1 = m). lia.
  rewrite H13 in H11. auto. admit. rewrite H2. 
  rewrite free_var_in_type_shift. auto. lia. lia. lia. rewrite free_var_in_type_subst.
  auto. rewrite H2. assert ((type_shift 0 (m + 1) S) = type_shift 0 1 (type_shift 0 (m - 1 + 1) S)).
  rewrite type_shift_combine. assert (m + 1 = 1 + (m - 1 + 1)).
  lia. rewrite H12. auto. rewrite H12. rewrite type_shift_inversion.
  rewrite free_var_in_type_shift_zero. auto.
- intros. simpl in H. remember (k =? 0) as b. destruct b. destruct Γ'. simpl in HeqΓ''.
  inversion HeqΓ''. simpl in HeqΓ''. inversion HeqΓ''. simpl. symmetry in Heqb. rewrite Heqb.
  inversion H. subst. auto. destruct Γ'. simpl in HeqΓ''. inversion HeqΓ''. simpl in HeqΓ''.
  inversion HeqΓ''. simpl. symmetry in Heqb. rewrite Heqb. apply IHenv with (S:=S).
  auto. auto. auto. symmetry in H4. rewrite H4 in H1. simpl in H1. auto.
Admitted.

Lemma get_var_type_and_subst: forall T Γ' k m Γ0 S U, get_var_type k (Γ' ++ env_type_bind :: Γ0) = Some T 
-> env (Γ' ++ env_type_bind :: Γ0)
-> m = count_env_type_bind Γ' 
-> U = type_shift 0 (m + 1) S
-> get_var_type k (env_reverse_shift m (env_subst m U Γ' ++ Γ0)) = 
Some (type_reverse_shift m ([[[m |→ U]]] T)).
intros. assert (env_subst m U Γ' ++ Γ0 = env_subst m U (Γ' ++ Γ0)). admit. rewrite H3.
apply get_var_type_and_subst_prep with (S:=S). auto. auto. auto. auto.
Admitted.

Lemma th23_5_1_type_prep: forall Γ Γ' m t T S U, Γ' ++ env_type_bind :: Γ |- t : T ->
m = count_env_type_bind Γ' ->
U = type_shift 0 (m + 1) S ->
env_reverse_shift m ((env_subst m U Γ') ++ Γ) |- (type_term_reverse_shift m ([[m |→ U]] t))
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
  assert (env_reverse_shift (m + 1) (env_subst (m + 1) (type_shift 0 1 U) (env_shift 0 1 Γ') ++ env_shift 0 1 Γ0)
  = env_shift 0 1 (env_reverse_shift m (env_subst m U Γ' ++ Γ0))).
  rewrite env_shift_swap_zero. assert (env_shift 0 1 (env_subst m U Γ' ++ Γ0) = 
  env_subst (m + 1) (type_shift 0 1 U) (env_shift 0 1 Γ') ++ env_shift 0 1 Γ0).
  rewrite env_shift_split. rewrite env_type_subst_zero. auto. rewrite H6. auto.
  rewrite H6 in H3. apply H3. rewrite HeqΓ''. rewrite env_shift_split. simpl. auto. 
  pose proof (count_env_type_bind_shift). symmetry in H7. rewrite H7. lia. rewrite H2.
  rewrite type_shift_combine. assert (1 + (m + 1) = m + 2). lia. rewrite H7. auto.
- intros. simpl. simpl in IHtype_bind. pose proof (TTApp (env_reverse_shift m (env_subst m U Γ' ++ Γ0)) 
(type_term_reverse_shift m
([[m |→ U]] t)) (type_reverse_shift (m + 1)
([[[(m + 1)
 |→ type_shift 0 1 U]]] T)) (type_reverse_shift m
([[[m |→ U]]] T'))). assert (env (env_reverse_shift m (env_subst m U Γ' ++ Γ0))).
 apply env_with_one_less_type_var with (Γ:=Γ)(S:=S). auto. auto. auto. auto.
 assert (env_reverse_shift m (env_subst m U Γ' ++ Γ0)
 |- type_term_reverse_shift m
      ([[m |→ U]] t) : ∀ type_reverse_shift (m + 1)
      ([[[(m + 1)
       |→ type_shift 0 1 U]]] T)). 
pose proof (IHtype_bind U S m Γ0 Γ'). assert (Datatypes.S m = m + 1). lia. rewrite H6 in H5.
apply H5. auto. auto. auto. pose proof (H3 H4 H5). 
remember (type_reverse_shift 0
([[[0
 |→ type_shift 0 1
      (type_reverse_shift m ([[[m |→ U]]] T'))]]] 
 type_reverse_shift (m + 1)
   ([[[m + 1 |→ type_shift 0 1 U]]] T))) as leftT.
remember ( type_reverse_shift m
([[[m
 |→ U]]] type_reverse_shift 0
           ([[[0 |→ type_shift 0 1 T']]] T))) as rightT.
assert (leftT = rightT).
pose proof (type_shift_inversion leftT m).
remember (type_reverse_shift m (type_shift m 1 leftT)) as leftT'. rewrite HeqleftT in HeqleftT'.
remember ( ([[[0 |→ type_shift 0 1 (type_reverse_shift m ([[[m |→ U]]] T'))]]] 
    type_reverse_shift (m + 1) ([[[m + 1 |→ type_shift 0 1 U]]] T))) as leftT''.
pose proof (type_shift_swap_m leftT'' m 0). assert (m >= 0). lia.
assert (has_free_var_in_type 0 leftT'' = false). 
subst. apply free_var_in_type_subst. apply free_var_in_type_shift. lia. pose proof (H8 H9 H10). rewrite H11 in HeqleftT'.
rewrite HeqleftT'' in HeqleftT'. remember (type_shift 0 1 (type_reverse_shift m ([[[m |→ U]]] T'))) as U'.
remember (type_reverse_shift (m + 1) ([[[m + 1 |→ type_shift 0 1 U]]] T)) as leftT'''.
pose proof (type_subst_dist_m leftT''' m 0 U'). apply H12 in H9. rewrite H9 in HeqleftT'.
rewrite HeqleftT''' in HeqleftT'. rewrite H7 in HeqleftT'. 
assert (type_shift 0 1 (type_reverse_shift m ([[[m |→ U]]] T')) =
type_reverse_shift (m + 1) (type_shift 0 1 ([[[m |→ U]]] T'))). apply type_shift_swap_zero. lia.
apply free_var_in_type_subst. rewrite H2. apply free_var_in_type_shift_zero.
rewrite H13 in HeqU'. remember (type_shift (m + 1) 1 U') as U''. rewrite HeqU' in HeqU''.
assert (U'' = (type_shift 0 1 ([[[m |→ U]]] T'))). rewrite HeqU''. apply type_shift_inversion_reverse.
apply free_var_in_type_shift_prep_2. lia. apply free_var_in_type_subst. rewrite H2. apply free_var_in_type_shift_zero.
remember (type_shift (m + 1) 1 (type_reverse_shift (m + 1) ([[[m + 1 |→ type_shift 0 1 U]]] T))) as T''.
assert (T'' = [[[m + 1 |→ type_shift 0 1 U]]] T). rewrite HeqT''. apply type_shift_inversion_reverse.
apply free_var_in_type_subst. apply free_var_in_type_shift_prep_2. lia. rewrite H2.
apply free_var_in_type_shift_zero.
pose proof free_var_in_type_shift.
remember ([[[m |→ U]]] type_reverse_shift 0 ([[[0 |→ type_shift 0 1 T']]] T)) as rightT'.
pose proof (type_shift_inversion rightT' 0). symmetry in H17. remember (type_shift 0 1 rightT') as rightT''.
rewrite HeqrightT' in HeqrightT''. 
pose proof (type_subst_dist_zero (type_reverse_shift 0 ([[[0 |→ type_shift 0 1 T']]] T)) 0 m U).
assert (m>=0). lia. apply H18 in H19. rewrite H19 in HeqrightT''.
remember (type_shift 0 1 (type_reverse_shift 0 ([[[0 |→ type_shift 0 1 T']]] T))) as V.
assert (V = [[[0 |→ type_shift 0 1 T']]] T). rewrite HeqV. apply type_shift_inversion_reverse.
apply free_var_in_type_subst. apply free_var_in_type_shift_zero. rewrite H20 in HeqrightT''.
rewrite type_subst_dist_subs in HeqrightT''. rewrite type_subst_dist_zero in H14.
rewrite HeqleftT'. rewrite H14. rewrite H15. rewrite HeqrightT. rewrite H17.
rewrite HeqrightT''. reflexivity. lia. lia. apply free_var_in_type_shift_zero.
apply free_var_in_type_shift_zero.  
rewrite H7 in H6. apply H6.
Qed.

Lemma env_one_less_var_bind: forall Γ Γ' T, env (Γ ++ env_var_bind T :: Γ') -> env (Γ ++ Γ').
intros. remember (Γ ++ env_var_bind T :: Γ') as Γ''. generalize dependent T.
generalize dependent Γ. generalize dependent Γ'. induction H.
- intros. destruct Γ. simpl in HeqΓ''. inversion HeqΓ''. simpl in HeqΓ''. inversion HeqΓ''.
- intros. destruct Γ0. simpl in HeqΓ''. inversion HeqΓ''. simpl in HeqΓ''. inversion HeqΓ''.
  pose proof (IHenv (env_reverse_shift 0 Γ') (env_reverse_shift 0 Γ0) (type_reverse_shift 0 T)).
  assert (env_reverse_shift 0 (env_shift 0 1 Γ) = Γ). rewrite env_shift_inversion. auto.
  rewrite H2 in H3. symmetry in H3. rewrite env_reverse_shift_split in H3. simpl in H3.
  apply H0 in H3. simpl. 
  pose proof (env_type_bind_cons (env_reverse_shift 0 Γ0 ++ env_reverse_shift 0 Γ') H3).
  rewrite env_shift_split in H4. rewrite env_shift_inversion_reverse in H4.
  rewrite env_shift_inversion_reverse in H4. auto.
- intros. destruct Γ0. simpl in HeqΓ''. inversion HeqΓ''. simpl. subst. auto.
  simpl in HeqΓ''. inversion HeqΓ''. simpl. pose proof (IHenv Γ' Γ0 T0 H2).
  apply (env_var_bind_cons T (Γ0 ++ Γ') H0).
Qed.

Lemma shift_and_type_term_shift: forall t c d c' d', shift c d (type_term_shift c' d' t)
= type_term_shift c' d' (shift c d t). intro. induction t.
- intros. simpl. auto.
- intros. simpl. rewrite IHt. auto.
- intros. simpl. rewrite IHt. auto.
- intros. simpl. rewrite IHt1. rewrite IHt2. auto.
- intros. simpl. remember (c <=? n) as b. destruct b. simpl. auto. simpl. auto.
- intros. simpl. rewrite IHt. auto.
- intros. simpl. rewrite IHt. auto.
Qed.

Lemma env_type_shift_and_shift_prep1: Lemma env_type_shift_and_shift: forall Γ' s S Γ n m,
Γ |- s : S ->
n = count_env_var_bind Γ' ->
m = count_env_type_bind Γ' ->
Γ' ++ Γ |- shift 0 n (type_term_shift 0 m s) : type_shift 0 m S.
induction Γ'. intros. simpl. simpl in H0. simpl in H1. rewrite H0. rewrite H1.
rewrite type_term_shift_zero. rewrite type_shift_zero. admit.
intros. destruct a. simpl in H0. simpl in H1. simpl. 
pose proof (IHΓ' s S Γ (n - 1) m). admit.
simpl. simpl in H0. simpl in H1. pose proof (IHΓ' s S Γ n (m - 1)). *)
 forall Γ' s S Γ n m,
Γ |- s : S ->
n = count_env_var_bind Γ' ->
m = count_env_type_bind Γ' ->
Γ' ++ Γ |- shift 0 n (type_term_shift 0 m s) : type_shift 0 m S.
induction Γ'. intros. simpl. simpl in H0. simpl in H1. rewrite H0. rewrite H1.
rewrite type_term_shift_zero. rewrite type_shift_zero. admit.
intros. destruct a. simpl in H0. simpl in H1. simpl. 
pose proof (IHΓ' s S Γ (n - 1) m). admit.
simpl. simpl in H0. simpl in H1. pose proof (IHΓ' s S Γ n (m - 1)).

(* Lemma env_type_shift_and_shift: forall Γ' s S Γ n m,
Γ |- s : S ->
n = count_env_var_bind Γ' ->
m = count_env_type_bind Γ' ->
Γ' ++ Γ |- shift 0 n (type_term_shift 0 m s) : type_shift 0 m S.
induction Γ'. intros. simpl. simpl in H0. simpl in H1. rewrite H0. rewrite H1.
rewrite type_term_shift_zero. rewrite type_shift_zero. admit.
intros. destruct a. simpl in H0. simpl in H1. simpl. 
pose proof (IHΓ' s S Γ (n - 1) m). admit.
simpl. simpl in H0. simpl in H1. pose proof (IHΓ' s S Γ n (m - 1)). *)


Lemma th23_5_1_var_prep: forall S S' Γ Γ' t T n m s s', 
Γ |- s : S ->
n = count_env_var_bind Γ' ->
m = count_env_type_bind Γ' ->
S' = type_shift 0 m S ->
s' = type_term_shift 0 m s ->
Γ' ++ env_var_bind S' :: (env_shift 0 m Γ) |- t : T ->
Γ' ++ (env_shift 0 m Γ) |- reverse_shift n ([n |→ shift 0 (n + 1) s'] t) : T.
intros. remember (Γ' ++ env_var_bind S' :: env_shift 0 m Γ) as Γ''. generalize dependent Γ'.
generalize dependent s. generalize dependent S. generalize dependent S'. generalize dependent Γ. 
generalize dependent n. generalize dependent m. generalize dependent s'. induction H4.
- intros. simpl. constructor. apply env_one_less_var_bind with (T:=S'). rewrite HeqΓ'' in H.
  auto.
- intros. simpl. constructor. apply env_one_less_var_bind with (T:=S'). rewrite HeqΓ'' in H.
  auto. apply IHtype_bind with (S':=S') (S:=S) (s:=s). auto. auto. auto. auto. auto. auto.
- intros. simpl. remember (k =? n) as b. destruct b.
  + assert (reverse_shift n (shift 0 (n + 1) s') = shift 0 n s'). admit. rewrite H6. admit.
  + simpl. remember (n <=? k) as b. destruct b. symmetry in Heqb0.
  constructor. apply env_one_less_var_bind with (T:=S'). rewrite HeqΓ'' in H. apply H.
  assert (n < k). apply Nat.leb_le in Heqb0. symmetry in Heqb. apply Nat.eqb_neq in Heqb. lia.
  admit. symmetry in Heqb0. apply Nat.leb_gt in Heqb0. admit.
- intros. simpl. constructor. apply env_one_less_var_bind with (T:=S'). rewrite HeqΓ'' in H.
  apply H. pose proof (IHtype_bind s' m (n+1) Γ0 S' S H2). assert (Datatypes.S n = n + 1).
  lia. rewrite H7. rewrite shift_combine. assert (1 + (n+1) = (n+1+1)). lia. rewrite H8.
  apply H6 with (Γ':=env_var_bind T1::Γ') (s:=s). auto. auto. simpl. auto. simpl. auto.
  simpl. rewrite HeqΓ''. auto.
- intros. simpl. apply TApp' with (T11:=T11). apply env_one_less_var_bind with (T:=S').
  rewrite HeqΓ'' in H. auto. apply IHtype_bind1 with (S':=S') (S:=S) (s:=s).
  auto. auto. auto. auto. auto. auto. apply IHtype_bind2 with (S':=S') (S:=S) (s:=s).
  auto. auto. auto. auto. auto. auto.
- intros. simpl. constructor. apply env_one_less_var_bind with (T:=S'). symmetry in HeqΓ''.
  rewrite HeqΓ''. auto. assert (type_term_shift 0 1 (shift 0 (n + 1) s') =
  shift 0 (n + 1) (type_term_shift 0 1 s')). rewrite shift_and_type_term_shift. auto. rewrite H6.
  assert (type_term_shift 0 1 s' = type_term_shift 0 (m+1) s). rewrite H3.
  rewrite type_term_shift_combine. assert (1+m=m+1). lia. rewrite H7. auto. rewrite H7.
  pose proof IHtype_bind (type_term_shift 0 (m+1) s) (m+1) n Γ0 (type_shift 0 (m+1) S) S.
  assert (type_shift 0 (m+1) S = type_shift 0 (m+1) S). reflexivity. 
  apply H8 with (s:=s) (Γ':=env_type_bind::env_shift 0 1 Γ') in H9. simpl in H9.
  rewrite env_shift_split. rewrite env_shift_combine. assert (1+m=m+1). lia. rewrite H10.
  apply H9. auto. auto. simpl. pose proof (count_env_var_bind_shift). symmetry in H10.
  rewrite H10. auto. simpl. pose proof (count_env_type_bind_shift). symmetry in H10.
  rewrite H10. auto. simpl. rewrite HeqΓ''. rewrite env_shift_split. simpl.
  rewrite env_shift_combine. rewrite H2. rewrite type_shift_combine. assert (1+m=m+1).
  lia. rewrite H10. auto. 
- intros. simpl. constructor. apply env_one_less_var_bind with (T:=S'). rewrite HeqΓ'' in H.
  auto. apply IHtype_bind with (S':=S') (S:=S) (s:=s). auto. auto. auto. auto. auto. auto.
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
    pose proof (th23_5_1_var_prep T11 T11 Γ nil t12 T12). simpl in H3. 
    pose proof (H3 0 0 t2 t2 H1). simpl in H4. pose proof (env_shift_zero Γ).
    rewrite H5 in H4. apply H4. auto. auto. rewrite type_shift_zero. auto.
    rewrite type_term_shift_zero. auto. auto. 
+ intros. inversion H1.
+ intros. inversion H1.
    - subst. apply IHtype_bind in H5. apply TTApp. auto. auto.
    - subst. inversion H0. subst. 
    pose proof (th23_5_1_type_prep (env_shift 0 1 Γ) nil 0 t0 T T' (type_shift 0 1 T') H6).
    simpl in H2. assert (0 = 0). auto. assert (type_shift 0 1 T' = type_shift 0 1 T'). auto.
    apply H2 in H3. pose proof (env_shift_inversion Γ). rewrite H7 in H3.
    apply H3. apply H4.
Qed.