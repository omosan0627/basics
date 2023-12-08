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

Lemma shift_id: forall s n, shift n 0 s = s. induction s.
- now simpl.
- now simpl.
- intros. simpl. now rewrite IHs1, IHs2, IHs3.
- intros. simpl. remember (n0 <=? n). destruct b. now replace (n + 0) with n. reflexivity.
- intros. simpl. rewrite IHs. reflexivity.
- intros. simpl. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

Lemma shift_inversion: forall s c n, reverse_shift (c + n) (shift c (n + 1) s) = shift c n s.
induction s.
- intros. now simpl.
- intros. now simpl.
- intros. simpl. now rewrite IHs1, IHs2, IHs3.
- intros. simpl. remember (c <=? n). destruct b. simpl. 
replace (c + n0 <=? n + (n0 + 1)) with true. replace (pred (n + (n0 + 1))) with (n + n0).
reflexivity. lia. symmetry. symmetry in Heqb. apply Nat.leb_le. apply Nat.leb_le in Heqb.
lia. simpl. replace (c + n0 <=? n) with false. reflexivity.
symmetry. symmetry in Heqb. apply Nat.leb_nle. apply Nat.leb_nle in Heqb. lia. 
- intros. simpl. replace (S (c + n)) with ((S c) + n). now rewrite IHs. lia.
- intros. simpl. now rewrite IHs1, IHs2. Qed.

Lemma shift_addition: forall s n d1 d2, shift n d1 (shift n d2 s) = shift n (d1 + d2) s.
induction s.
- intros. now simpl.
- intros. now simpl.
- intros. simpl. now rewrite IHs1, IHs2, IHs3.
- intros. simpl. remember (n0 <=? n). destruct b. simpl.
  replace (n0 <=? n + d2) with true. replace (n + d2 + d1) with (n + (d1 + d2)).
  reflexivity. lia. symmetry. symmetry in Heqb. apply Nat.leb_le.
  apply Nat.leb_le in Heqb. lia. simpl. symmetry in Heqb; rewrite Heqb. reflexivity.
- intros. simpl. rewrite IHs. reflexivity.
- intros. simpl. now rewrite IHs1, IHs2. Qed.

Lemma get_var_type_eq: forall Γ' n T Γ, length Γ' = n -> 
get_var_type n (Γ' ++ T :: Γ) = Some T. induction Γ'.
simpl. intros. replace (n =? 0) with true. reflexivity. symmetry. apply Nat.eqb_eq.
now rewrite H.
intros. simpl. simpl in H. replace (n =? 0) with false.
apply IHΓ'. lia. symmetry. apply Nat.eqb_neq. lia. Qed.

Lemma get_var_type_gt: forall Γ' k T Γ, length Γ' < k -> 
get_var_type k (Γ' ++ T :: Γ) = get_var_type (pred k) (Γ' ++ Γ).
induction Γ'. intros. simpl. simpl in H. replace (k =? 0) with false.
reflexivity. symmetry. apply Nat.eqb_neq. lia.
intros. simpl in H. simpl. replace (k =? 0) with false.
replace (pred k =? 0) with false. 
apply IHΓ'. lia. symmetry. apply Nat.eqb_neq. lia. symmetry. apply Nat.eqb_neq. lia.
Qed.

Lemma get_var_type_lt: forall Γ' Γ k, length Γ' > k ->
get_var_type k (Γ' ++ Γ) = get_var_type k Γ'. induction Γ'.
intros. simpl in H. inversion H. intros. simpl. simpl in H.
remember (k =? 0). destruct b. reflexivity. apply IHΓ'. 
symmetry in Heqb. apply Nat.eqb_neq in Heqb. lia. Qed.

Lemma type_shift: forall Γ' Γ t T S, Γ' ++ Γ |- t : T -> 
Γ' ++ S :: Γ |- shift (length Γ') 1 t : T.
intros. remember (Γ' ++ Γ) as Γ''. generalize dependent Γ'. generalize dependent Γ.
generalize dependent S. induction H.
- intros. simpl. constructor.
- intros. simpl. constructor.
- intros. simpl. constructor. now apply IHtype_step1. now apply IHtype_step2. 
  now apply IHtype_step3.
- intros. simpl. remember (length Γ' <=? k). destruct b. 
  + constructor. pose proof (get_var_type_gt Γ' (k + 1) S Γ0). assert (length Γ' < k + 1).
    symmetry in Heqb. apply Nat.leb_le in Heqb. lia. apply H0 in H1. rewrite H1.
    replace (pred (k + 1)) with k.  rewrite HeqΓ'' in H. apply H. lia.
  + constructor. pose proof (get_var_type_lt Γ' (S :: Γ0) k).
    pose proof (get_var_type_lt Γ' Γ0 k). assert (length Γ' > k). symmetry in Heqb. 
    apply Nat.leb_nle in Heqb. lia. pose proof (H1 H2). pose proof (H0 H2).
    rewrite HeqΓ'' in H. rewrite H3 in H. rewrite H4. now rewrite H.
- intros. simpl. constructor. pose proof (IHtype_step S Γ0 (T1 :: Γ')).
subst. assert (T1 :: Γ' ++ Γ0 = (T1 :: Γ') ++ Γ0). now simpl. apply H0 in H1.
replace (Datatypes.S (length Γ')) with (length (T1 :: Γ')). apply H1. simpl. lia.
- intros. simpl. refine (TApp _ _ T11 _ _ _ _). now apply IHtype_step1.
  now apply IHtype_step2. Qed.


(* 賢く帰納法回すと行けます。*)

Lemma lem9_3_8_prep: forall S Γ Γ' t T, Γ' ++ S :: Γ |- t : T -> forall n s,
length Γ' = n -> Γ' ++ Γ |- shift 0 n s : S -> 
Γ' ++ Γ |- reverse_shift n ([n |→ shift 0 (n + 1) s] t) : T.
intros ? ? ? ? ? ?. remember (Γ' ++ S :: Γ) as Γ''.
generalize dependent S. generalize dependent Γ.
generalize dependent Γ'.
induction H.
- intros. simpl. constructor.
- intros. simpl. constructor.
- intros. simpl. constructor. 
  + refine (IHtype_step1 _ _ _ HeqΓ'' _ _ H2 H3).
  + refine (IHtype_step2 _ _ _ HeqΓ'' _ _ H2 H3).
  + refine (IHtype_step3 _ _ _ HeqΓ'' _ _ H2 H3).
- intros. simpl. remember (k =? n). destruct b. 
  pose proof (shift_inversion s 0 n). simpl in H2.
  rewrite H2. symmetry in Heqb. apply Nat.eqb_eq in Heqb. subst. 
  pose proof (get_var_type_eq Γ' (length Γ') S Γ0). assert (length Γ' = length Γ').
  reflexivity. apply H0 in H3. rewrite H3 in H. inversion H. now subst. 
  simpl. remember (n <=? k). destruct b.
  + symmetry in Heqb. apply Nat.eqb_neq in Heqb. symmetry in Heqb0. apply Nat.leb_le in Heqb0.
    assert (n < k). lia. constructor. subst. 
    pose proof (get_var_type_gt Γ' k S Γ0 H2). now rewrite H0 in H.
  + constructor. rewrite HeqΓ'' in H. 
    pose proof (get_var_type_lt Γ' (S :: Γ0) k). pose proof (get_var_type_lt Γ' Γ0 k).
    assert (length Γ' > k). symmetry in Heqb0. apply Nat.leb_nle in Heqb0. lia.
    pose proof (H2 H4). pose proof (H3 H4). rewrite H5 in H. rewrite H6. rewrite H. reflexivity.
- intros. simpl. constructor.
  pose proof (IHtype_step (T1 :: Γ') Γ0 S).
  assert (T1 :: Γ = (T1 :: Γ') ++ S :: Γ0). rewrite HeqΓ''. simpl.
  reflexivity. pose proof (H2 H3 (n + 1) s).
  assert (length (T1 :: Γ') = n + 1). simpl. rewrite H0. lia.
  apply H4 in H5. replace (Datatypes.S n) with (n + 1).
  pose proof (shift_addition s 0 1 (n + 1)). rewrite H6.
  replace (1 + (n + 1)) with (n + 1 + 1).
  now replace (T1 :: Γ' ++ Γ0) with ((T1 :: Γ') ++ Γ0).
  lia. lia. pose proof (type_shift nil (Γ' ++ Γ0) (shift 0 n s) S T1). simpl in H6.
  apply H6 in H1. replace (shift 0 (n + 1) s) with (shift 0 1 (shift 0 n s)).
  apply H1. replace (n + 1) with (1 + n). apply shift_addition. lia.
- intros. simpl. refine (TApp _ _ T11 _ _ _ _). 
  refine (IHtype_step1 _ _ _ _ _ _ H1 H2). auto.
  refine (IHtype_step2 _ _ _ _ _ _ H1 H2). auto. Qed.

Corollary lem9_3_8: forall Γ S t T s, S :: Γ |- t : T -> Γ |- s : S
-> Γ |- reverse_shift 0 ([0 |→ shift 0 1 s] t) : T.
intros. pose proof (lem9_3_8_prep S Γ nil t T). 
assert (nil ++ S :: Γ = S :: Γ). now simpl. rewrite H2 in H1. 
apply H1 with (n:=0) (s:=s) in H. now simpl in H. now simpl. replace (shift 0 0 s) with s.
apply H0. pose proof (shift_id s). now rewrite H3. Qed.

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

Inductive multi_term_step: term -> term -> Prop:=
  | Refl: forall t, multi_term_step t t
  | Trans: forall t1 t2 t3, term_step t1 t2 -> multi_term_step t2 t3 -> multi_term_step t1 t3.
 
Notation "t1 -→* t2" := (multi_term_step t1 t2) (at level 62).

Fixpoint R (T: type) (t:term): Prop :=
  match T with
  | Bool => exists t', value t' /\ t -→* t'
  | T1 → T2 => (exists t', value t' /\ t -→* t') /\ (forall s, R T1 s -> R T2 (t ◦ s))
  end.

Lemma lem12_1_3: forall t T, R T t -> exists t', value t' /\ t -→* t'.
destruct T. intros. now unfold R in H. intros. now unfold R in H. Qed.

Lemma lem12_1_4: forall T t t', nil |- t : T /\ t -→ t' -> (R T t <-> R T t').
Admitted.

Inductive multi_vR: (list type) -> (list term) -> Prop :=
  | vRNil: multi_vR nil nil
  | vRCons: forall T Γ v vlist, nil |- v : T -> value v -> R T v -> multi_vR Γ vlist ->
  multi_vR (T :: Γ) (v :: vlist).

Fixpoint multi_subst (j: nat) (vlist: list term) (t: term): term :=
  match vlist with
  | nil => t
  | v :: vlist' => subst j v (multi_subst (S j) vlist' t)
  end.

Lemma lem12_1_5: forall Γ t T vlist, Γ |- t : T -> multi_vR Γ vlist ->
R T (multi_subst 0 vlist t).
intros. generalize dependent vlist. induction H.
- intros. replace (multi_subst 0 vlist True) with True. simpl. exists True. split.
  constructor. constructor. admit.
- intros. replace (multi_subst 0 vlist False) with False. simpl. exists False. split.
  constructor. constructor. admit.
- intros. admit.
- intros. generalize dependent k. generalize dependent T. induction H0.
  + intros. simpl in H. inversion H.
  + intros. simpl. admit.
- intros.

Theorem lem12_1_6: forall t T, nil |- t : T -> exists t', value t' /\ t -→* t'.
intros. pose proof (lem12_1_5 nil nil t T H vRNil). simpl in H0. now apply lem12_1_3 in H0.
Qed.