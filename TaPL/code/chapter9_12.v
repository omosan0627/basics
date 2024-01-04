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

Lemma value_stop: forall t t', value t -> t -→ t' -> Logic.False.
intros. destruct H. inversion H0. inversion H0. inversion H0. Qed.

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

Theorem thm3_5_4: forall t t' t'', t -→ t' -> t -→ t'' -> t' = t''.
intros. generalize dependent t''. induction H.
- intros. inversion H0. reflexivity. inversion H4.
- intros. inversion H0. reflexivity. inversion H4.
- intros. inversion H0. subst. inversion H. subst. inversion H. subst.
  pose proof (IHterm_step _ H5). subst. reflexivity.
- intros. inversion H0. subst. pose proof (IHterm_step _ H4). now subst.
  subst. now pose proof (value_stop _ _ H3 H). subst. inversion H.
- intros. inversion H1. subst. now pose proof (value_stop _ _ H H5).
  subst. pose proof (IHterm_step _ H6). now subst. subst.
  now pose proof (value_stop _ _ H5 H0).
- intros. inversion H0. inversion H4. subst. now pose proof (value_stop _ _ H H5).
  reflexivity. Qed.


Inductive multi_term_step: term -> term -> Prop:=
  | Refl: forall t, multi_term_step t t
  | Trans: forall t1 t2 t3, term_step t1 t2 -> multi_term_step t2 t3 -> multi_term_step t1 t3.
 
Notation "t1 -→* t2" := (multi_term_step t1 t2) (at level 62).

Definition halts (t:term): Prop := exists t', value t' /\ t -→* t'.

(* Propを値として見るの確かにな～ *)

Fixpoint R (T: type) (t:term): Prop :=
  match T with
  | Bool => nil |- t : T /\ halts t
  | T1 → T2 => nil |- t : T /\ halts t /\ (forall s, R T1 s -> R T2 (t ◦ s))
  end.

Lemma lem12_1_3: forall t T, R T t -> halts t.
destruct T. intros. now unfold R in H. intros. now unfold R in H. Qed.

Lemma Rtype: forall T t, R T t -> nil |- t : T.
induction T. intros. now unfold R in H. intros. now unfold R in H. Qed.

Lemma halts_before: forall t t', halts t -> t -→ t' -> halts t'.
intros. unfold halts in H. destruct H. destruct H. generalize dependent t'.
induction H1. 
  - intros. destruct H. inversion H0. inversion H0. inversion H0.
  - intros. pose proof (thm3_5_4 _ _ _ H0 H2). subst. unfold halts. exists t3.
    split. apply H. apply H1. Qed.

Lemma halts_after: forall t t', halts t' -> t -→ t' -> halts t.
intros. unfold halts in H. destruct H. destruct H. unfold halts. exists x.
split. apply H. refine (Trans _ _ _ H0 H1). Qed.

Lemma lem12_1_4_left: forall T t t', nil |- t : T -> t -→ t' -> R T t -> R T t'.
induction T.
- intros. split. refine (thm9_3_9 _ _ _ _ H H0). apply lem12_1_3 in H1.
  refine (halts_before _ _ H1 H0).
- intros. split. refine (thm9_3_9 _ _ _ _ H H0). unfold R in H1. fold R in H1.
  destruct H1. destruct H2. split. refine (halts_before _ _ H2 H0). intros. 
  refine (IHT2 (t ◦ s) (t' ◦ s) _ _ _). pose proof (H3 _ H4).
  refine (Rtype _ _ H5). now constructor. apply H3. apply H4. Qed.

Lemma lem12_1_4_left_multi: forall T t t', nil |- t : T -> t -→* t' -> R T t -> R T t'.
intros. generalize dependent T. induction H0. intros. auto.
intros. pose proof (lem12_1_4_left _ _ _ H1 H H2). pose proof (Rtype _ _ H3).
refine (IHmulti_term_step _ H4 H3). Qed.

Lemma lem12_1_4_right: forall T t t', nil |- t : T -> t -→ t' -> R T t' -> R T t.
induction T.
- intros. split. apply H. unfold R in H1. destruct H1. 
  refine (halts_after _ _ H2 H0).
- intros. split. apply H. unfold R in H1. fold R in H1. destruct H1.
  destruct H2. split. refine (halts_after _ _ H2 H0). intros. 
  pose proof (Rtype _ _ H4). apply H3 in H4. 
  refine (IHT2 (t ◦ s) (t' ◦ s) _ _ H4). refine (TApp _ _ T1 _ _ _ _). auto.
  auto. constructor. apply H0. Qed.

Lemma lem12_1_4_right_multi: forall T t t', nil |- t : T -> t -→* t' -> R T t' -> R T t.
intros. generalize dependent T. induction H0. intros. auto.
intros. pose proof (thm9_3_9 _ _ _ _ H1 H). pose proof (IHmulti_term_step _ H3 H2).
refine (lem12_1_4_right _ _ _ H1 H H4). Qed.

Inductive multi_vR: (list type) -> (list term) -> Prop :=
  | vRNil: multi_vR nil nil
  | vRCons: forall T Γ v vlist, value v -> R T v -> multi_vR Γ vlist ->
  multi_vR (T :: Γ) (v :: vlist).

Fixpoint multi_subst (vlist: list term) (t: term): term :=
  match vlist with
  | nil => t
  | v :: vlist' => multi_subst vlist' (reverse_shift 0 ([0 |→ shift 0 1 v] t))
  end.


Lemma multi_right: forall t1 t2 t3, t1 -→* t2 -> t2 -→ t3 -> t1 -→* t3.
intros. generalize dependent t3. induction H. intros. refine (Trans _ _ t3 H0 _). constructor.
intros. apply IHmulti_term_step in H1. refine (Trans _ _ _ H H1). Qed.

Lemma multi_if: forall t1 t2 t3 t1', t1 -→* t1' -> 
If t1 Then t2 Else t3 -→* If t1' Then t2 Else t3. intros. generalize dependent t2.
generalize dependent t3. induction H. intros. constructor.
intros. pose proof (EIf _ _ t4 t0 H). pose proof (IHmulti_term_step t0 t4).
refine (Trans _ _ _ H1 H2). Qed.

Lemma multi_app2: forall v t1 t1', t1 -→* t1' -> value v -> v ◦ t1 -→* v ◦ t1'.
intros. generalize dependent v. induction H. intros. constructor.
intros. pose proof (EApp2 v _ _ H1 H). pose proof (IHmulti_term_step _ H1).
refine (Trans _ _ _ H2 H3). Qed.

Lemma multi_subst_app: forall vlist t1 t2, multi_subst vlist t1 ◦ multi_subst vlist t2
= multi_subst vlist (t1 ◦ t2).
induction vlist.
- intros. simpl. reflexivity.
- intros. simpl. apply IHvlist. Qed.

Lemma multi_subst_if: forall vlist t1 t2 t3,
If (multi_subst vlist t1) Then (multi_subst vlist t2) Else (multi_subst vlist t3)
= multi_subst vlist (If t1 Then t2 Else t3).
induction vlist.
- intros. simpl. reflexivity.
- intros. simpl. apply IHvlist. Qed.

Lemma multi_subst_abst_value: forall vlist T t, value (multi_subst vlist (λ T, t)).
induction vlist. intros. simpl. constructor. intros. simpl. apply IHvlist. Qed.

Lemma get_var_type_less_k: forall Γ k T, get_var_type k Γ = Some T -> k < length Γ.
induction Γ. intros. simpl in H. inversion H. intros. simpl in H.
remember (k =? 0) as b. symmetry in Heqb. destruct b. 
- apply Nat.eqb_eq in Heqb. subst. simpl. lia.
- apply IHΓ in H. simpl. lia. Qed.

Lemma Γ_nil: forall t Γ T Γ', Γ |- t : T -> Γ ++ Γ' |- t : T. 
intros. generalize dependent Γ'. induction H.
- intros. constructor.
- intros. constructor.
- intros. constructor. apply IHtype_step1. apply IHtype_step2. apply IHtype_step3.
- intros. constructor. pose proof (get_var_type_lt Γ Γ' k). rewrite H in H0.
  apply H0. now pose proof (get_var_type_less_k _ _ _ H).
- intros. constructor. replace (T1 :: Γ ++ Γ') with ((T1 :: Γ) ++ Γ').
  apply IHtype_step. simpl. reflexivity.
- intros. refine (TApp _ _ T11 _ _ _ _). apply IHtype_step1. apply IHtype_step2. Qed.

Lemma multi_vR_nil: forall Γ vlist t T, multi_vR Γ vlist -> Γ |- t : T ->
nil |- multi_subst vlist t : T.
intros. generalize dependent T. generalize dependent t. induction H.
- intros. now simpl.
- intros. simpl.
  remember (reverse_shift 0 ([0 |→ shift 0 1 v] t)) as t'. symmetry in Heqt'.
  assert (Γ |- (λ T, t) ◦ v : T0). refine (TApp _ _ T _ _ _ _).
  constructor. auto. pose proof (Rtype _ _ H0). pose proof (Γ_nil v nil T Γ H3). 
  now simpl in H4. assert (Γ |- t' : T0).
  refine (thm9_3_9 _ _ _ _ H3 _). subst. now constructor. refine (IHmulti_vR _ _ H4). Qed.


Lemma subst_equal: forall t Γ T v, Γ |- t : T -> t = [length Γ |→ v] t.
induction t.
- intros. simpl. reflexivity.
- intros. simpl. reflexivity.
- intros. simpl. inversion H. subst. pose proof (IHt1 _ _ v H4).
  pose proof (IHt2 _ _ v H6). pose proof (IHt3 _ _ v H7).
  symmetry in H0, H1, H2. now rewrite H0, H1, H2.
- intros. inversion H. subst. simpl. remember (n =? length Γ) as b. symmetry in Heqb.
  destruct b. apply Nat.eqb_eq in Heqb. pose proof (get_var_type_less_k _ _ _ H2). lia.
  reflexivity.
- intros. simpl. destruct T. 
  + inversion H.
  + inversion H. subst. pose proof (IHt _ _ (shift 0 1 v) H2). simpl in H0. symmetry in H0.
    now rewrite H0.
- intros. simpl. inversion H. subst. pose proof (IHt1 _ _ v H3). pose proof (IHt2 _ _ v H5).
  symmetry in H0. symmetry in H1. rewrite H0. rewrite H1. reflexivity. Qed.

Lemma reverse_shift_equal: forall t Γ T, Γ |- t : T -> t = reverse_shift (length Γ) t.
induction t.
- intros. now simpl.
- intros. now simpl.
- intros. simpl. inversion H. subst. pose proof (IHt1 _ _ H4). pose proof (IHt2 _ _ H6).
  pose proof (IHt3 _ _ H7). symmetry in H0, H1, H2. now rewrite H0, H1, H2.
- intros. simpl. inversion H. subst. remember (length Γ <=? n) as b. symmetry in Heqb.
  destruct b. apply Nat.leb_le in Heqb. pose proof (get_var_type_less_k _ _ _ H2). lia.
  reflexivity.
- intros. simpl. inversion H. subst. pose proof (IHt _ _ H4). simpl in H0. symmetry in H0.
  now rewrite H0.
- intros. simpl. inversion H. subst. pose proof (IHt1 _ _ H3). pose proof (IHt2 _ _ H5).
  symmetry in H0, H1. now rewrite H0, H1. Qed.

Corollary multi_subst_equal: forall vlist t T, nil |- t : T -> t = multi_subst vlist t.
induction vlist. intros. simpl. reflexivity.
intros. simpl. pose proof (subst_equal _ _ _ (shift 0 1 a) H). simpl in H0. symmetry in H0. 
rewrite H0. pose proof (reverse_shift_equal _ _ _ H). simpl in H1. symmetry in H1. 
rewrite H1. apply (IHvlist _ T). apply H. Qed.

Fixpoint free_var (n: nat) (t: term): nat :=
match t with
  | True => 0
  | False => 0
  | Var k => k + 1 - n
  | If t1 Then t2 Else t3 => max (max (free_var n t1) (free_var n t2)) (free_var n t3)
  | λ _, t' => free_var (S n) t'
  | t1 ◦ t2 => max (free_var n t1) (free_var n t2)
  end.

Lemma free_var_zero: forall Γ t T, Γ |- t : T -> free_var (length Γ) t = 0.
intros. induction H.
- now simpl.
- now simpl.
- simpl. rewrite IHtype_step1, IHtype_step2, IHtype_step3. now simpl.
- simpl. pose proof (get_var_type_less_k Γ k T). pose proof (H0 H). lia.
- simpl. now simpl in IHtype_step.
- simpl. rewrite IHtype_step1, IHtype_step2. now simpl. Qed.

Lemma subst_nochange: forall Γ t x T c, Γ |- t : T -> length Γ <= c -> [c |→ x] t = t.
intros. generalize dependent x. generalize dependent c. induction H.
- intros. now simpl.
- intros. now simpl.
- intros. pose proof (IHtype_step1 _ H2 x). pose proof (IHtype_step2 _ H2 x).
  pose proof (IHtype_step3 _ H2 x). simpl. now rewrite H5, H3, H4.
- intros. apply get_var_type_less_k in H. simpl. 
  replace (k =? c) with false. reflexivity. symmetry. apply Nat.eqb_neq. lia.
- intros. simpl. assert (length (T1 :: Γ) <= S c). simpl. lia.
  pose proof (IHtype_step (S c) H1 (shift 0 1 x)). now rewrite H2.
- intros. pose proof (IHtype_step1 _ H1 x). pose proof (IHtype_step2 _ H1 x).
  simpl. now rewrite H3, H2. Qed.

Lemma shift_nochange: forall Γ t T c d, Γ |- t : T -> length Γ <= c -> shift c d t = t.
intros. generalize dependent c. generalize dependent d. induction H.
- intros. now simpl.
- intros. now simpl.
- intros. simpl. pose proof (IHtype_step1 d c H2). pose proof (IHtype_step2 d c H2).
  pose proof (IHtype_step3 d c H2). now rewrite H3, H4, H5.
- intros. simpl. replace (c <=? k) with false. reflexivity. symmetry.
  apply Nat.leb_nle. apply get_var_type_less_k in H. lia.
- intros. simpl. assert (shift (S c) d t2 = t2). refine (IHtype_step d (S c) _).
  simpl. lia. now rewrite H1.
- intros. simpl. pose proof (IHtype_step1 d c H1). pose proof (IHtype_step2 d c H1).
  now rewrite H2, H3. Qed.

Lemma reverse_shift_nochange: forall Γ t T c, Γ |- t : T -> length Γ <= c -> 
reverse_shift c t = t.
intros. generalize dependent c. induction H.
- intros. now simpl.
- intros. now simpl.
- intros. simpl. pose proof (IHtype_step1 _ H2). pose proof (IHtype_step2 _ H2).
  pose proof (IHtype_step3 _ H2). now rewrite H3, H4, H5.
- intros. simpl. replace (c <=? k) with false. reflexivity. symmetry.
  apply Nat.leb_nle. apply get_var_type_less_k in H. lia.
- intros. simpl. assert (reverse_shift (S c) t2 = t2). refine (IHtype_step _ _).
  simpl. lia. now rewrite H1.
- intros. simpl. pose proof (IHtype_step1 c H1). pose proof (IHtype_step2 c H1).
  now rewrite H2, H3. Qed.

Lemma subst_swap: forall t x x' T T' n, nil |- x : T -> nil |- x' : T' ->
[n |→ x'] reverse_shift n ([n |→ x] t) = [n |→ x] reverse_shift (S n) ([(S n) |→ x'] t).
induction t.
- intros. now simpl.
- intros. now simpl.
- intros. simpl. pose proof (IHt1 _ _ _ _ n H H0). pose proof (IHt2 _ _ _ _ n H H0).
  pose proof (IHt3 _ _ _ _ n H H0). now rewrite H1, H2, H3.
- intros. simpl. remember (n =? n0) as b1. remember (n =? S n0) as b2.
  symmetry in Heqb1. symmetry in Heqb2. destruct b1, b2. 
  + pose proof (EqNat.beq_nat_true _ _ Heqb1). pose proof (EqNat.beq_nat_true _ _ Heqb2). lia.
  + pose proof (EqNat.beq_nat_true _ _ Heqb1). subst. 
    replace (reverse_shift n0 x) with x. replace ([n0 |→ x'] x) with x.
    unfold reverse_shift. replace (S n0 <=? n0) with false. simpl. replace (n0 =? n0) with true.
    reflexivity. symmetry. apply Nat.leb_nle. lia. symmetry.
    refine (subst_nochange _ _ _ _ _ H _). simpl. lia. symmetry. 
    refine (reverse_shift_nochange _ _ _ n0 H _). simpl. lia.
  + pose proof (EqNat.beq_nat_true _ _ Heqb2). subst.
    replace (reverse_shift (S n0) x') with x'. replace ([n0 |→ x] x') with x'.
    unfold reverse_shift. replace (n0 <=? S n0) with true. simpl. 
    replace (n0 =? n0) with true. reflexivity. symmetry. apply Nat.leb_le. lia. symmetry.
    refine (subst_nochange _ _ _ _ _ H0 _). simpl. lia. symmetry.
    refine (reverse_shift_nochange _ _ _ (S n0) H0 _). simpl. lia.
  + remember (n <? n0) as b. symmetry in Heqb. destruct b. 
    * apply Nat.ltb_lt in Heqb. unfold reverse_shift.
      replace (n0 <=? n) with false. replace (S n0 <=? n) with false. simpl.
      replace (n =? n0) with false. reflexivity. symmetry. 
      apply Nat.leb_nle. lia. symmetry. apply Nat.leb_nle. lia.
    * apply Nat.ltb_ge in Heqb. apply EqNat.beq_nat_false in Heqb1.
      apply EqNat.beq_nat_false in Heqb2. unfold reverse_shift.
      replace (n0 <=? n) with true. replace (S n0 <=? n) with true. simpl.
      replace (pred n =? n0) with false. reflexivity. symmetry.
      apply Nat.eqb_neq. lia. symmetry. apply Nat.leb_le. lia. symmetry. apply Nat.leb_le. lia.
- intros. simpl. replace (shift 0 1 x) with x. replace (shift 0 1 x') with x'.
  pose proof (IHt _ _ _ _ (S n) H H0). now rewrite H1. symmetry.
  refine (shift_nochange _ _ _ _ _ H0 _). simpl. lia. symmetry.
  refine (shift_nochange _ _ _ _ _ H _). simpl. lia.
- intros. simpl. pose proof (IHt1 _ _ _ _ n H H0). pose proof (IHt2 _ _ _ _ n H H0).
  now rewrite H1, H2. Qed.

Lemma multi_subst_step: forall vlist Γ T T' t x, value x -> R T' x -> multi_vR Γ vlist ->
multi_subst vlist ((λ T, t) ◦ x) -→ multi_subst vlist (reverse_shift 0 ([0 |→ shift 0 1 x] t)).
induction vlist.
- intros. simpl. now constructor.
- intros. inversion H1. subst.
  simpl. remember (reverse_shift 1 ([1 |→ (shift 0 1 (shift 0 1 a))] t)) as t'.
  remember (reverse_shift 0 ([0 |→ shift 0 1 a] x)) as x'.
  pose proof (Rtype _ _ H0). assert ([0 |→ shift 0 1 a] x = x). 
  refine (subst_nochange _ _ _ _ _ H2 _). simpl. lia. rewrite H3 in Heqx'.
  symmetry in Heqx'. assert (reverse_shift 0 x = x).
  refine (reverse_shift_nochange _ _ _ 0 H2 _). simpl. lia. rewrite H5 in Heqx'.
  assert ([0 |→ shift 0 1 a] reverse_shift 0 ([0 |→ shift 0 1 x] t) = [0 |→ shift 0 1 x] t').
  subst. apply Rtype in H6.
  assert (shift 0 1 a = a). refine (shift_nochange _ _ _ 0 _ H6 _). simpl. lia.
  rewrite H8. rewrite H8.
  refine (subst_swap _ _ _ T' T0 0 _ _). replace (shift 0 1 x') with x'. apply H2.
  symmetry. apply (shift_nochange _ _ _ 0 _ H2). simpl. lia. apply H6.
  rewrite H8. subst. refine (IHvlist Γ0 _ T' _ _ _ _ _). apply H. apply H0. 
  apply H7. Qed.

Lemma lem12_1_5: forall Γ t T vlist, Γ |- t : T -> multi_vR Γ vlist ->
R T (multi_subst vlist t).
intros. generalize dependent vlist. induction H.
- intros. replace (multi_subst vlist True) with True. simpl. split.
  constructor. unfold halts. exists True. split. constructor. constructor. 
  apply (multi_subst_equal _ _ Bool). constructor.
- intros. replace (multi_subst vlist False) with False. simpl. split.
  constructor. unfold halts. exists False. split. constructor. constructor.
  apply (multi_subst_equal _ _ Bool). constructor.
- intros. 
  remember (multi_subst vlist t1) as t1'. symmetry in Heqt1'. 
  remember (multi_subst vlist t2) as t2'. symmetry in Heqt2'. 
  remember (multi_subst vlist t3) as t3'. symmetry in Heqt3'. 
  pose proof (IHtype_step1 _ H2). rewrite Heqt1' in H3. 
  pose proof (IHtype_step2 _ H2). rewrite Heqt2' in H4. 
  pose proof (IHtype_step3 _ H2). rewrite Heqt3' in H5. 
  replace (multi_subst vlist (If t1 Then t2 Else t3)) with
  (If t1' Then t2' Else t3'). assert (R Bool t1'). auto. unfold R in H3. destruct H3. 
  unfold halts in H7. destruct H7. destruct H7.
  refine (lem12_1_4_right_multi _ _ (If x Then t2' Else t3') _ _ _).
  pose proof (Rtype  _ _ H4). pose proof (Rtype _ _ H5). constructor.
  auto. auto. auto.
  + refine (multi_if _ _ _ _ H8).
  + pose proof (lem12_1_4_left_multi _ _ _ H3 H8 H6). pose proof (Rtype _ _ H9).
    pose proof (Rtype _ _ H4). pose proof (Rtype _ _ H5).
    destruct H7. 
    * refine (lem12_1_4_right _ _ t2' _ _ _). constructor. constructor. auto. auto.
      constructor. auto.
    * refine (lem12_1_4_right _ _ t3' _ _ _). constructor. constructor. auto. auto.
      constructor. auto.
    * inversion H10.
  + subst. apply multi_subst_if.
- intros. generalize dependent k. generalize dependent T. induction H0.
  + intros. simpl in H. inversion H.
  + intros. simpl. simpl in H2. remember (k =? 0). symmetry in Heqb. destruct b.
    replace (reverse_shift 0 (shift 0 1 v)) with v.
    replace (multi_subst vlist v) with v. inversion H2. subst. apply H0.
    refine (multi_subst_equal _ _ T _). refine (Rtype _ _ H0). 
    pose proof (shift_inversion v 0 0). simpl in H3.
    pose proof (shift_id v 0). rewrite H3. now rewrite H4. 
    replace (reverse_shift 0 (Var k)) with (Var (Init.Nat.pred k)).
    refine (IHmulti_vR _ _ H2). simpl. reflexivity.
- intros. split. assert (Γ |- λ T1, t2: T1 → T2). now constructor. 
  refine (multi_vR_nil _ _ _ _ H0 H1). split. 
  pose proof (multi_subst_abst_value vlist T1 t2). unfold halts. 
  exists (multi_subst vlist (λ T1, t2)). split. auto. constructor.
  intros. pose proof (lem12_1_3 _ _ H1). unfold halts in H2.
  destruct H2. destruct H2. pose proof (Rtype _ _  H1).
  pose proof (lem12_1_4_left_multi _ _ _ H4 H3 H1).
  assert (multi_vR (T1 :: Γ) (x :: vlist)). constructor. auto. auto. auto.
  pose proof (IHtype_step _ H6). simpl in H7.
  remember (reverse_shift 0 ([0 |→ shift 0 1 x] t2)) as t'.
  assert (multi_subst vlist (λ T1, t2) ◦ s -→* multi_subst vlist t').
  + assert (multi_subst vlist (λ T1, t2) ◦ s -→* multi_subst vlist (λ T1, t2) ◦ x). 
    refine (multi_app2 _ _ _ H3 _). apply multi_subst_abst_value.
    pose proof (multi_subst_app vlist (λ T1, t2) x). 
    replace (multi_subst vlist x) with x in H9.
    assert (multi_subst vlist ((λ T1, t2) ◦ x) -→ multi_subst vlist t').
    rewrite Heqt'. refine (multi_subst_step _ _ _ _ _ _ H2 H5 H0).
    rewrite H9 in H8. refine (multi_right _ _ _ H8 H10).
    refine (multi_subst_equal _ _ T1 _). refine (Rtype _ _ H5).
  + refine (lem12_1_4_right_multi _ _ _ _ H8 H7).
    refine (TApp _ _ T1 _ _ _ _). refine (multi_vR_nil _ _ _ _ H0 _).
    constructor. apply H. apply H4.
- intros. pose proof (IHtype_step1 _ H1). pose proof (IHtype_step2 _ H1).
  unfold R in H2. fold R in H2. destruct H2. destruct H4.
  replace (multi_subst vlist (t1 ◦ t2)) with 
  ((multi_subst vlist t1) ◦ (multi_subst vlist t2)). apply H5. apply H3.
  apply multi_subst_app.
Qed.

Theorem lem12_1_6: forall t T, nil |- t : T -> halts t.
intros. pose proof (lem12_1_5 nil t T nil H vRNil). simpl in H0. now apply lem12_1_3 in H0.
Qed.