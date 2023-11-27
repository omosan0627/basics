Inductive term : Type :=
  | True: term
  | False: term
  | IfThenElse: term -> term-> term-> term
  | O: term
  | Succ: term -> term
  | Pred: term -> term
  | IsZero: term -> term.

Notation "'If' A 'Then' B 'Else' C" := (IfThenElse A B C) (at level 60).

Inductive nvalue: term -> Prop :=
| nv_zero: nvalue O
| nv_succ: forall nv, nvalue nv -> nvalue (Succ nv).

Inductive value: term -> Prop :=
| v_true: value True
| v_false: value False
| v_nv: forall nv, nvalue nv -> value nv.

Inductive ttype: Type :=
  | Bool: ttype
  | Nat: ttype.


Inductive type_bind: term -> ttype -> Prop :=
  | TTrue: type_bind True Bool
  | TFalse: type_bind False Bool
  | TIf: forall t1 t2 t3 T, type_bind t1 Bool -> type_bind t2 T -> type_bind t3 T
  -> type_bind (If t1 Then t2 Else t3) T
  | TZero: type_bind O Nat
  | TSucc: forall t1, type_bind t1 Nat -> type_bind (Succ t1) Nat
  | TPred: forall t1, type_bind t1 Nat -> type_bind (Pred t1) Nat
  | TIsZero: forall t1, type_bind t1 Nat -> type_bind (IsZero t1) Bool.

Notation "A : B" := (type_bind A B) (at level 65). (* 低い方が先に適用される? *)

Lemma lem8_2_2_True: forall T, True : T -> T = Bool.
intros. inversion H. auto. Qed.
Lemma lem8_2_2_False: forall T, False : T -> T = Bool.
intros. inversion H. auto. Qed.
Lemma lem8_2_2_IfThenElse: forall t1 t2 t3 R, If t1 Then t2 Else t3 : R
-> t1 : Bool /\ t2 : R /\ t3 : R.
intros. inversion H. auto. Qed.
Lemma lem8_2_2_Zero: forall R, O : R -> R = Nat.
intros. inversion H. auto. Qed.
Lemma lem8_2_2_Succ: forall t1 R, Succ t1 : R -> R = Nat /\ t1 : Nat.
intros. inversion H. auto. Qed.
Lemma lem8_2_2_Pred: forall t1 R, Pred t1 : R -> R = Nat /\ t1 : Nat.
intros. inversion H. auto. Qed.
Lemma lem8_2_2_IsZero: forall t1 R, IsZero t1 : R -> R = Bool /\ t1 : Nat.
intros. inversion H. auto. Qed.

Theorem thm8_2_4: forall t R1 R2, t : R1 /\ t : R2 -> R1 = R2.
induction t.
- intros. destruct H. apply lem8_2_2_True in H, H0. now rewrite H, H0.
- intros. destruct H. apply lem8_2_2_False in H, H0. now rewrite H, H0.
- intros. destruct H. apply lem8_2_2_IfThenElse in H, H0.
destruct H. destruct H1. destruct H0. destruct H3.
pose proof (IHt2 R1 R2). auto.
- intros. destruct H. apply lem8_2_2_Zero in H, H0. now rewrite H, H0.
- intros. destruct H. apply lem8_2_2_Succ in H, H0.
destruct H. destruct H0. subst. auto.
- intros. destruct H. apply lem8_2_2_Pred in H, H0.
destruct H0. destruct H. subst. auto.
- intros. destruct H. apply lem8_2_2_IsZero in H, H0.
destruct H. destruct H0. subst. auto. Qed.

Lemma lem8_3_1_Bool: forall v, v : Bool -> value v -> v = True \/ v = False.
intros. inversion H0. auto. auto. subst. inversion H1. subst.
apply lem8_2_2_Zero in H. inversion H. subst. apply lem8_2_2_Succ in H.
destruct H. inversion H. Qed.
Lemma lem8_3_1_Nat: forall v, v : Nat -> value v -> nvalue v.
intros. inversion H0. subst. inversion H. subst. inversion H. apply H1. Qed.

Inductive step: term -> term-> Prop :=
  | EIfTrue: forall t2 t3, step (If True Then t2 Else t3) t2
  | EIfFalse: forall t2 t3, step (If False Then t2 Else t3) t3
  | EIf: forall t1 t1' t2 t3, (step t1 t1') 
  -> (step (If t1 Then t2 Else t3) (If t1' Then t2 Else t3))
  | ESucc: forall t1 t1', step t1 t1' -> step (Succ t1) (Succ t1')
  | EPredZero: step (Pred O) O
  | EPredSucc: forall nv, nvalue nv -> step (Pred (Succ nv)) nv
  | EPred: forall t1 t1', step t1 t1' -> step (Pred t1) (Pred t1')
  | EIsZeroZero: step (IsZero O) True
  | EIsZeroSucc: forall nv, nvalue nv -> step (IsZero (Succ nv)) False
  | EIsZero: forall t1 t1', step t1 t1' -> step (IsZero t1) (IsZero t1').

Notation "A --> B" := (step A B) (at level 65).

Theorem thm8_3_2: forall t T, t : T -> value t \/ (exists t', t --> t').
intros. induction H.
- left. constructor.
- left. constructor. 
- right. destruct IHtype_bind1. pose proof (lem8_3_1_Bool _  H H2).
destruct H3. subst. exists t2. constructor. subst. exists t3. constructor.
destruct H2. exists (If x Then t2 Else t3). constructor. apply H2.
- left. constructor. constructor.
- destruct IHtype_bind.
  + left. constructor. pose proof (lem8_3_1_Nat _ H H0). now constructor.
  + right. destruct H0. exists (Succ x). constructor. apply H0.
- right. destruct IHtype_bind.
  + pose proof (lem8_3_1_Nat _ H H0). inversion H1.
  exists O. constructor. exists nv. now constructor.
  + destruct H0. exists (Pred x). now constructor.
- right. destruct IHtype_bind.
  + pose proof (lem8_3_1_Nat _ H H0). inversion H1. exists True. now constructor.
  exists False. now constructor.
  + destruct H0. exists (IsZero x). now constructor. Qed.

Theorem thm8_3_3: forall t T, t : T -> forall t', t --> t' -> t' : T.
intros ? ? ?. induction H.
- intros. inversion H.
- intros. inversion H.
- intros. inversion H2.
  + now subst.
  + now subst.
  + pose proof (IHtype_bind1 _ H7). now constructor.
- intros. inversion H.
- intros. inversion H0. pose proof (IHtype_bind _ H2). now constructor.
- intros. inversion H0.
  + constructor.
  + subst. inversion H. apply H3.
  + apply IHtype_bind in H2. now constructor.
- intros. inversion H0.
  + constructor.
  + constructor.
  + apply IHtype_bind in H2. now constructor. Qed.
  