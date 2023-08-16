Require Import Psatz.


Inductive term : Type :=
  | True: term
  | False: term
  | If: term -> term-> term-> term
  | O: term
  | Succ: term -> term
  | Pred: term -> term
  | Iszero: term -> term
  | Wrong: term.

Inductive nvalue: term -> Prop :=
| nv_zero: nvalue O
| nv_succ: forall nv, nvalue nv -> nvalue (Succ nv).

Inductive value: term -> Prop :=
| v_true: value True
| v_false: value False
| v_nv: forall nv, nvalue nv -> value nv
| v_wrong: value Wrong.

Inductive badnat: term -> Prop :=
| bn_wrong: badnat Wrong
| bn_true: badnat True
| bn_false: badnat False.

Inductive badbool: term -> Prop :=
| bb_wrong: badbool Wrong
| bb_nv: forall nv, nvalue nv -> badbool nv.

Inductive NoWrong: term -> Prop :=
| nw_true: NoWrong True
| nw_false: NoWrong False
| nw_O: NoWrong O
| nw_succ: forall t, NoWrong t -> NoWrong (Succ t)
| nw_pred: forall t, NoWrong t -> NoWrong (Pred t)
| nw_iszero: forall t, NoWrong t -> NoWrong (Iszero t) 
| nw_if: forall t1 t2 t3, NoWrong t1 -> NoWrong t2 -> NoWrong t3 -> NoWrong (If t1 t2 t3).

Inductive step: term -> term-> Prop :=
  | EIfTrue: forall t2 t3, step (If True t2 t3) t2
  | EIfFalse: forall t2 t3, step (If False t2 t3) t3
  | EIf: forall t1 t1' t2 t3, (step t1 t1') -> (step (If t1 t2 t3) (If t1' t2 t3))
  | ESucc: forall t1 t1', step t1 t1' -> step (Succ t1) (Succ t1')
  | EPredZero: step (Pred O) O
  | EPredSucc: forall nv, nvalue nv -> step (Pred (Succ nv)) nv
  | EPred: forall t1 t1', step t1 t1' -> step (Pred t1) (Pred t1')
  | EIsZeroZero: step (Iszero O) True
  | EIsZeroSucc: forall nv, nvalue nv -> step (Iszero (Succ nv)) False
  | EIsZero: forall t1 t1', step t1 t1' -> step (Iszero t1) (Iszero t1')

  | EIfWrong: forall t1 t2 t3, badbool t1 -> step (If t1 t2 t3) Wrong
  | ESuccWrong: forall t, badnat t -> step (Succ t) Wrong
  | EPredWrong: forall t, badnat t -> step (Pred t) Wrong
  | EIsZeroWrong: forall t, badnat t -> step (Iszero t) Wrong.

Inductive goodstep: term -> term -> Prop :=
  | EGood: forall t1 t2, NoWrong t1 -> NoWrong t2 -> step t1 t2 -> goodstep t1 t2.

Lemma wrongnogood:  not (NoWrong Wrong). unfold not. intros. inversion H. Qed.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multistep: term -> term -> Prop :=
| Refl: forall t, multistep t t
| Trans: forall t1 t2 t3, step t1 t2 -> multistep t2 t3 -> multistep t1 t3.

Inductive multigoodstep: term -> term -> Prop :=
| EMultiGood: forall t, NoWrong t -> multigoodstep t t
| ETransGood: forall t1 t2 t3, goodstep t1 t2 -> multigoodstep t2 t3 -> multigoodstep t1 t3.

Inductive normalstop: term -> Prop :=
| nexist: forall t, NoWrong t -> (forall t1, not (goodstep t t1)) -> not (value t) -> normalstop t.

Lemma multitrans: forall t1 t2 t3, multistep t1 t2 -> multistep t2 t3 -> multistep t1 t3.
intros. generalize dependent t3. induction H. intros. apply H0. intros. apply IHmultistep in H1.
apply Trans with t2. apply H. apply H1. Qed.

Lemma nowrongnv: forall nv, nvalue nv -> NoWrong nv.
intros. induction H. apply nw_O. apply nw_succ. apply IHnvalue. Qed.

Lemma nvstep: forall nv t, nvalue nv -> not (step nv t). unfold not.
intros. generalize dependent t. induction H. intros. inversion H0. intros.
inversion H0. subst. apply IHnvalue in H2.  auto. subst. inversion H2. subst.
inversion H. subst. inversion H. subst. inversion H. Qed.

Lemma thm3_5_4: forall t t1 t2, step t t1 -> step t t2 -> t1 = t2.
intros. generalize dependent t2. induction H.
intros. inversion H0. subst. reflexivity. subst. inversion H4. inversion H4. inversion H5.
intros. inversion H0. subst. reflexivity. subst. inversion H4. inversion H4. inversion H5.
intros. inversion H0. subst. inversion H. subst. inversion H. subst. apply IHstep in H5. subst.
reflexivity. subst. inversion H5. subst. destruct H5. inversion H. 
apply nvstep with (nv:=nv) (t:=t1') in H1. contradiction. subst. 
apply nvstep with (t:=t1') (nv:=t1) in H. contradiction. apply H1.

intros. inversion H0. subst. apply IHstep in H2. subst. reflexivity. subst.
inversion H2. subst. inversion H. subst. inversion H. subst. inversion H.

intros. inversion H0. reflexivity. subst. inversion H1. subst. inversion H1.
intros. inversion H0. reflexivity. subst. apply nvstep with (nv:=Succ nv) (t:=t1') in H2.
contradiction. apply nv_succ. apply H. subst. inversion H2.

intros. inversion H0. subst. inversion H. subst. apply nvstep with (nv:=Succ t2) (t:=t1') in H.
contradiction. apply nv_succ. apply H2. subst. apply IHstep in H2. subst. reflexivity.
subst. inversion H2. subst. inversion H. subst. inversion H. subst. inversion H.
Admitted.


(* Lemma multistepexistsvalue: forall t, exists v, multistep t v /\ value v. Admitted. *)

Lemma nowrongorwrong: forall t, NoWrong t \/ not (NoWrong t).
induction t. left. apply nw_true. left. apply nw_false. destruct IHt1. destruct IHt2. destruct IHt3.
left. apply nw_if. apply H. apply H0. apply H1. right. unfold not. intros. inversion H2. contradiction.
right. unfold not; intros. inversion H1. contradiction. right; unfold not; intros. inversion H0. contradiction.
left. apply nw_O. destruct IHt. left. apply nw_succ. apply H. right. unfold not; intros. inversion H0. contradiction.
destruct IHt. left. apply nw_pred. apply H. right. unfold not. intros. inversion H0. contradiction.
destruct IHt. left. apply nw_iszero. apply H. right. unfold not; intros. inversion H0; contradiction.
right; unfold not. intros. inversion H. Qed.

Lemma nonvalueornvalue: forall nv, nvalue nv \/ not (nvalue nv).
induction nv.
right; unfold not; intros. inversion H.
right; unfold not; intros. inversion H.
right; unfold not; intros. inversion H.
left. apply nv_zero.
destruct IHnv.
left. apply nv_succ. apply H. right; unfold not; intros. inversion H0. contradiction.
right; unfold not; intros. inversion H.
right; unfold not; intros. inversion H.
right; unfold not; intros. inversion H. Qed.

Lemma novalueorvalue: forall t, value t \/ not (value t).
induction t. left; apply v_true. left; apply v_false. right.
unfold not; intros. inversion H. inversion H0. left. apply v_nv. apply nv_zero. destruct IHt. destruct H. right. unfold not; intros.
inversion H. inversion H0. inversion H3. right.
unfold not. intros. inversion H. inversion H0. inversion H3. left. apply v_nv. apply nv_succ. apply H.
right; unfold not; intros.
inversion H. inversion H0. inversion H3. right. unfold not; intros. assert (value t). inversion H0. inversion H1. apply v_nv.
apply H4. contradiction.
destruct IHt. destruct H.
right; unfold not; intros. inversion H. inversion H0.
right; unfold not; intros. inversion H. inversion H0.
right; unfold not; intros. inversion H0. inversion H1.
right; unfold not; intros. inversion H. inversion H0.

right; unfold not; intros. inversion H0. inversion H1.

destruct IHt. destruct H.
right; unfold not; intros. inversion H. inversion H0.
right; unfold not; intros. inversion H. inversion H0.
right; unfold not; intros. inversion H0. inversion H1.
right; unfold not; intros. inversion H. inversion H0.

right; unfold not; intros. inversion H0. inversion H1.
left. apply v_wrong. Qed.

Lemma multiif: forall t t' t2 t3, multistep t t' -> multistep (If t t2 t3) (If t' t2 t3).
intros. induction H. apply Refl. apply Trans with (If t0 t2 t3). apply EIf. apply H.
apply IHmultistep. Qed.

Lemma multisucc: forall t t', multistep t t' -> multistep (Succ t) (Succ t').
intros. induction H. apply Refl. apply Trans with (Succ t2). apply ESucc. apply H.
apply IHmultistep. Qed.

Lemma multipred: forall t t', multistep t t' -> multistep (Pred t) (Pred t').
intros. induction H. apply Refl. apply Trans with (Pred t2). apply EPred. apply H.
apply IHmultistep. Qed.

Lemma multiiszero: forall t t', multistep t t' -> multistep (Iszero t) (Iszero t').
intros. induction H. apply Refl. apply Trans with (Iszero t2). apply EIsZero. apply H.
apply IHmultistep. Qed.

Lemma A4: forall t, normalstop t -> multistep t Wrong.
intros. destruct H. unfold not in H1. induction t. assert (value True). apply v_true. contradiction.
assert (value False). apply v_false. contradiction. assert (forall t2, ~ goodstep t1 t2).
intros. unfold not; intros. assert (goodstep (If t1 t2 t3) (If t0 t2 t3)). apply EGood.
apply H. apply nw_if. inversion H2. inversion H. auto. inversion H. auto. inversion H; auto. apply EIf.
inversion H2; auto. apply H0 in H3. apply H3. destruct t1. 
assert (goodstep (If True t2 t3) t2). apply EGood. apply H. inversion H; auto. apply EIfTrue. 
apply H0 in H3; contradiction.
assert (goodstep (If False t2 t3) t3). apply EGood. apply H. inversion H; auto. apply EIfFalse. 
apply H0 in H3; contradiction.

inversion H. apply IHt1 in H6. apply multitrans with (If Wrong t2 t3). apply multiif. apply H6.
apply Trans with Wrong. apply EIfWrong. apply bb_wrong. apply Refl.
apply H2. intros. inversion H9. inversion H10. 
apply Trans with Wrong. apply EIfWrong. apply bb_nv. apply nv_zero. 
apply Refl.

assert (nvalue t1 \/ not (nvalue t1)). apply nonvalueornvalue. destruct H3.
apply Trans with Wrong. apply EIfWrong. apply bb_nv. apply nv_succ. apply H3. apply Refl. 
apply multitrans with (If Wrong t2 t3). apply multiif. apply IHt1. inversion H. apply H7.
apply H2. intros. inversion H4. inversion H5. contradiction. apply Trans with Wrong.
apply EIfWrong. apply bb_wrong. apply Refl. 

apply multitrans with (If Wrong t2 t3). apply multiif. apply IHt1. inversion H. apply H6.
apply H2. intros. inversion H3. inversion H4. apply Trans with Wrong. apply EIfWrong.
apply bb_wrong. apply Refl.

assert (nvalue t1 \/ not (nvalue t1)). apply nonvalueornvalue. destruct H3.
destruct H3. assert (goodstep (Iszero O) True). apply EGood. apply nw_iszero. apply nw_O.
apply nw_true. apply EIsZeroZero. apply H2 in H3. contradiction.
assert (goodstep (Iszero (Succ nv)) False). apply EGood. inversion H; auto. apply nw_false.
apply EIsZeroSucc. apply H3. apply H2 in H4; contradiction.

apply multitrans with (If Wrong t2 t3). apply multiif. apply IHt1. inversion H. apply H7.
apply H2. intros. inversion H4. inversion H5. apply Trans with Wrong. apply EIfWrong.
apply bb_wrong. apply Refl.

apply Trans with Wrong. apply EIfWrong. apply bb_wrong. apply Refl.
assert (value O). apply v_nv. apply nv_zero.
contradiction. 
assert (forall t2, ~ goodstep t t2). intros. unfold not; intros.
assert (goodstep (Succ t) (Succ t2)). apply EGood. apply H. apply nw_succ. inversion H2; auto.
apply ESucc. inversion H2; auto. apply H0 in H3; auto. 
assert (~ (nvalue t)). unfold not; intros.
assert (nvalue (Succ t)). apply nv_succ. apply H3. apply v_nv in H4. contradiction.
assert ( (value t) \/ not (value t)). apply novalueorvalue. destruct H4.
destruct H4. 
apply Trans with Wrong. apply ESuccWrong. apply bn_true. apply Refl.
apply Trans with Wrong. apply ESuccWrong. apply bn_false. apply Refl.
contradiction. apply Trans with Wrong. apply ESuccWrong. apply bn_wrong. apply Refl.
apply multitrans with (Succ Wrong). apply multisucc. apply IHt. inversion H; auto.
apply H2. apply H4. apply Trans with Wrong. apply ESuccWrong. apply bn_wrong. apply Refl.

assert (forall t2, ~ goodstep t t2). intros. unfold not; intros.
assert (goodstep (Pred t) (Pred t2)). apply EGood. apply H. apply nw_pred. inversion H2; auto.
apply EPred. inversion H2; auto. apply H0 in H3; auto. 
assert ( (value t) \/ not (value t)). apply novalueorvalue. destruct H3.
destruct H3. 
apply Trans with Wrong. apply EPredWrong. apply bn_true. apply Refl.
apply Trans with Wrong. apply EPredWrong. apply bn_false. apply Refl.
destruct H3. assert (goodstep (Pred O) O). apply EGood. apply H. apply nw_O. apply EPredZero.
apply H0 in H3. contradiction. assert (goodstep (Pred (Succ nv)) nv). apply EGood.
apply H. inversion H. inversion H5. apply H7. apply EPredSucc. apply H3. apply H0 in H4. contradiction.
apply Trans with Wrong. apply EPredWrong. apply bn_wrong. apply Refl.
apply multitrans with (Pred Wrong). apply multipred. apply IHt. inversion H. apply H5.
apply H2. apply H3. apply Trans with Wrong. apply EPredWrong. apply bn_wrong. apply Refl.

assert (forall t2, ~ goodstep t t2). intros. unfold not; intros.
assert (goodstep (Iszero t) (Iszero t2)). apply EGood. apply H. apply nw_iszero. inversion H2; auto.
apply EIsZero. inversion H2; auto. apply H0 in H3; auto. 
assert ( (value t) \/ not (value t)). apply novalueorvalue. destruct H3.
destruct H3. 
apply Trans with Wrong. apply EIsZeroWrong. apply bn_true. apply Refl.
apply Trans with Wrong. apply EIsZeroWrong. apply bn_false. apply Refl.
destruct H3. assert (goodstep (Iszero O) True). apply EGood. apply H. apply nw_true. apply EIsZeroZero.
apply H0 in H3. contradiction. assert (goodstep (Iszero (Succ nv)) False). apply EGood.
apply H. apply nw_false. apply EIsZeroSucc. apply H3. apply H0 in H4. contradiction.
apply Trans with Wrong. apply EIsZeroWrong. apply bn_wrong. apply Refl.
apply multitrans with (Iszero Wrong). apply multiiszero. apply IHt. inversion H. apply H5.
apply H2. apply H3. apply Trans with Wrong. apply EIsZeroWrong. apply bn_wrong. apply Refl.

apply Refl. Qed.

Theorem thm3_5_16: forall t, NoWrong t -> ((exists u, multigoodstep t u /\ normalstop u) <-> (exists v, multistep t v /\ v = Wrong)).
intros. split. intros. destruct H0. destruct H0. induction H0.
apply A4 in H1. exists Wrong. split. apply H1. reflexivity. inversion H0. apply IHmultigoodstep in H4. destruct H4. destruct H4.
exists x. split. inversion H0. apply Trans with (t2:=t2). apply H5. apply H4. apply H8. apply H1.
intros. destruct H0. destruct H0. induction H0.
subst. inversion H. assert ((NoWrong t2) \/ not (NoWrong t2)). apply nowrongorwrong. destruct H3. assert (NoWrong t2). apply H3.
apply IHmultistep in H3. destruct H3. destruct H3. exists x. split. apply ETransGood with t2. apply EGood.
apply H. apply H4. apply H0. apply H3. apply H5. apply H1. exists t1. split. apply EMultiGood. apply H. apply nexist.
apply H. unfold not. intros. assert (t0 = t2). inversion H4. apply thm3_5_4 with t1. apply H7. apply H0.
subst. inversion H4. contradiction. unfold not. intros. destruct H4. inversion H0. inversion H0. apply nvstep with (nv:=nv) (t:=t2) in H0.
apply H0. apply H4. inversion H0. Qed.