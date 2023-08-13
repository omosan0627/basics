Require Import Psatz.

Inductive term : Type :=
  | True: term
  | False: term
  | If: term -> term-> term-> term.
  
Inductive value: term -> Prop :=
| v_true: value True
| v_false: value False.


Fixpoint size (T:term): nat:=
  match T with
  | True => 1
  | False => 1
  | If t1 t2 t3 => (size t1) + (size t2) + (size t3) + 1
  end.


Definition eg_1 : term := If (If True False False) False True.

Inductive step: term -> term-> Prop :=
  | EIfTrue: forall t2 t3, step (If True t2 t3) t2
  | EIfFalse: forall t2 t3, step (If False t2 t3) t3
  | EIf: forall t1 t1' t2 t3, (step t1 t1') -> (step (If t1 t2 t3) (If t1' t2 t3)).

Lemma reduce_depth: forall t1 t2, step t1 t2 -> size t1 > size t2.
intros. induction H. simpl. lia. simpl. lia. simpl. lia. Qed.

Lemma no_step: forall t, not (step t t). unfold not.
intros. apply reduce_depth in H. lia. Qed.
Inductive normal: term -> Prop :=
| nexist: forall t, (forall t1, not (step t t1)) -> normal t.

Lemma If_one_step: forall t1 t2 t3, exists t, step (If t1 t2 t3) t.
intros. generalize dependent t2. generalize dependent t3.
induction t1. intros. exists t2. apply EIfTrue. intros. exists t3. apply EIfFalse.
assert (exists t: term, step (If t1_1 t1_2 t1_3) t).
apply IHt1_1. destruct H. intros.
exists (If x t2 t3). apply EIf. apply H. Qed.

Theorem thm3_5_7: forall t, value t -> normal t.
intros. induction t. apply nexist. intros. unfold not. intros. inversion H0.
apply nexist. intros. unfold not. intros. inversion H0. inversion H.
Qed.

Theorem thm3_5_8: forall t, normal t -> value t. induction t.
intros. apply v_true. intros. apply v_false. intros. assert (exists x, step (If t1 t2 t3) x).
apply If_one_step. destruct H0. assert (not (step (If t1 t2 t3) x)). inversion H. 
apply H1. contradiction. Qed. 

Theorem thm3_5_4: forall t1 t2 t3, (step t1 t2) -> (step t1 t3) -> t2=t3.
intros. generalize dependent t3.
induction H. intros.
inversion H0. reflexivity. subst. inversion H4.
intros. inversion H0. subst. reflexivity. inversion H4.
intros. inversion H0. subst. inversion H. subst. inversion H.  subst.
apply IHstep in H5. subst. reflexivity. 
Qed.  


Inductive multistep: term->term->Prop:=
  | Init: forall t1 t2, step t1 t2 -> multistep t1 t2
  | Refl: forall t, multistep t t
  | Trans: forall t1 t2 t3, multistep t1 t2 -> multistep t2 t3 -> multistep t1 t3.

Inductive multistep2: term->term->Prop:=
  | Refl2: forall t, multistep2 t t
  | Trans2: forall t1 t2 t3, step t1 t2 -> multistep2 t2 t3 -> multistep2 t1 t3.

Lemma multistep2_trans: forall t1 t2 t3, multistep2 t1 t2 -> multistep2 t2 t3 -> multistep2 t1 t3.
intros. generalize dependent t3. induction H. intros. apply H0.
intros. assert (multistep2 t2 t0). apply IHmultistep2. apply H1. apply Trans2 with (t2).
apply H. apply H2. Qed.

Theorem multistep_equiv: forall t1 t2, multistep t1 t2 <-> multistep2 t1 t2.
 split. intros. induction H. apply Trans2 with (t2:=t2). apply H. apply Refl2.
 apply Refl2. apply multistep2_trans with t2. auto. auto. intros. induction H. apply Refl. apply Trans with (t2:=t2).
 apply Init. apply H. apply IHmultistep2. Qed. 

Theorem thm3_5_11: forall t u v, multistep t u -> multistep t v -> normal u -> normal v -> u = v.
intros. apply thm3_5_8 in H1,H2. apply multistep_equiv in H, H0. generalize dependent u.
induction H0. intros. induction H. reflexivity. destruct H2.  inversion H. inversion H.
intros. destruct H1. destruct H3. inversion H. inversion H. apply IHmultistep2.
apply H2. assert (t2=t0). apply thm3_5_4 with (t1). apply H. apply H1. subst. apply H4.
apply H3. Qed.

Theorem multi_If: forall t t' t2 t3, multistep t t' -> multistep (If t t2 t3) (If t' t2 t3).
intros. induction H. apply Init. apply EIf. apply H. apply Refl.
apply Trans with (If t0 t2 t3). auto. auto. Qed.

Theorem thm3_5_12: forall t, exists t1, multistep t t1 /\ normal t1.
intros. induction t. exists True. split. apply Refl. apply thm3_5_7. apply v_true.
exists False. split. apply Refl. apply thm3_5_7. apply v_false.
destruct IHt1. destruct H. apply thm3_5_8 in H0. destruct H0.
assert (multistep (If t1 t2 t3) t2). apply Trans with (If True t2 t3). apply multi_If.
apply H. apply Init. apply EIfTrue. destruct IHt2. destruct H1.
exists x. split. apply Trans with (t2). apply H0. apply H1. apply H2.
assert (multistep (If t1 t2 t3) t3). apply Trans with (If False t2 t3). apply multi_If.
apply H. apply Init. apply EIfFalse. destruct IHt3. destruct H1. exists x.
split. apply Trans with t3. apply H0. apply H1. apply H2. Qed.

Inductive funnystep: term -> term-> Prop :=
  | FEIfTrue: forall t2 t3, funnystep (If True t2 t3) t2
  | FEIfFalse: forall t2 t3, funnystep (If False t2 t3) t3
  | FEIf: forall t1 t1' t2 t3, (funnystep t1 t1') -> (funnystep (If t1 t2 t3) (If t1' t2 t3))
  | FEFunny: forall t1 t2 t2' t3, (funnystep t2 t2') -> (funnystep (If t1 t2 t3) (If t1 t2' t3)).

Lemma diamond: forall r s t, funnystep r s -> funnystep r t -> s = t \/ funnystep s t \/ funnystep t s \/ (exists u, 
funnystep s u /\ funnystep t u). intros. generalize dependent t. induction H. intros. inversion H0. left. reflexivity.
subst. inversion H4. subst. right. right. right. exists t2'. split. apply H4. apply FEIfTrue.
intros. inversion H0. left. reflexivity.
intros. subst. inversion H4. subst. right. right. left. apply FEIfFalse. intros.
inversion H0. subst. inversion H. subst. inversion H. subst. apply IHfunnystep in H5.
destruct H5. left. subst. reflexivity. destruct H1.
right. left. apply FEIf. apply H1.
destruct H1. right. right. left. apply FEIf. apply H1. destruct H1. destruct H1. right. right. right. exists (If x t2 t3).
split. apply FEIf. apply H1. apply FEIf. apply H2. subst.
right. right. right. exists (If t1' t2' t3). split. apply FEFunny. apply H5. apply FEIf. apply H.
intros. inversion H0. subst. right. right. right. exists t2'. split. apply FEIfTrue.
apply H. subst. right. left. apply FEIfFalse. subst. right. right. right. exists (If t1' t2' t3).
split. apply FEIf. apply H5. apply FEFunny. apply H. subst. apply IHfunnystep in H5. destruct H5.
left. subst. reflexivity. destruct H1.
right. left. apply FEFunny. apply H1. destruct H1. right. right. left. apply FEFunny. apply H1.
destruct H1. destruct H1. right. right. right. exists (If t1 x t3). split.
apply FEFunny. apply H1. apply FEFunny. apply H2. Qed.  


Inductive funnymultistep2: term->term->Prop:=
  | FRefl2: forall t, funnymultistep2 t t
  | FTrans2: forall t1 t2 t3, funnystep t1 t2 -> funnymultistep2 t2 t3 -> funnymultistep2 t1 t3.

Lemma funny_one_step: forall t1 t2 v, funnymultistep2 t1 v -> funnystep t1 t2 -> value v -> 
funnymultistep2 t2 v. intros. generalize dependent t2. induction H.
intros. destruct H1. inversion H0. inversion H0. intros.
apply diamond with (r:=t1) (s:=t2) (t:=t0) in H. destruct H. subst. apply H0.
destruct H. apply IHfunnymultistep2. apply H1. apply H. destruct H.
apply FTrans2 with t2. apply H. apply H0. destruct H. destruct H.
apply IHfunnymultistep2 in H. apply FTrans2 with x. apply H3. apply H. apply H1. apply H2. Qed.

Theorem funny3_5_11: forall t u v, funnymultistep2 t u -> funnymultistep2 t v -> value u -> value v -> u = v.
intros. generalize dependent v. induction H. intros. induction H0. reflexivity.
destruct H1. inversion H. inversion H. intros. inversion H2. subst. destruct H3.
inversion H. inversion H. subst. apply diamond with (r:=t1) (s:=t2) (t:=t4) in H.
destruct H. subst. apply IHfunnymultistep2. apply H1. apply H5. apply H3.
destruct H. apply IHfunnymultistep2. apply H1. apply FTrans2 with t4. apply H.
apply H5. apply H3. destruct H. apply IHfunnymultistep2. apply H1. apply funny_one_step with t4.
apply H5. apply H. apply H3. apply H3.
destruct H. destruct H. apply IHfunnymultistep2. apply H1. assert (funnymultistep2 x v).
apply funny_one_step with t4. apply H5. apply H6. apply H3. apply FTrans2 with x. apply H. apply H7.
apply H3. apply H4. Qed.
