Inductive term : Type :=
  | True: term
  | False: term
  | If: term -> term-> term-> term.
  
Inductive value: term -> Prop :=
| v_true: value True
| v_false: value False.


Definition eg_1 : term := If (If True False False) False True.

Inductive step: term -> term-> Prop :=
  | EIfTrue: forall t2 t3, step (If True t2 t3) t2
  | EIfFalse: forall t2 t3, step (If False t2 t3) t3
  | EIf: forall t1 t1' t2 t3, (step t1 t1') -> (step (If t1 t2 t3) (If t1' t2 t3)).

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
  | Trans: forall t1 t2 t3, multistep t1 t2 -> step t2 t3 -> multistep t1 t3.

Lemma multitrans: forall t1 t2 t3, multistep t1 t2 -> multistep t2 t3 -> multistep t1 t3.
intros. generalize dependent t1. induction H0. intros.
apply Trans with (t2:=t1). exact H0. exact H. intros. exact H. intros. apply IHmultistep in H1.
apply Trans with (t2 := t2). apply H1. apply H. Qed. 

Lemma multi_true: forall t1 t2, value t1 -> multistep t1 t2 -> t2 = t1.
intros. induction H0. inversion H. subst. inversion H0.
subst. inversion H0. reflexivity. assert (value t1). apply H. apply IHmultistep in H. subst.
inversion H2. subst. inversion H1. subst. inversion H1. Qed.


Lemma multi_EIf: forall t1 t1' t2 t3, multistep t1 t1' -> multistep (If t1 t2 t3) (If t1' t2 t3).
intros. generalize dependent t2. generalize dependent t3. induction H.
intros. apply Init. apply EIf. exact H. intros. apply Refl.
intros. apply Trans with (t2 := If t2 t4 t0). apply IHmultistep. apply EIf. apply H0. Qed.

Lemma multi_IfTrue: forall t1 t2 t3, multistep t1 True -> multistep (If t1 t2 t3) t2.
intros. assert (multistep (If t1 t2 t3) (If True t2 t3)). apply multi_EIf. exact H.
apply Trans with (t2 := (If True t2 t3)). exact H0. apply EIfTrue. Qed.


Lemma multi_IfFalse: forall t1 t2 t3, multistep t1 False -> multistep (If t1 t2 t3) t3.
intros. assert (multistep (If t1 t2 t3) (If False t2 t3)). apply multi_EIf. exact H.
apply Trans with (t2 := (If False t2 t3)). exact H0. apply EIfFalse. Qed.

Theorem thm3_5_12: forall t, exists t1, multistep t t1 /\ normal t1.
intros. induction t. exists True. split. apply Refl. apply thm3_5_7. apply v_true.
exists False. split. apply Refl. apply thm3_5_7. apply v_false.
destruct IHt1. destruct H. apply thm3_5_8 in H0. inversion H0. subst.
apply multi_IfTrue with (t2 := t2) (t3 := t3) in H. destruct IHt2. destruct H1.
assert ((multistep (If t1 t2 t3) t2)->(multistep t2 x)->multistep (If t1 t2 t3) x).
apply multitrans. apply H3 in H. exists x. split. apply H. apply H2. apply H1.
subst. apply multi_IfFalse with (t2:=t2) (t3:=t3) in H.  destruct IHt3. destruct H1.
assert (multistep (If t1 t2 t3) t3 -> multistep t3 x -> multistep (If t1 t2 t3) x).
apply multitrans. apply H3 in H. exists x. split. apply H. apply H2. apply H1. Qed.

Theorem thm3_5_11: forall t u v, multistep t u -> multistep t v -> normal u -> normal v -> u = v.
Admitted.