Inductive term : Type :=
  | True: term
  | False: term
  | If: term -> term-> term-> term.
  
Inductive value: term -> Prop :=
| v_true: value True
| v_false: value False.


Definition eg_1 : term := If (If True False False) False True.

Inductive syntax: term -> term-> Prop :=
  | EIfTrue: forall t2 t3, syntax (If True t2 t3) t2
  | EIfFalse: forall t2 t3, syntax (If False t2 t3) t3
  | EIf: forall t1 t1' t2 t3, (syntax t1 t1') -> (syntax (If t1 t2 t3) (If t1' t2 t3)).

Inductive normal: term -> Prop :=
| nexist: forall t, (forall t1, not (syntax t t1)) -> normal t.


Theorem thm3_5_7: forall t, value t -> normal t.
intros. induction t. apply nexist. intros. unfold not. intros. inversion H0.
apply nexist. intros. unfold not. intros. inversion H0. inversion H.
Qed.

Theorem thm3_5_8: forall t, normal t -> value t. induction t.
intros. apply v_true. intros. apply v_false. intros. induction t1. 
inversion H. unfold not in H0. assert (syntax (If True t2 t3) t2). apply EIfTrue.
apply H0 in H2. contradiction. inversion H. unfold not in H0.
assert (syntax (If False t2 t3) t3). apply EIfFalse. apply H0 in H2. contradiction.
assert (not (value (If t1_1 t1_2 t1_3))). unfold not. intros. inversion H0.
assert (forall A B: Prop, (A->B) -> ((not B) -> (not A))). unfold not.
intros. apply H1 in H3. apply H2 in H3. contradiction. apply H1 in IHt1.
unfold not in IHt1. inversion H. unfold not in H2.
inversion H.
inversion H.

Theorem thm3_5_4: forall t1 t2 t3, (syntax t1 t2) -> (syntax t1 t3) -> t2=t3.
intros. generalize dependent t3.
induction H. intros.
inversion H0. reflexivity. subst. inversion H4.
intros. inversion H0. subst. reflexivity. inversion H4.
intros. inversion H0. subst. inversion H. subst. inversion H.  subst.
apply IHsyntax in H5. subst. reflexivity. 
Qed.  