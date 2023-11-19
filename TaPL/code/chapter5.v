Require Import List.
Require Import Nat.
Require Import Arith.

Inductive symbol : Type := 
| Symb: nat -> symbol.

Fixpoint eq_nat (n:nat) (m:nat) : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

Lemma eq_nat_eq: forall n, eq_nat n n = true.
induction n. simpl. reflexivity. simpl. apply IHn. Qed.

Lemma eq_nat_swap: forall n m, eq_nat n m = eq_nat m n.
intro. induction n. destruct m. simpl. reflexivity. simpl. reflexivity.
intros. destruct m. simpl. reflexivity. simpl. apply IHn. Qed.

Lemma eq_nat_equal: forall n m, eq_nat n m = true <-> n = m.
split. generalize dependent m. induction n. intros. destruct m. reflexivity. simpl in H.
inversion H. intros. destruct m. simpl in H. inversion H. simpl in H. apply IHn in H.
subst. reflexivity. generalize dependent m. induction n. destruct m.
simpl. reflexivity. intros. inversion H. intros. destruct m. inversion H.
inversion H. simpl. apply eq_nat_eq. Qed.


Definition eq_symbol (x: symbol) (y: symbol): bool :=
    match x, y with
    | Symb v, Symb w => eq_nat v w
    end.

Definition succ_symbol (x: symbol): symbol :=
    match x with
    | Symb v => Symb (S v)
    end.

Inductive term : Type :=
  | Var: symbol -> term
  | Abst: symbol -> term -> term
  | App: term -> term -> term.

Inductive index: Type :=
  | IndVar: nat -> index
  | IndAbst: index -> index
  | IndApp: index -> index -> index.

Definition VA: symbol := Symb 0.
Definition VB: symbol := Symb 1.
Definition VC: symbol := Symb 2.
Definition VD: symbol := Symb 3.
Definition VE: symbol := Symb 4.

Definition tru: term := Abst VA (Abst VB (Var VA)).
Definition fls: term := Abst VA (Abst VB (Var VD)).
Definition test: term := Abst VA (Abst VB (Abst VC (App (App (Var VA) (Var VB)) (Var VD)))).

Fixpoint find_index (l: list symbol) (x: symbol) : option nat :=
  match l with
  | nil => None 
  | t :: l => if eq_symbol x t then Some 0 else 
    (match find_index l x with
      | None => None
      | Some k => Some (S k)
    end)
  end.

Fixpoint removenames (t:term) (l: list symbol) : option index :=
  match t with
  | Var x => 
    (match find_index l x with 
      | None => None
      | Some x => Some (IndVar x)
    end)
  | Abst x t => 
    (match removenames t (x :: l) with
      | None => None 
      | Some s => Some (IndAbst s)
    end)
  | App t1 t2 => 
    (match removenames t1 l, removenames t2 l with
      | None, _ => None
      | _, None => None
      | Some s1, Some s2 => Some (IndApp s1 s2)
    end)
  end.

Fixpoint restorenames (i:index) (l: list symbol) : option term :=
  match i with
  | IndVar k => 
    (match nth_error l k with
      | None => None
      | Some x => Some (Var x)
    end)
  | IndAbst i1 => let x := 
    (match l with
      | nil => Symb 0
      | Symb k :: l' => Symb (S k)
    end) in
    (match restorenames i1 (x :: l) with 
      | None => None
      | Some s => Some (Abst x s)
    end)
  | IndApp i1 i2 => 
    (match restorenames i1 l, restorenames i2 l with
      | None, _ => None
      | _, None => None
      | Some s1, Some s2 => Some (App s1 s2)
    end)
  end.

Inductive Gamma: list symbol -> Prop :=
  | NSNil: Gamma nil
  | NSOne: forall x, Gamma (x :: nil)
  | NSCons: forall n m l, Gamma (Symb n :: l) -> n < m -> Gamma (Symb m :: Symb n :: l).

Lemma some_or_none: forall A, forall t: option A, (exists s, t = Some s) \/ t = None.
intros. destruct t. left. exists a. reflexivity. right. reflexivity. Qed.

Lemma Gamma_retain: forall x l, Gamma l -> (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end) = x ->
Gamma (x :: l). intros. generalize dependent x. induction H. intros. apply NSOne.
intros. destruct x0. destruct x. apply NSCons. apply NSOne. inversion H0. apply le_lt_n_Sm.
apply le_n. intros. subst. apply NSCons. apply NSCons. apply H. apply H0. apply le_lt_n_Sm. apply le_n.
Qed. 

Lemma Gamma_three: forall x y l, Gamma (x :: y :: l) -> Gamma (x :: l).
induction l. intros. apply NSOne. intros. inversion H. inversion H2.
apply NSCons. apply H7. apply lt_trans with (m:=n). apply H9. apply H4. Qed.

Lemma Gamma_find: forall l i j k, find_index l (Symb i) = Some k -> Gamma ((Symb j) :: l) -> j > i.
induction l. intros. simpl in H. inversion H. intros. assert (forall b, b = true \/ b = false).
intros. destruct b. left. reflexivity. right. reflexivity. assert (eq_symbol a (Symb i) = true \/ 
eq_symbol a (Symb i) = false). apply H1. destruct H2. simpl in H. destruct a. 
simpl in H2. assert (eq_nat n i = eq_nat i n). apply eq_nat_swap. rewrite H3 in H2. rewrite H2 in H.
inversion H. assert (i = n). apply eq_nat_equal in H2. apply H2. subst. inversion H0.
apply H8. destruct a. simpl in H. inversion H2. assert (eq_nat n i = eq_nat i n).
apply eq_nat_swap. rewrite H3 in H4. rewrite H4 in H. assert ((exists s, find_index l (Symb i) = Some s) \/ find_index l (Symb i) = None).
apply some_or_none. destruct H5. destruct H5. rewrite H5 in H. inversion H. 
apply IHl with (j:=j) in H5. apply H5. apply Gamma_three in H0. apply H0. rewrite H5 in H. inversion H. Qed.

Lemma not_equal_or_equal: forall (n0 :nat) (n1 :nat), n0 = n1 \/ ~ (n0 = n1).
intros. generalize dependent n1. induction n0. destruct n1. left. reflexivity. right. unfold not. intros. inversion H. 
induction n1. right. unfold not. intros. inversion H. assert (n0 = n1 \/ n0 <> n1).
apply IHn0. destruct H. left. subst. reflexivity. right. unfold not. intros. inversion H0.
contradiction. Qed. 

Lemma eqnot_eq_symbol: forall n1 n0, n1 <> n0 -> eq_symbol (Symb n1) (Symb n0) = false.
intros. unfold not in H. generalize dependent n0. induction n1. intros. destruct n0.
assert (0 = 0). reflexivity. apply H in H0. contradiction. simpl. reflexivity.
intros. destruct n0. simpl. reflexivity. simpl. simpl in IHn1. apply IHn1. intros. assert (S n1 = S n0).
subst. reflexivity. apply H in H1. apply H1. Qed.

Lemma eqnot_succ: forall n, S n <> n. unfold not. intros. induction n. inversion H.
inversion H. apply IHn in H1. apply H1. Qed.

Lemma lt_eq: forall n0, not (n0 > n0). intros. unfold not. intros.
induction n0. inversion H. apply gt_S_n in H. apply IHn0. apply H. Qed.

Corollary gt_eq_symbol: forall n1 n0, n1 < n0 -> eq_symbol (Symb n1) (Symb n0) = false.
intros. assert (n1 <> n0). unfold not. intros. subst. apply lt_eq in H. apply H.
apply eqnot_eq_symbol in H0. apply H0. Qed.


Lemma nth_error_inversion: forall l n x, Gamma l -> nth_error l n = Some x -> find_index l x = Some n.

induction l. intros. generalize dependent x. destruct n. intros. simpl in H0.  inversion H0.
intros. simpl in H0. inversion H0.
intros. destruct n. simpl in H0. inversion H0. simpl. assert (eq_symbol x x = true).
destruct x. unfold eq_symbol. apply eq_nat_eq. rewrite H1. reflexivity.
simpl in H0. apply IHl in H0. simpl. destruct x. destruct a. 
assert (find_index l (Symb n0) = Some n). apply H0.
apply Gamma_find with (j:=n1) in H0. 
assert (eq_symbol (Symb n0) (Symb n1) = false). apply gt_eq_symbol. apply H0. rewrite H2. 
assert ((exists s, find_index l (Symb n0) = Some s) \/ find_index l (Symb n0) = None).
apply some_or_none. destruct H2. destruct H3. destruct H2.
rewrite H1. reflexivity. assert (Some n = None). symmetry in H1. symmetry in H2. rewrite H1.
rewrite H2. reflexivity. inversion H3. apply H. inversion H. apply NSNil. apply H3. Qed.

Theorem thm6_1_5: forall i l t, Gamma l -> restorenames i l = Some t ->
removenames t l = Some i.
intros. generalize dependent l. generalize dependent t. 
induction i.
intros. inversion H0. assert ((exists s, nth_error l n = Some s) \/ nth_error l n = None).
apply some_or_none. destruct H1. destruct H1.
rewrite H1 in H2. inversion H2. simpl. assert (find_index l x = Some n). apply nth_error_inversion.
apply H. apply H1.  
rewrite H3. reflexivity. rewrite H1 in H2. inversion H2.
intros. inversion H0. assert (exists x, (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end) = x).
exists (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end).
reflexivity. destruct H1. rewrite H1 in H2.
assert ((exists s, restorenames i (x :: l) = Some s) \/ restorenames i (x :: l) = None). apply some_or_none.
destruct H3. destruct H3. rewrite H3 in H2. inversion H2. simpl. assert (removenames x0 (x :: l) = Some i).
apply IHi. apply Gamma_retain. apply H. apply H1. apply H3. rewrite H4. reflexivity. rewrite H3 in H2. inversion H2.
intros. inversion H0.
assert ((exists s1, restorenames i1 l = Some s1) \/ restorenames i1 l = None).
apply some_or_none. assert ((exists s1, restorenames i2 l = Some s1) \/ restorenames i2 l = None).
apply some_or_none. destruct H1. destruct H1. destruct H3. destruct H3. rewrite H1 in H2.
rewrite H3 in H2. inversion H2. simpl. assert (removenames x l = Some i1). apply IHi1.
apply H. apply H1. assert (removenames x0 l = Some i2). apply IHi2. apply H.
apply H3. rewrite H4. rewrite H6. reflexivity. rewrite H1 in H2. rewrite H3 in H2. inversion H2.
rewrite H1 in H2. inversion H2. Qed.

Fixpoint is_free_var (x: symbol) (t:term): bool :=
  match t with
  | Var y => eq_symbol x y
  | Abst y t1 => if eq_symbol x y then false else is_free_var x t1
  | App t1 t2 => is_free_var x t1 || is_free_var x t2
  end.

Definition is_false (b:bool): bool :=
  match b with
  | true => false
  | false => true
  end.

Fixpoint subst (x: symbol) (s:term) (t: term): option term :=
match t with
| Var y => if eq_symbol x y then Some s else Some (Var y)
| Abst y t1 => if eq_symbol x y then Some (Abst y t1) else if 
  is_false (is_free_var y s) then (match (subst x s t1) with 
  | None => None
  | Some t1' => Some (Abst y t1')
  end
  ) else None
| App t1 t2 => (match (subst x s t1), (subst x s t2) with
  | None, _ => None
  | _, None => None
  | Some t1', Some t2' => Some (App t1' t2')
end
)
end.

Inductive value: term -> Prop :=
  | v_Abst: forall x t1, value (Abst x t1).

Inductive term_step: term -> term -> Prop :=
  | EApp1: forall t1 t1' t2, term_step t1 t1' -> term_step (App t1 t2) (App t1' t2)
  | EApp2: forall v1 t2 t2', value v1 -> term_step t2 t2' -> term_step (App v1 t2) (App v1 t2')
  | EAppAbs: forall x t12 v2 s, value v2 -> subst x v2 t12 = Some s ->
    term_step (App (Abst x t12) v2) s.

(* alpha変換の定義をあるtermからremovenamesで一致するtermに置き換える、にする。*)    
(* alpha変換+term_stepを繰り返して、たどりつくtermの1つが得られれば良い。これは次のindex_stepを繰り返すこと
に他ならなくて、またindex_step i1 i2 -> shift_step i1 i2が示せれば、
1. removenames
2. shift_stepを繰り返す
3. restorenames
という枠組みでできる。*)    
Inductive index_step: list symbol -> index -> index -> Prop :=
  | TermRev: forall l i1 i2, (exists t1 t2, (removenames t1 l) = Some i1 /\ (removenames t2 l) = Some i2 /\ term_step t1 t2) 
  -> index_step l i1 i2.

Fixpoint eval (t:term): term :=
  match t with
  | App t1 t2 => (
    match t1 with
    | Abst x t12 => (
      match t2 with
      | Abst _ _ => (
        match subst x t2 t12 with
        | None => Var (Symb 1919)
        | Some s => s
        end
      )
      | _ => App t1 (eval t2)
      end
    )
    | _ => App (eval t1) t2
    end
  )
  | _ => Var (Symb 1919)
  end.

Lemma step_match_eval: forall t1 t2, term_step t1 t2 -> t2 = eval t1.
intros. induction H. 
subst. destruct t1. inversion H. inversion H. simpl. reflexivity.
subst. inversion H. destruct t2. inversion H0. inversion H0. simpl. reflexivity.
simpl. inversion H. subst. remember (subst x (Abst x0 t1) t12) as tt. revert Heqtt. subst. 
intros. reflexivity. Qed.

(* d: None-> means -1 *)
Fixpoint shift (t: index) (d: option nat) (c: nat): index :=
match t with
| IndVar k => if (k <? c) then IndVar k else
  (match d with
  | Some d' => IndVar (k + d')
  | None => IndVar (pred k)
  end)
| IndAbst t1 => IndAbst (shift t1 d (S c))
| IndApp t1 t2 => IndApp (shift t1 d c) (shift t2 d c)
end.

Fixpoint index_subst (j: nat) (s:index) (t: index): index :=
  match t with
  | IndVar k => if k =? j then s else IndVar k
  | IndAbst t1 => IndAbst (index_subst (S j) (shift s (Some 1) 0) t1)
  | IndApp t1 t2 => IndApp (index_subst j s t1) (index_subst j s t2)
  end.

Lemma shift_inversion: forall t c, shift (shift t (Some 1) c) None c = t. induction t.
intros. simpl. assert (n + 1 = S n). admit. rewrite H.
assert (n <? c = true \/ n <? c = false). admit. destruct H0. rewrite H0. simpl. rewrite H0. reflexivity.
rewrite H0. simpl. assert (n <? c = false -> S n <? c = false). admit. apply H1 in H0. rewrite H0.
reflexivity.
intros. simpl. assert (shift (shift t (Some 1) (S c)) None (S c) = t). apply IHt.
rewrite H. reflexivity.
simpl. intros. rewrite IHt1. rewrite IHt2. reflexivity. Admitted.

Lemma find_index_concat: forall l1 l2 s k, find_index (l1 ++ l2) s = Some k ->
find_index l1 s = Some k \/ (find_index l1 s = None /\ (exists i, find_index l2 s = Some i /\ i + length l1 = k)).
induction l1. intros. right. split. simpl. reflexivity.
exists k. split. simpl in H. apply H. simpl. admit.
intros. simpl in H. assert (eq_symbol s a = true \/ eq_symbol s a = false).
admit. destruct H0. rewrite H0 in H. inversion H. left. simpl. rewrite H0. reflexivity.
rewrite H0 in H. assert ((exists j, find_index (l1 ++ l2) s = Some j) \/ find_index (l1 ++ l2) s = None).
apply some_or_none. destruct H1. destruct H1. rewrite H1 in H. apply IHl1 in H1.
destruct H1. left. simpl. rewrite H0. rewrite H1. apply H. right.
split. simpl. rewrite H0. destruct H1. rewrite H1. reflexivity. destruct H1.
destruct H2. exists x0. split. destruct H2. apply H2. destruct H2. inversion H.
simpl. subst. admit. rewrite H1 in H. inversion H. Admitted. 

Lemma removenames_xx: forall t x l1 l2 l3 s1 c, removenames t  (l1 ++ (x :: l2) ++ l3) = Some s1 -> length l1 + length l2 = c
-> exists s2, removenames t (l1 ++ (x :: l2) ++ (x :: l3)) = Some s2 /\ s2 = shift s1 (Some 1) (S c).
induction t.
intros. simpl in H.
assert ((exists k, find_index (l1 ++ x :: l2 ++ l3) s = Some k) \/ find_index (l1 ++ x :: l2 ++ l3) s = None).
apply some_or_none. destruct H1. destruct H1. rewrite H1 in H. apply find_index_concat in H1.
destruct H1. exists s1. simpl.
assert ((exists k, find_index (l1 ++ x :: l2 ++ x :: l3) s = Some k) \/ find_index (l1 ++ x :: l2 ++ x ::l3) s = None).
apply some_or_none. destruct H2. destruct H2. rewrite H2. split.
apply find_index_concat in H2. destruct H2. rewrite H1 in H2. inversion H2. subst. apply H.
destruct H2. rewrite H2 in H1. inversion H1. inversion H. simpl. admit.
admit. destruct H1. destruct H2. destruct H2. simpl in H2.
assert (eq_symbol s x = true \/ eq_symbol s x = false). admit. destruct H4.
rewrite H4 in H2. exists (IndVar (length l1)).
simpl.
assert ((exists k, find_index (l1 ++ x :: l2 ++  x :: l3) s = Some k) \/ find_index (l1 ++ x :: l2 ++ x ::l3) s = None).
apply some_or_none. destruct H5. destruct H5. rewrite H5. split.
apply find_index_concat in H5. destruct H5. rewrite H1 in H5. inversion H5. destruct H5.
destruct H6. destruct H6. simpl in H6. rewrite H4 in H6. inversion H6. subst.
admit. inversion H. simpl. subst. inversion H2. simpl. assert (length l1 <? S (length l1 + length l2) = true).
admit. rewrite H0. reflexivity. admit.
rewrite H4 in H2. assert ((exists k, find_index (l2 ++ l3) s = Some k) \/ find_index (l2 ++ l3) s = None).
apply some_or_none. destruct H5. destruct H5. rewrite H5 in H2. inversion H2.
apply find_index_concat in H5. destruct H5. exists (IndVar ((length l1) + x1)).
split. simpl.
assert ((exists k, find_index (l1 ++ x :: l2 ++ x :: l3) s = Some k) \/ find_index (l1 ++ x :: l2 ++ x ::l3) s = None).
apply some_or_none. destruct H6. destruct H6. rewrite H6.
apply find_index_concat in H6. destruct H6. rewrite H1 in H6. inversion H6.
destruct H6. destruct H8. destruct H8. simpl in H8. rewrite H4 in H8.
assert ((exists k, find_index (l2 ++ x :: l3) s = Some k) \/ find_index (l2 ++ x ::l3) s = None). apply some_or_none.
destruct H10. destruct H10. rewrite H10 in H8. inversion H8.
apply find_index_concat in H10. destruct H10. rewrite H5 in H10. inversion H10. subst. admit.
destruct H10. rewrite H10 in H5. inversion H5. rewrite H10 in H8. inversion H8. admit. inversion H.
simpl. admit. destruct H5. destruct H6. destruct H6. exists (IndVar (length l1 + x1 + 1)). 
split. simpl.
assert ((exists k, find_index (l1 ++ x :: l2 ++ x :: l3) s = Some k) \/ find_index (l1 ++ x :: l2 ++ x ::l3) s = None).
apply some_or_none. destruct H9. destruct H9. rewrite H9. apply find_index_concat in H9.
destruct H9. rewrite H9 in H1. inversion H1. destruct H9. destruct H10. destruct H10.
assert (x :: l2 ++ x :: l3 = (x :: l2) ++ x :: l3). simpl. reflexivity. rewrite H12 in H10.
apply find_index_concat in H10. destruct H10. simpl in H10. rewrite H4 in H10. rewrite H5 in H10. inversion H10.
destruct H10. destruct H13. destruct H13. simpl in H13. rewrite H4 in H13.
assert ((exists k, find_index l3 s = Some k) \/ find_index l3 s = None). apply some_or_none.
destruct H15. destruct H15. rewrite H15 in H6. inversion H6. rewrite H15 in H13. inversion H13. subst.
simpl. admit. rewrite H15 in H6. inversion H6. admit. inversion H. subst. simpl. 
admit. rewrite H5 in H2. inversion H2. rewrite H1 in H. inversion H.


intros. simpl in H. assert ((exists s3, removenames t (s :: l1 ++ x :: l2 ++ l3) = Some s3) \/ removenames t (s :: l1 ++ x :: l2 ++ l3) = None).
apply some_or_none. destruct H1. destruct H1. rewrite H1 in H. assert (s :: l1 ++ x :: l2 ++ l3 = (s :: l1) ++ x :: l2 ++ l3).
simpl. reflexivity. rewrite H2 in H1. apply IHt with (c := S c) in H1. simpl in H1. destruct H1. destruct H1.
exists (IndAbst x1). split. simpl. rewrite H1. reflexivity. inversion H. rewrite H3. simpl. reflexivity.
simpl. rewrite H0. reflexivity. rewrite H1 in H. inversion H.
intros. simpl in H. 
assert ((exists s3, removenames t1 (l1 ++ x :: l2 ++ l3) = Some s3) \/ removenames t1 (l1 ++ x :: l2 ++ l3) = None).
apply some_or_none. 
assert ((exists s4, removenames t2 (l1 ++ x :: l2 ++ l3) = Some s4) \/ removenames t2 (l1 ++ x :: l2 ++ l3) = None).
apply some_or_none. 
destruct H1. destruct H1. destruct H2. destruct H2. rewrite H1 in H. rewrite H2 in H. 
apply IHt1 with (c:=c) in H1. apply IHt2 with (c:=c) in H2. destruct H1. destruct H1.
destruct H2. destruct H2. exists (IndApp x2 x3). split. simpl. 
assert (x :: l2 ++ x :: l3 = (x :: l2) ++ x :: l3). simpl. reflexivity. rewrite H5.
rewrite H1. rewrite H2.
reflexivity. inversion H. rewrite H3. rewrite H4. simpl. reflexivity. apply H0. apply H0.
rewrite H2 in H. rewrite H1 in H. inversion H. rewrite H1 in H. inversion H. Admitted.

Lemma subst_removenames_xx: forall t1 s x l1 l2 t2, removenames t1 (l2 ++ x :: x :: l1) = Some t2 ->
index_subst (S (length l2)) s t2 = t2. induction t1.
intros. simpl in H.
assert ((exists k, find_index (l2 ++ x :: x :: l1) s = Some k) \/ find_index (l2 ++ x :: x :: l1) s = None).
apply some_or_none. destruct H0. destruct H0. rewrite H0 in H. inversion H. simpl.
apply find_index_concat in H0. destruct H0. assert ((x0 =? S (length l2)) = false).
admit. rewrite H1. reflexivity. destruct H0. destruct H1. destruct H1.
simpl in H1. assert (eq_symbol s x = true \/ eq_symbol s x = false). admit.
destruct H4. rewrite H4 in H1. inversion H1. subst. assert (0 + length l2 =? S (length l2) = false).
admit. rewrite H2. reflexivity. rewrite H4  in H1.
assert ((exists k, find_index l1 s = Some k) \/ find_index l1 s = None).
apply some_or_none. destruct H5. destruct H5. rewrite H5 in H1. inversion H1. subst.
assert (S (S x2) + length l2 =? S (length l2) = false). admit. rewrite H2. reflexivity.
rewrite H5 in H1. inversion H1. rewrite H0 in H. inversion H.

intros. simpl in H.
assert ((exists s1, removenames t1 (s :: l2 ++ x :: x :: l1) = Some s1) \/ removenames t1 (s :: l2 ++ x :: x :: l1) = None).
apply some_or_none. destruct H0. destruct H0. rewrite H0 in H.
assert (s :: l2 ++ x :: x :: l1 = (s :: l2) ++ x :: x :: l1). simpl. reflexivity.
rewrite H1 in H0. apply IHt1 with (s:=(shift s0 (Some 1) 0)) in H0. inversion H. simpl.
simpl in H0. rewrite H0. reflexivity. rewrite H0 in H. inversion H.
intros. simpl in H.
assert ((exists s1, removenames t1_1 (l2 ++ x :: x :: l1) = Some s1) \/ removenames t1_1 (l2 ++ x :: x :: l1) = None).
apply some_or_none.
assert ((exists s2, removenames t1_2 (l2 ++ x :: x :: l1) = Some s2) \/ removenames t1_2 (l2 ++ x :: x :: l1) = None).
apply some_or_none.
destruct H0. destruct H0. rewrite H0 in H. destruct H1. destruct H1. rewrite H1 in H.
apply IHt1_1 with (s:=s) in H0. apply IHt1_2 with (s:=s) in H1.
inversion H. simpl. rewrite H0. rewrite H1. reflexivity.
rewrite H1 in H. inversion H. rewrite H0 in H. inversion H. Admitted.

Lemma removenames_non_free: forall t l1 l2 y i1 i2, 
removenames t (l1 ++ l2) = Some i1 -> removenames t (l1 ++ y :: l2) = Some i2 ->
is_free_var y t = false -> shift i1 (Some 2) (length l1) = shift i2 (Some 1) (length l1).

induction t. intros. simpl in H. simpl in H0. 
assert ((exists k, find_index (l1 ++ l2) s = Some k) \/ find_index (l1 ++ l2) s = None). apply some_or_none.
destruct H2. destruct H2. rewrite H2 in H. apply find_index_concat in H2. destruct H2.
assert ((exists k, find_index (l1 ++ y :: l2) s = Some k) \/ find_index (l1 ++ y :: l2) s = None). apply some_or_none.
destruct H3. destruct H3. rewrite H3 in H0. apply find_index_concat in H3. destruct H3. rewrite H3 in H2.
inversion H2. subst. inversion H. inversion H0. simpl. assert (x <? length l1 = true). admit. rewrite H4. reflexivity.
destruct H3. rewrite H3 in H2. inversion H2. admit. destruct H2. destruct H3. destruct H3.
assert ((exists k, find_index (l1 ++ y :: l2) s = Some k) \/ find_index (l1 ++ y :: l2) s = None). apply some_or_none.
destruct H5. destruct H5. rewrite H5 in H0. apply find_index_concat in H5. destruct H5. rewrite H5 in H2. inversion H2.
destruct H5. destruct H6. destruct H6. subst. inversion H. inversion H0.
simpl. simpl in H1. simpl in H6. assert (eq_symbol s y = false). admit. rewrite H4 in H6. rewrite H3 in H6.
inversion H6. admit.
rewrite H5 in H0. inversion H0. rewrite H2 in H. inversion H.
intros. simpl in H. simpl in H0. simpl in H1.

assert (eq_symbol y s = true \/ eq_symbol y s = false). admit.
destruct H2. rewrite H2 in H1. assert (y = s). admit. subst. 
assert ((exists s1, removenames t (s :: l1 ++ l2) = Some s1) \/ removenames t (s :: l1 ++ l2) = None).
apply some_or_none. destruct H3. destruct H3. rewrite H3 in H. assert (s :: l1 ++ l2 = nil ++ s :: l1 ++ l2).
simpl. reflexivity. rewrite H4 in H3. apply removenames_xx with (c:=length l1) in H3.
destruct H3. destruct H3. simpl in H3. rewrite H3 in H0. inversion H. inversion H0. subst.
simpl. admit. simpl. reflexivity. rewrite H3 in H. inversion H. rewrite H2 in H1.
assert ((exists s1, removenames t (s :: l1 ++ l2) = Some s1) \/ removenames t (s :: l1 ++ l2) = None).
apply some_or_none.
assert ((exists s1, removenames t (s :: l1 ++ y :: l2) = Some s1) \/ removenames t (s :: l1 ++ y :: l2) = None).
apply some_or_none.
destruct H3. destruct H3. destruct H4. destruct H4. rewrite H3 in H. rewrite H4 in H0.
inversion H. inversion H0. simpl.
assert (shift x (Some 2) (S (length l1)) = shift x0 (Some 1) (S (length l1))).
apply IHt with (l1:= s :: l1) (l2 := l2) (y:=y). simpl. apply H3. simpl. apply H4. apply H1.
rewrite H5. reflexivity. rewrite H4 in H0. inversion H0. rewrite H3 in H. inversion H.
intros.  simpl in H. simpl in H0. simpl in H1.
assert ((exists s1, removenames t1 (l1 ++ l2) = Some s1) \/ removenames t1 (l1 ++ l2) = None). apply some_or_none.
assert ((exists s2, removenames t2 (l1 ++ l2) = Some s2) \/ removenames t2 (l1 ++ l2) = None). apply some_or_none.
destruct H2. destruct H3. destruct H2. destruct H3. rewrite H2 in H. rewrite H3 in H.
inversion H.
assert ((exists s1, removenames t1 (l1 ++ y :: l2) = Some s1) \/ removenames t1 (l1 ++ y :: l2) = None). apply some_or_none.
assert ((exists s2, removenames t2 (l1 ++ y :: l2) = Some s2) \/ removenames t2 (l1 ++ y :: l2) = None). apply some_or_none.
destruct H4. destruct H4. destruct H6. destruct H6. rewrite H4 in H0. rewrite H6 in H0.
inversion H0. simpl. apply IHt1 with (y:=y) (i2:=x1) in H2. apply IHt2 with (y:=y) (i2:=x2) in H3.
rewrite H2. rewrite H3. reflexivity. apply H6. admit. apply H4. admit. rewrite H6 in H0. rewrite H4 in H0.
inversion H0. rewrite H4 in H0. inversion H0. rewrite H3 in H. destruct H2. rewrite H2 in H. inversion H.
rewrite H2 in H. inversion H. Admitted.





Inductive index_value: index -> Prop :=
  | iv_Abst: forall t1, index_value (IndAbst t1).

Inductive shift_step: index -> index -> Prop :=
  | IEApp1: forall i1 i1' i2, shift_step i1 i1' -> shift_step (IndApp i1 i2) (IndApp i1' i2)
  | IEApp2: forall v1 i2 i2', index_value v1 -> shift_step i2 i2' -> shift_step (IndApp v1 i2) (IndApp v1 i2')
  | IEAppAbs: forall i12 v2 i3, index_value v2 -> i3 = (shift (index_subst 0 (shift v2 (Some 1) 0) i12) None 0) ->
  shift_step (IndApp (IndAbst i12) v2) i3.

Inductive Gamma_index_step: list symbol -> index -> index -> Prop :=
  | GIstep: forall l i1 i2, 
  Gamma l /\ (exists t1, restorenames i1 l = Some t1) /\ (exists t2, restorenames i2 l = Some t2) 
  -> index_step l i1 i2 
  -> Gamma_index_step l i1 i2.

Inductive Gamma_shift_step: list symbol -> index -> index -> Prop :=
  | GSstep: forall l i1 i2,
  Gamma l /\ (exists t1, restorenames i1 l = Some t1) /\ (exists t2, restorenames i2 l = Some t2) 
  -> shift_step i1 i2
  -> Gamma_shift_step l i1 i2.

Theorem index_equals_shift: forall l i1 i2, 
  (Gamma_index_step l i1 i2 -> Gamma_shift_step l i1 i2).

(* intros. split. intros. apply GIstep. inversion H. subst. apply H0. destruct H. destruct H. destruct H1. destruct H1.
destruct H2. generalize dependent l. generalize dependent x. generalize dependent x0.
induction H0. intros. simpl in H1. simpl in H2.
assert ((exists s, restorenames i1 l = Some s) \/ restorenames i1 l = None). apply some_or_none.
assert ((exists s, restorenames i1' l = Some s) \/ restorenames i1' l = None). apply some_or_none.
assert ((exists s, restorenames i2 l = Some s) \/ restorenames i2 l = None). apply some_or_none.
apply TermRev.
destruct H3. destruct H3. destruct H4. destruct H4. destruct H5. destruct H5. rewrite H3 in H1. rewrite H4 in H2. 
rewrite H5 in H1. rewrite H5 in H2. assert (Gamma l). apply H. apply IHshift_step with (x0:=x2) (x := x1) in H.
inversion H. subst. destruct H7. destruct H7. destruct H7. destruct H8. exists (App x4 x3).
exists (App x5 x3). split. simpl. rewrite H7. apply thm6_1_5 in H5. rewrite H5. reflexivity. apply H6. 
split. simpl. rewrite H8. apply thm6_1_5 in H5. rewrite H5. reflexivity. apply H6.
apply EApp1. apply H9. apply H3. apply H4. rewrite H3 in H1. rewrite H5 in H1. inversion H1.
rewrite H4 in H2. inversion H2. rewrite H3 in H1. inversion H1.

intros. simpl in H2. simpl in H3.
assert ((exists s, restorenames v1 l = Some s) \/ restorenames v1 l = None). apply some_or_none.
assert ((exists s, restorenames i2 l = Some s) \/ restorenames i2 l = None). apply some_or_none.
assert ((exists s, restorenames i2' l = Some s) \/ restorenames i2' l = None). apply some_or_none.
destruct H4. destruct H4. destruct H5. destruct H5. destruct H6. destruct H6. rewrite H4 in H2.
rewrite H4 in H3. rewrite H5 in H2. rewrite H6 in H3. assert (Gamma l). apply H1. apply IHshift_step with (x0 := x3) (x:=x2) in H1.
apply TermRev. inversion H2. inversion H3. subst. inversion H1. destruct H8. destruct H8.
destruct H8. destruct H12. subst. exists (App x1 x). exists (App x1 x0).
split. simpl. apply thm6_1_5 in H4. rewrite H4. rewrite H8. reflexivity. apply H7.
split. simpl. apply thm6_1_5 in H4. rewrite H4. rewrite H12. reflexivity. apply H7.
apply EApp2. destruct H. simpl in H4.
assert (exists x, (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end) = x).
exists (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end). reflexivity.
destruct H. rewrite H in H4. 
assert ((exists s, (restorenames t1 (x4 :: l)) = Some s) \/ (restorenames t1 (x4 :: l)) = None).
apply some_or_none. destruct H9. destruct H9. rewrite H9 in H4. inversion H4. apply v_Abst.
rewrite H9 in H4. inversion H4. apply H13. apply H5. apply H6. rewrite H4 in H3. rewrite H6 in H3. inversion H3.
rewrite H4 in H2. rewrite H5 in H2. inversion H2. rewrite H4 in H3. inversion H3.

intros. apply TermRev. exists x. exists x0. split. apply thm6_1_5 in H1. apply H1.
apply H0. split. apply thm6_1_5 in H2. apply H2. apply H0. 
simpl in H1.
assert (exists v, (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end) = v).
exists (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end).
reflexivity. destruct H3. rewrite H3 in H1.
assert ((exists s, restorenames i12 (x1 :: l) = Some s) \/ restorenames i12 (x1 :: l) = None).
apply some_or_none. destruct H4. destruct H4. rewrite H4 in H1.
assert ((exists s, restorenames v2 l = Some s) \/ restorenames v2 l = None).
apply some_or_none. destruct H5. destruct H5. rewrite H5 in H1. inversion H1. apply EAppAbs.
inversion H. subst. simpl in H5.
assert (exists v, (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end) = v).
exists (match l with | nil => Symb 0 | s :: _ => match s with | Symb k => Symb (S k) end end).
reflexivity. destruct H3. rewrite H3 in H5.
assert ((exists s, restorenames t1 (x :: l) = Some s) \/ restorenames t1 (x :: l) = None).
apply some_or_none. destruct H6. destruct H6. rewrite H6 in H5. inversion H5. apply v_Abst.
rewrite H6 in H5. inversion H5.
admit. (* Hard. 示すのはことはできると思うが… (\lambda \lambda 1 0) (\lambda 0)とか。簡約形を単純に
restorenamesしても、term_stepは成立しない。実際片方だけ示せば良い。 *)
rewrite H5 in H1. inversion H1. rewrite H4 in H1. inversion H1.
 *)

intros. destruct H. apply GSstep. apply H. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
generalize dependent i1. generalize dependent i2. generalize dependent l. induction H2.
intros. simpl in H1. simpl in H0.
assert ((exists s, removenames t1 l = Some s) \/ removenames t1 l = None). apply some_or_none.
assert ((exists s, removenames t1' l = Some s) \/ removenames t1' l = None). apply some_or_none.
assert ((exists s, removenames t2 l = Some s) \/ removenames t2 l = None). apply some_or_none.
destruct H3. destruct H3. destruct H4. destruct H4. destruct H5. destruct H5.
rewrite H3 in H0. rewrite H5 in H0. rewrite H4 in H1. rewrite H5 in H1. apply IHterm_step with (i1:=x) in H4.
 inversion H0. inversion H1. apply IEApp1. apply H4. destruct H. split. apply H. destruct H6.
destruct H6. destruct H7. inversion H0. inversion H1. subst. simpl in H6. simpl in H7.
assert ((exists s, restorenames x l = Some s) \/ restorenames x l = None). apply some_or_none.
assert ((exists s, restorenames x0 l = Some s) \/ restorenames x0 l = None). apply some_or_none.
destruct H8. destruct H9. split. apply H8. apply H9. rewrite H9 in H7. inversion H7.
rewrite H8 in H6. inversion H6. apply H3. rewrite H3 in H0. rewrite H5 in H0. inversion H0.
 rewrite H4 in H1. inversion H1. rewrite H3 in H0. inversion H0.

intros. destruct H0. destruct H4. destruct H4. destruct H5. simpl in H1. simpl in H3.
assert ((exists s, removenames v1 l = Some s) \/ removenames v1 l = None). apply some_or_none.
assert ((exists s, removenames t2 l = Some s) \/ removenames t2 l = None). apply some_or_none.
assert ((exists s, removenames t2' l = Some s) \/ removenames t2' l = None). apply some_or_none.
destruct H6. destruct H6. destruct H7. destruct H7. destruct H8. destruct H8. 
rewrite H6 in H3. rewrite H7 in H3. rewrite H6 in H1. rewrite H8 in H1. inversion H1.
inversion H3. subst. simpl in H4. simpl in H5.
assert ((exists s, restorenames x1 l = Some s) \/ restorenames x1 l = None). apply some_or_none.
assert ((exists s, restorenames x2 l = Some s) \/ restorenames x2 l = None). apply some_or_none.
assert ((exists s, restorenames x3 l = Some s) \/ restorenames x3 l = None). apply some_or_none.
destruct H9. destruct H9. destruct H10. destruct H10. destruct H11. destruct H11.
assert (shift_step x2 x3). apply IHterm_step with l. apply H8. split. apply H0. split.
exists x5. apply H10. exists x6. apply H11. apply H7. apply IEApp2. inversion H. subst.
simpl in H6. assert ((exists s, (removenames t1 (x7 :: l)) = Some s) \/ (removenames t1 (x7 :: l)) = None).
apply some_or_none. destruct H13. destruct H13. rewrite H13 in H6. inversion H6. apply iv_Abst.
rewrite H13 in H6. inversion H6. apply H12. rewrite H9 in H5. rewrite H11 in H5. inversion H5.
rewrite H9 in H4. rewrite H10 in H4. inversion H4. rewrite H9 in H5. inversion H5. rewrite H6 in H1.
rewrite H8 in H1. inversion H1. rewrite H6 in H3. rewrite H7 in H3. inversion H3. rewrite H6 in H1.
inversion H1.



intros.
generalize dependent x. generalize dependent i1. generalize dependent v2. generalize dependent s.
generalize dependent l. generalize dependent i2.
induction t12. intros. 
simpl in H0. assert (eq_symbol x s = true \/ eq_symbol x s = false). admit.
destruct H4. rewrite H4 in H0. inversion H0. rewrite H6 in H3. 
assert (x = s). admit. rewrite H5 in H3. simpl in  H3. subst. 
rewrite H4 in H3. rewrite H1 in H3. inversion H3.
simpl in H3. apply IEAppAbs. admit. simpl. assert (shift (shift i2 (Some 1) 0) None 0 = i2).
apply shift_inversion. rewrite H5. reflexivity.
rewrite H4 in H0. inversion H0. simpl in H3. assert (eq_symbol s x = false). admit.
rewrite H5 in H3. assert ((exists k, find_index l s = Some k) \/ find_index l s = None). apply some_or_none.
destruct H7. destruct H7. rewrite H7 in H3. assert ((exists s, removenames v2 l = Some s) \/ removenames v2 l = None).
apply some_or_none. destruct H8. destruct H8. rewrite H8 in H3. inversion H3. apply IEAppAbs.
admit. simpl. assert (s0 = Var s). rewrite H6. reflexivity. rewrite H9 in H1.
simpl in H1. rewrite H7 in H1. inversion H1. reflexivity. rewrite H8 in H3. inversion H3. rewrite H7 in H3.
inversion H3.

intros. simpl in H0. assert (eq_symbol x s = true \/ eq_symbol x s = false). admit.
destruct H4. rewrite H4 in H0. inversion H0. subst. simpl in H1. simpl in H3.
assert (x = s). admit. subst.
assert ((exists i, removenames t12 (s :: l) = Some i) \/ removenames t12 (s :: l) = None). apply some_or_none.
assert ((exists i, removenames t12 (s :: s :: l) = Some i) \/ removenames t12 (s :: s :: l) = None). apply some_or_none.
destruct H5. destruct H5. destruct H6. destruct H6. rewrite H5 in H1. rewrite H6 in H3.
assert ((exists i, removenames v2 l = Some i) \/ removenames v2 l = None). apply some_or_none.
destruct H7. destruct H7. rewrite H7 in H3. inversion H3. inversion H1.
apply IEAppAbs. inversion H. subst. simpl in H7. 
assert ((exists i, removenames t1 (x2 :: l) = Some i) \/ removenames t1 (x2 :: l) = None). apply some_or_none.
destruct H8. destruct H8. rewrite H8 in H7. inversion H7. apply iv_Abst. rewrite H8 in H7. inversion H7.
simpl. assert (shift (shift x (Some 1) 1) None 1 = x). apply shift_inversion.
assert (x = shift (shift x (Some 1) 1) None 1). rewrite H8. reflexivity. rewrite H11.
assert (index_subst 1 (shift (shift x1 (Some 1) 0) (Some 1) 0) x0 = x0).
assert (s :: s :: l = nil ++ s :: s :: l). simpl. reflexivity. rewrite H12 in H6.
apply subst_removenames_xx with (s:=(shift (shift x1 (Some 1) 0) (Some 1) 0)) in H6.
simpl in H6. apply H6. rewrite H12. assert (shift x (Some 1) 1 = x0).
assert (s :: l = nil ++ (s :: nil) ++ l). simpl. reflexivity. rewrite H13 in H5.
apply removenames_xx with (c:=0) in H5. destruct H5. destruct H5. simpl in H5. rewrite H6 in H5.
inversion H5. rewrite H14. reflexivity. simpl. reflexivity. rewrite H13. reflexivity.
rewrite H7 in H3. inversion H3. rewrite H6 in H3. inversion H3. rewrite H5 in H1. inversion H1.
admit. (* hard*)

intros. simpl in H0.
assert ((exists s, subst x v2 t12_1 = Some s) \/ subst x v2 t12_1 = None). apply some_or_none.
assert ((exists s, subst x v2 t12_2 = Some s) \/ subst x v2 t12_2 = None). apply some_or_none.
destruct H4. destruct H4. destruct H5. destruct H5.
rewrite H4 in H0. rewrite H5 in H0. inversion H0. subst. simpl in H1.
assert ((exists i, removenames x0 l = Some i) \/ removenames x0 l = None). apply some_or_none.
assert ((exists i, removenames x1 l = Some i) \/ removenames x1 l = None). apply some_or_none.
destruct H6. destruct H6. destruct H7. destruct H7. rewrite H6 in H1. rewrite H7 in H1. 
inversion H1. simpl in H3.
assert ((exists i, removenames t12_1 (x :: l) = Some i) \/ removenames t12_1 (x :: l) = None). apply some_or_none.
assert ((exists i, removenames t12_2 (x :: l) = Some i) \/ removenames t12_2 (x :: l) = None). apply some_or_none.
destruct H8. destruct H8. destruct H10. destruct H10. rewrite H8 in H3. rewrite H10 in H3.
assert ((exists i, removenames v2 l = Some i) \/ removenames v2 l = None). apply some_or_none.
destruct H11. destruct H11. rewrite H11 in H3. inversion H3. apply IEAppAbs.
inversion H. subst. simpl in H11. 
assert ((exists i, removenames t1 (x7 :: l) = Some i) \/ removenames t1 (x7 :: l) = None). apply some_or_none.
destruct H9. destruct H9. rewrite H9 in H11. inversion H11. apply iv_Abst. rewrite H9 in H11. inversion H11.
simpl. assert (shift_step (IndApp (IndAbst x4) x6) x2). apply IHt12_1 with (l:=l) (s:=x0) (x:=x) (v2:=v2).
apply H6. apply H. admit. apply H4. simpl. rewrite H8. rewrite H11. reflexivity.
assert (shift_step (IndApp (IndAbst x5) x6) x3). apply IHt12_2 with (l:=l) (s:=x1) (x:=x) (v2:=v2).
apply H7. apply H. admit. apply H5. simpl. rewrite H10. rewrite H11. reflexivity.


simpl in H9.


admit. 


Fixpoint max_symbol_impl (t: term): nat :=
    match t with
    | Var (Symb v) => v
    | Abst (Symb v) t => max v (max_symbol_impl t)
    | App t1 t2 => max (max_symbol_impl t1) (max_symbol_impl t2)
    end.

Definition max_symbol (t:term): symbol := Symb (max_symbol_impl t).

(* [x \mapsto s] t. If it need alpha trans, return None*)