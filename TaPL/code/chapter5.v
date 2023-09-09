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

(* Gammaを 0 :: 1 :: ... :: n - 1 :: nil とする。これを l' = l ++ Gamma
で表現する。つまり本でのremovenames t l'はここではremovenames t l nに相当する*)
Fixpoint symbol_find (l: list symbol) (v: nat) (n: nat): option nat :=
  match l with
  | nil => if v <? n then Some v else None 
  | t :: l => if eq_symbol (Symb v) t then Some 0 else 
    (match symbol_find l v n with
      | None => None
      | Some w => Some (S w)
    end)
  end.

Fixpoint removenames (t:term) (l: list symbol) (n:nat) : option index :=
  match t with
  | Var (Symb v) => 
    (match symbol_find l v n with 
      | None => None
      | Some x => Some (IndVar x)
    end)
  | Abst x t => 
    (match removenames t (x :: l) n with
      | None => None 
      | Some s => Some (IndAbst s)
    end)
  | App t1 t2 => 
    (match removenames t1 l n, removenames t2 l n with
      | None, _ => None
      | _, None => None
      | Some s1, Some s2 => Some (IndApp s1 s2)
    end)
  end.

(* removenamesと同様。ただlはlistのlengthさえ分かればよい。*)
Fixpoint restorenames (i:index) (l: nat) (n: nat) : option term :=
  match i with
  (* v - l < nでなければならない*)
  | IndVar v => if v <? l then Some (Var (Symb (v + n))) else 
    (if v - l <? n then Some (Var (Symb (v - l))) else None)
  | IndAbst i1 => 
    (match restorenames i1 (S l) n with 
      | None => None
      | Some s => Some (Abst (Symb (n + l)) s)
    end)
  | IndApp i1 i2 => 
    (match restorenames i1 l n, restorenames i2 l n with
      | None, _ => None
      | _, None => None
      | Some s1, Some s2 => Some (App s1 s2)
    end)
  end.

Inductive natsymb: nat -> list symbol -> Prop :=
  | NSInit: natsymb 0 nil
  | NSStep: forall n l, natsymb n l -> natsymb (S n) (Symb n :: l).

Inductive abst_term_depth: term -> nat -> Prop :=
  | ATDVar: forall x, abst_term_depth (Var x) 0
  | ATDAbst: forall x t1 n, abst_term_depth t1 n -> abst_term_depth (Abst x t1) (S n)
  | ATDApp: forall t1 t2 n1 n2, abst_term_depth t1 n1 -> abst_term_depth t2 n2
  -> abst_term_depth (App t1 t2) (max n1 n2).

Lemma some_or_none: forall A, forall t: option A, (exists s, t = Some s) \/ t = None.
intros. destruct t. left. exists a. reflexivity. right. reflexivity. Qed.


Theorem thm6_1_5: forall i n l n' t, length l = n -> restorenames i n n' = Some t ->
removenames t l n' = Some i.
intros. generalize dependent n. generalize dependent n'. generalize dependent l. generalize dependent t. 
induction i.
intros. inversion H0. assert (forall b, b = true \/  b = false). intros. destruct b.
left. reflexivity. right. reflexivity. assert (n <? n0 = true \/ n <? n0 = false).
apply H1. destruct H3. rewrite H3 in H2. inversion H2. simpl. assert (symbol_find l (n + n') n' = Some n).
admit. rewrite H4. reflexivity. rewrite H3 in H2. assert (n - n0 <? n' = true \/ n - n0 <? n' = false).
apply H1. destruct H4. rewrite H4 in H2. inversion H2. simpl. assert (symbol_find l (n - n0) n' = Some n). 
admit. rewrite H5. reflexivity. rewrite H4 in H2. inversion H2.
intros. inversion H0.
assert ((exists s, restorenames i (S n) n' = Some s) \/ restorenames i (S n) n' = None). apply some_or_none.
destruct H1. destruct H1. rewrite H1 in H2. inversion H2. simpl.
assert (removenames x (Symb (n' + n) :: l) n' = Some i). apply IHi with (n:= (S n)).
simpl. subst. reflexivity. apply H1. rewrite H3. reflexivity. rewrite H1 in H2. inversion H2. 
intros. inversion H0. assert ((exists s1, restorenames i1 n n' = Some s1) \/ restorenames i1 n n' = None).
apply some_or_none. assert ((exists s1, restorenames i2 n n' = Some s1) \/ restorenames i2 n n' = None).
apply some_or_none. destruct H1. destruct H1. destruct H3. destruct H3. rewrite H1 in H2.
rewrite H3 in H2. inversion H2. simpl. assert (removenames x l n' = Some i1). apply IHi1 with (n:=n).
apply H. apply H1. assert (removenames x0 l n' = Some i2). apply IHi2 with (n:=n). apply H.
apply H3. rewrite H4. rewrite H6. reflexivity. rewrite H1 in H2. rewrite H3 in H2. inversion H2.
rewrite H1 in H2. inversion H2. Admitted.


unfold restorenames. unfold removenames. simpl. assert (n - 0 = n). destruct n.
reflexivity. simpl. reflexivity. rewrite H0. reflexivity. simpl in H. inversion H.
simpl in H. assert (forall n1 n2, 0 = max n1 n2 -> 0 = n1 /\ 0 = n2).
intros. destruct n1. split. reflexivity. simpl in H0. apply H0.
destruct n2. simpl in H0. inversion H0. simpl in H0. inversion H0.
apply H0 in H. destruct H. apply IHi1 in H. apply IHi2 in H1. unfold restorenames. unfold removenames.
simpl. unfold restorenames in H. unfold removenames in H. unfold restorenames in H1. unfold removenames in H1.
rewrite H. rewrite H1. reflexivity. 
intros. induction i.
simpl in H0. inversion H0. inversion H0.
unfold restorenames. unfold removenames. simpl.
intros. induction i. unfold restorenames. simpl. unfold removenames.
simpl. assert (n - 0 = n). induction n. simpl. reflexivity. simpl. reflexivity. rewrite H.
reflexivity. unfold restorenames. simpl.
unfold removenames. simpl. induction i. admit. simpl. admit. unfold restorenames. simpl. unfold removenames.
simpl. unfold restorenames in IHi1. unfold removenames in IHi1. 
unfold restorenames in IHi2. unfold removenames in IHi2. rewrite IHi1. rewrite IHi2.
reflexivity. Admitted.

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

Inductive index_step: index -> index -> Prop :=
  | TermRev: forall i1 i2, (exists t1 t2, (removenames t1 nil) = i1 /\ (removenames t2 nil) = i2 /\ term_step t1 t2) 
  -> index_step i1 i2.

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

Inductive index_value: index -> Prop :=
  | iv_Abst: forall t1, index_value (IndAbst t1).

Inductive shift_step: index -> index -> Prop :=
  | IEApp1: forall i1 i1' i2, shift_step i1 i1' -> shift_step (IndApp i1 i2) (IndApp i1' i2)
  | IEApp2: forall v1 i2 i2', index_value v1 -> shift_step i2 i2' -> shift_step (IndApp v1 i2) (IndApp v1 i2')
  | IEAppAbs: forall i12 v2, index_value v2 -> 
  shift_step (IndApp (IndAbst i12) v2) (shift (index_subst 0 (shift v2 (Some 1) 0) i12) None 0).

Theorem index_equals_shift: forall i1 i2, shift_step i1 i2 <-> index_step i1 i2.
intros. split. intros. apply TermRev. induction H.  destruct IHshift_step. destruct H0.
destruct H0. destruct H1.
admit. admit. destruct H. generalize dependent t1. induction i12. intros. admit.
intros. admit. admit. intros. destruct H. destruct H. destruct H.  destruct H.
destruct H0. subst. induction H1. simpl. apply IEApp1. apply IHterm_step.
simpl. apply IEApp2. destruct H. simpl. apply iv_Abst. apply IHterm_step.
simpl. apply IEAppAbs. 

Fixpoint max_symbol_impl (t: term): nat :=
    match t with
    | Var (Symb v) => v
    | Abst (Symb v) t => max v (max_symbol_impl t)
    | App t1 t2 => max (max_symbol_impl t1) (max_symbol_impl t2)
    end.

Definition max_symbol (t:term): symbol := Symb (max_symbol_impl t).

(* [x \mapsto s] t. If it need alpha trans, return None*)