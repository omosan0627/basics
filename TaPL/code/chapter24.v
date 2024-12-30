Theorem exist_all_second: forall T: Prop -> Prop, 
((exists X, T X) <-> (forall Y: Prop, (forall X, T X -> Y) -> Y)).
intros. split.
- intros. destruct H. now apply H0 in H.
- intros. apply H. intros. now exists X. Qed. 

(* たぶんだけど依存型入れるとまた状況が変わる?
Existential second order = universal second orderだったらNP=co-NP問題
が発生しないので *)