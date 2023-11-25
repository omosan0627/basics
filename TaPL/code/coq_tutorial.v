(* 場合分けを簡単にしたい。Some vs Noneとかtrue vs falseとか*)
(* 演算子を導入して読みやすくしたい。*)
(* assertを使っている部分をなくしたい。*)
(* 補題を新たに示さないといけないと分かったときに戻らないといけないのをやめたい。*)
(* 使えそうな補題を検索する方法を知りたい *)
(* Constructors: 適用可能なconstructorを1番からapplyしていく。 *)
(* refine: exactでplaceholder使える *)
(* replace: assert (a = b) as H. rewrite Hを一気にやる。便利すぎ *)
(* rewrite _ , _: 複数一気に書き換え *)
(* lia:つよい*)
(* elim: inductionの方法らしいが…何か古いみたいで推奨されていないと書いてあった*)
(* destruct _ as [|]: rememberと使うと強力。[]内で変数名も決められる。*)
(* -? + ?*)
(* remember?:変数を追加できる*)
(* discriminate?: *)
(* symmetry: 両辺入れ替え*)
(* constructor?*)
(* search: 検索*)
(* repeat*)
(* injection *)
(* apply (H (term)): Hにtermを適用する。H (term)を適用した先も->の形で関数なら更に適用OK*)
(* intros ? ? :?の数だけintrosするってこと*)
(* Ltac coqの証明のタクティクスをまとめて適用してくれるもの*)
(* 高階述語論理? 1階との差?*)
(* 41Semicolonさんのテクニックをとりあえず盗もう。*)
(* coqのdocumentationとかgitの使い方?*)
(* つまり型環境が前提で、->が関数の形です。forallが全称型、existsが依存型となっている*)
Definition true_or_false b: {b = true} + {b = false}.
pose (omo := {b = true} + {b = false}). (* 足すだけ *)
set (foo := {b = true} + {b = false}).  (* 置き換えもする*) unfold foo.
destruct b. left. reflexivity. right. reflexivity. Qed.

(* pose proof -> 関数適用して前提に加えてくれる。*)
Definition thm_succ: forall n m, n + m = m + n.
induction n. intros. simpl. apply plus_n_O.
intros. pose proof (IHn (S m)). simpl in H. simpl. symmetry. admit. Admitted.

(* if文はとりあえずrememberしとくと良い*)
(* なるべく 変数=計算の順番で書いとくと楽*)

