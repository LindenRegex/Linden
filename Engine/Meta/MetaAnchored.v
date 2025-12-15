(** * Meta anchored *)

(* Sometimes we know a regex will match only if it is executed at the start of the input. *)
(* In those cases the result of an anchored /r/ regex is the same as of the /.*?r/ regex. *)
(* This allows us to not run a full unanchored search, but just perform an anchored search *)
(* once at the very beginning. *)

Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree.
From Linden Require Import FunctionalUtils.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix Prefix.
From Linden Require Import EngineSpec.
From Linden Require Import Tactics.
From Warblre Require Import Base RegExpRecord.


Section MetaLiterals.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* a regex is anchored if the BeginInput anchor (^) needs to be satisfied *)
(* in order to match the regex r *)
Fixpoint is_anchored' (r:regex) : bool :=
	match r with
	| Anchor BeginInput => true
	| Disjunction r1 r2 => is_anchored' r1 && is_anchored' r2
	| Sequence r1 r2 => is_anchored' r1 || is_anchored' r2
	| Group _ r1 => is_anchored' r1
	| Quantified _ min _ r1 => (min != 0) && is_anchored' r1
	| Anchor _ | Lookaround _ _ | Epsilon | Regex.Character _ | Backreference _ => false
	end.

(* if the multiline flag is set, the regex is not considered anchored *)
Definition is_anchored (r:regex) : bool :=
	if RegExpRecord.multiline rer then false
	else is_anchored' r.

(* performs an anchored search at the start position if the regex is anchored *)
Definition try_anchored_search {engine:AnchoredEngine rer} (r:regex) (inp:input) : option (option leaf) :=
	if is_anchored r then
		if pref_str inp == [] then
			Some (exec rer r inp)
		else
			Some None
	else None.


(* generalization of being anchored into actions *)
Definition is_anchored_act (act:action) : bool :=
	match act with
	| Areg r => is_anchored' r
	| Acheck _ => false
	| Aclose _ => false
	end.

(* a list of actions is anchored if any of the actions are anchored *)
Fixpoint is_anchored_acts (acts:list action) : bool :=
	match acts with
	| [] => false
	| a :: rest => is_anchored_act a || is_anchored_acts rest
	end.

Lemma read_backref_not_begin:
	forall gm gid next c pref br_str nextinp,
		read_backref rer gm gid (Input next (c::pref)) forward = Some (br_str, nextinp) ->
		exists next' c' pref', nextinp = Input next' (c'::pref').
Proof.
	intros gm gid next c pref br_str nextinp Hread.
	rewrite read_backref_success_advance with (1:=Hread).
	destruct (length br_str).
	- simpl; eauto.
	- destruct next; simpl; eauto.
		destruct (rev (firstn n next)); simpl; eauto.
Qed.

(* for any anchored actions, the tree over those actions with an input that is *)
(* not at the start contains no results *)
Lemma is_anchored_match_not_begin:
	forall acts c next pref tree gm,
		RegExpRecord.multiline rer = false ->
		is_anchored_acts acts = true ->
		is_tree rer acts (Input next (c::pref)) gm forward tree ->
		tree_res tree Groups.GroupMap.empty (Input next (c::pref)) forward = None.
Proof.
	intros acts c next pref tree gm Hmulti Hanch Htree.
	remember (Input next (c::pref)) as inp.
	remember forward as dir.
	generalize dependent next. generalize dependent pref. generalize dependent c.
	induction Htree; intros ? pref next ?; simpl in *; subst;
		(* remove cases that are not anchored *)
		try easy;
		(* result is from the IH *)
		try solve[eapply res_group_map_indep; eauto].
	(* tree_char *)
	- unfold read_char in READ. destruct next; [discriminate|]. destruct char_match; [|discriminate].
		injection READ as <-.
		eapply res_group_map_indep; eauto.
	(* tree_disj*)
	-	boolprop; erewrite IHHtree1; eauto.
	(* tree_sequence *)
	- simpl in IHHtree. boolprop; eauto.
	(* tree_quant_forced *)
	- boolprop; eapply res_group_map_indep; eauto.
	(* tree_quant_free *)
	- boolprop.
		destruct greedy; simpl; erewrite IHHtree2; eauto.
		+	erewrite res_group_map_indep; eauto.
		+	erewrite res_group_map_indep; eauto.
	(* tree_lk *)
	- destruct positivity, (tree_res treelk); eauto.
		destruct l.
		eapply res_group_map_indep; eauto.
	(* tree_anchor *)
	- boolprop; eauto.
		unfold anchor_satisfied in ANCHOR. rewrite Hmulti in ANCHOR.
		now destruct a.
	(* tree_backref *)
	- pose proof (read_backref_not_begin _ _ _ _ _ _ _ READ_BACKREF) as [? [? [? ?]]].
		eapply res_group_map_indep; eauto.
Qed.

(* is_anchored_match_not_begin specialized to a single anchored regex *)
Lemma is_anchored_match_not_begin_regex:
	forall r c next pref tree,
		is_anchored r = true ->
		is_tree rer [Areg r] (Input next (c::pref)) Groups.GroupMap.empty forward tree ->
		first_leaf tree (Input next (c :: pref)) = None.
Proof.
	unfold is_anchored.
	intros r c next pref tree Hanch Htree.
	destruct RegExpRecord.multiline eqn:Hmulti; [discriminate|].
	assert (is_anchored_acts [Areg r] = true) by (simpl; now rewrite Hanch).
	eapply is_anchored_match_not_begin; eauto.
Qed.

(* for an anchored regex r, the result of a tree of r is the same as the result of the tree .*?r *)
Lemma anchored_regex_match:
	forall r inp tree1 tree2,
		is_anchored r = true ->
		is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree1 ->
		is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree2 ->
		first_leaf tree1 inp = first_leaf tree2 inp.
Proof.
	intros r inp tree1 tree2 Hanch Htree1 Htree2.
	inversion Htree2. inversion CONT. destruct plus; [discriminate|].
	replace tskip with tree1 in * by eauto using is_tree_determ.
	inversion ISTREE1; subst; unfold first_leaf; simpl.
	- unfold read_char in READ. destruct inp, next as [|c' next]; [discriminate|]. inversion READ.
		unfold advance_input'. subst. simpl.
		replace (tree_res tcont Groups.GroupMap.empty (Input next (c::pref)) forward) with (None : option leaf).
		now destruct (tree_res tree1).
		unfold is_anchored in Hanch. destruct RegExpRecord.multiline eqn:Hmulti; [discriminate|].
		symmetry. eapply is_anchored_match_not_begin; eauto.
		simpl. now rewrite Hanch.
	- now destruct tree_res.
Qed.


(* the anchored_search correctly finds unanchored results for anchored regexes *)
Theorem try_anchored_search_correct {engine:AnchoredEngine rer}:
	forall r inp leaf tree,
		supported_regex rer r = true ->
		is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree ->
		try_anchored_search r inp = Some leaf ->
		first_leaf tree inp = leaf.
Proof.
	intros r inp leaf tree Hsup Htree Hanch.
	unfold try_anchored_search in Hanch.
	destruct (is_anchored r) eqn:Hisanch; [|discriminate].
	eqdec; injection Hanch as <-.
	(* we are at the start of the input *)
	- inversion Htree. inversion CONT.
		symmetry. rewrite <-exec_correct with (tree:=tskip); eauto using anchored_regex_match.
	(* we are not at the start, there is no match *)
	- destruct inp, pref as [|c' pref]; [easy|].
		inversion Htree. inversion CONT.
		erewrite <-anchored_regex_match with (tree1:=tskip); eauto using is_anchored_match_not_begin_regex.
Qed.

End MetaLiterals.
