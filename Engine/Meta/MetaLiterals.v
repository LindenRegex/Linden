(** * Meta literals *)

(* Different optimizations related to doing literal-based searches and acceleration. *)

Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree.
From Linden Require Import FunctionalUtils.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix Prefix.
From Linden Require Import EngineSpec.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import Tactics.


Section MetaLiterals.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* whether a regex has capturing groups *)
Fixpoint has_groups (r:regex) : bool :=
  match r with
  | Group _ _ => true
  | Sequence r1 r2 | Disjunction r1 r2 => has_groups r1 || has_groups r2
  | Quantified _ _ _ r' | Lookaround _ r' => has_groups r'
  | Regex.Character _ | Epsilon | Backreference _ | Anchor _ => false
  end.

(* tries to perform a search using only the literal from the regex *)
(* On success, returns Some leaf. On failure, returns the None. *)
Definition try_lit_search {strs:StrSearch} (r:regex) (inp:input) : option (option leaf) :=
  match extract_literal rer r with
  | Prefix s => None
  | Impossible => Some None
  | Exact s =>
  		(* if it has asserts doing a string search is not enough *)
      if has_asserts r then None
      else
        match input_search s inp with
        | Some inp' =>
            (* if it has groups we must reconstruct them *)
            (* LATER: do group reconstruction with an anchored engine *)
            if has_groups r then None
            else Some (Some (advance_input_n inp' (length s) forward, Groups.GroupMap.empty))
        | None => Some None
        end
  end.

Definition has_groups_action (a:action) : bool :=
  match a with
  | Areg r => has_groups r
  | Acheck _ => false
  | Aclose _ => true
  end.

Fixpoint has_groups_actions (acts:list action) : bool :=
  match acts with
  | [] => false
  | a::t => has_groups_action a || has_groups_actions t
  end.

(* if a regex has no groups, then it defines no groups *)
Lemma has_no_groups_def_groups:
  forall r,
    has_groups r = false -> def_groups r = [].
Proof.
  induction r; eauto; try easy.
  - simpl; intros H; boolprop.
    now rewrite (IHr1 H), (IHr2 H0).
  - simpl; intros H; boolprop.
    now rewrite (IHr1 H), (IHr2 H0).
Qed.

(* if a list of actions contains no groups, any matching leaf produces an empty group map *)
Lemma no_groups_empty_gm:
  forall acts inp dir tree leaf,
    has_groups_actions acts = false ->
    is_tree rer acts inp Groups.GroupMap.empty dir tree ->
    tree_res tree Groups.GroupMap.empty inp dir = Some leaf ->
    snd leaf = Groups.GroupMap.empty.
Proof.
  intros acts inp dir tree leaf Hnogroups Htree Hleaf.
  remember Groups.GroupMap.empty as gm.
  generalize dependent leaf.
  induction Htree; intros leaf Hleaf;
    (* simplify *)
    subst; simpl in *; boolprop;
    (* remove cases with groups *)
    try discriminate;
    (* remove trivial cases *)
    inversion Hleaf; eauto.
  - eapply read_char_success_advance, advance_input_success in READ as <-.
    eauto.
  - destruct (tree_res t1), (tree_res t2); eauto.
  - destruct dir; simpl in IHHtree; boolprop; eapply IHHtree; eauto.
  - rewrite has_no_groups_def_groups in *; eauto.
  - destruct greedy; simpl in Hleaf; rewrite has_no_groups_def_groups in *; eauto.
    + destruct (tree_res titer); eauto.
    + destruct (tree_res tskip); eauto.
  - unfold lk_result in RES_LK. destruct positivity.
    + destruct (tree_res treelk) eqn:Hres; [destruct l|discriminate].
      injection RES_LK as <-.
      repeat specialize_prove IHHtree1 by eauto. specialize (IHHtree1 (i, g) ltac:(eauto)).
      simpl in IHHtree1. subst. eauto.
    + destruct (tree_res treelk); [discriminate|inversion RES_LK; subst; eauto].
  - rewrite <-read_backref_success_advance with (1:=READ_BACKREF) in Hleaf; eauto.
Qed.


(* if the try_lit_search returned a leaf, it is the first_leaf *)
Theorem try_lit_search_correct {strs:StrSearch}:
	forall r inp tree ol,
		is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree ->
		try_lit_search r inp = Some ol ->
		first_leaf tree inp = ol.
Proof.
	unfold try_lit_search.
	intros r inp tree ol Htree Htry.
  destruct extract_literal eqn:Heq.
  (* Exact *)
  - destruct has_asserts eqn:Hasserts; [discriminate|].
    destruct input_search eqn:Hsearch.
    (* we found a match *)
    + destruct has_groups eqn:Hgroups; [discriminate|].
      injection Htry as <-.
      eapply no_asserts_exact_literal in Hsearch as [gm' Hleaf]; eauto.
      eapply no_groups_empty_gm in Htree; simpl; boolprop; eauto. simpl in Htree. subst.
      now rewrite Hleaf.
    (* we did not find a match *)
    + injection Htry as <-.
      rewrite input_search_none_str_search in Hsearch.
      eapply str_search_none_nores_unanchored; eauto.
      now rewrite Heq.
  (* Prefix *)
  - discriminate.
  (* Impossible *)
  - injection Htry as <-.
    assert (extract_literal rer (lazy_prefix r) = Impossible). {
      assert (Hic: RegExpRecord.ignoreCase rer = false). {
        unfold extract_literal in Heq.
        destruct RegExpRecord.ignoreCase eqn:Hicm, r; easy.
      }
      simpl. now rewrite Hic, Heq.
    }
    eapply extract_literal_impossible; eauto.
Qed.

(* unanchored search where we first perform a single prefix acceleration *)
Definition search_acc_once {strs:StrSearch} {engine:UnanchoredEngine rer} (r:regex) (inp:input) : option leaf :=
  let p := prefix (extract_literal rer r) in
  (* we skip the initial input that does not match the prefix *)
  match (input_search p inp) with
  | None => None (* if prefix is not present anywhere, then we cannot match *)
  | Some inp' => un_exec rer r inp'
  end.

(* the result of unanchored matching is the same for all inputs between inp *)
(* and the next occurrence of the prefix after inp *)
Lemma un_exec_all_between_str_search_eq {strs:StrSearch} {engine:UnanchoredEngine rer}:
  forall i r inp inp',
    un_supported_regex rer r = true ->
    input_search (prefix (extract_literal rer r)) inp = Some inp' ->
    input_prefix i inp' forward ->
    input_prefix inp i forward ->
    un_exec rer r i = un_exec rer r inp'.
Proof.
  intros i r inp inp' Hsupported Hsearch Hprefix Hlow.
  remember forward as dir.
  induction Hprefix; subst.
  - reflexivity.
  - erewrite <-IHHprefix; eauto using ip_prev'.
    destruct inp1 as [next pref], next as [|c next]; [discriminate|inversion H]; subst.
    pose proof (is_tree_productivity rer [Areg (lazy_prefix r)] (Input (c :: next) pref) Groups.GroupMap.empty forward) as [tree Htree].
    pose proof (is_tree_productivity rer [Areg (lazy_prefix r)] (Input next (c::pref)) Groups.GroupMap.empty forward) as [tree' Htree'].
    erewrite <-!un_exec_correct; eauto.
    inversion Htree. inversion CONT. destruct plus; [discriminate|]. inversion ISTREE1; [|discriminate]. injection READ as <-.
    unfold first_leaf. subst. simpl. unfold advance_input'. simpl.
    assert (Hnoskip: tree_res tskip Groups.GroupMap.empty (Input (c :: next) pref) forward = None). {
      eapply extract_literal_prefix_contra, input_search_no_earlier; eauto.
      rewrite input_prefix_strict_suffix in Hprefix, Hlow.
      split; destruct Hprefix, Hlow; subst; eauto using ss_next', ss_advance.
    }
    rewrite Hnoskip. simpl.
    inversion Htree'. inversion TREECONT.
    + erewrite is_tree_determ with (t1:=tree') (t2:=treecont); eauto.
    + exfalso. now apply CHECKFAIL, read_suffix.
Qed.

Theorem search_acc_once_correct {strs:StrSearch} {engine:UnanchoredEngine rer}:
  forall r inp tree,
    un_supported_regex rer r = true ->
    is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree ->
    first_leaf tree inp = search_acc_once r inp.
Proof.
  unfold search_acc_once.
  intros r inp tree Hsupported Htree.
  destruct input_search eqn:Hsearch.
  (* we found a position to start at *)
  - erewrite un_exec_correct; eauto.
    assert (input_prefix inp i forward). {
      apply input_search_strict_suffix in Hsearch.
      now rewrite <-input_prefix_strict_suffix in Hsearch.
    }
    eapply un_exec_all_between_str_search_eq; eauto using ip_eq.
  (* there is no occurrence of the literal *)
  - rewrite input_search_none_str_search in Hsearch.
    eauto using str_search_none_nores_unanchored.
Qed.

Instance SearchAccOnceEngine {strs:StrSearch} {engine:UnanchoredEngine rer}: UnanchoredEngine rer := {
  un_exec := search_acc_once;
  un_supported_regex := un_supported_regex rer;
  un_exec_correct := search_acc_once_correct
}.

(** * Bruteforce search *)
(* We define a search routine which attempts to run an anchored engine at each position *)
(* returning the earliest result. We then prove that a prefix accelerated version is equivalent. *)

(* for each input position we run the anchored engine and return the earliest match *)
Fixpoint search_from {engine:AnchoredEngine rer} (r: regex) (next: string) (prev: string) : option leaf :=
  match (exec rer r (Input next prev)) with
  | Some leaf => Some leaf
  | None => match next with
            | [] => None
            | c::t => search_from r t (c::prev)
            end
  end.

Definition search_from_input {engine:AnchoredEngine rer} (r:regex) (inp:input) : option leaf :=
  search_from r (next_str inp) (pref_str inp).


(* same as search_from_input but skips input positions that do not match the prefix *)
(* TODO: make it skip multiple times *)
Definition search_from_input_acc {strs:StrSearch} {engine:AnchoredEngine rer} (r:regex) (inp:input) (lit:literal) : option leaf :=
  let p := prefix lit in
  (* we skip the initial input that does not match the prefix *)
  match (input_search p inp) with
  | None => None (* if prefix is not present anywhere, then we cannot match *)
  | Some i => search_from r (next_str i) (pref_str i)
  end.


Lemma search_from_before_jump_eq {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall i r inp inp',
    supported_regex rer r = true ->
    input_search (prefix (extract_literal rer r)) inp = Some inp' ->
    input_prefix i inp' forward ->
    input_prefix inp i forward ->
    search_from r (next_str i) (pref_str i) = search_from r (next_str inp') (pref_str inp').
Proof.
  intros i r inp inp' Hsubset Hsearch Hprefix Hlow.
  remember forward as dir.
  induction Hprefix; subst.
  - reflexivity.
  - pose proof H as Hadvance.
    specialize (IHHprefix Hsearch).
    unfold advance_input in H. destruct inp1 as [next1 pref1] eqn:Hinp1, next1 eqn:Hnext1; [easy|].
    inversion H. rewrite <-H1 in IHHprefix.
    assert (Hnone: exec rer r (Input (t :: s) pref1) = None). {
      assert (Hbetween: input_between inp inp3 inp1). {
        rewrite input_prefix_strict_suffix in Hprefix, Hlow.
        split; destruct Hprefix, Hlow; subst; eauto using ss_next', ss_advance.
      }
      subst.
      pose proof (is_tree_productivity rer [Areg r] (Input (t :: s) pref1) Groups.GroupMap.empty forward) as [tree Htree].
      erewrite <-exec_correct; eauto.
      eauto using input_search_no_earlier, extract_literal_prefix_contra.
    }
    simpl.
    rewrite Hnone.
    eauto using ip_prev'.
Qed.

Lemma input_search_exec_none {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall i r inp,
    supported_regex rer r = true ->
    input_search (prefix (extract_literal rer r)) inp = None ->
    input_prefix inp i forward ->
    exec rer r i = None.
Proof.
  intros i r inp Hsubset Hsearch Hlow.
  rewrite input_prefix_strict_suffix in Hlow.
  pose proof (is_tree_productivity rer [Areg r] i Groups.GroupMap.empty forward) as [tree Htree].
  erewrite <-exec_correct; eauto.
  eauto using input_search_not_found, extract_literal_prefix_contra.
Qed.

Lemma search_from_none_prefix {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall i r inp,
    supported_regex rer r = true ->
    input_search (prefix (extract_literal rer r)) inp = None ->
    input_prefix inp i forward ->
    search_from r (next_str i) (pref_str i) = None.
Proof.
  intros [next pref] r inp Hsubset Hsearch Hprefix.
  generalize dependent pref.
  induction next; intros pref Hprefix.
  - simpl; erewrite input_search_exec_none; eauto using ip_eq.
  - simpl in *.
    erewrite IHnext. erewrite input_search_exec_none.
    all: eauto using ip_prev'.
Qed.

Theorem builtin_exec_equiv {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall r inp,
    supported_regex rer r = true ->
    search_from_input r inp = search_from_input_acc r inp (extract_literal rer r).
Proof.
  intros r inp Hsubset.
  unfold search_from_input, search_from_input_acc.
  destruct input_search eqn:Hsearch.
  - assert (input_prefix inp i forward). {
      apply input_search_strict_suffix in Hsearch.
      now rewrite <-input_prefix_strict_suffix in Hsearch.
    }
    eapply search_from_before_jump_eq; eauto using ip_eq.
  - eapply search_from_none_prefix; eauto using ip_eq.
Qed.

End MetaLiterals.
