(** * The Meta engine  *)

(* Individual regex engines have their own unique strengths and weaknesses. *)
(* Some may support only a subset of regex features, some may be more *)
(* efficient depending on some characteristics of the regex or the input. *)
(* Sometimes we may even want to skip regex engines entirely and just do a *)
(* substring search. The Meta engine exploits these features by *)
(* encapsulating heuristics that look for matches using strategies it deems *)
(* to be the most efficient. *)

Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree.
From Linden Require Import FunctionalUtils.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix Prefix.
From Linden Require Import EngineSpec.
From Warblre Require Import Base RegExpRecord.


Section Meta.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* for each input position we run the anchored engine and return the earliest match *)
Fixpoint search_from {engine:AnchoredEngine rer} (r: regex) (next: string) (prev: string): option leaf :=
  match (exec rer r (Input next prev)) with
  | Some leaf => Some leaf
  | None => match next with
            | [] => None
            | c::t => search_from r t (c::prev)
            end
  end.

Definition pref_str (i: input) : string :=
  match i with
  | Input _ pref => pref
  end.

(* the string-quadratic algorithm described in RegExpBuiltinExec *)
Definition BuiltinExec {engine:AnchoredEngine rer} (r:regex) (inp:input) : option leaf :=
  search_from r (next_str inp) (pref_str inp).


(* prefixed version *)
Definition BuiltinExecPrefixed {strs:StrSearch} {engine:AnchoredEngine rer} (r:regex) (inp:input) : option leaf :=
  let lit := extract_literal rer r in
  if lit == Impossible then None else
    let p := prefix lit in
    (* we skip the initial input that does not match the prefix *)
    match (input_search p inp) with
    | None => None (* if prefix is not present anywhere, then we cannot match *)
    | Some i => search_from r (next_str i) (pref_str i)
    end.


(* Fixpoint jump_try {strs:StrSearch} {engine:AnchoredEngine} (r:regex) (p:string) (next pref:string) : option leaf :=
  (* we skip the initial input that does not match the prefix *)
  match (input_search p (Input next pref)) with
  | None => None (* if prefix is not present anywhere, then we cannot match *)
  | Some (Input  =>
      match (exec r (Input next pref)) with
      | Some leaf => Some leaf
      | None => match next with
                | [] => None
                | c::t => jump_try r p t (c::pref)
                end
      end
  end. *)

Lemma search_from_before_jump_eq {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall i r inp inp',
    supported_regex rer r ->
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
      rewrite <-exec_correct; eauto.
      eauto using input_search_no_earlier, extract_literal_prefix_contra.
    }
    simpl.
    rewrite Hnone.
    eauto using ip_prev'.
Qed.

Lemma input_search_exec_none {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall i r inp,
    supported_regex rer r ->
    input_search (prefix (extract_literal rer r)) inp = None ->
    input_prefix inp i forward ->
    exec rer r i = None.
Proof.
  intros i r inp Hsubset Hsearch Hlow.
  rewrite input_prefix_strict_suffix in Hlow.
  pose proof (is_tree_productivity rer [Areg r] i Groups.GroupMap.empty forward) as [tree Htree].
  rewrite <-exec_correct; eauto.
  eauto using input_search_not_found, extract_literal_prefix_contra.
Qed.

Lemma search_from_none_prefix {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall i r inp,
    supported_regex rer r ->
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

Lemma input_search_exec_impossible {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall inp r,
    supported_regex rer r ->
    extract_literal rer r = Impossible ->
    exec rer r inp = None.
Proof.
  intros inp r Hsubset Hextract.
  pose proof (is_tree_productivity rer [Areg r] inp Groups.GroupMap.empty forward) as [tree Htree].
  rewrite <-exec_correct; eauto.
  eauto using extract_literal_impossible.
Qed.

Lemma search_from_impossible_prefix {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall inp r,
    supported_regex rer r ->
    extract_literal rer r = Impossible ->
    search_from r (next_str inp) (pref_str inp) = None.
Proof.
  intros [next pref] r Hsubset Hextract.
  generalize dependent pref.
  induction next; intros pref; simpl; erewrite input_search_exec_impossible; eauto.
Qed.

Theorem builtin_exec_equiv {strs:StrSearch} {engine:AnchoredEngine rer}:
  forall r inp,
    supported_regex rer r ->
    BuiltinExec r inp = BuiltinExecPrefixed r inp.
Proof.
  intros r inp Hsubset.
  unfold BuiltinExec, BuiltinExecPrefixed.
  wt_eq.
  + eapply search_from_impossible_prefix; eauto.
  + destruct input_search eqn:Hsearch.
    - assert (input_prefix inp i forward). {
        apply input_search_strict_suffix in Hsearch.
        now rewrite <-input_prefix_strict_suffix in Hsearch.
      }
      eapply search_from_before_jump_eq; eauto using ip_eq.
    - eapply search_from_none_prefix; eauto using ip_eq.
Qed.


End Meta.
