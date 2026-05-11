(** * Meta literals *)

(* Different optimizations related to doing literal-based searches and acceleration. *)

From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree LazyPrefix.
From Linden Require Import FunctionalUtils GroupMapLemmas.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix Prefix.
From Linden Require Import EngineSpec.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import Tactics.


Section MetaLiterals.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).


(* tries to perform a search using only the literal from the regex *)
Definition try_lit_search {strs:StrSearch} (r:regex) (inp:input) : search_result :=
  match extract_literal rer r with
  | Prefix s => Unsupported
  | Impossible => Ok None
  | Exact s =>
      (* if it has asserts doing a string search is not enough *)
      if has_asserts r then Unsupported
      else
        match input_search s inp with
        | Some inp' =>
            (* if it has groups we must reconstruct them *)
            (* LATER: do group reconstruction with an anchored engine *)
            if def_groups r == [] then
              Ok (Some (advance_input_n inp' (length s) forward, Groups.GroupMap.empty))
            else Unsupported
        | None => Ok None
        end
  end.

(* if the try_lit_search returned a leaf, it is the first_leaf *)
Theorem try_lit_search_correct {strs:StrSearch}:
  forall r inp tree ol,
    is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree ->
    try_lit_search r inp = Ok ol ->
    first_leaf tree inp = ol.
Proof.
  unfold try_lit_search.
  intros r inp tree ol Htree Htry.
  destruct extract_literal eqn:Heq.
  (* Exact *)
  - destruct has_asserts eqn:Hasserts; [discriminate|].
    destruct input_search eqn:Hsearch.
    (* we found a match *)
    + eqdec; only 2: discriminate.
      injection Htry as <-.
      eapply exact_literal_result_unanchored in Hsearch as [gm' Hleaf]; eauto.
      eapply no_groups_empty_gm_regex in Htree; simpl; boolprop; eauto. simpl in Htree.
      now subst.
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
      split; ss_solve.
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
      ss_solve.
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

End MetaLiterals.
