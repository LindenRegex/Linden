(** * Some examples of Backtracking Trees  *)

From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import FunctionalUtils FunctionalSemantics.
From Linden Require Import Inst.
From Warblre Require Import Inst.
Require Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Open Scope string_scope.


(* Defining an example rer to execute our regexes with *)
Search (regex -> non_neg_integer).

(* setting flags to false *)
Definition rer_of (r:regex) : RegExpRecord :=
  RegExpRecord.make false false false tt (max_group r).

Section TreeExample.

Definition a := $ "a".
Definition b := $ "b".
Definition c := $ "c".

Example a_char : regex := Regex.Character (CdSingle a).
Example b_char : regex := Regex.Character (CdSingle b).
Example c_char : regex := Regex.Character (CdSingle c).


(** * Figure 2 of the paper  *)
Example fig2_regex: regex :=
  Sequence
    (Disjunction a_char
       (Disjunction
          (Sequence a_char (Group 1 b_char))
          a_char))
    (Sequence b_char c_char).

Example fig2_input: input := Input [a;b;b;c] [].

Example fig2_tree: tree :=
  Choice
    (Read a (Read b Mismatch))
    (Choice
       (Read a (GroupAction (Open 1) (Read b (GroupAction (Close 1) (Read b (Read c Match))))))
       (Read a (Read b Mismatch))).

Theorem fig2_is_tree:
  is_tree (rer_of fig2_regex) [Areg fig2_regex] fig2_input GroupMap.empty forward fig2_tree.
Proof.
  apply compute_tr_eq_is_tree. reflexivity.
Qed.

(* On page 8, right before section 3.2 *)
Theorem fig2_first_leaf:
  first_leaf fig2_tree fig2_input = Some (Input [] [c; b; b; a],
    GroupMap.close 2 1 (GroupMap.open 1 1 GroupMap.empty)).
Proof.
  reflexivity.
Qed.

(** * Figure 6 of the paper  *)
(* A counter-example of distributing the sequence over the disjunction *)

Example fig6_1_regex: regex :=
  Sequence
    (Disjunction a_char (Sequence a_char b_char))
    (Disjunction c_char b_char).

Example fig6_2_regex: regex :=
  Disjunction
    (Sequence (Disjunction a_char (Sequence a_char b_char)) c_char)
    (Sequence (Disjunction a_char (Sequence a_char b_char)) b_char).

Example fig6_input : input := Input [a;b;c] [].

Example fig6_1_tree: tree :=
  Choice
    (Read a (Choice Mismatch (Read b Match)))
    (Read a (Read b (Choice (Read c Match) Mismatch))).

Example fig6_2_tree: tree :=
  Choice
    (Choice (Read a Mismatch) (Read a (Read b (Read c Match))))
    (Choice (Read a (Read b Match)) (Read a (Read b Mismatch))).

Theorem fig6_1_is_tree:
  is_tree (rer_of fig6_1_regex) [Areg fig6_1_regex] fig6_input GroupMap.empty forward fig6_1_tree.
Proof.
  apply compute_tr_eq_is_tree. reflexivity.
Qed.

Theorem fig6_2_is_tree:
  is_tree (rer_of fig6_2_regex) [Areg fig6_2_regex] fig6_input GroupMap.empty forward fig6_2_tree.
Proof.
  apply compute_tr_eq_is_tree. reflexivity.
Qed.

(* The two trees have different results *)
Theorem different_results:
  first_leaf fig6_1_tree fig6_input <> first_leaf fig6_2_tree fig6_input.
Proof.
  unfold fig6_input, fig6_1_tree, fig6_2_tree, first_leaf. simpl.
  unfold advance_input'. simpl. intros H. inversion H.
Qed.

End TreeExample.
