(** * Engine specification *)

(* This module describes what it means to be a regex engine. *)
(* We also show that our engines follow these definitions. *)

Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree.
From Linden Require Import Parameters LWParameters.
From Linden Require Import PikeSubset SeenSets FunctionalPikeVM.
From Linden Require Import Correctness.
From Warblre Require Import Base RegExpRecord.


Section Engines.
  Context {VMS: VMSeen}.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* interface of an anchored, executable engine *)
Class AnchoredEngine := {
  exec: regex -> input -> option leaf;

  (* asserts the supported subset of regexes *)
  supported_regex: regex -> Prop;

  (* the execution follows the backtracking tree semantics *)
  exec_correct: forall r inp tree ol,
    supported_regex r ->
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    (first_leaf tree inp = ol <-> exec r inp = ol)
}.

(* we show that the PikeVM fits the scheme of an anchored engine *)
#[refine]
Instance PikeVMAnchoredEngine: AnchoredEngine := {
  exec r inp := match pike_vm_match rer r inp with
                | OutOfFuel => None
                | Finished res => res
                end;
  supported_regex := pike_regex;
}.
  (* exec_correct *)
  intros r inp tree ol Hsubset Htree.
  pose proof (pike_vm_match_terminates rer r inp Hsubset) as [res Hmatch].
  rewrite Hmatch.
  split.
  - intros Hleaf.
    subst. eauto using pike_vm_match_correct, pike_vm_correct.
  - intros <-.
    symmetry. eauto using pike_vm_match_correct, pike_vm_correct.
Qed.
End Engines.
