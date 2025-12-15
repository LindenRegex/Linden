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
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* interface of an anchored, executable engine *)
(* an anchored engine finds matches exactly at the beginning of the input *)
Class AnchoredEngine := {
  exec: regex -> input -> option leaf;

  (* asserts the supported subset of regexes *)
  supported_regex: regex -> bool;

  (* the execution follows the backtracking tree semantics *)
  exec_correct: forall r inp tree ol,
    supported_regex r = true ->
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    (first_leaf tree inp = ol <-> exec r inp = ol)
}.

Definition dot_star : regex :=
  Quantified false 0 NoI.Inf (Regex.Character CdAll).
Definition lazy_prefix (r:regex) : regex :=
  Sequence dot_star r.

(* interface of an unanchored, executable engine *)
(* an unanchored engine finds matches anywhere in the input *)
Class UnanchoredEngine := {
  un_exec: regex -> input -> option leaf;

  (* asserts the supported subset of regexes *)
  un_supported_regex: regex -> bool;

  (* the execution follows the backtracking tree semantics *)
  un_exec_correct: forall r inp tree ol,
    un_supported_regex r = true ->
    is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree ->
    (first_leaf tree inp = ol <-> un_exec r inp = ol)
}.
End Engines.

Section Instances.
  Context {VMS: VMSeen}.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* predicate stating that if we support a regex then we support its lazy prefix *)
Definition lazy_prefix_supported {engine:AnchoredEngine rer} : Prop :=
  forall r, supported_regex rer r = true -> supported_regex rer (lazy_prefix r) = true.

(* We show that any anchored engine can be turned into an unanchored engine by just *)
(* executing the anchored engine with a lazy prefix *)
#[refine]
Instance UnanchorEngine {engine:AnchoredEngine rer} (lazy_prefix_supp: lazy_prefix_supported): UnanchoredEngine rer := {
  un_exec r inp := exec rer (lazy_prefix r) inp;
  un_supported_regex r := supported_regex rer r;
}.
  (* un_exec_correct *)
  eauto using exec_correct.
Qed.

(* we show that the PikeVM fits the scheme of an anchored engine *)
#[refine]
Instance PikeVMAnchoredEngine: AnchoredEngine rer := {
  exec r inp := match pike_vm_match rer r inp with
                | OutOfFuel => None
                | Finished res => res
                end;
  supported_regex := is_pike_regex;
}.
  (* exec_correct *)
  intros r inp tree ol Hsubset Htree.
  rewrite is_pike_regex_correct in Hsubset.
  pose proof (pike_vm_match_terminates rer r inp Hsubset) as [res Hmatch].
  rewrite Hmatch.
  split.
  - intros Hleaf.
    subst. eauto using pike_vm_match_correct, pike_vm_correct.
  - intros <-.
    symmetry. eauto using pike_vm_match_correct, pike_vm_correct.
Qed.

End Instances.
