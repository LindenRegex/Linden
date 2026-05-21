(** * The Meta engine  *)

(* Individual regex engines have their own unique strengths and weaknesses. *)
(* Some may support only a subset of regex features, some may be more *)
(* efficient depending on some characteristics of the regex or the input. *)
(* Sometimes we may even want to skip regex engines entirely and just do a *)
(* substring search. The Meta engine exploits these features by *)
(* encapsulating heuristics that look for matches using strategies it deems *)
(* to be the most efficient. *)

From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree LazyPrefix.
From Linden Require Import Parameters LWParameters.
From Linden Require Import Prefix.
From Linden Require Import EngineSpec MetaLiterals MetaAnchored.
From Linden Require Import PikeSubset SeenSets.
From Linden Require Import Tactics.
From Warblre Require Import Base RegExpRecord.


Section Meta.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* abstract heuristic for picking an anchored and anchored engine  *)
Record meta_heuristic := {
  meta_supported_regex : regex -> bool;
  pick_anchored : regex -> input -> AnchoredEngine rer;
  anchored_supported : forall r inp,
    meta_supported_regex r = true ->
    let engine := pick_anchored r inp in
    engine.(supported_regex rer) r = true;
  pick_unanchored : regex -> input -> UnanchoredEngine rer;
  unanchored_supported : forall r inp,
    meta_supported_regex r = true ->
    let engine := pick_unanchored r inp in
    engine.(un_supported_regex rer) r = true;
}.

(* entry point for looking for a match for a regex r in an input inp *)
Definition meta_search {heuristic:meta_heuristic} (r:regex) (inp:input) : option leaf :=
  match @try_lit_search _ rer BruteForceStrSearch r inp with
  | Ok ol => ol
  | Unsupported =>
    match @try_anchored_search _ _ (heuristic.(pick_anchored) r inp) r inp with
    | Ok ol => ol
    | Unsupported => @un_exec _ _ (heuristic.(pick_unanchored) r inp) r inp
    end
  end.

Theorem meta_search_correct {heuristic:meta_heuristic}:
  forall r inp tree,
    heuristic.(meta_supported_regex) r = true ->
    is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree ->
    first_leaf tree inp = @meta_search heuristic r inp.
Proof.
  intros r inp tree Hsup Htree.
  unfold meta_search.
  destruct try_lit_search as [|ol'] eqn:Hlit.
  - (* literal search failed, try anchored search *)
    destruct try_anchored_search as [|ol'] eqn:Hanch.
    + (* anchored search not applicable, fall back to unanchored search *)
      pose proof (heuristic.(unanchored_supported) r inp).
      eauto using un_exec_correct.
    + (* anchored search succeeded *)
      pose proof (heuristic.(anchored_supported) r inp).
      eapply try_anchored_search_correct in Hanch as <-; eauto.
  - (* literal search succeeded *)
    eapply try_lit_search_correct in Hlit; eauto.
Qed.

(** Specialized Meta engine with a custom heuristic *)

(* The configuration of a Meta engine search *)
Record meta_config := {
  (* the memory limit the search should try to respect *)
  (* expressed in a somewhat arbitrary unit, attemps to be the unit of a pointer size *)
  (* if not specified, there is no limit *)
  memory_limit : option nat;
}.


Definition memobt_peak_memory_usage (r:regex) (inp:input) : nat :=
  regex_size r * total_length inp.

Definition can_use_memobt (config:meta_config) (r:regex) (inp:input) : bool :=
  match config.(memory_limit) with
    | Some lim => memobt_peak_memory_usage r inp <=? lim
    | None => true
  end.

(* a choice of an anchored engine *)
Definition pick_meta_anchored (config:meta_config) (r:regex) (inp:input) : AnchoredEngine rer :=
  if can_use_memobt config r inp then
    @MemoBTAnchoredEngine _ (MemoList _) rer
  else
    @PikeVMAnchoredEngine VMSlist _ rer.

(* a choice of an unanchored engine *)
Definition pick_meta_unanchored (config:meta_config) (r:regex) (inp:input) : UnanchoredEngine rer :=
  if can_use_memobt config r inp then
    @SearchAccOnceEngine _ rer BruteForceStrSearch (@MemoBTUnanchoredEngine _ (MemoList _) rer BruteForceStrSearch)
  else
    @SearchAccOnceEngine _ rer BruteForceStrSearch (@PikeVMUnanchoredEngine VMSlist _ rer BruteForceStrSearch).

Lemma pick_meta_anchored_supported (config:meta_config):
  forall r inp,
    is_pike_regex r = true ->
    let engine := pick_meta_anchored config r inp in
    engine.(supported_regex rer) r = true.
Proof.
  unfold pick_meta_anchored.
  intros.
  destruct can_use_memobt; eauto.
Qed.

Lemma pick_meta_unanchored_supported (config:meta_config):
  forall r inp,
    is_pike_regex r = true ->
    let engine := pick_meta_unanchored config r inp in
    engine.(un_supported_regex rer) r = true.
Proof.
  unfold pick_meta_unanchored.
  intros.
  destruct can_use_memobt; eauto.
Qed.

(* A specialized search function that deploys all verified optimizations *)
Definition search (config:meta_config) (r:regex) (inp:input) : option leaf :=
  @meta_search {|
    meta_supported_regex := is_pike_regex;
    pick_anchored := pick_meta_anchored config;
    anchored_supported := pick_meta_anchored_supported config;
    pick_unanchored := pick_meta_unanchored config;
    unanchored_supported := pick_meta_unanchored_supported config;
  |} r inp.

(* proof that the new search function is an anchored engine itself *)
Instance MetaEngine (config:meta_config): UnanchoredEngine rer := {
  un_exec := search config;
  un_supported_regex := is_pike_regex;
  un_exec_correct := ltac:(intros; now apply meta_search_correct);
}.

End Meta.
