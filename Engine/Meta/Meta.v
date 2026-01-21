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
From Linden Require Import Parameters LWParameters.
From Linden Require Import Prefix.
From Linden Require Import EngineSpec MetaLiterals MetaAnchored.
From Linden Require Import PikeSubset SeenSets.
From Linden Require Import Tactics.
From Warblre Require Import Base RegExpRecord.


Section Meta.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

Definition meta_supported_regex (r:regex) : bool :=
  is_pike_regex r.

(* The configuration of a Meta engine search *)
Record meta_config := {
  (* the memory limit the search should try to respect *)
  (* expressed in a somewhat arbitrary unit, attemps to be the unit of a pointer size *)
  (* if not specified, there is no limit *)
  memory_limit : option nat;
}.

(* FIXME: move this computation to FunctionalMemoBT and it should be with regards to :code, not regex size *)
Definition memobt_peak_memory_usage (r:regex) (inp:input) : nat :=
  regex_size r * total_length inp.

(* an anchored search with heuristics *)
Definition meta_search_anchored (config:meta_config) (r:regex) (inp:input) : option leaf :=
  let can_use_memobt := match config.(memory_limit) with
    | Some lim => memobt_peak_memory_usage r inp <=? lim
    | None => true
  end in
  if can_use_memobt then
    @exec _ _ (@MemoBTAnchoredEngine _ rer) r inp
  else
    @exec _ _ (@PikeVMAnchoredEngine VMSlist _ rer) r inp.

Theorem meta_search_anchored_correct (config:meta_config):
  forall r inp tree,
    meta_supported_regex r = true ->
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    first_leaf tree inp = meta_search_anchored config r inp.
Proof.
  intros r inp tree Hsup Htree.
  unfold meta_search_anchored.
  case_if.
  - (* use tha MemoBT engine *)
    eauto using exec_correct.
  - (* use tha PikeVM engine *)
    eauto using exec_correct.
Qed.

Instance MetaSearchAnchored (config:meta_config): AnchoredEngine rer := {
  exec := meta_search_anchored config;
  supported_regex := meta_supported_regex;
  exec_correct := meta_search_anchored_correct config
}.

(* MemoBT supports lazy_prefix *)
Lemma lazy_prefix_supported_memobt:
  @lazy_prefix_supported _ rer (MemoBTAnchoredEngine rer).
Proof. intro r. eauto. Qed.

Definition search (config:meta_config) (r:regex) (inp:input) : option leaf :=
  match @try_lit_search _ rer BruteForceStrSearch r inp with
  | Some ol => ol
  | None =>
    match @try_anchored_search _ _ (@MetaSearchAnchored config) r inp with
    | Some ol => ol
    | None =>
        let can_use_memobt := match config.(memory_limit) with
          | Some lim => memobt_peak_memory_usage r inp <=? lim
          | None => true
        end in
        if can_use_memobt then
          @un_exec _ _ (@SearchAccOnceEngine _ rer BruteForceStrSearch (@UnanchorEngine _ rer (@MemoBTAnchoredEngine _ rer) lazy_prefix_supported_memobt)) r inp
        else
          @un_exec _ _ (@SearchAccOnceEngine _ rer BruteForceStrSearch (@PikeVMUnanchoredEngine VMSlist _ rer BruteForceStrSearch)) r inp
    end
  end.


Theorem search_correct (config:meta_config):
  forall r inp tree,
    meta_supported_regex r = true ->
    is_tree rer [Areg (lazy_prefix r)] inp Groups.GroupMap.empty forward tree ->
    first_leaf tree inp = search config r inp.
Proof.
  intros r inp tree Hsup Htree.
  unfold search.
  unfold meta_supported_regex in Hsup.
  destruct try_lit_search as [ol'|] eqn:Hlit.
  - (* literal search succeeded *)
    eapply try_lit_search_correct in Hlit; eauto.
  - (* literal search failed, try anchored search *)
    destruct try_anchored_search as [ol'|] eqn:Hanch.
    + (* anchored search succeeded *)
      eapply try_anchored_search_correct in Hanch as <-; eauto.
    + (* anchored search not applicable, fall back to unanchored search *)
      case_if.
      * (* use tha MemoBT engine *)
        eauto using un_exec_correct.
      * (* use tha PikeVM engine *)
        eauto using un_exec_correct.
Qed.

Instance MetaEngine (config:meta_config): UnanchoredEngine rer := {
  un_exec := search config;
  un_supported_regex := meta_supported_regex;
  un_exec_correct := search_correct config
}.

End Meta.
