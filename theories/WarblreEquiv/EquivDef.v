From Linden Require Import Semantics FunctionalSemantics Tree Groups Regex Chars.
From Linden Require Import GroupMapMS MSInput GroupMapLemmas.
From Linden Require Import LWParameters Parameters.
From Linden Require Import Utils.
From Warblre Require Import Parameters Notation Base Result Match RegExpRecord.
From Stdlib Require Import ZArith List.
Import Notation.
Import Match.

(** * Equivalence definitions *)

Section EquivDef.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* Groups that we want to forbid from being defined before matching a regex. *)
  Definition forbidden_groups (reg: regex): list group_id :=
    match reg with
    | Quantified _ _ _ _ => nil
    | _ => def_groups reg
    end.


  (** ** Validity of input MatchStates with respect to a check *)
  (* A continuation is only equivalent to a list of actions containing some check Acheck inp 
     for input MatchStates that have either progressed or stayed unmodified wrt the input inp. *)

  (* Validity of a MatchState with respect to one fixed check input. *)
  Inductive ms_valid_wrt_check: MatchState -> input -> Direction -> Prop :=
  | Validcheck_forward: forall ms inp,
      (MatchState.endIndex ms >= Z.of_nat (idx inp))%Z -> ms_valid_wrt_check ms inp forward
  | Validcheck_backward: forall ms inp,
      (MatchState.endIndex ms <= Z.of_nat (idx inp))%Z -> ms_valid_wrt_check ms inp backward.

  (* Validity of a MatchState with respect to the checks of a list of actions. *)
  Definition ms_valid_wrt_checks (ms: MatchState) (act: actions) (dir: Direction): Prop :=
    forall inpcheck: input, In (Acheck inpcheck) act -> ms_valid_wrt_check ms inpcheck dir.

  
  (* Equivalence of results is defined as equivalence of MatchStates, group maps and inputs. *)
  Inductive equiv_res: option leaf -> option MatchState -> Prop :=
  | Equiv_res_None: equiv_res None None
  | Equiv_res_Some: forall inp gm ms,
      ms_matches_inp ms inp ->
      equiv_groupmap_ms gm ms ->
      equiv_res (Some (inp, gm)) (Some ms).


  (* Definition of when a MatcherContinuation performs a given list of actions. *)
  (* A MatcherContinuation mc, working on input string str0 and with the open group list gl,
  performs the actions described in act in the direction dir when: *)
  Definition equiv_cont (mc: MatcherContinuation) (gl: open_groups) (forbgroups: list group_id) (act: actions) (dir: Direction) (str0: string): Prop :=
    forall (gm: group_map) (ms: MatchState) (inp: input) (res: option MatchState) (fuel: nat) (t: tree),
      (* for all corresponding tuples of a MatchState ms, an input inp, a group map gm 
      and a list of open groups gl that use the input string str0, *)
      input_compat inp str0 ->
      equiv_groupmap_ms gm ms -> group_map_equiv_open_groups gm gl ->
      ms_matches_inp ms inp ->
      (* such that ms is valid with respect to the checks in act, *)
      ms_valid_wrt_checks ms act dir ->
      (* gm only contains CaptureRanges in the right direction (i.e. start <= end), *)
      gm_valid gm ->
      (* and gm does not define any of the groups in the forbidden groups, *)
      no_forbidden_groups gm forbgroups ->
      (* if the continuation mc called on ms yields the result res, *)
      mc ms = Success res ->
      (* then letting t be the tree corresponding to the actions in act on the input inp with group map gm and direction dir, *)
      compute_tree rer act inp gm dir fuel = Some t ->
      (* the first branch of t is equivalent to the result res. *)
      equiv_res (tree_res t gm inp dir) res.

  (* Definition of when a Matcher recognizes a regex in a given direction. *)
  (* A Matcher m is said to recognize a regex reg in direction dir when: *)
  Definition equiv_matcher (m: Matcher) (reg: regex) (dir: Direction): Prop :=
    (* for any input string str0, *)
    forall (str0: string) (mc: MatcherContinuation) (gl: open_groups) (forbgroups: list group_id) (act: actions),
    (* for any MatcherContinuation mc working with the list of open groups gl on the string str0 performing the actions act, *)
    equiv_cont mc gl forbgroups act dir str0 ->
    (* if the open groups do not contain any of the groups defined by reg, *)
    open_groups_disjoint gl (def_groups reg) ->
    (* and the continuation does not forbid defining any group defined by the regex, *)
    List.Disjoint (def_groups reg) forbgroups ->
    (* plugging the continuation mc into the matcher m yields a continuation that performs the actions Areg reg :: act. *)
    equiv_cont (fun ms => m ms mc) gl (forbidden_groups reg ++ forbgroups) (Areg reg :: act)%list dir str0.

End EquivDef.
