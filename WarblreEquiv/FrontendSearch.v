(** * The search loop of Warblre's [RegExpBuiltinExec] *)

(* [RegExpBuiltinExec]'s search loop [repeat_matcher_loop] runs its matcher
   from a start index given by the flags and lastIndex: once if sticky, and
   at every later position otherwise, returning the first success. This file
   names that search [whole_search] and proves the loop factors through it,
   preserving errors and unsuccessful searches. Nothing is assumed of the
   matcher: this is an identity of search algorithms. *)

From Stdlib Require Import List ZArith Lia.
From Warblre Require Import Frontend Base Result Notation BuiltinExec.
From Linden Require Import Parameters LWParameters Regex Groups ResultTranslation.
Import ListNotations Notation.

Fixpoint first_success {A B E : Type} (attempt : nat -> Result (option A) E)
    (project : nat -> A -> B) (positions : list nat) : Result (option B) E :=
  match positions with
  | [] => Result.Success None
  | i :: rest => match attempt i with
    | Result.Error error => Result.Error error
    | Result.Success None => first_success attempt project rest
    | Result.Success (Some value) => Result.Success (Some (project i value))
    end
  end.

Section FrontendSearch.
  Context {params : LindenParameters}.
  Local Notation FP := (@LWParameters params).
  (* Instances as Warblre's frontend types them. *)
  Local Notation Instance := (@RegExpInstance.type _ _ _ (@Parameters.character_marker FP)
    (@Parameters.string_marker FP) (@Parameters.unicode_property_marker FP)).

  (* A match found from position [i], with its whole-match range. *)
  Definition whole_range (i : nat) (state : MatchState) :=
    (capture_range (Z.of_nat i) (MatchState.endIndex state), state).

  (* The first successful match among [positions], with its whole-match range. *)
  Definition whole_search (matcher : string -> nat -> Result (option MatchState) Errors.MatchError.type)
      input positions := first_success (matcher input) whole_range positions.

  Lemma whole_search_some matcher input positions range ms :
    whole_search matcher input positions = Result.Success (Some (range, ms)) ->
    exists start, In start positions /\ matcher input start = Result.Success (Some ms) /\
      range = capture_range (Z.of_nat start) (MatchState.endIndex ms).
  Proof.
    induction positions as [|start positions IH]; [discriminate|].
    cbn [whole_search first_success whole_range]. destruct (matcher input start) as [[state|]|error] eqn:RUN; try discriminate.
    - intro EQ. injection EQ as <- <-. exists start. cbn. auto.
    - intro SEARCH. destruct (IH SEARCH) as [i [IN [MATCH RANGE]]]. exists i. cbn. auto.
  Qed.

  (* Linden reports the whole-match range through group 0, which Warblre's
     lowering leaves free. [whole_decode] reads it back. *)
  Definition whole_regex r := Group 0 r.

  Definition whole_decode groups (best : option Tree.leaf) := match best with
    | None => Some None
    | Some (_, gm) => match to_capture_range (GroupMap.find 0 gm), to_MatchState best groups with
      | Some range, Some ms => Some (Some (range, ms)) | _, _ => None end end.

  (* The index where [regExpBuiltinExec] starts its search loop. *)
  Definition frontend_index (R : Instance) :=
    let flags := RegExpInstance.originalFlags R in
    if orb (RegExpFlags.g flags) (RegExpFlags.y flags) then Z.to_nat (RegExpInstance.lastIndex R) else 0.

  (* [regExpBuiltinExec] runs [repeat_matcher_loop] from [frontend_index]. *)
  Lemma regExpBuiltinExec_search (R : Instance) (input : string) : (0 <= RegExpInstance.lastIndex R)%Z ->
    let flags := RegExpInstance.originalFlags R in
    exists finish, @regExpBuiltinExec FP R input =
      Result.bind (repeat_matcher_loop R input (length input) (RegExpFlags.g flags) (RegExpFlags.y flags)
        (RegExpInstance.regExpMatcher R) input (frontend_index R) (length input + 2)) finish.
  Proof.
    intro NONNEG. unfold regExpBuiltinExec, frontend_index. cbv zeta.
    destruct (RegExpFlags.g _), (RegExpFlags.y _); cbn [negb andb orb];
      rewrite from_int_nonneg by lia; eexists; reflexivity.
  Qed.

  Definition loop_result (R : Instance) (result : option (CaptureRange * MatchState)) : @LoopResult FP :=
    let flags := RegExpInstance.originalFlags R in
    match result with
    | None => Terminates (Null (if orb (RegExpFlags.g flags) (RegExpFlags.y flags) then RegExpInstance.setLastIndex R 0%Z else R))
    | Some (range, state) => Continues state (Z.to_nat (CaptureRange.startIndex range))
    end.

  (* Linden strings are lists of characters, so string and list indices agree. *)
  Lemma plain_string (input : string) : @PlainString FP input.
  Proof. repeat split. Qed.

  (* From [start], the loop tries one position if sticky, and every remaining position otherwise. *)
  Theorem repeat_matcher_loop_search (R : Instance) (input : string) start fuel :
    let flags := RegExpInstance.originalFlags R in
    let positions := S (length input) - start in
    positions < fuel ->
    repeat_matcher_loop R input (length input) (RegExpFlags.g flags) (RegExpFlags.y flags)
      (RegExpInstance.regExpMatcher R) input start fuel =
    Result.bind (whole_search (RegExpInstance.regExpMatcher R) input
        (seq start (if RegExpFlags.y flags then Nat.min 1 positions else positions)))
      (fun result => Result.Success (loop_result R result)).
  Proof.
    cbv zeta. revert start. induction fuel as [|fuel IH]; intros start FUEL; [lia|]. cbn [repeat_matcher_loop].
    unfold loop_result. destruct (Nat.leb_spec (S (length input)) start) as [PAST|WITHIN].
    - replace (S (length input) - start) with 0 by lia. now destruct RegExpFlags.y.
    - rewrite (to_list_index_plain (specParameters := FP) input (plain_string input)). cbn [Result.bind].
      replace (S (length input) - start) with (S (length input - start)) by lia.
      destruct (RegExpFlags.y _) eqn:STICKY; cbn [seq Nat.min whole_search first_success];
        destruct (RegExpInstance.regExpMatcher R input start) as [[state|]|error]; cbn;
        rewrite ?Nat2Z.id, ?Bool.orb_true_r; try reflexivity.
      etransitivity; [apply (IH (S start)); lia|].
      unfold loop_result. cbv zeta. now rewrite STICKY.
  Qed.

  (* Within the input, the loop reports the search over its positions: the start alone if sticky. *)
  Corollary whole_search_loop (R : Instance) (input : string) start expected :
    let flags := RegExpInstance.originalFlags R in
    start <= length input ->
    whole_search (RegExpInstance.regExpMatcher R) input
      (seq start (if RegExpFlags.y flags then 1 else S (length input) - start)) = Result.Success expected ->
    repeat_matcher_loop R input (length input) (RegExpFlags.g flags) (RegExpFlags.y flags)
      (RegExpInstance.regExpMatcher R) input start (length input + 2) = Result.Success (loop_result R expected).
  Proof.
    cbv zeta. intros WITHIN SEARCH. rewrite repeat_matcher_loop_search by lia.
    replace (Nat.min 1 (S (length input) - start)) with 1 by lia. now rewrite SEARCH.
  Qed.

End FrontendSearch.
