(** * Warblre's [RegExpBuiltinExec] search, in Linden's semantics and the PikeVM *)

(* [FrontendSearch] reduces the frontend to [whole_search], which tries the
   compiled Warblre matcher at one start position if sticky and at every later
   position otherwise. In Linden's tree semantics, the first leaf of [[^]*?r]
   is the first leaf of [r] at the earliest start position
   ([lazy_prefix_first]). Relating each of these leaves to Warblre transports
   the search to [whole_search] ([search_suffixes]). Running [whole_regex r],
   group 0 reports the start of the match ([whole_at]). For Pike regexes, one
   PikeVM run, anchored iff sticky, computes the frontend's search
   ([pike_vm_frontend_search]). *)

From Stdlib Require Import List ZArith Lia.
From Warblre Require Import Result Notation Base RegExpRecord Semantics Frontend BuiltinExec.
From Linden Require Import Parameters LWParameters Regex Groups Chars Tree ResultTranslation FunctionalPikeVM Prefix SeenSets Semantics FunctionalUtils PikeSubset EquivLemmas RegexpTranslation Correctness EquivMain StrictSuffix Complexity FrontendSearch FreshGroup GroupMapLemmas.
Import ListNotations Notation.

Fixpoint first_some {A B} (f : A -> option B) (l : list A) : option B :=
  match l with [] => None | a :: l => match f a with None => first_some f l | b => b end end.

Section FrontendCorrectness.
Context {params : LindenParameters}.
Local Notation lower := (fun wr => warblre_to_linden wr 0 (buildnm wr)).
Local Notation early_errors := (@StaticSemantics.earlyErrors (@LWParameters params)).
Local Notation warblre_compile := (@Warblre.spec.Semantics.Semantics.compilePattern (@LWParameters params)).

(** In Linden's semantics, the first leaf of [[^]*?r] is the first leaf of [r] at the earliest start. *)
Lemma lazy_prefix_first rer r next pref :
  linden_result rer (lazy_prefix r) (Input next pref) = first_some (linden_result rer r) (possible_suffixes next pref).
Proof.
  unfold linden_result at 1. generalize (@compute_tr_is_tree params rer [Areg (lazy_prefix r)] (Input next pref) GroupMap.empty forward).
  generalize (compute_tr rer [Areg (lazy_prefix r)] (Input next pref) GroupMap.empty forward) as tree.
  revert pref. induction next as [|c next IH]; intros pref tree TREE;
    inversion TREE; inversion CONT; (destruct plus; [discriminate|]); subst;
    unfold first_leaf; cbn [tree_res greedy_choice first_some possible_suffixes]; rewrite (is_tree_eq_compute_tr rer SKIP).
  - inversion ISTREE1; [discriminate|]. unfold linden_result, first_leaf. now destruct tree_res.
  - inversion ISTREE1; [|discriminate]. inversion READ; subst.
    inversion TREECONT; [|exfalso; apply CHECKFAIL, ss_advance; reflexivity]; subst.
    rewrite <- (IH _ _ ltac:(apply Semantics.tree_sequence; exact TREECONT0)). unfold linden_result, first_leaf. now destruct tree_res.
Qed.

(** Searching the positions of a string searches its suffixes: if each attempt
    decodes the leaf at its input, the first success decodes the first leaf. *)
Lemma search_suffixes {A B L E} (attempt : string -> nat -> Result (option A) E) (project : nat -> A -> B)
    (leaf : input -> option L) decode next pref :
  decode None = Some None -> (forall l, decode (Some l) <> Some None) ->
  (forall inp, exists a, attempt (input_str inp) (idx inp) = Result.Success a /\
    decode (leaf inp) = Some (option_map (project (idx inp)) a)) ->
  exists e, first_success (attempt (input_str (Input next pref))) project (seq (length pref) (S (length next))) =
    Result.Success e /\ decode (first_some leaf (possible_suffixes next pref)) = Some e.
Proof.
  intros NONE SOME STEP. revert pref. induction next as [|c next IH]; intro pref;
    match goal with |- context [input_str (Input ?n ?p)] => destruct (STEP (Input n p)) as [[a|] [RUN DEC]] end;
    cbn [seq first_success first_some possible_suffixes length idx option_map] in *; rewrite RUN;
    destruct (leaf _); try congruence; try (exfalso; eapply SOME; eassumption);
    try (eexists; split; [reflexivity|eassumption]).
  replace (input_str (Input (c :: next) pref)) with (input_str (Input next (c :: pref))) by (cbn; now rewrite <- app_assoc).
  exact (IH (c :: pref)).
Qed.

(** Group 0 of [whole_regex r] records the range of the leaf of [r]. *)
Lemma whole_at rer r groups inp : ~ In 0 (def_groups r) ->
  whole_decode groups (linden_result rer (whole_regex r) inp) =
    Some (option_map (whole_range (idx inp)) (to_MatchState (linden_result rer r inp) groups)).
Proof.
  intros DEFS. unfold linden_result, whole_regex, first_leaf.
  pose proof (group_first_leaf rer r 0 GroupMap.empty inp _ _ DEFS ltac:(now rewrite gm_find_empty)
    (compute_tr_is_tree rer) (compute_tr_is_tree rer)) as GROUP.
  destruct tree_res as [[last gm]|], tree_res as [[last' gm']|]; try contradiction; [|reflexivity].
  destruct GROUP as [<- [ZERO OTHERS]]. cbn [whole_decode to_MatchState]. rewrite ZERO.
  cbn. unfold whole_range. do 4 f_equal. apply map_ext. intro n. rewrite OTHERS by lia. reflexivity.
Qed.

(** The compiled matcher's attempt at any input decodes the leaf of [whole_regex r] there. *)
Lemma whole_attempt pattern rer r matcher inp :
  lower pattern = Result.Success r ->
  RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin pattern [] ->
  early_errors pattern [] = Result.Success false ->
  warblre_compile pattern rer = Result.Success matcher ->
  exists a, matcher (input_str inp) (idx inp) = Result.Success a /\
    whole_decode (RegExpRecord.capturingGroupsCount rer) (linden_result rer (whole_regex r) inp) =
      Some (option_map (whole_range (idx inp)) a).
Proof.
  intros LOWER COUNT EARLY COMP.
  pose proof (warblre_to_linden_sound_root _ _ LOWER) as EQUIV.
  assert (DEFS : ~ In 0 (def_groups r)) by (rewrite (equiv_def_groups' _ _ _ _ EQUIV), in_seq; lia).
  destruct (equiv_main pattern r rer inp EQUIV COUNT (EarlyErrors.earlyErrors _ EARLY)) as [m [res [COMP' [RUN EQUIVALENT]]]].
  rewrite COMP in COMP'. injection COMP' as <-. exists res. split; [exact RUN|].
  rewrite whole_at by exact DEFS. do 2 f_equal.
  apply to_MatchState_equal; [eauto using compilePattern_preserves_groupcount|].
  now apply EQUIVALENT.
Qed.

(** From [start], one PikeVM run of [whole_regex r], anchored or not, decodes Warblre's search. *)
Theorem pike_vm_whole_match {VMS : VMSeen} (strs : StrSearch) pattern rer r input start (anchored : bool) :
  lower pattern = Result.Success r ->
  pike_regex r ->
  RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin pattern [] ->
  early_errors pattern [] = Result.Success false ->
  start <= length input ->
  let inp := Input (skipn start input) (rev (firstn start input)) in
  exists matcher best expected,
    warblre_compile pattern rer = Result.Success matcher /\
    whole_search matcher input (seq start (if anchored then 1 else S (length input) - start)) = Result.Success expected /\
    (if anchored then @pike_vm_match params VMS rer (whole_regex r) inp
     else @pike_vm_match_unanchored params VMS rer strs (whole_regex r) inp) = Finished best /\
    whole_decode (RegExpRecord.capturingGroupsCount rer) best = Some expected.
Proof.
  intros LOWER PIKE COUNT EARLY WITHIN inp.
  destruct (@Compile.compilePattern_success (@LWParameters params) pattern rer (eq_sym COUNT) (EarlyErrors.earlyErrors _ EARLY)) as [matcher COMP].
  exists matcher.
  assert (WRAPPED : pike_regex (whole_regex r)) by (unfold whole_regex; eauto using pike_regex).
  assert (STR : input_str inp = input) by (cbn; now rewrite rev_involutive, firstn_skipn).
  assert (IDX : idx inp = start) by (cbn; rewrite length_rev, length_firstn; lia).
  destruct anchored.
  - destruct (whole_attempt pattern rer r matcher inp LOWER COUNT EARLY COMP) as [a [RUN DECODE]].
    destruct (@pike_vm_match_terminates params VMS rer _ inp WRAPPED) as [best PIKERUN].
    exists best, (option_map (whole_range start) a). rewrite STR, IDX in *.
    split; [exact COMP|]. split; [cbn; rewrite RUN; now destruct a|]. split; [exact PIKERUN|].
    rewrite <- DECODE. f_equal. eapply pike_vm_correct; eauto using compute_tr_is_tree, pike_vm_match_correct.
  - destruct (search_suffixes matcher whole_range (linden_result rer (whole_regex r))
      (whole_decode (RegExpRecord.capturingGroupsCount rer)) (skipn start input) (rev (firstn start input)))
      as [expected [SEARCH DECODE]]; [reflexivity|intros [? ?]; cbn; destruct to_capture_range; discriminate|
        intro; exact (whole_attempt pattern rer r matcher _ LOWER COUNT EARLY COMP)|].
    rewrite <- lazy_prefix_first in DECODE. fold inp in SEARCH, DECODE.
    destruct (@pike_vm_match_terminates_unanchored params VMS rer strs _ inp WRAPPED) as [best PIKERUN].
    exists best, expected. split; [exact COMP|]. split; [|split; [exact PIKERUN|]].
    + rewrite STR, length_rev, length_firstn, length_skipn, Nat.min_l in SEARCH by lia.
      replace (S (length input) - start) with (S (length input - start)) by lia. exact SEARCH.
    + rewrite <- DECODE. f_equal.
      eapply pike_vm_correct_unanchored; eauto using compute_tr_is_tree, pike_vm_match_correct_unanchored.
Qed.

(** One PikeVM run from the frontend's start index, anchored iff sticky, computes its search loop. *)
Theorem pike_vm_frontend_search {VMS : VMSeen} (strs : StrSearch) R r input :
  Initialized R ->
  early_errors (RegExpInstance.originalSource R) [] = Result.Success false ->
  lower (RegExpInstance.originalSource R) = Result.Success r ->
  pike_regex r ->
  let flags := RegExpInstance.originalFlags R in
  let rer := RegExpInstance.regExpRecord R in
  let start := frontend_index R in
  let inp := Input (skipn start input) (rev (firstn start input)) in
  exists expected,
    repeat_matcher_loop R input (length input) (RegExpFlags.g flags) (RegExpFlags.y flags)
      (RegExpInstance.regExpMatcher R) input start (length input + 2) = Result.Success (loop_result R expected) /\
    if length input <? start then expected = None else
    exists best,
      (if RegExpFlags.y flags then @pike_vm_match params VMS rer (whole_regex r) inp
       else @pike_vm_match_unanchored params VMS rer strs (whole_regex r) inp) = Finished best /\
      whole_decode (RegExpRecord.capturingGroupsCount rer) best = Some expected.
Proof.
  intros [_ COUNT COMP _] EARLY LOWER PIKE. cbv zeta. set (start := frontend_index R).
  rewrite repeat_matcher_loop_search by lia.
  destruct (Nat.ltb_spec (length input) start) as [PAST|WITHIN].
  - exists None. replace (S (length input) - start) with 0 by lia. split; [now destruct RegExpFlags.y|reflexivity].
  - destruct (pike_vm_whole_match strs _ _ r input start (RegExpFlags.y (RegExpInstance.originalFlags R)) LOWER PIKE (eq_sym COUNT) EARLY WITHIN)
      as [matcher [best [expected [COMP' [SEARCH [PIKERUN DECODE]]]]]].
    rewrite COMP in COMP'. injection COMP' as <-.
    exists expected. replace (Nat.min 1 (S (length input) - start)) with 1 by lia. split; [|eauto].
    match goal with |- Result.bind ?search _ = _ => replace search with (Result.Success (F := Errors.MatchError.type) expected) end; easy.
Qed.

End FrontendCorrectness.
