From Linden Require Import Equiv EquivDef LWParameters RegexpTranslation
  Chars Tree Semantics FunctionalSemantics Groups GroupMapMS Regex
  EquivLemmas Utils MSInput Tactics ComputeIsTree GroupMapLemmas FunctionalUtils
  Parameters ResultTranslation.
From Warblre Require Import Patterns RegExpRecord Parameters Semantics
  Result Base Notation Match.
From Stdlib Require Import List Lia PeanoNat ZArith DecidableClass.
Import Match.
Import Notation.
Import ListNotations.
Import Patterns.
Import Result.
Import Result.Notations.

Local Open Scope result_flow.

(** * Main equivalence theorems, linking everything together *)

Section EquivMain.
  Context {params: LindenParameters}.

  (** ** Some initialization results *)
  Section InitState.

    (* Initial match state corresponding to a string, an index and a RegExpRecord. *)
    Definition init_match_state (str0: string) (idx: nat) (rer: RegExpRecord): MatchState :=
      let cap := List.repeat undefined (RegExpRecord.capturingGroupsCount rer) in
      match_state str0 (Z.of_nat idx) cap.

    (* Such an initial match state is equivalent to the empty group map... *)
    Lemma init_ms_equiv_empty:
      forall str0 idx rer, equiv_groupmap_ms GroupMap.empty (init_match_state str0 idx rer).
    Proof.
      intros str0 idx rer. unfold equiv_groupmap_ms.
      intro gid_prec. rewrite gm_find_empty. unfold init_match_state. simpl.
      rewrite nth_repeat. constructor.
    Qed.

    (* ... and to the empty open group list. *)
    Lemma empty_gm_equiv_empty_gl:
      group_map_equiv_open_groups GroupMap.empty nil.
    Proof.
      unfold group_map_equiv_open_groups. intros gid idx. rewrite gm_find_empty.
      split; try discriminate. intro H. inversion H.
    Qed.

    (* The initial input corresponding to a string str0 is compatible with str0. *)
    Lemma init_input_compat:
      forall str0, input_compat (init_input str0) str0.
    Proof.
      intro str0. unfold init_input. constructor. reflexivity.
    Qed.

    (* The initial input corresponding to a string str0 and the initial match state
       corresponding to str0 and index 0 match each other. *)
    Lemma init_ms_matches_inp:
      forall inp rer,
        ms_matches_inp (init_match_state (input_str inp) (idx inp) rer) inp.
    Proof.
      intros inp rer. destruct inp as [next pref]. unfold init_match_state. constructor; reflexivity.
    Qed.

  End InitState.


  (** ** Plugging the identity MatcherContinuation into a Matcher compiled from some root regexp *)
  Theorem equiv_matcher_idmcont_compsucc:
    forall wroot lroot rer m,
      (* For all pairs of equivalent Warblre and Linden regexes, *)
      equiv_regex wroot lroot ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      (* if compiling the Warblre regex into a Matcher m succeeds, *)
      Semantics.compileSubPattern wroot nil rer forward = Success m ->
      forall str0,
        (* then plugging the identity MatcherContinuation into the Matcher m yields a
           MatcherContinuation that is equivalent to matching the Linden regex, under any input string. *)
        equiv_cont rer (fun ms => m ms id_mcont) nil (forbidden_groups lroot) [Areg lroot] forward str0.
  Proof.
    intros wroot lroot rer m Hequiv Hcapcount Hcompsucc str0.
    pose proof equiv rer lroot wroot as Hequivm.
    unfold equiv_matcher in Hequivm.
    replace (forbidden_groups lroot) with (forbidden_groups lroot ++ []) by apply app_nil_r.
    eapply Hequivm; eauto.
    - constructor.
    - apply Hequiv.
    - apply id_equiv.
    - apply open_groups_disjoint_nil_l.
    - apply List.Disjoint_nil_r.
  Qed.

  Lemma idx_is_inbounds:
    forall inp,
      (idx inp <=? length (input_str inp)) = true.
  Proof.
    intros [next pref]. apply Nat.leb_le.
    simpl. rewrite length_app, length_rev. lia.
  Qed.

  Lemma input_compat_self:
    forall inp, input_compat inp (input_str inp).
  Proof.
    intro inp. destruct inp as [next pref]. constructor. simpl. reflexivity.
  Qed.

  (** ** Corollary assuming that both compiling the regex and matching a string do not yield errors. *)
  Corollary equiv_main':
    forall wroot lroot rer m,
      (* For all pairs of equivalent Warblre and Linden regexes, *)
      equiv_regex wroot lroot ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      (* if compiling the Warblre regex into a matcher m succeeds, *)
      Semantics.compilePattern wroot rer = Success m ->
      (* then for any input inp, *)
      forall inp res t,
        (* if running m on the input successfully yields a result res, *)
        m (input_str inp) (idx inp) = Success res ->
        (* then letting t be the priority tree corresponding to matching the Linden regex
           on the input inp, *)
        t = compute_tr rer [Areg lroot] inp GroupMap.empty forward ->
        (* this tree respects the Linden semantics and *)
        is_tree rer [Areg lroot] inp GroupMap.empty forward t /\
        (* the result res is equivalent to the first branch of the tree. *)
        equiv_res (first_leaf t inp) res.
  Proof.
    intros wroot lroot rer m Hequiv Hcapcount Hcompsucc inp res t Heqres Heqt.
    pose proof equiv_matcher_idmcont_compsucc wroot lroot rer as Hequivm.
    unfold Semantics.compilePattern in Hcompsucc.
    destruct Semantics.compileSubPattern as [msp|]; simpl in *; try discriminate.
    injection Hcompsucc as <-.
    rewrite idx_is_inbounds in Heqres. simpl in *.
    specialize (Hequivm msp Hequiv Hcapcount eq_refl (input_str inp)).
    unfold equiv_cont in Hequivm.
    set (fuel := 1 + actions_fuel [Areg lroot] inp forward).
    set (ms0 := init_match_state (input_str inp) (idx inp) rer). change (match_state _ _ _) with ms0 in Heqres.
    change (fun y : MatchState => _) with id_mcont in Heqres.
    specialize (Hequivm GroupMap.empty ms0 inp res fuel).
    pose proof functional_terminates rer [Areg lroot] inp GroupMap.empty forward fuel as Hcomputetreesucc.
    specialize_prove Hcomputetreesucc by lia.
    specialize (Hequivm t).
    specialize_prove Hequivm by apply input_compat_self.
    specialize_prove Hequivm by apply init_ms_equiv_empty.
    specialize_prove Hequivm by apply empty_gm_equiv_empty_gl.
    specialize_prove Hequivm by apply init_ms_matches_inp.
    specialize_prove Hequivm. { apply ms_valid_wrt_checks_Areg, ms_valid_wrt_checks_nil. }
    specialize_prove Hequivm by apply empty_gm_valid.
    specialize_prove Hequivm by apply noforb_empty.
    specialize (Hequivm Heqres).
    assert (Hcompute: compute_tree rer [Areg lroot] inp GroupMap.empty forward fuel = Some t). {
      unfold compute_tr in Heqt. unfold Nat.add in fuel. unfold fuel in Hcomputetreesucc.
      destruct compute_tree.
      - f_equal. congruence.
      - contradiction.
    }
    specialize (Hequivm Hcompute).
    split.
    - apply compute_is_tree with (fuel := fuel); auto.
    - exact Hequivm.
  Qed.

  (* The same, but with an initial input that is at the beginning of the input string *)
  Corollary equiv_main'_str0:
    forall wroot lroot rer m,
      (* For all pairs of equivalent Warblre and Linden regexes, *)
      equiv_regex wroot lroot ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      (* if compiling the Warblre regex into a matcher m succeeds, *)
      Semantics.compilePattern wroot rer = Success m ->
      (* then for any input string str0, *)
      forall str0 res t,
        (* if running m on str0 successfully yields a result res, *)
        m str0 0 = Success res ->
        (* then letting t be the priority tree corresponding to matching the Linden regex
           on the string str0, *)
        t = compute_tr rer [Areg lroot] (init_input str0) GroupMap.empty forward ->
        (* this tree respects the Linden semantics and *)
        is_tree rer [Areg lroot] (init_input str0) GroupMap.empty forward t /\
        (* the result res is equivalent to the first branch of the tree. *)
        equiv_res (first_branch t str0) res.
  Proof.
    intros wroot lroot rer m EQUIV CAPTURES COMP_SUCC str0 res t EXEC_SUCC Heqt.
    apply equiv_main' with (wroot := wroot) (m := m); auto.
  Qed.

  (** ** Main theorem *)
  Corollary equiv_main:
    forall wroot lroot rer inp,
      (* For any pair of equivalent Linden and Warblre regexes, *)
      equiv_regex wroot lroot ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      (* such that the Warblre regex passes the early errors check, *)
      EarlyErrors.Pass_Regex wroot nil ->
      exists m res,
        (* compiling the Warblre regex successfully yields a matcher m, *)
        Semantics.compilePattern wroot rer = Success m /\
        (* and for any input inp, running m on the input yields some result res, *)
        m (input_str inp) (idx inp) = Success res /\
        (* and letting t be the priority tree corresponding to matching the Linden regex on inp, *)
        forall t, t = compute_tr rer [Areg lroot] inp GroupMap.empty forward ->
          (* this tree respects the Linden semantics and *)
          is_tree rer [Areg lroot] inp GroupMap.empty forward t /\
          (* the result res is equivalent to the first branch of this tree. *)
          equiv_res (first_leaf t inp) res.
  Proof.
    intros wroot lroot rer inp Hequiv Hcapcount HearlyErrors.
    symmetry in Hcapcount.
    pose proof Compile.compilePattern_success wroot rer as Hcompilesucc.
    specialize (Hcompilesucc Hcapcount HearlyErrors). destruct Hcompilesucc as [m Hcompilesucc].
    exists m.
    pose proof Match.no_failure wroot rer (input_str inp) (idx inp) m HearlyErrors Hcapcount Hcompilesucc as Hresnofail.
    pose proof Match.termination wroot rer (input_str inp) (idx inp) m HearlyErrors Hcapcount Hcompilesucc as Hresterminates.
    specialize_prove Hresnofail. {
      apply Nat.leb_le. apply idx_is_inbounds.
    }
    destruct (m (input_str inp) (idx inp)) as [res|[]] eqn:Heqres.
    2,3: contradiction.
    exists res. split; [|split]; auto.
    intros t Heqt. eapply equiv_main'; eauto.
  Qed.

  (* Same, but with an input that is at the beginning of the input string *)
  Corollary equiv_main_str0:
    forall wroot lroot rer str0,
      (* For any pair of equivalent Linden and Warblre regexes, *)
      equiv_regex wroot lroot ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      (* such that the Warblre regex passes the early errors check, *)
      EarlyErrors.Pass_Regex wroot nil ->
      exists m res,
        (* compiling the Warblre regex successfully yields a matcher m, *)
        Semantics.compilePattern wroot rer = Success m /\
        (* for any input string str0, running m on str0 yields some result res, *)
        m str0 0 = Success res /\
        (* and letting t be the priority tree corresponding to matching the Linden regex on str0, *)
        forall t, t = compute_tr rer [Areg lroot] (init_input str0) GroupMap.empty forward ->
          (* this tree respects the Linden semantics and *)
          is_tree rer [Areg lroot] (init_input str0) GroupMap.empty forward t /\
          (* the result res is equivalent to the first branch of this tree. *)
          equiv_res (first_branch t str0) res.
  Proof.
    intros wroot lroot rer str0 EQUIV CAPTURES EE.
    apply equiv_main with (inp := init_input str0); auto.
  Qed.

  (* Computing the result of matching a regex with the given flags on the given input. *)
  Definition linden_result (rer: RegExpRecord) (r: regex) (inp: input) :=
    let t := compute_tr rer [Areg r] inp GroupMap.empty forward in
    first_leaf t inp.


  (* A version of Semantics.compilePattern that returns a dummy function when it fails. *)
  Definition compilePattern (wr: Patterns.Regex) (rer: RegExpRecord): list Character -> non_neg_integer -> option MatchState :=
    match Semantics.compilePattern wr rer with
    | Success m =>
      fun (str0: list Character) (i: non_neg_integer) =>
      match m str0 i with
      | Success res => res
      | Error _ => None
      end
    | Error _ => (fun _ _ => None)
    end.

  (* Using Warblre's matcher invariant, we show that running the result of compilePattern
  on an input string yields either None or a MatchState that has a capture list with the
  right size. *)
  Lemma compilePattern_preserves_groupcount:
    forall wroot rer m str0 i res,
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      StaticSemantics.earlyErrors wroot [] = Success false ->
      Semantics.compilePattern wroot rer = Success m ->
      m str0 i = Success res ->
      ms_num_groups res (RegExpRecord.capturingGroupsCount rer).
  Proof.
    intros wroot rer m str0 i res CAPTURES EE COMP_SUCC EXEC_SUCC.
    pose proof EarlyErrors.earlyErrors wroot EE as EE_ind.
    symmetry in CAPTURES.
    pose proof MatcherInvariant.compileSubPattern wroot rer CAPTURES EE_ind wroot [] eq_refl forward as MI.
    unfold Semantics.compilePattern in COMP_SUCC.
    destruct Semantics.compileSubPattern as [msub|] eqn:COMPSUB_SUCC; try discriminate. simpl in COMP_SUCC.
    specialize (MI msub eq_refl).
    injection COMP_SUCC as <-.
    destruct Nat.leb eqn:IN_BOUNDS; try discriminate. simpl in *.
    rewrite Nat.leb_le in IN_BOUNDS.
    pose proof initialState_validity str0 i rer IN_BOUNDS as INIT_VALID.
    specialize (MI _ (fun y : MatchState =>
               Coercions.wrap_option Errors.MatchError.type MatchState
                 (Coercions.MatchState_or_failure y)) INIT_VALID).
    simpl in MI.
    destruct MI as [MI | MI].
    - (* None *)
      rewrite MI in EXEC_SUCC. injection EXEC_SUCC as <-. constructor.
    - (* Some result *)
      destruct MI as [y [VALID_y [_ MI]]].
      rewrite <- MI in EXEC_SUCC. injection EXEC_SUCC as <-.
      unfold MatchState.Valid in VALID_y. constructor. tauto.
  Qed.

  (* Corollary where we reconstruct Warblre's output MatchState from Linden's output result,
  and we translate the Warblre regex to Linden. *)
  Corollary equiv_main_reconstruct:
    forall wroot lroot rer inp,
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      (* For any Warblre regex that passes the early errors check, *)
      StaticSemantics.earlyErrors wroot nil = Success false ->
      (* letting lroot be the corresponding Linden regex, *)
      lroot = warblre_to_linden' wroot 0 (buildnm wroot) ->
      (* Warblre's execution result on any input is equivalent to Linden's execution result on that input. *)
      (compilePattern wroot rer) (input_str inp) (idx inp) = to_MatchState (linden_result rer lroot inp) (RegExpRecord.capturingGroupsCount rer).
  Proof.
    intros wroot lroot rer str0 CAPTURES EE Heqlroot.
    pose proof earlyErrors_pass_translation_nomonad wroot EE as EQUIV. rewrite <- Heqlroot in EQUIV.
    pose proof EarlyErrors.earlyErrors wroot EE as EE_ind.
    pose proof equiv_main wroot lroot rer str0 EQUIV CAPTURES EE_ind as H.
    destruct H as [m [res [COMP_SUCC [EXEC_SUCC LW_EQUIV]]]].
    unfold compilePattern. rewrite COMP_SUCC, EXEC_SUCC.
    unfold linden_result. specialize (LW_EQUIV _ eq_refl). destruct LW_EQUIV as [_ LW_EQUIV].
    symmetry. apply to_MatchState_equal; auto. eauto using compilePattern_preserves_groupcount.
  Qed.

  (* The same, but with an input that is at the beginning of the input string. *)
  Corollary equiv_main_reconstruct_str0:
    forall wroot lroot rer str0,
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wroot nil ->
      (* For any Warblre regex that passes the early errors check, *)
      StaticSemantics.earlyErrors wroot nil = Success false ->
      (* letting lroot be the corresponding Linden regex, *)
      lroot = warblre_to_linden' wroot 0 (buildnm wroot) ->
      (* Warblre's execution result on string str0 is equivalent to Linden's execution result on string str0. *)
      (compilePattern wroot rer) str0 0 = to_MatchState (linden_result rer lroot (init_input str0)) (RegExpRecord.capturingGroupsCount rer).
  Proof.
    intros wroot lroot rer str0 CAPTURES EE Heqlroot.
    apply equiv_main_reconstruct with (inp := init_input str0); auto.
  Qed.

End EquivMain.
