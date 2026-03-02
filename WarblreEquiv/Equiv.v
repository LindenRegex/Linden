From Linden Require Import EquivDef RegexpTranslation Regex LWParameters
  Semantics FunctionalSemantics CharDescrCharSet Tactics
  NumericLemmas MSInput Chars Groups EquivLemmas Utils GroupMapLemmas
  LKFactorization StrictSuffix Parameters.
From Warblre Require Import Parameters Semantics RegExpRecord Patterns
  Node Result Notation Typeclasses List Base Node Match.
Import Patterns.
Import Result.Notations.
Import Notation.
Import NodeProps.Zipper.
Import Match.
From Stdlib Require Import ZArith PeanoNat Lia RelationClasses.

Local Open Scope result_flow.

(** * Core of the equivalence proof *)

Section Equiv.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* The identity continuation *)
  Definition id_mcont: MatcherContinuation :=
    fun x => Success (Some x).

  (* The identity continuation is equivalent to the empty list of actions with
  any list of forbidden groups and any list of open groups *)
  Lemma id_equiv:
    forall gl forbgroups dir str0,
      equiv_cont rer id_mcont gl forbgroups nil dir str0.
  Proof.
    intros. unfold equiv_cont.
    intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid
      Hnoforbidden; simpl; try discriminate.
    unfold id_mcont. intro H. injection H as <-. intro H. injection H as <-.
    simpl. constructor; assumption.
  Qed.

  (* Case when the repeat matcher is done iterating the regex because min = max = 0. *)
  Lemma repeatMatcher'_done_equiv:
    forall greedy parenIndex parenCount,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher rer m lreg dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall fuel, equiv_matcher rer
        (fun ms mc => Semantics.repeatMatcher' m 0 (NoI.N 0) greedy ms mc parenIndex parenCount fuel)
        (Regex.Quantified greedy 0 (NoI.N 0) lreg) dir.
  Proof.
    intros greedy parenIndex parenCount m lreg dir Hequiv Hgroupsvalid fuel.
    unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms inp res [|treefuel] t Hinpcompat Hgmms
      Hgmgl Hmsinp Hmsvalidchecks Hgmvalid Hnoforbidden; simpl; try discriminate.
    destruct fuel as [|fuel]; simpl; try discriminate.
    intros Hres Ht. eapply Hequivcont; eauto using ms_valid_wrt_checks_tail.
  Qed.

  (* Case when the repeat matcher can choose between iterating the sub-regexp and exiting the quantifier because min = 0 but max != 0. *)
  Lemma repeatMatcher'_free_equiv:
    forall greedy parenIndex parenCount,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher rer m lreg dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall fuel delta, equiv_matcher rer
        (fun ms mc => Semantics.repeatMatcher' m 0 delta greedy ms mc parenIndex parenCount fuel)
        (Regex.Quantified greedy 0 delta lreg) dir.
    Proof.
      (* We perform induction on the fuel. The case fuel = 0 is immediate. *)
      intros greedy parenIndex parenCount m lreg dir Hequiv Hgroupsvalid fuel.
      induction fuel as [|fuel IHfuel]. 1: discriminate.

      (* For delta = 0, we apply repeatMatcher'_done_equiv. *)
      intro delta.
      destruct (delta =? NoI.N (nat_to_nni 0))%NoI eqn:Hdeltazero.
      1: { rewrite noi_eqb_eq in Hdeltazero. subst delta. now apply repeatMatcher'_done_equiv. }
      simpl. rewrite Hdeltazero.
      (* Let mc be a continuation equivalent to actions act. *)
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
      (* We now prove that plugging mc into the repeat matcher yields a continuation that performs actions Areg (Quantified greedy 0 delta lreg)::act. *)
      (* Let ms be a valid input MatchState. *)
      unfold equiv_cont. intros gm ms inp res fueltree t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
      (* Assume that the capture reset succeeds. *)
      destruct List.Update.Nat.Batch.update as [cap'|] eqn:Heqcap'; simpl; try discriminate.
      (* mcloop performs a progress check then calls the repeat matcher with one less fuel and one less detlta. *)
      set (mcloop := fun y: MatchState => if (_ =? _)%Z then _ else _).
      set (msreset := match_state _ _ cap').
      (* We characterize mcloop. *)
      assert (Hmcloopequiv: equiv_cont rer mcloop gl forbgroups (Acheck inp::Areg (Regex.Quantified greedy 0 (delta - 1)%NoI lreg)::act)%list dir str0). {
        unfold equiv_cont. intros gm' ms' inp' res' fueltree' t' Hinp'compat Hgm'ms' Hgm'gl Hms'inp' Hms'checks Hgm'valid Hnoforbidden'.
        unfold mcloop.
        destruct (_ =? _)%Z eqn:Heqcheck.
        - (* Case 1: the input has not progressed *)
          intro H. injection H as <-.
          destruct fueltree' as [|fueltree']; simpl; try discriminate.
          rewrite ms_same_end_same_inp with (ms := ms') (ms' := ms) (inp := inp') (inp' := inp) (str0 := str0) by assumption.
          rewrite strict_suffix_irreflexive_bool.
          intro H. injection H as <-.
          constructor.
        - (* Case 2: the input has progressed *)
          set (delta' := if (delta =? +∞)%NoI then _ else _).
          specialize (IHfuel delta').
          unfold equiv_matcher in IHfuel. specialize (IHfuel str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj).
          unfold equiv_cont in IHfuel.
          intros Hres'succ.
          destruct fueltree' as [|fueltree']; simpl; try discriminate.
          (* Follows from Hms'checks and other hypotheses linking ms', inp', inp and str0 *)
          replace (is_strict_suffix inp' inp dir) with true. 2: { symmetry; eapply progresscheck_success_ssuffix; eauto. }
          destruct compute_tree as [treecont|] eqn:Htreecontsucc; simpl; try discriminate.
          intro H. injection H as <-.
          simpl. eapply IHfuel; eauto.
          all: replace (delta') with (delta-1)%NoI by now destruct delta.
          + eauto using ms_valid_wrt_checks_tail.
          + apply Htreecontsucc.
      }
      (* About m msreset mcloop *)
      unfold equiv_matcher in Hequiv. specialize (Hequiv str0 mcloop gl _ _ Hmcloopequiv Hgldisj).
      set (gmreset := GroupMap.reset (def_groups lreg) gm).
      unfold equiv_cont in Hequiv.
      specialize (Hequiv Hdef_forbid_disj gmreset msreset inp).
      destruct fueltree as [|fueltree]; simpl; try discriminate.

      (* About mc ms *)
      unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms inp).

      (* Deduplicate Linden part *)
      set (topt := (match compute_tree rer _ inp _ dir fueltree with | Some titer => _ | None => None end)).
      replace (match delta with | NoI.N n => _ | +∞ => _ end) with topt.
      2: { destruct delta as [[|delta']|]; simpl in *; try discriminate; reflexivity. }
      subst topt.

      destruct (compute_tree rer _ inp (GroupMap.reset _ _) dir fueltree) as [titer|] eqn:Htitersucc; simpl; try discriminate.
      destruct (compute_tree rer act inp gm dir fueltree) as [tskip|] eqn:Htskipsucc; simpl; try discriminate.
      intros Hres H. injection H as <-.
      specialize Hequiv with (fuel := fueltree) (t := titer) (1 := Hinpcompat)
        (2 := ltac:(eapply equiv_gm_ms_reset; eauto; reflexivity))
        (3 := ltac:(eapply equiv_open_groups_reset; eauto))
        (* msreset is valid with respect to the checks in act because of the
        assumption on ms and wrt the check with inp because msreset matches inp *)
        (5 := ltac:(eapply msreset_valid_checks; eauto; reflexivity))
        (6 := ltac:(now apply gm_reset_valid))
        (* gmreset does not contain any of the forbidden groups in lreg because
        those have just been reset, and does not contain any of the rest of the
        forbidden groups by assumption on gm *)
        (7 := ltac:(eapply noforb_reset; eauto; reflexivity)).

      (* Case analysis on greediness *)
      destruct greedy.
      - destruct (m msreset mcloop) as [resloop|] eqn:Hresloopsucc; simpl; try discriminate.
        specialize (Hequiv resloop).
        specialize_prove Hequiv. { destruct ms. eapply ms_matches_inp_capchg; eauto. }
        specialize (Hequiv eq_refl Htitersucc).
        destruct resloop as [resloopms|]; simpl in *.
        + injection Hres as <-. inversion Hequiv. simpl. unfold gmreset in H. rewrite <- H. simpl. constructor; assumption.
        + inversion Hequiv. simpl. unfold gmreset in H0. rewrite <- H0. simpl. eapply Hequivcont; eauto using ms_valid_wrt_checks_tail.

      - destruct (mc ms) as [resskip|] eqn:Hresskipsucc; simpl; try discriminate.
        (* Probably similar to greedy case *)
        specialize (Hequivcont resskip fueltree tskip Hinpcompat Hgmms Hgmgl Hmsinp).
        specialize_prove Hequivcont. { apply ms_valid_wrt_checks_tail in Hmschecks. auto. }
        specialize (Hequivcont Hgmvalid Hnoforbidden eq_refl Htskipsucc).
        specialize (Hequiv res).
        specialize_prove Hequiv. { destruct ms. eapply ms_matches_inp_capchg; eauto. }
        destruct resskip as [resskipms|]; simpl in *.
        + (* resskip is not None *)
          injection Hres as <-. inversion Hequivcont. simpl. constructor; assumption.
        + (* resloop is None *)
          inversion Hequivcont. simpl. specialize (Hequiv Hres Htitersucc). auto.
  Qed.

  (* General case; the proof below mostly deals with the case max > 0 and applies
  the two above lemmas otherwise *)
  Lemma repeatMatcher'_equiv:
    forall greedy parenIndex parenCount,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher rer m lreg dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall fuel min delta, equiv_matcher rer
        (fun ms mc => Semantics.repeatMatcher' m min (NoI.N min + delta)%NoI greedy ms mc parenIndex parenCount fuel)
        (Regex.Quantified greedy min delta lreg) dir.
  Proof.
    intros greedy parenIndex parenCount m lreg dir Hequiv Hgroupsvalid fuel.
    induction fuel as [|fuel IHfuel]. 1: discriminate.

    intros min delta.
    set (max := (NoI.N min + delta)%NoI).
    destruct (max =? NoI.N (nat_to_nni 0))%NoI eqn:Hmaxzero.
    1: { (* Apply repeatMatcher'_done_equiv *)
      rewrite noi_eqb_eq in Hmaxzero. rewrite Hmaxzero.
      unfold max in Hmaxzero. destruct delta as [delta|]; try discriminate.
      simpl in Hmaxzero. destruct min; try discriminate. destruct delta; try discriminate. apply repeatMatcher'_done_equiv; auto.
    }
    destruct min as [|min'].
    1: { (* Apply repeatMatcher'_free_equiv *)
      subst max. replace (NoI.N 0 + delta)%NoI with delta by now destruct delta.
      apply repeatMatcher'_free_equiv; auto.
    }
    (* Now we have min <> 0 *)
    unfold equiv_matcher.
    intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj. unfold equiv_cont.
    intros gm ms inp res fueltree t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
    simpl.
    rewrite Hmaxzero.
    replace (min' - 0) with min' by lia.
    destruct List.Update.Nat.Batch.update as [capreset|] eqn:Hcapreset; simpl; try discriminate.
    rewrite mini_plus_plusminus_one with (mini := min') (plus := delta) by reflexivity.
    specialize (IHfuel min' delta). unfold equiv_matcher in IHfuel. specialize (IHfuel str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj).
    unfold equiv_matcher in Hequiv. specialize (Hequiv str0 _ gl forbgroups _ IHfuel Hgldisj Hdef_forbid_disj).
    set (msreset := match_state _ _ capreset).
    unfold equiv_cont in Hequiv.
    specialize (Hequiv (GroupMap.reset (def_groups lreg) gm) msreset inp res).
    intro Hressucc. destruct fueltree as [|fueltree]; simpl; try discriminate.
    destruct (compute_tree rer _ inp (GroupMap.reset _ _) dir fueltree) as [titer|] eqn:Htitersucc; simpl; try discriminate.
    intro H. injection H as <-.
    simpl. eapply Hequiv; eauto.
    - eapply equiv_gm_ms_reset; eauto.
    - eapply equiv_open_groups_reset; eauto.
    - destruct ms. eapply ms_matches_inp_capchg; eauto.
    - unfold msreset. apply ms_valid_wrt_checks_inpcap with (winp' := MatchState.input ms) (cap' := MatchState.captures ms).
      do 2 apply ms_valid_wrt_checks_Areg. apply ms_valid_wrt_checks_tail in Hmschecks. now destruct ms.
    - now apply gm_reset_valid.
    - eapply noforb_reset; eauto.
  Qed.

  Corollary repeatMatcher_equiv:
    forall greedy parenIndex parenCount,
    forall (m: Matcher) (lreg: regex) (dir: Direction),
      equiv_matcher rer m lreg dir ->
      def_groups lreg = List.seq (parenIndex + 1) parenCount ->
      forall min delta, equiv_matcher rer
        (fun ms mc => Semantics.repeatMatcher m min (NoI.N min + delta)%NoI greedy ms mc parenIndex parenCount)
        (Regex.Quantified greedy min delta lreg) dir.
  Proof.
    intros greedy parenIndex parenCount m lreg dir Hequiv Hgroupsvalid min delta.
    unfold Semantics.repeatMatcher, equiv_matcher.
    intros. unfold equiv_cont. intros.
    eapply repeatMatcher'_equiv; eauto.
  Qed.



  (* Lemma for character set matchers *)
  Lemma charSetMatcher_equiv:
    forall charset cd,
      equiv_cd_charset rer cd charset ->
      forall dir inv,
        equiv_matcher rer (Semantics.characterSetMatcher rer charset inv dir) (Regex.Character (if inv then CdInv cd else cd)) dir.
  Proof.
    intros charset cd Hequiv dir inv.
    unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
    unfold Semantics.characterSetMatcher.
    set (nextend := if (dir ==? forward)%wt then _ else _).
    destruct ((nextend <? 0)%Z || _)%bool eqn:Hoob; simpl.
    - (* Out of bounds *)
      intro Hres. injection Hres as <-. destruct fuel as [|fuel]; try discriminate. simpl.
      erewrite read_oob_fail_bool by eauto.
      intro Heqt. injection Heqt as <-. simpl. constructor.
    - (* In bounds *)
      pose proof next_inbounds_nextinp ms inp dir nextend Hmsinp eq_refl Hoob as [inp' Hadv].
      destruct List.Indexing.Int.indexing as [chr|] eqn:Hgetchr; simpl; try discriminate.
      (* Some simplification *)
      set (exist_can := CharSet.exist_canonicalized rer charset (Character.canonicalize rer chr)).
      fold (negb inv). fold (negb exist_can).
      do 2 rewrite Tactics.BooleanSimplifier.identity_if.
      (* Case analysis on whether read fails *)
      destruct ((negb inv && negb exist_can) || (inv && exist_can))%bool eqn:Hmatch.
      + (* Read fails *)
        replace (if (_: bool) then _ else if (_: bool) then _ else _) with (Success (F := Errors.MatchError.type) (@None MatchState)).
        2: {
          destruct (negb inv && negb exist_can)%bool. 1: reflexivity.
          destruct (inv && exist_can)%bool. 1: reflexivity. discriminate.
        }
        intro Hcontsucc. injection Hcontsucc as <-.
        destruct fuel as [|fuel]; simpl; try discriminate.
        destruct inv; simpl in *.
        * rewrite (proj2 (read_char_success' rer ms inp chr _ _ dir inp' nextend Hequiv Hmsinp eq_refl Hgetchr Hmatch Hadv)).
          intro H. injection H as <-. simpl. constructor.
        * rewrite Bool.orb_false_r in Hmatch.
          apply Bool.negb_true_iff in Hmatch. rewrite (proj1 (read_char_fail' rer ms chr inp inp' dir _ _ nextend Hequiv Hmsinp eq_refl Hgetchr Hmatch Hadv)).
          intro H. injection H as <-. simpl. constructor.
      + (* Read succeeds *)
        apply Bool.orb_false_elim in Hmatch. destruct Hmatch as [Hmatch1 Hmatch2].
        rewrite Hmatch1, Hmatch2.
        intro Hcontsucc. destruct fuel as [|fuel]; simpl; try discriminate.
        replace (read_char rer (if inv then CdInv cd else cd) inp dir) with (Some (chr, inp')).
        2: {
          symmetry. destruct inv; simpl in *.
          - exact (proj2 (read_char_fail' rer ms chr inp inp' dir _ _ nextend Hequiv Hmsinp eq_refl Hgetchr Hmatch2 Hadv)).
          - apply Bool.negb_false_iff in Hmatch1. exact (proj1 (read_char_success' rer ms inp chr _ _ dir inp' nextend Hequiv Hmsinp eq_refl Hgetchr Hmatch1 Hadv)).
        }
        destruct compute_tree as [tcont|] eqn:Htcont; simpl; try discriminate.
        intro H. injection H as <-. simpl.
        unfold equiv_cont in Hequivcont.
        rewrite advance_input_success with (nexti := inp') by assumption.
        eapply Hequivcont with (ms := match_state (MatchState.input ms) nextend (MatchState.captures ms)); eauto.
        3: {
          apply ms_valid_wrt_checks_tail in Hmschecks. destruct dir; simpl in *; constructor; unfold nextend.
          - specialize (Hmschecks inpcheck H). inversion Hmschecks. simpl. lia.
          - specialize (Hmschecks inpcheck H). inversion Hmschecks. simpl. lia.
        }
        (* 3: advancing the end index does not make validity wrt checks false *)
        1: eauto using advance_input_compat.
        eapply ms_matches_inp_adv; eauto. unfold MSInput.advance_ms. now destruct dir.
  Qed.

  Lemma characterClassEscape_equiv:
    forall (nm:namedmap) (lroot: regex) (wroot: Regex)
      (root_equiv: equiv_regex wroot lroot),
    forall esc wreg lreg ctx,
      wreg = AtomEsc (ACharacterClassEsc esc) ->
      Root wroot (wreg, ctx) ->
      equiv_regex' wreg lreg (StaticSemantics.countLeftCapturingParensBefore wreg ctx) nm ->
      forall m dir,
        Semantics.compileSubPattern wreg ctx rer dir = Success m ->
        equiv_matcher rer m lreg dir.
  Proof.
    intros nm lroot wroot root_equiv esc wreg lreg ctx -> Hroot Hequiv m dir Hcompilesucc.
    inversion Hequiv.
    - subst esc0 lreg. pose proof equiv_cd_CharacterClassEscape rer esc cd H0 as [a [HcompileCharSet Hequivcdcs]].
      unfold Semantics.compileSubPattern, Semantics.compileToCharSet, Coercions.ClassAtom_to_range, Coercions.ClassEscape_to_ClassAtom, Coercions.CharacterClassEscape_to_ClassEscape in Hcompilesucc.
      setoid_rewrite HcompileCharSet in Hcompilesucc. simpl in Hcompilesucc.
      injection Hcompilesucc as <-. apply charSetMatcher_equiv with (inv := false); auto. rewrite CharSet.union_empty. 1: auto.
      exact CharSet.empty_spec.
    - inversion H1; congruence.
    - inversion H; congruence.
  Qed.

  Lemma characterEscape_equiv:
    forall (lroot: regex) (wroot: Regex)
      (root_equiv: equiv_regex wroot lroot),
    forall esc cd ctx,
      Root wroot (AtomEsc (ACharacterEsc esc), ctx) ->
      equiv_CharacterEscape esc cd ->
      forall m dir,
        Semantics.compileSubPattern (AtomEsc (ACharacterEsc esc)) ctx rer dir = Success m ->
        equiv_matcher rer m (Regex.Character cd) dir.
  Proof.
    intros lroot wroot Hequivroot esc cd ctx Hroot Hequiv m dir.
    inversion Hequiv as [controlesc cd0 Hequiv'' Heqesc Heqcd0 | l cd0 Hequiv'' Heqesc Heqcd0 | Heqesc Heqcd | d1 d2 Heqesc Heqcd | c Heqesc Heqcd | head tail Heqesc Heqcd | hex Heqesc Heqcd | c Heqesc Heqcd].
    - inversion Hequiv'' as [Heqcontrolesc Heqcd | Heqcontrolesc Heqcd | Heqcontrolesc Heqcd | Heqcontrolesc Heqcd | Heqcontrolesc Heqcd]; simpl; intro H; injection H as <-;
      eapply charSetMatcher_equiv with (inv := false); eauto; unfold nat_to_nni; rewrite Character.numeric_pseudo_bij; apply equiv_cd_single.
    - inversion Hequiv'' as [l0 i Heqi Heql0 Heqcd].
      simpl. rewrite <- Heqi. intro H. injection H as <-.
      eapply charSetMatcher_equiv with (inv := false); eauto. apply equiv_cd_single.
    - simpl; intro H; injection H as <-; eapply charSetMatcher_equiv with (inv := false); eauto; unfold nat_to_nni; rewrite Character.numeric_pseudo_bij; apply equiv_cd_single.
    - simpl. intro H. injection H as <-. eapply charSetMatcher_equiv with (inv := false); eauto. apply equiv_cd_single.
    - simpl. intro H. injection H as <-. eapply charSetMatcher_equiv with (inv := false); eauto; unfold nat_to_nni; rewrite Character.numeric_pseudo_bij; apply equiv_cd_single.
    - simpl. intro H. injection H as <-. eapply charSetMatcher_equiv with (inv := false); eauto. apply equiv_cd_single.
    - simpl. intro H. injection H as <-. eapply charSetMatcher_equiv with (inv := false); eauto. apply equiv_cd_single.
    - simpl. intro H. injection H as <-. eapply charSetMatcher_equiv with (inv := false); eauto; unfold nat_to_nni; rewrite Character.numeric_pseudo_bij; apply equiv_cd_single.
  Qed.

  Lemma characterClass_equiv:
    forall (lroot: regex) (wroot: Regex)
      (root_equiv: equiv_regex wroot lroot),
      forall cc cd ctx,
        Root wroot (CharacterClass cc, ctx) ->
        equiv_CharClass cc cd ->
        forall m dir,
          Semantics.compileSubPattern (CharacterClass cc) ctx rer dir = Success m ->
          equiv_matcher rer m (Regex.Character cd) dir.
  Proof.
    intros lroot wroot root_equiv cc cd ctx Hroot Hequiv' m dir.
    inversion Hequiv' as [crs cd0 Hequiv'' Heqcc' Heqcd0 | crs cd0 Hequiv'' Heqcc' Heqcd0]; simpl.
    - pose proof equiv_cd_ClassRanges rer crs cd Hequiv'' as [a [Heqa Hequiva]]. setoid_rewrite Heqa. simpl.
      intro H. injection H as <-. eapply charSetMatcher_equiv with (inv := false); eauto.
    - subst cd. pose proof equiv_cd_ClassRanges rer crs cd0 Hequiv'' as [a [Heqa Hequiva]]. setoid_rewrite Heqa. simpl.
      intro H. injection H as <-. eapply charSetMatcher_equiv with (inv := true); eauto.
  Qed.


  (* Lemma for backreferences *)
  Lemma backref_equiv:
    forall gid dir,
      equiv_matcher rer (Semantics.backreferenceMatcher rer gid dir)
        (Backreference (positive_to_nat gid)) dir.
  Proof.
    intros. unfold equiv_matcher.
    intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms [next pref] res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforb; try discriminate.
    pose proof ms_matches_inp_inbounds ms _ Hmsinp as Hmsinb.
    simpl in *. unfold Semantics.backreferenceMatcher, read_backref.
    destruct indexing as [r|] eqn:Heqr; simpl; try discriminate.
    destruct r as [[startIdx endIdx]|] eqn:Hr; simpl.
    - (* Range is defined *)
      pose proof equiv_gm_ms_indexing_find_nonneg gm ms gid startIdx endIdx Hgmms Heqr as [Hfind [HstartIdxnneg HendIdxnneg]].
      rewrite Hfind.
      set (rlen := (endIdx - startIdx)%Z).
      assert (Hrlennneg: (rlen >= 0)%Z). {
        unfold gm_valid in Hgmvalid. specialize (Hgmvalid (positive_to_nat gid)).
        rewrite Hfind in Hgmvalid. inversion Hgmvalid. lia.
      }
      replace (Z.to_nat endIdx - Z.to_nat startIdx) with (Z.to_nat rlen) by lia.
      destruct dir; simpl.
      + (* Forward *)
        set (endMatch := (MatchState.endIndex ms + rlen)%Z).
        replace (endMatch <? 0)%Z with false by lia. simpl.
        assert (Hoobiff: (endMatch >? Z.of_nat (length (MatchState.input ms)))%Z = true <->
          (Z.to_nat rlen >? length next) = true) by eauto using endMatch_oob_forward.
        (*simpl in Hoobiff.*)
        rewrite <- Bool.eq_iff_eq_true in Hoobiff. setoid_rewrite <- Hoobiff.
        destruct Z.gtb eqn:Hoob.
        * (* Out of bounds *)
          intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
        * (* In bounds *)
          destruct List.Exists.exist as [existsdiff|] eqn:Hexistsdiffres; simpl; try discriminate.
          assert (Hexistsdiffiff : existsdiff = true <-> (List.map (Character.canonicalize rer) (List.firstn (Z.to_nat rlen) next) ==? List.map (Character.canonicalize rer) (substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx)))%wt = false) by eauto using exists_diff_iff.
          rewrite Bool.negb_involutive_reverse with (b := existsdiff) in Hexistsdiffiff.
          rewrite Bool.negb_true_iff in Hexistsdiffiff.
          destruct existsdiff.
          -- (* Some character is different *)
             destruct Hexistsdiffiff as [Hexistsdiffiff _]. rewrite Hexistsdiffiff by reflexivity.
             intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
          -- (* No character is different *)
             assert (Hfirstn_next_substr: (List.map (Character.canonicalize rer) (List.firstn (Z.to_nat rlen) next) ==?
               List.map (Character.canonicalize rer) (substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx)))%wt = true). {
               symmetry. destruct EqDec.eqb; try reflexivity.
               destruct Hexistsdiffiff. discriminate (H0 eq_refl).
             }
             rewrite Hfirstn_next_substr. rewrite EqDec.inversion_true in Hfirstn_next_substr.
             set (ms' := match_state _ _ _). set (inp' := Input _ _).
             assert (Hms'inp': ms_matches_inp ms' inp'). { eapply msinp_backref_fwd; eauto. all: reflexivity. }
             assert (Hinp'compat: input_compat inp' str0). { eapply msinp_backref_fwd with (next := next) (pref := pref); eauto. reflexivity. }
             intro Hres.
             destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
             intro H. injection H as <-. simpl.
             unfold equiv_cont in Hequivcont.
             (*rewrite <- Hfirstn_next_substr.*)
             replace (length (List.firstn _ next)) with (Z.to_nat rlen).
             2: { symmetry in Hoobiff. rewrite Nat.leb_gt in Hoobiff. rewrite List.length_firstn. lia. }
             fold inp'.
             apply Hequivcont with (ms := ms') (fuel := fuel); auto.
             (* Remains to prove that the new MatchState remains valid with respect to the checks in act *)
             apply ms_valid_wrt_checks_tail in Hmschecks.
             unfold ms_valid_wrt_checks. intros inpcheck Hcheckin.
             specialize (Hmschecks inpcheck Hcheckin). inversion Hmschecks as [ms0 inpcheck0 Hendge |]. subst ms0 inpcheck0.
             constructor.
             assert (MatchState.endIndex ms' >= MatchState.endIndex ms)%Z. {
               unfold ms', endMatch. simpl. lia.
             }
             lia.
      + (* Backward *)
        replace (MatchState.endIndex ms - rlen >? Z.of_nat (length (MatchState.input ms)))%Z with false by lia.
        rewrite Bool.orb_false_r.
        assert (Hoobiff: (MatchState.endIndex ms - rlen <? 0)%Z = true <-> (Z.to_nat rlen >? length pref) = true) by eauto using beginMatch_oob_backward.
        rewrite <- Bool.eq_iff_eq_true in Hoobiff. (*simpl in Hoobiff.*)
        setoid_rewrite <- Hoobiff.
        destruct Z.ltb.
        * (* Out of bounds *)
          intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
        * (* In bounds *)
          destruct List.Exists.exist as [existsdiff|] eqn:Hexistsdiffres; simpl; try discriminate.
          assert (HbeginMatchinb: (MatchState.endIndex ms - rlen >= 0)%Z). {
            (* The fact that List.Exists.exist succeeds means that indexing the first character succeeds *)
            unfold List.Range.Int.Bounds.range in Hexistsdiffres. replace (rlen - 0)%Z with rlen in Hexistsdiffres by lia.
            destruct (Z.to_nat rlen) eqn:Hrlennat.
            1: { replace rlen with 0%Z by lia. lia. }
            simpl in Hexistsdiffres.
            destruct List.Indexing.Int.indexing in Hexistsdiffres; simpl in *; try discriminate.
            replace (Z.min _ _ + 0)%Z with (MatchState.endIndex ms - rlen)%Z in Hexistsdiffres by lia.
            destruct List.Indexing.Int.indexing as [gi|] eqn:Hindexingfirst in Hexistsdiffres; simpl in *; try discriminate.
            apply List.Indexing.Int.success_bounds in Hindexingfirst. lia.
          }
          assert (Hexistsdiffiff : existsdiff = true <-> (List.map (Character.canonicalize rer) (List.rev (List.firstn (Z.to_nat rlen) pref)) ==? List.map (Character.canonicalize rer) (substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx)))%wt = false) by
            eauto using exists_diff_iff_bwd.
          rewrite Bool.negb_involutive_reverse with (b := existsdiff) in Hexistsdiffiff.
          rewrite Bool.negb_true_iff in Hexistsdiffiff.
          destruct existsdiff.
          -- (* Some character is different *)
             destruct Hexistsdiffiff as [Hexistsdiffiff _]. rewrite Hexistsdiffiff by reflexivity.
             intros H1 H2. injection H1 as <-. injection H2 as <-. constructor.
          -- (* No character is different *)
             assert (Hfirstn_pref_substr: (List.map (Character.canonicalize rer) (List.rev (List.firstn (Z.to_nat rlen) pref)) ==?
               List.map (Character.canonicalize rer) (substr (Input next pref) (Z.to_nat startIdx) (Z.to_nat endIdx)))%wt = true). {
               symmetry. destruct EqDec.eqb; try reflexivity.
               destruct Hexistsdiffiff. discriminate (H0 eq_refl).
             }
             rewrite Hfirstn_pref_substr. rewrite EqDec.inversion_true in Hfirstn_pref_substr.
             set (ms' := match_state _ _ _). set (inp' := Input _ _).
             assert (Hms'inp': ms_matches_inp ms' inp'). { eapply msinp_backref_bwd with (next := next) (pref := pref) (rlen := rlen); eauto. reflexivity. }
             assert (Hinp'compat: input_compat inp' str0). { eapply msinp_backref_bwd with (next := next) (pref := pref) (rlen := rlen); eauto. }
             intro Hres.
             destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
             intro H. injection H as <-. simpl.
             unfold equiv_cont in Hequivcont.
             replace (length (List.rev _)) with (Z.to_nat rlen).
             2: { symmetry in Hoobiff. rewrite Nat.leb_gt in Hoobiff. rewrite List.length_rev, List.length_firstn. lia. }
             fold inp'.
             apply Hequivcont with (ms := ms') (fuel := fuel); auto.
             (* Remains to prove that the new MatchState remains valid with respect to the checks in act *)
             apply ms_valid_wrt_checks_tail in Hmschecks.
             unfold ms_valid_wrt_checks. intros inpcheck Hcheckin.
             specialize (Hmschecks inpcheck Hcheckin). inversion Hmschecks as [|ms0 inpcheck0 Hendge]. subst ms0 inpcheck0.
             constructor.
             assert (MatchState.endIndex ms' <= MatchState.endIndex ms)%Z. {
               unfold ms'. simpl. lia.
             }
             lia.
    - (* Range is undefined *)
      destruct GroupMap.find as [[startIdx [endIdx|]]|] eqn:Hfind.
      + exfalso. eapply equiv_gm_ms_indexing_none; eauto.
      + destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intros Hres H. injection H as <-.
        simpl.
        replace (match dir with | forward | _ => Input next pref end) with (Input next pref) by now destruct dir.
        apply Hequivcont with (ms := ms) (fuel := fuel); auto.
        now apply ms_valid_wrt_checks_tail in Hmschecks.
      + (* Copy-pasting *)
        destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intros Hres H. injection H as <-.
        simpl.
        replace (match dir with | forward | _ => Input next pref end) with (Input next pref) by now destruct dir.
        apply Hequivcont with (ms := ms) (fuel := fuel); auto.
        now apply ms_valid_wrt_checks_tail in Hmschecks.
  Qed.

  (* Groups, whether named or unnamed (factorization) *)
  Lemma equiv_groups:
    forall wr lr gn_opt n ctx nm
      (IH: forall m dir,
        Semantics.compileSubPattern wr (Group_inner gn_opt :: ctx) rer dir = Success m ->
        equiv_matcher rer m lr dir)
      (Heqn: n = StaticSemantics.countLeftCapturingParensBefore (Group gn_opt wr) ctx)
      (EQUIV: equiv_regex' wr lr (S n) nm),
    forall m dir,
      Semantics.compileSubPattern (Group gn_opt wr) ctx rer dir = Success m ->
      equiv_matcher rer m (Regex.Group (S n) lr) dir.
  Proof.
    intros. simpl in *.
    destruct Semantics.compileSubPattern as [msub|] eqn:COMP_SUB; try discriminate.
    simpl in H. specialize (IH msub dir COMP_SUB).
    injection H as <-.
    unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
    unfold equiv_cont. intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden; simpl; try discriminate.
    set (mcclose := fun (y: MatchState) => _).
    assert (Hequivmcclose: equiv_cont rer mcclose ((S n, idx inp)::gl)%list forbgroups (Aclose (S n)::act)%list dir str0). {
      unfold equiv_cont. intros gm' ms' inp' res' [|fuel'] t' Hinp'compat Hgm'ms' Hgm'gl' Hms'inp' Hms'checks Hgm'valid Hnoforbidden'; simpl; try discriminate.
      destruct compute_tree as [treecont|] eqn:Htreecont; simpl; try discriminate.
      unfold mcclose.
      set (rres := if (dir ==? forward)%wt then _ else _). destruct rres as [r|] eqn:Hrres; simpl; try discriminate.
      replace (StaticSemantics.countLeftCapturingParensBefore _ ctx + 1) with (S n) by lia.
      simpl. replace (n - 0) with n by lia.
      destruct List.Update.Nat.One.update as [cap'|] eqn:Heqcap'; simpl; try discriminate.
      intros Hres' Ht'. injection Ht' as <-. simpl.
      eapply Hequivcont with (ms := match_state (MatchState.input ms) (MatchState.endIndex ms') cap'); eauto.
      - eapply equiv_gm_ms_close_group; eauto.
      - eapply equiv_open_groups_close_group; eauto.
      - eapply ms_matches_inp_close_group; eauto.
      - apply ms_valid_wrt_checks_inpcap with (winp' := MatchState.input ms') (cap' := MatchState.captures ms'). destruct ms'; simpl. eauto using ms_valid_wrt_checks_tail.
      - auto using gm_close_valid.
      - eauto using noforb_close_group.
    }
    destruct compute_tree as [treecont|] eqn:Htreecont; simpl; try discriminate.
    intros Hres H. injection H as <-. simpl.
    eapply IH; eauto.
    + eauto using open_groups_disjoint_open_group. (* Group list disjointness; follows from Hgldisj and Hequiv (for group S n) *)
    + eauto using disj_forbidden_child, Child_Group.
    + eauto using equiv_gm_ms_open_group. (* Group map equivalence after opening a group; follows from Hnoforbidden (!) *)
    + eauto using equiv_gm_gl_open_group. (* Group map equivalence to open groups after opening a group *)
    + apply ms_valid_wrt_checks_Areg, ms_valid_wrt_checks_Aclose. eauto using ms_valid_wrt_checks_tail.
    + auto using gm_open_valid.
    + eauto using noforb_open_group. (* Follows from Hnoforbidden (groups other than S n), Hdef_forbid_disj and Hequiv (S n) *)
  Qed.

  (* Main equivalence theorem: *)
  Theorem equiv:
    forall (lroot: regex) (wroot: Regex)
      (* Let lroot and wroot be a pair of equivalent regexes. *)
      (root_equiv: equiv_regex wroot lroot),
      (* Then for any sub-regex wreg of the root Warblre regex, *)
    forall (wreg: Regex) (lreg: regex) ctx
      (Hroot: Root wroot (wreg, ctx))
      (* and any Linden regex lreg that is equivalent to this sub-regex with the right number of left capturing parentheses before, *)
      (Hequiv: equiv_regex' wreg lreg (StaticSemantics.countLeftCapturingParensBefore wreg ctx) (buildnm wroot)),
      forall m dir
        (* if compileSubPattern with direction dir yields a Matcher for regex wreg, *)
        (Hcompsucc: Semantics.compileSubPattern wreg ctx rer dir = Success m),
        (* then this Matcher is equivalent to the regex lreg and direction dir. *)
        equiv_matcher rer m lreg dir.
  Proof.
    do 8 intro.
    remember (StaticSemantics.countLeftCapturingParensBefore _ _) as n in Hequiv.
    remember (buildnm wroot) as nm in Hequiv.
    revert ctx Hroot Heqn Heqnm.
    induction Hequiv as [
      n nm |
      n c nm |
      n nm |
      n gid nm |
      n nm name gid NAME |
      esc cd n nm Hequivesc |
      esc cd n nm Hequivesc |
      cc cd n nm Hequivcc |
      n wr1 wr2 lr1 lr2 nm Hequiv1 IH1 Hequiv2 IH2 |
      n wr1 wr2 lr1 lr2 nm Hequiv1 IH1 Hequiv2 IH2 |
      n wr lr wquant lquant wgreedylazy greedy nm Hequiv IH Hequivquant Hequivgreedy |
      n wr lr nm Hequiv IH |
      name n wr lr nm Hgid Hequiv IH |
      n wr lr wlk llk nm Hequiv IH Hequivlk |
      n wr lanchor nm Hanchequiv
    ].

    - (* Epsilon *)
      intros ctx _ _ _ m dir. simpl.
      intro. injection Hcompsucc as <-.
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont _ _.
      unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden Hmcsucc.
      destruct fuel as [|fuel]; try discriminate.
      simpl.
      intro Hsubtreesucc.
      eapply Hequivcont; eauto using ms_valid_wrt_checks_tail.

    - (* Character *)
      intros ctx Hroot Heqn Heqnm m dir Hcompsucc.
      injection Hcompsucc as <-.
      apply charSetMatcher_equiv with (inv := false); auto. apply equiv_cd_single.

    - (* Dot *)
      intros ctx Hroot Heqn Heqnm m dir Hcompsucc.
      injection Hcompsucc as <-.
      apply charSetMatcher_equiv with (inv := false); auto. destruct (RegExpRecord.dotAll rer) eqn:HdotAll.
      + apply equiv_cd_dot_dotAll. auto.
      + apply equiv_cd_dot_noDotAll. auto.

    - (* Backreference *)
      intros ctx Hroot Heqn Heqnm m dir. simpl.
      destruct Nat.leb eqn:Hgidinbounds; try discriminate. simpl.
      intro H. injection H as <-.
      auto using backref_equiv.

    - (* Named Backreference *)
      intros ctx Hroot Heqn Heqnm m dir. simpl.
      destruct (length _ =? 1) eqn:Hnumgs; simpl; try discriminate.
      rewrite PeanoNat.Nat.eqb_eq in Hnumgs.
      destruct List.Unique.unique as [gs|err] eqn:Heqgs; try discriminate.
      unshelve erewrite (buildnm_gsmatch_unique _ nm (AtomEsc (GroupEsc name)) ctx name gs eq_refl Hnumgs _ Heqgs) in NAME.
      1: { rewrite <- Hroot. auto. }
      simpl. injection NAME as ->.
      destruct NonNegInt.to_positive as [gid'|] eqn:Hgidpos; try discriminate. simpl.
      intro H. injection H as <-.
      rewrite <- (NonNegInt.to_positive_soundness gid gid' Hgidpos).
      auto using backref_equiv.

    - (* AtomEsc (ACharacterClassEsc esc); idem *)
      intros ctx Hroot Heqn Heqnm m dir Hcompsucc.
      eapply characterClassEscape_equiv with (nm := nm); eauto. constructor. assumption.

    - (* AtomEsc (ACharacterEsc esc); idem *)
      intros ctx Hroot Heqn Heqnm m dir Hcompsucc.
      eapply characterEscape_equiv; eauto.

    - (* CharacterClass; idem *)
      intros ctx Hroot Heqn Heqnm m dir Hcompsucc.
      eapply characterClass_equiv; eauto.

    - (* Disjunction *)
      intros ctx Hroot Heqn Heqnm m dir.
      simpl.
      (* Compilation of the two sub-regexes succeeds *)
      destruct Semantics.compileSubPattern as [m1|] eqn:Hcompsucc1; simpl; try discriminate.
      destruct (Semantics.compileSubPattern _ (Disjunction_right _ :: ctx)) as [m2|] eqn:Hcompsucc2; simpl; try discriminate.
      intro H. injection H as <-.
      (* Specialize the induction hypotheses naturally *)
      specialize (IH1 (Disjunction_left wr2 :: ctx)%list).
      specialize_prove IH1 by eauto using Down.same_root_down0, Down_Disjunction_left.
      specialize_prove IH1. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia. }
      specialize (IH1 Heqnm m1 dir Hcompsucc1).
      specialize (IH2 (Disjunction_right wr1 :: ctx)%list).
      specialize_prove IH2 by eauto using Down.same_root_down0, Down_Disjunction_right.
      specialize_prove IH2. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. erewrite num_groups_equiv by eauto. lia. }
      specialize (IH2 Heqnm m2 dir Hcompsucc2).
      (* Introduce the required variables *)
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
      unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
      unfold equiv_matcher in IH1, IH2.
      (* Specialize the induction hypotheses again naturally *)
      specialize (IH1 str0 mc gl forbgroups act Hequivcont).
      specialize_prove IH1 by eauto using disj_parent_disj_child, Child_Disjunction_left.
      specialize_prove IH1 by eauto using disj_forbidden_child, Child_Disjunction_left.
      specialize (IH2 str0 mc gl forbgroups act Hequivcont).
      specialize_prove IH2 by eauto using disj_parent_disj_child, Child_Disjunction_right.
      specialize_prove IH2 by eauto using disj_forbidden_child, Child_Disjunction_right.
      unfold equiv_cont in IH1, IH2.
      (* Eliminate failing cases *)
      destruct fuel as [|fuel]; simpl; try discriminate.
      destruct m1 as [res1|] eqn:Hres1; simpl; try discriminate.
      destruct compute_tree as [t1|] eqn:Ht1; simpl; try discriminate.
      destruct (compute_tree rer (Areg lr2 :: act)%list _ _ _ _) as [t2|] eqn:Ht2; simpl; try discriminate.
      specialize (IH1 gm ms inp res1 fuel t1 Hinpcompat Hgmms Hgmgl Hmsinp).
      specialize_prove IH1. { apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail. }
      specialize (IH1 Hgmvalid).
      specialize_prove IH1. { apply noforbidden_child with (parent := Regex.Disjunction lr1 lr2).
        - apply Child_Disjunction_left.
        - intros [greedy [min [delta [rsub Habs]]]]; discriminate.
        - assumption. }
      specialize (IH1 Hres1 Ht1).
      (* Case analysis on whether the left branch matches *)
      destruct res1 as [msres1|] eqn:Hmsres1; simpl.
      + (* Left choice matches *)
        intro H. injection H as <-. intro H. injection H as <-.
        simpl.
        inversion IH1 as [ | gm1 msres1' IH1' Heqgm1 Heqmsres1' ]. simpl. constructor; assumption.
      + (* Left choice does not match *)
        rename res into res2.
        intros Hres2 H. injection H as <-. simpl.
        inversion IH1 as [ HNone1 | ]. simpl.
        eapply IH2; eauto.
        * apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail.
        * apply noforbidden_child with (parent := Regex.Disjunction lr1 lr2).
          -- apply Child_Disjunction_right.
          -- intros [greedy [min [delta [rsub Habs]]]]; discriminate.
          -- assumption.

    - (* Sequence *)
      intros ctx Hroot Heqn Heqnm m dir. simpl.
      (* Compilation of the two sub-regexes succeeds *)
      destruct Semantics.compileSubPattern as [m1|] eqn:Hcompsucc1; simpl; try discriminate.
      destruct (Semantics.compileSubPattern _ (Seq_right _ :: ctx)%list) as [m2|] eqn:Hcompsucc2; simpl; try discriminate.
      (* Specialize the induction hypotheses naturally *)
      specialize (IH1 (Seq_left wr2 :: ctx)%list).
      specialize_prove IH1 by eauto using Down.same_root_down0, Down_Seq_left.
      specialize_prove IH1. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia. }
      specialize (IH1 Heqnm m1 dir Hcompsucc1).
      specialize (IH2 (Seq_right wr1 :: ctx)%list).
      specialize_prove IH2 by eauto using Down.same_root_down0, Down_Seq_right.
      specialize_prove IH2. { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. erewrite num_groups_equiv by eauto. lia. }
      specialize (IH2 Heqnm m2 dir Hcompsucc2).
      intro Heqm.
      unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
      unfold equiv_cont. intros gm ms inp res [|fuel] t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden; try discriminate; simpl.
      (* Two similar reasonings for each direction *)
      destruct dir; injection Heqm as <-.
      + (* Forward *)
        set (mc2 := fun s => _).
        assert (Hequivcont2: equiv_cont rer mc2 gl (forbidden_groups lr2 ++ forbgroups) (Areg lr2 :: act)%list forward str0). {
          unfold equiv_cont. clear gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
          intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hnoforbidden. unfold mc2.
          intros Hres Ht. eapply IH2; eauto.
          1: eauto using disj_parent_disj_child, Child_Sequence_right.
          eauto using disj_forbidden_child, Child_Sequence_right.
        }
        intros Hres Ht. eapply IH1; eauto.
        * eauto using disj_parent_disj_child, Child_Sequence_left.
        * eauto using disj_forbidden_seq.
        * do 2 apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail.
        * now apply noforbidden_seq.

      + (* Backward *)
        set (mc1 := fun s => _).
        assert (Hequivcont1: equiv_cont rer mc1 gl (forbidden_groups lr1 ++ forbgroups) (Areg lr1 :: act)%list backward str0). {
          unfold equiv_cont. clear gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforbidden.
          intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hnoforbidden. unfold mc1.
          intros Hres Ht. eapply IH1; eauto.
          1: eauto using disj_parent_disj_child, Child_Sequence_left.
          eauto using disj_forbidden_child, Child_Sequence_left. (* Same as forward *)
        }
        intros Hres Ht. eapply IH2; eauto.
        * eauto using disj_parent_disj_child, Child_Sequence_right.
        * eauto using disj_forbidden_seq_bwd.
        * do 2 apply ms_valid_wrt_checks_Areg. eauto using ms_valid_wrt_checks_tail.
        * now apply noforbidden_seq_bwd.

    - (* Quantified *)
      intros ctx Hroot Heqn Heqnm m dir. simpl.
      destruct Semantics.compileSubPattern as [msub|] eqn:Hcompsuccsub; simpl; try discriminate.
      specialize (IH (Quantified_inner (wgreedylazy wquant)::ctx)%list).
      specialize_prove IH by eauto using Down.same_root_down0, Down_Quantified_inner.
      specialize_prove IH. {
        simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia.
      }
      specialize (IH Heqnm msub dir Hcompsuccsub).
      set (min := Semantics.CompiledQuantifier_min _).
      set (max := Semantics.CompiledQuantifier_max _).
      rewrite compilequant_greedy with (lquant := lquant) (greedy := greedy) by assumption.
      set (parenIndex := StaticSemantics.countLeftCapturingParensBefore _ ctx).
      set (parenCount := StaticSemantics.countLeftCapturingParensWithin _ _).
      destruct (min <=? max)%NoI eqn:Hmini_le_maxi; simpl; try discriminate.
      intro H. injection H as <-.
      rewrite <- noi_add_diff with (x := min) (y := max) by assumption.
      pose proof equiv_def_groups wr lr n nm parenCount (Quantified_inner (wgreedylazy wquant) :: ctx)%list Hequiv eq_refl as Hgroupsvalid.
      rewrite Heqn in Hgroupsvalid. replace (StaticSemantics.countLeftCapturingParensBefore _ _) with parenIndex in Hgroupsvalid. 2: {
        unfold parenIndex, StaticSemantics.countLeftCapturingParensBefore. reflexivity.
      }
      inversion Hequivquant as [
        Heqwquant Heqlquant |
        Heqwquant Heqlquant |
        Heqwquant Heqlquant |
        nrep Heqwquant Heqlquant |
        nmin Heqwquant Heqlquant |
        mini' maxi' Hle' Heqwquant Heqlquant]; subst wquant lquant;
      inversion Hequivgreedy as [Heqwgl Heqgreedy | Heqwgl Heqgreedy]; subst wgreedylazy greedy; simpl in *; try apply repeatMatcher_equiv; auto.
      all: replace (nrep - min) with 0 by lia; apply repeatMatcher_equiv; auto.

    - (* Group *)
      intros ctx ROOT EQ_n EQ_nm.
      apply equiv_groups with (nm := nm); auto.
      apply IH; auto. simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia.

    - (* named group; same as unnamed group *)
      intros ctx ROOT EQ_n EQ_nm.
      apply equiv_groups with (nm := nm); auto.
      apply IH; auto. simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia.

    - (* Lookarounds *)
      intros ctx Hroot Heqn Heqnm m dir.

      (* Replace Warblre code with factorized code *)
      apply equiv_lookaround_dir_pos in Hequivlk. destruct Hequivlk as [lkdir [lkpos [Heqwlk Heqllk]]].
      subst wlk llk.
      intro Hcompsucc. unfold equiv_matcher.
      intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
      unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforb.
      pose proof lookaroundMatcher_fact lkdir lkpos wr ctx rer dir mc ms as FACT.
      destruct Semantics.compileSubPattern as [m'|]; try discriminate. injection Hcompsucc as ->.
      destruct lookaroundMatcher as [m'|] eqn:Hlkmatchersucc; try discriminate. injection FACT as ->.
      unfold lookaroundMatcher in Hlkmatchersucc.
      destruct Semantics.compileSubPattern as [msub|] eqn:Heqmsub; simpl in *; try discriminate.
      injection Hlkmatchersucc as <-.

      (* Unfold compute_tree to get a meaningful expression *)
      destruct fuel as [|fuel]; simpl; try discriminate.

      (* About msub *)
      specialize IH with (ctx := (lkCtx lkdir lkpos :: ctx)%list) (3 := Heqnm) (m := msub) (dir := lkdir) (4 := Heqmsub).
      specialize_prove IH. { auto using lk_root_fact. }
      specialize_prove IH. { rewrite lk_fact_countParens. auto. }
      (* About msub ms (fun y: MatchState => Success (Some y)) *)
      unfold equiv_matcher in IH.
      specialize (IH str0 id_mcont gl nil nil).
      specialize_prove IH. { apply id_equiv. }
      specialize_prove IH. { auto. }
      specialize_prove IH. { apply List.Disjoint_nil_r. }
      unfold equiv_cont in IH.
      specialize IH with (gm := gm) (ms := ms) (inp := inp) (fuel := fuel) (1 := Hinpcompat) (2 := Hgmms) (3 := Hgmgl) (4 := Hmsinp) (6 := Hgmvalid).
      fold id_mcont.
      destruct msub as [rsub|]; try discriminate. simpl.
      rewrite lkdir_to_lookaround.
      destruct compute_tree as [treelk|] eqn:Heqtreelk; try discriminate.
      specialize IH with (res := rsub) (t := treelk) (3 := eq_refl) (4 := eq_refl).
      specialize_prove IH. { apply ms_valid_wrt_checks_Areg, ms_valid_wrt_checks_nil. }
      specialize_prove IH. {
        unfold GroupMapMS.no_forbidden_groups. intros gid Hin.
        apply Hnoforb, List.in_or_app. left. apply in_forb_implies_in_def. rewrite List.app_nil_r in Hin. auto.
      }

      unfold lk_result. rewrite positivity_to_lookaround, lkdir_to_lookaround.

      destruct lkpos; destruct rsub as [mslk|]; simpl.
      + (* Positive lookaround, lookaround finds a match *)
        inversion IH as [|inpafterlk gmafterlk rlk' Hrlk'inpafterlk Hequivafterlk Heqgmafterlk Heqrlk']. subst rlk'.
        set (msafterlk := match_state _ _ _).
        unfold equiv_cont in Hequivcont. specialize (Hequivcont gmafterlk msafterlk inp res fuel).
        destruct (compute_tree rer act inp gmafterlk dir fuel) as [treecont|] eqn:Heqtreecont; simpl; try discriminate.
        specialize (Hequivcont treecont Hinpcompat).
        specialize_prove Hequivcont by eauto using equiv_gmafterlk_msafterlk. (* Only depends on captures, follows from Hequivafterlk *)
        specialize_prove Hequivcont by eauto using equiv_open_groups_lk. (* Follows from Hgmgl, Heqgmafterlk, Htlk and Hnoforbidden; see paper reasoning (non-trivial, but should not depend on compileSubPattern) *)
        specialize_prove Hequivcont. { unfold msafterlk. apply ms_matches_inp_capchg with (cap := MatchState.captures ms). now destruct ms. }
        specialize_prove Hequivcont. { unfold msafterlk. apply ms_valid_wrt_checks_inpcap with (winp' := MatchState.input ms) (cap' := MatchState.captures ms). apply ms_valid_wrt_checks_tail in Hmschecks. now destruct ms. }
        specialize_prove Hequivcont. { pose proof tree_res_gm_valid treelk gm inp inpafterlk gmafterlk lkdir Hgmvalid. rewrite <- Heqgmafterlk in H. auto. } (* tree_res preserves validity of group maps *)
        specialize_prove Hequivcont. { eapply noforb_lk with (lr := lr); eauto. } (* Follows from Hnoforbidden, Heqgmafterlk and Htlk; non-trivial but should not depend on compileSubPattern *)
        intro Hcontsucc. specialize (Hequivcont Hcontsucc eq_refl).
        intro H. injection H as <-.
        simpl. rewrite positivity_to_lookaround, lkdir_to_lookaround. rewrite <- Heqgmafterlk. assumption.
      + (* Positive lookaround, lookaround does not find a match *)
        intro H. injection H as <-.
        inversion IH. intro H. injection H as <-.
        simpl. constructor.
      + (* Negative lookaround, lookaround finds a match *)
        intro H. injection H as <-.
        inversion IH. intro H'. injection H' as <-.
        simpl. constructor.
      + (* Negative lookaround, lookaround does not find a match *)
        inversion IH.
        unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms inp res fuel).
        destruct (compute_tree rer act inp gm dir fuel) as [treecont|]; try discriminate.
        intros Hres H. injection H as <-. simpl.
        rewrite positivity_to_lookaround, lkdir_to_lookaround. rewrite <- H0.
        apply Hequivcont; auto.
        * eauto using ms_valid_wrt_checks_tail.
        * eauto using noforb_tail.


    - (* Anchor *)
      intros ctx Hroot Heqn Heqnm m dir. inversion Hanchequiv as [Heqwr Heqlanchor | Heqwr Heqlanchor | Heqwr Heqlanchor | Heqwr Heqlanchor].

      + (* Input start *)
        simpl. intro H. injection H as <-.
        unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
        unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforb.
        destruct fuel as [|fuel]; simpl; try discriminate.
        destruct (MatchState.endIndex ms =? 0)%Z eqn:Hatbegin; simpl.
        * (* At begin *)
          rewrite Z.eqb_eq in Hatbegin. unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms inp res fuel).
          unfold anchor_satisfied.
          pose proof begin_input_pref_empty _ _ Hatbegin Hmsinp as Hprefnil. destruct Hprefnil as [next ->].
          destruct compute_tree as [treecont|]; try discriminate.
          specialize (Hequivcont treecont Hinpcompat Hgmms Hgmgl Hmsinp).
          specialize_prove Hequivcont. { apply ms_valid_wrt_checks_tail in Hmschecks. auto. }
          specialize (Hequivcont Hgmvalid Hnoforb).
          intro Hres. specialize (Hequivcont Hres eq_refl). intro H. injection H as <-.
          simpl in *. auto.
        * (* Not at begin *)
          unfold anchor_satisfied.
          rewrite Z.eqb_neq in Hatbegin.
          pose proof begin_input_pref_nonempty _ _ Hatbegin Hmsinp as Hprefnotnil. destruct Hprefnotnil as [next [x [pref ->]]].
          destruct RegExpRecord.multiline; simpl.
          -- (* Multiline *)
             rewrite ms_matches_inp_prevchar2 with (next := next) (pref := pref) (x := x) by auto.
             simpl.
             unfold Characters.line_terminators. setoid_rewrite from_list_contains_inb.
             destruct List.inb.
             ++ unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms (Input next (x::pref)%list) res fuel).
                destruct compute_tree as [treecont|]; try discriminate.
                specialize (Hequivcont treecont Hinpcompat Hgmms Hgmgl Hmsinp).
                specialize_prove Hequivcont. { apply ms_valid_wrt_checks_tail in Hmschecks. auto. }
                specialize (Hequivcont Hgmvalid Hnoforb).
                intro Hres. specialize (Hequivcont Hres eq_refl). intro H. injection H as <-.
                simpl in *. auto. (* Copy-pasted... *)
             ++ intros H H0. injection H as <-. injection H0 as <-. simpl. constructor.
          -- intro H. injection H as <-. intro H. injection H as <-. simpl. constructor.

      + (* Input end *)
        simpl. intro H. injection H as <-.
        unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
        unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforb.
        destruct fuel as [|fuel]; simpl; try discriminate.
        destruct (MatchState.endIndex ms =? _)%Z eqn:Hatend; simpl.
        * (* At end *)
          rewrite Z.eqb_eq in Hatend. intro Hres.
          unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms inp res fuel).
          unfold anchor_satisfied.
          pose proof end_input_next_empty _ _ Hatend Hmsinp as Hnextnil. destruct Hnextnil as [pref ->].
          destruct compute_tree as [treecont|]; try discriminate.
          intro H. injection H as <-. simpl. apply Hequivcont; auto. apply ms_valid_wrt_checks_tail in Hmschecks. auto.
        * (* Not at end *)
          rewrite Z.eqb_neq in Hatend.
          unfold anchor_satisfied.
          pose proof end_input_next_nonempty _ _ Hatend Hmsinp as Hnextnotnil. destruct Hnextnotnil as [pref [x [next ->]]].
          destruct RegExpRecord.multiline; simpl.
          -- rewrite (proj2 (ms_matches_inp_currchar2 ms _ _ _ _ Hmsinp eq_refl)).
             simpl.
             unfold Characters.line_terminators. setoid_rewrite from_list_contains_inb.
             destruct List.inb.
             ++ unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms (Input (x::next)%list pref) res fuel).
                destruct compute_tree as [treecont|]; try discriminate.
                specialize (Hequivcont treecont Hinpcompat Hgmms Hgmgl Hmsinp).
                specialize_prove Hequivcont. { apply ms_valid_wrt_checks_tail in Hmschecks. auto. }
                specialize (Hequivcont Hgmvalid Hnoforb).
                intro Hres. specialize (Hequivcont Hres eq_refl). intro H. injection H as <-.
                simpl in *. auto. (* Copy-pasted... *)
             ++ intros H H0. injection H as <-. injection H0 as <-. simpl. constructor.
          -- intro H. injection H as <-. intro H. injection H as <-. simpl. constructor.

      + (* Word boundary *)
        simpl. intro H. injection H as <-.
        unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
        unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforb.
        destruct fuel as [|fuel]; simpl; try discriminate.
        destruct Semantics.isWordChar as [a|] eqn:Hwca; simpl in *. 2: discriminate.
        destruct (Semantics.isWordChar rer (_ ms) (MatchState.endIndex ms)) as [b|] eqn:Hwcb; simpl in *. 2: discriminate.
        rewrite ifthenelse_xorb. pose proof is_boundary_xorb _ _ _ _ _ Hmsinp Hwca Hwcb as Hisboundary.
        destruct xorb.
        * (* We are on a boundary *)
          intro Hres.
          unfold anchor_satisfied.
          destruct inp as [next pref]. setoid_rewrite <- Hisboundary.
          unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms (Input next pref) res fuel).
          destruct compute_tree as [treecont|]; try discriminate.
          intro H. injection H as <-. simpl. apply Hequivcont; auto. apply ms_valid_wrt_checks_tail in Hmschecks. auto.
        * (* We are not *)
          intro Hres. injection Hres as <-.
          unfold anchor_satisfied. destruct inp as [next pref].
          setoid_rewrite <- Hisboundary. intro H. injection H as <-. simpl. constructor.

      + (* Non word boundary *)
        simpl. intro H. injection H as <-.
        unfold equiv_matcher. intros str0 mc gl forbgroups act Hequivcont Hgldisj Hdef_forbid_disj.
        unfold equiv_cont. intros gm ms inp res fuel t Hinpcompat Hgmms Hgmgl Hmsinp Hmschecks Hgmvalid Hnoforb.
        destruct fuel as [|fuel]; simpl; try discriminate.
        destruct Semantics.isWordChar as [a|] eqn:Hwca; simpl in *. 2: discriminate.
        destruct (Semantics.isWordChar rer (_ ms) (MatchState.endIndex ms)) as [b|] eqn:Hwcb; simpl in *. 2: discriminate.
        rewrite ifthenelse_negb_xorb. pose proof is_boundary_xorb _ _ _ _ _ Hmsinp Hwca Hwcb as Hisboundary.
        destruct xorb.
        * (* We are on a boundary *)
          simpl. intro Hres. injection Hres as <-.
          unfold anchor_satisfied. destruct inp as [next pref].
          setoid_rewrite <- Hisboundary. simpl. intro H. injection H as <-. constructor.
        * (* We are not *)
          simpl. intro Hres.
          unfold anchor_satisfied.
          destruct inp as [next pref]. setoid_rewrite <- Hisboundary. simpl.
          unfold equiv_cont in Hequivcont. specialize (Hequivcont gm ms (Input next pref) res fuel).
          destruct compute_tree as [treecont|]; try discriminate.
          intro H. injection H as <-. simpl. apply Hequivcont; auto. apply ms_valid_wrt_checks_tail in Hmschecks. auto.

  Qed.
End Equiv.
