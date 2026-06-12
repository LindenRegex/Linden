From Linden.Rewriting Require Import ProofSetup.

(** * Rewriting anchors as lookarounds *)

Section Anchors.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Notation ascii_word_canon :=
    (forall c,
        In c Character.ascii_word_characters ->
        In (Character.canonicalize rer c) Character.ascii_word_characters).

  Notation ascii_word_inall :=
    (forall c, In c Character.ascii_word_characters -> In c Character.all).

  Notation canonicalize_nonall_stable :=
    (forall c, In (Character.canonicalize rer c) Character.all <-> In c Character.all).

  Notation line_terminators_canon :=
    (forall c,
        In c Character.line_terminators <->
          In (Character.canonicalize rer c) Character.line_terminators).

  Definition CdList (cs: list Parameters.Character) :=
    List.fold_right (fun c cd => CdUnion (CdSingle c) cd) CdEmpty cs.

  Definition desugar_anchor (a: anchor) :=
    match a with
    | BeginInput =>
        if RegExpRecord.multiline rer then
          Disjunction
            (Lookaround NegLookBehind (Character CdAll))
            (Lookaround LookBehind (Character (CdList Character.line_terminators)))
        else
            (Lookaround NegLookBehind (Character CdAll))
    | EndInput =>
        if RegExpRecord.multiline rer then
          Disjunction
            (Lookaround NegLookAhead (Character CdAll))
            (Lookaround LookAhead (Character (CdList Character.line_terminators)))
        else
          Lookaround NegLookAhead (Character CdAll)
    | WordBoundary =>
        Disjunction
          (Sequence
             (Lookaround NegLookBehind (Character CdWordChar))
             (Lookaround LookAhead (Character CdWordChar)))
          (Sequence
             (Lookaround LookBehind (Character CdWordChar))
             (Lookaround NegLookAhead (Character CdWordChar)))
    | NonWordBoundary =>
        Sequence
          (Disjunction
             (Lookaround LookBehind (Character CdWordChar))
             (Lookaround NegLookAhead (Character CdWordChar)))
          (Disjunction
             (Lookaround NegLookBehind (Character CdWordChar))
             (Lookaround LookAhead (Character CdWordChar)))
    end.

  Lemma char_match_cdlist c cs:
    char_match rer c (CdList cs) = inb_canonicalized rer c cs.
  Proof.
    unfold CdList, char_match, inb_canonicalized; induction cs; simpl.
    all: try rewrite Utils.List.inb_cons, IHcs; reflexivity.
  Qed.

  Lemma char_match_line_terminators c (Hlc: line_terminators_canon):
    char_match rer c (CdList Character.line_terminators) =
      Utils.List.inb c Character.line_terminators.
  Proof.
    rewrite char_match_cdlist; unfold inb_canonicalized.
    apply Bool.eq_iff_eq_true; rewrite !Utils.List.inb_spec, in_map_iff.
    split; [ intros (c' & Hc & HIn) | solve[eauto] ].
    rewrite Hlc in *; congruence.
  Qed.

  (* FIXME why do I need this? *)
  Instance: Parameters := (@LWParameters.LWParameters params).

  (* FIXME move closer to definition *)
  Lemma wordCharacters_spec c:
    CharSet.In c (wordCharacters rer) <->
      CharSet.In c Characters.ascii_word_characters \/
        (CharSet.In c Characters.all /\ CharSet.In (Character.canonicalize rer c) Characters.ascii_word_characters).
  Proof.
    unfold wordCharacters, Semantics.Semantics.wordCharacters,
      Coercions.wrap_CharSet; simpl.
    rewrite !CharSet.union_spec.
    rewrite !CharSet.filter_spec.
    rewrite !Bool.andb_true_iff, !Bool.negb_true_iff.
    rewrite !CharSet.contains_spec.
    rewrite !CharSet.contains_false_iff.
    setoid_rewrite CharSet.from_list_spec.
    assert (In c Character.ascii_word_characters \/ ~  In c Character.ascii_word_characters)
      by (rewrite <- !CharSet.from_list_contains;
          destruct CharSet.contains; eauto).
    intuition.
  Qed.

  Lemma wordCharacters_canonical t (Hac: ascii_word_canon) (Haa: ascii_word_inall) (Hcan_nonall_st: canonicalize_nonall_stable):
    CharSet.contains (wordCharacters rer) t =
      CharSet.exist_canonicalized rer (wordCharacters rer) (Character.canonicalize rer t).
  Proof.
    apply Bool.eq_true_iff_eq.
    rewrite CharSet.exist_canonicalized_equiv, CharSet.exist_iff.
    setoid_rewrite CharSet.contains_spec.
    setoid_rewrite EqDec.inversion_true.
    setoid_rewrite wordCharacters_spec.
    setoid_rewrite CharSet.from_list_spec.
    split; [ | intros (c & HIn & Hsamecan) ].
    - intuition eauto.
    - assert (In t Character.all \/ ~ In t Character.all)
        by (rewrite <- !CharSet.from_list_contains;
            destruct CharSet.contains; eauto).
      destruct H.
      + rewrite <- Hsamecan. intuition eauto.
      + assert (In c Character.all). { destruct HIn. - auto. - tauto. }
        pose proof Hcan_nonall_st c as Hcan_nonall_st_c.
        pose proof Hcan_nonall_st t as Hcan_nonall_st_t.
        rewrite <- Hsamecan in Hcan_nonall_st_t. tauto.
  Qed.

  Lemma char_match_word_char c (Ha: ascii_word_canon) (Haa: ascii_word_inall) (Hcan_nonall_st: canonicalize_nonall_stable):
    char_match rer c CdWordChar =
      CharSet.contains (wordCharacters rer) c.
  Proof.
    unfold char_match; simpl.
    symmetry; eauto using wordCharacters_canonical.
  Qed.

  Hint Rewrite char_match_line_terminators char_match_word_char using eauto : tree_equiv_symbex.

  Theorem desugar_anchor_correct (a: anchor):
    ascii_word_canon ->
    ascii_word_inall ->
    canonicalize_nonall_stable ->
    line_terminators_canon ->
    Anchor a ≅[rer] desugar_anchor a.
  Proof.
    intros; destruct a; tree_equiv_rw.
    all: destruct dir; tree_equiv_symbex.
    all: reflexivity.
  Qed.

  Corollary desugar_anchor_correct_noi (a: anchor) (Haa: ascii_word_inall):
    rer.(RegExpRecord.ignoreCase) = false ->
    Anchor a ≅[rer] desugar_anchor a.
  Proof.
    intros Hic; apply desugar_anchor_correct.
    all: intros c; try rewrite canonicalize_casesenst; intuition.
  Qed.
End Anchors.
