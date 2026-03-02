From Linden Require Import Chars LWParameters Parameters RegexpTranslation WarblreLemmas.
From Warblre Require Import Parameters Semantics Result Patterns RegExpRecord Typeclasses.
Import Result.Notations.
Import Patterns.
From Stdlib Require Import Lia.

Local Open Scope result_flow.

(** Equivalence between character descriptors and CharSets *)

Section CharDescrCharSet.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* Definition *)
  Definition equiv_cd_charset (cd: char_descr) (charset: CharSet) :=
    forall c: Character, char_match rer c cd = CharSet.exist_canonicalized rer charset (Character.canonicalize rer c).

  (* Lemma for character descriptor union *)
  Lemma equiv_cd_union:
    forall cd1 cd2 s1 s2,
      equiv_cd_charset cd1 s1 -> equiv_cd_charset cd2 s2 ->
      equiv_cd_charset (CdUnion cd1 cd2) (CharSet.union s1 s2).
  Proof.
    intros cd1 cd2 s1 s2 Hequiv1 Hequiv2 c. unfold char_match.
    simpl. rewrite CharSet.exist_canonicalized_equiv.
    apply Bool.eq_iff_eq_true. rewrite CharSet.exist_iff.
    setoid_rewrite CharSet.union_contains.
    split.
    - intro H. apply Bool.orb_prop in H. destruct H.
      + specialize (Hequiv1 c). setoid_rewrite H in Hequiv1.
        symmetry in Hequiv1. rewrite CharSet.exist_canonicalized_equiv in Hequiv1.
        setoid_rewrite CharSet.exist_iff in Hequiv1.
        setoid_rewrite Bool.orb_true_iff. firstorder.
      + specialize (Hequiv2 c). setoid_rewrite H in Hequiv2.
        symmetry in Hequiv2. rewrite CharSet.exist_canonicalized_equiv in Hequiv2.
        setoid_rewrite CharSet.exist_iff in Hequiv2.
        setoid_rewrite Bool.orb_true_iff. firstorder.
    - setoid_rewrite Bool.orb_true_iff. intros [c0 [Hcontains Hcanonicalize]].
      destruct Hcontains as [Hcontains | Hcontains].
      + left. specialize (Hequiv1 c). setoid_rewrite Hequiv1.
        setoid_rewrite CharSet.exist_canonicalized_equiv.
        rewrite CharSet.exist_iff. exists c0. auto.
      + right. specialize (Hequiv2 c). setoid_rewrite Hequiv2.
        setoid_rewrite CharSet.exist_canonicalized_equiv.
        rewrite CharSet.exist_iff. exists c0. auto.
  Qed.

  (* Lemmas for various character descriptors *)
  Lemma equiv_cd_empty:
    equiv_cd_charset CdEmpty CharSet.empty.
  Proof.
    intro c. unfold char_match. simpl.
    rewrite CharSet.exist_canonicalized_equiv.
    symmetry. apply Bool.not_true_is_false.
    intro ABS. rewrite CharSet.exist_iff in ABS.
    destruct ABS as [c0 [ABS _]].
    rewrite CharSet.empty_contains in ABS. discriminate ABS.
  Qed.

  Lemma equiv_cd_digits:
    equiv_cd_charset CdDigits Characters.digits.
  Proof.
    intro c. simpl. reflexivity.
  Qed.

  Lemma equiv_cd_whitespace:
    equiv_cd_charset CdWhitespace (CharSet.union Characters.white_spaces Characters.line_terminators).
  Proof.
    intro c. simpl. reflexivity.
  Qed.

  Lemma equiv_cd_wordchar:
    equiv_cd_charset CdWordChar (Chars.wordCharacters rer).
  Proof.
    intro c. simpl. reflexivity.
  Qed.

  Lemma equiv_cd_range:
    forall cl ch,
      Character.numeric_value cl <= Character.numeric_value ch ->
      equiv_cd_charset (CdRange cl ch) (CharSet.range cl ch).
  Proof.
    intros cl ch Hle c. unfold char_match. simpl.
    do 2 rewrite Character.numeric_pseudo_bij. reflexivity.
  Qed.

  Lemma equiv_cd_dot_dotAll:
    RegExpRecord.dotAll rer = true ->
    equiv_cd_charset CdDot Characters.all.
  Proof.
    intros HdotAll c. unfold char_match. simpl. unfold dot_matches. rewrite HdotAll. reflexivity.
  Qed.

  Lemma equiv_cd_dot_noDotAll:
    RegExpRecord.dotAll rer = false ->
    equiv_cd_charset CdDot (CharSet.remove_all Characters.all Characters.line_terminators).
  Proof.
    intros HnoDotAll c. unfold char_match. simpl. unfold dot_matches. rewrite HnoDotAll.
    reflexivity.
  Qed.

  Lemma equiv_cd_single:
    forall c, equiv_cd_charset (CdSingle c) (CharSet.singleton c).
  Proof.
    intros c chr. unfold char_match. simpl.
    rewrite CharSet.exist_canonicalized_equiv. rewrite CharSet.singleton_exist.
    destruct EqDec.eqb eqn:H.
    - rewrite EqDec.inversion_true in H. symmetry. rewrite H. apply EqDec.reflb.
    - symmetry. apply Bool.not_true_is_false. intro ABS.
      rewrite EqDec.inversion_true in ABS. rewrite ABS, EqDec.reflb in H. discriminate H.
  Qed.

  Lemma equiv_cd_unicodeprop:
    forall p, equiv_cd_charset (CdUnicodeProp p) (CharSet.from_list (Property.code_points_for p)).
  Proof.
    intros p c. unfold char_match. simpl. reflexivity.
  Qed.

  (* Lemma for CharacterClassEscapes *)
  Lemma equiv_cd_CharacterClassEscape:
    forall esc cd,
      equiv_CharacterClassEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc (CCharacterClassEsc esc)) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd Hequiv.
    inversion Hequiv as [
      Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd | Heqesc Heqcd |
      p Heqesc Heqcd | p Heqesc Heqcd ];
      simpl; unfold Coercions.Coercions.wrap_CharSet; eexists; split; try solve[reflexivity];
      try solve[unfold equiv_cd_charset; reflexivity].
  Qed.

  (* Lemma for ControlEscapes *)
  Lemma equiv_cd_ControlEscape:
    forall esc cd,
      equiv_ControlEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc (CCharacterEsc (ControlEsc esc))) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd Hequiv.
    inversion Hequiv; simpl; unfold Coercions.Coercions.wrap_CharSet; eexists; split;
      try solve[reflexivity]; unfold Numeric.nat_to_nni; rewrite Character.numeric_pseudo_bij;
      apply equiv_cd_single.
  Qed.

  (* Lemma for CharacterEscapes *)
  Lemma equiv_cd_CharacterEscape:
    forall esc cd,
      equiv_CharacterEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc (CCharacterEsc esc)) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd Hequiv.
    inversion Hequiv as [
      esc0 cd0 Hequiv' Heqesc Heqcd0 | l cd0 Hequiv' Heqesc Heqcd0 | Heqesc Heqcd |
      d1 d2 Heqesc Heqcd | c Heqesc Heqcd | head tail Heqesc Heqcd | hex Heqesc Heqcd |
      c Heqesc Heqcd].
    - apply equiv_cd_ControlEscape. assumption.
    - inversion Hequiv' as [l0 i Heqi Heql0 Heqcd]. subst cd0 l0.
      simpl. rewrite <- Heqi.
      unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. 1: reflexivity.
      unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
  Qed.

  (* Lemma for ClassEscapes *)
  Lemma equiv_cd_ClassEscape:
    forall esc cd,
      equiv_ClassEscape esc cd ->
      exists a, Semantics.compileToCharSet_ClassAtom (ClassEsc esc) rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros esc cd Hequiv. inversion Hequiv as [Heqesc Heqcd | Heqesc Heqcd | |].
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split.
      + reflexivity.
      + unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split.
      + reflexivity.
      + unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. apply equiv_cd_single.
    - apply equiv_cd_CharacterClassEscape; auto.
    - apply equiv_cd_CharacterEscape; auto.
  Qed.

  (* Lemmas for ClassRanges *)
  Lemma equiv_cd_ClassAtom:
    forall ca cacd,
      equiv_ClassAtom ca cacd ->
      exists a, Semantics.compileToCharSet_ClassAtom ca rer = Success a /\ equiv_cd_charset cacd a.
  Proof.
    intros ca cacd Hequiv.
    inversion Hequiv as [c Heqca Heqcacd | esc cd Hequiv' Heqca Heqcacd].
    - simpl. unfold Coercions.Coercions.wrap_CharSet. eexists. split. + reflexivity. + apply equiv_cd_single.
    - apply equiv_cd_ClassEscape; assumption.
  Qed.

  Lemma equiv_ClassAtom_single_charset:
    forall (a: ClassAtom) (c: Character),
      equiv_ClassAtom a (CdSingle c) ->
      Semantics.compileToCharSet_ClassAtom a rer = Success (CharSet.singleton c).
  Proof.
    intros a c EQUIV. inversion EQUIV; subst.
    - simpl. reflexivity.
    - inversion H; subst.
      + simpl. unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. reflexivity.
      + simpl. unfold Numeric.nat_to_nni. rewrite Character.numeric_pseudo_bij. reflexivity.
      + inversion H0.
      + inversion H0; subst; simpl; unfold Numeric.nat_to_nni; try rewrite Character.numeric_pseudo_bij; try reflexivity.
        * inversion H1; subst; simpl; rewrite Character.numeric_pseudo_bij; reflexivity.
        * inversion H1; subst. reflexivity.
  Qed.

  Lemma equiv_cd_ClassRanges:
    forall crs cd,
      equiv_ClassRanges crs cd ->
      exists a, Semantics.compileToCharSet crs rer = Success a /\
             equiv_cd_charset cd a.
  Proof.
    intros crs cd Hequiv.
    induction Hequiv as [|ca cacd t tcd Hequiv' Hequiv IH | l h cl ch t tcd Hequivl Hequivh Hl_le_h Hequiv IH].
    - simpl. unfold Coercions.Coercions.wrap_CharSet.
      eexists. split. + reflexivity. + apply equiv_cd_empty.
    - simpl. pose proof equiv_cd_ClassAtom ca cacd Hequiv' as [A [HeqA Hequivatom]].
      rewrite HeqA. simpl.
      destruct IH as [B [HeqB IH]]. rewrite HeqB. simpl.
      unfold Coercions.Coercions.wrap_CharSet. eexists. split. + reflexivity. + now apply equiv_cd_union.
    - simpl.
      rewrite equiv_ClassAtom_single_charset with (c := cl) by auto.
      rewrite equiv_ClassAtom_single_charset with (c := ch) by auto.
      simpl.
      destruct IH as [C [HeqC IH]]. rewrite HeqC. simpl.
      unfold Semantics.characterRange. setoid_rewrite CharSet.singleton_size. simpl.
      do 2 rewrite CharSet.singleton_unique. simpl.
      pose proof Hl_le_h as Hl_le_h'. rewrite <- PeanoNat.Nat.leb_le in Hl_le_h'. rewrite Hl_le_h'. simpl.
      unfold Coercions.Coercions.wrap_CharSet. eexists. split.
      + reflexivity.
      + apply equiv_cd_union; auto. do 2 rewrite Character.numeric_pseudo_bij. apply equiv_cd_range. assumption.
  Qed.
End CharDescrCharSet.
