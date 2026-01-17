From Stdlib Require Import List ZArith Lia.
From Warblre Require Import Notation Parameters Match Base Result Typeclasses.
Import Notation.
Import Match.
Import Result.Notations.
From Linden Require Import Chars LWParameters FunctionalSemantics StrictSuffix Parameters.

Local Open Scope result_flow.


(** * Definitions and lemmas linking Warblre MatchStates with Linden inputs *)

Section MSInput.
  Context {params: LindenParameters}.

  (* Advance match state by one character *)
  Definition advance_ms (s: MatchState) (dir: Direction): MatchState :=
    let newend :=
      match dir with
      | forward => (MatchState.endIndex s + 1)%Z
      | backward => (MatchState.endIndex s - 1)%Z
      end in
    {|
      MatchState.input := MatchState.input s;
      MatchState.endIndex := newend;
      MatchState.captures := MatchState.captures s |}.



  (* We say that a MatchState ms matches an input Input next pref when they represent the same
     string and the same position; in other words, when rev pref ++ next = MatchState.input ms
     and len pref = MatchState.endIndex ms. *)
  Inductive ms_matches_inp: MatchState -> input -> Prop :=
  | Ms_matches_inp: forall (s: string) (end_ind: nat) cap (next pref: string),
      List.length pref = end_ind -> List.rev pref ++ next = s ->
      ms_matches_inp {| MatchState.input := s; MatchState.endIndex := Z.of_nat end_ind;
                                               MatchState.captures := cap |} (Input next pref).

  (* The initial state wrt a string matches the initial input wrt this string. *)
  Lemma init_ms_matches_inp:
    forall str rer, ms_matches_inp (MatchState.init rer str 0) (init_input str).
  Proof.
    intros str rer. now constructor.
  Qed.

  (* Inversion lemma: when a MatchState matches an input, we have
  MatchState.input ms = List.rev pref ++ next. *)
  Lemma ms_matches_inp_invinp:
    forall ms pref next,
      ms_matches_inp ms (Input next pref) -> MatchState.input ms = List.rev pref ++ next.
  Proof.
    intros ms pref next Hmatches. inversion Hmatches. symmetry. assumption.
  Qed.

  (* The initial input of a string is compatible with the string. *)
  Lemma init_input_compat:
    forall str, input_compat (init_input str) str.
  Proof.
    intro str. constructor. reflexivity.
  Qed.

  (* A transitivity lemma: a MatchState ms that matches an input inp that is itself
  compatible with a string str0 has str0 as its input string. *)
  Lemma inp_compat_ms_str0:
    forall (str0: string) (inp: input),
      input_compat inp str0 ->
      forall ms, ms_matches_inp ms inp -> MatchState.input ms = str0.
  Proof.
    intros str0 [next pref] Hcompat ms Hmatches.
    apply ms_matches_inp_invinp in Hmatches.
    inversion Hcompat. congruence.
  Qed.

  (* As a consequence, if two MatchStates ms1 and ms2 respectively match inputs inp1 and inp2
     that are both compatible with str0, then ms1 and ms2 have the same input string. *)
  Lemma inp_compat_ms_same_inp:
    forall (str0: string) (inp1 inp2: input),
      input_compat inp1 str0 -> input_compat inp2 str0 ->
      forall ms1 ms2,
        ms_matches_inp ms1 inp1 -> ms_matches_inp ms2 inp2 ->
        MatchState.input ms1 = MatchState.input ms2.
  Proof.
    intros str0 [next1 pref1] [next2 pref2] Hcompat1 Hcompat2 ms1 ms2 Hmatches1 Hmatches2.
    transitivity str0.
    - eapply inp_compat_ms_str0.
      + apply Hcompat1.
      + apply Hmatches1.
    - symmetry. eapply inp_compat_ms_str0.
      + apply Hcompat2.
      + apply Hmatches2.
  Qed.

  (* The corresponding Linden inputs of two MatchStates that have the same end index
  and are compatible with the same input string are equal. *)
  Lemma ms_same_end_same_inp:
    forall ms ms' inp inp' str0,
      (MatchState.endIndex ms =? MatchState.endIndex ms')%Z = true ->
      ms_matches_inp ms inp -> ms_matches_inp ms' inp' ->
      input_compat inp str0 -> input_compat inp' str0 ->
      inp = inp'.
  Proof.
    intros [str endInd cap] [str' endInd' cap'] [next pref] [next' pref'] str0 Hsameend Hmsinp Hms'inp' Hinpcompat Hinp'compat.
    inversion Hmsinp. inversion Hms'inp'. subst cap0 s next0 pref0 cap1 s0 next1 pref1.
    rename end_ind0 into end_ind'.
    inversion Hinpcompat. subst next0 pref0 str1. inversion Hinp'compat. subst next0 pref0 str1.
    rewrite H4 in H5. rewrite H6 in H12. subst str str'.
    simpl in Hsameend. apply Z.eqb_eq in Hsameend. subst endInd'.
    assert (end_ind' = end_ind) by lia. rewrite H in H8. clear H.
    f_equal.
    - apply (f_equal (skipn end_ind)) in H4, H6. rewrite skipn_app in H4, H6.
      subst end_ind. rewrite rev_length in H4, H6.
      replace (length pref - length pref') with 0 in H6 by lia. rewrite Nat.sub_diag in H4.
      rewrite <- H8 in H6 at 1. rewrite <- rev_length in H6 at 1. rewrite <- rev_length in H4 at 1.
      rewrite skipn_all in H4, H6. simpl in H4, H6. congruence.
    - apply (f_equal (firstn end_ind)) in H4, H6. rewrite firstn_app in H4, H6.
      subst end_ind. rewrite rev_length in H4, H6.
      rewrite H8 in H6. rewrite Nat.sub_diag in H4, H6. rewrite <- H8 in H6 at 1.
      rewrite <- rev_length in H4 at 1, H6 at 1. rewrite firstn_all in H4, H6.
      simpl in H4, H6. rewrite app_nil_r in H4, H6.
      apply (f_equal (rev (A := Character))) in H4, H6. rewrite rev_involutive in H4, H6. congruence. 
  Qed.

  Lemma strict_suffix_irreflexive_bool:
    forall inp dir, is_strict_suffix inp inp dir = false.
  Proof.
    intros inp dir. apply is_strict_suffix_inv_false.
    intro Habs. apply ss_neq in Habs. contradiction.
  Qed.

  (* Whether a MatchState matches an input does not depend on its captures. *)
  Lemma ms_matches_inp_capchg:
    forall str endInd cap cap' inp,
      ms_matches_inp (match_state str endInd cap) inp ->
      ms_matches_inp (match_state str endInd cap') inp.
  Proof.
    intros str endInd cap cap' inp Hmatches.
    inversion Hmatches. now constructor.
  Qed.

  (* If a MatchState matches some input, then the endIndex of the MatchState is in bounds. *)
  Lemma ms_matches_inp_inbounds:
    forall ms inp,
      ms_matches_inp ms inp ->
      (0 <= MatchState.endIndex ms <= Z.of_nat (length (MatchState.input ms)))%Z.
  Proof.
    intros ms [next pref] Hmsinp.
    inversion Hmsinp. subst next0 pref0. simpl.
    subst end_ind. split. 1: lia.
    rewrite <- H3, app_length, rev_length. lia.
  Qed.

  (* Corollary with a compatible input string. *)
  Corollary ms_matches_inp_inbounds_str0:
    forall ms inp str0,
      ms_matches_inp ms inp -> input_compat inp str0 ->
      (0 <= MatchState.endIndex ms <= Z.of_nat (length str0))%Z.
  Proof.
    intros ms inp str0 Hmatches Hcompat.
    rewrite <- inp_compat_ms_str0 with (str0 := str0) (inp := inp) (ms := ms) by assumption.
    eapply ms_matches_inp_inbounds; eauto.
  Qed.

  Lemma error_succ_abs {F S} `{Ferr: Result.AssertionError F}:
    forall x: S, Result.assertion_failed = Success x -> False.
  Proof.
    intros x Hfail. unfold Result.assertion_failed in Hfail. now destruct Ferr.
  Qed.

  (* Linking current characters of matching MatchStates and Linden inputs *)
  Lemma ms_matches_inp_currchar {F} `{Ferr: Result.AssertionError F}:
    forall ms inp c,
      ms_matches_inp ms inp ->
      List.List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms) = Success c ->
      MatchState.endIndex ms <> Z.of_nat (length (MatchState.input ms)) /\
        exists pref next', inp = Input (c::next') pref.
  Proof.
    intros ms inp c Hmatches Hgetchr.
    inversion Hmatches as [str0 end_ind cap next pref Hlenpref Hstr0 Heqms Heqinp].
    subst ms inp. simpl in *.
    rewrite List.List.Indexing.Int.of_nat in Hgetchr.
    pose proof List.List.Indexing.Nat.success_bounds str0 end_ind c Hgetchr as Hindvalid. split. 1: lia.
    unfold List.List.Indexing.Nat.indexing in Hgetchr.
    destruct (nth_error str0 end_ind) as [c'|] eqn:Hgetchr'; simpl in *.
    2: exfalso; eapply error_succ_abs; eauto.
    injection Hgetchr as ->.
    (* Any way to automate this from now on? *)
    pose proof f_equal (@length Character) Hstr0 as Hstr0len. rewrite app_length in Hstr0len. rewrite <- rev_length in Hlenpref. rewrite <- Hstr0 in Hgetchr'.
    rewrite nth_error_app2 in Hgetchr' by lia.
    replace (end_ind - length _) with 0 in Hgetchr' by lia.
    destruct next as [|x next']. 1: discriminate.
    simpl in Hgetchr'. injection Hgetchr' as ->.
    exists pref. exists next'. reflexivity.
  Qed.

  Lemma ms_matches_inp_currchar2 {F} `{Ferr: Result.AssertionError F}:
    forall ms inp c next' pref,
      ms_matches_inp ms inp ->
      inp = Input (c::next') pref ->
      MatchState.endIndex ms <> Z.of_nat (length (MatchState.input ms)) /\
        List.List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms) = Success c.
  Proof.
    intros ms inp c next' pref Hmatches Heqinp. subst inp.
    inversion Hmatches as [str0 end_ind cap next pref0 Hlenpref Hstr0 Heqms Heqnext].
    subst ms pref0 next. simpl in *.
    split.
    - apply (f_equal (@length Character)) in Hstr0. rewrite app_length, rev_length, Hlenpref in Hstr0. simpl in Hstr0. lia.
    - rewrite List.List.Indexing.Int.of_nat.
      unfold List.List.Indexing.Nat.indexing. rewrite <- Hstr0.
      rewrite nth_error_app2. 2: rewrite rev_length; lia. replace (end_ind - _) with 0 by (rewrite rev_length; lia).
      auto.
  Qed.

  Lemma ms_matches_inp_prevchar {F} `{Ferr: Result.AssertionError F}:
    forall ms inp c,
      ms_matches_inp ms inp ->
      List.List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms - 1) = Success c ->
      exists pref' next, inp = Input next (c::pref').
  Proof.
    intros ms inp c Hmatches Hgetchr.
    inversion Hmatches as [str0 end_ind cap next pref Hlenpref Hstr0 Heqms Heqinp].
    subst inp ms. simpl in *.
    destruct pref as [|x pref'].
    1: { simpl in *. subst end_ind. simpl in *. exfalso. eapply error_succ_abs; eauto. }
    simpl in *.
    exists pref'. exists next. f_equal. f_equal.
    subst end_ind. replace (Z.of_nat _ - 1)%Z with (Z.of_nat (length pref')) in Hgetchr by lia. rewrite List.List.Indexing.Int.of_nat in Hgetchr.
    rewrite <- Hstr0 in Hgetchr. unfold List.List.Indexing.Nat.indexing in Hgetchr.
    rewrite nth_error_app1 in Hgetchr. 2: { rewrite app_length, rev_length. simpl. lia. }
    rewrite nth_error_app2 in Hgetchr. 2: { rewrite rev_length. reflexivity. }
    replace (length _ - length _) with 0 in Hgetchr. 2: { rewrite rev_length. lia. }

    simpl in *. now injection Hgetchr.
  Qed.

  Lemma ms_matches_inp_prevchar2 {F} `{Ferr: Result.AssertionError F}:
    forall ms next pref x,
      ms_matches_inp ms (Input next (x::pref)) ->
      List.List.Indexing.Int.indexing (MatchState.input ms) (MatchState.endIndex ms - 1) = Success x.
  Proof.
    intros ms next pref x Hmsinp.
    inversion Hmsinp as [str0 end_ind cap next' pref0 Hlenpref Hstr0 Heqms]. subst next' pref0.
    simpl in *.
    replace (Z.of_nat end_ind - 1)%Z with (Z.of_nat (length pref)) by lia.
    rewrite List.List.Indexing.Int.of_nat.
    unfold List.List.Indexing.Nat.indexing. rewrite <- Hstr0.
    rewrite nth_error_app1. 2: { rewrite app_length, rev_length. simpl. lia. }
    rewrite nth_error_app2. 2: { rewrite rev_length. reflexivity. }
    rewrite rev_length, Nat.sub_diag. reflexivity.
  Qed.
End MSInput.
