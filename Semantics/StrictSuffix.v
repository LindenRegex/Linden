From Linden Require Import Chars Parameters LWParameters.
From Warblre Require Import Base Parameters.
From Stdlib Require Import List Lia.
Import ListNotations.


Section StrictSuffix.
  Context {params: LindenParameters}.

  (** * Suffixes  *)

  (* advance_input is the next suffix *)
  (* but now we explore the transitive closure of this relation *)

  Inductive strict_suffix : input -> input -> Direction -> Prop :=
  | ss_advance:
    forall inp nextinp dir,
      advance_input inp dir = Some nextinp ->
      strict_suffix nextinp inp dir
  | ss_next:
    forall inp1 inp2 inp3 dir,
      advance_input inp2 dir = Some inp1 ->
      strict_suffix inp2 inp3 dir ->
      strict_suffix inp1 inp3 dir.

  (** * Functional version of strict_suffix *)

  (* Another, functional, version of strict suffix *)
  Fixpoint strict_suffix_forward (inp:input) (next pref:string): bool :=
    match next with
    | [] => false                  (* cannot be a strict suffix of the end of string *)
    | c::next' =>
        if (Input next' (c::pref) ==? inp)%wt then true
        else strict_suffix_forward inp next' (c::pref)
    end.

  Fixpoint strict_suffix_backward (inp:input) (next pref:string): bool :=
    match pref with
    | [] => false                  (* cannot be a (backward) strict suffix of the beginning of string *)
    | c::pref' =>
        if (Input (c::next) pref' ==? inp)%wt then true
        else strict_suffix_backward inp (c::next) pref'
    end.

  Definition is_strict_suffix (inp1 inp2:input) (dir:Direction) : bool :=
    match inp2 with
    | Input next2 pref2 =>
        match dir with
        | forward => strict_suffix_forward inp1 next2 pref2
        | backward => strict_suffix_backward inp1 next2 pref2
        end
    end.


  (** * Lemmas about strict_suffix and is_strict_suffix *)

  Lemma decide_nil {A}:
    forall l: list A, {l = []} + {l <> []}.
  Proof.
    intro l. destruct l.
    - left. reflexivity.
    - right. discriminate.
  Defined.

  Theorem ss_fwd_diff:
    forall next1 pref1 next2 pref2,
      strict_suffix (Input next1 pref1) (Input next2 pref2) forward <->
        exists diff, diff <> [] /\ next2 = diff ++ next1 /\ pref1 = rev diff ++ pref2.
  Proof.
    intros next1 pref1 next2 pref2. split.
    {
      intro Hss. remember forward as dir. remember (Input next1 pref1) as inp1. remember (Input next2 pref2) as inp2.
      revert next1 pref1 next2 pref2 Heqinp1 Heqinp2.
      induction Hss as [inp nextinp dir Hadv|inp1 inp2 inp3 dir Hadv Hss IH]; subst dir.
      - intros. subst inp nextinp. simpl in Hadv. destruct next2 as [|h next2']; simpl in *; try discriminate.
        injection Hadv as <- <-. exists [h]. split; [|split]; easy.
      - intros next1 pref1 next3 pref3 -> ->. destruct inp2 as [next2 pref2].
        specialize (IH eq_refl _ _ _ _ eq_refl eq_refl). destruct IH as [diff [Hdiffcons [Hnext23 Hpref23]]].
        simpl in Hadv. destruct next2 as [|h next2']; try discriminate.
        injection Hadv as <- <-. exists (diff ++ [h]). split; [|split].
        + destruct diff; easy.
        + rewrite Hnext23, <- app_assoc. reflexivity.
        + rewrite Hpref23, rev_app_distr, <- app_assoc. reflexivity.
    }
    {
      intros [diff [Hdiffcons [Hnext12 Hpref12]]].
      rewrite <- length_zero_iff_nil in Hdiffcons. remember (length diff) as nd.
      revert next1 pref1 next2 pref2 diff Heqnd Hdiffcons Hnext12 Hpref12. induction nd as [|nd' IH].
      - easy.
      - intros next1 pref1 next2 pref2 diff Hlendiff _ Hnext12 Hpref12.
        destruct diff as [|x diff']; try discriminate.
        destruct (decide_nil diff') as [Hnil | Hnotnil].
        + subst diff'. simpl in *. apply ss_advance. simpl. rewrite Hnext12. f_equal. f_equal. congruence.
        + pose proof exists_last Hnotnil as [diff'' [a Heqdiff']]. subst diff'.
          (* Situation:
          |-----------|---|--------|---|-------|
            rev pref2  [x]  diff''  [a]  next1
          *)
          apply ss_next with (inp2 := Input (a::next1) (rev (x :: diff'') ++ pref2)).
          * simpl. f_equal. f_equal. rewrite Hpref12. simpl.
            rewrite rev_app_distr, <- app_assoc, <- app_assoc, <- app_assoc. reflexivity.
          * simpl in *. rewrite app_length in Hlendiff. simpl in *. apply IH with (diff := x :: diff'').
            -- simpl. lia.
            -- lia.
            -- rewrite <- app_comm_cons. rewrite <- app_assoc in Hnext12. auto.
            -- f_equal.
    }
  Qed.

  Theorem ss_bwd_diff:
    forall next1 pref1 next2 pref2,
      strict_suffix (Input next1 pref1) (Input next2 pref2) backward <->
        exists diff, diff <> [] /\ next1 = diff ++ next2 /\ pref2 = rev diff ++ pref1.
  Proof.
    intros next1 pref1 next2 pref2. split.
    {
      intro Hss. remember backward as dir. remember (Input next1 pref1) as inp1. remember (Input next2 pref2) as inp2.
      revert next1 pref1 next2 pref2 Heqinp1 Heqinp2.
      induction Hss as [inp nextinp dir Hadv|inp1 inp2 inp3 dir Hadv Hss IH]; subst dir.
      - intros. subst inp nextinp. simpl in Hadv. destruct pref2 as [|h pref2']; simpl in *; try discriminate.
        injection Hadv as <- <-. exists [h]. split; [|split]; easy.
      - intros next1 pref1 next3 pref3 -> ->. destruct inp2 as [next2 pref2].
        specialize (IH eq_refl _ _ _ _ eq_refl eq_refl). destruct IH as [diff [Hdiffcons [Hnext23 Hpref23]]].
        simpl in Hadv. destruct pref2 as [|h pref2']; try discriminate.
        injection Hadv as <- <-. exists (h :: diff). split; [|split].
        + destruct diff; easy.
        + rewrite Hnext23, <- app_comm_cons. reflexivity.
        + rewrite Hpref23. simpl. rewrite <- app_assoc. reflexivity.
    }
    {
      intros [diff [Hdiffcons [Hnext12 Hpref12]]].
      rewrite <- length_zero_iff_nil in Hdiffcons. remember (length diff) as nd.
      revert next1 pref1 next2 pref2 diff Heqnd Hdiffcons Hnext12 Hpref12. induction nd as [|nd' IH].
      - easy.
      - intros next1 pref1 next2 pref2 diff Hlendiff _ Hnext12 Hpref12.
        destruct diff as [|x diff']; try discriminate.
        destruct (decide_nil diff') as [Hnil | Hnotnil].
        + subst diff'. simpl in *. apply ss_advance. simpl. rewrite Hpref12. f_equal. f_equal. congruence.
        + pose proof exists_last Hnotnil as [diff'' [a Heqdiff']]. subst diff'.
          (* Situation:
          |-----------|---|--------|---|-------|
            rev pref1  [x]  diff''  [a]  next2
          *)
          apply ss_next with (inp2 := Input (diff'' ++ a :: next2) (x :: pref1)).
          * simpl. f_equal. f_equal. rewrite Hnext12. simpl.
            rewrite <- app_assoc. reflexivity.
          * simpl in *. rewrite app_length in Hlendiff. simpl in *. apply IH with (diff := diff'' ++ [a]).
            -- rewrite app_length. simpl. lia.
            -- lia.
            -- rewrite <- app_assoc. auto.
            -- rewrite <- app_assoc in Hpref12. auto.
    }
  Qed.

  Lemma ss_next':
    forall inp1 inp2 inp3 dir,
      strict_suffix inp1 inp2 dir ->
      advance_input inp3 dir = Some inp2 ->
      strict_suffix inp1 inp3 dir.
  Proof.
    intros inp1 inp2 inp3 dir H12. revert inp3. induction H12 as [inp2 inp1 dir H12 | inp1 inp2 inp3 dir H12 H23 IH].
    - intros inp3 H23. eauto using ss_next, ss_advance.
    - intros inp4 H34. eauto using ss_next, ss_advance, IH.
  Qed.


  Lemma strict_suffix_forward_sound:
    forall inp next pref,
      strict_suffix_forward inp next pref = true -> strict_suffix inp (Input next pref) forward.
  Proof.
    intros inp next. induction next as [|c next' IH].
    1: discriminate.
    intro pref. simpl.
    destruct (Input next' (c::pref) ==? inp)%wt eqn:Hequal.
    1: { rewrite EqDec.inversion_true in Hequal. intros _. apply ss_advance. subst inp. reflexivity. }
    intro H. specialize (IH (c::pref) H).
    eapply ss_next'; eauto.
  Qed.

  Lemma strict_suffix_forward_complete:
    forall inp next pref,
      strict_suffix inp (Input next pref) forward -> strict_suffix_forward inp next pref = true.
  Proof.
    intros [next' pref'] next pref Hss.
    apply ss_fwd_diff in Hss. destruct Hss as [diff [Hdiffcons [Hnextnext' Hprefpref']]].
    revert next' pref' next pref Hdiffcons Hnextnext' Hprefpref'.
    induction diff as [|x diff' IH].
    { easy. }
    (* Situation:
    |--------|-|------|---------|
       pref   x  diff    next'
    *)
    intros next' pref' next pref _ Hnextnext' Hprefpref'. rewrite Hnextnext', <- app_comm_cons.
    simpl.
    destruct (decide_nil diff') as [Hdiff'nil | Hdiff'notnil].
    - subst diff'. simpl in *. rewrite <- Hprefpref', EqDec.reflb. reflexivity.
    - destruct EqDec.eqb; try reflexivity.
      apply IH; auto.
      simpl in Hprefpref'. rewrite <- app_assoc in Hprefpref'. auto.
  Qed.

  Lemma strict_suffix_backward_sound:
    forall inp next pref,
      strict_suffix_backward inp next pref = true -> strict_suffix inp (Input next pref) backward.
  Proof.
    intros inp next pref. revert next. induction pref as [|c pref' IH].
    1: discriminate.
    intro next. simpl.
    destruct (Input (c::next) pref' ==? inp)%wt eqn:Hequal.
    1: { rewrite EqDec.inversion_true in Hequal. intros _. apply ss_advance. subst inp. reflexivity. }
    intro H. specialize (IH (c::next) H).
    eapply ss_next'; eauto.
  Qed.

  Lemma strict_suffix_backward_complete:
    forall inp next pref,
      strict_suffix inp (Input next pref) backward -> strict_suffix_backward inp next pref = true.
  Proof.
    intros [next' pref'] next pref Hss.
    apply ss_bwd_diff in Hss. destruct Hss as [diff [Hdiffcons [Hnextnext' Hprefpref']]].
    revert next' pref' next pref Hdiffcons Hnextnext' Hprefpref'.
    induction diff as [|x diff' IH] using rev_ind.
    { easy. }
    (* Situation:
    |--------|-|------|---------|
       pref'  x  diff'   next
    *)
    intros next' pref' next pref _ Hnextnext' Hprefpref'. rewrite Hprefpref', rev_app_distr. simpl.
    destruct (decide_nil diff') as [Hdiff'nil | Hdiff'notnil].
    - subst diff'. simpl in *. rewrite <- Hnextnext', EqDec.reflb. reflexivity.
    - destruct EqDec.eqb; try reflexivity.
      apply IH; auto.
      rewrite <- app_assoc in Hnextnext'. auto.
  Qed.

  Theorem is_strict_suffix_correct:
    forall inp1 inp2 dir,
      is_strict_suffix inp1 inp2 dir = true <-> strict_suffix inp1 inp2 dir.
  Proof.
    intros [next1 pref1] [next2 pref2] dir. destruct dir; simpl.
    - split; intro.
      + now apply strict_suffix_forward_sound.
      + now apply strict_suffix_forward_complete.
    - split; intro.
      + now apply strict_suffix_backward_sound.
      + now apply strict_suffix_backward_complete.
  Qed.

  Corollary is_strict_suffix_inv_false:
    forall inp1 inp2 dir,
      is_strict_suffix inp1 inp2 dir = false <-> ~strict_suffix inp1 inp2 dir.
  Proof.
    intros inp1 inp2 dir. split; intro.
    - intro Habs. apply is_strict_suffix_correct in Habs. congruence.
    - destruct is_strict_suffix eqn:His_ss; try reflexivity.
      apply is_strict_suffix_correct in His_ss. contradiction.
  Qed.

  Theorem read_suffix:
    forall inp dir nextinp,
      advance_input inp dir = Some nextinp ->
      strict_suffix nextinp inp dir.
  Proof.
    intros inp dir nextinp H. constructor. auto.
  Qed.

  Lemma advance_current_plus_one:
    forall inp1 inp2 dir,
      advance_input inp2 dir = Some inp1 ->
      length (current_str inp2 dir) = S (length (current_str inp1 dir)).
  Proof.
    intros [next1 pref1] [next2 pref2] [|] H; simpl in H.
    - destruct next2; inversion H. simpl. auto.
    - destruct pref2; inversion H. simpl. auto.
  Qed.

  Lemma strict_suffix_current:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir -> length (current_str inp1 dir) < length (current_str inp2 dir).
  Proof.
    intros inp1 inp2 dir Hss.
    induction Hss as [inp nextinp dir H | inp1 inp2 inp3 dir Hadv Hss IH].
    - pose proof advance_current_plus_one nextinp inp dir H. lia.
    - pose proof advance_current_plus_one inp1 inp2 dir Hadv. lia.
  Qed.

  Theorem read_char_suffix:
    forall inp dir nextinp cd c rer,
      read_char rer cd inp dir = Some (c, nextinp) ->
      strict_suffix nextinp inp dir.
  Proof.
    intros [next pref] dir nextinp cd c rer H. destruct dir; simpl in H.
    - destruct next; inversion H. destruct (char_match rer t cd); inversion H; subst.
      apply read_suffix. simpl. auto.
    - destruct pref; inversion H. destruct (char_match rer t cd); inversion H; subst.
      apply read_suffix. simpl. auto.
  Qed.


  Theorem strict_suffix_trans:
    forall inp1 inp2 inp3 dir,
      strict_suffix inp1 inp2 dir ->
      strict_suffix inp2 inp3 dir ->
      strict_suffix inp1 inp3 dir.
  Proof.
    intros inp1 inp2 inp3 dir H H0. induction H.
    - eapply ss_next; eauto.
    - eapply ss_next; eauto.
  Qed.

  Lemma strict_advance:
    forall inp1 inp2 dir nextinp1,
      strict_suffix inp1 inp2 dir ->
      advance_input inp1 dir = Some nextinp1 ->
      exists nextinp2, advance_input inp2 dir = Some nextinp2 /\
                    strict_suffix nextinp1 nextinp2 dir.
  Proof.
    intros [next1 pref1] [next2 pref2] dir [next1next next1pref] Hss Hadv.
    destruct dir.
    - (* Forward *)
      apply ss_fwd_diff in Hss. destruct Hss as [diff [Hdiffcons [Hnext12 Hpref12]]].
      destruct diff as [|x diff']; try easy. clear Hdiffcons.
      exists (Input (diff' ++ next1) (x :: pref2)). split.
      + rewrite Hnext12, <- app_comm_cons. simpl. reflexivity.
      + apply ss_fwd_diff. simpl in Hadv. destruct next1 as [|h next1']; try discriminate.
        injection Hadv as <- <-. exists (diff' ++ [h]). split; [|split].
        * now destruct diff'.
        * rewrite <- app_assoc. reflexivity.
        * rewrite Hpref12, rev_app_distr. simpl. rewrite <- app_assoc. reflexivity.
    - (* Backward *)
      apply ss_bwd_diff in Hss. destruct Hss as [diff [Hdiffcons [Hnext12 Hpref12]]].
      apply exists_last in Hdiffcons. destruct Hdiffcons as [diff' [a Heqdiff]]. subst diff.
      exists (Input (a :: next2) (rev diff' ++ pref1)). split.
      + rewrite Hpref12, rev_app_distr. simpl. reflexivity.
      + apply ss_bwd_diff. simpl in Hadv. destruct pref1 as [|h pref1']; try discriminate.
        injection Hadv as <- <-. exists (h :: diff'). split; [|split].
        * easy.
        * rewrite Hnext12, <- app_comm_cons, <- app_assoc. reflexivity.
        * simpl. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma strict_no_advance:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir ->
      advance_input inp2 dir = None ->
      False.
  Proof.
    intros inp1 inp2 dir Hss. induction Hss.
    - intro. congruence.
    - auto.
  Qed.

  Lemma advance_suffix:
    forall inp inpnext inpsuf dir,
      strict_suffix inpsuf inp dir ->
      advance_input inp dir = Some inpnext ->
      inpnext = inpsuf \/ strict_suffix inpsuf inpnext dir.
  Proof.
    intros [next pref] [nextnext nextpref] [sufnext sufpref] dir Hss Hadv.
    destruct dir.
    - (* Forward *)
      apply ss_fwd_diff in Hss. destruct Hss as [diff [Hdiffcons [Hnext_sufnext Hpref_sufpref]]].
      destruct diff as [|x diff']; try easy. clear Hdiffcons.
      destruct diff' as [|y diff''].
      + rewrite Hnext_sufnext in Hadv. simpl in *. injection Hadv as <- <-. left. f_equal. congruence.
      + right. apply ss_fwd_diff. rewrite Hnext_sufnext in Hadv. simpl in *.
        injection Hadv as <- <-. exists (y :: diff''). split; [|split].
        * easy.
        * apply app_comm_cons.
        * simpl. rewrite <- app_assoc. do 2 rewrite <- app_assoc in Hpref_sufpref. auto.
    - (* Backward *)
      apply ss_bwd_diff in Hss. destruct Hss as [diff [Hdiffcons [Hnext_sufnext Hpref_sufpref]]].
      apply exists_last in Hdiffcons. destruct Hdiffcons as [diff' [x Heqdiff]]. subst diff.
      destruct (decide_nil diff') as [Hnil | Hnotnil].
      + subst diff'. rewrite Hpref_sufpref in Hadv. simpl in *. injection Hadv as <- <-. left. f_equal. congruence.
      + right. apply exists_last in Hnotnil. destruct Hnotnil as [diff'' [y Heqdiff']]. subst diff'.
        apply ss_bwd_diff. rewrite Hpref_sufpref, rev_app_distr in Hadv. simpl in *.
        injection Hadv as <- <-. exists (diff'' ++ [y]). split; [|split].
        * now destruct diff''.
        * rewrite <- app_assoc in Hnext_sufnext. auto.
        * reflexivity.
  Qed.

  Lemma ss_neq:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir -> inp1 <> inp2.
  Proof.
    intros inp1 inp2 dir Hss Habs. subst inp2.
    pose proof strict_suffix_current inp1 inp1 dir Hss. lia.
  Qed.

  (** * Prefixes *)

  (* In general you should use strict_suffix in definitions. *)
  (* The usage of input_prefix should be reserved for scenarios *)
  (* where you need the induction to have reflexive base case, *)
  (* and the inductive step to build from the biggest to smallest *)
  (* prefixes. *)

  (* relation that one input is a non-strict prefix of another *)
  Inductive input_prefix : input -> input -> Direction -> Prop :=
  | ip_eq : forall inp dir, input_prefix inp inp dir
  | ip_prev : forall inp1 inp2 inp3 dir,
      advance_input inp1 dir = Some inp2 ->
      input_prefix inp2 inp3 dir ->
      input_prefix inp1 inp3 dir.

  Lemma ip_prev':
    forall inp1 inp2 inp3 dir,
      input_prefix inp1 inp2 dir ->
      advance_input inp2 dir = Some inp3 ->
      input_prefix inp1 inp3 dir.
  Proof. induction 1; eauto using ip_prev, ip_eq. Qed.

  (* equivalence between input_prefix and strict_suffix *)
  Lemma input_prefix_strict_suffix:
    forall i1 i2 dir,
      input_prefix i1 i2 dir <->
        i2 = i1 \/ strict_suffix i2 i1 dir.
  Proof.
    split; intros H.
    - induction H; [auto|].
      destruct IHinput_prefix; subst; eauto using ss_advance, ss_next'.
    - destruct H; [subst; auto using ip_eq|].
      induction H; subst; eauto using ip_eq, ip_prev, ip_prev'.
  Qed.

End StrictSuffix.
