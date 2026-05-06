From Linden Require Import Chars Parameters LWParameters.
From Linden Require Import ListLemmas.
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
          * simpl in *. rewrite length_app in Hlendiff. simpl in *. apply IH with (diff := x :: diff'').
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
          * simpl in *. rewrite length_app in Hlendiff. simpl in *. apply IH with (diff := diff'' ++ [a]).
            -- rewrite length_app. simpl. lia.
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

  Lemma advance_input_n_succ_success:
    forall inp n dir inpn inpn_adv,
      inpn = advance_input_n inp n dir ->
      advance_input inpn dir = Some inpn_adv ->
      advance_input_n inp (S n) dir = inpn_adv.
  Proof.
    intros [next pref] n [] inpn inpn_adv Heqinpn Hadv.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n next) as [|h next'] eqn:Hskipn; try discriminate.
      injection Hadv as <-.
      pose proof firstn_skipn n next. rewrite Hskipn in H. rewrite <- H.
      pose proof length_skipn n next. rewrite Hskipn in H0.
      assert (Hlen: length (firstn n next) = n). {
        simpl in *.
        assert (length next > n) by lia.
        apply firstn_length_le. lia.
      }
      f_equal.
      + rewrite skipn_app. rewrite skipn_all2 by lia.
        replace (S n - length _) with 1 by lia. reflexivity.
      + rewrite app_comm_cons. f_equal. do 2 rewrite firstn_app.
        rewrite firstn_all2 by lia. replace (S n - length _) with 1 by lia. simpl.
        replace (n - length _) with 0 by lia. simpl.
        rewrite <- Hlen at 2. rewrite firstn_all. rewrite rev_app_distr. simpl.
        rewrite app_nil_r. reflexivity.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n pref) as [|h pref'] eqn:Hskipn; try discriminate.
      injection Hadv as <-.
      pose proof firstn_skipn n pref. rewrite Hskipn in H. rewrite <- H.
      pose proof length_skipn n pref. rewrite Hskipn in H0.
      assert (Hlen: length (firstn n pref) = n). {
        simpl in *.
        assert (length pref > n) by lia.
        apply firstn_length_le. lia.
      }
      f_equal.
      + rewrite app_comm_cons. f_equal. do 2 rewrite firstn_app.
        rewrite firstn_all2 by lia. replace (S n - length _) with 1 by lia. simpl.
        replace (n - length _) with 0 by lia. simpl.
        rewrite <- Hlen at 2. rewrite firstn_all. rewrite rev_app_distr. simpl.
        rewrite app_nil_r. reflexivity.
      + rewrite skipn_app. rewrite skipn_all2 by lia.
        replace (S n - length _) with 1 by lia. reflexivity.
  Qed.

  Lemma advance_input_n_succ_fail:
    forall inp n dir inpn,
      inpn = advance_input_n inp n dir ->
      advance_input inpn dir = None ->
      advance_input_n inp (S n) dir = inpn.
  Proof.
    intros [next pref] n [] inpn Heqinpn Hadv.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n next) eqn:Hskipn; try discriminate.
      f_equal.
      + apply skipn_nil_length in Hskipn. apply skipn_all2. lia.
      + apply skipn_nil_length in Hskipn. rewrite firstn_all2 by lia.
        rewrite firstn_all2 by lia. reflexivity.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n pref) eqn:Hskipn; try discriminate.
      f_equal.
      + apply skipn_nil_length in Hskipn. rewrite firstn_all2 by lia.
        rewrite firstn_all2 by lia. reflexivity.
      + apply skipn_nil_length in Hskipn. apply skipn_all2. lia.
  Qed.

  Lemma advance_input_n_suffix:
    forall inp n dir inp',
      inp' = advance_input_n inp n dir ->
      inp' = inp \/ strict_suffix inp' inp dir.
  Proof.
    intros inp n dir. induction n.
    - intro inp'. rewrite advance_input_n_0. auto.
    - intro inp'. set (inpn := advance_input_n inp n dir).
      specialize (IHn inpn eq_refl).
      destruct (advance_input inpn dir) as [inpn_adv | ] eqn:Hinpnadv.
      + rewrite advance_input_n_succ_success with (inpn := inpn) (inpn_adv := inpn_adv); auto.
        intros ->. destruct IHn as [IHn | IHn].
        * (* Impossible, but does not matter *)
          rewrite <- IHn. right. apply ss_advance. auto.
        * right. apply ss_advance in Hinpnadv. eauto using strict_suffix_trans.
      + rewrite advance_input_n_succ_fail with (inpn := inpn); auto. intros ->.
        auto.
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

  Lemma ss_irreflexive :
    forall inp dir,
      ~strict_suffix inp inp dir.
  Proof.
    intros inp dir H.
    now apply ss_neq in H.
  Qed.

  Lemma ss_asymm:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir ->
      ~strict_suffix inp2 inp1 dir.
  Proof.
    intros inp1 inp2 dir H1 H2.
    apply (ss_irreflexive inp1 dir).
    eapply strict_suffix_trans; eauto.
  Qed.


  Lemma ss_forward_backward :
    forall inp1 inp2,
      strict_suffix inp1 inp2 forward -> strict_suffix inp2 inp1 backward.
  Proof.
    remember forward as dir.
    induction 1; subst.
    - destruct inp as [next ?], next; [discriminate|injection H as <-].
      eauto using ss_advance.
    - destruct inp2 as [next ?], next; [discriminate|injection H as <-].
      eauto using ss_next'.
  Qed.

  Lemma ss_backward_forward :
    forall inp1 inp2,
      strict_suffix inp1 inp2 backward -> strict_suffix inp2 inp1 forward.
  Proof.
    remember backward as dir.
    induction 1; subst.
    - destruct inp as [? pref], pref; [discriminate|injection H as <-].
      eauto using ss_advance.
    - destruct inp2 as [? pref], pref; [discriminate|injection H as <-].
      eauto using ss_next'.
  Qed.

  Lemma ss_backward_forward_iff :
    forall inp1 inp2,
      strict_suffix inp1 inp2 backward <-> strict_suffix inp2 inp1 forward.
  Proof.
    intros. split; eauto using ss_forward_backward, ss_backward_forward.
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

From Stdlib Require Import Classes.RelationClasses.
From StrictOrderSolver Require Import Solver.

(** Solver for strict_suffixes *)
Section StrictSuffixSolver.
  Context {params: LindenParameters}.

  #[export]
  Instance StrictSuffixSO : StrictOrder (fun a b => strict_suffix a b forward).
  Proof.
    split.
    - (* Irreflexivity *)
      intros x H. eapply ss_irreflexive; eauto.
    - (* Transitivity *)
      intros x y z Hxy Hyz. eapply strict_suffix_trans; eauto.
  Qed.

  Lemma advance_input_flip:
    forall inp1 inp2,
      advance_input inp1 forward = Some inp2 <->
        advance_input inp2 backward = Some inp1.
  Proof.
    intros [next1 pref1] [next2 pref2]. split; intro H.
    - destruct next1 as [|c next1']; [discriminate|]. now injection H as <- <-.
    - destruct pref2 as [|c pref1']; [discriminate|]. now injection H as <- <-.
  Qed.

End StrictSuffixSolver.

(* canonicalize into forward strict suffixes *)
Ltac ss_canon :=
  match goal with
  (* split disjunctions *)
  | [H: _ \/ _ |- _] => destruct H; subst
  (* generate strict_suffix *)
  | |- input_prefix _ _ _ =>
    rewrite input_prefix_strict_suffix
  | [H: input_prefix _ _ _ |- _] =>
    rewrite input_prefix_strict_suffix in H
  (* simplify advance_input *)
  | [H: advance_input ?inp1 forward = Some _ |- _] =>
    eapply read_suffix in H; eauto
  | [H: context[Input ?next (?c::?pref)] |- _] =>
    (* make sure we don't prove it more than once *)
    let thm := constr:(strict_suffix (Input next (c::pref)) (Input (c::next) pref) forward) in
    lazymatch goal with
    | [H': thm |- _] => fail "already proven"
    | _ => assert thm by (apply ss_advance; simpl; reflexivity)
    end
  (* flip backward to forward *)
  | [H: advance_input ?inp1 backward = Some ?inp2 |- _] =>
    rewrite <-advance_input_flip in H
  | [H: strict_suffix _ _ backward |- _] =>
    rewrite ss_backward_forward_iff in H
  | |- strict_suffix _ _ backward =>
    rewrite ss_backward_forward_iff
  | [H: strict_suffix _ _ forward |- _] => idtac
  | [H: strict_suffix _ _ ?dir |- _] => destruct dir
  end.

(* solves a strict_suffix goal by finding a proof *)
(* or by finding a contradiction *)
(* assumes statements are canonicalized with ss_canon *)
Ltac ss_solve' :=
  match goal with
  (* input_prefix might have generated disjunctions in the goal *)
  | |- _ \/ _ => (left; ss_solve') || (right; ss_solve')
  | _ => strict_order (fun a b => strict_suffix a b forward) || easy
  end.

Ltac ss_solve := solve[repeat ss_canon; ss_solve'].
