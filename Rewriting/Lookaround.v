From Linden Require Import ProofSetup.
From Linden.Semantics Require Import Examples Chars Groups GroupMapLemmas.
From Linden.Rewriting Require Import Unamb.
Import FlatMap.

(** * Some rewrites of lookarounds *)

Section Lookarounds.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Lemma lookaround_min_quantifier_epsilon:
    forall greedy d lk r min,
      Quantified greedy min d (Lookaround lk r)
        ≅[rer] Quantified greedy min 0 r.
  Proof.
    
    
    Lemma lookaround_quantifier_epsilon:
      forall greedy d lk r,
        Quantified greedy 0 d (Lookaround lk r)
          ≅[rer] Quantified greedy 0 0 r.
    Proof.
      intros greedy d lk r.
      split. simpl. solve_groups_equiv.
      intros i g t1 t2 T1 T2.
      unfold tree_equiv_tr_dir.
      inversion T2; inversion SKIP; subst.
      clear T2 SKIP. 2: destruct plus; discriminate.
      inversion T1; subst.
      inversion SKIP; reflexivity.
      inversion ISTREE1; try inversion TREECONT; subst.
      exfalso; eapply StrictSuffix.ss_irreflexive; eauto.
      all: destruct greedy; simpl; inversion SKIP; subst.
      all: destruct (positivity lk), (tree_leaves treelk (GroupMap.reset (def_groups r) g) i (lk_dir lk)); simpl; try destruct l; reflexivity.
    Qed.

    Ltac lookaround_simpl :=
      repeat (match goal with
              | [H: _ :: _ = [] |- _] => discriminate
              | [H: Some ?a = None |- _] => discriminate
              | [H: None = Some _ |- _] => discriminate
              | [|- leaves_equiv _ ?a ?a] => reflexivity
              | [H: leaves_equiv _ ?a ?b |- leaves_equiv _ ?b ?a] => symmetry; assumption
              | [H: is_tree _ [Areg (Lookaround _ _)] _ _ _ _ |- _ ] => (inversion H; subst; clear H)
              | [H: is_tree _ [Areg (Sequence _ _)] _ _ _ _ |- _ ] => (inversion H; subst; clear H)
              | [H: is_tree _ (Areg (Lookaround _ _) ::_ )  _ _ _ _ |- _ ] => (inversion H; subst; clear H)
              | [H: is_tree _ [] _ _ _ _ |- _ ] => (inversion H; subst; clear H; simpl)
              | [H1: is_tree _ ?a _ _ _ ?ta, H2: is_tree _ ?a _ _ _ ?tb |- _ ] =>  pose proof (is_tree_determ _ _ _ _ _ _  _ H1 H2); subst; clear H2
              | [H: Some ?a = Some ?b |- _] => inversion H; subst; clear H
              | [H: ?a :: _ = ?b :: _ |- _] => inversion H; subst; clear H
              | [H: context[lk_result] |- _ ] => unfold lk_result in H
              | [H: context[tree_res] |- _] => rewrite first_tree_leaf in H
              | [H: lk_dir ?lk = _ |- context[lk_dir ?lk]] => rewrite H
              | [H1: lk_dir ?lk = _, H2: context[lk_dir ?lk] |- _] => rewrite H1 in H2
              | _ => simpl in *; auto
              end).

    Lemma lookaround_advances:
      forall i g g3 dir t1 t2 t3 lk r1 r2 acts, 
        is_tree rer ([Areg (Lookaround lk r1)] ++ acts) i g dir t1 ->
        is_tree rer r2 i g3 dir t2 ->
        is_tree rer [Areg r1] i g (lk_dir lk) t3 ->  
        ((exists g2 t4,
             is_tree rer acts i g2 dir t4 /\
               leaves_equiv [] (tree_leaves t2 g3 i dir) (tree_leaves t4 g2 i dir) /\
               lk_result lk t3 g i = Some g2)
         \/ (
             tree_leaves t2 g3 i dir = [] /\
               lk_result lk t3 g i = None
        )) ->
        leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t2 g3 i dir).
    Proof.
      intros i g g3 dir t1 t2 t3 lk r1 r2 acts T1 T2 T3 [[g2 [t4 [T4 [lEq lkRes]]]] | [lEq lkREs]].
      all: lookaround_simpl; destruct (positivity lk), (tree_leaves treelk g i (lk_dir lk)); lookaround_simpl.
      all: try destruct l; lookaround_simpl; rewrite lEq; reflexivity.
    Qed.


    Lemma lookaround_seq_rec:
      forall lk r s,
        lk_dir lk = forward ->
        positivity lk = true ->
        (Lookaround lk (Sequence (Lookaround lk r) s))
          ≅[rer][forward] Sequence (Lookaround lk r) (Lookaround lk s).
    Proof.
      intros lk r s lkDIR lkPOS.
      split. simpl. solve_groups_equiv.
      intros i g t1 t2 T1 T2. unfold tree_equiv_tr_dir.
      inversion T2; subst. simpl in CONT. symmetry.
      pose proof (is_tree_productivity rer [Areg r] i g (lk_dir lk)) as [t3 T3].
      eapply lookaround_advances with (acts := [Areg (Lookaround lk s)]); eauto.
      remember (lk_result lk t3 g i) as l1. destruct l1.
      - left. exists g0. pose proof (is_tree_productivity rer [Areg (Lookaround lk s)] i g0 forward) as [t4 T4]. exists t4. split; auto. split; auto.
        pose proof (is_tree_productivity rer [Areg s] i g0 (lk_dir lk)) as [t5 T5].
        symmetry. eapply lookaround_advances with (acts := []); eauto.
        remember (lk_result lk t5 g0 i) as l2. destruct l2.
        + left. exists g1. pose proof (is_tree_productivity rer [] i g1 forward) as [t6 T6]. exists t6.
          split; auto. split; auto.
          pose proof (is_tree_productivity rer [Areg (Sequence (Lookaround lk r) s)] i g (lk_dir lk)) as [t7 T7]. 
          eapply lookaround_advances with (acts := []); eauto.
          left. exists g1, t6. repeat split; auto. reflexivity.
          rewrite lkDIR in T7. inversion T7; subst; simpl in CONT0.
          inversion CONT0; subst; eapply is_tree_determ with (t1 := treelk) in T3; eauto; subst.    
          2: rewrite <- Heql1 in FAIL_LK; discriminate.
          unfold lk_result; simpl. unfold lk_result in RES_LK, Heql2.
          remember (tree_res t3 g i (lk_dir lk)) as l1.
          unfold lk_result in Heql1.
          destruct (positivity lk); destruct l1; try discriminate; try destruct l; rewrite <- Heql0 in Heql1; inversion Heql1; inversion RES_LK; subst.
          all: eapply is_tree_determ with (t1 := treecont) in T5; try rewrite lkDIR; eauto; subst.
          all: rewrite Heql2; rewrite lkDIR; reflexivity.
        + right. split; auto. inversion T1; subst. clear T1.
          rewrite lkDIR in TREELK. inversion TREELK; subst.
          simpl in CONT0.
          inversion CONT0; eapply is_tree_determ with (t1 := treelk0) in T3; eauto; subst.
          2: rewrite FAIL_LK in Heql1; discriminate.
          rewrite RES_LK0 in Heql1; inversion Heql1; subst. rewrite lkDIR in T5.
          eapply is_tree_determ with (t1 := treecont0) in T5; eauto; subst.
          inversion TREECONT; subst. simpl.
          unfold lk_result in Heql2. unfold lk_result in RES_LK0; rewrite first_tree_leaf in Heql2, RES_LK0.
          destruct (positivity lk), (tree_leaves t3 g i (lk_dir lk)); try destruct l; try discriminate; try reflexivity; simpl in *.
          all: try inversion RES_LK0; subst.
          all: try destruct (tree_leaves t5 gmlk0 i (lk_dir lk)).
          all: try reflexivity; try (simpl in Heql2; destruct l; discriminate).
      - right. split; auto. inversion T1; auto; subst.
        rewrite lkDIR in TREELK. inversion TREELK; subst.
        simpl in CONT0. inversion CONT0; subst; simpl.
        all: eapply is_tree_determ with (t1 := treelk0) in T3; eauto; subst.
        rewrite RES_LK0 in Heql1. inversion Heql1.
        unfold lk_result in RES_LK, FAIL_LK. rewrite lkPOS; reflexivity.
    Qed.

    Lemma lookaround_no_groups_epsilons:
      forall lk r,
        def_groups r = [] ->
        positivity lk = true ->
        Disjunction (Lookaround lk r) Epsilon ≅[rer] Epsilon.
    Proof.
      intros lk r rEmpt lkTrue.
      split. simpl. rewrite rEmpt. reflexivity.
      intros i g t1 t2 T1 T2. unfold tree_equiv_tr_dir.
      inversion T1; inversion T2;  inversion ISTREE2; inversion ISTREE; inversion ISTREE0; subst.
      clear T1 T2 ISTREE2 ISTREE ISTREE0. simpl.
      inversion ISTREE1; subst.
      - lookaround_simpl; simpl.
        remember (tree_leaves treelk g i (lk_dir lk)) as l2.
        destruct (positivity lk), l2; simpl; eauto.
        all: try destruct l; leaves_equiv_t.
        eapply emptygroups_const_groups in TREELK; eauto.
        2: rewrite <- Heql2; auto; rewrite app_cons; eapply in_app_iff; left; simpl; auto.
        subst. leaves_equiv_t.
      - simpl. reflexivity.
    Qed.
    
    
    Lemma lookaround_opps_fails:
      forall lk1 lk2 r ,
        def_groups r = [] ->
        positivity lk1 = false ->
        positivity lk2 = true ->
        lk_dir lk1 = lk_dir lk2 ->
        (Sequence (Lookaround lk1 r) (Lookaround lk2 r)) ≅[rer][forward] fail_regex.
    Proof.
      intros lk1 lk2 r GROUPEMPT neqPos eqDir lkEq.
      split. simpl. rewrite GROUPEMPT. solve_groups_equiv.
      intros i g t1 t2 T1 T2. unfold tree_equiv_tr_dir.
      erewrite fail_regex_fail with (t := t2); eauto.
      lookaround_simpl.
      - remember (tree_leaves treelk g i (lk_dir lk2)) as l1.
        destruct (positivity lk1), (positivity lk2), l1; simpl in RES_LK.
        all: try reflexivity; try discriminate.
        inversion RES_LK; subst. lookaround_simpl.
        rewrite <- Heql1. reflexivity.
      - destruct (positivity lk1), (tree_leaves treelk g i (lk_dir lk2)); try destruct l ; reflexivity.
    Qed.

    Lemma lk_result_eqs_impl_lk_eqs:
      forall lk1 r1 r2 lk2  i g t1 t2  dir,
        is_tree rer [Areg (Lookaround lk1 r1)] i g dir t1 ->
        is_tree rer [Areg (Lookaround lk2 r2)] i g  dir t2 ->
        (forall t3 t4,
            is_tree rer [Areg r1] i g (lk_dir lk1) t3 ->
            is_tree rer [Areg r2] i g  (lk_dir lk2) t4 -> 
            (lk_result lk1 t3 g i = lk_result lk2 t4 g i)) ->
        leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t2 g i dir).
    Proof.
      intros.
      pose proof (is_tree_productivity rer [Areg r1] i g (lk_dir lk1)) as [t3 T3].
      pose proof (is_tree_productivity rer [Areg r2] i g (lk_dir lk2)) as [t4 T4].
      specialize (H1 _ _ T3 T4). 
      eapply lookaround_advances with (acts := []); eauto.
      remember (lk_result lk1 t3 g i) as l1. destruct l1.
      - left. exists g0, Match. split. constructor. split; auto.
        eapply lookaround_advances with (acts := []); eauto. constructor.
        left. exists g0, Match. split. constructor. split; auto. reflexivity.
      - right. split; auto.
        inversion H0; subst. 2: reflexivity.
        eapply is_tree_determ with (t1 := t4) in TREELK; eauto; subst.
        rewrite <- H1  in RES_LK. discriminate.
    Qed.

    Lemma leaves_equiv_impl_lk_equiv:
      forall r acts1 acts2 t1 t2 g i lk1,
        is_tree rer ([Areg r] ++ acts1) i g (lk_dir lk1) t1 ->
        is_tree rer ([Areg r] ++ acts2) i g (lk_dir lk1) t2 ->
        (forall t3 t4 i0 g0,
            is_tree rer acts1 i0 g0 (lk_dir lk1) t3 ->
            is_tree rer acts2 i0 g0 (lk_dir lk1) t4 ->
            lk_result lk1 t3 g0 i0 = lk_result lk1 t4 g0 i0) ->
        lk_result lk1 t1 g i = lk_result lk1 t2 g i.
    Proof.
      intros. unfold lk_result.
      pose proof (is_tree_productivity rer [Areg r] i g (lk_dir lk1)) as [t5 T5].
      rewrite app_cons in H, H0.
      eapply leaves_concat with (act1 := [Areg r]) in H, H0; eauto.
      etransitivity; rewrite first_tree_leaf. reflexivity.
      remember (tree_leaves t5 g i (lk_dir lk1)) as p1.
      remember (tree_leaves t1 g i (lk_dir lk1)) as p2.
      remember (tree_leaves t2 g i (lk_dir lk1)) as p3.
      clear Heqp1 Heqp3 Heqp2. revert p2 H p3 H0.
      induction p1; intros.
      - inversion H0; inversion H; reflexivity.
      - inversion H; inversion H0; subst.
        inversion HEAD; inversion HEAD0; subst.
        specialize (H1 _ _ _ _ TREE TREE0).
        unfold lk_result in H1. rewrite first_tree_leaf in H1.
        symmetry in H1. rewrite first_tree_leaf in H1.
        destruct (positivity lk1), (tree_leaves t (snd a) (fst a) (lk_dir lk1)), (tree_leaves t0 (snd a) (fst a) (lk_dir lk1)); try destruct l; try destruct l1; simpl; simpl in H1; try reflexivity; try discriminate.
        eapply IHp1; eauto.
        symmetry. assumption.
        eapply IHp1; eauto.
    Qed.
    
    

    Lemma lookaround_eqs_lookaround_tail:
      forall r s,
        (Lookaround LookAhead (Sequence r s)) ≅[rer] (Lookaround LookAhead (Sequence r (Lookaround LookAhead s))).
    Proof.
      intros r s. split. simpl. groups_equiv_eq.
      intros i g t1 t2 T1 T2. unfold tree_equiv_tr_dir.
      eapply lk_result_eqs_impl_lk_eqs; eauto. intros. clear t1 T1 t2 T2.
      inversion H; inversion H0; subst. simpl in CONT, CONT0. clear H H0.
      eapply leaves_equiv_impl_lk_equiv; eauto. exact CONT.  exact CONT0. intros.
      lookaround_simpl. unfold lk_result. simpl.
      destruct (tree_res treelk g0 i0 forward); try destruct l; reflexivity.
      unfold lk_result. simpl. rewrite first_tree_leaf.
      assumption.
    Qed.

    Lemma lk_result_returns:
      forall r lk t g g0 i,
        def_groups r = [] ->
        is_tree rer [Areg r] i g (lk_dir lk) t ->
        lk_result lk t g i = Some g0 ->
        g = g0.
    Proof.
      intros r lk t g g0 i GROUPEMPT T1 LKRes.
      unfold def_groups in GROUPEMPT.
      unfold lk_result in LKRes. destruct (positivity lk).
      2: destruct (tree_res t g i (lk_dir lk)); inversion LKRes; reflexivity.
      rewrite first_tree_leaf in LKRes.
      remember (tree_leaves t g i (lk_dir lk)) as Tl1. destruct Tl1.
      simpl in LKRes; discriminate.
      destruct l.
      eapply emptygroups_const_groups; eauto. 
      rewrite <- HeqTl1. simpl. simpl in LKRes. inversion LKRes; subst.
      left. reflexivity.
    Qed.
    

    Lemma charall_lk_rest_returns:
      forall greedy d i g dir t ,
        is_tree rer [Areg (Quantified greedy 0 d (Character CdAll))] i g dir t ->
        exists g2, lk_result LookAhead t g i = Some g2.
    Proof.
      intros. unfold lk_result.
      destruct greedy. 
      2: inversion H; inversion SKIP; subst; simpl; exists g; reflexivity.
      inversion H; subst; simpl.
      - inversion SKIP; exists g; reflexivity.
      - inversion SKIP; subst. unfold seqop. destruct (tree_res titer g i forward).
        destruct l. exists g0; reflexivity.
        simpl. exists g; reflexivity.
    Qed.
    
    
    Lemma lookaround_lk_char:
      forall r s greedy d,
        (Lookaround LookAhead (Sequence r (Sequence (Lookaround LookAhead s) (Quantified greedy 0 d (Character CdAll)))))
          ≅[rer] (Lookaround LookAhead (Sequence r s)).
    Proof.
      intros r s greedy d NOGROUP.
      symmetry. etransitivity. eapply lookaround_eqs_lookaround_tail.
      split. simpl. solve_groups_equiv.
      intros i g t1 t2 T1 T2. unfold tree_equiv_tr_dir.
      eapply lk_result_eqs_impl_lk_eqs; eauto. clear t1 t2 T1 T2. intros t1 t2 T1 T2.
      inversion T1; inversion T2; subst. clear T1 T2. simpl in CONT, CONT0.
      eapply leaves_equiv_impl_lk_equiv; eauto; simpl. exact CONT. exact CONT0.
      clear t1 t2 CONT CONT0.
      intros t1 t2 i0 g0 T1 T2. inversion T2; subst. simpl in CONT. 
      eapply leaves_equiv_impl_lk_equiv; simpl. exact T1. exact CONT. intros.
      inversion H; subst. unfold lk_result at 1. simpl. symmetry.
      epose proof (charall_lk_rest_returns _ _ _ _ _ _ H0) as [g2 lkRes].
      assert (def_groups (Quantified greedy 0 d (Character CdAll)) = []) as GROUPEMPT by reflexivity.
      eapply lk_result_returns in GROUPEMPT; eauto; subst; simpl; eauto. 
    Qed.

    Lemma lookaround_equiv:
      forall r s lk, 
        r ≅[rer] s ->
        Lookaround lk r ≅[rer] Lookaround lk s.
    Proof.
      intros r s lk rEqs dir.
      split. destruct (rEqs dir). auto.
      intros i g t1 t2 T1 T2. unfold tree_equiv_tr_dir.
      eapply lk_result_eqs_impl_lk_eqs; eauto. intros t3 t4 T3 T4.
      eapply equiv_lk_result_same; eauto.
    Qed.
    
End Lookarounds.
