From Linden Require Import ProofSetup.
From Linden.Semantics Require Import Examples.
From Linden.Rewriting Require Import Examples FlatMap ForcedQuant Associativity Distributivity RegexpTree Unamb.


Section ScottOwens.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Lemma fails_fails_tail:
    forall dir r, 
      actions_equiv_dir rer dir [Areg r; Areg fail_regex] [Areg fail_regex].
  Proof.
    intros dir r i g t1 t2 T1 T2. unfold tree_equiv_tr_dir.
    specialize (is_tree_productivity rer [Areg r] i g dir ) as [t3 T3].
    rewrite app_cons in T1. eapply leaves_concat with (act1 := [Areg r]) in T1; eauto.
    pose proof  (fail_regex_fail _ _ _ _ _ T2) as FRF. rewrite FRF.
    remember (tree_leaves t3 g i dir) as l3.
    remember (tree_leaves t1 g i dir) as l1.
    clear Heql3 Heql1. generalize dependent l1.
    induction l3; intros l1 T1. inversion T1. reflexivity.
    inversion T1; subst. specialize (IHl3 lmapped FM).
    inversion HEAD; subst. destruct a; simpl in *.
    rewrite (fail_regex_fail _ _ _ _ _ TREE). inversion IHl3. reflexivity.
    inversion SEEN.
  Qed.
  
  Lemma fails_fail_left:
    forall r dir,
      def_groups r = [] -> 
      Sequence fail_regex r ≅[rer][dir] fail_regex.
  Proof.
    intros r dir. split. simpl. rewrite H. reflexivity.
    intros i g  t1 t2 T1 T2.
    unfold tree_equiv_tr_dir.
    pose proof  (fail_regex_fail _ _ _ _ _ T2) as FRF.
    destruct dir; inversion T1; subst; simpl in CONT.
    rewrite app_cons in CONT.
    eapply leaves_concat with (act1 := [Areg fail_regex]) in CONT; eauto.
    rewrite FRF in CONT. inversion CONT. rewrite FRF. reflexivity.
    eapply fails_fails_tail; eauto.
  Qed.

  Lemma fails_fail_right:
    forall r dir,
      def_groups r = [] ->
      Sequence r fail_regex ≅[rer][dir] fail_regex.
  Proof.
    intros r dir. split. simpl. rewrite H. reflexivity.
    intros i g  t1 t2 T1 T2.
    unfold tree_equiv_tr_dir.
    pose proof  (fail_regex_fail _ _ _ _ _ T2) as FRF.
    destruct dir; inversion T1; subst; simpl in CONT.
    eapply fails_fails_tail; eauto.
    rewrite app_cons in CONT.
    eapply leaves_concat with (act1 := [Areg fail_regex]) in CONT; eauto.
    rewrite FRF in CONT. inversion CONT. rewrite FRF. reflexivity.
  Qed.

  Lemma disj_shrinks_dir:
    forall r dir,
      Disjunction r r ≅[rer][dir] r.
  Proof.
    intros r dir.
    split. simpl. solve_groups_equiv.
    intros i g t1 t2 T1 T2. inversion T1; subst.
    unfold tree_equiv_tr_dir. simpl.
    specialize (is_tree_determ _ _ _ _ _ _ _ T2 ISTREE1) as p1.
    specialize (is_tree_determ _ _ _ _ _ _ _ T2 ISTREE2) as p2. subst.
    symmetry. eapply leaves_equiv_repet.
  Qed.



  Lemma disj_equiv_assoc_dir:
    forall r0 r1 r2 dir,
      Disjunction r0 (Disjunction r1 r2) ≅[rer][dir] Disjunction (Disjunction r0 r1) r2.
  Proof.
    intros r0 r1 r2 dir.
    split. simpl. solve_groups_equiv.
    intros i g t1 t2 T1 T2.
    inversion T1; inversion T2; inversion ISTREE2; inversion ISTREE0; subst.
    unfold tree_equiv_tr_dir. simpl.
    assert (t0 = t8 /\ t6 = t9 /\ t7 = t5) as [e1 [e2 e3]]. 2: subst.
    repeat constructor; eapply is_tree_determ; eauto.
    rewrite app_assoc. reflexivity.
  Qed.

  Lemma disj_equiv_fails:
    forall r,
      Disjunction fail_regex r ≅[rer] r.
  Proof.
    split. simpl. reflexivity.
    intros i g t1 t2 T1 T2. inversion T1; subst.
    unfold tree_equiv_tr_dir. simpl.
    specialize (is_tree_determ _ _ _ _ _ _ _ ISTREE2 T2) as eq1. subst.
    rewrite (fail_regex_fail _ _ _ _ _ ISTREE1). simpl. reflexivity.
  Qed.

  Lemma failregex_closed_eqs_epsilon:
    forall greedy delta,
      (Quantified greedy 0 delta fail_regex)  ≅[rer] Epsilon.
  Proof.
    intros greedy delta. split. simpl. reflexivity.
    intros i g t1 t2 T1 T2. inversion T2; inversion T1; subst.
    inversion ISTREE; inversion SKIP; subst. reflexivity.
    inversion ISTREE; inversion SKIP; subst. simpl.
    specialize (is_tree_productivity rer [Areg fail_regex] i (GroupMap.reset (def_groups fail_regex) g) dir) as [t3 T3].
    rewrite app_cons in ISTREE1.  eapply leaves_concat with (act1 := [Areg fail_regex]) in ISTREE1; eauto.
    rewrite (fail_regex_fail _ _ _ _ _ T3) in ISTREE1. inversion ISTREE1; subst. unfold tree_equiv_tr_dir.
    destruct greedy; simpl; rewrite <- H; reflexivity.
  Qed.


  Lemma empt_quantified_equiv_empt:
    forall greedy min delta,
      (Quantified greedy min delta Epsilon)  ≅[rer] Epsilon.
  Proof.
    intros greedy min delta. split. simpl. reflexivity.
    intros i g t1 t2 T1 T2. inversion T2; inversion ISTREE; subst.
    unfold tree_equiv_tr_dir. simpl.
    generalize dependent t1.
    induction min; intros t1 T1.
    - inversion T1; inversion SKIP; subst; simpl. reflexivity.
      destruct greedy; simpl.
      1, 2: inversion ISTREE1; inversion ISTREE0; subst.
      1, 3: pose proof (StrictSuffix.ss_irreflexive i dir); contradiction.
      1, 2:  simpl; reflexivity.
    - inversion T1; inversion ISTREE1; subst. simpl in *.
      eapply IHmin; eauto.
  Qed.
  
  Lemma skip_check:
    forall i1 act1 act2 dir,
    actions_equiv_dir rer dir ([Acheck i1] ++ act1 ++ [Acheck i1] ++ act2) ([Acheck i1] ++ act1 ++ act2).
  Proof.   
    intros i act1 act2 dir.
    etransitivity. all: rewrite app_assoc.
    reflexivity. rewrite app_assoc. eapply app_eq_right.
    intros i1 g1 t1 t2 T1 T2.
    inversion T1; inversion T2; try contradiction; subst; auto. 2: reflexivity.
    unfold tree_equiv_tr_dir. simpl.
    eapply leaves_concat with (act1 := act1) in TREECONT; eauto.
    assert (forall inp1 gm1, In (inp1, gm1) (tree_leaves treecont0 g1 i1 dir) -> i1 = inp1 \/ StrictSuffix.strict_suffix inp1 i1 dir). {
      intros. eapply input_only_forward in H; eauto.
    }
    remember (tree_leaves treecont0 g1 i1 dir) as l1.
    remember (tree_leaves treecont g1 i1 dir) as l2.
    clear Heql1 Heql2 T1 T2 TREECONT0.
    generalize dependent l2.
    induction l1; intros; inversion TREECONT. reflexivity.
    inversion HEAD; subst. destruct a; simpl in *.
    rewrite app_cons. eapply leaves_equiv_app. 2: eapply IHl1; eauto.
    inversion TREE. inversion TREECONT0; subst. reflexivity.
    assert (i1 = i0 \/ StrictSuffix.strict_suffix i0 i1 dir) as [c1 | c2] by (eapply H; left; reflexivity).
    subst. contradiction.
    subst. Search StrictSuffix.strict_suffix. eapply StrictSuffix.strict_suffix_trans in PROGRESS; eauto. contradiction.
  Qed.
    

                      
  Lemma quantified_true_quantified_eq_quantified:
    forall r,
      def_groups r = [] ->
      (Quantified true 0 +∞ r) ≅[rer] (Quantified true 0 +∞ ((Quantified true 0 +∞ r))).
  Proof.
    intros r GROUPEMPT dir.
    split. simpl. reflexivity.
    intros i.
    remember (remaining_length i dir) as l.
    assert (Hlength_le: remaining_length i dir <= l) by lia. clear Heql. generalize dependent i.
    induction l; intros i IL g t1 t2 T1 T2.
    + eapply quantifier_null_length in T1; auto.
      eapply quantifier_null_length in T2; auto.
      unfold tree_equiv_tr_dir. rewrite T1, T2. reflexivity.
    + apply Nat.lt_eq_cases in IL as [c1 | c2]. eapply IHl; eauto. lia.
      unfold tree_equiv_tr_dir.
      inversion T1; inversion T2; inversion ISTREE0; subst. simpl in *.
      destruct plus0; discriminate.
      destruct plus0, plus, plus1; try discriminate. simpl in *.
      inversion SKIP1.  pose proof (StrictSuffix.ss_irreflexive i dir).
      contradiction. subst. rewrite <- app_assoc. simpl.
      apply leaves_equiv_app.
      2: inversion SKIP0; inversion SKIP; subst; reflexivity.
      clear CHECKFAIL SKIP1 H17 SKIP T1 T2 ISTREE0.
      pose proof (is_tree_productivity rer [Areg r; Acheck i; Areg (Quantified true 0 +∞ r); Areg (Quantified true 0 +∞ (Quantified true 0 +∞ r))] i (GroupMap.reset (def_groups r) (GroupMap.reset (def_groups r) g)) dir) as [t3 T3].
      pose proof (skip_check i  [Areg (Quantified true 0 +∞ r)] [Areg (Quantified true 0 +∞ (Quantified true 0 +∞ r))] dir).
      eapply app_eq_left with (acts := [Areg r]) in H.
      simpl in H.
      etransitivity. 2: symmetry; eapply H; eauto. clear H.
      rewrite GROUPEMPT in *. simpl in *.
      eapply quantifier_inf_step_advances; eauto.
      exact ISTREE1. exact T3. intros.
      pose proof (is_tree_productivity rer [Areg (Quantified true 0 +∞ r); Areg (Quantified true 0  +∞ r)] i0 gm dir) as [t4 T4].
      etransitivity. symmetry. eapply atmost_atmost_equiv_actions_minf; eauto.
      rewrite app_cons in H2, T4. eapply leaves_concat with (act1 := [Areg (Quantified true 0 +∞ r)])in H2, T4; eauto.
      Search FlatMap.
      eapply flatmap_leaves_equiv_r_prop with (l := (tree_leaves t1 gm i0 dir)) (P := (fun (leaf: leaf) => let (i', g') := leaf in remaining_length i' dir < S l)); eauto.
      intros le P l1 l2 a1 a2. inversion a1; inversion a2; subst.
      destruct le; simpl in *. eapply IHl; eauto. lia.
      apply Forall_forall. intros x inX. destruct x.
      eapply input_only_forward in H0; eauto. destruct H0. 
      subst. lia. Search StrictSuffix.strict_suffix. apply strict_suffix_remaining_length in H0. lia.
  Qed.

  Lemma quantified_false_quantified_eq_quantified:
    forall r,
      def_groups r = [] ->
      (Quantified true 0 +∞ r) ≅[rer] (Quantified true 0 +∞ ((Quantified false 0 +∞ r))).
  Proof.
    intros r GROUPEMPT dir.
    split. simpl. reflexivity.
    intros i.
    unfold tree_equiv_tr_dir.
    remember (remaining_length i dir) as l.
    assert (Hlength_le: remaining_length i dir <= l) by lia. clear Heql. generalize dependent i.
    induction l; intros i IL g t1 t2 T1 T2.
    - eapply quantifier_null_length in T1, T2; eauto.
      rewrite T1, T2; reflexivity.
    - apply Nat.lt_eq_cases in IL as [c1 | c2]. eapply IHl; eauto. lia.
      inversion T1; inversion T2; inversion ISTREE0; subst.
      destruct plus0; discriminate.
      destruct plus, plus0, plus1; try discriminate.
      simpl in *.  inversion SKIP1. exfalso. eapply StrictSuffix.ss_irreflexive; eauto.
      subst. simpl in *. eapply leaves_equiv_app.
      2: inversion SKIP; inversion SKIP0; subst; reflexivity.
      clear T1 T2 SKIP1 ISTREE0 CHECKFAIL H17 H1 H9 SKIP SKIP0.
      pose proof (is_tree_productivity rer [Areg r; Acheck i; Areg (Quantified false 0 +∞ r); Areg (Quantified true 0 +∞ (Quantified false 0 +∞ r))] i g dir) as [t3 T3].
      pose proof (skip_check i  [Areg (Quantified false 0 +∞ r)] [Areg (Quantified true 0 +∞ (Quantified false 0 +∞ r))] dir). eapply app_eq_left with (acts := [Areg r]) in H.
      simpl in H. rewrite GROUPEMPT in *. simpl in *. etransitivity.
      2: symmetry; eapply H; auto. 2: exact T3.
      eapply quantifier_inf_step_advances with (r := r); eauto.
      exact ISTREE1. exact T3. intros.
      pose proof (is_tree_productivity rer [Areg (Quantified false 0 +∞  r); Areg (Quantified true 0 +∞ r)] i0 gm dir) as [t4 T4]. etransitivity.
      symmetry. eapply atmost_atmost_equiv_actions_false_trueinf; eauto.
      pose proof (is_tree_productivity rer [Areg (Quantified false 0 +∞  r)] i0 gm dir) as [t5 T5]. 
      rewrite app_cons in H2, T4. eapply leaves_concat with (act1 := [Areg (Quantified false 0 +∞ r)]) in H2, T4; eauto. Search FlatMap.
      eapply flatmap_leaves_equiv_r_prop with (l := (tree_leaves t5 gm i0 dir)) (P := (fun (leaf: leaf) => let (i', g') := leaf in remaining_length i' dir < S l)); eauto.
      intros le P l1 l2 a1 a2. inversion a1; inversion a2; subst.
      destruct le; simpl in *. eapply IHl; eauto. lia.
      apply Forall_forall. intros x inX. destruct x.
      eapply input_only_forward in T5; eauto. destruct T5. 
      subst. lia. apply strict_suffix_remaining_length in H3. lia.
  Qed.
      
End ScottOwens.
