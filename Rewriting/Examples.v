From Linden Require Import ProofSetup.
Import FlatMap.

(** * A few examples of regex rewrites *)

Section Utilities.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Lemma sequence_assoc_equiv r0 r1 r2:
    Sequence r0 (Sequence r1 r2) ≅[rer] Sequence (Sequence r0 r1) r2.
  Proof.
    (* autounfold with tree_equiv; destruct dir; tree_equiv_inv. *)
    (*tree_equiv_rw; destruct dir; compute_tr_simpl.*)
    unfold tree_equiv. intros [].
    - unfold tree_equiv_dir. split. 1: simpl; rewrite app_assoc; reflexivity.
      intros i gm tr1 tr2 TREE1 TREE2. inversion TREE1; subst. inversion TREE2; subst. simpl in *.
      clear TREE1 TREE2.
      inversion CONT0; subst. simpl in CONT1.
      clear CONT0. revert i gm tr1 tr2 CONT CONT1.
      change (actions_equiv_dir rer forward [Areg r0; Areg (Sequence r1 r2)] [Areg r0; Areg r1; Areg r2]).
      apply app_eq_left with (acts := [Areg r0]).
      unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. simpl in CONT. replace t2 with t1 by (eapply is_tree_determ; eauto). reflexivity.
    - unfold tree_equiv_dir. split. 1: simpl; rewrite app_assoc; reflexivity.
      intros i gm tr1 tr2 TREE1 TREE2. inversion TREE1; subst. inversion TREE2; subst. simpl in *.
      clear TREE1 TREE2.
      inversion CONT; subst. simpl in CONT1.
      clear CONT. revert i gm tr1 tr2 CONT1 CONT0.
      change (actions_equiv_dir rer backward [Areg r2; Areg r1; Areg r0] [Areg r2; Areg (Sequence r0 r1)]).
      apply app_eq_left with (acts := [Areg r2]).
      unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE2; subst. simpl in CONT. replace t2 with t1 by (eapply is_tree_determ; eauto). reflexivity.
  Qed.

  Lemma sequence_assoc_equiv_dir r0 r1 r2:
    forall dir, Sequence r0 (Sequence r1 r2) ≅[rer][dir] Sequence (Sequence r0 r1) r2.
  Proof.
    intros dir.
    pose proof (sequence_assoc_equiv r0 r1 r2 dir) as SEQASSOC. assumption.
  Qed.
  

  Create HintDb is_tree.
  Hint Constructors is_tree: is_tree.
  Lemma is_tree_skip_epsilon_r a i gm dir tr:
    is_tree rer a i gm dir tr ->
    is_tree rer (a ++ [Areg Epsilon]) i gm dir tr.
  Proof.
    induction 1; subst; simpl; eauto with is_tree.
    rewrite <- app_assoc in IHis_tree; eauto with is_tree.
  Qed.


  Lemma is_tree_skip_quant_zero_r a i gm dir tr greedy r:
    is_tree rer a i gm dir tr ->
    is_tree rer (a ++ [Areg (Quantified greedy 0 (NoI.N 0) r)]) i gm dir tr.
  Proof.
    induction 1; subst; simpl; eauto with is_tree.
    rewrite <- app_assoc in IHis_tree; eauto with is_tree.
  Qed.

  Lemma seq_equiv_dir: forall x x' y y' dir, x ≅[rer][dir] x' -> y ≅[rer][dir] y' -> Sequence x y ≅[rer][dir] Sequence x' y'.
  Proof.
    intros x x' y y' [] EQUIV_x EQUIV_y.
    - destruct EQUIV_x as [DEF_GROUPS_x EQUIV_x]. destruct EQUIV_y as [DEF_GROUPS_y EQUIV_y].

      split. 1: { simpl. apply groups_equiv_app; auto. }
      intros i gm tr1 tr2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst. simpl in *. clear TREE1 TREE2.
      revert i gm tr1 tr2 CONT CONT0.
      change (actions_equiv_dir rer forward [Areg x; Areg y] [Areg x'; Areg y']).
      change (actions_equiv_dir rer forward [Areg x] [Areg x']) in EQUIV_x.
      change (actions_equiv_dir rer forward [Areg y] [Areg y']) in EQUIV_y.
      apply app_eq_both with (a1 := [Areg x]) (a2 := [Areg x']) (b1 := [Areg y]) (b2 := [Areg y']) (dir := forward); auto.
    - destruct EQUIV_x as [DEF_GROUPS_x EQUIV_x]. destruct EQUIV_y as [DEF_GROUPS_y EQUIV_y].
      split. 1: { simpl. apply groups_equiv_app; auto. }
      intros i gm tr1 tr2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst. simpl in *. clear TREE1 TREE2.
      revert i gm tr1 tr2 CONT CONT0.
      change (actions_equiv_dir rer backward [Areg y; Areg x] [Areg y'; Areg x']).
      change (actions_equiv_dir rer backward [Areg x] [Areg x']) in EQUIV_x.
      change (actions_equiv_dir rer backward [Areg y] [Areg y']) in EQUIV_y.
      apply app_eq_both with (a1 := [Areg y]) (a2 := [Areg y']) (b1 := [Areg x]) (b2 := [Areg x']); auto.
  Qed.

  Corollary seq_equiv:
    forall x x' y y', x ≅[rer] x' -> y ≅[rer] y' -> Sequence x y ≅[rer] Sequence x' y'.
  Proof.
    intros x x' y y' EQUIV_x EQUIV_y []; auto using seq_equiv_dir.
  Qed.
End Utilities.

Section Examples.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Lemma sequence_epsilon_left_equiv r:
    Sequence Epsilon r ≅[rer] r.
  Proof.
    red; destruct dir; tree_equiv_inv.
    all: try apply (is_tree_skip_epsilon_r rer [Areg r]); eauto using compute_tr_is_tree.
    all: reflexivity.
  Qed.

  Lemma sequence_epsilon_right_equiv r:
    Sequence r Epsilon ≅[rer] r.
  Proof.
    red; destruct dir; tree_equiv_inv.
    all: try apply (is_tree_skip_epsilon_r rer [Areg r]); eauto using compute_tr_is_tree.
    all: reflexivity.
  Qed.

  Lemma quantified_zero_equiv r:
    def_groups r = [] ->
    forall greedy, Quantified greedy 0 (NoI.N 0) r ≅[rer] Epsilon.
  Proof.
    tree_equiv_rw; compute_tr_simpl.
    reflexivity.
  Qed.

  (* above, we need no groups, because epsilon doesn't define any.
     still, if a 0 quantifier is used in sequence with a regex that
     defines the same group, we can remove the 0 quantifier (without
     first rewriting to epsilon) *)
  Lemma quantified_zero_seq_left r s greedy:
    incl (def_groups r) (def_groups s) ->
    Sequence (Quantified greedy 0 (NoI.N 0) r) s ≅[rer] s.
  Proof.
    intros INCL dir. split.
    1: { simpl. split; [apply incl_app; [auto | apply incl_refl] | apply incl_appr, incl_refl]. }
    destruct dir; tree_equiv_simpl; tree_inv TREE1; [tree_inv TREE2 | ..].
    all: try apply (is_tree_skip_quant_zero_r rer [Areg s]); eauto using compute_tr_is_tree.
    all: reflexivity.
  Qed.

  Lemma quantified_zero_seq_right r s greedy:
    incl (def_groups r) (def_groups s) ->
    Sequence s (Quantified greedy 0 (NoI.N 0) r) ≅[rer] s.
  Proof.
    intros INCL dir. split.
    1: { simpl. split; [apply incl_app; [apply incl_refl | auto] | apply incl_appl, incl_refl]. }
    destruct dir; tree_equiv_simpl; tree_inv TREE1; [tree_inv TREE2 | ..].
    all: try apply (is_tree_skip_quant_zero_r rer [Areg s]); eauto using compute_tr_is_tree.
    all: reflexivity.
  Qed.

  Lemma quantified_S_equiv_forward n:
    forall delta r greedy,
      (Quantified greedy (S n) delta r)
        ≅[rer][forward] (Sequence (Quantified greedy 1 (NoI.N 0) r) (Quantified greedy n delta r)).
  Proof.
    intros. split. 1: { simpl. solve_groups_equiv. }
    intros i gm tr1 tr2 TREE1 TREE2.

    inversion TREE1; subst. inversion TREE2; subst. simpl in CONT. inversion CONT; subst.
    clear TREE1 TREE2 CONT.
    unfold tree_equiv_tr_dir. simpl.
    remember (GroupMap.reset (def_groups r) gm) as gm'.
    clear gm Heqgm'.
    revert i gm' titer titer0 ISTREE1 ISTREE0.
    change (actions_equiv_dir rer forward [Areg r; Areg (Quantified greedy n delta r)] [Areg r; Areg (Quantified greedy 0 (NoI.N 0) r); Areg (Quantified greedy n delta r)]).
    apply app_eq_left with (acts := [Areg r]).
    unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE2; subst.
    2: { destruct plus; discriminate. }
    replace t2 with t1 by eauto using is_tree_determ. reflexivity.
  Qed.

  Lemma quantified_S_equiv_backward n:
    forall delta r greedy,
      (Quantified greedy (S n) delta r)
        ≅[rer][backward] (Sequence (Quantified greedy n delta r) (Quantified greedy 1 (NoI.N 0) r)).
  Proof.
    intros. split. 1: { simpl. solve_groups_equiv. }
    intros i gm tr1 tr2 TREE1 TREE2.
    inversion TREE1; subst. inversion TREE2; subst. simpl in CONT. inversion CONT; subst.
    clear TREE1 TREE2 CONT.
    unfold tree_equiv_tr_dir. simpl.
    remember (GroupMap.reset (def_groups r) gm) as gm'.
    clear gm Heqgm'.
    revert i gm' titer titer0 ISTREE1 ISTREE0.
    change (actions_equiv_dir rer backward [Areg r; Areg (Quantified greedy n delta r)] [Areg r; Areg (Quantified greedy 0 (NoI.N 0) r); Areg (Quantified greedy n delta r)]).
    apply app_eq_left with (acts := [Areg r]).
    unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE2; subst.
    2: { destruct plus; discriminate. }
    replace t2 with t1 by eauto using is_tree_determ. reflexivity.
  Qed.


  Lemma quantified_one_equiv r:
    def_groups r = [] ->
    forall greedy, Quantified greedy 1 (NoI.N 0) r ≅[rer] r.
  Proof.
    tree_equiv_inv; try rewrite H; simpl; eauto.
    2: { apply (is_tree_skip_quant_zero_r rer [Areg r]). eauto. }
    apply leaves_equiv_refl.
  Qed.
  
  

  Lemma disj_equiv_dir: forall x x' y y' dir, x ≅[rer][dir] x' -> y ≅[rer][dir] y' -> Disjunction x y ≅[rer][dir] Disjunction x' y'.
  Proof.
    intros x x' y y' dir [GRPX EQSX] [GRPY EQSY]; split; simpl.
    apply groups_equiv_app; auto.
    intros i gm t1 t2 TREE1 TREE2.
    inversion TREE1; inversion TREE2; subst. clear TREE1 TREE2. simpl.
    unfold tree_equiv_tr_dir. simpl. apply leaves_equiv_app.
    specialize (EQSX _ _ _ _ ISTREE1 ISTREE0). auto.
    specialize (EQSY _ _ _ _ ISTREE2 ISTREE3). auto.
  Qed.



  Lemma disj_elim_copy: forall r1 r2 dir,
      Disjunction (Disjunction r1 r2) r1 ≅[rer][dir] Disjunction r1 r2.
  Proof.
    intros r1 r2 dir.
    split. simpl. solve_groups_equiv.
    intros i g t1 t2 T1 T2. inversion T1; inversion T2; inversion ISTREE1; subst.
    clear ISTREE1 T1 T2.
    unfold tree_equiv_tr_dir; simpl.
    eapply is_tree_determ with (t1 := t3) in ISTREE0, ISTREE4; eauto.
    eapply is_tree_determ with (t1 := t7) in ISTREE3; eauto. subst.
    simpl. rewrite <- app_assoc. symmetry.
    eapply leaves_equiv_append_head.
  Qed.

  (* INFINITY: Here are lemmas to simplify the work with *)

  (* If the remaining length is 0, and we have a regex followed by a check,
   then the leaves of the corresponding tree is empty*)
  Lemma null_length_fails:
    forall i g dir r t acts,
      remaining_length i dir <= 0 ->
      is_tree rer ([Areg r; Acheck i] ++ acts) i g dir t ->
      tree_leaves t g i dir = [].
  Proof.
    intros i g d r t acts l.
    assert (NL1: actions_no_leaves rer ([Areg r; Acheck i] ++ acts) d). {
      apply actions_no_leaves_add_left with (a:= [Areg r]).
      apply actions_no_leaves_add_right with (a := [Acheck i]) (b := acts).
      apply check_end_no_leaves. auto. lia.
    }
    unfold actions_no_leaves in NL1. eapply NL1; eauto. 
  Qed.

  
  Lemma quantifier_null_length_skip:
    forall i d g dir acts r t1 t2 greedy,
      remaining_length i dir <= 0 ->
      is_tree rer ([Areg (Quantified greedy 0 d r)] ++ acts) i g dir t1 ->
      is_tree rer acts i g dir t2 ->
      tree_leaves t1 g i dir = tree_leaves t2 g i dir.
  Proof.
    intros i d g dir acts r t1 t2  greedy l T1 T2. 
    inversion T1; subst. eapply is_tree_determ with (t1 := t1) (t2 := t2) in SKIP; eauto.
    subst; reflexivity.
    specialize (null_length_fails _ _ _ _ _ _ l ISTREE1) as nlf.
    pose proof (is_tree_determ _ _ _ _ _ _ _  T2 SKIP). subst.
    destruct greedy; simpl; rewrite nlf; try rewrite app_nil_r; auto.
  Qed.

  Lemma quantifier_null_length:
    forall i d g dir r t1 greedy,
      remaining_length i dir <= 0 ->
      is_tree rer ([Areg (Quantified greedy 0 d r)]) i g dir t1 ->
      tree_leaves t1 g i dir = [(i, g)].
  Proof.
    intros.
    pose proof (is_tree_productivity rer [] i g dir) as [t2 T2].
    pose proof (quantifier_null_length_skip _ _ _ _ _ _ _  _ _ H H0 T2).
    inversion T2; subst. rewrite H1; reflexivity.
  Qed.


    
  (* Inputs of leaves only make (non-strictly positive) progress in the direction of matching *)
  Lemma input_only_forward:
    forall l t gm gm1 gm2 inp1 inp2 dir,
      is_tree rer l inp1 gm dir t ->
      In (inp2, gm2) (tree_leaves t gm1 inp1 dir) ->
      inp1 = inp2 \/ StrictSuffix.strict_suffix inp2 inp1 dir.
  Proof.
    intros l t gm gm1 gm2 inp1 inp2 dir TREE IN.
    generalize dependent gm2. generalize dependent gm1.
    induction TREE; intros; simpl in IN; eauto; try contradiction.
    - inversion IN; try contradiction. inversion H. auto.
    - apply read_char_success_advance in READ.
      unfold advance_input' in IN. rewrite READ in IN.
      eapply StrictSuffix.ss_advance in READ.
      apply IHTREE in IN. destruct IN; subst; auto.
      right. eapply StrictSuffix.strict_suffix_trans; eauto.
    - apply in_app_or in IN as [IN1 | IN2]; eauto.
    - subst tquant. destruct greedy; simpl in IN;
        apply in_app_or in IN as [IN1 | IN2]; eauto.
    - destruct positivity eqn:POS;
        destruct tree_leaves as [|[i gm']]; eauto; inversion IN.
    - apply read_backref_success_advance in READ_BACKREF. rewrite <- READ_BACKREF in IN.
      apply IHTREE in IN.
      apply advance_input_n_suffix in READ_BACKREF as [p1 | p2]; subst; auto.
      right. destruct IN; subst; eauto.
      eapply StrictSuffix.strict_suffix_trans; eauto.
  Qed.

  (* An input cannot go backwards after passing througth a regex*)
  Lemma input_does_not_back:
    forall r t gm gm2 inp1 inp2 dir,
      is_tree rer [Areg r] inp1 gm dir t ->
      In (inp2, gm2) (tree_leaves t gm inp1 dir) ->
      ~ StrictSuffix.strict_suffix inp2 inp1 dir ->
      inp1 = inp2.
  Proof.
    intros.
    destruct (input_only_forward _ _ _ _ _ _ _ _ H H0).
    assumption. contradiction.
  Qed.


  Lemma quantifier_null_length_head_skip:
    forall i d g dir r t1 t2 t3 greedy acts,
      remaining_length i dir <= 0 ->
      is_tree rer ([Areg r; Areg (Quantified greedy 0 d r)] ++ acts) i g dir t1 ->
      is_tree rer [Areg r] i g dir t2 ->
      is_tree rer ([Areg r] ++ acts) i g dir t3 ->
      leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t3 g i dir).
  Proof.
    intros. 
    rewrite app_cons in H0. eapply leaves_concat with (act1 := [Areg r]) in H0, H2; eauto.
    assert (forall i0 g0, In (i0, g0) (tree_leaves t2 g i dir) -> i = i0 \/ StrictSuffix.strict_suffix i0 i dir). intros. eapply input_only_forward; eauto.
    remember (tree_leaves t2 g i dir) as l.
    remember (tree_leaves t3 g i dir) as l3.
    remember (tree_leaves t1 g i dir) as l1. clear Heql1 Heql Heql3.
    generalize dependent t1. generalize dependent t3.
    revert l3 H2 l1 H0.
    induction l; intros.
    - inversion H0; inversion H2; eauto. reflexivity.
    - inversion H2; inversion H0; inversion HEAD; inversion HEAD0; subst.
      clear HEAD HEAD0. destruct a; simpl in *.
      apply leaves_equiv_app. eapply quantifier_null_length_skip with (acts := acts)in TREE0; eauto.
      rewrite TREE0. reflexivity.
      assert (i = i0 \/ StrictSuffix.strict_suffix i0 i dir).
      eapply H3; intros; eauto. destruct H4; subst. lia.
      apply strict_suffix_remaining_length in H4; lia.
      eapply IHl; eauto.
  Qed.

  


  Lemma quantifier_null_length_head:
    forall i d g dir r t1 t2  greedy,
      remaining_length i dir <= 0 ->
      is_tree rer [Areg r; Areg (Quantified greedy 0 d r)] i g dir t1 ->
      is_tree rer [Areg r] i g dir t2 ->
      leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t2 g i dir).
  Proof.
    intros. eapply quantifier_null_length_head_skip with (acts := []); eauto.
    rewrite app_nil_r; eauto.
  Qed.

  Lemma quantifier_inf_step_advances:
    forall i r  n dir acts1 acts2 g t1 t2,
      remaining_length i dir = n ->
         is_tree rer ([Areg r; Acheck i] ++ acts1) i g dir t1 ->
         is_tree rer ([Areg r; Acheck i] ++ acts2) i g dir t2 ->
         (forall i,
             remaining_length i dir < n ->
             forall (gm : group_map) (t1 t2 : tree),
               is_tree rer acts1 i gm dir t1 ->
               is_tree rer acts2 i gm dir t2 -> leaves_equiv [] (tree_leaves t1 gm i dir) (tree_leaves t2 gm i dir)) ->
         leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t2 g i dir).
  Proof.
    intros i r n dir acts1 acts2 g t1 t2 HeqL T1 T2 IH.
    specialize (is_tree_productivity rer [Areg r] i g dir) as [t3 T3].
    rewrite app_cons in T1, T2. eapply leaves_concat with (act1 := [Areg r]) in T1, T2; eauto.
    remember (tree_leaves t3 g i dir) as l2.
    induction l2. inversion T2; inversion T1; subst. reflexivity.
    eapply flatmap_leaves_equiv_r; eauto. unfold equiv_leaffuncts. intros.
    inversion H; inversion H0; subst. 
    inversion TREE; inversion TREE0; subst; try contradiction. destruct a; simpl in *.
    2: reflexivity.
    eapply IH; eauto. eapply strict_suffix_remaining_length; eauto.
  Qed.
  
Lemma quantifier_inf_step_skip:
    forall i dir acts1 acts21 acts22 g t1 t2,
      is_tree rer (acts1 ++ acts21) i g dir t1 ->
      is_tree rer (acts1 ++ acts22) i g dir t2 ->
      (forall i,
        forall (gm : group_map) (t1 t2 : tree),
          is_tree rer acts21 i gm dir t1 ->
          is_tree rer acts22 i gm dir t2 -> leaves_equiv [] (tree_leaves t1 gm i dir) (tree_leaves t2 gm i dir)) ->
      leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t2 g i dir).
  Proof.
    intros i  dir acts1 acts21 acts22 g t1 t2  T1 T2 IH.
    specialize (is_tree_productivity rer acts1 i g dir) as [t3 T3].
    eapply leaves_concat with (act1 := acts1) in T1, T2; eauto.
    remember (tree_leaves t3 g i dir) as l2.
    induction l2. inversion T2; inversion T1; subst. reflexivity.
    eapply flatmap_leaves_equiv_r; eauto. unfold equiv_leaffuncts. intros.
    inversion H; inversion H0; subst. destruct lf; simpl in *.
    eapply IH; eauto. 
  Qed.
End Examples. 




