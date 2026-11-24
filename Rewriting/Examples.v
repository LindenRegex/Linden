From Linden Require Import ProofSetup.
Import FlatMap.

(** * A few examples of regex rewrites *)

Section Utilities.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

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

  Lemma disj_equiv_dir:
    forall x x' y y' dir,
      x ≅[rer][dir] x' -> y ≅[rer][dir] y' ->
      Disjunction x y ≅[rer][dir] Disjunction x' y'.
  Proof.
    intros x x' y y' dir EQX EQY; simpl.
    specialize (regex_equiv_ctx_samedir _ x x' dir EQX (CDisjunctionR CHole y) (eq_refl)) as XX'.
    specialize (regex_equiv_ctx_samedir _ y y' dir EQY (CDisjunctionL x' CHole) (eq_refl)) as YY'.
    simpl in XX', YY'. rewrite XX'. rewrite YY'. reflexivity.
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

  (** * PROPERTIES ON INPUT AND GROUPS NOT CHANGING *)
  (* The next section contains lemmas showing that the groups on leaves of r remain
     the same as the group passed on input for r if no groups are defined in r.
     They also shows that for all regexes, the inputs on it's leaves
     can only advance compared to the input it has started from.
   *)

  (* If all elements in a list do not define groups, and are either a regex
     or a check ,then all leave's groups will be the same as the regex's
     group input *)
  Lemma emptygroups_const_groups_ind:
    forall acts inp gm dir t,
      is_tree rer acts inp gm dir t ->
      Forall (fun a => (exists r, a = Areg r /\ def_groups r = []) \/ (exists i, a = Acheck i)) acts ->
      Forall (fun l: leaf => let (_ , gm1) := l in gm = gm1) (tree_leaves t gm inp dir).
  Proof.
    intros acts inp gm dir t T1 inA. 
    induction T1; simpl; auto; eapply Forall_cons_iff in inA as [[[r [closeR undefR]] | [i checkId]] e2]; try discriminate; auto.
    all: try inversion closeR; try inversion checkId; subst; simpl in undefR; try discriminate.
    - apply read_char_success_advance in READ.
      unfold advance_input'. rewrite READ. eapply IHT1; auto.
    - eapply app_eq_nil in undefR as [a1Empt a2Empt].
      eapply Forall_app; split.
      + eapply IHT1_1; eauto.
      + eapply IHT1_2; eauto.
    - eapply app_eq_nil in undefR as [a1Empt a2Empt].
      eapply IHT1. eapply Forall_app; split; auto.
      destruct dir; repeat (eapply Forall_cons_iff; split); try eapply FlatMap_nil.
      all: left; eexists; auto.
    - rewrite undefR in *. simpl in IHT1. eapply IHT1; eauto. 
      repeat (eapply Forall_cons_iff; split); auto.
      all: left; eexists; auto.
    - destruct greedy; simpl; eapply Forall_app; split.
      2, 3: eapply IHT1_2; eauto.
      + rewrite undefR in *; eapply IHT1_1; eauto.
        repeat (eapply Forall_cons_iff; split); auto.
        2: right; eexists; eauto.
        all: left; eexists; eauto.
      + rewrite undefR in *; eapply IHT1_1; eauto.
        repeat (eapply Forall_cons_iff; split); auto.
        2: right; eexists; eauto.
        all: left; eexists; eauto.
    - unfold lk_result in RES_LK. rewrite first_tree_leaf in RES_LK.
      remember (positivity lk) as l1.
      remember (tree_leaves treelk gm inp (lk_dir lk)) as l2.
      destruct l1, l2; try apply Forall_nil.
      + destruct l. simpl in *. inversion RES_LK; subst.
        assert (Forall (fun l : leaf => let (_, gm1) := l in gm = gm1) ((i, gmlk) :: l2)).
        eapply IHT1_1. eapply Forall_cons. left. exists r1; auto. apply Forall_nil.
        eapply Forall_cons_iff in H as [eq1 eq2]; subst.
        eapply IHT1_2; auto.
      + simpl in RES_LK. inversion RES_LK; subst. eapply IHT1_2; eauto.
    - apply read_backref_success_advance in READ_BACKREF.
      rewrite <- READ_BACKREF. eapply IHT1; auto.
  Qed.

  (* In the case where we define no groups, the groups created remain constant *)
  Lemma emptygroups_const_groups:
    forall  r inp inp2 gm gm2 dir t,
      def_groups r = [] ->
      is_tree rer [Areg r] inp gm dir t ->
      In (inp2, gm2) (tree_leaves t gm inp dir) ->
      gm = gm2.
  Proof.
    intros. eapply Forall_forall in H1.
    2: eapply emptygroups_const_groups_ind; eauto.
    simpl in H1; auto.
  Qed.

  (* Inputs of leaves only make (non-strictly positive) progress in the direction
     of matching *)
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

  (* An input cannot go backwards after passing througth a regex *)
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
End Examples.
