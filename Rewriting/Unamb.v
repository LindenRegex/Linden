From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import Examples FlatMap ForcedQuant Associativity Distributivity RegexpTree.


Section UnAmbiguity.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).
  
  (* Unambigous tree with at most a matching leaf *)
  Definition unamb_tree (t: tree) :=
    forall (gm: group_map) (i:input) (d: Direction),
      length (tree_leaves t gm i d) <= 1.

  Definition unamb (l: list action): Prop :=
    forall (i: input) (gm: group_map) (d: Direction) (t: tree),
      is_tree rer l i gm d t ->
      unamb_tree t.
  
  Fixpoint na (r: regex) : bool :=
    match r with
    | Epsilon | Character _ | Anchor _ | Backreference _ => true
    | Disjunction _ _ => false
    | Sequence r1 r2 => andb (na r1) (na r2)
    | Group _ r | Lookaround _ r => na r
    | Quantified _ _  (NoI.N 0) r1 => na r1
    | Quantified _ _ _ _ => false
    end.

  Fixpoint na_list (l: actions) : bool :=
    match l with
    | [] => true
    | (Areg r :: xs) => andb (na r) (na_list xs)
    | (Acheck _ :: xs) | Aclose _ :: xs => na_list xs
    end.

  (* This naive analysis is correct: it only accepts regexes whose trees are unambiguous *)
  Theorem naive_analysis_correctness:
    forall l d i gm t,
      na_list l = true ->
      is_tree rer l i gm d t ->
      unamb_tree t.
  Proof.
    intros l d i gm t NA TREE.
    unfold unamb_tree. intros i0 gm0 d0.
    generalize dependent i0. generalize dependent gm0. generalize dependent d0.
    induction TREE; intros; simpl; simpl in NA; try lia; auto.
    - apply andb_true_iff in NA as [NA NAC].
      apply andb_true_iff in NA as [NA1 NA2].
      apply IHTREE. destruct dir; simpl; rewrite NA1, NA2, NAC; auto.
    - destruct plus; try destruct n; inversion NA.
      apply IHTREE. simpl. apply andb_true_iff in NA as [NA1 NAC].
      rewrite NA1. rewrite NAC. auto.
    - apply andb_true_iff in NA as [NA1 NAC]. auto.
    - destruct plus; try destruct n; inversion NA.
    - apply andb_true_iff in NA as [NA1 NAC].
      destruct positivity eqn:POS; destruct tree_leaves as [|[i gm']]; simpl; try lia; auto.
  Qed.



  Corollary naive_unambiguity:
    forall r, na r = true -> unamb [Areg r].
  Proof.
    unfold unamb. intros r NA i gm d t TREE. eapply naive_analysis_correctness; eauto.
    simpl. rewrite NA. auto.
  Qed.

  Lemma FlatMap_one_leaf:
    forall X Y (x:X) f (y:list Y),
      FlatMap [x] f y ->
      f x y.
  Proof.
    intros X Y x f y H. inversion H; inversion FM; subst.
    rewrite app_nil_r. auto.
  Qed.

  Lemma unamb_list:
    forall r  i gm d t,
      unamb [Areg r] ->
      is_tree rer [Areg r] i gm d t ->
      tree_leaves t gm i d = [] \/ exists e, tree_leaves t gm i d = [e].
  Proof.
    intros r  i gm d t  UNAMBR RERTREE.
    pose proof UNAMBR i gm d t RERTREE gm i d.
    destruct (tree_leaves t gm i d). left. reflexivity.
    destruct l0. right. exists l. reflexivity.
    simpl in H. lia.
  Qed.

  (* Lemmas to move: these lemmas do not belong here and seem out of place.
   Need to ask where to store them *)


  (* In the case where we define no groups, the group created after the pass of a regex remains constant *)
  Lemma emptygroups_const_groups:
    forall  r inp inp2 gm gm2 dir t,
      def_groups r = [] ->
      is_tree rer [Areg r] inp gm dir t ->
      In (inp2, gm2) (tree_leaves t gm inp dir) ->
      gm = gm2.
  Proof.
  Admitted.
  
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

  (* If a regex is unambigous and does not define any groups, then we can get rid of a check if (inp, gm) has already been seen *)
  Lemma check_not_stops_quantifier n:
    forall r1 inp gm dir t1 t2 g,
      def_groups r1 = [] ->
      unamb [Areg r1] ->
      is_tree rer [Areg r1; Acheck inp; Areg (Quantified g 0 n r1)] inp gm dir t1 ->
      is_tree rer [Areg r1; Areg (Quantified g 0 n r1)] inp gm dir t2 ->
      leaves_equiv [] ((inp, gm) :: tree_leaves t1 gm inp dir) ((inp, gm) :: tree_leaves t2 gm inp dir).
  Proof.
    intros r1 inp gm dir t1 t2 g UNDEFGROUPS UNAMBR TREE1 TREE2. 
    specialize (is_tree_productivity rer [Areg r1] inp gm dir) as [t3 TREE3].
    rewrite app_cons in TREE1, TREE2. eapply leaves_concat with (act1 := [Areg r1]) in TREE1, TREE2; eauto.
    destruct (tree_leaves t3 gm inp dir) as [| [inp2 gm2] l] eqn: Ln.
    (* Case 1: list is empty*)
    - inversion TREE1; inversion TREE2; subst. reflexivity.
    - destruct l.
      (* Case 2: length of list > 2 (non unambigous)*)
      2: { specialize (UNAMBR inp gm dir t3 TREE3 gm inp dir). rewrite Ln in UNAMBR. simpl in UNAMBR. lia. }
      (* Case 3: length of list = a *)
      apply FlatMap_one_leaf in TREE2, TREE1.
      inversion TREE2; inversion TREE1; inversion TREE0.
      + (* Case 3.1: progress *)
        subst; simpl.
        rewrite  (is_tree_determ  _ _ _ _ _ _ _ TREE TREECONT). reflexivity.
      + (* Case 3.2: Mismatch *)
        clear TREE2 TREE1 H3. subst; simpl in *.
        assert (dd: In (inp2, gm2) (tree_leaves t3 gm inp dir)).
        rewrite Ln; simpl; left; auto.
        pose proof (emptygroups_const_groups _ _ _ _  _ _ _ UNDEFGROUPS TREE3 dd).
        pose proof (input_does_not_back _ _ _ _ _ _ _ TREE3 dd CHECKFAIL).
        inversion TREE; subst. inversion SKIP; subst; auto. simpl. leaves_equiv_t.
        rewrite UNDEFGROUPS; rewrite UNDEFGROUPS in ISTREE1, TREE; inversion SKIP; subst; simpl in *. clear SKIP TREE.
        rewrite app_cons in ISTREE1.
        eapply leaves_concat with (act1 := [Areg r1]) in ISTREE1; eauto.
        rewrite Ln in ISTREE1. apply FlatMap_one_leaf in ISTREE1. inversion ISTREE1; subst.
        inversion TREE; subst. simpl in PROGRESS. contradiction.
        destruct g; simpl; rewrite <- H3; leaves_equiv_t.
  Qed.

  
  (* after check this only works with an unamb case *)
  Lemma check_not_stops_quantifier_tail n:
    forall r1 inp gm dir t1 t2 g,
      def_groups r1 = [] ->
      unamb [Areg r1] ->
      is_tree rer [Areg r1; Acheck inp; Areg (Quantified g 0 n r1)] inp gm dir t1 ->
      is_tree rer [Areg r1; Areg (Quantified g 0 n r1)] inp gm dir t2 ->
      leaves_equiv [] (tree_leaves t1 gm inp dir ++ [(inp, gm)]) (tree_leaves t2 gm inp dir ++ [(inp, gm)]).
  Proof.
    intros r1 inp gm dir t1 t2 g UNDEFGROUPS UNAMBR TREE1 TREE2.
    specialize (is_tree_productivity rer [Areg r1] inp gm dir) as [t3 TREE3].
    rewrite app_cons in TREE1, TREE2.
    eapply leaves_concat with (act1 := [Areg r1]) in TREE1, TREE2; eauto.
    destruct (tree_leaves t3 gm inp dir) as [| [inp2 gm2] l] eqn: Ln.
    - (* Case 1: list is empty*)
      inversion TREE1; inversion TREE2; subst. reflexivity.
    - destruct l.
      (* Case 2: length of list > 2 (non unambigous)*)
      2: { specialize (UNAMBR inp gm dir t3 TREE3 gm inp dir). rewrite Ln in UNAMBR. simpl in UNAMBR. lia. }
      (* Case 3: length of list = a *)
     apply FlatMap_one_leaf in TREE2, TREE1.
      inversion TREE2; inversion TREE1; inversion TREE0.
      + (* Case 3.1: progress *)
        subst; simpl in *.
        clear TREE1 TREE2 TREE0. rewrite app_cons. etransitivity. clear H3 H7 t1.
        2: { rewrite app_cons. reflexivity. }
        apply leaves_equiv_app. 2: reflexivity. clear Ln PROGRESS.
        revert inp2 gm2 treecont t TREECONT TREE.
        change (actions_equiv_dir rer dir [Areg (Quantified g 0 n r1)] [Areg (Quantified g 0 n r1)]). reflexivity.
      + (* Case 3.2: Mismatch *)
        clear TREE2 TREE1 H3. subst; simpl in *.
        assert (dd: In (inp2, gm2) (tree_leaves t3 gm inp dir)).
        rewrite Ln; simpl; left; auto.
        pose proof (emptygroups_const_groups _ _ _ _  _ _ _ UNDEFGROUPS TREE3 dd).
        pose proof (input_does_not_back _ _ _ _ _ _ _ TREE3 dd CHECKFAIL).
        inversion TREE; subst. inversion SKIP; subst; auto. simpl. leaves_equiv_t.
        rewrite UNDEFGROUPS; rewrite UNDEFGROUPS in ISTREE1, TREE; inversion SKIP; subst; simpl in *.
        clear SKIP TREE.
        rewrite app_cons in ISTREE1.
        eapply leaves_concat with (act1 := [Areg r1]) in ISTREE1; eauto.
        rewrite Ln in ISTREE1. apply FlatMap_one_leaf in ISTREE1. inversion ISTREE1; subst.
        inversion TREE; subst. simpl in PROGRESS. contradiction.
        destruct g; simpl; rewrite <- H3; simpl; leaves_equiv_t.
  Qed.    


  (* Syntaxic lemmas: some syntaxic rules to simplify the overall structure of the proof *)
  
  (* you can distribute an unambiguous regex on the left *)
  Theorem unamb_distribute_left:
    forall r1 r2 r3,
      def_groups r1 = [] ->
      unamb [Areg r1] ->
      (Sequence r1 (Disjunction r2 r3)) ≅[rer] (Disjunction (Sequence r1 r2) (Sequence r1 r3)).
  Proof.
    unfold unamb. intros r1 r2 r3 NOGROUP UA.
    split. { simpl. rewrite NOGROUP. auto. }
    destruct dir.
    (* the backward case is true even without unambiguity *)
    2: { apply Distributivity.LeftBackward.factored_expanded_left_equiv. auto. }
    (* forward case *)
    unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE2; inversion TREE1; inversion ISTREE1; inversion ISTREE2; subst.
    clear TREE1 TREE2 ISTREE1 ISTREE2. simpl in *.
    rename t0 into t12. rename t3 into t13. rename t1 into t123.
    rename CONT into T123. rename CONT0 into T12. rename CONT1 into T13.
    specialize (is_tree_productivity rer [Areg r1] inp gm forward) as [t1 TREER1].
    rewrite app_cons in T123, T12, T13.
    (* the leaves of t123, t12 and t13 can be expressed as a FlatMap *)
    eapply leaves_concat with (act1:=[Areg r1]) in T123, T12, T13; eauto.
    unfold tree_equiv_tr_dir.  simpl.
    destruct (tree_leaves t1 gm inp forward) as [|[i1 gm1] l] eqn:LEAVES1.
    (* no leaf in r1: no leaf everywhere *)
    { inversion T123; inversion T12; inversion T13; subst. constructor. }
    destruct l as [|].
    (* there can't be more than one leaf *)
    2: { apply UA in TREER1. specialize (TREER1 gm inp forward).
         rewrite LEAVES1 in TREER1. simpl in TREER1. lia. }
    (* r1 has exactly one leaf: the FlatMaps are simply trees starting from that leaf *)
    apply FlatMap_one_leaf in T123, T12, T13.
    inversion T123; inversion TREE; inversion T12; inversion T13; subst.
    simpl.
    specialize (is_tree_determ _ _ _ _ _ _ _ ISTREE1 TREE0) as H.
    specialize (is_tree_determ _ _ _ _ _ _ _ ISTREE2 TREE1) as H1. subst.
    apply leaves_equiv_refl.
  Qed.


  (* you can distribute an unambiguous regex on the right *)
  Theorem unamb_distribute_right:
    forall r1 r2 r3,
      def_groups r3 = [] ->
      unamb [Areg r3] ->
      (Sequence (Disjunction r1 r2) r3) ≅[rer] (Disjunction (Sequence r1 r3) (Sequence r2 r3)).
  Proof. 
    intros r1 r2 r3 GRPEMPTY UNAMBR3.
    split. simpl. rewrite GRPEMPTY. repeat rewrite app_nil_r. reflexivity.
    destruct dir.
    apply Distributivity.Right.factored_expanded_right_equiv. assumption.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; inversion TREE2; inversion ISTREE1;inversion ISTREE2; subst.
    clear TREE1 TREE2 ISTREE1 ISTREE2. simpl in *.
    rename t0 into t2. rename CONT into TREE1. rename CONT0 into TREE2. rename CONT1 into TREE3.
    specialize (is_tree_productivity rer [Areg r3] inp gm backward) as [t4 TREE4].
    rewrite app_cons in TREE1, TREE2, TREE3.
    eapply leaves_concat with (act1:= [Areg r3]) in TREE1, TREE2, TREE3; eauto.
    unfold tree_equiv_tr_dir. simpl.
    destruct (tree_leaves t4 gm inp backward) as [|[inp2 gm2] l] eqn:LEAVES1.
    inversion TREE1; inversion TREE2; inversion TREE3; subst. constructor. 
    destruct l as [|].
    2: {
      specialize (UNAMBR3 inp gm backward t4 TREE4 gm inp backward) as FF.
      rewrite LEAVES1 in FF. simpl in FF. lia.
    }
    apply FlatMap_one_leaf in TREE1, TREE2, TREE3.
    inversion TREE3; inversion TREE2; inversion TREE1; inversion TREE5; subst. simpl.
    specialize (is_tree_determ _ _ _ _ _ _ _ ISTREE1 TREE0) as eq1.
    specialize (is_tree_determ _ _ _ _ _ _ _ ISTREE2 TREE) as eq2. subst.
    apply leaves_equiv_refl.
  Qed.
  
  Theorem non_greedy_quantifier_steps_opt:
    forall r n,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified false 0 (n + 1) r) ≅[rer] (Disjunction Epsilon (Quantified false 1 n r)).
  Proof.
    intros r n GROUPEMPT UNAMBR.
    split. simpl. rewrite GROUPEMPT. auto.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1. inversion TREE2. lia.
    inversion TREE2.  subst. simpl.
    rename titer into t11. rename tskip into t12. rename t0 into t22. rename t3 into t21.
    rename ISTREE1 into TREE11. rename ISTREE0 into TREE22. rename ISTREE2 into TREE21. rename SKIP into TREE12.
    unfold tree_equiv_tr_dir. simpl.
    inversion TREE12; inversion TREE22. inversion ISTREE. inversion TREE21. subst.
    rewrite GROUPEMPT in *. simpl in *.
    destruct plus;  simpl in H1;  try discriminate. 
    all: inversion H1; subst; eapply check_not_stops_quantifier; eauto.
    assert (n0 = n) by lia. subst. assumption.
  Qed.

  (* you can transform a quantifier into a easier one. *)
  Theorem greedy_quantifier_steps_opt:
    forall r n ,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified true 0 (S n)%NoI r) ≅[rer] (Disjunction (Quantified true 1 n r) Epsilon).
  Proof.
    intros r n GROUPEMPT UNAMBR.
    split. simpl. rewrite GROUPEMPT. auto.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; inversion TREE2; inversion ISTREE0; inversion ISTREE2; subst.
    clear TREE1 TREE2 ISTREE0 ISTREE2. 
    rename titer into t11. rename tskip into t12. rename t3 into t22. rename titer0 into t21.
    rename ISTREE1 into TREE11. rename ISTREE into TREE22. rename ISTREE3 into TREE21. rename SKIP into TREE12.
    unfold tree_equiv_tr_dir. simpl.
    inversion TREE12; inversion TREE22. subst.
    rewrite GROUPEMPT in *. simpl in *.
    destruct plus; destruct n; simpl in H1; try discriminate.
    inversion H1. subst. eapply check_not_stops_quantifier_tail; eauto.
    inversion H1. subst. eapply check_not_stops_quantifier_tail; eauto.
  Qed.

  Theorem unamb_quantifier_pops_left:
    forall r m n g,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified g (S m) n r)
        ≅[rer] Sequence (Quantified g 1 (NoI.N 0) r) (Quantified g m n r).
  Proof.
    intros r m n g GROUPEMPT UNAMBR dir.
    destruct dir. {apply quantified_S_equiv_forward. assumption. }
    (* Forward case has already been proven*)
    induction m as [| i IH].
    (* Starting with the induction of the min case*)
    2:{
      (* r{min + 2, delta}*)
      rewrite quantified_S_equiv_backward.
      (* r{min + 1, delta} r{1, 0}*)
      etransitivity. {apply seq_equiv_dir. apply IH. reflexivity. }
      (* (r{1, 0} r{min, delta}) r{1, 0}*)
      rewrite <- sequence_assoc_equiv_dir.
      (* r{1, 0} (r{min, delta} r{1, 0})*)
      etransitivity. {apply seq_equiv_dir. reflexivity. rewrite <- quantified_S_equiv_backward. reflexivity. assumption. }
      reflexivity. assumption.
    }
    (*Three cases: 0, (S n) and infinity*)
    destruct n. induction n.
    - (* Base case: n = 0*)
      symmetry.
      (*r{1, 0} r{0, 0}*)
      etransitivity. {
        apply seq_equiv. reflexivity. apply quantified_zero_equiv. assumption.
      }
      (*r{1, 0} Epsilon*)
      apply (sequence_epsilon_right_equiv rer ).
    - (* Inductive case: (S n)*)
      (* r{1, delta1 + 1}*)
      rewrite quantified_S_equiv_backward; auto.
      (* r{0, delta1 + 1}r{1, 0}*)
      destruct g; simpl.
    (* Greedy case *)
    + etransitivity. { eapply seq_equiv. apply greedy_quantifier_steps_opt. 3: apply quantified_one_equiv. all: auto. }
      (* (r{1, delta1} | ) r *)
      rewrite (unamb_distribute_right _ _ _ GROUPEMPT UNAMBR backward).
      (* (r{1, delta1} r | r *)
      etransitivity. {
        apply disj_equiv_dir. apply seq_equiv_dir. apply IHn. 
        rewrite <-  (quantified_one_equiv _ _ GROUPEMPT true backward). reflexivity.
        apply sequence_epsilon_left_equiv.
      }
      (* ((r{1, 0} r{0, delta1}) r{1, 0} | r *)
      etransitivity. {
        apply disj_equiv_dir. rewrite <- sequence_assoc_equiv_dir. apply seq_equiv_dir.
        apply quantified_one_equiv; auto. rewrite <- quantified_S_equiv_backward; auto.
        reflexivity. rewrite <- (sequence_epsilon_right_equiv _ _ backward). reflexivity.
      }
      (* (r r{1, delta1}) | r *)
      rewrite <- (unamb_distribute_left _ _ _ GROUPEMPT UNAMBR backward).
      (* r (r{1, delta1} | )  *)
      etransitivity. { eapply seq_equiv. rewrite <- quantified_one_equiv. 3: rewrite <- greedy_quantifier_steps_opt. all: auto. all: reflexivity. }
      (* r{1, 0} r{0, delta1 + 1}  *)
      reflexivity.
    + (* Nongreedy case *)
      etransitivity. { eapply seq_equiv. rewrite <- Nat.add_1_r.  apply non_greedy_quantifier_steps_opt. 3: apply quantified_one_equiv. all: auto. }
      (* (| r{1, delta1}) r *)
      rewrite (unamb_distribute_right _ _ _ GROUPEMPT UNAMBR backward).
      (* r | r{1, delta1} r *)
      etransitivity. {
        apply disj_equiv_dir. apply sequence_epsilon_left_equiv.
        apply seq_equiv_dir. apply IHn. 
        rewrite <-  (quantified_one_equiv _ _ GROUPEMPT false backward). reflexivity.        
      }
      (* r | (r{1, 0} r{0, delta1}) r{1, 0} *)
      etransitivity. {
        apply disj_equiv_dir. rewrite <- (sequence_epsilon_right_equiv _ _ backward). reflexivity.
        rewrite <- sequence_assoc_equiv_dir. apply seq_equiv_dir.
        apply quantified_one_equiv; auto. rewrite <- quantified_S_equiv_backward; auto.
        reflexivity. 
      }
      (* r | r r{1, delta1} *)
      rewrite <- (unamb_distribute_left _ _ _ GROUPEMPT UNAMBR backward).
      (* r (r{1, delta1} | )  *)
      etransitivity. { eapply seq_equiv. rewrite <- quantified_one_equiv. 3: rewrite <- non_greedy_quantifier_steps_opt. all: auto. all: reflexivity. }
      rewrite Nat.add_1_r.
      (* r{1, 0} r{0, delta1 + 1}  *)
      reflexivity.
    - split. simpl. rewrite GROUPEMPT. reflexivity.
      intros i gm t1 t2 T1 T2.
      unfold tree_equiv_tr_dir.
      remember (remaining_length i backward) as l.
      assert (Hlength_le: remaining_length i backward <= l) by lia. clear Heql.
      generalize dependent i. revert g t1 t2.
      induction l; intros g t1 t2 i TREE1 TREE2 Hlength_le. 
      inversion TREE1; inversion TREE2; subst. clear TREE1 TREE2. simpl in CONT.
      specialize (is_tree_productivity rer [Areg (Quantified g 1 (NoI.N 0) r)] i gm backward) as [t3 TREE3].
      eapply quantifier_null_length_skip with (acts := [Areg (Quantified g 1 (NoI.N 0) r)]) in CONT; eauto.
      inversion TREE3; subst. rewrite CONT.
  Admitted.
  
  Theorem unamb_quantifier_pops_right:
    forall r m n g,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified g (S m) n r)
        ≅[rer] Sequence (Quantified g m n r) (Quantified g 1 (NoI.N 0) r).
  Proof.
    intros r m n g GROUPEMPT UNAMBR dir.
    destruct dir. 2: {apply quantified_S_equiv_backward. assumption. } (* Backward case has already been proven*)
                induction m as [| i IH].
    (* Starting with the induction of the min case*)
    2:{
      (* r{min + 2, delta}*)
      rewrite quantified_S_equiv_forward.
      (* r{1, 0} r{min + 1, delta} *)
      etransitivity. {apply seq_equiv_dir. reflexivity. apply IH. }
      (* r{1, 0} (r{min, delta} r{1, 0})*)
      rewrite  sequence_assoc_equiv_dir.
      (* (r{1, 0} r{min, delta}) r{1, 0}*)
      etransitivity. {apply seq_equiv_dir. rewrite <- quantified_S_equiv_forward. 2: auto. all: reflexivity. }
      reflexivity. assumption.
    }
    (*Three cases: 0, (S n) and infinity*)
    destruct n. induction n.
    + (* Base case: n = 0*)
      symmetry.
      (*r{0, 0} r{1, 0}*)
      etransitivity. {
        apply seq_equiv.  apply quantified_zero_equiv. assumption. reflexivity.
      }
      (* Epsilon r{1, 0} *)
      apply (sequence_epsilon_left_equiv rer ).
    + (* Inductive case: (S n)*)
      (* r{1, delta1 + 1}*)
      rewrite quantified_S_equiv_forward; auto.
      (* r{1, 0} r{0, delta1 + 1}*)
      destruct g; simpl.
    - (* Greedy case *)

      etransitivity. { eapply seq_equiv. apply quantified_one_equiv. 2: apply greedy_quantifier_steps_opt. all: auto. }
      (* r (r{1, delta1} | )  *)
      rewrite (unamb_distribute_left _ _ _ GROUPEMPT UNAMBR forward).
      (* (r{1, delta1} r | r *)
      etransitivity. {
        apply disj_equiv_dir. apply seq_equiv_dir.
        rewrite <-  (quantified_one_equiv _ _ GROUPEMPT true forward). reflexivity.
        apply IHn. apply sequence_epsilon_right_equiv.
      }
      (* r{1, 0} (r{0, delta1} r{1, 0}) | r *)
      etransitivity. {
        apply disj_equiv_dir. rewrite sequence_assoc_equiv_dir. apply seq_equiv_dir.
        rewrite <- quantified_S_equiv_forward; auto. reflexivity.
        apply quantified_one_equiv; auto. 
        rewrite <- (sequence_epsilon_left_equiv _ _ forward). reflexivity.
      }
      (* ( r{1, delta1}) r | r *)
      rewrite <- (unamb_distribute_right _ _ _ GROUPEMPT UNAMBR forward).
      (* (r{1, delta1} | ) r *)
      etransitivity. { eapply seq_equiv. 2: rewrite <- quantified_one_equiv. rewrite <- greedy_quantifier_steps_opt. all: auto. all: reflexivity. }
      (* r{0, delta1 + 1} r{1, 0} *)
      reflexivity.
    -  (* Nongreedy case *)
      etransitivity. { eapply seq_equiv. 2:rewrite <- Nat.add_1_r; apply non_greedy_quantifier_steps_opt. apply quantified_one_equiv. all: auto. }
      (* r (| r{1, delta1}) *)
      rewrite (unamb_distribute_left _ _ _ GROUPEMPT UNAMBR forward).
      (* r | r r{1, delta1} *)
      etransitivity. {
        apply disj_equiv_dir. apply sequence_epsilon_right_equiv.
        apply seq_equiv_dir.
        rewrite <-  (quantified_one_equiv _ _ GROUPEMPT false forward). reflexivity.
        apply IHn. 
      }
      (* r | r{1, 0} (r{0, delta1} r{1, 0}) *)
      etransitivity. {
        apply disj_equiv_dir. rewrite <- (sequence_epsilon_left_equiv _ _ forward). reflexivity.
        rewrite  sequence_assoc_equiv_dir. apply seq_equiv_dir.
        rewrite <- quantified_S_equiv_forward; auto. reflexivity.
        apply quantified_one_equiv; auto. 
      }
      (* r | r{1, delta1} r *)
      rewrite <- (unamb_distribute_right _ _ _ GROUPEMPT UNAMBR forward).
      (* ( | r{1, delta1}) r  *)
      etransitivity. {
        eapply seq_equiv. rewrite <- non_greedy_quantifier_steps_opt. rewrite  Nat.add_1_r.
        reflexivity. auto. 
        2: rewrite <- quantified_one_equiv. all: auto.  all: reflexivity. }
      (* r{0, delta1 + 1} r{1, 0} *)
      reflexivity.
      + (* Infinity case*)
        etransitivity.
        2: {
          apply seq_equiv. reflexivity. rewrite quantified_one_equiv. reflexivity. assumption.
        }
        etransitivity. {
          rewrite  quantified_S_equiv_forward. apply seq_equiv_dir. apply quantified_one_equiv. 2: reflexivity. all: assumption.
        }
        split. simpl; rewrite GROUPEMPT. reflexivity.
        destruct g.
    - intros i g t1 t2 TREE1 TREE2.
      remember (remaining_length i forward) as l.
      assert (Hlength_le: remaining_length i forward <= l) by lia. clear Heql.
      generalize dependent i. revert g t1 t2.
      induction l; intros g t1 t2 i TREE1 TREE2 Hlength_le. 
      inversion TREE2; inversion CONT. subst. simpl in *.
      unfold tree_equiv_tr_dir.
      assert (NL2: actions_no_leaves rer [Areg r; Acheck i; Areg (Quantified true 0 plus r); Areg r] forward). {
        apply actions_no_leaves_add_left with (a:= [Areg r]).
        apply actions_no_leaves_add_right with (a := [Acheck i]) (b := [Areg (Quantified true 0 plus r); Areg r]).
        apply check_end_no_leaves. auto. lia.
      } 
      unfold actions_no_leaves in NL2. simpl.
      rewrite (NL2 _ _ titer); eauto. simpl.
      clear NL2 H8 ISTREE1 CONT. specialize (unamb_list) as dd.
      (* T1 *)
      Search leaves_equiv.
      inversion TREE1; subst.
      rewrite GROUPEMPT in *; simpl in *.
      rewrite app_cons in CONT.
      eapply leaves_concat with (act1 := [Areg r]) in CONT; eauto.
      specialize (unamb_list _ _ _ _ _ UNAMBR SKIP) as [nil | [el elList]].
      rewrite nil in *. inversion CONT. reflexivity.
      rewrite elList in *. apply FlatMap_one_leaf in CONT.
      inversion CONT; subst.
      assert (remaining_length (fst el) forward <= 0).
      assert (el = (fst el, snd el) \/ False). left. destruct el. reflexivity.
      specialize  (input_only_forward _ _ _ g (snd el) _ (fst el) _  SKIP) as iforward. rewrite elList in iforward. simpl in iforward.
      specialize (iforward H) as [c1 | c2].
      subst. assumption.
      specialize (strict_suffix_remaining_length _ _ _ c2) as p. lia.
      inversion TREE; subst.
      assert (NL2: actions_no_leaves rer [Areg r; Acheck (fst el); Areg (Quantified true 0 plus0 r)] forward). {
        apply actions_no_leaves_add_left with (a:= [Areg r]).
        apply actions_no_leaves_add_right with (a := [Acheck (fst el)]) (b := [Areg (Quantified true 0 plus0 r)]).
        apply check_end_no_leaves. auto. lia.
      }
      simpl. unfold actions_no_leaves in NL2.
      rewrite (NL2 _ _ titer0); eauto. simpl.
      inversion SKIP0; subst. simpl. destruct el. reflexivity.
      (* Inductive case *)
      unfold tree_equiv_tr_dir.
      inversion TREE1; inversion TREE2; subst. clear TREE1 TREE2.
      simpl in CONT, CONT0. inversion CONT0; subst. destruct plus. discriminate.
      rewrite GROUPEMPT in CONT0, ISTREE1. simpl in CONT0, ISTREE1.
      clear H1 CONT0. rewrite app_cons in CONT, ISTREE1.
      eapply leaves_concat with (act1 := [Areg r]) in CONT, ISTREE1; eauto.
      specialize (unamb_list _ _ _ _ _ UNAMBR SKIP) as [nil | [el elList]].
      rewrite nil in CONT, ISTREE1. inversion ISTREE1; inversion CONT; subst.
      rewrite GROUPEMPT; simpl. rewrite <- H; rewrite nil. reflexivity.
      rewrite elList in ISTREE1, CONT. apply FlatMap_one_leaf in ISTREE1, CONT.
      inversion ISTREE1; inversion CONT; subst. clear CONT ISTREE1. destruct el; rewrite GROUPEMPT; simpl in *.
      inversion TREE0; inversion SKIP0; subst. destruct plus. discriminate. clear TREE0 SKIP0 H1.
      simpl. rewrite elList. rewrite GROUPEMPT. simpl.
      inversion TREE; subst.
      apply strict_suffix_remaining_length in PROGRESS.
      assert (remaining_length i0 forward <= l) by lia.
      unfold tree_equiv_tr_dir in IHl. simpl in H3; rewrite <- H3.
      rewrite GROUPEMPT in ISTREE1; simpl in ISTREE1.
      specialize (is_tree_productivity rer [Areg r; Areg (Quantified true 0  +∞ r)] i0 g0 forward) as [t5 T5].
      specialize (check_not_stops_quantifier_tail _ _ _ _ _ _ _ _ GROUPEMPT UNAMBR ISTREE1 T5) as tEq2.
      eapply leaves_equiv_trans. apply tEq2. 
      apply leaves_equiv_app. eapply IHl; eauto; constructor; assumption.
      reflexivity.
      rewrite <- H3. simpl.
      assert (i = i0). {
        assert (In (i0, g0) (tree_leaves tskip g i forward)) as inSKIP.
        rewrite elList. constructor. reflexivity.
        specialize (input_only_forward _ _ _ g g0 _ i0 _ SKIP inSKIP ) as [c1 | c2].
        assumption. contradiction.
      }
      assert (g = g0). {
        assert (In (i0, g0) (tree_leaves tskip g i forward)) as inSKIP.
        rewrite elList. constructor. reflexivity.
        exact (emptygroups_const_groups _ _ _ _ _ _ _ GROUPEMPT SKIP inSKIP).
      }
      rewrite <- H in ISTREE1; rewrite <- H0 in ISTREE1. 
      rewrite app_cons in ISTREE1. rewrite GROUPEMPT in ISTREE1. simpl in ISTREE1.
      eapply leaves_concat with (act1 := [Areg r]) in  ISTREE1; eauto.
      specialize (unamb_list _ _ _ _ _ UNAMBR SKIP) as [nil | [l2 l2List]].
      rewrite nil in  ISTREE1. inversion ISTREE1; subst. rewrite <- H1. reflexivity.
      rewrite l2List in ISTREE1. apply FlatMap_one_leaf in ISTREE1.
      inversion ISTREE1; inversion TREE0. destruct l2; simpl in *.
      rewrite elList in l2List. inversion l2List; subst.
      contradiction.
      subst. rewrite <- H6. leaves_equiv_t.
    - intros i g t1 t2 TREE1 TREE2.
      remember (remaining_length i forward) as l.
      assert (Hlength_le: remaining_length i forward <= l) by lia. clear Heql.
      generalize dependent i. revert g t1 t2.
      induction l; intros g t1 t2 i TREE1 TREE2 Hlength_le.
      
      inversion TREE2; inversion CONT. subst. simpl in *.
      unfold tree_equiv_tr_dir.
      assert (NL2: actions_no_leaves rer [Areg r; Acheck i; Areg (Quantified false 0 plus r); Areg r] forward). {
        apply actions_no_leaves_add_left with (a:= [Areg r]).
        apply actions_no_leaves_add_right with (a := [Acheck i]) (b := [Areg (Quantified false 0 plus r); Areg r]).
        apply check_end_no_leaves. auto. lia.
      } 
      unfold actions_no_leaves in NL2. simpl.
      rewrite (NL2 _ _ titer); eauto. simpl.
      clear NL2 H8 ISTREE1 CONT. 
      (* T1 *)
      inversion TREE1; subst.
      rewrite GROUPEMPT in *; simpl in *.
      rewrite app_cons in CONT.
      eapply leaves_concat with (act1 := [Areg r]) in CONT; eauto.
      specialize (unamb_list _ _ _ _ _ UNAMBR SKIP) as [nil | [el elList]].
      rewrite nil in *. inversion CONT. reflexivity.
      rewrite elList in *. apply FlatMap_one_leaf in CONT.
      inversion CONT; subst.
      assert (remaining_length (fst el) forward <= 0).
      assert (el = (fst el, snd el) \/ False). left. destruct el. reflexivity.
      specialize  (input_only_forward _ _ _ g  (snd el) _  (fst el)  _ SKIP) as iforward. rewrite elList in iforward. simpl in iforward.
      specialize (iforward H) as [c1 | c2].
      subst. assumption.
      specialize (strict_suffix_remaining_length _ _ _ c2) as p. lia.
      inversion TREE; subst.
      assert (NL2: actions_no_leaves rer [Areg r; Acheck (fst el); Areg (Quantified false 0 plus0 r)] forward). {
        apply actions_no_leaves_add_left with (a:= [Areg r]).
        apply actions_no_leaves_add_right with (a := [Acheck (fst el)]) (b := [Areg (Quantified false 0 plus0 r)]).
        apply check_end_no_leaves. auto. lia.
      }
      simpl. unfold actions_no_leaves in NL2.
      rewrite (NL2 _ _ titer0); eauto. simpl.
      inversion SKIP0; subst. simpl. destruct el. reflexivity.
      (* Inductive case *)
      unfold tree_equiv_tr_dir.
      inversion TREE1; inversion TREE2; subst. clear TREE1 TREE2.
      simpl in CONT, CONT0. inversion CONT0; subst. destruct plus. discriminate.
      rewrite GROUPEMPT in CONT0, ISTREE1. simpl in CONT0, ISTREE1.
      clear H1 CONT0. rewrite app_cons in CONT, ISTREE1.
      eapply leaves_concat with (act1 := [Areg r]) in CONT, ISTREE1; eauto.
      specialize (unamb_list _ _ _ _ _ UNAMBR SKIP) as [nil | [el elList]].
      rewrite nil in CONT, ISTREE1. inversion ISTREE1; inversion CONT; subst.
      rewrite GROUPEMPT; simpl. rewrite <- H; rewrite nil. reflexivity.
      rewrite elList in ISTREE1, CONT. apply FlatMap_one_leaf in ISTREE1, CONT.
      inversion ISTREE1; inversion CONT; subst. clear CONT ISTREE1. destruct el; rewrite GROUPEMPT; simpl in *.
      inversion TREE0; inversion SKIP0; subst. destruct plus. discriminate. clear TREE0 SKIP0 H1.
      simpl. rewrite elList. rewrite GROUPEMPT. simpl.
      inversion TREE; subst.
      apply strict_suffix_remaining_length in PROGRESS.
      assert (remaining_length i0 forward <= l) by lia.
      unfold tree_equiv_tr_dir in IHl. simpl in H3; rewrite <- H3.
      rewrite GROUPEMPT in ISTREE1; simpl in ISTREE1.
      specialize (is_tree_productivity rer [Areg r; Areg (Quantified false 0  +∞ r)] i0 g0 forward) as [t5 T5].
      specialize (check_not_stops_quantifier _ _ _ _ _ _ _ _ GROUPEMPT UNAMBR ISTREE1 T5) as tEq2.
      eapply leaves_equiv_trans. apply tEq2. rewrite app_cons.
      etransitivity. 2: rewrite app_cons; reflexivity.
      apply leaves_equiv_app. reflexivity.
      eapply IHl; eauto; constructor; assumption.
      rewrite <- H3. simpl.
      assert (i = i0). {
        assert (In (i0, g0) (tree_leaves tskip g i forward)) as inSKIP.
        rewrite elList. constructor. reflexivity.
        specialize (input_only_forward _ _ _ g g0 _ i0 _ SKIP inSKIP ) as [c1 | c2].
        assumption. contradiction.
      }
      assert (g = g0). {
        assert (In (i0, g0) (tree_leaves tskip g i forward)) as inSKIP.
        rewrite elList. constructor. reflexivity.
        exact (emptygroups_const_groups _ _ _ _ _ _ _ GROUPEMPT SKIP inSKIP).
      }
      rewrite <- H in ISTREE1; rewrite <- H0 in ISTREE1. 
      rewrite app_cons in ISTREE1. rewrite GROUPEMPT in ISTREE1. simpl in ISTREE1.
      eapply leaves_concat with (act1 := [Areg r]) in  ISTREE1; eauto.
      specialize (unamb_list _ _ _ _ _ UNAMBR SKIP) as [nil | [l2 l2List]].
      rewrite nil in  ISTREE1. inversion ISTREE1; subst. rewrite <- H1. reflexivity.
      rewrite l2List in ISTREE1. apply FlatMap_one_leaf in ISTREE1.
      inversion ISTREE1; inversion TREE0. destruct l2; simpl in *.
      rewrite elList in l2List. inversion l2List; subst.
      contradiction.
      subst. rewrite <- H6. leaves_equiv_t.
  Qed.

  
  (* t1 = t3 /\ t2 <= t3 -> t1 = t2 ++ t3
   peut etre changé en: t2 <= t3 -> t3 = t2 ++ t3*)
  Theorem leaves_incl2:
    forall l1 l2 l3  acts ,
      leaves_equiv [] l1 l3 ->
      l2 ++ acts = l1 ->
      leaves_equiv [] l1 (l2 ++ l3).
  Proof.
    intros t1 t2 t3  acts  lEq1 lEq2.
    rewrite <- lEq2 in lEq1. rewrite <- lEq2. clear t1 lEq2.
    assert (leaves_equiv [] t2 t2) by reflexivity.
    eapply leaves_equiv_app  with (p1 := t2) in lEq1. 2: reflexivity.
    eapply leaves_equiv_trans; eauto.
    rewrite app_assoc. apply leaves_equiv_app with (l1 := acts) (l2 := acts).
    2: reflexivity.
    eapply leaves_equiv_repet.
  Qed.

  Lemma unamb_quantifier_invertible:
    forall r m n g,
      def_groups r = [] ->
      unamb [Areg r] ->
      Sequence (Quantified g 1 (NoI.N 0) r) (Quantified g m n r) ≅[rer] Sequence (Quantified g m n r) (Quantified g 1 (NoI.N 0) r).
  Proof.
    intros r m n g GROUPEMPT UNAMBR.
    rewrite <- unamb_quantifier_pops_left.
    rewrite unamb_quantifier_pops_right.
    reflexivity.
    all: assumption.
  Qed.

  Theorem greedy_quantifier_steps_opt_min:
    forall r n min,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified true min (S n)%NoI r) ≅[rer] (Disjunction (Quantified true (min + 1) n r) (Quantified true min 0 r)).
  Proof.
    intros r n min UNDEFGROUPS UNAMBR dir.
    induction min; simpl. symmetry.
    etransitivity. {
      eapply disj_equiv_dir. reflexivity. apply quantified_zero_equiv; eauto.
    }
    symmetry. eapply greedy_quantifier_steps_opt; auto.
    etransitivity. eapply unamb_quantifier_pops_left; eauto.
    etransitivity. eapply seq_equiv_dir. apply quantified_one_equiv; eauto. eapply IHmin.
    etransitivity. eapply unamb_distribute_left; eauto.
    apply disj_equiv_dir. etransitivity.
    apply seq_equiv. rewrite  <- quantified_one_equiv with (greedy := true); eauto.
    1, 2: reflexivity. symmetry.
    eapply unamb_quantifier_pops_left; auto.
    symmetry. etransitivity. eapply unamb_quantifier_pops_left; auto.
    apply seq_equiv. 2: reflexivity. apply quantified_one_equiv; auto.
  Qed.


  Theorem non_greedy_quantifier_steps_opt_min:
    forall r n min,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified false min (S n)%NoI r) ≅[rer] (Disjunction (Quantified false min 0 r) (Quantified false (min + 1) n r)).
  Proof.
    intros r n min UNDEFGROUPS UNAMBR dir.
    induction min; simpl. symmetry.
    + etransitivity. {
        eapply disj_equiv_dir.  apply quantified_zero_equiv; eauto. reflexivity.
      }
      symmetry. etransitivity. rewrite <- Nat.add_1_r. eapply non_greedy_quantifier_steps_opt; auto. reflexivity.
    + etransitivity. eapply unamb_quantifier_pops_left; eauto.
      etransitivity. eapply seq_equiv_dir. apply quantified_one_equiv; eauto. eapply IHmin.
      etransitivity. eapply unamb_distribute_left; eauto.
      apply disj_equiv_dir. etransitivity.
      apply seq_equiv. rewrite  <- quantified_one_equiv with (greedy := false); eauto.
      1, 2: reflexivity. symmetry.
      etransitivity. eapply unamb_quantifier_pops_left; auto. reflexivity.
      symmetry. etransitivity. eapply unamb_quantifier_pops_left; auto.
      apply seq_equiv. 2: reflexivity. apply quantified_one_equiv; auto.
  Qed.


  Theorem atmost_level_tail (m: nat) (d: non_neg_integer_or_inf) r:
    forall inp gm dir t1 t2,
      is_tree rer [Areg (Quantified false 0 m r)] inp gm dir t1 ->
      is_tree rer [Areg (Quantified false 0 (m+d)%NoI r)] inp gm dir t2 ->
      unamb [Areg r] ->
      exists acts,  ((tree_leaves t1 gm inp dir) ++ acts) = (tree_leaves t2 gm inp dir).
  Proof.
    revert d r.
    induction m; intros.
    + inversion H; inversion SKIP; subst.
      inversion H0; inversion SKIP0; subst.
      simpl. exists []. reflexivity.
      inversion SKIP0; subst. simpl.
      exists (tree_leaves titer (GroupMap.reset (def_groups r) gm) inp dir).
      reflexivity. destruct plus; discriminate.
    + inversion H; inversion SKIP; subst. simpl. clear H SKIP.
      inversion H0; inversion SKIP; subst. simpl. clear H0 SKIP.
      destruct d; discriminate. simpl.
      rewrite app_cons in ISTREE1, ISTREE0.
      specialize (is_tree_productivity rer [Areg r] inp (GroupMap.reset (def_groups r) gm) dir) as [t3 T3].
      eapply leaves_concat with (act1 := [Areg r]) in ISTREE1, ISTREE0; eauto.
      pose proof (unamb_list _ _ _ _ _ H1 T3) as [c1 | [el c2]].
      rewrite c1 in *. inversion ISTREE0; inversion ISTREE1; subst.
      exists []. reflexivity.
      rewrite c2 in *. apply FlatMap_one_leaf in ISTREE0, ISTREE1.
      inversion ISTREE0; inversion ISTREE1; subst. simpl in *.
      inversion TREE; inversion TREE0; subst.
      2, 3: contradiction.
      2: { simpl. exists []. reflexivity. }
      destruct el; simpl in *. destruct plus. 2: discriminate.
      inversion H4. subst.
      destruct plus0, d; try discriminate.
      inversion H3; subst.
      specialize (IHm (NoI.N (n0)) _ _ _ _ _ treecont TREECONT0).
      simpl in IHm. specialize (IHm TREECONT H1) as [acts lEq].
      exists acts. etransitivity. 1,2: rewrite app_cons. reflexivity. f_equal.
      apply lEq.
      specialize (IHm +∞ _ _ _ _ _ treecont TREECONT0). simpl in IHm.
      specialize (IHm TREECONT H1) as [acts lEq].
      exists acts. etransitivity. 1,2: rewrite app_cons. reflexivity.
      f_equal. apply lEq.
  Qed.

  Theorem unamb_list_nat_eqs:
    forall r i g dir t1 t2 (delta1: nat) delta2,
      def_groups r = [] ->
      unamb [Areg r] ->
      is_tree rer
        [Areg (Quantified false 0 delta1 r); Areg (Quantified false 0 delta2 r)]
        i g dir t1 ->
      is_tree rer [Areg (Quantified false 0 (delta1 + delta2)%NoI r)] i g dir t2 ->
      leaves_equiv [] (tree_leaves t1 g i dir)
        (tree_leaves t2 g i dir).
  Proof.
    intros r i g d t1 t2 delta1 . revert i g t1 t2. 
    induction delta1; intros i g t1 t2 delta2 GROUPEMPT UNAMBR T1 T2.
    + inversion T1; subst. 2: destruct plus; discriminate. destruct delta2; simpl in T1, T2.
      all: specialize (is_tree_determ _ _ _ _ _ _ _ T2 SKIP) as cd; rewrite cd; reflexivity.
    + inversion T1; inversion T2; subst. destruct delta2; discriminate.
      (* destruct plus, plus0; try discriminate. inversion H9; subst. *) 
      rewrite app_cons in ISTREE1, ISTREE0. rewrite GROUPEMPT in *.
      specialize (is_tree_productivity rer [Areg r] i g d) as [t3 T3].
      eapply leaves_concat with (act1 := [Areg r]) in ISTREE1, ISTREE0; eauto. simpl.
      specialize (unamb_list _ _ _ _ _ UNAMBR T3) as [e1 | [el e2]].
      simpl in *. rewrite e1 in ISTREE0, ISTREE1. inversion ISTREE0; inversion ISTREE1; subst.
      inversion SKIP0; inversion SKIP; subst. inversion SKIP1; reflexivity.
      rewrite GROUPEMPT. inversion SKIP1; subst. simpl.
      rewrite app_cons in ISTREE2. rewrite GROUPEMPT in *.
      eapply leaves_concat with (act1 := [Areg r]) in ISTREE2; eauto. simpl in ISTREE2.
      rewrite e1 in ISTREE2. inversion ISTREE2; subst. reflexivity.
      simpl in *. rewrite e2 in ISTREE0, ISTREE1. apply FlatMap_one_leaf in ISTREE0, ISTREE1.
      inversion ISTREE1; inversion ISTREE0; try discriminate; subst. destruct el; simpl in *.
      (* case 1*)
      inversion SKIP; inversion SKIP1; inversion SKIP0; subst. simpl.
      etransitivity. 1, 2: rewrite app_cons. reflexivity.
      apply leaves_equiv_app. reflexivity. inversion H1; inversion H0; subst.
      inversion TREE0; inversion TREE; try contradiction; subst. simpl.
      destruct plus, plus0; try discriminate. inversion H0; inversion H9. subst.
      eapply IHdelta1; eauto. simpl. reflexivity.
      (* case 2*)
      rewrite GROUPEMPT in *. simpl in *.
      rewrite app_cons in ISTREE2. 
      eapply leaves_concat with (act1 := [Areg r]) in ISTREE2; eauto. simpl in ISTREE2.
      rewrite e2 in ISTREE2. apply FlatMap_one_leaf in ISTREE2.
      inversion ISTREE2; subst. inversion TREE0; inversion TREE1; inversion TREE; try contradiction; subst.
      2: simpl; reflexivity.
      simpl. etransitivity. 1, 2: rewrite app_cons. reflexivity.
      apply leaves_equiv_app. reflexivity.
      destruct plus0, plus1; try discriminate.
      inversion H9; destruct plus. 2: discriminate. inversion H1; subst.
      pose proof (atmost_level_tail _  (S delta1) _ _ _ _ _ treecont TREECONT0).
      simpl in H. assert (n0 + S delta1 = delta1 + S n0) by lia. rewrite H0 in H.
      specialize (H TREECONT UNAMBR) as [acts eq]. 
      symmetry. eapply leaves_incl2; eauto. symmetry.
      eapply IHdelta1; eauto.
      inversion H9; destruct plus. 2: discriminate. inversion H1; subst.
      symmetry. eapply leaves_incl2; eauto.
      symmetry. eapply IHdelta1; eauto.
      pose proof (is_tree_determ _ _ _ _ _ _ _ TREECONT0 TREECONT); subst.
      apply app_nil_r.
  Qed.

  Theorem unamb_list_inf_eqs:
    forall r i g dir t1 t2 delta1,
      def_groups r = [] ->
      unamb [Areg r] ->
      is_tree rer [Areg (Quantified false 0 +∞ r)] i g dir t1 ->
      is_tree rer
        [Areg (Quantified false 0 +∞ r); Areg (Quantified false 0 delta1 r)]
        i g dir t2 ->
      leaves_equiv [] (tree_leaves t1 g i dir)
        (tree_leaves t2 g i dir).
  Proof.
    intros r i g dir t1 t2 delta2 UNDEFGROUPS UNAMBR T1 T2.
    remember (remaining_length i dir) as l.
    assert (Hlength_le: remaining_length i dir <= l) by lia. clear Heql.
    revert i g t1 t2 T1 T2 Hlength_le.
    induction l; intros i g t1 t2 T1 T2 Hlength_le; simpl.
    + inversion T1; inversion T2; subst. destruct plus, plus0; try discriminate. clear T1 T2.
      inversion SKIP; subst.
      inversion SKIP0; inversion SKIP1; subst.
      simpl. etransitivity. 1,2: rewrite app_cons. reflexivity.
      apply leaves_equiv_app. 1:reflexivity. simpl.
      assert (tree_leaves titer (GroupMap.reset (def_groups r) g) i dir = []).
      eapply null_length_fails; eauto. exact ISTREE1. 
      assert (tree_leaves titer0 (GroupMap.reset (def_groups r) g) i dir = []).
      eapply null_length_fails; eauto. exact ISTREE0.
      rewrite H0. rewrite H. reflexivity.
      simpl. etransitivity. 1,2: rewrite app_cons. reflexivity.
      apply leaves_equiv_app. 1:reflexivity. simpl.
      assert (tree_leaves titer (GroupMap.reset (def_groups r) g) i dir = []).
      eapply null_length_fails; eauto. exact ISTREE1. 
      assert (tree_leaves titer0 (GroupMap.reset (def_groups r) g) i dir = []).
      eapply null_length_fails; eauto. exact ISTREE0.
      assert (tree_leaves titer1 (GroupMap.reset (def_groups r) g) i dir = []).
      eapply null_length_fails; eauto. exact ISTREE2.
      rewrite H0. rewrite H.  rewrite H2. reflexivity.
    + apply GroupId.le_lteq in Hlength_le as [p1 | p2].
      rewrite  Nat.lt_succ_r in p1.  eapply IHl; eauto.
      inversion T1; inversion T2; subst. simpl. destruct plus, plus0; try discriminate.
      simpl in *. specialize (is_tree_productivity rer [Areg r] i g dir ) as [t3 T3].
      inversion SKIP0; subst.
    - rewrite UNDEFGROUPS in ISTREE0, ISTREE1. simpl in ISTREE0, ISTREE1.
      eapply leaves_concat with (act1 := [Areg r]) in ISTREE0, ISTREE1; eauto. inversion SKIP1; inversion SKIP; subst. simpl.
      specialize (unamb_list _ _ _ _ _ UNAMBR T3) as [lEmpt | [el ld]].
      rewrite lEmpt in ISTREE1, ISTREE0. inversion ISTREE1; inversion ISTREE0.
      rewrite UNDEFGROUPS; simpl. rewrite <- H. rewrite <- H2.
      reflexivity.
      rewrite ld in ISTREE1, ISTREE0. apply FlatMap_one_leaf in ISTREE1, ISTREE0.
      inversion ISTREE1; inversion ISTREE0; subst.
      rewrite UNDEFGROUPS; simpl. destruct el; simpl in *.
      rewrite <- H8. rewrite <- H4. inversion TREE0; inversion TREE; try contradiction; subst.
      simpl. etransitivity. 1, 2: rewrite app_cons. reflexivity.
      apply leaves_equiv_app. reflexivity.
      eapply IHl; eauto. Search remaining_length.
      pose proof (strict_suffix_remaining_length _ _ _ PROGRESS). lia.
      reflexivity.
    -  rewrite UNDEFGROUPS in ISTREE0, ISTREE1, ISTREE2. simpl in ISTREE0, ISTREE1, ISTREE2.
       eapply leaves_concat with (act1 := [Areg r]) in ISTREE0, ISTREE1, ISTREE2; eauto. inversion SKIP1; inversion SKIP; subst. simpl.
       specialize (unamb_list _ _ _ _ _ UNAMBR T3) as [lEmpt | [el ld]].
       rewrite lEmpt in ISTREE1, ISTREE0, ISTREE2. inversion ISTREE1; inversion ISTREE0; inversion ISTREE2.
       rewrite UNDEFGROUPS; simpl. rewrite <- H. rewrite <- H2. rewrite <- H4.
       reflexivity.
       rewrite ld in ISTREE1, ISTREE0, ISTREE2. apply FlatMap_one_leaf in ISTREE1, ISTREE0, ISTREE2.
       inversion ISTREE1; inversion ISTREE0; inversion ISTREE2; subst.
       rewrite UNDEFGROUPS; simpl. destruct el; simpl in *.
       rewrite <- H8. rewrite <- H4. rewrite <- H13.
       inversion TREE0; inversion TREE; inversion TREE1; try contradiction; subst.
       2: simpl; reflexivity.
       simpl. etransitivity. 1, 2: rewrite app_cons. reflexivity.
       apply leaves_equiv_app. reflexivity.
       destruct plus. 
       pose proof (atmost_level_tail _  +∞ _ _ _ _ _ treecont0 TREECONT1).
       simpl in H. specialize (H TREECONT0 UNAMBR) as [acts eq]. 
       eapply leaves_incl2; eauto. eapply IHl; eauto.
       pose proof (strict_suffix_remaining_length _ _ _ PROGRESS); try lia.
       pose proof (is_tree_determ _ _ _ _ _ _ _ TREECONT0 TREECONT1); subst.
       eapply leaves_incl2; eauto. eapply IHl; eauto.
       pose proof (strict_suffix_remaining_length _ _ _ PROGRESS); try lia.
       apply app_nil_r.
  Qed.
  
  Theorem unamb_equivalence_base_case_inf_forward:
    forall r delta2 ,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Sequence (Quantified false 0 +∞ r)
         (* r{0, Delta2, g } *)
         (Quantified false 0 delta2 r))
        ≅[rer][forward] (Quantified false 0 +∞ r).
  Proof.
    intros r delta1 UNDEFGROUPS.
    split. simpl. rewrite UNDEFGROUPS. reflexivity.
    intros i g t1 t2 T1 T2.
    unfold tree_equiv_tr_dir.
    inversion T1; subst. simpl in *. clear T1.
    symmetry.
    eapply unamb_list_inf_eqs; eauto.
  Qed.
  
  Theorem unamb_equivalence_base_case_inf_backward:
    forall r delta1,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Sequence (Quantified false 0 delta1 r)
         (* r{0, Delta2, g } *)
         (Quantified false 0  +∞ r))
        ≅[rer][backward] (Quantified false 0 +∞ r).
  Proof. 
    intros r delta1 UNDEFGROUPS.
    split. simpl. rewrite UNDEFGROUPS. reflexivity.
    intros i g t1 t2 T1 T2.
    unfold tree_equiv_tr_dir.
    inversion T1; subst. simpl in *. clear T1.
    symmetry.
    eapply unamb_list_inf_eqs; eauto.
  Qed.

  (* Base case: r{0, delta1}r{0, delta2} = r{0, delta1 + delta2}*)
  Theorem unamb_equivalence_base_case:
    forall r delta1 delta2 g,
      def_groups r = [] -> 
      (* if the tree corresponding to the regex is unambigous *)
      unamb [Areg r] ->
      (* r{0, Delta1, g } *)
      (Sequence (Quantified g 0 delta1 r)
         (* r{0, Delta2, g } *)
         (Quantified g 0 delta2 r))
        ≅[rer] (Quantified g 0 (delta1 + delta2)%NoI r).
  Proof.
    intros reg delta1 delta2 g UNDEFGROUPS UNAMBR.
    destruct g. {apply atmost_atmost_equiv. assumption. } (* The greedy case has already been proven*)
    split. simpl. rewrite UNDEFGROUPS. reflexivity.
    intros i g t1 t2 T1 T2. inversion T1; subst.
    destruct dir, delta1, delta2; simpl in *.
    - eapply unamb_list_nat_eqs; eauto.
    - eapply unamb_list_nat_eqs; eauto.
    - symmetry. eapply unamb_list_inf_eqs; eauto.
    - symmetry. eapply unamb_list_inf_eqs; eauto.
    - rewrite PeanoNat.Nat.add_comm in T2. eapply unamb_list_nat_eqs; eauto.
    - symmetry. eapply unamb_list_inf_eqs; eauto.
    - eapply unamb_list_nat_eqs; eauto.
    - symmetry. eapply unamb_list_inf_eqs; eauto.
  Qed.
  
  

  (*INDUCTION HELPERS: These proof show that if the base case true is true for the merge of regexes, then the min1 and min2 cases are true *)
  (* Intermediate step: r{0, delta1}r{min2, delta2} = r{min2, delta1 + delta2}*)
  Theorem unamb_equivalence_chain_I1:
    forall r g1 g2 g3 min2 delta1 delta2,
      def_groups r = [] -> 
      (* if the tree corresponding to the regex is unambigous *)
      unamb [Areg r] ->
      (Sequence (Quantified g1 0 delta1 r) (Quantified g2 0 delta2 r))
        ≅[rer] (Quantified g3 0 (delta1 + delta2)%NoI r) ->
      (* r{0, Delta1, g } *)
      (Sequence (Quantified g1 0 delta1 r) (Quantified g2 min2 delta2 r))
        ≅[rer] (Quantified g3 min2 (delta1 + delta2)%NoI r).
  Proof.
    intros reg g1 g2 g3 min2 delta1 delta2 GROUPEMPT UNAMBR IH.
    induction min2.
    (* Base case: done in previous proof*)
    - eapply IH; eauto.
    (*Inductive case: if is true for min2 then it is true for min2 + 1*)
    - (*r{0, delta1} r{min2+1, delta2}*)
      etransitivity. {      
        apply seq_equiv. reflexivity.
        apply unamb_quantifier_pops_right; assumption.
      }
      (* r{0, delta1} (r{min2, delta2} r{1,0})*)
      rewrite sequence_assoc_equiv.
      (* (r{0, delta1} r{min2, delta2}) r{1,0}*)
      etransitivity. {
        apply seq_equiv. apply IHmin2. reflexivity.
      }
      (* (r{min2, delta1 + delta2})  r{1,0} using IH*)
      etransitivity. {
        eapply seq_equiv. reflexivity.
        rewrite quantified_one_equiv; auto.
        rewrite <- quantified_one_equiv with (greedy := g3); auto. reflexivity.
      }
      rewrite <- unamb_quantifier_pops_right; try assumption.
      (* r{min2 + 1, delta1 + delta2} *)
      reflexivity.
  Qed.

  
  (* Final statement: if a tree is unambigous then the two chains correspond *)
  Theorem unamb_equivalence_chain:
    forall r g1 g2 g3 min1 min2 delta1 delta2,
      def_groups r = [] -> 
      (* if the tree corresponding to the regex is unambigous *)
      unamb [Areg r] ->
      (* if the base case is true*)
      (Sequence (Quantified g1 0 delta1 r) (Quantified g2 0 delta2 r))
        ≅[rer] (Quantified g3 0 (delta1 + delta2)%NoI r) ->
      (Sequence (Quantified g1 min1 delta1 r) (Quantified g2 min2 delta2 r))
        ≅[rer] (Quantified g3 (min1 + min2) (delta1 + delta2)%NoI r).
  Proof.
    intros r g1 g2 g3 min1 min2 Delta1 Delta2  GROUPEMPT UNAMBR.
    induction min1.
    (* Base case: done in an adjacent proof*)
    - apply unamb_equivalence_chain_I1; eauto.
    (*Inductive case: if is true for min1 then it is true for min1 + 1*)
    - (*r{min1+1, delta1} r{min2, delta2}*)
      etransitivity. {      
        apply seq_equiv. 2: reflexivity.
        apply unamb_quantifier_pops_left; assumption.
      }
      (* (r{1,0} r{min1, delta1}) r{min2, delta2}*)
      rewrite <- sequence_assoc_equiv.
      (* r{1,0} (r{min1, delta1} r{min2, delta2})*)
      etransitivity. {
        apply seq_equiv. reflexivity.
        apply IHmin1; auto.
      }
      (* r{1,0} (r{min1 + min2, delta1 + delta2}) using IH*)
      etransitivity. {
        eapply seq_equiv. 
        rewrite quantified_one_equiv; auto.
        rewrite <- quantified_one_equiv with (greedy := g3); auto. all: reflexivity.
      }
      rewrite <- unamb_quantifier_pops_left; try assumption.
      (* r{min1 + min2 + 1, delta1 + delta2} *)
      reflexivity.
  Qed.



  (* FINAL THEOREMS: all the equalities we initially wanted to prove*)
  Theorem unamb_equivalence_chain_uni_g:
    forall r g min1 min2 delta1 delta2,
      def_groups r = [] -> 
      (* if the tree corresponding to the regex is unambigous *)
      unamb [Areg r] ->
      (* if the base case is true*)
      (Sequence (Quantified g min1 delta1 r) (Quantified g min2 delta2 r))
        ≅[rer] (Quantified g (min1 + min2) (delta1 + delta2)%NoI r).
    intros.
    eapply unamb_equivalence_chain; auto. eapply unamb_equivalence_base_case; auto.
  Qed.
  
  (* Same as above only this time in respect to the function *)
  Corollary unamb_fun_equivalence_chain:
    forall r g min1 min2 delta1 delta2,
      def_groups r = [] -> 
      (* if the tree corresponding to the regex is unambigous *)
      na r = true ->
      (* r{min1, Delta1, g } *)
      (Sequence (Quantified g min1 delta1 r)
         (* r{min2, Delta2, g } *)
         (Quantified g min2 delta2 r))
        ≅[rer] (Quantified g (min1 + min2) (delta1 + delta2)%NoI r).
  Proof.
    intros r g min1 min2 delta1 delta2 GROUPEMPT NATRUE.
    (* just translate the original statement to the function*)
    eapply unamb_equivalence_chain_uni_g; try apply naive_unambiguity; auto.
  Qed.

  Lemma atmost_leaves_incl_self (d: non_neg_integer_or_inf) (g: bool)r:
    forall inp gm1  dir tm,
      is_tree rer [Areg (Quantified g 0 d r)] inp gm1 dir tm ->
      incl [(inp, gm1)] (tree_leaves tm gm1 inp dir).
  Proof.
    intros i gm dir tm TM.
    specialize (is_tree_productivity rer [Areg (Quantified g 0 0 r)] i gm dir) as [tn  TN].
    pose proof (atmost_leaves_incl' _ _ d _ _ _ _ _ _ tm TN).
    inversion TN; inversion SKIP; subst. simpl in H.
    destruct d; eapply H; auto.
    destruct plus; discriminate.
  Qed.


  
  Lemma atmost_leaves_incl_self_double (d1 d2: non_neg_integer_or_inf) (g1 g2: bool)r:
    forall inp gm1 dir tm,
      is_tree rer [Areg (Quantified g1 0 d1 r); Areg (Quantified g2 0 d2 r)] inp gm1 dir tm ->
      incl [(inp, gm1)] (tree_leaves tm gm1 inp dir).
  Proof.
    intros i gm1 dir tm T1.
    inversion T1; subst. inversion SKIP; subst.
    inversion SKIP0; subst. intros x iA. inversion iA.
    simpl. left. assumption. inversion H.
    inversion SKIP0; subst. destruct g2; simpl; intros x iA.
    apply in_or_app. right. assumption.
    constructor. inversion iA; auto. inversion H.
    apply atmost_leaves_incl_self in SKIP. intros x iA.
    specialize (SKIP x iA). destruct g1; simpl; apply in_or_app. 
    right. assumption. left. assumption.
  Qed.

  Lemma quantifier_inf_step_advances_incl:
    forall i r  dir acts1 acts2 g t1 t2, 
      is_tree rer ([Areg r; Acheck i] ++ acts1) i g dir t1 ->
      is_tree rer ([Areg r; Acheck i] ++ acts2) i g dir t2 ->
      (forall i' gm' t3 t4, is_tree rer acts1 i' gm' dir t3 ->
                       is_tree rer acts2 i' gm' dir t4 ->
                       remaining_length i' dir < remaining_length i dir ->
                       incl (tree_leaves t3 gm' i' dir) (tree_leaves t4 gm' i' dir)) ->
      incl (tree_leaves t1 g i dir) (tree_leaves t2 g i dir).
  Proof.
    intros. intros x xInA.
    specialize (is_tree_productivity rer [Areg r] i g dir) as [t5 T5].
    rewrite app_cons in H, H0. eapply leaves_concat with (act1 := [Areg r])in H, H0; eauto.
    remember (tree_leaves t5 g i dir) as l1.
    remember (tree_leaves t2 g i dir) as l2.
    remember (tree_leaves t1 g i dir) as l3. clear Heql1 Heql2 Heql3.
    generalize dependent l3.
    revert l1 l2 H0.
    induction l1; intros.
    - inversion H. rewrite <- H4 in xInA. contradiction.
    - inversion H0; inversion H; subst.
      eapply in_or_app.
      apply in_app_or in xInA as [c1 | c2].
      left. inversion HEAD; inversion HEAD0; subst.
      inversion TREE; inversion TREE0; try contradiction; subst.
      destruct a. simpl in *.
      2: contradiction.
      2: right; eapply IHl1; eauto.
      clear IHl1.
      revert x c1. eapply H1; eauto. 
      eapply strict_suffix_remaining_length. auto.
  Qed.

  
  Lemma quant_seg_incl (n: nat):
    forall r inp gm g d1 d2 dir tm  tn ,
      def_groups r = [] ->
      is_tree rer ([Areg (Quantified true 0 +∞ r);Areg (Quantified g 0 d1 r)]) inp gm dir tm ->
      is_tree rer  ([Areg (Quantified false 0 d2 r)]) inp gm dir tn ->
      incl (tree_leaves tn gm inp dir) (tree_leaves tm gm inp dir).
  Proof.
    intros. remember (remaining_length inp dir) as l.
    assert (Hlength_le: remaining_length inp dir <= l) by lia. clear Heql. generalize dependent inp. revert tm tn d1 d2 gm.
    induction l; intros.
    - specialize (is_tree_productivity rer [Areg (Quantified g 0 d1 r)] inp gm dir) as [t5 T5].
      eapply quantifier_null_length_skip with (acts := [Areg (Quantified g 0 d1 r)])in H0; eauto; eauto.
      eapply quantifier_null_length in T5, H1; auto. rewrite H0, T5, H1. intros x xIn; assumption.
    - inversion H1.
      + inversion SKIP. subst. simpl. eapply atmost_leaves_incl_self_double; eauto.
      + subst. simpl. intros x xIn. apply in_app_or in xIn as [c1 | c2]. revert x c1.
        inversion SKIP; subst. simpl. eapply atmost_leaves_incl_self_double; eauto.
        inversion H0; subst. simpl. eapply in_or_app. left.
        rewrite H in *. simpl in *. eapply quantifier_inf_step_advances_incl with (acts1 := [Areg (Quantified false 0 plus r)]) (acts2 := [Areg (Quantified true 0 plus0 r); Areg (Quantified g 0 d1 r)]); eauto.
        destruct plus0. discriminate.
        intros. eapply IHl; eauto. 
        lia.
  Qed.
  
  Lemma leaves_equiv_incl3:
    forall a b c,
      incl b a ->
      leaves_equiv [] a c ->
      leaves_equiv [] (a ++ b) c.
  Proof.
    intros. rewrite <- app_nil_r. eapply leaves_equiv_app2.
    assumption. rewrite app_nil_r. revert a H H0.
    induction b. intros a H H0. reflexivity.
    intros. destruct a. constructor.
    Search is_seen. rewrite is_seen_spec.
    eapply H; eauto. simpl. left. reflexivity.
    eapply IHb; eauto. intros x iA. specialize (H x). simpl in H.
    eapply H. right; auto.
  Qed.


  Lemma leaves_equiv_incl4:
    forall a b c d,
      incl c a ->
      leaves_equiv [] (a ++ b) d ->
      leaves_equiv [] (a ++ b ++ c) d.
  Proof.
    intros. rewrite app_assoc.
    eapply leaves_equiv_incl3 ; eauto.
    intros x xIa. apply in_or_app. left. auto.
  Qed.

  Lemma leaves_equiv_incl2:
    forall a b c d e: list leaf,
      leaves_equiv [] a b -> leaves_equiv [] c e ->
      incl d a ->
      leaves_equiv [] (a ++ c ++ d) (b ++ e).
  Proof.
    intros.
    apply leaves_equiv_incl4. assumption.
    apply leaves_equiv_app; auto.
  Qed.

  
  
  
  Lemma atmost_atmost_equiv_actions_trueinf_false (n: non_neg_integer_or_inf) r:
    forall dir ,
      def_groups r = [] ->
      actions_equiv_dir rer dir [Areg (Quantified true 0 +∞ r); Areg (Quantified false 0 n r)] [Areg (Quantified true 0 +∞ r)].
  Proof.
    intros dir  GROUPEMPT i.
    unfold tree_equiv_tr_dir.
    remember (remaining_length i dir) as l.
    assert (Hlength_le: remaining_length i dir <= l) by lia. clear Heql. generalize dependent i.
    induction l; intros i HeqL gm t1 t2 T1 T2.
    - eapply quantifier_null_length in T2; auto.
      specialize (is_tree_productivity rer [Areg (Quantified false 0 n r)] i gm dir) as [t3 T3].
      eapply quantifier_null_length_skip with (acts := [Areg (Quantified false 0 n r)])in T1; eauto.
      eapply quantifier_null_length in T3; subst; auto. rewrite T2, T1, T3. reflexivity.
    - inversion T1; inversion T2; inversion SKIP; subst. simpl.
      +  apply leaves_equiv_app.
         eapply quantifier_inf_step_advances with (r := r) (acts2 := [Areg (Quantified true 0 plus0 r)]) (acts1 := [Areg (Quantified true 0 plus r); Areg (Quantified false 0 (NoI.N 0) r)]); eauto.
         destruct plus0, plus; try discriminate.
         intros; eapply IHl; eauto. lia.
         inversion SKIP0; inversion SKIP1; subst; reflexivity.
      + simpl in *. apply leaves_equiv_incl2.
        eapply quantifier_inf_step_advances; eauto.
        exact ISTREE1. exact ISTREE0. intros.
        destruct plus, plus0; try discriminate.
        eapply IHl; eauto. lia.
        inversion SKIP1; inversion SKIP0; reflexivity.
        destruct plus, plus0; try discriminate.
        clear SKIP1 ISTREE0 T2 T1 H9 H1 SKIP0 IHl.
        rewrite GROUPEMPT in *. simpl in *.
        specialize (is_tree_productivity rer [Areg (Quantified false 0 plus1 r)] i gm dir) as [t4 T4].
        specialize (is_tree_productivity rer [Areg (Quantified true 0 +∞ r);
                                              Areg
                                                (Quantified false 0 match plus1 with
                                                   | NoI.N r' => NoI.N (S r')
                                                   | +∞ => +∞
                                                   end
                                                   r)] i gm dir) as [t5 T5].
        eapply quantifier_inf_step_advances_incl with (acts1 := [Areg (Quantified false 0 plus1 r)]) (acts2 := [Areg (Quantified true 0 +∞ r);
                                                                                                                Areg
                                                                                                                  (Quantified false 0 match plus1 with
                                                                                                                     | NoI.N r' => NoI.N (S r')
                                                                                                                     | +∞ => +∞
                                                                                                                     end
                                                                                                                     r)]); simpl; eauto.
        intros; eapply quant_seg_incl; eauto.
  Qed.

  
  Lemma atmost_atmost_equiv_actions_false_trueinf (n: non_neg_integer_or_inf) r:
    forall dir ,
      def_groups r = [] ->
      actions_equiv_dir rer dir [Areg (Quantified false 0 n r); Areg (Quantified true 0 +∞ r)] [Areg (Quantified true 0 +∞ r)].
  Proof.
    intros dir GROUPEMPT i.
    unfold tree_equiv_tr_dir.
    remember (remaining_length i dir) as l. 
    assert (Hlength_le: remaining_length i dir <= l) by lia. clear Heql. generalize dependent i. revert n.
    induction l; intros n i HeqL gm t1 t2 T1 T2.
    - eapply quantifier_null_length in T2.
      specialize (is_tree_productivity rer [Areg (Quantified true 0 +∞ r)] i gm dir) as [t3 T3].
      eapply quantifier_null_length_skip with (acts := [Areg (Quantified true 0 +∞ r)])in T1; eauto. 2: lia.
      eapply quantifier_null_length in T3; eauto. rewrite T2, T1, T3. reflexivity.
    - apply Nat.lt_eq_cases in HeqL as [c1 | c2].
      eapply IHl; eauto. lia.
      inversion T1; inversion T2;  subst. simpl.
      eapply is_tree_determ in T2; eauto. subst; reflexivity.
      simpl. eapply leaves_equiv_app5. inversion SKIP; subst. simpl.
      destruct plus1, plus0; try discriminate.
      eapply leaves_equiv_app. eapply is_tree_determ  with (t1 := titer1) in ISTREE0; eauto.
      subst. reflexivity.
      inversion SKIP0; inversion SKIP1; subst. reflexivity.
      rewrite GROUPEMPT in *. simpl in *.
      eapply quantifier_inf_step_advances with (acts2 := [Areg (Quantified true 0 plus0 r)]) (acts1 := [Areg (Quantified false 0 plus r); Areg (Quantified true 0 +∞ r)]); eauto.
      destruct plus0. discriminate.
      intros. eapply IHl; eauto. lia.
  Qed.

  Lemma atmost_atmost_equiv_true_false:
    forall r  min1 min2 delta2 g,
      def_groups r = [] ->
      unamb [Areg r] -> 
      (Sequence (Quantified true min1 +∞ r) (Quantified g min2 delta2 r))
        ≅[rer] (Quantified true (min1 + min2) +∞ r).
  Proof.
    intros r m1 m2 delta2 g GROUPEMPT UNAMBR.
    eapply unamb_equivalence_chain; auto.
    destruct g. eapply unamb_equivalence_chain_uni_g; eauto.
    split. simpl. rewrite GROUPEMPT. reflexivity.
    destruct dir; simpl; intros i gm t1 t2 T1 T2. 
    inversion T1; subst. simpl in CONT.
    eapply atmost_atmost_equiv_actions_trueinf_false; eauto.
    inversion T1; subst. simpl in CONT.
    eapply atmost_atmost_equiv_actions_false_trueinf; eauto.
  Qed.

  Lemma atmost_atmost_equiv_false_true:
    forall r  min1 min2 delta1 g,
      def_groups r = [] ->
      unamb [Areg r] -> 
      (Sequence (Quantified g min1 delta1 r) (Quantified true min2 +∞ r))
        ≅[rer] (Quantified true (min1 + min2) +∞ r).
  Proof.
    intros r m1 m2 delta1 g GROUPEMPT UNAMBR.
    assert ((delta1 + +∞)%NoI = +∞). destruct delta1; auto.
    rewrite <- H at 2. eapply unamb_equivalence_chain; auto.
    destruct g. eapply unamb_equivalence_chain_uni_g; eauto.
    split. simpl. rewrite GROUPEMPT. reflexivity.
    rewrite H.
    destruct dir; simpl; intros i gm t1 t2 T1 T2. 
    inversion T1; subst. simpl in CONT.
    eapply atmost_atmost_equiv_actions_false_trueinf; eauto.
    inversion T1; subst. simpl in CONT.
    eapply atmost_atmost_equiv_actions_trueinf_false; eauto.
  Qed.

End UnAmbiguity.

