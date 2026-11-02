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

  (* Prefix of list (like inclusion but keeping a sense of order) *)
  Definition prefix {A} (a b: list A) :=
    exists acts, b = a ++ acts.

  (** Inductive definition of prefix **)
  Lemma prefix_head {A}:
    forall (a b c: list A),
      prefix (a ++ b) (a ++ c) ->
      prefix b c.
  Proof.
    intros a b c [acts actsEq].
    exists acts. rewrite <- app_assoc in actsEq.
    apply app_inv_head in actsEq. auto.
  Qed.

  (** Inductive definition of prefix **)
  Lemma prefix_h {A}:
    forall a (b c: list A),
      prefix (a :: b) (a :: c) ->
      prefix b c.
  Proof.
    intros a b c d. 
    eapply prefix_head. rewrite <- app_cons.
    rewrite <- app_cons. exact d.
  Qed.

  (** Base case of prefix **)
  Lemma prefix_base {A}:
    forall (a: list A),
      prefix [] a.
  Proof.
    intros a. exists a. auto.
  Qed.

  (** Reflexivity of prefix **)
  Lemma prefix_refl {A}:
    forall (a: list A),
      prefix a a.
  Proof.
    intros. exists []. rewrite app_nil_r. auto.
  Qed.
  
  (** If a list has a prefix and is equal to another  list then we can append the prefix in the equality **)
  Theorem leaves_equiv_pref:
    forall l1 l2 l3 ,
      leaves_equiv [] l1 l3 ->
      prefix l2 l1 ->
      leaves_equiv [] l1 (l2 ++ l3).
  Proof.
    intros t1 t2 t3  lEq1 [acts lPref].
    rewrite lPref in lEq1. rewrite  lPref. clear t1 lPref.
    assert (leaves_equiv [] t2 t2) by reflexivity.
    eapply leaves_equiv_app  with (p1 := t2) in lEq1. 2: reflexivity.
    eapply leaves_equiv_trans; eauto.
    rewrite app_assoc. apply leaves_equiv_app with (l1 := acts) (l2 := acts).
    2: reflexivity.
    eapply leaves_equiv_repet.
  Qed.

  (* If a property is true for all elements in a list it is true for it's head and it's tail*)
  Lemma in_concat_prop:
    forall d rest P, 
      (forall a : action, In a (d :: rest) -> P a) ->
      P d /\ (forall a, In a rest -> P a).
  Proof.
    intros. split. 
    eapply H. simpl. auto.
    intros. apply H. simpl. auto.
  Qed.


  (* If all elements in a list do not define groups, and are either a regex or a check ,then the group in the tree will be the same*)
  Lemma emptygroups_const_groups_ind:
    forall acts inp inp2 gm gm2 dir t,
      is_tree rer acts inp gm dir t ->
      (forall a, In a acts -> (exists r, a = (Areg r) /\ def_groups r = []) \/ exists inp, a = (Acheck inp)) ->
      In (inp2, gm2) (tree_leaves t gm inp dir) ->
      gm = gm2.
  Proof.
    intros acts i1 i2 g1 g2 dir t1 T1 inTa inT.
    revert i2 g2 inT inTa.
    (* simple case: derives directly from definition*)
    induction T1; intros; simpl in inT; try inversion inT; try inversion H; try reflexivity.
    (* The property is true both for the head and the tail*)
    all: eapply in_concat_prop in inTa as [[[rn rnIn] | [i iIn]] d3].
    (* Delete cases where we have a check*)
    all: try (destruct rnIn; inversion H); try discriminate.
    (* Divide all cases where in contains two lists*)
    all: try apply in_app_or in inT as [c1 | c2].
    (* Solve all trivial cases *)
    all: try (eapply IHT1; eauto; intros).
    - unfold advance_input' in inT.
      apply read_char_success_advance in READ.
      rewrite READ in inT. exact inT.
    - eapply IHT1_1; eauto; intros. subst. simpl in H0.
      apply app_eq_nil in H0 as [l1 l2]. 
      destruct H1. left. exists r1; split; auto.
      eapply d3; eauto.
    - eapply IHT1_2; eauto; intros. subst. simpl in H0.
      apply app_eq_nil in H0 as [l1 l2].
      destruct H1. left. exists r2; split; auto.
      eapply d3; eauto.
    - intros. apply in_app_or in H1 as [in1 | in2].
      2: eapply d3; eauto.
      subst. simpl in H0. apply app_eq_nil in H0 as [l1 l2].
      destruct dir; destruct in1; try inversion H0; try inversion H1; left.
      1, 4: (exists r1; split; eauto).
      all: (exists r2; split; eauto).
    - subst. simpl in H0. rewrite H0 in *.
      simpl in *. eapply IHT1; eauto. intros.
      repeat destruct H1; eauto. 
    - subst. simpl in H0. rewrite H0 in *.
      simpl in *. destruct greedy; simpl in inT.
      all: apply in_app_or in inT as [inT1 | inT2].
      2, 3: eapply IHT1_2; eauto.
      all: eapply IHT1_1; intros; repeat destruct H1; eauto. 
    - subst. simpl in H0. rewrite app_cons in H0.
      apply app_eq_nil in H0 as [l1 l2]. discriminate.
    - unfold lk_result in RES_LK. rewrite first_tree_leaf in RES_LK.
      remember (positivity lk) as l1.
      remember (tree_leaves treelk gm inp (lk_dir lk)) as l2.
      destruct l1, l2; try inversion inT.
      + destruct l. simpl in *. inversion RES_LK; subst.
        assert (gmlk = g2). eapply IHT1_2; eauto. subst.
        eapply IHT1_1; eauto. intros. destruct H1; auto. left; exists r1; split; auto.
        contradiction.
      + simpl in RES_LK. inversion RES_LK; subst. eapply IHT1_2; eauto.
    - eapply read_backref_success_advance in READ_BACKREF.
      rewrite <- READ_BACKREF in inT; exact inT.
  Qed.

  
  (* In the case where we define no groups, the groups created remain constant *)
  Lemma emptygroups_const_groups:
    forall  r inp inp2 gm gm2 dir t,
      def_groups r = [] ->
      is_tree rer [Areg r] inp gm dir t ->
      In (inp2, gm2) (tree_leaves t gm inp dir) ->
      gm = gm2.
  Proof.
    intros. eapply emptygroups_const_groups_ind; eauto.
    intros. inversion H2; inversion H3. subst.  left. exists r. split; eauto.
  Qed.

  (* Lemmas on leaves: here are some lemmas that manage tree representations *)
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
    rewrite app_cons in TREE1, TREE2.
    eapply leaves_concat with (act1 := [Areg r1]) in TREE1, TREE2; eauto.
    eapply unamb_list in UNAMBR as [t | [[inp2 gm2] t]]; eauto; rewrite t in TREE1, TREE2.
    (* Case 1: list is empty*)
    - inversion TREE1; inversion TREE2; subst. reflexivity.
    (* Case 2: length of list = a *)
    - apply FlatMap_one_leaf in TREE2, TREE1.
      inversion TREE2; inversion TREE1; inversion TREE0.
      (* Case 2.1: Progress *)
      + subst; simpl.
        rewrite  (is_tree_determ  _ _ _ _ _ _ _ TREE TREECONT). reflexivity.
      (* Case 2.2: Mismatch *)
      + clear TREE2 TREE1 H3. subst; simpl in *.
        assert (IinT3: In (inp2, gm2) (tree_leaves t3 gm inp dir)).
        destruct g; simpl; rewrite t; left; reflexivity.   
        assert (inp = inp2) by (eapply input_does_not_back; eauto).
        assert (gm = gm2) by (eapply emptygroups_const_groups; eauto).
        inversion TREE; inversion SKIP; subst. simpl. leaves_equiv_t.
        rewrite UNDEFGROUPS in *; simpl in *.
        rewrite app_cons in ISTREE1.
        eapply leaves_concat with (act1 := [Areg r1])in ISTREE1; eauto.
        rewrite t in ISTREE1. apply FlatMap_one_leaf in ISTREE1.
        inversion ISTREE1; inversion TREE1; subst; simpl in *.
        exfalso. eapply StrictSuffix.ss_irreflexive; eauto.
        destruct g; simpl; rewrite <- H3.
        leaves_equiv_t. leaves_equiv_t.
  Qed.
  
  


  (* If a regex is unambigous and does not define any groups, then we can get rid of a check if (inp, gm) is present at the end *)
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
    eapply unamb_list in UNAMBR as [t | [[inp2 gm2] t]]; eauto; rewrite t in TREE1, TREE2.
    (* Case 1: list is empty*)
    - inversion TREE1; inversion TREE2; subst. reflexivity.
    (* Case 2: length of list = a *)
    - apply FlatMap_one_leaf in TREE2, TREE1.
      inversion TREE2; inversion TREE1; inversion TREE0.
      (* Case 2.1: Progress *)
      + subst; simpl.
        rewrite  (is_tree_determ  _ _ _ _ _ _ _ TREE TREECONT). reflexivity.
      (* Case 2.2: Mismatch *)
      + clear TREE2 TREE1 H3. subst; simpl in *.
        assert (IinT3: In (inp2, gm2) (tree_leaves t3 gm inp dir)).
        destruct g; simpl; rewrite t; left; reflexivity.   
        assert (inp = inp2) by (eapply input_does_not_back; eauto).
        assert (gm = gm2) by (eapply emptygroups_const_groups; eauto).
        inversion TREE; inversion SKIP; subst. simpl. leaves_equiv_t.
        rewrite UNDEFGROUPS in *; simpl in *.
        rewrite app_cons in ISTREE1.
        eapply leaves_concat with (act1 := [Areg r1])in ISTREE1; eauto.
        rewrite t in ISTREE1. apply FlatMap_one_leaf in ISTREE1.
        inversion ISTREE1; inversion TREE1; subst; simpl in *.
        exfalso. eapply StrictSuffix.ss_irreflexive; eauto.
        destruct g; simpl; rewrite <- H3.
        leaves_equiv_t. leaves_equiv_t.
  Qed.

  (* If a lazy quantifier has a lower number than another, then it is a prefix of it *)
  Theorem atmost_level_prefix (m: nat) (d: non_neg_integer_or_inf) r:
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
      unamb [Areg r] ->
      is_tree rer
        [Areg (Quantified false 0 delta1 r); Areg (Quantified false 0 delta2 r)]
        i g dir t1 ->
      is_tree rer [Areg (Quantified false 0 (delta1 + delta2)%NoI r)] i g dir t2 ->
      leaves_equiv [] (tree_leaves t1 g i dir)
        (tree_leaves t2 g i dir).
  Proof.
    intros r i g d t1 t2 delta1 . revert i g t1 t2. 
    induction delta1; intros i g t1 t2 delta2 UNAMBR T1 T2.
    - inversion T1; subst. 2: destruct plus; discriminate. destruct delta2; simpl in T1, T2.
      all: specialize (is_tree_determ _ _ _ _ _ _ _ T2 SKIP) as cd; rewrite cd; reflexivity.
    - inversion T1; inversion T2; subst. destruct delta2; discriminate.
      rewrite app_cons in ISTREE1, ISTREE0. 
      specialize (is_tree_productivity rer [Areg r] i (GroupMap.reset (def_groups r) g) d) as [t3 T3].
      eapply leaves_concat with (act1 := [Areg r]) in ISTREE1, ISTREE0; eauto. simpl.
      specialize (unamb_list _ _ _ _ _ UNAMBR T3) as [e1 | [el e2]].
      simpl in *. rewrite e1 in ISTREE0, ISTREE1. inversion ISTREE0; inversion ISTREE1; subst.
      inversion SKIP0; inversion SKIP; subst. inversion SKIP1; reflexivity.
      inversion SKIP1; subst. simpl.
      rewrite app_cons in ISTREE2. 
      eapply leaves_concat with (act1 := [Areg r]) in ISTREE2; eauto. simpl in ISTREE2.
      rewrite e1 in ISTREE2. inversion ISTREE2; subst. reflexivity.
      simpl in *. rewrite e2 in ISTREE0, ISTREE1. apply FlatMap_one_leaf in ISTREE0, ISTREE1.
      inversion ISTREE1; inversion ISTREE0; try discriminate; subst. destruct el; simpl in *.
      inversion SKIP; inversion SKIP1; inversion SKIP0; subst. simpl.
      + etransitivity. 1, 2: rewrite app_cons. reflexivity.
        apply leaves_equiv_app. reflexivity. inversion H1; inversion H0; subst.
        inversion TREE0; inversion TREE; try contradiction; subst. simpl.
        destruct plus, plus0; try discriminate. inversion H0; inversion H9. subst.
        eapply IHdelta1; eauto. simpl. reflexivity.
      + rewrite app_cons in ISTREE2. 
        eapply leaves_concat with (act1 := [Areg r]) in ISTREE2; eauto. simpl in ISTREE2.
        rewrite e2 in ISTREE2. apply FlatMap_one_leaf in ISTREE2.
        inversion ISTREE2; subst.
        inversion TREE0; inversion TREE1; inversion TREE; try contradiction; subst.
        2: simpl;  rewrite <- H5; reflexivity.
        simpl. etransitivity. 1, 2: rewrite app_cons. reflexivity.
        apply leaves_equiv_app. reflexivity.
        destruct plus0, plus1; try discriminate.
        inversion H9; destruct plus. 2: discriminate. inversion H1; subst.
        pose proof (atmost_level_prefix _  (S delta1) _ _ _ _ _ treecont TREECONT0).
        simpl in H. assert (n0 + S delta1 = delta1 + S n0) by lia. rewrite H0 in H.
        specialize (H TREECONT UNAMBR) as [acts eq]. 
        symmetry. eapply leaves_equiv_pref; unfold prefix; eauto. symmetry.
        eapply IHdelta1; eauto. rewrite <- H5. simpl. exists acts. auto.
        symmetry. eapply leaves_equiv_pref; eauto. destruct plus. 2: discriminate.
        inversion H1; subst.
        symmetry. eapply IHdelta1; eauto.
        exists []. rewrite <- H5. simpl. simpl in TREECONT0.
        eapply is_tree_determ in TREECONT; eauto. subst. rewrite app_nil_r.
        reflexivity.
  Qed.

  Theorem unamb_list_inf_eqs:
    forall r i g dir t1 t2 delta1,
      unamb [Areg r] ->
      is_tree rer [Areg (Quantified false 0 +∞ r)] i g dir t1 ->
      is_tree rer
        [Areg (Quantified false 0 +∞ r); Areg (Quantified false 0 delta1 r)]
        i g dir t2 ->
      leaves_equiv [] (tree_leaves t1 g i dir)
        (tree_leaves t2 g i dir).
  Proof.
    intros r i g dir t1 t2 delta2 UNAMBR T1 T2.
    remember (remaining_length i dir) as l.
    assert (Hlength_le: remaining_length i dir <= l) by lia. clear Heql.
    revert i g t1 t2 T1 T2 Hlength_le.
    induction l; intros i g t1 t2 T1 T2 Hlength_le; simpl.
    - specialize (is_tree_productivity rer [Areg (Quantified false 0 delta2 r)] i g dir) as [t3 T3].
      eapply quantifier_null_length_skip with (t2 := t3) in T2; eauto.
      eapply quantifier_null_length in T3, T1; eauto. rewrite T1, T2, T3. reflexivity.
    - apply GroupId.le_lteq in Hlength_le as [p1 | p2].
      rewrite  Nat.lt_succ_r in p1.  eapply IHl; eauto.
      inversion T1; inversion T2; subst. simpl. destruct plus, plus0; try discriminate.
      simpl in *. specialize (is_tree_productivity rer [Areg r] i (GroupMap.reset (def_groups r) g) dir ) as [t3 T3].
      inversion SKIP0; subst.
      + eapply leaves_concat with (act1 := [Areg r]) in ISTREE0, ISTREE1; eauto. inversion SKIP1; inversion SKIP; subst. simpl.
        specialize (unamb_list _ _ _ _ _ UNAMBR T3) as [lEmpt | [el ld]].
        rewrite lEmpt in ISTREE1, ISTREE0. inversion ISTREE1; inversion ISTREE0.
        reflexivity.
        rewrite ld in ISTREE1, ISTREE0. apply FlatMap_one_leaf in ISTREE1, ISTREE0.
        inversion ISTREE1; inversion ISTREE0; subst.
        destruct el; simpl in *.
        inversion TREE0; inversion TREE; try contradiction; subst.
        simpl. etransitivity. 1, 2: rewrite app_cons. reflexivity.
        apply leaves_equiv_app. reflexivity.
        eapply IHl; eauto. 
        pose proof (strict_suffix_remaining_length _ _ _ PROGRESS). lia.
        reflexivity.
      + eapply leaves_concat with (act1 := [Areg r]) in ISTREE0, ISTREE1, ISTREE2; eauto. inversion SKIP1; inversion SKIP; subst. simpl.
        specialize (unamb_list _ _ _ _ _ UNAMBR T3) as [lEmpt | [el ld]].
        rewrite lEmpt in ISTREE1, ISTREE0, ISTREE2. inversion ISTREE1; inversion ISTREE0; inversion ISTREE2.
        
        reflexivity.
        rewrite ld in ISTREE1, ISTREE0, ISTREE2. apply FlatMap_one_leaf in ISTREE1, ISTREE0, ISTREE2.
        inversion ISTREE1; inversion ISTREE0; inversion ISTREE2; subst.
        destruct el; simpl in *.
        inversion TREE0; inversion TREE; inversion TREE1; try contradiction; subst.
        2: simpl; reflexivity.
        simpl. etransitivity. 1, 2: rewrite app_cons. reflexivity.
        apply leaves_equiv_app. reflexivity.
        destruct plus. 
        pose proof (atmost_level_prefix _  +∞ _ _ _ _ _ treecont0 TREECONT1).
        simpl in H. specialize (H TREECONT0 UNAMBR) as [acts eq]. 
        eapply leaves_equiv_pref; unfold prefix; eauto. eapply IHl; eauto.
        pose proof (strict_suffix_remaining_length _ _ _ PROGRESS); try lia.
        pose proof (is_tree_determ _ _ _ _ _ _ _ TREECONT0 TREECONT1); subst.
        eapply leaves_equiv_pref; unfold prefix;  eauto. eapply IHl; eauto.
        pose proof (strict_suffix_remaining_length _ _ _ PROGRESS); try lia.
        exists []. rewrite app_nil_r; reflexivity.
  Qed.
  
  
  

  (* SYNTAXIC LEMMAS: some syntaxic rules to simplify the overall structure of the proof *)
  
  (* you can distribute an unambiguous regex on the left *)
  Theorem unamb_distribute_left:
    forall r1 r2 r3,
      unamb [Areg r1] ->
      (Sequence r1 (Disjunction r2 r3)) ≅[rer] (Disjunction (Sequence r1 r2) (Sequence r1 r3)).
  Proof.
    unfold unamb. intros r1 r2 r3  UA.
    split. simpl. solve_groups_equiv.
    destruct dir.
    (* the backward case is true even without unambiguity *)
    2: { apply Distributivity.LeftBackward.factored_expanded_left_equiv. }
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
      unamb [Areg r3] ->
      (Sequence (Disjunction r1 r2) r3) ≅[rer] (Disjunction (Sequence r1 r3) (Sequence r2 r3)).
  Proof. 
    intros r1 r2 r3 UNAMBR3.
    split. simpl. solve_groups_equiv.
    destruct dir.
    apply Distributivity.Right.factored_expanded_right_equiv. 
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

  
  (* If a regex is unambigous, then it's open greedy quantified can expand into a disjunction*)
  Theorem non_greedy_quantifier_steps_opt:
    forall r n,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified false 0 (n + 1) r) ≅[rer] (Disjunction Epsilon (Quantified false 1 n r)).
  Proof.
    intros r n GROUPEMPT UNAMBR.
    split. simpl. solve_groups_equiv.
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

  
  (* If a regex is unambigous, then it's open lazy quantified can expand into a disjunction*)
  Theorem greedy_quantifier_steps_opt:
    forall r n ,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified true 0 (S n)%NoI r) ≅[rer] (Disjunction (Quantified true 1 n r) Epsilon).
  Proof.
    intros r n GROUPEMPT UNAMBR.
    split. simpl. solve_groups_equiv.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; inversion TREE2; inversion ISTREE0; inversion ISTREE2; subst.
    clear TREE1 TREE2 ISTREE0 ISTREE2. 
    rename titer into t11. rename tskip into t12. rename t3 into t22. rename titer0 into t21.
    rename ISTREE1 into TREE11. rename ISTREE into TREE22.
    rename ISTREE3 into TREE21. rename SKIP into TREE12.
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
    destruct dir. {apply quantified_S_equiv_forward. }
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
      etransitivity. {
        apply seq_equiv_dir. reflexivity.
        rewrite <- quantified_S_equiv_backward. reflexivity. }
      reflexivity. 
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
        rewrite (unamb_distribute_right _ _ _ UNAMBR backward).
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
        rewrite <- (unamb_distribute_left _ _ _  UNAMBR backward).
        (* r (r{1, delta1} | )  *)
        etransitivity. { eapply seq_equiv. rewrite <- quantified_one_equiv. 3: rewrite <- greedy_quantifier_steps_opt. all: auto. all: reflexivity. }
        (* r{1, 0} r{0, delta1 + 1}  *)
        reflexivity.
      + (* Nongreedy case *)
        etransitivity. { eapply seq_equiv. rewrite <- Nat.add_1_r.  apply non_greedy_quantifier_steps_opt. 3: apply quantified_one_equiv. all: auto. }
        (* (| r{1, delta1}) r *)
        rewrite (unamb_distribute_right _ _ _  UNAMBR backward).
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
        rewrite <- (unamb_distribute_left _ _ _  UNAMBR backward).
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
      inversion T1; inversion T2; subst; simpl in CONT. clear T1 T2.
      generalize dependent i. revert g t2 titer.
      induction l; intros g t1 t2 i Hlength_le TREE1 TREE2. 
      + specialize  (is_tree_productivity rer [Areg (Quantified g 1 (NoI.N 0) r)] i gm backward) as [t4 T4]. 
        eapply quantifier_null_length_skip with (acts := [Areg (Quantified g 1 (NoI.N 0) r)]) in TREE2; eauto.
        rewrite GROUPEMPT in *; simpl in *.
        specialize  (is_tree_productivity rer [Areg r] i gm backward) as [t3 T3].
        eapply quantifier_null_length_head  with (t2 := t3) in TREE1; eauto.
        etransitivity. eapply TREE1.
        inversion T4; subst. rewrite GROUPEMPT in *; simpl in *.
        eapply quantifier_null_length_head in ISTREE1; eauto.
        symmetry. rewrite TREE2. auto.
      + Admitted.
  
  
  Theorem unamb_quantifier_pops_right:
    forall r m n g,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified g (S m) n r)
        ≅[rer] Sequence (Quantified g m n r) (Quantified g 1 (NoI.N 0) r).
  Proof.
    intros r m n g GROUPEMPT UNAMBR
      dir.
    destruct dir. 2: {apply quantified_S_equiv_backward. } (* Backward case has already been proven*)
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
      reflexivity. 
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
      rewrite (unamb_distribute_left _ _ _  UNAMBR forward).
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
      rewrite <- (unamb_distribute_right _ _ _  UNAMBR forward).
      (* (r{1, delta1} | ) r *)
      etransitivity. { eapply seq_equiv. 2: rewrite <- quantified_one_equiv. rewrite <- greedy_quantifier_steps_opt. all: auto. all: reflexivity. }
      (* r{0, delta1 + 1} r{1, 0} *)
      reflexivity.
    -  (* Nongreedy case *)
      etransitivity. { eapply seq_equiv. 2:rewrite <- Nat.add_1_r; apply non_greedy_quantifier_steps_opt. apply quantified_one_equiv. all: auto. }
      (* r (| r{1, delta1}) *)
      rewrite (unamb_distribute_left _ _ _  UNAMBR forward).
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
      rewrite <- (unamb_distribute_right _ _ _  UNAMBR forward).
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
    - Admitted.
  


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
    destruct g. {apply atmost_atmost_equiv. } (* The greedy case has already been proven*)
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

  
  (* Genetal helper statement: if a regex is unambigous and the base case is true for the quantified merge, then the merge is also true for all min1, min2 *)
  Theorem unamb_equivalence_chain_ind:
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
    (* The base cas has to be given in an adjacent proof*)
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


  (** Final proofs: show equalities of quantified merges **)

  (* Can merge any two quantifiers if the regex is unambigous and they are both greedy or lazy*)
  Theorem unamb_equivalence_chain_uni_g:
    forall r g min1 min2 delta1 delta2,
      def_groups r = [] -> 
      (* if the tree corresponding to the regex is unambigous *)
      unamb [Areg r] ->
      (Sequence (Quantified g min1 delta1 r) (Quantified g min2 delta2 r))
        ≅[rer] (Quantified g (min1 + min2) (delta1 + delta2)%NoI r).
    intros.
    eapply unamb_equivalence_chain_ind; auto. eapply unamb_equivalence_base_case; auto.
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

  
End UnAmbiguity.

