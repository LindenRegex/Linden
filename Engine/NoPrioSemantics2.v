From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics PikeSubset.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import StrictSuffix.
From Linden Require Import FunctionalSemantics.
From Linden Require Import ComputeIsTree.
From Linden Require Import Parameters.
From Linden Require Import FlatMap Equivalence FunctionalUtils.


(* A rephrasing of the semantics, where priority does not matter *)
(* It's a relation about leaves, not necessarily the first one *)
(* There are no actions, the shape of the regex determines the relation *)
(* For this version, we don't veen consider group_maps (although we could compute them along the way)
   Because for the reversal property we don't need them. *)

Section NoPrioSemantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Inductive noprio: Direction -> input -> regex -> input -> Prop :=
  | np_eps:
    forall dir inp,
      noprio dir inp Epsilon inp
  | np_char:
    forall dir inp cd c nextinp
      (READ: read_char rer cd inp dir = Some (c, nextinp)),
      noprio dir inp (Regex.Character cd) nextinp
  | np_disj_left:
    forall dir inp r1 r2 nextinp
      (LEFT: noprio dir inp r1 nextinp),
      noprio dir inp (Disjunction r1 r2) nextinp
  | np_disj_right:
    forall dir inp r1 r2 nextinp
      (RIGHT: noprio dir inp r2 nextinp),
      noprio dir inp (Disjunction r1 r2) nextinp
  | np_seq_forward:
    forall inp0 r1 r2 inp1 inp2
      (SEQ1: noprio forward inp0 r1 inp1)
      (SEQ2: noprio forward inp1 r2 inp2),
      noprio forward inp0 (Sequence r1 r2) inp2
  | np_seq_backward:
    forall inp0 r1 r2 inp1 inp2
      (SEQ1: noprio backward inp0 r2 inp1)
      (SEQ2: noprio backward inp1 r1 inp2),
      noprio backward inp0 (Sequence r1 r2) inp2
  | np_quant_forced:
    forall dir inp0 r gidl min delta greedy inp1 inp2
      (RESET: gidl = def_groups r)
      (ITER: noprio dir inp0 r inp1)
      (LOOP: noprio dir inp1 (Quantified greedy min delta r) inp2),
      noprio dir inp0 (Quantified greedy (S min) delta r) inp2
  | np_quant_done:
    forall dir inp r greedy,
      noprio dir inp (Quantified greedy 0 (NoI.N 0) r) inp
  | np_quant_free:
    forall dir inp0 r greedy delta gidl inp1 inp2
      (RESET: gidl = def_groups r)
      (ITER: noprio dir inp0 r inp1)
      (PROGRESS: strict_suffix inp1 inp0 dir)
      (LOOP: noprio dir inp1 (Quantified greedy 0 delta r) inp2),
      noprio dir inp0 (Quantified greedy 0 (NoI.N 1 + delta)%NoI r) inp2
  | np_quant_skip:
    forall dir inp r greedy delta,
      noprio dir inp (Quantified greedy 0 (NoI.N 1 + delta)%NoI r) inp
  | np_group:
    forall dir inp r gid nextinp
      (GROUP: noprio dir inp r nextinp),
      noprio dir inp (Group gid r) nextinp
  | np_anchor:
    forall dir inp a
      (ANCHOR: anchor_satisfied rer a inp = true),
      noprio dir inp (Anchor a) inp.
  
  (* LATER: there will be an issue if we want to add negative lookarounds: strict positivity *)
  (* We might want to declare an oracle version of this, since this reversal is used in engines when we already know about the values of deeper lookarounds. *)
    
  (** * NoPrio Tree Equivalence  *)

  Lemma two_app:
    forall A (a1 a2:A), [a1; a2] = [a1] ++ [a2].
  Proof. auto. Qed.

  Lemma three_app:
    forall A (a1 a2 a3:A), [a1; a2; a3] = [a1] ++ [a2] ++ [a3].
  Proof. auto. Qed.

  (* If we can find a leaf in the tree of the first list of actions,
   then a leaf in the tree of the second list,
   then that final leaf is a leaf of the tree of the concatenation *)
  Lemma in_leaves_app:
    forall dir inp0 gm0 inp1 gm1 inp2 gm2 a1 a2 t1 t2 t12
      (TREE12: is_tree rer (a1 ++ a2) inp0 gm0 dir t12)
      (TREE1: is_tree rer a1 inp0 gm0 dir t1)
      (TREE2: is_tree rer a2 inp1 gm1 dir t2)
      (IN1: In (inp1,gm1) (tree_leaves t1 gm0 inp0 dir))
      (IN2: In (inp2, gm2) (tree_leaves t2 gm1 inp1 dir)),
      In (inp2, gm2) (tree_leaves t12 gm0 inp0 dir).
  Proof.
    intros dir inp0 gm0 inp1 gm1 inp2 gm2 a1 a2 t1 t2 t12 TREE12 TREE1 TREE2 IN1 IN2.
    specialize (leaves_concat _ _ _ _ _ _ _ _ TREE12 TREE1) as FM.
    assert (ACT: act_from_leaf rer a2 dir (inp1, gm1) (tree_leaves t2 gm1 inp1 dir)).
    { constructor. simpl. auto. }
    specialize (FlatMap_in _ _ _ _ _ (act_from_leaf_determ _ _ _) FM IN1 ACT) as FM_IN.
    rewrite Forall_forall in FM_IN.
    apply FM_IN. auto.
  Qed.

  Lemma in_leaves_app3:
    forall dir inp0 gm0 inp1 gm1 inp2 gm2 inp3 gm3 a1 a2 a3 t1 t2 t3 t123
      (TREE123: is_tree rer (a1 ++ a2 ++ a3) inp0 gm0 dir t123)
      (TREE1: is_tree rer a1 inp0 gm0 dir t1)
      (TREE2: is_tree rer a2 inp1 gm1 dir t2)
      (TREE3: is_tree rer a3 inp2 gm2 dir t3)
      (IN1: In (inp1,gm1) (tree_leaves t1 gm0 inp0 dir))
      (IN2: In (inp2, gm2) (tree_leaves t2 gm1 inp1 dir))
      (IN3: In (inp3, gm3) (tree_leaves t3 gm2 inp2 dir)),
      In (inp3, gm3) (tree_leaves t123 gm0 inp0 dir).
  Proof.
    intros dir inp0 gm0 inp1 gm1 inp2 gm2 inp3 gm3 a1 a2 a3 t1 t2 t3 t123 TREE123 TREE1 TREE2 TREE3 IN1 IN2 IN3.
    specialize (is_tree_productivity rer (a2 ++ a3) inp1 gm1 dir) as [t23 TREE23].
    assert (IN23: In (inp3, gm3) (tree_leaves t23 gm1 inp1 dir)).
    { apply (in_leaves_app _ _ _ _ _ _ _ _ _ _ _ _ TREE23 TREE2 TREE3 IN2 IN3). }
    apply (in_leaves_app _ _ _ _ _ _ _ _ _ _ _ _ TREE123 TREE1 TREE23 IN1 IN23).
  Qed.

  (* all leaves obtained from noprio are leaves of the backtracking tree *)
  Theorem noprio_is_leaf:
    forall dir r inp gm t leafinp
      (TREE: is_tree rer [Areg r] inp gm dir t),
      noprio dir inp r leafinp -> 
      exists leafgm, In (leafinp, leafgm) (tree_leaves t gm inp dir).
  Proof.
    intros dir r inp gm t leafinp TREE NP. 
    generalize dependent t. generalize dependent gm.
    induction NP; intros.
    - inversion TREE; subst. inversion ISTREE; subst.
      simpl. eauto.
    - inversion TREE; subst;
        rewrite READ0 in READ; inversion READ; subst.
      inversion TREECONT; subst. simpl.
      apply read_char_success_advance in READ0.
      unfold advance_input'. rewrite READ0. eauto.
    - inversion TREE; subst. apply IHNP in ISTREE1 as [leafgm IH1].
      simpl. eexists. apply in_or_app. eauto.
    - inversion TREE; subst. apply IHNP in ISTREE2 as [leafgm IH2].
      simpl. eexists. apply in_or_app. eauto.
    - inversion TREE; subst.
      simpl in CONT. rewrite two_app in CONT.
      specialize (is_tree_productivity rer [Areg r1] inp0 gm forward) as [t1 HT1].
      apply IHNP1 in HT1 as H. destruct H as [gm1 IN1].
      specialize (is_tree_productivity rer [Areg r2] inp1 gm1 forward) as [t2 HT2].
      apply IHNP2 in HT2 as H. destruct H as [gm2 IN2].
      eexists. eapply in_leaves_app; eauto.
    - inversion TREE; subst.
      simpl in CONT. rewrite two_app in CONT.
      specialize (is_tree_productivity rer [Areg r2] inp0 gm backward) as [t2 HT2].
      apply IHNP1 in HT2 as H. destruct H as [gm2 IN2].
      specialize (is_tree_productivity rer [Areg r1] inp1 gm2 backward) as [t1 HT1].
      apply IHNP2 in HT1 as H. destruct H as [gm1 IN1].
      eexists. eapply in_leaves_app; eauto.
    - inversion TREE; subst.
      rewrite two_app in ISTREE1.
      specialize (is_tree_productivity rer [Areg r] inp0 (GroupMap.reset (def_groups r) gm) dir) as [t1 HT1].
      assert (IN1: exists gm1, In (inp1, gm1) (tree_leaves t1 (GroupMap.reset (def_groups r) gm) inp0 dir)).
      { apply IHNP1. auto. } destruct IN1 as [gm1 IN1].
      specialize (is_tree_productivity rer [Areg (Quantified greedy min delta r)] inp1 gm1 dir) as [t2 HT2].
      assert (IN2: exists gm2, In (inp2, gm2) (tree_leaves t2 gm1 inp1 dir)).
      { apply IHNP2. auto. } destruct IN2 as [gm2 IN2].
      eexists. eapply (in_leaves_app _ _ _ _ _ inp2 gm2 _ _ _ _ _ ISTREE1 HT1 HT2 IN1 IN2); eauto.
    - inversion TREE; subst.
      + inversion SKIP; subst. simpl. eauto.
      + destruct plus; inversion H1.
    - inversion TREE; subst.
      { destruct delta; inversion H1. }
      assert (DP: plus = delta).
      { destruct plus; destruct delta; auto; inversion H1; auto. }
      subst. clear H1. clear SKIP.
      specialize (is_tree_productivity rer [Areg r] inp0 (GroupMap.reset (def_groups r) gm) dir) as [t1 HT1].
      assert (IN1: exists gm1, In (inp1, gm1) (tree_leaves t1 (GroupMap.reset (def_groups r) gm) inp0 dir)).
      { apply IHNP1. auto. } destruct IN1 as [gm1 IN1].
      specialize (is_tree_productivity rer [Acheck inp0] inp1 gm1 dir) as [t2 HT2].
      assert (IN2: In (inp1, gm1) (tree_leaves t2 gm1 inp1 dir)).
      { inversion HT2; subst.
        - inversion TREECONT; subst. simpl. auto.
        - apply CHECKFAIL in PROGRESS. inversion PROGRESS. (* we know progress happened *)
      }
      specialize (is_tree_productivity rer [Areg (Quantified greedy 0 delta r)] inp1 gm1 dir) as [t3 HT3].      
      assert (IN3: exists gm2, In (inp2, gm2) (tree_leaves t3 gm1 inp1 dir)).
      { apply IHNP2. auto. } destruct IN3 as [gm2 IN3].
      rewrite three_app in ISTREE1.
      destruct greedy; simpl.
      + eexists. apply in_or_app. left.
        eapply (in_leaves_app3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ISTREE1 HT1 HT2 HT3 IN1 IN2 IN3). 
      + eexists. apply in_or_app. right.
        eapply (in_leaves_app3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ISTREE1 HT1 HT2 HT3 IN1 IN2 IN3). 
    - inversion TREE; subst.
      { destruct delta; inversion H1. }
      inversion SKIP. subst.
      destruct greedy; simpl; eauto.
      eexists. apply in_or_app; simpl; eauto.      
    - inversion TREE; subst.
      rewrite two_app in TREECONT.
      specialize (is_tree_productivity rer [Areg r] inp (GroupMap.open (idx inp) gid gm) dir) as [t1 HT1].
      assert (IN1: exists nextgm, In (nextinp, nextgm) (tree_leaves t1 (GroupMap.open (idx inp) gid gm) inp dir)).
      { apply IHNP. auto. } destruct IN1 as [nextgm IN1].
      specialize (is_tree_productivity rer [Aclose gid] nextinp nextgm dir) as [t2 HT2].
      assert (IN2: In (nextinp, GroupMap.close (idx nextinp) gid nextgm) (tree_leaves t2 nextgm nextinp dir)).
      { inversion HT2. subst. inversion TREECONT0. subst. simpl. auto. }
      eexists. eapply (in_leaves_app _ _ _ _ _ nextinp (GroupMap.close (idx nextinp) gid nextgm) _ _ _ _ _ TREECONT HT1 HT2 IN1 IN2); eauto.
    - inversion TREE; subst;
        rewrite ANCHOR0 in ANCHOR; inversion ANCHOR.
      inversion TREECONT; subst. simpl. eauto.
  Qed.

  (* Other direction: generalizing the noprio semantics to actions *)

  Inductive noprio_action: Direction -> input -> action -> input -> Prop :=
  | np_regex:
    forall dir inp r nextinp
      (NP: noprio dir inp r nextinp),
      noprio_action dir inp (Areg r) nextinp
  | np_close:
    forall dir inp gid,
      noprio_action dir inp (Aclose gid) inp
  | np_check:
    forall dir inp inpcheck
      (PROGRESS: strict_suffix inp inpcheck dir),
      noprio_action dir inp (Acheck inpcheck) inp.

  Inductive noprio_list: Direction -> input -> list action -> input -> Prop :=
  | np_nil:
    forall dir inp,
      noprio_list dir inp [] inp
  | np_cons:
    forall dir inp0 a inp1 l inp2
      (NP_A: noprio_action dir inp0 a inp1)
      (NP_L: noprio_list dir inp1 l inp2),
      noprio_list dir inp0 (a::l) inp2.

  Lemma is_tree_action_noprio:
    forall dir inp0 gm0 l t inp1 gm1
      (SUBSET: pike_actions l)
      (TREE: is_tree rer l inp0 gm0 dir t)
      (LEAF: In (inp1, gm1) (tree_leaves t gm0 inp0 dir)),
      noprio_list dir inp0 l inp1.
  Proof.
    intros dir inp0 gm0 l t inp1 gm1 SUBSET TREE LEAF.
    induction TREE; simpl in LEAF; subst;
      try solve [inversion LEAF]; pike_subset.
    - destruct LEAF as [LEAF|LEAF]; inversion LEAF; subst. constructor.
    - repeat (econstructor; eauto).
    - repeat (econstructor; eauto). 
    - repeat (econstructor; eauto).
    - econstructor; eauto.
      2: { apply read_char_success_advance in READ as ADV.
           unfold advance_input' in LEAF. rewrite ADV in LEAF. eauto. }
      repeat (econstructor; eauto). 
    - apply in_app_or in LEAF as [LEAF|LEAF].
      + assert (noprio_list dir inp (Areg r1::cont) inp1).
        { apply IHTREE1; auto. pike_subset. }
        inversion H; subst. inversion NP_A. repeat (econstructor; eauto).
      + assert (noprio_list dir inp (Areg r2::cont) inp1).
        { apply IHTREE2; auto. pike_subset. }
        inversion H; subst. inversion NP_A. solve[repeat (econstructor; eauto)].
    - destruct dir.
      + simpl in IHTREE.
        assert (noprio_list forward inp (Areg r1 :: Areg r2 :: cont) inp1).
        { apply IHTREE; auto. pike_subset. }
        inversion H; inversion NP_L; inversion NP_A; inversion NP_A0; subst.
        repeat (econstructor; eauto).
      + simpl in IHTREE.
        assert (noprio_list backward inp (Areg r2 :: Areg r1 :: cont) inp1).
        { apply IHTREE; auto. pike_subset. }
        inversion H; inversion NP_L; inversion NP_A; inversion NP_A0; subst.
        repeat (econstructor; eauto).
    - specialize (IHTREE H2 LEAF).
      repeat econstructor; eauto.
    - destruct plus; inversion H3; subst.
      specialize (IHTREE2 H2).
      assert (In (inp1,gm1) (tree_leaves titer (GroupMap.reset (def_groups r1) gm) inp dir) \/
                In (inp1,gm1) (tree_leaves tskip gm inp dir)) as [LEAFSKIP|LEAFITER].
      { destruct greedy; simpl in LEAF; apply in_app_or in LEAF; auto.
        destruct LEAF; auto. }
      (* skip *)
      2: { econstructor; eauto. econstructor; eauto. apply np_quant_skip. }
      (* iter *)
      assert (noprio_list dir inp (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 +∞ r1) :: cont) inp1).
      { apply IHTREE1; auto. pike_subset. }
      inversion H; inversion NP_L; inversion NP_A; inversion NP_A0; inversion NP_L0; inversion NP_A1; subst.
      repeat (econstructor; eauto).
    - destruct plus; inversion H3. subst.
      specialize (IHTREE2 H2).
      assert (In (inp1,gm1) (tree_leaves titer (GroupMap.reset (def_groups r1) gm) inp dir) \/
                In (inp1,gm1) (tree_leaves tskip gm inp dir)) as [LEAFSKIP|LEAFITER].
      { destruct greedy; simpl in LEAF; apply in_app_or in LEAF; auto.
        destruct LEAF; auto. }
      (* skip *)
      2: { econstructor; eauto. econstructor; eauto. apply np_quant_skip. }
      (* iter *)
      assert (noprio_list dir inp (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp1).
      { apply IHTREE1; auto. pike_subset. }
      inversion H; inversion NP_L; inversion NP_A; inversion NP_A0; inversion NP_L0; inversion NP_A1; subst.
      repeat (econstructor; eauto).
    - destruct plus; inversion H3.
    - assert (noprio_list dir inp (Areg r1 :: Aclose gid :: cont) inp1).
      { apply IHTREE; auto. pike_subset. }
      inversion H; inversion NP_A; inversion NP_L; inversion NP_A0; subst.
      repeat (econstructor; eauto).
    - specialize (IHTREE H2 LEAF).
      repeat (econstructor; eauto).
  Qed.

  (* For the Pike Subset, the NoPrio Semantics exactly coincides with leaves of the Tree Semantics *)
  Theorem noprio_eq_is_leaf:
    forall dir r inp gm t leafinp
      (SUBSET: pike_regex r)
      (TREE: is_tree rer [Areg r] inp gm dir t),
      noprio dir inp r leafinp <-> 
        exists leafgm, In (leafinp, leafgm) (tree_leaves t gm inp dir).
  Proof.
    intros dir r inp gm t leafinp SUBSET TREE. split.
    - apply noprio_is_leaf. auto.
    - intros [leafgm H]. eapply is_tree_action_noprio in TREE; eauto.
      2: pike_subset.
      inversion TREE; inversion NP_A; inversion NP_L; subst. auto.
  Qed.

  (** * Reversal Property  *)

  Definition reverse (d:Direction): Direction :=
    match d with
    | forward => backward
    | backward => forward
    end.

  Lemma read_char_reverse:
    forall cd inp dir c nextinp,
      read_char rer cd inp dir = Some (c, nextinp) ->
      read_char rer cd nextinp (reverse dir) = Some (c, inp).
  Proof.
    intros cd [next1 pref1] dir c [next2 pref2] H.
    destruct dir; simpl; simpl in H.
    - destruct next1; inversion H.
      destruct (char_match) eqn:CM; inversion H. subst.
      rewrite CM. auto.
    - destruct pref1; inversion H.
      destruct (char_match) eqn:CM; inversion H. subst.
      rewrite CM. auto.
  Qed.
  
  Theorem noprio_reversal:
    forall dir r inp1 inp2
      (NP1: noprio dir inp1 r inp2),
      noprio (reverse dir) inp2 r inp1.
  Proof.
    intros dir r inp1 inp2 NP1.
    induction NP1; intros.
    - repeat (econstructor; eauto).
    - apply read_char_reverse in READ as REV.
      destruct dir; simpl; econstructor; eauto.
    - repeat (econstructor; eauto). 
    - solve[repeat (econstructor; eauto)].
    - repeat (econstructor; eauto).
    - repeat (econstructor; eauto).
    - admit.
    (* does not work: in one direction we do r and then r{min}
       in the other we also do r and then r{min}, but we would like them switched to apply IH.
       One solution would be to prove that for noprio, r.r{} is equivalent to r{}.r *)
    - repeat (econstructor; eauto).
    - admit.
    - eapply np_quant_skip.
    - repeat (econstructor; eauto).
    - repeat (econstructor; eauto).
  Admitted.
  
End NoPrioSemantics.
