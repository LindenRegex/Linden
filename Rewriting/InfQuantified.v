From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import Examples FlatMap.

Section InfQuantified.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).
  
  (** * INDUCTION ON STRING LENGTH: *)
  (* The next section presents some helper lemmas for induction on the input
     length string.
     They are useful to easily advance on the input on certain regexes or
     proving failure of certain regexes in the case of a null input *)

  (* If the remaining length is 0, and we have a regex followed by a check,
   then the corresponding tree has no leaves*)
  Lemma null_length_check_fails:
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

  (* If the remaining length is 0, and we have a tree which represents a quantified
     followed by some other action, then the leaves of the corresponding tree are the
     same than the leaves of the tree of the action *)
  Lemma quantified_null_length_skip:
    forall i d g dir acts r t1 t2 greedy,
      remaining_length i dir <= 0 ->
      is_tree rer ([Areg (Quantified greedy 0 d r)] ++ acts) i g dir t1 ->
      is_tree rer acts i g dir t2 ->
      tree_leaves t1 g i dir = tree_leaves t2 g i dir.
  Proof.
    intros i d g dir acts r t1 t2  greedy l T1 T2.
    inversion T1; subst. eapply is_tree_determ with (t1 := t1) (t2 := t2) in SKIP; eauto.
    subst; reflexivity.
    specialize (null_length_check_fails _ _ _ _ _ _ l ISTREE1) as nlf.
    pose proof (is_tree_determ _ _ _ _ _ _ _  T2 SKIP). subst.
    destruct greedy; simpl; rewrite nlf; try rewrite app_nil_r; auto.
  Qed.

   (* A more specific case of the lemma above where there are no actions made
     after the quantified *)
  Lemma quantified_null_length:
    forall i d g dir r t1 greedy,
      remaining_length i dir <= 0 ->
      is_tree rer ([Areg (Quantified greedy 0 d r)]) i g dir t1 ->
      tree_leaves t1 g i dir = [(i, g)].
  Proof.
    intros.
    pose proof (is_tree_productivity rer [] i g dir) as [t2 T2].
    pose proof (quantified_null_length_skip _ _ _ _ _ _ _  _ _ H H0 T2).
    inversion T2; subst. rewrite H1; reflexivity.
  Qed.

  (* If the remaining length is 0, and we have a tree which represents a regex
     followed by a quantified followed by some other action, then the leaves of
     the tree are the same than the leaves of the tree of the regex followed by the actions *)
  Lemma quantified_null_length_head_skip:
    forall i d g dir r t1 t2 greedy acts,
      remaining_length i dir <= 0 ->
      is_tree rer ([Areg r; Areg (Quantified greedy 0 d r)] ++ acts) i g dir t1 ->
      is_tree rer ([Areg r] ++ acts) i g dir t2 ->
      leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t2 g i dir).
  Proof.
    intros.
    (* Preparing the transformation in FlatMap of the two trees *)
    pose proof (is_tree_productivity rer [Areg r] i g dir) as [t3 T3].
    rewrite app_cons in H0. eapply leaves_concat with (act1 := [Areg r]) in H0, H1; eauto.
    assert (forall i0 g0, In (i0, g0) (tree_leaves t3 g i dir) -> i = i0 \/ StrictSuffix.strict_suffix i0 i dir). intros. eapply input_only_forward; eauto.
    remember (tree_leaves t3 g i dir) as l.
    remember (tree_leaves t2 g i dir) as l3.
    remember (tree_leaves t1 g i dir) as l1. clear Heql1 Heql Heql3.
    generalize dependent t1. generalize dependent t3.
    revert l3 H1 l1 H0.
    induction l; intros.
    - (* BASE CASE: no outputs out of [Areg r] *)
      inversion H0; inversion H1; eauto. reflexivity.
    - (*INDUCTIVE CASE: new output out of [Areg r] knowing the previous follow the properyty *)
      inversion H1; inversion H0; inversion HEAD; inversion HEAD0; subst.
      clear HEAD HEAD0. destruct a; simpl in *. apply leaves_equiv_app.
      + (* Since the length is equal to 0, the quantified will always be skipped *)
        eapply quantified_null_length_skip with (acts := acts)in TREE0; eauto.
        rewrite TREE0. reflexivity.
        assert (i = i0 \/ StrictSuffix.strict_suffix i0 i dir).
        eapply H2; intros; eauto. destruct H3; subst. lia.
        apply strict_suffix_remaining_length in H3; lia.
      + (* The leaves which already follow the property *)
        eapply IHl; eauto.
  Qed.

  (* Specific instance of the case above where there are no acts after the quantified,
     the tree just becomes equal to the tree of the prefix *)
  Lemma quantified_null_length_head:
    forall i d g dir r t1 t2  greedy,
      remaining_length i dir <= 0 ->
      is_tree rer [Areg r; Areg (Quantified greedy 0 d r)] i g dir t1 ->
      is_tree rer [Areg r] i g dir t2 ->
      leaves_equiv [] (tree_leaves t1 g i dir) (tree_leaves t2 g i dir).
  Proof.
    intros. eapply quantified_null_length_head_skip with (acts := []); eauto.
    rewrite app_nil_r; eauto.
  Qed.

  (* If for a length n two trees represent a regex r followed by a check followed
     by two different acts, then if the two acts are equal for all length < n,
     the two trees are equal at length = n *)
  Lemma step_advances_eqs:
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
    rewrite app_cons in T1, T2.
    eapply leaves_concat with (act1 := [Areg r]) in T1, T2; eauto.
    remember (tree_leaves t3 g i dir) as l2.
    induction l2. inversion T2; inversion T1; subst. reflexivity.
    eapply flatmap_leaves_equiv_r; eauto. unfold equiv_leaffuncts. intros.
    inversion H; inversion H0; subst.
    inversion TREE; inversion TREE0; subst; try contradiction. destruct a; simpl in *.
    2: reflexivity.
    eapply IH; eauto. eapply strict_suffix_remaining_length; eauto.
  Qed.

  (* If two trees represent the same series of actions followed by a different
     series of actions, then if the two series of actions are equal the two trees are
     also equal *)
  Lemma quantified_inf_step_skip:
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
End InfQuantified.
