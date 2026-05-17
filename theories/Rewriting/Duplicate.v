From Linden.Rewriting Require Import ProofSetup.

(** * Simplifying Duplicate Regexes  *)
(* This showcases why we want to remove duplicate in leaves equivalence:
    even though (r|r) clearly has more leaves than r, these are still equivalent *)


Section Duplicate.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Lemma cons_monotony:
    forall a seen,
    forall x, is_seen x seen = true -> is_seen x (a::seen) = true.
  Proof.
    intros a seen x H. simpl. apply Bool.orb_true_iff. right. auto.
  Qed.

  Lemma equiv_nil_seen:
    forall seen, leaves_equiv seen [] (rev seen).
  Proof.
    intros seen. induction seen; try constructor. simpl.
    pose proof (leaves_equiv_app2 (a::seen) [] (rev seen) [] [a]). apply H.
    - eapply leaves_equiv_monotony with (seen1:= seen); auto.
      apply cons_monotony.
    - simpl. destruct a. constructor; simpl; try reflexivity.
      apply Bool.orb_true_iff. left. apply andb_true_intro. split; auto.
      apply input_eqb_true. auto. apply gm_eqb_true. auto.
  Qed.


  Lemma leaves_equiv_double:
    forall l seen, leaves_equiv seen l (l ++ (rev seen ++ l)).
  Proof.
    intros l seen. generalize dependent seen.
    induction l; intros.
    { simpl. rewrite app_nil_r. apply equiv_nil_seen. }
    simpl. destruct a as [inp gm].
    specialize (IHl ((inp,gm)::seen)). simpl in IHl. rewrite <- app_assoc in IHl. simpl in IHl.
    destruct (is_seen (inp, gm) seen) eqn:SEEN; try solve [constructor; auto].
    apply equiv_seen_right; auto. apply equiv_seen_left; auto.        
    eapply leaves_equiv_monotony with (seen1:=(inp,gm)::seen); eauto.
    intros [i2 g2] H. simpl in H. apply Bool.orb_true_iff in H as [H|H]; auto.
    apply andb_prop in H as [H1 H2].
    apply input_eqb_true in H1. apply gm_eqb_true in H2. subst. auto.
  Qed.


  Theorem duplicate_elim:
    forall r, def_groups r = [] ->
          Disjunction r r ≅[rer] r.
  Proof.
    unfold tree_equiv, tree_equiv_dir, actions_equiv_dir, tree_equiv_tr_dir. intros r NOG. split; intros.
    { simpl. rewrite NOG. auto. }
    inversion TREE1; subst. eapply is_tree_determ in ISTREE1; eauto. subst.
    eapply is_tree_determ in TREE2; eauto. subst. simpl.
    specialize (leaves_equiv_double (tree_leaves t2 gm inp dir) []). simpl. intros.
    apply leaves_equiv_rel_Symmetric. auto.
  Qed.

End Duplicate.
