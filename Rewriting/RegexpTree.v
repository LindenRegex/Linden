From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import Examples FlatMap ForcedQuant Associativity Distributivity.

Coercion nat_to_N (n: nat) := NoI.N n.

(*|
# Regexp-tree
|*)

Section RegexpTree.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (*|
## Bounded repetitions
|*)

  Section BoundedRepetitions.
    Lemma bounded_util_fwd m n delta r:
      def_groups r = [] -> (* r{m}r{n,n+k} ≅[forward] r{m+n,m+n+k}, generalized from regexp_tree *)
      (Sequence (Quantified true m 0 r) (Quantified true n delta r))
        ≅[rer][forward] Quantified true (m + n) delta r.
    Proof.
      induction m as [ | m' IHm ]; simpl; intros.
      - etransitivity.
        apply seq_equiv.
        apply quantified_zero_equiv.
        auto.
        reflexivity.
        etransitivity.
        apply sequence_epsilon_left_equiv.
        reflexivity.
      - etransitivity.
        { apply seq_equiv_dir.
          apply quantified_S_equiv_forward.
          auto.
          reflexivity. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_forward.
          auto. }
        etransitivity.
        { symmetry.
          eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        reflexivity.
        auto.
    Qed.

    Lemma bounded_util_bwd m n delta r:
      def_groups r = [] -> (* r{n,n+k}r{m} ≅[backward] r{m+n,m+n+k}, generalized from regexp_tree *)
      (Sequence (Quantified true n delta r) (Quantified true m 0 r))
        ≅[rer][backward] Quantified true (m + n) delta r.
    Proof.
      induction m as [ | m' IHm ]; simpl; intros.
      - etransitivity.
        apply seq_equiv_dir.
        reflexivity.
        apply quantified_zero_equiv.
        auto.
        etransitivity.
        apply sequence_epsilon_right_equiv.
        reflexivity.
      - etransitivity.
        { apply seq_equiv_dir.
          reflexivity.
          apply quantified_S_equiv_backward.
          auto. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_backward.
          auto. }
        etransitivity.
        { eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        auto.
        reflexivity.
    Qed.

    Lemma bounded_bounded_equiv_true m n r: (* r{m}r{n} ≅ r{m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true n 0 r))
        ≅[rer] Quantified true (m + n) 0 r.
    Proof.
      intros H [].
      - apply bounded_util_fwd. auto.
      - rewrite PeanoNat.Nat.add_comm. apply bounded_util_bwd. auto.
    Qed.

    Corollary bounded_bounded_equiv p m n r: (* r{m}r{n} ≅ r{m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified p m 0 r) (Quantified p n 0 r))
        ≅[rer] Quantified p (m + n) 0 r.
    Proof.
      pose proof bounded_bounded_equiv_true m n r. destruct p; intros; auto.
      etransitivity. 2: apply forced_equiv.
      etransitivity; auto.
      apply seq_equiv; symmetry; apply forced_equiv.
    Qed.

    Lemma bounded_atmost_equiv_true m n r: (* r{m}r{0,n} ≅[forward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true 0 n r))
        ≅[rer][forward] Quantified true m n r.
    Proof. intro NO_GROUPS. rewrite bounded_util_fwd, PeanoNat.Nat.add_0_r. 1: reflexivity. auto. Qed.

    Corollary bounded_atmost_equiv p m n r: (* r{m}r{0,n} ≅[forward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified p m 0 r) (Quantified true 0 n r))
        ≅[rer][forward] Quantified true m n r.
    Proof.
      pose proof bounded_atmost_equiv_true m n r. destruct p; intros; auto.
      etransitivity; auto.
      apply seq_equiv. symmetry. apply forced_equiv. reflexivity.
    Qed.

    Lemma atmost_bounded_equiv_true m n r: (* r{0,n}r{m} ≅[backward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true 0 n r) (Quantified true m 0 r))
        ≅[rer][backward] Quantified true m n r.
    Proof. intro NO_GROUPS. rewrite bounded_util_bwd, PeanoNat.Nat.add_0_r. 1: reflexivity. auto. Qed.

    Corollary atmost_bounded_equiv p m n r: (* r{0,n}r{m} ≅[backward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true 0 n r) (Quantified p m 0 r))
        ≅[rer][backward] Quantified true m n r.
    Proof.
      pose proof atmost_bounded_equiv_true m n r. destruct p; intros; auto.
      etransitivity; auto. apply seq_equiv. reflexivity. symmetry. apply forced_equiv.
    Qed.

    Lemma bounded_atmost_lazy_equiv_true m n r: (* r{m}r{0,n}? ≅[forward] r{m,m+n}? *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified false 0 n r))
        ≅[rer][forward] Quantified false m n r.
    Proof.
      intro NO_GROUPS.
      induction m as [|m IHm]; simpl.
      - etransitivity.
        apply seq_equiv_dir.
        apply quantified_zero_equiv.
        auto.
        reflexivity.
        apply sequence_epsilon_left_equiv.
      - etransitivity.
        { apply seq_equiv_dir.
          apply quantified_S_equiv_forward.
          auto.
          reflexivity. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_forward.
          auto. }
        etransitivity.
        { symmetry.
          eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        apply forced_equiv.
        auto.
    Qed.

    Corollary bounded_atmost_lazy_equiv p m n r: (* r{m}r{0,n}? ≅[forward] r{m,m+n}? *)
      def_groups r = [] ->
      (Sequence (Quantified p m 0 r) (Quantified false 0 n r))
        ≅[rer][forward] Quantified false m n r.
    Proof.
      pose proof bounded_atmost_lazy_equiv_true m n r. destruct p; intros; auto.
      etransitivity; auto. apply seq_equiv. symmetry. apply forced_equiv. reflexivity.
    Qed.

    Lemma atmost_bounded_lazy_equiv_true m n r: (* r{0,n}?r{m} ≅[backward] r{m,m+n}? *)
      def_groups r = [] ->
      (Sequence (Quantified false 0 n r) (Quantified true m 0 r))
        ≅[rer][backward] Quantified false m n r.
    Proof.
      intro NO_GROUPS.
      induction m as [|m IHm]; simpl.
      - etransitivity.
        apply seq_equiv_dir.
        reflexivity.
        apply quantified_zero_equiv.
        auto.
        apply sequence_epsilon_right_equiv.
      - etransitivity.
        { apply seq_equiv_dir.
          reflexivity.
          apply quantified_S_equiv_backward.
          auto. }
        etransitivity; cycle 1.
        { symmetry.
          eapply quantified_S_equiv_backward.
          auto. }
        etransitivity.
        { eapply sequence_assoc_equiv. }
        eapply seq_equiv_dir.
        auto.
        apply forced_equiv.
    Qed.

    Corollary atmost_bounded_lazy_equiv p m n r: (* r{0,n}?r{m} ≅[backward] r{m,m+n}? *)
      def_groups r = [] ->
      (Sequence (Quantified false 0 n r) (Quantified p m 0 r))
        ≅[rer][backward] Quantified false m n r.
    Proof.
      pose proof atmost_bounded_lazy_equiv_true m n r. destruct p; intros; auto.
      etransitivity; auto. apply seq_equiv. reflexivity. symmetry. apply forced_equiv.
    Qed.

    Lemma bounded_atmost_forward:
      forall r n m g,
        def_groups r = [] ->
        (Sequence (Quantified g m 0 r) (Quantified g 0 n r))
          ≅[rer][forward] Quantified g m n r.
    Proof.
      intros r n m g DEF. destruct g.
      - apply bounded_atmost_equiv. auto.
      - etransitivity.
        { eapply seq_equiv. 2: reflexivity.
          rewrite <- forced_equiv. reflexivity. }
        apply bounded_atmost_lazy_equiv. auto.
    Qed.


    Lemma atmost_bounded_backward:
      forall r n m g,
        def_groups r = [] ->
        (Sequence (Quantified g 0 n r) (Quantified g m 0 r))
          ≅[rer][backward] Quantified g m n r.
    Proof.
      intros r n m g DEF. destruct g.
      - apply atmost_bounded_equiv. auto.
      - etransitivity.
        { eapply seq_equiv. reflexivity.
          rewrite <- forced_equiv. reflexivity. }
        apply atmost_bounded_lazy_equiv. auto.
    Qed.



    Context (c0 c1 c2: Parameters.Character).

    Hypothesis H01: Character.canonicalize rer c0 <> Character.canonicalize rer c1.
    Hypothesis H02: Character.canonicalize rer c0 <> Character.canonicalize rer c2.
    Hypothesis H12: Character.canonicalize rer c1 <> Character.canonicalize rer c2.

    Lemma atmost_bounded_nequiv: (* r{0,m}r{n} ≅ r{n,n+m} *)
      exists m n r,
        (Sequence (Quantified true 0 m r) (Quantified true n 0 r))
          ≇[rer] Quantified true n m r.
    Proof.
      exists 1, 1, (Disjunction c0 (Sequence c0 c1)).
      tree_equiv_rw.
      exists forward, (init_input [c0; c1; c0]), GroupMap.empty.
      compute_tr_cbv.
      inversion 1.
    Qed.


    (** * Proving r{0,m}r{0,n} ≅ r{0,m+n} *)
    (* We reason by induction on either m (if m is finite) or the remaining length
    of the input to match (if m is infinite). *)
    (* In the inductive case, the trees of r{0,m+1}r{0,n} and r{0,m+1+n} have
    the following form: *)
    (*
            r{0,m+1}r{0,n}                             r{0,m+1+n}
                Choice                                   Choice
               /       \                                /      \
              /          \                             /        \
        r{0,m}r{0,n}     r{0,n}                  r{0,m+n}      Match
                         Choice
                        /       \
                      /          \
                r{0,n-1}        Match
     *)
    (* By induction hypothesis, the leaves of the subtrees r{0,m}r{0,n}
    and r{0,m+n} are equivalent. *)
    (* On the left, however, we have an extra branch, r{0,n-1}. We then argue
    that since n-1 < m+n, the leaves of that branch are included in the
    leaves of the branch r{0,m+n}, and hence are duplicates of the leaves of
    r{0,m+n}, so the equivalence holds. *)

    (* Inclusion of lists (viewed as sets) *)
    Definition incl {A} (a b: list A) :=
      forall x, In x a -> In x b.

    (* Function inclusion with propositional functions: when for all a, f1(a) ⊆ f2(a). *)
    (* We will use this notion with f1 := act_from_leaf [r{0,n-1}] and
    f2 := act_from_leaf [r{0,m+n}]. *)
    Definition funct_incl {A B} (f1 f2: A -> list B -> Prop) :=
      forall a l1 l2, f1 a l1 -> f2 a l2 -> incl l1 l2.

    Lemma flatmap_incl {A B}:
      forall (leaves: list A) (f1 f2: A -> list B -> Prop) leaves1 leaves2,
        FlatMap leaves f1 leaves1 ->
        FlatMap leaves f2 leaves2 ->
        funct_incl f1 f2 ->
        incl leaves1 leaves2.
    Proof.
      intros leaves f1 f2 leaves1 leaves2 FM1 FM2 INCL.
      generalize dependent leaves2.
      induction FM1.
      - intros _ _ _ [].
      - specialize (IHFM1 INCL). intros leaves2 FM2 lf Hin.
        inversion FM2; subst.
        specialize (INCL _ _ _ HEAD HEAD0).
        apply in_app_or in Hin. destruct Hin.
        + apply in_or_app. left. auto.
        + apply in_or_app. right. unfold incl in IHFM1. auto.
    Qed.

    (* The inclusion lemma: for all m and d, the leaves of r{0,m} are
    included in those of r{0,m+d}. *)
    Lemma atmost_leaves_incl' (m: nat) (d: non_neg_integer_or_inf) (g: bool)r:
      forall inp gm dir tm tn,
        is_tree rer [Areg (Quantified g 0 m r)] inp gm dir tm ->
        is_tree rer [Areg (Quantified g 0 (m+d)%NoI r)] inp gm dir tn ->
        incl (tree_leaves tm gm inp dir) (tree_leaves tn gm inp dir).
    Proof.
      induction m as [|m IHm].
      - intros inp gm dir tm tn TREE_m TREE_n.
        inversion TREE_m; subst. 2: { destruct plus; discriminate. }
                               inversion SKIP; subst.
        inversion TREE_n; subst.
        + inversion SKIP0; subst. unfold incl. auto.
        + inversion SKIP0; subst. simpl.
          intros lf H. destruct H; try solve[inversion H]. subst lf.
          destruct g; simpl. apply in_or_app; right; left; reflexivity.
          left. constructor.
      - intros inp gm dir tm tn TREE_m TREE_n.
        inversion TREE_m; subst.
        inversion TREE_n; subst. 1: { destruct d; discriminate. } clear TREE_m TREE_n.
        assert (plus = m). { destruct plus; try discriminate. injection H1 as ->. reflexivity. }
        assert (plus0 = (m + d)%NoI). { destruct plus0; destruct d; try discriminate. - injection H2 as ->. reflexivity. - reflexivity. }
        subst plus plus0. clear H1 H2.
        inversion SKIP; subst. inversion SKIP0; subst.
        simpl.
        assert (TREErcheck: exists trcheck, is_tree rer [Areg r; Acheck inp] inp (GroupMap.reset (def_groups r) gm) dir trcheck). {
          eexists. eapply compute_tr_is_tree.
        }
        destruct TREErcheck as [trcheck TREErcheck].
        pose proof leaves_concat rer _ _ _ [Areg r; Acheck inp] _ _ _ ISTREE1 TREErcheck as CONCAT.
        pose proof leaves_concat rer _ _ _ [Areg r; Acheck inp] _ _ _ ISTREE0 TREErcheck as CONCAT0.
        intros lf Hin.
        destruct g; simpl in *. apply in_app_or in Hin. destruct Hin.
        + apply in_or_app. left. eapply (flatmap_incl _ _ _ _ _ CONCAT CONCAT0); eauto.
          unfold funct_incl. intros a l1 l2 ACT1 ACT2.
          inversion ACT1; subst. inversion ACT2; subst. apply IHm; auto.
        + apply in_or_app. auto.
        + destruct Hin. left; assumption.
          right. eapply (flatmap_incl _ _ _ _ _ CONCAT CONCAT0); eauto.
          unfold funct_incl. intros a l1 l2 ACT1 ACT2. inversion ACT1; subst.
          inversion ACT2; subst. apply IHm; auto.
    Qed.



    (* Specialization to d = n-m *)
    Corollary atmost_leaves_incl_nat (m n: nat) (g: bool) r:
      m <= n ->
      forall inp gm dir tm tn,
        is_tree rer [Areg (Quantified g 0 m r)] inp gm dir tm ->
        is_tree rer [Areg (Quantified g 0 n r)] inp gm dir tn ->
        incl (tree_leaves tm gm inp dir) (tree_leaves tn gm inp dir).
    Proof.
      intros. apply atmost_leaves_incl' with (m := m) (d := n-m) (r := r) (tm := tm) (g := g); auto.
      simpl. replace (m + (n - m)) with n by lia. auto.
    Qed.

    (* Specialization to d = +∞ *)
    Corollary atmost_leaves_incl_infty (m: nat) (g: bool) r:
      forall inp gm dir tm tn,
        is_tree rer [Areg (Quantified g 0 m r)] inp gm dir tm ->
        is_tree rer [Areg (Quantified g 0 +∞ r)] inp gm dir tn ->
        incl (tree_leaves tm gm inp dir) (tree_leaves tn gm inp dir).
    Proof.
      intros. apply atmost_leaves_incl' with (m := m) (d := +∞) (r := r) (tm := tm) (g := g); auto.
    Qed.

    Lemma leaves_equiv_incl':
      forall a b c: list leaf,
        leaves_equiv [] a b ->
        incl c b ->
        leaves_equiv [] (a ++ c) b.
    Proof.
      intros. symmetry. rewrite <- app_nil_r with (l := b).
      apply leaves_equiv_app2.
      - now symmetry.
      - rewrite app_nil_r. induction c.
        + reflexivity.
        + destruct a0 as [inp gm]. apply equiv_seen_right.
          * apply is_seen_spec. unfold incl in H0. apply H0. left. reflexivity.
          * apply IHc. intros x Hin. apply H0. right. auto.
    Qed.

    Lemma leaves_equiv_incl:
      forall a b c d e: list leaf,
        leaves_equiv [] a b -> leaves_equiv [] d e ->
        incl c b ->
        leaves_equiv [] (a ++ c ++ d) (b ++ e).
    Proof.
      intros. rewrite app_assoc.
      apply leaves_equiv_app; auto. apply leaves_equiv_incl'; auto.
    Qed.

    Lemma atmost_atmost_equiv_actions_mnat (m: nat) (n: non_neg_integer_or_inf) r:
      forall dir, actions_equiv_dir rer dir [Areg (Quantified true 0 m r); Areg (Quantified true 0 n r)]
                    [Areg (Quantified true 0 (NoI.add m n) r)].
    Proof.
      induction m as [|m IHm].
      - simpl. replace (match n with | NoI.N r' => NoI.N r' | +∞ => +∞ end) with n by now destruct n.
        unfold actions_equiv_dir. intros dir inp gm t1 t2 TREE1 TREE2.
        inversion TREE1; subst. 2: { destruct plus; discriminate. }
                              replace t2 with t1 by eauto using is_tree_determ. reflexivity.
      - intros dir i gm tr1 tr2 TREE1 TREE2.
        inversion TREE1; subst. inversion TREE2; subst. 1: destruct n; discriminate. inversion SKIP0; subst.
        simpl. clear TREE1 TREE2 SKIP0.
        assert (plus0 = (m + n)%NoI). { destruct plus0; destruct n; try discriminate. - injection H2 as ->. simpl. reflexivity. - reflexivity. }
        assert (plus = m). { destruct plus; try discriminate. injection H1 as ->. reflexivity. }
        subst plus plus0. clear H1 H2.
        inversion SKIP; subst; simpl.
        + inversion SKIP0; subst. unfold tree_equiv_tr_dir. simpl. apply leaves_equiv_app. 2: reflexivity.
          clear SKIP SKIP0.
          remember i as i' in ISTREE1 at 1, ISTREE0 at 1. clear Heqi'.
          remember (GroupMap.reset (def_groups r) gm) as gm'. clear gm Heqgm'.
          revert i gm' titer titer0 ISTREE1 ISTREE0.
          apply app_eq_left with (acts := [Areg r; Acheck i']).
          auto.
        + inversion SKIP0; subst. simpl.
          clear SKIP SKIP0.
          change (match plus with
                  | NoI.N r' => NoI.N (S r')
                  | +∞ => +∞
                  end) with (1 + plus)%NoI in *. rename plus into n.
          assert (INCL: incl (tree_leaves titer1 (GroupMap.reset (def_groups r) gm) i
                                dir) (tree_leaves titer0 (GroupMap.reset (def_groups r) gm) i
                                        dir)). {
            assert (TREErcheck: exists trcheck, is_tree rer [Areg r; Acheck i] i (GroupMap.reset (def_groups r) gm) dir trcheck)
              by (eexists; eapply compute_tr_is_tree).
            destruct TREErcheck as [trcheck TREErcheck].
            pose proof leaves_concat rer _ _ _ [Areg r; Acheck i] [Areg (Quantified true 0 n r)] _ _ ISTREE2 TREErcheck as CONCAT2.
            pose proof leaves_concat rer _ _ _ [Areg r; Acheck i] [Areg (Quantified true 0 (m + (1 + n))%NoI r)] _ _ ISTREE0 TREErcheck as CONCAT0.
            eapply (flatmap_incl _ _ _ _ _ CONCAT2 CONCAT0); eauto.
            unfold funct_incl. intros a l1 l2 ACT1 ACT2.
            inversion ACT1; subst. inversion ACT2; subst.
            destruct n as [n|].
            - simpl in TREE0. apply atmost_leaves_incl_nat with (m := n) (n := m + S n) (r := r) (g := true); eauto. lia.
            - simpl in TREE0. replace t0 with t by eauto using is_tree_determ. unfold incl. auto.
          }
          assert (EQUIV: leaves_equiv [] (tree_leaves titer (GroupMap.reset (def_groups r) gm) i
                                            dir) (tree_leaves titer0 (GroupMap.reset (def_groups r) gm) i dir)). {
            clear INCL ISTREE2 titer1.
            remember (GroupMap.reset (def_groups r) gm) as gm'. clear gm Heqgm'.
            remember i as i' in ISTREE1 at 1, ISTREE0 at 1. clear Heqi'.
            revert i gm' titer titer0 ISTREE1 ISTREE0.
            apply app_eq_left with (acts := [Areg r; Acheck i']). auto.
          }
          apply leaves_equiv_incl; auto. reflexivity.
    Qed.

    Lemma atmost_atmost_equiv_actions_minf (n: non_neg_integer_or_inf) r:
      forall dir, actions_equiv_dir rer dir [Areg (Quantified true 0 +∞ r); Areg (Quantified true 0 n r)]
                    [Areg (Quantified true 0 +∞ r)].
    Proof.
      unfold actions_equiv_dir.
      intros dir inp.
      remember (remaining_length inp dir) as l.
      assert (Hlength_le: remaining_length inp dir <= l) by lia. clear Heql.
      generalize dependent inp.
      induction l as [|l IHl].
      - (* At end of input; iterating the regex can never succeed because the subsequent
        check will always fail *)
        intros inp Hend gm t1 t2 TREE1 TREE2.
        inversion TREE1; subst. inversion TREE2; subst.
        inversion SKIP0; subst. unfold tree_equiv_tr_dir. simpl.
        assert (NO_LEAVES: actions_no_leaves rer [Areg r; Acheck inp; Areg (Quantified true 0 plus r);
                                                  Areg (Quantified true 0 n r)] dir). {
          apply actions_no_leaves_add_left with (a := [Areg r]).
          apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified true 0 plus r);
                                                                            Areg (Quantified true 0 n r)]).
          apply check_end_no_leaves. lia.
        }
        assert (NO_LEAVES0: actions_no_leaves rer [Areg r; Acheck inp;
                                                   Areg (Quantified true 0 plus0 r)] dir). {
          apply actions_no_leaves_add_left with (a := [Areg r]).
          apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified true 0 plus0 r)]).
          apply check_end_no_leaves. lia.
        }
        unfold actions_no_leaves in NO_LEAVES, NO_LEAVES0.
        rewrite NO_LEAVES by auto. rewrite NO_LEAVES0 with (gm := GroupMap.reset _ gm) by auto.
        clear NO_LEAVES NO_LEAVES0 ISTREE1 ISTREE0 SKIP0 TREE1 TREE2.
        inversion SKIP; subst.
        + inversion SKIP0; subst. simpl. reflexivity.
        + inversion SKIP0; subst. simpl.
          assert (NO_LEAVES1: actions_no_leaves rer [Areg r; Acheck inp;
                                                     Areg (Quantified true 0 plus1 r)] dir). {
            apply actions_no_leaves_add_left with (a := [Areg r]).
            apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified true 0 plus1 r)]).
            apply check_end_no_leaves. lia.
          }
          rewrite NO_LEAVES1 by auto. reflexivity.

      - (* Not at end of input *)
        intros inp Hremlength gm t1 t2 TREE1 TREE2.
        inversion TREE1; subst. inversion TREE2; subst. inversion SKIP0; subst.
        simpl. clear TREE1 TREE2 SKIP0.
        assert (plus = +∞). { destruct plus; try discriminate. reflexivity. }
        assert (plus0 = +∞). { destruct plus0; try discriminate. reflexivity. }
        subst plus plus0. clear H1 H2.
        assert (EQUIV: leaves_equiv []
                         (tree_leaves titer (GroupMap.reset (def_groups r) gm) inp dir)
                         (tree_leaves titer0 (GroupMap.reset (def_groups r) gm) inp dir)). {
          apply actions_equiv_interm_prop with
            (rer := rer)
            (a1 := [Areg r; Acheck inp]) (a2 := [Areg r; Acheck inp])
            (b1 := [Areg (Quantified true 0 +∞ r); Areg (Quantified true 0 n r)])
            (b2 := [Areg (Quantified true 0 +∞ r)])
            (P := fun lf => StrictSuffix.strict_suffix (fst lf) inp dir)
            (dir := dir).
          - unfold actions_equiv_dir. intros.
            replace t2 with t1 by eauto using is_tree_determ. reflexivity.
          - apply actions_respect_prop_add_left with (a := [Areg r]) (b := [Acheck inp]).
            apply check_actions_prop.
          - apply actions_respect_prop_add_left with (a := [Areg r]) (b := [Acheck inp]).
            apply check_actions_prop.
          - unfold actions_equiv_dir_cond. intros lf SS t1 t2 TREE1 TREE2.
            apply IHl; auto. pose proof strict_suffix_remaining_length _ _ _ SS. lia.
          - auto.
          - auto.
        }
        inversion SKIP; subst; clear SKIP.
        + inversion SKIP0; subst; clear SKIP0. simpl.
          apply leaves_equiv_app. 2: reflexivity. auto.
        + rename plus into n. inversion SKIP0; subst; clear SKIP0. simpl.
          assert (INCL: incl (tree_leaves titer1 (GroupMap.reset (def_groups r) gm) inp
                                dir) (tree_leaves titer0 (GroupMap.reset (def_groups r) gm) inp
                                        dir)). {
            assert (TREErcheck: exists trcheck, is_tree rer [Areg r; Acheck inp] inp (GroupMap.reset (def_groups r) gm) dir trcheck)
              by (eexists; eapply compute_tr_is_tree).
            destruct TREErcheck as [trcheck TREErcheck].
            pose proof leaves_concat rer _ _ _ [Areg r; Acheck inp] [Areg (Quantified true 0 n r)] _ _ ISTREE2 TREErcheck as CONCAT2.
            pose proof leaves_concat rer _ _ _ [Areg r; Acheck inp] [Areg (Quantified true 0 +∞ r)] _ _ ISTREE0 TREErcheck as CONCAT0.
            eapply (flatmap_incl _ _ _ _ _ CONCAT2 CONCAT0); eauto.
            unfold funct_incl. intros a l1 l2 ACT1 ACT2.
            inversion ACT1; subst. inversion ACT2; subst.
            destruct n as [n|].
            - apply atmost_leaves_incl_infty with (m := n) (r := r) (g := true); auto.
            - replace t0 with t by eauto using is_tree_determ. unfold incl. auto.
          }
          apply leaves_equiv_incl; auto. reflexivity.
    Qed.



    Lemma atmost_atmost_equiv (m n: non_neg_integer_or_inf) r: (* r{0,m}r{0,n} ≅ r{0,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true 0 m r) (Quantified true 0 n r))
        ≅[rer] Quantified true 0 (m + n)%NoI r.
    Proof.
      intros NO_GROUPS dir. split. 1: { simpl. rewrite NO_GROUPS. reflexivity. }
                                 intros i gm tr1 tr2 TREE1. inversion TREE1; subst. clear TREE1. rewrite app_nil_r in CONT.
      destruct m as [m|]; destruct n as [n|]; destruct dir;
        simpl in CONT; revert i gm tr1 tr2 CONT; simpl.

      (* m and n are finite *)
      - apply atmost_atmost_equiv_actions_mnat.
      - rewrite PeanoNat.Nat.add_comm. apply atmost_atmost_equiv_actions_mnat.

      (* m is finite, n is infinite *)
      - apply atmost_atmost_equiv_actions_mnat.
      - apply atmost_atmost_equiv_actions_minf.

      (* m is infinite, n is finite *)
      - apply atmost_atmost_equiv_actions_minf.
      - apply atmost_atmost_equiv_actions_mnat.

      (* Both m and n are infinite *)
      - apply atmost_atmost_equiv_actions_minf.
      - apply atmost_atmost_equiv_actions_minf.
    Qed.

    (** * The four cases used in the new Quantifiers Merge Transform of regexp-tree *)

    (* r{n1}r{n2,m2} -> r{n1+n2,n1+m2}
       r{n1}r{n2,m2}? -> r{n1+n2,n1+m2}?
       r{n1}?r{n2,m2} -> r{n1+n2,n1+m2}
       r{n1}?r{n2,m2}? -> r{n1+n2,n1+m2}? *)
    Theorem merge_forced_forward:
      forall r n1 g1 n2 m2 g2,
        def_groups r = [] ->
        (Sequence (Quantified g1 n1 0 r) (Quantified g2 n2 m2 r))
          ≅[rer][forward] Quantified g2 (n1+n2) m2 r.
    Proof.
      intros r n1 g1 n2 m2 g2 DEF.
      (* break down r{n2,n2+m2} into r{n2}r{0,m2} *)
      eapply tree_equiv_dir_transitive.
      { apply seq_equiv_dir. reflexivity.
        rewrite <- bounded_atmost_forward; auto. reflexivity. }
      (* sequence associativity *)
      eapply tree_equiv_dir_transitive.
      { apply seq_assoc. }
      (* set to true the greediness of forced iterations *)
      eapply tree_equiv_dir_transitive.
      { apply seq_equiv_dir. 2: reflexivity.
        apply seq_equiv_dir; apply forced_equiv_true. }
      (* merge the forced iterations r{n1}r{n2} *)
      eapply tree_equiv_dir_transitive.
      { eapply seq_equiv_dir. 2: reflexivity.
        apply bounded_bounded_equiv. auto. }
      (* set the greediness of r{n1+n2} to g2 *)
      eapply tree_equiv_dir_transitive.
      { eapply seq_equiv_dir. 2: reflexivity.
        symmetry. apply forced_equiv_true with (g:=g2). }
      (* merge the forced iterations r{n1+n2} back with the free iterations r{0,m2} *)
      apply bounded_atmost_forward. auto.
    Qed.

    (* r{n1,m1}r{0,m2} -> r{n1,m1+m2} *)
    Theorem merge_greedy_forward:
      forall r n1 m1 m2,
        def_groups r = [] ->
        (Sequence (Quantified true n1 m1 r) (Quantified true 0 m2 r))
          ≅[rer][forward] Quantified true n1 (m1 + m2)%NoI r.
    Proof.
      intros r n1 m1 m2 DEF.
      (* break down r{n1,n1+m1} into r{n1}r{0,m1} *)
      eapply tree_equiv_dir_transitive.
      { apply seq_equiv_dir. 2: reflexivity.
        rewrite <- bounded_atmost_forward; auto. reflexivity. }
      (* sequence associativity *)
      eapply tree_equiv_dir_transitive.
      { symmetry. apply seq_assoc. }
      (* merge the free iterations r{0,m1}r{0,m2} *)
      eapply tree_equiv_dir_transitive.
      { eapply seq_equiv_dir. reflexivity.
        apply atmost_atmost_equiv. auto. }
      (* merge the forced iterations r{n1} back with the free iterations r{0,m1+m2} *)
      apply bounded_atmost_forward. auto.
    Qed.

    (* r{n1,m1}r{n2} -> r{n1+n2,m1+n2}
       r{n1,m1}?r{n2} -> r{n1+n2,m1+n2}?
       r{n1,m1}r{n2}? -> r{n1+n2,m1+n2}
       r{n1,m1}?r{n2}? -> r{n1+n2,m1+n2}? *)
    Theorem merge_forced_backward:
      forall r n1 m1 g1 n2 g2,
        def_groups r = [] ->
        (Sequence (Quantified g1 n1 m1 r) (Quantified g2 n2 0 r))
          ≅[rer][backward] Quantified g1 (n1+n2) m1 r.
    Proof.
      intros r n1 m1 g1 n2 g2 DEF.
      (* break down r{n1,n1+m1} into r{0,m1}r{n1} *)
      eapply tree_equiv_dir_transitive.
      { apply seq_equiv_dir. 2: reflexivity.
        rewrite <- atmost_bounded_backward; auto. reflexivity. }
      (* sequence associativity *)
      eapply tree_equiv_dir_transitive.
      { symmetry. apply seq_assoc. }
      (* set to true the greediness of forced iterations *)
      eapply tree_equiv_dir_transitive.
      { apply seq_equiv_dir. reflexivity.
        apply seq_equiv_dir; apply forced_equiv_true. }
      (* merge the forced iterations r{n1}r{n2} *)
      eapply tree_equiv_dir_transitive.
      { eapply seq_equiv_dir. reflexivity.
        apply bounded_bounded_equiv. auto. }
      (* set the greediness of r{n1+n2} to g1 *)
      eapply tree_equiv_dir_transitive.
      { eapply seq_equiv_dir. reflexivity.
        symmetry. apply forced_equiv_true with (g:=g1). }
      (* merge the forced iterations r{n1+n2} back with the free iterations r{0,m2} *)
      apply atmost_bounded_backward. auto.
    Qed.

    (* r{0,m1}r{n2,m2} -> r{n2,m1+m2} *)
    Theorem merge_greedy_backward:
      forall r m1 n2 m2,
        def_groups r = [] ->
        (Sequence (Quantified true 0 m1 r) (Quantified true n2 m2 r))
          ≅[rer][backward] Quantified true n2 (m1 + m2)%NoI r.
    Proof.
      intros r m1 n2 m2 DEF.
      (* break down r{n2,n2+m2} into r{n2}r{0,m2} *)
      eapply tree_equiv_dir_transitive.
      { apply seq_equiv_dir. reflexivity.
        rewrite <- atmost_bounded_backward; auto. reflexivity. }
      (* sequence associativity *)
      eapply tree_equiv_dir_transitive.
      { apply seq_assoc. }
      (* merge the free iterations r{0,m1}r{0,m2} *)
      eapply tree_equiv_dir_transitive.
      { eapply seq_equiv_dir. 2: reflexivity.
        apply atmost_atmost_equiv. auto. }
      (* merge the forced iterations r{n2} back with the free iterations r{0,m1+m2} *)
      apply atmost_bounded_backward. auto.
    Qed.

    (** * Proving open  greedy on both sides **)

    (** Helpers to prove tree equality by other equalities and inclusions**)
    Lemma leaves_equiv_incl2:
      forall a b c,
        incl b a ->
        leaves_equiv [] a c ->
        leaves_equiv [] (a ++ b) c.
    Proof. 
      intros. rewrite <- app_nil_r. eapply leaves_equiv_app2.
      assumption. rewrite app_nil_r. revert a H H0.
      induction b. intros a H H0. reflexivity.
      intros. destruct a. constructor.
      rewrite is_seen_spec. eapply H; eauto. simpl. left. reflexivity.
      eapply IHb; eauto. intros x iA. specialize (H x). simpl in H.
      eapply H. right; auto.
    Qed.

    Lemma leaves_equiv_incl3:
      forall a b c d,
        incl c a ->
        leaves_equiv [] (a ++ b) d ->
        leaves_equiv [] (a ++ b ++ c) d.
    Proof.
      intros. rewrite app_assoc.
      eapply leaves_equiv_incl2 ; eauto.
      intros x xIa. apply in_or_app. left. auto.
    Qed.

    Lemma leaves_equiv_incl4:
      forall a b c d e: list leaf,
        leaves_equiv [] a b ->
        leaves_equiv [] c e ->
        incl d a ->
        leaves_equiv [] (a ++ c ++ d) (b ++ e).
    Proof.
      intros.
      apply leaves_equiv_incl3. assumption.
      apply leaves_equiv_app; auto.
    Qed.

    (* A quantified always contains the current group and input*)
    Lemma atmost_leaves_incl_self (d: non_neg_integer_or_inf) (g: bool)r:
      forall inp gm1  dir tm,
        is_tree rer [Areg (Quantified g 0 d r)] inp gm1 dir tm ->
        incl [(inp, gm1)] (tree_leaves tm gm1 inp dir).
    Proof.
      intros i gm dir tm TM.
      specialize (is_tree_productivity rer [Areg (Quantified g 0 0 r)] i gm dir) as [tn  TN].
      pose proof (atmost_leaves_incl' _  d _ _ _ _ _ _ tm TN).
      inversion TN; inversion SKIP; subst. simpl in H.
      destruct d; eapply H; auto.
      destruct plus; discriminate.
    Qed.
    
    (* A quantified followed by another quantified always contains the current group and input*)
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

    (** Induction helper, but instead than with equality it works for inclusivity**)
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
        apply in_app_or in xInA as [cx | cy].
        left. inversion HEAD; inversion HEAD0; subst.
        inversion TREE; inversion TREE0; try contradiction; subst.
        destruct a. simpl in *.
        2: contradiction.
        2: right; eapply IHl1; eauto.
        clear IHl1.
        revert x cx. eapply H1; eauto. 
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
        + subst. simpl. intros x xIn. apply in_app_or in xIn as [cx | cy]. revert x cx.
          inversion SKIP; subst. simpl. eapply atmost_leaves_incl_self_double; eauto.
          inversion H0; subst. simpl. eapply in_or_app. left.
          rewrite H in *. simpl in *.
          eapply quantifier_inf_step_advances_incl with
            (acts1 := [Areg (Quantified false 0 plus r)])
            (acts2 := [Areg (Quantified true 0 plus0 r); Areg (Quantified g 0 d1 r)]); eauto.
          destruct plus0. discriminate.
          intros. eapply IHl; eauto. 
          lia.
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
        + simpl in *. apply leaves_equiv_incl4.
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
          eapply quantifier_inf_step_advances_incl with
            (acts1 := [Areg (Quantified false 0 plus1 r)])
            (acts2 := [Areg (Quantified true 0 +∞ r); Areg (Quantified false 0 match plus1 with | NoI.N r' => NoI.N (S r') | +∞ => +∞ end r)]); simpl; eauto.
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
      - apply Nat.lt_eq_cases in HeqL as [cx | cy].
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


    Lemma quantified_open_greedy_left:
    forall r delta1 g,
      def_groups r = [] -> 
      (Sequence (Quantified g 0 delta1 r) (Quantified true 0 +∞ r))
        ≅[rer] (Quantified true 0 +∞ r).
  Proof.
    intros r delta1 g GROUPEMPT.
    destruct g.
    - (** True case (already proven) **)
      etransitivity. eapply atmost_atmost_equiv; eauto.
      destruct delta1; reflexivity.
    - (** False case (list analysis) **)
      split. simpl. rewrite GROUPEMPT. reflexivity.
      intros i g t1 t2 T1 T2. destruct dir.
      + inversion T1; subst; clear T1.
        simpl in CONT. eapply atmost_atmost_equiv_actions_false_trueinf; eauto.
      + inversion T1; subst; clear T1.
        simpl in CONT. eapply atmost_atmost_equiv_actions_trueinf_false; eauto.
  Qed.
  
  Lemma quantified_open_greedy_right:
    forall r delta1 g,
      def_groups r = [] -> 
      (Sequence (Quantified true 0 +∞ r) (Quantified g 0 delta1 r))
        ≅[rer] (Quantified true 0 +∞ r).
  Proof.
    intros r delta1 g GROUPEMPT.
    destruct g.
    - (** True case (already proven) **)
      etransitivity. eapply atmost_atmost_equiv; eauto.
      destruct delta1; reflexivity.
    - (** False case (list analysis) **)
      split. simpl. rewrite GROUPEMPT. reflexivity.
      intros i g t1 t2 T1 T2. destruct dir.
      + inversion T1; subst; clear T1.
        simpl in CONT. eapply atmost_atmost_equiv_actions_trueinf_false; eauto.
      + inversion T1; subst; clear T1.
        simpl in CONT. eapply atmost_atmost_equiv_actions_false_trueinf; eauto.
  Qed.

  Lemma quantified_open_inf_switch_tree:
    forall r i g t1 t2 dir,
      def_groups r = [] ->
    is_tree rer [Areg (Quantified true 0 +∞ r); Areg r] i g dir t1 ->
      is_tree rer [Areg r; Areg (Quantified true 0 +∞ r)] i g dir t2 ->
      tree_equiv_tr_dir i g dir t1 t2.
    Proof.
      intros r i g t1 t2 dir GROUPEMPT T1 T2.
      remember (remaining_length i dir) as l.
      assert (Hlength_le: remaining_length i dir <= l) by lia. clear Heql.
      generalize dependent i.
      induction l; intros.
      - specialize (is_tree_productivity rer [Areg r] i g dir) as [t3 T3].
        eapply quantifier_null_length_head in T2; eauto.
        eapply quantifier_null_length_skip with (acts := [Areg r]) in T1; eauto.
        unfold tree_equiv_tr_dir. rewrite T1. symmetry; auto.
      - apply GroupId.le_lteq in Hlength_le as [p1 | p2]. eapply IHl; eauto. lia.
        unfold tree_equiv_tr_dir. inversion T1; subst. clear T1. simpl.
        rewrite GROUPEMPT in *; simpl in *.
        rewrite app_cons in T2, ISTREE1. eapply leaves_concat with (act1 := [Areg r])in T2, ISTREE1; eauto.
        remember (tree_leaves tskip g i dir) as l1. induction l1.
        + inversion T2; inversion ISTREE1. reflexivity.
        + inversion T2; inversion HEAD; subst. rewrite app_cons.
          Admitted.
          
            
        
        
        
        
        
      

  Lemma quantified_open_inf_switch:
    forall r dir,
      def_groups r = [] ->
    (Sequence (Quantified true 0 +∞ r) r)
      ≅[rer][dir] Sequence r (Quantified true 0 +∞ r).
    Proof.
      intros r dir GROUPEMPT.
      split. simpl. reflexivity.
      intros i g t1 t2 T1 T2.
      destruct dir.
      - inversion T1; inversion T2; subst.
         simpl in CONT, CONT0. eapply quantified_open_inf_switch_tree; eauto.
      - inversion T1; inversion T2; subst.
        simpl in CONT, CONT0. symmetry. eapply quantified_open_inf_switch_tree; eauto.
    Qed.

  Lemma quantified_open_pop_left:
    forall min1  r dir,
      def_groups r = [] ->
    (Sequence (Quantified true 0 +∞ r) (Quantified true min1 0 r))
      ≅[rer][dir] (Quantified true min1 +∞ r).
  Proof.
    intros min r dir GROUPEMPT.
    destruct dir. 2: eapply merge_forced_backward; eauto.
    induction min.
    - etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply quantified_zero_equiv; auto.
      } eapply sequence_epsilon_right_equiv.
    -  etransitivity. {
         eapply seq_equiv_dir. reflexivity.
         eapply quantified_S_equiv_forward; auto.
       } etransitivity. eapply sequence_assoc_equiv.
       etransitivity. {
         eapply seq_equiv_dir. eapply seq_equiv_dir.
         reflexivity.
         eapply  quantified_one_equiv; eauto.
         reflexivity.
       } etransitivity. {
         eapply seq_equiv_dir.
         eapply quantified_open_inf_switch. reflexivity.
       } etransitivity. {
         symmetry. eapply sequence_assoc_equiv.
       } etransitivity. {
         eapply seq_equiv_dir. reflexivity.
         eapply IHmin.
       } etransitivity. {
         eapply seq_equiv_dir. symmetry. eapply quantified_one_equiv; auto.
         reflexivity.
       }
       symmetry. eapply quantified_S_equiv_forward; auto.
  Qed.
       
          
  Lemma quantified_open_pop_right:
    forall min1  r dir,
      def_groups r = [] ->
    (Sequence (Quantified true min1 0 r) (Quantified true 0 +∞ r))
      ≅[rer][dir] (Quantified true min1 +∞ r).
  Proof.
    intros min r dir GROUPEMPT.
    destruct dir.
    etransitivity. eapply merge_forced_forward; eauto. rewrite Nat.add_0_r. reflexivity.
    induction min.
    - etransitivity. {
        eapply seq_equiv_dir. 
        eapply quantified_zero_equiv; auto.
        reflexivity.
      } eapply sequence_epsilon_left_equiv.
    -  etransitivity. {
         eapply seq_equiv_dir. 
         eapply quantified_S_equiv_backward; auto.
         reflexivity.
       } etransitivity. symmetry. eapply sequence_assoc_equiv.
       etransitivity. {
         eapply seq_equiv_dir. reflexivity. eapply seq_equiv_dir.
         
         eapply  quantified_one_equiv; eauto.
         reflexivity.
       } etransitivity. {
         eapply seq_equiv_dir. reflexivity.
         symmetry. eapply quantified_open_inf_switch. 
       } etransitivity. {
         eapply sequence_assoc_equiv.
       } etransitivity. {
         eapply seq_equiv_dir.
         eapply IHmin. reflexivity.
       } etransitivity. {
         eapply seq_equiv_dir. reflexivity.
         symmetry. eapply quantified_one_equiv; auto.
       }
       symmetry. eapply quantified_S_equiv_backward; auto.
  Qed.
    

  Lemma quantified_open_greedy_right_min:
    forall r min1 min2 delta1 g,
      def_groups r = [] -> 
      (Sequence (Quantified true min1 +∞ r) (Quantified g min2 delta1 r))
        ≅[rer] (Quantified true (min1 + min2) +∞ r).
  Proof.
    intros r min1 min2 delta1 g GROUPEMPT dir.
    destruct dir.
    - symmetry. etransitivity. {
        symmetry. eapply merge_forced_forward with (g1 := true); auto.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        symmetry. eapply quantified_open_pop_right; auto.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply seq_equiv_dir. reflexivity.
        symmetry. eapply quantified_open_greedy_right with (g := g); auto.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply sequence_assoc_equiv.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply seq_equiv_dir. eapply quantified_open_pop_right; eauto.
        reflexivity.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply seq_equiv_dir. symmetry. eapply quantified_open_pop_left; auto.
        reflexivity.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        symmetry. eapply sequence_assoc_equiv.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply seq_equiv_dir. reflexivity.
        eapply merge_forced_forward; auto.
      } etransitivity. eapply sequence_assoc_equiv.
      etransitivity. {
        eapply seq_equiv_dir.
        eapply quantified_open_pop_right; auto. reflexivity.
      } rewrite GroupId.add_0_r. reflexivity.
    - symmetry. etransitivity. {
        symmetry. eapply merge_forced_backward with (g2 := true); auto.
      }
      etransitivity. {
        eapply seq_equiv_dir.
        symmetry. eapply quantified_open_pop_right; auto.
        reflexivity.
      }
      etransitivity. {
        eapply seq_equiv_dir. eapply seq_equiv_dir. 1, 3: reflexivity.
        symmetry. eapply quantified_open_greedy_right with (g := g); auto.
      }
      etransitivity. symmetry. eapply sequence_assoc_equiv.
      etransitivity. {
        eapply seq_equiv_dir. reflexivity. symmetry. eapply sequence_assoc_equiv.
      }
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply seq_equiv_dir. reflexivity.
        eapply merge_forced_backward; auto.
      }
      etransitivity. eapply sequence_assoc_equiv.
      etransitivity. {
        eapply seq_equiv_dir. eapply quantified_open_pop_right; auto.
        reflexivity.
      } reflexivity. 
  Qed.


  Lemma quantified_open_greedy_left_min:
    forall r min1 min2 delta1 g,
      def_groups r = [] -> 
      (Sequence (Quantified g min1 delta1 r) (Quantified true min2 +∞ r))
        ≅[rer] (Quantified true (min1 + min2) +∞ r).
  Proof.
    intros r min1 min2 delta1 g GROUPEMPT dir.
    destruct dir.
    - symmetry. etransitivity. {
        symmetry. eapply merge_forced_forward with (g1 := true); auto.
      } etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        symmetry. eapply quantified_open_pop_left; auto.
      } etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply seq_equiv_dir. symmetry.
        eapply quantified_open_greedy_left with (g := g); auto.
        reflexivity.
      } etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        symmetry. eapply sequence_assoc_equiv.
      } etransitivity. {
        eapply seq_equiv_dir. reflexivity. eapply seq_equiv_dir. reflexivity.
        eapply quantified_open_pop_left; auto.
      } etransitivity. eapply sequence_assoc_equiv.
      etransitivity. {
        eapply seq_equiv_dir. eapply merge_forced_forward; auto. reflexivity.
      } rewrite GroupId.add_0_r. reflexivity.
    - symmetry. etransitivity. {
        symmetry. eapply merge_forced_backward with (g2 := true); auto.
      } etransitivity. {
        eapply seq_equiv_dir. symmetry. eapply quantified_open_pop_left; auto. reflexivity.
      } etransitivity. {
        eapply seq_equiv_dir. eapply seq_equiv_dir.
        symmetry. eapply quantified_open_greedy_left with (delta1 := delta1) (g := g); auto.
        all: reflexivity.
      } etransitivity. {
        eapply seq_equiv_dir. 
        symmetry. eapply sequence_assoc_equiv.
        reflexivity.
      } etransitivity. {
        eapply seq_equiv_dir. eapply seq_equiv_dir. reflexivity.
        eapply quantified_open_pop_left; eauto. reflexivity.
      }
      etransitivity. {
        eapply seq_equiv_dir. eapply seq_equiv_dir. 2: symmetry; eapply quantified_open_pop_right; auto. all: reflexivity.
      }
      etransitivity. {
        eapply seq_equiv_dir.
        eapply sequence_assoc_equiv. reflexivity.
      } etransitivity. {
        eapply seq_equiv_dir. eapply seq_equiv_dir.
        eapply merge_forced_backward; auto.
        all: reflexivity.
      }
      simpl. etransitivity. symmetry. eapply sequence_assoc_equiv.
      etransitivity. {
        eapply seq_equiv_dir. reflexivity.
        eapply quantified_open_pop_left; auto.
      } reflexivity.
  Qed.
                
  End BoundedRepetitions.

  (*|
## Character classes

Illustrative examples taken from https://github.com/DmitrySoshnikov/regexp-tree/tree/master/src/optimizer (not complete).
|*)

  Section Ranges.
    Variables c0 c1 c2: Parameters.Character.
    Hypothesis H01: Character.numeric_value c0 <= Character.numeric_value c1.
    Hypothesis H12: Character.numeric_value c1 <= Character.numeric_value c2.

    Lemma char_match_range_split c:
      char_match rer c (CdRange c0 c2) =
        char_match rer c (CdUnion (CdRange c0 c1) (CdRange c1 c2)).
    Proof.
      unfold char_match; simpl; apply Bool.eq_iff_eq_true.
      rewrite !Character.numeric_pseudo_bij.
      autorewrite with charset in *; autounfold with charset.
      setoid_rewrite CharSet.range_spec.
      setoid_rewrite EqDec.inversion_true.
      split; intros H; [ | destruct H ].
      all: destruct H as (c' & ?Hle & <-).
      1: destruct (le_ge_dec (Character.numeric_value c') (Character.numeric_value c1)).
      all: firstorder eauto with lia.
    Qed.

    Hint Rewrite char_match_range_split : tree_equiv_symbex.

    Lemma range_range_equiv: (* [a-de-f] -> [a-f] *)
      Character (CdUnion (CdRange c0 c1) (CdRange c1 c2)) ≅[rer]
        Character (CdRange c0 c2).
    Proof.
      tree_equiv_rw; tree_equiv_symbex; leaves_equiv_t.
    Qed.
  End Ranges.

  Section CharacterClasses.
    Hint Unfold char_match : tree_equiv_symbex.

    Lemma class_union_equiv cd0 cd1:
      Disjunction (Character cd0) (Character cd1) ≅[rer] Character (CdUnion cd0 cd1).
    Proof.
      tree_equiv_rw; tree_equiv_symbex; leaves_equiv_t.
    Qed.

    Lemma class_single_left_equiv c0:
      Character (CdUnion (CdSingle c0) CdEmpty) ≅[rer] Character (CdSingle c0).
    Proof.
      tree_equiv_rw; tree_equiv_symbex; leaves_equiv_t.
    Qed.

    Lemma class_single_right_equiv c0:
      Character (CdUnion CdEmpty (CdSingle c0)) ≅[rer] Character (CdSingle c0).
    Proof.
      tree_equiv_rw; tree_equiv_symbex; leaves_equiv_t.
    Qed.
  End CharacterClasses.
End RegexpTree.

