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

    Lemma bounded_bounded_equiv m n r: (* r{m}r{n} ≅ r{m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true n 0 r))
        ≅[rer] Quantified true (m + n) 0 r.
    Proof.
      intros H [].
      - apply bounded_util_fwd. auto.
      - rewrite PeanoNat.Nat.add_comm. apply bounded_util_bwd. auto.
    Qed.

    Lemma bounded_atmost_equiv m n r: (* r{m}r{0,n} ≅[forward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true m 0 r) (Quantified true 0 n r))
        ≅[rer][forward] Quantified true m n r.
    Proof. intro NO_GROUPS. rewrite bounded_util_fwd, PeanoNat.Nat.add_0_r. 1: reflexivity. auto. Qed.

    Lemma atmost_bounded_equiv m n r: (* r{0,n}r{m} ≅[backward] r{m,m+n} *)
      def_groups r = [] ->
      (Sequence (Quantified true 0 n r) (Quantified true m 0 r))
        ≅[rer][backward] Quantified true m n r.
    Proof. intro NO_GROUPS. rewrite bounded_util_bwd, PeanoNat.Nat.add_0_r. 1: reflexivity. auto. Qed.

    Lemma bounded_atmost_lazy_equiv m n r: (* r{m}r{0,n}? ≅[forward] r{m,m+n}? *)
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

    Lemma atmost_bounded_lazy_equiv m n r: (* r{0,n}?r{m} ≅[backward] r{m,m+n}? *)
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
    Lemma atmost_leaves_incl' (m: nat) (d: non_neg_integer_or_inf) r:
      forall inp gm dir tm tn,
        is_tree rer [Areg (Quantified true 0 m r)] inp gm dir tm ->
        is_tree rer [Areg (Quantified true 0 (m+d)%NoI r)] inp gm dir tn ->
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
          apply in_or_app. right. left. reflexivity.
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
        apply in_app_or in Hin. destruct Hin.
        + apply in_or_app. left. eapply (flatmap_incl _ _ _ _ _ CONCAT CONCAT0); eauto.
          unfold funct_incl. intros a l1 l2 ACT1 ACT2.
          inversion ACT1; subst. inversion ACT2; subst. apply IHm; auto.
        + apply in_or_app. auto.
    Qed.

    (* Specialization to d = n-m *)
    Corollary atmost_leaves_incl_nat (m n: nat) r:
      m <= n ->
      forall inp gm dir tm tn,
        is_tree rer [Areg (Quantified true 0 m r)] inp gm dir tm ->
        is_tree rer [Areg (Quantified true 0 n r)] inp gm dir tn ->
        incl (tree_leaves tm gm inp dir) (tree_leaves tn gm inp dir).
    Proof.
      intros. apply atmost_leaves_incl' with (m := m) (d := n-m) (r := r) (tm := tm); auto.
      simpl. replace (m + (n - m)) with n by lia. auto.
    Qed.

    (* Specialization to d = +∞ *)
    Corollary atmost_leaves_incl_infty (m: nat) r:
      forall inp gm dir tm tn,
        is_tree rer [Areg (Quantified true 0 m r)] inp gm dir tm ->
        is_tree rer [Areg (Quantified true 0 +∞ r)] inp gm dir tn ->
        incl (tree_leaves tm gm inp dir) (tree_leaves tn gm inp dir).
    Proof.
      intros. apply atmost_leaves_incl' with (m := m) (d := +∞) (r := r) (tm := tm); auto.
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
            - simpl in TREE0. apply atmost_leaves_incl_nat with (m := n) (n := m + S n) (r := r); eauto. lia.
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
            - apply atmost_leaves_incl_infty with (m := n) (r := r); auto.
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



  

Lemma concat_regs_ret_empt_group:
        forall r1 r2 inp1 inp2 gm1 gm2 dir t,
          (forall (inp1 inp2 : input) (gm1 gm2 : group_map) 
             (dir : Direction) (t : tree),
              is_tree rer [Areg r1] inp1 gm1 dir t ->
              In (inp2, gm2) (tree_leaves t gm1 inp1 dir) -> gm1 = gm2) ->
          (forall (inp1 inp2 : input) (gm1 gm2 : group_map) 
             (dir : Direction) (t : tree),
              is_tree rer [Areg r2] inp1 gm1 dir t ->
              In (inp2, gm2) (tree_leaves t gm1 inp1 dir) -> gm1 = gm2) ->
          is_tree rer [Areg r1; Areg r2] inp1 gm1 dir t -> 
          In (inp2, gm2) (tree_leaves t gm1 inp1 dir) ->
          gm1 = gm2.
  Proof.
    intros r1 r2 inp1 inp2 gm1 gm2 dir t IH1 IH2 TREE1 TLEAVES1.
     specialize (is_tree_productivity rer [Areg r1] inp1 gm1 dir) as [t2 TREE2].
      rewrite app_cons in TREE1. eapply leaves_concat with (act1:= [Areg r1]) in TREE1; eauto.
      pose proof (act_from_leaf_determ rer [Areg r2] dir) as R2determ.
      pose proof (In_FlatMap _  _  _ _  R2determ TREE1 TLEAVES1) as [lf [l0 [Inlf [act Inlp]]]].
      destruct lf as [inp3 gm3].
      specialize (IH1 inp1 inp3 gm1 gm3 _ t2  TREE2 Inlf).
      inversion act; subst. simpl in *.
      specialize (IH2 inp3 inp2 gm3 gm2 _ t0  TREE Inlp).
      assumption.
  Qed.

Lemma concat_regs_ret_empt_group_check:
        forall r1 r2 inp1 inp2 gm1 gm2 dir t,
          (forall (inp1 inp2 : input) (gm1 gm2 : group_map) 
             (dir : Direction) (t : tree),
              is_tree rer [Areg r1] inp1 gm1 dir t ->
              In (inp2, gm2) (tree_leaves t gm1 inp1 dir) -> gm1 = gm2) ->
          (forall (inp1 inp2 : input) (gm1 gm2 : group_map) 
             (dir : Direction) (t : tree),
              is_tree rer [Areg r2] inp1 gm1 dir t ->
              In (inp2, gm2) (tree_leaves t gm1 inp1 dir) -> gm1 = gm2) ->
          is_tree rer [Areg r1; Acheck inp1; Areg r2] inp1 gm1 dir t -> 
          In (inp2, gm2) (tree_leaves t gm1 inp1 dir) ->
          gm1 = gm2.
  Proof.
    intros r1 r2 inp1 inp2 gm1 gm2 dir t IH1 IH2 TREE1 TLEAVES1.
    specialize (is_tree_productivity rer [Areg r1] inp1 gm1 dir) as [t2 TREE2].
    rewrite app_cons in TREE1. eapply leaves_concat with (act1:= [Areg r1]) in TREE1; eauto.
      pose proof (act_from_leaf_determ rer [Acheck inp1; Areg r2] dir) as R2determ.
      pose proof (In_FlatMap _  _  _ _  R2determ TREE1 TLEAVES1) as [lf [l0 [Inlf [act Inlp]]]].
      destruct lf as [inp3 gm3].
      specialize (IH1 inp1 inp3 gm1 gm3 _ t2  TREE2 Inlf).
      inversion act; subst. simpl in *.
      inversion TREE; subst.
      specialize (IH2 inp3 inp2 gm3 gm2 _ treecont TREECONT Inlp).
      assumption. inversion Inlp.
  Qed.



  Lemma undefgroup_is_imm:
    forall r inp inp2 gm gm2 dir t,
      def_groups r = [] ->
      is_tree rer [Areg r] inp gm dir t ->
      In (inp2, gm2) (tree_leaves t gm inp dir) ->
      gm = gm2.
  Proof.
    intros r.
    induction r; try discriminate; intros inp inp2 gm gm2 dir t GROUPEMPT TREE1 TLEAVES; auto.
    (*C1: Epsilon *)
    inversion TREE1; inversion ISTREE; subst. 
    simpl in TLEAVES. destruct TLEAVES. inversion H; auto. contradiction.
    (*C2: Character*)
    inversion TREE1. inversion TREECONT; subst.
    inversion TLEAVES; auto. unfold advance_input' in H.
    inversion H; auto.
    contradiction.
    subst. inversion TLEAVES.
    (*C3: Disjunction *)
    inversion TREE1. simpl in *. inversion TREE1; subst. simpl in TLEAVES.
    specialize (app_eq_nil _ _ GROUPEMPT) as [r1Nat r2Nat].
    specialize (in_app_or _ _ _ TLEAVES) as [ inT1 | inT2 ].
    eapply (IHr1 _ _ _ _ _ _ r1Nat ISTREE1). apply inT1.
    eapply (IHr2 _ _ _ _ _ _ r2Nat ISTREE2). apply inT2.
    (*C4: Sequence *)
    inversion TREE1; simpl in GROUPEMPT.
    specialize (app_eq_nil _ _ GROUPEMPT) as [r1Empt r2Empt]. clear GROUPEMPT.
    inversion TREE1; subst.
    destruct dir; simpl in CONT.
    (* foreward *)
    simpl in CONT0.
    apply (concat_regs_ret_empt_group r1 r2 inp inp2 gm gm2 forward t); try assumption.
    intros; eapply IHr1; eauto. intros; eapply IHr2; eauto.
    (*backward*)
    simpl in CONT0.
    apply (concat_regs_ret_empt_group r2 r1 inp inp2 gm gm2 backward t); try assumption.
    intros; eapply IHr2; eauto. intros; eapply IHr1; eauto.
    (*C5: Backreference *)
    4:{
      inversion TREE1; subst.
      inversion TREECONT; subst. destruct TLEAVES.
      inversion H; auto. contradiction.
      destruct TLEAVES.
    }
    (*C5: Anchor *)
    3: {
      inversion TREE1; subst.
      inversion TREECONT; subst. destruct TLEAVES. inversion H; auto.
      contradiction. destruct TLEAVES.
    }
    (*C5: Lookaround *)
    2: {
      inversion TREE1; subst.
      2: {destruct TLEAVES. }
      inversion TREECONT; subst. clear TREE1 TREECONT.
      simpl in GROUPEMPT.
      remember (positivity lk ) as l1.
      remember (tree_leaves treelk gm inp (lk_dir lk)) as l2.
      simpl in TLEAVES. rewrite <- Heql1 in TLEAVES. rewrite <- Heql2 in TLEAVES.
      destruct l1, l2; try inversion TLEAVES; try inversion H; try discriminate; auto.
      destruct l; specialize (IHr _ i  _ gm2 _ _ GROUPEMPT TREELK).
      rewrite <- Heql2 in IHr.
      apply IHr. constructor. destruct TLEAVES. inversion H; auto.
      contradiction.
    }
    (*C7: Quantifier*)
    simpl in GROUPEMPT. revert t dir inp inp2 gm gm2 TREE1 TLEAVES.
    induction min.
    (* Case min+1 with induction*)
    2: {
      intros t dir inp inp2 gm gm2 TREE1 TLEAVES.
      inversion TREE1; subst. rewrite GROUPEMPT in *. simpl in *.
      apply (concat_regs_ret_empt_group r (Quantified greedy min delta r) inp inp2 gm gm2 dir titer); try assumption.
      intros; eapply IHr; eauto. intros; eapply IHmin; eauto.
    }
    (*Case min = 0, delta = 0*)
    destruct delta. induction n; intros t dir inp inp2 gm gm2 TREE1 TLEAVES.
    inversion TREE1; inversion SKIP; subst. inversion TLEAVES; try contradiction. inversion H; auto.
    destruct plus; auto. inversion H1; auto. discriminate.
    (*Case min = 0, delta = n+1*)
    inversion TREE1; subst. destruct plus; inversion H1. subst.
    pose proof (concat_regs_ret_empt_group_check r (Quantified greedy 0 (NoI.N n) r) inp inp2 gm gm2 dir titer).
    destruct greedy.
    (*case greedy*)
    - rewrite GROUPEMPT in TLEAVES, ISTREE1; simpl in *.
      specialize (in_app_or _ _ _ TLEAVES) as [ inT1 | inT2 ].
      2: {inversion SKIP; subst. inversion inT2. inversion H0. auto. contradiction. }
      apply H; try assumption.
      intros; eapply IHr; eauto.
      intros; eapply IHn; eauto.
      (*case non greedy*)
    - rewrite GROUPEMPT in TLEAVES, ISTREE1; simpl in *.
      specialize (in_app_or _ _ _ TLEAVES) as [ inT1 | inT2 ].
      inversion SKIP; subst. inversion inT1. inversion H0. auto. contradiction.
      apply H; try assumption.
      intros; eapply IHr; eauto.
      intros; eapply IHn; eauto.
    - (*Case min = 0, delta = +inf*)
      intros. 
      remember (remaining_length inp dir) as l.
      assert (Hlength_le: remaining_length inp dir <= l) by lia. clear Heql.
      generalize dependent inp. revert t gm gm2 inp2 dir.
      induction l; intros t gm gm2 inp2 dir inp TREE1 LEAVES lEq.
      inversion TREE1; inversion SKIP; subst. destruct plus. discriminate. clear H1 SKIP.
      assert (NL: actions_no_leaves rer [Areg r; Acheck inp; Areg (Quantified greedy 0 +∞ r)] dir). {
        apply actions_no_leaves_add_left with (a := [Areg r]).
        apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified greedy 0 +∞ r)]).
        apply check_end_no_leaves. lia.
      }
      specialize (NL _ _ _ ISTREE1).
      destruct greedy; simpl in *; rewrite NL in LEAVES; inversion LEAVES; inversion H; auto.
      (* N + 1*)
      apply GroupId.le_lteq in lEq as [leq | eq].
      rewrite GroupId.lt_succ_r in leq. eapply IHl; eauto.
      inversion TREE1; inversion SKIP; subst. destruct plus. discriminate.
      clear SKIP.
      destruct greedy; simpl in LEAVES.
      (* greedy*)
      apply in_app_or in LEAVES as [LEAVES | LEAVES]; try inversion LEAVES; try inversion H; auto.
      specialize (is_tree_productivity rer [Areg r] inp (GroupMap.reset (def_groups r) gm) dir) as [t3 TREE3].
    rewrite app_cons in ISTREE1. eapply leaves_concat with (act1:= [Areg r]) in ISTREE1; eauto.
      pose proof (act_from_leaf_determ rer [Acheck inp; Areg (Quantified true 0 +∞ r)] dir) as R2determ.
      pose proof (In_FlatMap _  _  _ _  R2determ ISTREE1 LEAVES) as [lf [l0 [Inlf [act Inlp]]]]. 
      destruct lf as [inp3 gm3].
      inversion act; subst. inversion TREE; subst. simpl in *.
      Search StrictSuffix.strict_suffix.
      specialize (strict_suffix_remaining_length _ _ _ PROGRESS) as dd.
      specialize (IHr _ _ _ _ _ _ GROUPEMPT TREE3 Inlf).
      assert (remaining_length inp3 dir <= l). 
      rewrite eq in dd. rewrite <- GroupId.lt_succ_r. assumption.
      specialize (IHl _ _ _ _ _ _  TREECONT Inlp H). subst. rewrite GROUPEMPT. reflexivity. inversion act; subst.
      (*Case where mismatch*)
      simpl in *. inversion act; subst.
      contradiction.
      (*nongreedy*)
      destruct  LEAVES as [LEAVES | LEAVES]; try inversion LEAVES; try inversion H; auto.
      specialize (is_tree_productivity rer [Areg r] inp (GroupMap.reset (def_groups r) gm) dir) as [t3 TREE3].
      rewrite app_cons in ISTREE1. eapply leaves_concat with (act1:= [Areg r]) in ISTREE1; eauto.
      pose proof (act_from_leaf_determ rer [Acheck inp; Areg (Quantified false 0 +∞ r)] dir) as R2determ.
      pose proof (In_FlatMap _  _  _ _  R2determ ISTREE1 LEAVES) as [lf [l0 [Inlf [act Inlp]]]]. 
      destruct lf as [inp3 gm3].
      inversion act; subst. inversion TREE; subst. simpl in *.
      Search StrictSuffix.strict_suffix.
      specialize (strict_suffix_remaining_length _ _ _ PROGRESS) as dd.
      specialize (IHr _ _ _ _ _ _ GROUPEMPT TREE3 Inlf).
      assert (remaining_length inp3 dir <= l). 
      rewrite eq in dd. rewrite <- GroupId.lt_succ_r. assumption.
      specialize (IHl _ _ _ _ _ _  TREECONT Inlp H). subst. rewrite GROUPEMPT. reflexivity. inversion act; subst.
      (*Case where mismatch*)
      simpl in *. inversion act; subst.
      contradiction.
  Qed.

        

 
  Lemma input_only_forward:
    forall l t gm gm1 gm2 inp1 inp2 dir,
      is_tree rer l inp1 gm dir t ->
      In (inp2, gm2) (tree_leaves t gm1 inp1 dir) ->
      inp1 = inp2 \/ StrictSuffix.strict_suffix inp2 inp1 dir.
  Proof.
    intros acts. intros t gm gm1 gm2 inp1 inp2 d. revert t gm gm1 gm2 inp1 inp2.
    induction acts; intros t g1 g3 g2 i1 i2 T1 I1.
    + inversion T1; subst. simpl in I1. inversion  I1. inversion H. auto. contradiction.
    + destruct a.
      2: {
        inversion T1; subst.
        simpl in I1. eapply IHacts with (inp1 := i1) (inp2 := i2); eauto.
        simpl in I1. contradiction.
      }
      2: {
        inversion T1; subst. simpl in I1.
        eapply IHacts with (inp1 := i1) (inp2 := i2); eauto.
      }
      revert acts t g1 g2 g3 i1 i2 d T1 I1  IHacts.
      induction r; intros acts  t g1 g2 g3 i1 i2 d T1 I1 IHacts.
      1: inversion T1; eapply IHacts; eauto.
      1: {
        inversion T1; subst; simpl in I1.
        unfold advance_input' in I1.
        apply read_char_success_advance in READ.
        rewrite READ in I1.
        eapply StrictSuffix.ss_advance in READ.
        assert (nextinp = i2 \/ StrictSuffix.strict_suffix i2 nextinp d) as [c1 | c2].
        eapply IHacts; eauto.
        subst. right. assumption.
        right. eapply StrictSuffix.strict_suffix_trans; eauto.
        contradiction.
      }
      1: {
        inversion T1; subst; simpl in I1. apply in_app_or in I1 as [c1 | c2].
        eapply IHr1; eauto.
        eapply IHr2; eauto.
      }
      1: {
        inversion T1; destruct d; simpl in CONT.
        eapply IHr1 with (acts:= Areg r2 :: acts); eauto.
        eapply IHr2 with (acts:= Areg r1 :: acts); eauto.
      }
      3: {
        inversion T1; subst. eapply (IHr (Aclose id :: acts)); eauto.
        intros. inversion H; subst. eapply IHacts; eauto.
      }
      3: {
        inversion T1; subst. eapply IHacts; eauto. inversion I1.
      }
      3: {
        inversion T1; subst; clear T1.
        simpl in I1.  apply read_backref_success_advance in READ_BACKREF. rewrite <- READ_BACKREF in I1.
        assert (nextinp = i2 \/ StrictSuffix.strict_suffix i2 nextinp d) as [c1 | c2]. eapply IHacts; eauto.
        apply advance_input_n_suffix in READ_BACKREF as [p1 | p2].
        all: subst. left; reflexivity.
        right; assumption.
        remember (advance_input_n i1 (length br_str) d) as tip.
        apply advance_input_n_suffix in Heqtip as [p1 | p2].
        subst. right; assumption. right.
        eapply StrictSuffix.strict_suffix_trans; eauto.
        inversion I1.
      }
      2: {
        inversion T1; subst. simpl in I1. 2: inversion I1.
        destruct (positivity lk), (tree_leaves treelk g3 i1 (lk_dir lk)); try inversion I1.
        destruct l.
        all: eapply IHacts; eauto.       
      }
      revert t g1 g2 g3 i1 i2 T1 I1.
      (*induction on min*)
      induction min.
      2: {intros  t  g1 g2 g3 i1 i2  T1 I1. inversion T1; subst. eapply IHr with (acts:= Areg (Quantified greedy min delta r) :: acts); eauto.}
      destruct delta.
      (*induction*)
      induction n; intros t  g1 g2 g3 i1 i2 T1 I1.  
      (*case 0*)
      inversion T1; subst. eapply IHacts ; eauto.
      destruct plus; discriminate.
      (*case n + 1*)
      inversion T1. destruct plus. 2: discriminate.
      inversion H1; subst.
      destruct greedy; simpl in *.
      (* greedy *)
      apply in_app_or in I1 as [c1 | c2].
      2: eapply IHacts; eauto.
      eapply IHr with (acts := Acheck i1 :: Areg (Quantified true 0 (NoI.N n) r) :: acts); eauto.
      intros. inversion H; subst.
      2: inversion H0.
      eapply IHn; eauto.
      (* non greedy*)
      apply in_app_or in I1 as [c1 | c2].
      eapply IHacts; eauto.
      eapply IHr with (acts := Acheck i1 :: Areg (Quantified false 0 (NoI.N n) r) :: acts); eauto.
      intros. inversion H; subst.
      2: inversion H0.
      eapply IHn; eauto.
      (* infinite *)
      intros  t g1 g2 g3 i1 i2  T1 I1.  
      remember (remaining_length i1 d) as l.
      assert (Hlength_le: remaining_length i1 d <= l) by lia. clear Heql.
      generalize dependent i1. revert g1 g2 g3 i2 t.
      induction l; intros g1 g2 g3 i2  t i1 T1 I1 Hlength_le.
      inversion T1; subst.
      assert (NL: actions_no_leaves rer (Areg r :: Acheck i1 :: Areg (Quantified greedy 0 plus r) :: acts) d). {
        apply actions_no_leaves_add_left with (a := [Areg r]).
        apply actions_no_leaves_add_right with (a:=  [Acheck i1]) (b := Areg (Quantified greedy 0 plus r) :: acts).
        apply check_end_no_leaves. lia.
      }
      destruct plus. discriminate.
      destruct greedy; simpl in *.
      apply in_app_or in I1 as [c1 | c2].  
      specialize (NL _ _ _ ISTREE1).
      apply leaves_indep with (gm2 := (GroupMap.reset (def_groups r) g3)) (inp2:= i1) (dir2:= d) in NL.
      rewrite NL in c1. inversion c1.
      eapply IHacts; eauto.
      apply in_app_or in I1 as [c1 | c2].
      eapply IHacts; eauto.
      specialize (NL _ _ _ ISTREE1).
      apply leaves_indep with (gm2 := (GroupMap.reset (def_groups r) g3)) (inp2:= i1) (dir2:= d) in NL.
      rewrite NL in c2. inversion c2.
      (*IH*)
      apply GroupId.le_lteq in Hlength_le as [leq | eq].
      eapply IHl; eauto. lia.
      inversion T1; subst. destruct plus. discriminate.
      destruct greedy; simpl in *.
      apply in_app_or in I1 as [c1 | c2].
      2: eapply IHacts; eauto.
      eapply IHr with (acts := Acheck i1 :: Areg (Quantified true 0 +∞ r) :: acts); eauto.
      intros. inversion H; subst. 2: inversion H0.
      simpl in H0. eapply IHl; eauto. 
      apply strict_suffix_remaining_length in PROGRESS.
      lia.
      apply in_app_or in I1 as [c1 | c2].
      eapply IHacts; eauto.
      eapply IHr with (acts := Acheck i1 :: Areg (Quantified false 0 +∞ r) :: acts); eauto.
      intros. inversion H; subst. 2: inversion H0.
      simpl in H0. eapply IHl; eauto. 
      apply strict_suffix_remaining_length in PROGRESS.
      lia.
  Qed.
      
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


  (* after check this only works with an unamb case *)
  Lemma check_not_stops_quantifier n:
    forall r1 inp gm dir t1 t2,
      def_groups r1 = [] ->
      unamb [Areg r1] ->
      is_tree rer [Areg r1; Acheck inp; Areg (Quantified true 0 n r1)] inp gm dir t1 ->
      is_tree rer [Areg r1; Areg (Quantified true 0 n r1)] inp gm dir t2 ->
      leaves_equiv [] (tree_leaves t1 gm inp dir ++ [(inp, gm)]) (tree_leaves t2 gm inp dir ++ [(inp, gm)]).
  Proof.
    intros r1 inp gm dir t1 t2 UNDEFGROUPS UNAMBR TREE1 TREE2.
    specialize (is_tree_productivity rer [Areg r1] inp gm dir) as [t3 TREE3].
    rewrite app_cons in TREE1, TREE2.
    eapply leaves_concat with (act1 := [Areg r1]) in TREE1, TREE2; eauto.
    destruct (tree_leaves t3 gm inp dir) as [| [inp2 gm2] l] eqn: Ln.
    (* Case 1: list is empty*)
    inversion TREE1; inversion TREE2; subst. reflexivity.
    destruct l.
    (* Case 2: length of list > 2 (non unambigous)*)
    2: { specialize (UNAMBR inp gm dir t3 TREE3 gm inp dir). rewrite Ln in UNAMBR. simpl in UNAMBR. lia. }
    (* Case 3: length of list = a *)
    apply FlatMap_one_leaf in TREE2, TREE1.
    inversion TREE2; inversion TREE1; inversion TREE0.
    (* Case 3.1: progress *)
    subst; simpl in *.
    clear TREE1 TREE2 TREE0. rewrite app_cons. etransitivity. clear H3 H7 t1.
    2: { rewrite app_cons. reflexivity. }
    apply leaves_equiv_app. 2: reflexivity. clear Ln PROGRESS.
    revert inp2 gm2 treecont t TREECONT TREE.
    change (actions_equiv_dir rer dir [Areg (Quantified true 0 n r1)] [Areg (Quantified true 0 n r1)]). reflexivity.
    (* Case 3.2: Mismatch *)
    clear TREE2 TREE1 H3. subst; simpl in *.
    assert (dd: In (inp2, gm2) (tree_leaves t3 gm inp dir)).
    rewrite Ln; simpl; left; auto.
    pose proof (undefgroup_is_imm _ _ _ _  _ _ _ UNDEFGROUPS TREE3 dd).
    pose proof (input_does_not_back _ _ _ _ _ _ _ TREE3 dd CHECKFAIL).
    inversion TREE; subst. inversion SKIP; subst; auto. simpl. leaves_equiv_t.
    rewrite UNDEFGROUPS; rewrite UNDEFGROUPS in ISTREE1, TREE; inversion SKIP; subst; simpl in *.
    clear SKIP TREE.
    rewrite app_cons in ISTREE1.
    eapply leaves_concat with (act1 := [Areg r1]) in ISTREE1; eauto.
    rewrite Ln in ISTREE1. apply FlatMap_one_leaf in ISTREE1. inversion ISTREE1; subst.
    inversion TREE; subst. simpl in PROGRESS. contradiction. leaves_equiv_t.
  Qed.
    
  (* you can transform a quantifier into a easier one. *)
  Theorem greedy_quantifier_steps_opt:
    forall r n,
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
    inversion H1. subst. eapply check_not_stops_quantifier; eauto.
    inversion H1. subst. eapply check_not_stops_quantifier; eauto.
  Qed.
  

  Theorem unamb_quantifier_pops_left:
    forall r  m n,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified true (S m) n r)
        ≅[rer] Sequence (Quantified true 1 (NoI.N 0) r) (Quantified true m n r).
  Proof.
    intros r m n GROUPEMPT UNAMBR dir.
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
    + (* Base case: n = 0*)
      symmetry.
      (*r{1, 0} r{0, 0}*)
      etransitivity. {
        apply seq_equiv. reflexivity. apply quantified_zero_equiv. assumption.
      }
      (*r{1, 0} Epsilon*)
      apply (sequence_epsilon_right_equiv rer ).
    + (* Inductive case: (S n)*)
      (* r{1, delta1 + 1}*)
      rewrite quantified_S_equiv_backward; auto.
      (* r{0, delta1 + 1}r{1, 0}*)

      (* Greedy case *)
      etransitivity. { eapply seq_equiv. apply greedy_quantifier_steps_opt. 3: apply quantified_one_equiv. all: auto. }
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
    + etransitivity.
          2: {
            apply seq_equiv.  rewrite quantified_one_equiv. reflexivity. assumption. reflexivity.
          }
          etransitivity. {
            rewrite  quantified_S_equiv_backward. apply seq_equiv_dir. reflexivity. apply quantified_one_equiv. all: assumption.
          }
          split. simpl; rewrite GROUPEMPT. reflexivity.
          intros i g t1 t2 TREE1 TREE2.
          remember (remaining_length i backward) as l.
          assert (Hlength_le: remaining_length i backward <= l) by lia. clear Heql.
          generalize dependent i. revert g t1 t2.
          induction l; intros g t1 t2 i TREE1 TREE2 Hlength_le. 
          inversion TREE2; inversion CONT. subst. simpl in *.
          unfold tree_equiv_tr_dir.
          assert (NL2: actions_no_leaves rer [Areg r; Acheck i; Areg (Quantified true 0 plus r); Areg r] backward). {
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
          assert (remaining_length (fst el) backward <= 0).
          assert (el = (fst el, snd el) \/ False). left. destruct el. reflexivity.
          specialize  (input_only_forward _ _ _ g  (snd el) _  (fst el)  _ SKIP) as iforward. rewrite elList in iforward. simpl in iforward.
          specialize (iforward H) as [c1 | c2].
          subst. assumption.
          specialize (strict_suffix_remaining_length _ _ _ c2) as p. lia.
          inversion TREE; subst.
          assert (NL2: actions_no_leaves rer [Areg r; Acheck (fst el); Areg (Quantified true 0 plus0 r)] backward). {
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
          assert (remaining_length i0 backward <= l) by lia.
          unfold tree_equiv_tr_dir in IHl. simpl in H3; rewrite <- H3.
          rewrite GROUPEMPT in ISTREE1; simpl in ISTREE1.
          specialize (is_tree_productivity rer [Areg r; Areg (Quantified true 0  +∞ r)] i0 g0 backward) as [t5 T5].
          specialize (check_not_stops_quantifier _ _ _ _ _ _ _ GROUPEMPT UNAMBR ISTREE1 T5) as tEq2.
           eapply leaves_equiv_trans. apply tEq2. 
           apply leaves_equiv_app. eapply IHl; eauto; constructor; assumption.
           reflexivity.
           rewrite <- H3. simpl.
           assert (i = i0). {
             assert (In (i0, g0) (tree_leaves tskip g i backward)) as inSKIP.
             rewrite elList. constructor. reflexivity.
             specialize (input_only_forward _ _ _ g g0 _ i0 _ SKIP inSKIP ) as [c1 | c2].
             assumption. contradiction.
           }
           assert (g = g0). {
             assert (In (i0, g0) (tree_leaves tskip g i backward)) as inSKIP.
             rewrite elList. constructor. reflexivity.
             exact (undefgroup_is_imm _ _ _ _ _ _ _ GROUPEMPT SKIP inSKIP).
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

     


  Theorem unamb_quantifier_pops_right:
    forall r m n,
      def_groups r = [] ->
      unamb [Areg r] ->
      (Quantified true (S m) n r)
        ≅[rer] Sequence (Quantified true m n r) (Quantified true 1 (NoI.N 0) r).
    Proof.
      intros r m n GROUPEMPT UNAMBR dir.
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
        + (* Infinity case*)
          etransitivity.
          2: {
            apply seq_equiv. reflexivity. rewrite quantified_one_equiv. reflexivity. assumption.
          }
          etransitivity. {
            rewrite  quantified_S_equiv_forward. apply seq_equiv_dir. apply quantified_one_equiv. 2: reflexivity. all: assumption.
          }
          split. simpl; rewrite GROUPEMPT. reflexivity.
          intros i g t1 t2 TREE1 TREE2.
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
          specialize (check_not_stops_quantifier _ _ _ _ _ _ _ GROUPEMPT UNAMBR ISTREE1 T5) as tEq2.
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
             exact (undefgroup_is_imm _ _ _ _ _ _ _ GROUPEMPT SKIP inSKIP).
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
           
   Lemma unamb_quantifier_invertible:
        forall r m n,
          def_groups r = [] ->
          unamb [Areg r] ->
          Sequence (Quantified true 1 (NoI.N 0) r) (Quantified true m n r) ≅[rer] Sequence (Quantified true m n r) (Quantified true 1 (NoI.N 0) r).
      Proof.
        intros r m n GROUPEMPT UNAMBR.
        rewrite <- unamb_quantifier_pops_left.
        rewrite unamb_quantifier_pops_right.
        reflexivity.
        all: assumption.
      Qed.


                   

  (* Intermediate step: r{0, delta1}r{min2, delta2} = r{min2, delta1 + delta2}*)
      Theorem unamb_equivalence_chain_I1:
        forall r min2 delta1 delta2,
          def_groups r = [] -> 
          (* if the tree corresponding to the regex is unambigous *)
          unamb [Areg r] ->
          (* r{0, Delta1, g } *)
          (Sequence (Quantified true 0 delta1 r)
             (* r{min2, Delta2, g } *)
             (Quantified true min2 delta2 r))
            ≅[rer] (Quantified true min2 (delta1 + delta2)%NoI r).
      Proof.
        intros reg min2 delta1 delta2 GROUPEMPT UNAMBR.
        induction min2.
        (* Base case: done in previous proof*)
        - eapply atmost_atmost_equiv; eauto.
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
          rewrite <- unamb_quantifier_pops_right; try assumption.
          (* r{min2 + 1, delta1 + delta2} *)
          reflexivity.
      Qed.

      
    (* Final statement: if a tree is unambigous then the two chains correspond *)
    Theorem unamb_equivalence_chain:
        forall r min1 min2 delta1 delta2,
          def_groups r = [] -> 
          (* if the tree corresponding to the regex is unambigous *)
          unamb [Areg r] ->
          (* r{min1, Delta1, g } *)
          (Sequence (Quantified true min1 delta1 r)
             (* r{min2, Delta2, g } *)
             (Quantified true min2 delta2 r))
            ≅[rer] (Quantified true (min1 + min2) (delta1 + delta2)%NoI r).
      Proof.
        intros r min1 min2 Delta1 Delta2  GROUPEMPT UNAMBR.
        induction min1.
        (* Base case: done in an adjacent proof*)
        - apply unamb_equivalence_chain_I1; assumption.
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
            apply IHmin1.
          }
          (* r{1,0} (r{min1 + min2, delta1 + delta2}) using IH*)
          rewrite <- unamb_quantifier_pops_left; try assumption.
          (* r{min1 + min2 + 1, delta1 + delta2} *)
          reflexivity.
      Qed.

      
      (* Same as above only this time in respect to the function *)
      Corollary unamb_fun_equivalence_chain:
        forall r min1 min2 delta1 delta2,
          def_groups r = [] -> 
          (* if the tree corresponding to the regex is unambigous *)
          na r = true ->
          (* r{min1, Delta1, g } *)
          (Sequence (Quantified true min1 delta1 r)
             (* r{min2, Delta2, g } *)
             (Quantified true min2 delta2 r))
            ≅[rer] (Quantified true (min1 + min2) (delta1 + delta2)%NoI r).
      Proof.
        intros r min1 min2 delta1 delta2 GROUPEMPT NATRUE.
        (* just translate the original statement to the function*)
        apply unamb_equivalence_chain; try apply naive_unambiguity; auto.
      Qed.
           
End UnAmbiguity.

