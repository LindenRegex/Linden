From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import Examples FlatMap ForcedQuant Associativity.

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
