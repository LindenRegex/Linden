From Linden Require Import Semantics FunctionalSemantics Chars StrictSuffix Parameters.
From Warblre Require Import Parameters Base RegExpRecord.
From Stdlib Require Import Lia List.

(** * Proving that the functional version of the semantics, compute_tree,
yields trees that respect the inductive semantics *)

Section ComputeIsTree.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Theorem compute_is_tree:
    forall act inp gm dir fuel t,
      compute_tree rer act inp gm dir fuel = Some t ->
      is_tree rer act inp gm dir t.
  Proof.
    intros act inp gm dir fuel. revert act inp gm dir. induction fuel as [|fuel IHfuel]; try discriminate.

    intros act inp gm dir t. simpl.
    destruct act as [|[reg | inpcheck | gid] acts].
    1: {
      intros H. injection H as <-. apply tree_match.
    }

    1: destruct reg as [ | cd | r1 r2 | r1 r2 | greedy min delta r | lk r | gid r | a | gid].

    - (* Empty *)
      intros H. apply tree_epsilon. apply IHfuel; auto.

    - (* Char *)
      destruct Chars.read_char as [[c nextinp]|] eqn:Hreadchar.
      + destruct (compute_tree rer acts nextinp gm dir fuel) as [treecont|] eqn:Hcomputecont; try discriminate.
        intros H. injection H as <-.
        apply tree_char with (nextinp := nextinp); auto.
      + intros H. injection H as <-.
        apply tree_char_fail. auto.

    - (* Disjunction *)
      destruct compute_tree as [t1|] eqn:Hcompute1; try discriminate.
      destruct (compute_tree rer (Areg r2 :: acts)%list inp gm dir fuel) as [t2|] eqn:Hcompute2; try discriminate.
      intros H. injection H as <-.
      apply tree_disj; apply IHfuel; auto.

    - (* Sequence *)
      intros Hcompsucc. apply tree_sequence; apply IHfuel; auto.

    - (* Quantified *)
      destruct min as [|min'].
      1: destruct delta as [[|n']|].
      + (* Done *)
        intros Hcomputesucc. apply tree_quant_done; apply IHfuel; auto.
      + (* Free, finite delta *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        destruct (compute_tree rer acts inp gm dir fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
        intros H. injection H as <-.
        change (Numeric.NoI.N (S n')) with (Numeric.NoI.add (Numeric.NoI.N 1) (Numeric.NoI.N n')).
        eapply tree_quant_free with (titer := titer) (tskip := tskip).
        * reflexivity.
        * apply IHfuel.
          simpl in Hiter. replace (n' - 0) with n' in Hiter by lia. auto.
        * apply IHfuel; auto.
        * reflexivity.
      + (* Free, infinite delta *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        destruct (compute_tree rer acts inp gm dir fuel) as [tskip|] eqn:Hskip; simpl; try discriminate.
        intros H. injection H as <-.
        change Numeric.NoI.Inf with (Numeric.NoI.add (Numeric.NoI.N 1) Numeric.NoI.Inf).
        eapply tree_quant_free with (titer := titer) (tskip := tskip).
        * reflexivity.
        * apply IHfuel. simpl in Hiter. auto.
        * apply IHfuel; auto.
        * reflexivity.
      + (* Forced *)
        destruct compute_tree as [titer|] eqn:Hiter; simpl; try discriminate.
        intros H. injection H as <-.
        apply tree_quant_forced; auto.

    - (* Lookaround *)
      destruct compute_tree as [treelk|] eqn:Htreelk; simpl; try discriminate.
      destruct (lk_result lk treelk gm inp) eqn:LKRES.
      + (* Lookaround succeds *)
        destruct (compute_tree rer acts inp g dir fuel) as [treecont|] eqn:Hcomputecont; try discriminate.
        intros H. injection H as <-.
        apply tree_lk with (gmlk := g); auto.
      + (* Lookaround fails *)
        intros H. injection H as <-.
        apply tree_lk_fail; auto.

    - (* Group *)
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intros H. injection H as <-.
      apply tree_group. auto.

    - (* Anchor *)
      destruct anchor_satisfied eqn:Hanchor.
      + (* Anchor is satisfied *)
        destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
        intros H. injection H as <-.
        apply tree_anchor; auto.
      + (* Anchor is not satisfied *)
        intros H. injection H as <-.
        apply tree_anchor_fail; auto.

    - (* Backreference *)
      destruct read_backref as [[br_str nextinp]|] eqn:Hreadbr.
      + (* Success *)
        destruct compute_tree as [tcont|] eqn:Htcont; try discriminate.
        intros H. injection H as <-.
        apply tree_backref with (nextinp := nextinp); auto.
      + (* Failure *)
        intro H. injection H as <-.
        auto using tree_backref_fail.

    - (* Check *)
      destruct is_strict_suffix eqn:Hssuffix.
      + (* Is strict suffix *)
        destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
        intros H. injection H as <-.
        apply tree_check; auto.
        (* follows from Hssuffix *) apply is_strict_suffix_correct in Hssuffix. eauto using ss_neq.
      + (* Is not strict suffix *)
        intros H. injection H as <-.
        apply tree_check_fail. (* Now follows from Hvalidchecks and Hssuffix! *)
        apply is_strict_suffix_inv_false. auto.


    - (* Close *)
      destruct compute_tree as [treecont|] eqn:Htreecont; try discriminate.
      intros H. injection H as <-.
      apply tree_close. apply IHfuel; auto.
  Qed.

End ComputeIsTree.
