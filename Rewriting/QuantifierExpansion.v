From Linden Require Import ProofSetup.
From Linden.Rewriting Require Import FlatMap RegexpTree Examples.

(** * Expanding quantifiers *)

(* In this file, we expand away counted quantifiers, such that we can use an
   engine that does not support them natively.
   Most expansions are already present in RegExpTree.v, but we need more.  *)

Section QuantifierExpansion.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (** * Lazy Optional Quantifiers *)
  (* Those can't be directly expanded with a simple sequence, we have proved that this does not maintain priority.
     Instead, we expand them into disjunction with epsilon.
     When iterating, we also need to use `r{0,1}` as a way to force a progress check around `r`.
     This expansion will make the NFA compiler produce some non-optimal bytecode, with too many forks,
     but allows to keep the native subset supported by the engine quite small. *)

  (* Note that this trick only works in the forward direction. *)

  (* leaves of r{0,k}? are included in those of r{0,k+1}? *)
  Lemma lazy_atmost_leaves_incl k r:
    forall inp gm dir tk tk1,
      is_tree rer [Areg (Quantified false 0 (NoI.N k) r)] inp gm dir tk ->
      is_tree rer [Areg (Quantified false 0 (NoI.N (S k)) r)] inp gm dir tk1 ->
      incl (tree_leaves tk gm inp dir) (tree_leaves tk1 gm inp dir).
  Proof.
    induction k as [|k IHk]; intros inp gm dir tk tk1 TREEk TREEk1.
    - inversion TREEk; subst. 2: { destruct plus; discriminate. }
      inversion SKIP; inversion TREEk1; inversion SKIP0; subst. simpl.
      intros lf [<- | []]. left. auto.
    - inversion TREEk; inversion TREEk1; subst.
      assert (plus = NoI.N k) as -> by (destruct plus; try discriminate; injection H1 as ->; reflexivity).
      assert (plus0 = NoI.N (S k)) as -> by (destruct plus0; try discriminate; injection H9 as ->; reflexivity).
      clear H1 H9. inversion SKIP; inversion SKIP0; subst. simpl.
      specialize (@compute_tr_is_tree _ rer [Areg r; Acheck inp] inp (GroupMap.reset (def_groups r) gm) dir) as TREErcheck.
      pose proof leaves_concat rer _ _ _ [Areg r; Acheck inp] [Areg (Quantified false 0 (NoI.N k) r)] _ _ ISTREE1 TREErcheck as CONCAT.
      pose proof leaves_concat rer _ _ _ [Areg r; Acheck inp] [Areg (Quantified false 0 (NoI.N (S k)) r)] _ _ ISTREE0 TREErcheck as CONCAT0.
      intros lf [<- | Hin]. { left. auto. }
      right. eapply (flatmap_incl _ _ _ _ _ CONCAT CONCAT0); eauto.
      unfold funct_incl. intros a l1 l2 ACT1 ACT2.
      inversion ACT1; inversion ACT2; subst. apply IHk; auto.
  Qed.

  (* expansion of lazy optional iterations *)
  (* r{0,k+1}? ≅[forward] epsilon | (?: r? r{0,k}?) *)
  Theorem lazy_atmost_expand k r:
    Quantified false 0 (NoI.N (S k)) r ≅[rer][forward]
      Disjunction Epsilon (Sequence (Quantified true 0 (NoI.N 1) r) (Quantified false 0 (NoI.N k) r)).
  Proof.
    split. 1: { simpl. solve_groups_equiv. }
    intros inp gm t1 t2 TREE1 TREE2.
    pose proof TREE1 as TREE1'.
    inversion TREE1; subst. rename ISTREE1 into ITER1, SKIP into SKIP1.
    assert (plus = NoI.N k) as -> by (destruct plus; try discriminate; injection H1 as ->; reflexivity).
    clear H1. inversion SKIP1; subst.
    inversion TREE2; subst. rename ISTREE1 into TEPS, ISTREE2 into TSEQ.
    inversion TEPS; subst. rename ISTREE into TNIL. inversion TNIL; subst.
    inversion TSEQ; subst. simpl in CONT. inversion CONT; subst.
    rename ISTREE1 into ITER2, SKIP into SKIP2.
    assert (plus = NoI.N 0) as -> by (destruct plus; try discriminate; injection H1 as ->; reflexivity).
    clear H1.
    pose proof (lazy_atmost_leaves_incl k r inp gm forward _ _ SKIP2 TREE1') as INCL.
    assert (EQUIV: leaves_equiv []
      (tree_leaves titer (GroupMap.reset (def_groups r) gm) inp forward)
      (tree_leaves titer0 (GroupMap.reset (def_groups r) gm) inp forward)). {
      clear - ITER1 ITER2.
      remember (GroupMap.reset (def_groups r) gm) as gm'. clear Heqgm'.
      remember inp as inp' in ITER1 at 1, ITER2 at 1. clear Heqinp'.
      revert inp gm' titer titer0 ITER1 ITER2.
      change (actions_equiv_dir rer forward ([Areg r; Acheck inp'] ++ [Areg (Quantified false 0 (NoI.N k) r)])
        ([Areg r; Acheck inp'] ++ [Areg (Quantified true 0 (NoI.N 0) r); Areg (Quantified false 0 (NoI.N k) r)])).
      apply app_eq_left.
      intros i gm'' ta tb TA TB. inversion TB; subst. 2: { destruct plus; discriminate. }
      replace tb with ta by eauto using is_tree_determ. reflexivity.
    }
    unfold tree_equiv_tr_dir. simpl in *.
    symmetry. rewrite app_comm_cons. apply leaves_equiv_incl'; auto.
    apply leaves_equiv_app with (p1 := [(inp, gm)]) (p2 := [(inp, gm)]). { reflexivity. }
    symmetry. auto.
  Qed.


  (* we can then recursively expand any r{0,k}?
     until we use only r{0,1} and r{0,0} quantifiers *)
  Fixpoint expand_lazy_atmost (k: nat) (r: regex) : regex :=
    match k with
    | 0 => Quantified false 0 (NoI.N 0) r
    | S k' => Disjunction Epsilon (Sequence (Quantified true 0 (NoI.N 1) r) (expand_lazy_atmost k' r))
    end.

  Theorem expand_lazy_atmost_equiv k r:
    Quantified false 0 (NoI.N k) r ≅[rer][forward] expand_lazy_atmost k r.
  Proof.
    induction k as [|k IHk]; simpl.
    - reflexivity.
    - etransitivity. 1: apply lazy_atmost_expand.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionL Epsilon (CSequenceL (Quantified true 0 (NoI.N 1) r) CHole)); auto.
  Qed.

  (** * Greedy Optional Quantifier  *)
  (* this simply recursively applies an existing quantifier rewrite *)

  Fixpoint expand_greedy_atmost (k: nat) (r: regex) : regex :=
    match k with
    | 0 => Quantified true 0 (NoI.N 0) r
    | S k' => Sequence (Quantified true 0 (NoI.N 1) r) (expand_greedy_atmost k' r)
    end.

  Theorem expand_greedy_atmost_equiv k r:
    Quantified true 0 (NoI.N k) r ≅[rer] expand_greedy_atmost k r.
  Proof.
    induction k as [|k IHk]; simpl; intro dir.
    - reflexivity.
    - etransitivity. 1: { symmetry. apply (atmost_atmost_equiv rer (NoI.N 1) (NoI.N k) r). }
      apply regex_equiv_ctx_samedir with (ctx := CSequenceL (Quantified true 0 (NoI.N 1) r) CHole); auto.
  Qed.

  (** * Forced iterations *)
  (* similarly, we use existing rewrites to peel off forced iterations *)

  (* r{n,Δ} ≅[forward] r{1} r{1} ... r{1} r{0,Δ} *)
  Fixpoint expand_forced (n: nat) (greedy: bool) (delta: non_neg_integer_or_inf) (r: regex) : regex :=
    match n with
    | 0 => Quantified greedy 0 delta r
    | S n' => Sequence (Quantified greedy 1 (NoI.N 0) r) (expand_forced n' greedy delta r)
    end.

  Theorem expand_forced_equiv n greedy delta r:
    Quantified greedy n delta r ≅[rer][forward] expand_forced n greedy delta r.
  Proof.
    induction n as [|n IHn]; simpl.
    - reflexivity.
    - etransitivity. 1: apply quantified_S_equiv_forward.
      eapply regex_equiv_ctx_samedir with (ctx := CSequenceL (Quantified greedy 1 (NoI.N 0) r) CHole); auto.
  Qed.


  (** * Full Transformation  *)
  (* here, we expand away all non-supported quantifiers *)

  (* forced iterations become r{1}, then the remaining free iterations r{0,Δ}
     become r{0,1} and r{0,0} when Δ is finite. *)
  Fixpoint expand_counted (greedy: bool) (min: nat) (delta: non_neg_integer_or_inf) (r: regex) : regex :=
    match min with
    | S n => Sequence (Quantified greedy 1 (NoI.N 0) r) (expand_counted greedy n delta r)
    | 0 =>
        match delta with
        | NoI.N k => if greedy then expand_greedy_atmost k r else expand_lazy_atmost k r
        | NoI.Inf => Quantified greedy 0 NoI.Inf r
        end
    end.

  (* genealized to regexes *)
  Fixpoint expand_quant (r: regex) : regex :=
    match r with
    | Epsilon | Character _ | Anchor _ | Backreference _ | Lookaround _ _ => r
    | Disjunction r1 r2 => Disjunction (expand_quant r1) (expand_quant r2)
    | Sequence r1 r2 => Sequence (expand_quant r1) (expand_quant r2)
    | Group gid r1 => Group gid (expand_quant r1)
    | Quantified greedy min delta r1 => expand_counted greedy min delta (expand_quant r1)
    end.

  Theorem expand_counted_equiv greedy min delta r:
    Quantified greedy min delta r ≅[rer][forward] expand_counted greedy min delta r.
  Proof.
    induction min as [|n IHn]; simpl.
    - destruct delta as [k|]; [destruct greedy|].
      + apply expand_greedy_atmost_equiv.
      + apply expand_lazy_atmost_equiv.
      + reflexivity.
    - etransitivity. { apply quantified_S_equiv_forward. }
      apply regex_equiv_ctx_samedir with (ctx := CSequenceL (Quantified greedy 1 (NoI.N 0) r) CHole); auto.
  Qed.

  Theorem expand_quant_equiv r:
    r ≅[rer][forward] expand_quant r.
  Proof.
    induction r; simpl; try reflexivity.
    - transitivity (Disjunction (expand_quant r1) r2).
      + apply regex_equiv_ctx_samedir with (ctx := CDisjunctionR CHole r2); auto.
      + apply regex_equiv_ctx_samedir with (ctx := CDisjunctionL (expand_quant r1) CHole); auto.
    - apply seq_equiv_dir; auto.
    - transitivity (Quantified greedy min delta (expand_quant r)).
      + apply regex_equiv_quant. auto.
      + apply expand_counted_equiv.
    - apply regex_equiv_ctx_samedir with (ctx := CGroup id CHole); auto.
  Qed.

  Lemma expand_lazy_prefix_equiv r:
    lazy_prefix r ≅[rer][forward] lazy_prefix (expand_quant r).
  Proof.
    unfold lazy_prefix.
    apply regex_equiv_ctx_samedir with (ctx := CSequenceL dot_star CHole); auto.
    apply expand_quant_equiv.
  Qed.

End QuantifierExpansion.
