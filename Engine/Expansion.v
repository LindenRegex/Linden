(** * Expanding quantifiers *)

(* Thanks to our rewriting proofs, we can support many features,
   such as quantifiers, using an engine which does not support them,
   by expanding these features away. *)

From Linden Require Import Regex Parameters PikeSubset.
From Linden.Rewriting Require Import QuantifierExpansion.
From Warblre Require Import Numeric Base.
From Linden Require Import Chars Groups Tree Semantics FunctionalUtils.
From Linden Require Import NFA PikeVM SeenSets Correctness.
From Linden Require Import Prefix MemoBT EquivMain RegexpTranslation ResultTranslation LWParameters.
From Linden.Rewriting Require Import Equivalence.
From Warblre Require Import RegExpRecord Semantics Result StaticSemantics.
Import Result.Notations.
Local Open Scope result_flow.
From Stdlib Require Import List.
Import ListNotations.

Section Expansion.
  Context {params: LindenParameters}.

  (** * Source subset *)
  (* The pike_subset, extended with all quantifiers *)
  Inductive source_regex : regex -> Prop :=
  | src_eps:
    source_regex Epsilon
  | src_char:
    forall cd, source_regex (Regex.Character cd)
  | src_disj:
    forall r1 r2,
      source_regex r1 ->
      source_regex r2 ->
      source_regex (Disjunction r1 r2)
  | src_seq:
    forall r1 r2,
      source_regex r1 ->
      source_regex r2 ->
      source_regex (Sequence r1 r2)
  | src_quant:
    forall greedy min delta r1,
      source_regex r1 ->
      source_regex (Quantified greedy min delta r1)
  | src_group:
    forall g r1,
      source_regex r1 ->
      source_regex (Group g r1)
  | src_anchor:
    forall a, source_regex (Anchor a).

  (** * Expanding away counted quantifier creates a supported regex *)
  (* Using the quantifier expansion defined in Rewriting/QuantifierExpansion *)

  Lemma expand_greedy_atmost_subset:
    forall n r,
      pike_regex r -> pike_regex (expand_greedy_atmost n r).
  Proof.
    intros n r SUBSET. induction n; simpl;
      repeat (constructor; auto).
  Qed.

  Lemma expand_lazy_atmost_subset:
    forall n r,
      pike_regex r -> pike_regex (expand_lazy_atmost n r).
  Proof.
    intros n r SUBSET. induction n; simpl;
      repeat (constructor; auto).
  Qed.

  Lemma expand_counted_subset:
    forall greedy min delta r,
      pike_regex r -> pike_regex (expand_counted greedy min delta r).
  Proof.
    intros greedy min delta r SUBSET. induction min; simpl.
    - destruct delta as [del|]; [destruct greedy|].
      + apply expand_greedy_atmost_subset. auto.
      + apply expand_lazy_atmost_subset. auto.
      + constructor. auto.
    - repeat (constructor; auto).
  Qed.

  Theorem expand_quant_subset:
    forall r,
      source_regex r -> pike_regex (expand_quant r).
  Proof.
    intros r SUBSET. induction SUBSET; simpl;
      try constructor; auto.
    apply expand_counted_subset. auto.
  Qed.

End Expansion.

(** * Engine Correctness for the Source Subset *)
(* Running the engine on the expansion of a regex of the source subset
   computes the backtracking result of the original regex *)


Section ExpansionCorrectness.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context (rer: RegExpRecord).

  (* Using equivaence to transfer a first leaf result *)
  Lemma first_leaf_transfer r1 r2 inp t1 result:
    r1 ≅[rer][forward] r2 ->
    is_tree rer [Areg r1] inp GroupMap.empty forward t1 ->
    (forall t2, is_tree rer [Areg r2] inp GroupMap.empty forward t2 -> result = first_leaf t2 inp) ->
    result = first_leaf t1 inp.
  Proof.
    intros EQUIV TREE1 RES.
    pose proof (@compute_tr_is_tree _ rer [Areg r2] inp GroupMap.empty forward) as TREE2.
    rewrite (RES _ TREE2). symmetry.
    apply (observe_equivalence rer _ _ EQUIV inp _ _ TREE1 TREE2).
  Qed.

  (* Now we simply generalize all theorems from Correctness.v *)

  (** * PikeVM *)

  Theorem pike_vm_correct_source:
    forall r inp tree result,
      (* the regex `r` is in the source subset *)
      source_regex r ->
      (* `tree` is the tree of the regex `r` for the input `inp` *)
      is_tree rer [Areg r] inp GroupMap.empty forward tree ->
      (* the result of the PikeVM on the expansion of `r` is `result` *)
      trc_pike_vm rer (compilation (expand_quant r)) (pike_vm_initial_state inp) (PVS_final result) ->
      (* This `result` is the priority result of the `tree` *)
      result = first_leaf tree inp.
  Proof.
    intros r inp tree result SOURCE TREE TRC.
    eapply first_leaf_transfer; eauto using expand_quant_equiv.
    intros t2 TREE2. eapply pike_vm_correct; eauto using expand_quant_subset.
  Qed.

  Theorem pike_vm_correct_unanchored_source {strs:StrSearch}:
    forall r inp tree result,
      (* the regex `r` is in the source subset *)
      source_regex r ->
      (* `tree` is the tree of the regex `[^]*?r` for the input `inp` *)
      is_tree rer [Areg (lazy_prefix r)] inp GroupMap.empty forward tree ->
      (* the result of the PikeVM on the expansion of `r` is `result` *)
      trc_pike_vm rer (compilation (expand_quant r))
        (pike_vm_initial_state_unanchored (extract_literal rer (expand_quant r)) inp) (PVS_final result) ->
      (* This `result` is the priority result of the `tree` *)
      result = first_leaf tree inp.
  Proof.
    intros r inp tree result SOURCE TREE TRC.
    eapply first_leaf_transfer; eauto using expand_lazy_prefix_equiv.
    intros t2 TREE2. eapply pike_vm_correct_unanchored; eauto using expand_quant_subset.
  Qed.

  (* Equivalence of PikeVM to Warblre backtracking algorithm *)
  Theorem pike_vm_same_warblre_source:
    forall lr wr inp,
      source_regex lr ->
      equiv_regex wr lr ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wr nil ->
      EarlyErrors.Pass_Regex wr nil ->
      forall result,
        trc_pike_vm rer (compilation (expand_quant lr)) (pike_vm_initial_state inp) (PVS_final result) ->
        EquivDef.equiv_res result ((EquivMain.compilePattern wr rer) (input_str inp) (idx inp)).
  Proof.
    intros lr wr inp Hsource Hequiv Hcapcount HearlyErrors.
    pose proof equiv_main wr lr rer inp Hequiv Hcapcount HearlyErrors as HequivMain.
    destruct HequivMain as [m [res [Hcompsucc [Hexecsucc Hsameresult]]]].
    unfold compilePattern. rewrite Hcompsucc, Hexecsucc.
    set (tree := FunctionalUtils.compute_tr rer [Areg lr] inp GroupMap.empty forward).
    specialize (Hsameresult tree eq_refl). destruct Hsameresult as [His_tree Hsameresult].
    intros result Hpikeresult.
    pose proof pike_vm_correct_source lr inp tree result Hsource His_tree Hpikeresult as Hsameresult'.
    rewrite Hsameresult'. assumption.
  Qed.

  (* Same, but with an input that is at the beginning of the input string *)
  Theorem pike_vm_same_warblre_str0_source:
    forall lr wr str0,
      source_regex lr ->
      equiv_regex wr lr ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wr nil ->
      EarlyErrors.Pass_Regex wr nil ->
      forall result,
        trc_pike_vm rer (compilation (expand_quant lr)) (pike_vm_initial_state (init_input str0)) (PVS_final result) ->
        EquivDef.equiv_res result ((EquivMain.compilePattern wr rer) str0 0).
  Proof.
    intros lr wr str0 Hsource Hequiv Hcapcount HearlyErrors.
    apply pike_vm_same_warblre_source; auto.
  Qed.

  (* Equivalence of PikeVM to Warblre Semantics *)
  (* A version closer to the paper definition *)
  Theorem pike_vm_warblre_source:
    forall rw r inp result,
      (* For a correct RegExpRecord *)
      RegExpRecord.capturingGroupsCount rer = countLeftCapturingParensWithin rw [] ->
      (* For any Warblre regex that passes the early errors check, *)
      earlyErrors rw nil = Success false ->
      (* letting r be the corresponding Linden regex, *)
      r = warblre_to_linden' rw 0 (buildnm rw) ->
      (* such that it is in the source subset *)
      source_regex r ->
      (* When PikeVM reaches a final result on the expansion of r *)
      trc_pike_vm rer (compilation (expand_quant r)) (pike_vm_initial_state inp) (PVS_final result) ->
      (* this result is equal to Warblre's execution result *)
      (compilePattern rw rer) (input_str inp) (idx inp) = to_MatchState result (RegExpRecord.capturingGroupsCount rer).
  Proof.
    intros rw r inp result RER EARLY TOLINDEN SOURCE TRC.
    specialize (earlyErrors_pass_translation _ EARLY) as [lr SUCCESS].
    unfold warblre_to_linden' in TOLINDEN. rewrite SUCCESS in TOLINDEN. subst.
    specialize (warblre_to_linden_sound_root _ _ SUCCESS) as EQUIV.
    apply EarlyErrors.earlyErrors in EARLY as PASS.
    specialize (equiv_main _ _ _ inp EQUIV RER PASS) as [m [res [COMP_SUCC [EXEC_SUCC LW_EQUIV]]]].
    unfold compilePattern. rewrite COMP_SUCC, EXEC_SUCC.
    specialize (LW_EQUIV (compute_tr rer [Areg lr] inp GroupMap.empty forward) eq_refl) as [ISTREE LW_EQUIV].
    specialize (pike_vm_correct_source _ _ _ _ SOURCE ISTREE TRC) as FIRST. subst.
    symmetry. apply to_MatchState_equal; auto.
    eapply compilePattern_preserves_groupcount; eauto.
  Qed.

  (** * MemoBT *)

  Theorem memobt_correct_source:
    forall r inp tree result initms finalms,
      (* the regex `r` is in the source subset *)
      source_regex r ->
      (* the initial memoset is correct  *)
      correctms rer initms (compilation (expand_quant r)) ->
      (* `tree` is the tree of the regex `r` for the input `inp` *)
      is_tree rer [Areg r] inp GroupMap.empty forward tree ->
      (* the result of MemoBT on the expansion of `r` is `result` *)
      trc_memo_bt rer (compilation (expand_quant r)) (MemoBT.initial_state inp initms) (MBT_final result finalms) ->
      (* This `result` is the priority result of the `tree` *)
      result = first_leaf tree inp
      (* when the result is None, the final memoset is correct *)
      /\ (result = None -> correctms rer finalms (compilation (expand_quant r))).
  Proof.
    intros r inp tree result initms finalms SOURCE CORRECT TREE TRC.
    pose proof (expand_quant_subset _ SOURCE) as SUBSET.
    split.
    - eapply first_leaf_transfer; eauto using expand_quant_equiv.
      intros t2 TREE2. apply (proj1 (memobt_correct rer _ _ _ _ _ _ SUBSET CORRECT TREE2 TRC)).
    - apply (proj2 (memobt_correct rer _ _ _ _ _ _ SUBSET CORRECT (@compute_tr_is_tree _ rer _ _ _ _) TRC)).
  Qed.

  Theorem memobt_correct_init_source:
    forall r inp tree result ms,
      (* the regex `r` is in the source subset *)
      source_regex r ->
      (* `tree` is the tree of the regex `r` for the input `inp` *)
      is_tree rer [Areg r] inp GroupMap.empty forward tree ->
      (* the result of MemoBT on the expansion of `r` is `result` *)
      trc_memo_bt rer (compilation (expand_quant r)) (MemoBT.initial_state inp initial_memoset) (MBT_final result ms) ->
      (* This `result` is the priority result of the `tree` *)
      result = first_leaf tree inp
      (* when the result is None, the final memoset is correct *)
      /\ (result = None -> correctms rer ms (compilation (expand_quant r))).
  Proof.
    intros r inp tree result ms SOURCE TREE TRC.
    eapply memobt_correct_source; eauto. apply correctms_init.
  Qed.

  (* Equivalence of MemoBT to Warblre backtracking algorithm *)
  Theorem memobt_same_warblre_source:
    forall lr wr inp initms finalms,
      source_regex lr ->
      correctms rer initms (compilation (expand_quant lr)) ->
      equiv_regex wr lr ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wr nil ->
      EarlyErrors.Pass_Regex wr nil ->
      forall result,
        trc_memo_bt rer (compilation (expand_quant lr)) (MemoBT.initial_state inp initms) (MBT_final result finalms) ->
        EquivDef.equiv_res result ((EquivMain.compilePattern wr rer) (input_str inp) (idx inp)).
  Proof.
    intros lr wr inp initms finalms Hsource Hcorrect Hequiv Hcapcount HearlyErrors.
    pose proof equiv_main wr lr rer inp Hequiv Hcapcount HearlyErrors as HequivMain.
    destruct HequivMain as [m [res [Hcompsucc [Hexecsucc Hsameresult]]]].
    unfold compilePattern. rewrite Hcompsucc, Hexecsucc.
    set (tree := FunctionalUtils.compute_tr rer [Areg lr] inp GroupMap.empty forward).
    specialize (Hsameresult tree eq_refl). destruct Hsameresult as [His_tree Hsameresult].
    intros result Hmemoresult.
    pose proof memobt_correct_source lr inp tree result initms finalms Hsource Hcorrect His_tree Hmemoresult as [Hsameresult' Hcorrect'].
    rewrite Hsameresult'. assumption.
  Qed.

  Theorem memobt_same_warblre_init_source:
    forall lr wr inp ms,
      source_regex lr ->
      equiv_regex wr lr ->
      RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wr nil ->
      EarlyErrors.Pass_Regex wr nil ->
      forall result,
        trc_memo_bt rer (compilation (expand_quant lr)) (MemoBT.initial_state inp initial_memoset) (MBT_final result ms) ->
        EquivDef.equiv_res result ((EquivMain.compilePattern wr rer) (input_str inp) (idx inp)).
  Proof.
    intros lr wr inp ms H H0 H1 H2 result H3.
    eapply memobt_same_warblre_source; eauto. apply correctms_init.
  Qed.

End ExpansionCorrectness.
