(** * Correctness theorems for the PikeVM engine  *)

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA PikeTree PikeVM.
From Linden Require Import PikeEquiv PikeSubset.
From Linden Require Import EquivMain RegexpTranslation GroupMapMS.
From Linden Require Import ResultTranslation FunctionalUtils SeenSets.
From Linden Require Import Parameters Prefix.
From Linden Require Import Parameters.
From Warblre Require Import Base Semantics Result RegExpRecord StaticSemantics.
Import Result.Notations.

Local Open Scope result_flow.
From Linden Require Import LWParameters.

(** * Transitive Reflexive Closure of Small-step semantics  *)

Inductive trc {A:Type} {R: A -> A -> Prop}: A -> A -> Prop:=
| trc_refl: forall a, trc a a
| trc_cons:
  forall x y z
    (STEP: R x y)
    (TRC: trc y z),
    trc x z.

Lemma trc_step:
  forall A (R:A->A->Prop) x y,
    R x y ->
    @trc A R x y.
Proof.
  intros A R x y H. eapply trc_cons; eauto. eapply trc_refl.
Qed.


Section Correctness.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context (rer: RegExpRecord).

Definition trc_pike_tree := @trc pike_tree_state pike_tree_step.
Definition trc_pike_vm (c:code) (dir:Direction) (os:nfa_oracles) := @trc pike_vm_state (pike_vm_step rer c dir os).

(* The Pike invariant is preserved through the TRC *)
Lemma vm_to_tree:
  forall svm1 st1 svm2 r code os
    (COMPILE: compilation r = code)
    (STWF: stutter_wf rer code)
    (INVARIANT: pike_inv rer r os st1 svm1)
    (TRCVM: trc_pike_vm code forward os svm1 svm2),
    exists st2, trc_pike_tree st1 st2 /\ pike_inv rer r os st2 svm2.
Proof.
  intros svm1 st1 svm2 r code os COMPILE STWF INVARIANT TRCVM.
  generalize dependent st1. induction TRCVM; intros.
  { exists st1. split; auto. apply trc_refl. }
  eapply PikeEquiv.invariant_preservation in STEP; eauto.
  destruct STEP as [[pts2 [TSTEP INV]] | INV].
  - apply IHTRCVM in INV as [st2 [TTRC TINV]].
    exists st2. split; auto. eapply trc_cons; eauto.
  - apply IHTRCVM in INV as [st2 [TTRC TINV]].
    exists st2. split; auto.
Qed.

(* Any execution of the PikeVM to a final state corresponds to an execution of the PikeTree *)
Theorem pike_vm_to_pike_tree:
  forall r inp os tree result,
    pike_regex r ->
    bool_tree rer [Areg r] inp CanExit forward tree ->
    trc_pike_vm (compilation r) forward os (pike_vm_initial_state inp) (PVS_final result) ->
    trc_pike_tree (pike_tree_initial_state tree inp) (PTS_final result).
Proof.
  intros r inp os tree result SUBSET OS TREE TRCVM.
  pose proof (initial_pike_inv rer r inp os tree TREE SUBSET OS) as INIT.
  eapply vm_to_tree in TRCVM as [vmfinal [TRCTREE INV]]; eauto.
  - inversion INV; subst. auto.
  - eapply compilation_stutter_wf; eauto.
Qed.

Theorem pike_vm_to_pike_tree_unanchored {strs:StrSearch}:
  forall r inp os tree result future_tree,
    pike_regex r ->
    bool_tree rer [Areg r] inp CanExit forward tree ->
    trc_pike_vm (compilation r) forward os (pike_vm_initial_state_unanchored (extract_literal rer r) inp forward) (PVS_final result) ->
    future_tree_shape rer r inp future_tree ->
    exists future, may_erase future_tree future /\
    trc_pike_tree (pike_tree_initial_state_unanchored tree future inp) (PTS_final result).
Proof.
  intros r inp os tree result future_tree SUBSET OS TREE TRCVM NEXTFUTURE.
  pose proof (initial_pike_inv_unanchored rer _ _ _ _ _ TREE SUBSET OS NEXTFUTURE) as [future [M INIT]].
  eapply vm_to_tree in TRCVM as [vmfinal [TRCTREE INV]]; eauto.
  - inversion INV; subst. eauto.
  - eapply compilation_stutter_wf; eauto.
Qed.

(* Through the TRC of PikeTree, the result is the result of the tree *)
Lemma pike_tree_trc_correct:
  forall s1 s2 result
    (INV: piketreeinv s1 result)
    (TRC: trc_pike_tree s1 s2),
    piketreeinv s2 result.
Proof.
  intros s1 s2 result INV TRC.
  induction TRC; auto.
  apply IHTRC. eapply pts_preservation; eauto.
Qed.


(** * Correctness Theorem of the PikeVM result  *)

Theorem pike_vm_correct:
  forall r inp os tree result,
    (* the regex `r` is in the supported subset *)
    pike_regex r ->
    (* `tree` is the tree of the regex `r` for the input `inp` *)
    is_tree rer [Areg r] inp GroupMap.empty forward tree ->
    (* the result of the PikeVM is `result` *)
    trc_pike_vm (compilation r) forward os (pike_vm_initial_state inp) (PVS_final result) ->
    (* This `result` is the priority result of the `tree` *)
    result = first_leaf tree inp.
Proof.
  intros r inp os tree result SUBSET OS TREE TRC.
  eapply encode_equal with (b:=CanExit) in TREE as BOOLTREE; pike_subset.
  eapply pike_vm_to_pike_tree in TRC; eauto.
  assert (SUBTREE: pike_subtree tree).
  { eapply pike_actions_pike_tree with (cont:=[Areg r]); eauto.
    pike_subset. }
  generalize (init_piketree_inv tree inp SUBTREE). intros INIT.
  eapply pike_tree_trc_correct in TRC as FINALINV; eauto.
  inversion FINALINV. subst. auto.
Qed.

Theorem pike_vm_correct_unanchored {strs:StrSearch}:
  forall r inp os tree result,
    (* the regex `r` is in the supported subset *)
    pike_regex r ->
    (* `tree` is the tree of the regex `[^]*?r` for the input `inp` *)
    is_tree rer [Areg (lazy_prefix r)] inp GroupMap.empty forward tree ->
    (* the result of the PikeVM is `result` *)
    trc_pike_vm (compilation r) forward os (pike_vm_initial_state_unanchored (extract_literal rer r) inp forward) (PVS_final result) ->
    (* This `result` is the priority result of the `tree` *)
    result = first_leaf tree inp.
Proof.
  intros r inp os tree result SUBSET OS TREE TRC.
  eapply encode_equal with (b:=CanExit) in TREE as BOOLTREE; pike_subset.
  inversion BOOLTREE; inversion CONT; destruct plus; [discriminate|]; subst.
  eapply pike_vm_to_pike_tree_unanchored in TRC as [? [? TRC]]; eauto.
  eapply pike_tree_trc_correct in TRC as FINALINV.
  2: eapply init_piketree_inv_unanchored; subst; unfold initial_future_unanchored; eauto.
  inversion FINALINV. subst. auto.
Qed.


(* Equivalence of PikeVM to Warblre backtracking algorithm *)
Theorem pike_vm_same_warblre:
  forall lr los wr inp,
    pike_regex lr ->
    equiv_regex wr lr ->
    RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wr nil ->
    EarlyErrors.Pass_Regex wr nil ->
    forall result,
      trc_pike_vm (compilation lr) forward los (pike_vm_initial_state inp) (PVS_final result) ->
      EquivDef.equiv_res result ((EquivMain.compilePattern wr rer) (input_str inp) (idx inp)).
Proof.
  intros lr los wr inp Hpike Hos Hequiv Hcapcount HearlyErrors.
  pose proof equiv_main wr lr rer inp Hequiv Hcapcount HearlyErrors as HequivMain.
  destruct HequivMain as [m [res [Hcompsucc [Hexecsucc Hsameresult]]]].
  unfold compilePattern. rewrite Hcompsucc, Hexecsucc.
  set (tree := FunctionalUtils.compute_tr rer [Areg lr] inp GroupMap.empty forward).
  specialize (Hsameresult tree eq_refl). destruct Hsameresult as [His_tree Hsameresult].
  intros result Hpikeresult.
  pose proof pike_vm_correct lr inp los tree result Hpike Hos His_tree Hpikeresult as Hsameresult'.
  rewrite Hsameresult'. assumption.
Qed.

(* Same, but with an input that is at the beginning of the input string *)
Theorem pike_vm_same_warblre_str0:
  forall lr los wr str0,
    pike_regex lr ->
    equiv_regex wr lr ->
    RegExpRecord.capturingGroupsCount rer = StaticSemantics.countLeftCapturingParensWithin wr nil ->
    EarlyErrors.Pass_Regex wr nil ->
    forall result,
      trc_pike_vm (compilation lr) forward los (pike_vm_initial_state (init_input str0)) (PVS_final result) ->
      EquivDef.equiv_res result ((EquivMain.compilePattern wr rer) str0 0).
Proof.
  intros lr los wr str0 Hpike Hos Hequiv Hcapcount HearlyErrors.
  apply pike_vm_same_warblre; auto.
Qed.

(* Equivalence of PikeVM to Warblre Semantics *)
(* A version closer to the paper definition *)
Theorem pike_vm_warblre:
  forall rw r os inp result,
    (* For a correct RegExpRecord *)
    RegExpRecord.capturingGroupsCount rer = countLeftCapturingParensWithin rw [] ->
    (* For any Warblre regex that passes the early errors check, *)
    earlyErrors rw nil = Success false ->
    (* letting r be the corresponding Linden regex, *)
    r = warblre_to_linden' rw 0 (buildnm rw) ->
    (* such that it is in the supported PikeVM subset *)
    pike_regex r ->
    (* When PikeVM reaches a final result *)
    trc_pike_vm (compilation r) forward os (pike_vm_initial_state inp) (PVS_final result) ->
    (* this result is equal to Warblre's execution result *)
    (compilePattern rw rer) (input_str inp) (idx inp) = to_MatchState result (RegExpRecord.capturingGroupsCount rer).
Proof.
  intros rw r os inp result RER EARLY TOLINDEN SUBSET OS TRC.
  specialize (earlyErrors_pass_translation _ EARLY) as [lr SUCCESS].
  unfold warblre_to_linden' in TOLINDEN. rewrite SUCCESS in TOLINDEN. subst.
  specialize (warblre_to_linden_sound_root _ _ SUCCESS) as EQUIV.
  apply EarlyErrors.earlyErrors in EARLY as PASS.
  specialize (equiv_main _ _ _ inp EQUIV RER PASS) as [m [res [COMP_SUCC [EXEC_SUCC LW_EQUIV]]]].
  unfold compilePattern. rewrite COMP_SUCC, EXEC_SUCC.
  specialize (LW_EQUIV (compute_tr rer [Areg lr] inp GroupMap.empty forward) eq_refl) as [ISTREE LW_EQUIV].
  specialize (pike_vm_correct _ _ _ _ _ SUBSET OS ISTREE TRC) as FIRST. subst.
  symmetry. apply to_MatchState_equal; auto.
  eapply compilePattern_preserves_groupcount; eauto.
Qed.

End Correctness.
