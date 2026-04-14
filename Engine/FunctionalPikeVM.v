(* The PikeVM algorithm, expressed as a fuel-based function *)

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import PikeVM Correctness SeenSets Semantics.Examples.
From Linden Require Import Complexity.
From Linden Require Import Parameters Prefix.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import FunctionalUtils FunctionalSemantics.

Section FunctionalPikeVM.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context (rer: RegExpRecord).
(** * Functional Definition  *)

(* a functional version of the small step *)
Definition pike_vm_func_step (c:code') (dir:Direction) (os:nfa_oracles) (pvs:pike_vm_state) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | PVS inp active best blocked nextprefix seen =>
      match active with
      | [] =>
          match blocked with
          | [] =>
              match nextprefix with
              | Some (n, lit, strs) =>
                let nextinp := advance_input_n inp (S n) dir in
                PVS nextinp [pike_vm_initial_thread] best [] (next_prefix_counter nextinp dir lit) initial_seenpcs (* pvs_acc *)
              | None => PVS_final best (* pvs_final *)
              end
          | thr::blocked =>
              match (advance_input inp dir) with
              | None => PVS_final best (* pvs_end *)
              | Some nextinp =>
                  match nextprefix with
                  | None => PVS nextinp (thr::blocked) best [] None initial_seenpcs (* pvs_nextchar *)
                  | Some (0, lit, strs) => PVS nextinp (thr::blocked ++ [pike_vm_initial_thread]) best [] (next_prefix_counter nextinp dir lit) initial_seenpcs (* pvs_nextchar_generate *)
                  | Some (S n, lit, strs) => PVS nextinp (thr::blocked) best [] (Some (n, lit, strs)) initial_seenpcs (* pvs_nextchar_filter *)
                  end
              end
          end
      | t::active =>
          match (seen_thread seen t) with
          | true => PVS inp active best blocked nextprefix seen (* pvs_skip *)
          | false =>
              let nextseen := add_thread seen t in
              match (epsilon_step' rer t c dir os inp) with
              | EpsActive nextactive =>
                  PVS inp (nextactive++active) best blocked nextprefix nextseen (* pvs_active *)
              | EpsMatch =>
                  PVS inp [] (Some (inp,gm_of t)) blocked None nextseen (* pvs_match *)
              | EpsBlocked newt =>
                  PVS inp active best (blocked ++ [newt]) nextprefix nextseen (* pvs_blocked *)
              end
          end
      end
  end.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint pike_vm_loop (c:code') (dir:Direction) (os:nfa_oracles) (pvs:pike_vm_state) (fuel:nat) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | _ =>
      match fuel with
      | 0 => pvs
      | S fuel =>
          pike_vm_loop c dir os (pike_vm_func_step c dir os pvs) fuel
      end
  end.

(* an upper bound for the fuel necessary to compute a result *)
Definition vm_fuel (r:regex) (inp:input) (dir:Direction): nat :=
  complexity r inp dir.

Inductive matchres : Type :=
| OutOfFuel
| Finished: option leaf -> matchres.

Definition getres (pvs:pike_vm_state) : matchres :=
  match pvs with
  | PVS_final best => Finished best
  | _ => OutOfFuel
  end.

Definition nfa_oracles_dir (os: nfa_oracles) (dir: Direction) : nfa_oracles :=
  match dir with
  | forward => os
  | backward => nfa_oracles_reverse os
  end.

Parameter nfa_oracles_create : (regex -> nfa_oracles).
Axiom nfa_oracles_create_correct:
  forall r inp,
    nfa_oracles_correct rer (nfa_oracles_create r) r inp.

(* Functional version of the PikeVM *)
Definition pike_vm_match (r:regex) (inp:input) (dir:Direction) : matchres :=
  let code := translate_code (compilation r) in
  let fuel := vm_fuel r inp dir in
  let pvsinit := pike_vm_initial_state inp in
  getres (pike_vm_loop code dir (nfa_oracles_dir (nfa_oracles_create r) dir) pvsinit fuel).

(* Functional version of the unanchored PikeVM *)
Definition pike_vm_match_unanchored {strs:StrSearch} (r:regex) (inp:input) (dir:Direction): matchres :=
  let code := translate_code (compilation r) in
  let fuel := vm_fuel r inp dir in
  let pvsinit := pike_vm_initial_state_unanchored (extract_literal rer r) inp dir in
  getres (pike_vm_loop code dir (nfa_oracles_dir (nfa_oracles_create r) dir) pvsinit fuel).


(** * Smallstep correspondence  *)

Inductive final_state: pike_vm_state -> Prop :=
| pfinal: forall best, final_state (PVS_final best).

Ltac match_destr:=
  match goal with
  | [ H : match ?x with _ => _ end = _  |- _ ] => let H := fresh "H" in destruct x eqn:H
  end.

Theorem func_step_correct:
  forall c dir os pvs1 pvs2,
    pike_vm_func_step (translate_code c) dir os pvs1 = pvs2 ->
    pike_vm_step rer c dir os pvs1 pvs2 \/ final_state pvs1.
Proof.
  unfold pike_vm_func_step. intros c dir os pvs1 pvs2 H.
  repeat match_destr; subst; try rewrite <-epsilon_step_translate in H3; try solve[left; constructor; auto].
  right. constructor.
Qed.

Corollary func_step_not_final:
  forall c dir os inp active best blocked nextprefix seen,
    pike_vm_step rer c dir os (PVS inp active best blocked nextprefix seen) (pike_vm_func_step (translate_code c) dir os (PVS inp active best blocked nextprefix seen)).
Proof.
  intros c dir os inp active best blocked nextprefix seen. specialize (func_step_correct c dir os (PVS inp active best blocked nextprefix seen) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem loop_trc:
  forall c dir os pvs1 pvs2 fuel,
    pike_vm_loop (translate_code c) dir os pvs1 fuel = pvs2 ->
    trc_pike_vm rer c dir os pvs1 pvs2.
Proof.
  intros c dir os pvs1 pvs2 fuel H.
  generalize dependent pvs1. induction fuel; intros; simpl in H.
  { destruct pvs1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply func_step_not_final. apply IHfuel. auto.
  - constructor.
Qed.

Lemma step_loop:
  forall c dir os pvs1 pvs2 fuel,
    pike_vm_step rer c dir os pvs1 pvs2 ->
    pike_vm_loop (translate_code c) dir os pvs1 (S fuel) = pike_vm_loop (translate_code c) dir os pvs2 fuel.
Proof.
  intros c dir os pvs1 pvs2 fuel H. destruct H; simpl;
    try rewrite <-epsilon_step_translate in *; now rewrite ?ADVANCE, ?SEEN, ?UNSEEN, ?STEP.
Qed.

Theorem steps_loop:
  forall c dir os pvs1 pvs2 fuel,
    steps (pike_vm_step rer c dir os) pvs1 fuel (PVS_final pvs2) ->
    pike_vm_loop (translate_code c) dir os pvs1 fuel = (PVS_final pvs2).
Proof.
  intros c dir os pvs1 pvs2 fuel H. remember (PVS_final pvs2) as result.
  induction H; subst.
  - destruct n; simpl; auto.
  - destruct x.
    2: { inversion STEP. }
    erewrite step_loop; eauto.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem pike_vm_match_correct:
  forall r dir inp result,
    pike_vm_match r inp dir = Finished result ->
    trc_pike_vm rer (compilation r) dir (nfa_oracles_dir (nfa_oracles_create r) dir) (pike_vm_initial_state inp) (PVS_final result).
Proof.
  unfold pike_vm_match, getres. intros r dir inp result H.
  match_destr; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem pike_vm_match_correct_unanchored {strs:StrSearch}:
  forall r dir inp result,
    pike_vm_match_unanchored r inp dir = Finished result ->
    trc_pike_vm rer (compilation r) dir (nfa_oracles_dir (nfa_oracles_create r) dir) (pike_vm_initial_state_unanchored (extract_literal rer r) inp dir) (PVS_final result).
Proof.
  unfold pike_vm_match_unanchored, getres. intros r dir inp result H.
  match_destr; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(* the function always terminates *)
Theorem pike_vm_match_terminates:
  forall r inp dir,
    pike_regex r ->
    exists result, pike_vm_match r inp dir = Finished result.
Proof.
  intros r inp dir SUBSET. unfold pike_vm_match, vm_fuel.
  apply pikevm_complexity with (VMS:=VMS) (rer:=rer) (inp:=inp) (dir:=dir) (os:=nfa_oracles_dir (nfa_oracles_create r) dir) in SUBSET as [result TERM].
  exists result. apply steps_loop in TERM. rewrite TERM. auto.
Qed.

(* the function always terminates *)
Theorem pike_vm_match_terminates_unanchored {strs:StrSearch}:
  forall r inp dir,
    pike_regex r ->
    exists result, pike_vm_match_unanchored r inp dir = Finished result.
Proof.
  intros r inp dir SUBSET. unfold pike_vm_match_unanchored, vm_fuel.
  apply pikevm_complexity_unanchored with (strs:=strs) (VMS:=VMS) (rer:=rer) (inp:=inp) (dir:=dir) (os:=nfa_oracles_dir (nfa_oracles_create r) dir) in SUBSET as [result TERM]; auto.
  exists result. apply steps_loop in TERM. rewrite TERM. auto.
Qed.

(* relating the final state of the reverse direction for the TRC *)
Lemma trc_pike_vm_reverse:
  forall c dir os pvs result1 result2,
    trc_pike_vm rer c dir os pvs (PVS_final result1) ->
    trc_pike_vm rer c (direction_reverse dir) (nfa_oracles_reverse os) (pvs_reverse pvs) (PVS_final result2) ->
    result1 = leaf_reverse result2.
Proof.
  intros c dir os pvs result1 result2 H1.
  remember (PVS_final result1) as pvs_end.
  induction H1; intros H2; subst.
  - inversion H2; subst.
    + now rewrite leaf_reverse_involutive.
    + easy.
  - inversion H2; subst.
    + now destruct x.
    + eapply IHtrc; eauto.
      eapply pikevm_step_reverse in STEP as Heq; eauto.
      apply f_equal with (f:=pvs_reverse) in Heq.
      rewrite pvs_reverse_involutive in Heq.
      now subst.
Qed.

(* expresses anchored matching in the reverse direction in terms of the the other direction *)
Lemma pike_vm_match_reverse :
  forall r inp dir result1 result2,
    pike_vm_match r inp dir = Finished result1 ->
    pike_vm_match r (input_reverse inp) (direction_reverse dir) = Finished result2 ->
    result1 = leaf_reverse result2.
Proof.
  intros r inp dir result1 result2 H1%pike_vm_match_correct H2%pike_vm_match_correct.
  eapply trc_pike_vm_reverse; destruct dir; eauto; simpl.
  now rewrite nfa_oracles_reverse_involutive.
Qed.

(* expresses unanchored matching in the reverse direction in terms of the the other direction *)
Lemma pike_vm_match_reverse_unanchored {strs:StrSearch}:
  forall r inp dir result1 result2,
    pike_vm_match_unanchored r inp dir = Finished result1 ->
    pike_vm_match_unanchored r (input_reverse inp) (direction_reverse dir) = Finished result2 ->
    result1 = leaf_reverse result2.
Proof.
  intros r inp dir result1 result2 H1%pike_vm_match_correct_unanchored H2%pike_vm_match_correct_unanchored.
  unfold pike_vm_initial_state_unanchored in *.
  eapply trc_pike_vm_reverse; destruct dir; eauto; simpl; now rewrite next_prefix_counter_reverse, ?nfa_oracles_reverse_involutive.
Qed.

End FunctionalPikeVM.

(** * Execution Examples  *)

From Linden Require Import Inst.
From Warblre Require Import Inst.
Require Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Open Scope string_scope.

Section Example.
  (** * Nullable Quantifier Example *)
  (* Matching ((a|epsilon)(epsilon|b))* on string "ab" matches "ab", a specificity of Javascript semantics *)

  Definition a : Character.type := $ "a".
  Definition b : Character.type := $ "b".

  Example a_char : regex := Regex.Character (CdSingle a).
  Example b_char : regex := Regex.Character (CdSingle b).

  Example nq_regex: regex :=
    greedy_star(Sequence
                  (Disjunction(a_char)(Epsilon))
                  (Disjunction(Epsilon)(b_char))).

  Example nq_bytecode := [Fork 1 10; BeginLoop; ResetRegs []; Fork 4 6; Consume (CdSingle a); Jmp 6; Fork 7 8; Jmp 9; Consume (CdSingle b); EndLoop 0; Accept].

  Lemma compile_nq: compilation nq_regex = nq_bytecode.
  Proof. auto. Qed.

  Example nq_inp: input := Input [a;b] [].

  Lemma nullable_quant:
    pike_vm_match (rer_of nq_regex) nq_regex nq_inp forward = Finished (Some (Input [] [b;a], GroupMap.empty)).
  Proof. reflexivity. Qed.

(** * Example from the paper - Figure 15  *)
(* regex (a*|a)b on string "ab" *)

Example paper_regex : regex := Sequence (Group 1 (Disjunction (greedy_star a_char) a_char)) b_char.

Example paper_bytecode := [SetRegOpen 1; Fork 2 8; Fork 3 7; BeginLoop; ResetRegs []; Consume (CdSingle a);
                           EndLoop 2; Jmp 9; Consume (CdSingle a); SetRegClose 1; Consume (CdSingle b); Accept].

Lemma compile_paper: compilation paper_regex = paper_bytecode.
Proof. auto. Qed.

Example paper_input := Input [a;b] [].

Example paper_tree: tree :=
  GroupAction (Open 1) (
      Choice
        (Choice (
             GroupAction (Reset []) (Read a (Progress (
                                                 Choice (GroupAction (Reset []) Mismatch)
                                                   (GroupAction (Close 1) (Read b Match)))
               ))
           ) (GroupAction (Close 1) Mismatch))
        (Read a (GroupAction (Close 1) (Read b Match)))).

Lemma paper_is_tree:
  is_tree (rer_of paper_regex) [Areg paper_regex] paper_input GroupMap.empty forward paper_tree.
Proof.
  apply compute_tr_eq_is_tree. reflexivity.
Qed.

Example final_gm : GroupMap.t :=
  GroupMap.close 1 1 (GroupMap.open 0 1 GroupMap.empty).

Lemma paper_pikevm_exec:
  pike_vm_match (rer_of paper_regex) paper_regex paper_input forward = Finished (Some (Input [] [b;a], final_gm)).
Proof. reflexivity. Qed.

End Example.
