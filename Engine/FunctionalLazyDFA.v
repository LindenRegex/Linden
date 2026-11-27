From Stdlib Require Import List Lia Bool.
From Stdlib Require Import Relation_Definitions Relation_Operators Operators_Properties.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import (* Tree *) Semantics NFA.
From Linden Require Import BooleanSemantics.
From Linden Require Import Parameters (* SeenSets Prefix *).
From Linden Require Import Complexity.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import PikeSubset.
From Linden Require Import PeekingAnalysis.
From Linden Require Import FunctionalUtils FunctionalSemantics. (* todo check *)
From Linden Require Import LazyDFA.

Section FunctionalLazyDFA.
  Context {params: LindenParameters}.
  (* Context {VMS: VMSeen}. *)
  Context (rer: RegExpRecord).  
  Context {disj: Disjoint rer}.

Definition ldfa_epsilon_step (c: code) (st: ldfa_epsilon_state) : ldfa_epsilon_state :=
  match st with
  | LDFA_Eps_Done _ => st
  | LDFA_Eps_Running inp out workqueue =>
    match workqueue with
    | nil => LDFA_Eps_Done out (* elr_final *) (* once we're done with our workqueue, just return our "out" *)
    | curr :: tail => (* pas de current mutable, on va juste remettre à la head de la workqueue en fait *)
      if dfa_state_contains out curr then (* if state already in we don't explore it again *)
        LDFA_Eps_Running (inp) (out) (tail) (* elr_seen *) (* so new workqueue is tail, with curr popped *)
      else
      (* gotta remember we need to insert "curr" in "out" here, at the end !! *)
        let new_out := (out ++ [curr]) in
        match get_pc c (fst curr) with
        | None | Some (Consume _) | Some (KillThread) | Some (Accept) => 
          LDFA_Eps_Running (inp) (new_out) (tail) (* elr_break *) (* break : we go back to the workqueue pop after inserting curr at the end *)
        | Some (Fork _ out1 out2) => 
          LDFA_Eps_Running (inp) (new_out) ((out1, snd curr) :: [(out2, snd curr)] ++ tail) (* elr_fork *)
          (* we insert current in out, and head of workqueue is direct followup, but we also add the future explo at the tail *)
        | Some (Jmp l) => 
          LDFA_Eps_Running (inp) (new_out) ((l, snd curr) :: tail) (* elr_jmp *)
        | Some (CheckAnchor anc) => 
          match anchor_satisfied rer anc inp with
          | false => LDFA_Eps_Running (inp) (new_out) (tail) (* elr_anc_unsat *) (* equiv break *)
          | true => LDFA_Eps_Running (inp) (new_out) (((fst curr + 1), snd curr) :: tail) (* elr_anc_sat *)
          end
        | Some (BeginLoop) =>
          LDFA_Eps_Running (inp) (new_out) ((fst curr + 1, CannotExit) :: tail) (* elr_bgnloop *)
        | Some (EndLoop l) =>
          match (snd curr) with
          | CanExit => LDFA_Eps_Running (inp) (new_out) ((l, CanExit) :: tail) (* elr_endloop_sat *) (* canexit equiv to snd curr *)
          | CannotExit => LDFA_Eps_Running (inp) (new_out) (tail) (* elr_endloop_unsat *) (* break *)
          end
        | Some (SetRegOpen _) | Some (SetRegClose _) | Some (ResetRegs _) => 
          LDFA_Eps_Running inp (out ++ [curr]) ((next_step curr) :: tail) (* elr_skip *)
        end
    end
  end.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint ldfa_epsilon_loop (c:code) (st:ldfa_epsilon_state) (fuel:nat) : ldfa_epsilon_state :=
  match st with
  | LDFA_Eps_Done _ => st
  | _ =>
    match fuel with
    | 0 => st
    | S fuel =>
      ldfa_epsilon_loop c (ldfa_epsilon_step c st) fuel
    end
  end.

Definition ldfa_eps_fuel (c:code) : nat := (2 + 4 * (size c)).

Definition ldfa_next_step (c: code) (inp:input) (st: ldfa_nextloop_state) : ldfa_nextloop_state :=
  match st with
  | LDFA_Next_Done _ _ => st
  | LDFA_Next_Running n current_pcs =>
    match current_pcs with
    | [] => LDFA_Next_Done n false (* nlr_final *)
    | pc :: pcs =>
      match get_pc c (fst pc) with 
      | Some Accept => LDFA_Next_Done n true (* nlr_accept *)
      | Some (Consume cd) =>
        match (check_read rer cd inp forward) with
        | CanRead => 
          let epsi := ldfa_epsilon_loop c (LDFA_Eps_Running inp n ([next_step pc])) (ldfa_eps_fuel c) in
          match epsi with
          | LDFA_Eps_Done out => (LDFA_Next_Running (out) pcs) (* nlr_consume *)
          | _ => (LDFA_Next_Done [] false) (* shouldnt happen *) 
          end
        | CannotRead => (LDFA_Next_Running n pcs) (* nlr_noconsume *)
        end
      | Some KillThread => (LDFA_Next_Done [] false) (* nlr_kill *)
      | _ => (LDFA_Next_Running n pcs) (* nlr_skip *)
      end
    end
  end.

Fixpoint ldfa_next_loop (c:code) (inp:input) (st:ldfa_nextloop_state) (fuel:nat) : ldfa_nextloop_state :=
  match st with
  | LDFA_Next_Done _ _ => st
  | _ =>
    match fuel with
    | 0 => st
    | S fuel =>
      ldfa_next_loop c inp (ldfa_next_step c inp st) fuel
    end
  end.

Definition ldfa_main_step (c: code) (inp:input) (st: ldfa_state) : ldfa_state :=
  match st with
  | LDFA_final _ => st
  | LDFA curr inp ttab best => 
    match advance_input inp forward with
    | None =>
      if dfa_state_hasmatch c curr then
        LDFA_final (Some inp) (* ldfalr_final_match *)
      else
        LDFA_final best (* ldfalr_final_nomatch *)
    | Some next_i =>
      match next_char inp with
      | Some char =>
        match get_trans ttab curr char with
        | Some (next, true) => (LDFA next next_i ttab (Some inp)) (* ldfalr_cached_match *)
        | Some (next, false) => (LDFA next next_i ttab best) (* ldfalr_cached_nomatch *)
        | None => 
          match ldfa_next_loop c inp (LDFA_Next_Running [] curr) (length curr + 1) with
          | (LDFA_Next_Done next true) => (LDFA next next_i (add_trans ttab curr char next true) (Some inp)) (* ldfalr_new_match *)
          | (LDFA_Next_Done next false) => (LDFA next next_i (add_trans ttab curr char next false) best) (* ldfalr_new_nomatch *)
          | _ => (* shouldnt happen *) (LDFA_final None)
          end
        end
      | _ => (* shouldnt happen *) (LDFA_final None)
      end
    end
  end.

Fixpoint ldfa_main_loop (c:code) (inp:input) (st:ldfa_state) (fuel:nat) : ldfa_state :=
  match st with
  | LDFA_final _ => st
  | _ =>
    match fuel with
    | 0 => st
    | S fuel =>
      ldfa_main_loop c inp (ldfa_main_step c inp st) fuel
    end
  end.

Definition initial_ldfa_state (c:code) (inp:input) : ldfa_state :=
  match (ldfa_epsilon_loop c (initial_epsilon_state inp) (ldfa_eps_fuel c)) with
  | LDFA_Eps_Done out => LDFA out inp [] None
  | _ => (* shouldnt happen *) LDFA_final None
  end.

Inductive matchres : Type :=
| OutOfFuel
| Finished: option input -> matchres.

Definition getres (st:ldfa_state) : matchres :=
  match st with
  | LDFA_final best => Finished best
  | _ => OutOfFuel
  end.

(* Functional version of the lazy dfa *)
Definition lazydfa_match (r:regex) (inp:input) : matchres :=
  let code := compilation r in
  let fuel := inpsize inp in
  let init_st := initial_ldfa_state code inp in
  getres (ldfa_main_loop code inp init_st fuel).

(** * Smallstep correspondence  *)

Ltac match_destr:=
  match goal with
  | [ H : match ?x with _ => _ end = _  |- _ ] => let H := fresh "H" in destruct x eqn:H
  end.

Ltac solver:=
  match goal with
  | [H: get_pc ?c ?pc = _ |- match get_pc ?c ?pc with _ => _ end = _ ] => rewrite H 
  | _ => unfold is_epsilon, is_epsilon_break, is_epsilon_skip, is_nextloop_skip in *; subst; auto
  end.

(****** EPSILON ******)

Inductive eps_final_state: ldfa_epsilon_state -> Prop :=
| lefinal: forall best, eps_final_state (LDFA_Eps_Done best).

Inductive epsres : Type :=
| EpsOutOfFuel
| EpsFinished: dfa_state -> epsres.

Definition eps_getres (st:ldfa_epsilon_state) : epsres :=
  match st with
  | LDFA_Eps_Done out => EpsFinished out
  | _ => EpsOutOfFuel
  end.

Definition ldfa_eps_match (r:regex) (inp:input) : epsres :=
  let code := compilation r in
  let fuel := eps_complexity r in
  let init_st := initial_epsilon_state inp in
  eps_getres (ldfa_epsilon_loop code init_st fuel).

Theorem eps_func_step_correct:
  forall c st1 st2,
    ldfa_epsilon_step c st1 = st2 ->
    epsilon_loop_rel rer c st1 st2 \/ eps_final_state st1.
Proof.
  unfold ldfa_epsilon_step. intros c st1 st2 H.
  repeat match_destr; subst; try solve[left; constructor; repeat solver].
  5: right; constructor.
  all: left.
  - eapply elr_anc_sat; eauto.
  - eapply elr_anc_unsat; eauto.
  - eapply elr_fork ; eauto.
  - eapply elr_endloop_unsat; eauto.
Qed.

Corollary eps_func_step_not_final:
  forall c inp out wq,
    epsilon_loop_rel rer c (LDFA_Eps_Running inp out wq) (ldfa_epsilon_step c (LDFA_Eps_Running inp out wq)).
Proof.
  intros. specialize (eps_func_step_correct c (LDFA_Eps_Running inp out wq) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem eps_loop_trc:
  forall c st1 st2 fuel,
    ldfa_epsilon_loop c st1 fuel = st2 ->
    clos_refl_trans_1n _ (epsilon_loop_rel rer c) st1 st2.
Proof.
  intros c st1 st2 fuel H.
  generalize dependent st1. induction fuel; intros; simpl in H.
  { destruct st1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply eps_func_step_not_final.
  - constructor.
Qed.

Lemma eps_step_loop:
  forall c st1 st2 fuel,
    epsilon_loop_rel rer c st1 st2 ->
    ldfa_epsilon_loop c st1 (S fuel) = ldfa_epsilon_loop c st2 fuel.
Proof.
  intros c st1 st2 fuel H. destruct H; simpl in *;
    try now rewrite ?SEEN, ?NOTSEEN, ?FORK_PC, ?JMP_PC, ?ANC_PC, ?ANC_UNSAT, ?ANC_SAT, ?BGNLOOP_PC, ?ENDLOOP_PC, ?ENDLOOP_EXIT, ?ENDLOOP_BLOCKED.
    all:unfold is_epsilon_break, is_epsilon_skip in *; destruct (get_pc c (fst curr)); destruct b; rewrite NOTSEEN; try congruence; auto.
Qed.

Theorem eps_steps_loop:
  forall c st1 st2 fuel,
    steps (epsilon_loop_rel rer c) st1 fuel (LDFA_Eps_Done st2) ->
    ldfa_epsilon_loop c st1 fuel = (LDFA_Eps_Done st2).
Proof.
  intros. remember (LDFA_Eps_Done st2) as result.
  induction H; subst.
  - destruct n; simpl; auto.
  - destruct x.
    2: { inversion STEP. }
    erewrite eps_step_loop; eauto.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem eps_match_correct:
  forall r inp result,
    ldfa_eps_match r inp = EpsFinished result ->
    clos_refl_trans_1n _ (epsilon_loop_rel rer (compilation r)) (initial_epsilon_state inp) (LDFA_Eps_Done result).
Proof.
  unfold ldfa_eps_match, eps_getres. intros.
  match_destr; inversion H; subst.
  eapply eps_loop_trc; eauto.
Qed.

(* the function always terminates *)
Theorem eps_match_terminates:
  forall r inp,
    pike_regex r ->
    exists result, ldfa_eps_match r inp = EpsFinished result.
Proof.
  intros r inp SUBSET. unfold ldfa_eps_match.
  eapply ldfa_eps_complexity with (rer:=rer) (disj:=disj) (r:=r) (inp:=inp) in SUBSET as [result STEPS].
  exists result. apply eps_steps_loop in STEPS. rewrite STEPS. auto.
Qed.

(****** NEXT ******)

Inductive next_final_state: ldfa_nextloop_state -> Prop :=
| lnfinal: forall next fm, next_final_state (LDFA_Next_Done next fm).
(* 
Inductive nextres : Type :=
| NextOutOfFuel
| NextFinished: dfa_state -> bool -> nextres.

Definition next_getres (st:ldfa_nextloop_state) : nextres :=
  match st with
  | LDFA_Next_Done next fm => NextFinished next fm
  | _ => NextOutOfFuel
  end.

Definition ldfa_next_match (r:regex) (inp:input) : nextres :=
  let code := compilation r in
  let fuel := next_complexity r in
  let init_st := initial_next_state inp in
  next_getres (ldfa_next_loop code init_st fuel). *)

Theorem next_func_step_correct:
  forall c inp st1 st2,
    ldfa_next_step c inp st1 = st2 ->
    next_loop_rel rer c inp st1 st2 \/ next_final_state st1.
Proof.
  unfold ldfa_next_step. intros.
  repeat match_destr; subst; try solve[left; constructor; repeat solver].
  4: right; constructor.
  all: left.
  - (* contradiction *) 
    
    admit.
  - eapply nlr_consume; eauto. apply clos_rt1n_rt. eapply eps_loop_trc; eauto.
  - eapply nlr_noconsume; eauto.
Admitted.

Corollary next_func_step_not_final:
  forall c inp next curr_pcs,
    next_loop_rel rer c inp (LDFA_Next_Running next curr_pcs) (ldfa_next_step c inp (LDFA_Next_Running next curr_pcs)).
Proof.
  intros. specialize (next_func_step_correct c inp (LDFA_Next_Running next curr_pcs) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem next_loop_trc:
  forall c inp s1 s2 fuel,
    ldfa_next_loop c inp s1 fuel = s2 ->
    clos_refl_trans_1n _ (next_loop_rel rer c inp) s1 s2.
Proof.
  intros.
  generalize dependent s1. induction fuel; intros; simpl in H.
  { destruct s1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply next_func_step_not_final.
  - constructor.
Qed.

Lemma next_step_loop:
  forall c inp s1 s2 fuel,
    next_loop_rel rer c inp s1 s2 ->
    ldfa_next_loop c inp s1 (S fuel) = ldfa_next_loop c inp s2 fuel.
Proof.
  intros. destruct H;
    try solve [simpl in *; now rewrite ?ACCEPT_PC, ?CONSUME_PC, ?CANT_READ_CHAR, ?KILL_PC].
    - pose proof (crt_steps _ _ _ _ EPSI) as [n' STEPS]. pose proof (eps_steps_loop _ _ _ _ STEPS) as EPSLOOP. 
    cbn [ldfa_next_loop]. cbn [ldfa_next_step]. rewrite CONSUME_PC, CAN_READ_CHAR. 
    replace n' with (ldfa_eps_fuel c) in EPSLOOP. rewrite EPSLOOP; auto. admit.
    - unfold is_nextloop_skip in *. simpl in *. destruct (get_pc c (fst pc)); destruct b; try congruence; auto.
Admitted.

Theorem next_steps_loop:
  forall c inp s1 s2 fm fuel,
    steps (next_loop_rel rer c inp) s1 fuel (LDFA_Next_Done s2 fm) ->
    ldfa_next_loop c inp s1 fuel = (LDFA_Next_Done s2 fm).
Proof.
  intros. remember (LDFA_Next_Done s2 fm) as result.
  induction H; subst.
  - destruct n; simpl; auto.
  - destruct x.
    2: { inversion STEP. }
    erewrite next_step_loop; eauto.
Qed.
(* 
(* when the function finishes, it returns the correct result *)
Theorem next_match_correct:
  forall r inp result,
    ldfa_next_match r inp = NextFinished result ->
    clos_refl_trans_1n _ (next_loop_rel rer (compilation r)) (initial_next_state inp) (LDFA_Next_Done result).
Proof.
  unfold ldfa_next_match, next_getres. intros.
  match_destr; inversion H; subst.
  eapply next_loop_trc; eauto.
Qed.

(* the function always terminates *)
Theorem next_match_terminates:
  forall r inp,
    pike_regex r ->
    exists result, ldfa_next_match r inp = NextFinished result.
Proof.
  intros r inp SUBSET. unfold ldfa_next_match.
  eapply ldfa_next_complexity with (rer:=rer) (disj:=disj) (r:=r) (inp:=inp) in SUBSET as [result STEPS].
  exists result. apply next_steps_loop in STEPS. rewrite STEPS. auto.
Qed. *)

(****** MAIN *******)

Inductive final_state: ldfa_state -> Prop :=
| lfinal: forall best, final_state (LDFA_final best).

Theorem func_step_correct:
  forall c inp s1 s2,
    ldfa_main_step c inp s1 = s2 ->
    ldfa_loop_rel rer c s1 s2 \/ final_state s1.
Proof.
  unfold ldfa_main_step. intros.
  repeat match_destr; subst; try solve[left; constructor; auto].
  7: right; constructor.
  all: left.
  - eapply ldfalr_cached_match; eauto.
  - eapply ldfalr_cached_nomatch; eauto.
  - (* contradiction *) admit.
  - eapply ldfalr_new_match; eauto. apply clos_rt1n_rt; eapply next_loop_trc; eauto.
  -  eapply ldfalr_new_nomatch; eauto. apply clos_rt1n_rt; eapply next_loop_trc; eauto.
  - destruct (advance_next_char inp0 i H1) as [ch h]; congruence.
Admitted.

Corollary func_step_not_final:
  forall c curr i ttab best,
    ldfa_loop_rel rer c (LDFA curr i ttab best) (ldfa_main_step c i (LDFA curr i ttab best)).
Proof.
  intros. specialize (func_step_correct c i (LDFA curr i ttab best) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem loop_trc:
  forall c inp s1 s2 fuel,
    ldfa_main_loop c inp s1 fuel = s2 ->
    clos_refl_trans_1n _ (ldfa_loop_rel rer c) s1 s2.
Proof.
  intros.
  generalize dependent s1. induction fuel; intros; simpl in H.
  { destruct s1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply func_step_not_final with (i:=inp0).
  - constructor.
Qed.

Lemma step_loop:
  forall c inp s1 s2 fuel,
    ldfa_loop_rel rer c s1 s2 ->
    ldfa_main_loop c inp s1 (S fuel) = ldfa_main_loop c inp s2 fuel.
Proof.
  intros. destruct H; simpl in *;
    try now rewrite ?EOI, ?HAS_MATCH, ?NO_MATCH, ?NEXT_CHAR, ?CACHED_TRANS, ?ADVANCE.
  all: rewrite ADVANCE, NEXT_CHAR, NOT_CACHED_TRANS; 
  pose proof (crt_steps _ _ _ _ COMP_NEXT) as [n' STEPS]; 
  pose proof (next_steps_loop _ _ _ _ _ _ STEPS) as NEXTLOOP;
  replace n' with (length curr + 1) in NEXTLOOP; try (rewrite NEXTLOOP; auto). 
  all: admit.
Admitted.

Theorem steps_loop:
  forall c inp s1 s2 fuel,
    steps (ldfa_loop_rel rer c) s1 fuel (LDFA_final s2) ->
    ldfa_main_loop c inp s1 fuel = (LDFA_final s2).
Proof.
  intros. remember (LDFA_final s2) as result.
  induction H; subst.
  - destruct n; simpl; auto.
  - destruct x.
    2: { inversion STEP. }
    erewrite step_loop; eauto.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem ldfa_match_correct:
  forall r inp result,
    lazydfa_match r inp = Finished result ->
    clos_refl_trans_1n _ (ldfa_loop_rel rer (compilation r)) (initial_ldfa_state (compilation r) inp) (LDFA_final result).
Proof.
  unfold lazydfa_match, getres. intros.
  match_destr; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(* the function always terminates *)
Theorem ldfa_match_terminates:
  forall r inp,
    pike_regex r ->
    exists result, lazydfa_match r inp = Finished result.
Proof.
  intros r inp SUBSET. unfold lazydfa_match.
  remember (initial_ldfa_state (compilation r) inp) as init_st.
  unfold initial_ldfa_state in *.
  eapply ldfa_complexity with (rer:=rer) (disj:=disj) (r:=r) (inp:=inp) in SUBSET as [result STEPS].
  exists result; apply steps_loop with (inp:=inp) in STEPS; rewrite STEPS; auto. 
  unfold initial_ldfa_rel, epsilon_closure_rel. 
  destruct (ldfa_epsilon_loop (compilation r) (initial_epsilon_state inp) (ldfa_eps_fuel (compilation r))) eqn:h.
  - (* contradiction *) admit.
  - exists out; split; auto. apply clos_rt1n_rt. apply eps_loop_trc with (fuel:=(ldfa_eps_fuel (compilation r))); auto.
Admitted.

End FunctionalLazyDFA.