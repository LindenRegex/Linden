(* The PikeVm algorithm, expressed as a fuel-based function *)

Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import PikeVM Correctness SeenSets Semantics.Examples.
From Linden Require Import Complexity.
From Linden Require Import Parameters.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import FunctionalUtils FunctionalSemantics.
Require Import Derive.

Section FunctionalPikeVM.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context (rer: RegExpRecord).
(** * Functional Definition  *)

(* a functional version of the small step *)
Definition pike_vm_func_step (c:code) (pvs:pike_vm_state) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | PVS inp active best blocked seen =>
      match active with
      | [] =>
          match blocked with
          | [] => PVS_final best (* pvs_final *)
          | thr::blocked =>
              match (advance_input inp forward) with
              | None => PVS_final best (* pvs_end *)
              | Some nextinp => PVS nextinp (thr::blocked) best [] initial_seenpcs (* pvs_nextchar *)
              end
          end     
      | t::active =>
          match (seen_thread seen t) with
          | true => PVS inp active best blocked seen (* pvs_skip *)
          | false =>
              let nextseen := add_thread seen t in
              match (epsilon_step rer t c inp) with
              | EpsActive nextactive =>
                  PVS inp (nextactive++active) best blocked nextseen (* pvs_active *)
              | EpsMatch =>
                  PVS inp [] (Some (inp,gm_of t)) blocked nextseen (* pvs_match *)
              | EpsBlocked newt =>
                  PVS inp active best (blocked ++ [newt]) nextseen (* pvs_blocked *)
              end
          end
      end
  end.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint pike_vm_loop (c:code) (pvs:pike_vm_state) (fuel:nat) : pike_vm_state :=
  match pvs with
  | PVS_final _ => pvs
  | _ =>
      match fuel with
      | 0 => pvs
      | S fuel =>
          pike_vm_loop c (pike_vm_func_step c pvs) fuel
      end
  end.

(* an upper bound for the fuel necessary to compute a result *)
Definition vm_fuel (r:regex) (inp:input) : nat :=
  complexity r inp. 

Inductive matchres : Type :=
| OutOfFuel
| Finished: option leaf -> matchres.

Definition getres (pvs:pike_vm_state) : matchres :=
  match pvs with
  | PVS_final best => Finished best
  | _ => OutOfFuel
  end.

(* Functional version of the PikeVM *)
Definition pike_vm_match (r:regex) (inp:input) : matchres :=
  let code := compilation r in
  let fuel := vm_fuel r inp in
  let pvsinit := pike_vm_initial_state inp in
  getres (pike_vm_loop code pvsinit fuel).
                                                   

(** * Smallstep correspondence  *)

Inductive final_state: pike_vm_state -> Prop :=
| pfinal: forall best, final_state (PVS_final best).

Ltac match_destr:=
  match goal with
  | [ H : match ?x with _ => _ end = _  |- _ ] => let H := fresh "H" in destruct x eqn:H
  end.

Theorem func_step_correct:
  forall c pvs1 pvs2,
    pike_vm_func_step c pvs1 = pvs2 ->
    pike_vm_step rer c pvs1 pvs2 \/ final_state pvs1.
Proof.
  unfold pike_vm_func_step. intros c pvs1 pvs2 H.
  repeat match_destr; subst; try solve[left; constructor; auto].
  right. constructor.
Qed.

Corollary func_step_not_final:
  forall c inp active best blocked seen,
    pike_vm_step rer c (PVS inp active best blocked seen) (pike_vm_func_step c (PVS inp active best blocked seen)).
Proof.
  intros c inp active best blocked seen. specialize (func_step_correct c (PVS inp active best blocked seen) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem loop_trc:
  forall c pvs1 pvs2 fuel,
    pike_vm_loop c pvs1 fuel = pvs2 ->
    trc_pike_vm rer c pvs1 pvs2.
Proof.
  intros c pvs1 pvs2 fuel H.
  generalize dependent pvs1. induction fuel; intros; simpl in H.
  { destruct pvs1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply func_step_not_final. apply IHfuel. auto.
  - constructor.
Qed.

Lemma step_loop:
  forall c pvs1 pvs2 fuel,
    pike_vm_step rer c pvs1 pvs2 ->
    pike_vm_loop c pvs1 (S fuel) = pike_vm_loop c pvs2 fuel.
Proof.
  intros c pvs1 pvs2 fuel H. destruct H; simpl; auto.
  - destruct blocked; auto.
    rewrite ADVANCE; auto.
  - rewrite ADVANCE; auto.
  - rewrite SEEN; auto.
  - rewrite UNSEEN; rewrite STEP; auto.
  - rewrite UNSEEN; rewrite STEP; auto.
  - rewrite UNSEEN; rewrite STEP; auto.
Qed.

Theorem steps_loop:
  forall c pvs1 pvs2 fuel,
    steps (pike_vm_step rer c) pvs1 fuel (PVS_final pvs2) ->
    pike_vm_loop c pvs1 fuel = (PVS_final pvs2).
Proof.
  intros c pvs1 pvs2 fuel H. remember (PVS_final pvs2) as result.
  induction H; subst.
  - destruct n; simpl; auto.
  - destruct x.
    2: { inversion STEP. }
    erewrite step_loop; eauto.
Qed.


(* when the function finishes, it retruns the correct result *)
Theorem pike_vm_match_correct:
  forall r inp result,
    pike_vm_match r inp = Finished result ->
    trc_pike_vm rer (compilation r) (pike_vm_initial_state inp) (PVS_final result).
Proof.
  unfold pike_vm_match, getres. intros r inp result H. 
  match_destr; subst; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(* the function always terminates *)
Theorem pike_vm_match_terminates:
  forall r inp,
    pike_regex r ->
    exists result, pike_vm_match r inp = Finished result.
Proof.
  intros r inp SUBSET. unfold pike_vm_match, vm_fuel.
  apply pikevm_complexity with (VMS:=VMS) (rer:=rer) (inp:=inp) in SUBSET as [result TERM].
  exists result. apply steps_loop in TERM. rewrite TERM. auto.
Qed.

(* unrolling one PikeVM step   *)
Lemma unroll_loop:
  forall code inp active best blocked seen fuel,
    pike_vm_loop code (PVS inp active best blocked seen) (S fuel) =
      pike_vm_loop code (pike_vm_func_step code (PVS inp active best blocked seen)) fuel.
Proof. auto. Qed.

End FunctionalPikeVM.

(** * Execution Examples  *)

From Linden Require Import Inst.
From Warblre Require Import Inst.
Require Import Coq.Strings.Ascii Coq.Strings.String.
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
    pike_vm_match (rer_of nq_regex) nq_regex nq_inp = Finished (Some (Input [] [b;a], GroupMap.empty)).
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
  pike_vm_match (rer_of paper_regex) paper_regex paper_input = Finished (Some (Input [] [b;a], final_gm)).
Proof. reflexivity. Qed.

Notation compute x :=
  ltac:(let c := (eval cbv in x) in exact c).

Derive paper_exec SuchThat
  (forall inp,
      let r := paper_regex in
      let rer := rer_of r in
      let code := compilation r in
      forall t g bb tl,
      let pvs := PVS inp ((t, g, bb) :: tl) None [] initial_seenpcs in
      (* let fuel := 10 in *)
      (* let pvsinit := pike_vm_initial_state inp in *)
      pike_vm_func_step rer code pvs
        (* pike_vm_loop rer code pvsinit fuel *)
      = paper_exec t g bb tl inp)
  As paper_exec_correct.
Proof.
  remember paper_exec as body eqn:Heq; rewrite Heq;
    subst paper_exec.
  instantiate (1 := ltac:(intros t g bb tl inp)); cbv beta.
  (* unshelve instantiate (1 := ?[body]); cycle 1. *)

  intros.
  cbv -[naive_params] in code.
  cbv -[naive_params] in rer; subst rer.
  simpl; unfold EpsDead.

  Ltac compute_pc :=
    change (get_pc ?c ?t') with (compute (get_pc c t')); cbv iota.

  Ltac step t :=
    match goal with
    | [  |- context[match get_pc _ _ with _ => _ end] ] =>
        instantiate (1 := ltac:(destruct t)); destruct t;
        [ compute_pc | ]
    | [  |- context[match @check_read ?params ?rer ?c ?inp ?fw with _ => _ end]] =>
        instantiate (1 := ltac:(destruct (@check_read params rer c inp fw)));
        destruct (@check_read params rer c inp fw); cbv zeta iota
    | [  |- context[match ?b with CanExit => _ | CannotExit => _ end]] =>
        instantiate (1 := ltac:(destruct b));
        destruct b; cbv zeta iota
    end.

  Ltac refl :=
    repeat match goal with
      | [ h := _ |- _ ] => subst h
      end; reflexivity.

  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  step t; [ repeat step 0; refl | cbv beta in Heq ].
  compute_pc.
  simpl List.app in Heq.
  simpl Nat.add in Heq.
  unfold check_read in Heq.
Qed.

  Unshelve.
  12: {

    (* instantiate (1 := ?[f]). *)
    (* [f]: { *)
    match goal with
    end.

    all: reflexivity

  simpl.
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].
  step t; [ reflexivity | ].

  all: repeat match goal with
         | [  |- context[match get_pc _ _ with _ => _ end] ] =>
             instantiate (1 := ltac:(destruct t)); destruct t;
             [ ;
                | ]
         end.




  do 13 try destruct t.
  all: cbv beta.
  do 13 try destruct t.
  all: change (get_pc ?c ?t') with (compute (get_pc c t')); unfold EpsDead; cbv iota.

  do 10 match goal with
    | [  |- context[get_pc _ _] ] =>

        destruct t;
        [ change (get_pc ?c ?t') with (compute (get_pc c t')); cbv iota | ]
    | _ =>
        idtac
    end.
  destruct t [.
  simpl.
  intros.
  subst pvs.
  unfold pike_vm_func_step.
  simpl.
  unfold epsilon_step.
  simpl get_pc.
  cbv iota.
  simpl seen_thread.
  cbv iota.



  (* remember (vm_fuel paper_regex (Input s [])) as fuel. *)

  cbv in code.
  Arguments pike_vm_initial_state !_ /.
  simpl in pvsinit.
  cbv in rer.
  subst rer code pvsinit.
  unfold pike_vm_loop.


  change (pike_vm_initial_state ?i) with (compute (pike_vm_initial_state i)).
  change (rer_of ?r) with (compute (rer_of r)).
  change (compilation ?r) with (compute (compilation r)).

  assert nat as n by exact 0.
  set (vm_fuel _ _).

  remember (vm_fuel _ _) as fuel.
  remember (compilation _) as c eqn:Hc; cbv in Hc; subst c.
  remember (rer_of _) as c eqn:Hc.

  cbv in c. ; subst c.



  simpl pike_vm_initial_state.
  replace (vm_fuel paper_regex (Input s [])) with 7 by admit; simpl.

  Unshelve.
  intros.
  simpl.
  simpl.
  all: intros; cbv beta.
  intros.

  body: []
  intros.

  destruct s.


End Example.
