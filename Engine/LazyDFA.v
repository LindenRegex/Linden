From Stdlib Require Import List Lia Bool.
From Stdlib Require Import Relation_Definitions Relation_Operators.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics.
From Linden Require Import Parameters SeenSets Prefix.
From Warblre Require Import Base RegExpRecord.


Section LazyDFA.
  Context {params: LindenParameters}.
  (* Context {VMS: VMSeen}. *)
  Context (rer: RegExpRecord).  

(* todo this should probs be in chars *)
Definition next_char (i: input) : option Character :=
	match (next_str i) with
	| c::tail => Some c
	| _ => None
	end.


Definition internal_state: Type := (label * LoopBool). (* "nfa state" *)
Definition internal_state_eq_dec : forall x y : internal_state, {x = y} + {x <> y}.
Proof. repeat (decide equality). Defined.
Definition is_epsilon (c: code) (i: internal_state) : bool :=
	match get_pc c (fst i) with
	| Some (Fork _ _) | Some (EndLoop _) | Some (Jmp _) | Some (CheckAnchor _) | Some (BeginLoop) => true 
	| _ => false
	end. 

Definition dfa_state: Type := list internal_state.
Definition dfa_state_eq_dec : forall x y : dfa_state, {x = y} + {x <> y}.
Proof. repeat (decide equality). Defined.

Definition dec_eqb {T} (dec : forall x y : T, {x = y} + {x <> y}) (x y : T) : bool :=
  if dec x y then true else false.

Definition dfa_state_contains (st: dfa_state) (i: internal_state) : bool :=
	List.existsb (fun x => dec_eqb internal_state_eq_dec x i) st.

Definition dfa_state_hasmatch (c:code) (st: dfa_state) : bool :=
	List.existsb (fun '(l, b) => match (get_pc c l) with | Some Accept => true | _ => false end) st.

(* could opti by doing range of bytes instead of having one line in the cache per character... *)
Definition transition_table: Type := list (dfa_state * Character * dfa_state * bool). (* current state & char -> next state & found_match *)

(* get next state if cached in table, given current state and what character we're reading *)
Definition get_trans (table: transition_table) (curr: dfa_state) (char: Character) : option (dfa_state * bool) :=
    option_map (fun '(_, _, s', fm) => (s', fm))
    (find (fun '(s, c, _, _) => dec_eqb dfa_state_eq_dec s curr
                          && dec_eqb EqDec.eq_dec c char) table).

Definition add_trans (table : transition_table) (curr : dfa_state) (char : Character)
  (next : dfa_state) (found_match : bool) : transition_table :=
  (curr, char, next, found_match) :: table.

(* states of the LazyDFA algorithm *)
Inductive ldfa_state : Type :=
| LDFA (curr:  dfa_state) (inp: input) (ttab: transition_table) (best: option input) (*next: dfa_state*)
| LDFA_final (res:option input). (* seulement à la toute fin de la main loop *)
(* assuming that we have an anchored search, we just need to report the input, since we have no capture group *)


(********** epsilon-exploration **********)

Inductive ldfa_epsilon_state : Type :=
| LDFA_Eps_Running (inp: input) (out: dfa_state) (workqueue: dfa_state)
| LDFA_Eps_Done (out: dfa_state).

Definition is_epsilon_break (c:code) (curr: internal_state) : bool :=
match get_pc c (fst curr) with
| None | Some (Consume _) | Some (KillThread) | Some (Accept) => true
| _ => false
end.

Definition is_epsilon_skip (c:code) (curr:internal_state) : bool :=
match get_pc c (fst curr) with
| Some (SetRegOpen _) | Some (SetRegClose _) | Some (ResetRegs _) => true
| _ => false
end.

Definition next_step (curr:internal_state) : internal_state := (fst curr + 1, snd curr).

(*
	Return the list (ordered by priority) of nfa states (constituant un dfa_state) reachable through epsilon transitions (without consuming input)
	from given nfa_start_state (with its boolean for nullable quantifier), and given the input to check the anchors
	attention ! on doit passer out, parce que le set est partagé entre les states du ldfa 
	equiv to epsilon_closure_single, de base c'est appelé avec une workqueue contenant que 1 nfa_state 
*)
Inductive epsilon_loop_rel (c: code): ldfa_epsilon_state -> ldfa_epsilon_state -> Prop :=
| elr_final : forall inp out, (* return out when workqueue empty *)
	epsilon_loop_rel c (LDFA_Eps_Running inp out []) (LDFA_Eps_Done out) 
| elr_seen : (* if curr is already in out, we skip it and work on the rest of the workqueue *)
	forall inp out curr tail 
	(SEEN: dfa_state_contains out curr = true),
		epsilon_loop_rel c (LDFA_Eps_Running inp out (curr :: tail)) (LDFA_Eps_Running inp out (tail))
| elr_break : (* break : we go back to the workqueue pop after inserting curr at the end *)
	forall inp out (curr: internal_state) (tail: dfa_state) 
	(NOTSEEN: dfa_state_contains out curr = false) 
	(BREAK_PCS: is_epsilon_break c curr = true),
		epsilon_loop_rel c (LDFA_Eps_Running inp out (curr :: tail)) (LDFA_Eps_Running inp (out ++ [curr]) (tail))
| elr_fork : (* we insert current in out, and head of workqueue is direct followup, but we also add the future explo at the tail *)
	forall inp out curr tail out1 out2 
	(NOTSEEN: dfa_state_contains out curr = false) 
	(FORK_PC: get_pc c (fst curr) = Some (Fork out1 out2)),
		epsilon_loop_rel c 	(LDFA_Eps_Running inp out (curr :: tail)) 
							(LDFA_Eps_Running inp (out ++ [curr]) ((out1, snd curr) :: [(out2, snd curr)] ++ tail))
| elr_jmp : (* jump : we go to the indicated label *)
	forall inp out curr tail l 
	(NOTSEEN: dfa_state_contains out curr = false) 
	(JMP_PC: get_pc c (fst curr) = Some (Jmp l)),
		epsilon_loop_rel c (LDFA_Eps_Running inp out (curr :: tail)) (LDFA_Eps_Running inp (out ++ [curr]) ((l, snd curr) :: tail))
| elr_anc_unsat : (* not satisfied anchor : the current thread dies *)
	forall inp out curr tail anc 
	(NOTSEEN: dfa_state_contains out curr = false)
	(ANC_PC: get_pc c (fst curr) = Some (CheckAnchor anc))
	(ANC_UNSAT: anchor_satisfied rer anc inp = false),
		epsilon_loop_rel c (LDFA_Eps_Running inp out (curr :: tail)) (LDFA_Eps_Running inp (out ++ [curr]) (tail))
| elr_anc_sat : (* satisfied anchor : we continue to the next pc *)
	forall inp out curr tail anc 
	(NOTSEEN: dfa_state_contains out curr = false)
	(ANC_PC: get_pc c (fst curr) = Some (CheckAnchor anc))
	(ANC_SAT: anchor_satisfied rer anc inp = true),
		epsilon_loop_rel c 	(LDFA_Eps_Running inp out (curr :: tail)) 
							(LDFA_Eps_Running inp (out ++ [curr]) ((next_step curr) :: tail))
| elr_bgnloop : (* beginloop : we continue to next pc and set loop bool *)
	forall inp out curr tail 
	(NOTSEEN: dfa_state_contains out curr = false) 
	(BGNLOOP_PC: get_pc c (fst curr) = Some (BeginLoop)),
		epsilon_loop_rel c 	(LDFA_Eps_Running inp out (curr :: tail)) 
							(LDFA_Eps_Running inp (out ++ [curr]) ((fst curr + 1, CannotExit) :: tail))
| elr_endloop_sat : (* end_loop which can exit : we continue to next label *)
	forall inp out curr tail l 
	(NOTSEEN: dfa_state_contains out curr = false)
	(ENDLOOP_PC: get_pc c (fst curr) = Some (EndLoop l))
	(ENDLOOP_EXIT: (snd curr) = CanExit),
		epsilon_loop_rel c (LDFA_Eps_Running inp out (curr :: tail)) (LDFA_Eps_Running inp (out ++ [curr]) ((l, CanExit) :: tail))
| elr_endloop_unsat : (* end_loop which cannot exit : the current thread dies, we break *)
	forall inp out curr tail l 
	(NOTSEEN: dfa_state_contains out curr = false)
	(ENDLOOP_PC: get_pc c (fst curr) = Some (EndLoop l))
	(ENDLOOP_BLOCKED: (snd curr) = CannotExit),
		epsilon_loop_rel c (LDFA_Eps_Running inp out (curr :: tail)) (LDFA_Eps_Running inp (out ++ [curr]) (tail))
| elr_reg_skip : (* we consider capture groups operations as nop and simply skip them *)
	forall inp out (curr: internal_state) (tail: dfa_state) 
	(NOTSEEN: dfa_state_contains out curr = false) 
	(SKIP_PCS: is_epsilon_skip c curr = true),
		epsilon_loop_rel c (LDFA_Eps_Running inp out (curr :: tail)) (LDFA_Eps_Running inp (out ++ [curr]) ((next_step curr) :: tail)).


(********** compute next nfa states **********)


Inductive ldfa_nextloop_state : Type :=
| LDFA_Next_Running (next: dfa_state) (current_pcs: dfa_state)
| LDFA_Next_Done (next: dfa_state) (found_match: bool).

Definition is_nextloop_skip (c:code) (curr:internal_state) : bool :=
match get_pc c (fst curr) with
| Some (Consume _) | Some Accept | Some KillThread => false
| _ => true
end.

Inductive next_loop_rel (c:code) (i:input) : ldfa_nextloop_state -> ldfa_nextloop_state -> Prop :=
| nlr_final : forall n,
	next_loop_rel c i (LDFA_Next_Running n []) (LDFA_Next_Done n false)
| nlr_accept : forall n pc pcs
	(ACCEPT_PC: get_pc c (fst pc) = Some (Accept)),
		next_loop_rel c i (LDFA_Next_Running n (pc :: pcs)) (LDFA_Next_Done n true)
| nlr_consume : forall n pc pcs cd out
	(CONSUME_PC: get_pc c (fst pc) = Some (Consume cd))
	(CAN_READ_CHAR: check_read rer cd i forward = CanRead)
	(* have to pass current n as the "out" since it's shared between current threads *)
	(EPSI: clos_refl_trans _ (epsilon_loop_rel c) (LDFA_Eps_Running i n ([next_step pc])) (LDFA_Eps_Done out)),
		next_loop_rel c i (LDFA_Next_Running n (pc :: pcs)) (LDFA_Next_Running (n ++ out) pcs)
| nlr_noconsume : forall n pc pcs cd (* if we can't read, we skip *)
	(CONSUME_PC: get_pc c (fst pc) = Some (Consume cd))
	(CANT_READ_CHAR: check_read rer cd i forward = CannotRead),
		next_loop_rel c i (LDFA_Next_Running n (pc :: pcs)) (LDFA_Next_Running n pcs)
| nlr_skip : forall n pc pcs
	(SKIP_PCS: is_nextloop_skip c pc = true),
		next_loop_rel c i (LDFA_Next_Running n (pc :: pcs)) (LDFA_Next_Running n pcs)
| nlr_kill : forall n pc pcs
	(KILL_PC: get_pc c (fst pc) = Some (KillThread)),
		next_loop_rel c i (LDFA_Next_Running n (pc :: pcs)) (LDFA_Next_Done [] false).


(********** main loop **********)

(* 
| LDFA (curr: dfa_state) (inp: input) (ttab: transition_table) (best: option input) (next: dfa_state)
| LDFA_final (res:option input). 
assuming init_state : LDFA (curr = (epsilon_closure c i [] code@0)) (i) (ttab = []) (best = None)
assuming infinite cache for now : could late add non deterministic step that clears the cache
*)
Inductive ldfa_loop_rel (c:code) : ldfa_state -> ldfa_state -> Prop := 
| ldfalr_final_match : forall i curr ttab best
	(* if we're at the end of the input, we check if there was a match at the last char then return the best match *)
	(EOI: advance_input i forward = None)
	(HAS_MATCH: dfa_state_hasmatch c curr = true),
			ldfa_loop_rel c (LDFA curr i ttab best) (LDFA_final (Some i))
| ldfalr_final_nomatch : forall i curr ttab best
	(* if we're at the end of the input, we check if there was a match at the last char then return the best match *)
	(EOI: advance_input i forward = None)
	(NO_MATCH: dfa_state_hasmatch c curr = false),			
		ldfa_loop_rel c (LDFA curr i ttab best) (LDFA_final best)
| ldfalr_cached_match : forall curr i ttab best next next_i char (* if next state is cached and contains a match *)
	(NEXT_CHAR: next_char i = Some char)
	(CACHED_TRANS: get_trans ttab curr char = Some (next, true))
	(ADVANCE: advance_input i forward = Some next_i),
		ldfa_loop_rel c (LDFA curr i ttab best) (LDFA next next_i ttab (Some i)) (* update curr, inp, best *)
| ldfalr_cached_nomatch : forall curr i ttab best next next_i char (* if next state is cached and doesn't have a match *)
	(NEXT_CHAR: next_char i = Some char)
	(CACHED_TRANS: get_trans ttab curr char = Some (next, false))
	(ADVANCE: advance_input i forward = Some next_i),
		ldfa_loop_rel c (LDFA curr i ttab best) (LDFA next next_i ttab best) (* update curr, inp *)
| ldfalr_new_match : forall curr i ttab best next next_i char (* if next state isn't cached, we calc it and it has match *)
	(NEXT_CHAR: next_char i = Some char)
	(NOT_CACHED_TRANS: get_trans ttab curr char = None)
	(ADVANCE: advance_input i forward = Some next_i)
	(COMP_NEXT: clos_refl_trans _ (next_loop_rel c i) (LDFA_Next_Running [] curr) (LDFA_Next_Done next true)),
		let next_ttab := (add_trans ttab curr char next true) in
		ldfa_loop_rel c (LDFA curr i ttab best) (LDFA next next_i next_ttab (Some i)) (* update curr, inp, best, table *)
| ldfalr_new_nomatch : forall curr i ttab best next next_i char (* if next state isn't cached, we calc it and doesn't match *)
	(NEXT_CHAR: next_char i = Some char)
	(NOT_CACHED_TRANS: get_trans ttab curr char = None)
	(ADVANCE: advance_input i forward = Some next_i)
	(COMP_NEXT: clos_refl_trans _ (next_loop_rel c i) (LDFA_Next_Running [] curr) (LDFA_Next_Done next false)),
		let next_ttab := (add_trans ttab curr char next false) in
		ldfa_loop_rel c (LDFA curr i ttab best) (LDFA next next_i next_ttab best) (* update curr, inp, table *)
.


(********** initial state **********)

Definition initial_int_state : internal_state := (0, CanExit).
Definition initial_epsilon_state (inp: input) : ldfa_epsilon_state := LDFA_Eps_Running inp [] [initial_int_state].

Definition epsilon_closure_rel (c : code) (start : internal_state) (inp : input) (out : dfa_state) : Prop :=
  clos_refl_trans _ (epsilon_loop_rel c) (LDFA_Eps_Running inp [] [start]) (LDFA_Eps_Done out).

(* tells if given "st" state is an initial ldfa state *)
Definition initial_ldfa_rel (c : code) (inp : input) (st : ldfa_state) : Prop :=
  exists initial_dfa_state, epsilon_closure_rel c initial_int_state inp initial_dfa_state 
  							/\ st = LDFA initial_dfa_state inp [] None.


(********** determinism of the relations **********)

(* The epsilon step relation is deterministic *)
Theorem ldfa_epsilon_deterministic:
  forall c epso eps1 eps2
    (STEP1: epsilon_loop_rel c epso eps1)
    (STEP2: epsilon_loop_rel c epso eps2),
    eps1 = eps2.
Proof.
	intros. 
	inversion STEP1 ; subst; inversion STEP2; subst;
	unfold is_epsilon_break, is_epsilon_skip in *;
	repeat match goal with
	| H : get_pc ?c ?l = Some _ |- _ =>  rewrite H in *
	| H : context [match get_pc ?c ?l with _ => _ end] |- _ =>
      destruct (get_pc c l) as [ instr | ]; [ destruct instr | ]
  	end; try discriminate; try congruence.		  
Qed.

(* a done state can't eps-step to anything *)
Lemma eps_done_terminal : forall c out s,
  ~ epsilon_loop_rel c (LDFA_Eps_Done out) s.
Proof. intros c out s H. inversion H. Qed.

(* a done state can only eps-star to itself *)
Lemma rtc_eps_done : forall c out next,
  clos_refl_trans _ (epsilon_loop_rel c) (LDFA_Eps_Done out) next ->
  next = LDFA_Eps_Done out.
Proof.
  intros.
  remember (LDFA_Eps_Done out) as out_state.
  induction (H); subst.
  - pose proof (eps_done_terminal _ _ _ H0) as Hdone. contradiction.
  - reflexivity.
  - specialize (IHc0_1 eq_refl c0_1). subst.
  apply IHc0_2. reflexivity. apply H.
Qed.

(* 
	x -> y & x -*> b means 
	either x->y was the first (deter) step towards b and thus we can continue y-*>b 
	or it already is b
*)
Lemma rtc_eps_step : forall c x y b,
  epsilon_loop_rel c x y ->
  clos_refl_trans _ (epsilon_loop_rel c) x b ->
  clos_refl_trans _ (epsilon_loop_rel c) y b \/ b = x.
Proof.
  intros c x y b H_step H.
  revert y H_step.
  induction H as [x b Hb | | x m b H1 IH1 H2 IH2]; intros y H_step.
  - (* x -> b, and x -> y, so y = b & b -*> b *)
    assert (y = b) by (eapply ldfa_epsilon_deterministic; eauto).
    subst. left. apply rt_refl.
  - (* b = x *)
    right. reflexivity.
  - (* x ->* m ->* b *)
    destruct (IH1 _ H_step) as [Hym | Hmx].
    + (* y -*> m -*> b *) left. eapply rt_trans; eauto.
    + subst. apply IH2. exact H_step.
Qed.

Lemma rtc_eps_to_done : forall c start mid o
  (STARsm: clos_refl_trans _ (epsilon_loop_rel c) start mid)
  (STARsd: clos_refl_trans _ (epsilon_loop_rel c) start (LDFA_Eps_Done o)),
  clos_refl_trans _ (epsilon_loop_rel c) mid (LDFA_Eps_Done o).
Proof.
  intros.
  induction STARsm; intros.
  - destruct (rtc_eps_step _ _ _ _ H STARsd).
    + exact H0.
    + subst. exfalso. eapply eps_done_terminal; eauto.
  - assumption.
  - apply IHSTARsm2. apply IHSTARsm1. assumption.
Qed.

Lemma epsilon_rtc_deterministic : 
	forall c s out1 out2
		(CLOS1: clos_refl_trans _ (epsilon_loop_rel c) s (LDFA_Eps_Done out1)) 
		(CLOS2: clos_refl_trans _ (epsilon_loop_rel c) s (LDFA_Eps_Done out2)),
		out1 = out2.
Proof.
	intros.
	remember (LDFA_Eps_Done out1) as end1 eqn:Hend1.
	remember (LDFA_Eps_Done out2) as end2 eqn:Hend2.
  	revert out1 Hend1 (* out2 Hend2 *).
	induction (CLOS1) as [ | | start mid fin STEP1 IH1 STEP2 IH2]; intros; subst.
	- inversion CLOS2; subst.
		+ assert (LDFA_Eps_Done out1 = LDFA_Eps_Done out2).
		eapply (ldfa_epsilon_deterministic c x _ _ H H0). 
		congruence.
		+ pose proof (eps_done_terminal _ _ _ H) as Hdone. contradiction.
		+ destruct (rtc_eps_step _ _ _ _ H CLOS2) as [Hd | Hx].
		* apply rtc_eps_done in Hd; congruence.
		* subst. exfalso. eapply eps_done_terminal; eauto.
	- pose proof (rtc_eps_done _ _ _ CLOS2 ). congruence.
	- specialize (IH1 STEP1 CLOS2 ) ; specialize (IH2 STEP2).
	(* can prove [mid = Done out1] or [mid -*> Done out2]
		mid could be step(s) before Done out1, so no?
	*)
	pose proof (rtc_eps_to_done _ _ _ _ STEP1 CLOS2) as Hmid.
	eapply (IH2 Hmid out1 eq_refl). 
Qed.

Theorem ldfa_next_deterministic:
  forall c i nexto next1 next2
    (STEP1: next_loop_rel c i nexto next1)
    (STEP2: next_loop_rel c i nexto next2),
    next1 = next2.
Proof.
	intros.
	inversion STEP1 ; subst; inversion STEP2; try reflexivity; unfold is_nextloop_skip in *;
	repeat match goal with
	| H : get_pc ?c ?l = Some _ |- _ =>  rewrite H in *
	end; try congruence.
	subst.
	assert (out = out0) by (eapply epsilon_rtc_deterministic; eauto).
	congruence.
Qed.

(****************)

(* a done state can't next-step to anything *)
Lemma next_done_terminal : forall c i out b s,
  ~ next_loop_rel c i (LDFA_Next_Done out b) s.
Proof. intros until 1. inversion H. Qed.

(* a done state can only next-star to itself *)
Lemma rtc_next_done : forall c i out b next,
  clos_refl_trans _ (next_loop_rel c i) (LDFA_Next_Done out b) next ->
  next = LDFA_Next_Done out b.
Proof.
  intros.
  remember (LDFA_Next_Done out b) as out_state.
  induction (H); subst.
  - pose proof (next_done_terminal _ _ _ _ _ H0) as Hdone. contradiction.
  - reflexivity.
  - specialize (IHc0_1 eq_refl c0_1). subst.
  apply IHc0_2. reflexivity. apply H.
Qed.

(* 
	x -> y & x -*> b means 
	either x->y was the first (deter) step towards b and thus we can continue y-*>b 
	or it already is b
*)
Lemma rtc_next_step : forall c i x y b,
  next_loop_rel c i x y ->
  clos_refl_trans _ (next_loop_rel c i) x b ->
  clos_refl_trans _ (next_loop_rel c i) y b \/ b = x.
Proof.
  intros c i x y b H_step H.
  revert y H_step.
  induction H as [x b Hb | | x m b H1 IH1 H2 IH2]; intros y H_step.
  - (* x -> b, and x -> y, so y = b & b -*> b *)
    assert (y = b) by (eapply ldfa_next_deterministic; eauto).
    subst. left. apply rt_refl.
  - (* b = x *)
    right. reflexivity.
  - (* x ->* m ->* b *)
    destruct (IH1 _ H_step) as [Hym | Hmx].
    + (* y -*> m -*> b *) left. eapply rt_trans; eauto.
    + subst. apply IH2. exact H_step.
Qed.

Lemma rtc_next_to_done : forall c i start mid o b
  (STARsm: clos_refl_trans _ (next_loop_rel c i) start mid)
  (STARsd: clos_refl_trans _ (next_loop_rel c i) start (LDFA_Next_Done o b)),
  clos_refl_trans _ (next_loop_rel c i) mid (LDFA_Next_Done o b).
Proof.
  intros.
  induction STARsm; intros.
  - destruct (rtc_next_step _ _ _ _ _ H STARsd).
    + exact H0.
    + subst. exfalso. eapply next_done_terminal; eauto.
  - assumption.
  - apply IHSTARsm2. apply IHSTARsm1. assumption.
Qed.

Lemma next_rtc_deterministic : 
	forall c i s out1 b1 out2 b2
		(CLOS1: clos_refl_trans _ (next_loop_rel c i) s (LDFA_Next_Done out1 b1)) 
		(CLOS2: clos_refl_trans _ (next_loop_rel c i) s (LDFA_Next_Done out2 b2)),
		out1 = out2 /\ b1 = b2.
Proof.
	intros.
	remember (LDFA_Next_Done out1 b1) as end1 eqn:Hend1.
	remember (LDFA_Next_Done out2 b2) as end2 eqn:Hend2.
  	revert out1 b1 Hend1 (* out2 Hend2 *).
	induction (CLOS1) as [ | | start mid fin STEP1 IH1 STEP2 IH2]; intros; subst.
	- inversion CLOS2; subst.
		+ assert (LDFA_Next_Done out1 b1 = LDFA_Next_Done out2 b2).
		eapply (ldfa_next_deterministic c i x _ _ H H0). constructor; congruence.
		+ pose proof (next_done_terminal _ _ _ _ _ H) as Hdone. contradiction.
		+ destruct (rtc_next_step _ _ _ _ _ H CLOS2) as [Hd | Hx].
		* apply rtc_next_done in Hd; constructor; congruence.
		* subst. exfalso. eapply next_done_terminal; eauto.
	- pose proof (rtc_next_done _ _ _ _ _ CLOS2 ). constructor; congruence.
	- specialize (IH1 STEP1 CLOS2 ) ; specialize (IH2 STEP2).
	pose proof (rtc_next_to_done _ _ _ _ _ _ STEP1 CLOS2) as Hmid.
	constructor;
	eapply (IH2 Hmid out1 _ eq_refl). 
Qed.

(* todo bouger dans chars aussi? *)
Theorem next_char_deterministic:
  forall i char1 char2
    (NC1: next_char i = Some char1)
    (NC2: next_char i = Some char2),
    char1 = char2.
Proof.
	intros. unfold next_char in *. unfold next_str in *.
	congruence.
Qed.

Theorem ldfa_deterministic:
  forall c ldfao ldfa1 ldfa2
    (STEP1: ldfa_loop_rel c ldfao ldfa1)
    (STEP2: ldfa_loop_rel c ldfao ldfa2),
    ldfa1 = ldfa2.
Proof.
	intros.
	inversion STEP1 ; subst; inversion STEP2; subst; try reflexivity;
	repeat match goal with
	| H : advance_input ?i ?forward = _ |- _ =>  rewrite H in *
	| H : dfa_state_hasmatch ?c ?curr = _ |- _ =>  rewrite H in *
	end; try congruence; inversion ADVANCE; 
	destruct (next_rtc_deterministic _ _ _ _ _ _ _ COMP_NEXT COMP_NEXT0) as [NEXT_DETER_O NEXT_DETER_B]; 
	subst; try congruence; unfold add_trans in *; epose proof (next_char_deterministic _ _ _ NEXT_CHAR NEXT_CHAR0 ); subst; reflexivity.
Qed.


(********** progress of the relations **********)

(* Definition is_epsilon_break (c:code) (curr: internal_state) : bool :=
match get_pc c (fst curr) with
| None | Some (Consume _) | Some (KillThread) | Some (Accept) => true
| _ => false
end.

Definition is_epsilon_skip (c:code) (curr:internal_state) : bool :=
match get_pc c (fst curr) with
| Some (SetRegOpen _) | Some (SetRegClose _) | Some (ResetRegs _) => true
| _ => false
end. *)

Theorem ldfa_eps_progress:
  forall c inp out wq,
  exists eps_next,
    epsilon_loop_rel c (LDFA_Eps_Running inp out wq) eps_next.
Proof.
	intros.
	destruct wq as [| curr wq].
	- eexists. apply elr_final.
	- destruct (dfa_state_contains out curr) eqn:SEEN.
		+ eexists. apply elr_seen. eauto.
		+ destruct (get_pc c (fst curr)) eqn:CURR_PC.
			* 
			assert (IS_BREAK : is_epsilon_break c curr =
				match b with
				| Consume _ | KillThread | Accept => true
				| _ => false
				end)
				by (unfold is_epsilon_break; rewrite CURR_PC; reflexivity).
			assert (IS_SKIP : is_epsilon_skip c curr =
				match b with
				| SetRegOpen _ | SetRegClose _ | ResetRegs _ => true
				| _ => false
				end)
				by (unfold is_epsilon_skip; rewrite CURR_PC; reflexivity).
			
			destruct b; simpl in *;
			repeat match goal with
			| H : is_epsilon_break ?c ?curr = true |- _ => eexists; apply elr_break; eauto
			| H : is_epsilon_skip ?c ?curr = true |- _ => eexists; apply elr_reg_skip; eauto
			end.
			-- destruct (anchor_satisfied rer a inp) eqn:SAT_ANC; eexists; [eapply elr_anc_sat | eapply elr_anc_unsat]; eauto.
			-- eexists; apply elr_jmp; eauto.
			-- eexists; apply elr_fork; eauto.
			-- eexists; apply elr_bgnloop; eauto.
			-- destruct (snd curr) eqn:EXIT; eexists; [apply elr_endloop_sat | eapply elr_endloop_unsat]; eauto.			
			* eexists. apply elr_break. eauto. unfold is_epsilon_break. rewrite CURR_PC. reflexivity.

Qed.


Theorem ldfa_next_progress:
  forall c inp next current_pcs,
  exists next_state,
    next_loop_rel c inp (LDFA_Next_Running next current_pcs) next_state.
Proof.
	intros.
	destruct (current_pcs).
	- eexists; apply nlr_final; eauto.
	- set (get_curr := get_pc c (fst i)).
	destruct (get_pc c (fst i)) eqn:CURR_PC ;
	assert (IS_SKIP : is_nextloop_skip c i =
				match get_curr with
				| Some (Consume _) | Some Accept | Some KillThread => false
				| _ => true
				end)
				by (unfold is_nextloop_skip; rewrite CURR_PC; reflexivity); 
	try destruct b;			
	simpl in *; try match goal with
	| H : is_nextloop_skip ?c ?i = true |- _ => eexists; apply nlr_skip; eauto
	| H : get_pc _ _ = Some Accept |- _ => eexists; apply nlr_accept; eauto
	| H : get_pc _ _ = Some KillThread |- _ => eexists; apply nlr_kill; eauto
	| H : get_pc _ _ = Some (Consume ?cd) |- _ => destruct (check_read rer cd inp forward) eqn:H_READ
	end.
		+ eexists. eapply nlr_consume; eauto. admit.	
		+ eexists; eapply nlr_noconsume; eauto.
Admitted.


(* 
(* input juste pour check les anchors 
	version initiale avec une fonction *)
Fixpoint epsilon_loop (c: code) (inp: input) (out: dfa_state) (workqueue: dfa_state) : dfa_state :=
	match workqueue with
	| nil => out (* once we're done with our workqueue, just return our "out" *)
	| curr :: tail => (* pas de current mutable, on va juste remettre à la head de la workqueue en fait *)
		if dfa_state_contains out curr then (* if state already in we don't explore it again *)
			epsilon_loop (c) (inp) (out) (tail) (* so new workqueue is tail, with curr popped *)
		else
		(* gotta remember we need to insert "curr" in "out" here, at the end !! *)
			let new_out := (out ++ [curr]) in
			match get_pc c (fst curr) with
			| None | Some (Consume _) | Some (SetRegOpen _) | Some (SetRegClose _) | Some (ResetRegs _) | Some (KillThread) | Some (Accept) => 
				epsilon_loop (c) (inp) (new_out) (tail) (* break : we go back to the workqueue pop after inserting curr at the end *)
			| Some (Fork out1 out2) => 
				epsilon_loop (c) (inp) (new_out) ([(out1, snd curr)] ++ tail ++ [(out2, snd curr)]) 
				(* we insert current in out, and head of workqueue is direct followup, but we also add the future explo at the tail *)
			| Some (Jmp l) => 
				epsilon_loop (c) (inp) (new_out) ((l, snd curr) :: tail)
			| Some (CheckAnchor anc) => 
				match anchor_satisfied rer anc inp with
				| false => epsilon_loop (c) (inp) (new_out) (tail) (* equiv break *)
				| true => epsilon_loop (c) (inp) (new_out) (((fst curr + 1), snd curr) :: tail)
				end
			| Some (BeginLoop) =>
				epsilon_loop (c) (inp) (new_out) ((fst curr + 1, CannotExit) :: tail)
			| Some (EndLoop l) =>
				match (snd curr) with
				| CannotExit => epsilon_loop (c) (inp) (new_out) (tail) (* break *)
				| CanExit => epsilon_loop (c) (inp) (new_out) ((l, CanExit) :: tail) (* canexit equiv to snd curr *)
				end
			end
	end.


(*
	Return the list (ordered by priority) of nfa states (constituant un dfa_state) reachable through epsilon transitions (without consuming input)
	from given nfa_start_state (with its boolean for nullable quantifier), and given the input to check the anchors
	attention ! on doit passer out, parce que le set est partagé entre les states du ldfa
*)
(* can be turned into relation easily / maybe has to be fixpoint, idk? *)
(* c'est juste une mini opti présente dans rust pour pas passer par la boucle mais ça donne le meme résultat, 
donc pour l'instant on fait sans, et peut etre on prouvera plus tard que ça fait bien le meme resultat et on remplacera *)
Definition epsilon_closure (c: code) (start: internal_state) (inp: input) (out: dfa_state) : dfa_state :=
	if is_epsilon c start then
		epsilon_loop c inp out [start] (* begin with just start state in workqueue *)
	else (* opti to not go thru the algo if it's not epsilon state *)
		[start]. (* just return out *) 

*)
