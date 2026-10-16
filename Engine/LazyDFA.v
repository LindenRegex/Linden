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

(* epsilon-exploration  *)

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

(* 
Definition epsilon_closure (c: code) (start: internal_state) (inp: input) (out: dfa_state) : dfa_state :=
if exists new_out, (clos_refl_trans _ (epsilon_loop_rel c) (LDFA_Eps_Running inp out [start]) (LDFA_Eps_Done new_out)) then new_out else [].
*)
(* Definition epsilon_closure_rel (c : code) (start : internal_state) (inp : input) (out : dfa_state) : Prop :=
  clos_refl_trans _ (epsilon_loop_rel c) (LDFA_Eps_Running inp [] [start]) (LDFA_Eps_Done out). *)

(* Definition initial_int_state : internal_state := (0, CanExit).
Definition initial_dfa_state : dfa_state := epsilon_closure c inp [] [initial_int_state].
Definition initial_ldfa_state (c: code) (inp: input) : ldfa_state := LDFA initial_dfa_state inp [] None. *)

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
| nlr_skip : forall n pc pcs
	(SKIP_PCS: is_nextloop_skip c pc = true),
		next_loop_rel c i (LDFA_Next_Running n (pc :: pcs)) (LDFA_Next_Running n pcs)
| nlr_kill : forall n pc pcs
	(KILL_PC: get_pc c (fst pc) = Some (KillThread)),
		next_loop_rel c i (LDFA_Next_Running n (pc :: pcs)) (LDFA_Next_Done [] false).

(* 
| LDFA (curr: dfa_state) (inp: input) (ttab: transition_table) (best: option input) (next: dfa_state)
| LDFA_final (res:option input). 
assuming init_state : LDFA (curr = (epsilon_closure c i [] code@0)) (i) (ttab = []) (best = None) (next = [])
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
