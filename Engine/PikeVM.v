(** * PikeVM Algorithm  *)

(* The PikeVM algorithm, expressed as small-step semantics on the bytecode NFA *)
(* It records the code labels it has already handled to avoid doing work twice *)

(*
Anchored vs unanchored PikeVM:

The PikeVM can operate in two modes: anchored and unanchored. Which mode we operate
in is determined by the initial state we provide to the PikeVM. An anchored PikeVM
finds matches only at the current position of the input, while an unanchored PikeVM
finds matches at any position of the input.

Normally, we can obtain an unanchored engine from an anchored one for a regex /r/ by
simply executing the engine with the regex /[^]*?r/. Here, we take an optimized approach
by simulating the /[^]*?/ in the engine directly. This allows us to perfom optimizations
during execution. The simulation is done by attaching (as lowest priority) the initial
thread to the active list whenever we advance the input. The optimizations come from
knowing the literal of the regex allowing us to skip appending the initial thread at
certain positions. We do it by maintaining a prefix counter.

A prefix counter consists of two things:
- A literal. This literal does not change throughout the entire execution of the PikeVM
- A counter. It indicates in how many characters we will reach a position where
  the literal matches the prefix of the input. If we are at position n of the input,
  and the counter is k means, that at position n + k + 1, the prefix matches.

The counter is decreased each time we consume a character. Whenever we consume a
character and the counter is nonzero, we know that at this position we will not
find a match. Therefore we perform the "filtering" step and not include the initial
thread. When the counter is zero, we might find a match at the next position, so we
include the initial thread in "generating" step. Finally, if we run out of both active
and blocked thread, we can do the "acceleration" step, where we jump ahead in the input
to the next position where the prefix matches.
*)

From Stdlib Require Import List Lia FunctionalExtensionality.
Import ListNotations.

From Linden Require Import Regex Chars Groups FunctionalSemantics.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets Prefix.
From Warblre Require Import Base RegExpRecord.


Section PikeVM.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context (rer: RegExpRecord).

(** * PikeVM threads  *)

Definition thread : Type := (label * group_map * LoopBool).

Definition upd_label (t:thread) (next:label): thread :=
  match t with (l,r,b) => (next,r,b) end.

Definition advance_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,b) end.

(* used after consuming *)
Definition block_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,CanExit) end.

Definition open_thread (t:thread) (gid:group_id) (idx:nat) : thread :=
  match t with (l,r,b) => (l+1, GroupMap.open idx gid r, b) end.

Definition close_thread (t:thread) (gid:group_id) (idx:nat) : thread :=
  match t with (l,r,b) => (l+1, GroupMap.close idx gid r, b) end.

Definition reset_thread (t:thread) (gidl:list group_id) : thread :=
  match t with (l,r,b) => (l+1, GroupMap.reset gidl r, b) end.

Definition begin_thread (t:thread) : thread :=
  match t with (l,r,b) => (l+1,r,CannotExit) end.

Definition gm_of (t:thread) : group_map :=
  match t with (pc,gm,b) => gm end.

Definition seen_thread (seen:seenpcs) (t:thread) :bool :=
  match t with
  | (pc, gm, b) => inseenpc seen pc b
  end.

Definition add_thread (seen:seenpcs) (t:thread) : seenpcs :=
  match t with
  | (pc, gm, b) => add_seenpcs seen pc b
  end.


(** * NFA epsilon-exploration  *)

(* the result of one step of exploring transitions *)
Inductive epsilon_result : Type :=
| EpsActive: list thread -> epsilon_result
| EpsMatch: epsilon_result
| EpsBlocked: thread -> epsilon_result.

Definition EpsDead : epsilon_result := EpsActive [].

(* flips begin and end input anchors *)
Definition flip_anchor (a:anchor) : anchor :=
  match a with
  | BeginInput => EndInput
  | EndInput => BeginInput
  | WordBoundary => WordBoundary
  | NonWordBoundary => NonWordBoundary
  end.

(* get the anchor to check depending on the direction *)
Definition anchor_dir (a:anchor) (dir:Direction): anchor :=
  match dir with
  | forward => a
  | backward => flip_anchor a
  end.

(* get current string position index depending on the direction *)
Definition idx_dir (inp:input) (dir:Direction): nat :=
  match dir with
  | forward => idx inp
  | backward =>
    let 'Input next pref := inp in
    List.length next
  end.

(* an atomic step for a thread *)
Definition epsilon_step (t:thread) (c:code) (dir:Direction) (os:nfa_oracles) (i:input): epsilon_result :=
  let '(pc, gm, b) := t in
  match get_pc c pc with
  | None => EpsDead
  | Some instr =>
      match instr with
      | Accept => EpsMatch
      | Consume cd => match check_read rer cd i dir with
                      | CannotRead => EpsDead
                      | CanRead => EpsBlocked (block_thread t)
                      end
      | CheckAnchor a => match anchor_satisfied rer (anchor_dir a dir) i with
                         | false => EpsDead
                         | true => EpsActive [advance_thread t]
                         end
      | Jmp next => EpsActive [upd_label t next]
      | Fork l1 l2 => EpsActive [upd_label t l1; upd_label t l2]
      | SetRegOpen gid => EpsActive [open_thread t gid (idx_dir i dir)]
      | SetRegClose gid => EpsActive [close_thread t gid (idx_dir i dir)]
      | ResetRegs gidl => EpsActive [reset_thread t gidl]
      | BeginLoop => EpsActive [begin_thread t]
      | EndLoop next => match b with
                        | CannotExit => EpsDead
                        | CanExit => EpsActive [upd_label t next]
                        end
      | OracleQuery n _ _ => match nth_error os n with
                             | None => EpsDead
                             | Some oracle =>
                                 if oracle i then EpsActive [advance_thread t]
                                 else EpsDead
                             end
      | KillThread => EpsDead
      end
  end.

  Inductive bytecode': Type :=
  | Accept'
  | Consume': char_descr -> bytecode'
  | CheckAnchor': anchor -> bytecode'
  | Jmp': label -> bytecode'
  | Fork': label -> label -> bytecode'
  | SetRegOpen': group_id -> bytecode'
  | SetRegClose': group_id -> bytecode'
  | ResetRegs': list group_id -> bytecode'
  | BeginLoop': bytecode'
  | EndLoop': label -> bytecode'    (* also contains the backedge instead of adding a jump *)
  | OracleQuery': nat -> bytecode'
  | KillThread': bytecode'         (* for unsupported features *)
  .

  Definition code' : Type := list bytecode'.

  Definition translate (instr: bytecode) : bytecode' :=
    match instr with
    | Accept => Accept'
    | Consume cd => Consume' cd
    | CheckAnchor a => CheckAnchor' a
    | Jmp next => Jmp' next
    | Fork l1 l2 => Fork' l1 l2
    | SetRegOpen gid => SetRegOpen' gid
    | SetRegClose gid => SetRegClose' gid
    | ResetRegs gidl => ResetRegs' gidl
    | BeginLoop => BeginLoop'
    | EndLoop next => EndLoop' next
    | OracleQuery n _ _ => OracleQuery' n
    | KillThread => KillThread'
    end.
  Definition translate_code (c:code) : code' :=
    List.map translate c.
  Definition get_pc' (c:code') (pc:label) : option bytecode' :=
    List.nth_error c pc.

  Lemma translate_get_pc :
    forall c pc,
      get_pc' (translate_code c) pc = match get_pc c pc with
                                      | None => None
                                      | Some instr => Some (translate instr)
                                      end.
  Proof.
    unfold get_pc, get_pc'.
    induction c; intro pc; simpl.
    - now rewrite !nth_error_nil.
    - destruct pc; simpl.
      + easy.
      + easy.
  Qed.

Definition epsilon_step' (t:thread) (c:code') (dir:Direction) (os:nfa_oracles) (i:input): epsilon_result :=
  let '(pc, gm, b) := t in
  match get_pc' c pc with
  | None => EpsDead
  | Some instr =>
      match instr with
      | Accept' => EpsMatch
      | Consume' cd => match check_read rer cd i dir with
                        | CannotRead => EpsDead
                        | CanRead => EpsBlocked (block_thread t)
                        end
      | CheckAnchor' a => match anchor_satisfied rer (anchor_dir a dir) i with
                           | false => EpsDead
                           | true => EpsActive [advance_thread t]
                           end
      | Jmp' next => EpsActive [upd_label t next]
      | Fork' l1 l2 => EpsActive [upd_label t l1; upd_label t l2]
      | SetRegOpen' gid => EpsActive [open_thread t gid (idx_dir i dir)]
      | SetRegClose' gid => EpsActive [close_thread t gid (idx_dir i dir)]
      | ResetRegs' gidl => EpsActive [reset_thread t gidl]
      | BeginLoop' => EpsActive [begin_thread t]
      | EndLoop' next => match b with
                        | CannotExit => EpsDead
                        | CanExit => EpsActive [upd_label t next]
                        end
      | OracleQuery' n => match nth_error os n with
                         | None => EpsDead
                         | Some oracle =>
                            if oracle i then EpsActive [advance_thread t]
                            else EpsDead
                         end
      | KillThread' => EpsDead
      end
  end.

  Lemma epsilon_step_translate :
    forall t c dir os inp,
      epsilon_step t c dir os inp = epsilon_step' t (translate_code c) dir os inp.
  Proof.
    intros t c dir os inp.
    destruct t as [[pc gm] b].
    unfold epsilon_step, epsilon_step'.
    rewrite translate_get_pc.
    destruct get_pc; eauto.
    destruct b0; simpl; easy.
  Qed.




(** * PikeVM Semantics  *)

(* kinds of occurrence states *)
Variant occurrence :=
(* we only collect the highest priority result *)
| Best (best: option leaf)
(* we collect end positions of matches regardless of priority *)
| All (positions: list leaf).

(* depending on how we collect occurrences, we handle the `Accept` instruction *)
(* we update the `occurrence` state and the list of active threads/trees *)
Definition accept {A} (occ: occurrence) (inp: input) (gm: group_map) (active: list A): list A * occurrence :=
  match occ with
  (* we kill all lower priority threads/trees *)
  | Best _ => ([], Best (Some (inp, gm)))
  (* we keep all threads/trees to produce lower priority results *)
  | All positions => (active, All ((inp, gm) :: positions))
  end.

(* semantic states of the PikeVM algorithm *)
Inductive pike_vm_state : Type :=
| PVS (inp:input) (active: list thread) (occ: occurrence) (blocked: list thread) (nextprefix: option (nat * literal * StrSearch)) (seen: seenpcs)
| PVS_final (occ: occurrence).

(* given an input and literal, we compute the next prefix counter *)
(* since the counter is always offset by one, we first try to advance the input before performing a prefix search *)
Definition next_prefix_counter {strs:StrSearch} (inp: input) (dir: Direction) (lit: literal) : option (nat * literal * StrSearch) :=
  match advance_input inp dir with
  | None => None
  | Some (Input next pref) =>
      let search := str_search (prefix lit) match dir with
                    | forward => next
                    | backward => pref
                    end in
      match search with
      | None => None
      | Some n => Some (n, lit, strs)
      end
  end.

Definition pike_vm_initial_thread : thread := (0, GroupMap.empty, CanExit).
(* initial state for the PikeVM which operates in unanchored fashion *)
Definition pike_vm_initial_state_unanchored {strs:StrSearch} (lit:literal) (inp:input) (dir:Direction) (occ:occurrence): pike_vm_state :=
  let nextprefix := next_prefix_counter inp dir lit in
  PVS inp [pike_vm_initial_thread] occ [] nextprefix initial_seenpcs.
(* initial state for the PikeVM which operates in anchored fashion *)
Definition pike_vm_initial_state (inp:input) (occ:occurrence): pike_vm_state :=
  PVS inp [pike_vm_initial_thread] occ [] None initial_seenpcs.


(* small-step semantics for the PikeVM algorithm *)
Variant pike_vm_step (c:code) (dir:Direction) (os:nfa_oracles): pike_vm_state -> pike_vm_state -> Prop :=
| pvs_final:
(* moving to a final state when there are no more active or blocked threads *)
  forall inp occ seen,
    pike_vm_step c dir os (PVS inp [] occ [] None seen) (PVS_final occ)
| pvs_acc:
(* if there are no more active or blocked threads and we know where the next prefix matches, *)
(* we accelerate to that point *)
  forall inp occ n lit strs nextinp seen
    (ADVANCE: advance_input_n inp (S n) dir = nextinp),
    pike_vm_step c dir os (PVS inp [] occ [] (Some (n, lit, strs)) seen) (PVS nextinp [pike_vm_initial_thread] occ [] (next_prefix_counter nextinp dir lit) initial_seenpcs)
| pvs_end:
  (* when the list of active is empty and we've reached the end of string *)
  (* in practice, this rule is never used because we can have no blocked threads *)
  (* when there is no input left. We keep this rule for convenience in the proofs *)
  (* and for relating it to the functional version *)
  forall inp occ thr blocked nextprefix seen
    (ADVANCE: advance_input inp dir = None),
    pike_vm_step c dir os (PVS inp [] occ (thr::blocked) nextprefix seen) (PVS_final occ)
| pvs_nextchar:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 occ thr blocked seen
    (ADVANCE: advance_input inp1 dir = Some inp2),
    pike_vm_step c dir os (PVS inp1 [] occ (thr::blocked) None seen) (PVS inp2 (thr::blocked) occ [] None initial_seenpcs)
| pvs_nextchar_generate:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* since the nextprefix counter reached zero, we must also append as lowest priority the initial thread *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 occ lit strs thr blocked seen
    (ADVANCE: advance_input inp1 dir = Some inp2),
    pike_vm_step c dir os (PVS inp1 [] occ (thr::blocked) (Some (0, lit, strs)) seen) (PVS inp2 ((thr::blocked) ++ [pike_vm_initial_thread]) occ [] (next_prefix_counter inp2 dir lit) initial_seenpcs)
| pvs_nextchar_filter:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* since the nextprefix counter is nonzero, we do not append the initial thread *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 occ n lit strs thr blocked seen
    (ADVANCE: advance_input inp1 dir = Some inp2),
    pike_vm_step c dir os (PVS inp1 [] occ (thr::blocked) (Some (S n, lit, strs)) seen) (PVS inp2 (thr::blocked) occ [] (Some (n, lit, strs)) initial_seenpcs)
| pvs_skip:
  (* when the pc has already been seen at this current index, we skip it entirely *)
  forall inp t active occ blocked nextprefix seen
    (SEEN: seen_thread seen t = true),
    pike_vm_step c dir os (PVS inp (t::active) occ blocked nextprefix seen) (PVS inp active occ blocked nextprefix seen)
| pvs_active:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp t active occ blocked nextprefix seen nextactive
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c dir os inp = EpsActive nextactive),
    pike_vm_step c dir os (PVS inp (t::active) occ blocked nextprefix seen) (PVS inp (nextactive++active) occ blocked nextprefix (add_thread seen t))
| pvs_match:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp t active active' occ occ' blocked nextprefix seen
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c dir os inp = EpsMatch)
    (ACC: accept occ inp (gm_of t) active = (active', occ')),
    pike_vm_step c dir os (PVS inp (t::active) occ blocked nextprefix seen) (PVS inp active' occ' blocked None (add_thread seen t))
| pvs_blocked:
  (* add the new blocked thread after the previous ones *)
  forall inp t active occ blocked nextprefix seen newt
    (UNSEEN: seen_thread seen t = false)
    (STEP: epsilon_step t c dir os inp = EpsBlocked newt),
    pike_vm_step c dir os (PVS inp (t::active) occ blocked nextprefix seen) (PVS inp active occ (blocked ++ [newt]) nextprefix (add_thread seen t)).

(** * PikeVM properties  *)

Theorem pikevm_deterministic:
  forall c dir os pvso pvs1 pvs2
    (STEP1: pike_vm_step c dir os pvso pvs1)
    (STEP2: pike_vm_step c dir os pvso pvs2),
    pvs1 = pvs2.
Proof.
  intros c dir os pvso pvs1 pvs2 STEP1 STEP2. inversion STEP1; subst.
  - inversion STEP2; subst; auto.
  - inversion STEP2; subst; auto.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0.
    subst. auto.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0; auto.
  - inversion STEP2; subst; auto; rewrite ADVANCE in ADVANCE0; inversion ADVANCE0; auto.
  - inversion STEP2; subst; auto; rewrite UNSEEN in SEEN; inversion SEEN.
  - inversion STEP2; subst; auto; try (rewrite UNSEEN in SEEN; inversion SEEN);
      rewrite STEP in STEP0; inversion STEP0.
    subst. auto.
  - inversion STEP2; subst; auto; try (rewrite UNSEEN in SEEN; inversion SEEN);
      rewrite STEP in STEP0; inversion STEP0; rewrite ACC in ACC0; inversion ACC0; now subst.
  - inversion STEP2; subst; auto; try (rewrite UNSEEN in SEEN; inversion SEEN);
      rewrite STEP in STEP0; inversion STEP0.
    subst. auto.
Qed.

Theorem pikevm_progress:
  forall c dir os inp active occ blocked nextprefix seen,
  exists pvs_next,
    pike_vm_step c dir os (PVS inp active occ blocked nextprefix seen) pvs_next.
Proof.
  intros c dir os inp active occ blocked nextprefix seen.
  destruct active as [|[[pc gm] b] active].
  - destruct blocked as [|t blocked].
    + destruct nextprefix.
      * destruct p as [[n lit] strs]. eexists. now apply pvs_acc.
      * eexists. apply pvs_final.
    + destruct (advance_input inp dir) eqn:INP.
      * destruct nextprefix.
        -- destruct p as [[n lit] strs], n.
          ++ eexists. apply pvs_nextchar_generate. eauto.
          ++ eexists. apply pvs_nextchar_filter. eauto.
        -- eexists. apply pvs_nextchar. eauto.
      * eexists. apply pvs_end. eauto.
  - destruct (seen_thread seen (pc,gm,b)) eqn:SEEN.
    { eexists. apply pvs_skip. auto. }
    destruct (epsilon_step (pc,gm,b) c dir os inp) eqn:EPS.
    + eexists. apply pvs_active; eauto.
    + destruct occ; eexists; apply pvs_match; simpl; eauto.
    + eexists. apply pvs_blocked; eauto.
Qed.

(** Backward direction *)

(* All proofs about the PikeVM will reason about the forward direction. *)
(* Running the PikeVM in the backward direction means that characters *)
(* are processed right-to-left rather than left-to-right. This direction *)
(* mimics reversing the input which we want to avoid due to it being *)
(* expensive. *)
(* Here, we define the result of the backward direction in terms of the *)
(* forward direction. We essentially reverse everything refering to *)
(* the input. *)

Definition leaf_reverse (l: leaf) : leaf :=
  let (inp, gm) := l in
  (input_reverse inp, gm).

Definition option_reverse {A B} (f: A -> B) (o: option A) : option B :=
  option_map f o.

Definition o_leaf_reverse := option_reverse leaf_reverse.

Definition occurrence_reverse (occ: occurrence) : occurrence :=
  match occ with
  | Best o => Best (o_leaf_reverse o)
  | All positions => All (List.map leaf_reverse positions)
  end.

Definition pvs_reverse (pvs: pike_vm_state) : pike_vm_state :=
  match pvs with
  | PVS inp active occ blocked nextprefix seen => PVS (input_reverse inp) active (occurrence_reverse occ) blocked nextprefix seen
  | PVS_final occ => PVS_final (occurrence_reverse occ)
  end.

Definition nfa_oracle_reverse (o: nfa_oracle) : nfa_oracle := fun i => o (input_reverse i).
Definition nfa_oracles_reverse (os: nfa_oracles) : nfa_oracles := List.map nfa_oracle_reverse os.

Notation involutive f := (forall x, f (f x) = x).

Lemma map_map_involutive {A}: forall (f : A -> A) l,
  involutive f ->
  map f (map f l) = l.
Proof.
  intros f l invo.
  rewrite map_map.
  induction l.
  - reflexivity.
  - simpl. now rewrite invo, IHl.
Qed.

Lemma flip_anchor_involutive : involutive flip_anchor.
Proof. now destruct x. Qed.

Lemma leaf_reverse_involutive : involutive leaf_reverse.
Proof.
  destruct x; simpl; now rewrite input_reverse_involutive.
Qed.

Lemma o_leaf_reverse_involutive : involutive o_leaf_reverse.
Proof.
  destruct x; simpl; now rewrite ?leaf_reverse_involutive.
Qed.

Lemma occurrence_reverse_involutive : involutive occurrence_reverse.
Proof.
  destruct x; simpl.
  - now rewrite o_leaf_reverse_involutive.
  - rewrite map_map_involutive.
    + reflexivity.
    + exact leaf_reverse_involutive.
Qed.

Lemma pvs_reverse_involutive : involutive pvs_reverse.
Proof.
  destruct x as [inp active occ blocked nextprefix seen|occ]; simpl.
  - now rewrite input_reverse_involutive, occurrence_reverse_involutive.
  - now rewrite occurrence_reverse_involutive.
Qed.

Lemma nfa_oracle_reverse_involutive : involutive nfa_oracle_reverse.
Proof.
  intros o.
  unfold nfa_oracle_reverse.
  extensionality i.
  now rewrite input_reverse_involutive.
Qed.

Lemma nfa_oracles_reverse_involutive : involutive nfa_oracles_reverse.
Proof.
  induction x; simpl.
  - reflexivity.
  - now rewrite IHx, nfa_oracle_reverse_involutive.
Qed.

Lemma nfa_oracles_reverse_get :
  forall os i o,
    nth_error os i = Some o ->
    nth_error (nfa_oracles_reverse os) i = Some (nfa_oracle_reverse o).
Proof.
  induction os; intros [|i]; simpl; congruence || eauto.
Qed.

Lemma nfa_oracles_reverse_none :
  forall os i,
    nth_error os i = None ->
    nth_error (nfa_oracles_reverse os) i = None.
Proof.
  induction os; intros [|i]; simpl; congruence || eauto.
Qed.

Lemma advance_input_reverse_none : forall inp dir,
  advance_input inp dir = None <-> advance_input (input_reverse inp) (direction_reverse dir) = None.
Proof.
  intros [next pref] dir.
  split; intros; now destruct dir, next, pref.
Qed.

Lemma advance_input_reverse_some : forall inp dir inp',
  advance_input inp dir = Some inp' <-> advance_input (input_reverse inp) (direction_reverse dir) = Some (input_reverse inp').
Proof.
  intros [next pref] dir inp'.
  split; intros.
  - destruct dir, next, pref; discriminate || now injection H as <-.
  - destruct dir, next, pref; simpl in *; try discriminate;
      inversion H;
      eapply f_equal with (f:=input_reverse) in H1;
      simpl in H1;
      now rewrite H1, input_reverse_involutive.
Qed.

Lemma advance_input_n_reverse : forall inp dir n,
  advance_input_n inp n dir = input_reverse (advance_input_n (input_reverse inp) n (direction_reverse dir)).
Proof.
  intros [next pref]. now destruct dir.
Qed.

Lemma check_read_reverse :
  forall cd inp dir,
    check_read rer cd inp dir = check_read rer cd (input_reverse inp) (direction_reverse dir).
Proof.
  intros ? [next pref]. now destruct dir.
Qed.

Lemma anchor_satisfied_reverse :
  forall a inp,
    anchor_satisfied rer a inp = anchor_satisfied rer (flip_anchor a) (input_reverse inp).
Proof.
  intros a [next pref]. destruct a, next, pref; simpl; reflexivity || now rewrite Bool.xorb_comm.
Qed.

Lemma idx_dir_reverse : forall inp dir,
  idx_dir inp dir = idx_dir (input_reverse inp) (direction_reverse dir).
Proof.
  intros [next pref]. now destruct dir.
Qed.

Lemma epsilon_step_reverse :
  forall t c dir os inp,
    epsilon_step t c dir os inp = epsilon_step t c (direction_reverse dir) (nfa_oracles_reverse os) (input_reverse inp).
Proof.
  intros [[pc gm] b] c dir os inp.
  simpl. destruct get_pc as [inst|]; [|reflexivity]; destruct inst; try easy.
  - now rewrite check_read_reverse.
  - unfold anchor_dir. destruct dir; now rewrite anchor_satisfied_reverse, ?flip_anchor_involutive.
  - now rewrite idx_dir_reverse.
  - now rewrite idx_dir_reverse.
  - destruct nth_error eqn:Hnth.
    + eapply nfa_oracles_reverse_get in Hnth as ->.
      unfold nfa_oracle_reverse.
      now rewrite input_reverse_involutive.
    + now eapply nfa_oracles_reverse_none in Hnth as ->.
Qed.

Lemma next_prefix_counter_reverse {strs:StrSearch}:
  forall inp dir lit,
    next_prefix_counter inp dir lit = next_prefix_counter (input_reverse inp) (direction_reverse dir) lit.
Proof.
  now destruct dir, inp as [[|c next] [|c' pref]].
Qed.

Lemma accept_reverse {A}:
  forall occ inp gm active occ1 occ2 active1 active2,
    @accept A occ inp gm active = (active1, occ1) ->
    accept (occurrence_reverse occ) (input_reverse inp) gm active = (active2, occ2) ->
    active1 = active2 /\ occ1 = occurrence_reverse occ2.
Proof.
  intros occ inp gm active occ1 occ2 active1 active2 Hacc Hacc_rev.
  destruct occ; simpl in *;
    injection Hacc as <- <-;
    injection Hacc_rev as <- <-; simpl.
  - now rewrite input_reverse_involutive.
  - rewrite input_reverse_involutive, map_map_involutive.
    + easy.
    + exact leaf_reverse_involutive.
Qed.

Hint Rewrite
	flip_anchor_involutive
	direction_reverse_involutive
	leaf_reverse_involutive
	o_leaf_reverse_involutive
  occurrence_reverse_involutive
	pvs_reverse_involutive
	input_reverse_involutive
  epsilon_step_reverse : invo.

Tactic Notation "reverse" := autorewrite with invo using try (easy || congruence).

(* the PikeVM in a forward direction corresponds to a mapped version in the backward direction *)
Lemma pikevm_step_reverse :
  forall c dir os pvs pvs_next1 pvs_next2,
    pike_vm_step c dir os pvs pvs_next1 ->
    pike_vm_step c (direction_reverse dir) (nfa_oracles_reverse os) (pvs_reverse pvs) pvs_next2 ->
    pvs_next1 = pvs_reverse pvs_next2.
Proof.
  intros c dir os pvs pvs_next1 pvs_next2 H1 H2.
  inversion H1; subst; simpl in *.
  - inversion H2; subst. simpl. reverse.
  - inversion H2; subst. simpl.
    f_equal; reverse.
    + apply advance_input_n_reverse.
    + now rewrite next_prefix_counter_reverse, advance_input_n_reverse, input_reverse_involutive.
  - inversion H2; subst; simpl; reverse; rewrite advance_input_reverse_none in ADVANCE; congruence.
  - inversion H2; subst; simpl; rewrite advance_input_reverse_some in ADVANCE; try congruence.
    rewrite ADVANCE0 in ADVANCE; injection ADVANCE as ->.
    reverse.
  - inversion H2; subst; simpl; rewrite advance_input_reverse_some in ADVANCE; try congruence.
    rewrite ADVANCE0 in ADVANCE; injection ADVANCE as ->.
    f_equal; reverse; eauto using next_prefix_counter_reverse.
  - inversion H2; subst; simpl; rewrite advance_input_reverse_some in ADVANCE; try congruence.
    rewrite ADVANCE0 in ADVANCE; injection ADVANCE as ->.
    reverse.
  - inversion H2; subst; simpl; reverse.
  - inversion H2; subst; simpl; reverse; rewrite epsilon_step_reverse in STEP; congruence.
  - inversion H2; subst; simpl; reverse; rewrite epsilon_step_reverse in STEP; try congruence.
    eapply accept_reverse in ACC as [? ?]; eauto; now subst.
  - inversion H2; subst; simpl; reverse; rewrite epsilon_step_reverse in STEP; congruence.
Qed.

End PikeVM.
