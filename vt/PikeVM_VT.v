(** * PikeVM Algorithm with virtual tree registers *)

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

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets Prefix.
From Linden Require Import VirtualTree RegsData2.
From Linden Require Import PikeVM.
From Warblre Require Import Base RegExpRecord.

Module Regs := VT(RegsData).

Import RegsData.

Section PikeVM.
  Context {params: LindenParameters}.
  Context {VMS: VMSeen}.
  Context (rer: RegExpRecord).

(** * Registers *)

  Definition regs := Regs.State.
  Definition regs_id := nat. (* virtual tree leaf id *)
  Definition gid_to_idx (gid:group_id) : nat := 2 * gid.

  (** * PikeVM threads  *)
  
Definition thread_vt : Type := (label * regs_id * LoopBool).

Definition upd_label_vt (t:thread_vt) (next:label) (ri:regs_id) : thread_vt :=
  match t with (l,r,b) => (next,ri,b) end.

Definition advance_thread_vt (t:thread_vt) : thread_vt :=
  match t with (l,r,b) => (l+1,r,b) end.

(* used after consuming *)
Definition block_thread_vt (t:thread_vt) : thread_vt :=
  match t with (l,r,b) => (l+1,r,CanExit) end.

Definition open_thread_vt (t:thread_vt) (gid:group_id) (idx:nat) (r:regs): thread_vt * regs :=
  match t with
    (l,ri,b) =>
      (* the third value in the triple is unused *)
      let new_data := Incomplete([(gid_to_idx gid, Valid(idx), Undefined)]) in
      let r' := Regs.insert ri new_data r in
      ((l+1, ri, b), r') end.

Definition close_thread_vt (t:thread_vt) (gid:group_id) (idx:nat) (r:regs): thread_vt * regs :=
  match t with
    (l,ri,b) =>
      (* the third value in the triple is unused *)
      let new_data := Incomplete([(gid_to_idx gid + 1, Valid(idx), Undefined)]) in
      let r' := Regs.insert ri new_data r in
      ((l+1, ri, b), r') end.
(* In GroupMap.close, if the opening value is greater than idx, then they are switched. 
Should I do that ?
TODO: get_compressed data on ri, get with gid_to_idx gid, if larger, add update for both regs *)

Definition reset_thread_vt (t:thread_vt) (gidl:list group_id) (r:regs): thread_vt * regs :=
  match t with
    (l,ri,b) =>
      let r' := List.fold_left (fun r gid =>
                        let new_data := Incomplete([]) in
                        Regs.insert ri new_data r) gidl r in
      ((l+1, ri, b), r') end.

Definition begin_thread_vt (t:thread_vt) : thread_vt :=
  match t with (l,r,b) => (l+1,r,CannotExit) end.

(*Definition gm_of (t:thread_vt) : group_map :=
  match t with (pc,gm,b) => gm end.*)
Definition ri_of (t:thread_vt) : regs_id :=
  match t with (pc,ri,b) => ri end.

Definition seen_thread_vt (seen:seenpcs) (t:thread_vt) :bool :=
  match t with
  | (pc, gm, b) => inseenpc seen pc b
  end.

Definition add_thread_vt (seen:seenpcs) (t:thread_vt) : seenpcs :=
  match t with
  | (pc, gm, b) => add_seenpcs seen pc b
  end.


(** * NFA epsilon-exploration  *)

(* the result of one step of exploring transitions *)
Inductive epsilon_result_vt : Type :=
| EpsActive: list thread_vt -> epsilon_result_vt
| EpsMatch: epsilon_result_vt
| EpsBlocked: thread_vt -> epsilon_result_vt.

Definition EpsDead : epsilon_result_vt := EpsActive [].

(* an atomic step for a thread *)
(* TODO add regs as input and output: so that we can insert/split/delete *)
Definition epsilon_step_vt (t:thread_vt) (c:code) (i:input) (r:regs) : epsilon_result_vt * regs :=
  match t with
  | (pc, ri, b) =>
      match get_pc c pc with
      | None =>
          let r' := Regs.delete ri r in
          (EpsDead, r')
      | Some instr =>
          match instr with
          | Accept => (EpsMatch, r)
          | Consume cd => match check_read rer cd i forward with
                          | CannotRead =>
                              let r' := Regs.delete ri r in
                              (EpsDead, r')
                          | CanRead => (EpsBlocked (block_thread_vt t), r)
                         end
          | CheckAnchor a => match anchor_satisfied rer a i with
                             | false =>
                                 let r' := Regs.delete ri r in
                                 (EpsDead, r')
                             | true => (EpsActive [advance_thread_vt t], r)
                             end
          | Jmp next => (EpsActive [upd_label_vt t next ri], r)
          | Fork l1 l2 =>
              let (r', ri') := (Regs.split ri r) in
              (EpsActive [upd_label_vt t l1 ri; upd_label_vt t l2 ri'], r')
          | SetRegOpen gid =>
              let (t', r') := open_thread_vt t gid (idx i) r in
              (EpsActive [t'], r')
          | SetRegClose gid =>
              let (t', r') := close_thread_vt t gid (idx i) r in
              (EpsActive [t'], r')
          | ResetRegs gidl =>
              let (t', r') := reset_thread_vt t gidl r in
              (EpsActive [t'], r')
          | BeginLoop => (EpsActive [begin_thread_vt t], r)
          | EndLoop next => match b with
                            | CannotExit =>
                                let r' := Regs.delete ri r in
                                (EpsDead, r')
                            | CanExit => (EpsActive [upd_label_vt t next ri], r)
                            end
          | KillThread =>
              let r' := Regs.delete ri r in
              (EpsDead, r')
          end
      end
  end.

(** * PikeVM Semantics  *)

Definition leaf_vt : Type := input * regs_id.

(* semantic states of the PikeVM algorithm *)
Inductive pike_vm_state_vt : Type :=
| PVS (inp:input) (active: list thread_vt) (best: option leaf_vt) (blocked: list thread_vt) (nextprefix: option (nat * literal * StrSearch)) (seen: seenpcs) (r:regs)
| PVS_final (best: option leaf_vt) (r: regs).

(* given an input and literal, we compute the next prefix counter *)
(* since the counter is always offset by one, we first try to advance the input before performing a prefix search *)
Definition next_prefix_counter {strs:StrSearch} (inp: input) (lit: literal) : option (nat * literal * StrSearch) :=
  match advance_input inp forward with
  | None => None
  | Some (Input next pref) =>
      match str_search (prefix lit) next with
      | None => None
      | Some n => Some (n, lit, strs)
      end
  end.

Definition vt_initial_id := 0.
Definition pike_vm_initial_thread_vt : thread_vt := (0, vt_initial_id, CanExit).

(* initial state for the PikeVM which operates in unanchored fashion *)
(* ignored for vt *)
(*Definition pike_vm_initial_state_unanchored {strs:StrSearch} (lit:literal) (inp:input) : pike_vm_state :=
  let nextprefix := next_prefix_counter inp lit in
  PVS inp [pike_vm_initial_thread] None [] nextprefix initial_seenpcs.*)

(* initial state for the PikeVM which operates in anchored fashion *)
Definition pike_vm_initial_state_vt (inp:input) (regs_size: nat) : pike_vm_state_vt :=
  PVS inp [pike_vm_initial_thread_vt] None [] None initial_seenpcs (Regs.initial_tree regs_size).

Definition delete_thread_regs_from_regs_state: list thread_vt -> regs -> regs :=
  List.fold_left (fun r t => (* get regs_id from thread, delete it from r *)
                    match t with
                      (_, ri, _) => Regs.delete ri r end).
Definition delete_best_regs_from_regs_state (best:option leaf_vt) (r:regs) : regs :=
  match best with
  | Some (_, ri) => Regs.delete ri r
  | None => r
  end.

(* small-step semantics for the PikeVM algorithm *)
Inductive pike_vm_step_vt (c:code): pike_vm_state_vt -> pike_vm_state_vt -> Prop :=
| pvs_final:
  (* moving to a final state when there are no more active or blocked threads *)
  forall inp best seen regs,
    pike_vm_step_vt c (PVS inp [] best [] None seen regs) (PVS_final best regs)
| pvs_end:
  (* when the list of active is empty and we've reached the end of string *)
  (* in practice, this rule is never used because we can have no blocked threads *)
  (* when there is no input left. We keep this rule for convenience in the proofs *)
  (* and for relating it to the functional version *)
  forall inp best thr blocked nextprefix seen regs regs'
         (ADVANCE: advance_input inp forward = None)
         (DELETE_REGS: regs' = delete_thread_regs_from_regs_state (thr::blocked) regs),
    pike_vm_step_vt c (PVS inp [] best (thr::blocked) nextprefix seen regs) (PVS_final best regs')
| pvs_nextchar:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 best thr blocked seen regs
         (ADVANCE: advance_input inp1 forward = Some inp2),
    pike_vm_step_vt c (PVS inp1 [] best (thr::blocked) None seen regs) (PVS inp2 (thr::blocked) best [] None initial_seenpcs regs)
| pvs_skip:
  (* when the pc has already been seen at this current index, we skip it entirely *)
  forall inp t active best blocked nextprefix seen regs regs'
         (SEEN: seen_thread_vt seen t = true)
         (DELETE_REG:  regs' = delete_thread_regs_from_regs_state [t] regs), (* t is killed, so its regs are deleted *)
    pike_vm_step_vt c (PVS inp (t::active) best blocked nextprefix seen regs) (PVS inp active best blocked nextprefix seen regs')
| pvs_active:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp t active best blocked nextprefix seen nextactive regs regs'
         (UNSEEN: seen_thread_vt seen t = false)
         (STEP: epsilon_step_vt t c inp regs = (EpsActive nextactive, regs')), (* returns next regs *)
    pike_vm_step_vt c (PVS inp (t::active) best blocked nextprefix seen regs)
      (PVS inp (nextactive++active) best blocked nextprefix (add_thread_vt seen t) regs')
| pvs_match:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp t active best blocked nextprefix seen regs regs' regs''
         (UNSEEN: seen_thread_vt seen t = false)
         (STEP: epsilon_step_vt t c inp regs = (EpsMatch, regs'))
         (* delete regs of active threads (except t) and of previous best match *)
         (DELETE_REGS: regs'' = delete_thread_regs_from_regs_state active
                                  (delete_best_regs_from_regs_state best regs')),
    pike_vm_step_vt c (PVS inp (t::active) best blocked nextprefix seen regs) 
      (PVS inp [] (Some (inp,ri_of t)) blocked None (add_thread_vt seen t) regs'')
| pvs_blocked:
  (* add the new blocked thread after the previous ones *)
  forall inp t active best blocked nextprefix seen newt regs regs'
         (UNSEEN: seen_thread_vt seen t = false)
         (STEP: epsilon_step_vt t c inp regs = (EpsBlocked newt, regs')), (* returns new regs *)
    pike_vm_step_vt c (PVS inp (t::active) best blocked nextprefix seen regs) (PVS inp active best (blocked ++ [newt]) nextprefix (add_thread_vt seen t) regs').
(* Unanchored PikeVM rules are removed: pvs_acc, pvs_nextchar_generate, pvs_next_char_filter *)

(** * Equivalence to the original PikeVM *)

equiv :
group map vs (nat * regs) : forall i, gett on groupm i = get on regs with i

equiv on states : same lists on threads (but must define equiv for threads)

Lemma steps_on_both_side : 
  orig state has prefix = None -> (* so that we avoid the deleted steps *)
  equiv state on orig + vt version ->
  do a step (feed state to pike_vm_step) ->
  output states are equiv.

Theorem pikevm_vt_equiv: 
  forall ... ->
  trc_pike_vm (compilation r) (pike_vm_initial_state inp) (PVS_final result) ->
  trc_pike_vm_vt (compilation r) (pike_vm_initial_state_vt inp) (PVS_final result_vt) ->
  equiv result result_vt.

Theorem pikevm_deterministic:
  forall c pvso pvs1 pvs2
    (STEP1: pike_vm_step c pvso pvs1)
    (STEP2: pike_vm_step c pvso pvs2),
    pvs1 = pvs2.
Proof.
  intros c pvso pvs1 pvs2 STEP1 STEP2. inversion STEP1; subst.
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
      rewrite STEP in STEP0; inversion STEP0.
  - inversion STEP2; subst; auto; try (rewrite UNSEEN in SEEN; inversion SEEN);
      rewrite STEP in STEP0; inversion STEP0.
    subst. auto.
Qed.

Theorem pikevm_progress:
  forall c inp active best blocked nextprefix seen,
  exists pvs_next,
    pike_vm_step c (PVS inp active best blocked nextprefix seen) pvs_next.
Proof.
  intros c inp active best blocked nextprefix seen.
  destruct active as [|[[pc gm] b] active].
  - destruct blocked as [|t blocked].
    + destruct nextprefix.
      * destruct p as [[n lit] strs]. eexists. now apply pvs_acc.
      * eexists. apply pvs_final.
    + destruct (advance_input inp forward) eqn:INP.
      * destruct nextprefix.
        -- destruct p as [[n lit] strs], n.
          ++ eexists. apply pvs_nextchar_generate. eauto.
          ++ eexists. apply pvs_nextchar_filter. eauto.
        -- eexists. apply pvs_nextchar. eauto.
      * eexists. apply pvs_end. eauto.
  - destruct (seen_thread seen (pc,gm,b)) eqn:SEEN.
    { eexists. apply pvs_skip. auto. }
    destruct (epsilon_step (pc,gm,b) c inp) eqn:EPS.
    + eexists. apply pvs_active; eauto.
    + eexists. apply pvs_match; eauto.
    + eexists. apply pvs_blocked; eauto.
Qed.

End PikeVM.
