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
From Stdlib Require Import Program.Equality.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets Prefix.
From Linden Require Import VirtualTree RegsData2.
From Linden Require Import PikeVM Correctness.
From Warblre Require Import Base RegExpRecord.

Module Regs := VT(RegsData).

Import RegsData.

Section PikeVM_VT.
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
| EpsActive_vt: list thread_vt -> epsilon_result_vt
| EpsMatch_vt: epsilon_result_vt
| EpsBlocked_vt: thread_vt -> epsilon_result_vt.

Definition EpsDead_vt : epsilon_result_vt := EpsActive_vt [].

(* an atomic step for a thread *)
(* TODO add regs as input and output: so that we can insert/split/delete *)
Definition epsilon_step_vt (t:thread_vt) (c:code) (i:input) (r:regs) : epsilon_result_vt * regs :=
  match t with
  | (pc, ri, b) =>
      match get_pc c pc with
      | None =>
          let r' := Regs.delete ri r in
          (EpsDead_vt, r')
      | Some instr =>
          match instr with
          | Accept => (EpsMatch_vt, r)
          | Consume cd => match check_read rer cd i forward with
                          | CannotRead =>
                              let r' := Regs.delete ri r in
                              (EpsDead_vt, r')
                          | CanRead => (EpsBlocked_vt (block_thread_vt t), r)
                         end
          | CheckAnchor a => match anchor_satisfied rer a i with
                             | false =>
                                 let r' := Regs.delete ri r in
                                 (EpsDead_vt, r')
                             | true => (EpsActive_vt [advance_thread_vt t], r)
                             end
          | Jmp next => (EpsActive_vt [upd_label_vt t next ri], r)
          | Fork l1 l2 =>
              let (r', ri') := (Regs.split ri r) in
              (EpsActive_vt [upd_label_vt t l1 ri; upd_label_vt t l2 ri'], r')
          | SetRegOpen gid =>
              let (t', r') := open_thread_vt t gid (idx i) r in
              (EpsActive_vt [t'], r')
          | SetRegClose gid =>
              let (t', r') := close_thread_vt t gid (idx i) r in
              (EpsActive_vt [t'], r')
          | ResetRegs gidl =>
              let (t', r') := reset_thread_vt t gidl r in
              (EpsActive_vt [t'], r')
          | BeginLoop => (EpsActive_vt [begin_thread_vt t], r)
          | EndLoop next => match b with
                            | CannotExit =>
                                let r' := Regs.delete ri r in
                                (EpsDead_vt, r')
                            | CanExit => (EpsActive_vt [upd_label_vt t next ri], r)
                            end
          | KillThread =>
              let r' := Regs.delete ri r in
              (EpsDead_vt, r')
          end
      end
  end.

(** * PikeVM Semantics  *)

Definition leaf_vt : Type := input * regs_id.

(* semantic states of the PikeVM algorithm *)
Inductive pike_vm_state_vt : Type :=
| PVS_vt (inp:input) (active: list thread_vt) (best: option leaf_vt) (blocked: list thread_vt) (nextprefix: option (nat * literal * StrSearch)) (seen: seenpcs) (r:regs)
| PVS_final_vt (best: option leaf_vt) (r: regs).

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
  PVS_vt inp [pike_vm_initial_thread_vt] None [] None initial_seenpcs (Regs.initial_tree regs_size).

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
| pvs_final_vt:
  (* moving to a final state when there are no more active or blocked threads *)
  forall inp best seen regs,
    pike_vm_step_vt c (PVS_vt inp [] best [] None seen regs) (PVS_final_vt best regs)
| pvs_end_vt:
  (* when the list of active is empty and we've reached the end of string *)
  (* in practice, this rule is never used because we can have no blocked threads *)
  (* when there is no input left. We keep this rule for convenience in the proofs *)
  (* and for relating it to the functional version *)
  forall inp best thr blocked nextprefix seen regs regs'
         (ADVANCE: advance_input inp forward = None)
         (DELETE_REGS: regs' = delete_thread_regs_from_regs_state (thr::blocked) regs),
    pike_vm_step_vt c (PVS_vt inp [] best (thr::blocked) nextprefix seen regs)
      (PVS_final_vt best regs')
| pvs_nextchar_vt:
  (* when the list of active threads is empty (but not blocked), restart from the blocked ones, proceeding to the next character *)
  (* reset the set of seen pcs *)
  forall inp1 inp2 best thr blocked seen regs
         (ADVANCE: advance_input inp1 forward = Some inp2),
    pike_vm_step_vt c (PVS_vt inp1 [] best (thr::blocked) None seen regs)
      (PVS_vt inp2 (thr::blocked) best [] None initial_seenpcs regs)
| pvs_skip_vt:
  (* when the pc has already been seen at this current index, we skip it entirely *)
  forall inp t active best blocked nextprefix seen regs regs'
         (SEEN: seen_thread_vt seen t = true)
         (DELETE_REG:  regs' = delete_thread_regs_from_regs_state [t] regs), (* t is killed, so its regs are deleted *)
    pike_vm_step_vt c (PVS_vt inp (t::active) best blocked nextprefix seen regs)
      (PVS_vt inp active best blocked nextprefix seen regs')
| pvs_active_vt:
  (* generated new active threads: add them in front of the low-priority ones *)
  forall inp t active best blocked nextprefix seen nextactive regs regs'
         (UNSEEN: seen_thread_vt seen t = false)
         (STEP: epsilon_step_vt t c inp regs = (EpsActive_vt nextactive, regs')), (* returns next regs *)
    pike_vm_step_vt c (PVS_vt inp (t::active) best blocked nextprefix seen regs)
      (PVS_vt inp (nextactive++active) best blocked nextprefix (add_thread_vt seen t) regs')
| pvs_match_vt:
  (* a match is found, discard remaining low-priority active threads *)
  forall inp t active best blocked nextprefix seen regs regs' regs''
         (UNSEEN: seen_thread_vt seen t = false)
         (STEP: epsilon_step_vt t c inp regs = (EpsMatch_vt, regs'))
         (* delete regs of active threads (except t) and of previous best match *)
         (DELETE_REGS: regs'' = delete_thread_regs_from_regs_state active
                                  (delete_best_regs_from_regs_state best regs')),
    pike_vm_step_vt c (PVS_vt inp (t::active) best blocked nextprefix seen regs) 
      (PVS_vt inp [] (Some (inp,ri_of t)) blocked None (add_thread_vt seen t) regs'')
| pvs_blocked_vt:
  (* add the new blocked thread after the previous ones *)
  forall inp t active best blocked nextprefix seen newt regs regs'
         (UNSEEN: seen_thread_vt seen t = false)
         (STEP: epsilon_step_vt t c inp regs = (EpsBlocked_vt newt, regs')), (* returns new regs *)
    pike_vm_step_vt c (PVS_vt inp (t::active) best blocked nextprefix seen regs)
      (PVS_vt inp active best (blocked ++ [newt]) nextprefix (add_thread_vt seen t) regs').
(* Unanchored PikeVM rules are removed: pvs_acc, pvs_nextchar_generate, pvs_next_char_filter *)

(** * Equivalence to the original PikeVM *)

Definition trc_pike_vm_vt (c:code) := @trc pike_vm_state_vt (pike_vm_step_vt c).

Definition rer_to_regs_size : nat :=
  match rer with
  | RegExpRecord.make _ _ _ _ cgc => 2 * cgc (* regs_size = 2 * rer.capturingGroupsCount *)
  end.

Definition gm_regs_vals (gid: group_id) (gm: group_map) : option nat * option nat :=
  match GroupMap.find gid gm with
  | None => (None, None)
  | Some (GroupMap.Range v None) => (Some v, None)
  | Some (GroupMap.Range o (Some c)) => (Some o, Some c)
  end.

Definition vt_regs_vals (gid: group_id) (regsdata: RegsData.t) : option nat * option nat :=
  let (cp1, _) := get_at (gid_to_idx gid) 0 regsdata in
  let (cp2, _) := get_at (gid_to_idx gid + 1) 0 regsdata in
  (cp1, cp2).

Definition gm_vt_equiv (gm: group_map) (ri: regs_id) (r: regs) : Prop :=
  match Regs.get_compressed_data ri r with
  | None => gm = GroupMap.empty (* assuming groupmap is empty when no updates have been made *)
  | Some (regsdata) =>
      forall gid, gm_regs_vals gid gm = vt_regs_vals gid regsdata
  end.

Definition leaves_equiv (res: option leaf) (res_vt: option leaf_vt) (r:regs) : Prop :=
  match res, res_vt with
  | None, None => True
  | Some (inp, gm), Some (inp_vt, ri) => inp = inp_vt /\ gm_vt_equiv gm ri r
  |_, _ => False
  end.

Definition thread_equiv (t: thread) (t_vt: thread_vt) (r: regs) : Prop :=
  match t, t_vt with
    (l, gm, b), (l_vt, ri, b_vt) => l = l_vt /\ gm_vt_equiv gm ri r /\ b = b_vt
  end.

Definition threads_equiv (t: list thread) (t_vt: list thread_vt) (r: regs): Prop :=
  List.Forall2 (fun t t_vt => thread_equiv t t_vt r) t t_vt.

Definition state_equiv (s: pike_vm_state) (s_vt: pike_vm_state_vt) : Prop :=
  match s, s_vt with
  | PVS i act best blo np seen, PVS_vt i' act' best' blo' np' seen' r =>
      i = i' /\ np = np' /\ seen = seen' /\
        threads_equiv act act' r /\ threads_equiv blo blo' r /\ leaves_equiv best best' r
  | PVS_final best, PVS_final_vt best' r => leaves_equiv best best' r
  | _, _ => False
  end.

Lemma seen_equiv : forall t t_vt seen r,
    thread_equiv t t_vt r ->
    seen_thread_vt seen t_vt = seen_thread seen t.
Proof.
  intros t t_vt seen r H.
  unfold thread_equiv in *.
  unfold seen_thread, seen_thread_vt in *.
  destruct t as [[l gm] b].
  destruct t_vt as [[l_vt ri] b_vt].
  destruct H as [Hl [Hr Hb]].
  subst.
  reflexivity.
Qed.

Lemma epsilon_step_equiv_active :
  forall c inp t t_vt nextactive_vt r r',
    thread_equiv t t_vt r ->
    epsilon_step_vt t_vt c inp r = (EpsActive_vt nextactive_vt, r') ->
    (exists nextactive,
        epsilon_step rer t c inp = EpsActive nextactive /\
    threads_equiv nextactive nextactive_vt r').
Admitted.

Lemma epsilon_step_equiv_match :
  forall c inp t t_vt r r',
    thread_equiv t t_vt r ->
    epsilon_step_vt t_vt c inp r = (EpsMatch_vt, r') ->
    epsilon_step rer t c inp = EpsMatch /\ r = r'.
Proof.
  intros c inp t t_vt r r' Heq H.
  unfold epsilon_step_vt, epsilon_step, thread_equiv in *.
  destruct t_vt as [[l_vt ri] b_vt].
  destruct t as [[l gm] b].
  destruct Heq as [Hl [Hr Hb]]. subst.
  destruct (get_pc c l_vt) eqn:BC.
  - destruct b eqn:B;
      try (injection H as H1 H2; inversion H1).
    + injection H as H. subst.
      auto.
    + destruct (check_read rer c0 inp forward); injection H as H1 H2; inversion H1.
    + destruct (anchor_satisfied rer a inp); injection H as H1 H2; inversion H1.
    + destruct b_vt; injection H as H _; inversion H.
  - injection H as H1 H2. inversion H1.
Qed.

Lemma epsilon_step_equiv_blocked :
  forall c inp t t_vt newt_vt r r',
    thread_equiv t t_vt r ->
    epsilon_step_vt t_vt c inp r = (EpsBlocked_vt newt_vt, r') ->
    (exists newt,
        epsilon_step rer t c inp = EpsBlocked newt /\
          thread_equiv newt newt_vt r') /\ r = r'.
Proof.
  intros c inp t t_vt newt_vt r r' Heq H.
  unfold epsilon_step_vt, epsilon_step, thread_equiv in *.
  destruct t_vt as [[l_vt ri] b_vt].
  destruct t as [[l gm] b].
  destruct Heq as [Hl [Hr Hb]]. subst.
  destruct (get_pc c l_vt) eqn:BC.
  - destruct b eqn:B;
      try (injection H as H1 H2; inversion H1).
    + destruct (check_read rer c0 inp forward);
        injection H as H1 H2.
      * split; try assumption.
        subst.
        exists (l_vt + 1, gm, CanExit).
        auto.
      * inversion H1.
    + destruct (anchor_satisfied rer a inp); injection H as H1 H2; inversion H1.
    + destruct b_vt; injection H as H _; inversion H.
  - injection H as H1 H2. inversion H1.
Qed.

Lemma pike_vm_step_vt_equiv :
  forall c s s_vt s' s_vt',
    (* s = (PVS inp act best blo None seen) *)
    (* s_vt = (PVS inp act_vt best_vt blo_vt None seen regs) *)
    state_equiv s s_vt ->
    pike_vm_step rer c s s' ->
    pike_vm_step_vt c s_vt s_vt' ->
    state_equiv s' s_vt'.
Proof.
  unfold state_equiv.
  intros c s s_vt s' s_vt' H STEP STEPVT.
  dependent induction STEPVT; destruct s; try contradiction.
  - (* pvs_final_vt *)
    destruct H as [Hinp [Hnp [Hs [EQUIV_ACT [EQUIV_BLO EQUIV_LEA]]]]].
    destruct active as [| t act]; inversion EQUIV_ACT; subst.
    destruct blocked as [| t blo]; inversion EQUIV_BLO; subst.
    inversion STEP. subst.
    assumption.
  - (* pvs_end_vt *)
    destruct H as [Hinp [Hnp [Hs [EQUIV_ACT [EQUIV_BLO EQUIV_LEA]]]]].
    destruct active as [| t act]; inversion EQUIV_ACT; subst.
    destruct blocked0 as [| t blo]; inversion EQUIV_BLO; subst.
    inversion STEP; subst; try congruence.
    admit.
  - (* pvs_nextchar_vt *)
    destruct H as [Hinp [Hnp [Hs [EQUIV_ACT [EQUIV_BLO EQUIV_LEA]]]]].
    inversion EQUIV_ACT. subst.
    inversion EQUIV_BLO. subst.
    inversion STEP; subst.
    + congruence.
    + repeat split; try assumption. congruence.
  - (* pvs_skip_vt *)
    destruct H as [Hinp [Hnp [Hs [EQUIV_ACT [EQUIV_BLO EQUIV_LEA]]]]].
    destruct active0 as [| t act]; inversion EQUIV_ACT; subst.
    apply seen_equiv with (seen:= seen) in H2; auto.
    inversion STEP; subst; try (rewrite H2 in *; congruence).
    admit.
  - (* pvs_active_vt *)
    destruct H as [Hinp [Hnp [Hs [EQUIV_ACT [EQUIV_BLO EQUIV_LEA]]]]].
    destruct active0 as [| t act]; inversion EQUIV_ACT; subst.
    specialize (epsilon_step_equiv_active _ _ _ _ _ _ _ H2 STEP0) as STEP1.
    destruct STEP1 as [na [STEP1 Hna]].
    apply seen_equiv with (seen:= seen) in H2; auto.
    inversion STEP; subst; try (rewrite H12 in *; congruence); try congruence.
    admit.
  - (* pvs_match_vt *)
    destruct H as [Hinp [Hnp [Hs [EQUIV_ACT [EQUIV_BLO EQUIV_LEA]]]]].
    destruct active0 as [| t act]; inversion EQUIV_ACT; subst.
    specialize (epsilon_step_equiv_match _ _ _ _ _ _ H2 STEP0) as [STEP1 Hr].
    specialize (seen_equiv t t0 seen regs0 H2) as Hse.
    inversion STEP; subst; try (rewrite H12 in *; congruence); try congruence.
    repeat split; try reflexivity.
    + admit.
    + constructor.
    + admit.
    + unfold thread_equiv in *.
      admit.
  - (* pvs_blocked_vt *)
    destruct H as [Hinp [Hnp [Hs [EQUIV_ACT [EQUIV_BLO EQUIV_LEA]]]]].
    destruct active0 as [| t act]; inversion EQUIV_ACT; subst.
    specialize (epsilon_step_equiv_blocked _ _ _ _ _ _ _ H2 STEP0) as [[nt [STEP1 Hnt]] Hr].
    apply seen_equiv with (seen:= seen) in H2; auto.
    inversion STEP; subst; try (rewrite H12 in *; congruence); try congruence.
    repeat split; auto.
    + admit.
    + rewrite STEP1 in STEP2. injection STEP2 as STEP2. subst.
      apply Forall2_app; auto.
Admitted.

Theorem trc_pikevm_vt_equiv: 
  forall r s s_vt result result_vt regs,
    state_equiv s s_vt ->
    trc_pike_vm rer r s (PVS_final result) ->
    trc_pike_vm_vt r s_vt (PVS_final_vt result_vt regs) ->
    leaves_equiv result result_vt regs.
Proof.
  intros r s s_vt result result_vt regs EQUIV TRC TRCVT.
  dependent induction TRC.
  - unfold state_equiv in EQUIV.
    destruct s_vt; try contradiction.
    inversion TRCVT; subst.
    + assumption.
    + inversion STEP.
  - inversion TRCVT. subst.
    + unfold state_equiv in EQUIV.
      destruct x; try contradiction.
      inversion STEP.
    + eapply IHTRC with (s_vt := y0).
      * eapply pike_vm_step_vt_equiv; eauto.
      * reflexivity.
      * assumption.
Qed.

Lemma init_states_equiv :
  forall inp,
    state_equiv (pike_vm_initial_state inp) (pike_vm_initial_state_vt inp rer_to_regs_size).
Proof.
  intro inp.
  unfold pike_vm_initial_state, pike_vm_initial_state_vt.
  simpl.
  repeat split; repeat constructor.
Qed.

Theorem pikevm_vt_equiv: 
  forall r inp result result_vt regs,
  trc_pike_vm rer (compilation r) (pike_vm_initial_state inp) (PVS_final result) ->
  trc_pike_vm_vt (compilation r) (pike_vm_initial_state_vt inp (rer_to_regs_size)) (PVS_final_vt result_vt regs) ->
  leaves_equiv result result_vt regs.
Proof.
  intros r inp result result_vt regs TRC TRCVT.
  eapply trc_pikevm_vt_equiv.
  - apply init_states_equiv.
  - exact TRC.
  - exact TRCVT.
Qed.

End PikeVM_VT.
