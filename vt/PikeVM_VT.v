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

From Stdlib Require Import List Lia Permutation.
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

  (** * PikeVM_VT threads  *)
  
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
        match Regs.get_compressed_data ri r with
        | None => (t, r) (* does nothing when the group has not been opened *)
        | Some regsdata =>
            match get_at (gid_to_idx gid) 0 regsdata with
            (* the second value is the unused clock *)
            | (None, _) => (t, r) (* does nothing when the group has not been opened *)
            | (Some startIdx, _) =>
                if (startIdx <=? idx) then
                  let new_close := Incomplete([(gid_to_idx gid + 1, Valid(idx), Undefined)]) in
                  let r' := Regs.insert ri new_close r in
                  ((l+1, ri, b), r')
                else
                  let new_start := Incomplete([(gid_to_idx gid, Valid(idx), Undefined)]) in
                  let new_close := Incomplete([(gid_to_idx gid + 1, Valid(startIdx), Undefined)]) in
                  let r' := Regs.insert ri new_start r in
                  let r'' := Regs.insert ri new_close r' in
                  ((l+1, ri, b), r'')
            end
        end
    end.

  Definition reset_thread_vt (t:thread_vt) (gidl:list group_id) (r:regs): thread_vt * regs :=
    match t with
      (l,ri,b) =>
        let r' := List.fold_left (
                      fun r gid =>
                        let new_start := Incomplete([(gid_to_idx gid, Invalid, Undefined)]) in
                        let new_close := Incomplete([(gid_to_idx gid + 1, Invalid, Undefined)]) in
                        let r' := Regs.insert ri new_start r in
                        Regs.insert ri new_close r')
                    gidl r in
        ((l+1, ri, b), r') end.

  Definition begin_thread_vt (t:thread_vt) : thread_vt :=
    match t with (l,r,b) => (l+1,r,CannotExit) end.
  
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

  (** * PikeVM_VT Semantics  *)

  Definition leaf_vt : Type := input * regs_id.

  (* semantic states of the PikeVM_VT algorithm *)
  Inductive pike_vm_state_vt : Type :=
  | PVS_vt (inp:input) (active: list thread_vt) (best: option leaf_vt) (blocked: list thread_vt) (nextprefix: option (nat * literal * StrSearch)) (seen: seenpcs) (r:regs)
  | PVS_final_vt (best: option leaf_vt) (r: regs).

(* given an input and literal, we compute the next prefix counter *)
(* since the counter is always offset by one, we first try to advance the input before performing a prefix search *)
(*Definition next_prefix_counter {strs:StrSearch} (inp: input) (lit: literal) : option (nat * literal * StrSearch) :=
  match advance_input inp forward with
  | None => None
  | Some (Input next pref) =>
      match str_search (prefix lit) next with
      | None => None
      | Some n => Some (n, lit, strs)
      end
  end.*)
  Definition rer_to_regs_size : nat :=
  match rer with
  | RegExpRecord.make _ _ _ _ cgc => 2 * cgc (* regs_size = 2 * rer.capturingGroupsCount *)
  end.
  
  Definition vt_initial_id := 0.
  Definition pike_vm_initial_thread_vt : thread_vt := (0, vt_initial_id, CanExit).

  (* initial state for the PikeVM_VT which operates in anchored fashion *)
  Definition pike_vm_initial_state_vt (inp:input) (regs_size: nat) : pike_vm_state_vt :=
    PVS_vt inp [pike_vm_initial_thread_vt] None [] None initial_seenpcs (Regs.initial_tree regs_size).

  Print fold_right. Print fold_left.
  Definition delete_thread_regs_from_regs_state (lt:list thread_vt) (r:regs) : regs :=
    List.fold_right (fun t r => (* get regs_id from thread, delete it from r *)
                      match t with
                        (_, ri, _) => Regs.delete ri r end) r lt.
  Definition delete_best_regs_from_regs_state (best:option leaf_vt) (r:regs) : regs :=
    match best with
    | Some (_, ri) => Regs.delete ri r
    | None => r
    end.

  (* small-step semantics for the PikeVM_VT algorithm *)
  (* Unanchored PikeVM rules are removed: pvs_acc, pvs_nextchar_generate, pvs_next_char_filter *)
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

  Definition trc_pike_vm_vt (c:code) := @trc pike_vm_state_vt (pike_vm_step_vt c).

  (** * Equivalence to the original PikeVM *)

  (*** * Defining equivalence *)

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

  Definition all_ris (s_vt: pike_vm_state_vt) : list regs_id :=
    match s_vt with
    | PVS_vt _ act (Some leaf) blo _ _ _ =>
        (map ri_of act) ++ [(match leaf with (_, ri) => ri end)] ++ (map ri_of blo)
    | PVS_vt _ act None blo _ _ _ =>
        (map ri_of act) ++ (map ri_of blo)
    | PVS_final_vt (Some leaf) _ => match leaf with (_, ri) => [ri] end
    | PVS_final_vt None _ => []
    end.

  Definition gm_vt_equiv (gm: group_map) (ri: regs_id) (r: regs) : Prop :=
    match Regs.get_compressed_data ri r with
    | None => gm = GroupMap.empty (* assuming groupmap is empty when no updates have been made *)
    | Some (regsdata) =>
        forall gid, gm_regs_vals gid gm = vt_regs_vals gid regsdata
    end.

  Inductive leaves_equiv : option leaf -> option leaf_vt -> regs -> Prop :=
  | no_match_equiv: forall r, leaves_equiv None None r
  | match_equiv:
    forall inp gm ri r
           (GMVT: gm_vt_equiv gm ri r),
      leaves_equiv (Some (inp, gm)) (Some (inp, ri)) r.

  Inductive thread_equiv : thread -> thread_vt -> regs -> Prop :=
  | thread_eq:
    forall l b gm ri r
           (GMVT: gm_vt_equiv gm ri r),
      thread_equiv (l, gm, b) (l, ri, b) r.

  Definition threads_equiv (t: list thread) (t_vt: list thread_vt) (r: regs): Prop :=
    List.Forall2 (fun t t_vt => thread_equiv t t_vt r) t t_vt.

  Inductive state_equiv: pike_vm_state -> pike_vm_state_vt -> Prop :=
  | pvs_state_equiv:
    forall inp act act_vt best best_vt blo blo_vt np seen r
           (EQUIV_ACT: threads_equiv act act_vt r)
           (EQUIV_LEA: leaves_equiv best best_vt r)
           (EQUIV_BLO: threads_equiv blo blo_vt r),
      state_equiv (PVS inp act best blo np seen) (PVS_vt inp act_vt best_vt blo_vt np seen r)
  | pvs_final_state_equiv:
    forall best best_vt r
           (EQUIV_LEA: leaves_equiv best best_vt r),
      state_equiv (PVS_final best) (PVS_final_vt best_vt r).

  (*** * Helpers: EpsMatch and EpsBlock do not modify the register state *)

  Lemma epsmatch_same_regs :
    forall c inp t_vt r r',
      epsilon_step_vt t_vt c inp r = (EpsMatch_vt, r') ->
      r = r'.
  Proof.
    intros c inp t_vt r r' H.
    unfold epsilon_step_vt in *.
    destruct t_vt as [[l_vt ri] b_vt].
    destruct (get_pc c l_vt) eqn:BC.
    - destruct b eqn:B;
        try (injection H as H1 H2; inversion H1).
      + injection H as H. assumption.
      + destruct (check_read rer c0 inp forward); injection H as H1 H2; inversion H1.
      + destruct (anchor_satisfied rer a inp); injection H as H1 H2; inversion H1.
      + destruct (close_thread_vt (l_vt, ri, b_vt) g (idx inp) r); injection H as H1 H2; inversion H1.
      + destruct b_vt; injection H as H _; inversion H.
    - injection H as H1 H2. inversion H1.
  Qed.

  Lemma epsblocked_same_regs :
    forall c inp t_vt t_vt' r r',
      epsilon_step_vt t_vt c inp r = (EpsBlocked_vt t_vt', r') ->
      r = r' /\ t_vt' = block_thread_vt t_vt.
  Proof.
    intros c inp t_vt t_vt' r r' H.
    unfold epsilon_step_vt in *.
    destruct t_vt as [[l_vt ri] b_vt].
    destruct (get_pc c l_vt) eqn:BC.
    - destruct b eqn:B;
        try (injection H as H1 H2; inversion H1).
      + destruct (check_read rer c0 inp forward); injection H as H1 H2; inversion H1.
        unfold block_thread_vt.
        auto.
      + destruct (anchor_satisfied rer a inp); injection H as H1 H2; inversion H1.
      + destruct (close_thread_vt (l_vt, ri, b_vt) g (idx inp) r); injection H as H1 H2; inversion H1.
      + destruct b_vt; injection H as H _; inversion H.
    - injection H as H1 H2. inversion H1.
  Qed.

  Lemma epsblocked_orig :
    forall c inp t t',
      epsilon_step rer t c inp = EpsBlocked t' ->
      t' = block_thread t.
  Proof.
    intros c inp t t' H.
    unfold epsilon_step in *.
    destruct t as [[l gm] b].
    destruct (get_pc c l) eqn:BC.
    - destruct b0 eqn:B; try inversion H.
      + destruct (check_read rer c0 inp forward); try inversion H.
        congruence.
      + destruct (anchor_satisfied rer a inp); inversion H.
      + destruct b; inversion H.
    - inversion H.
  Qed.

  (*** * Invariant: register state is valid *)

  Lemma fold_left_preserves {A} {B} :
    forall (l: list A) (acc: B) P f,
      P acc ->
      (forall a x, P a -> In x l -> P (f a x)) ->
      P (fold_left f l acc).
  Proof.
    induction l as [|x xs IH]; intros acc P f H H'; simpl in *.
    - assumption.
    - apply IH.
      + apply H'; auto.
      + intros a x' HP Hin.
        apply H'; auto.
  Qed.

  Lemma fold_right_preserves {A} {B} :
    forall (l: list A) (acc: B) P f,
      P acc ->
      (forall a x, P a -> In x l -> P (f x a)) ->
      P (fold_right f acc l).
  Proof.
    induction l as [|x xs IH]; intros acc P f H Hf; simpl in *.
    - assumption.
    - apply Hf.
      + apply IH; auto.
      + auto.
  Qed.

  Inductive state_valid_regs: pike_vm_state_vt -> Prop :=
  | pvs_valid_regs:
    forall inp act best blo np seen regs
           (VALID_REGS: Regs.is_valid_state regs),
      state_valid_regs (PVS_vt inp act best blo np seen regs)
  | pvs_final_valid_regs:
    forall best regs
           (VALID_REGS: Regs.is_valid_state regs),
      state_valid_regs (PVS_final_vt best regs).

  Lemma epsactive_valid_regs :
    forall c inp t tl r r',
      Regs.is_valid_state r ->
      epsilon_step_vt t c inp r = (EpsActive_vt tl, r') ->
      Regs.is_valid_state r'.
  Proof.
    intros c inp t tl r r' VALID STEP.
    unfold epsilon_step_vt in *.
    destruct t as [[l ri] b].
    destruct (get_pc c l) eqn:BC.
    - destruct b0 eqn:B;
        try (injection STEP as H1 H2; inversion H1); subst.
      + destruct (check_read rer c0 inp forward); injection STEP as H1 H2.
        * inversion H1.
        * subst.
          apply Regs.delete_valid.
          assumption.
      + destruct (anchor_satisfied rer a inp); injection STEP as H1 H2; subst;
          try apply Regs.delete_valid; assumption.
      + assumption.
      + apply Regs.split_valid.
        assumption.
      + apply Regs.insert_valid.
        * admit. (* TODO prove inserted data is valid *)
        * assumption.
      + unfold close_thread_vt in *.
        destruct (Regs.get_compressed_data ri r) eqn:COMP.
        * destruct (get_at (gid_to_idx g) 0 t0) eqn:GA.
          destruct o eqn:O;
            try (injection STEP as H1 H2; subst; assumption).
          destruct (n <=? idx inp);
            injection STEP as H1 H2; subst;
            repeat try apply Regs.insert_valid;
            try assumption.
          all: admit. (* TODO prove inserted data is valid *)
        * injection STEP as H1 H2; subst; assumption.
      + apply fold_left_preserves; try assumption.
        intros a x Hv Hin.
        repeat apply Regs.insert_valid; try assumption.
        all: admit. (* TODO prove inserted data is valid *)
      + assumption.
      + destruct b; injection STEP as H1 H2; subst;
          try apply Regs.delete_valid; assumption.
      + apply Regs.delete_valid; assumption.
    - injection STEP as H1 H2; subst.
      apply Regs.delete_valid; assumption.
  Admitted.

  Lemma pike_vm_step_vt_valid_regs :
    forall c s_vt s_vt',
      (* s_vt = (PVS inp act_vt best_vt blo_vt None seen regs) *)
      state_valid_regs s_vt ->
      pike_vm_step_vt c s_vt s_vt' ->
      state_valid_regs s_vt'.
  Proof.
    intros c s_vt s_vt' H STEP.
    dependent induction STEP; inversion H; subst; constructor.
    - assumption.
    - unfold delete_thread_regs_from_regs_state.
      apply fold_right_preserves; try assumption.
      intros a x Hs Hin.
      destruct x as [[l ri] b].
      apply Regs.delete_valid.
      assumption.
    - assumption.
    - simpl.
      destruct t0 as [[l ri] b].
      apply Regs.delete_valid.
      assumption.
    - apply epsactive_valid_regs in STEP; try assumption.
    - apply epsmatch_same_regs in STEP. subst.
      unfold delete_best_regs_from_regs_state.
      destruct best;
        unfold delete_thread_regs_from_regs_state;
        apply fold_right_preserves; try assumption;
        try destruct l as [i l]; try (intros a x Hs Hin; destruct x as [[l' ri] b]);
        apply Regs.delete_valid; assumption.
    - apply epsblocked_same_regs in STEP. destruct STEP as [Hr Hnewt]. subst.
      assumption.
  Qed.

  Lemma init_state_valid_regs :
    forall inp,
      state_valid_regs (pike_vm_initial_state_vt inp rer_to_regs_size).
  Proof.
    intros inp.
    unfold pike_vm_initial_state_vt.
    constructor.
    unfold Regs.initial_tree, Regs.is_valid_state. simpl.
    unfold Regs.is_valid_tree_ids. unfold Regs.get_all_ids.
    repeat split; try tauto.
    constructor; auto.
    constructor.
  Qed.

  (*** * Invariant: register state's leaves ids is a permutation of state's regs_ids *)

  Definition leaf_ids_of (s: pike_vm_state_vt) : list nat :=
    match s with
    | PVS_vt _ _ _ _ _ _ r => Regs.get_all_ids (Regs.tree r)
    | PVS_final_vt _ r => Regs.get_all_ids (Regs.tree r)
    end.

  Lemma delete_threads_regs_removed :
    forall lt regs,
      (* NoDup map ri_of lt  ->*)
      incl (map ri_of lt) (Regs.get_all_ids (Regs.tree regs)) ->
      let regs' := delete_thread_regs_from_regs_state lt regs in
      Permutation (Regs.get_all_ids (Regs.tree regs))
        ((Regs.get_all_ids (Regs.tree regs')) ++ (map ri_of lt)).
  Proof.
    induction lt; intros regs INCL; simpl in *.
    - rewrite app_nil_r.
      apply Permutation_refl.
    - destruct a as [[l ri] b].
      simpl.
      eapply perm_trans.
      + apply IHlt.
        apply incl_cons_inv in INCL.
        tauto.
      + eapply perm_trans.
        2: apply Permutation_middle.
        rewrite app_comm_cons.
        apply Permutation_app_tail.
        
  Admitted.
    
  Lemma perm_incl {A} :
    forall (a b: list A),
      Permutation a b ->
      incl a b.
  Proof.
    unfold incl.
    intros a b PERM.
    dependent induction PERM; intros n H; simpl in *.
    - tauto.
    - destruct H; auto.
    - destruct H as [H | [H | H]]; auto.
    - auto.
  Qed.
  
  Lemma pike_vm_step_vt_threads_are_leaves :
    forall c s_vt s_vt',
      (* s_vt = (PVS inp act_vt best_vt blo_vt None seen regs) *)
      state_valid_regs s_vt ->
      Permutation (all_ris s_vt) (leaf_ids_of s_vt) ->
      pike_vm_step_vt c s_vt s_vt' ->
      Permutation (all_ris s_vt') (leaf_ids_of s_vt').
  Proof.
    intros c s_vt s_vt' VALID ALLIDS STEP.
    dependent induction STEP.
    - destruct best; simpl in *;
        try destruct l as [_ ri]; rewrite ALLIDS;
        apply Permutation_refl.
    - destruct best; destruct thr as [[l' ri] b];
        try destruct l;
        subst;
        eapply Permutation_app_inv_r with (l:= map ri_of ((l', ri, b) :: blocked));
        eapply perm_trans;
        try exact ALLIDS; apply delete_threads_regs_removed;
        apply perm_incl in ALLIDS; try tauto;
        apply incl_cons_inv in ALLIDS;
        try tauto.
    - destruct best; simpl in *.
      + destruct l.
        rewrite <- ALLIDS.
        rewrite app_comm_cons. apply Permutation_app_comm.
      + rewrite app_nil_r. rewrite ALLIDS.
        apply Permutation_refl.
    - destruct best; simpl in *; destruct t0 as [[l' ri] b].
      + destruct l.
        admit.
      + admit.
    - destruct best; simpl in *.
      all: admit.
    - apply epsmatch_same_regs in STEP. subst.
      admit.
    - apply epsblocked_same_regs in STEP. destruct STEP as [Hr Hnewt]. subst.
      destruct best; simpl in *;
        try destruct l;
        rewrite <- ALLIDS;
        destruct t0 as [[l ri] b];
        rewrite map_app; simpl;
        try rewrite app_assoc with (m:= r :: map ri_of blocked) (n:= [ri]);
        try rewrite app_assoc with (m:= map ri_of blocked) (n:= [ri]);
        apply Permutation_app_comm.
  Admitted.

  Lemma init_state_threads_are_leaves :
    forall inp,
      let si := pike_vm_initial_state_vt inp rer_to_regs_size in
      Permutation (all_ris si) (leaf_ids_of si).
  Proof.
    intros inp; simpl.
    unfold vt_initial_id.
    repeat constructor.
  Qed.

  (*** * Equivalence invariant *)

  Lemma seen_equiv : forall t t_vt seen r,
      thread_equiv t t_vt r ->
      seen_thread_vt seen t_vt = seen_thread seen t.
  Proof.
    intros t t_vt seen r H.
    inversion H. subst.
    unfold seen_thread, seen_thread_vt in *.
    reflexivity.
  Qed.

  Lemma add_equiv_threads_to_seen : forall t t_vt seen r,
      thread_equiv t t_vt r ->
      add_thread seen t = add_thread_vt seen t_vt.
  Proof.
    unfold add_thread, add_thread_vt.
    intros t t_vt seen r H.
    inversion H. subst.
    reflexivity.
  Qed.

  Lemma epsilon_step_equiv_active :
    forall c inp t t_vt nextactive_vt r r',
      thread_equiv t t_vt r ->
      epsilon_step_vt t_vt c inp r = (EpsActive_vt nextactive_vt, r') ->
      (exists nextactive,
          epsilon_step rer t c inp = EpsActive nextactive /\
            threads_equiv nextactive nextactive_vt r').
  Proof.
    intros c inp t t_vt nextactive_vt r r' Heq H.
    inversion Heq. subst.
    unfold epsilon_step_vt, epsilon_step in *.
    destruct (get_pc c l) eqn:BC.
    - destruct b0 eqn:B;
        try (injection H as H1 H2; inversion H1); subst.
      + destruct (check_read rer c0 inp forward); injection H as H1 H2; inversion H1.
        subst.
        exists [].
        split; [reflexivity | constructor].
      + destruct (anchor_satisfied rer a inp); injection H as H1 H2; inversion H1; subst.
        * admit.
        * exists [].
          split; [reflexivity | constructor].
      + exists ([upd_label (l, gm, b) l0]).
        split; try reflexivity.
        repeat constructor.
        assumption.
      + exists ([upd_label (l, gm, b) l0; upd_label (l, gm, b) l0]).
        split; try reflexivity.
        repeat constructor.
        all: admit.
      + exists ([open_thread (l, gm, b) g (idx inp)]).
        split; try reflexivity.
        repeat constructor.
        admit.
      + exists ([close_thread (l, gm, b) g (idx inp)]).
        split; try reflexivity.
        repeat constructor.
        admit.
      + exists ([reset_thread (l, gm, b) l0]).
        split; try reflexivity.
        repeat constructor.
        admit.
      + exists ([begin_thread (l, gm, b)]).
        split; try reflexivity.
        repeat constructor.
        assumption.
      + destruct b; injection H as H1 H2; inversion H1; subst.
        * exists ([upd_label (l, gm, CanExit) l0]).
          split; try reflexivity.
          repeat constructor.
          assumption.
        * exists [].
          split; [reflexivity | constructor].
      + exists [].
        split; [reflexivity | constructor].
    - injection H as H1 H2. inversion H1. subst.
      exists [].
      split.
      + reflexivity.
      + constructor.
  Admitted.

  Lemma epsilon_step_equiv_match :
    forall c inp t t_vt r r',
      thread_equiv t t_vt r ->
      epsilon_step_vt t_vt c inp r = (EpsMatch_vt, r') ->
      epsilon_step rer t c inp = EpsMatch.
  Proof.
    intros c inp t t_vt r r' Heq H.
    unfold epsilon_step_vt, epsilon_step in *.
    inversion Heq. subst.
    destruct (get_pc c l) eqn:BC.
    - destruct b0 eqn:B;
        try (injection H as H1 H2; inversion H1).
      + injection H as H. subst.
        auto.
      + destruct (check_read rer c0 inp forward); injection H as H1 H2; inversion H1.
      + destruct (anchor_satisfied rer a inp); injection H as H1 H2; inversion H1.
      + destruct (close_thread_vt (l, ri, b) g (idx inp) r).
        injection H as H1 H2; inversion H1.
      + destruct b; injection H as H _; inversion H.
    - injection H as H1 H2. inversion H1.
  Qed.

  Lemma epsilon_step_equiv_blocked :
    forall c inp t t_vt newt_vt r r',
      thread_equiv t t_vt r ->
      epsilon_step_vt t_vt c inp r = (EpsBlocked_vt newt_vt, r') ->
      (exists newt,
          epsilon_step rer t c inp = EpsBlocked newt /\
            thread_equiv newt newt_vt r').
  Proof.
    intros c inp t t_vt newt_vt r r' Heq H.
    unfold epsilon_step_vt, epsilon_step in *.
    inversion Heq. subst.
    destruct (get_pc c l) eqn:BC.
    - destruct b0 eqn:B;
        try (injection H as H1 H2; inversion H1).
      + destruct (check_read rer c0 inp forward);
          injection H as H1 H2.
        * subst.
          exists (l+1, gm, CanExit).
          split; try constructor.
          assumption.
        * inversion H1.
      + destruct (anchor_satisfied rer a inp); injection H as H1 H2; inversion H1.
      + destruct (close_thread_vt (l, ri, b) g (idx inp) r);
          injection H as H1 H2; inversion H1.
      + destruct b; injection H as H _; inversion H.
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
    intros c s s_vt s' s_vt' H STEP STEPVT.
    dependent induction STEPVT; destruct s; inversion H; subst.
    - (* pvs_final_vt *)
      inversion EQUIV_ACT. inversion EQUIV_BLO. subst.
      inversion STEP. subst.
      constructor.
      assumption.
    - (* pvs_end_vt *)
      inversion EQUIV_ACT. inversion EQUIV_BLO. subst.
      inversion STEP; subst; try congruence.
      constructor.
      admit.
    - (* pvs_nextchar_vt *)
      inversion EQUIV_ACT. inversion EQUIV_BLO. subst.
      inversion STEP; subst.
      + congruence.
      + rewrite ADVANCE in ADVANCE0. injection ADVANCE0 as INP. rewrite INP.
        constructor; assumption.
    - (* pvs_skip_vt *)
      inversion EQUIV_ACT. subst.
      apply seen_equiv with (seen:= seen) in H3; auto.
      inversion STEP; subst; try (rewrite H3 in *; congruence).
      constructor.
      + admit.
      + destruct best0, best; inversion EQUIV_LEA; subst; constructor.
        admit.
      + admit.
    - (* pvs_active_vt *)
      inversion EQUIV_ACT. subst.
      specialize (epsilon_step_equiv_active _ _ _ _ _ _ _ H3 STEP0) as STEP1.
      destruct STEP1 as [na [STEP1 Hna]].
      specialize (seen_equiv _ _ seen regs0 H3) as Hse.
      specialize (add_equiv_threads_to_seen _ _ seen _ H3) as Hadd.
      inversion STEP; subst; try (rewrite H12 in *; congruence); try congruence.
      rewrite Hadd.
      constructor.
      + admit.
      + destruct best0, best; inversion EQUIV_LEA; subst; constructor.
        admit.
      + admit.
    - (* pvs_match_vt *)
      inversion EQUIV_ACT. subst.
      specialize (epsilon_step_equiv_match _ _ _ _ _ _ H3 STEP0) as STEP1.
      specialize (epsmatch_same_regs _ _ _ _ _ STEP0) as Hr.
      specialize (seen_equiv _ _ seen regs0 H3) as Hse.
      specialize (add_equiv_threads_to_seen _ _ seen _ H3) as Hadd.
      inversion STEP; subst; try (rewrite H12 in *; congruence); try congruence.
      rewrite Hadd.
      constructor.
      + constructor.
      + constructor.
        admit.
      + admit.
    - (* pvs_blocked_vt *)
      inversion EQUIV_ACT. subst.
      specialize (epsilon_step_equiv_blocked _ _ _ _ _ _ _ H3 STEP0) as [nt [STEP1 Hnt]].
      specialize (epsblocked_same_regs _ _ _ _ _ _ STEP0) as [Hr Hnewt].
      specialize (seen_equiv _ _ seen regs0 H3) as Hse.
      specialize (add_equiv_threads_to_seen _ _ seen _ H3) as Hadd.
      inversion STEP; subst; try (rewrite H12 in *; congruence); try congruence.
      rewrite Hadd.
      constructor; auto.
      rewrite STEP2 in *. injection STEP1 as STEP1. subst.
      apply epsblocked_orig in STEP2. subst.
      apply Forall2_app; try assumption.
      constructor; auto.
  Admitted.

  Lemma init_states_equiv :
    forall inp,
      state_equiv (pike_vm_initial_state inp) (pike_vm_initial_state_vt inp rer_to_regs_size).
  Proof.
    intro inp.
    unfold pike_vm_initial_state, pike_vm_initial_state_vt.
    simpl.
    repeat split; repeat constructor.
  Qed.

  (*** * Main results *)

  Lemma trc_pikevm_vt_equiv: 
    forall r s s_vt result result_vt regs,
      state_equiv s s_vt ->
      trc_pike_vm rer r s (PVS_final result) ->
      trc_pike_vm_vt r s_vt (PVS_final_vt result_vt regs) ->
      leaves_equiv result result_vt regs.
  Proof.
    intros r s s_vt result result_vt regs EQUIV TRC TRCVT.
    dependent induction TRC.
    - inversion EQUIV. subst.
      inversion TRCVT; subst.
      + assumption.
      + inversion STEP.
    - inversion TRCVT; subst.
      + inversion EQUIV. subst.
        inversion STEP.
      + eapply IHTRC with (s_vt := y0).
        * eapply pike_vm_step_vt_equiv; eauto.
        * reflexivity.
        * assumption.
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
