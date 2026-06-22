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
            match get_at (gid_to_idx gid) regsdata with
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
  Definition ri_of_leaf (l: option leaf_vt) : list regs_id :=
    match l with
    | Some (_, ri) => [ri]
    | None => []
    end.

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

  Definition max_gid_of (bc: bytecode) : group_id :=
    match bc with
    | Accept | Consume _ | CheckAnchor _ | Jmp _ | Fork _ _ | BeginLoop | EndLoop _ | KillThread => 0
    | SetRegOpen gid => gid
    | SetRegClose gid => gid
    | ResetRegs gidl => fold_left max gidl 0
    end.
  Definition max_group_c (c: code) : group_id :=
    fold_left (fun acc bc => max (max_gid_of bc) acc) c 0.

  Definition reg_to_regs_size (r: regex) :=
    2 * max_group_c (compilation r) + 2.
  
  Definition vt_initial_id := 0.
  Definition pike_vm_initial_thread_vt : thread_vt := (0, vt_initial_id, CanExit).

  (* initial state for the PikeVM_VT which operates in anchored fashion *)
  Definition pike_vm_initial_state_vt (inp:input) (regs_size: nat) : pike_vm_state_vt :=
    PVS_vt inp [pike_vm_initial_thread_vt] None [] None initial_seenpcs (Regs.initial_tree regs_size).

  Print fold_right. Print fold_left.
  Definition delete_ris_from_regs_state (lr: list regs_id) (r: regs) : regs :=
    List.fold_right (fun ri r => Regs.delete ri r) r lr.
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
           (DELETE_REGS: regs' = delete_ris_from_regs_state (map ri_of (thr::blocked)) regs),
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
           (DELETE_REG:  regs' = delete_ris_from_regs_state [ri_of t] regs), (* t is killed, so its regs are deleted *)
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
           (DELETE_REGS: regs'' = delete_ris_from_regs_state (ri_of_leaf best ++ (map ri_of active)) regs),
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
    let (cp1, _) := get_at (gid_to_idx gid) regsdata in
    let (cp2, _) := get_at (gid_to_idx gid + 1) regsdata in
    (cp1, cp2).

  Definition all_ris (s_vt: pike_vm_state_vt) : list regs_id :=
    match s_vt with
    | PVS_vt _ act best blo _ _ _ =>
        (map ri_of act) ++ (ri_of_leaf best) ++ (map ri_of blo)
    | PVS_final_vt best _ => ri_of_leaf best
    end.
    (*match s_vt with
    | PVS_vt _ act (Some leaf) blo _ _ _ =>
        (map ri_of act) ++ [(match leaf with (_, ri) => ri end)] ++ (map ri_of blo)
    | PVS_vt _ act None blo _ _ _ =>
        (map ri_of act) ++ (map ri_of blo)
    | PVS_final_vt (Some leaf) _ => match leaf with (_, ri) => [ri] end
    | PVS_final_vt None _ => []
    end.*)

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

  Print epsilon_step_vt.

  (*Lemma epsactive_inv :
    forall c inp t r r' tl,
      epsilon_step_vt t c inp r = (EpsActive_vt tl, r') ->
      let (rsplit, ri') := Regs.split (ri_of t) r in
      let (topen, ropen) := 
      tl = [] /\ r' = Regs.delete (ri_of t) r \/
        tl = [advance_thread_vt t] /\ r' = r \/
        (exists next, tl = [upd_label_vt t next (ri_of t)] /\ r' = r) \/
        (exists l1 l2, tl = [upd_label_vt t l1 (ri_of t); upd_labet_vt t l2 ri'] /\ r' = rsplit) \/*)
        
                                             

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

  Lemma in_smaller_than_max: forall l x acc,
      In x l ->
      x <= fold_left max l acc.
  Proof.
    induction l; intros x acc H; simpl in *.
    - contradiction.
    - destruct H as [H|H].
      + subst.
        apply fold_left_preserves; lia.
      + auto.
  Qed.

  Lemma max_gid_is_greatest' : forall c bc l acc,
      get_pc c l = Some bc ->
      max_gid_of bc <= fold_left (fun acc bc => Nat.max (max_gid_of bc) acc) c acc.
  Proof.
    induction c; intros bc l acc H; unfold get_pc in H; simpl in *.
    - rewrite nth_error_nil in H. congruence.
    - unfold max_group_c.
      destruct l eqn:L; simpl in H.
      * injection H as H. rewrite H.
        apply fold_left_preserves; lia.
      * eapply IHc.
        exact H.
  Qed.

  Lemma max_gid_is_greatest : forall c bc l,
      get_pc c l = Some bc ->
      max_gid_of bc <= max_group_c c.
  Proof.
    intros.
    eapply max_gid_is_greatest' with (acc:= 0).
    eassumption.
  Qed.

  Inductive state_valid_regs (regs_size : nat) : pike_vm_state_vt -> Prop :=
  | pvs_valid_regs:
    forall inp act best blo np seen regs
           (VALID_REGS: Regs.is_valid_state regs)
           (VALID_PARAM: Regs.param regs = regs_size),
      state_valid_regs regs_size (PVS_vt inp act best blo np seen regs)
  | pvs_final_valid_regs:
    forall best regs
           (VALID_REGS: Regs.is_valid_state regs)
           (VALID_PARAM: Regs.param regs = regs_size),
      state_valid_regs regs_size (PVS_final_vt best regs).

  Lemma epsactive_valid_regs :
    forall c inp t tl r r',
      Regs.param r = 2 * max_group_c c + 2 ->
      Regs.is_valid_state r ->
      epsilon_step_vt t c inp r = (EpsActive_vt tl, r') ->
      Regs.is_valid_state r' /\ Regs.param r = Regs.param r'.
  Proof.
    intros c inp t tl r r' PARAM VALID STEP.
    unfold epsilon_step_vt in *.
    destruct t as [[l ri] b].
    destruct (get_pc c l) eqn:BC.
    - destruct b0 eqn:B;
        try (injection STEP as H1 H2; inversion H1); subst.
      + destruct (check_read rer c0 inp forward); injection STEP as H1 H2.
        * inversion H1.
        * subst.
          split; [apply Regs.delete_valid; assumption | apply Regs.delete_param_unchanged].
      + destruct (anchor_satisfied rer a inp); injection STEP as H1 H2; subst; split;
          try apply Regs.delete_valid; try assumption;
          try apply Regs.delete_param_unchanged; reflexivity.
      + split; [assumption | reflexivity].
      + split; [apply Regs.split_valid; assumption | apply Regs.split_param_unchanged].
      + split; try apply Regs.insert_param_unchanged.
        apply Regs.insert_valid.
        * apply max_gid_is_greatest in BC.
          simpl in *.
          split. lia.
          repeat constructor.
          unfold is_valid_index, gid_to_idx.
          simpl. lia.
        * assumption.
      + unfold close_thread_vt in *.
        destruct (Regs.get_compressed_data ri r) eqn:COMP.
        * destruct (get_at (gid_to_idx g) t0) eqn:GA.
          destruct o eqn:O;
            try (injection STEP as H1 H2; subst; split; [assumption | reflexivity]).
          destruct (n <=? idx inp);
            injection STEP as H1 H2; subst;
            split;
            repeat try apply Regs.insert_valid;
            try assumption; try apply Regs.insert_param_unchanged.
          1,2,3: apply max_gid_is_greatest in BC;
          simpl in *;
          split; try lia;
          repeat constructor;
          unfold is_valid_index, gid_to_idx;
          simpl; lia.
          eapply eq_trans; eapply Regs.insert_param_unchanged.
        * injection STEP as H1 H2; subst; split; [assumption | reflexivity].
      + apply fold_left_preserves. try (split; [assumption | reflexivity]).
        intros a x [Hv Hp] Hin.
        split; try (rewrite Hp; eapply eq_trans; eapply Regs.insert_param_unchanged).
        repeat apply Regs.insert_valid; try assumption.
        all: apply max_gid_is_greatest in BC;
          apply in_smaller_than_max with (acc:=0) in Hin;
          simpl in *;
          split; try lia;
          repeat constructor;
          unfold is_valid_index, gid_to_idx;
          simpl; lia.
      + split; [assumption | reflexivity].
      + destruct b; injection STEP as H1 H2; subst;
          split; try reflexivity; try assumption.
        apply Regs.delete_valid; assumption.
      + split.
        * apply Regs.delete_valid; assumption.
        * apply Regs.delete_param_unchanged.
    - injection STEP as H1 H2; subst.
      split.
      * apply Regs.delete_valid; assumption.
      * apply Regs.delete_param_unchanged.
  Qed.

  Lemma pike_vm_step_vt_valid_regs :
    forall c s_vt s_vt',
      (* s_vt = (PVS inp act_vt best_vt blo_vt None seen regs) *)
      state_valid_regs (2 * max_group_c c + 2) s_vt ->
      pike_vm_step_vt c s_vt s_vt' ->
      state_valid_regs (2 * max_group_c c + 2) s_vt'.
  Proof.
    intros c s_vt s_vt' H STEP.
    dependent induction STEP; inversion H; subst; constructor; try auto.
    - unfold delete_ris_from_regs_state.
      apply fold_right_preserves; try assumption.
      intros a x Hs Hin.
      apply Regs.delete_valid.
      assumption.
    - unfold delete_ris_from_regs_state.
      rewrite <- VALID_PARAM.
      apply fold_right_preserves;
        [reflexivity | intros a x H'; rewrite <- H'; symmetry; apply Regs.delete_param_unchanged].
    - simpl.
      destruct t0 as [[l ri] b].
      apply Regs.delete_valid.
      assumption.
    - apply epsactive_valid_regs in STEP; try tauto.
    - apply epsactive_valid_regs in STEP; destruct STEP as [STEP STEP']; congruence.
    - apply epsmatch_same_regs in STEP. subst.
      unfold delete_ris_from_regs_state.
      destruct best;
        apply fold_right_preserves; try assumption;
        try destruct l as [i l]; try (intros a x Hs Hin);
        apply Regs.delete_valid; assumption.
    - unfold delete_ris_from_regs_state.
      rewrite <- VALID_PARAM.
      apply fold_right_preserves;
        [reflexivity | intros a x H'; rewrite <- H'; symmetry; apply Regs.delete_param_unchanged].
    - apply epsblocked_same_regs in STEP. destruct STEP as [Hr Hnewt]. subst.
      assumption.
    - apply epsblocked_same_regs in STEP. destruct STEP as [STEP _]; congruence.
  Qed.

  Lemma init_state_valid_regs :
    forall inp r,
      let regs_size := 2 * max_group_c (compilation r) + 2 in
      state_valid_regs regs_size (pike_vm_initial_state_vt inp (reg_to_regs_size r)).
  Proof.
    intros inp.
    unfold pike_vm_initial_state_vt.
    constructor.
    - unfold Regs.initial_tree, Regs.is_valid_state. simpl.
      unfold Regs.is_valid_tree_ids. unfold Regs.get_all_ids.
      repeat split; try tauto.
      constructor; auto.
      constructor.
    - unfold reg_to_regs_size.
      reflexivity.
  Qed.

  (*** * Invariant: register state's leaves ids is a permutation of state's regs_ids *)

  Definition leaf_ids_of (s: pike_vm_state_vt) : list nat :=
    match s with
    | PVS_vt _ _ _ _ _ _ r => Regs.get_all_ids (Regs.tree r)
    | PVS_final_vt _ r => Regs.get_all_ids (Regs.tree r)
    end.

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

  Lemma list_helper {A} : forall (l l' l'': list A) x,
      incl (x :: l'') l ->
      NoDup (x :: l'') ->
      Permutation l (l' ++ l'') ->
      In x l'.
  Proof.
    intros l l' l'' x INCL NODUP PERM.
    assert (IN: In x l) by (apply INCL; simpl; tauto).
    assert (IN': In x (l' ++ l'')) by (eapply Permutation_in; eauto).
    apply in_app_or in IN'.
    apply NoDup_cons_iff in NODUP.
    tauto.
  Qed.

  Lemma delete_threads_regs_removed :
    forall lr regs,
      Regs.is_valid_state regs ->
      NoDup lr  ->
      incl lr (Regs.get_all_ids (Regs.tree regs)) ->
      let regs' := delete_ris_from_regs_state lr regs in
      Permutation (Regs.get_all_ids (Regs.tree regs))
        ((Regs.get_all_ids (Regs.tree regs')) ++ lr).
  Proof.
    induction lr; intros regs VALID NODUP INCL; simpl in *.
    unfold Regs.is_valid_state in VALID.
    - rewrite app_nil_r.
      apply Permutation_refl.
    - simpl.
      eapply perm_trans.
      + inversion NODUP. subst.
        apply IHlr; apply incl_cons_inv in INCL; try tauto.
      + eapply perm_trans.
        2: apply Permutation_middle.
        rewrite app_comm_cons.
        apply Permutation_app_tail.
        apply Regs.delete_ids'; simpl in *. 
        * eapply list_helper with (l:= Regs.get_all_ids (Regs.tree regs)).
          -- exact INCL.
          -- assumption.
          -- inversion NODUP. subst.
             apply IHlr; auto.
             apply incl_cons_inv in INCL; tauto.
  Admitted.

  (*Lemma delete_threads_regs_removed' :
    forall lt regs,
      Regs.is_valid_state regs ->
      NoDup (map ri_of lt)  ->
      incl (map ri_of lt) (Regs.get_all_ids (Regs.tree regs)) ->
      let regs' := delete_thread_regs_from_regs_state lt regs in
      Permutation (Regs.get_all_ids (Regs.tree regs))
        ((Regs.get_all_ids (Regs.tree regs')) ++ (map ri_of lt)).
  Proof.
    induction lt; intros regs VALID NODUP INCL; simpl in *.
    - rewrite app_nil_r.
      apply Permutation_refl.
    - destruct a as [[l ri] b].
      simpl.
      eapply perm_trans.
      + inversion NODUP. subst.
        apply IHlt; apply incl_cons_inv in INCL; try tauto.
      + eapply perm_trans.
        2: apply Permutation_middle.
        rewrite app_comm_cons.
        apply Permutation_app_tail.
        apply Regs.delete_ids'; simpl in *.
        * eapply list_helper with (l:= Regs.get_all_ids (Regs.tree regs)).
          -- exact INCL.
          -- assumption.
          -- inversion NODUP. subst.
             apply IHlt; auto.
             apply incl_cons_inv in INCL; tauto.
        * admit.
        * admit.
  Admitted.*)
(*
  Lemma perm_swap_around {A} : forall (x: A) l l',
      Permutation (l ++ x :: l') (l' ++ x :: l).
  Proof.
    intros x l l'. Check app_cons.
    transitivity (l ++ l' ++ [x]).
    Search (Permutation (_ ++ _) _).
    - apply Permutation_app_head.
      rewrite app_cons.
      apply Permutation_app_comm.
    - transitivity ((l' ++ l) ++ [x]).
      + rewrite app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm.
      + rewrite <- app_assoc.
        apply Permutation_app_head.
        rewrite app_cons with (l:=l).
        apply Permutation_app_comm.
  Qed.*)

  Lemma incl_app_comm {A} : forall (l l' l'': list A),
      incl (l' ++ l'') l ->
      incl (l'' ++ l') l.
  Proof.
    unfold incl.
    intros l l' l'' H x Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin];
      apply H; apply in_or_app; [right | left]; assumption.
  Qed.

  Lemma active_regs_leaves :
    forall t c inp regs regs' nextactive,
      Regs.is_valid_state regs ->
      Regs.is_valid_id (Regs.tree regs) (ri_of t) ->
      epsilon_step_vt t c inp regs = (EpsActive_vt nextactive, regs') ->
      let rids := Regs.get_all_ids (Regs.tree regs) in
      let rids' := Regs.get_all_ids (Regs.tree regs') in
      let (_, ri') := Regs.split (ri_of t) regs in
      Permutation rids (ri_of t :: rids') /\ nextactive = [] \/
        Permutation (ri' :: rids) rids' /\ map ri_of nextactive = [ri_of t; ri'] \/
        rids = rids' /\ map ri_of nextactive = [ri_of t].
  Proof.
    intros t c inp regs regs' na VALID VID STEP.
    unfold Regs.is_valid_state, Regs.is_valid_tree_ids in VALID.
    simpl in *.
    unfold epsilon_step_vt in STEP.
    destruct t as [[l_vt ri] b_vt].
    destruct (get_pc c l_vt) eqn:PC.
    - destruct b eqn:B.
      + injection STEP as STEP _. inversion STEP.
      + destruct (check_read rer c0 inp forward).
        * injection STEP as STEP _. inversion STEP.
        * left.
          injection STEP as Hs Hr; subst.
          split; try reflexivity.
          apply Regs.delete_ids'; tauto.
      + destruct (anchor_satisfied rer a inp).
        * right. right. injection STEP as Hs Hr; subst. auto.
        * left.
          injection STEP as Hs Hr; subst.
          split; try reflexivity.
          apply Regs.delete_ids'; tauto.
      + right. right. injection STEP as Hs Hr; subst. auto.
      + right. left.
        injection STEP as Hs Hr; subst.
        split; try reflexivity.
        apply Regs.split_ids; try tauto.
        apply Regs.greater_than_max_is_invalid_id. lia.
      + right. right.
        unfold open_thread_vt in *.
        injection STEP as Hs Hr; subst.
        split; try reflexivity.
        apply Regs.insert_ids.
      + right. right.
        unfold close_thread_vt in *.
        destruct (Regs.get_compressed_data ri regs);
          try destruct (get_at (gid_to_idx g) t0) as [cp clk]; try destruct cp;
          try destruct (n <=? idx inp);
          injection STEP as Hs Hr; subst;
          split; try reflexivity.
        * apply Regs.insert_ids.
        * eapply eq_trans; apply Regs.insert_ids.
      + right. right.
        unfold reset_thread_vt in *.
        injection STEP as Hs Hr; subst.
        split; try reflexivity.
        apply fold_left_preserves; try reflexivity.
        intros a x Heq Hin.
        rewrite Heq.
        eapply eq_trans; apply Regs.insert_ids.
      + right. right. injection STEP as Hs Hr; subst. auto.
      + destruct b_vt.
        * right. right. injection STEP as Hs Hr; subst. auto.
        * left.
          injection STEP as Hs Hr; subst.
          split; try reflexivity.
          apply Regs.delete_ids'; tauto.
      + left.
        injection STEP as Hs Hr; subst.
        split; try reflexivity.
        apply Regs.delete_ids'; tauto.
    - left.
      injection STEP as Hs Hr; subst.
      split; try reflexivity.
      apply Regs.delete_ids'; tauto.
  Qed.
  
  Lemma pike_vm_step_vt_threads_are_leaves :
    forall c s_vt s_vt',
      (* s_vt = (PVS inp act_vt best_vt blo_vt None seen regs) *)
      state_valid_regs (2 * max_group_c c + 2) s_vt ->
      Permutation (all_ris s_vt) (leaf_ids_of s_vt) ->
      pike_vm_step_vt c s_vt s_vt' ->
      Permutation (all_ris s_vt') (leaf_ids_of s_vt').
  Proof.
    intros c s_vt s_vt' VALID ALLIDS STEP.
    dependent induction STEP;
      inversion VALID; subst;
      unfold Regs.is_valid_state, Regs.is_valid_tree_ids in VALID_REGS.
    - simpl in *.
      rewrite app_nil_r in ALLIDS.
      rewrite ALLIDS.
      apply Permutation_refl.
    - simpl all_ris. simpl in ALLIDS. unfold leaf_ids_of.
      destruct thr as [[l' ri] b].
      subst.
      eapply Permutation_app_inv_r with (l:= map ri_of ((l', ri, b) :: blocked)).
      rewrite ALLIDS.
      apply delete_threads_regs_removed.
      + auto.
      + apply Permutation_sym, Permutation_NoDup in ALLIDS; try tauto.
        eapply NoDup_app_remove_l; eauto.
      + apply perm_incl in ALLIDS; try tauto.
        apply incl_app_inv in ALLIDS. tauto.
    - simpl in *.
      rewrite <- ALLIDS.
      rewrite app_nil_r, app_comm_cons.
      apply Permutation_app_comm.
    - simpl all_ris. simpl in ALLIDS. unfold leaf_ids_of.
      eapply Permutation_app_inv_r with (l:= [ri_of t0]).
      eapply perm_trans with (l':= (Regs.get_all_ids (Regs.tree regs0))).
      + rewrite <- ALLIDS.
        rewrite app_cons with (l:= map ri_of active ++ ri_of_leaf best ++ map ri_of blocked).
        apply Permutation_app_comm.
      + apply delete_threads_regs_removed; auto.
        -- apply ListHelpers.NoDup_one.
        -- apply perm_incl in ALLIDS.
           rewrite app_cons in ALLIDS.
           rewrite app_cons in ALLIDS.
           apply incl_app_inv in ALLIDS. tauto.
    - simpl in *.
      apply active_regs_leaves in STEP;
        try assumption;
        try (apply perm_incl, incl_cons_inv in ALLIDS; tauto).
      simpl in STEP.
      destruct STEP as [[Hr Hna] | [[Hr Hna] | [Hr Hna]]].
      + rewrite Hna. simpl.
        eapply Permutation_cons_inv with (a:= ri_of t0).
        rewrite ALLIDS.
        assumption.
      + rewrite <- Hr.
        repeat rewrite map_app. rewrite Hna.
        eapply perm_trans; [eapply perm_swap | constructor; exact ALLIDS].
      + rewrite <- Hr.
        repeat rewrite map_app. rewrite Hna.
        exact ALLIDS.
    - apply epsmatch_same_regs in STEP. subst.
      eapply Permutation_app_inv_r with (l:= ri_of_leaf best ++ map ri_of active).
      eapply perm_trans with (l':= (Regs.get_all_ids (Regs.tree regs'))).
      + rewrite <- ALLIDS.
        simpl all_ris. simpl in ALLIDS. unfold leaf_ids_of.
        simpl. constructor.
        apply Permutation_app_middle.
        apply Permutation_app_comm.
      + apply delete_threads_regs_removed; auto;
          simpl in ALLIDS; rewrite app_assoc in ALLIDS.
        * apply Permutation_sym, Permutation_NoDup in ALLIDS; try tauto.
          apply NoDup_cons_iff in ALLIDS; destruct ALLIDS as [_ ALLIDS].
          apply NoDup_app_remove_r in ALLIDS.
          apply ListHelpers.NoDup_app_comm.
          assumption.
        * apply perm_incl in ALLIDS.
          apply incl_cons_inv in ALLIDS; destruct ALLIDS as [_ ALLIDS].
          apply incl_app_inv in ALLIDS; destruct ALLIDS as [ALLIDS _].
          apply incl_app_comm.
          assumption.
    - apply epsblocked_same_regs in STEP. destruct STEP as [Hr Hnewt].
      simpl in *. subst.
      rewrite <- ALLIDS.
      destruct t0 as [[l0 ri0] b0].
      rewrite map_app. simpl.
      rewrite app_cons with (l:= map ri_of active ++ ri_of_leaf best ++ map ri_of blocked).
      rewrite app_assoc with (n:= [ri0]).
      rewrite app_assoc with (n:= [ri0]).
      apply Permutation_app_comm.
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

  Lemma Forall2_and {A B} (f g : A -> B -> Prop) :
  forall l l',
    Forall2 f l l' ->
    Forall2 g l l' ->
    Forall2 (fun x y => f x y /\ g x y) l l'.
  Proof.
    intros l l' Hf Hg.
    induction Hf.
    - inversion Hg; constructor.
    - inversion Hg; subst.
      constructor.
      + auto.
      + auto.
  Qed.

  Lemma Forall2_notin_r :
  forall A B C (x : C) (l : list A) (l' : list B) p (f: B -> C),
    Forall2 (fun z y => p z y /\ f y <> x) l l' ->
    ~ In x (map f l').
  Proof.
    intros A B C x l l' p f H.
    induction H.
    - simpl; tauto.
    - simpl.
      intros [Hx | Hin].
      + subst. destruct H as [H H']. congruence.
      + apply IHForall2; assumption.
  Qed.

  Lemma notin_r_Forall :
    forall A B C (x : C) (l : list A) (l' : list B) (f: B -> C),
      ~ In x (map f l') ->
      length l = length l' ->
      Forall2 (fun z y => f y <> x) l l'.
  Proof.
    induction l; intros l' f H Hl.
    - simpl in *.
      destruct l'; try constructor; simpl in *; congruence.
    - simpl in *. destruct l'; simpl in *.
      + lia.
      + constructor.
        tauto.
        auto.
  Qed.

  Lemma threads_equiv_delete : forall l lvt regs ri,
      Regs.is_valid_state regs ->
      ~ In ri (map ri_of lvt) ->
      threads_equiv l lvt regs ->
      threads_equiv l lvt (Regs.delete ri regs).
  Proof.
    intros l lvt regs ri VALID IN EQUIV.
    unfold threads_equiv in *.
    assert (Forall2 (fun t tvt => thread_equiv t tvt regs /\ ri_of tvt <> ri) l lvt) as H.
    - apply Forall2_and; auto.
      apply notin_r_Forall; auto.
      eapply Forall2_length; exact EQUIV.
    - induction H; subst; constructor.
      + inversion EQUIV; subst.
        inversion H4; subst.
        constructor.
        unfold gm_vt_equiv in *.
        assert (Regs.get_compressed_data ri0 (Regs.delete ri regs) =
                  Regs.get_compressed_data ri0 regs) as GC.
        * apply Regs.delete_get_unchanged; auto.
          simpl in IN. symmetry. tauto.
        * rewrite GC. assumption.
      + apply IHForall2.
        * eapply Forall2_notin_r. exact H0.
        * inversion EQUIV; auto.
  Qed.

  Lemma leaves_equiv_delete : forall l lvt regs ri,
      Regs.is_valid_state regs ->
      ri_of_leaf lvt <> [ri] ->
      leaves_equiv l lvt regs ->
      leaves_equiv l lvt (Regs.delete ri regs).
  Proof.
    intros l lvt regs ri VALID IN EQUIV.
    inversion EQUIV; subst; constructor.
    unfold gm_vt_equiv in *.
    assert (Regs.get_compressed_data ri0 (Regs.delete ri regs) =
              Regs.get_compressed_data ri0 regs) as GC.
    - apply Regs.delete_get_unchanged; auto.
      simpl in IN. congruence.
    - rewrite GC. assumption.
  Qed.

  Lemma epsilon_step_equiv_active :
    forall c inp t t_vt nextactive_vt r r' act act_vt blo blo_vt l l_vt,
      Regs.is_valid_state r ->
      threads_equiv act act_vt r ->
      ~ In (ri_of t_vt) (map ri_of act_vt) ->
      threads_equiv blo blo_vt r ->
      ~ In (ri_of t_vt) (map ri_of blo_vt) ->
      leaves_equiv l l_vt r ->
      ri_of_leaf l_vt <> [ri_of t_vt] ->
      thread_equiv t t_vt r ->
      epsilon_step_vt t_vt c inp r = (EpsActive_vt nextactive_vt, r') ->
      (exists nextactive,
          epsilon_step rer t c inp = EpsActive nextactive /\
            threads_equiv nextactive nextactive_vt r' /\
            threads_equiv act act_vt r' /\
            threads_equiv blo blo_vt r' /\
            leaves_equiv l l_vt r').
  Proof.
    intros c inp t t_vt nextactive_vt r r' act act_vt blo blo_vt l l_vt.
    intros VALID EQACT INACT EQBLO INBLO EQLEA INLEA EQUIV STEP.
    inversion EQUIV; subst.
    unfold epsilon_step_vt, epsilon_step in *.
    destruct (get_pc c l0) eqn:PC.
    - destruct b0 eqn:B.
      + inversion STEP.
      + destruct (check_read rer c0 inp forward); inversion STEP.
        eexists; repeat split; try constructor.
        1, 2: apply threads_equiv_delete; auto.
        apply leaves_equiv_delete; auto.
      + destruct (anchor_satisfied rer a inp); inversion STEP; subst.
        * eexists; repeat split; try assumption.
          repeat constructor.
          assumption.
        * eexists; repeat split; try constructor.
          1, 2: apply threads_equiv_delete; auto.
          apply leaves_equiv_delete; auto.
      + inversion STEP; subst.
        eexists; repeat split; try assumption.
        repeat constructor.
        assumption.
      + destruct (Regs.split ri r) as [rs ri'] eqn:SPLIT.
        inversion STEP; subst.
        eexists; repeat split.
        all: admit. (* split *)
      + unfold open_thread, open_thread_vt in *.
        inversion STEP; subst.
        eexists; repeat split.
        all: admit. (* insert *)
      + unfold close_thread, close_thread_vt in *.
        inversion STEP; subst.
        admit.
      + admit.
      + inversion STEP; subst.
        eexists; repeat split; try assumption.
        repeat constructor.
        assumption.
      + destruct b; inversion STEP; subst;
          eexists; repeat split; try assumption.
        1, 2: repeat constructor; assumption.
        1, 2: apply threads_equiv_delete; auto.
        apply leaves_equiv_delete; auto.
      + inversion STEP; subst.
        eexists; repeat split; try constructor.
        1, 2: apply threads_equiv_delete; auto.
        apply leaves_equiv_delete; auto.
    - inversion STEP; subst.
      eexists; repeat split; try constructor.
      1, 2: apply threads_equiv_delete; auto.
      apply leaves_equiv_delete; auto.
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

  Lemma in_not_in_neq {A}: forall (x y: A) l,
      In x l ->
      ~ In y l ->
      x <> y.
  Proof.
    intros x y l Hx Hy Heq.
    apply Hy. congruence.
  Qed.

  Lemma threads_equ_del': forall lri regs lt ltvt,
      Forall2 (fun t tvt => thread_equiv t tvt regs /\
                              Regs.is_valid_state regs /\ ~ In (ri_of tvt) lri) lt ltvt ->
      let regs' := delete_ris_from_regs_state lri regs in
      Forall2 (fun t tvt => thread_equiv t tvt regs' /\
                              Regs.is_valid_state regs') lt ltvt.
  Proof.
    intros lri regs lt ltvt EQUIV.
    simpl.
    eapply Forall2_impl.
    2: exact EQUIV.
    intros rs th [Heq [Hv Hinl]].
    unfold delete_ris_from_regs_state.
    apply fold_right_preserves.
    - tauto.
    - intros rs' th' [Heq' Hv'] Hin.
      split.
      + inversion Heq'; subst. constructor.
        unfold gm_vt_equiv in *.
        assert (GC: Regs.get_compressed_data ri (Regs.delete th' rs') =
                      Regs.get_compressed_data ri rs').
        * apply Regs.delete_get_unchanged; auto.
          simpl in *.
          eapply in_not_in_neq; eauto.
        * rewrite GC. assumption.
      + apply Regs.delete_valid. assumption.
  Qed.

  Lemma Forall2_and {A B} (f g : A -> B -> Prop) :
  forall l l',
    Forall2 f l l' ->
    Forall2 g l l' ->
    Forall2 (fun x y => f x y /\ g x y) l l'.
  Proof.
    intros l l' Hf Hg.
    induction Hf.
    - inversion Hg; constructor.
    - inversion Hg; subst.
      constructor.
      + auto.
      + auto.
  Qed.

  Lemma Forall2_true_pred {A B} :
    forall (l : list A) (l' : list B) p,
      length l = length l' ->
      p ->
      Forall2 (fun x y => p) l l'.
  Proof.
    induction l as [|x l IH]; intros l' p Hlen Hp.
    - destruct l'.
      + constructor.
      + simpl in *. lia.
    - destruct l'; simpl in Hlen.
      + congruence.
      + inversion Hlen.
        constructor.
        * assumption.
        * apply IH; [lia | assumption].
  Qed.
    
  Lemma threads_equ_del: forall lri regs lt ltvt,
      Regs.is_valid_state regs ->
      (forall x, In x lri -> ~ In x (map ri_of ltvt)) ->
      threads_equiv lt ltvt regs ->
      threads_equiv lt ltvt (delete_ris_from_regs_state lri regs).
  Proof.
    intros lri regs lt ltvt VALID IN EQUIV.
    eapply Forall2_impl.
    2: apply threads_equ_del'.
    - intros t tvt [He Hs]. exact He.
    - unfold threads_equiv in EQUIV.
      apply Forall2_and; try exact EQUIV.
      apply Forall2_and.
      + apply Forall2_true_pred with (p:= Regs.is_valid_state regs).
        * eapply Forall2_length; eauto.
        * assumption.
      + assert (Hforall : Forall (fun y => ~ In (ri_of y) lri) ltvt).
        * apply Forall_forall.
          intros y Hy Hin.
          specialize (IN (ri_of y) Hin).
          apply IN.
          apply in_map; exact Hy.
        * revert Hforall. induction EQUIV; intro Hforall;
            inversion Hforall; subst; constructor; auto.
          apply IHEQUIV; auto.
          intros ri Hin.
          specialize (IN ri Hin). simpl in IN.
          tauto.
  Qed.

  Lemma leaves_equ_del: forall lri regs l lvt,
      Regs.is_valid_state regs ->
      ~ incl (ri_of_leaf lvt) lri \/ ri_of_leaf lvt = [] ->
      leaves_equiv l lvt regs ->
      leaves_equiv l lvt (delete_ris_from_regs_state lri regs).
  Proof.
    intros lri regs l lvt VALID INCL EQUIV.
    inversion EQUIV; subst; constructor.
    unfold gm_vt_equiv in *.
    assert (GC: Regs.get_compressed_data ri (delete_ris_from_regs_state lri regs) =
                  Regs.get_compressed_data ri regs).
    - unfold delete_ris_from_regs_state.
      remember (fold_right (fun ri r => Regs.delete ri r) regs lri) as fr.
      apply proj1 with (B:= Regs.is_valid_state fr).
      rewrite Heqfr.
      apply fold_right_preserves.
      + split; auto.
      + intros rs x [Heq Hv] Hin.
        split.
        * apply Regs.delete_get_unchanged; auto.
          intros Hxri.
          unfold incl in INCL.
          simpl in INCL.
          destruct INCL as [INCL | INCL].
          -- apply INCL.
             intros a H; destruct H; [subst; assumption | contradiction].
          -- congruence.
        * apply Regs.delete_valid.
          assumption.
    - rewrite GC.
      assumption.
  Qed.

  Lemma perm_nd_in {A} : forall (l a b c d : list A),
      Permutation (a ++ c) l ->
      incl b a ->
      incl d c ->
      NoDup l ->
      (forall x, In x b -> ~ In x d).
  Proof.
    intros l a b c d PERM IAB ICD ND.
    intros x Hb Hd.
    apply Permutation_sym in PERM.
    apply Permutation_NoDup in PERM; try assumption.
    unfold incl in *.
    apply IAB in Hb. apply ICD in Hd.
    eapply ListHelpers.NoDup_in_app; eauto.
  Qed.

  Lemma NoDup_app_not_incl_or_nil {A} :
  forall (a b : list A),
    NoDup (a ++ b) ->
    ~ incl a b \/ a = [].
  Proof.
    intros a b Hnd.
    destruct a as [|x a].
    - right; reflexivity.
    - left.
      intro Hincl.
      assert (Hinb : In x b) by (apply Hincl; left; reflexivity).
      inversion Hnd; subst.
      apply H1.
      apply in_or_app.
      tauto.
  Qed.

  Lemma nodup3 {A}: forall (a b c: list A),
      NoDup (a ++ b ++ c) ->
      NoDup (a ++ c ++ b).
  Proof.
     intros a b c Hnd.
     apply (Permutation_NoDup (l := a ++ b ++ c)).
     - apply Permutation_app_head.
       apply Permutation_app_comm.
     - auto.
  Qed.

  Lemma pike_vm_step_vt_equiv :
    forall c s s_vt s' s_vt',
      (* s = (PVS inp act best blo None seen) *)
      (* s_vt = (PVS inp act_vt best_vt blo_vt None seen regs) *)
      state_valid_regs (2 * max_group_c c + 2) s_vt ->
      Permutation (all_ris s_vt) (leaf_ids_of s_vt) ->
      state_equiv s s_vt ->
      pike_vm_step rer c s s' ->
      pike_vm_step_vt c s_vt s_vt' ->
      state_equiv s' s_vt'.
  Proof.
    intros c s s_vt s' s_vt' VALID PERM H STEP STEPVT.
    dependent induction STEPVT; destruct s; inversion H; subst;
      inversion VALID; subst;
      unfold Regs.is_valid_state, Regs.is_valid_tree_ids in VALID_REGS.
    - (* pvs_final_vt *)
      inversion EQUIV_ACT. inversion EQUIV_BLO. subst.
      inversion STEP. subst.
      constructor.
      assumption.
    - (* pvs_end_vt *)
      inversion EQUIV_ACT. inversion EQUIV_BLO. subst.
      inversion STEP; subst; try congruence.
      constructor.
      apply leaves_equ_del; try assumption.
      simpl in PERM. apply NoDup_app_not_incl_or_nil.
      apply Permutation_sym, Permutation_NoDup in PERM; try tauto.
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
      + apply threads_equ_del.
        * auto.
        * simpl in PERM.
          rewrite app_cons in PERM.
          eapply perm_nd_in;
            [exact PERM |
              apply incl_refl |
              apply incl_appl, incl_refl |
              tauto].
        * exact H4.
      + apply leaves_equ_del; try assumption.
        simpl in PERM. apply NoDup_app_not_incl_or_nil.
        apply Permutation_sym, Permutation_NoDup in PERM; try tauto.
        rewrite app_comm_cons, app_assoc in PERM.
        apply NoDup_app_remove_r, ListHelpers.NoDup_app_comm in PERM.
        rewrite List.List.app_cons in PERM.
        apply NoDup_app_remove_r in PERM.
        assumption.
      + apply threads_equ_del.
        * inversion VALID; auto.
        * simpl in PERM.
          rewrite app_comm_cons in PERM.
          eapply perm_nd_in; [exact PERM | unfold incl; simpl; tauto |
                               apply incl_appr, incl_refl | tauto].
        * assumption.
    - (* pvs_active_vt *)
      inversion EQUIV_ACT. subst.
      specialize (seen_equiv _ _ seen regs0 H3) as Hse.
      specialize (add_equiv_threads_to_seen _ _ seen _ H3) as Hadd.
      apply Permutation_sym, Permutation_NoDup in PERM; try tauto. simpl in PERM.
      inversion PERM; subst.
      repeat rewrite in_app_iff in H2.
      assert (~ In (ri_of t0) (map ri_of active)) as Hinact by tauto.
          (*(intros C; eapply in_map with (f:= ri_of) in C; tauto).*)
      assert (~ In t0 blocked) as Hinblo by (intros C; eapply in_map with (f:= ri_of) in C; tauto).
      assert (ri_of_leaf best <> [ri_of t0]) as Hinbest
          by (destruct best; try destruct l0; simpl in *; try congruence;
              assert (r <> ri_of t0) as K; [tauto | congruence]).
      specialize (epsilon_step_equiv_active _ _ _ _ _ _ _
                    l active blocked0 blocked best0 best
                    H4 Hinact EQUIV_BLO Hinblo EQUIV_LEA Hinbest H3 STEP0) as STEP1.
      destruct STEP1 as [na [STEP1 Heq]].
      inversion STEP; subst; try (rewrite H12 in *; congruence); try congruence.
      rewrite Hadd.
      rewrite STEP2 in STEP1. injection STEP1 as EQNA. subst.
      constructor; try apply Forall2_app; tauto.
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
      + apply leaves_equ_del; try assumption.
        * simpl. simpl in PERM.
          apply NoDup_app_not_incl_or_nil.
          apply Permutation_sym, Permutation_NoDup in PERM; try tauto.
          rewrite app_cons, app_assoc, app_assoc in PERM. apply NoDup_app_remove_r in PERM.
          apply nodup3. assumption.
        * inversion H3; subst.
          constructor. simpl.
          assumption.
      + apply threads_equ_del.
        * auto.
        * simpl in PERM.
          rewrite app_cons, app_assoc, app_assoc in PERM.
          eapply perm_nd_in;
            [exact PERM |
              rewrite <- app_assoc; apply incl_appr, incl_app_comm, incl_refl |
              apply incl_refl |
              tauto].
        * assumption.
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
  Qed.

  Lemma init_states_equiv :
    forall inp r,
      state_equiv (pike_vm_initial_state inp) (pike_vm_initial_state_vt inp (reg_to_regs_size r)).
  Proof.
    intro inp.
    unfold pike_vm_initial_state, pike_vm_initial_state_vt.
    simpl.
    repeat split; repeat constructor.
  Qed.

  (*** * Main results *)
  
  Lemma trc_pikevm_vt_equiv: 
    forall r s s_vt result result_vt regs,
      state_valid_regs (2 * max_group_c r + 2) s_vt ->
      Permutation (all_ris s_vt) (leaf_ids_of s_vt) ->
      state_equiv s s_vt ->
      trc_pike_vm rer r s (PVS_final result) ->
      trc_pike_vm_vt r s_vt (PVS_final_vt result_vt regs) ->
      leaves_equiv result result_vt regs.
  Proof.
    intros r s s_vt result result_vt regs VALID PERM EQUIV TRC TRCVT.
    dependent induction TRC.
    - inversion EQUIV. subst.
      inversion TRCVT; subst.
      + assumption.
      + inversion STEP.
    - inversion TRCVT; subst.
      + inversion EQUIV. subst.
        inversion STEP.
      + eapply IHTRC with (s_vt := y0).
        * eapply pike_vm_step_vt_valid_regs; eauto.
        * eapply pike_vm_step_vt_threads_are_leaves; eauto.
        * eapply pike_vm_step_vt_equiv; eauto.
        * reflexivity.
        * assumption.
  Qed.

  Theorem pikevm_vt_equiv: 
    forall r inp result result_vt regs,
      trc_pike_vm rer (compilation r) (pike_vm_initial_state inp) (PVS_final result) ->
      trc_pike_vm_vt (compilation r) (pike_vm_initial_state_vt inp (reg_to_regs_size r)) (PVS_final_vt result_vt regs) ->
      leaves_equiv result result_vt regs.
  Proof.
    intros r inp result result_vt regs TRC TRCVT.
    eapply trc_pikevm_vt_equiv.
    - apply init_state_valid_regs.
    - simpl. unfold vt_initial_id. repeat constructor.
    - apply init_states_equiv.
    - exact TRC.
    - exact TRCVT.
  Qed.

End PikeVM_VT.
