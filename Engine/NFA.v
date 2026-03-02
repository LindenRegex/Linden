From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree.
From Linden Require Import Semantics PikeSubset.
From Linden Require Import Parameters.
From Warblre Require Import Numeric.

Section NFA.
  Context {params: LindenParameters}.

  (** * NFA Bytecode *)
  (* the bytecode generated for the PikeVM algorithm *)

  Definition label : Type := nat.

  Inductive bytecode: Type :=
  | Accept
  | Consume: char_descr -> bytecode
  | CheckAnchor: anchor -> bytecode
  | Jmp: label -> bytecode
  | Fork: label -> label -> bytecode
  | SetRegOpen: group_id -> bytecode
  | SetRegClose: group_id -> bytecode
  | ResetRegs: list group_id -> bytecode
  | BeginLoop: bytecode
  | EndLoop: label -> bytecode    (* also contains the backedge instead of adding a jump *)
  | KillThread: bytecode         (* for unsupported features *)
  .

  Definition code : Type := list bytecode.

  Definition get_pc (c:code) (pc:label) : option bytecode :=
    List.nth_error c pc.

  (** * Bytecode Properties  *)
  Lemma get_prefix:
    forall c pc prev,
      get_pc (prev ++ c) (length prev + pc) = get_pc c pc.
  Proof.
    unfold get_pc. intros.
    rewrite nth_error_app2; try f_equal; lia.
  Qed.

  Corollary get_first:
    forall c prev,
      get_pc (prev ++ c) (length prev) = get_pc c 0.
  Proof.
    intros. replace (length prev) with (length prev + 0) by lia.
    apply get_prefix.
  Qed.

  Corollary get_first_0:
    forall c prev x,
      x = length prev ->
      get_pc (prev ++ c) (x) = get_pc c 0.
  Proof.
    intros. subst. apply get_first.
  Qed.

  Corollary get_second:
    forall c prev,
      get_pc (prev ++ c) (S (length prev)) = get_pc c 1.
  Proof.
    intros. replace (S (length prev)) with (length prev + 1) by lia.
    apply get_prefix.
  Qed.

  Corollary get_third:
    forall c prev,
      get_pc (prev ++ c) (S (S (length prev))) = get_pc c 2.
  Proof.
    intros. replace (S (S (length prev))) with (length prev + 2) by lia.
    apply get_prefix.
  Qed.

  Lemma get_suffix:
    forall c suffix pc i,
      get_pc c pc = Some i ->
      get_pc (c++suffix) pc = Some i.
  Proof.
    unfold get_pc. intros c suffix pc i H.
    assert (pc < length c).
    { apply nth_error_Some. rewrite H. unfold not. intros. inversion H0. }
    rewrite nth_error_app1; auto.
  Qed.

  Lemma get_prev:
    forall prev suffix pc i,
      get_pc (prev ++ suffix) pc = Some i ->
      pc < length prev ->
      get_pc prev pc = Some i.
  Proof.
    unfold get_pc. intros. rewrite nth_error_app1 in H; auto.
  Qed.

  Definition next_pcs (pc:label) (b:bytecode) : list label :=
    match b with
    | Consume _ | CheckAnchor _ | SetRegOpen _ | SetRegClose _ | ResetRegs _ | BeginLoop => [S pc]
    | Accept | KillThread => []
    | Jmp l | EndLoop l => [l]
    | Fork l1 l2 => [l1; l2]
    end.

  (** * NFA Compilation  *)

  Definition greedy_fork (greedy:bool) (l1 l2:label) :=
    if greedy
    then Fork l1 l2
    else Fork l2 l1.

  (* also returns the next fresh label *)
  Fixpoint compile (r:regex) (fresh:label) : code * label :=
    match r with
    | Epsilon => ([], fresh)
    | Character cd => ([Consume cd], S fresh)
    | Disjunction r1 r2 =>
        let (bc1, f1) := compile r1 (S fresh) in
        let (bc2, f2) := compile r2 (S f1) in
        ([Fork (S fresh) (S f1)] ++ bc1 ++ [Jmp f2] ++ bc2, f2)
    | Sequence r1 r2 =>
        let (bc1, f1) := compile r1 fresh in
        let (bc2, f2) := compile r2 f1 in
        (bc1 ++ bc2, f2)
    | Quantified greedy 0 (NoI.N 0) r1 => ([], fresh)
    | Quantified greedy 0 (NoI.N 1) r1 =>
        let (bc1, f1) := compile r1 (S (S (S fresh))) in
        ([greedy_fork greedy (S fresh) (S f1); BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop (S f1)], S f1)
    | Quantified greedy 0 (NoI.Inf) r1 =>
        let (bc1, f1) := compile r1 (S (S (S fresh))) in
        ([greedy_fork greedy (S fresh) (S f1); BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop fresh], S f1)
    | Group gid r1 =>
        let (bc1, f1) := compile r1 (S fresh) in
        ([SetRegOpen gid] ++ bc1 ++ [SetRegClose gid], S f1)
    | Anchor a => ([CheckAnchor a], S fresh)
    | _ => ([KillThread], S fresh) (* unsupported features *)
    end.

  (* adds an accept at the end of the code *)
  Definition compilation (r:regex) : code :=
    match (compile r 0) with
    | (c,fresh) => c ++ [Accept]
    end.

  (** * Inductive NFA characterization *)
  (* like a representation predicate *)

  (* nfa_rep r code pc1 pc2 means that the bytecode for r is represented in code, from pc1 to pc2 (excluded)  *)
  Inductive nfa_rep : regex -> code -> label -> label -> Prop :=
  | nfa_rep_epsilon:
    forall c lbl,
      nfa_rep Epsilon c lbl lbl
  | nfa_rep_char:
    forall c cd lbl
      (CONSUME: get_pc c lbl = Some (Consume cd)),
      nfa_rep (Character cd) c lbl (S lbl)
  | nfa_rep_disj:
    forall c r1 r2 start end1 end2
      (FORK: get_pc c start = Some (Fork (S start) (S end1)))
      (NFA1: nfa_rep r1 c (S start) end1)
      (JMP: get_pc c end1 = Some (Jmp end2))
      (NFA2: nfa_rep r2 c (S end1) end2),
      nfa_rep
        (Disjunction r1 r2) c start end2
  | nfa_rep_seq:
    forall c r1 r2 start end1 end2
      (NFA1: nfa_rep r1 c start end1)
      (NFA2: nfa_rep r2 c end1 end2),
      nfa_rep (Sequence r1 r2) c start end2
  | nfa_rep_done:
    forall c r1 greedy lbl,
      nfa_rep (Quantified greedy 0 (NoI.N 0) r1) c lbl lbl
  | nfa_rep_qmark:
    forall c r1 greedy start end1
      (FORK: get_pc c start = Some (greedy_fork greedy (S start) (S end1)))
      (BEGIN: get_pc c (S start) = Some (BeginLoop))
      (RESET: get_pc c (S (S start)) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S start))) end1)
      (END: get_pc c end1 = Some (EndLoop (S end1))),
      nfa_rep (Quantified greedy 0 (NoI.N 1) r1) c start (S end1)
  | nfa_rep_star:
    forall c r1 greedy start end1
      (FORK: get_pc c start = Some (greedy_fork greedy (S start) (S end1)))
      (BEGIN: get_pc c (S start) = Some (BeginLoop))
      (RESET: get_pc c (S (S start)) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S start))) end1)
      (END: get_pc c end1 = Some (EndLoop start)),
      nfa_rep (Quantified greedy 0 (NoI.Inf) r1) c start (S end1)
  | nfa_rep_group:
    forall c r1 gid start end1
      (OPEN: get_pc c start = Some (SetRegOpen gid))
      (NFA1: nfa_rep r1 c (S start) end1)
      (CLOSE: get_pc c end1 = Some (SetRegClose gid)),
      nfa_rep (Group gid r1) c start (S end1)
  | nfa_rep_anchor:
    forall c a lbl
      (CHECK: get_pc c lbl = Some (CheckAnchor a)),
      nfa_rep (Anchor a) c lbl (S lbl)
  | nfa_unsupported:
    forall c r lbl
      (UNSUPPORTED: ~ pike_regex r)
      (KILL: get_pc c lbl = Some KillThread),
      nfa_rep r c lbl (S lbl).

  (** * Compile Characterization  *)

  Lemma cons_app:
    forall A (x:A) l, x::l = [x] ++ l.
  Proof. intros. simpl. auto. Qed.

  Lemma nfa_rep_extend:
    forall r c start endl suffix,
      nfa_rep r c start endl ->
      nfa_rep r (c++suffix) start endl.
  Proof.
    intros r c start endl suffix H. generalize dependent suffix.
    induction H; intros; econstructor;
      try (erewrite get_suffix; eauto); try apply IHnfa_rep;
      try apply IHnfa_rep1; try apply IHnfa_rep2. auto.
  Qed.



  (* correctness of the returned fresh label *)
  Lemma fresh_correct:
    forall r fresh l next,
      compile r fresh = (l, next) ->
      fresh + List.length l = next.
  Proof.
    Ltac inv_comp H := inversion H; subst; simpl; lia.
    intros r.
    induction r; intros fresh l next COMPILE; try solve[inv_comp COMPILE].
    - inversion COMPILE.
      destruct (compile r1 (S fresh)) as [bc1 f1] eqn:COMP1. destruct (compile r2 (S f1)) as [bc2 f2] eqn:COMP2.
      inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2. simpl.
      rewrite <- COMP1 in COMP2. simpl in COMP2. rewrite length_app. simpl. lia.
    - inversion COMPILE.
      destruct (compile r1 fresh) as [bc1 f1] eqn:COMP1. destruct (compile r2 f1) as [bc2 f2] eqn:COMP2.
      inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2.
      rewrite <- COMP1 in COMP2. rewrite length_app. lia.
    - inversion COMPILE. destruct min.
      2: { inversion H0. simpl. lia. }
      destruct delta.
      + destruct n; try destruct n; try solve[inversion H0; simpl; lia].
        destruct (compile r (S (S (S fresh)))) as [bc1 f1] eqn:COMP1.
        inversion H0. apply IHr in COMP1.
        subst. simpl. rewrite length_app. simpl. lia.
      + destruct (compile r (S (S (S fresh)))) as [bc1 f1] eqn:COMP1.
        inversion H0. apply IHr in COMP1.
        subst. simpl. rewrite length_app. simpl. lia.
    - inversion COMPILE.
      destruct (compile r (S fresh)) as [bc1 f1] eqn:COMP1. inversion H0. apply IHr in COMP1.
      subst. simpl. rewrite length_app. simpl. lia.
  Qed.

  (* this shows that the compilation function adheres to the representation predicate *)
  Theorem compile_nfa_rep:
    forall r c start endl prev,
      compile r start = (c, endl) ->
      start = List.length prev ->
      nfa_rep r (prev ++ c) start endl.
  Proof.
    intros r. induction r; intros.
    - inversion H. subst. rewrite app_nil_r. constructor.
    - inversion H. subst. constructor. apply get_first.
    - inversion H. destruct (compile r1 (S start)) as [bc1 end1] eqn:COMP1. destruct (compile r2 (S end1)) as [bc2 end2] eqn:COMP2.
      inversion H2. subst. apply nfa_rep_disj with (end1:=end1).
      + rewrite get_first. simpl. auto.
      + apply IHr1 with (prev:=prev ++ [Fork (S (length prev)) (S end1)]) in COMP1.
        2: { rewrite length_app. simpl. lia. }
        replace (prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
          (((prev ++ [Fork (S (length prev)) (S end1)]) ++ bc1) ++ (Jmp endl :: bc2)).
        2:{ rewrite <- app_assoc. rewrite <- app_assoc. auto. }
        apply nfa_rep_extend. auto.
      + apply fresh_correct in COMP1. rewrite <- COMP1.
        replace (S (length prev) + length bc1) with (length prev + (S (length bc1))) by lia.
        rewrite get_prefix. rewrite cons_app. rewrite app_assoc. apply get_first.
      + apply IHr2 with (prev:= prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) in COMP2.
        * replace (prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
            ((prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) ++ bc2).
          2: { rewrite <- app_assoc. simpl. apply f_equal. apply f_equal. rewrite <- app_assoc. auto. }
          auto.
        * apply fresh_correct in COMP1. rewrite <- COMP1. simpl.
          rewrite length_app. simpl. rewrite length_app. simpl. lia.
    - inversion H. destruct (compile r1 start) as [bc1 end1] eqn:COMP1. destruct (compile r2 end1) as [bc2 end2] eqn:COMP2.
      inversion H2. subst. econstructor.
      + apply IHr1 with (prev:=prev) in COMP1; auto.
        rewrite app_assoc. apply nfa_rep_extend. eauto.
      + apply IHr2 with (prev:=prev ++ bc1) in COMP2; auto.
        * rewrite app_assoc. auto.
        * apply fresh_correct in COMP1. rewrite length_app. lia.
    - inversion H. destruct min.
      2: { inversion H2. subst. apply nfa_unsupported.
          - unfold not. intros. inversion H0.
          - rewrite get_first. simpl. auto. }
      destruct (destruct_delta delta) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]]; subst delta.
      (* Zero repetitions *)
      + inversion H2. subst. constructor.
      (* Question Mark *)
      + destruct (compile r (S (S (S start)))) as [bc1 end1] eqn:COMP1. inversion H2. subst. constructor.
        * rewrite get_first. simpl. auto.
        * rewrite get_second. simpl. auto.
        * rewrite get_third. simpl. auto.
        * apply IHr with (prev:=prev ++ [greedy_fork greedy (S (length prev)) (S end1); BeginLoop; ResetRegs (def_groups r)]) in COMP1.
          ** rewrite <- app_assoc in COMP1. simpl in COMP1.
             replace (prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (S end1)]) with
               ((prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (S end1)]).
             2: { rewrite <- app_assoc. auto. }
             apply nfa_rep_extend. auto.
          ** rewrite length_app. simpl. lia.
        * replace (prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (S end1)]) with
            ((prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (S end1)]).
          2: { rewrite <- app_assoc. auto. }
          apply fresh_correct in COMP1. subst. apply get_first_0.
          simpl. rewrite length_app. simpl. lia.
      (* Star *)
      + destruct (compile r (S (S (S start)))) as [bc1 end1] eqn:COMP1. inversion H2. subst. constructor.
        * rewrite get_first. simpl. auto.
        * rewrite get_second. simpl. auto.
        * rewrite get_third. simpl. auto.
        * apply IHr with (prev:=prev ++ [greedy_fork greedy (S (length prev)) (S end1); BeginLoop; ResetRegs (def_groups r)]) in COMP1.
          ** rewrite <- app_assoc in COMP1. simpl in COMP1.
             replace (prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (length prev)]) with
               ((prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (length prev)]).
             2: { rewrite <- app_assoc. auto. }
             apply nfa_rep_extend. auto.
          ** rewrite length_app. simpl. lia.
        * replace (prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (length prev)]) with
            ((prev ++ greedy_fork greedy (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (length prev)]).
          2: { rewrite <- app_assoc. auto. }
          apply fresh_correct in COMP1. subst. apply get_first_0.
          simpl. rewrite length_app. simpl. lia.
      (* Unsupported *)
      + assert (([KillThread], S start) = (c,endl)).
        { destruct delta'; auto. lia. destruct delta'; auto. lia. }
        inversion H1. subst. apply nfa_unsupported.
        * unfold not. intros. inversion H0; subst; lia.
        * rewrite get_first. simpl. auto.
    - inversion H. subst. apply nfa_unsupported.
      + unfold not. intros. inversion H0.
      + rewrite get_first. simpl. auto.
    - inversion H. destruct (compile r (S start)) as [bc1 end1] eqn:COMP1. inversion H2. subst.
      constructor.
      + rewrite get_first. simpl. auto.
      +  apply IHr with (prev:=prev ++ [SetRegOpen id]) in COMP1.
        2: { rewrite length_app. simpl. lia. }
        replace (prev ++ SetRegOpen id :: bc1 ++ [SetRegClose id]) with ((prev ++ SetRegOpen id :: bc1) ++ [SetRegClose id]).
        2:{ rewrite <- app_assoc. auto. }
        apply nfa_rep_extend. rewrite <- app_assoc in COMP1. simpl in COMP1. auto.
      + replace (prev ++ SetRegOpen id :: bc1 ++ [SetRegClose id]) with ((prev ++ SetRegOpen id :: bc1) ++ [SetRegClose id]).
        2:{ rewrite <- app_assoc. auto. }
        apply get_first_0. apply fresh_correct in COMP1. subst. rewrite length_app. simpl. lia.
    - inversion H. subst. constructor. apply get_first.
    - inversion H. subst. apply nfa_unsupported.
      + unfold not. intros. inversion H0.
      + rewrite get_first. simpl. auto.
  Qed.


  (** * Lifting the representation predicate to continuations  *)
  (* This is useful to relate the continuations used in the tree semantics to the code produced by the NFA compiler *)

  (* action_rep a c pc1 pc2 indicates that the bytecode for a is located in code c between labels pc1 and pc2  *)
  Inductive action_rep : action -> code -> label -> label -> Prop :=
  | areg_bc:
    forall r c pcstart pcend
      (NFA: nfa_rep r c pcstart pcend),
      action_rep (Areg r) c pcstart pcend
  | acheck_bc:
    forall c str pc pcnext
      (END: get_pc c pc = Some (EndLoop pcnext)),
      action_rep (Acheck str) c pc pcnext
  | aclose_bc:
    forall c gid pc
      (CLOSE: get_pc c pc = Some (SetRegClose gid)),
      action_rep (Aclose gid) c pc (S pc).

  (* continuation_rep cont c pc n means that the bytecode for cont is located in c at labels pc *)
  (* inside the representation of the continuation, there might be extra jump instructions *)
  (* this representation has to end on an accept instruction, at the end of the bytecode *)
  Inductive actions_rep : actions -> code -> label -> Prop :=
  | empty_bc:
    (* when the continuation is empty, it means we have nothing more to do and found a match *)
    (* in the bytecode, this means an accept *)
    forall c pc
      (ACCEPT: get_pc c pc = Some Accept),
      actions_rep [] c pc
  | cons_bc:
    forall a cont c pcstart pcmid
      (ACTION: action_rep a c pcstart pcmid)
      (CONT: actions_rep cont c pcmid),
      actions_rep (a::cont) c pcstart
  | jump_bc:
    forall cont c pcstart pc
      (CONT: actions_rep cont c pcstart)
      (JMP: get_pc c pc = Some (Jmp pcstart)),
      actions_rep cont c pc.

  (** * Stuttering  *)
  (* There are a few cases where the PikeVM takes more steps than the Pike Tree. *)
  (* These are stutter steps. *)
  (* They correspond to
    - being at a Jmp instruction, inserted for a disjunction
    - being at a BeginLoop instruction, inserted for a quantifier
  *)

  (* With the definitions below, we provide ways to know when a state is going to stutter *)

  (* returns true if that state will stutter *)
  (* or if we are at an unsupported feature *)
  Definition stutters (pc:label) (code:code) : bool :=
    match get_pc code pc with
    | Some (Jmp _) => true
    | Some BeginLoop => true
    | Some KillThread => true
    | _ => false
    end.

  Lemma does_stutter:
    forall pc code, stutters pc code = true ->
              get_pc code pc = Some BeginLoop \/ (exists next, get_pc code pc = Some (Jmp next)) \/ get_pc code pc = Some KillThread.
  Proof.
    unfold stutters. intros. destruct get_pc; try destruct b; inversion H; eauto.
  Qed.

  Lemma doesnt_stutter_jmp:
    forall pc code next, stutters pc code = false -> get_pc code pc = Some (Jmp next) -> False.
  Proof.
    unfold stutters, not. intros. destruct get_pc; try destruct b; inversion H0. inversion H.
  Qed.

  Lemma doesnt_stutter_begin:
    forall pc code, stutters pc code = false -> get_pc code pc = Some BeginLoop -> False.
  Proof.
    unfold stutters, not. intros. destruct get_pc; try destruct b; inversion H0. inversion H.
  Qed.

  Lemma doesnt_stutter_kill:
    forall pc code, stutters pc code = false -> get_pc code pc = Some KillThread -> False.
  Proof.
    unfold stutters, not. intros. destruct get_pc; try destruct b; inversion H0. inversion H.
  Qed.

End NFA.


Ltac no_stutter :=
  match goal with
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (Jmp _) |- _ ] => exfalso; eapply doesnt_stutter_jmp; eauto
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (BeginLoop) |- _ ] => exfalso; eapply doesnt_stutter_begin; eauto
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (KillThread) |- _ ] => exfalso; eapply doesnt_stutter_kill; eauto
  end.

Ltac stutter :=
  match goal with
  | [ H : stutters ?pc ?code = true, H1: get_pc ?code ?pc = Some _ |- _ ] =>
      try solve[unfold stutters in H; rewrite H1 in H; inversion H]
  end.

Ltac invert_rep :=
   match goal with
   | [ H : actions_rep (Areg _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep (Aclose _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep (Acheck _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep [] _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Areg _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Aclose _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Acheck _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Epsilon) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Regex.Character _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Disjunction _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Sequence _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Quantified _ _ _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Group _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Anchor _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | _ => try no_stutter
   end.
