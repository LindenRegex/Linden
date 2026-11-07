From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree.
From Linden Require Import Semantics PikeSubset.
From Linden Require Import Parameters.
From Linden Require Import PeekingAnalysis.
From Warblre Require Import Numeric.

Section NFA.
  Context {params: LindenParameters}.
  Context {rer: RegExpRecord.RegExpRecord}.
  Context {disj: Disjoint rer}.

  (** * Peeking  *)
  (* As an optimization, we allow the Fork instruction to peek at
     the surrounding characters.
     Some Forks may be annotated with peeking information, constraints on each branch.
     While this resembles the "lookahead" of parsing, this is called "peeking"
     to avoid the confusion with regex lookaheads. *)

  Inductive peek : Type :=
  (* a regular fork, always produces two threads *)
  | NoPeek
  (* A Branch can decide ahead of time which successor to consider *)
  (* If cd can be matched, then it takes the first one, otherwise the second *)
  (* The boolean argument only indicates the greediness of what generated it,
     it is unused in the execution, only helpful to keep an elegant invariant *)
  | Branch (cd:char_descr) (g:bool).

  (** * NFA Bytecode *)
  (* the bytecode generated for the PikeVM algorithm *)

  Definition label : Type := nat.
  Definition lbl_eq_dec : forall (l1 l2 : label), { l1 = l2 } + { l1 <> l2 }.
  Proof. repeat decide equality. Defined.

  Inductive bytecode: Type :=
  | Accept
  | Consume: char_descr -> bytecode
  | CheckAnchor: anchor -> bytecode
  | Jmp: label -> bytecode
  | Fork: peek -> label -> label -> bytecode
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
    | Fork _ l1 l2 => [l1; l2]
    end.

  (** * NFA Compilation  *)

  (* computes the annotation of a fork, given the result of the begins analysis *)
  Definition compute_peek (g:bool) (o1 o2: option char_descr) : peek :=
    match o1, o2 with
    | Some cd1, Some cd2 => if disjoint_checker rer cd1 cd2 then Branch cd1 g else NoPeek
    | _, _ => NoPeek
    end.

  Lemma compute_peek_cases:
    forall g o1 o2,
      compute_peek g o1 o2 = NoPeek \/
        exists cd1 cd2, o1 = Some cd1 /\ o2 = Some cd2 /\
                     disjoint_checker rer cd1 cd2 = true /\
                     compute_peek g o1 o2 = Branch cd1 g.
  Proof.
    intros g [cd1|] [cd2|]; unfold compute_peek; auto.
    destruct (disjoint_checker rer cd1 cd2) eqn:D; auto.
    right. exists cd1, cd2. auto.
  Qed.

  (* a branch must not swap out its order of labels
     because the character descriptor that we put inside it always
     refers to the first label *)
  Definition greedy_fork (greedy:bool) (p:peek) (l1 l2:label) :=
    if greedy
    then Fork p l1 l2
    else match p with
         | Branch _ _ => Fork p l1 l2
         | NoPeek => Fork p l2 l1
         end.

  (* also returns the next fresh label *)
  (* after describes what must be read after the current regex being compiled,
     in order to provide information for the peek analysis (None=unknown) *)
  Fixpoint compile (r:regex) (fresh:label) (after:option char_descr): code * label :=
    match r with
    | Epsilon => ([], fresh)
    | Character cd => ([Consume cd], S fresh)
    | Disjunction r1 r2 =>
        let (bc1, f1) := compile r1 (S fresh) after in
        let (bc2, f2) := compile r2 (S f1) after in
        let annot := compute_peek true (begins r1 after) (begins r2 after) in
        ([Fork annot (S fresh) (S f1)] ++ bc1 ++ [Jmp f2] ++ bc2, f2)
    | Sequence r1 r2 =>
        let (bc1, f1) := compile r1 fresh (begins r2 after) in
        let (bc2, f2) := compile r2 f1 after in
        (bc1 ++ bc2, f2)
    | Quantified greedy 0 (NoI.N 0) r1 => ([], fresh)
    | Quantified greedy 0 (NoI.N 1) r1 =>
        let (bc1, f1) := compile r1 (S (S (S fresh))) after in
        ([greedy_fork greedy NoPeek (S fresh) (S f1); BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop (S f1)], S f1)
    | Quantified greedy 0 (NoI.Inf) r1 =>
        let (bc1, f1) := compile r1 (S (S (S fresh))) None in
        ([greedy_fork greedy NoPeek (S fresh) (S f1); BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop fresh], S f1)
    | Quantified greedy 1 (NoI.N 0) r1 =>
        let (bc1, f1) := compile r1 (S fresh) after in
        ([ResetRegs (def_groups r1)] ++ bc1, f1)
    | Group gid r1 =>
        let (bc1, f1) := compile r1 (S fresh) after in
        ([SetRegOpen gid] ++ bc1 ++ [SetRegClose gid], S f1)
    | Anchor a => ([CheckAnchor a], S fresh)
    | _ => ([KillThread], S fresh) (* unsupported features *)
    end.

  (* adds an accept at the end of the code *)
  Definition compilation (r:regex) : code :=
    match (compile r 0 None) with
    | (c,fresh) => c ++ [Accept]
    end.

  (** * Inductive NFA characterization *)
  (* like a representation predicate *)

  (* nfa_rep r code pc1 pc2 means that the bytecode for r is represented in code, from pc1 to pc2 (excluded)  *)
  (* like in compile, after represents information about what follows the current regex *)
  Inductive nfa_rep : regex -> option char_descr -> code -> label -> label -> Prop :=
  | nfa_rep_epsilon:
    forall c after lbl,
      nfa_rep Epsilon after c lbl lbl
  | nfa_rep_char:
    forall c cd after lbl
      (CONSUME: get_pc c lbl = Some (Consume cd)),
      nfa_rep (Character cd) after c lbl (S lbl)
  | nfa_rep_disj:
    forall c r1 r2 after start end1 end2
      (FORK: get_pc c start = Some (Fork (compute_peek true (begins r1 after) (begins r2 after)) (S start) (S end1)))
      (NFA1: nfa_rep r1 after c (S start) end1)
      (JMP: get_pc c end1 = Some (Jmp end2))
      (NFA2: nfa_rep r2 after c (S end1) end2),
      nfa_rep
        (Disjunction r1 r2) after c start end2
  | nfa_rep_seq:
    forall c r1 r2 after start end1 end2
      (NFA1: nfa_rep r1 (begins r2 after) c start end1)
      (NFA2: nfa_rep r2 after c end1 end2),
      nfa_rep (Sequence r1 r2) after c start end2
  | nfa_rep_done:
    forall c r1 greedy after lbl,
      nfa_rep (Quantified greedy 0 (NoI.N 0) r1) after c lbl lbl
  | nfa_rep_qmark:
    forall c r1 greedy after start end1
      (FORK: get_pc c start = Some (greedy_fork greedy NoPeek (S start) (S end1)))
      (BEGIN: get_pc c (S start) = Some (BeginLoop))
      (RESET: get_pc c (S (S start)) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 after c (S (S (S start))) end1)
      (END: get_pc c end1 = Some (EndLoop (S end1))),
      nfa_rep (Quantified greedy 0 (NoI.N 1) r1) after c start (S end1)
  | nfa_rep_star:
    forall c r1 greedy after start end1
      (FORK: get_pc c start = Some (greedy_fork greedy NoPeek (S start) (S end1)))
      (BEGIN: get_pc c (S start) = Some (BeginLoop))
      (RESET: get_pc c (S (S start)) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 None c (S (S (S start))) end1)
      (END: get_pc c end1 = Some (EndLoop start)),
      nfa_rep (Quantified greedy 0 (NoI.Inf) r1) after c start (S end1)
  | nfa_rep_one:
    forall c r1 greedy after start end1
      (RESET: get_pc c start = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 after c (S start) end1),
      nfa_rep (Quantified greedy 1 (NoI.N 0) r1) after c start end1
  | nfa_rep_group:
    forall c r1 gid after start end1
      (OPEN: get_pc c start = Some (SetRegOpen gid))
      (NFA1: nfa_rep r1 after c (S start) end1)
      (CLOSE: get_pc c end1 = Some (SetRegClose gid)),
      nfa_rep (Group gid r1) after c start (S end1)
  | nfa_rep_anchor:
    forall c a after lbl
      (CHECK: get_pc c lbl = Some (CheckAnchor a)),
      nfa_rep (Anchor a) after c lbl (S lbl)
  | nfa_unsupported:
    forall c r after lbl
      (UNSUPPORTED: ~ pike_regex r)
      (KILL: get_pc c lbl = Some KillThread),
      nfa_rep r after c lbl (S lbl).

  (** * Compile Characterization  *)

  Lemma cons_app:
    forall A (x:A) l, x::l = [x] ++ l.
  Proof. intros. simpl. auto. Qed.

  Lemma nfa_rep_extend:
    forall r after c start endl suffix,
      nfa_rep r after c start endl ->
      nfa_rep r after (c++suffix) start endl.
  Proof.
    intros r after c start endl suffix H. generalize dependent suffix.
    induction H; intros; econstructor;
      try (erewrite get_suffix; eauto); try apply IHnfa_rep;
      try apply IHnfa_rep1; try apply IHnfa_rep2. auto.
  Qed.



  (* correctness of the returned fresh label *)
  Lemma fresh_correct:
    forall r fresh after l next,
      compile r fresh after = (l, next) ->
      fresh + List.length l = next.
  Proof.
    Ltac inv_comp H := inversion H; subst; simpl; lia.
    intros r.
    induction r; intros fresh after l next COMPILE; try solve[inv_comp COMPILE].
    - inversion COMPILE.
      destruct (compile r1 (S fresh) after) as [bc1 f1] eqn:COMP1. destruct (compile r2 (S f1) after) as [bc2 f2] eqn:COMP2.
      inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2. simpl.
      rewrite <- COMP1 in COMP2. simpl in COMP2. rewrite length_app. simpl. lia.
    - inversion COMPILE.
      destruct (compile r1 fresh (begins r2 after)) as [bc1 f1] eqn:COMP1. destruct (compile r2 f1 after) as [bc2 f2] eqn:COMP2.
      inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2.
      rewrite <- COMP1 in COMP2. rewrite length_app. lia.
    - inversion COMPILE. destruct min.
      2: { destruct min; [destruct delta as [[|]|]|]; try solve[inversion H0; simpl; lia].
           destruct (compile r (S fresh) after) as [bc1 f1] eqn:COMP1.
           inversion H0. apply IHr in COMP1. subst. simpl. lia. }
      destruct delta.
      + destruct n; try destruct n; try solve[inversion H0; simpl; lia].
        destruct (compile r (S (S (S fresh))) after) as [bc1 f1] eqn:COMP1.
        inversion H0. apply IHr in COMP1.
        subst. simpl. rewrite length_app. simpl. lia.
      + destruct (compile r (S (S (S fresh))) None) as [bc1 f1] eqn:COMP1.
        inversion H0. apply IHr in COMP1.
        subst. simpl. rewrite length_app. simpl. lia.
    - inversion COMPILE.
      destruct (compile r (S fresh) after) as [bc1 f1] eqn:COMP1. inversion H0. apply IHr in COMP1.
      subst. simpl. rewrite length_app. simpl. lia.
  Qed.

  (* this shows that the compilation function adheres to the representation predicate *)
  Theorem compile_nfa_rep:
    forall r after c start endl prev,
      compile r start after = (c, endl) ->
      start = List.length prev ->
      nfa_rep r after (prev ++ c) start endl.
  Proof.
    intros r. induction r; intros.
    - inversion H. subst. rewrite app_nil_r. constructor.
    - inversion H. subst. constructor. apply get_first.
    - inversion H. destruct (compile r1 (S start) after) as [bc1 end1] eqn:COMP1. destruct (compile r2 (S end1) after) as [bc2 end2] eqn:COMP2.
      inversion H2. subst. apply nfa_rep_disj with (end1:=end1).
      + rewrite get_first. simpl. auto.
      + apply IHr1 with (prev:=prev ++ [Fork (compute_peek true (begins r1 after) (begins r2 after)) (S (length prev)) (S end1)]) in COMP1.
        2: { rewrite length_app. simpl. lia. }
        replace (prev ++ Fork (compute_peek true (begins r1 after) (begins r2 after)) (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
          (((prev ++ [Fork (compute_peek true (begins r1 after) (begins r2 after)) (S (length prev)) (S end1)]) ++ bc1) ++ (Jmp endl :: bc2)).
        2:{ rewrite <- app_assoc. rewrite <- app_assoc. auto. }
        apply nfa_rep_extend. auto.
      + apply fresh_correct in COMP1. rewrite <- COMP1.
        replace (S (length prev) + length bc1) with (length prev + (S (length bc1))) by lia.
        rewrite get_prefix. rewrite cons_app. rewrite app_assoc. apply get_first.
      + apply IHr2 with (prev:= prev ++ Fork (compute_peek true (begins r1 after) (begins r2 after)) (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) in COMP2.
        * replace (prev ++ Fork (compute_peek true (begins r1 after) (begins r2 after)) (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
            ((prev ++ Fork (compute_peek true (begins r1 after) (begins r2 after)) (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) ++ bc2).
          2: { rewrite <- app_assoc. simpl. apply f_equal. apply f_equal. rewrite <- app_assoc. auto. }
          auto.
        * apply fresh_correct in COMP1. rewrite <- COMP1. simpl.
          rewrite length_app. simpl. rewrite length_app. simpl. lia.
    - inversion H. destruct (compile r1 start (begins r2 after)) as [bc1 end1] eqn:COMP1. destruct (compile r2 end1 after) as [bc2 end2] eqn:COMP2.
      inversion H2. subst. econstructor.
      + apply IHr1 with (prev:=prev) in COMP1; auto.
        rewrite app_assoc. apply nfa_rep_extend. eauto.
      + apply IHr2 with (prev:=prev ++ bc1) in COMP2; auto.
        * rewrite app_assoc. auto.
        * apply fresh_correct in COMP1. rewrite length_app. lia.
    - inversion H. destruct min.
      2: { destruct min; [destruct delta as [[|]|]|].
           (* unique iteration {1} *)
           1: { destruct (compile r (S start) after) as [bc1 end1] eqn:COMP1. inversion H2. subst.
                apply nfa_rep_one.
                - rewrite get_first. auto.
                - apply IHr with (prev:=prev ++ [ResetRegs (def_groups r)]) in COMP1.
                  + rewrite <- app_assoc in COMP1. auto.
                  + rewrite length_app. simpl. lia. }
           (* other quantifiers unsupported *)
           all: inversion H2; subst; apply nfa_unsupported;
             [ unfold not; intros; inversion H0 | rewrite get_first; auto ]. }
      destruct (destruct_delta delta) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]]; subst delta.
      (* Zero repetitions *)
      + inversion H2. subst. constructor.
      (* Question Mark *)
      + destruct (compile r (S (S (S start))) after) as [bc1 end1] eqn:COMP1. inversion H2. subst. constructor.
        * rewrite get_first. simpl. auto.
        * rewrite get_second. simpl. auto.
        * rewrite get_third. simpl. auto.
        * apply IHr with (prev:=prev ++ [greedy_fork greedy NoPeek (S (length prev)) (S end1); BeginLoop; ResetRegs (def_groups r)]) in COMP1.
          ** rewrite <- app_assoc in COMP1. simpl in COMP1.
             replace (prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (S end1)]) with
               ((prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (S end1)]).
             2: { rewrite <- app_assoc. auto. }
             apply nfa_rep_extend. auto.
          ** rewrite length_app. simpl. lia.
        * replace (prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (S end1)]) with
            ((prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (S end1)]).
          2: { rewrite <- app_assoc. auto. }
          apply fresh_correct in COMP1. subst. apply get_first_0.
          simpl. rewrite length_app. simpl. lia.
      (* Star *)
      + destruct (compile r (S (S (S start))) None) as [bc1 end1] eqn:COMP1. inversion H2. subst. constructor.
        * rewrite get_first. simpl. auto.
        * rewrite get_second. simpl. auto.
        * rewrite get_third. simpl. auto.
        * apply IHr with (prev:=prev ++ [greedy_fork greedy NoPeek (S (length prev)) (S end1); BeginLoop; ResetRegs (def_groups r)]) in COMP1.
          ** rewrite <- app_assoc in COMP1. simpl in COMP1.
             replace (prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (length prev)]) with
               ((prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (length prev)]).
             2: { rewrite <- app_assoc. auto. }
             apply nfa_rep_extend. auto.
          ** rewrite length_app. simpl. lia.
        * replace (prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1 ++ [EndLoop (length prev)]) with
            ((prev ++ greedy_fork greedy NoPeek (S (length prev)) (S end1) :: BeginLoop :: ResetRegs (def_groups r) :: bc1) ++ [EndLoop (length prev)]).
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
    - inversion H. destruct (compile r (S start) after) as [bc1 end1] eqn:COMP1. inversion H2. subst.
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

  (* action_rep a after c pc1 pc2 indicates that the bytecode for a, with information after,
     is located in code c between labels pc1 and pc2  *)
  Inductive action_rep : action -> option char_descr -> code -> label -> label -> Prop :=
  | areg_bc:
    forall r after c pcstart pcend
      (NFA: nfa_rep r after c pcstart pcend),
      action_rep (Areg r) after c pcstart pcend
  | acheck_bc:
    forall c str after pc pcnext
      (END: get_pc c pc = Some (EndLoop pcnext)),
      action_rep (Acheck str) after c pc pcnext
  | aclose_bc:
    forall c gid after pc
      (CLOSE: get_pc c pc = Some (SetRegClose gid)),
      action_rep (Aclose gid) after c pc (S pc).

  (* As an invariant of actions_rep, we show that
     the after information correctly describes the analysis of the continuation *)
  Definition after_ok (after:option char_descr) (cont:actions) : Prop :=
    after = None \/ after = begins_actions cont.

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
    forall a after cont c pcstart pcmid
      (ACTION: action_rep a after c pcstart pcmid)
      (AFTER: after_ok after cont)
      (CONT: actions_rep cont c pcmid),
      actions_rep (a::cont) c pcstart
  | jump_bc:
    forall cont c pcstart pc
      (CONT: actions_rep cont c pcstart)
      (JMP: get_pc c pc = Some (Jmp pcstart)),
      actions_rep cont c pc.

  (** * After analysis invariant preservation  *)

  Lemma after_ok_none:
    forall cont, after_ok None cont.
  Proof. left. auto. Qed.

  Lemma after_ok_seq:
    forall after r cont,
      after_ok after cont ->
      after_ok (begins r after) (Areg r :: cont).
  Proof.
    intros after r cont [N|E]; subst; simpl.
    - destruct (begins r None) eqn:B; [right|left]; auto.
      symmetry. apply begins_none. auto.
    - right. auto.
  Qed.

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

(* proves that the analysis information correctly describes the continuation *)
Ltac solve_after_ok :=
  match goal with
  | [ |- after_ok _ _ ] =>
      first [assumption | apply after_ok_none | apply after_ok_seq; assumption]
  end.

Ltac prove_actions_rep := repeat (first [solve_after_ok | econstructor]; eauto).

Ltac invert_rep :=
   match goal with
   | [ H : actions_rep (Areg _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep (Aclose _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep (Acheck _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep [] _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Areg _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Aclose _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Acheck _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Epsilon) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Regex.Character _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Disjunction _ _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Sequence _ _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Quantified _ _ _ _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Group _ _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Anchor _) _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | _ => try no_stutter
   end.
