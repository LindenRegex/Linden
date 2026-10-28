From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree.
From Linden Require Import Semantics PikeSubset.
From Linden Require Import Parameters.
From Warblre Require Import Base Numeric RegExpRecord.

Section NFA.
  Context {params: LindenParameters}.

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
  | Fork: label -> label -> bytecode
  | ForkLazy: label -> label -> bytecode (* runs the second label first *)
  | SetRegOpen: group_id -> bytecode
  | SetRegClose: group_id -> bytecode
  | ResetRegs: list group_id -> bytecode
  | BeginLoop: bytecode
  | EndLoop: label -> bytecode    (* also contains the backedge instead of adding a jump *)
  | KillThread: bytecode         (* for unsupported features *)
  (* Peek without consuming: matching descriptor selects the first target;
     a mismatch (including end of input) selects the second. *)
  | Branch: char_descr -> label -> label -> bytecode
  (* Loop entry that peeks without consuming: the body (first label) is only
     entered when the descriptor matches; the exit (second label) is always
     kept, after the body for [LoopBranch] and before it for [LoopBranchLazy]. *)
  | LoopBranch: char_descr -> label -> label -> bytecode
  | LoopBranchLazy: char_descr -> label -> label -> bytecode
  (* The descriptor of the branching instruction just before; never executed. *)
  | Data: char_descr -> bytecode
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
    | Accept | KillThread | Data _ => []
    | Jmp l | EndLoop l => [l]
    | Fork l1 l2 | ForkLazy l1 l2 | Branch _ l1 l2 | LoopBranch _ l1 l2 | LoopBranchLazy _ l1 l2 => [l1; l2]
    end.

  (* the compiler places the first label of every forking instruction right after it,
     past the descriptor cell of a branching instruction *)
  Definition next_first (c:code) (pc:label) (b:bytecode) : Prop :=
    match b with
    | Fork l _ | ForkLazy l _ => l = S pc
    | Branch cd l _ | LoopBranch cd l _ | LoopBranchLazy cd l _ =>
        l = S (S pc) /\ get_pc c (S pc) = Some (Data cd)
    | _ => True
    end.

  (** * NFA Compilation  *)

  Definition greedy_fork (greedy:bool) (l1 l2:label) :=
    if greedy
    then Fork l1 l2
    else ForkLazy l1 l2.

  (** [branches] enables [Branch] and [LoopBranch]: a disjunction whose
      alternatives must start with distinct characters, or a loop whose body
      must start with a known character, peeks at the input instead of forking. *)
  Context (rer: RegExpRecord) (branches: bool).

  (* Only a mandatory leading character qualifies. We deliberately do not look
     through nullable prefixes, alternations or quantifiers. *)
  Fixpoint lead_descr (r: regex) : option char_descr :=
    match r with
    | Regex.Character cd => Some cd
    | Sequence r1 _ => lead_descr r1
    | Group _ r1 => lead_descr r1
    | _ => None
    end.

  (* the first of two leading descriptors, if they are distinct characters *)
  Definition distinct_peek (d1 d2: option char_descr) : option char_descr :=
    match branches, d1, d2 with
    | true, Some (CdSingle c1), Some (CdSingle c2) =>
        if Character.canonicalize rer c1 == Character.canonicalize rer c2
        then None else Some (CdSingle c1)
    | _, _, _ => None
    end.

  (* the descriptor a disjunction peeks at, if it branches *)
  Definition disjunction_peek (r1 r2: regex) : option char_descr :=
    distinct_peek (lead_descr r1) (lead_descr r2).

  Definition disjunction_fork (r1 r2: regex) (l1 l2: label) : bytecode :=
    match disjunction_peek r1 r2 with
    | Some cd => Branch cd l1 l2
    | None => Fork l1 l2
    end.

  (* the descriptor a loop peeks at, if it branches *)
  Definition loop_peek (r1: regex) : option char_descr :=
    if branches then lead_descr r1 else None.

  (* [fl] is the descriptor that whatever follows the loop must start with:
     a loop whose body and continuation start differently needs no fork *)
  Definition loop_fork (greedy: bool) (r1: regex) (fl: option char_descr) (body exit: label) : bytecode :=
    match loop_peek r1, distinct_peek (loop_peek r1) fl, greedy with
    | Some cd, Some _, _ => Branch cd body exit
    | Some cd, None, true => LoopBranch cd body exit
    | Some cd, None, false => LoopBranchLazy cd body exit
    | None, _, _ => greedy_fork greedy body exit
    end.

  (* a branching instruction keeps its descriptor in the next cell *)
  Definition pad (peek: option char_descr) : code :=
    match peek with Some cd => [Data cd] | None => [] end.
  Definition gap (peek: option char_descr) : nat := length (pad peek).

  (* [fl] describes what follows [r]; also returns the next fresh label *)
  Fixpoint compile (r:regex) (fl: option char_descr) (fresh:label) : code * label :=
    match r with
    | Epsilon => ([], fresh)
    | Regex.Character cd => ([Consume cd], S fresh)
    | Disjunction r1 r2 =>
        let peek := disjunction_peek r1 r2 in
        let (bc1, f1) := compile r1 fl (S (gap peek + fresh)) in
        let (bc2, f2) := compile r2 fl (S f1) in
        ([disjunction_fork r1 r2 (S (gap peek + fresh)) (S f1)] ++ pad peek ++ bc1 ++ [Jmp f2] ++ bc2, f2)
    | Sequence r1 r2 =>
        let (bc1, f1) := compile r1 (lead_descr r2) fresh in
        let (bc2, f2) := compile r2 fl f1 in
        (bc1 ++ bc2, f2)
    | Quantified greedy 0 (NoI.N 0) r1 => ([], fresh)
    | Quantified greedy 0 (NoI.N 1) r1 =>
        let peek := loop_peek r1 in
        let (bc1, f1) := compile r1 None (S (S (S (gap peek + fresh)))) in
        ([loop_fork greedy r1 fl (S (gap peek + fresh)) (S f1)] ++ pad peek ++
         [BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop (S f1)], S f1)
    | Quantified greedy 0 (NoI.Inf) r1 =>
        let peek := loop_peek r1 in
        let (bc1, f1) := compile r1 None (S (S (S (gap peek + fresh)))) in
        ([loop_fork greedy r1 fl (S (gap peek + fresh)) (S f1)] ++ pad peek ++
         [BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop fresh], S f1)
    | Group gid r1 =>
        let (bc1, f1) := compile r1 fl (S fresh) in
        ([SetRegOpen gid] ++ bc1 ++ [SetRegClose gid], S f1)
    | Anchor a => ([CheckAnchor a], S fresh)
    | _ => ([KillThread], S fresh) (* unsupported features *)
    end.

  (* adds an accept at the end of the code *)
  Definition compilation (r:regex) : code :=
    match (compile r None 0) with
    | (c,fresh) => c ++ [Accept]
    end.

  (* [leads c pc cd]: every thread at [pc] reads [cd] before anything else *)
  Inductive leads (c: code) : label -> char_descr -> Prop :=
  | leads_consume: forall pc cd, get_pc c pc = Some (Consume cd) -> leads c pc cd
  | leads_jmp: forall pc l cd, get_pc c pc = Some (Jmp l) -> leads c l cd -> leads c pc cd
  | leads_open: forall pc g cd, get_pc c pc = Some (SetRegOpen g) -> leads c (S pc) cd -> leads c pc cd
  | leads_close: forall pc g cd, get_pc c pc = Some (SetRegClose g) -> leads c (S pc) cd -> leads c pc cd.

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
      nfa_rep (Regex.Character cd) c lbl (S lbl)
  | nfa_rep_disj:
    forall c r1 r2 start end1 end2
      (FORK: get_pc c start = Some (disjunction_fork r1 r2 (S (gap (disjunction_peek r1 r2) + start)) (S end1)))
      (PAD: forall cd, disjunction_peek r1 r2 = Some cd -> get_pc c (S start) = Some (Data cd))
      (NFA1: nfa_rep r1 c (S (gap (disjunction_peek r1 r2) + start)) end1)
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
    forall c r1 greedy fl start end1
      (FORK: get_pc c start = Some (loop_fork greedy r1 fl (S (gap (loop_peek r1) + start)) (S end1)))
      (FOLLOW: forall cd, fl = Some cd -> leads c (S end1) cd)
      (PAD: forall cd, loop_peek r1 = Some cd -> get_pc c (S start) = Some (Data cd))
      (BEGIN: get_pc c (S (gap (loop_peek r1) + start)) = Some (BeginLoop))
      (RESET: get_pc c (S (S (gap (loop_peek r1) + start))) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S (gap (loop_peek r1) + start)))) end1)
      (END: get_pc c end1 = Some (EndLoop (S end1))),
      nfa_rep (Quantified greedy 0 (NoI.N 1) r1) c start (S end1)
  | nfa_rep_star:
    forall c r1 greedy fl start end1
      (FORK: get_pc c start = Some (loop_fork greedy r1 fl (S (gap (loop_peek r1) + start)) (S end1)))
      (FOLLOW: forall cd, fl = Some cd -> leads c (S end1) cd)
      (PAD: forall cd, loop_peek r1 = Some cd -> get_pc c (S start) = Some (Data cd))
      (BEGIN: get_pc c (S (gap (loop_peek r1) + start)) = Some (BeginLoop))
      (RESET: get_pc c (S (S (gap (loop_peek r1) + start))) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S (gap (loop_peek r1) + start)))) end1)
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

  Lemma leads_extend:
    forall c pc cd suffix, leads c pc cd -> leads (c ++ suffix) pc cd.
  Proof.
    induction 1; [eapply leads_consume|eapply leads_jmp|eapply leads_open|eapply leads_close];
      eauto using get_suffix.
  Qed.

  Lemma nfa_rep_extend:
    forall r c start endl suffix,
      nfa_rep r c start endl ->
      nfa_rep r (c++suffix) start endl.
  Proof.
    intros r c start endl suffix H. generalize dependent suffix.
    induction H; intros; econstructor;
      try solve [erewrite get_suffix; eauto]; try solve [intros; erewrite get_suffix; eauto];
      try solve [eauto using leads_extend];
      try apply IHnfa_rep; try apply IHnfa_rep1; try apply IHnfa_rep2.
  Qed.



  (* correctness of the returned fresh label *)
  Lemma fresh_correct:
    forall r fl fresh l next,
      compile r fl fresh = (l, next) ->
      fresh + List.length l = next.
  Proof.
    intros r. induction r; intros fl fresh l next COMPILE; cbn [compile] in COMPILE;
      repeat match type of COMPILE with
      | context [match ?x with _ => _ end] => lazymatch x with compile _ _ _ => fail | _ => destruct x end
      | context [compile ?r' ?fl ?f] => let C := fresh "C" in
          destruct (compile r' fl f) eqn:C; first [apply IHr1 in C | apply IHr2 in C | apply IHr in C]
      end;
      inversion COMPILE; subst; unfold gap; simpl; repeat (rewrite length_app; simpl); lia.
  Qed.

  Lemma nfa_rep_list:
    forall r c1 c2 start endl, c1 = c2 -> nfa_rep r c2 start endl -> nfa_rep r c1 start endl.
  Proof. intros; subst; auto. Qed.

  Lemma leads_list:
    forall c1 c2 pc cd, leads c2 pc cd -> c1 = c2 -> leads c1 pc cd.
  Proof. intros; subst; auto. Qed.

  Lemma get_at:
    forall pre x suf n, n = length pre -> get_pc (pre ++ x :: suf) n = Some x.
  Proof. intros; subst; rewrite get_first; reflexivity. Qed.

  Ltac list_eq := simpl; rewrite <- ?app_assoc; simpl; rewrite <- ?app_assoc; reflexivity.

  (* rewrite the code in the goal as [pre ++ x :: _] and read x at [length pre] *)
  Ltac get_at_with pre :=
    match goal with |- get_pc ?c _ = Some ?x =>
      let E := fresh in
      assert (E: exists suf, c = pre ++ x :: suf) by (eexists; list_eq);
      destruct E as [? ->]; apply get_at
    end.

  (* compiled code starts by reading the mandatory first character *)
  Lemma compile_leads:
    forall r fl c start endl prev suffix cd,
      compile r fl start = (c, endl) -> start = List.length prev -> lead_descr r = Some cd ->
      leads (prev ++ c ++ suffix) start cd.
  Proof.
    induction r; intros * COMP START LEAD; cbn [compile lead_descr] in *; try discriminate.
    - injection LEAD as <-. injection COMP as <- <-. apply leads_consume. get_at_with prev; auto.
    - destruct (compile r1 _ _) as [bc1 f1] eqn:C1, (compile r2 _ _) as [bc2 f2]. injection COMP as <- <-.
      rewrite <- app_assoc. eapply IHr1; eauto.
    - destruct (compile r _ _) as [bc1 f1] eqn:C1. injection COMP as <- <-.
      eapply leads_open; [get_at_with prev; auto|].
      eapply leads_list; [eapply IHr with (prev := prev ++ [SetRegOpen id]); eauto|list_eq].
      rewrite length_app; simpl; lia.
  Qed.

  (* this shows that the compilation function adheres to the representation predicate *)
  Theorem compile_nfa_rep_suffix:
    forall r fl c start endl prev suffix,
      compile r fl start = (c, endl) ->
      start = List.length prev ->
      (forall cd, fl = Some cd -> leads (prev ++ c ++ suffix) endl cd) ->
      nfa_rep r (prev ++ c ++ suffix) start endl.
  Proof.
    intros r. induction r; intros fl c start endl prev suffix H START FOLLOW; cbn [compile] in H.
    - inversion H. subst. constructor.
    - inversion H. subst. constructor. get_at_with prev; auto.
    - destruct (compile r1 _ _) as [bc1 end1] eqn:COMP1.
      destruct (compile r2 _ (S end1)) as [bc2 end2] eqn:COMP2.
      injection H as <- <-. apply fresh_correct in COMP1 as LEN1. subst start.
      set (p := disjunction_peek r1 r2) in *.
      set (df := disjunction_fork r1 r2 (S (gap p + length prev)) (S end1)).
      apply nfa_rep_disj with (end1:=end1).
      + get_at_with prev; auto.
      + intros cd P. subst p. rewrite P in *. get_at_with (prev ++ [df]).
        rewrite length_app. simpl. lia.
      + eapply nfa_rep_list;
          [|apply IHr1 with (fl := fl) (prev := prev ++ [df] ++ pad p) (suffix := Jmp end2 :: bc2 ++ suffix);
            [exact COMP1|subst p; rewrite !length_app; unfold gap; simpl; lia|]].
        * list_eq.
        * intros cd F. eapply leads_list; [eapply leads_jmp; [|apply FOLLOW, F]|list_eq].
          get_at_with (prev ++ [df] ++ pad p ++ bc1). rewrite !length_app. unfold gap in *. simpl. lia.
      + get_at_with (prev ++ [df] ++ pad p ++ bc1). rewrite !length_app. unfold gap in *. simpl. lia.
      + eapply nfa_rep_list;
          [|apply IHr2 with (fl := fl) (prev := prev ++ [df] ++ pad p ++ bc1 ++ [Jmp end2]) (suffix := suffix);
            [exact COMP2|subst p; rewrite !length_app; unfold gap in *; simpl; lia|]].
        * list_eq.
        * intros cd F. eapply leads_list; [apply FOLLOW, F|list_eq].
    - destruct (compile r1 _ start) as [bc1 end1] eqn:COMP1. destruct (compile r2 _ end1) as [bc2 end2] eqn:COMP2.
      inversion H. subst. apply fresh_correct in COMP1 as LEN1. econstructor.
      + eapply nfa_rep_list;
          [|apply IHr1 with (fl := lead_descr r2) (prev:=prev) (suffix := bc2 ++ suffix); [exact COMP1|auto|]].
        * list_eq.
        * intros cd F. rewrite app_assoc. eapply compile_leads; eauto. rewrite length_app. lia.
      + eapply nfa_rep_list;
          [|apply IHr2 with (fl := fl) (prev:=prev ++ bc1) (suffix := suffix); [exact COMP2|rewrite length_app; lia|]].
        * list_eq.
        * intros cd F. eapply leads_list; [apply FOLLOW, F|list_eq].
    - destruct min.
      2: { inversion H. subst. apply nfa_unsupported.
          - unfold not. intros. inversion H0.
          - get_at_with prev; auto. }
      destruct (destruct_delta delta) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]]; subst delta.
      (* Zero repetitions *)
      1: (inversion H; subst; constructor).
      (* Unsupported *)
      3: { assert (([KillThread], S start) = (c,endl)).
        { destruct delta'; auto. lia. destruct delta'; auto. lia. }
        inversion H0. subst. apply nfa_unsupported.
        * unfold not. intros. inversion H1; subst; lia.
        * get_at_with prev; auto. }
      (* Question Mark and Star *)
      all: destruct (compile r _ _) as [bc1 end1] eqn:COMP1; injection H as <- <-; subst start;
        apply fresh_correct in COMP1 as LEN1;
        set (lf := loop_fork greedy r fl (S (gap (loop_peek r) + length prev)) (S end1)) in *;
        econstructor.
      all: try (get_at_with prev; reflexivity).
      all: try exact FOLLOW.
      all: try (intros cd P; rewrite P in *; get_at_with (prev ++ [lf]);
          rewrite length_app; simpl; lia).
      all: try (get_at_with (prev ++ [lf] ++ pad (loop_peek r)); rewrite !length_app; unfold gap; simpl; lia).
      all: try (get_at_with (prev ++ [lf] ++ pad (loop_peek r) ++ [BeginLoop]); rewrite !length_app; unfold gap; simpl; lia).
      all: try (match goal with |- context[_ ++ [EndLoop ?e]] =>
          eapply nfa_rep_list;
            [|apply IHr with (fl := None) (prev := prev ++ [lf] ++ pad (loop_peek r) ++ [BeginLoop; ResetRegs (def_groups r)])
                (suffix := [EndLoop e] ++ suffix);
              [exact COMP1|rewrite !length_app; unfold gap; simpl; lia|discriminate]];
          list_eq end).
      all: try (get_at_with (prev ++ [lf] ++ pad (loop_peek r) ++ [BeginLoop; ResetRegs (def_groups r)] ++ bc1);
          rewrite !length_app; unfold gap in *; simpl; lia).
    - inversion H. subst. apply nfa_unsupported.
      + unfold not. intros. inversion H0.
      + get_at_with prev; auto.
    - destruct (compile r _ (S start)) as [bc1 end1] eqn:COMP1. inversion H. subst.
      apply fresh_correct in COMP1 as LEN1. constructor.
      + get_at_with prev; auto.
      + eapply nfa_rep_list; [|apply IHr with (fl := fl) (prev:=prev ++ [SetRegOpen id]) (suffix := SetRegClose id :: suffix);
          [exact COMP1|rewrite length_app; simpl; lia|]].
        * list_eq.
        * intros cd F. eapply leads_list; [eapply leads_close; [|apply FOLLOW, F]|list_eq].
          get_at_with (prev ++ [SetRegOpen id] ++ bc1). rewrite !length_app. simpl. lia.
      + get_at_with (prev ++ [SetRegOpen id] ++ bc1). rewrite !length_app. simpl. lia.
    - inversion H. subst. constructor. get_at_with prev; auto.
    - inversion H. subst. apply nfa_unsupported.
      + unfold not. intros. inversion H0.
      + get_at_with prev; auto.
  Qed.

  Theorem compile_nfa_rep:
    forall r c start endl prev,
      compile r None start = (c, endl) ->
      start = List.length prev ->
      nfa_rep r (prev ++ c) start endl.
  Proof.
    intros. rewrite <- (app_nil_r c). apply compile_nfa_rep_suffix with (fl := None); auto. discriminate.
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

  Lemma loop_fork_cases:
    forall greedy r1 fl l1 l2,
      loop_fork greedy r1 fl l1 l2 = greedy_fork greedy l1 l2 \/
      exists cd, lead_descr r1 = Some cd /\
        (loop_fork greedy r1 fl l1 l2 = (if greedy then LoopBranch cd l1 l2 else LoopBranchLazy cd l1 l2) \/
         distinct_peek (lead_descr r1) fl = Some cd /\
         loop_fork greedy r1 fl l1 l2 = Branch cd l1 l2).
  Proof.
    intros. unfold loop_fork, loop_peek, distinct_peek.
    destruct branches, (lead_descr r1) as [[]|], fl as [[]|], greedy; try destruct (_ == _); eauto 7.
  Qed.

  Lemma disjunction_fork_next:
    forall r1 r2 l1 l2 pc, next_pcs pc (disjunction_fork r1 r2 l1 l2) = [l1; l2].
  Proof. intros. unfold disjunction_fork. destruct disjunction_peek; auto. Qed.

  Lemma loop_fork_next:
    forall greedy r1 fl l1 l2 pc, next_pcs pc (loop_fork greedy r1 fl l1 l2) = [l1; l2].
  Proof.
    intros. destruct (loop_fork_cases greedy r1 fl l1 l2) as [->|[? [_ [->|[_ ->]]]]]; destruct greedy; auto.
  Qed.

  Lemma disjunction_fork_no_stutter:
    forall r1 r2 l1 l2 pc code,
      get_pc code pc = Some (disjunction_fork r1 r2 l1 l2) -> stutters pc code = false.
  Proof.
    intros. unfold stutters. rewrite H. unfold disjunction_fork. destruct disjunction_peek; auto.
  Qed.

  Lemma loop_fork_no_stutter:
    forall greedy r1 fl l1 l2 pc code,
      get_pc code pc = Some (loop_fork greedy r1 fl l1 l2) -> stutters pc code = false.
  Proof.
    intros. unfold stutters. rewrite H. unfold loop_fork, greedy_fork.
    destruct loop_peek, greedy; try destruct distinct_peek; auto.
  Qed.

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
  | [ H : stutters ?pc ?code = true, H1: get_pc ?code ?pc = Some (disjunction_fork _ _ _ _ _ _) |- _ ] =>
      rewrite (disjunction_fork_no_stutter _ _ _ _ _ _ _ _ H1) in H; discriminate
  | [ H : stutters ?pc ?code = true, H1: get_pc ?code ?pc = Some (loop_fork _ _ _ _ _ _ _) |- _ ] =>
      rewrite (loop_fork_no_stutter _ _ _ _ _ _ _ _ _ H1) in H; discriminate
  | [ H : stutters ?pc ?code = true, H1: get_pc ?code ?pc = Some _ |- _ ] =>
      try solve[unfold stutters in H; rewrite H1 in H; inversion H]
  end.

Ltac locate_pc pc GET :=
  try match goal with PAD: forall cd, ?p = Some cd -> get_pc _ _ = Some (Data cd) |- _ =>
    remember p as pk eqn:P; destruct pk; [pose proof (PAD _ eq_refl) as DATA|]; cbn [gap pad length Nat.add] in *
  end;
  repeat match goal with
  | H : get_pc ?cc ?l = Some ?j, G : get_pc ?cc pc = Some _ |- _ =>
      assert (pc = l \/ pc <> l) as [->|] by lia;
      [rewrite H in GET; injection GET as <-; clear H|clear H]
  end.

Ltac invert_rep :=
   match goal with
   | [ H : actions_rep _ _ (Areg _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep _ _ (Aclose _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep _ _ (Acheck _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep _ _ [] _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep _ _ (Areg _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep _ _ (Aclose _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep _ _ (Acheck _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Epsilon) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Regex.Character _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Disjunction _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Sequence _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Quantified _ _ _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Group _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Anchor _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | _ => try no_stutter
   end.
