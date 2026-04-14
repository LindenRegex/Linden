From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups StrictSuffix.
From Linden Require Import Tree.
From Linden Require Import Semantics PikeSubset BooleanSemantics.
From Linden Require Import Parameters.
From Warblre Require Import Base RegExpRecord Numeric.

Section NFA.
  Context {params: LindenParameters}.
  Context (rer : RegExpRecord).

  Definition nfa_oracle := input -> bool.
  Definition nfa_oracles := list nfa_oracle.
  Definition nfa_oracle_idx := nat.


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
  | SetRegOpen: group_id -> bytecode
  | SetRegClose: group_id -> bytecode
  | ResetRegs: list group_id -> bytecode
  | BeginLoop: bytecode
  | EndLoop: label -> bytecode    (* also contains the backedge instead of adding a jump *)
  | OracleQuery: nfa_oracle_idx -> lookaround -> regex -> bytecode
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

  Lemma get_nil :
    forall pc i,
      get_pc [] pc <> Some i.
  Proof. destruct pc; easy. Qed.

  Lemma get_single :
    forall pc i1 i2,
      get_pc [i1] pc = Some i2 ->
      i1 = i2 /\ pc = 0.
  Proof.
    intros. destruct pc; simpl in H.
    - split; congruence.
    - now eapply get_nil in H.
  Qed.

  Lemma get_app :
    forall pc i c1 c2,
      get_pc (c1 ++ c2) pc = Some i ->
      get_pc c1 pc = Some i \/ get_pc c2 (pc - length c1) = Some i.
  Proof.
    unfold get_pc.
    intros.
    destruct (Nat.ltb pc (length c1)) as [|] eqn:Hpc.
    - left.
      rewrite PeanoNat.Nat.ltb_lt in Hpc.
      erewrite <-nth_error_app1; eauto.
    - right.
      rewrite PeanoNat.Nat.ltb_ge in Hpc.
      erewrite <-nth_error_app2; eauto.
  Qed.

  Lemma get_cons :
    forall pc i i' c,
      get_pc (i' :: c) pc = Some i ->
      i' = i \/ get_pc c (pc - 1) = Some i.
  Proof.
    intros. destruct pc; simpl in H |- *.
    - left. congruence.
    - right. now rewrite PeanoNat.Nat.sub_0_r.
  Qed.

  Ltac get_pc :=
    match goal with
    | |- get_pc (?prev ++ ?c) ?pc = Some ?i =>
      (eapply get_first || eapply get_second || eapply get_third); eauto
    | [H: get_pc [] ?pc = Some ?i |- _] =>
      exfalso;
      eapply get_nil; eauto
    | [H: get_pc [?i1] ?pc = Some ?i2 |- _] =>
      eapply get_single in H as [?H1 ?H2];
      subst;
      inversion H1; try congruence || eauto
    | [H: get_pc (?i' :: ?c) ?pc = Some ?i |- _] =>
      eapply get_cons in H as [H|H]; try get_pc || congruence || eauto
    | [H: get_pc (?c1 ++ ?c2) ?pc = Some ?i |- _] =>
      eapply get_app in H as [H|H]; try get_pc || congruence || eauto
    end.

  Definition next_pcs (pc:label) (b:bytecode) : list label :=
    match b with
    | Consume _ | CheckAnchor _ | SetRegOpen _ | SetRegClose _
      | ResetRegs _ | BeginLoop | OracleQuery _ _ _ => [S pc]
    | Accept | KillThread => []
    | Jmp l | EndLoop l => [l]
    | Fork l1 l2 => [l1; l2]
    end.

  (** * NFA Compilation  *)

  Definition greedy_fork (greedy:bool) (l1 l2:label) :=
    if greedy
    then Fork l1 l2
    else Fork l2 l1.

  (* also returns the next fresh label and lookaround index *)
  Fixpoint compile (r:regex) (fresh:label) (lk_idx:nfa_oracle_idx): code * label * nfa_oracle_idx :=
    match r with
    | Epsilon => ([], fresh, lk_idx)
    | Character cd => ([Consume cd], S fresh, lk_idx)
    | Disjunction r1 r2 =>
        let '(bc1, f1, lk_idx1) := compile r1 (S fresh) lk_idx in
        let '(bc2, f2, lk_idx2) := compile r2 (S f1) lk_idx1 in
        ([Fork (S fresh) (S f1)] ++ bc1 ++ [Jmp f2] ++ bc2, f2, lk_idx2)
    | Sequence r1 r2 =>
        let '(bc1, f1, lk_idx1) := compile r1 fresh lk_idx in
        let '(bc2, f2, lk_idx2) := compile r2 f1 lk_idx1 in
        (bc1 ++ bc2, f2, lk_idx2)
    | Quantified greedy 0 (NoI.N 0) r1 => ([], fresh, lk_idx)
    | Quantified greedy 0 (NoI.N 1) r1 =>
        let '(bc1, f1, lk_idx1) := compile r1 (S (S (S fresh))) lk_idx in
        ([greedy_fork greedy (S fresh) (S f1); BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop (S f1)], S f1, lk_idx1)
    | Quantified greedy 0 (NoI.Inf) r1 =>
        let '(bc1, f1, lk_idx1) := compile r1 (S (S (S fresh))) lk_idx in
        ([greedy_fork greedy (S fresh) (S f1); BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop fresh], S f1, lk_idx1)
    | Group gid r1 =>
        let '(bc1, f1, lk_idx1) := compile r1 (S fresh) lk_idx in
        ([SetRegOpen gid] ++ bc1 ++ [SetRegClose gid], S f1, lk_idx1)
    | Anchor a => ([CheckAnchor a], S fresh, lk_idx)
    | Lookaround lk r1 => ([OracleQuery lk_idx lk r1], S fresh, S lk_idx)
    | _ => ([KillThread], S fresh, lk_idx) (* unsupported features *)
    end.

  (* adds an accept at the end of the code *)
  Definition compilation (r:regex) : code :=
    let '(c, _, _) := compile r 0 0 in
    c ++ [Accept].

  (** * Inductive NFA characterization *)
  (* like a representation predicate *)

  (* nfa_rep r code pc1 pc2 lk_idx1 lk_idx2 means that *)
  (* the bytecode for r is represented in code, from pc1 to pc2 (excluded), with lookaround indices used from lk_idx1 to lk_idx2 (excluded) *)
  Inductive nfa_rep : regex -> code -> label -> label -> nfa_oracle_idx -> nfa_oracle_idx -> Prop :=
  | nfa_rep_epsilon:
    forall c lbl lk_idx,
      nfa_rep Epsilon c lbl lbl lk_idx lk_idx
  | nfa_rep_char:
    forall c cd lbl lk_idx
      (CONSUME: get_pc c lbl = Some (Consume cd)),
      nfa_rep (Regex.Character cd) c lbl (S lbl) lk_idx lk_idx
  | nfa_rep_disj:
    forall c r1 r2 start end1 end2 lk_idx lk_idx1 lk_idx2
      (FORK: get_pc c start = Some (Fork (S start) (S end1)))
      (NFA1: nfa_rep r1 c (S start) end1 lk_idx lk_idx1)
      (JMP: get_pc c end1 = Some (Jmp end2))
      (NFA2: nfa_rep r2 c (S end1) end2 lk_idx1 lk_idx2),
      nfa_rep
        (Disjunction r1 r2) c start end2 lk_idx lk_idx2
  | nfa_rep_seq:
    forall c r1 r2 start end1 end2 lk_idx lk_idx1 lk_idx2
      (NFA1: nfa_rep r1 c start end1 lk_idx lk_idx1)
      (NFA2: nfa_rep r2 c end1 end2 lk_idx1 lk_idx2),
      nfa_rep (Sequence r1 r2) c start end2 lk_idx lk_idx2
  | nfa_rep_done:
    forall c r1 greedy lbl lk_idx,
      nfa_rep (Quantified greedy 0 (NoI.N 0) r1) c lbl lbl lk_idx lk_idx
  | nfa_rep_qmark:
    forall c r1 greedy start end1 lk_idx lk_idx1
      (FORK: get_pc c start = Some (greedy_fork greedy (S start) (S end1)))
      (BEGIN: get_pc c (S start) = Some (BeginLoop))
      (RESET: get_pc c (S (S start)) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S start))) end1 lk_idx lk_idx1)
      (END: get_pc c end1 = Some (EndLoop (S end1))),
      nfa_rep (Quantified greedy 0 (NoI.N 1) r1) c start (S end1) lk_idx lk_idx1
  | nfa_rep_star:
    forall c r1 greedy start end1 lk_idx lk_idx1
      (FORK: get_pc c start = Some (greedy_fork greedy (S start) (S end1)))
      (BEGIN: get_pc c (S start) = Some (BeginLoop))
      (RESET: get_pc c (S (S start)) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S start))) end1 lk_idx lk_idx1)
      (END: get_pc c end1 = Some (EndLoop start)),
      nfa_rep (Quantified greedy 0 (NoI.Inf) r1) c start (S end1) lk_idx lk_idx1
  | nfa_rep_group:
    forall c r1 gid start end1 lk_idx lk_idx1
      (OPEN: get_pc c start = Some (SetRegOpen gid))
      (NFA1: nfa_rep r1 c (S start) end1 lk_idx lk_idx1)
      (CLOSE: get_pc c end1 = Some (SetRegClose gid)),
      nfa_rep (Group gid r1) c start (S end1) lk_idx lk_idx1
  | nfa_rep_anchor:
    forall c a lbl lk_idx
      (CHECK: get_pc c lbl = Some (CheckAnchor a)),
      nfa_rep (Anchor a) c lbl (S lbl) lk_idx lk_idx
  | nfa_rep_lookaround:
    forall c i r1 lk lbl
      (ORACLE: get_pc c lbl = Some (OracleQuery i lk r1)),
      nfa_rep (Lookaround lk r1) c lbl (S lbl) i (S i)
  | nfa_unsupported:
    forall c r lbl lk_idx
      (UNSUPPORTED: ~ pike_regex r)
      (KILL: get_pc c lbl = Some KillThread),
      nfa_rep r c lbl (S lbl) lk_idx lk_idx.

  (** * Compile Characterization  *)

  Lemma cons_app:
    forall A (x:A) l, x::l = [x] ++ l.
  Proof. intros. simpl. auto. Qed.

  Lemma nfa_rep_extend:
    forall r c start endl lk_idx lk_idx' suffix,
      nfa_rep r c start endl lk_idx lk_idx' ->
      nfa_rep r (c++suffix) start endl lk_idx lk_idx'.
  Proof.
    intros r c start endl lk_idx lk_idx' suffix H. generalize dependent suffix.
    induction H; intros; econstructor;
      try (erewrite get_suffix; eauto); try apply IHnfa_rep;
      try apply IHnfa_rep1; try apply IHnfa_rep2. auto.
  Qed.



  (* correctness of the returned fresh label *)
  Lemma fresh_correct:
    forall r fresh l next lk_idx lk_idx',
      compile r fresh lk_idx = (l, next, lk_idx') ->
      fresh + List.length l = next.
  Proof.
    Ltac inv_comp H := inversion H; subst; simpl; lia.
    intros r.
    induction r; intros fresh l next lk_idx lk_idx' COMPILE; try solve[inv_comp COMPILE].
    - inversion COMPILE.
      destruct (compile r1 (S fresh)) as [[bc1 f1] lk_idx1] eqn:COMP1. destruct (compile r2 (S f1)) as [[bc2 f2] lk_idx2] eqn:COMP2.
      inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2. simpl.
      rewrite <- COMP1 in COMP2. simpl in COMP2. rewrite length_app. simpl. lia.
    - inversion COMPILE.
      destruct (compile r1 fresh) as [[bc1 f1] lk_idx1] eqn:COMP1. destruct (compile r2 f1) as [[bc2 f2] lk_idx2] eqn:COMP2.
      inversion H0. subst f2. apply IHr1 in COMP1. apply IHr2 in COMP2.
      rewrite <- COMP1 in COMP2. rewrite length_app. lia.
    - inversion COMPILE. destruct min.
      2: { inversion H0. simpl. lia. }
      destruct delta.
      + destruct n; try destruct n; try solve[inversion H0; simpl; lia].
        destruct (compile r (S (S (S fresh)))) as [[bc1 f1] lk_idx1] eqn:COMP1.
        inversion H0. apply IHr in COMP1.
        subst. simpl. rewrite length_app. simpl. lia.
      + destruct (compile r (S (S (S fresh)))) as [[bc1 f1] lk_idx1] eqn:COMP1.
        inversion H0. apply IHr in COMP1.
        subst. simpl. rewrite length_app. simpl. lia.
    - inversion COMPILE.
      destruct (compile r (S fresh)) as [[bc1 f1] lk_idx1] eqn:COMP1. inversion H0. apply IHr in COMP1.
      subst. simpl. rewrite length_app. simpl. lia.
  Qed.

  (* this shows that the compilation function adheres to the representation predicate *)
  Theorem compile_nfa_rep:
    forall r c start lk_idx endl prev lk_idx',
      compile r start lk_idx = (c, endl, lk_idx') ->
      start = List.length prev ->
      nfa_rep r (prev ++ c) start endl lk_idx lk_idx'.
  Proof.
    intros r. induction r; intros.
    - inversion H. subst. rewrite app_nil_r. constructor.
    - inversion H. subst. constructor. get_pc.
    - inversion H. destruct (compile r1 (S start)) as [[bc1 end1] lk_idx1] eqn:COMP1. destruct (compile r2 (S end1)) as [[bc2 end2] lk_idx2] eqn:COMP2.
      inversion H2. subst. apply nfa_rep_disj with (end1:=end1) (lk_idx1:=lk_idx1); try get_pc.
      + apply IHr1 with (prev:=prev ++ [Fork (S (length prev)) (S end1)]) in COMP1.
        2: { rewrite length_app. simpl. lia. }
        replace (prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
          (((prev ++ [Fork (S (length prev)) (S end1)]) ++ bc1) ++ (Jmp endl :: bc2)).
        2:{ rewrite <- app_assoc. rewrite <- app_assoc. auto. }
        apply nfa_rep_extend. auto.
      + apply fresh_correct in COMP1. rewrite <- COMP1.
        replace (S (length prev) + length bc1) with (length prev + (S (length bc1))) by lia.
        rewrite get_prefix. rewrite cons_app. rewrite app_assoc. get_pc.
      + apply IHr2 with (prev:= prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) in COMP2.
        * replace (prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ Jmp endl :: bc2) with
            ((prev ++ Fork (S (length prev)) (S end1) :: bc1 ++ [Jmp endl]) ++ bc2).
          2: { rewrite <- app_assoc. simpl. apply f_equal. apply f_equal. rewrite <- app_assoc. auto. }
          auto.
        * apply fresh_correct in COMP1. rewrite <- COMP1. simpl.
          rewrite length_app. simpl. rewrite length_app. simpl. lia.
    - inversion H. destruct (compile r1 start) as [[bc1 end1] lk_idx1] eqn:COMP1. destruct (compile r2 end1) as [[bc2 end2] lk_idx2] eqn:COMP2.
      inversion H2. subst. econstructor.
      + apply IHr1 with (prev:=prev) in COMP1; auto.
        rewrite app_assoc. apply nfa_rep_extend. eauto.
      + apply IHr2 with (prev:=prev ++ bc1) in COMP2; auto.
        * rewrite app_assoc. auto.
        * apply fresh_correct in COMP1. rewrite length_app. lia.
    - inversion H. destruct min.
      2: { inversion H2. subst. apply nfa_unsupported.
          - unfold not. intros. inversion H0.
          - get_pc. }
      destruct (destruct_delta delta) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]]; subst delta.
      (* Zero repetitions *)
      + inversion H2. subst. constructor.
      (* Question Mark *)
      + destruct (compile r (S (S (S start)))) as [[bc1 end1] lk_idx1] eqn:COMP1. inversion H2. subst. constructor; try get_pc.
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
      + destruct (compile r (S (S (S start)))) as [[bc1 end1] lk_idx1] eqn:COMP1. inversion H2. subst. constructor; try get_pc.
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
      + assert (([KillThread], S start, lk_idx) = (c,endl, lk_idx')).
        { destruct delta'; auto. lia. destruct delta'; auto. lia. }
        inversion H1. subst. apply nfa_unsupported.
        * unfold not. intros. inversion H0; subst; lia.
        * get_pc.
    - inversion H. subst. eapply nfa_rep_lookaround.
      get_pc.
    - inversion H. destruct (compile r (S start)) as [[bc1 end1] lk_idx1] eqn:COMP1. inversion H2. subst.
      constructor; try get_pc.
      + apply IHr with (prev:=prev ++ [SetRegOpen id]) in COMP1.
        2: { rewrite length_app. simpl. lia. }
        replace (prev ++ SetRegOpen id :: bc1 ++ [SetRegClose id]) with ((prev ++ SetRegOpen id :: bc1) ++ [SetRegClose id]).
        2:{ rewrite <- app_assoc. auto. }
        apply nfa_rep_extend. rewrite <- app_assoc in COMP1. simpl in COMP1. auto.
      + replace (prev ++ SetRegOpen id :: bc1 ++ [SetRegClose id]) with ((prev ++ SetRegOpen id :: bc1) ++ [SetRegClose id]).
        2:{ rewrite <- app_assoc. auto. }
        apply get_first_0. apply fresh_correct in COMP1. subst. rewrite length_app. simpl. lia.
    - inversion H. subst. constructor. get_pc.
    - inversion H. subst. apply nfa_unsupported.
      + unfold not. intros. inversion H0.
      + get_pc.
  Qed.

  (** * Oracle correctness *)

  (* the correctness condition for a single oracle with regards to a `Lookaround lk r1` *)
  Definition nfa_oracle_correct (o: nfa_oracle) (inp: input) (lk: lookaround) (r1: regex): Prop :=
    forall inp' b t,
      (* if the input is related to the input we are matching on *)
      inp' = inp \/ strict_suffix inp' inp forward ->
      (* and `t` is the backtracking tree of the lookaround *)
      bool_tree rer [Areg r1] inp' b (lk_dir lk) t ->
      (* then the oracle correctly answers whether the lookaround was satisfied *)
      o inp' = if tree_res t GroupMap.empty inp' (lk_dir lk) then positivity lk else negb (positivity lk).

  Fixpoint nfa_oracles_correct' (os: nfa_oracles) (r: regex) (inp: input) (lk_idx: nfa_oracle_idx): nfa_oracle_idx * Prop :=
    match r with
    | Sequence r1 r2 | Disjunction r1 r2 =>
        let '(lk_idx1, prop1) := nfa_oracles_correct' os r1 inp lk_idx in
        let '(lk_idx2, prop2) := nfa_oracles_correct' os r2 inp lk_idx1 in
        (lk_idx2, prop1 /\ prop2)
    | Quantified _ 0 (NoI.N 1) r1 | Quantified _ 0 (NoI.Inf) r1 | Group _ r1 =>
        let '(lk_idx1, prop1) := nfa_oracles_correct' os r1 inp lk_idx in
        (lk_idx1, prop1)
    | Lookaround lk r1 => (S lk_idx,
        match nth_error os lk_idx with
        | None => False
        | Some o => nfa_oracle_correct o inp lk r1
        end)
    | _ => (lk_idx, True)
    end.

  (* oracles `os` are correct with respect to a regex `r` if at every input position *)
  (* it correctly reports if a lookaround matches *)
  Definition nfa_oracles_correct (os: nfa_oracles) (r: regex) (inp: input): Prop :=
    snd (nfa_oracles_correct' os r inp 0).

  (* the returned lk_idx is independent from the input *)
  Lemma nfa_oracles_correct_same_lk_idx :
    forall r os inp1 inp2 lk_idx lk_idx1 lk_idx2 P1 P2
      (Hos1: nfa_oracles_correct' os r inp1 lk_idx = (lk_idx1, P1))
      (Hos2: nfa_oracles_correct' os r inp2 lk_idx = (lk_idx2, P2)),
      lk_idx1 = lk_idx2.
  Proof.
    induction r; simpl; intros;
      try injection Hos1 as <- <-; try injection Hos2 as <- <-;
      try easy.
    - destruct (nfa_oracles_correct' os r1 inp1) eqn:Hos11, (nfa_oracles_correct' os r2 inp1) eqn:Hos12.
      destruct (nfa_oracles_correct' os r1 inp2) eqn:Hos21, (nfa_oracles_correct' os r2 inp2) eqn:Hos22.
      injection Hos1 as <- <-. injection Hos2 as <- <-.
      replace n1 with n in * by eauto.
      eauto.
    - destruct (nfa_oracles_correct' os r1 inp1) eqn:Hos11, (nfa_oracles_correct' os r2 inp1) eqn:Hos12.
      destruct (nfa_oracles_correct' os r1 inp2) eqn:Hos21, (nfa_oracles_correct' os r2 inp2) eqn:Hos22.
      injection Hos1 as <- <-. injection Hos2 as <- <-.
      replace n1 with n in * by eauto.
      eauto.
    - destruct (nfa_oracles_correct' os r inp1 lk_idx) eqn:Hos1'.
      destruct (nfa_oracles_correct' os r inp2 lk_idx) eqn:Hos2'.
      destruct min; [destruct delta as [[|[|]]|]|];
        injection Hos1 as <- <-; injection Hos2 as <- <-; eauto.
    - destruct (nfa_oracles_correct' os r inp1 lk_idx) eqn:Hos1'.
      destruct (nfa_oracles_correct' os r inp2 lk_idx) eqn:Hos2'.
      injection Hos1 as <- <-; injection Hos2 as <- <-; eauto.
  Qed.

  (* the oracle is correct for all strict suffixes *)
  Lemma nfa_oracle_correct_strict_suffix :
    forall o inp lk r1 inp',
      nfa_oracle_correct o inp lk r1 ->
      strict_suffix inp' inp forward ->
      nfa_oracle_correct o inp' lk r1.
  Proof.
    unfold nfa_oracle_correct.
    intros.
    destruct H1; subst; eauto using strict_suffix_trans.
  Qed.

  Lemma nfa_oracles_correct_strict_suffix' :
    forall r o inp inp' lk_idx,
      snd (nfa_oracles_correct' o r inp lk_idx) ->
      strict_suffix inp' inp forward ->
      snd (nfa_oracles_correct' o r inp' lk_idx).
  Proof.
    induction r; simpl; intros; try easy.
    - destruct (nfa_oracles_correct' o r1 inp) eqn:Hos1, (nfa_oracles_correct' o r2 inp) eqn:Hos2.
      destruct (nfa_oracles_correct' o r1 inp') eqn:Hos1', (nfa_oracles_correct' o r2 inp') eqn:Hos2'.
      rewrite nfa_oracles_correct_same_lk_idx with (1:=Hos1) (2:=Hos1') in *.
      apply f_equal with (f:=snd) in Hos1, Hos2, Hos1', Hos2'.
      simpl in *.
      rewrite <-Hos1', <-Hos2'.
      rewrite <-Hos1, <-Hos2 in H. destruct H.
      eauto.
    - destruct (nfa_oracles_correct' o r1 inp) eqn:Hos1, (nfa_oracles_correct' o r2 inp) eqn:Hos2.
      destruct (nfa_oracles_correct' o r1 inp') eqn:Hos1', (nfa_oracles_correct' o r2 inp') eqn:Hos2'.
      rewrite nfa_oracles_correct_same_lk_idx with (1:=Hos1) (2:=Hos1') in *.
      apply f_equal with (f:=snd) in Hos1, Hos2, Hos1', Hos2'.
      simpl in *.
      rewrite <-Hos1', <-Hos2'.
      rewrite <-Hos1, <-Hos2 in H. destruct H.
      eauto.
    - destruct (nfa_oracles_correct' o r inp) eqn:Hos', (nfa_oracles_correct' o r inp') eqn:Hos''.
      apply f_equal with (f:=snd) in Hos', Hos''.
      simpl in *.
      rewrite <-Hos''.
      rewrite <-Hos' in H.
      destruct min; [destruct delta as [[|[|]]|]|]; eauto.
    - destruct nth_error. 2: easy.
      eapply nfa_oracle_correct_strict_suffix; eauto.
    - destruct (nfa_oracles_correct' o r inp) eqn:Hos', (nfa_oracles_correct' o r inp') eqn:Hos''.
      apply f_equal with (f:=snd) in Hos', Hos''.
      simpl in *.
      rewrite <-Hos''.
      rewrite <-Hos' in H.
      eauto.
  Qed.

  (* the oracles are correct for all strict suffixes *)
  Corollary nfa_oracles_correct_strict_suffix :
    forall r o inp inp',
      nfa_oracles_correct o r inp ->
      strict_suffix inp' inp forward ->
      nfa_oracles_correct o r inp'.
  Proof.
    unfold nfa_oracles_correct.
    intros.
    eapply nfa_oracles_correct_strict_suffix'; eauto.
  Qed.

  (* the returned lk_idx is the same for compilation and correctness of oracles *)
  Lemma compile_oracles_correct_same_lk_idx :
    forall r os fresh fresh' inp lk_idx lk_idx1 lk_idx2 c P
      (Hcomp: compile r fresh lk_idx = (c, fresh', lk_idx1))
      (Hos: nfa_oracles_correct' os r inp lk_idx = (lk_idx2, P)),
      lk_idx1 = lk_idx2.
  Proof.
    induction r; intros; simpl in *;
      try injection Hcomp as <- <- <-; try injection Hos as <- <-;
      try easy.
    - destruct (compile r1 (S fresh)) eqn:Hcomp1, p, (compile r2 (S l)) eqn:Hcomp2, p.
      destruct (nfa_oracles_correct' os r1 inp lk_idx) eqn:Hos1, (nfa_oracles_correct' os r2 inp n1) eqn:Hos2.
      injection Hcomp as <- <- <-. injection Hos as <- <-.
      replace n1 with n in * by eauto.
      eauto.
    - destruct (compile r1 fresh) eqn:Hcomp1, p, (compile r2 l) eqn:Hcomp2, p.
      destruct (nfa_oracles_correct' os r1 inp lk_idx) eqn:Hos1, (nfa_oracles_correct' os r2 inp n1) eqn:Hos2.
      injection Hcomp as <- <- <-. injection Hos as <- <-.
      replace n1 with n in * by eauto.
      eauto.
    - destruct (compile r (S (S (S fresh)))) eqn:Hcomp', p.
      destruct (nfa_oracles_correct' os r inp lk_idx) eqn:Hos'.
      replace n0 with n in * by eauto.
      destruct min; [destruct delta as [[|[|]]|]|];
        injection Hcomp as <- <- <-; injection Hos as <- <-; easy.
    - destruct (compile r (S fresh)) eqn:Hcomp', p.
      destruct (nfa_oracles_correct' os r inp lk_idx) eqn:Hos'.
      replace n0 with n in * by eauto.
      injection Hcomp as <- <- <-; injection Hos as <- <-; easy.
  Qed.


  (* if `os` are correct, then for all `OracleQuery`s we have an oracle *)
  Lemma nfa_oracles_get' :
    forall r os pc i c fresh fresh' inp lk_idx lk_idx' lk r1
      (Hcomp: compile r fresh lk_idx = (c, fresh', lk_idx'))
      (Hos: snd (nfa_oracles_correct' os r inp lk_idx))
      (Hget: get_pc c pc = Some (OracleQuery i lk r1)),
      nth_error os i <> None.
  Proof.
    induction r; intros; simpl in *;
      try injection Hcomp as <- <- <-;
      try solve[get_pc].
    - destruct (compile r1 (S fresh)) eqn:Hcomp1, p, (compile r2 (S l)) eqn:Hcomp2, p.
      destruct (nfa_oracles_correct' os r1 inp lk_idx) eqn:Hos1, (nfa_oracles_correct' os r2 inp n1) eqn:Hos2.
      simpl in Hos.
      injection Hcomp as <- <- <-.
      rewrite compile_oracles_correct_same_lk_idx with (1:=Hcomp1) (2:=Hos1) in *.
      get_pc.
      + eapply IHr1; eauto.
        now rewrite Hos1.
      + eapply IHr2; eauto.
        now rewrite Hos2.
    - destruct (compile r1 fresh) eqn:Hcomp1, p, (compile r2 l) eqn:Hcomp2, p.
      destruct (nfa_oracles_correct' os r1 inp lk_idx) eqn:Hos1, (nfa_oracles_correct' os r2 inp n1) eqn:Hos2.
      rewrite compile_oracles_correct_same_lk_idx with (1:=Hcomp1) (2:=Hos1) in *.
      simpl in Hos.
      injection Hcomp as <- <- <-.
      get_pc.
      + eapply IHr1; eauto.
        now rewrite Hos1.
      + eapply IHr2; eauto.
        now rewrite Hos2.
    - destruct (compile r (S (S (S fresh)))) eqn:Hcomp', p.
      destruct (nfa_oracles_correct' os r inp lk_idx) eqn:Hos'.
      destruct min; [destruct delta as [[|[|]]|]|];
        injection Hcomp as <- <- <-.
      + get_pc.
      + destruct greedy; eapply IHr; eauto; simpl in *; now rewrite Hos' || get_pc.
      + get_pc.
      + destruct greedy; eapply IHr; eauto; simpl in *; now rewrite Hos' || get_pc.
      + get_pc.
    - get_pc. subst.
      destruct nth_error; easy.
    - destruct (compile r (S fresh)) eqn:Hcomp', p.
      destruct (nfa_oracles_correct' os r inp lk_idx) eqn:Hos'.
      simpl in Hos.
      injection Hcomp as <- <- <-.
      get_pc.
      eapply IHr; eauto.
      now rewrite Hos'.
  Qed.

  (* if `os` are correct, then for all `OracleQuery`s we have an oracle *)
  Corollary nfa_oracles_get :
    forall r os inp pc i lk r1
      (Hos: nfa_oracles_correct os r inp)
      (Hget: get_pc (compilation r) pc = Some (OracleQuery i lk r1)),
      nth_error os i <> None.
  Proof.
    unfold compilation.
    intros.
    destruct compile eqn:Hcom, p.
    eapply nfa_oracles_get'; eauto; simpl; get_pc.
  Qed.

  (** * Lifting the representation predicate to continuations  *)
  (* This is useful to relate the continuations used in the tree semantics to the code produced by the NFA compiler *)

  (* action_rep a c pc1 pc2 lk_idx1 lk_idx2 indicates that the bytecode for a is located in code c between labels pc1 and pc2, *)
  (* with lookaround indices used from lk_idx1 to lk_idx2 (excluded)   *)
  Inductive action_rep : action -> code -> label -> label -> nfa_oracle_idx -> nfa_oracle_idx -> Prop :=
  | areg_bc:
    forall r c pcstart pcend lk_idx lk_idx'
      (NFA: nfa_rep r c pcstart pcend lk_idx lk_idx'),
      action_rep (Areg r) c pcstart pcend lk_idx lk_idx'
  | acheck_bc:
    forall c str pc pcnext lk_idx
      (END: get_pc c pc = Some (EndLoop pcnext)),
      action_rep (Acheck str) c pc pcnext lk_idx lk_idx
  | aclose_bc:
    forall c gid pc lk_idx
      (CLOSE: get_pc c pc = Some (SetRegClose gid)),
      action_rep (Aclose gid) c pc (S pc) lk_idx lk_idx.

  (* actions_rep cont c pc means that the bytecode for cont is located in c at labels pc *)
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
    forall a cont c pcstart pcmid lk_idx lk_idx'
      (ACTION: action_rep a c pcstart pcmid lk_idx lk_idx')
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
   | [ H : action_rep (Areg _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Aclose _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep (Acheck _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Epsilon) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Regex.Character _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Disjunction _ _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Sequence _ _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Quantified _ _ _ _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Group _ _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Anchor _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep (Lookaround _ _) _ _ _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | _ => try no_stutter
   end.

Create HintDb rep.
Hint Constructors nfa_rep : rep.
Hint Constructors action_rep : rep.
Hint Constructors actions_rep : rep.
Hint Resolve nfa_rep_extend : rep.

Ltac rep_impl n := unshelve eauto n with rep; eauto.
Tactic Notation "rep" integer(n) := rep_impl n.
Tactic Notation "rep" := rep 7.
