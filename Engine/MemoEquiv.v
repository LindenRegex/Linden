(** * Equivalence between MemoBT algorithm and MemoTree algorithm  *)

From Stdlib Require Import List Lia.
Import ListNotations.


From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import PikeEquiv MemoTree MemoBT TreeRep.


Section MemoEquiv.
  Context {params: LindenParameters}.
  Context {MS: MemoSet params}.
  Context (rer: RegExpRecord).

  (* FIXME: these are generalizations of definitions used in the PikeEquiv proof *)
  (* it could be nice to only use the generalized version everywhere *)
  (* I should write an NFA library *)

  (* a tree and a configuration are equivalent when they are about to execute the same thing *)
  (* this means when the tree represents a given list of actions, *)
  (* the config is at a pc that will execute the nfa of that same list of actions *)
  Inductive tree_config (code:code) : (tree * group_map * input) -> config -> Prop :=
  | tc_eq:
    forall inp tree gm pc b actions
      (TREE: bool_tree rer actions inp b tree)
      (CONT: actions_rep actions code pc)
      (SUBSET: pike_actions actions),
      tree_config code (tree, gm, inp) (pc, gm, b, inp)
  | tc_reset:
    forall inp tree gm pc b gidl
      (TC: tree_config code (tree,GroupMap.reset gidl gm,inp) (pc+1,GroupMap.reset gidl gm,b,inp))
      (RESET: get_pc code pc = Some (ResetRegs gidl)),
      tree_config code (GroupAction (Reset gidl) tree, gm, inp) (pc,gm,b,inp)
  | tc_begin:
    forall inp tree gm pc b
      (TC: tree_config code (tree,gm,inp) (pc+1,gm,CannotExit,inp))
      (BEGIN: get_pc code pc = Some BeginLoop),
      tree_config code (tree,gm,inp) (pc,gm,b,inp).

  (* rephrasing the lemma below so that induction handles pairs better *)
  Lemma tc_same_interm:
    forall code treegm1 treegm2 config1 config2
      (TC1: tree_config code treegm1 config1)
      (TC2: tree_config code treegm2 config2)
      (SAMEPC: fst (fst (fst config1)) = fst (fst (fst config2)))
      (SAMEB: snd (fst config1) = snd (fst config2))
      (SAMEGM1: snd (fst (fst config1)) = snd (fst treegm1))
      (SAMEGM2: snd (fst (fst config2)) = snd (fst treegm2))
      (SAMEINP: snd config1 = snd treegm2),
      fst (fst treegm1) = fst (fst treegm2).
  Proof.
    intros code treegm1 treegm2 config1 config2 TC1.
    generalize dependent config2. generalize dependent treegm2.
    induction TC1; intros; subst.
    - inversion TC2; subst;
        simpl in SAMEB; simpl in SAMEPC; simpl in SAMEGM1; simpl in SAMEGM2; subst;
        simpl in SAMEINP;
        try solve[eapply actions_rep_start in CONT; eauto; inversion CONT].
      simpl. subst. symmetry. eapply actions_rep_unicity in CONT; eauto.
    - inversion TC2; subst;
        simpl in SAMEB; simpl in SAMEPC; simpl in SAMEGM1; simpl in SAMEGM2; subst;
        try solve[eapply actions_rep_start in CONT; eauto; inversion CONT].
      2: { rewrite BEGIN in RESET. inversion RESET. }
      rewrite RESET in RESET0. inversion RESET0. subst.
      specialize (IHTC1 _ _ TC (eq_refl _) (eq_refl _) (eq_refl _) (eq_refl _)).
      simpl in IHTC1. destruct IHTC1; subst; simpl; auto.
    - inversion TC2; subst;
        simpl in SAMEB; simpl in SAMEPC; simpl in SAMEGM1; simpl in SAMEGM2; subst;
        try solve[eapply actions_rep_start in CONT; eauto; inversion CONT].
      { rewrite BEGIN in RESET. inversion RESET. }
      specialize (IHTC1 _ _ TC (eq_refl _) (eq_refl _) (eq_refl _) (eq_refl _)).
      simpl in IHTC1. destruct IHTC1; subst; simpl; auto.
  Qed.


  Lemma tc_same_tree:
    forall code inp t1 gm1 t2 gm2 pc b
      (TC1: tree_config code (t1,gm1,inp) (pc,gm1,b,inp))
      (TC2: tree_config code (t2,gm2,inp) (pc,gm2,b,inp)),
      t1 = t2.
  Proof.
    intros code inp t1 gm1 t2 gm2 pc b TC1 TC2.
    eapply tc_same_interm in TC1; eauto. simpl in TC1. auto.
  Qed.


  (* the initial active config and the initial active tree are related with the invariant *)
  Lemma initial_tree_config:
    forall r code tree inp
      (COMPILE: compilation r = code)
      (TREE: bool_tree rer [Areg r] inp CanExit tree)
      (SUBSET: pike_regex r),
      tree_config code (tree, GroupMap.empty,inp) (0, GroupMap.empty, CanExit,inp).
  Proof.
    intros r code tree inp COMPILE TREE SUBSET.
    unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
    apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
    apply fresh_correct in COMP. simpl in COMP. subst.
    subst. eapply tc_eq; eauto.
    2: { repeat (constructor; auto). }
    apply cons_bc with (pcmid := length c).
    - constructor. apply nfa_rep_extend. auto.
    - constructor. replace (length c) with (length c + 0) by auto. rewrite get_prefix. auto.
  Qed.


  (* lifting the equivalence predicate to lists *)
  Inductive list_tree_config (code:code) : list (tree * group_map * input) -> list config -> Prop :=
  | ltc_nil: list_tree_config code [] []
  | ltc_cons:
    forall inp treelist threadlist tree gm pc b
      (LTC: list_tree_config code treelist threadlist)
      (TC: tree_config code (tree, gm, inp) (pc, gm, b, inp)),
      list_tree_config code ((tree,gm,inp)::treelist) ((pc,gm,b,inp)::threadlist).

  Lemma ltc_app:
    forall code tl1 tl2 vl1 vl2
      (LTC1: list_tree_config code tl1 vl1)
      (LTC2: list_tree_config code tl2 vl2),
      list_tree_config code (tl1 ++ tl2) (vl1 ++ vl2).
  Proof.
    intros. induction LTC1; auto. simpl. econstructor; eauto.
  Qed.

  (* This is not, strictly speaking, an inclusion, which explains the second case of this disjunction *)
  (* Sometimes, we add seen pcs on the MemoBT side that do not correspond yet to any seen tree on the MemoTree side *)
  (* this happens during stuttering steps: such pcs are always stuttering, equivalent to the current active tree, *)
  (* but these pcs are not equal to the current pc : they're smaller *)
  (* the relation is then indexed by the current pc *)
  Definition seen_inclusion (c:code) (treeseen:seentrees) (memoset:memoset) (current:option (tree*group_map*input)) (currentpc:label): Prop :=
    forall pc b inp
      (SEEN: is_memo memoset pc b inp = true),
      (exists t gm,
          inseen treeseen t = true /\
            tree_config c (t, gm, inp) (pc, gm, b, inp))
      \/
        (stutters pc c = true /\
           exists t gm, pc < currentpc /\ current = Some (t,gm,inp) /\
                     tree_config c (t,gm,inp) (pc,gm,b,inp)).

  Lemma add_inclusion:
    forall treeseen memoset code inp tree pc gm b nextcurrent nextpc
      (INCL: seen_inclusion code treeseen memoset (Some (tree,gm,inp)) pc)
      (TT: tree_config code (tree,gm,inp) (pc,gm,b,inp)),
      seen_inclusion code (add_seentrees treeseen tree) (memoize memoset pc b inp) nextcurrent nextpc.
  Proof.
    intros treeseen memoset code inp tree pc gm b nextcurrent nextpc INCL TT.
    unfold seen_inclusion in *.
    intros pc0 b0 inp0 SEEN. apply is_memo_add in SEEN. destruct SEEN as [EQ|SEEN].
    - inversion EQ. subst. left. exists tree. exists gm. split; auto. apply in_add. left. auto.
    - specialize (INCL pc0 b0 inp0 SEEN).
      destruct INCL as [[ts [gms [SEENs TTs]]] | [ST [ts [gms [GEQ [EQ TTS]]]]]].
      + left. exists ts. exists gms. split; auto. apply in_add. right; auto.
      + left. exists ts. exists gms. split; auto.
        apply in_add. left; auto. inversion EQ. auto.
  Qed.


  Lemma skip_inclusion:
    forall code inp treeseen memoset tree gm currentpc
      (INCL: seen_inclusion code treeseen memoset (Some (tree, gm, inp)) currentpc)
      (SEEN: inseen treeseen tree = true),
    forall current nextpc,
      seen_inclusion code treeseen memoset current nextpc.
  Proof.
    intros code inp treeseen threadseen tree gm currentpc INCL SEEN current nextpc.
    unfold seen_inclusion in *.
    intros pc b inp0 SEENPC.
    specialize (INCL pc b inp0 SEENPC).
    destruct INCL as [[ts [gms [SEENs TTs]]] | [ST [ts [gms [GEQ [EQ TTS]]]]]].
    - left. exists ts. exists gms. split; auto.
    - left. exists ts. exists gms. split; auto. inversion EQ. subst. auto.
  Qed.

  Lemma stutter_inclusion:
    forall code inp treeseen memoset t gm pc b nextpc
      (GT: pc < nextpc )
      (INCL: seen_inclusion code treeseen memoset (Some (t, gm, inp)) pc)
      (STUTTERS: stutters pc code = true)
      (TT: tree_config code (t,gm,inp) (pc,gm,b,inp)),
      seen_inclusion code treeseen (memoize memoset pc b inp) (Some (t,gm,inp)) nextpc.
  Proof.
    intros code inp treeseen memoset t gm pc b nextpc GT INCL STUTTERS TT.
    unfold seen_inclusion in *.
    intros pc0 b0 inp0 SEEN.
    apply is_memo_add in SEEN. destruct SEEN as [EQ | SEEN].
    { inversion EQ. subst. right. split; auto.
      exists t. exists gm. split; auto. }
    specialize (INCL pc0 b0 inp0 SEEN).
    destruct INCL as [[ts [gms [SEENs TTs]]] | [ST [ts [gms [GEQ [EQ TTS]]]]]].
    - left. exists ts. exists gms. split; auto.
    - right. split; auto. exists ts. exists gms. split; auto. lia.
  Qed.


  Definition head_pc (stk:list config) : label :=
    match stk with
    | [] => 0
    | (pc,_,_,_)::_ => pc
    end.

  (* Simulation Invariant *)
  Inductive memo_inv (code:code): mtree_state -> mbt_state -> Prop :=
  | memoinv:
    forall treestk treeseen stk memoset
      (STACK: list_tree_config code treestk stk)
      (INCL: seen_inclusion code treeseen memoset (hd_error treestk) (head_pc stk)),
      memo_inv code (MTree treestk treeseen) (MBT stk memoset)
  | memoinv_final:
    forall result,
      memo_inv code (MTree_final result) (MBT_final result).


  (** * Invariant Initialization  *)

  Lemma initial_inclusion:
    forall c current currentpc,
      seen_inclusion c initial_seentrees initial_memoset current currentpc.
  Proof.
    intros c current currentpc. unfold seen_inclusion. intros pc b inp SEEN.
    rewrite initial_empty in SEEN. inversion SEEN.
  Qed.


  (* the initial states of both smallstep semantics are related with the invariant *)
  Lemma initial_memo_inv:
    forall r inp tree code
      (TREE: bool_tree rer [Areg r] inp CanExit tree)
      (COMPILE: compilation r = code)
      (SUBSET: pike_regex r),
      memo_inv code (initial_tree_state tree inp) (MemoBT.initial_state inp).
  Proof.
    intros r inp tree code TREE COMPILE SUBSET.
    unfold compilation in COMPILE. destruct (compile r 0) as [c fresh] eqn:COMP.
    apply compile_nfa_rep with (prev := []) in COMP as REP; auto. simpl in REP.
    apply fresh_correct in COMP. simpl in COMP. subst.
    eapply memoinv; auto.
    - econstructor.
      + constructor.
      + apply tc_eq with (actions:=[Areg r]); auto.
        2: { pike_subset. }
        eapply cons_bc; constructor.
        * apply nfa_rep_extend; eauto.
        * replace (length c) with (length c + 0) by auto.
          rewrite get_prefix. auto.
    - apply initial_inclusion.
  Qed.


  (** * Invariant Preservation  *)

  (* identifying states of MemoBT that are going to take a skip step *)
  Definition skip_state (mbs:mbt_state) : bool :=
    match mbs with
    | MBT_final _ => false
    | MBT stk memoset =>
        match stk with
        | [] => false
        | (pc,gm,b,inp)::stk => is_memo memoset pc b inp
        end
    end.

  (* fixme: this resembles generate_match from PikeEquiv.
     what should be the general version? *)
  Lemma exec_match:
    forall t pc gm b inp code leaf,
      exec_tree (t, gm, inp) = TMatch leaf ->
      tree_config code (t, gm, inp) (pc, gm, b, inp) ->
      stutters pc code = false ->
      exec_instr rer code (pc, gm, b, inp) = FoundMatch leaf.
  Proof.
    intros t pc gm b inp code leaf TREESTEP TC NOSTUTTER.
    unfold exec_tree in TREESTEP. destruct t; inversion TREESTEP; subst. clear TREESTEP.
    inversion TC; subst; try no_stutter.
    remember Match as TMATCH.
    (* here we have to proceed by induction because there are many ways to get a Match tree *)
    (* it could be epsilon, it could be epsilon followed by epsilon etc *)
    induction TREE; intros; subst; try inversion HeqTMATCH.
    - simpl. invert_rep. rewrite ACCEPT. auto.
    - repeat invert_rep. apply IHTREE; auto. pike_subset.
    - repeat invert_rep. apply IHTREE; auto.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. apply IHTREE; auto. pike_subset.
    - destruct greedy; inversion CHOICE.
  Qed.

  Lemma exec_dead:
    forall t pc gm b inp code,
      exec_tree (t, gm, inp) = TDead ->
      tree_config code (t, gm, inp) (pc, gm, b, inp) ->
      stutters pc code = false ->
      exec_instr rer code (pc, gm, b, inp) = Dead.
  Proof.
    intros t pc gm b inp code TREESTEP TC NOSTUTTER.
    inversion TC; subst; try no_stutter.
    2: { simpl in TREESTEP. inversion TREESTEP. }
    remember Mismatch as TMIS.
    induction TREE; intros; subst; try inversion HeqMIS; subst;
      simpl in TREESTEP; try solve[inversion TREESTEP].
    - repeat invert_rep. simpl. rewrite END. auto.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - repeat invert_rep. simpl. rewrite CONSUME, READ. auto.
    - repeat invert_rep. eapply IHTREE; repeat (econstructor; eauto); pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - destruct greedy; inversion TREESTEP.
    - repeat invert_rep. simpl. rewrite CHECK, ANCHOR. auto.
  Qed.


  Lemma exec_read:
    forall t pc gm b inp code char,
      tree_config code (Read char t, gm, inp) (pc, gm, b, inp) ->
      stutters pc code = false ->
      exists nextinp,
        advance_input inp forward = Some nextinp /\
        exec_instr rer code (pc, gm, b, inp) = Explore [(pc+1, gm, CanExit, nextinp)] /\
          tree_config code (t,gm,nextinp) (pc+1,gm,CanExit,nextinp).
  Proof.
    intros t pc gm b inp code char TC NOSTUTTER.
    inversion TC; subst; try invert_rep.
    remember (Read char t) as TREAD.
    induction TREE; intros; subst; try inversion HeqTREAD; subst.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - repeat invert_rep. exists nextinp.
      assert (CHECK: check_read rer cd inp forward = CanRead /\ advance_input inp forward = Some nextinp) by (apply can_read_correct; eauto).
      destruct CHECK as [CHECK ADVANCE0].
      repeat invert_rep. simpl. rewrite CONSUME, READ. split; auto. split; auto.
      eapply tc_eq; eauto.
      2: { pike_subset. }
      replace (pc + 1) with (S pc) by lia. auto.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - destruct greedy; inversion CHOICE.
  Qed.

  Lemma exec_open:
    forall t pc gm b inp code gid,
      tree_config code (GroupAction (Open gid) t, gm, inp) (pc, gm, b, inp) ->
      stutters pc code = false ->
      exec_instr rer code (pc, gm, b, inp) = Explore [(pc+1, GroupMap.open (idx inp) gid gm, b, inp)] /\
        tree_config code (t,GroupMap.open (idx inp) gid gm,inp) (pc+1, GroupMap.open (idx inp) gid gm, b, inp).
  Proof.
    intros t pc gm b inp code gid TC NOSTUTTER.
    inversion TC; subst; try invert_rep.
    remember (GroupAction (Open gid) t) as TOPEN.
    induction TREE; intros; subst; try inversion HeqTOPEN; subst.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - destruct greedy; inversion CHOICE.
    - repeat invert_rep. simpl. rewrite OPEN. split; auto.
      eapply tc_eq; eauto.
      2: { pike_subset. }
      replace (pc+1) with (S pc) by lia.
      apply cons_bc with (pcmid:=end1); repeat (econstructor; eauto).
  Qed.

  Lemma exec_close:
    forall t pc gm b inp code gid,
      tree_config code (GroupAction (Close gid) t, gm, inp) (pc, gm, b, inp) ->
      stutters pc code = false ->
      exec_instr rer code (pc, gm, b, inp) = Explore [(pc+1, GroupMap.close (idx inp) gid gm, b, inp)] /\
        tree_config code (t,GroupMap.close (idx inp) gid gm,inp) (pc+1, GroupMap.close (idx inp) gid gm, b, inp).
  Proof.
    intros t pc gm b inp code gid TC NOSTUTTER.
    inversion TC; subst; try no_stutter.
    remember (GroupAction (Close gid) t) as TCLOSE.
    induction TREE; intros; subst; try inversion HeqTCLOSE; subst.
    - repeat invert_rep. simpl. rewrite CLOSE. split; auto.
      econstructor; eauto. 2: pike_subset.
      replace (pc + 1) with (S pc) by lia. auto.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - destruct greedy; inversion CHOICE.
  Qed.

  Lemma exec_reset:
    forall gidl tree inp code pc b gm,
      tree_config code (GroupAction (Reset gidl) tree, gm, inp) (pc,gm,b,inp)  ->
      stutters pc code = false ->
      exec_instr rer code (pc,gm,b,inp) = Explore [(pc+1, GroupMap.reset gidl gm, b,inp)] /\
        tree_config code (tree,GroupMap.reset gidl gm,inp) (pc+1, GroupMap.reset gidl gm, b,inp).
  Proof.
    intros gidl tree inp code pc b gm TC NOSTUTTER.
    inversion TC; subst.
    - exfalso. eapply no_tree_reset; eauto.
    - simpl. rewrite RESET. split; auto.
    - exfalso. eapply doesnt_stutter_begin; eauto.
  Qed.

  Theorem exec_checkpass:
    forall t pc gm b inp code,
      tree_config code (Progress t, gm, inp) (pc, gm, b,inp) ->
      stutters pc code = false ->
      exists nextpc, exec_instr rer code (pc, gm, b, inp) = Explore [(nextpc,gm,CanExit,inp)] /\
                  tree_config code (t,gm,inp) (nextpc,gm,CanExit,inp).
  Proof.
    intros t pc gm b inp code TC NOSTUTTER.
    inversion TC; subst; try no_stutter.
    remember (Progress t) as TPASS.
    induction TREE; intros; subst; try inversion HeqTPASS; subst.
    - repeat invert_rep. pike_subset. simpl. exists pcmid.
      rewrite END. split; auto. econstructor; eauto.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - destruct greedy; inversion CHOICE.
  Qed.

  Theorem exec_anchorpass:
    forall t pc gm b inp code a,
      tree_config code (AnchorPass a t, gm, inp) (pc, gm, b, inp) ->
      stutters pc code = false ->
      exec_instr rer code (pc, gm, b, inp) = Explore [(pc+1,gm,b,inp)] /\
        tree_config code (t,gm,inp) (pc+1,gm,b,inp).
  Proof.
    intros t pc gm b inp code a TC NOSTUTTER.
    inversion TC; subst; try no_stutter.
    remember (AnchorPass a t) as TANCHOR.
    induction TREE; intros; subst; try inversion HeqTANCHOR; subst.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - destruct greedy; inversion CHOICE.
    - repeat invert_rep. simpl. rewrite CHECK, ANCHOR. split; auto.
      eapply tc_eq; eauto.
      2: { pike_subset. }
      replace (pc+1) with (S pc) by lia.
      assumption.
  Qed.

  Theorem exec_choice:
    forall tree1 tree2 gm inp code pc b exptree
      (TREESTEP: exec_tree (Choice tree1 tree2, gm, inp) = TExplore exptree)
      (NOSTUTTER: stutters pc code = false)
      (Tc: tree_config code (Choice tree1 tree2, gm, inp) (pc, gm, b, inp)),
    exists expconfig,
      exec_instr rer code (pc, gm, b, inp) = Explore expconfig /\
        list_tree_config code exptree expconfig.
  Proof.
    intros tree1 tree2 gm inp code pc b exptree TREESTEP NOSTUTTER TC.
    unfold exec_tree in TREESTEP. inversion TREESTEP. subst. clear TREESTEP.
    inversion TC; subst; try no_stutter.
    remember (Choice tree1 tree2) as TCHOICE.
    induction TREE; intros; subst; try inversion HeqTCHOICE; subst.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - repeat invert_rep. exists [(S pc,gm,b,inp);(S end1,gm,b,inp)]. split.
      + unfold exec_instr. rewrite FORK. auto.
      + constructor.
        * constructor. constructor.
          apply tc_eq with (actions:=Areg r2::cont); auto.
          2: { pike_subset. }
          repeat (econstructor; eauto).
        * apply tc_eq with (actions:=Areg r1::cont); auto.
          2: { pike_subset. }
          eapply cons_bc with (pcmid:=end1).
          ** constructor; auto.
          ** eapply jump_bc; eauto.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
      repeat (econstructor; eauto). pike_subset.
    - repeat invert_rep. eapply IHTREE; eauto. pike_subset.
    - (* when the choice comes from a quantifier *)
      destruct (destruct_delta (NoI.N 1 + plus)%NoI) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]].
      (* Zero Repetition *)
      + destruct plus; inversion DZ.
      + { (* Question Mark *)
          destruct plus; inversion D1. subst.
          repeat invert_rep. destruct greedy; inversion CHOICE; subst.
          +                           (* greedy qmark *)
            simpl. rewrite FORK. exists [(S pc, gm, b, inp); (S end1, gm, b, inp)]. split; auto.
            econstructor.
            * econstructor. constructor.
              apply tc_eq with (actions:=cont); auto. pike_subset.
            * apply tc_begin; auto.
              replace (S (S pc)) with (S pc +1) in RESET by lia.
              apply tc_reset; auto.
              apply tc_eq with (actions:=Areg r1 :: Acheck(inp)::Areg(Quantified true 0 (NoI.N 0) r1)::cont); auto.
              2: { pike_subset. }
              apply cons_bc with (pcmid:=end1).
              { constructor. replace (S pc+1+1) with (S (S (S pc))) by lia. auto. }
              repeat (econstructor; eauto).
          +                           (* lazy qmark *)
            simpl. rewrite FORK. exists [(S end1, gm, b, inp); (S pc, gm, b, inp)]. split; auto.
            econstructor.
            * constructor. constructor. apply tc_begin; auto.
              replace (S (S pc)) with (S pc + 1) in RESET by lia.
              apply tc_reset; auto.
              apply tc_eq with (actions:=Areg r1 :: Acheck(inp)::Areg(Quantified false 0 (NoI.N 0) r1)::cont); auto.
              2: { pike_subset. }
              apply cons_bc with (pcmid:=end1).
              { constructor. replace (S pc+1+1) with (S (S (S pc))) by lia. auto. }
              repeat (econstructor; eauto).
            * apply tc_eq with (actions:=cont); auto. pike_subset.
        }
      + { (* Star *)
          destruct plus; inversion DINF.
          repeat invert_rep. destruct greedy; inversion CHOICE; subst.
          +                           (* greedy star *)
            simpl. rewrite FORK. exists [(S pc, gm, b, inp); (S end1, gm, b, inp)]. split; auto.
            econstructor.
            * econstructor. constructor.
              apply tc_eq with (actions:=cont); auto. pike_subset.
            * apply tc_begin; auto.
              replace (S (S pc)) with (S pc +1) in RESET by lia.
              apply tc_reset; auto.
              apply tc_eq with (actions:=Areg r1 :: Acheck(inp)::Areg(Quantified true 0 +∞ r1)::cont); auto.
              2: { pike_subset. }
              apply cons_bc with (pcmid:=end1).
              { constructor. replace (S pc+1+1) with (S (S (S pc))) by lia. auto. }
              repeat (econstructor; eauto).
              replace (S (S pc)) with (S pc + 1) by lia. auto.
          +                           (* lazy star *)
            simpl. rewrite FORK. exists [(S end1, gm, b, inp); (S pc, gm, b, inp)]. split; auto.
            econstructor.
            * constructor. constructor. apply tc_begin; auto.
              replace (S (S pc)) with (S pc + 1) in RESET by lia.
              apply tc_reset; auto.
              apply tc_eq with (actions:=Areg r1 :: Acheck(inp)::Areg(Quantified false 0 +∞ r1)::cont); auto.
              2: { pike_subset. }
              apply cons_bc with (pcmid:=end1).
              { constructor. replace (S pc+1+1) with (S (S (S pc))) by lia. auto. }
              repeat (econstructor; eauto).
              replace (S (S pc)) with (S pc + 1) by lia. auto.
            * apply tc_eq with (actions:=cont); auto. pike_subset.
        }
      (* Unsupported *)
      + rewrite DUN in SUBSET. inversion SUBSET; subst. inversion H1; subst. inversion H0; subst; lia.
  Qed.

  (* next we combine the exec lemmas together, for the general non-stuttering case *)
  Theorem exec_explore:
    forall tree gm inp code pc b exptree
      (TREESTEP: exec_tree (tree,gm,inp) = TExplore exptree)
      (NOSTUTTER: stutters pc code = false)
      (TT: tree_config code (tree, gm, inp) (pc, gm, b, inp)),
    exists expconfig,
      exec_instr rer code (pc, gm, b, inp) = Explore expconfig /\
        list_tree_config code exptree expconfig.
  Proof.
    intros tree gm inp code pc b exptree TREESTEP NOSTUTTER TC.
    destruct tree; simpl in TREESTEP; inversion TREESTEP; subst.
    - eapply exec_dead in TC; auto. exists []. split; eauto. constructor.
    - eapply exec_choice; eauto.
    - eapply exec_read in TC as [nextinp [ADV [EXEC TC]]]; eauto.
      apply PikeTree.advance_next in ADV. subst.
      eexists. split; eauto.
      constructor; eauto. constructor.
    - inversion TC; subst; try no_stutter.
      eapply subset_semantics in TREE as SUBSETTREE; auto.
      inversion SUBSETTREE.
    - eapply exec_checkpass in TC as [nextpc [STEP EQ]]; auto.
      exists [(nextpc,gm,CanExit,inp)]. split; eauto.
      constructor; auto. constructor.
    - eapply exec_anchorpass in TC as [STEP EQ]; auto.
      exists [(pc+1,gm,b,inp)]. split; eauto.
      constructor; auto. constructor.
    - destruct g.
      + eapply exec_open in TC as [STEP EQ]; auto.
        exists [(pc+1,GroupMap.open (idx inp) g gm,b,inp)]. split; eauto.
        constructor; auto. constructor.
      + eapply exec_close in TC as [STEP EQ]; auto.
        exists [(pc+1,GroupMap.close (idx inp) g gm,b,inp)]. split; eauto.
        constructor; auto. constructor.
      + eapply exec_reset in TC as [STEP EQ]; auto.
        exists [(pc + 1, GroupMap.reset gl gm, b, inp)]. split; eauto.
        constructor; auto. constructor.
    - inversion TC; subst; try no_stutter.
      eapply subset_semantics in TREE as SUBSETTREE; auto.
      inversion SUBSETTREE.
    - inversion TC; subst; try no_stutter.
      eapply subset_semantics in TREE as SUBSETTREE; auto.
      inversion SUBSETTREE.
  Qed.

  (* in the case where we are at a stuttering step, we show that we still preserve the invariant *)
  Theorem exec_stutter:
    forall tree gm inp code pc b
      (TC: tree_config code (tree,gm,inp) (pc,gm,b,inp))
      (STUTTER: stutters pc code = true),
    exists nextpc nextb,
      exec_instr rer code (pc,gm,b,inp) = Explore [(nextpc,gm,nextb,inp)] /\
        tree_config code (tree,gm,inp) (nextpc,gm,nextb,inp).
  Proof.
    intros tree gm inp code pc b TC STUTTER.
    inversion TC; subst.
    (* reset is not stuttering *)
    2: { unfold stutters in STUTTER. rewrite RESET in STUTTER. inversion STUTTER. }
    (* at a beginloop instruction *)
    2: { exists (pc + 1). exists CannotExit. split; try split; auto.
         simpl. rewrite BEGIN. auto. }
    (* at a jmp instruction *)
    generalize dependent pc.
    induction TREE; intros.
    - invert_rep. stutter.
      exists pcstart. exists b. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=[]); auto; constructor; auto.
    - invert_rep.
      { invert_rep. stutter. }
      exists pcstart. exists CanExit. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=Acheck strcheck::cont); try constructor; auto; pike_subset.
    - invert_rep.
      { invert_rep. stutter. }
      exists pcstart. exists CannotExit. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=Acheck strcheck::cont); try constructor; auto; pike_subset.
    - invert_rep.
      { invert_rep. stutter. }
      exists pcstart. exists b. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=Aclose gid::cont); try constructor; auto; pike_subset.
    - invert_rep.
      + invert_rep. invert_rep; try in_subset.
        eapply IHTREE; eauto. pike_subset.
      + exists pcstart. exists b. split; try split; try lia.
        * simpl. rewrite JMP. auto.
        * apply tc_eq with (actions:=Areg Epsilon :: cont); try constructor; auto; pike_subset.
    - invert_rep.
      { invert_rep. invert_rep; try in_subset; try stutter. }
      exists pcstart. exists b. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=Areg (Regex.Character cd) :: cont); try constructor; auto; pike_subset.
        eapply tree_char; eauto.
    - invert_rep.
      { invert_rep. invert_rep; try in_subset; try stutter. }
      exists pcstart. exists b. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=Areg (Regex.Character cd) :: cont); try constructor; auto; pike_subset.
    - invert_rep.
      { invert_rep. invert_rep; try in_subset; try stutter. }
      exists pcstart. exists b. split; try split; try lia.
      * simpl. rewrite JMP. auto.
      * apply tc_eq with (actions:=Areg (Disjunction r1 r2) :: cont); try constructor; auto; pike_subset.
    - invert_rep.
      + invert_rep. invert_rep; try in_subset.
        eapply IHTREE; eauto. pike_subset.
        repeat (econstructor; eauto).
      + exists pcstart. exists b. split; try split; try lia.
        * simpl. rewrite JMP. auto.
        * apply tc_eq with (actions:=Areg (Sequence r1 r2) :: cont); try constructor; auto; pike_subset.
    - invert_rep.
      { invert_rep. invert_rep; try in_subset; try stutter. }
      exists pcstart. exists b. split; try split; try lia.
      * simpl. rewrite JMP. auto.
      * apply tc_eq with (actions:=Areg (Quantified greedy (S min) plus r1) :: cont); try constructor; auto; pike_subset.
    - invert_rep.
      + invert_rep. invert_rep; try in_subset.
        eapply IHTREE; eauto. pike_subset.
      + exists pcstart. exists b. split; try split; try lia.
        * simpl. rewrite JMP. auto.
        * apply tc_eq with (actions:=Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont); try constructor; auto; pike_subset.
    - destruct (destruct_delta (NoI.N 1 + plus)%NoI) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]].
      (* Zero repetition *)
      + destruct plus; inversion DZ.
      (* Question Mark *)
      + destruct plus; inversion D1. subst. invert_rep.
        { invert_rep. invert_rep; try in_subset. destruct greedy; stutter. }
        exists pcstart. exists b. split; try split; try lia.
        * simpl. rewrite JMP. auto.
        * apply tc_eq with (actions:=Areg (Quantified greedy 0 (NoI.N 1 + NoI.N 0)%NoI r1) :: cont); try constructor; auto; pike_subset.
          eapply tree_quant_free; eauto.
      (* Star *)
      + destruct plus; inversion DINF. invert_rep.
        { invert_rep. invert_rep; try in_subset. destruct greedy; stutter. }
        exists pcstart. exists b. split; try split; try lia.
        * simpl. rewrite JMP. auto.
        * apply tc_eq with (actions:=Areg (Quantified greedy 0 (NoI.N 1 + +∞)%NoI r1) :: cont); try constructor; auto; pike_subset.
          eapply tree_quant_free; eauto.
      (* Unsupported *)
      + rewrite DUN in SUBSET. inversion SUBSET; inversion H1; inversion H4; subst; lia.
    - invert_rep.
      { invert_rep. invert_rep; try in_subset; try stutter. }
      exists pcstart. exists b. split; try split; try lia.
      * simpl. rewrite JMP. auto.
      * apply tc_eq with (actions:=Areg (Group gid r1):: cont); try constructor; auto; pike_subset.
    - invert_rep.
      { invert_rep. invert_rep; try in_subset; try stutter. }
      exists pcstart. exists b. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=Areg (Anchor a) :: cont); try constructor; auto; pike_subset.
    - invert_rep.
      { invert_rep. invert_rep; try in_subset; try stutter. }
      exists pcstart. exists b. split; try split; try lia.
      + simpl. rewrite JMP. auto.
      + apply tc_eq with (actions:=Areg (Anchor a) :: cont); try constructor; auto; pike_subset.
  Qed.


  (* fixme: this should be automatic from a new definition of stutter_wf *)
  Lemma stutter_wf_exec_instr:
    forall code pc gm b nextpc nextgm nextb inp nextinp,
      stutter_wf rer code ->
      stutters pc code = true ->
      exec_instr rer code (pc,gm,b,inp) = Explore[(nextpc,nextgm,nextb,nextinp)] ->
      pc < nextpc.
  Proof.
    intros code pc gm b nextpc nextgm nextb inp nextinp WF STUTTERS EXEC.
    unfold stutter_wf in WF. unfold exec_instr in EXEC.
    destruct (get_pc code pc) eqn:GET; [|inversion EXEC].
    destruct b0; try solve[inversion EXEC; lia].
    - destruct read_char; try destruct p; inversion EXEC. lia.
    - destruct anchor_satisfied; inversion EXEC. lia.
    - inversion EXEC; subst.
      eapply (WF pc nextgm nextb nextpc nextgm nextb nextinp); eauto.
      unfold PikeVM.epsilon_step. rewrite GET.
      unfold PikeVM.upd_label. eauto.
    - destruct b; inversion EXEC; subst.
      eapply (WF pc nextgm CanExit nextpc nextgm CanExit nextinp); eauto.
      unfold PikeVM.epsilon_step. rewrite GET.
      unfold PikeVM.upd_label. eauto.
  Qed.



  Theorem invariant_preservation:
  forall code mts1 mbs1 mbs2
    (STWF: stutter_wf rer code)
    (INV: memo_inv code mts1 mbs1)
    (MEMOSTEP: memobt_step rer code mbs1 mbs2),
    (* either we make a step on both sides, preserving invariant *)
    (
      exists mts2,
        memotree_step mts1 mts2 /\
          memo_inv code mts2 mbs2
    )
    \/
      (* or we make a stuttering step, preserving invariant with mts1 *)
      (
          memo_inv code mts1 mbs2
      ).
  Proof.
    intros code mts1 mbs1 mbs2 STWF INV MEMOSTEP.
    inversion INV; subst.
    (* Final states make no step *)
    2: { inversion MEMOSTEP. }
    destruct (skip_state (MBT stk memoset)) eqn:SKIP.
    (* skip steps are performed in lockstep *)
    { left. destruct stk as [|[[[pc gm] b] inp] stk]; simpl in SKIP, INCL.
      { inversion SKIP. }
      inversion MEMOSTEP; try (rewrite UNSEEN in SKIP; inversion SKIP); subst.
      inversion STACK; subst.
      apply INCL in SKIP as [[teq [gmeq [SEENEQ TTEQ]]] | [STUTTER [t' [gm' [GEQ [EQ TTS]]]]]].
      2: { lia. }
      assert (teq = tree); subst.
      { eapply tc_same_tree; eauto. }
      exists (MTree treelist treeseen). split; constructor; auto.
      eapply skip_inclusion; eauto.
    }
    destruct treestk as [|[[t gm] inp] treestk].
    (* no more active trees or configs: no match found *)
    { inversion STACK. subst.
      left. inversion MEMOSTEP. subst. exists (MTree_final None). split; constructor; auto.
    }
    (* there is an active tree/config *)
    destruct stk as [|[[[pc gm'] b] inp'] stk]; inversion STACK; subst.
    rename gm' into gm. rename inp' into inp.
    destruct (stutters pc code) eqn:STUTTERS.
    (* Stuttering step *)
    { right. specialize (exec_stutter _ _ _ _ _ _ TC STUTTERS) as [nextpc [nextb [EXECBT LTCNEXT]]].
      assert (mbs2 = MBT ([(nextpc, gm, nextb, inp)]++stk) (memoize memoset pc b inp)); subst.
      { eapply memobt_deterministic; eauto. constructor; auto. }
      simpl. constructor; auto.
      { constructor; auto. }
      simpl. apply stutter_inclusion; auto.
      eapply stutter_wf_exec_instr; eauto.
    }
    left. simpl in SKIP. destruct (exec_tree (t, gm, inp)) eqn:EXEC.
    (* Match is found *)
    { eapply exec_match in EXEC as EXEC_INSTR; eauto.
      assert (mbs2 = MBT_final (Some l)); subst.
      { eapply memobt_deterministic; eauto. constructor; auto. }
      exists (MTree_final (Some l)). split; constructor; auto.
    }
    (* We keep exploring *)
    specialize (exec_explore _ _ _ _ _ _ _ EXEC STUTTERS TC) as [expconfig [EXECBT LTCNEXT]].
    assert (mbs2 = MBT (expconfig++stk) (memoize memoset pc b inp)); subst.
    { eapply memobt_deterministic; eauto. constructor; auto. }
    exists (MTree (l++treestk) (add_seentrees treeseen t)).
    split; constructor; auto.
    { apply ltc_app; auto. }
    eapply add_inclusion; eauto.
Qed.


End MemoEquiv.
