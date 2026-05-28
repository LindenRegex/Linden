From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics PikeSubset.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import StrictSuffix.
From Linden Require Import FunctionalSemantics.
From Linden Require Import ComputeIsTree.
From Linden Require Import Parameters.


(* An alternate definition of the semantics, using a boolean to know if one can exit a loop *)
(* And not using a group_map to exhibit the uniform-future property by construction *)



(** * Loop Boolean  *)
(* The loop boolean, indicating if we can exit a loop iteration or not *)
(* CanExit means that we are allowed to exit any quantifier: we have read a character more recently than we have entered a free quantifier *)
(* CannotExit means we can't exit the most recent quantifier we entered, because we haven't read anything since *)
Inductive LoopBool : Type :=
| CanExit
| CannotExit.


Section BooleanSemantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (** * Boolean Semantics  *)
  (* where checks consult the boolean instead of actually comparing strings *)

  Inductive bool_tree: actions -> input -> LoopBool -> Direction -> tree -> Prop :=
  | tree_done:
    (* nothing to do on an empty list of actions *)
    forall inp b dir,
      bool_tree [] inp b dir Match
  | tree_check:
    (* pops a successful check from the action list *)
    (* NEW: this only checks the boolean allows exit and not the strcheck in the tree *)
    forall inp strcheck cont treecont dir
      (TREECONT: bool_tree cont inp CanExit dir treecont),
      bool_tree (Acheck strcheck :: cont) inp CanExit dir (Progress treecont)
  | tree_check_fail:
  (* pops a failing check from the action list *)
    forall inp strcheck cont dir,
      bool_tree (Acheck strcheck :: cont) inp CannotExit dir Mismatch
  | tree_close:
  (* pops the closing of a group from the action list *)
    forall inp b cont treecont gid dir
      (TREECONT: bool_tree cont inp b dir treecont),
      bool_tree (Aclose gid :: cont) inp b dir (GroupAction (Close gid) treecont)
  | tree_epsilon:
    forall inp b cont tcont dir
      (ISTREE: bool_tree cont inp b dir tcont),
      bool_tree ((Areg Epsilon)::cont) inp b dir tcont
  | tree_char:
    forall c cd inp b nextinp cont tcont dir
      (READ: read_char rer cd inp dir = Some (c, nextinp))
      (* NEW: changes the boolean to CanExit *)
      (TREECONT: bool_tree cont nextinp CanExit dir tcont),
      bool_tree (Areg (Regex.Character cd) :: cont) inp b dir (Read c tcont)
  | tree_char_fail:
    forall cd inp b cont dir
      (READ: read_char rer cd inp dir = None),
      bool_tree (Areg (Regex.Character cd) :: cont) inp b dir Mismatch
  | tree_disj:
    forall r1 r2 cont t1 t2 inp b dir
      (ISTREE1: bool_tree (Areg r1 :: cont) inp b dir t1)
      (ISTREE2: bool_tree (Areg r2 :: cont) inp b dir t2),
      bool_tree (Areg (Disjunction r1 r2) :: cont) inp b dir (Choice t1 t2)
  | tree_sequence:
    (* adding next regex to the continuation *)
    forall r1 r2 cont t inp b dir
      (CONT: bool_tree (seq_list r1 r2 dir ++ cont) inp b dir t),
      bool_tree (Areg (Sequence r1 r2) :: cont) inp b dir t
  | tree_quant_forced:
    (* the quantifier is forced to iterate, because there is a strictly positive minimum *)
    forall r1 greedy min plus cont titer inp b gidl dir
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration *)
      (ISTREE1: bool_tree (Areg r1 :: Areg (Quantified greedy min plus r1) :: cont) inp b dir titer),
      bool_tree (Areg (Quantified greedy (S min) plus r1) :: cont) inp b dir (GroupAction (Reset gidl) titer)
  | tree_quant_done:
    (* the quantifier is done iterating, because min and max are zero *)
    forall r1 greedy cont tskip inp b dir
      (SKIP: bool_tree cont inp b dir tskip),
      bool_tree (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp b dir tskip
  | tree_quant_free:
    (* the quantifier is free to iterate or stop *)
    forall r1 greedy plus cont titer tskip tquant inp b gidl dir
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration, then a check, then executing the next quantifier *)
      (* NEW: switching the boolean to CannotExit *)
      (ISTREE1: bool_tree (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 plus r1) :: cont) inp CannotExit dir titer)
      (* skipping the quantifier entirely *)
      (SKIP: bool_tree cont inp b dir tskip)
      (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
      bool_tree (Areg (Quantified greedy 0 (NoI.N 1 + plus)%NoI r1) :: cont) inp b dir tquant
  | tree_group:
    forall r1 cont treecont inp b gid dir
      (TREECONT: bool_tree (Areg r1 :: Aclose gid :: cont) inp b dir treecont),
      bool_tree (Areg (Group gid r1) :: cont) inp b dir (GroupAction (Open gid) treecont)
  | tree_lk:
    forall lk r1 cont treecont treelk inp b gmlk dir
      (TREELK: bool_tree [Areg r1] inp b (lk_dir lk) treelk)
      (* since we have no backreferences, we do not care about the group map *)
      (RES_LK: lk_result lk treelk GroupMap.empty inp = Some gmlk)
      (TREECONT: bool_tree cont inp b dir treecont),
      bool_tree (Areg (Lookaround lk r1) :: cont) inp b dir (LK lk treelk treecont)
  | tree_lk_fail:
    forall lk r1 cont treelk inp b dir
      (TREELK: bool_tree [Areg r1] inp b (lk_dir lk) treelk)
      (* since we have no backreferences, we do not care about the group map *)
      (FAIL_LK: lk_result lk treelk GroupMap.empty inp = None),
      bool_tree (Areg (Lookaround lk r1) :: cont) inp b dir (LKFail lk treelk)
  | tree_anchor:
    forall a cont treecont inp b dir
      (ANCHOR: anchor_satisfied rer a inp = true)
      (TREECONT: bool_tree cont inp b dir treecont),
      bool_tree (Areg (Anchor a) :: cont) inp b dir (AnchorPass a treecont)
  | tree_anchor_fail:
    forall a cont inp b dir
      (ANCHOR: anchor_satisfied rer a inp = false),
      bool_tree (Areg (Anchor a) :: cont) inp b dir Mismatch.


(** * Boolean Tree Equivalence  *)

(* As we go down the tree, the boolean should "encode" the continuation and the current string *)
(* Meaning that the boolean is true when we can exit with the current string *)
(* And the boolean is false when we cannot *)


(** * First Step: encoding the invariant  *)

Inductive bool_encoding: LoopBool -> input -> actions -> Direction -> Prop :=
(* an empty continuation can be encoded with any boolean *)
| nil_encode:
  forall str b dir,
    bool_encoding b str [] dir
| cons_reg:
  forall b str cont r dir
    (ENCODE: bool_encoding b str cont dir),
    bool_encoding b str (Areg r::cont) dir
| cons_close:
  forall b str cont gid dir
    (ENCODE: bool_encoding b str cont dir),
    bool_encoding b str (Aclose gid::cont) dir
| cons_true:
  forall stk str head dir
    (ENCODE: bool_encoding CanExit str stk dir)
    (STRICT: strict_suffix str head dir),
    bool_encoding CanExit str (Acheck head::stk) dir
| cons_false:
  (* when we push the current string to the stack *)
  forall b stk str dir
    (ENCODE: bool_encoding b str stk dir),
    bool_encoding CannotExit str (Acheck str::stk) dir.


(* when we are already encoded with true, reading a new character preserves this true encoding *)
(* when we are encoded with false, reading a new character switches to being encoded with true *)
Lemma true_encoding_forward:
  forall str c pref cont b,
    bool_encoding b (Input (c::str) pref) cont forward ->
    bool_encoding CanExit (Input str (c::pref)) cont forward.
Proof.
  intros str c pref cont b H.
  remember (Input (c::str) pref) as prevstr.
  remember forward as dir.
  induction H; intros; subst.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
    eapply ss_next; eauto. simpl. auto.
  - constructor.
    + apply IHbool_encoding; auto.
    + subst. simpl.
      eapply ss_advance; eauto.
Qed.

Lemma true_encoding_backward:
  forall str c next cont b,
    bool_encoding b (Input next (c::str)) cont backward ->
    bool_encoding CanExit (Input (c::next) str) cont backward.
Proof.
  intros str c next cont b H.
  remember (Input next (c::str)) as nextstr.
  remember backward as dir.
  induction H; intros; subst.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
    eapply ss_next; eauto. simpl. auto.
  - constructor.
    + apply IHbool_encoding; auto.
    + subst. simpl.
      eapply ss_advance; eauto.
Qed.

(* if the string is different than the check, we know the boolean is true *)
Lemma encoding_different:
  forall b str strcheck cont dir,
    bool_encoding b str (Acheck strcheck::cont) dir ->
    str <> strcheck ->
    b = CanExit.
Proof.
  intros b0 str [strcheck pref] cont dir H.
  remember (Acheck (Input strcheck pref)::cont) as prevcont.
  induction H; intros; auto; inversion Heqprevcont;
    exfalso; auto.
Qed.

(* if the check is going to fail, we know the boolean is false *)
Lemma encoding_same:
  forall b str cont dir,
    bool_encoding b str (Acheck str::cont) dir -> b = CannotExit.
Proof.
  intros b str cont dir H.
  remember (Acheck str::cont) as prevcont.
  induction H; intros; auto; inversion Heqprevcont.
  subst. apply ss_neq in STRICT. contradiction.
Qed.

Lemma encode_next:
  forall b inp cont r dir,
    bool_encoding b inp (Areg r::cont) dir <->
    bool_encoding b inp cont dir.
Proof.
  intros b inp cont r dir. split; intros H.
  - inversion H; subst.
    inversion ENCODE; subst; auto.
  - destruct inp. constructor. inversion H; subst; auto.
Qed.

Lemma encode_close:
  forall b inp cont g dir,
    bool_encoding b inp (Aclose g::cont) dir <->
    bool_encoding b inp cont dir.
Proof.
  intros b inp cont g dir. split; intros H.
  - inversion H; subst.
    inversion ENCODE; subst; auto.
  - destruct inp. constructor. inversion H; subst; auto.
Qed.

(** * Encoding means suffixes (strict or not)  *)
(* Here we encode the invariant that the current input is always either equal or strict suffix of any checks in the current list of actions *)

Lemma encoding_suffix:
  forall b inp act chk dir,
    bool_encoding b inp act dir ->
    In (Acheck chk) act ->
    inp = chk \/ strict_suffix inp chk dir.
Proof.
  intros. induction H.
  - inversion H0.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
    right. subst. auto.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
Qed.

Lemma lk_result_indep_none:
  forall lk treelk gm1 gm2 inp,
    lk_result lk treelk gm1 inp = None ->
    lk_result lk treelk gm2 inp = None.
Proof.
  unfold lk_result.
  intros.
  destruct positivity.
  - destruct tree_res eqn:Hres1; [now destruct l|].
    now rewrite res_indep with (1:=Hres1).
  - destruct tree_res eqn:Hres1; [|discriminate].
    eapply res_indep_some in Hres1 as [? Hres]; eauto.
    now rewrite Hres.
Qed.

Lemma lk_result_indep_some:
  forall lk treelk gm1 gm2 gmlk1 inp,
    lk_result lk treelk gm1 inp = Some gmlk1 ->
    exists gmlk2, lk_result lk treelk gm2 inp = Some gmlk2.
Proof.
  unfold lk_result.
  intros.
  destruct positivity.
  - destruct tree_res eqn:Hres1; [|discriminate].
    eapply res_indep_some in Hres1 as [? Hres]; eauto.
    destruct x.
    eexists. now rewrite Hres.
  - destruct tree_res eqn:Hres1; [now destruct l|injection H as <-].
    eexists. now rewrite res_indep with (1:=Hres1).
Qed.

(** * Second Step: encoding equality  *)
(* the two tree constructions are equal *)

Theorem encode_equal:
  forall inp cont b dir t gm
    (PIKE: pike_actions cont)
    (ENCODE: bool_encoding b inp cont dir)
    (TREE: is_tree rer cont inp gm dir t),
    bool_tree cont inp b dir t.
Proof.
  intros inp cont b dir t gm PIKE ENCODE TREE.
  generalize dependent b.
  induction TREE; inversion PIKE; subst; intros;
    try solve[constructor; auto]; try solve[inversion H1; inversion H0].
  - assert (b = CanExit).
    { eapply encoding_different; eauto.
      eapply ss_neq; eauto. }
    subst. constructor. eapply IHTREE; eauto.
    inversion ENCODE; subst; auto.
  - assert (inp = strcheck \/ strict_suffix inp strcheck dir).
    { eapply encoding_suffix; eauto. simpl. auto. }
    destruct H; try contradiction. subst.
    assert (b = CannotExit).
    { eapply encoding_same; eauto. }
    subst. constructor.
  - constructor; apply IHTREE; auto;
      inversion ENCODE; subst; auto.
  - constructor; apply IHTREE; auto;
      inversion ENCODE; subst; auto.
  - apply encode_next in ENCODE.
    subst. econstructor; eauto. apply IHTREE; auto.
    destruct nextinp. destruct inp. simpl in READ.
    destruct dir.
    + destruct next0; inversion READ. destruct (char_match rer t cd); inversion READ; subst.
      eapply true_encoding_forward; eauto.
    + destruct pref0; inversion READ. destruct (char_match rer t cd); inversion READ; subst.
      eapply true_encoding_backward; eauto.
  - apply encode_next in ENCODE. inversion H1. inversion H0. subst. constructor.
    + apply IHTREE1; auto.
      { pike_subset. }
      apply encode_next. auto.
    + apply IHTREE2; auto.
      { pike_subset. }
      apply encode_next. auto.
  - constructor. apply IHTREE; eauto.
    { destruct dir; pike_subset. }
    destruct dir; inversion ENCODE; subst; constructor; constructor; auto.
  - inversion ENCODE. subst. constructor; auto.
  - destruct (destruct_delta (NoI.N 1 + plus)%NoI) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]].
    (* Zero repetitions *)
    + destruct plus; inversion DZ.
    (* Question Mark *)
    + eapply tree_quant_free; eauto.
      * destruct plus; inversion D1; subst.
        eapply IHTREE1; eauto.
        { pike_subset. }
        apply encode_next. eapply cons_false; eauto.
        inversion ENCODE. subst. constructor. eauto.
      * eapply IHTREE2; auto. apply encode_next in ENCODE. auto.
    (* Star *)
    + destruct plus; inversion DINF.
      eapply tree_quant_free; eauto.
      * eapply IHTREE1; auto.
        { pike_subset. }
        apply encode_next. eapply cons_false; eauto.
      * subst. eapply IHTREE2; auto. apply encode_next in ENCODE. auto.
    (* Unsupported *)
    + rewrite DUN in PIKE. assert (delta' <> 0).
      { destruct plus; inversion DUN. lia. }
      inversion PIKE. subst. inversion H4; subst.
      inversion H3; subst; lia.
  - constructor. apply IHTREE; auto.
    { inversion H1. inversion H0. subst. repeat progress (constructor; auto). }
    apply encode_next in ENCODE.
    apply encode_next. apply encode_close. auto.
  - apply encode_next in ENCODE.
    econstructor; eauto.
Qed.

Corollary boolean_correct:
  forall r inp dir t,
    pike_regex r ->
    is_tree rer [Areg r] inp GroupMap.empty dir t ->
    bool_tree [Areg r] inp CanExit dir t.
Proof.
  intros r str dir t PIKE H.
  eapply encode_equal; eauto.
  { constructor; constructor; auto. }
  constructor. constructor.
Qed.


(* Pike actions translate to Pike trees *)
Theorem subset_semantics:
  forall actions tree inp b dir
    (SUBSET: pike_actions actions)
    (ISTREE: bool_tree actions inp b dir tree),
    pike_subtree tree.
Proof.
  intros actions tree inp b dir SUBSET ISTREE.
  induction ISTREE;
    pike_subset;
    try (eapply IHISTREE || eapply IHISTREE1 || eapply IHISTREE2);
    pike_subset.
  - destruct dir; pike_subset.
  - destruct plus; inversion H3. destruct greedy; pike_subset.
    + eapply IHISTREE1. pike_subset.
    + eapply IHISTREE1. pike_subset.
  - destruct plus; inversion H3. subst.
    destruct greedy; pike_subset.
    + eapply IHISTREE1. pike_subset.
    + eapply IHISTREE1. pike_subset.
  - destruct plus; inversion H3.
Qed.

(** * Determinism  *)
(* I can't use determinism of is_tree since I've only proved one direction of equivalence *)

  Theorem bool_tree_determ:
    forall actions i b dir t1 t2,
      bool_tree actions i b dir t1 ->
      bool_tree actions i b dir t2 ->
      t1 = t2.
  Proof.
    intros actions i b dir t1 t2 H H0.
    generalize dependent t2.
    induction H; intros;
      try solve[inversion H0; subst; auto; f_equal; apply IHbool_tree; auto].
    - inversion H0; subst; auto; rewrite READ0 in READ; inversion READ.
      subst. f_equal. apply IHbool_tree. auto.
    - inversion H0; subst; auto; rewrite READ0 in READ; inversion READ.
    - inversion H1; subst. apply IHbool_tree1 in ISTREE1. apply IHbool_tree2 in ISTREE2.
      subst. auto.
    - inversion H0; subst; auto.
      destruct plus; inversion H3.
    - inversion H1; subst; auto.
      { destruct plus; inversion H4. }
      assert (plus0 = plus).
      { destruct plus0; destruct plus; inversion H4; auto. }
      subst. f_equal.
      + f_equal. apply IHbool_tree1; auto.
      + apply IHbool_tree2; auto.
    - inversion H1; subst; eauto.
      f_equal; eauto.
      specialize (IHbool_tree1 treelk0 ltac:(eauto)). subst.
      congruence.
    - inversion H0; subst; eauto.
      { specialize (IHbool_tree treelk0 ltac:(eauto)). subst. congruence. }
      f_equal; eauto.
    - inversion H0; subst; rewrite ANCHOR0 in ANCHOR; inversion ANCHOR.
      f_equal. apply IHbool_tree. auto.
    - inversion H0; subst; rewrite ANCHOR0 in ANCHOR; inversion ANCHOR. auto.
  Qed.

(* the other direction of implication is obtained using only determinism and productivity *)

  Theorem bool_to_istree:
    forall acts b inp dir t,
      bool_encoding b inp acts dir ->
      pike_actions acts ->
      bool_tree acts inp b dir t ->
      is_tree rer acts inp GroupMap.empty dir t.
  Proof.
    intros acts b inp dir t ENCODE H H0.
    (* productivity *)
    assert (exists t', is_tree rer acts inp GroupMap.empty dir t') as [t' ISTREE].
    { destruct (compute_tree rer acts inp  GroupMap.empty dir (S (actions_fuel acts inp dir))) eqn:PROD.
      2: { generalize functional_terminates. intros H1. apply H1 in PROD; auto; lia. }
      exists t0. eapply compute_is_tree; eauto. }
    eapply encode_equal in ISTREE as BOOLTREE; eauto.
    (* determinism *)
    assert (t = t') by (eapply bool_tree_determ; eauto). subst. auto.
  Qed.

  Theorem bool_to_istree_regex:
    forall r inp dir t,
      pike_regex r ->
      bool_tree [Areg r] inp CanExit dir t ->
      is_tree rer [Areg r] inp GroupMap.empty dir t.
  Proof.
    intros r inp dir t H H0.
    assert (bool_encoding CanExit inp [Areg r] dir) by (constructor; constructor).
    eapply bool_to_istree; eauto; pike_subset.
  Qed.


  Theorem booltree_istree_equiv:
    forall r inp dir t,
      pike_regex r ->
      bool_tree [Areg r] inp CanExit dir t <->
      is_tree rer [Areg r] inp GroupMap.empty dir t.
  Proof.
    intros r inp dir t SUBSET. split.
    - apply bool_to_istree_regex; auto.
    - apply boolean_correct; auto.
  Qed.

End BooleanSemantics.
