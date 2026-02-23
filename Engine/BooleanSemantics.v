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

  Inductive bool_tree: actions -> input -> LoopBool -> tree -> Prop :=
  | tree_done:
    (* nothing to do on an empty list of actions *)
    forall inp b,
      bool_tree [] inp b Match
  | tree_check:
    (* pops a successful check from the action list *)
    (* NEW: this only checks the boolean allows exit and not the strcheck in the tree *)
    forall inp strcheck cont treecont
      (TREECONT: bool_tree cont inp CanExit treecont),
      bool_tree (Acheck strcheck :: cont) inp CanExit (Progress treecont)
  | tree_check_fail:
  (* pops a failing check from the action list *)
    forall inp strcheck cont,
      bool_tree (Acheck strcheck :: cont) inp CannotExit Mismatch
  | tree_close:
  (* pops the closing of a group from the action list *)
    forall inp b cont treecont gid
      (TREECONT: bool_tree cont inp b treecont),
      bool_tree (Aclose gid :: cont) inp b (GroupAction (Close gid) treecont)
  | tree_epsilon:
    forall inp b cont tcont
      (ISTREE: bool_tree cont inp b tcont),
      bool_tree ((Areg Epsilon)::cont) inp b tcont
  | tree_char:
    forall c cd inp b nextinp cont tcont
      (READ: read_char rer cd inp forward = Some (c, nextinp))
      (* NEW: changes the boolean to CanExit *)
      (TREECONT: bool_tree cont nextinp CanExit tcont),
      bool_tree (Areg (Regex.Character cd) :: cont) inp b (Read c tcont)
  | tree_char_fail:
    forall cd inp b cont
      (READ: read_char rer cd inp forward = None),
      bool_tree (Areg (Regex.Character cd) :: cont) inp b Mismatch
  | tree_disj:
    forall r1 r2 cont t1 t2 inp b
      (ISTREE1: bool_tree (Areg r1 :: cont) inp b t1)
      (ISTREE2: bool_tree (Areg r2 :: cont) inp b t2),
      bool_tree (Areg (Disjunction r1 r2) :: cont) inp b (Choice t1 t2)
  | tree_sequence:
    (* adding next regex to the continuation *)
    forall r1 r2 cont t inp b
      (CONT: bool_tree (Areg r1 :: Areg r2 :: cont) inp b t),
      bool_tree (Areg (Sequence r1 r2) :: cont) inp b t
  | tree_quant_forced:
    (* the quantifier is forced to iterate, because there is a strictly positive minimum *)
    forall r1 greedy min plus cont titer inp b gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration *)
      (ISTREE1: bool_tree (Areg r1 :: Areg (Quantified greedy min plus r1) :: cont) inp b titer),
      bool_tree (Areg (Quantified greedy (S min) plus r1) :: cont) inp b (GroupAction (Reset gidl) titer)
  | tree_quant_done:
    (* the quantifier is done iterating, because min and max are zero *)
    forall r1 greedy cont tskip inp b
      (SKIP: bool_tree cont inp b tskip),
      bool_tree (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp b tskip
  | tree_quant_free:
    (* the quantifier is free to iterate or stop *)
    forall r1 greedy plus cont titer tskip tquant inp b gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration, then a check, then executing the next quantifier *)
      (* NEW: switching the boolean to CannotExit *)
      (ISTREE1: bool_tree (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 plus r1) :: cont) inp CannotExit titer)
      (* skipping the quantifier entirely *)
      (SKIP: bool_tree cont inp b tskip)
      (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
      bool_tree (Areg (Quantified greedy 0 (NoI.N 1 + plus)%NoI r1) :: cont) inp b tquant
  | tree_group:
    forall r1 cont treecont inp b gid
      (TREECONT: bool_tree (Areg r1 :: Aclose gid :: cont) inp b treecont),
      bool_tree (Areg (Group gid r1) :: cont) inp b (GroupAction (Open gid) treecont)
  | tree_anchor:
    forall a cont treecont inp b
      (ANCHOR: anchor_satisfied rer a inp = true)
      (TREECONT: bool_tree cont inp b treecont),
      bool_tree (Areg (Anchor a) :: cont) inp b (AnchorPass a treecont)
  | tree_anchor_fail:
    forall a cont inp b
      (ANCHOR: anchor_satisfied rer a inp = false),
      bool_tree (Areg (Anchor a) :: cont) inp b Mismatch.


(** * Boolean Tree Equivalence  *)

(* As we go down the tree, the boolean should "encode" the continuation and the current string *)
(* Meaning that the boolean is true when we can exit with the current string *)
(* And the boolean is false when we cannot *)


(** * First Step: encoding the invariant  *)

Inductive bool_encoding: LoopBool -> input -> actions -> Prop :=
(* an empty continuation can be encoded with any boolean *)
| nil_encode:
  forall str b,
    bool_encoding b str []
| cons_reg:
  forall b str cont r
    (ENCODE: bool_encoding b str cont),
    bool_encoding b str (Areg r::cont)
| cons_close:
  forall b str cont gid
    (ENCODE: bool_encoding b str cont),
    bool_encoding b str (Aclose gid::cont)
| cons_true:
  forall stk str head
    (ENCODE: bool_encoding CanExit str stk)
    (STRICT: strict_suffix str head forward),
    bool_encoding CanExit str (Acheck head::stk)
| cons_false:
  (* when we push the current string to the stack *)
  forall b stk str
    (ENCODE: bool_encoding b str stk),
    bool_encoding CannotExit str (Acheck str::stk).


(* when we are already encoded with true, reading a new character preserves this true encoding *)
(* when we are encoded with false, reading a new character switches to being encoded with true *)
Lemma true_encoding:
  forall str c pref cont b,
    bool_encoding b (Input (c::str) pref) cont ->
    bool_encoding CanExit (Input str (c::pref)) cont.
Proof.
  intros str c pref cont b H.
  remember (Input (c::str) pref) as prevstr.
  induction H; intros.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto. rewrite Heqprevstr in STRICT.
    eapply ss_next; eauto. simpl. auto.
  - constructor.
    + apply IHbool_encoding; auto.
    + subst. simpl.
      eapply ss_advance; eauto.
Qed.

(* if the string is different than the check, we know the boolean is true *)
Lemma encoding_different:
  forall b str strcheck cont,
    bool_encoding b str (Acheck strcheck::cont) ->
    str <> strcheck ->
    b = CanExit.
Proof.
  intros b0 str [strcheck pref] cont H.
  remember (Acheck (Input strcheck pref)::cont) as prevcont.
  induction H; intros; auto; inversion Heqprevcont;
    exfalso; auto.
Qed.

(* if the check is going to fail, we know the boolean is false *)
Lemma encoding_same:
  forall b str cont,
    bool_encoding b str (Acheck str::cont) -> b = CannotExit.
Proof.
  intros b str cont H.
  remember (Acheck str::cont) as prevcont.
  induction H; intros; auto; inversion Heqprevcont.
  subst. apply ss_neq in STRICT. contradiction.
Qed.

Lemma encode_next:
  forall b inp cont r,
    bool_encoding b inp (Areg r::cont) <->
    bool_encoding b inp cont.
Proof.
  intros b inp cont r. split; intros H.
  - inversion H; subst.
    inversion ENCODE; subst; auto.
  - destruct inp. constructor. inversion H; subst; auto.
Qed.

Lemma encode_close:
  forall b inp cont g,
    bool_encoding b inp (Aclose g::cont) <->
    bool_encoding b inp cont.
Proof.
  intros b inp cont g. split; intros H.
  - inversion H; subst.
    inversion ENCODE; subst; auto.
  - destruct inp. constructor. inversion H; subst; auto.
Qed.

(** * Encoding means suffixes (strict or not)  *)
(* Here we encode the invariant that the current input is always either equal or strict suffix of any checks in the current list of actions *)

Lemma encoding_suffix:
  forall b inp act chk,
    bool_encoding b inp act ->
    In (Acheck chk) act ->
    inp = chk \/ strict_suffix inp chk forward.
Proof.
  intros. induction H.
  - inversion H0.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
    right. subst. auto.
  - simpl in H0. destruct H0 as [H0|IN]; try inversion H0; auto.
Qed.


(** * Second Step: encoding equality  *)
(* the two tree constructions are equal *)

Theorem encode_equal:
  forall inp cont b t gm
    (PIKE: pike_actions cont)
    (ENCODE: bool_encoding b inp cont)
    (TREE: is_tree rer cont inp gm forward t),
    bool_tree cont inp b t.
Proof.
  intros inp cont b t gm PIKE ENCODE TREE.
  generalize dependent b.
  remember forward as dir.
  induction TREE; inversion PIKE; subst; intros;
    try solve[constructor; auto]; try solve [inversion H1; inversion H0].
  - assert (b = CanExit).
    { eapply encoding_different; eauto.
      eapply ss_neq; eauto. }
    subst. constructor. eapply IHTREE; eauto.
    inversion ENCODE; subst; auto.
  - assert (inp = strcheck \/ strict_suffix inp strcheck forward).
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
    destruct next0; inversion READ. destruct (char_match rer t cd); inversion READ; subst.
    eapply true_encoding; eauto.
  - apply encode_next in ENCODE. inversion H1. inversion H0. subst. constructor.
    + apply IHTREE1; auto.
      { pike_subset. }
      apply encode_next. auto.
    + apply IHTREE2; auto.
      { pike_subset. }
      apply encode_next. auto.
  - constructor. subst. simpl in IHTREE. apply IHTREE; eauto.
    { pike_subset. }
    inversion ENCODE; subst; constructor; constructor; auto.
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
  forall r inp t,
    pike_regex r ->
    is_tree rer [Areg r] inp GroupMap.empty forward t ->
    bool_tree [Areg r] inp CanExit t.
Proof.
  intros r str t PIKE H.
  eapply encode_equal; eauto.
  { constructor; constructor; auto. }
  constructor. constructor.
Qed.


(* Pike actions translate to Pike trees *)
Theorem subset_semantics:
  forall actions tree inp b
    (SUBSET: pike_actions actions)
    (ISTREE: bool_tree actions inp b tree),
    pike_subtree tree.
Proof.
  intros actions tree inp b SUBSET ISTREE.
  induction ISTREE; try eapply IHISTREE; pike_subset.
  - eapply IHISTREE1. pike_subset.
  - eapply IHISTREE2. pike_subset.
  - destruct plus; inversion H3. destruct greedy; pike_subset.
    + eapply IHISTREE1. pike_subset.
    + eapply IHISTREE1. pike_subset.
  - destruct plus; inversion H3. subst.
    destruct greedy; pike_subset.
    + eapply IHISTREE1. pike_subset.
    + eapply IHISTREE1. pike_subset.
  - destruct plus; inversion H3.
  - eapply IHISTREE. pike_subset.
Qed.

(** * Determinism  *)
(* I can't use determinism of is_tree since I've only proved one direction of equivalence *)

  Theorem bool_tree_determ:
    forall actions i b t1 t2,
      bool_tree actions i b t1 ->
      bool_tree actions i b t2 ->
      t1 = t2.
  Proof.
    intros actions i b t1 t2 H H0.
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
    - inversion H0; subst; rewrite ANCHOR0 in ANCHOR; inversion ANCHOR.
      f_equal. apply IHbool_tree. auto.
    - inversion H0; subst; rewrite ANCHOR0 in ANCHOR; inversion ANCHOR. auto.
  Qed.

(* the other direction of implication is obtained using only determinism and productivity *)

  Theorem bool_to_istree:
    forall acts b inp t,
      bool_encoding b inp acts ->
      pike_actions acts ->
      bool_tree acts inp b t ->
      is_tree rer acts inp GroupMap.empty forward t.
  Proof.
    intros acts b inp t ENCODE H H0.
    (* productivity *)
    assert (exists t', is_tree rer acts inp GroupMap.empty forward t') as [t' ISTREE].
    { destruct (compute_tree rer acts inp  GroupMap.empty forward (S (actions_fuel acts inp forward))) eqn:PROD.
      2: { generalize functional_terminates. intros H1. apply H1 in PROD; auto; lia. }
      exists t0. eapply compute_is_tree; eauto. }
    eapply encode_equal in ISTREE as BOOLTREE; eauto.
    (* determinism *)
    assert (t = t') by (eapply bool_tree_determ; eauto). subst. auto.
  Qed.

  Theorem bool_to_istree_regex:
    forall r inp t,
      pike_regex r ->
      bool_tree [Areg r] inp CanExit t ->
      is_tree rer [Areg r] inp GroupMap.empty forward t.
  Proof.
    intros r inp t H H0.
    assert (bool_encoding CanExit inp [Areg r]) by (constructor; constructor).
    eapply bool_to_istree; eauto; pike_subset.
  Qed.


  Theorem booltree_istree_equiv:
    forall r inp t,
      pike_regex r ->
      bool_tree [Areg r] inp CanExit t <->
      is_tree rer [Areg r] inp GroupMap.empty forward t.
  Proof.
    intros r inp t SUBSET. split.
    - apply bool_to_istree_regex; auto.
    - apply boolean_correct; auto.
  Qed.

End BooleanSemantics.
