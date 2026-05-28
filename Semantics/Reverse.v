From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups StrictSuffix.
From Linden Require Import Tree Semantics FunctionalUtils.
From Linden Require Import FlatMap.
From Linden Require Import PikeSubset Tactics.
From Linden Require Import Utils Parameters LWParameters ListLemmas.
From Warblre Require Import Base RegExpRecord.

(** Reversal of regexes and tree directions *)

Section Reverse.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (** Reversal/flipping operations for regexes *)

  (* flips the direction of a lookaround *)
  Definition flip_lookaround (lk: lookaround) : lookaround :=
    match lk with
    | LookAhead => LookBehind
    | LookBehind => LookAhead
    | NegLookAhead => NegLookBehind
    | NegLookBehind => NegLookAhead
    end.

  (* flips begin and end input anchors *)
  Definition flip_anchor (a:anchor) : anchor :=
    match a with
    | BeginInput => EndInput
    | EndInput => BeginInput
    | WordBoundary => WordBoundary
    | NonWordBoundary => NonWordBoundary
    end.

  (* reverses a regex by flipping the sequences, lookarounds, and anchors *)
  Fixpoint regex_reverse (r: regex) : regex :=
    match r with
    | Epsilon => Epsilon
    | Regex.Character cd => Regex.Character cd
    | Disjunction r1 r2 => Disjunction (regex_reverse r1) (regex_reverse r2)
    | Sequence r1 r2 => Sequence (regex_reverse r2) (regex_reverse r1)
    | Quantified g min delta r1 => Quantified g min delta (regex_reverse r1)
    | Lookaround lk r1 => Lookaround (flip_lookaround lk) (regex_reverse r1)
    | Group id r1 => Group id (regex_reverse r1)
    | Anchor a => Anchor (flip_anchor a)
    | Backreference id => Backreference id
    end.

  Lemma regex_reverse_involutive : forall r, regex_reverse (regex_reverse r) = r.
  Proof.
    induction r; simpl; rewrite ?IHr, ?IHr1, ?IHr2; try reflexivity.
    - now destruct lk.
    - now destruct a.
  Qed.

  Lemma def_groups_none_regex_reverse:
    forall r,
      def_groups r = [] ->
      def_groups (regex_reverse r) = [].
  Proof.
    induction r; simpl; intros H;
      try rewrite ?IHr, ?IHr1, ?IHr2;
      try apply app_eq_nil in H as [H1 H2];
      try easy.
  Qed.

  Lemma pike_regex_reverse:
    forall r,
      pike_regex r ->
      pike_regex (regex_reverse r).
  Proof.
    induction r; simpl; intro H; pike_subset.
    now apply def_groups_none_regex_reverse.
  Qed.

  Lemma anchor_satisfied_reverse :
    forall a inp,
      anchor_satisfied rer a inp = anchor_satisfied rer (flip_anchor a) (input_reverse inp).
  Proof.
    intros [] [[] []]; simpl; reflexivity || now rewrite Bool.xorb_comm.
  Qed.

  Fixpoint flip_lookarounds (t: tree): tree :=
    match t with
    | Mismatch => Mismatch
    | Match => Match
    | Choice t1 t2 => Choice (flip_lookarounds t1) (flip_lookarounds t2)
    | Read c t => Read c (flip_lookarounds t)
    | ReadBackRef str t => ReadBackRef str (flip_lookarounds t)
    | Progress t => Progress (flip_lookarounds t)
    | AnchorPass a t => AnchorPass a (flip_lookarounds t)
    | GroupAction g t => GroupAction g (flip_lookarounds t)
    | LK lk tlk t => LK (flip_lookaround lk) (flip_lookarounds tlk) (flip_lookarounds t)
    | LKFail lk tlk => LKFail (flip_lookaround lk) (flip_lookarounds tlk)
    end.


  Lemma has_backreferneces_regex_reverse:
    forall r,
      has_backreferences r = has_backreferences (regex_reverse r).
  Proof.
    induction r; simpl; rewrite ?IHr1, ?IHr2; eauto.
    now rewrite Bool.orb_comm.
  Qed.


  Fixpoint has_backreferences_actions (acts: list action) : bool :=
    match acts with
    | [] => false
    | Areg r :: acts' => has_backreferences r || has_backreferences_actions acts'
    | Acheck _ :: acts' | Aclose _ :: acts' => has_backreferences_actions acts'
    end.

  Lemma pike_regex_no_backreferences_actions:
    forall acts,
      pike_actions acts ->
      has_backreferences_actions acts = false.
  Proof.
    induction 1; simpl.
    - easy.
    - rewrite IHpike_actions. destruct a; try easy.
      inversion H; subst.
      now rewrite (pike_regex_no_backreferences r H2).
  Qed.

  Fixpoint regex_reverse_actions (acts: list action) : list action :=
    match acts with
    | [] => []
    | Areg r :: acts' => Areg (regex_reverse r) :: regex_reverse_actions acts'
    | Acheck inp :: acts' => Acheck (input_reverse inp) :: regex_reverse_actions acts'
    | a :: acts' => a :: regex_reverse_actions acts'
    end.

  Lemma lk_result_reverse_none:
    forall lk treelk gm inp,
      lk_result lk treelk gm inp = None ->
      lk_result (flip_lookaround lk) (flip_lookarounds treelk) gm (input_reverse inp) = None.
  Proof.
    unfold lk_result.
    induction treelk; intros gm inp Hres.
    - now destruct lk.
    - now destruct lk.
    - admit.
  Admitted.


  Lemma reverse_direction:
    forall acts dir inp t,
      is_tree rer acts inp GroupMap.empty dir t ->
      is_tree rer (regex_reverse_actions acts) (input_reverse inp) GroupMap.empty (direction_reverse dir) (flip_lookarounds t).
  Proof.
    remember GroupMap.empty as gm.
    induction 1; subst; simpl;
      try solve[econstructor; eauto].
    - constructor; auto.
      now rewrite <-input_reverse_suffix, <-ss_flip_iff.
    - constructor; auto.
      now rewrite <-input_reverse_suffix, <-ss_flip_iff.
    - econstructor; eauto.
      now eapply read_char_reverse_some.
    - econstructor; eauto.
      now eapply read_char_reverse_none.
    - constructor.
      destruct dir; eauto.
    - simpl in *.
      econstructor.
      admit.
      admit.
    - econstructor.
      3: eauto.
      admit.
      admit.
      admit.
    - constructor.
      admit.
    - econstructor.
      + now destruct lk.
      + admit.
      + eauto.
    - econstructor.
      + now destruct lk.
      + apply lk_result_reverse_none; eauto.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.


  Lemma tree_leaf_dir_reverse:
    forall acts dir inp1 inp2 gm2 t1 t2,
      has_backreferences_actions acts = false ->
      is_tree rer acts inp1 GroupMap.empty dir t1 ->
      is_tree rer (rev acts) inp2 GroupMap.empty (direction_reverse dir) t2 ->
      In (inp2, gm2) (tree_leaves t1 GroupMap.empty inp1 dir) ->
      exists gm1, In (inp1, gm1) (tree_leaves t2 GroupMap.empty inp2 (direction_reverse dir)).
  Proof.
    intros * Hback Htree1.
    generalize dependent t2.
    generalize dependent inp2.
    generalize dependent gm2.
    remember GroupMap.empty as gm. (* FIXME: generalize gm *)
    induction Htree1; intros * Htree2 Hin1; subst; simpl in *; boolprop;
      (* actions that are backreferences *)
      try discriminate;
      (* trees with no leaves *)
      try contradiction;
      (* tree for the continuation *)
      try pose proof is_tree_productivity rer (rev cont) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
    (* match *)
    - inversion_clear Htree2; subst; simpl.
      injection Hin1 as <- <-.
      eauto.
    (* progress *)
    - admit.
    (* close group *)
    - specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Aclose gid] inp gm2' (direction_reverse dir) as [t'' Ht''].
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. inversion TREECONT. subst.
      simpl. eauto.
    (* epsilon *)
    - specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Areg Epsilon] inp gm2' (direction_reverse dir) as [t'' Ht''].
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. inversion ISTREE. subst.
      simpl. eauto.
    (* read *)
    -
      eapply read_char_success_advance in READ as Hadv.
      pose proof advance_input_success _ _ _ Hadv as Hadv'. rewrite Hadv' in *.
      specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Areg (Regex.Character cd)] nextinp gm2' (direction_reverse dir) as [t'' Ht''].
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''.
      2: {
        exfalso. subst.
        destruct inp as [[] []], dir; simpl in READ, READ0; destruct char_match; discriminate.
      }
      inversion TREECONT. subst.
      simpl. erewrite advance_input'_undo; eauto.
    (* disjunction *)
    - clear Htrest trest.
      rewrite in_app_iff in Hin1. destruct Hin1 as [Hin1 | Hin1].
      +
        pose proof is_tree_productivity rer (rev cont ++ [Areg r1]) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
        specialize (IHHtree1_1 ltac:(simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
        exists gm2'.
        admit. (* since inp is in tree of r1, then it must be in the tree of r1|r2 *)
      +
        pose proof is_tree_productivity rer (rev cont ++ [Areg r2]) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
        specialize (IHHtree1_2 ltac:(simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
        (* pose proof is_tree_atomic_productivity [[Areg r1]] inp2 gm2' (direction_reverse dir) as [t'' Ht'']. *)
        exists gm2'.
        admit. (* since inp is in tree of r2, then it must be in the tree of r1|r2 *)
    (* sequence *)
    -
    clear Htrest trest.
      pose proof is_tree_productivity rer (rev (seq_list r1 r2 dir ++ cont)) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
      specialize (IHHtree1 ltac:(destruct dir; simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Areg (Sequence r1 r2)] inp gm2' (direction_reverse dir) as [t'' Ht''].
      rewrite rev_app_distr in Htrest.
      assert (t2 = trest). {
        (* first you need to change the definition of `rev` on the actions to flip adjacent regexes *)
        (* then by the fact that tree of [Seq r1 r2] is the same as tree of [r1; r2] and tree determinism *)
        admit.
      }
      subst.
      eauto.
    (* quant forced *)
    - admit.
    (* quant done *)
    - specialize (IHHtree1 Hback0 eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Areg (Quantified greedy 0 (NoI.N 0) r1)] inp gm2' (direction_reverse dir) as [t'' Ht''].
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. 2: destruct plus; congruence. inversion SKIP. subst.
      simpl. eauto.
    (* quant free *)
    - admit.
    (* group *)
    - admit.
    (* lookaround *)
    - admit.
    (* anchor *)
    - specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Areg (Anchor a)] inp gm2' (direction_reverse dir) as [t'' Ht''].
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. 2: congruence. inversion TREECONT. subst.
      simpl. eauto.
  Admitted.

  (* returns the next action that has to be handled and the remaining actions *)
  Fixpoint handle (acts: list actions) : option (action * list actions) :=
    match acts with
    | [] => None
    | [] :: acts' => handle acts'
    | (a :: actsl) :: acts' => Some (a, actsl :: acts')
    end.

  (* FIXME: double check an iff is needed. Maybe one way implication is sufficient *)
  Lemma handle_empty_concat:
    forall acts,
      handle acts = None <-> concat acts = [].
  Proof.
    induction acts; simpl; split; intros H.
    - reflexivity.
    - reflexivity.
    - destruct a.
      + now rewrite <-IHacts.
      + discriminate.
    - apply app_eq_nil in H as [-> H].
      now rewrite IHacts.
  Qed.

  Lemma handle_concat_append:
    forall acts a cont,
      handle acts = Some (a, cont) ->
      concat acts = a :: concat cont.
  Proof.
    induction acts; simpl; intros * H.
    - discriminate.
    - destruct a.
      + now erewrite IHacts; eauto.
      + now injection H as <- <-.
  Qed.

  Lemma handle_rev_concat_append:
    forall acts a cont,
      handle acts = Some (a, cont) ->
      concat (rev acts) = concat (rev cont) ++ [a].
  Proof.
    induction acts; simpl; intros * H.
    - discriminate.
    - destruct a.
      + rewrite <-IHacts, concat_app, app_nil_r; eauto.
      +
        injection H as <- <-.
        simpl. rewrite !concat_app, <-app_assoc.
        simpl. rewrite app_nil_r.
        simpl.

  Admitted.


  (* Same as is_tree, but we store a list of `actions` rather than a list of `action`. *)
  (* This distinction allows us to keep track of which actions are treated atomically. *)
  (* In the end, the tree it defines is the same as is_tree's but gives more structure *)
  (* to the actions. *)
  Inductive is_tree_atomic: list actions -> input -> group_map -> Direction -> tree -> Prop :=
  | tree_match:
    (* nothing to do on an empty list of actions *)
    forall inp gm dir acts,
      handle acts = None ->
      is_tree_atomic acts inp gm dir Match
  | tree_check:
  (* pops a successful check from the action list *)
    forall inp gm dir strcheck cont treecont acts
      (PROGRESS: strict_suffix inp strcheck dir)
      (TREECONT: is_tree_atomic cont inp gm dir treecont),
      handle acts = Some (Acheck strcheck, cont) ->
      is_tree_atomic acts inp gm dir (Progress treecont)
  | tree_check_fail:
  (* pops a failing check from the action list *)
    forall inp gm dir strcheck cont acts
      (CHECKFAIL: ~strict_suffix inp strcheck dir),
      handle acts = Some (Acheck strcheck, cont) ->
      is_tree_atomic acts inp gm dir Mismatch
  | tree_close:
  (* pops the closing of a group from the action list *)
    forall inp gm dir cont treecont gid acts
      (TREECONT: is_tree_atomic cont inp (GroupMap.close (idx inp) gid gm) dir treecont),
      handle acts = Some (Aclose gid, cont) ->
      is_tree_atomic acts inp gm dir (GroupAction (Close gid) treecont)
  | tree_epsilon:
    forall inp gm dir cont tcont acts
      (ISTREE: is_tree_atomic cont inp gm dir tcont),
      handle acts = Some (Areg Epsilon, cont) ->
      is_tree_atomic acts inp gm dir tcont
  | tree_char:
    forall c cd inp gm dir nextinp cont tcont acts
      (READ: read_char rer cd inp dir = Some (c, nextinp))
      (TREECONT: is_tree_atomic cont nextinp gm dir tcont),
      handle acts = Some (Areg (Regex.Character cd), cont) ->
      is_tree_atomic acts inp gm dir (Read c tcont)
  | tree_char_fail:
    forall cd inp gm dir cont acts
      (READ: read_char rer cd inp dir = None),
      handle acts = Some (Areg (Regex.Character cd), cont) ->
      is_tree_atomic acts inp gm dir Mismatch
  | tree_disj:
    forall r1 r2 cont t1 t2 inp gm dir acts
      (ISTREE1: is_tree_atomic ([Areg r1] :: cont) inp gm dir t1)
      (ISTREE2: is_tree_atomic ([Areg r2] :: cont) inp gm dir t2),
      handle acts = Some (Areg (Disjunction r1 r2), cont) ->
      is_tree_atomic acts inp gm dir (Choice t1 t2)
  | tree_sequence:
    (* adding next regex to the continuation *)
    forall r1 r2 cont t inp gm dir acts
      (CONT: is_tree_atomic (seq_list r1 r2 dir :: cont) inp gm dir t),
      handle acts = Some (Areg (Sequence r1 r2), cont) ->
      is_tree_atomic acts inp gm dir t
  | tree_quant_forced:
    (* the quantifier is forced to iterate, because there is a strictly positive minimum *)
    forall r1 greedy min plus cont titer inp gm dir gidl acts
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration *)
      (ISTREE1: is_tree_atomic ([Areg r1; Areg (Quantified greedy min plus r1)] :: cont) inp (GroupMap.reset gidl gm) dir titer),
      handle acts = Some (Areg (Quantified greedy (S min) plus r1), cont) ->
      is_tree_atomic acts inp gm dir (GroupAction (Reset gidl) titer)
  | tree_quant_done:
    (* the quantifier is done iterating, because min and max are zero *)
    forall r1 greedy cont tskip inp gm dir acts
      (SKIP: is_tree_atomic cont inp gm dir tskip),
      handle acts = Some (Areg (Quantified greedy 0 (NoI.N 0) r1), cont) ->
      is_tree_atomic acts inp gm dir tskip
  | tree_quant_free:
    (* the quantifier is free to iterate or stop *)
    forall r1 greedy plus cont titer tskip tquant inp gm dir gidl acts
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration, then a check, then executing the next quantifier *)
      (ISTREE1: is_tree_atomic ([Areg r1; Acheck inp; Areg (Quantified greedy 0 plus r1)] :: cont) inp (GroupMap.reset gidl gm) dir titer)
      (* skipping the quantifier entirely *)
      (SKIP: is_tree_atomic cont inp gm dir tskip)
      (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
      handle acts = Some (Areg (Quantified greedy 0 (NoI.N 1 + plus)%NoI r1), cont) ->
      is_tree_atomic acts inp gm dir tquant
  | tree_group:
    forall r1 cont treecont inp gm dir gid acts
      (TREECONT: is_tree_atomic ([Areg r1; Aclose gid] :: cont) inp (GroupMap.open (idx inp) gid gm) dir treecont),
      handle acts = Some (Areg (Group gid r1), cont) ->
      is_tree_atomic acts inp gm dir (GroupAction (Open gid) treecont)
  | tree_lk:
    forall lk r1 cont treecont treelk inp gm gmlk dir acts
      (* there is a tree for the lookaround *)
      (TREELK: is_tree_atomic [[Areg r1]] inp gm (lk_dir lk) treelk)
      (* the lookaround tree has the expected result, resulting in a new group map gmlk *)
      (RES_LK: lk_result lk treelk gm inp = Some gmlk)
      (TREECONT: is_tree_atomic cont inp gmlk dir treecont),
      handle acts = Some (Areg (Lookaround lk r1), cont) ->
      is_tree_atomic acts inp gm dir (LK lk treelk treecont)
  | tree_lk_fail:
    forall lk r1 cont treelk inp gm dir acts
      (TREELK: is_tree_atomic [[Areg r1]] inp gm (lk_dir lk) treelk)
      (* the lookaround tree does not have the expected result *)
      (FAIL_LK: lk_result lk treelk gm inp = None),
      handle acts = Some (Areg (Lookaround lk r1), cont) ->
      is_tree_atomic acts inp gm dir (LKFail lk treelk)
  | tree_anchor:
    forall a cont treecont inp gm dir acts
      (ANCHOR: anchor_satisfied rer a inp = true)
      (TREECONT: is_tree_atomic cont inp gm dir treecont),
      handle acts = Some (Areg (Anchor a), cont) ->
      is_tree_atomic acts inp gm dir (AnchorPass a treecont)
  | tree_anchor_fail:
    forall a cont inp gm dir acts
      (ANCHOR: anchor_satisfied rer a inp = false),
      handle acts = Some (Areg (Anchor a), cont) ->
      is_tree_atomic acts inp gm dir Mismatch
  | tree_backref:
    forall gid inp gm nextinp dir cont tcont br_str acts
      (READ_BACKREF: read_backref rer gm gid inp dir = Some (br_str, nextinp))
      (TREECONT: is_tree_atomic cont nextinp gm dir tcont),
      handle acts = Some (Areg (Backreference gid), cont) ->
      is_tree_atomic acts inp gm dir (ReadBackRef br_str tcont)
  | tree_backref_fail:
    forall gid inp gm dir cont acts
      (READ_BACKREF: read_backref rer gm gid inp dir = None),
      handle acts = Some (Areg (Backreference gid), cont) ->
      is_tree_atomic acts inp gm dir Mismatch.

  Create HintDb is_tree.
  Hint Constructors is_tree : is_tree.
  Lemma is_tree_atomic_is_tree:
    forall acts inp gm dir t,
      is_tree_atomic acts inp gm dir t -> is_tree rer (concat acts) inp gm dir t.
  Proof.
    induction 1; only 1: solve[rewrite (proj1 (handle_empty_concat acts)); eauto with is_tree];
      (erewrite handle_concat_append; eauto);
      eauto with is_tree.
  Qed.

  Lemma is_tree_atomic_is_tree':
    forall acts inp gm dir t,
      is_tree_atomic acts inp gm dir t <-> is_tree rer (concat acts) inp gm dir t.
  Proof.
    split.
    - induction 1; only 1: solve[rewrite (proj1 (handle_empty_concat acts)); eauto with is_tree];
        (erewrite handle_concat_append; eauto);
        eauto with is_tree.
    - remember (concat acts) as acts'.
      generalize dependent acts.
      induction 2.
      + constructor. now rewrite handle_empty_concat.
      + econstructor; eauto.
        eapply IHis_tree.

  Admitted.


  Lemma handle_empty_rev:
    forall acts,
      handle acts = None ->
      handle (rev acts) = None.
  Proof.
  Admitted.

  Lemma handle_has_backreferences:
    forall acts a cont,
      has_backreferences_actions (concat acts) = false ->
      handle acts = Some (a, cont) ->
      has_backreferences_actions [a] = false /\ has_backreferences_actions (concat cont) = false.
  Proof.
  Admitted.

  Lemma tree_leaf_dir_reverse':
    forall acts dir inp1 inp2 gm2 t1 t2,
      has_backreferences_actions (concat acts) = false ->
      is_tree_atomic acts inp1 GroupMap.empty dir t1 ->
      is_tree_atomic (rev acts) inp2 GroupMap.empty (direction_reverse dir) t2 ->
      In (inp2, gm2) (tree_leaves t1 GroupMap.empty inp1 dir) ->
      exists gm1, In (inp1, gm1) (tree_leaves t2 GroupMap.empty inp2 (direction_reverse dir)).
  Proof.
    intros * Hback Htree1 Htree2%is_tree_atomic_is_tree.
    generalize dependent t2.
    generalize dependent inp2.
    generalize dependent gm2.
    remember GroupMap.empty as gm. (* FIXME: generalize gm *)
    induction Htree1; intros * Htree2 Hin1; subst; simpl in *; boolprop;
      (* actions that are backreferences *)
      try discriminate;
      (* trees with no leaves *)
      try contradiction;
      (* remove all is_tree_atomic *)
      repeat match goal with
      | H: is_tree_atomic _ _ _ _ _ |- _ => apply is_tree_atomic_is_tree in H
      end;
      (* tree for the continuation *)
      try pose proof is_tree_productivity rer (concat (rev cont)) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest];
      (* simplify Hback condition *)
      try (erewrite handle_concat_append in Hback; [simpl in Hback|eassumption]);
      (* synchronize Htree2 *)
      try (erewrite handle_concat_append in Htree2; [|eassumption]).
    (* match *)
    - eapply (proj1 (handle_empty_concat acts)) in H.
      rewrite concat_nil_rev in Htree2; auto.
      inversion_clear Htree2; subst; simpl.
      injection Hin1 as <- <-.
      eauto.
    (* progress *)
    - specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Acheck strcheck] inp gm2' (direction_reverse dir) as [t'' Ht''].
      erewrite handle_rev_concat_append in Htree2; eauto.
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''.
      2: {
        subst. simpl.
        (* hmmm, there is no contradiction here *)
        admit.
      }
      inversion TREECONT. subst.
      simpl. eauto.
    (* close group *)
    - specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Aclose gid] inp gm2' (direction_reverse dir) as [t'' Ht''].
      erewrite handle_rev_concat_append in Htree2; eauto.
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. inversion TREECONT. subst.
      simpl. eauto.
    (* epsilon *)
    - specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Areg Epsilon] inp gm2' (direction_reverse dir) as [t'' Ht''].
      erewrite handle_rev_concat_append in Htree2; eauto.
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. inversion ISTREE. subst.
      simpl. eauto.
    (* read *)
    - eapply read_char_success_advance in READ as Hadv.
      pose proof advance_input_success _ _ _ Hadv as Hadv'. rewrite Hadv' in *.
      specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer [Areg (Regex.Character cd)] nextinp gm2' (direction_reverse dir) as [t'' Ht''].
      erewrite handle_rev_concat_append in Htree2; eauto.
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''.
      2: {
        exfalso. subst.
        destruct inp as [[] []], dir; simpl in READ, READ0; destruct char_match; discriminate.
      }
      inversion TREECONT. subst.
      simpl. erewrite advance_input'_undo; eauto.
    (* disjunction *)
    - simpl in Hback.
      clear Htrest trest.
      rewrite in_app_iff in Hin1. destruct Hin1 as [Hin1 | Hin1].
      +
        pose proof is_tree_productivity rer (concat (rev cont ++ [[Areg r1]])) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
        specialize (IHHtree1_1 ltac:(destruct dir; simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
        erewrite handle_rev_concat_append in Htree2; eauto.
        exists gm2'.
        admit. (* since inp is in tree of r1, then it must be in the tree of r1|r2 *)
      +
        pose proof is_tree_productivity rer (concat (rev cont ++ [[Areg r2]])) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
        specialize (IHHtree1_2 ltac:(destruct dir; simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
        (* pose proof is_tree_atomic_productivity [[Areg r1]] inp2 gm2' (direction_reverse dir) as [t'' Ht'']. *)
        erewrite handle_rev_concat_append in Htree2; eauto.
        exists gm2'.
        admit. (* since inp is in tree of r2, then it must be in the tree of r1|r2 *)
    (* sequence *)
    -
    clear Htrest trest.
      pose proof is_tree_productivity rer (concat (rev cont ++ [seq_list r1 r2 dir])) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
      simpl in *.
      specialize (IHHtree1 ltac:(destruct dir; simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      assert (t2 = trest). {
        erewrite handle_rev_concat_append in Htree2; eauto.
        admit. (* the tree of [Areg r1; Areg r2] is the same as tree of [Areg (Sequence r1 r2)] *)
      }
      subst.
      eauto.
    (* quant forced *)
    -
      clear Htrest trest.
      pose proof is_tree_productivity rer (concat (rev cont ++ [[Areg r1; Areg (Quantified greedy min plus r1)]])) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
      assert (Hemptyreset: forall gm, GroupMap.reset gm GroupMap.empty = GroupMap.empty). {
        admit.
      }
      rewrite Hemptyreset in *.
      simpl in Hback.
      specialize (IHHtree1 ltac:(destruct dir; simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      erewrite handle_rev_concat_append in Htree2; eauto.
      admit. (* inp is in tree of [r1; quant n r1] so inp is in tree of [quant (S n) r1] *)
    (* quant done *)
    - simpl in Hback. boolprop.
      specialize (IHHtree1 Hback0 eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer (concat [[Areg (Quantified greedy 0 (NoI.N 0) r1)]]) inp gm2' (direction_reverse dir) as [t'' Ht''].
      erewrite handle_rev_concat_append in Htree2; eauto.
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. 2: destruct plus; congruence. inversion SKIP. subst.
      simpl. eauto.
    (* quant free *)
    - clear Htrest trest.
      simpl in Hback.
      assert ((In (inp2, gm2) (tree_leaves titer (GroupMap.reset (def_groups r1) GroupMap.empty) inp dir) \/ In (inp2, gm2) (tree_leaves tskip GroupMap.empty inp dir))). {
        destruct greedy; simpl in Hin1; rewrite in_app_iff in Hin1; tauto.
      }
      clear Hin1.
      destruct H0 as [Hin1 | Hin1].
      +
        pose proof is_tree_productivity rer (concat (rev cont ++ [[Areg r1; Acheck inp; Areg (Quantified greedy 0 plus r1)]])) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
        assert (Hemptyreset: forall gm, GroupMap.reset gm GroupMap.empty = GroupMap.empty). {
          admit.
        }
        rewrite Hemptyreset in *.
        specialize (IHHtree1_1 ltac:(destruct dir; simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
        erewrite handle_rev_concat_append in Htree2; eauto.
        exists gm2'.
        admit. (* since inp is in tree of [r1; Acheck inp; quant n r1], then it must be in the tree of [quant (S n) r1] *)
      +
        pose proof is_tree_productivity rer (concat (rev cont)) inp2 GroupMap.empty (direction_reverse dir) as [trest Htrest].
        specialize (IHHtree1_2 ltac:(destruct dir; simpl; boolprop; eauto) eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
        erewrite handle_rev_concat_append in Htree2; eauto.
        exists gm2'.
        admit. (* since inp is in tree of [], then it must be in the tree of [quant (S n) r1] *)
        (* the above explanation is not correct. This might need a more complicated induction hypothesis *)
    (* group *)
    - admit. (* need generalization of gm *)
    (* lookaround *)
    - admit.
    (* anchor *)
    -
      specialize (IHHtree1 Hback eq_refl _ _ _ Htrest Hin1) as [gm2' Hin2].
      pose proof is_tree_productivity rer (concat [[Areg (Anchor a)]]) inp gm2' (direction_reverse dir) as [t'' Ht''].
      erewrite handle_rev_concat_append in Htree2; eauto.
      eexists. eapply tree_leaves_cont; eauto.
      inversion Ht''. 2: congruence. inversion TREECONT. subst.
      simpl. eauto.
    - discriminate.
  Admitted.

  Lemma tree_leaf_dir_reverse_regex:
    forall r dir inp1 inp2 gm2 t1 t2,
      has_backreferences r = false ->
      is_tree rer [Areg r] inp1 GroupMap.empty dir t1 ->
      is_tree rer [Areg r] inp2 GroupMap.empty (direction_reverse dir) t2 ->
      In (inp2, gm2) (tree_leaves t1 GroupMap.empty inp1 dir) ->
      exists gm1, In (inp1, gm1) (tree_leaves t2 GroupMap.empty inp2 (direction_reverse dir)).
  Proof.
    intros * Hback Htree1 Htree2 Hin1.
    eapply tree_leaf_dir_reverse' with (acts:=[[Areg r]]); eauto.
    - simpl. boolprop. tauto.
    (* - rewrite is_tree_atomic_is_tree; eauto.
    - rewrite is_tree_atomic_is_tree; eauto. *)
  Admitted.


  Theorem tree_leaf_regex_reverse :
    forall r inp1 inp2 gm2 t1 t2 dir,
      has_backreferences r = false ->
      is_tree rer [Areg r] inp1 GroupMap.empty dir t1 ->
      is_tree rer [Areg (regex_reverse r)] (input_reverse inp2) GroupMap.empty dir t2 ->
      In (inp2, gm2) (tree_leaves t1 GroupMap.empty inp1 dir) ->
      exists gm1, In (input_reverse inp1, gm1) (tree_leaves t2 GroupMap.empty (input_reverse inp2) dir).
  Proof.
  Admitted.


End Reverse.
