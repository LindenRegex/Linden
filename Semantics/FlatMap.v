From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Tree Semantics Chars Regex.
From Linden Require Import Parameters.
From Warblre Require Import Base RegExpRecord.


(** * Flat mapping: definition and lemmas *)

(* a propositional version of flat_map *)
(* FlatMap lbase f lmapped means that lmapped corresponds to the list lbase where each element has been replaced by its image by f *)
Inductive FlatMap {X Y:Type} : list X -> (X -> list Y -> Prop) -> list Y -> Prop :=
| FM_nil: forall f,
  FlatMap [] f []
| FM_cons:
  forall lbase f lmapped x ly
    (FM: FlatMap lbase f lmapped)
    (HEAD: f x ly),
    FlatMap (x::lbase) f (ly ++ lmapped).

(* We could use the functional flat_map, but this would require using the function compute_tr that associates a tree to each regex and input. *)
(* The proof does not strictly rely on this function, it merely relies on the
existence of a unique tree associated to each regex and input. *)

(* Used in disjunction and free quantifier cases of contextual equivalence proof *)
Property FlatMap_app {X Y: Type}:
  forall (lbase1 lbase2 : list X) (f: X -> list Y -> Prop) (lmapped1 lmapped2: list Y),
    FlatMap lbase1 f lmapped1 ->
    FlatMap lbase2 f lmapped2 ->
    FlatMap (lbase1 ++ lbase2) f (lmapped1 ++ lmapped2).
Proof.
  intros lbase1 lbase2 f lmapped1 lmapped2 FM1 FM2.
  induction FM1.
  - auto.
  - rewrite <- app_assoc, <- app_comm_cons. constructor; auto.
Qed.

(* Determinism of a propositional function *)
Definition determ {A B: Type} (f: A -> B -> Prop) :=
  forall x y1 y2, f x y1 -> f x y2 -> y1 = y2.


(* Building up to flatmap_leaves_equiv_l *)

Lemma FlatMap_in {A B}:
  forall (l: list A) (f: A -> list B -> Prop) fl x fx,
    (* For a deterministic f, *)
    determ f ->
    (* if f flat maps l to fl, *)
    FlatMap l f fl ->
    (* and x is in l, *)
    In x l ->
    f x fx ->
    (* then all the elements of f(x) are in fl. *)
    Forall (fun y => In y fl) fx.
Proof.
  intros l f fl x fx DETERM FM INxl F.
  revert fl FM.
  induction l.
  1: inversion INxl.
  intros fl FM. destruct INxl.
  - subst a. inversion FM; subst.
    assert (ly = fx) by eauto (* using DETERM *). subst ly. clear HEAD FM F IHl.
    induction fx.
    + constructor.
    + constructor.
      * rewrite <- app_comm_cons. left. reflexivity.
      * eapply Forall_impl; eauto. simpl. tauto.
  - inversion FM; subst. specialize (IHl H lmapped FM0).
    eapply Forall_impl; eauto. simpl. intro. rewrite in_app_iff. tauto.
Qed.

Section Leaves.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

(* Getting the leaves of a continuation applied to a particular leaf *)
(* This predicate will be used to express that appending a list of actions a2 to a list
of actions a1 corresponds to extending the leaves of the tree corresponding to actions
a1 with trees corresponding to the actions of a2 (see lemma leaves_concat below) *)
Inductive act_from_leaf : actions -> Direction -> leaf -> list leaf -> Prop :=
| afl:
  forall act dir l t
    (TREE: is_tree rer act (fst l) (snd l) dir t),
    act_from_leaf act dir l (tree_leaves t (snd l) (fst l) dir).

(* The function act_from_leaf is deterministic *)
Lemma act_from_leaf_determ: forall act dir, determ (act_from_leaf act dir).
Proof.
  intros act dir x y1 y2 Hxy1 Hxy2.
  inversion Hxy1; subst. inversion Hxy2; subst.
  assert (t0 = t) by eauto using is_tree_determ. subst t0. reflexivity.
Qed.

(* Adding new things to the continuation is the same as extending each leaf of the tree with these new things *)
Theorem leaves_concat:
  forall inp gm dir act1 act2 tapp t1
    (TREE_APP: is_tree rer (act1 ++ act2) inp gm dir tapp)
    (TREE_1: is_tree rer act1 inp gm dir t1),
    FlatMap (tree_leaves t1 gm inp dir) (act_from_leaf act2 dir) (tree_leaves tapp gm inp dir).
Proof.
  intros. generalize dependent tapp.
  induction TREE_1; intros; simpl in *.
  - (* Done *)
    rewrite <- app_nil_r. constructor; constructor. auto.

  - (* Check pass *)
    inversion TREE_APP; subst. 2: contradiction.
    simpl. apply IHTREE_1. auto.

  - (* Check fail *)
    inversion TREE_APP; subst. 1: contradiction.
    simpl. constructor.

  - (* Close *)
    inversion TREE_APP; subst. simpl.
    apply IHTREE_1. auto.

  - (* Epsilon *)
    inversion TREE_APP; subst. auto.

  - (* Read char success *)
    inversion TREE_APP; subst. 2: congruence.
    simpl.
    rewrite READ in READ0. injection READ0 as <- <-.
    rewrite advance_input_success with (nexti := nextinp).
    2: eauto using read_char_success_advance.
    auto.

  - (* Read char fail *)
    inversion TREE_APP; subst. 1: congruence.
    simpl. constructor.

  - (* Disjunction *)
    inversion TREE_APP; subst.
    simpl. apply FlatMap_app; auto.

  - (* Sequence *)
    inversion TREE_APP; subst.
    rewrite app_assoc in CONT. auto.

  - (* Forced quantifier *)
    inversion TREE_APP; subst. simpl.
    auto.

  - (* Done quantifier *)
    inversion TREE_APP; subst.
    2: { destruct plus; discriminate. }
    auto.

  - (* Free quantifier *)
    inversion TREE_APP; subst.
    1: { destruct plus; discriminate. }
    assert (plus0 = plus). {
      destruct plus0; destruct plus; try discriminate; try reflexivity.
      injection H1 as <-. auto.
    }
    subst plus0.
    unfold greedy_choice. destruct greedy.
    + (* Greedy *)
      simpl. apply FlatMap_app; auto.
    + (* Lazy *)
      simpl. apply FlatMap_app; auto.

  - (* Group *)
    inversion TREE_APP; subst. simpl.
    auto.

  - (* Lookaround success *)
    inversion TREE_APP; subst;
      assert (treelk0 = treelk) by (eapply is_tree_determ; eauto); subst.
    2: { rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
    rewrite RES_LK in RES_LK0. injection RES_LK0 as <-.
    destruct positivity eqn:Hpos.
    + unfold lk_result in RES_LK. rewrite Hpos in RES_LK.
      pose proof first_tree_leaf treelk gm inp (lk_dir lk) as LK_FIRST.
      destruct (tree_res treelk gm inp (lk_dir lk)) as [[inplk gmlk']|] eqn:TREERES_LK; try discriminate.
      injection RES_LK as ->.
      destruct (tree_leaves treelk gm inp (lk_dir lk)) as [|[inplk' gmlk'] q] eqn:TREELEAVES_LK; try discriminate.
      simpl in *. injection LK_FIRST as <- <-. rewrite Hpos.
      rewrite TREELEAVES_LK. auto.
    + unfold lk_result in RES_LK. rewrite Hpos in RES_LK.
      destruct (tree_res treelk gm inp (lk_dir lk)) eqn:TREERES; inversion RES_LK. subst.
      assert (tree_leaves treelk gmlk inp (lk_dir lk) = []).
      { apply leaves_indep with (gm1 := gmlk) (inp1 := inp) (dir1 := lk_dir lk).
        apply hd_error_none_nil. rewrite <- first_tree_leaf. auto. }
      simpl. rewrite Hpos, H. auto.

  - (* Lookaround failure *)
    inversion TREE_APP; subst;
      assert (treelk0 = treelk) by (eapply is_tree_determ; eauto); subst.
    { rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
    simpl. constructor.

  - (* Anchor *)
    inversion TREE_APP; subst.
    2: congruence.
    simpl. auto.

  - (* Anchor fail *)
    inversion TREE_APP; subst.
    1: congruence.
    simpl. constructor.

  - (* Backref *)
    inversion TREE_APP; subst.
    2: congruence.
    rewrite READ_BACKREF in READ_BACKREF0. injection READ_BACKREF0 as <- <-.
    simpl.
    replace (advance_input_n _ _ _) with nextinp.
    2: eauto using read_backref_success_advance.
    auto.

  - (* Backref fail *)
    inversion TREE_APP; subst.
    1: congruence.
    simpl. constructor.
Qed.

End Leaves.
