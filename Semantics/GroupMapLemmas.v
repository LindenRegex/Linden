From Linden Require Import Groups Tactics.
From Stdlib Require Import List DecidableClass Lia PeanoNat.

(** * Lemmas related to group maps *)

Lemma gm_find_empty:
  forall gid, GroupMap.find gid GroupMap.empty = None.
Proof.
  intro gid.
  destruct GroupMap.find eqn:Hfind; try reflexivity.
  exfalso. apply GroupMap.MapS.find_2 in Hfind.
  exact (GroupMap.MapS.empty_1 Hfind).
Qed.

Lemma gm_find_add:
  forall gid r gm,
    GroupMap.find gid (GroupMap.MapS.add gid r gm) = Some r.
Proof.
  intros gid r gm. apply GroupMap.MapS.find_1, GroupMap.MapS.add_1. reflexivity.
Qed.

Lemma group_map_open_find_other:
  forall gm idx gid gid',
    gid <> gid' ->
    GroupMap.find gid' (GroupMap.open idx gid gm) = GroupMap.find gid' gm.
Proof.
  intros gm idx gid gid' Hneq.
  unfold GroupMap.open.
  destruct (GroupMap.find gid' gm) as [r|] eqn:Hfindgm.
  - apply GroupMap.MapS.find_2 in Hfindgm. now apply GroupMap.MapS.find_1, GroupMap.MapS.add_2.
  - unfold GroupMap.find.
    destruct GroupMap.MapS.find as [r|] eqn:Hfindgmadd; try reflexivity.
    apply GroupMap.MapS.find_2, GroupMap.MapS.add_3, GroupMap.MapS.find_1 in Hfindgmadd. 2: assumption.
    unfold GroupMap.find in Hfindgm. congruence.
Qed.

Lemma group_map_open_find:
  forall gm idx gid,
    GroupMap.find gid (GroupMap.open idx gid gm) = Some (GroupMap.Range idx None).
Proof.
  intros gm idx gid. unfold GroupMap.open.
  apply GroupMap.MapS.find_1, GroupMap.MapS.add_1. reflexivity.
Qed.

Lemma group_map_close_find_other:
  forall gm idx gid gid',
    gid <> gid' ->
    GroupMap.find gid' (GroupMap.close idx gid gm) = GroupMap.find gid' gm.
Proof.
  intros gm idx gid gid' Hneq.
  unfold GroupMap.close.
  destruct (GroupMap.find gid gm); simpl. 2: reflexivity.
  destruct r as [startIdx endIdxOpt].
  destruct (GroupMap.find gid' gm) as [r|] eqn:Hfindgm.
  - apply GroupMap.MapS.find_2 in Hfindgm. destruct Nat.leb.
    + apply GroupMap.MapS.find_1, GroupMap.MapS.add_2; assumption.
    + apply GroupMap.MapS.find_1, GroupMap.MapS.add_2; assumption.
  - destruct (GroupMap.find gid' (if Nat.leb _ _ then _ else _)) as [r|] eqn:Hfindgmadd; try reflexivity.
    destruct Nat.leb.
    + apply GroupMap.MapS.find_2, GroupMap.MapS.add_3, GroupMap.MapS.find_1 in Hfindgmadd. 2: assumption. unfold GroupMap.find in Hfindgm. congruence.
    + apply GroupMap.MapS.find_2, GroupMap.MapS.add_3, GroupMap.MapS.find_1 in Hfindgmadd. 2: assumption. unfold GroupMap.find in Hfindgm. congruence.
Qed.

Lemma group_map_close_find_success_le:
  forall gm startIdx origEndOpt endIdx gid,
    GroupMap.find gid gm = Some (GroupMap.Range startIdx origEndOpt) ->
    startIdx <= endIdx ->
    GroupMap.find gid (GroupMap.close endIdx gid gm) = Some (GroupMap.Range startIdx (Some endIdx)).
Proof.
  intros gm startIdx origEndOpt endIdx gid Hfind Hle.
  unfold GroupMap.close. rewrite Hfind. replace (startIdx <=? endIdx) with true.
  2: { symmetry. now apply <- Nat.leb_le. }
  apply GroupMap.MapS.find_1, GroupMap.MapS.add_1. reflexivity.
Qed.

Lemma group_map_close_find_success_gt:
  forall gm startIdx origEndOpt endIdx gid,
    GroupMap.find gid gm = Some (GroupMap.Range startIdx origEndOpt) ->
    startIdx > endIdx ->
    GroupMap.find gid (GroupMap.close endIdx gid gm) = Some (GroupMap.Range endIdx (Some startIdx)).
Proof.
  intros gm startIdx origEndOpt endIdx gid Hfind Hgt.
  assert (Hnle: ~(startIdx <= endIdx)) by lia.
  rewrite <- Nat.leb_le in Hnle. rewrite Bool.not_true_iff_false in Hnle.
  unfold GroupMap.close. rewrite Hfind, Hnle.
  apply GroupMap.MapS.find_1, GroupMap.MapS.add_1. reflexivity.
Qed.

Lemma group_map_close_find_success_exists:
  forall gm startIdx origEndOpt endIdx gid,
    GroupMap.find gid gm = Some (GroupMap.Range startIdx origEndOpt) ->
    exists start' end', GroupMap.find gid (GroupMap.close endIdx gid gm) = Some (GroupMap.Range start' (Some end')).
Proof.
  intros gm startIdx origEndOpt endIdx gid H.
  decide (startIdx <= endIdx) as Hle.
  - rewrite (group_map_close_find_success_le _ _ _ _ _ H) by assumption. eexists. eexists. reflexivity.
  - rewrite (group_map_close_find_success_gt _ _ _ _ _ H) by lia. eexists. eexists. reflexivity.
Qed.

Lemma group_map_close_find_fail:
  forall gm endIdx gid,
    GroupMap.find gid gm = None ->
    GroupMap.find gid (GroupMap.close endIdx gid gm) = None.
Proof.
  intros gm endIdx gid Hfind. unfold GroupMap.close.
  rewrite Hfind. assumption.
Qed.

Inductive is_open_range: option GroupMap.range -> Prop :=
| Is_open_range: forall startIdx, is_open_range (Some (GroupMap.Range startIdx None)).

Lemma group_map_close_find_notopen:
  forall gm endIdx gid,
    ~is_open_range (GroupMap.find gid (GroupMap.close endIdx gid gm)).
Proof.
  intros gm endIdx gid.
  destruct (GroupMap.find gid gm) as [[startIdx origEndOpt]|] eqn:Hfindorig.
  - apply group_map_close_find_success_exists with (endIdx := endIdx) in Hfindorig. destruct Hfindorig as [start' [end' ->]].
    intro Habs. inversion Habs.
  - apply group_map_close_find_fail with (endIdx := endIdx) in Hfindorig. rewrite Hfindorig. intro H. inversion H.
Qed.

Lemma gm_remove_find_other:
  forall gm gid gid',
    gid' <> gid ->
    GroupMap.find gid' (GroupMap.MapS.remove gid gm) = GroupMap.find gid' gm.
Proof.
  intros gm gid gid' Hdiff.
  destruct (GroupMap.find gid' gm) as [r|] eqn:Hfindorig.
  - apply GroupMap.MapS.find_1, GroupMap.MapS.remove_2.
    1: congruence. apply GroupMap.MapS.find_2. exact Hfindorig.
  - destruct (GroupMap.find gid' (GroupMap.MapS.remove _ _)) as [r|] eqn:Hfindremoved; try reflexivity.
    apply GroupMap.MapS.find_2, GroupMap.MapS.remove_3, GroupMap.MapS.find_1 in Hfindremoved. unfold GroupMap.find in Hfindorig. congruence.
Qed.

Lemma gm_remove_find:
  forall gm gid,
    GroupMap.find gid (GroupMap.MapS.remove gid gm) = None.
Proof.
  intros gm gid.
  destruct GroupMap.find as [r|] eqn:Hfind; try reflexivity.
  exfalso. pose proof GroupMap.MapS.remove_1. unfold not in H. apply H with (x := gid) (y := gid) (m := gm) (elt := GroupMap.range).
  1: reflexivity. unfold GroupMap.MapS.In, GroupMap.MapS.Raw.PX.In.
  exists r. apply GroupMap.MapS.find_2. exact Hfind.
Qed.

Lemma gm_reset_find_other:
  forall gidl gm gid,
    ~In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = GroupMap.find gid gm.
Proof.
  intros gidl gm gid Hnotin.
  generalize dependent gm. induction gidl as [|x rtl IH] using rev_ind.
  - simpl. reflexivity.
  - intro gm. unfold GroupMap.reset. rewrite fold_left_app. simpl.
    change (fold_left _ rtl gm) with (GroupMap.reset rtl gm).
    assert (Hgidnotx: gid <> x). {
      rewrite in_app_iff in Hnotin. simpl in *. symmetry. tauto.
    }
    specialize_prove IH. {
      intro Habs. rewrite in_app_iff in Hnotin. tauto.
    }
    specialize (IH gm).
    transitivity (GroupMap.find gid (GroupMap.reset rtl gm)). 2: exact IH.
    now apply gm_remove_find_other.
Qed.

Lemma gm_reset_find:
  forall gidl gm gid,
    In gid gidl -> GroupMap.find gid (GroupMap.reset gidl gm) = None.
Proof.
  intros gidl gm gid Hin.
  induction gidl as [|x rtl IH] using rev_ind.
  - inversion Hin.
  - apply in_app_or in Hin. destruct Hin as [Hinrtl | Heqx].
    + unfold GroupMap.reset. rewrite fold_left_app. simpl. change (fold_left _ rtl gm) with (GroupMap.reset rtl gm).
      decide (gid = x) as Hgidx.
      * subst gid. apply gm_remove_find.
      * rewrite gm_remove_find_other by assumption. auto.
    + simpl in Heqx. destruct Heqx as [Heqx|[]].
      unfold GroupMap.reset. rewrite fold_left_app. simpl. change (fold_left _ rtl gm) with (GroupMap.reset rtl gm).
      subst x. apply gm_remove_find.
Qed.

Inductive range_dir_valid: option GroupMap.range -> Prop :=
| Range_dir_valid_None: range_dir_valid None
| Range_dir_valid_open: forall startIdx, range_dir_valid (Some (GroupMap.Range startIdx None))
| Range_dir_valid_closed: forall startIdx endIdx,
    startIdx <= endIdx -> range_dir_valid (Some (GroupMap.Range startIdx (Some endIdx))).

Definition gm_valid (gm: GroupMap.t): Prop :=
  forall gid: group_id, range_dir_valid (GroupMap.find gid gm).

Inductive gm_opt_valid : option GroupMap.t -> Prop :=
| Gm_None_valid: gm_opt_valid None
| Gm_Some_valid: forall gm, gm_valid gm -> gm_opt_valid (Some gm).

Lemma empty_gm_valid: gm_valid GroupMap.empty.
Proof.
  intro gid. rewrite gm_find_empty. constructor.
Qed.

Lemma gm_open_valid:
  forall gm gid idx,
    gm_valid gm -> gm_valid (GroupMap.open idx gid gm).
Proof.
  intros gm gid idx Hvalid gid'.
  decide (gid' = gid).
  - subst gid'. rewrite group_map_open_find. constructor.
  - rewrite group_map_open_find_other. 2: congruence. apply Hvalid.
Qed.

Lemma gm_close_valid:
  forall gm gid idx,
    gm_valid gm -> gm_valid (GroupMap.close idx gid gm).
Proof.
  intros gm gid idx Hvalid gid'.
  decide (gid' = gid).
  - subst gid'. unfold GroupMap.close.
    destruct (GroupMap.find gid gm) as [[startIdx endIdxOpt]|] eqn:Hfindorig; simpl.
    + destruct Nat.leb eqn:Hle; simpl.
      * apply Nat.leb_le in Hle. rewrite gm_find_add. constructor. assumption.
      * apply Nat.leb_nle in Hle. rewrite gm_find_add. constructor. lia.
    + rewrite Hfindorig. constructor.
  - rewrite group_map_close_find_other. 2: congruence. apply Hvalid.
Qed.

Lemma gm_reset_valid:
  forall gm gidl,
    gm_valid gm -> gm_valid (GroupMap.reset gidl gm).
Proof.
  intros gm gidl Hvalid gid.
  destruct (in_dec Nat.eq_dec gid gidl) as [Hin | Hnotin].
  - rewrite gm_reset_find by assumption. constructor.
  - rewrite gm_reset_find_other by assumption. apply Hvalid.
Qed.

Lemma gm_reset_undefined:
  forall gidl gm,
    (forall gid, In gid gidl -> GroupMap.find gid gm = None) ->
    GroupMap.reset gidl gm = gm.
Proof.
  intros gidl gm H.
  apply GroupMap.MapS.Equal_eq. intros gid.
  destruct (in_dec Nat.eq_dec gid gidl) as [Hin|Hnotin].
  - rewrite gm_reset_find; auto. symmetry. auto.
  - apply gm_reset_find_other. auto.
Qed.

(** * Reset Equivalence *)
(* For Rewriting results, we need to characterize group_sets which produce the same
   group map after being reset. This will allows us to equate two regexes with a
   diffreent list of reset group ids (def_groups), and yet ensure the equivalence
   is still contextual when the context contains a quantifier with a reset. *)

(* group sets with the same elements, regardless of orde or duplicates, are equivalent *)
Definition groups_equiv (l1 l2: group_set) : Prop :=
  incl l1 l2 /\ incl l2 l1.

Lemma groups_equiv_refl: forall l, groups_equiv l l.
Proof. intros l. split; apply incl_refl. Qed.

Lemma groups_equiv_sym: forall l1 l2, groups_equiv l1 l2 -> groups_equiv l2 l1.
Proof. intros l1 l2 [H1 H2]. split; auto. Qed.

Lemma groups_equiv_trans:
  forall l1 l2 l3, groups_equiv l1 l2 -> groups_equiv l2 l3 -> groups_equiv l1 l3.
Proof.
  intros l1 l2 l3 [H12 H21] [H23 H32].
  split; eapply incl_tran; eauto.
Qed.

#[global] Instance groups_equiv_Equivalence: RelationClasses.Equivalence groups_equiv :=
  { Equivalence_Reflexive := groups_equiv_refl;
    Equivalence_Symmetric := groups_equiv_sym;
    Equivalence_Transitive := groups_equiv_trans }.

Lemma groups_equiv_app:
  forall l1 l1' l2 l2',
    groups_equiv l1 l1' -> groups_equiv l2 l2' ->
    groups_equiv (l1 ++ l2) (l1' ++ l2').
Proof.
  intros l1 l1' l2 l2' [H1 H1'] [H2 H2'].
  split; apply incl_app_app; auto.
Qed.

Lemma groups_equiv_cons:
  forall g l l', groups_equiv l l' -> groups_equiv (g :: l) (g :: l').
Proof.
  intros g l l' [H H']. split; intros x [->|Hx]; simpl; auto.
Qed.

(* two resets of equivalent group sets produce the same group map *)
Lemma reset_groups_equiv_same:
  forall l1 l2 gm,
    groups_equiv l1 l2 ->
    GroupMap.reset l1 gm = GroupMap.reset l2 gm.
Proof.
  intros l1 l2 gm [H1 H2]. apply GroupMap.MapS.Equal_eq. intros gid.
  destruct (in_dec Nat.eq_dec gid l1) as [Hin1|Hnotin1].
  - rewrite !gm_reset_find; auto.
  - rewrite !gm_reset_find_other; auto.
Qed.

(* proves group equivalence for lists built with app and cons *)
Ltac solve_groups_equiv :=
  unfold groups_equiv, incl; split; intros ?; rewrite ?in_app_iff; simpl; tauto.
