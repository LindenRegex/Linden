(** * Wrapping a regex in a fresh group *)

(* Group maps only flow through trees slot by slot, and a backreference to a
   group that is absent or still open reads the empty string. So a group that
   a regex does not define does not change its tree, whether it is absent or
   open. Wrapping the regex in that group therefore changes its first leaf
   only by recording the group's range, from the start input to the leaf. *)

From Stdlib Require Import List Lia.
From Linden Require Import Regex Chars Groups Tree Semantics Parameters GroupMapLemmas
  FunctionalUtils FlatMap Equivalence EquivLemmas.
From Warblre Require Import Base RegExpRecord.
Import ListNotations.

Section FreshGroup.
Context {params : LindenParameters} (rer : RegExpRecord).

(* Two group maps that agree outside group [g], and where [g] is not closed:
   a backreference to [g] then reads the empty string in both. *)
Definition unclosed (range : option GroupMap.range) :=
  match range with Some (GroupMap.Range _ (Some _)) => False | _ => True end.
Definition agree g gm1 gm2 := unclosed (GroupMap.find g gm1) /\ unclosed (GroupMap.find g gm2) /\
  forall n, n <> g -> GroupMap.find n gm1 = GroupMap.find n gm2.

Lemma group_update_find op pos gid gm1 gm2 :
  GroupMap.find gid gm1 = GroupMap.find gid gm2 ->
  GroupMap.find gid (GroupMap.update pos op gm1) = GroupMap.find gid (GroupMap.update pos op gm2).
Proof.
  intro SAME. destruct op as [g|g|gs]; cbn [GroupMap.update].
  - destruct (Nat.eq_dec gid g) as [->|NE];
      [now rewrite !group_map_open_find|now rewrite !group_map_open_find_other by congruence].
  - destruct (Nat.eq_dec gid g) as [->|NE]; [|now rewrite !group_map_close_find_other by congruence].
    unfold GroupMap.close. rewrite SAME. destruct (GroupMap.find g gm2) as [[start finish]|] eqn:FIND; [|now rewrite SAME, FIND].
    destruct (start <=? pos); now rewrite !gm_find_add.
  - destruct (in_dec Nat.eq_dec gid gs); [now rewrite !gm_reset_find|now rewrite !gm_reset_find_other].
Qed.

(* The groups a group action writes. *)
Definition touched op := match op with Open n | Close n => [n] | Reset gs => gs end.

Lemma update_find_untouched g op pos gm :
  ~ In g (touched op) -> GroupMap.find g (GroupMap.update pos op gm) = GroupMap.find g gm.
Proof.
  intro FRESH. destruct op; cbn in FRESH;
    [apply group_map_open_find_other|apply group_map_close_find_other|apply gm_reset_find_other]; tauto.
Qed.

Lemma agree_update g op pos gm1 gm2 : ~ In g (touched op) ->
  agree g gm1 gm2 -> agree g (GroupMap.update pos op gm1) (GroupMap.update pos op gm2).
Proof.
  intros FRESH (UNCLOSED1 & UNCLOSED2 & AGREE). unfold agree.
  rewrite !update_find_untouched by exact FRESH. split; [|split]; auto using group_update_find.
Qed.

(* Opening an unclosed group keeps it unclosed. *)
Lemma agree_open g pos gm : unclosed (GroupMap.find g gm) -> agree g gm (GroupMap.open pos g gm).
Proof.
  intro UNCLOSED. unfold agree. rewrite group_map_open_find. split; [|split]; [exact UNCLOSED|exact I|].
  intros n NE. symmetry. apply group_map_open_find_other. congruence.
Qed.

(* Each slot of a result, and its endpoint, depend only on that slot initially. *)
Lemma tree_res_slot t : forall inp dir gm1 gm2 gid, GroupMap.find gid gm1 = GroupMap.find gid gm2 ->
  option_map (fun '(last, gm) => (last, GroupMap.find gid gm)) (tree_res t gm1 inp dir) =
  option_map (fun '(last, gm) => (last, GroupMap.find gid gm)) (tree_res t gm2 inp dir).
Proof.
  induction t; intros inp dir gm1 gm2 gid SAME; cbn [tree_res option_map];
    try reflexivity; try (now rewrite SAME); eauto using group_update_find.
  - specialize (IHt1 inp dir gm1 gm2 gid SAME). unfold seqop.
    destruct (tree_res t1 gm1 inp dir), (tree_res t1 gm2 inp dir); cbn in *; try discriminate; eauto.
  - specialize (IHt1 inp (lk_dir lk) gm1 gm2 gid SAME).
    destruct (positivity lk), (tree_res t1 gm1 inp (lk_dir lk)) as [[? ?]|],
      (tree_res t1 gm2 inp (lk_dir lk)) as [[? ?]|]; cbn in *; try discriminate; eauto.
    injection IHt1. eauto.
Qed.

(* A tree leaves the groups its actions do not define untouched. *)
Lemma tree_res_keeps acts inp gm dir t g :
  is_tree rer acts inp gm dir t -> ~ In g (actions_def_groups acts) ->
  forall gm1 inp1 dir1 last gm2, tree_res t gm1 inp1 dir1 = Some (last, gm2) ->
  GroupMap.find g gm2 = GroupMap.find g gm1.
Proof.
  intros TREE FRESH gm1 inp1 dir1 last gm2 RES.
  pose proof (compute_tree_compute_tr rer acts inp gm dir) as COMPUTE.
  rewrite <- (is_tree_eq_compute_tr rer TREE) in COMPUTE.
  eapply actions_tree_no_outside_groups; eassumption.
Qed.

Lemma read_backref_agree g gm1 gm2 gid inp dir : agree g gm1 gm2 ->
  read_backref rer gm1 gid inp dir = read_backref rer gm2 gid inp dir.
Proof.
  intros (UNCLOSED1 & UNCLOSED2 & AGREE). unfold read_backref.
  destruct (Nat.eq_dec gid g) as [->|NE]; [|now rewrite AGREE].
  destruct (GroupMap.find g gm1) as [[? [?|]]|], (GroupMap.find g gm2) as [[? [?|]]|]; easy.
Qed.

Local Ltac fresh_tac := cbn [actions_def_groups def_groups touched app seq_list In] in *; rewrite ?in_app_iff in *; cbn [In] in *; tauto.

Lemma lk_result_agree g lk r t gm1 gm2 inp :
  is_tree rer [Areg r] inp gm1 (lk_dir lk) t -> ~ In g (def_groups r) -> agree g gm1 gm2 ->
  match lk_result lk t gm1 inp, lk_result lk t gm2 inp with
  | Some gmlk1, Some gmlk2 => agree g gmlk1 gmlk2 | None, None => True | _, _ => False end.
Proof.
  intros TREE FRESH AGREE. unfold lk_result.
  pose proof (fun n NE => tree_res_slot t inp (lk_dir lk) gm1 gm2 n (proj2 (proj2 AGREE) n NE)) as SLOTS.
  specialize (SLOTS (S g) ltac:(lia)) as SHAPE.
  destruct (positivity lk), (tree_res t gm1 inp (lk_dir lk)) as [[? ?]|] eqn:RES1,
    (tree_res t gm2 inp (lk_dir lk)) as [[? ?]|] eqn:RES2; cbn in SHAPE; try discriminate; try easy.
  unfold agree in *. rewrite !(tree_res_keeps _ _ _ _ _ g TREE ltac:(fresh_tac) _ _ _ _ _ RES1),
    !(tree_res_keeps _ _ _ _ _ g TREE ltac:(fresh_tac) _ _ _ _ _ RES2).
  split; [|split]; try easy. intros n NE. specialize (SLOTS n NE). cbn in SLOTS. congruence.
Qed.

Local Hint Extern 1 (~ In _ _) => fresh_tac : core.
Local Hint Extern 1 (agree _ (GroupMap.close ?pos ?gid _) _) => apply (agree_update _ (Close gid) pos) : core.
Local Hint Extern 1 (agree _ (GroupMap.open ?pos ?gid _) _) => apply (agree_update _ (Open gid) pos) : core.
(* Resets do not depend on the position. *)
Local Hint Extern 1 (agree _ (GroupMap.reset ?gs _) _) => apply (agree_update _ (Reset gs) 0) : core.

(* A tree does not depend on a group its actions do not define. *)
Lemma is_tree_agree g acts inp gm1 dir t :
  is_tree rer acts inp gm1 dir t -> ~ In g (actions_def_groups acts) ->
  forall gm2, agree g gm1 gm2 -> is_tree rer acts inp gm2 dir t.
Proof.
  induction 1; intros FRESH gm2 AGREE; subst; try destruct dir;
    try (pose proof (lk_result_agree g lk r1 treelk gm gm2 inp ltac:(eassumption) ltac:(fresh_tac) AGREE) as LK;
      rewrite ?RES_LK, ?FAIL_LK in LK; destruct (lk_result lk treelk gm2 inp) eqn:LK2; try contradiction);
    try rewrite (read_backref_agree _ _ _ _ _ _ AGREE) in *; econstructor; eauto.
Qed.

Definition close_leaf gid (l : leaf) := let '(last, groups) := l in (last, GroupMap.close (idx last) gid groups).

Lemma close_from_leaf gid l leaves : act_from_leaf rer [Aclose gid] forward l leaves -> leaves = [close_leaf gid l].
Proof.
  intro FROM. inversion FROM; subst. inversion TREE; subst. inversion TREECONT; subst. now destruct l.
Qed.

(* Appending a closing action closes the group in every leaf, preserving priority. *)
Lemma close_continuation acts inp gm gid t tc :
  is_tree rer acts inp gm forward t ->
  is_tree rer (acts ++ [Aclose gid]) inp gm forward tc ->
  tree_res tc gm inp forward = option_map (close_leaf gid) (tree_res t gm inp forward).
Proof.
  intros TREE CLOSE. rewrite !first_tree_leaf,
    (FlatMap_map _ _ _ _ (close_from_leaf gid) (leaves_concat rer inp gm forward acts [Aclose gid] tc t CLOSE TREE)).
  now destruct (tree_leaves t gm inp forward).
Qed.

(* Forward leaves are not before the input. *)
Lemma tree_res_forward t : forall gm inp last groups,
  tree_res t gm inp forward = Some (last, groups) -> idx inp <= idx last.
Proof.
  induction t; intros gm inp last groups RUN; cbn [tree_res] in RUN;
    try discriminate; try (injection RUN as <- <-; lia); eauto.
  - unfold seqop in RUN. destruct (tree_res t1 gm inp forward) as [[i g]|] eqn:LEFT; eauto.
    injection RUN as <- <-. eauto.
  - apply IHt in RUN. destruct inp as [[|? next] pref]; cbn in *; lia.
  - apply IHt in RUN. destruct inp as [next pref]. cbn in *. rewrite length_app in RUN. lia.
  - destruct (positivity lk), (tree_res t1 gm inp (lk_dir lk)) as [[? ?]|]; try discriminate; eauto.
Qed.

(* From any group map where [gid] is not closed, wrapping a regex that does
   not define [gid] in that group only records its range in the first leaf. *)
Theorem group_first_leaf r gid gm inp t w :
  ~ In gid (def_groups r) -> unclosed (GroupMap.find gid gm) ->
  is_tree rer [Areg r] inp gm forward t ->
  is_tree rer [Areg (Group gid r)] inp gm forward w ->
  match tree_res w gm inp forward, tree_res t gm inp forward with
  | Some (last, groups), Some (last', groups') => last = last' /\
      GroupMap.find gid groups = Some (GroupMap.Range (idx inp) (Some (idx last))) /\
      forall n, n <> gid -> GroupMap.find n groups = GroupMap.find n groups'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros DEFS UNCLOSED TREE W. inversion W; subst. cbn [tree_res GroupMap.update].
  pose proof (agree_open gid (idx inp) gm UNCLOSED) as AGREE.
  set (opened := GroupMap.open (idx inp) gid gm) in *.
  assert (BODY := is_tree_agree gid _ _ _ _ _ TREE ltac:(fresh_tac) opened AGREE).
  rewrite (close_continuation _ _ _ _ _ _ BODY TREECONT).
  pose proof (fun n NE => tree_res_slot t inp forward _ _ n (proj2 (proj2 AGREE) n NE)) as SLOTS.
  pose proof (SLOTS (S gid) ltac:(lia)) as ENDPOINT.
  destruct (tree_res t opened inp forward) as [[last actual]|] eqn:ACTUAL;
    destruct (tree_res t gm inp forward) as [[last' expected]|];
    injection ENDPOINT as <- _ || discriminate ENDPOINT || exact I.
  cbn [option_map]. split; [reflexivity|]. split.
  - refine (group_map_close_find_success_le _ _ _ _ _ _ (tree_res_forward _ _ _ _ _ ACTUAL)).
    rewrite (tree_res_keeps _ _ _ _ _ gid BODY ltac:(fresh_tac) _ _ _ _ _ ACTUAL).
    apply group_map_open_find.
  - intros n NE. rewrite group_map_close_find_other by congruence.
    specialize (SLOTS n NE). cbn [option_map] in SLOTS. now injection SLOTS as ->.
Qed.

End FreshGroup.
