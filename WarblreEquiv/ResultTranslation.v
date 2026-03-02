From Linden Require Import EquivDef Parameters LWParameters Groups.
From Warblre Require Import Notation.
Import Notation.
Import ZArith PeanoNat.

(** * Translating Linden matching results back into Warblre results *)

Section ResultTranslation.
  Context {params: LindenParameters}.

  Definition to_capture_range (range_opt: option GroupMap.range): option CaptureRange :=
    match range_opt with
    | None | Some (GroupMap.Range _ None) => None
    | Some (GroupMap.Range startIdx (Some endIdx)) => Some (capture_range (Z.of_nat startIdx) (Z.of_nat endIdx))
    end.

  Lemma to_capture_range_equal:
    forall lrange_opt wrange_opt,
    GroupMapMS.equiv_ranges_opt lrange_opt wrange_opt ->
    to_capture_range lrange_opt = wrange_opt.
  Proof.
    intros lrange_opt wrange_opt EQUIV.
    inversion EQUIV; subst; auto.
    inversion H; subst. simpl in *. reflexivity.
  Qed.

  Definition to_MatchState (res: option Tree.leaf) (num_groups: nat): option MatchState :=
    match res with
    | None => None
    | Some (inp, gm) =>
      let input := Chars.input_str inp in
      let endIndex := Chars.idx inp in
      let captures :=
        List.map
          (fun gid_prec => to_capture_range (GroupMap.find (S gid_prec) gm))
          (List.seq 0 num_groups)
      in
      Some (match_state input (Z.of_nat endIndex) captures)
    end.

  Inductive ms_num_groups: option MatchState -> nat -> Prop :=
  | Ms_num_groups_None: forall n, ms_num_groups None n
  | Ms_num_groups_Some: forall n ms, List.length (MatchState.captures ms) = n -> ms_num_groups (Some ms) n.

  Definition num_captures_opt (ms_opt: option MatchState): nat :=
    match ms_opt with
    | None => 0
    | Some ms => List.length (MatchState.captures ms)
    end.

  Lemma ms_num_groups_refl:
    forall ms_opt, ms_num_groups ms_opt (num_captures_opt ms_opt).
  Proof.
    intros [ms|]; simpl; constructor; auto.
  Qed.

  Lemma to_MatchState_equal:
    forall res_opt ms_opt n,
      ms_num_groups ms_opt n ->
      equiv_res res_opt ms_opt ->
      to_MatchState res_opt n = ms_opt.
  Proof.
    intros res_opt ms_opt n NUM_GROUPS EQUIV.
    inversion EQUIV; subst; auto.
    inversion NUM_GROUPS; subst. simpl.
    f_equal.
    inversion H; subst. simpl. f_equal.
    unfold GroupMapMS.equiv_groupmap_ms in H0. simpl in H0.
    clear EQUIV H NUM_GROUPS.
    apply List.nth_ext with (d := None) (d' := None).
    1: { rewrite List.length_map, List.length_seq. reflexivity. }
    rewrite List.length_map, List.length_seq. intros n IN_BOUNDS.
    set (g := fun gid_prec =>
        if gid_prec <? length cap then
          to_capture_range (GroupMap.find (S gid_prec) gm)
        else None).
    rewrite List.map_ext_in with
      (g := g).
    2: {
      clear dependent n. intros n IN_BOUNDS.
      apply List.in_seq in IN_BOUNDS. destruct IN_BOUNDS as [_ IN_BOUNDS]. simpl in IN_BOUNDS.
      unfold g. apply Nat.ltb_lt in IN_BOUNDS. rewrite IN_BOUNDS. reflexivity.
    }
    replace None with (g (length cap)) at 1.
    2: { unfold g. rewrite Nat.ltb_irrefl. reflexivity. }
    rewrite List.map_nth.
    rewrite List.seq_nth; auto. simpl.
    unfold g. apply Nat.ltb_lt in IN_BOUNDS. rewrite IN_BOUNDS.
    specialize (H0 n).
    apply to_capture_range_equal. auto.
  Qed.

  Corollary to_MatchState_equal':
    forall res_opt ms_opt,
      equiv_res res_opt ms_opt ->
      to_MatchState res_opt (num_captures_opt ms_opt) = ms_opt.
  Proof.
    intros. apply to_MatchState_equal; auto. apply ms_num_groups_refl.
  Qed.

End ResultTranslation.
