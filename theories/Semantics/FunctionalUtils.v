From Stdlib Require Import List.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import Regex Chars Groups Tree Semantics FunctionalSemantics ComputeIsTree Parameters.
Import ListNotations.

(** * Some utilities related to the functional version of the semantics *)

Section Utilities.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Definition compute_tr (act: actions) (inp: input) (gm: group_map) (dir: Direction): tree :=
    match compute_tree rer act inp gm dir (S (actions_fuel act inp dir)) with
    | Some tr => tr
    | None => Mismatch
    end.

  Lemma compute_tr_is_tree {actions i gm dir} :
    is_tree rer actions i gm dir (compute_tr actions i gm dir).
  Proof.
    unfold compute_tr.
    pose proof functional_terminates rer actions i gm dir _ (PeanoNat.Nat.lt_succ_diag_r _).
    destruct compute_tree eqn:Htr; try contradiction.
    eauto using compute_is_tree.
  Qed.

  Lemma compute_tr_reg_is_tree {r i gm dir} :
    is_tree rer [Areg r] i gm dir (compute_tr [Areg r] i gm dir).
  Proof.
    eauto using compute_tr_is_tree.
  Qed.

  Theorem is_tree_productivity: forall acts inp gm dir,
    exists tree, is_tree rer acts inp gm dir tree.
  Proof. eexists. apply compute_tr_is_tree. Qed.

  Lemma is_tree_eq_compute_tr {actions i gm dir} :
    forall {tr}, is_tree rer actions i gm dir tr -> tr = compute_tr actions i gm dir.
  Proof.
    eauto using is_tree_determ, compute_tr_is_tree.
  Qed.

  Lemma compute_tr_eq_is_tree {actions i gm dir} :
    forall {tr}, tr = compute_tr actions i gm dir -> is_tree rer actions i gm dir tr.
  Proof.
    intros. subst. apply compute_tr_is_tree.
  Qed.

  Lemma compute_tr_ind {actions i gm dir P} :
    P (compute_tr actions i gm dir) ->
    forall {tr}, is_tree rer actions i gm dir tr -> P tr.
  Proof.
    intros HP tr Htr.
    erewrite is_tree_determ with (1 := Htr) (2 := compute_tr_is_tree).
    assumption.
  Qed.

  Lemma compute_tr_reg_ind {r i gm dir P} :
    P (compute_tr [Areg r] i gm dir) ->
    forall {tr}, is_tree rer [Areg r] i gm dir tr -> P tr.
  Proof.
    intros; eapply compute_tr_ind; eauto.
  Qed.

  Definition compute_tr_unfold act inp gm dir :=
    match act with
    (* tree_done *)
    | [] => Match
    (* tree_check, tree_check_fail *)
    | Acheck strcheck :: cont =>
        if StrictSuffix.is_strict_suffix inp strcheck dir then
          let treecont := compute_tr cont inp gm dir in
          Progress treecont
        else Mismatch
    (* tree_close *)
    | Aclose gid :: cont =>
        let treecont := compute_tr cont inp (GroupMap.close (idx inp) gid gm) dir in
        GroupAction (Close gid) treecont
    (* tree_epsilon *)
    | Areg Epsilon::cont => compute_tr cont inp gm dir
    (* tree_char, tree_char_fail *)
    | Areg (Regex.Character cd)::cont =>
        match read_char rer cd inp dir with
        | Some (c, nextinp) =>
            let treecont := compute_tr cont nextinp gm dir in
            Read c treecont
        | None => Mismatch
        end
    (* tree_disj *)
    | Areg (Disjunction r1 r2)::cont =>
        let t1 := compute_tr (Areg r1 :: cont) inp gm dir in
        let t2 := compute_tr (Areg r2 :: cont) inp gm dir in
        Choice t1 t2
    (* tree_sequence *)
    | Areg (Sequence r1 r2)::cont =>
        compute_tr (seq_list r1 r2 dir ++ cont) inp gm dir
    (* tree_quant_forced *)
    | Areg (Quantified greedy (S min) delta r1)::cont =>
        let gidl := def_groups r1 in
        let titer := compute_tr (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp (GroupMap.reset gidl gm) dir in
        GroupAction (Reset gidl) titer
    (* tree_quant_done *)
    | Areg (Quantified greedy 0 (NoI.N 0) r1)::cont =>
        compute_tr cont inp gm dir
    (* tree_quant_free *)
    | Areg (Quantified greedy 0 delta r1)::cont =>
        let gidl := def_groups r1 in
        let titer := compute_tr (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir in
        let tskip := compute_tr cont inp gm dir in
        greedy_choice greedy (GroupAction (Reset gidl) titer) tskip
    (* tree_group *)
    | Areg (Group gid r1)::cont =>
        let treecont := compute_tr (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir in
        GroupAction (Open gid) treecont
    (* tree_lk, tree_lk_fail *)
    | Areg (Lookaround lk r1)::cont =>
        let treelk := compute_tr [Areg r1] inp gm (lk_dir lk) in
        match lk_result lk treelk gm inp with
        | Some gmlk =>
            let treecont := compute_tr cont inp gmlk dir in
            LK lk treelk treecont
        | None =>  LKFail lk treelk
        end
    (* tree_anchor, tree_anchor_fail *)
    | Areg (Anchor a)::cont =>
        if anchor_satisfied rer a inp then
          let treecont := compute_tr cont inp gm dir in
          AnchorPass a treecont
        else
          Mismatch
    (* tree_backref, tree_backref_fail *)
    | Areg (Backreference gid)::cont =>
        match read_backref rer gm gid inp dir with
        | Some (br_str, nextinp) =>
            let tcont := compute_tr cont nextinp gm dir in
            ReadBackRef br_str tcont
        | None =>
            Mismatch
        end
    end.

  Lemma compute_tree_None_compute_tr act inp gm dir fuel:
    compute_tree rer act inp gm dir fuel <> None ->
    compute_tree rer act inp gm dir fuel = Some (compute_tr act inp gm dir).
  Proof.
    intros HNone; destruct compute_tree eqn:Htr in *; [ | congruence ].
    apply compute_is_tree in Htr.
    f_equal; eauto using is_tree_determ, compute_tr_is_tree.
  Qed.

  Lemma compute_tree_compute_tr act inp gm dir:
    let fuel := S (actions_fuel act inp dir) in
    compute_tree rer act inp gm dir fuel = Some (compute_tr act inp gm dir).
  Proof.
    unfold compute_tr.
    pose proof functional_terminates rer act inp gm dir _ (PeanoNat.Nat.lt_succ_diag_r _).
    destruct compute_tree; congruence.
  Qed.

  Arguments compute_tree params rer !act inp gm dir fuel.

  Lemma compute_tr_rw act inp gm dir:
    compute_tr act inp gm dir = compute_tr_unfold act inp gm dir.
  Proof.
    unfold compute_tr.
    pose proof compute_tree_compute_tr act inp gm dir as HnotNone.
    destruct act as [|act cont]; simpl in *.
    { reflexivity. }
    destruct act.
    - destruct r.
      + set (treecont_opt := compute_tree rer cont inp gm dir _) in *.
        assert (treecont_opt <> None). { destruct treecont_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold treecont_opt in H.
        rewrite H in *. reflexivity.
      + destruct read_char as [[c nextinp]|]. 2: reflexivity.
        set (treecont_opt := compute_tree rer cont nextinp gm dir _) in *.
        assert (treecont_opt <> None). { destruct treecont_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold treecont_opt in H.
        rewrite H in *. reflexivity.
      + set (t1_opt := compute_tree rer (Areg r1 :: cont) inp gm dir (regex_fuel (Disjunction r1 r2) inp dir + actions_fuel cont inp dir)) in *.
        assert (t1_opt <> None). { destruct t1_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold t1_opt in H.
        rewrite H in *.
        set (t2_opt := compute_tree rer (Areg r2 :: cont) inp gm dir (regex_fuel (Disjunction r1 r2) inp dir + actions_fuel cont inp dir)) in *.
        assert (t2_opt <> None). { destruct t2_opt; discriminate. }
        apply compute_tree_None_compute_tr in H0. fold t2_opt in H0.
        rewrite H0 in *. reflexivity.
      + set (tr_opt := compute_tree rer _ inp gm dir _) in *.
        assert (tr_opt <> None). { destruct tr_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold tr_opt in H.
        rewrite H in *. reflexivity.
      + destruct min as [|min'].
        * destruct delta as [[|n']|].
          -- set (tr_opt := compute_tree rer cont inp gm dir _) in *.
             assert (tr_opt <> None). { destruct tr_opt; discriminate. }
             apply compute_tree_None_compute_tr in H. fold tr_opt in H.
             rewrite H in *. reflexivity.
          -- set (titer_opt := compute_tree rer _ inp _ dir _) in *.
             assert (titer_opt <> None). { destruct titer_opt; discriminate. }
             apply compute_tree_None_compute_tr in H. fold titer_opt in H.
             rewrite H in *.
             set (tskip_opt := compute_tree rer cont inp gm dir _) in *.
             assert (tskip_opt <> None). { destruct tskip_opt; discriminate. }
             apply compute_tree_None_compute_tr in H0. fold tskip_opt in H0.
             rewrite H0 in *. reflexivity.
          -- set (titer_opt := compute_tree rer _ inp _ dir _) in *.
             assert (titer_opt <> None). { destruct titer_opt; discriminate. }
             apply compute_tree_None_compute_tr in H. fold titer_opt in H.
             rewrite H in *.
             set (tskip_opt := compute_tree rer cont inp gm dir _) in *.
             assert (tskip_opt <> None). { destruct tskip_opt; discriminate. }
             apply compute_tree_None_compute_tr in H0. fold tskip_opt in H0.
             rewrite H0 in *. reflexivity.
        * set (titer_opt := compute_tree rer _ inp _ dir _) in *.
          assert (titer_opt <> None). { destruct titer_opt; discriminate. }
          apply compute_tree_None_compute_tr in H. fold titer_opt in H.
          rewrite H in *. reflexivity.
      + set (treelk_opt := compute_tree rer [Areg r] inp gm _ _) in *.
        assert (treelk_opt <> None). { destruct treelk_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold treelk_opt in H.
        rewrite H in *.
        destruct lk_result. 2: reflexivity.
        set (treecont_opt := compute_tree rer cont inp g dir _) in *.
        assert (treecont_opt <> None). { destruct treecont_opt; discriminate. }
        apply compute_tree_None_compute_tr in H0. fold treecont_opt in H0.
        rewrite H0 in *. reflexivity.
      + set (treecont_opt := compute_tree rer _ inp _ dir _) in *.
        assert (treecont_opt <> None). { destruct treecont_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold treecont_opt in H.
        rewrite H in *. reflexivity.
      + destruct anchor_satisfied. 2: reflexivity.
        set (treecont_opt := compute_tree rer cont inp gm dir _) in *.
        assert (treecont_opt <> None). { destruct treecont_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold treecont_opt in H.
        rewrite H in *. reflexivity.
      + destruct read_backref as [[br_str nextinp]|]. 2: reflexivity.
        set (tcont_opt := compute_tree rer cont nextinp gm dir _) in *.
        assert (tcont_opt <> None). { destruct tcont_opt; discriminate. }
        apply compute_tree_None_compute_tr in H. fold tcont_opt in H.
        rewrite H in *. reflexivity.
    - set (treecont_opt := compute_tree rer cont inp gm dir _) in *.
      destruct StrictSuffix.is_strict_suffix.
      2: reflexivity.
      assert (treecont_opt <> None). { destruct treecont_opt; discriminate. }
      apply compute_tree_None_compute_tr in H. fold treecont_opt in H.
      rewrite H in *. reflexivity.
    - set (treecont_opt := compute_tree rer cont inp _ dir _) in *.
      assert (treecont_opt <> None). { destruct treecont_opt; discriminate. }
      apply compute_tree_None_compute_tr in H. fold treecont_opt in H.
      rewrite H in *. reflexivity.
  Qed.

  Definition compute_tr_dep (act: actions) (inp: input) (gm: group_map) (dir: Direction): tree :=
    let fuel := S (actions_fuel act inp dir) in
    let opt := compute_tree rer act inp gm dir fuel in
    match opt as o return opt = o -> tree with
    | Some tr =>
        fun _ => tr
    | None =>
        fun Heq => False_rect _ (functional_terminates rer act inp gm dir fuel (PeanoNat.Nat.lt_succ_diag_r _) Heq)
    end eq_refl.

  Lemma compute_tr_dep_is_tree {actions i gm dir} :
    is_tree rer actions i gm dir (compute_tr_dep actions i gm dir).
  Proof.
    unfold compute_tr_dep.
    set (functional_terminates _ _ _ _ _ _ _) as fn; clearbody fn.
    destruct compute_tree eqn:Htr; try contradiction.
    eauto using compute_is_tree.
  Qed.

  (* LATER: we could also try to define `compute_tr_dep_unfold` like `compute_tr_unfold` *)
  Lemma compute_tr_dep_reg_is_tree {r i gm dir} :
    is_tree rer [Areg r] i gm dir (compute_tr_dep [Areg r] i gm dir).
  Proof.
    eauto using compute_tr_dep_is_tree.
  Qed.
End Utilities.

Arguments compute_tr_unfold: simpl nomatch.

Ltac compute_tr_step :=
  match goal with
  | [  |- context[compute_tr ?act ?i ?gm ?dir] ] =>
      (* With `simpl nomatch`, progress simpl guarantees that we
                  rewrite only compute_tr instances that are unfoldable. *)
      rewrite (compute_tr_rw act i gm dir); progress simpl
  | _ => rewrite !app_nil_r || (progress unfold seq_list)
  end.

Ltac compute_tr_simpl :=
  repeat compute_tr_step.

Lemma EqDec_eqb {T} `{EqDec T} (t0 t1: T) : t0 = t1 -> EqDec.eqb t0 t1 = true.
Proof. apply EqDec.inversion_true. Qed.

Lemma EqDec_neqb {T} `{EqDec T} (t0 t1: T) : t0 <> t1 -> EqDec.eqb t0 t1 = false.
Proof. apply EqDec.inversion_false. Qed.

Ltac compute_tr_cbv :=
  unfold compute_tr;
  repeat (simpl; unfold char_match; simpl; try ((rewrite EqDec_eqb + rewrite EqDec_neqb); [ | congruence ])).
