Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars.
From Linden Require Import Tree.
From Linden Require Import NumericLemmas.
From Linden Require Import Groups Semantics.
From Linden Require Import StrictSuffix.
From Linden Require Import Parameters.
From Warblre Require Import Numeric Base RegExpRecord.

From Stdlib Require Import Lia DecidableClass.

(** * Functional version of the inductive semantics *)

Section FunctionalSemantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).



  (** * Total input  *)

  (* When computing fuel, what's the worst possible string we could have to match in a given direction *)
  (* This is used for lookarounds fuel: since they may change direction, we can't predict ahead of time  *)
  (* how much string they'll get to work with from the current input *)
  Definition worst_input (inp:input) (dir:Direction) : input :=
    match inp with
    | Input next pref =>
        match dir with
        | forward => Input ((rev pref) ++ next) []
        | backward => Input [] ((rev next) ++ pref)
        end
    end.

  Lemma advance_same_worst:
    forall nextinp inp d,
      advance_input inp d = Some nextinp ->
      (forall dir, worst_input nextinp dir = worst_input inp dir).
  Proof.
    intros nextinp inp d H.
    destruct inp as [next pref]. destruct d; simpl in H.
    + destruct next; try discriminate. injection H as <-. intros []; simpl.
      * rewrite <- app_assoc. simpl. reflexivity.
      * rewrite <- app_assoc. simpl. reflexivity.
    + destruct pref; try discriminate. injection H as <-. intros []; simpl.
      * rewrite <- app_assoc. simpl. reflexivity.
      * rewrite <- app_assoc. simpl. reflexivity.
  Qed.

  Lemma suffix_same_worst:
    forall inp1 inp2 d,
      strict_suffix inp1 inp2 d ->
      (forall dir, worst_input inp1 dir = worst_input inp2 dir).
  (* suffixes have the same total string *)
  Proof.
    intros inp1 inp2 d Hss. induction Hss.
    - apply advance_same_worst with (d := dir). auto.
    - pose proof advance_same_worst _ _ _ H. intro dir'.
      rewrite H0. apply IHHss.
  Qed.

  Lemma worst_input_suffix:
    forall inp worst dir,
      worst_input inp dir = worst ->
      worst = inp \/ strict_suffix inp worst dir.
  Proof.
    intros [next pref] [worstnext worstpref] []; simpl.
    - (* Forward *)
      intro H. injection H as <- <-.
      destruct pref as [|x pref'].
      + left. reflexivity.
      + right. apply ss_fwd_diff.
        exists (rev (x :: pref')). split; [|split].
        * simpl. now destruct rev.
        * reflexivity.
        * rewrite rev_involutive, app_nil_r. reflexivity.
    - (* Backward *)
      intro H. injection H as <- <-.
      destruct next as [|x next'].
      + left. reflexivity.
      + right. apply ss_bwd_diff.
        exists (x :: next'). split; [|split].
        * easy.
        * rewrite app_nil_r. reflexivity.
        * reflexivity.
  Qed.


  (** * Computing the measure  *)

  (* The predecessor of a non_negative or infinite delta of a quantifier *)
  Definition noi_pred (noi:non_neg_integer_or_inf) : non_neg_integer_or_inf :=
    match noi with
    | NoI.N x => NoI.N (x - 1)
    | NoI.Inf => NoI.Inf
    end.


  (* The maximum number of iterations for a quantifier *)
  Definition max_iter (inp:input) (dir:Direction): nat :=
    1 + length (current_str inp dir).

  Lemma strict_suffix_max_iter:
    forall inp1 inp2 dir,
      strict_suffix inp1 inp2 dir ->
      max_iter inp1 dir < max_iter inp2 dir.
  Proof.
    intros inp1 inp2 dir H. apply strict_suffix_current in H.
    unfold max_iter. lia.
  Qed.

  Lemma advance_max_iter:
    forall inp nextinp dir,
      advance_input inp dir = Some nextinp ->
      max_iter inp dir = S (max_iter nextinp dir).
  Proof.
    intros [next pref] nextinp [|] H; simpl in H.
    - destruct next; inversion H. auto.
    - destruct pref; inversion H. auto.
  Qed.

  Lemma no_advance_max_iter:
    forall inp dir,
      advance_input inp dir = None ->
      max_iter inp dir = 1.
  Proof.
    intros [next pref] dir H. unfold max_iter. destruct dir; simpl in *.
    - destruct next; inversion H. auto.
    - destruct pref; inversion H. auto.
  Qed.


  (* An upper bound on the number of actions required for a regex *)
  Fixpoint regex_fuel (r:regex) (inp:input) (dir:Direction) : nat :=
    match r with
    | Epsilon => 1
    | Regex.Character _ => 1
    | Disjunction r1 r2 =>
        1 + (regex_fuel r1 inp dir) + (regex_fuel r2 inp dir)
    | Sequence r1 r2 =>
        1 + (regex_fuel r1 inp dir) + (regex_fuel r2 inp dir)
    | Quantified b min delta r1 =>
        let rfuel := regex_fuel r1 inp dir in
        (2 + rfuel) * (min + max_iter inp dir)
    | Lookaround lk r1 =>
        2 + (regex_fuel r1 (worst_input inp (lk_dir lk)) (lk_dir lk))
    | Group _ r1 =>
        2 + (regex_fuel r1 inp dir)
    | Anchor _ => 1
    | Backreference _ => 1
    end.

  Fixpoint actions_fuel (act:actions) (inp:input) (dir:Direction) : nat :=
    match act with
    | [] => 1
    | (Areg r)::l => (regex_fuel r inp dir) + (actions_fuel l inp dir)
    | (Acheck inpcheck)::l =>
        (* advance_input is the next closest possible input after having passed a check *)
        match (advance_input inpcheck dir) with
        | Some nextinp => 1 + actions_fuel l nextinp dir
        | None => 0
        end
    | (Aclose _):: l => 1 + (actions_fuel l inp dir)
    end.

  (** * Monotony Lemmas  *)

  Lemma regex_monoton:
    forall r dir inp1 inp2,
      strict_suffix inp1 inp2 dir ->
      regex_fuel r inp1 dir <= regex_fuel r inp2 dir.
  Proof.
    intros r dir inp1 inp2 H.
    induction r; simpl; try lia.
    - apply strict_suffix_max_iter in H as MAX.
      apply PeanoNat.Nat.add_le_mono; try lia.
      apply PeanoNat.Nat.add_le_mono; try lia.
      apply PeanoNat.Nat.mul_le_mono; try lia.
    - apply suffix_same_worst with (dir:=lk_dir lk) in H as WORST.
      rewrite WORST. lia.
  Qed.

  Lemma actions_monoton:
    forall act dir inp1 inp2,
      strict_suffix inp1 inp2 dir ->
      actions_fuel act inp1 dir <= actions_fuel act inp2 dir.
  Proof.
    intros act dir inp1 inp2 H. induction act.
    { simpl. lia. }
    destruct a.
    - simpl. apply regex_monoton with (r:=r) in H as R. lia.
    - simpl. destruct (advance_input i dir) eqn:ADV; try lia.
    - simpl. lia.
  Qed.

  (** * Termination Lemmas  *)
  (* Proving, for each recursive call, that the measure strictly decreases *)

  Lemma check_termination:
    forall cont inp strcheck dir,
      strict_suffix inp strcheck dir ->
      actions_fuel cont inp dir < actions_fuel (Acheck strcheck :: cont) inp dir.
  Proof.
    intros cont inp strcheck dir SS.
    simpl. destruct (advance_input strcheck dir) eqn:ADV.
    2: { exfalso. eapply strict_no_advance; eauto. }
    generalize (advance_suffix _ _ _ _ SS ADV). intros [INPEQ | SS2].
    - subst. lia.
    - generalize (actions_monoton cont _ _ _ SS2). intros H. lia.
  Qed.

  Lemma close_termination:
    forall cont inp dir gid,
      actions_fuel cont inp dir < actions_fuel (Aclose gid :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma epsilon_termination:
    forall cont inp dir,
      actions_fuel cont inp dir < actions_fuel (Areg Epsilon :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma character_termination:
    forall cont inp dir cd c nextinp,
      read_char rer cd inp dir = Some (c, nextinp) ->
      actions_fuel cont nextinp dir < actions_fuel (Areg (Regex.Character cd) :: cont) inp dir.
  Proof.
    intros cont inp dir cd c nextinp H. apply read_char_suffix in H. simpl.
    apply actions_monoton with (act:=cont) in H. lia.
  Qed.

  Lemma disjunction_left_termination:
    forall cont inp dir r1 r2,
      actions_fuel (Areg r1 :: cont) inp dir < actions_fuel (Areg (Disjunction r1 r2) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma disjunction_right_termination:
    forall cont inp dir r1 r2,
      actions_fuel (Areg r2 :: cont) inp dir < actions_fuel (Areg (Disjunction r1 r2) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma sequence_termination:
    forall cont inp dir r1 r2,
      actions_fuel (seq_list r1 r2 dir ++ cont) inp dir < actions_fuel (Areg (Sequence r1 r2) :: cont) inp dir.
  Proof. intros. destruct dir; simpl; lia. Qed.

  Lemma quant_forced_termination:
    forall cont inp dir r1 min delta greedy,
      actions_fuel (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp dir <
        actions_fuel (Areg (Quantified greedy (S min) delta r1) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma quant_done_termination:
    forall cont inp dir r1 greedy,
      actions_fuel cont inp dir < actions_fuel (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma quant_free_skip_termination:
    forall cont inp dir r1 greedy delta,
      actions_fuel cont inp dir < actions_fuel (Areg (Quantified greedy 0 delta r1)::cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma le_lt_S:
    forall n m,
      n <= m -> n < S m.
  Proof. lia. Qed.

  Lemma quant_free_iter_termination:
    forall cont inp dir r1 greedy delta,
      actions_fuel (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp dir <
        actions_fuel (Areg (Quantified greedy 0 delta r1) :: cont) inp dir.
  Proof.
    intros cont inp dir r1 greedy delta.
    destruct (advance_input inp dir) eqn:ADV; simpl; rewrite ADV.
    (* it's not possible to pass the check *)
    2: { apply no_advance_max_iter in ADV. rewrite ADV. lia. }
    apply read_suffix in ADV as SS.
    apply regex_monoton with (r:=r1) in SS as SMALLER_R.
    apply actions_monoton with (act:=cont) in SS as SMALLER_CONT.
    apply advance_current_plus_one in ADV as SMALLER_LEN.
    rewrite SMALLER_LEN.
    apply advance_max_iter in ADV as SMALLER_MAX.
    rewrite SMALLER_MAX.
    assert (RMAX: regex_fuel r1 i dir * max_iter i dir <= regex_fuel r1 inp dir * max_iter i dir).
    { apply GroupId.mul_le_mono_r. auto. }
    lia.
    (* used before lia worked, to inspect the measure calculation *)
    (* pose (R2 := regex_fuel r1 inp dir). fold R2. fold R2 in SMALLER_R. *)
    (* pose (R1 := regex_fuel r1 i dir). fold R1. fold R1 in SMALLER_R. *)
    (* pose (ACT2 := actions_fuel cont inp dir). fold ACT2. fold ACT2 in SMALLER_CONT. *)
    (* pose (ACT1 := actions_fuel cont i dir). fold ACT1. fold ACT1 in SMALLER_CONT. *)
    (* pose (MAX := max_iter i dir). fold MAX. fold MAX in SMALLER_MAX. *)
    (* pose (LEN := length (current_str i dir)). fold LEN. *)
  Qed.

  Lemma group_termination:
    forall cont inp dir r1 gid,
      actions_fuel (Areg r1 :: Aclose gid :: cont) inp dir < actions_fuel (Areg (Group gid r1) :: cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma lk_after_termination:
    forall cont inp dir lk r1,
      actions_fuel cont inp dir < actions_fuel (Areg (Lookaround lk r1)::cont) inp dir.
  Proof. intros. simpl. lia. Qed.

  Lemma lk_lk_termination:
    forall cont inp dir lk r1,
      actions_fuel [Areg r1] inp (lk_dir lk) < actions_fuel (Areg (Lookaround lk r1)::cont) inp dir.
  Proof.
    intros. simpl.
    destruct (worst_input_suffix inp (worst_input inp (lk_dir lk)) (lk_dir lk) eq_refl).
    - rewrite H. lia.
    - pose proof regex_monoton r1 (lk_dir lk) inp (worst_input inp (lk_dir lk)) H. lia.
  Qed.

  Lemma advance_input_n_0:
    forall inp dir, advance_input_n inp 0 dir = inp.
  Proof.
    intros [next pref] dir. simpl. now destruct dir.
  Qed.

  (* May be used to simplify the lemma right after this one *)
  Lemma skipn_cons_length {A}:
    forall n (l: list A) x q,
      skipn n l = x :: q ->
      length l > n.
  Proof.
    intros n l x q Hskipn.
    pose proof firstn_skipn n l. rewrite Hskipn in H.
    pose proof skipn_length n l. rewrite Hskipn in H0.
    simpl in H0. lia.
  Qed.

  Lemma advance_input_n_succ_success:
    forall inp n dir inpn inpn_adv,
      inpn = advance_input_n inp n dir ->
      advance_input inpn dir = Some inpn_adv ->
      advance_input_n inp (S n) dir = inpn_adv.
  Proof.
    intros [next pref] n [] inpn inpn_adv Heqinpn Hadv.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n next) as [|h next'] eqn:Hskipn; try discriminate.
      injection Hadv as <-.
      pose proof firstn_skipn n next. rewrite Hskipn in H. rewrite <- H.
      pose proof skipn_length n next. rewrite Hskipn in H0.
      assert (Hlen: length (firstn n next) = n). {
        simpl in *.
        assert (length next > n) by lia.
        apply firstn_length_le. lia.
      }
      f_equal.
      + rewrite skipn_app. rewrite skipn_all2 by lia.
        replace (S n - length _) with 1 by lia. reflexivity.
      + rewrite app_comm_cons. f_equal. do 2 rewrite firstn_app.
        rewrite firstn_all2 by lia. replace (S n - length _) with 1 by lia. simpl.
        replace (n - length _) with 0 by lia. simpl.
        rewrite <- Hlen at 2. rewrite firstn_all. rewrite rev_app_distr. simpl.
        rewrite app_nil_r. reflexivity.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n pref) as [|h pref'] eqn:Hskipn; try discriminate.
      injection Hadv as <-.
      pose proof firstn_skipn n pref. rewrite Hskipn in H. rewrite <- H.
      pose proof skipn_length n pref. rewrite Hskipn in H0.
      assert (Hlen: length (firstn n pref) = n). {
        simpl in *.
        assert (length pref > n) by lia.
        apply firstn_length_le. lia.
      }
      f_equal.
      + rewrite app_comm_cons. f_equal. do 2 rewrite firstn_app.
        rewrite firstn_all2 by lia. replace (S n - length _) with 1 by lia. simpl.
        replace (n - length _) with 0 by lia. simpl.
        rewrite <- Hlen at 2. rewrite firstn_all. rewrite rev_app_distr. simpl.
        rewrite app_nil_r. reflexivity.
      + rewrite skipn_app. rewrite skipn_all2 by lia.
        replace (S n - length _) with 1 by lia. reflexivity.
  Qed.

  Lemma skipn_nil_length {A}:
    forall n (l: list A),
      skipn n l = [] -> length l <= n.
  Proof.
    intros n l Hskipn.
    pose proof firstn_skipn n l. rewrite Hskipn in H.
    apply (f_equal (length (A := A))) in H. rewrite app_length in H.
    simpl in H. rewrite <- plus_n_O in H. rewrite <- H. apply firstn_le_length.
  Qed.

  Lemma advance_input_n_succ_fail:
    forall inp n dir inpn,
      inpn = advance_input_n inp n dir ->
      advance_input inpn dir = None ->
      advance_input_n inp (S n) dir = inpn.
  Proof.
    intros [next pref] n [] inpn Heqinpn Hadv.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n next) eqn:Hskipn; try discriminate.
      f_equal.
      + apply skipn_nil_length in Hskipn. apply skipn_all2. lia.
      + apply skipn_nil_length in Hskipn. rewrite firstn_all2 by lia.
        rewrite firstn_all2 by lia. reflexivity.
    - unfold advance_input_n in *. subst inpn. unfold advance_input in Hadv.
      destruct (skipn n pref) eqn:Hskipn; try discriminate.
      f_equal.
      + apply skipn_nil_length in Hskipn. rewrite firstn_all2 by lia.
        rewrite firstn_all2 by lia. reflexivity.
      + apply skipn_nil_length in Hskipn. apply skipn_all2. lia.
  Qed.

  Lemma advance_input_n_suffix:
    forall inp n dir inp',
      inp' = advance_input_n inp n dir ->
      inp' = inp \/ strict_suffix inp' inp dir.
  Proof.
    intros inp n dir. induction n.
    - intro inp'. rewrite advance_input_n_0. auto.
    - intro inp'. set (inpn := advance_input_n inp n dir).
      specialize (IHn inpn eq_refl).
      destruct (advance_input inpn dir) as [inpn_adv | ] eqn:Hinpnadv.
      + rewrite advance_input_n_succ_success with (inpn := inpn) (inpn_adv := inpn_adv); auto.
        intros ->. destruct IHn as [IHn | IHn].
        * (* Impossible, but does not matter *)
          rewrite <- IHn. right. apply ss_advance. auto.
        * right. apply ss_advance in Hinpnadv. eauto using strict_suffix_trans.
      + rewrite advance_input_n_succ_fail with (inpn := inpn); auto. intros ->.
        auto.
  Qed.

  Lemma backref_suffix:
    forall gm gid inp dir br_str nextinp,
      read_backref rer gm gid inp dir = Some (br_str, nextinp) ->
      nextinp = inp \/ strict_suffix nextinp inp dir.
  Proof.
    intros ? ? [next pref] ? ? ? ?. unfold read_backref in H.
    destruct GroupMap.find as [r|].
    2: { injection H as <-. left. congruence. }
    destruct r as [startIdx endIdxOpt].
    destruct endIdxOpt as [endIdx|].
    2: { injection H as <-. left. congruence. }
    destruct dir.
    - destruct Nat.leb; try discriminate.
      destruct EqDec.eqb; try discriminate.
      injection H as <-. fold (advance_input_n (Input next pref) (endIdx - startIdx) forward) in H.
      apply advance_input_n_suffix with (n := endIdx - startIdx). congruence.
    - destruct Nat.leb; try discriminate.
      destruct EqDec.eqb; try discriminate.
      injection H as <-. fold (advance_input_n (Input next pref) (endIdx - startIdx) backward) in H.
      apply advance_input_n_suffix with (n := endIdx - startIdx). congruence.
  Qed.

  Lemma backref_termination:
    forall cont inp dir gid gm br_str nextinp,
      read_backref rer gm gid inp dir = Some (br_str, nextinp) ->
      actions_fuel cont nextinp dir < actions_fuel (Areg (Backreference gid)::cont) inp dir.
  Proof.
    intros. simpl. apply backref_suffix in H.
    destruct H.
    - subst nextinp. lia.
    - apply actions_monoton with (act := cont) in H. lia.
  Qed.

  Lemma anchor_termination:
    forall cont inp dir a,
      actions_fuel cont inp dir < actions_fuel (Areg (Anchor a)::cont) inp dir.
  Proof. intros. simpl. lia. Qed.


  (** * Computing a tree  *)

  Fixpoint compute_tree (act: actions) (inp: input) (gm: group_map) (dir: Direction) (fuel:nat): option tree :=
    match fuel with
    | 0 => None
    | S fuel => 
        match act with
        (* tree_done *)
        | [] => Some Match
        (* tree_check, tree_check_fail *)
        | Acheck strcheck :: cont =>
            if (is_strict_suffix inp strcheck dir) then
              match (compute_tree cont inp gm dir fuel) with
              | Some treecont => Some (Progress treecont)
              | None => None
              end
            else Some Mismatch            
        (* tree_close *)
        | Aclose gid :: cont =>
            match (compute_tree cont inp (GroupMap.close (idx inp) gid gm) dir fuel) with
            | Some treecont => Some (GroupAction (Close gid) treecont)
            | None => None
            end          
        (* tree_epsilon *)
        | Areg Epsilon::cont => compute_tree cont inp gm dir fuel
        (* tree_char, tree_char_fail *)
        | Areg (Regex.Character cd)::cont =>
            match read_char rer cd inp dir with
            | Some (c, nextinp) =>
                match (compute_tree cont nextinp gm dir fuel) with
                | Some treecont => Some (Read c treecont)
                | None => None
                end
            | None => Some Mismatch
                end
        (* tree_disj *)
        | Areg (Disjunction r1 r2)::cont =>
            match (compute_tree (Areg r1 :: cont) inp gm dir fuel, compute_tree (Areg r2 :: cont) inp gm dir fuel) with
            | (Some t1, Some t2) => Some (Choice t1 t2)
            | _ => None
            end
        (* tree_sequence *)
        | Areg (Sequence r1 r2)::cont =>
            compute_tree (seq_list r1 r2 dir ++ cont) inp gm dir fuel
        (* tree_quant_forced *)
        | Areg (Quantified greedy (S min) delta r1)::cont =>
            let gidl := def_groups r1 in
            match compute_tree (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel with
            | Some titer => Some (GroupAction (Reset gidl) titer)
            | None => None
            end          
        (* tree_quant_done *)
        | Areg (Quantified greedy 0 (NoI.N 0) r1)::cont =>
            compute_tree cont inp gm dir fuel
        (* tree_quant_free *)
        | Areg (Quantified greedy 0 delta r1)::cont =>
            let gidl := def_groups r1 in
            match  (compute_tree (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel, compute_tree cont inp gm dir fuel) with
            | (Some titer, Some tskip) =>  Some (greedy_choice greedy (GroupAction (Reset gidl) titer) tskip)
            | _ => None
            end
        (* tree_group *)
        | Areg (Group gid r1)::cont =>
            match compute_tree (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir fuel with
            | Some treecont => Some (GroupAction (Open gid) treecont)
            | _ => None
            end          
        (* tree_lk, tree_lk_fail *)
        | Areg (Lookaround lk r1)::cont =>
            let treelk := compute_tree [Areg r1] inp gm (lk_dir lk) fuel in
            match treelk with
            | None => None
            | Some treelk =>
                match lk_result lk treelk gm inp with
                | Some gmlk =>
                  let treecont := compute_tree cont inp gmlk dir fuel in
                  match treecont with None => None | Some treecont =>
                    Some (LK lk treelk treecont)
                  end
                | None => Some (LKFail lk treelk)
                end
            end
        (* tree_anchor, tree_anchor_fail *)
        | Areg (Anchor a)::cont =>
          if anchor_satisfied rer a inp then
            let treecont := compute_tree cont inp gm dir fuel in
            match treecont with None => None | Some treecont =>
              Some (AnchorPass a treecont)
            end
          else
            Some Mismatch
        (* tree_backref, tree_backref_fail *)
        | Areg (Backreference gid)::cont =>
          match read_backref rer gm gid inp dir with
          | Some (br_str, nextinp) =>
            let tcont := compute_tree cont nextinp gm dir fuel in
            match tcont with None => None | Some tcont =>
              Some (ReadBackRef br_str tcont)
            end
          | None =>
            Some Mismatch
          end
        end
    end.
    
  (** * Functional Semantics Termination  *)

  Lemma somenone:
    forall T (x:T), Some x <> None.
  Proof.
    intros T x. unfold not. intros H. inversion H.
  Qed.

  Lemma noi_destruct:
    forall n, n = NoI.N 0 \/ n <> NoI.N 0.
  Proof.
    destruct n.
    2: { right. unfold not. intros H. inversion H. }
    destruct n.
    - left. auto.
    - right. unfold not. intros H. inversion H.
  Qed.

  Theorem functional_terminates:
    forall act inp gm dir fuel,
      fuel > actions_fuel act inp dir ->
      compute_tree act inp gm dir fuel <> None.
  Proof.
    intros act inp gm dir fuel H.
    generalize dependent act. generalize dependent inp. 
    generalize dependent gm. generalize dependent dir.
    induction fuel; intros.
    { inversion H. }
    destruct act as [|a act].
    { simpl. apply somenone. }
    destruct a.
    - destruct r.
      + simpl. generalize (epsilon_termination act inp dir). intros.
        assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH.
        destruct (compute_tree act inp gm dir fuel); try contradiction.
        apply somenone.
      + simpl. destruct (read_char rer cd inp dir) eqn:READ; try apply somenone.
        destruct p as [c nextinp].
        generalize (character_termination act inp dir cd c nextinp READ). intros.
        assert (ENOUGH: fuel > actions_fuel act nextinp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH.
        destruct (compute_tree act nextinp gm dir fuel); try contradiction.
        apply somenone.
      + simpl. generalize (disjunction_left_termination act inp dir r1 r2). intros.
        generalize (disjunction_right_termination act inp dir r1 r2). intros.
        assert (ENOUGH1: fuel > actions_fuel (Areg r1::act) inp dir) by lia.
        assert (ENOUGH2: fuel > actions_fuel (Areg r2::act) inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH1. apply IHfuel with (gm:=gm) in ENOUGH2.
        destruct (compute_tree (Areg r1 :: act) inp gm dir fuel); try contradiction.
        destruct (compute_tree (Areg r2 :: act) inp gm dir fuel); try contradiction.
        apply somenone.
      + simpl. generalize (sequence_termination act inp dir r1 r2). intros.
        assert (ENOUGH: fuel > actions_fuel (seq_list r1 r2 dir ++ act) inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH. auto.
      + destruct min eqn:HMIN.
        { generalize (noi_destruct delta). intros [DELTA_DONE | DELTA_FREE]; subst.
          -                       (* quant done *)
            simpl. generalize (quant_done_termination act inp dir r greedy). intros.
            assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
            apply IHfuel with (gm:=gm) in ENOUGH. auto.
          -                       (* quant free *)
            generalize (quant_free_iter_termination act inp dir r greedy delta). intros.
            generalize (quant_free_skip_termination act inp dir r greedy delta). intros.
            assert (ENOUGH1: fuel > actions_fuel (Areg r :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r) :: act) inp dir) by lia.
            assert (ENOUGH2: fuel > actions_fuel act inp dir) by lia.
            apply IHfuel with (gm:=(GroupMap.reset (def_groups r) gm)) in ENOUGH1.
            apply IHfuel with (gm:=gm) in ENOUGH2.
            simpl. destruct delta.
            + destruct n. auto.
              destruct (compute_tree (Areg r :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred (NoI.N (S n))) r) :: act) inp (GroupMap.reset (def_groups r) gm) dir fuel); try contradiction.
              destruct (compute_tree act inp gm dir fuel); try contradiction.
              apply somenone.
            + destruct (compute_tree (Areg r :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred +∞) r) :: act) inp (GroupMap.reset (def_groups r) gm) dir fuel); try contradiction.
              destruct (compute_tree act inp gm dir fuel); try contradiction.
              apply somenone.
        }
        {                         (* quant forced *)
          simpl. generalize (quant_forced_termination act inp dir r n delta greedy). intros. subst.
          assert (ENOUGH: fuel > actions_fuel (Areg r :: Areg (Quantified greedy n delta r) :: act) inp dir) by lia.
          apply IHfuel with (gm:=(GroupMap.reset (def_groups r) gm)) in ENOUGH.
          destruct (compute_tree (Areg r :: Areg (Quantified greedy n delta r) :: act) inp (GroupMap.reset (def_groups r) gm) dir fuel); try contradiction.
          apply somenone.
        }
      + simpl.    (* Lookarounds *)
        assert (LK_ENOUGH: fuel > actions_fuel [Areg r] inp (lk_dir lk)). {
          pose proof lk_lk_termination act inp dir lk r. lia.
        }
        pose proof IHfuel (lk_dir lk) gm inp [Areg r] LK_ENOUGH.
        destruct compute_tree as [treelk|]; try contradiction.
        assert (LK_AFTER_ENOUGH: fuel > actions_fuel act inp dir). {
          pose proof lk_after_termination act inp dir lk r. lia.
        }
        destruct (lk_result lk treelk gm inp) eqn:LKRES; try apply somenone.
        pose proof IHfuel dir g inp act LK_AFTER_ENOUGH.
        destruct compute_tree; [apply somenone|contradiction].
      + simpl. generalize (group_termination act inp dir r id). intros.
        assert (ENOUGH: fuel > actions_fuel (Areg r :: Aclose id :: act) inp dir) by lia.
        apply IHfuel with (gm:=(GroupMap.open (idx inp) id gm)) in ENOUGH.
        destruct (compute_tree (Areg r :: Aclose id :: act) inp (GroupMap.open (idx inp) id gm) dir fuel); try contradiction.
        apply somenone.
      + simpl. destruct anchor_satisfied. 2: apply somenone. (* Anchors *)
        assert (ENOUGH: fuel > actions_fuel act inp dir). { pose proof anchor_termination act inp dir a. lia. }
        apply IHfuel with (gm := gm) in ENOUGH.
        destruct compute_tree; [apply somenone|contradiction].
      + simpl.    (* Backreferences *) 
        destruct read_backref as [[br_str nextinp]|] eqn:Hreadbr; try apply somenone.
        apply backref_termination with (cont := act) in Hreadbr.
        assert (ENOUGH: fuel > actions_fuel act nextinp dir) by lia.
        apply IHfuel with (gm := gm) in ENOUGH.
        destruct compute_tree; [apply somenone|contradiction].
    - simpl. destruct (is_strict_suffix inp i dir) eqn:SS.
      + apply is_strict_suffix_correct in SS.
        eapply check_termination with (cont:=act) in SS as FUEL.
        assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
        apply IHfuel with (gm:=gm) in ENOUGH.
        destruct (compute_tree act inp gm dir fuel) eqn:CMP; try contradiction.
        apply somenone.
      + apply somenone.
    - simpl. generalize (close_termination act inp dir g). intros.
      assert (ENOUGH: fuel > actions_fuel act inp dir) by lia.
      apply IHfuel with (gm:=GroupMap.close (idx inp) g gm) in ENOUGH.
      destruct (compute_tree act inp (GroupMap.close (idx inp) g gm) dir fuel); try contradiction.
      apply somenone.
  Qed.

End FunctionalSemantics.
