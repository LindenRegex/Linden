From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars.
From Linden Require Import Tree.
From Linden Require Import NumericLemmas.
From Warblre Require Import Numeric Base RegExpRecord.
From Linden Require Import Groups.
From Linden Require Import StrictSuffix.
From Linden Require Import Parameters LWParameters.
From Stdlib Require Import Lia.

(** * Inductive semantics of JavaScript regexes *)
(* This relates a regex and a string to their backtracking tree *)


Section Semantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* Reading a substring from a group map *)
  Definition read_backref (gm: group_map) (gid: group_id) (inp: input) (dir: Direction): option (string * input) :=
    match GroupMap.find gid gm with
    | None | Some (GroupMap.Range _ None) => Some ([], inp)
    | Some (GroupMap.Range startIdx (Some endIdx)) =>
      let sub_can := List.map (Character.canonicalize rer) (substr inp startIdx endIdx) in
      let len := endIdx - startIdx in
      match inp with
      | Input next pref =>
        match dir with
        | forward =>
          if len >? List.length next then
            None
          else
            let firstn := List.firstn len next in
            if (List.map (Character.canonicalize rer) firstn ==? sub_can)%wt then
              Some (firstn, advance_input_n inp len forward)
            else
              None
        | backward =>
          if len >? List.length pref then
            None
          else
            let rev_firstn := List.rev (List.firstn len pref) in
            if (List.map (Character.canonicalize rer) rev_firstn ==? sub_can)%wt then
              Some (rev_firstn, advance_input_n inp len backward)
            else
              None
        end
      end
    end.

  Lemma read_backref_success_advance:
    forall gm gid inp dir br_str nextinp,
      read_backref gm gid inp dir = Some (br_str, nextinp) ->
      nextinp = advance_input_n inp (length br_str) dir.
  Proof.
    intros gm gid inp dir br_str nextinp H.
    unfold read_backref in H. unfold advance_input_n.
    destruct GroupMap.find as [[startIdx [endIdx|]]|].
    - destruct inp as [next pref]. destruct dir.
      + (* Forward *)
        destruct Nat.leb eqn:Hinb; try discriminate.
        rewrite PeanoNat.Nat.leb_gt in Hinb.
        destruct EqDec.eqb eqn:Hsubeq; try discriminate.
        injection H as H <-.
        rewrite EqDec.inversion_true in Hsubeq.
        replace (length br_str) with (endIdx - startIdx). 1: reflexivity.
        rewrite <- H. apply (f_equal (length (A := Parameters.Character))) in Hsubeq.
        do 2 rewrite length_map in Hsubeq. rewrite length_firstn. lia.
      + (* Backward *)
        destruct Nat.leb eqn:Hinb; try discriminate.
        rewrite PeanoNat.Nat.leb_gt in Hinb.
        destruct EqDec.eqb eqn:Hsubeq; try discriminate.
        injection H as H <-.
        rewrite EqDec.inversion_true in Hsubeq.
        replace (length br_str) with (endIdx - startIdx). 1: reflexivity.
        rewrite <- H. apply (f_equal (length (A := Parameters.Character))) in Hsubeq.
        do 2 rewrite length_map in Hsubeq. rewrite length_rev, length_firstn. lia.
    - injection H as <- <-. simpl. now destruct inp, dir.
    - injection H as <- <-. simpl. now destruct inp, dir.
  Qed.

  (** * Lookaround tree functions  *)

  (* Checks for a result in a lookaround tree *)
  (* Positive lookarounds expect trees with a result, and negative ones expect trees without results *)
  (* In cases where the lookaround holds, computes the updated group_map after finding the first result in a tree of lookarounds *)
  Definition lk_result (lk:lookaround) (t:tree) (gm:group_map) (inp:input) : option group_map :=
    match (positivity lk) with
    | true =>
        match tree_res t gm inp (lk_dir lk) with
        | None => None      (* expected a result *)
        | Some (_, gm') => Some gm'
        end
    | false =>
        match tree_res t gm inp (lk_dir lk) with
        | Some _ => None         (* expected no result *)
        | None => Some gm        (* negative lookarounds keep the gm unchanged *)
        end
    end.

  (** * Anchor semantics *)

  Definition is_boundary (i:input) : bool :=
    match i with
    | Input next pref =>
        match next, pref with
        | [], [] => false
        | [], c::p' => word_char rer c
        | c::n', [] => word_char rer c
        | c1::n', c2::p' =>
            xorb (word_char rer c1) (word_char rer c2)
        end
    end.

  (* Checks whether the string is at an input boundary, i.e. start/end of input or line terminator if multiline *)
  Definition is_input_boundary (multiline: bool) (str: string): bool :=
    match str with
    | [] => true
    | x::q => multiline && Utils.List.inb x Character.line_terminators
    end.

  (* independent of the direction *)
  Definition anchor_satisfied (a:anchor) (i:input) : bool :=
    match i with
    | Input next pref =>
        match a with
        | BeginInput =>
            is_input_boundary (RegExpRecord.multiline rer) pref
        | EndInput =>
            is_input_boundary (RegExpRecord.multiline rer) next
        | WordBoundary =>
            is_boundary i
        | NonWordBoundary =>
            negb (is_boundary i)
        end
    end.

  (** * Continuation Semantics *)

  (* actions encode the next things to do while constructing a tree, a stack of continuations *)
  (* it can either be matching a regex *)
  (* or checking that the current string is different from another string (for the JS star) *)
  (* or closing a group after it's been opened *)
  Inductive action: Type :=
  | Areg: regex -> action
  | Acheck: input -> action
  | Aclose: group_id -> action.

  Definition actions: Type := list action.

  (* Adds two regexes to the stack of actions, in an order dependent of the direction *)
  Definition seq_list (r1 r2: regex) (dir: Direction) : actions :=
    match dir with
    | forward => [Areg r1; Areg r2]
    | backward => [Areg r2; Areg r1]
    end.

  (* `is_tree actions inp t` means that `t` is a correct backtracking tree for all `actions` on `inp` *)
  Inductive is_tree: actions -> input -> group_map -> Direction -> tree -> Prop :=
  | tree_match:
    (* nothing to do on an empty list of actions *)
    forall inp gm dir,
      is_tree [] inp gm dir Match
  | tree_check:
  (* pops a successful check from the action list *)
    forall inp gm dir strcheck cont treecont
      (PROGRESS: strict_suffix inp strcheck dir)
      (TREECONT: is_tree cont inp gm dir treecont),
      is_tree (Acheck strcheck :: cont) inp gm dir (Progress treecont)
  | tree_check_fail:
  (* pops a failing check from the action list *)
    forall inp gm dir strcheck cont
      (CHECKFAIL: ~strict_suffix inp strcheck dir),
      is_tree (Acheck strcheck :: cont) inp gm dir Mismatch
  | tree_close:
  (* pops the closing of a group from the action list *)
    forall inp gm dir cont treecont gid
      (TREECONT: is_tree cont inp (GroupMap.close (idx inp) gid gm) dir treecont),
      is_tree (Aclose gid :: cont) inp gm dir (GroupAction (Close gid) treecont)
  | tree_epsilon:
    forall inp gm dir cont tcont
      (ISTREE: is_tree cont inp gm dir tcont),
      is_tree ((Areg Epsilon)::cont) inp gm dir tcont
  | tree_char:
    forall c cd inp gm nextinp dir cont tcont
      (READ: read_char rer cd inp dir = Some (c, nextinp))
      (TREECONT: is_tree cont nextinp gm dir tcont),
      is_tree (Areg (Regex.Character cd) :: cont) inp gm dir (Read c tcont)
  | tree_char_fail:
    forall cd inp gm dir cont
      (READ: read_char rer cd inp dir = None),
      is_tree (Areg (Regex.Character cd) :: cont) inp gm dir Mismatch
  | tree_disj:
    forall r1 r2 cont t1 t2 inp gm dir
      (ISTREE1: is_tree (Areg r1 :: cont) inp gm dir t1)
      (ISTREE2: is_tree (Areg r2 :: cont) inp gm dir t2),
      is_tree (Areg (Disjunction r1 r2) :: cont) inp gm dir (Choice t1 t2)
  | tree_sequence:
    (* adding next regex to the continuation *)
    forall r1 r2 cont t inp gm dir
      (CONT: is_tree (seq_list r1 r2 dir ++ cont) inp gm dir t),
      is_tree (Areg (Sequence r1 r2) :: cont) inp gm dir t
  | tree_quant_forced:
    (* the quantifier is forced to iterate, because there is a strictly positive minimum *)
    forall r1 greedy min plus cont titer inp gm dir gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration *)
      (ISTREE1: is_tree (Areg r1 :: Areg (Quantified greedy min plus r1) :: cont) inp (GroupMap.reset gidl gm) dir titer),
      is_tree (Areg (Quantified greedy (S min) plus r1) :: cont) inp gm dir (GroupAction (Reset gidl) titer)
  | tree_quant_done:
    (* the quantifier is done iterating, because min and max are zero *)
    forall r1 greedy cont tskip inp gm dir
      (SKIP: is_tree cont inp gm dir tskip),
      is_tree (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) inp gm dir tskip
  | tree_quant_free:
    (* the quantifier is free to iterate or stop *)
    forall r1 greedy plus cont titer tskip tquant inp gm dir gidl
      (* the list of capture groups to reset *)
      (RESET: gidl = def_groups r1)
      (* doing one iteration, then a check, then executing the next quantifier *)
      (ISTREE1: is_tree (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 plus r1) :: cont) inp (GroupMap.reset gidl gm) dir titer)
      (* skipping the quantifier entirely *)
      (SKIP: is_tree cont inp gm dir tskip)
      (CHOICE: tquant = greedy_choice greedy (GroupAction (Reset gidl) titer) tskip),
      is_tree (Areg (Quantified greedy 0 (NoI.N 1 + plus)%NoI r1) :: cont) inp gm dir tquant
  | tree_group:
    forall r1 cont treecont inp gm dir gid
      (TREECONT: is_tree (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir treecont),
      is_tree (Areg (Group gid r1) :: cont) inp gm dir (GroupAction (Open gid) treecont)
  | tree_lk:
    forall lk r1 cont treecont treelk inp gm gmlk dir
      (* there is a tree for the lookaround *)
      (TREELK: is_tree [Areg r1] inp gm (lk_dir lk) treelk)
      (* the lookaround tree has the expected result, resulting in a new group map gmlk *)
      (RES_LK: lk_result lk treelk gm inp = Some gmlk)
      (TREECONT: is_tree cont inp gmlk dir treecont),
      is_tree (Areg (Lookaround lk r1) :: cont) inp gm dir (LK lk treelk treecont)
  | tree_lk_fail:
    forall lk r1 cont treelk inp gm dir
      (TREELK: is_tree [Areg r1] inp gm (lk_dir lk) treelk)
      (* the lookaround tree does not have the expected result *)
      (FAIL_LK: lk_result lk treelk gm inp = None),
      is_tree (Areg (Lookaround lk r1) :: cont) inp gm dir (LKFail lk treelk)
  | tree_anchor:
    forall a cont treecont inp gm dir
      (ANCHOR: anchor_satisfied a inp = true)
      (TREECONT: is_tree cont inp gm dir treecont),
      is_tree (Areg (Anchor a) :: cont) inp gm dir (AnchorPass a treecont)
  | tree_anchor_fail:
    forall a cont inp gm dir
      (ANCHOR: anchor_satisfied a inp = false),
      is_tree (Areg (Anchor a) :: cont) inp gm dir Mismatch
  | tree_backref:
    forall gid inp gm nextinp dir cont tcont br_str
      (READ_BACKREF: read_backref gm gid inp dir = Some (br_str, nextinp))
      (TREECONT: is_tree cont nextinp gm dir tcont),
      is_tree (Areg (Backreference gid) :: cont) inp gm dir (ReadBackRef br_str tcont)
  | tree_backref_fail:
    forall gid inp gm dir cont
      (READ_BACKREF: read_backref gm gid inp dir = None),
      is_tree (Areg (Backreference gid) :: cont) inp gm dir Mismatch.



  Definition priotree (r:regex) (str:string) (t:tree): Prop :=
    is_tree [Areg r] (init_input str) GroupMap.empty forward t.

  Definition priotree_inp (r:regex) (inp:input) (t:tree): Prop :=
    is_tree [Areg r] inp GroupMap.empty forward t.


  (** * Determinism  *)
  Theorem is_tree_determ:
    forall actions i gm dir t1 t2,
      is_tree actions i gm dir t1 ->
      is_tree actions i gm dir t2 ->
      t1 = t2.
  Proof.
    intros actions i gm dir t1 t2 H.
    generalize dependent t2.
    induction H; intros.
    - inversion H; subst; auto.
    - inversion H0; subst; auto.
      + apply IHis_tree in TREECONT. subst. auto.
      + exfalso. auto.
    - inversion H; subst; auto.
      exfalso. auto.
    - inversion H0; subst; auto.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H0; auto.
    - inversion H0; subst; auto; rewrite READ0 in READ; inversion READ; subst.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H; subst; auto.
      rewrite READ0 in READ. inversion READ.
    - inversion H1; subst; auto.
      apply IHis_tree1 in ISTREE1. apply IHis_tree2 in ISTREE2. subst. auto.
    - inversion H0; subst; auto.
    - inversion H0; subst; auto.
      apply IHis_tree in ISTREE1.
      subst. auto.
    - inversion H0; subst; auto.
      destruct plus; discriminate.
    - inversion H1; subst; auto.
      + destruct plus; discriminate.
      + apply plus_one_inj in H4. subst plus0.
        apply IHis_tree1 in ISTREE1. apply IHis_tree2 in SKIP. subst. auto.
    - inversion H0; subst; auto.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H1; subst; auto.
      2: { apply IHis_tree1 in TREELK. subst. rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
      apply IHis_tree1 in TREELK. subst treelk0. rewrite RES_LK in RES_LK0. injection RES_LK0 as RES_LK0.
      subst gmlk0. apply IHis_tree2 in TREECONT. subst. auto.
    - inversion H0; subst; auto.
      { apply IHis_tree in TREELK. subst. rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
      apply IHis_tree in TREELK. subst. auto.
    - inversion H0; subst; auto.
      + f_equal. auto.
      + congruence.
    - inversion H; subst; auto. congruence.
    - inversion H0; subst; auto; rewrite READ_BACKREF0 in READ_BACKREF; inversion READ_BACKREF; subst.
      apply IHis_tree in TREECONT. subst. auto.
    - inversion H; subst; auto; rewrite READ_BACKREF0 in READ_BACKREF; inversion READ_BACKREF; subst.
  Qed.

  Corollary priotree_determ:
    forall r s t1 t2,
      priotree r s t1 ->
      priotree r s t2 ->
      t1 = t2.
  Proof.
    unfold priotree. intros r s t1 t2 H H0. eapply is_tree_determ; eauto.
  Qed.

  Corollary priotree_inp_determ:
    forall r inp t1 t2,
      priotree_inp r inp t1 ->
      priotree_inp r inp t2 ->
      t1 = t2.
  Proof.
    unfold priotree_inp. intros r inp t1 t2 H H0. eapply is_tree_determ; eauto.
  Qed.

  (* We could also prove that there always exists a priotree for any regexes and string,
   bu that amounts to proving the termination of the priotree construction. *)


  (** * Highest priority result  *)
  (* the highest priority result is just the first branch of the corresponding tree *)

  Inductive highestprio_result: regex -> string -> option leaf -> Prop :=
  | bt_result:
    forall r str res tree
      (TREE: priotree r str tree)
      (FIRST: first_branch tree str = res),
      highestprio_result r str res.

  Inductive highestprio_result_inp: regex -> input -> option leaf -> Prop :=
  | hp_result_inp:
    forall r inp res tree
      (TREE: priotree_inp r inp tree)
      (FIRST: first_leaf tree inp = res),
      highestprio_result_inp r inp res.

  Lemma highestprio_determ:
    forall r str res1 res2,
      highestprio_result r str res1 ->
      highestprio_result r str res2 ->
      res1 = res2.
  Proof.
    intros r str res1 res2 H H0. inversion H. subst.
    inversion H0. subst.
    specialize (priotree_determ _ _ _ _ TREE TREE0). intros. subst. auto.
  Qed.

  Lemma highestprio_inp_determ:
    forall r inp res1 res2,
      highestprio_result r inp res1 ->
      highestprio_result r inp res2 ->
      res1 = res2.
  Proof.
    intros r inp res1 res2 H H0. inversion H. subst.
    inversion H0. subst.
    specialize (priotree_determ _ _ _ _ TREE TREE0). intros. subst. auto.
  Qed.
End Semantics.
