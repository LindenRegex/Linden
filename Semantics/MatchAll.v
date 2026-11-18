From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars.
From Linden Require Import Tree.
From Linden Require Import NumericLemmas.
From Warblre Require Import Numeric Base RegExpRecord.
From Linden Require Import Groups.
From Linden Require Import StrictSuffix.
From Linden Require Import Semantics.
From Linden Require Import FunctionalSemantics.
From Linden Require Import FunctionalUtils.
From Linden Require Import FlatMap Equivalence.
From Linden Require Import Parameters LWParameters.
From Stdlib Require Import Lia.
From Stdlib Require Import FunInd Recdef.

(** * Semantics of matchall (both inductive and functional) *)
(* This relates a regex and a string to the results of matchall *)


Section Semantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).
  Definition is_tree := is_tree rer.

  (** [matchall_matches r inp l] means that l is the result of allmatch for 
  the regex r on the input inp *)
  Inductive matchall_matches : regex -> input -> list leaf -> Prop := 
    | matchall_end_nomatch : 
      (* no match for the regex *)
      forall (r : regex) (inp : input) t
        (TREE : is_tree [Areg r] inp GroupMap.empty forward t)
        (NOMATCH : first_leaf t inp = None)
        (END : advance_input inp forward = None),
        matchall_matches r inp []
    | matchall_end_emptymatch : 
      (* an empty match at the end of the string *)
      forall (r : regex) (inp : input) t gm
        (TREE : is_tree [Areg r] inp GroupMap.empty forward t)
        (MATCH : first_leaf t inp = Some (inp, gm))
        (END : advance_input inp forward = None),
        matchall_matches r inp [(inp,gm)]
    | matchall_mid_nomatch : 
      (* no match starting here, we look at the next position *)
      forall (r : regex) (inp : input) t inp' res
        (TREE : is_tree [Areg r] inp GroupMap.empty forward t)
        (NOMATCH : first_leaf t inp = None)
        (MID : advance_input inp forward = Some inp')
        (REC : matchall_matches r inp' res),
        matchall_matches r inp res
    | matchall_mid_nonempty : 
      (* we eat the top priority match and get the matches on the rest *)
      forall (r : regex) (inp : input) t inp' gm res 
        (TREE : is_tree [Areg r] inp GroupMap.empty forward t)
        (MATCH : first_leaf t inp = Some (inp', gm))
        (PROGRESS : strict_suffix inp' inp forward) (* progress condition *)
        (REC : matchall_matches r inp' res), 
        matchall_matches r inp ((inp',gm)::res)
    | matchall_mid_empty : 
      (* we have an empty match *)
      forall (r : regex) (inp : input) t inp' gm res
        (TREE : is_tree [Areg r] inp GroupMap.empty forward t) 
        (MATCH : first_leaf t inp = Some (inp, gm))
        (MID : advance_input inp forward = Some inp')
        (REC : matchall_matches r inp' res),
        matchall_matches r inp ((inp,gm)::res)
  .

  Definition deterministic  {A:Type} (f : A -> Prop) : Prop 
  := forall x y, f x -> f y -> x = y.  

  Lemma end_of_match : forall t inp inp' gm, advance_input inp forward = None -> 
    first_leaf t inp = Some (inp',gm) -> inp = inp'. 
  Proof.
  unfold first_leaf. 
  intros t inp inp' gm Hadv Hleaf. generalize dependent (GroupMap.empty). 
  induction t;intros gmi Hleaf ;inversion Hleaf;subst;eauto.
  - destruct (tree_res t1 gmi inp forward) eqn:Et1;inversion H0; subst;eauto. 
  - eapply IHt.  unfold advance_input' in H0. rewrite Hadv in H0. eauto.
  - eapply IHt. rewrite advance_input_n_end in H0;eauto. 
  - destruct (positivity lk); destruct (tree_res t1 gmi inp (lk_dir lk)).
    all:try congruence.
    + destruct l;eauto.
    + eauto.
  Qed.

  Theorem matchall_deterministic : forall r inp, 
    deterministic (matchall_matches r inp).
  Proof.
  unfold deterministic.
  intros r inp l1 l2 Hm1. induction Hm1 in l2|-*;intro Hm2.
  all: inversion Hm2;subst; clear Hm2.
  all: assert (t=t0) by eauto using is_tree_determ; subst. 
  all: try congruence.
  - assert (inp = inp') by eauto using end_of_match. subst.  exfalso. eapply ss_irreflexive. eassumption.
  - apply IHHm1. congruence.
  - rewrite MATCH0 in MATCH. inversion MATCH. subst. exfalso. eapply ss_irreflexive. eassumption.  
  - rewrite MATCH0 in MATCH. inversion MATCH. subst. f_equal. auto.
  - rewrite MATCH0 in MATCH. inversion MATCH. subst. exfalso. eapply ss_irreflexive. eassumption. 
  - rewrite MATCH0 in MATCH. inversion MATCH. subst. exfalso. eapply ss_irreflexive. eassumption. 
  - rewrite MATCH0 in MATCH. inversion MATCH. subst. f_equal. rewrite MID0 in MID. inversion MID. subst. 
    now apply IHHm1.
  Qed.

End Semantics.

Section FunctionalSemantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Definition stsf x y := strict_suffix x y forward.
  
  Lemma advance_input'_spec: forall inp dir,  (exists inp',advance_input' inp dir = inp' /\ advance_input inp dir = Some inp') \/ (advance_input' inp dir = inp).
  Proof.
  intros inp dir.
  unfold advance_input'. destruct (advance_input inp dir) eqn:Ei.
    - left. exists i. auto.
    - auto.
  Qed.   

  Lemma leaves_included: forall t inp inp' gm, first_leaf t inp = Some (inp', gm) ->
    stsf inp' inp \/ inp' = inp.
  Proof.
    unfold first_leaf. generalize dependent GroupMap.empty. intros gmi t. generalize dependent gmi.
    induction t; intros gmi inp inp' gm Hleaf;inversion Hleaf; subst; eauto.
    - destruct (tree_res t1 gmi inp forward) eqn:Et;inversion H0;subst;eauto.
    - destruct (advance_input'_spec inp forward).
      + (* advance_input inp = Some i *)
       destruct H as [inp'' [H' H]]. 
        subst. apply IHt in H0. destruct H0.
        * left. eapply ss_next';eauto. 
        * left. constructor. now subst.
      + (* advance_input inp = None *)
        rewrite H in H0. eapply IHt. eauto. 
    - destruct (length str).
      + rewrite advance_input_n_0 in H0. apply IHt in H0. assumption.
      + apply IHt in H0. remember (advance_input_n inp (S n) forward) as inp''. 
        apply advance_input_n_suffix in Heqinp''. destruct Heqinp'';subst;eauto.
        destruct H0;subst;eauto. left. eapply strict_suffix_trans;eauto.
    - destruct (positivity lk);destruct (tree_res t1 gmi inp (lk_dir lk)); try congruence;eauto.
      destruct l;eauto.
  Qed.

  Lemma stsf_translate : forall inp inp', stsf inp inp' -> remaining_length inp forward < remaining_length inp' forward.
  Proof.
  intros inp inp' H. unfold stsf in H. remember forward as f eqn:Ef.
  generalize Ef. induction H;intros He;subst.
  - destruct inp, nextinp. inversion H. destruct next;try congruence.
    simpl. inversion H1. subst. lia.
  - transitivity (remaining_length inp2 forward);auto.
    destruct inp1,inp2. inversion H. destruct next0;try congruence.
    inversion H2. subst. simpl. lia.
  Qed.
      
  Function matchall (r: regex) (inp:input) {measure (fun x => remaining_length x forward) inp}: list leaf :=
    let t := compute_tr_dep rer [Areg r] inp GroupMap.empty forward in 
    match first_leaf t inp with 
      | None => match advance_input inp forward with 
                    | None => []                        (* matchall_end_nomatch *)
                    | Some inp' => matchall r inp'      (* matchall_mid_nomatch *)
                end
      | Some (inp', gm) => match advance_input inp forward with 
                    | None => [(inp',gm)]               (* matchall_end_emptymatch *)
                    | Some inp'' => if input_eq_dec inp' inp then (* is the match empty ? *)
                                    (inp,gm)::matchall r inp'' (* matchall_mid_empty *)
                                else (inp',gm)::matchall r inp'(* matchall_mid_nonempty *)
                    end
    end.
    Proof.
    - intros. subst. enough (stsf inp'' inp). {now apply stsf_translate. }  now constructor. 
    - intros. enough (stsf inp' inp). {now apply stsf_translate. }  apply leaves_included in teq. destruct teq;auto. congruence. 
    - intros. enough (stsf inp' inp). {now apply stsf_translate. } now constructor. 
    Defined.

  Theorem functional_matchall_correct: forall r inp, matchall_matches rer r inp (matchall r inp).
  Proof.
    intros r inp.
    apply matchall_ind;intros;subst.
  - eapply matchall_end_nomatch;eauto.
    unfold t.
    apply (compute_tr_dep_is_tree rer). 
  - eapply matchall_mid_nomatch; eauto. apply (compute_tr_dep_is_tree rer).
  - assert (inp0=inp') by eauto using end_of_match. subst. eapply matchall_end_emptymatch;eauto. apply (compute_tr_dep_is_tree rer).
  - eapply matchall_mid_empty;eauto. apply (compute_tr_dep_is_tree rer).
  - eapply matchall_mid_nonempty;eauto. 
    + apply (compute_tr_dep_is_tree rer).
    + apply leaves_included in e. destruct e;try congruence. assumption.
  Qed.

  Theorem matchall_total: forall r inp, exists l, matchall_matches rer r inp l.
  Proof.
  intros r inp. exists (matchall r inp).
  apply functional_matchall_correct. 
  Qed.

End FunctionalSemantics.

Section RegexRewrite.
  Context {params: LindenParameters}.
  Context (rer : RegExpRecord).

  (* (r) *)
  Definition parenthesize (r : regex) : regex := 
    Group 0 r.

  (* (?:(r)|) *)
  Definition r_or_nil (r : regex) : regex :=
    Disjunction (parenthesize r) Epsilon. 

  (* (?![^]) *)
  Definition negative_all : regex :=
    Lookaround NegLookAhead (Regex.Character CdAll).

  (* r [^]*? *)
  Definition lazy_postfix (r : regex) : regex :=
    Sequence r dot_star.

  (*
    [^]*? (?: (r) [^]*? )* (?![^]) (?:(r)|)
  *)
  Definition transform_regex (r : regex) : regex :=
    lazy_prefix
        (Sequence (Sequence
            (greedy_star (lazy_postfix (parenthesize r)))
            negative_all)
            (r_or_nil r)).

End RegexRewrite.

Section BigProof.
  Context {params: LindenParameters}.
  Context (rer : RegExpRecord).

  (* modularity of appartenance in leaves. A leaf of the succession 
  of two actions can be obtained through a leaf of each of these.  *)
  Lemma flatmap_in_mod: forall t tx x inp q tl gm, 
  is_tree rer (x::q) inp gm forward t -> 
  is_tree rer [x] inp gm forward tx ->
  (exists leafx, (In leafx (tree_leaves tx gm inp forward) /\
  act_from_leaf rer q forward leafx tl)) ->
  (exists leafq, In leafq tl) ->
  exists res, In res (tree_leaves t gm inp forward).
  Proof.
  intros t tx x inp q tl gm Ht Htx [leafx [Hinx Hact]] [leafq Hinq]. 
  inversion Hact. subst. 
  rewrite app_cons in Ht. eapply (leaves_concat _  _ _ _ [x] q) in Ht;eauto. 
  eapply (FlatMap_in _ _ _ _ _ (act_from_leaf_determ _  _ _)) in Ht;eauto.
  exists leafq. 
  rewrite Forall_forall in Ht. auto.
  Qed.

  (* helper lemma for the construction of trees w/ proof. Maybe this already exists ? *)
  Lemma tree_ex : forall a inp gm dir, 
  exists t, is_tree rer a inp gm dir t.
  Proof.
  intros. exists (compute_tr_dep rer a inp gm dir).
  apply compute_tr_dep_is_tree.
  Qed.

  (* tactic to use the above lemma *)
  Ltac build_tree act inp gm dir := 
    pose (tree_ex act inp gm dir) as H_build_tree;destruct H_build_tree.

  (* tactic to use flatmap_in_mod, gives the two appartenance goals. 
  WARNING: leaves existential variables, st the first goal HAS to be filled first,  *)
  Ltac step_in H:= match goal with 
  | [H: is_tree _ (?x::?q) ?inp ?gm ?dir _ |- _]  => build_tree [x] inp gm dir;
                                                     build_tree q inp gm dir;
                                                 eapply flatmap_in_mod; try eassumption;clear H
  end.
  Ltac inv H := inversion H;subst;simpl;clear H.
  Ltac finish := split;try constructor;eauto.

  Lemma remove_empty : forall n, 
    MapS.remove (elt:=GroupMap.range) n GroupMap.empty = GroupMap.empty.
  Proof. 
    intro.
    now apply GroupMap.eqb_eq.
  Qed.

  Lemma rewrite_empty : forall l,
  GroupMap.reset l GroupMap.empty = GroupMap.empty.
  Proof.
  induction l.
  - reflexivity.
  - simpl. apply GroupMap.eqb_eq. rewrite remove_empty. 
    rewrite IHl. easy.
  Qed. 

  Lemma grp_empty : forall l,
  (GroupMap.reset l (MapS.remove (elt:=GroupMap.range) 0 GroupMap.empty)) = GroupMap.empty.
  Proof.
  rewrite remove_empty. intro. apply rewrite_empty.
  Qed.

  Lemma eat_all_dot: forall inp t gms, 
  is_tree rer [Areg dot_star] inp gms forward t -> 
  exists inp' gm', In (inp', gm') (tree_leaves t gms inp forward) /\ advance_input inp' forward = None /\ (stsf inp' inp \/ inp' = inp).
  Proof.
  intros. 
  pose (advance_end_prefix inp forward) as Hend.
  destruct Hend as [inp' [Hend Hsuff]].
  remember forward as fwd.
  generalize dependent t.
  revert gms. 
  induction Hsuff;intros gms t Ht; subst.
  - inv Ht. inv SKIP. exists inp,gms. split;auto.
  - inv Ht. destruct plus;inv H2.  inv ISTREE1.
    + apply read_char_success_advance in READ. rewrite READ in H. inv H.
      inv TREECONT.
      * eapply IHHsuff in Hend;eauto.
        destruct Hend as [inp' [gm' [Hin [Hend' Hsf']]]].
        exists inp',gm'. split.
        -- rewrite in_app_iff. right. unfold advance_input'. rewrite READ.
          assumption.
        -- split;auto. left. destruct Hsf';subst;eauto. eapply strict_suffix_trans;eauto.
      *  exfalso. apply CHECKFAIL. now constructor.
    +  apply cannot_read_correct in READ. unfold check_read in READ.
       destruct inp1. destruct next.
       * inv H.
       * simpl in READ. inv READ.
  Qed.  

  Lemma can_eat_entire_string : forall (r:regex) (inp:input) t str gms,
    stsf inp str ->
    is_tree rer [Areg dot_star;
                 Acheck str;
                 Areg (greedy_star (lazy_postfix (parenthesize r)));
                 Areg negative_all;
                 Areg (r_or_nil r)]
                inp gms forward t ->
  exists res, In res (tree_leaves t gms inp forward)
  .
  Proof.
  intros r inp t str gms Hstsf H.
  build_tree [Areg dot_star] inp gms forward.
  remember H0 as Hx. clear HeqHx.
  apply eat_all_dot in H0. destruct H0 as [inp' [gm [Hin [Hend Hprog]]]].
  build_tree [Acheck str; Areg (greedy_star (lazy_postfix (parenthesize r)));
              Areg negative_all; Areg (r_or_nil r)] inp' gm forward.
  eapply (flatmap_in_mod t x);try eassumption.
  - (* we reach the end of the string through the first star *)
    exists (inp',gm). split;auto. constructor. eassumption. 
  - simpl. clear Hx Hin H. step_in H0.
    + (* Acheck str *)
      inv H.
      * (* check passes *)
        inv TREECONT. exists (inp',gm). finish.
      * (* check fails: impossible *)
        exfalso. apply CHECKFAIL.  destruct Hprog;subst;auto. eapply strict_suffix_trans;eauto.
    + step_in H1.
      * (* Areg (greedy_star (lazy_postfix (parenthesize r))) *)
        (* we just SKIP the star *)
        inv H0. inv SKIP. exists (inp',gm). rewrite in_app_iff. split.
        ** right. now constructor.
        ** constructor;eauto.
      * step_in H2.
        -- (* Areg negative_all *)
           (* i.e. are we at the end ? *) 
           inv H1. 
            ++ (* we pass the check *) 
              inv TREECONT. inv TREELK.
              ** (* we read a char (absurd) *)
                 inv TREECONT. simpl in READ. apply read_char_success_advance in READ. congruence.
              ** (* we couldn't read a char *)
                exists (inp',gm). split;eauto. constructor. eassumption. 
            ++ (* we fail the lookahead *)
              unfold lk_result in FAIL_LK. simpl in FAIL_LK. destruct (tree_res treelk gm inp' forward) eqn:El;inv FAIL_LK. inv TREELK. 
              ** (* we could read a char *)
                inv TREECONT. apply read_char_success_advance in READ. simpl in READ. congruence.
              ** (* we couldn't read a char *)
                 inv El.
        -- (* Areg (r_or_nil r) *)
           (* we just skip *)
          inv H3. inv ISTREE2. inv ISTREE. exists (inp',gm). rewrite in_app_iff. right. now constructor. 
  Qed. 

  Inductive has_no_0_grp:  regex -> Prop :=
    | ng0_eps : has_no_0_grp Epsilon 
    | ng0_chr : forall cd, 
                has_no_0_grp (Regex.Character cd)
    | ng0_dsj : forall r1 r2, 
                has_no_0_grp r1 -> 
                has_no_0_grp r2 -> 
                has_no_0_grp (Disjunction r1 r2)
    | ng0_seq : forall r1 r2, 
                has_no_0_grp r1 -> 
                has_no_0_grp r2 -> 
                has_no_0_grp (Sequence r1 r2)
    | ng0_quant : forall greedy min delta r1, 
                has_no_0_grp r1 -> 
                has_no_0_grp (Quantified greedy min delta r1)
    | ng0_lk : forall lk r, 
                has_no_0_grp r -> 
                has_no_0_grp (Lookaround lk r)
    | ng0_grp : forall id r, 
                id <> 0 ->
                has_no_0_grp r -> 
                has_no_0_grp (Group id r)
    | ng0_anchr : forall a, 
                has_no_0_grp (Anchor a)
    | ng0_bckrf : forall id, 
                has_no_0_grp (Backreference id)
  .


  Definition hd_fst {A} (l: option (list A)) x := match x with 
    None => l = None 
    | Some x => exists res, l = Some (x::res)
    end.

  Lemma hd_opt_seql {A} : forall (l1 l2: option (list A)) x y,
  hd_fst l1 x /\ hd_fst l2 y -> hd_fst (seql l1 l2) (seqop x y).
  Proof.
  intros [[|]|] [[|]|] [|] [|]. all:unfold hd_fst;simpl ;intro H.
  all:inv H;try congruence.
  all: inv H0;inv H1. all:try inv H. 
  Qed.

  (* Lemma put_egg_in_basket : forall r inp gm ,
  is_tree rer [Areg r;Aclose 0] inp gm forward Match ->
  matchall_res t gm inp forward = [] *)

  Lemma notrm : forall inp gm dir l, 
  ~ (is_tree rer (l++[Aclose 0]) inp gm dir Match).
  Proof.
  induction l.
  - simpl. intro H. inv H.
  - simpl. intro H. inv H.
    + apply IHl. assumption.
    + destruct dir;simpl in CONT.   
  Admitted. 
  
  Lemma simple_result: forall t r inp, 
  is_tree rer [Areg r;Aclose 0] inp GroupMap.empty forward t ->
  has_no_0_grp r ->
  hd_fst (matchall_res t GroupMap.empty inp forward) (first_leaf t inp).
  Proof.
  Admitted.

  (* Lemma same_tree : forall r l t1 t2 inp gm, 
  is_tree rer [r] inp gm forward t1 ->
  is_tree rer (r::l) inp gm forward t2 -> 
   *)

  (* Lemma matchall_res_spec_inside_r : 
  forall r inp  t t_mod l, 
  is_tree rer [Areg (parenthesize r)] inp GroupMap.empty forward t ->
  is_tree rer ((Areg (parenthesize r))::l) inp GroupMap.empty forward t_mod ->
  hd_fst (matchall_res t_mod GroupMap.empty inp forward) (first_leaf t inp).
  Proof.
  intros . inv H. inv H0. 
  remember ([Areg r;Aclose 0]) as acts.
  remember (GroupMap.open (idx inp) 0 GroupMap.empty) as gmm.





  generalize dependent inp.
  (* induction treecont in l,treecont0|-*;intros;inv TREECONT;try inv ISTREE;simpl in*. *)



  induction r in l,treecont,treecont0|-*;intros ;inv TREECONT;inv TREECONT0;simpl;cbn;try congruence.
  - inv ISTREE. inv ISTREE0. inv TREECONT. simpl. admit. (* TODO : condition on result in l*)
  - inv TREECONT1. inv TREECONT. inv TREECONT0. rewrite READ0 in READ. inv READ. 
    admit. (* idem *)
  - apply hd_opt_seql. split;eauto.
  - simpl in *.   admit.
  - simpl in *. 
  Admitted. 
 *)
  Lemma helper: 
  forall r inp inp' t t_mod gm l t2, 
  is_tree rer [Areg (parenthesize r)] inp GroupMap.empty forward t ->
  is_tree rer ((Areg (parenthesize r))::l) inp GroupMap.empty forward t_mod ->
  first_leaf t inp = Some (inp', gm) ->
  stsf inp' inp -> 
  is_tree rer l inp' GroupMap.empty forward t2 ->
  (exists res, In res (tree_leaves t2 GroupMap.empty inp' forward)) -> 
  matchall_res t_mod GroupMap.empty inp forward = Some ((inp',gm)::matchall_first_leaf t2 inp').
  Proof.
  (* intros.
  assert (hd_fst (matchall_res t_mod GroupMap.empty inp forward)  (first_leaf t inp)) as Hr. {
    eapply matchall_res_spec_inside_r;eauto.
  }
  rewrite H1 in Hr.
  inv Hr.
  rewrite H5. f_equal. f_equal.
  
  induction t_mod;inv Etmod.
  -  inv H6. *)
  Admitted.

  (* 
  Proof ideas: 
  we need to prove all at once. The determining argument is, 
  at the point where we have the close 0 we get a non empty result from 
  matchall_first_leaf t2 inp' and the path taken up to this point is 
  the same as first_leaf. d
   *)
  Lemma correct_match_on_point: 
  forall r inp inp' t t_mod gm t2, 
  is_tree rer [Areg (parenthesize r)] inp GroupMap.empty forward t ->
  is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t_mod ->
  first_leaf t inp = Some (inp', gm) ->
  stsf inp' inp ->
  is_tree rer [Areg (transform_regex r)] inp' GroupMap.empty forward t2 ->
  matchall_first_leaf t_mod inp = (inp', gm) :: matchall_first_leaf t2 inp'.
  Proof.
  unfold matchall_first_leaf.
  intros.
  inv H0. inv CONT. inv SKIP. inv CONT. inv CONT0. simpl in *. inv ISTREE0. simpl in *. 
  rewrite grp_empty in *. 
  assert (matchall_res titer0 GroupMap.empty inp forward = Some ((inp',gm)::(matchall_first_leaf titer0 inp'))) as Hr. {
    clear SKIP ISTREE1 H5 H3 plus titer. destruct plus0;inv H6. build_tree [Areg dot_star; Acheck inp; Areg (Quantified true 0 +∞ (lazy_postfix (parenthesize r)));
Areg negative_all; Areg (r_or_nil r)] inp' GroupMap.empty forward. 
    eapply helper;eauto;admit.
    (* eapply can_eat_entire_string;eauto. *)
  }
  rewrite Hr.
  simpl. f_equal. unfold matchall_first_leaf. 
  (* now : need to show that the transformed regex is invariant by 
    translation along a split point (w.r.t the result extracted) *)
  Admitted.

  (* Returns the beginning of a match *)
  Definition find_beginning (inp: input) gm : input := 
    match GroupMap.find 0 gm with 
      | Some (GroupMap.Range StartIdx _) => advance_input_n inp (StartIdx - (idx inp)) forward
      | None => inp
    end.

  Lemma correct_matches:
  forall r inp t ,
  is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t ->
  Forall
    (fun x => exists inp' t,
        (inp' = inp \/ stsf inp inp') /\
        is_tree rer [Areg (parenthesize r)] inp' GroupMap.empty forward t /\
        first_leaf t inp' = Some x
    )
    (matchall_first_leaf t inp).
  Proof.
  (* proof notes : 
  'just' need to find the inp'. for a given x, the *end* of the match is in 
  the leaf, we need to get the *beginning* from the capture groups somehow
  (use find_beginning, how to prove it is correct ???)
  then build t,  
   *)
  Admitted.


  Lemma correct_skip_on_point: 
  forall r inp inp' t t_mod t2, 
  is_tree rer [Areg (parenthesize r)] inp GroupMap.empty forward t ->
  is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t_mod ->
  first_leaf t inp = None ->
  advance_input inp forward = Some inp' ->
  is_tree rer [Areg (transform_regex r)] inp' GroupMap.empty forward t2 ->
  matchall_first_leaf t_mod inp = matchall_first_leaf t2 inp'.
  Proof.
  Admitted.

  Lemma correct_empty_on_point:
  forall r inp inp' t t_mod gm t2, 
  is_tree rer [Areg (parenthesize r)] inp GroupMap.empty forward t ->
  is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t_mod ->
  first_leaf t inp = Some (inp, gm) ->
  advance_input inp forward = Some inp' ->
  is_tree rer [Areg (transform_regex r)] inp' GroupMap.empty forward t2 ->
  matchall_first_leaf t_mod inp = (inp, gm) :: matchall_first_leaf t2 inp'.
  Proof.
  Admitted.

  (* at the end of the string, no matches *)
  Lemma base_case: 
  forall r inp t t_mod, 
  is_tree rer [Areg (parenthesize r)] inp GroupMap.empty forward t ->
  is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t_mod ->
  first_leaf t inp = None ->
  advance_input inp forward = None -> 
  matchall_first_leaf t_mod inp  = [].
  Proof.
  intros. 
  unfold matchall_first_leaf. 
  destruct (matchall_res t_mod GroupMap.empty inp forward) eqn:Em;auto.
  (* proof idea : all matches in l are also a match of r  either at inp or at 
  a suffix of it (lemma correct_matches).  Here, no case is possible.  *)

  
  Admitted.

  Lemma base_case_empty: 
  forall r inp t gm t_mod, 
  is_tree rer [Areg (parenthesize r)] inp GroupMap.empty forward t ->
  is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t_mod ->
  first_leaf t inp = Some(inp,gm) ->
  advance_input inp forward = None -> 
  matchall_first_leaf t_mod inp  = [(inp,gm)].
  Proof.
  intros.
  unfold matchall_first_leaf.
  (* proof idea : by double inclusion, as above the only possible 
  match is at inp, by unicity it is (inp,gm), we need to show (inp,gm) in l,
  need to show that as we are at the end it is always possible *)
  Admitted.

  Theorem transform_correct : 
    forall (r : regex) (inp : input) t l,
    is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t ->     
    matchall_matches rer (parenthesize r) inp l ->
    matchall_first_leaf t inp = l. 
  Proof.
  intros r inp t l Ht Hm. remember (parenthesize r) as pr. 
  generalize dependent t.
  induction Hm; intros t0 Ht0;subst.
  - (* matchall_end_nomatch *)
    eapply base_case;eauto.
  - (* matchall_end_emptymatch *)
    eapply base_case_empty;eauto.
  -  (* matchall_mid_nomatch *)
    build_tree [Areg (transform_regex r)] inp' GroupMap.empty forward.
    erewrite correct_skip_on_point;eauto.
  - (* matchall_mid_nonempty_match *)
    build_tree [Areg (transform_regex r)] inp' GroupMap.empty forward.
    erewrite correct_match_on_point;eauto. f_equal. auto. 
  - (* matchall_mid_empty_match *)
    build_tree [Areg (transform_regex r)] inp' GroupMap.empty forward.
    erewrite correct_empty_on_point;eauto. f_equal. auto.
  Qed.

  Lemma other_transform_correct: 
  forall (r : regex) (inp : input) t,
    is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t ->     
    matchall_matches rer (parenthesize r) inp (matchall_first_leaf t inp).
  Proof.
    intros. destruct (matchall_total rer (parenthesize r) inp) as [l Hl].
    remember Hl as Hl'. clear HeqHl'.
    eapply transform_correct in Hl;eauto. now rewrite <- Hl in Hl'.
  Qed.

End BigProof.
