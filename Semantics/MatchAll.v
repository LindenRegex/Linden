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
    | matchall_nil_end : 
      (* no match for the regex *)
      forall (r : regex) (inp : input) t, 
        is_tree [Areg r] inp GroupMap.empty forward t -> 
        first_leaf t inp = None ->
        advance_input inp forward = None ->
        matchall_matches r inp []
    | matchall_some_end : 
      (* an empty match at the end of the string *)
      forall (r : regex) (inp : input) t gm, 
        is_tree [Areg r] inp GroupMap.empty forward t -> 
        first_leaf t inp = Some (inp, gm) ->
        advance_input inp forward = None -> 
        matchall_matches r inp [(inp,gm)]
    | matchall_next : 
      (* no match starting here, we look at the next position *)
      forall (r : regex) (inp : input) t inp' res, 
        is_tree [Areg r] inp GroupMap.empty forward t -> 
        first_leaf t inp = None ->
        advance_input inp forward = Some inp' ->  
        matchall_matches r inp' res ->
        matchall_matches r inp res
    | matchall_cons_some : 
      (* we eat the top priority match and get the matches on the rest *)
      forall (r : regex) (inp : input) t inp' gm res, 
        is_tree [Areg r] inp GroupMap.empty forward t -> 
        first_leaf t inp = Some (inp', gm) -> 
        strict_suffix inp' inp forward -> (* progress condition *)
        matchall_matches r inp' res -> 
        matchall_matches r inp ((inp',gm)::res)
    | matchall_cons_none : 
      (* we have an empty match *)
      forall (r : regex) (inp : input) t inp' gm res, 
        is_tree [Areg r] inp GroupMap.empty forward t -> 
        first_leaf t inp = Some (inp, gm) -> 
        advance_input inp forward = Some inp' ->
        matchall_matches r inp' res -> 
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
  - clear H2. assert (inp = inp') by eauto using end_of_match. subst.  exfalso. eapply ss_irreflexive. eassumption.
  - apply IHHm1. congruence.
  - rewrite H3 in H0. inversion H0. subst. exfalso. eapply ss_irreflexive. eassumption.  
  - rewrite H3 in H0. inversion H0. subst. f_equal. auto.
  - rewrite H3 in H0. inversion H0. subst. exfalso. eapply ss_irreflexive. eassumption. 
  - rewrite H3 in H0. inversion H0. subst. exfalso. eapply ss_irreflexive. eassumption. 
  - rewrite H3 in H0. inversion H0. subst. f_equal. rewrite H4 in H1. inversion H1. subst. 
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
  generalize Ef. induction H;intros He;subst. (* why is the dance around forward needed ? *)
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
                    | None => []                        (* matchall_nil_end *)
                    | Some inp' => matchall r inp'      (* matchall_next *)
                end
      | Some (inp', gm) => match advance_input inp forward with 
                    | None => [(inp',gm)]               (* matchall_some_end *)
                    | Some inp'' => if input_eq_dec inp' inp then (* is the match empty ? *)
                                    (inp,gm)::matchall r inp'' (* matchall_cons_none *)
                                else (inp',gm)::matchall r inp'(* matchall_cons_some *)
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
  - eapply matchall_nil_end;eauto.
    unfold t.
    apply (compute_tr_dep_is_tree rer). 
  - eapply matchall_next; eauto. apply (compute_tr_dep_is_tree rer).
  - assert (inp0=inp') by eauto using end_of_match. subst. eapply matchall_some_end;eauto. apply (compute_tr_dep_is_tree rer).
  - eapply matchall_cons_none;eauto. apply (compute_tr_dep_is_tree rer).
  - eapply matchall_cons_some;eauto. 
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


  Theorem transform_correct : 
    forall (r : regex) (inp : input) t l,
    is_tree rer [Areg (transform_regex r)] inp GroupMap.empty forward t -> 
    matchall_first_leaf t inp = l -> 
    matchall_matches rer (parenthesize r) inp l.
  Proof.
  Admitted.

End RegexRewrite.
