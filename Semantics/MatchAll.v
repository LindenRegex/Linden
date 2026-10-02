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
From Linden Require Import Parameters LWParameters.
From Stdlib Require Import Lia.
From Stdlib Require Import FunInd Recdef.

(** * Inductive semantics of JavaScript regexes *)
(* This relates a regex and a string to their backtracking tree *)


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
        idx inp < idx inp' -> (* progress condition *)
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

  Lemma matchall_deterministic : forall r inp, 
    deterministic (matchall_matches r inp).
  Proof.
  unfold deterministic.
  intros r inp l1 l2 Hm1. induction Hm1 in l2|-*;intro Hm2.
  all: inversion Hm2;subst; clear Hm2.
  all: assert (t=t0) by eauto using is_tree_determ; subst. 
  all: try congruence.
  - clear H2. assert (inp = inp') by eauto using end_of_match. subst. lia.
  - apply IHHm1. congruence.
  - rewrite H3 in H0. inversion H0. subst. lia. 
  - rewrite H3 in H0. inversion H0. subst. f_equal. auto.
  - rewrite H3 in H0. inversion H0. subst. lia.
  - rewrite H3 in H0. inversion H0. subst. lia. 
  - rewrite H3 in H0. inversion H0. subst. f_equal. rewrite H4 in H1. inversion H1. subst. 
    now apply IHHm1.
  Qed.

End Semantics.

Section FunctionalSemantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Definition tree_builder (r : regex) (inp : input) : tree.
  refine (let ct := compute_tree rer [Areg r] inp GroupMap.empty forward (S (actions_fuel [Areg r] inp forward)) in _).
  destruct ct eqn:Ect.
  - exact t.
  - exfalso. assert (ct <> None). { apply functional_terminates. apply PeanoNat.Nat.lt_succ_diag_r. } apply H. exact Ect.
  Defined.

  Function matchall (r: regex) (inp:input) {measure (fun x => remaining_length x forward) inp}: list leaf :=
    let t := tree_builder r inp in 
    match first_leaf t inp with 
      | None => match advance_input inp forward with 
                    | None => []                        (* matchall_nil_end *)
                    | Some inp' => matchall r inp'      (* matchall_next *)
                end
      | Some (inp', gm) => match advance_input inp forward with 
                    | None => [(inp',gm)]               (* matchall_some_end *)
                    | Some inp'' => if input_eq_dec inp' inp then 
                                    (inp,gm)::matchall r inp'' (* matchall_cons_none *)
                                else (inp',gm)::matchall r inp'
                    end
    end.
    Proof.
    Admitted.

Lemma matchall_total: forall r inp, exists l, matchall_matches rer r inp l.
  Proof.
  intros r inp. exists (matchall r inp).
  Admitted.


End FunctionalSemantics.

Section RegexRewrite.
  Context {params: LindenParameters}.


  (* (?:(r)|) *)
  Definition r_or_nil (r : regex) : regex :=
    Disjunction r Epsilon. (* todo capture group ? *)

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
            (greedy_star (lazy_postfix r))
            negative_all)
            (r_or_nil r)).

End RegexRewrite.
