Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics.
From Linden Require Import Parameters.
From Linden Require Import Tactics.
From Warblre Require Import Numeric Base.

(* The subset of regexes supported by the PikeVM engine *)

Section PikeSubset.
  Context {params: LindenParameters}.


  (** * PikeVM supported subset  *)

  (* since the tree of r{0,1} will generate the tree of r{0,0},
     it's quite convenient to add r{0,0} to the language as well *)
  Inductive pike_regex : regex -> Prop :=
  | pike_eps:
    pike_regex Epsilon
  | pike_char:
    forall cd, pike_regex (Regex.Character cd)
  | pike_disj:
    forall r1 r2,
      pike_regex r1 ->
      pike_regex r2 ->
      pike_regex (Disjunction r1 r2)
  | pike_seq:
    forall r1 r2,
      pike_regex r1 ->
      pike_regex r2 ->
      pike_regex (Sequence r1 r2)
  | pike_star:
    forall r1 b,
      pike_regex r1 ->
      pike_regex (Quantified b 0 NoI.Inf r1)
  | pike_qmark:
    forall r1 b,
      pike_regex r1 ->
      pike_regex (Quantified b 0 (NoI.N 1) r1)
  | pike_zero:
    forall r1 b,
      pike_regex (Quantified b 0 (NoI.N 0) r1)
  | pike_group:
    forall g r1,
      pike_regex r1 ->
      pike_regex (Group g r1)
  | pike_anchor:
    forall a, pike_regex (Anchor a).


  (* lifting to actions *)
  Inductive pike_action: action -> Prop :=
  | pike_areg:
    forall r1,
      pike_regex r1 ->
      pike_action (Areg r1)
  | pike_aclose: forall g, pike_action (Aclose g)
  | pike_acheck: forall s, pike_action (Acheck s).

  (* lifting to actions lists *)
  Inductive pike_actions: actions -> Prop :=
  | pike_nil: pike_actions []
  | pike_cons: forall a l,
      pike_action a ->
      pike_actions l ->
      pike_actions (a::l).

  (* only a subset of trees can correspond to a pike regex *)
  Inductive pike_subtree: tree -> Prop :=
  | pike_mismatch: pike_subtree Mismatch
  | pike_match: pike_subtree Match
  | pike_choice: forall t1 t2,
      pike_subtree t1 -> pike_subtree t2 ->
      pike_subtree (Choice t1 t2)
  | pike_read: forall cd t1,
      pike_subtree t1 ->
      pike_subtree (Read cd t1)
  | pike_progress: forall t1,
      pike_subtree t1 ->
      pike_subtree (Progress t1)
  | pike_anchorpass: forall a t1,
      pike_subtree t1 ->
      pike_subtree (AnchorPass a t1)
  | pike_groupaction: forall ga t1,
      pike_subtree t1 ->
      pike_subtree (GroupAction ga t1).

  (* used for the lists of trees gm and input manipulated by the PikeTree and MemoTree algorithms *)
  Definition pike_list (l: list (tree * group_map * input)) : Prop :=
    (forall t gm i, In (t, gm, i) l -> pike_subtree t).

  (* Functional version *)
  Fixpoint is_pike_regex (r:regex) : bool :=
    match r with
    | Epsilon => true
    | Regex.Character _ => true
    | Disjunction r1 r2 => is_pike_regex r1 && is_pike_regex r2
    | Sequence r1 r2 => is_pike_regex r1 && is_pike_regex r2
    | Quantified _ 0 (NoI.N 0) r1 => true
    | Quantified _ 0 NoI.Inf r1 | Quantified _ 0 (NoI.N 1) r1 => is_pike_regex r1
    | Group _ r1 => is_pike_regex r1
    | Anchor _ => true
    | _ => false
    end.

  Lemma is_pike_regex_correct:
    forall r,
      is_pike_regex r = true <-> pike_regex r.
  Proof.
    intros r. split; intros H.
    - induction r; try econstructor; simpl in *; boolprop; eauto; try discriminate.
      (* quatified *)
      destruct min; [|discriminate].
      destruct delta; [|constructor; eauto].
      destruct n; [constructor|].
      destruct n; [constructor; eauto|discriminate].
    - induction H; simpl in *; boolprop; eauto.
  Qed.


  (** * Subset Properties  *)

  Lemma destruct_delta:
    forall d, d = NoI.N 0 \/ d = NoI.N 1 \/ d = NoI.Inf \/ (exists del, d = NoI.N del /\ del > 1).
  Proof.
    intros d. destruct d; auto.
    destruct n; eauto. right. destruct n; eauto. right. right. exists (S (S n)). split; auto. lia.
  Qed.

  Lemma pike_list_cons:
    forall t gm i l,
      pike_list ((t,gm,i)::l) <-> pike_subtree t /\ pike_list l.
  Proof.
    intros t gm i l. unfold pike_list. split; try split; intros. 
    - eapply H; eauto. left. eauto.
    - eapply H; eauto. right. eauto.
    - destruct H. inversion H0; subst.
      + inversion H2. subst. auto.
      + eapply H1. eauto.
  Qed.

  Lemma pike_list_app:
    forall l1 l2,
      pike_list (l1 ++ l2) <-> pike_list l1 /\ pike_list l2.
  Proof.
    intros l1 l2. unfold pike_list. split; try split; intros.
    - eapply H. rewrite in_app_iff. left. eauto.
    - eapply H. rewrite in_app_iff. right. eauto.
    - destruct H. rewrite in_app_iff in H0. destruct H0.
      + eapply H; eauto.
      + eapply H1; eauto.
  Qed.

  Lemma pike_list_empty:
    pike_list [].
  Proof.
    unfold pike_list. intros. inversion H.
  Qed.

  Lemma pike_list_single:
    forall t gm i, pike_subtree t -> pike_list [(t,gm,i)].
  Proof.
    unfold pike_list. intros t gm i H t0 gm0 i0 H0. inversion H0; inversion H1; subst; auto.
  Qed.

  Lemma pike_list_twice:
    forall t1 t2 gm1 gm2 i1 i2, pike_subtree t1 -> pike_subtree t2 -> pike_list [(t1,gm1,i1);(t2,gm2,i2)].
  Proof.
    unfold pike_list. intros t1 t2 gm1 gm2 i1 i2 H H0 t gm i H1.
    inversion H1; inversion H2; try inversion H3; subst; auto.
  Qed.

  (** * Lists of trees and gm  *)
  (* For some algorithms like MemoTree, we might want to manipulate lists of (tree * group_map * input).
     But some algorithms like PikeTree manipulate lists of (tree * group_map), all at the same input.
     We provide a function to supplement a list of (tree * group_map) with a constant input.
   *)

  Definition suppl (l:list (tree * group_map)) (i:input) : list (tree * group_map * input) :=
    List.map (fun tgm => (fst tgm,snd tgm,i)) l.

  Lemma suppl_app:
    forall l1 l2 inp,
      suppl (l1 ++ l2) inp = suppl l1 inp ++ suppl l2 inp.
  Proof.
    intros l1 l2 inp. unfold suppl. rewrite map_app. auto.
  Qed.
  
End PikeSubset.



(* inverting evidence of belonging to the subset *)
Ltac invert_subset := 
  match goal with
  | [ H : pike_list (suppl ((_, _) :: _) _) |- _ ] => simpl in H
  | [ H : pike_list ((_,_,_)::_) |- _ ] => apply pike_list_cons in H; destruct H
  | [ H : pike_list (?tgmi::_) |- _ ] => destruct ?tgmi as [[t gm]i]
  | [ H : pike_list (_ ++ _) |- _ ] => apply pike_list_app in H; destruct H
    
  | [ H : pike_subtree (Choice _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (Read _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (Progress _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (GroupAction _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (ReadBackRef _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (AnchorPass _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (LK _ _ _) |- _ ] => inversion H; clear H
  | [ H : pike_subtree (LKFail _ _) |- _ ] => inversion H; clear H                                       

  | [ H : pike_actions (_ :: _) |- _ ] => inversion H; clear H

  | [ H : pike_action (Areg _) |- _ ] => inversion H; clear H
                                                           
  | [ H : pike_regex (Regex.Character _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Disjunction _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Sequence _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Quantified _ _ _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Group _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Lookaround _ _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Anchor _) |- _ ] => inversion H; clear H
  | [ H : pike_regex (Backreference _) |- _ ] => inversion H; clear H

  | [ |- pike_list (suppl ((_, _) :: _) _) ] => simpl suppl
  | [ |- pike_list (suppl [] _) ] => simpl suppl
  | [ |- pike_list (suppl (_ ++ _) _) ] => rewrite suppl_app
  | [ |- pike_list (_ ++ _) ] => apply pike_list_app; split
  | [ |- pike_list (_ :: _) ] => apply pike_list_cons; split
  | [ |- pike_list [] ] => apply pike_list_empty
  | [ |- pike_list [(_,_,_)] ] => apply pike_list_single
  | [ |- pike_list [(_,_,_);(_,_,_)] ] => apply pike_list_twice
  | [ |- pike_list [?tgmi] ] => destruct ?tgmi as [[t gm]i]

  end.

Ltac pike_subset :=
  repeat (invert_subset; subst); repeat (constructor; auto); auto.

Ltac in_subset :=
  match goal with
  | [ H : ~ pike_regex (Epsilon) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Regex.Character _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Disjunction _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Sequence _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Quantified _ _ _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Group _ _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  | [ H : ~ pike_regex (Anchor _) |- _ ] => try solve[exfalso; apply H; pike_subset]
  end.

Section PikeSubsetLemma.
  Context {params: LindenParameters}.
  (* prove that one can only construct pike subtrees from pike regexes *)
  Lemma pike_actions_pike_tree:
    forall rer cont inp gm dir t,
      pike_actions cont ->
      is_tree rer cont inp gm dir t ->
      pike_subtree t.
  Proof.
    intros rer cont inp gm dir t PIKE ISTREE.
    induction ISTREE; try apply IHISTREE; pike_subset; auto.
    - apply IHISTREE1. pike_subset. 
    - apply IHISTREE2. pike_subset.
    - destruct dir; simpl; pike_subset. 
    - destruct greedy.
      + pike_subset. apply IHISTREE1. destruct plus; inversion H3. pike_subset. 
      + pike_subset. apply IHISTREE1. destruct plus; inversion H3. pike_subset.
    - destruct greedy.
      + pike_subset. apply IHISTREE1. destruct plus; inversion H3. pike_subset.
      + pike_subset. apply IHISTREE1. destruct plus; inversion H3. pike_subset.
    - destruct plus; inversion H3.
    - apply IHISTREE. pike_subset.
  Qed.
End PikeSubsetLemma.
