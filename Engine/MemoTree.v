(** * MemoTree algorithm  *)
(* A backtracking algorithm, with memoization, on trees *)

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import MemoBT PikeTree.


Section MemoTree.
  Context {params: LindenParameters}.
  Context {TS: TSeen params}.

  (* configurations to be explored by the memoized backtracking engine *)
  Definition tree_config: Type := tree * group_map * input.
  Definition tree_stack: Type := list tree_config.

  (* states of the MemoBT algorithm *)
  Inductive mtree_state : Type :=
  | MTree (stk:tree_stack) (ts: seentrees): mtree_state
  | MTree_final (res:option leaf) : mtree_state.

  Definition initial_tree_state (t:tree) (i:input) : mtree_state :=
    MTree [(t, GroupMap.empty, i)] initial_seentrees.

  (** * MemoTree small-step semantics *)

  Inductive exec_tree_result : Type :=
  | TMatch: leaf -> exec_tree_result
  | TExplore: list tree_config -> exec_tree_result.

  Definition TDead : exec_tree_result := TExplore [].

  (* computes the next trees in a depth-first seach order *)
  Definition exec_tree (tc:tree_config) : exec_tree_result :=
    match tc with
    | (t, gm, i) =>
        match t with
        | Mismatch | ReadBackRef _ _ | LK _ _ _ | LKFail _ _ => TDead
        | Match => TMatch (i, gm)
        | Choice t1 t2 => TExplore [(t1,gm,i);(t2,gm,i)]
        | Read _ t1 => TExplore [(t1,gm,next_inp i)]
        | Progress t1 | AnchorPass _ t1 => TExplore [(t1,gm,i)]
        | GroupAction a t1 => TExplore [(t1,GroupMap.update (idx i) a gm, i)]
        end
    end.


  Inductive memotree_step: mtree_state -> mtree_state -> Prop :=
  (* we exhausted all configurations, there is no match *)
  | mtree_nomatch: forall ts,
      memotree_step (MTree [] ts) (MTree_final None)
  (* the memoization allows to skip the current configuration *)
  | mtree_skip:
    forall ts t gm i stk
      (SEEN: inseen ts t = true),
      memotree_step (MTree ((t,gm,i)::stk) ts) (MTree stk ts)
  (* a match is found, we discard the stack *)
  | mtree_match:
    forall ts t gm i leaf stk
      (MATCH: exec_tree (t,gm,i) = TMatch leaf),
      memotree_step (MTree ((t,gm,i)::stk) ts) (MTree_final (Some leaf))
  (* we keep exploring, and add each handled tree to the treeseen set *)
  | mtree_explore:
    forall ts t gm i nextconfs stk
      (EXPLORE: exec_tree (t,gm,i) = TExplore nextconfs),
      memotree_step (MTree ((t,gm,i)::stk) ts) (MTree (nextconfs++stk) (add_seentrees ts t)).

  (** * MemoTree properties  *)

  Theorem memotree_progress:
    forall stk ts,
    exists ms, memotree_step (MTree stk ts) ms.
  Proof.
    intros stk ts. destruct stk as [|[[t gm] i] stk].
    { eexists. econstructor. }
    destruct (exec_tree (t,gm,i)) eqn:EXEC.
    - eexists. eapply mtree_match. eauto.
    - eexists. eapply mtree_explore. eauto.
  Qed.

  (** * MemoTree Correctness  *)
  (* This algorithm always returns the leftmost accepting result of the initial tree *)

  (* Invariant of the MemoTree execution *)
  (* at any moment, all the possible results of the current state are all equal (equal to the first result of the original tree) *)
  (* at any moment, all trees manipulated by the algorithms are trees for the subset of regexes supported  *)
  Inductive memotree_inv: mtree_state -> option leaf -> Prop :=
  | mi:
    forall result stk seen
      (SAMERES: forall res, list_nd stk seen res -> res = result)
      (SUBSET: pike_list stk),
      memotree_inv (MTree stk seen) result
  | mi_final:
    forall result,
      memotree_inv (MTree_final result) result.

  (* This uses the non-deterministic results of the stack, just like the PikeTree proof. *)
  (* Such results can non-deteterministically skip any subtree in the seen set *)

  (** * Initialization  *)
  (* In the initial state, the invariant holds *)

  Lemma init_memotree_inv:
    forall t inp,
      pike_subtree t ->
      memotree_inv (initial_tree_state t inp) (first_leaf t inp).
  Proof.
    intros t. unfold first_leaf. unfold initial_tree_state. constructor; simpl; pike_subset; auto.
    intros res LISTND.
    simpl. apply tree_nd_initial; auto.
    inversion LISTND; subst. inversion TLR; subst. rewrite seqop_none. auto.
  Qed.

  (** * Invariant Preservation  *)

  Theorem memotree_preservation:
    forall ms1 ms2 res
      (MSTEP: memotree_step ms1 ms2)
      (INVARIANT: memotree_inv ms1 res),
      memotree_inv ms2 res.
  Proof.
    intros ms1 ms2 res MSTEP INVARIANT.
    destruct INVARIANT.
    2: { inversion MSTEP. }
    inversion MSTEP; subst; [| | |destruct t; inversion EXPLORE; subst];
      try solve[pike_subset].
    (* no match *)
    - assert (None = result).
      { apply SAMERES. constructor. }
      subst. constructor.
    (* skipping *)
    - constructor; pike_subset. intros res LISTND.
      apply SAMERES. eapply tlr_cons with (l1:=None); eauto.
      apply tr_skip. auto.
    (* match found *)
    - destruct t; inversion MATCH; subst.
      assert (Some (i,gm) = result).
      { apply SAMERES. eapply tlr_cons with (l2:=list_result stk0); try solve[constructor].
        apply list_result_nd. pike_subset. }
      subst. constructor.
    (* Mismatch *)
    - simpl. constructor; pike_subset. intros res LISTND.
      apply SAMERES. eapply tlr_cons; try solve[constructor].
      eapply list_add_seen with (gm:=gm) (inp:=i) in LISTND; eauto.
    (* Choice *)
    - simpl. constructor; pike_subset. intros res LISTND.
      inversion LISTND; subst. inversion TLR; subst.
      apply SAMERES.
      apply add_parent_tree in TR.
      2: { (simpl; lia). }
      apply add_parent_tree in TR0.
      2: { (simpl; lia). }
      assert (PARENT: tree_nd (Choice t1 t2) gm i seen (seqop l1 l0)).
      { apply tr_choice; auto. }
      (* case analysis: did t contribute to the result? *)
      destruct (seqop l1 l0) as [leaf|] eqn:CHOICE.
      + econstructor; eauto.
        * apply list_result_nd. pike_subset.
        * rewrite seqop_assoc. rewrite CHOICE. simpl. auto.
      (* when the tree did not contribute, adding it to seen does not change the results *)
      + destruct l1; destruct l0; inversion CHOICE.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR0; eauto.
        econstructor; eauto.
    (* Read *)
    - simpl. constructor; pike_subset. intros res LISTND.
      inversion LISTND; subst. apply SAMERES.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (Read c t) gm i seen l1).
      { apply tr_read. auto. }
      (* case analysis: did t1 contribute to the result? *)
      destruct l1 as [leaf1|].
      + simpl. eapply tlr_cons; eauto.
        apply list_result_nd; auto.
      (* when the tree did not contribute, adding it to seen does not change the results *)
      + econstructor; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
    (* Progress *)
    - simpl. constructor; pike_subset. intros res LISTND.
      inversion LISTND; subst. apply SAMERES.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (Progress t) gm i seen l1).
      { apply tr_progress. auto. }
      (* case analysis: did t1 contribute to the result? *)
      destruct l1 as [leaf1|].
      + simpl. eapply tlr_cons; eauto.
        apply list_result_nd; auto.
      (* when the tree did not contribute, adding it to seen does not change the results *)
      + econstructor; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
    (* AnchorPass *)
    - simpl. constructor; pike_subset. intros res LISTND.
      inversion LISTND; subst. apply SAMERES.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (AnchorPass a t) gm i seen l1).
      { apply tr_anchorpass. auto. }
      (* case analysis: did t1 contribute to the result? *)
      destruct l1 as [leaf1|].
      + simpl. eapply tlr_cons; eauto.
        apply list_result_nd; auto.
      (* when the tree did not contribute, adding it to seen does not change the results *)
      + econstructor; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
    (* GroupAction *)
    - simpl. constructor; pike_subset. intros res LISTND.
      inversion LISTND; subst. apply SAMERES.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (GroupAction g t) gm i seen l1).
      { apply tr_groupaction. auto. }
      (* case analysis: did t1 contribute to the result? *)
      destruct l1 as [leaf1|].
      + simpl. eapply tlr_cons; eauto.
        apply list_result_nd; auto.
      (* when the tree did not contribute, adding it to seen does not change the results *)
      + econstructor; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
  Qed.

End MemoTree.
