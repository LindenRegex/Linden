(** * Pike Tree Algorithm  *)

(* An algorithm that takes a tree as input, and finds the first or all matches *)
(* Its execution is close to the kind of execution the PikeVM is doing on the bytecode *)
(* It explores multiples ordered branches in parallel, synced with their current input position *)
(* It also records in a "seen" set, *)
(* all the trees it has already started to explore *)
(* Non-deterministically, it can decide not to explore a tree it has already seen *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.

From Linden Require Import Regex Chars Groups Tree.
From Linden Require Import PikeSubset SeenSets PikeVM.
From Linden Require Import Parameters BooleanSemantics Semantics.
From Linden Require Import ListLemmas.
From Warblre Require Import Base RegExpRecord.

(* Read, Progress, Choice, Reset *)
Notation lazy_iter c t1 t2 := (Read c (Progress (Choice t1 (GroupAction (Reset []) t2)))).


Section PikeTree.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).
  Context {TS: TSeen params}.

  Global Opaque seentrees initial_seentrees add_seentrees inseen in_add initial_nothing.

(** * Pike Tree - tree steps  *)

(* returns three things:
 - the list of active trees to explore next. can be empty. Each has its own group map
 - option leaf: a result found
 - option tree: if the tree is blocked consuming a character *)

  Inductive step_result : Type :=
  | StepActive: list (tree * group_map) -> step_result (* generated new active threads, possibly 0 *)
  | StepMatch: step_result                (* a match was found *)
  | StepBlocked: tree -> step_result     (* the thread was blocked *)
  .

  Definition StepDead := StepActive []. (* the thread died *)

  (* this corresponds to an atomic step of a single tree *)
  Definition tree_bfs_step (t:tree) (gm:group_map) (inp:input): step_result :=
    match t with
    | Mismatch | ReadBackRef _ _ | LKFail _ _ => StepDead
    | LK lk tlk t1 =>
      match lk_result lk tlk gm inp with
      | Some gm' => StepActive [(t1, gm')]
      | None => StepDead
      end
    | Match => StepMatch
    | Choice t1 t2 => StepActive [(t1,gm); (t2,gm)]
    | Read c t1 => StepBlocked t1
    | Progress t1 => StepActive [(t1,gm)]
    | AnchorPass a t1 => StepActive [(t1,gm)]
    | GroupAction a t1 => StepActive [(t1, GroupMap.update (idx inp) a gm)]
    end.
  (* trees for unsupported features also return StepDead *)
  (* We could support them in this algorithm, but the only problem is ReadBackref which may advance the string in more than one index *)

  Definition upd_blocked {X:Type} (newblocked: option X) (blocked: list X) :=
    match newblocked with Some b => b::blocked | None => blocked end.

  Definition next_inp (i:input) :=
    advance_input' i forward.

  Lemma advance_next:
    forall i1 i2,
      advance_input i1 forward = Some i2 ->
      next_inp i1 = i2.
  Proof.
    intros i1 i2 H. unfold next_inp, advance_input'. rewrite H. auto.
  Qed.


  (** * Pike Tree Seen Small Step Semantics  *)

  (* The semantic states of the PikeTree algorithm *)
  Inductive pike_tree_state : Type :=
  | PTS (inp:input) (active: list (tree * group_map)) (occ: occurrence) (blocked: list (tree * group_map)) (future: option tree) (seen:seentrees)
  | PTS_final (occ: occurrence).

  (* when generating a new active tree at the beginning, or when doing the acceleration step,
     we may erase the new `future` as long as it does not contain a result.
     This corresponds to the PikeVM behavior where, after generating or skipping, literal
     search returns that there is no possible match for the prefix anymore. *)
  Inductive may_erase: tree -> option tree -> Prop :=
  | no_erase:
    forall t, may_erase t (Some t)
  | erases:
    forall t inp (NORES: first_leaf t inp = None),
      may_erase t None.

  (* the initial future for the unanchored version of the PikeTree *)
  Definition initial_future_actions_unanchored (r: regex) (inp: input) :=
    [Areg (Regex.Character CdAll); Acheck inp; Areg dot_star; Areg r].
  Definition future_tree_shape (r: regex) (inp: input) (future: tree): Prop :=
    bool_tree rer (initial_future_actions_unanchored r inp) inp CannotExit forward future.
  Definition initial_future_unanchored (r: regex) (inp: input) (future: option tree): Prop :=
    exists tree, future_tree_shape r inp tree /\ may_erase tree future.


  Definition pike_tree_initial_tree (t: tree) := (t, GroupMap.empty).
  (* LATER: consider redefining as an inductive. This will simplify stating
    "there exists an initial state" which is useful, since we care about particular
    initializations of the PikeTree which follow the PikeVM execution *)
  Definition pike_tree_initial_state_unanchored (t:tree) (future:option tree) (i:input) (occ:occurrence): pike_tree_state :=
    PTS i [pike_tree_initial_tree t] occ [] future initial_seentrees.
  Definition pike_tree_initial_state (t:tree) (i:input) (occ:occurrence): pike_tree_state :=
    PTS i [pike_tree_initial_tree t] occ [] None initial_seentrees.

  (* non-deterministic acceleration by skipping head branches with no results *)
  (* `tree_acceleration inp future inp' future' t` means that for future tree at *)
  (* input inp, inp' is the input position we accelerated to, future' is the new *)
  (* future tree, and t is new active tree. This corresponds to the acceleration *)
  (* step in PikeVM which skips input characters where the prefix does not match. *)
  Inductive tree_acceleration : input -> tree -> input -> tree -> tree -> Prop :=
  | acc_keep:
      forall inp c next pref future t1 t2
        (INPUT: inp = Input (c::next) pref)
        (FUTURE: future = lazy_iter c t1 t2),
      tree_acceleration inp future (Input next (c::pref)) t2 t1
  | acc_skip:
      forall inp c next pref future t1 t2 nextinp acc t
        (INPUT: inp = Input (c::next) pref)
        (FUTURE: future = lazy_iter c t1 t2)
        (LEAF: first_leaf t1 (Input next (c::pref)) = None)
        (TRANS: tree_acceleration (Input next (c::pref)) t2 nextinp acc t),
        tree_acceleration inp future nextinp acc t.

  (* Small-step semantics for the PikeTree algorithm *)
  Inductive pike_tree_step : pike_tree_state -> pike_tree_state -> Prop :=
  | pts_skip:
  (* skip an active tree if it has been seen before *)
  (* this is non-deterministic, we can also not skip it by using the other rules *)
    forall inp t gm active occ blocked future seen
      (SEEN: inseen seen t = true),
      pike_tree_step (PTS inp ((t,gm)::active) occ blocked future seen) (PTS inp active occ blocked future seen)
  | pts_acc:
  (* if there are no more active or blocked trees and we have some future, *)
  (* we accelerate by non-deterministically skipping branches with no results *)
    forall inp occ seen nextinp future acc t next_future
      (ACC: tree_acceleration inp future nextinp acc t)
      (ERASE: may_erase acc next_future),
      pike_tree_step (PTS inp [] occ [] (Some future) seen) (PTS nextinp [pike_tree_initial_tree t] occ [] next_future initial_seentrees)
  | pts_final:
  (* moving to a final state when there are no more active or blocked trees *)
    forall inp occ future seen
      (LEAF: option_flat_map (fun t => tree_leaves t GroupMap.empty inp forward) future = []),
      pike_tree_step (PTS inp [] occ [] future seen) (PTS_final occ)
  | pts_nextchar:
    (* when the list of active trees is empty, restart from the blocked ones, proceeding to the next character *)
    (* resetting the seen trees *)
    forall inp occ blocked tgm seen,
      pike_tree_step (PTS inp [] occ (tgm::blocked) None seen) (PTS (next_inp inp) (tgm::blocked) occ [] None initial_seentrees)
  | pts_nextchar_generate:
    (* when the list of active trees is empty and the next tree is a segment of a lazy star prefix, *)
    (* restart from the blocked ones and the head iteration of the lazy star, proceeding to the next character *)
    (* resetting the seen trees *)
    forall inp c next pref occ blocked tgm future t1 t2 seen next_future
      (INPUT: inp = Input (c::next) pref)
      (FUTURE: future = Some (lazy_iter c t1 t2))
      (ERASE: may_erase t2 next_future),
      pike_tree_step (PTS inp [] occ (tgm::blocked) future seen) (PTS (Input next (c::pref)) ((tgm::blocked) ++ [pike_tree_initial_tree t1]) occ [] next_future initial_seentrees)
  | pts_nextchar_filter:
    (* when the list of active trees is empty and the next tree is a segment of a lazy star prefix, *)
    (* and the head iteration of the lazy star contains no result, *)
    (* restart from the blocked ones, proceeding to the next character *)
    (* resetting the seen trees *)
    forall inp c next pref occ blocked tgm future t1 t2 seen
      (INPUT: inp = Input (c::next) pref)
      (FUTURE: future = Some (lazy_iter c t1 t2))
      (LEAF: first_leaf t1 (Input next (c::pref)) = None),
      pike_tree_step (PTS inp [] occ (tgm::blocked) future seen) (PTS (Input next (c::pref)) (tgm::blocked) occ [] (Some t2) initial_seentrees)
  | pts_active:
    (* generated new active trees: add them in front of the low-priority ones *)
    forall inp t gm active occ blocked future nextactive seen1 seen2
      (STEP: tree_bfs_step t gm inp = StepActive nextactive)
      (ADD_SEEN: add_seentrees seen1 t = seen2),
      pike_tree_step (PTS inp ((t,gm)::active) occ blocked future seen1) (PTS inp (nextactive++active) occ blocked future seen2)
  | pts_match:
    (* a match is found, discard remaining low-priority active trees *)
    forall inp t gm active active' occ occ' blocked future seen1 seen2
      (STEP: tree_bfs_step t gm inp = StepMatch)
      (ADD_SEEN: add_seentrees seen1 t = seen2)
      (ACC: accept occ inp gm active = (active', occ')),
      pike_tree_step (PTS inp ((t,gm)::active) occ blocked future seen1) (PTS inp active' occ' blocked None seen2)
  | pts_blocked:
  (* add the new blocked thread after the previous ones *)
    forall inp t gm active occ blocked newt future seen1 seen2
      (STEP: tree_bfs_step t gm inp = StepBlocked newt)
      (ADD_SEEN: add_seentrees seen1 t = seen2),
      pike_tree_step (PTS inp ((t,gm)::active) occ blocked future seen1) (PTS inp active occ (blocked ++ [(newt,gm)]) future seen2).


  Lemma tree_acceleration_pike_subtree:
    forall inp future nextinp acc t,
      tree_acceleration inp future nextinp acc t ->
      pike_subtree future ->
      pike_subtree acc /\ pike_subtree t.
  Proof.
    intros inp future nextinp acc t ACC SUBSET.
    induction ACC; subst.
    - pike_subset.
    - apply IHACC. pike_subset.
  Qed.

  Lemma tree_acceleration_bool_tree:
    forall r inp future nextinp acc t,
      future_tree_shape r inp future ->
      tree_acceleration inp future nextinp acc t ->
      bool_tree rer [Areg r] nextinp CanExit forward t /\ future_tree_shape r nextinp acc.
  Proof.
    unfold future_tree_shape, initial_future_actions_unanchored.
    intros r inp future nextinp acc t FUTURE ACC.
    induction ACC; subst; [|apply IHACC].
    all:
      inversion FUTURE; inversion TREECONT; inversion TREECONT0;
      inversion READ; inversion CHOICE;
      destruct plus; [discriminate|]; now subst.
  Qed.

  Lemma tree_acceleration_advances_input:
    forall inp future nextinp acc t,
      tree_acceleration inp future nextinp acc t ->
      length (next_str nextinp) < length (next_str inp).
  Proof. induction 1; subst; simpl in *; lia. Qed.

  Lemma tree_acceleration_input_irreflexive:
    forall inp future acc t,
      ~tree_acceleration inp future inp acc t.
  Proof.
    intros inp future acc t H.
    apply tree_acceleration_advances_input in H.
    lia.
  Qed.

  (** * Pike Tree Seen Correction  *)


  (** * Non-deterministic tree results *)
  (* any possible results after skipping or not any sub-tree in the seen set *)
  Inductive tree_nd: tree -> group_map -> input -> seentrees -> list leaf -> Prop :=
  | tr_skip:
    forall seen t gm inp
      (SEEN: inseen seen t = true),
      tree_nd t gm inp seen []
  | tr_mismatch:
    forall gm inp seen, tree_nd Mismatch gm inp seen []
  | tr_match:
    forall gm inp seen, tree_nd Match gm inp seen [(inp,gm)]
  | tr_choice:
    forall t1 t2 gm inp l1 l2 seen
      (TR1: tree_nd t1 gm inp seen l1)
      (TR2: tree_nd t2 gm inp seen l2),
      tree_nd (Choice t1 t2) gm inp seen (l1 ++ l2)
  | tr_read:
    forall t cd gm inp l seen
      (TR: tree_nd t gm (next_inp inp) seen l),
      tree_nd (Read cd t) gm inp seen l
  | tr_progress:
    forall t gm inp l seen
      (TR: tree_nd t gm inp seen l),
      tree_nd (Progress t) gm inp seen l
  | tr_anchorpass:
    forall a t gm inp l seen
      (TR: tree_nd t gm inp seen l),
      tree_nd (AnchorPass a t) gm inp seen l
  | tr_groupaction:
    forall t act gm inp l seen
      (TR: tree_nd t (GroupMap.update (idx inp) act gm) inp seen l),
      tree_nd (GroupAction act t) gm inp seen l
  | tr_lookaround:
    forall lk tlk t gm gm' inp l seen
      (RES_LK: lk_result lk tlk gm inp = Some gm')
      (TR: tree_nd t gm' inp seen l),
      tree_nd (LK lk tlk t) gm inp seen l
  (* When the tree is constructed by `is_tree`, this case can never happen *)
  (* since LK tree node is constructed only when `lk_result` returns `Some`. *)
  (* However, here we operate on arbitrary trees so we must handle this case. *)
  | tr_lookaroundnone:
    forall lk tlk t gm inp seen
      (RES_LK: lk_result lk tlk gm inp = None),
      tree_nd (LK lk tlk t) gm inp seen []
  | tr_lookaroundfail:
    forall lk tlk gm inp seen, tree_nd (LKFail lk tlk) gm inp seen [].

  (* the normal result, obtained with function tree_leaves without skipping anything, is a possible result *)
  Lemma tree_leaves_nd:
    forall t gm inp seen,
      pike_subtree t ->
      tree_nd t gm inp seen (tree_leaves t gm inp forward).
  Proof.
    induction t; intros; simpl; try solve[pike_subset]; try solve[constructor; auto].
    (* lookarounds *)
    destruct positivity eqn:Hpos, tree_leaves eqn:Hres; try destruct l.
    - eapply tr_lookaroundnone. unfold lk_result.
      rewrite <-first_tree_empty in Hres.
      now rewrite Hpos, Hres.
    - eapply first_tree_some in Hres.
      eapply tr_lookaround.
      + unfold lk_result. now rewrite Hpos, Hres.
      + eapply IHt2; pike_subset.
    - rewrite <-first_tree_empty in Hres.
      eapply tr_lookaround.
      + unfold lk_result. now rewrite Hpos, Hres.
      + eapply IHt2; pike_subset.
    - eapply tr_lookaroundnone. unfold lk_result.
      eapply first_tree_some in Hres.
      now rewrite Hpos, Hres.
  Qed.

  (* when there is nothing in seen, there is only one possible result *)
  Lemma tree_nd_initial:
    forall t gm inp res,
      pike_subtree t ->
      tree_nd t gm inp initial_seentrees res ->
      res = tree_leaves t gm inp forward.
  Proof.
    intros t gm inp res PIKE H.
    remember initial_seentrees as init.
    induction H; simpl; pike_subset; auto.
    - subst. rewrite initial_nothing in SEEN. inversion SEEN.
    - pike_subset. specialize (IHtree_nd1 H3 eq_refl).
      specialize (IHtree_nd2 H4 eq_refl). subst. auto.
    - unfold lk_result in RES_LK.
      destruct positivity, (tree_leaves tlk) eqn:Hleaves; try destruct l0;
        (rewrite <-first_tree_empty in Hleaves || eapply first_tree_some in Hleaves); rewrite Hleaves in RES_LK;
        easy || (injection RES_LK as <-; eauto).
    - unfold lk_result in RES_LK.
      destruct positivity, (tree_leaves tlk) eqn:Hleaves; try destruct l;
        (rewrite <-first_tree_empty in Hleaves || eapply first_tree_some in Hleaves); rewrite Hleaves in RES_LK; easy.
  Qed.

  (** * List Results  *)
  (* all possible results in a list of trees - deterministic and non-deterministic versions *)

  Definition list_result (l:list (tree * group_map * input)) : list leaf :=
    flat_map (fun tgmi => tree_leaves (fst (fst tgmi)) (snd (fst tgmi)) (snd tgmi) forward) l.

  Lemma list_result_app:
    forall l1 l2,
      list_result (l1 ++ l2) = (list_result l1) ++ (list_result l2).
  Proof.
    induction l1; intros; auto; simpl.
    now rewrite <-app_assoc, IHl1.
  Qed.

  Inductive list_nd: list (tree * group_map * input) -> seentrees -> list leaf -> Prop :=
  | tlr_nil:
    forall seen, list_nd [] seen []
  | tlr_cons:
    forall t gm active inp seen l1 l2 l3
      (TR: tree_nd t gm inp seen l1)
      (TLR: list_nd active seen l2)
      (SEQ: l3 = l1 ++ l2),
      list_nd ((t,gm,inp)::active) seen l3.

  (* the normal result for a list, without skipping anything, is a possible result *)
  Lemma list_result_nd:
    forall active seen,
      pike_list active ->
      list_nd active seen (list_result active).
  Proof.
    intros active. induction active; try destruct a as [[t gm] i]; intros; pike_subset; try constructor.
    simpl; econstructor; eauto. apply tree_leaves_nd. auto.
  Qed.

  (* when there is nothing in seen, there is only one possible result *)
  Lemma list_nd_initial:
    forall l res,
      pike_list l ->
      list_nd l initial_seentrees res ->
      res = list_result l.
  Proof.
    intros l res PIKE H.
    remember initial_seentrees as init.
    induction H; simpl; auto; pike_subset.
    apply tree_nd_initial in TR as <-; eauto.
    now rewrite IHlist_nd.
  Qed.

  (** * Non deterministic results lemmas  *)

  (* when lk_result returns none, it is independent of the gm and the inp *)
  Lemma lk_result_indep_none:
    forall lk tlk gm1 gm2 inp1 inp2,
      lk_result lk tlk gm1 inp1 = None ->
      lk_result lk tlk gm2 inp2 = None.
  Proof.
    unfold lk_result.
    intros lk tlk gm1 gm2 inp1 inp2 H.
    destruct positivity, tree_res eqn:Hres.
    - now destruct l.
    - erewrite res_indep; eauto.
    - now eapply res_indep_some in Hres as [l' ->].
    - easy.
  Qed.

  (* when lk_result returns some, it is independent of the gm and the inp *)
  Lemma lk_result_indep_some:
    forall lk tlk gm1 gm2 inp1 inp2 res1,
      lk_result lk tlk gm1 inp1 = Some res1 ->
      exists res2, lk_result lk tlk gm2 inp2 = Some res2.
  Proof.
    unfold lk_result.
    intros lk tlk gm1 gm2 inp1 inp2 res1 H.
    destruct positivity, tree_res eqn:Hres; try discriminate.
    - eapply res_indep_some in Hres as [l' ->].
      destruct l'. eauto.
    - erewrite res_indep; eauto.
  Qed.

  (* a tree_nd having no results is independent of the gm and the inp *)
  Lemma no_tree_result_nd:
    forall t seen gm1 gm2 inp1 inp2
      (NORES: tree_nd t gm1 inp1 seen []),
      tree_nd t gm2 inp2 seen [].
  Proof.
    induction t; intros;
      try solve[inversion NORES; subst; try solve[constructor; auto]; try solve [constructor; eapply IHt; eauto]].
    - inversion NORES; subst.
      + apply tr_skip. auto.
      + destruct l1, l2; inversion H.
        apply tr_choice; eauto.
    - inversion NORES; subst.
      + apply tr_skip. auto.
      + eapply lk_result_indep_some in RES_LK as [gm'' RES_LK''].
        eapply tr_lookaround; eauto.
      + eapply tr_lookaroundnone.
        eapply lk_result_indep_none; eauto.
  Qed.

  (* skipping over a new tree doesn't change the result if the tree that is being skipped does not have results *)
  Lemma add_seen:
    forall t seen tseen gm inp res
      (NORES: tree_leaves tseen gm inp forward = [])
      (TREEND: tree_nd t gm inp (add_seentrees seen tseen) res)
      (SUBSET: pike_subtree tseen),
      tree_nd t gm inp seen res.
  Proof.
    intros t seen tseen gm inp res NORES TREEND SUBSET.
    remember (add_seentrees seen tseen) as add.
    induction TREEND; subst; try solve[constructor; auto];
      try solve [econstructor; eauto; apply IHTREEND; auto; eapply leaves_indep; eauto].
    apply in_add in SEEN as [EQ | SEEN].
    - subst. rewrite <- NORES. apply tree_leaves_nd; auto.
    - apply tr_skip. auto.
  Qed.

  (* same lemma generalizes to lists of trees *)
  Lemma list_add_seen:
    forall l seen tseen gm inp res
      (NORES: tree_leaves tseen gm inp forward = [])
      (LISTND: list_nd l (add_seentrees seen tseen) res)
      (SUBSET: pike_subtree tseen),
      list_nd l seen res.
  Proof.
    intros l seen tseen gm inp res NORES LISTND SUBSET.
    remember (add_seentrees seen tseen) as add.
    induction LISTND; subst; econstructor; eauto.
    eapply add_seen; eauto. eapply leaves_indep; eauto.
  Qed.

  (* skipping over a new tree doesn't change the result if the tree that is being skipped can produce a None result *)
  Lemma add_seen_nd:
    forall t seen tseen gm inp res
      (NORES: tree_nd tseen gm inp seen [])
      (TREEND: tree_nd t gm inp (add_seentrees seen tseen) res),
      tree_nd t gm inp seen res.
  Proof.
    intros t seen tseen gm inp res NORES TREEND.
    remember (add_seentrees seen tseen) as add.
    induction TREEND; subst; try solve[constructor; auto];
      try solve [econstructor; eauto; apply IHTREEND; auto; eapply no_tree_result_nd; eauto].
    - apply in_add in SEEN as [EQ | SEEN].
      + subst. apply NORES.
      + apply tr_skip. auto.
  Qed.

  (* same lemma generalizes to lists of trees *)
  Lemma list_add_seen_nd:
    forall l seen tseen gm inp res
      (NORES: tree_nd tseen gm inp seen [])
      (LISTND: list_nd l (add_seentrees seen tseen) res),
      list_nd l seen res.
  Proof.
    intros l seen tseen gm inp res NORES LISTND.
    remember (add_seentrees seen tseen) as add.
    induction LISTND; subst; econstructor; eauto.
    eapply add_seen_nd; eauto. eapply no_tree_result_nd; eauto.
  Qed.

  (* using the size of the tree will help us make sure that whenever a tree generates active subtrees, *)
  (* none of these subtrees can contain the parent tree that generated them *)
  Fixpoint size (t:tree) : nat :=
    match t with
    | Mismatch | Match | LKFail _ _ => O
    | Read _ t1 | Progress t1 | GroupAction _ t1 | AnchorPass _ t1 | ReadBackRef _ t1 => 1 + size t1
    | Choice t1 t2 => size t1 + size t2 + 1
    | LK _ tlk t1 => 1 + size t1
    end.

  (* skipping over a new tree does not change the result of another tree if we know that the newly *)
  (* skipped over tree cannot appear in the tree we compute the result of *)
  Lemma add_parent_tree:
    forall tseen t res seen gm inp
      (SIZE: size t < size tseen)
      (TREEND: tree_nd t gm inp (add_seentrees seen tseen) res),
      tree_nd t gm inp seen res.
  Proof.
    intros tseen t res seen gm inp SIZE TREEND.
    remember (add_seentrees seen tseen) as add.
    induction TREEND; subst; simpl in SIZE;
      try solve [econstructor; eauto; apply IHTREEND; auto; lia].
    - apply in_add in SEEN as [EQ | SEEN].
      + subst. exfalso. eapply PeanoNat.Nat.lt_irrefl. eauto.
      + apply tr_skip. auto.
    - constructor.
      + apply IHTREEND1; auto. lia.
      + apply IHTREEND2; auto. lia.
  Qed.

  Definition occurrences (occ: occurrence) : list leaf :=
    match occ with
    | Best (Some best) => [best]
    | Best None => []
    | All positions => positions
    end.

  (* the `occurrence` is compatible with the list of leaves *)
  Definition occurrence_compat (occ: occurrence) (leaves: list leaf) : Prop :=
    match occ with
    (* when tracking only the best position, it must be the head of the list *)
    | Best best => best = hd_error leaves
    (* when tracking all positions, they must contain the same elements as the list *)
    | All positions => list_ext positions leaves
    end.

  (* whether two occurrences are of the same kind *)
  Definition same_occurrence_kind (occ1 occ2: occurrence) : Prop :=
    match occ1, occ2 with
    | Best _, Best _ => True
    | All _, All _ => True
    | _, _ => False
    end.

  Inductive state_nd: input -> list (tree*group_map) -> occurrence -> list (tree*group_map) -> option tree -> seentrees -> occurrence -> Prop :=
  | sr:
    forall blocked active occ inp future seen r1 r2 r3 occseq
      (BLOCKED: list_result (suppl blocked (next_inp inp)) = r1)
      (ACTIVE: list_nd (suppl active inp) seen r2)
      (FUTURE: option_flat_map (fun t => tree_leaves t GroupMap.empty inp forward) future = r3)
      (SEQ: occurrence_compat occseq (r1 ++ r2 ++ r3 ++ occurrences occ))
      (SAMEKIND: same_occurrence_kind occ occseq),
      state_nd inp active occ blocked future seen occseq.

  (* Invariant of the PikeTree execution *)
  (* at any moment, all the possible results of the current state are all compatible (equal to the first result of the original tree or have the same positions) *)
  (* at any moment, all trees manipulated by the algorithms are trees for the subset of regexes supported  *)
  Inductive piketreeinv: pike_tree_state -> list leaf -> Prop :=
  | pi:
    forall leaves blocked active occ inp future seen
      (COMPAT: forall occres, state_nd inp active occ blocked future seen occres -> occurrence_compat occres leaves)
      (SUBSET_AC: pike_list (suppl active inp))
      (SUBSET_BL: pike_list (suppl blocked (next_inp inp)))
      (SUBSET_FU: match future with | Some t => pike_subtree t | None => True end),
      piketreeinv (PTS inp active occ blocked future seen) leaves
  | sr_final:
    forall occ leaves,
      occurrence_compat occ leaves ->
      piketreeinv (PTS_final occ) leaves.

  (** * Non-deterministic results of empty trees  *)
  Lemma state_nd_future_none:
    forall inp active best blocked future seen res,
      tree_leaves future GroupMap.empty inp forward = [] ->
      state_nd inp active best blocked None seen res ->
      state_nd inp active best blocked (Some future) seen res.
  Proof.
    intros inp active best blocked future seen res ERASE ND.
    inversion ND; subst. simpl in ND.
    econstructor; eauto.
  Qed.

  Theorem state_nd_erase:
    forall inp active best blocked future seen res erased,
      may_erase future erased ->
      state_nd inp active best blocked erased seen res ->
      state_nd inp active best blocked (Some future) seen res.
  Proof.
    intros inp active best blocked future seen res erased ERASE ND.
    inversion ERASE; subst; auto.
    unfold first_leaf in NORES. rewrite first_tree_empty in NORES.
    eapply state_nd_future_none; eauto using leaves_indep.
  Qed.


  (** * Initialization  *)

  (* In the initial state, the invariant holds *)

  Ltac occ_simpl :=
    match goal with
    | SAMEKIND: same_occurrence_kind (Best _) ?occ |- _ =>
      destruct occ; [clear SAMEKIND|inversion SAMEKIND];
      match goal with
      | SEQ: occurrence_compat (Best _) _ |- _ => simpl in SEQ; subst
      | _ => idtac
      end
    | SAMEKIND: same_occurrence_kind (All _) ?occ |- _ =>
      destruct occ; [inversion SAMEKIND|clear SAMEKIND];
      match goal with
      | SEQ: occurrence_compat (All _) _ |- _ => simpl in SEQ
      | _ => idtac
      end
    | _ => idtac
    end.

  Ltac inv_state_nd :=
    match goal with
    | H: state_nd _ _ _ _ _ _ _ |- _ =>
      inversion_clear H;
      occ_simpl;
      subst; simpl
    end.

  Lemma init_piketree_inv:
    forall t inp occ,
      pike_subtree t ->
      occ = Best None \/ occ = All [] ->
      piketreeinv (pike_tree_initial_state t inp occ) (tree_leaves t GroupMap.empty inp forward).
  Proof.
    unfold pike_tree_initial_state.
    intros t inp occ Hsubset Hocc. constructor; simpl; pike_subset.
    intros res STATEND. inv_state_nd.
    inversion ACTIVE; subst. inversion TLR; subst.
    apply tree_nd_initial in TR as <-; auto.
    destruct Hocc; subst; occ_simpl; now rewrite !app_nil_r in *.
  Qed.

  Lemma init_piketree_inv_unanchored:
    forall t r inp tree future occ,
      pike_regex r ->
      initial_future_unanchored r inp future ->
      bool_tree rer [Areg r] inp CanExit forward t ->
      bool_tree rer [Areg (lazy_prefix r)] inp CanExit forward tree ->
      occ = Best None \/ occ = All [] ->
      piketreeinv (pike_tree_initial_state_unanchored t future inp occ) (tree_leaves tree GroupMap.empty inp forward).
  Proof.
    unfold initial_future_unanchored, future_tree_shape.
    intros t r inp tree future occ PIKEREG [tree' [FUTURESHAPE FUTUREINIT]] T TREE Hocc.
    assert (pike_subtree t). {
      eapply pike_actions_pike_tree; try eapply bool_to_istree_regex with (gm:=GroupMap.empty); eauto; pike_subset.
    }
    destruct FUTUREINIT as [future|].
    {
      assert (pike_subtree future). {
        eapply subset_semantics; eauto; pike_subset.
      }
      assert (Heq: tree = Choice t (GroupAction (Reset []) future)). {
        inversion TREE; inversion CONT; destruct plus; [discriminate|]; subst.
        apply bool_tree_determ with (t1:=titer) in FUTURESHAPE; auto.
        apply bool_tree_determ with (t1:=tskip) in T; auto.
        now subst.
      }
      unfold pike_tree_initial_state_unanchored. constructor; simpl; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      inversion ACTIVE; subst. inversion TLR; subst.
      apply tree_nd_initial in TR as <-; auto.
      destruct Hocc; subst; occ_simpl; now rewrite !app_nil_r in *.
    }
    {
      unfold first_leaf in NORES.
      rewrite first_tree_empty in NORES.
      (* if we initialize future to None, this is exactly init_piketree_inv *)
      assert (Heq: tree_leaves tree GroupMap.empty inp forward = tree_leaves t GroupMap.empty inp forward). {
        inversion TREE. inversion CONT. destruct plus; [discriminate|subst].
        replace titer with t0 by eauto using bool_tree_determ.
        replace tskip with t by eauto using bool_tree_determ.
        simpl.
        apply leaves_indep with (inp2:=inp) (gm2:=GroupMap.empty) (dir2:=forward) in NORES as ->.
        now rewrite app_nil_r.
      } rewrite Heq.
      now eapply init_piketree_inv.
    }
  Qed.

  (** * Invariant Preservation  *)

  Lemma tree_acceleration_pts_preservation:
    forall inp best future nextinp acc t res seen next_future,
      pike_subtree future ->
      tree_acceleration inp future nextinp acc t ->
      state_nd nextinp [pike_tree_initial_tree t] best [] (Some acc) initial_seentrees res ->
      may_erase acc next_future ->
      state_nd inp [] best [] (Some future) seen res.
  Proof.
    intros inp best future nextinp acc t res seen next_future SUBSET ACC STATEND ERASE.
    pose proof (tree_acceleration_pike_subtree _ _ _ _ _ ACC SUBSET) as [SUBSET_ACC SUBSET_T].
    inv_state_nd.
    apply list_nd_initial in ACTIVE; simpl; pike_subset.
    econstructor; try econstructor || eauto. subst.
    unfold list_result.
    induction ACC; subst; simpl; unfold advance_input', advance_input; simpl in *.
    - now rewrite app_nil_r, app_assoc in SEQ.
    - unfold first_leaf in LEAF.
      rewrite first_tree_empty in LEAF.
      rewrite LEAF.
      apply IHACC; eauto; pike_subset.
  Qed.

  (* we can freely append from the left without affecting the equality of two hd_error *)
  Lemma hd_error_app_l {A}:
    forall (l1 l2 l: list A),
      hd_error l1 = hd_error l2 ->
      hd_error (l ++ l1) = hd_error (l ++ l2).
  Proof. now destruct l. Qed.

  Theorem pts_preservation:
    forall pts1 pts2 res
      (PSTEP: pike_tree_step pts1 pts2)
      (INVARIANT: piketreeinv pts1 res),
      piketreeinv pts2 res.
  Proof.
    intros pts1 pts2 res PSTEP INVARIANT.
    destruct INVARIANT.
    2: { inversion PSTEP. }
    inversion PSTEP; subst; [| | | | | |destruct t; inversion STEP; subst| |].
    (* skipping *)
    - constructor; pike_subset; auto.
      intros res STATEND.
      apply COMPAT. inv_state_nd.
      econstructor; eauto.
      eapply tlr_cons with (l1:=[]); eauto. apply tr_skip. auto.
    (* acceleration *)
    - pose proof (tree_acceleration_pike_subtree _ _ _ _ _ ACC SUBSET_FU) as [SUBSET_ACC SUBSET_T].
      constructor; pike_subset; auto.
      2, 3: destruct next_future; inversion ERASE; subst; simpl; pike_subset.
      intros res STATEND. apply COMPAT.
      eapply state_nd_erase in STATEND as ERASEND; eauto.
      inversion ERASE; subst; eapply tree_acceleration_pts_preservation; eauto.
    (* final *)
    - constructor.
      apply COMPAT. econstructor; try econstructor.
      + rewrite LEAF. destruct occ; simpl.
        * now destruct best.
        * easy.
      + now destruct occ.
    (* nextchar *)
    - constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      apply list_nd_initial in ACTIVE; pike_subset.
      simpl. subst.
      apply COMPAT. econstructor; eauto using tlr_nil.
    (* nextchar_generate *)
    - constructor; pike_subset; auto.
      2, 3: destruct next_future; inversion ERASE; subst; simpl; pike_subset.
      intros res STATEND. apply COMPAT.
      inv_state_nd.
      apply list_nd_initial in ACTIVE; pike_subset.
      2: simpl; pike_subset.
      econstructor; eauto using tlr_nil. simpl in *. unfold next_inp, advance_input', advance_input.
      subst.
      rewrite suppl_app, list_result_app, app_assoc in SEQ.
      unfold list_result at 2 in SEQ.
      simpl in SEQ. rewrite app_nil_r in SEQ.
      inversion ERASE; subst; simpl in SEQ.
      (* we did not erase `future` *)
      * now repeat rewrite app_assoc in *.
      (* we erased `future` *)
      * unfold first_leaf in NORES.
        rewrite first_tree_empty in NORES.
        eapply leaves_indep in NORES.
        rewrite NORES.
        now repeat rewrite app_assoc in *.
    (* nextchar_filter *)
    - constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      apply list_nd_initial in ACTIVE; pike_subset.
      subst.
      apply COMPAT.
      econstructor; eauto using tlr_nil.
      unfold first_leaf in LEAF.
      rewrite first_tree_empty in LEAF.
      simpl in *. unfold next_inp, advance_input', advance_input.
      now rewrite LEAF.
    (* mismatch *)
    - simpl. constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      apply COMPAT.
      econstructor; eauto. econstructor; eauto.
      * eapply tr_mismatch.
      * eapply list_add_seen with (gm:=gm) (inp:=inp) in ACTIVE; eauto.
      * eauto.
    (* choice *)
    - simpl. constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      inversion ACTIVE; subst. inversion TLR; subst.
      apply COMPAT.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      apply add_parent_tree in TR0.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (Choice t1 t2) gm inp seen (l1 ++ l0)).
      { apply tr_choice; auto. }
      (* case analysis: did t contribute to the result? *)
      destruct (l1 ++ l0) eqn:CHOICE.
      (* when the tree did not contribute, adding it to seen does not change the results *)
      * destruct l1, l0; inversion CHOICE.
        econstructor; simpl; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR0; eauto.
        econstructor; eauto.
      * destruct occ; occ_simpl.
        -- rewrite app_assoc with (l:=l1), CHOICE.
           eapply sr with (r2:=(l :: l2) ++ (list_result (suppl active0 inp))); simpl; eauto using hd_error_app_l.
           econstructor; eauto using list_result_nd.
        -- admit.
    (* progress fail *)
    - simpl. constructor; pike_subset; auto.
    (* progress *)
    - simpl. constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      inversion ACTIVE; subst.
      apply COMPAT.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (Progress t) gm inp seen l1).
      { apply tr_progress; auto. }
      (* case analysis: did t contribute to the result? *)
      destruct l1 as [|leaf1].
      (* when the tree did not contribute, adding it to seen does not change the results *)
      * econstructor; simpl; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
        econstructor; eauto.
      * destruct occ; occ_simpl.
        -- eapply sr with (r2:=(leaf1 :: l1) ++ (list_result (suppl active0 inp))); simpl; eauto using hd_error_app_l.
           econstructor; eauto using list_result_nd.
        -- admit.
    (* anchor pass *)
    - constructor; simpl; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      inversion ACTIVE; subst.
      apply COMPAT.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (AnchorPass a t) gm inp seen l1).
      { apply tr_anchorpass; auto. }
      (* case analysis: did t contribute to the result? *)
      destruct l1 as [|leaf1].
      (* when the tree did not contribute, adding it to seen does not change the results *)
      * econstructor; simpl; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
        econstructor; eauto.
      * destruct occ; occ_simpl.
        -- eapply sr with (r2:=(leaf1 :: l1) ++ (list_result (suppl active0 inp))); simpl; eauto using hd_error_app_l.
           econstructor; eauto using list_result_nd.
        -- admit.
    (* group action *)
    - simpl. constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      inversion ACTIVE; subst.
      apply COMPAT.
      apply add_parent_tree in TR.
      2: { simpl. lia. }
      assert (PARENT: tree_nd (GroupAction g t) gm inp seen l1).
      { apply tr_groupaction; auto. }
      (* case analysis: did t contribute to the result? *)
      destruct l1 as [|leaf1].
      (* when the tree did not contribute, adding it to seen does not change the results *)
      + econstructor; simpl; eauto.
        eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
        econstructor; eauto.
      + destruct occ; occ_simpl.
        * eapply sr with (r2:=(leaf1 :: l1) ++ (list_result (suppl active0 inp))); simpl; eauto using hd_error_app_l.
           econstructor; eauto using list_result_nd.
        * admit.
    (* LK *)
    - constructor; try (destruct lk_result eqn:Hlk; injection H0 as <-); pike_subset; auto.
      (* lk_result succeeded *)
      + intros res STATEND. inv_state_nd.
        apply COMPAT.
        inversion ACTIVE; subst.
        apply add_parent_tree in TR.
        2: { simpl. lia. }
        assert (PARENT: tree_nd (LK lk t1 t2) gm inp seen l1).
        { eapply tr_lookaround; eauto. }
        (* case analysis: did t contribute to the result? *)
        destruct l1 as [|leaf1].
        (* when the tree did not contribute, adding it to seen does not change the results *)
        * econstructor; simpl; eauto.
          eapply list_add_seen_nd with (gm:=gm) in TLR; eauto.
          econstructor; eauto.
        * destruct occ; occ_simpl.
          -- eapply sr with (r2:=(leaf1 :: l1) ++ (list_result (suppl active0 inp))); simpl; eauto using hd_error_app_l.
             econstructor; eauto using list_result_nd.
          -- admit.
      (* lk_result failed *)
      + intros res STATEND. inv_state_nd. apply COMPAT.
        econstructor; simpl; eauto. econstructor; eauto.
        * eapply tr_lookaroundnone; eauto.
        * eapply list_add_seen with (gm:=gm) (inp:=inp) in ACTIVE; eauto; pike_subset.
          unfold lk_result in Hlk. simpl.
          destruct positivity, tree_leaves eqn:Hleaves; try destruct l;
            (rewrite <-first_tree_empty in Hleaves || eapply first_tree_some in Hleaves); rewrite Hleaves in Hlk; easy.
        * eauto.
    (* LKFail *)
    - simpl. constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd. apply COMPAT.
      econstructor; eauto. econstructor; eauto.
      + eapply tr_lookaroundfail.
      + eapply list_add_seen with (gm:=gm) (inp:=inp) in ACTIVE; eauto. pike_subset.
      + eauto.
    (* match *)
    - destruct t; inversion STEP; try now destruct lk_result; subst.
      destruct occ; injection ACC as <- <-.
      + constructor; pike_subset; auto.
        intros res STATEND. inv_state_nd.
        inversion ACTIVE; subst. simpl in *.
        apply (COMPAT (Best (hd_error (list_result (suppl blocked (next_inp inp)) ++ [(inp, gm)])))).
        eapply sr with (r2:=(inp,gm) :: list_result (suppl active0 inp)); simpl; eauto using hd_error_app_l.
        econstructor; eauto using tr_match, list_result_nd.
      + admit.
    (* blocked *)
    - destruct t; inversion STEP; try now destruct lk_result; subst. constructor; pike_subset; auto.
      intros res STATEND. inv_state_nd.
      apply COMPAT.
      rewrite suppl_app, list_result_app in SEQ. simpl in SEQ.
      rewrite app_nil_r, <-app_assoc, app_assoc with (n:=(option_flat_map (fun t : tree => tree_leaves t GroupMap.empty inp forward) future ++ occurrences occ)) in SEQ.
      destruct (tree_leaves newt gm (next_inp inp)) eqn:REST.
      * econstructor; simpl; eauto.
        eapply tlr_cons.
        (* if the blocked tree did not contain a match, we prove that the adding it to the seen set *)
        (* does not change the skipping of the following active trees, using list_add_seen *)
        -- apply tree_leaves_nd. pike_subset.
        -- eapply list_add_seen in ACTIVE; simpl; eauto. pike_subset.
        -- simpl. unfold next_inp in REST. rewrite REST. simpl. auto.
      (* if the blocked tree contained a match, then we don't care about the result of active *)
      (* we can simply use the result obtained without skipping anything *)
      * eapply sr with (r2:=(l :: l0) ++ list_result (suppl active0 inp)); simpl; eauto using hd_error_app_l.
        eapply tlr_cons.
        -- apply tree_leaves_nd. pike_subset.
        -- apply list_result_nd; auto.
        -- simpl. unfold next_inp in REST. rewrite REST. simpl. auto.
  Admitted.

End PikeTree.
