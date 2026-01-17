From Stdlib Require Export Bool Arith List Equivalence Lia.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import Regex Chars Groups Tree Semantics
  FunctionalSemantics FunctionalUtils ComputeIsTree Parameters
  LWParameters LeavesEquivalence FlatMap.

Export ListNotations.

(** * Leaves equivalence of regexes: definition and proof that it allows
rewriting under a context *)

Section Definitions.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).


  (* Equivalence and non-equivalence definitions using is_tree *)
  Section IsTree.
    (** * Observational equivalence *)
    Definition observ_equiv (r1 r2: regex): Prop :=
      forall inp t1 t2
        (TREE1: is_tree rer [Areg r1] inp GroupMap.empty forward t1)
        (TREE2: is_tree rer [Areg r2] inp GroupMap.empty forward t2),
        first_leaf t1 inp = first_leaf t2 inp.


    (** * Equivalence and non-equivalence of trees *)

    (* Equivalence: when the lists of leaves of the trees are equivalent *)
    Definition tree_equiv_tr_dir i gm dir tr1 tr2 :=
      leaves_equiv [] (tree_leaves tr1 gm i dir) (tree_leaves tr2 gm i dir).

    (* Non-equivalence: when the first leaves are different *)
    Definition tree_nequiv_tr_dir i gm dir tr1 tr2 :=
      tree_res tr1 gm i dir <> tree_res tr2 gm i dir.


    (** * Actions equivalence *)

    (* When for all inputs, they have the same leaves in the same order (with possible duplicates) *)
    (* We first state equivalence for one given direction, e.g. rewritings involving sequences may only be valid in one direction *)
    Definition actions_equiv_dir (dir: Direction) (acts1 acts2: actions): Prop :=
      forall inp gm t1 t2
        (TREE1: is_tree rer acts1 inp gm dir t1)
        (TREE2: is_tree rer acts2 inp gm dir t2),
        tree_equiv_tr_dir inp gm dir t1 t2.
    
    Definition actions_equiv_dir_cond (dir: Direction) (P: leaf -> Prop) (acts1 acts2: actions): Prop :=
      forall lf, P lf ->
      forall t1 t2
        (TREE1: is_tree rer acts1 (fst lf) (snd lf) dir t1)
        (TREE2: is_tree rer acts2 (fst lf) (snd lf) dir t2),
        tree_equiv_tr_dir (fst lf) (snd lf) dir t1 t2.
    
    (* Stating for all directions *)
    Definition actions_equiv (acts1 acts2: actions): Prop :=
      forall dir, actions_equiv_dir dir acts1 acts2.


    (** * Regex equivalence *)

    (* Two regexes are equivalent when they define the same groups and
      yield equivalent lists of leaves when matched on the same input. *)
    Definition tree_equiv_dir dir r1 r2 :=
      def_groups r1 = def_groups r2 /\
      actions_equiv_dir dir [Areg r1] [Areg r2].
    
    (* Stating for all directions *)
    Definition tree_equiv r1 r2 :=
      forall dir, tree_equiv_dir dir r1 r2.

    (* Two regexes are non-equivalent when there exist an input and group map
       such that matching the regexes on the input and group map yield
       (observationally) different results. *)
    Definition tree_nequiv_dir dir r1 r2 :=
      exists i gm tr1 tr2,
        is_tree rer [Areg r1] i gm dir tr1 /\
        is_tree rer [Areg r2] i gm dir tr2 /\
        tree_nequiv_tr_dir i gm dir tr1 tr2.

    (* Stating for all directions *)
    Definition tree_nequiv r1 r2 :=
      exists dir, tree_nequiv_dir dir r1 r2.

  End IsTree.


  (** * Equivalence and non-equivalence definitions using compute_tr *)
  Section ComputeTree.
    Definition tree_equiv_compute_dir dir r1 r2 :=
      def_groups r1 = def_groups r2 /\
      forall i gm,
        tree_equiv_tr_dir
          i gm dir
          (compute_tr rer [Areg r1] i gm dir)
          (compute_tr rer [Areg r2] i gm dir).

    Definition tree_equiv_compute r1 r2 :=
      forall dir, tree_equiv_compute_dir dir r1 r2.

    Definition tree_nequiv_compute_dir dir r1 r2 :=
      exists i gm,
        tree_nequiv_tr_dir
          i gm dir
          (compute_tr rer [Areg r1] i gm dir)
          (compute_tr rer [Areg r2] i gm dir).

    Definition tree_nequiv_compute r1 r2 :=
      exists dir, tree_nequiv_compute_dir dir r1 r2.
  End ComputeTree.


  (* Lemmas relating the is_tree and compute_tr versions of the definitions. *)
  Section ComputeTreeIsTree.
    Lemma tree_equiv_compute_dir_iff {dir r1 r2} :
      tree_equiv_dir dir r1 r2 <-> tree_equiv_compute_dir dir r1 r2.
    Proof.
      unfold tree_equiv_dir, tree_equiv_compute_dir, actions_equiv_dir, tree_equiv_tr_dir; split.
      - intros [DEF_GROUPS EQUIV]. eauto 6 using compute_tr_is_tree.
      - intros [DEF_GROUPS Heq]; split; auto. intros * H1 H2.
        pattern t1; eapply compute_tr_ind with (2 := H1); eauto.
        pattern t2; eapply compute_tr_ind with (2 := H2); eauto.
    Qed.

    Lemma tree_equiv_compute_iff {r1 r2} :
      tree_equiv r1 r2 <-> tree_equiv_compute r1 r2.
    Proof.
      unfold tree_equiv, tree_equiv_compute; split; intros;
        apply tree_equiv_compute_dir_iff; eauto.
    Qed.

    Lemma tree_nequiv_compute_dir_iff r1 r2 dir :
      tree_nequiv_dir dir r1 r2 <-> tree_nequiv_compute_dir dir r1 r2.
    Proof.
      unfold tree_nequiv_dir, tree_nequiv_compute_dir, tree_nequiv_tr_dir.
      split.
      - intros (i & gm & tr1 & tr2 & Htr1 & Htr2 & Hneq).
        rewrite (is_tree_eq_compute_tr rer Htr1), (is_tree_eq_compute_tr rer Htr2) in Hneq.
        eauto.
      - intros (i & gm & Hneq).
        eauto 7 using compute_tr_is_tree.
    Qed.

    Lemma tree_nequiv_compute_iff {r1 r2} :
      tree_nequiv r1 r2 <-> tree_nequiv_compute r1 r2.
    Proof.
      unfold tree_nequiv, tree_nequiv_compute.
      pose proof tree_nequiv_compute_dir_iff r1 r2.
      split; intros (dir & Hneq); exists dir; specialize (H dir); intuition.
    Qed.
  End ComputeTreeIsTree.


  (** * Regex contexts *)
  Section Contexts.
    Inductive regex_ctx: Type :=
    | CHole

    | CDisjunctionL (r1 : regex) (c2 : regex_ctx)
    | CDisjunctionR (c1 : regex_ctx) (r2 : regex)

    | CSequenceL (r1 : regex) (c2 : regex_ctx)
    | CSequenceR (c1 : regex_ctx) (r2 : regex)

    | CQuantified (greedy: bool) (min: nat) (delta: non_neg_integer_or_inf) (c1 : regex_ctx)
    | CLookaround (lk : lookaround) (c1 : regex_ctx)
    | CGroup (gid : group_id) (c1 : regex_ctx)
    .


    Fixpoint plug_ctx (c : regex_ctx) (r : regex) : regex :=
      match c with
      | CHole => r
      | CDisjunctionL r1 c2 => Disjunction r1 (plug_ctx c2 r)
      | CDisjunctionR c1 r2 => Disjunction (plug_ctx c1 r) r2
      | CSequenceL r1 c2 => Sequence r1 (plug_ctx c2 r)
      | CSequenceR c1 r2 => Sequence (plug_ctx c1 r) r2
      | CQuantified greedy min delta c1 => Quantified greedy min delta (plug_ctx c1 r)
      | CLookaround lk c1 => Lookaround lk (plug_ctx c1 r)
      | CGroup gid c1 => Group gid (plug_ctx c1 r)
      end.

    (* Direction of contexts *)
    Inductive contextdir: Type := Forward | Backward | Same.

    Fixpoint ctx_dir (ctx: regex_ctx): contextdir :=
      match ctx with
      | CHole => Same
      | CDisjunctionL _ c | CDisjunctionR c _ | CSequenceL _ c | CSequenceR c _ => ctx_dir c
      | CQuantified _ _ _ c | CGroup _ c => ctx_dir c
      | CLookaround lk c =>
        let override_dir := match lk_dir lk with
        | forward => Forward
        | backward => Backward
        end in
        match ctx_dir c with
        | Same => override_dir
        | d => d
        end
      end.
  
  End Contexts.


End Definitions.


(** * Automation *)
#[export]
Hint Unfold
  tree_equiv
  tree_equiv_dir
  tree_equiv_tr_dir
  tree_equiv_compute
  tree_equiv_compute_dir
  actions_equiv
  actions_equiv_dir
  tree_nequiv
  tree_nequiv_dir
  tree_nequiv_tr_dir
  tree_nequiv_compute
  tree_nequiv_compute_dir
  : tree_equiv.

Hint Rewrite app_nil_l app_nil_r : tree_equiv.
Hint Rewrite <- app_assoc : tree_equiv.

Hint Unfold seq_list : tree_equiv_simpl.

Ltac tree_equiv_simpl :=
  repeat progress (
      autounfold with tree_equiv tree_equiv_simpl;
      autorewrite with tree_equiv;
      simpl; intros
    ).

Ltac tree_equiv_prepare :=
  tree_equiv_simpl;
  try (apply conj; [ try congruence | ]).

Ltac tree_equiv_rw :=
  try setoid_rewrite tree_equiv_compute_dir_iff;
  try setoid_rewrite tree_equiv_compute_iff;
  try setoid_rewrite tree_nequiv_compute_dir_iff;
  try setoid_rewrite tree_nequiv_compute_iff;
  tree_equiv_prepare; [ .. | intros ].

Ltac tree_inv H :=
  erewrite is_tree_determ with (1 := H);
  [ | repeat (econstructor; tree_equiv_simpl) ].

Ltac tree_equiv_inv :=
  tree_equiv_prepare;
  [ .. | intros * Hl Hr; tree_inv Hl; [ tree_inv Hr | .. ] ].

Hint Unfold
     compute_tr
     anchor_satisfied is_boundary is_input_boundary
     read_char word_char
     andb orb negb xorb
  : tree_equiv_symbex.

Hint Rewrite
  PeanoNat.Nat.leb_le
  PeanoNat.Nat.leb_nle
  : tree_equiv_symbex.

Ltac tree_equiv_symbex_step :=
  match goal with
  | _ => progress autorewrite with tree_equiv_symbex in *
  | _ => progress autounfold with tree_equiv_symbex
  | _ => progress simpl
  | [  |- context[match ?x with _ => _ end] ] =>
      lazymatch x with
      | context[match _ with _ => _ end] => fail
      | _ => destruct x eqn:?
      end
  end.

Ltac tree_equiv_symbex :=
  repeat tree_equiv_symbex_step.


Ltac leaves_equiv_step :=
  first [ apply equiv_nil
        | apply equiv_cons'
        | (apply equiv_seen_left + apply equiv_seen_right);
          [ apply is_seen_spec; unfold In; tauto | ] ].

Ltac leaves_equiv_t :=
  first [ reflexivity | repeat leaves_equiv_step ].

Hint Rewrite
  @CharSet.exist_canonicalized_equiv
  @CharSet.exist_spec
  @CharSet.exist_false_iff
  @CharSet.contains_spec
  @CharSet.contains_false_iff
  @CharSet.range_spec
  EqDec.inversion_false
  EqDec.inversion_true
  Bool.andb_true_iff
  Bool.andb_false_iff
  Bool.orb_true_iff
  Bool.orb_false_iff
  Bool.negb_true_iff
  Bool.negb_false_iff
  : charset.

Hint Unfold CharSet.Exists
  : charset.

Hint Extern 1 => lia : lia.



(** * The tree, actions and regex equivalence relations are indeed equivalence relations. *)
Section Relation.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).


  Ltac eqv := repeat red; tree_equiv_rw; solve [congruence | intuition | firstorder].


  (* Tree equivalence *)
  Section TreeEquivTr.
    Context (i: input) (gm: group_map) (dir: Direction).

    Lemma tree_equiv_tr_dir_refl:
      Relation_Definitions.reflexive tree (tree_equiv_tr_dir i gm dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_tr_dir. reflexivity.
    Qed.

    Lemma tree_equiv_tr_dir_sym:
      Relation_Definitions.symmetric tree (tree_equiv_tr_dir i gm dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_tr_dir. intros x y H. symmetry. auto.
    Qed.

    Lemma tree_equiv_tr_dir_trans:
      Relation_Definitions.transitive tree (tree_equiv_tr_dir i gm dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_tr_dir. intros x y z Hxy Hyz.
      etransitivity; eauto.
    Qed.

    #[global] Add Relation tree (tree_equiv_tr_dir i gm dir)
          reflexivity proved by tree_equiv_tr_dir_refl
          symmetry proved by tree_equiv_tr_dir_sym
          transitivity proved by tree_equiv_tr_dir_trans
          as tree_equiv_tr_dir_rel.
  End TreeEquivTr.


  (* Actions equivalence *)
  Section Actions.
    Section DirSpecific.
      Context (dir: Direction).

      Lemma actions_equiv_dir_refl:
        Relation_Definitions.reflexive actions (actions_equiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.reflexive, actions_equiv_dir. intros. specialize (is_tree_determ rer _ _ _ _ _ _ TREE1 TREE2).
        intros <-. reflexivity.
      Qed.

      Lemma actions_equiv_dir_sym:
        Relation_Definitions.symmetric actions (actions_equiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.symmetric, actions_equiv_dir. intros a1 a2 H inp gm t1 t2 TREE1 TREE2.
        symmetry; auto.
      Qed.

      Lemma actions_equiv_dir_trans:
        Relation_Definitions.transitive actions (actions_equiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.transitive, actions_equiv_dir. intros a1 a2 a3 H H0 inp gm t1 t3 TREE1 TREE3.
        assert (exists t2, is_tree rer a2 inp gm dir t2).
        { exists (compute_tr rer a2 inp gm dir). apply compute_tr_is_tree. }
        (* otherwise any regex is equivalent to a regex without tree *)
        destruct H1 as [t2 TREE2].
        etransitivity; eauto.
      Qed.

      #[global] Add Relation actions (actions_equiv_dir rer dir)
          reflexivity proved by actions_equiv_dir_refl
          symmetry proved by actions_equiv_dir_sym
          transitivity proved by actions_equiv_dir_trans
          as actions_equiv_dir_rel.
    End DirSpecific.


    Lemma actions_equiv_refl:
      Relation_Definitions.reflexive actions (actions_equiv rer).
    Proof.
      unfold Relation_Definitions.reflexive, actions_equiv. intros acts dir. reflexivity.
    Qed.

    Lemma actions_equiv_sym:
      Relation_Definitions.symmetric actions (actions_equiv rer).
    Proof.
      unfold Relation_Definitions.symmetric, actions_equiv. intros a1 a2 H dir. symmetry. auto.
    Qed.

    Lemma actions_equiv_trans:
      Relation_Definitions.transitive actions (actions_equiv rer).
    Proof.
      unfold Relation_Definitions.transitive, actions_equiv. intros a1 a2 a3 H12 H23 dir. transitivity a2; auto.
    Qed.

    #[global] Add Relation actions (actions_equiv rer)
        reflexivity proved by actions_equiv_refl
        symmetry proved by actions_equiv_sym
        transitivity proved by actions_equiv_trans
        as actions_equiv_rel.
  
  End Actions.


  (* Regex equivalence *)

  Section DirSpecific.
    Context (dir: Direction).
      
    (* tree_equiv_dir *)
    Lemma tree_equiv_dir_reflexive:
      Relation_Definitions.reflexive regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_dir.
      intros x; split; auto. reflexivity.
    Qed.

    Lemma tree_equiv_dir_symmetric:
      Relation_Definitions.symmetric regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_dir.
      intros x y [DEF_GROUPS Hequiv]; split; try solve[congruence].
      symmetry. auto.
    Qed.

    Lemma tree_equiv_dir_transitive:
      Relation_Definitions.transitive regex (tree_equiv_dir rer dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_dir.
      intros x y z [DEF_GROUPS12 H12] [DEF_GROUPS23 H23]; split; try solve[congruence].
      transitivity [Areg y]; auto.
    Qed.

    #[global] Add Relation regex (tree_equiv_dir rer dir)
        reflexivity proved by tree_equiv_dir_reflexive
        symmetry proved by tree_equiv_dir_symmetric
        transitivity proved by tree_equiv_dir_transitive
        as tree_equiv_dir_rel.


    (* tree_equiv_compute_dir *)
    Lemma tree_equiv_compute_dir_reflexive:
      Relation_Definitions.reflexive regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.reflexive, tree_equiv_compute_dir.
      intros x; split; auto. reflexivity.
    Qed.

    Lemma tree_equiv_compute_dir_symmetric:
      Relation_Definitions.symmetric regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.symmetric, tree_equiv_compute_dir, tree_equiv_tr_dir.
      intros x y [DEF_GROUPS Hequiv]; split; try solve[congruence].
      symmetry. auto.
    Qed.

    Lemma tree_equiv_compute_dir_transitive:
      Relation_Definitions.transitive regex (tree_equiv_compute_dir rer dir).
    Proof.
      unfold Relation_Definitions.transitive, tree_equiv_compute_dir, tree_equiv_tr_dir.
      intros x y z [DEF_GROUPSxy Hxy] [DEF_GROUPSyz Hyz]; split; try solve[congruence].
      intros i gm.
      etransitivity; eauto.
    Qed.

    #[global] Add Relation regex (tree_equiv_compute_dir rer dir)
        reflexivity proved by tree_equiv_compute_dir_reflexive
        symmetry proved by tree_equiv_compute_dir_symmetric
        transitivity proved by tree_equiv_compute_dir_transitive
        as tree_equiv_compute_dir_rel.
  End DirSpecific.


  (* tree_equiv *)
  Lemma tree_equiv_reflexive:
    Relation_Definitions.reflexive regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.reflexive, tree_equiv.
    intros x dir. reflexivity.
  Qed.

  Lemma tree_equiv_symmetric:
    Relation_Definitions.symmetric regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.symmetric, tree_equiv.
    intros x y H dir. symmetry. auto.
  Qed.

  Lemma tree_equiv_transitive:
    Relation_Definitions.transitive regex (tree_equiv rer).
  Proof.
    unfold Relation_Definitions.transitive, tree_equiv.
    intros x y z Hxy Hyz dir. transitivity y; auto.
  Qed.

  #[global] Add Relation regex (tree_equiv rer)
      reflexivity proved by tree_equiv_reflexive
      symmetry proved by tree_equiv_symmetric
      transitivity proved by tree_equiv_transitive
      as tree_equiv_rel.
      

  (* tree_equiv_compute *)
  Lemma tree_equiv_compute_reflexive:
    Relation_Definitions.reflexive regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.reflexive, tree_equiv_compute. reflexivity.
  Qed.

  Lemma tree_equiv_compute_symmetric:
    Relation_Definitions.symmetric regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.symmetric, tree_equiv_compute.
    intros x y Hxy dir. symmetry. auto.
  Qed.

  Lemma tree_equiv_compute_transitive:
    Relation_Definitions.transitive regex (tree_equiv_compute rer).
  Proof.
    unfold Relation_Definitions.transitive, tree_equiv_compute.
    intros x y z Hxy Hyz dir.
    transitivity y; auto.
  Qed.

  #[global] Add Relation regex (tree_equiv_compute rer)
      reflexivity proved by tree_equiv_compute_reflexive
      symmetry proved by tree_equiv_compute_symmetric
      transitivity proved by tree_equiv_compute_transitive
      as tree_equiv_compute_rel.

  (* Non-equivalence is irreflexive and symmetric *)
  Section Nequiv.
    Section DirSpecific.
      Context (dir: Direction).

      #[global] Instance tree_nequiv_dir_irrefl: Irreflexive (tree_nequiv_dir rer dir).
      Proof.
        unfold Irreflexive, Reflexive, complement, tree_nequiv_dir.
        tree_equiv_rw. destruct H as [i [gm H]]. apply H. auto.
      Qed.

      Lemma tree_nequiv_dir_sym:
        Relation_Definitions.symmetric regex (tree_nequiv_dir rer dir).
      Proof.
        unfold Relation_Definitions.symmetric, tree_nequiv_dir.
        tree_equiv_rw. destruct H as [i [gm H]]. exists i. exists gm.
        symmetry. auto.
      Qed.
      
      #[global] Add Relation regex (tree_nequiv_dir rer dir)
          symmetry proved by tree_nequiv_dir_sym
          as tree_nequiv_dir_rel.


      #[global] Instance tree_nequiv_compute_dir_irrefl : Irreflexive (tree_nequiv_compute_dir rer dir).
      Proof.
        unfold Irreflexive, Reflexive, complement, tree_nequiv_compute_dir.
        tree_equiv_rw. destruct H as [i [gm H]]. apply H. auto.
      Qed.

      Lemma tree_nequiv_compute_dir_sym:
        Relation_Definitions.symmetric regex (tree_nequiv_compute_dir rer dir).
      Proof.
        unfold Relation_Definitions.symmetric, tree_nequiv_compute_dir.
        tree_equiv_rw. destruct H as [i [gm H]].
        exists i. exists gm. symmetry. auto.
      Qed.

      #[global] Add Relation regex (tree_nequiv_compute_dir rer dir)
          symmetry proved by tree_nequiv_compute_dir_sym
          as tree_nequiv_compute_dir_rel.
    End DirSpecific.

    #[global] Instance tree_nequiv_irrefl: Irreflexive (tree_nequiv rer).
    Proof.
      unfold Irreflexive, Reflexive, complement, tree_nequiv.
      intros x [dir0 H].
      pose proof tree_nequiv_dir_irrefl. unfold Irreflexive, Reflexive, complement in H0.
      eauto.
    Qed.
    
    Lemma tree_nequiv_sym:
      Relation_Definitions.symmetric regex (tree_nequiv rer).
    Proof.
      unfold Relation_Definitions.symmetric, tree_nequiv. intros x y [dir H].
      exists dir. symmetry. auto.
    Qed.
      
    #[global] Add Relation regex (tree_nequiv rer)
        symmetry proved by tree_nequiv_sym
        as tree_nequiv_rel.

    #[global] Instance tree_nequiv_compute_irrefl: Irreflexive (tree_nequiv_compute rer).
    Proof.
      unfold Irreflexive, Reflexive, complement, tree_nequiv_compute.
      intros x [dir H].
      pose proof tree_nequiv_compute_dir_irrefl. unfold Irreflexive, Reflexive, complement in H0.
      eauto.
    Qed.

    Lemma tree_nequiv_compute_sym:
      Relation_Definitions.symmetric regex (tree_nequiv_compute rer).
    Proof.
      unfold Relation_Definitions.symmetric, tree_nequiv_compute.
      intros x y [dir H]. exists dir. symmetry. auto.
    Qed.

    #[global] Add Relation regex (tree_nequiv_compute rer)
        symmetry proved by tree_nequiv_compute_sym
         as tree_nequiv_compute_rel.
  End Nequiv.
End Relation.


(* Notations *)
Notation "r1 ≅[ rer ][ dir ] r2" := (tree_equiv_dir rer dir r1 r2) (at level 70, format "r1  ≅[ rer ][ dir ]  r2").
Notation "r1 ≅[ rer ] r2" := (tree_equiv rer r1 r2) (at level 70, format "r1  ≅[ rer ]  r2").
Notation "r1 ≇[ rer ][ dir ] r2" := (tree_nequiv_dir rer dir r1 r2) (at level 70, format "r1  ≇[ rer ][ dir ]  r2").
Notation "r1 ≇[ rer ] r2" := (tree_nequiv rer r1 r2) (at level 70, format "r1  ≇[ rer ]  r2").


Section Congruence.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (** * Observational Consequence on Backtracking Results  *)

  Lemma observe_equivalence_gen:
    forall r1 r2 dir,
      r1 ≅[rer][dir] r2 ->
      forall inp gm t1 t2,
        is_tree rer [Areg r1] inp gm dir t1 ->
        is_tree rer [Areg r2] inp gm dir t2 ->
        tree_res t1 gm inp dir = tree_res t2 gm inp dir.
  Proof.
    intros r1 r2 dir EQUIV inp gm t1 t2 TREE1 TREE2.
    unfold tree_equiv_dir, actions_equiv_dir in EQUIV. apply proj2 in EQUIV.
    specialize (EQUIV inp gm t1 t2 TREE1 TREE2).
    unfold tree_equiv_tr_dir in EQUIV.
    apply equiv_head in EQUIV. do 2 rewrite first_tree_leaf. auto.
  Qed.

  Theorem observe_equivalence:
    forall r1 r2
      (EQUIV: r1 ≅[rer][forward] r2),
      observ_equiv rer r1 r2.
  Proof.
    intros r1 r2 EQUIV inp t1 t2 TREE1 TREE2.
    unfold first_leaf. eauto using observe_equivalence_gen.
  Qed.


  (* Getting the leaves of a continuation applied to a particular leaf *)
  (* This predicate will be used to express that appending a list of actions a2 to a list
  of actions a1 corresponds to extending the leaves of the tree corresponding to actions
  a1 with trees corresponding to the actions of a2 (see lemma leaves_concat below) *)
  Inductive act_from_leaf : actions -> Direction -> leaf -> list leaf -> Prop :=
  | afl:
    forall act dir l t
      (TREE: is_tree rer act (fst l) (snd l) dir t),
      act_from_leaf act dir l (tree_leaves t (snd l) (fst l) dir).


  (* Adding new things to the continuation is the same as extending each leaf of the tree with these new things *)
  Theorem leaves_concat:
    forall inp gm dir act1 act2 tapp t1
      (TREE_APP: is_tree rer (act1 ++ act2) inp gm dir tapp)
      (TREE_1: is_tree rer act1 inp gm dir t1),
      FlatMap (tree_leaves t1 gm inp dir) (act_from_leaf act2 dir) (tree_leaves tapp gm inp dir).
  Proof.
    intros. generalize dependent tapp.
    induction TREE_1; intros; simpl in *.
    - (* Done *)
      rewrite <- app_nil_r. constructor; constructor. auto.
    
    - (* Check pass *)
      inversion TREE_APP; subst. 2: contradiction.
      simpl. apply IHTREE_1. auto.
    
    - (* Check fail *)
      inversion TREE_APP; subst. 1: contradiction.
      simpl. constructor.
    
    - (* Close *)
      inversion TREE_APP; subst. simpl.
      apply IHTREE_1. auto.
    
    - (* Epsilon *)
      inversion TREE_APP; subst. auto.

    - (* Read char success *)
      inversion TREE_APP; subst. 2: congruence.
      simpl.
      rewrite READ in READ0. injection READ0 as <- <-.
      rewrite advance_input_success with (nexti := nextinp).
      2: eauto using read_char_success_advance.
      auto.
    
    - (* Read char fail *)
      inversion TREE_APP; subst. 1: congruence.
      simpl. constructor.
    
    - (* Disjunction *)
      inversion TREE_APP; subst.
      simpl. apply FlatMap_app; auto.
    
    - (* Sequence *)
      inversion TREE_APP; subst.
      rewrite app_assoc in CONT. auto.
    
    - (* Forced quantifier *)
      inversion TREE_APP; subst. simpl.
      auto.
    
    - (* Done quantifier *)
      inversion TREE_APP; subst.
      2: { destruct plus; discriminate. }
      auto.
    
    - (* Free quantifier *)
      inversion TREE_APP; subst.
      1: { destruct plus; discriminate. }
      assert (plus0 = plus). {
        destruct plus0; destruct plus; try discriminate; try reflexivity.
        injection H1 as <-. auto.
      }
      subst plus0.
      unfold greedy_choice. destruct greedy.
      + (* Greedy *)
        simpl. apply FlatMap_app; auto.
      + (* Lazy *)
        simpl. apply FlatMap_app; auto.
      
    - (* Group *)
      inversion TREE_APP; subst. simpl.
      auto.
    
    - (* Lookaround success *)
      inversion TREE_APP; subst;
        assert (treelk0 = treelk) by (eapply is_tree_determ; eauto); subst.
      2: { rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
      rewrite RES_LK in RES_LK0. injection RES_LK0 as <-.
      destruct positivity eqn:Hpos.
      + unfold lk_result in RES_LK. rewrite Hpos in RES_LK.
        pose proof first_tree_leaf treelk gm inp (lk_dir lk) as LK_FIRST.
        destruct (tree_res treelk gm inp (lk_dir lk)) as [[inplk gmlk']|] eqn:TREERES_LK; try discriminate.
        injection RES_LK as ->.
        destruct (tree_leaves treelk gm inp (lk_dir lk)) as [|[inplk' gmlk'] q] eqn:TREELEAVES_LK; try discriminate.
        simpl in *. injection LK_FIRST as <- <-. rewrite Hpos.
        rewrite TREELEAVES_LK. auto.
      + unfold lk_result in RES_LK. rewrite Hpos in RES_LK.
        destruct (tree_res treelk gm inp (lk_dir lk)) eqn:TREERES; inversion RES_LK. subst.
        assert (tree_leaves treelk gmlk inp (lk_dir lk) = []).
        { apply leaves_group_map_indep with (gm1 := gmlk) (inp1 := inp) (dir1 := lk_dir lk).
          apply hd_error_none_nil. rewrite <- first_tree_leaf. auto. }
        simpl. rewrite Hpos, H. auto.
  
    - (* Lookaround failure *)
      inversion TREE_APP; subst;
        assert (treelk0 = treelk) by (eapply is_tree_determ; eauto); subst.
      { rewrite RES_LK in FAIL_LK. inversion FAIL_LK. }
      simpl. constructor.
    
    - (* Anchor *)
      inversion TREE_APP; subst.
      2: congruence.
      simpl. auto.
    
    - (* Anchor fail *)
      inversion TREE_APP; subst.
      1: congruence.
      simpl. constructor.
    
    - (* Backref *)
      inversion TREE_APP; subst.
      2: congruence.
      rewrite READ_BACKREF in READ_BACKREF0. injection READ_BACKREF0 as <- <-.
      simpl.
      replace (advance_input_n _ _ _) with nextinp.
      2: eauto using read_backref_success_advance.
      auto.
    
    - (* Backref fail *)
      inversion TREE_APP; subst.
      1: congruence.
      simpl. constructor.
  Qed.


  (** * Continuation Lemmas  *)

  (* building up to contextual equivalence *)
  (* to reason about the leaves of an app, we use the flatmap result *)


  (* The function act_from_leaf is deterministic *)
  Lemma act_from_leaf_determ: forall act dir, determ (act_from_leaf act dir).
  Proof.
    intros act dir x y1 y2 Hxy1 Hxy2.
    inversion Hxy1; subst. inversion Hxy2; subst.
    assert (t0 = t) by eauto using is_tree_determ. subst t0. reflexivity.
  Qed.


  (* Appending a list of actions acts to the right of two equivalent lists of actions
  a1 and a2 yields equivalent lists of actions. *)
  (* This is needed in the contextual equivalence proof for the sequence case and the free quantifier case, as well as for app_eq_both (see below) *)
  Lemma app_eq_right:
    forall a1 a2 acts dir
      (ACTS_EQ: actions_equiv_dir rer dir a1 a2),
      actions_equiv_dir rer dir (a1 ++ acts) (a2 ++ acts).
  Proof.
    intros. unfold actions_equiv_dir in *.
    intros inp gm t1acts t2acts TREE1acts TREE2acts.
    assert (exists t1, is_tree rer a1 inp gm dir t1). {
      exists (compute_tr rer a1 inp gm dir). apply compute_tr_is_tree.
    }
    assert (exists t2, is_tree rer a2 inp gm dir t2). {
      exists (compute_tr rer a2 inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [t1 TREE1]. destruct H0 as [t2 TREE2].
    pose proof leaves_concat inp gm dir a1 acts t1acts t1 TREE1acts TREE1.
    pose proof leaves_concat inp gm dir a2 acts t2acts t2 TREE2acts TREE2.
    specialize (ACTS_EQ inp gm t1 t2 TREE1 TREE2).
    unfold tree_equiv_tr_dir.
    eauto using flatmap_leaves_equiv_l, act_from_leaf_determ.
  Qed.

  
  (* Same as app_eq_right, but prepending this time the actions to the left *)
  (* Used in the sequence case *)
  Lemma app_eq_left:
    forall a1 a2 acts dir
      (ACTS_EQ: actions_equiv_dir rer dir a1 a2),
      actions_equiv_dir rer dir (acts ++ a1) (acts ++ a2).
  Proof.
    intros. unfold actions_equiv_dir in *.
    intros inp gm t1acts t2acts TREE1acts TREE2acts.
    assert (exists tacts, is_tree rer acts inp gm dir tacts). {
      exists (compute_tr rer acts inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [tacts TREEacts].
    pose proof leaves_concat inp gm dir acts a1 t1acts tacts TREE1acts TREEacts.
    pose proof leaves_concat inp gm dir acts a2 t2acts tacts TREE2acts TREEacts.
    eapply flatmap_leaves_equiv_r; eauto.
    (* Now act_from_leaf a1 dir and act_from_leaf a2 dir are morally equivalent *)
    unfold equiv_leaffuncts. intros lf yf yg Hyf Hyg.
    inversion Hyf; subst. inversion Hyg; subst. apply ACTS_EQ; auto.
  Qed.
  
  (* If a1 ≅ a2 and b1 ≅ b2, then a1 ++ b1 ≅ a2 ++ b2. *)
  (* Used in quantifier case of contextual equivalence proof *)
  Lemma app_eq_both:
    forall a1 a2 b1 b2 dir
      (A_EQ: actions_equiv_dir rer dir a1 a2)
      (B_EQ: actions_equiv_dir rer dir b1 b2),
      actions_equiv_dir rer dir (a1 ++ b1) (a2 ++ b2).
  Proof.
    intros. transitivity (a1++b2).
    - apply app_eq_left. auto.
    - apply app_eq_right. auto.
  Qed.


  (** ** Preparing the proof by induction for quantifiers *)
  (* For quantifiers, we perform a proof by induction on the remaining length of the input to be matched. *)
  (* Therefore, at any given point, we know the equivalence of r1{0, Δ, p} with r2{0, Δ, p} only for inputs whose remaining length is less than some integer n. *)
  (* For an input inp whose remaining length is n, after unfolding the quantifier once, we need to prove that the lists of actions [r1; Acheck inp; r1{0, Δ, p}] and [r2; Acheck inp; r2{0, Δ, p}] are equivalent. *)
  (* We then argue that the lists of actions [r1; Acheck inp] and [r2; Acheck inp] are not only equivalent but also respect the condition that any leaf has strictly progressed wrt inp, and hence have a remaining length of less than n. *)
  (* We can then apply the induction hypothesis stated at the beginning of this paragraph. *)

  (* A list of actions acts is said to respect a property P in direction dir when: *)
  Definition actions_respect_prop_dir (acts: actions) (dir: Direction) (P: leaf -> Prop): Prop :=
    forall inp gm t
      (* whenever t is a tree corresponding to actions acts and direction dir, *)
      (TREE: is_tree rer acts inp gm dir t),
      (* all the leaves of t respect P. *)
      Forall P (tree_leaves t gm inp dir).
  (* Used for check actions in the context of the induction proof for free quantifiers  *)

  (* Appending lists of actions that are conditionally equivalent, provided that the prepended actions respect the condition *)
  Lemma actions_equiv_interm_prop:
    forall (a1 a2 b1 b2: actions) (P: leaf -> Prop) (dir: Direction),
      actions_equiv_dir rer dir a1 a2 ->
      actions_respect_prop_dir a1 dir P ->
      actions_respect_prop_dir a2 dir P ->
      actions_equiv_dir_cond rer dir P b1 b2 ->
      actions_equiv_dir rer dir (a1 ++ b1) (a2 ++ b2).
  Proof.
    intros a1 a2 b1 b2 P dir EQUIV_a PROP1 PROP2 EQUIV_b.
    transitivity (a1 ++ b2).
    - unfold actions_equiv_dir. intros inp gm t1 t2 TREE1 TREE2.
      assert (exists ta1, is_tree rer a1 inp gm dir ta1). { exists (compute_tr rer a1 inp gm dir). apply compute_tr_is_tree. }
      destruct H as [ta1 TREEa1].
      pose proof leaves_concat _ _ _ _ _ _ _ TREE1 TREEa1 as CONCAT1.
      pose proof leaves_concat _ _ _ _ _ _ _ TREE2 TREEa1 as CONCAT2.
      unshelve eapply (flatmap_leaves_equiv_r_prop _ _ _ _ _ P _ _ CONCAT1 CONCAT2); auto.
      unfold equiv_leaffuncts_cond. intros. inversion H0; subst. inversion H1; subst.
      apply EQUIV_b; auto.
    - apply app_eq_right. auto.
  Qed.

  (* If a list of actions respects a property, then prepending actions to the list does not change that. *)
  Lemma actions_respect_prop_add_left:
    forall (a b: actions) (P: leaf -> Prop) (dir: Direction),
      actions_respect_prop_dir b dir P ->
      actions_respect_prop_dir (a ++ b) dir P.
  Proof.
    intros a b P dir PROPb.
    unfold actions_respect_prop_dir. intros inp gm t TREE.
    assert (exists ta, is_tree rer a inp gm dir ta). {
      exists (compute_tr rer a inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [ta TREEa].
    pose proof leaves_concat _ _ _ _ _ _ _ TREE TREEa as CONCAT.
    unfold actions_respect_prop_dir in PROPb.
    remember (act_from_leaf b dir) as f.
    induction CONCAT. 1: constructor.
    apply Forall_app. split; auto. subst f.
    inversion HEAD; subst. apply PROPb. auto.
  Qed.

  (* Definition of when a list of actions never yields any leaf *)
  (* Used for checks that are at the end of the input *)
  Definition actions_no_leaves (a: actions) (dir: Direction): Prop :=
    forall inp gm t,
      is_tree rer a inp gm dir t ->
      tree_leaves t gm inp dir = [].

  (* Relating the above definition to actions that respect a condition that is always false *)
  Lemma actions_prop_False_no_leaves:
    forall (a: actions) (dir: Direction) (P: leaf -> Prop),
      actions_respect_prop_dir a dir P ->
      (forall lf, ~P lf) ->
      actions_no_leaves a dir.
  Proof.
    intros a dir P RESPECT PROP_FALSE.
    unfold actions_no_leaves. intros inp gm t TREE.
    unfold actions_respect_prop_dir in RESPECT. apply RESPECT in TREE.
    destruct tree_leaves; try reflexivity.
    inversion TREE; subst. exfalso. apply (PROP_FALSE l H1).
  Qed.

  Lemma actions_no_leaves_prop_False:
    forall (a: actions) (dir: Direction),
      actions_no_leaves a dir ->
      actions_respect_prop_dir a dir (fun _ => False).
  Proof.
    intros a dir NO_LEAVES.
    unfold actions_respect_prop_dir. unfold actions_no_leaves in NO_LEAVES.
    intros. rewrite NO_LEAVES; auto.
  Qed.

  (* If a list of actions b never yields any leaves, then prepending actions to the left of b does not change that. *)
  Lemma actions_no_leaves_add_left:
    forall a b dir,
      actions_no_leaves b dir ->
      actions_no_leaves (a ++ b) dir.
  Proof.
    intros a b dir NO_LEAVES.
    apply actions_no_leaves_prop_False in NO_LEAVES.
    apply actions_respect_prop_add_left with (a := a) in NO_LEAVES.
    apply actions_prop_False_no_leaves with (P := fun _ => False); auto.
  Qed.

  (* If a list of actions a never yields any leaves, then appending actions to the right of b does not change that either. *)
  Lemma actions_no_leaves_add_right:
    forall a b dir,
      actions_no_leaves a dir ->
      actions_no_leaves (a ++ b) dir.
  Proof.
    intros a b dir NO_LEAVES.
    unfold actions_no_leaves in *. intros inp gm t TREEab.
    assert (exists ta, is_tree rer a inp gm dir ta). {
      exists (compute_tr rer a inp gm dir). apply compute_tr_is_tree.
    }
    destruct H as [ta TREEa].
    pose proof leaves_concat _ _ _ _ _ _ _ TREEab TREEa as FLAT_MAP.
    rewrite NO_LEAVES in FLAT_MAP by assumption. inversion FLAT_MAP. reflexivity.
  Qed.


  (* A check action respects the property that all leaves have strictly advanced with respect to the check. *)
  Lemma check_actions_prop:
    forall inp dir,
      actions_respect_prop_dir [Acheck inp] dir
        (fun lf : input * group_map => StrictSuffix.strict_suffix (fst lf) inp dir).
  Proof.
    intros inp dir. unfold actions_respect_prop_dir.
    intros inp' gm t TREE. inversion TREE; subst; simpl.
    - inversion TREECONT; subst. simpl. constructor; auto.
    - constructor.
  Qed.


  (** *** The quantifier lemmas *)
  (* Forced case: If we know that r1 ≅ r2 and that r1{0, Δ, p} ≅ r2{0, Δ, p}, then we
  prove by induction on min that for all min ≥ 0, r1{min, Δ, p} ≅ r2{min, Δ, p}. *)
  Lemma regex_equiv_quant_forced:
    forall r1 r2 dir,
      tree_equiv_dir rer dir r1 r2 ->
      forall greedy delta,
        tree_equiv_dir rer dir (Quantified greedy 0 delta r1) (Quantified greedy 0 delta r2) ->
        forall min,
          tree_equiv_dir rer dir (Quantified greedy min delta r1) (Quantified greedy min delta r2).
  Proof.
    intros r1 r2 dir EQUIV greedy delta EQUIV_ZERO.
    destruct EQUIV_ZERO as [DEF_GROUPS EQUIV_ZERO]. simpl in DEF_GROUPS.
    induction min as [|min' IH]. 1: split; assumption.
    unfold tree_equiv_dir. split; try assumption. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    rewrite <- DEF_GROUPS in *.
    unfold tree_equiv_tr_dir. simpl.
    apply app_eq_both with (a1 := [Areg r1]) (a2 := [Areg r2]) (b1 := [Areg (Quantified greedy min' delta r1)]) (b2 := [Areg (Quantified greedy min' delta r2)]).
    - unfold actions_equiv_dir. unfold tree_equiv_dir in EQUIV.
      apply EQUIV.
    - unfold actions_equiv_dir. unfold tree_equiv_dir in IH.
      apply IH.
    - simpl. apply ISTREE1.
    - simpl. apply ISTREE0.
  Qed.

  (* Done case *)
  Lemma regex_equiv_quant_done:
    forall r1 r2 dir greedy,
      def_groups r1 = def_groups r2 ->
      tree_equiv_dir rer dir (Quantified greedy 0 (NoI.N 0) r1) (Quantified greedy 0 (NoI.N 0) r2).
  Proof.
    intros. unfold tree_equiv_dir.
    split; auto. intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    - inversion SKIP; subst; inversion SKIP0; subst. unfold tree_equiv_tr_dir. reflexivity.
    - destruct plus; discriminate.
    - destruct plus; discriminate.
    - destruct plus; discriminate.
  Qed.

  (* If inp' is a strict suffix of inp, then the remaining length of inp' is less
  than that of inp. *)
  (* Used in the induction proof for the free quantifier case *)
  Lemma strict_suffix_remaining_length:
    forall inp' inp dir,
      StrictSuffix.strict_suffix inp' inp dir ->
      remaining_length inp' dir < remaining_length inp dir.
  Proof.
    intros [next1 pref1] [next2 pref2] [] STRICT_SUFFIX.
    - (* Forward *)
      apply StrictSuffix.ss_fwd_diff in STRICT_SUFFIX.
      destruct STRICT_SUFFIX as [diff [DIFF_NOTNIL [Heqnext2 Heqpref1]]]. simpl.
      rewrite Heqnext2, app_length.
      destruct diff; try contradiction. simpl. lia.
    - (* Backward *)
      apply StrictSuffix.ss_bwd_diff in STRICT_SUFFIX.
      destruct STRICT_SUFFIX as [diff [DIFF_NOTNIL [Heqnext1 Heqpref2]]]. simpl.
      rewrite Heqpref2, app_length, rev_length.
      destruct diff; try contradiction. simpl. lia.
  Qed.

  (* A check action that is at the end of the input never yields any leaves. *)
  Lemma check_end_no_leaves:
    forall inp dir,
      remaining_length inp dir = 0 ->
      actions_no_leaves [Acheck inp] dir.
  Proof.
    intros inp dir END.
    apply actions_prop_False_no_leaves with (P := fun lf => StrictSuffix.strict_suffix (fst lf) inp dir).
    - apply check_actions_prop.
    - intros lf ABS. apply strict_suffix_remaining_length in ABS. lia.
  Qed.

  (* Free quantifier case *)
  (* If r1 ≅ r2, then r1{0, Δ, p} ≅ r2{0, Δ, p} for all Δ and p. *)
  (* TODO? Try to make the proof simpler *)
  Lemma regex_equiv_quant_free:
    forall r1 r2 dir,
      tree_equiv_dir rer dir r1 r2 ->
      forall greedy delta,
        tree_equiv_dir rer dir (Quantified greedy 0 delta r1) (Quantified greedy 0 delta r2).
  Proof.
    intros r1 r2 dir Hequiv greedy delta.
    destruct Hequiv as [DEF_GROUPS Hequiv].
    (* Proceed by induction on the remaining length of the input *)
    split; auto. intros inp gm t1 t2 TREE1. remember (remaining_length inp dir) as n.
    assert (remaining_length inp dir <= n) as Hle_n by lia. clear Heqn.
    revert inp gm Hle_n delta t1 t2 TREE1. induction n.
    - (* At end of input *)
      intros inp gm Hend delta t1 t2 TREE1 TREE2.
      inversion TREE1; subst; inversion TREE2; subst.
      + (* Done *) inversion SKIP; subst. inversion SKIP0; subst. unfold tree_equiv_tr_dir. reflexivity.
      + destruct plus; discriminate.
      + destruct plus; discriminate.
      + (* Free *) assert (plus = plus0). { destruct plus0; destruct plus; congruence. }
        subst plus0. clear H1.
        inversion SKIP; subst inp0 gm0 dir0 tskip. inversion SKIP0; subst inp0 gm0 dir0 tskip0.
        unfold tree_equiv_tr_dir.
        assert (NO_LEAVES: actions_no_leaves [Areg r1; Acheck inp; Areg (Quantified greedy 0 plus r1)] dir). {
          apply actions_no_leaves_add_left with (a := [Areg r1]).
          apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified greedy 0 plus r1)]).
          apply check_end_no_leaves. lia.
        }
        assert (NO_LEAVES0: actions_no_leaves [Areg r2; Acheck inp; Areg (Quantified greedy 0 plus r2)] dir). {
          apply actions_no_leaves_add_left with (a := [Areg r2]).
          apply actions_no_leaves_add_right with (a := [Acheck inp]) (b := [Areg (Quantified greedy 0 plus r2)]).
          apply check_end_no_leaves. lia.
        }
        unfold actions_no_leaves in NO_LEAVES, NO_LEAVES0.
        destruct greedy; simpl.
        * rewrite NO_LEAVES by auto. rewrite NO_LEAVES0 by auto. reflexivity.
        * rewrite NO_LEAVES by auto. rewrite NO_LEAVES0 by auto. reflexivity.
    - (* Not at the end of input *)
      intros inp gm Hremlength delta t1 t2 TREE1 TREE2.
      inversion TREE1; subst; inversion TREE2; subst.
      + (* Done *) inversion SKIP; inversion SKIP0. unfold tree_equiv_tr_dir. reflexivity.
      + destruct plus; discriminate.
      + destruct plus; discriminate.
      + (* Free *) assert (plus = plus0). { destruct plus0; destruct plus; congruence. }
        subst plus0. clear H1.
        inversion SKIP; subst inp0 gm0 dir0 tskip. inversion SKIP0; subst inp0 gm0 dir0 tskip0.
        unfold tree_equiv_tr_dir.
        rewrite <- DEF_GROUPS in *.
        assert (leaves_equiv [] (tree_leaves titer (GroupMap.reset (def_groups r1) gm) inp dir)
          (tree_leaves titer0 (GroupMap.reset (def_groups r1) gm) inp dir)). {
          eapply actions_equiv_interm_prop with
            (a1 := [Areg r1; Acheck inp]) (a2 := [Areg r2; Acheck inp])
            (P := fun lf => StrictSuffix.strict_suffix (fst lf) inp dir).
          5: apply ISTREE1. 5: apply ISTREE0.
          -- apply app_eq_right with (a1 := [Areg r1]) (a2 := [Areg r2]) (acts := [Acheck inp]).
             unfold actions_equiv_dir. intros. apply Hequiv; auto.
          -- apply actions_respect_prop_add_left with (a := [Areg r1]) (b := [Acheck inp]).
             apply check_actions_prop.
          -- apply actions_respect_prop_add_left with (a := [Areg r2]) (b := [Acheck inp]).
             apply check_actions_prop.
          -- (* Apply IHn *)
             unfold actions_equiv_dir_cond. clear TREE1 TREE2. intros [inp' gm'] STRICT_SUFFIX t1 t2 TREE1 TREE2. simpl in *.
             apply IHn with (delta := plus); auto.
             pose proof strict_suffix_remaining_length _ _ _ STRICT_SUFFIX. lia.
        }
        destruct greedy; simpl.
        * (* Greedy *)
          apply leaves_equiv_app. 2: reflexivity. auto.
        * (* Lazy *)
          apply leaves_equiv_app with (p1 := [(inp, gm)]) (p2 := [(inp, gm)]). 1: reflexivity. auto.
  Qed.

  (* Quantifier case: if r1 ≅ r2, then r1{min, Δ, p} ≅ r2{min, Δ, p} for all min, Δ and p. *)
  Theorem regex_equiv_quant:
    forall r1 r2 dir,
      tree_equiv_dir rer dir r1 r2 ->
      forall greedy min delta,
        tree_equiv_dir rer dir (Quantified greedy min delta r1) (Quantified greedy min delta r2).
  Proof.
    intros r1 r2 dir EQUIV greedy min delta.
    destruct min.
    - apply regex_equiv_quant_free. auto.
    - auto using regex_equiv_quant_forced, regex_equiv_quant_free.
  Qed.


  (* The direction of a context starting with a lookaround is never Same. *)
  Lemma ctx_dir_lookaround_not_Same:
    forall lk ctx, ctx_dir (CLookaround lk ctx) <> Same.
  Proof.
    intros lk ctx. destruct lk; simpl; destruct (ctx_dir ctx); discriminate.
  Qed.


  (** * Main theorems: regex equivalence is preserved by plugging into a context *)

  (* Theorem for bidirectional contexts *)
  Theorem regex_equiv_ctx_samedir:
    forall r1 r2 dir,
      r1 ≅[rer][dir] r2 ->
      forall ctx,
        ctx_dir ctx = Same ->
        (plug_ctx ctx r1) ≅[rer][dir] (plug_ctx ctx r2).
  Proof.
    intros r1 r2 dir Hequiv ctx Hctxdir.
    induction ctx.
    - (* Hole *) auto.
    - (* Disjunction left *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      unfold tree_equiv_tr_dir in *.
      simpl. apply leaves_equiv_app; auto.
      assert (t1 = t0) by (eapply is_tree_determ; eauto). subst t1. apply leaves_equiv_refl.
    
    - (* Disjunction right *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      unfold tree_equiv_tr_dir in *.
      simpl. apply leaves_equiv_app; auto.
      assert (t4 = t3) by (eapply is_tree_determ; eauto). subst t4. apply leaves_equiv_refl.

    - (* Sequence left *)
      simpl in *. unfold tree_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      destruct dir.
      + (* Forward *)
        simpl in *. pose proof app_eq_left _ _ [Areg r0] forward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      + (* Backward *)
        simpl in *. pose proof app_eq_right _ _ [Areg r0] backward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      
    - (* Sequence right *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      destruct dir.
      + (* Forward *)
        simpl in *. pose proof app_eq_right _ _ [Areg r0] forward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      + (* Backward *)
        simpl in *. pose proof app_eq_left _ _ [Areg r0] backward IHctx.
        unfold actions_equiv_dir in H. simpl in H. unfold tree_equiv_tr_dir in *. auto.
      
    - (* Quantified *)
      simpl in *. specialize (IHctx Hctxdir). apply regex_equiv_quant. auto.

    - (* Lookaround: direction of context is never Same *)
      exfalso. exact (ctx_dir_lookaround_not_Same _ _ Hctxdir).

    - (* Group *)
      simpl in *. unfold tree_equiv_dir, actions_equiv_dir in *. specialize (IHctx Hctxdir).
      destruct IHctx as [IHgroups IHctx]. split.
      1: { simpl. f_equal. auto. }
      intros inp gm t1 t2 TREE1 TREE2.
      inversion TREE1; subst. inversion TREE2; subst.
      unfold tree_equiv_tr_dir in *. simpl.
      assert (TREE1': exists t1, is_tree rer [Areg (plug_ctx ctx r1)] inp (GroupMap.open (idx inp) gid gm) dir t1). {
        exists (compute_tr rer [Areg (plug_ctx ctx r1)] inp (GroupMap.open (idx inp) gid gm) dir). apply compute_tr_is_tree.
      }
      assert (TREE2': exists t2, is_tree rer [Areg (plug_ctx ctx r2)] inp (GroupMap.open (idx inp) gid gm) dir t2). {
        exists (compute_tr rer [Areg (plug_ctx ctx r2)] inp (GroupMap.open (idx inp) gid gm) dir). apply compute_tr_is_tree.
      }
      destruct TREE1' as [t1 TREE1']. destruct TREE2' as [t2 TREE2'].
      change [Areg ?A; Aclose gid] with ([Areg A] ++ [Aclose gid]) in TREECONT.
      change [Areg ?A; Aclose gid] with ([Areg A] ++ [Aclose gid]) in TREECONT0.
      pose proof leaves_concat _ _ _ _ _ _ _ TREECONT TREE1' as APP1.
      pose proof leaves_concat _ _ _ _ _ _ _ TREECONT0 TREE2' as APP2.
      eapply flatmap_leaves_equiv_l. 3: apply APP1. 3: apply APP2. 2: auto. apply act_from_leaf_determ.
  Qed.


  (* Lemmas for lookarounds *)
  Lemma equiv_lk_result_same:
    forall lk r1 r2,
      r1 ≅[rer][lk_dir lk] r2 ->
      forall inp gm treelk1 treelk2,
        is_tree rer [Areg r1] inp gm (lk_dir lk) treelk1 ->
        is_tree rer [Areg r2] inp gm (lk_dir lk) treelk2 ->
        lk_result lk treelk1 gm inp = lk_result lk treelk2 gm inp.
  Proof.
    intros lk r1 r2 EQUIV inp gm treelk1 treelk2 TREE1 TREE2.
    unfold lk_result.
    rewrite observe_equivalence_gen with (r1 := r1) (r2 := r2) (t2 := treelk2) by auto. reflexivity.
  Qed.

  Lemma tree_leaves_lk:
    forall lk tlk t1 gm inp dir,
      tree_leaves (LK lk tlk t1) gm inp dir =
        match lk_result lk tlk gm inp with
        | Some gm_res => tree_leaves t1 gm_res inp dir
        | None => [] (* should not happen *)
        end.
  Proof.
    intros. unfold lk_result. simpl.
    rewrite first_tree_leaf.
    destruct positivity; destruct tree_leaves as [ | [inp' gm']]; simpl; auto.
  Qed.

  Lemma regex_equiv_ctx_lookaround:
    forall r1 r2 lk,
      r1 ≅[rer][lk_dir lk] r2 ->
      forall dir,
        (Lookaround lk r1) ≅[rer][dir] (Lookaround lk r2).
  Proof.
    intros r1 r2 lk EQUIV dir. unfold tree_equiv_dir in *.
    destruct EQUIV as [DEF_GROUPS EQUIV]. split; auto.
    intros inp gm t1 t2 TREE1 TREE2.
    inversion TREE1; subst; inversion TREE2; subst.
    - (* Both lookaheads succeed *)
      pose proof equiv_lk_result_same lk r1 r2 (conj DEF_GROUPS EQUIV) _ _ _ _ TREELK TREELK0 as RES_LK_EQ.
      unfold tree_equiv_tr_dir. do 2 rewrite tree_leaves_lk.
      rewrite <- RES_LK_EQ. rewrite RES_LK.
      inversion TREECONT; subst. inversion TREECONT0; subst. reflexivity.
    - (* Impossible case *)
      exfalso. pose proof equiv_lk_result_same lk r1 r2 (conj DEF_GROUPS EQUIV) _ _ _ _ TREELK TREELK0. congruence.
    - (* Impossible case *)
      exfalso. pose proof equiv_lk_result_same lk r1 r2 (conj DEF_GROUPS EQUIV) _ _ _ _ TREELK TREELK0. congruence.
    - (* Both lookaheads fail *)
      unfold tree_equiv_tr_dir. simpl. reflexivity.
  Qed.


  (* Eight inversion lemmas for context directions involving lookarounds *)
  Lemma ctx_dir_lookahead_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookAhead ctx) = Forward ->
      ctx_dir ctx = Forward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.
  
  Lemma ctx_dir_lookahead_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookAhead ctx) = Backward ->
      ctx_dir ctx = Backward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_lookbehind_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookBehind ctx) = Forward ->
      ctx_dir ctx = Forward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_lookbehind_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround LookBehind ctx) = Backward ->
      ctx_dir ctx = Backward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_neglookahead_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookAhead ctx) = Forward ->
      ctx_dir ctx = Forward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.
  
  Lemma ctx_dir_neglookahead_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookAhead ctx) = Backward ->
      ctx_dir ctx = Backward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_neglookbehind_fwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookBehind ctx) = Forward ->
      ctx_dir ctx = Forward.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.

  Lemma ctx_dir_neglookbehind_bwd_inv:
    forall ctx,
      ctx_dir (CLookaround NegLookBehind ctx) = Backward ->
      ctx_dir ctx = Backward \/ ctx_dir ctx = Same.
  Proof.
    intros ctx H. simpl in *.
    destruct (ctx_dir ctx); try discriminate; auto.
  Qed.


  (* Theorem for forward contexts *)
  Theorem regex_equiv_ctx_forward:
    forall r1 r2,
      r1 ≅[rer][forward] r2 ->
      forall ctx, ctx_dir ctx = Forward ->
        (plug_ctx ctx r1) ≅[rer] (plug_ctx ctx r2).
  Proof.
    intros r1 r2 EQUIV ctx Hctxforward.
    induction ctx.
    - discriminate.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionL _ CHole); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionR CHole _); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceL _ CHole); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceR CHole _); auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CQuantified _ _ _ CHole); auto.
    - unfold tree_equiv in *. destruct lk.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_lookahead_fwd_inv in Hctxforward. destruct Hctxforward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_lookbehind_fwd_inv in Hctxforward. auto.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_neglookahead_fwd_inv in Hctxforward. destruct Hctxforward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_neglookbehind_fwd_inv in Hctxforward. auto.
    - specialize (IHctx Hctxforward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CGroup _ CHole); auto.
  Qed.


  (* Theorem for backward contexts *)
  Theorem regex_equiv_ctx_backward:
    forall r1 r2,
      r1 ≅[rer][backward] r2 ->
      forall ctx, ctx_dir ctx = Backward ->
        (plug_ctx ctx r1) ≅[rer] (plug_ctx ctx r2).
  Proof.
    intros r1 r2 EQUIV ctx Hctxbackward.
    induction ctx.
    - discriminate.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionL _ CHole); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CDisjunctionR CHole _); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceL _ CHole); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CSequenceR CHole _); auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CQuantified _ _ _ CHole); auto.
    - unfold tree_equiv in *. destruct lk; try discriminate.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_lookahead_bwd_inv in Hctxbackward. auto.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_lookbehind_bwd_inv in Hctxbackward. destruct Hctxbackward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_neglookahead_bwd_inv in Hctxbackward. auto.
      + simpl. apply regex_equiv_ctx_lookaround.
        apply ctx_dir_neglookbehind_bwd_inv in Hctxbackward. destruct Hctxbackward.
        * auto.
        * apply regex_equiv_ctx_samedir; auto.
    - specialize (IHctx Hctxbackward).
      intro dir. simpl.
      apply regex_equiv_ctx_samedir with (ctx := CGroup _ CHole); auto.
  Qed.

End Congruence.
