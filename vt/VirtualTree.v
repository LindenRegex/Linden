
Require Import CData.
Require Import ListHelpers.

From Stdlib Require Import Arith Lia List Permutation.
Import ListNotations.

Module VT (Data : CDATA).
  Import Data.

  (* Definitions *)

  (** Inductive type *)

  Inductive VirtualTree : Type :=
  | Stump
  | Node (data: Data.t) (child: VirtualTree)
  | Branch (l: VirtualTree) (r: VirtualTree)
  | Leaf (id: nat).

  (** Validity *)

  (*** Structure validity *)

  Fixpoint is_valid_tree_structure (t: VirtualTree) : Prop :=
    match t with
    | Stump => True
    | Node _ c => match c with
                  | Stump => False
                  | Node _ _ => False
                  | _ => is_valid_tree_structure c
                  end
    | Branch l r => match l, r with
                    | Stump, _ => False
                    | _, Stump => False
                    | _, _ => (is_valid_tree_structure l) /\ (is_valid_tree_structure r)
                    end
    | Leaf _ => True
    end.

  (*** Leaves ids validity *)

  Fixpoint get_all_ids (t: VirtualTree) : list nat :=
    match t with
    | Stump => []
    | Node d c => get_all_ids c
    | Branch l r => (get_all_ids l) ++ (get_all_ids r)
    | Leaf id => [id]
    end.

  Definition is_valid_tree_ids (t: VirtualTree) : Prop := NoDup (get_all_ids t).

  (*** Node data validity *)

  Fixpoint is_valid_tree_data (t: VirtualTree) (p: Data.p) : Prop :=
    match t with
    | Stump => True
    | Node d c => Data.is_valid p d /\ is_valid_tree_data c p
    | Branch l r => is_valid_tree_data l p /\ is_valid_tree_data r p
    | Leaf _ => True
    end.

  (*** External id validity *)

  Fixpoint contains_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Stump => false
    | Node _ c => contains_id c id
    | Branch l r => contains_id l id || contains_id r id
    | Leaf i => i =? id
    end.

  Definition is_valid_id (t: VirtualTree) (id: nat) : Prop :=
    In id (get_all_ids t).

  Fixpoint max_id_in_tree (t: VirtualTree) : nat :=
    match t with
    | Stump => 0 (* Stump case does not matter *)
    | Node _ c => max_id_in_tree c
    | Branch l r => Nat.max (max_id_in_tree l) (max_id_in_tree r)
    | Leaf i => i
    end.

  (** State *)

  (* Tree and compression parameter for Data *)
  Definition State := (VirtualTree * Data.p)%type.

  Definition tree (s: State) : VirtualTree :=
    match s with
    | (t, _) => t
    end.
  
  Definition param (s: State) : Data.p :=
    match s with
    | (_, p) => p
    end.

  Definition is_valid_state (s: State) : Prop :=
    is_valid_tree_structure (tree s) /\
      is_valid_tree_ids (tree s) /\
      is_valid_tree_data (tree s) (param s).

  (* Dead tree: function results are Stump as well *)
  Definition dead (param: Data.p) : State :=
    (Stump, param).

  (* Initial tree structure for usage: the tree can be modified *)
  Definition initial_tree (param: Data.p) : State :=
    (Leaf 0, param).

  (** Boolean structure checkers *)
  
  Definition is_leaf_with_id (t: VirtualTree) (id: nat) : bool :=
    match t with
    | Leaf i => Nat.eqb i id
    | _ => false
    end.

  Definition is_stump (t: VirtualTree) : bool :=
    match t with
    | Stump => true
    | _ => false
    end.

  (* Checks for a chain containing only nodes (zero or one node if the structure is valid)
     with a leaf with the input id at the end *)
  Fixpoint is_stem_with_id (id : nat) (t: VirtualTree) : bool :=
    match t with
    | Stump => false
    | Node _ c => is_stem_with_id id c
    | Branch _ _ => false
    | Leaf i => Nat.eqb i id
    end.

  (** Operations *)

  (*** Insert: add some data (Data.t) at one leaf *)

  Fixpoint insert_in_tree (id: nat) (new: Data.t) (t: VirtualTree) (p: Data.p) : VirtualTree :=
    match t with
    | Stump => Stump
    | Node d c => if is_leaf_with_id c id
                  then Node (Data.compress p d new) c
                  else Node d (insert_in_tree id new c p)
    | Branch l r => Branch (insert_in_tree id new l p) (insert_in_tree id new r p)
    | Leaf i => if (i =? id)
                then Node new (Leaf i)
                else Leaf i
    end.

  Definition insert (id: nat) (new : Data.t) (s: State) : State :=
    (insert_in_tree id new (tree s) (param s), param s).

  (*** Split: replace a leaf with a branch whose children are leaves.
   The children's ids are id and new_id *)

  Fixpoint split_in_tree (id: nat) (new_id: nat) (t: VirtualTree) : VirtualTree :=
    match t with
    | Stump => Stump
    | Node d c => Node d (split_in_tree id new_id c)
    | Branch l r => Branch (split_in_tree id new_id l) (split_in_tree id new_id r)
    | Leaf i => if (i =? id)
                then Branch (Leaf i) (Leaf new_id)
                else Leaf i
    end.

  Definition split (id: nat) (s: State) : State * nat :=
    let t:= tree s in
    let new_id := (max_id_in_tree t) + 1 in
    ((split_in_tree id new_id t, param s), new_id).

  (*** Delete: delete a leaf *)

  Fixpoint delete_in_tree (id : nat) (t: VirtualTree) (p: Data.p) : VirtualTree :=
    match t with
    | Stump => Stump
    | Node d c =>
        let c' := delete_in_tree id c p in
        match c' with
        | Stump => Stump
        | Branch _ _ => Node d c'
        | Node d'' c'' => Node (Data.compress p d d'') c''
        | Leaf i => Node d c'
        end
    | Branch l r => if (is_stem_with_id id l)
                    then r
                    else if (is_stem_with_id id r)
                         then l
                         else Branch (delete_in_tree id l p) (delete_in_tree id r p)
    | Leaf i => if (i =? id)
                then Stump
                else Leaf i
    end.

  Definition delete (id: nat) (s: State) :=
    (delete_in_tree id (tree s) (param s), param s).

  (*** Get: get the compressed data for one leaf *)

  (* Top down computation *)
  Fixpoint get_compressed_data_in_tree (id: nat)
    (t: VirtualTree) (p: Data.p) (acc: option Data.t):
    option Data.t :=
    match t with
    | Stump => acc
    | Node d c =>
        let acc' := match acc with
                    | Some a => Some (Data.compress p a d)
                    | None => Some d
                    end in
        get_compressed_data_in_tree id c p acc'
    | Branch l r =>
        match (get_compressed_data_in_tree id l p acc) with
        | Some a => Some a
        | None => get_compressed_data_in_tree id r p acc
        end
    | Leaf i => if Nat.eqb i id
                then acc
                else None
    end.

  Definition get_compressed_data (id: nat) (s: State): option Data.t :=
    get_compressed_data_in_tree id (tree s) (param s) None.

  (* Properties *)

  (** Id validity helpers *)

  Lemma contains_valid_id : forall t id,
      contains_id t id = true <-> is_valid_id t id.
  Proof.
    unfold is_valid_id.
    intros t id. split; induction t; intros H; simpl in *; auto.
    - congruence.
    - apply in_app_iff.
      apply Bool.orb_prop in H.
      tauto.
    - apply Nat.eqb_eq in H.
      tauto.
    - apply Bool.orb_true_intro.
      apply in_app_iff in H.
      tauto.
    - apply Nat.eqb_eq.
      tauto.
  Qed.

  Lemma not_contains_valid_id : forall t id,
      contains_id t id = false <-> ~ is_valid_id t id.
  Proof.
    unfold is_valid_id.
    split; intros.
    - intros C.
      apply contains_valid_id in C.
      congruence.
    - induction t0; simpl in *; auto.
      + rewrite in_app_iff in H.
        apply Bool.orb_false_iff.
        split; auto.
      + apply Nat.eqb_neq.
        tauto.
  Qed.

  Lemma greater_than_max_is_invalid_id : forall t x,
      x > max_id_in_tree t ->
      ~ is_valid_id t x.
  Proof.
    unfold not, is_valid_id.
    intros t. induction t; intros x H C; simpl in *.
    - auto.
    - eapply IHt; eauto.
    - apply Nat.max_lub_lt_iff in H.
      destruct H as [H1 H2].
      apply in_app_iff in C.
      destruct C as [C1 | C2];
        [apply IHt1 with (x:=x) | apply IHt2 with (x:=x)];
        auto;
        lia.
    - lia.
  Qed.

  Lemma valid_id_is_leq_max: forall t x,
      is_valid_id t x ->
      x <= max_id_in_tree t.
  Proof.
    unfold is_valid_id.
    intros t. induction t; intros x H; simpl in *;
      auto; try lia.
    - apply in_app_iff in H.
      destruct H as [H1 | H2].
      + apply IHt1 in H1.
        lia.
      + apply IHt2 in H2.
        lia.
  Qed.

  Lemma branch_id_valid_in_one : forall l r id,
      is_valid_tree_ids (Branch l r) ->
      ~ (is_valid_id l id ) \/ ~ (is_valid_id r id).
  Proof.
    intros l r id H.
    unfold is_valid_id in *.
    unfold is_valid_tree_ids in H. simpl in H.
    destruct (contains_id (Branch l r) id) eqn:Hi; simpl in Hi.
    - apply Bool.orb_prop in Hi.
      destruct Hi as [Hi | Hi];
        [right | left];
        apply contains_valid_id in Hi;
        eapply ListHelpers.NoDup_in_app; eauto.
      apply ListHelpers.NoDup_app_comm; auto.
    - apply Bool.orb_false_iff in Hi.
      rewrite not_contains_valid_id in Hi.
      tauto.
  Qed.

  Lemma get_all_ids_stem_with_id : forall t i,
      is_stem_with_id i t = true ->
      get_all_ids t = [i].
  Proof.
    intros t i.
    induction t; intros H; simpl in *; try congruence; auto.
    apply Nat.eqb_eq in H; subst; reflexivity.
  Qed.

  (** Structure helpers *)

  Lemma is_Leaf_with_id : forall t id,
      is_leaf_with_id t id = true -> t = Leaf id.
  Proof.
    intros t i H. destruct t; simpl in *; try congruence.
    apply Nat.eqb_eq in H.
    congruence.
  Qed.

  Lemma is_Stump : forall t,
      is_stump t = true -> t = Stump.
  Proof.
    intros t H; destruct t; simpl in *; try congruence.
  Qed.

  Lemma is_not_Stump : forall t,
      is_stump t = false -> t <> Stump.
  Proof.
    intros t H; destruct t; simpl in *; congruence.
  Qed.

  Lemma node_of_child_with_valid_structure : forall d c,
      c <> Stump ->
      (forall d' c', c <> Node d' c') ->
      is_valid_tree_structure c ->
      is_valid_tree_structure (Node d c).
  Proof.
    intros. simpl in *.
    destruct c; auto.
    specialize (H0 data c).
    congruence.
  Qed.

  Lemma branch_of_children_with_valid_structure : forall l r,
      l <> Stump ->
      r <> Stump ->
      is_valid_tree_structure l ->
      is_valid_tree_structure r ->
      is_valid_tree_structure (Branch l r).
  Proof.
    intros. simpl in *.
    destruct l; destruct r; auto.
  Qed.

  Lemma is_stem_with_id_struct : forall t id,
      is_valid_tree_structure t ->
      is_stem_with_id id t = true ->
      (t = Leaf id \/ (exists d, t = Node d (Leaf id))).
  Proof.
    intros t id; induction t; intros Hs H; simpl in *; try congruence.
    - right.
      destruct t0 eqn:T0; try contradiction; simpl in *; try congruence.
      exists data.
      apply Nat.eqb_eq in H.
      congruence.
    - left.
      apply Nat.eqb_eq in H.
      congruence.
  Qed.

  Lemma is_stem_with_invalid_id : forall t id,
      ~ is_valid_id t id ->
      is_stem_with_id id t = false.
  Proof.
    unfold is_valid_id.
    intros t id H.
    induction t; simpl in *; auto.
    - apply Nat.eqb_neq. lia.
  Qed.

  Lemma invalid_id_in_stem_with_id : forall t i j,
      is_valid_tree_structure t ->
      is_stem_with_id i t = true ->
      i <> j ->
      ~ is_valid_id t j.
  Proof.
    unfold is_valid_id.
    intros t i j Hs H Hij.
    apply is_stem_with_id_struct in H; auto.
    destruct H as [H | [d H]]; subst; simpl; lia.
  Qed.

  (** Tactics definitions *)

  Ltac solve_node_trivial :=
    match goal with
    | [H: ?x |- ?x] => assumption
    | [ |- ?t <> Stump] => destruct t; try contradiction; congruence
    | [ |- is_valid_tree_structure ?t] => destruct t; tauto
    | [ |- is_valid_tree_ids ?t] => unfold is_valid_tree_ids; tauto
    | _ => tauto
    end.

  Ltac solve_branch_trivial :=
    match goal with
    | [t1: VirtualTree, t2: VirtualTree |- ?t <> Stump] =>
        destruct t1, t2; try contradiction; congruence
    | [t1: VirtualTree, t2: VirtualTree |- is_valid_tree_structure ?t] =>
        destruct t1, t2; tauto
    | [H: is_valid_tree_ids (Branch ?t1 ?t2) |- is_valid_tree_ids ?t1] =>
        unfold is_valid_tree_ids; simpl in *; eapply NoDup_app_remove_r; eauto
    | [H: is_valid_tree_ids (Branch ?t1 ?t2) |- is_valid_tree_ids ?t2] =>
        unfold is_valid_tree_ids; simpl in *; eapply NoDup_app_remove_l; eauto
    | [H: ~ is_valid_id (Branch ?t1 ?t2) ?i |- ~ is_valid_id ?t1 ?i] =>
        unfold is_valid_id in *; simpl in H; rewrite in_app_iff in H; tauto
    | [H: ~ is_valid_id (Branch ?t1 ?t2) ?i |- ~ is_valid_id ?t2 ?i] =>
        unfold is_valid_id in *; simpl in H; rewrite in_app_iff in H; tauto
    | _ => tauto
    end.

  Ltac branch_valid_xor :=
    match goal with
      | [Hids: is_valid_tree_ids (Branch ?t1 ?t2), Hi: is_valid_id (Branch ?t1 ?t2) ?i |- _] =>
          specialize (branch_id_valid_in_one t1 t2 i Hids) as XOR;
          assert (I': is_valid_id (Branch t1 t2) i) by assumption;
          unfold is_valid_id in Hi; simpl in Hi;
          apply in_app_iff in Hi; destruct Hi as [Hi | Hi]
      end.

  Ltac destruct_stems :=
    repeat match goal with
      | [ |- context[is_stem_with_id ?i ?t1] ] =>
          destruct (is_stem_with_id i t1) eqn:B1
      | [ |- context[is_stem_with_id ?i ?t2] ] =>
          destruct (is_stem_with_id i t2) eqn:B2
      | [Hids : is_valid_tree_ids (Branch ?t1 ?t2),
            B1: is_stem_with_id ?i ?t1 = true, B2: is_stem_with_id ?i ?t2 = true |- _] =>
          apply get_all_ids_stem_with_id in B1, B2;
          unfold is_valid_tree_ids in *; simpl in *;
          rewrite B1, B2 in Hids; simpl in *;
          apply ListHelpers.not_NoDup_two in Hids; contradiction
      | [Hids : NoDup (get_all_ids ?t1 ++ get_all_ids ?t2),
            B1: is_stem_with_id ?i ?t1 = true, B2: is_stem_with_id ?i ?t2 = true |- _] =>
          apply get_all_ids_stem_with_id in B1, B2;
          rewrite B1, B2 in Hids; simpl in *;
          apply ListHelpers.not_NoDup_two in Hids; contradiction
    end.

  (** Get properties *)

  Lemma get_is_valid_in_tree : forall t p i o,
      is_valid_tree_data t p ->
      (forall d, o = Some d -> Data.is_valid p d) ->
      (forall d, get_compressed_data_in_tree i t p o = Some d -> Data.is_valid p d).
  Proof.
    intros t param i; induction t; intros o Hd Hv d' Hd'; simpl in *; auto.
    - destruct o eqn:O; simpl in *.
      + eapply IHt; try tauto.
        2: eauto.
        intros d H. injection H as H. subst.
        apply Data.compress_valid.
        * auto.
        * tauto.
      + eapply IHt; try tauto.
        2: eauto.
        intros d H. injection H as H. subst.
        tauto.
    - destruct (get_compressed_data_in_tree i t1 param o) eqn:G1.
      + injection Hd' as Hd'. subst.
        eapply IHt1; eauto. tauto.
      + eapply IHt2; eauto. tauto.
    - destruct (id =? i); try congruence.
      auto.
  Qed.

  Lemma get_on_invalid_id_in_tree : forall t p i o,
      t <> Stump ->
      is_valid_tree_structure t ->
      ~ is_valid_id t i ->
      get_compressed_data_in_tree i t p o = None.
  Proof.
    unfold is_valid_id.
    intros t; induction t; intros param i o Ht Hs H; simpl in *.
    - congruence.
    - apply IHt; try solve_node_trivial.
    - rewrite in_app_iff in H.
      rewrite IHt1; try apply IHt2; try solve_branch_trivial.
    - destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I.
        tauto.
      + reflexivity.
  Qed.

  Lemma get_on_valid_id_from_some : forall t p i d,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_id t i ->
      (exists d', get_compressed_data_in_tree i t p (Some d) = Some d').
  Proof.
    intros t. induction t; intros param i d Hs Hids Hi; simpl in *; eauto.
    - eapply IHt; try solve_node_trivial.
    - branch_valid_xor.
      + eapply IHt1 in Hi; try solve_branch_trivial.
        destruct Hi as [d' Hi].
        erewrite Hi.
        eauto.
      + rewrite get_on_invalid_id_in_tree;
          try solve_branch_trivial.
        eapply IHt2; try solve_branch_trivial.
    - unfold is_valid_id in *.
      simpl in *.
      destruct Hi as [Hi | Hi]; try contradiction.
      subst.
      rewrite Nat.eqb_refl.
      eauto.
  Qed.

  Theorem get_is_valid : forall s i,
      is_valid_state s ->
      (forall d, get_compressed_data i s = Some d -> Data.is_valid (param s) d).
  Proof.
    unfold get_compressed_data.
    intros s i [Hs [Hids Hd]].
    eapply get_is_valid_in_tree; eauto.
    intros. congruence.
  Qed.

  Theorem get_on_invalid_id : forall s i,
      is_valid_state s ->
      ~ is_valid_id (tree s) i ->
      get_compressed_data i s = None.
  Proof.
    unfold get_compressed_data.
    intros s i [Hs [Hids Hd]] Hi.
    destruct s as [t p].
    destruct t eqn:T.
    1: simpl. reflexivity.
    all: apply get_on_invalid_id_in_tree; auto; simpl; congruence.
  Qed.

  (** Insert properties *)

  Lemma insert_on_invalid_id : forall t p i d,
      ~ is_valid_id t i ->
      t = insert_in_tree i d t p.
  Proof.
    unfold is_valid_id.
    intros t p i d. induction t; intros H; simpl in *; auto.
    - destruct (is_leaf_with_id t0 i) eqn:L.
      + apply is_Leaf_with_id in L. subst.
        simpl in *.
        specialize (IHt H).
        rewrite Nat.eqb_refl in IHt.
        congruence.
      + rewrite <- IHt; auto.
    - rewrite in_app_iff in H.
      rewrite <- IHt1, <- IHt2; tauto.
    - destruct (_ =? _) eqn:I; try congruence.
      apply Nat.eqb_eq in I; lia.
  Qed.

  Lemma insert_is_stump : forall t p id d,
      insert_in_tree id d t p = Stump -> t = Stump.
  Proof.
    intros t p id d H.
    destruct t; simpl in *; try congruence.
    - destruct (is_leaf_with_id _); simpl; congruence.
    - destruct (_ =? _); congruence.
  Qed.

  Lemma insert_is_not_stump : forall t p id d,
      t <> Stump -> (insert_in_tree id d t p) <> Stump.
  Proof.
    intros t. intros.
    destruct t; simpl in *; try congruence.
    - destruct (is_leaf_with_id _ _); congruence.
    - destruct (_ =? _); congruence.
  Qed.

  (*** Insert: Validity of resulting state *)

  (* Tree ids are unchanged *)
  Lemma insert_ids : forall t p id d,
      get_all_ids t = get_all_ids (insert_in_tree id d t p).
  Proof.
    intros t param i d. induction t; simpl in *; try auto.
    - destruct (is_leaf_with_id t0 i); simpl in *; auto.
    - rewrite <- IHt1. rewrite <- IHt2; auto.
    - destruct (id =? i) eqn:I; simpl; auto.
  Qed.

  Lemma insert_valid_ids : forall t p id d,
      is_valid_tree_ids t ->
      is_valid_tree_ids (insert_in_tree id d t p).
  Proof.
    intros.
    unfold is_valid_tree_ids in *.
    rewrite <- insert_ids;
      assumption.
  Qed.

  Lemma insert_valid_data : forall t p id d,
      Data.is_valid p d ->
      is_valid_tree_data t p ->
      is_valid_tree_data (insert_in_tree id d t p) p.
  Proof.
    intros t. induction t; intros param i d Hd H; simpl in *.
    - tauto.
    - destruct H as [H Hc].
      destruct (is_leaf_with_id t0 i); simpl.
      + split.
        * apply Data.compress_valid; assumption.
        * assumption.
      + split; auto.
    - destruct H as [H1 H2].
      split; auto.
    - destruct (id =? i); simpl; tauto.
  Qed.

  Lemma insert_valid_structure : forall t p id d,
      is_valid_tree_structure t ->
      is_valid_tree_structure (insert_in_tree id d t p).
  Proof.
    intros t; induction t; intros param i d H; auto.
    - simpl in *.
      destruct t0 eqn:T0; try contradiction.
      + unfold is_leaf_with_id.
        apply node_of_child_with_valid_structure;
          auto;
          try intros; simpl;
          congruence.
      + simpl in *.
        destruct (id =? i); auto.
    - simpl insert_in_tree.
      simpl in H.
      apply branch_of_children_with_valid_structure.
      + destruct (is_stump t1) eqn:T1.
        * apply is_Stump in T1. rewrite T1 in *.
          contradiction.
        * apply insert_is_not_stump.
          apply is_not_Stump.
          assumption.
      + destruct (is_stump t2) eqn:T2.
        * apply is_Stump in T2. rewrite T2 in *.
          destruct t1; contradiction.
        * apply insert_is_not_stump.
          apply is_not_Stump.
          assumption.
      + apply IHt1. solve_branch_trivial.
      + apply IHt2. solve_branch_trivial.
    - simpl in *.
      destruct (id =? i); auto.
  Qed.
  
  (* the output state of insert is a valid state *)
  Theorem insert_valid : forall s id d,
      Data.is_valid (param s) d ->
      is_valid_state s ->
      is_valid_state (insert id d s).
  Proof.
    intros.
    destruct H0 as [Hs [Hids Hd]].
    repeat split.
    - apply insert_valid_structure.
      assumption.
    - apply insert_valid_ids.
      assumption.
    - apply insert_valid_data;
        assumption.
  Qed.

  Lemma insert_param_unchanged : forall s id d,
      param s = param (insert id d s).
  Proof. auto. Qed.

  (*** Insert: helper tactic *)

  Ltac solve_insert_trivial :=
    repeat match goal with
    | [ |- is_valid_tree_structure (insert_in_tree ?id ?d ?t ?p)] =>
        apply insert_valid_structure; try solve_branch_trivial
    | [ |- insert_in_tree ?id ?d ?t ?p <> Stump] =>
        apply insert_is_not_stump; destruct t; try contradiction; congruence
    | [ |- ~ is_valid_id (insert_in_tree ?i ?d ?t1 ?param) ?i] =>
        rewrite <- insert_on_invalid_id
    | _ => tauto
    end.

  (*** Insert: Get on resulting state *)

  Lemma insert_get_none_in_tree : forall t p id d o,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_id t id ->
      get_compressed_data_in_tree id t p o = None ->
      get_compressed_data_in_tree id
        (insert_in_tree id d t p) p o = Some d.
  Proof.
    intros t; induction t;
      intros param i d o Hs Hids Hid H;
      simpl in *.
    - contradiction.
    - unfold is_valid_id in Hid. simpl in Hid.
      apply get_on_valid_id_from_some with
        (d:= match o with | Some a => compress param a data | None => data end)
        (p:= param)
        in Hid;
        try solve_node_trivial.
      destruct Hid as [d' Hid].
      destruct o; try congruence.
    - branch_valid_xor.
      + destruct (get_compressed_data_in_tree i t1 param o) eqn:G; try congruence.
        erewrite IHt1; try solve_branch_trivial.
      + rewrite get_on_invalid_id_in_tree; try solve_insert_trivial.
        apply IHt2; try solve_branch_trivial.
        destruct (get_compressed_data_in_tree i t1 param o);
          try congruence; auto.
    - unfold is_valid_id in *. simpl in *.
      destruct Hid as [Hid |]; try contradiction.
      subst.
      rewrite Nat.eqb_refl in *; simpl.
      rewrite Nat.eqb_refl. subst.
      reflexivity.
  Qed.

  Theorem insert_get_none : forall s id d,
      is_valid_state s ->
      is_valid_id (tree s) id ->
      get_compressed_data id s = None ->
      get_compressed_data id (insert id d s) = Some d.
  Proof.
    intros s id d [Hs [Hids Hd]] Hid H.
    unfold get_compressed_data, insert.
    simpl.
    apply insert_get_none_in_tree; auto.
  Qed.

  Lemma invalid_id_in_insert : forall t p i d id,
      ~ is_valid_id t id ->
      ~ is_valid_id (insert_in_tree i d t p) id.
  Proof.
    intros.
    unfold is_valid_id in *.
    rewrite <- insert_ids in *.
    assumption.
  Qed.

  Lemma insert_get_some_in_tree : forall t p id d c_old o,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_tree_data t p ->
      is_valid_id t id ->
      Data.is_valid p d ->
      (forall o', o = Some o' -> Data.is_valid p o') -> 
      get_compressed_data_in_tree id t p o = Some c_old ->
      get_compressed_data_in_tree id (insert_in_tree id d t p) p o = Some (Data.compress p c_old d).
  Proof.
    intros t; induction t; intros param i d c_old o Hs Hids Hdata Hi Hd Ho H; simpl in *; auto.
    - contradiction.
    - destruct (is_leaf_with_id t0 i) eqn:L.
      + apply is_Leaf_with_id in L. subst. simpl in *.
        rewrite Nat.eqb_refl in *.
        destruct o eqn:O.
        * injection H as H. rewrite <- H.
          rewrite Data.compress_assoc; auto.
          tauto.
        * injection H as H. subst.
          reflexivity.
      + simpl.
        destruct o eqn:O;
          apply IHt; try solve_node_trivial.
        all: intros o' H'; injection H' as H'; rewrite <- H';
          try apply Data.compress_valid;
          try tauto; apply Ho; auto.
    - branch_valid_xor.
      + destruct (get_compressed_data_in_tree i t1 param o) eqn:G.
        * injection H as H.
          rewrite IHt1 with (c_old := t0); try solve_branch_trivial.
          congruence.
        * rewrite get_on_invalid_id_in_tree with (t:=t2) in H; try solve_branch_trivial.
          congruence.
      + rewrite get_on_invalid_id_in_tree with (t:=t1) in H; try solve_branch_trivial.
        rewrite get_on_invalid_id_in_tree; solve_insert_trivial.
        apply IHt2; solve_branch_trivial.
    - unfold is_valid_id in *. destruct Hi as [Hi |]; try contradiction.
      apply Nat.eqb_eq in Hi. rewrite Hi in *.
      simpl. rewrite Hi.
      subst.
      reflexivity.
  Qed.

  Theorem insert_get_some : forall s id d c_old,
      is_valid_state s ->
      is_valid_id (tree s) id ->
      Data.is_valid (param s) d ->
      get_compressed_data id s = Some c_old -> (* case where data already existed for id *)
      get_compressed_data id (insert id d s) = Some (Data.compress (param s) c_old d).
  Proof.
    intros s id d c [Hs [Hids Hd]] Hid H.
    unfold get_compressed_data, insert.
    apply insert_get_some_in_tree; auto.
    intros. congruence.
  Qed.

  Lemma insert_get_unchanged_in_tree : forall t p i j d o o',
      i <> j ->
      get_compressed_data_in_tree j t p o' = o ->
      get_compressed_data_in_tree j (insert_in_tree i d t p) p o' = o.
  Proof.
    intros t; induction t;
      intros param i j d o o' Hij H;
      simpl in *.
    - assumption.
    - destruct (is_leaf_with_id t0 i) eqn:L; simpl.
      + apply is_Leaf_with_id in L. subst. simpl.
        apply Nat.eqb_neq in Hij.
        rewrite Hij.
        reflexivity.
      + rewrite IHt with (o:= o); auto.
    - destruct (get_compressed_data_in_tree j t1 param o') eqn:G.
      + rewrite IHt1 with (o := Some t0); auto.
      + rewrite IHt1 with (o := None); auto.
    - destruct (id =? i) eqn:I; simpl.
      + apply Nat.eqb_eq in I. subst.
        apply Nat.eqb_neq in Hij. rewrite Hij.
        reflexivity.
      + assumption.
  Qed.

  (* the data for all other leaves is unchanged *)
  Theorem insert_get_unchanged : forall s i j d o,
      i <> j ->
      get_compressed_data j s = o ->
      get_compressed_data j (insert i d s) = o.
  Proof.
    intros s i j d o Hij H.
    unfold get_compressed_data in *.
    apply insert_get_unchanged_in_tree; auto.
  Qed.

  (** Split properties *)

  Lemma split_on_invalid_id: forall t i i',
      ~ is_valid_id t i ->
      t = split_in_tree i i' t.
  Proof.
    unfold is_valid_id.
    intros t i i'; induction t; intros H; simpl in *; auto.
    - rewrite <- IHt; auto.
    - rewrite in_app_iff in H.
      destruct (contains_id t1 i);
        rewrite <- IHt1; try tauto;
        rewrite <- IHt2; try tauto.
    - destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I.
        lia.
      + reflexivity.
  Qed.

  Lemma split_is_Stump : forall t i i',
      split_in_tree i i' t = Stump -> t = Stump.
  Proof.
    intros t i i' H.
    destruct t; simpl in *; auto; try congruence.
    - destruct (id =? i); congruence.
  Qed.

  Lemma split_is_node : forall t i i' d c,
      split_in_tree i i' t = Node d c ->
      (exists c', t = Node d c' /\ c = split_in_tree i i' c').
  Proof.
    intros t i i' d c H.
    destruct t; simpl in *; try congruence.
    - exists t0.
      injection H as Hd Hc. subst.
      auto.
    - destruct (id =? i); simpl; congruence.
  Qed.

  Lemma split_is_branch : forall t i i' l r,
      is_valid_tree_ids t ->
      split_in_tree i i' t = Branch l r ->
      (exists l', t = Branch l' r /\ l = split_in_tree i i' l') \/
        (exists r', t = Branch l r' /\ r = split_in_tree i i' r') \/
        (t = Leaf i /\ l = Leaf i /\ r = Leaf i').
  Proof.
    intros t i i' l r Hids H.
    destruct t; simpl in *; try congruence.
    - destruct (contains_id (Branch t1 t2) i) eqn:I.
      + apply contains_valid_id in I.
        branch_valid_xor.
        * left.
          exists t1.
          rewrite <- split_on_invalid_id with (t:=t2) in H; try tauto.
          injection H as H1 H2. subst.
          auto.
        * right. left.
          exists t2.
          rewrite <- split_on_invalid_id with (t:=t1) in H; try tauto.
          injection H as H1 H2. subst.
          auto.
      + left.
        rewrite not_contains_valid_id in I.
        exists t1.
        rewrite <- split_on_invalid_id with (t:=t1) in *; try solve_branch_trivial.
        rewrite <- split_on_invalid_id with (t:=t2) in H; try solve_branch_trivial.
        injection H as H1 H2. subst.
        auto.
    - right. right.
      destruct (id =? i) eqn:I; try congruence.
      injection H as Hl Hr. subst.
      apply Nat.eqb_eq in I. subst.
      auto.
  Qed.

  Lemma split_is_leaf : forall t i i' id,
      split_in_tree i i' t = Leaf id ->
      t = Leaf id.
  Proof.
    intros t i i' id H.
    destruct t; simpl in *; try congruence.
    - destruct (id0 =? i); simpl; try congruence.
  Qed.

  Lemma split_is_not_Stump : forall t i i',
      t <> Stump -> (split_in_tree i i' t) <> Stump.
  Proof.
    intros t i i' H.
    destruct t; simpl; try congruence.
    - destruct (id =? i); congruence.
  Qed.

  (*** Split: Validity of resulting state *)

  Lemma split_valid_structure : forall t i i',
      is_valid_tree_structure t ->
      is_valid_tree_structure (split_in_tree i i' t).
  Proof.
    intros t i i'; induction t; intros Hs; auto.
    - simpl split_in_tree.
      simpl in Hs.
      apply node_of_child_with_valid_structure.
      + apply split_is_not_Stump; solve_node_trivial.
      + intros d' c'.
        destruct (split_in_tree i i' t0) eqn:S; try congruence.
        apply split_is_node in S. destruct S as [c'' [S1 S2]].
        subst.
        contradiction.
      + apply IHt; solve_node_trivial.
    - simpl split_in_tree.
      simpl in Hs.
      apply branch_of_children_with_valid_structure;
        try apply split_is_not_Stump;
        try apply IHt1; try apply IHt2;
        solve_branch_trivial.
    - simpl in *.
      destruct (id =? i); simpl; auto.
  Qed.

  Lemma split_ids : forall t i i',
      is_valid_tree_ids t ->
      ~ is_valid_id t i' ->
      is_valid_id t i ->
      Permutation (i' :: (get_all_ids t)) (get_all_ids (split_in_tree i i' t)).
  Proof.
    intros t; induction t; intros i i' Hids H' H; simpl in *.
    - contradiction.
    - auto.
    - branch_valid_xor.
      + rewrite app_comm_cons.
        apply Permutation_app.
        * apply IHt1; try solve_branch_trivial.
        * rewrite <- split_on_invalid_id; try tauto.
          apply Permutation_refl.
      + econstructor.
        * eapply Permutation_middle.
        * apply Permutation_app.
          -- rewrite <- split_on_invalid_id; try tauto.
             apply Permutation_refl.
          -- apply IHt2; try solve_branch_trivial.
    - unfold is_valid_id in *. simpl in H. destruct H as [H | H]; try contradiction.
      rewrite H. rewrite Nat.eqb_refl.
      simpl.
      constructor.
  Qed.

  Lemma split_valid_ids: forall t i i',
      ~ is_valid_id t i' ->
      is_valid_tree_ids t ->
      is_valid_tree_ids (split_in_tree i i' t).
  Proof.
    intros t; induction t; intros i i' Hin Hids; simpl in *.
    - assumption.
    - unfold is_valid_tree_ids in *; simpl in *.
      auto.
    - unfold is_valid_tree_ids. simpl.
      destruct (contains_id (Branch t1 t2) i) eqn:I.
      + rewrite contains_valid_id in I.
        branch_valid_xor; eapply Permutation_NoDup.
        * eapply Permutation_app_tail.
          eapply split_ids; try solve_branch_trivial.
        * rewrite <- app_comm_cons.
          rewrite <- split_on_invalid_id with (t:=t2) in *; try tauto.
          apply NoDup_cons; auto.
        * eapply Permutation_app_head.
          eapply split_ids; try solve_branch_trivial.
        * rewrite <- split_on_invalid_id with (t:=t1) in *; try tauto.
          apply ListHelpers.NoDup_app_add;
            unfold is_valid_id in *; simpl in *;
            rewrite in_app_iff in *; tauto.
      + apply Bool.orb_false_iff in I.
        repeat rewrite not_contains_valid_id in I.
        repeat rewrite <- split_on_invalid_id; try tauto.
    - destruct (id =? i).
      unfold is_valid_tree_ids in *; simpl in *.
      + unfold not in Hin.
        destruct (i' =? id) eqn:I. 
        * apply Nat.eqb_eq in I. rewrite I in *.
          unfold is_valid_id in *; simpl in *.
          tauto.
        * apply Nat.eqb_neq in I.
          apply ListHelpers.NoDup_two.
          auto.
      + assumption.
  Qed.
  
  Lemma split_valid_data: forall t p i i',
      is_valid_tree_data t p ->
      is_valid_tree_data (split_in_tree i i' t) p.
  Proof.
    intros t; induction t; intros param i i' H; simpl in *.
    - tauto.
    - destruct H as [Hd Hc].
      split; auto.
    - destruct H as [H1 H2].
      destruct (contains_id t1 i);
        split;
        auto.
    - destruct (id =? i); simpl; tauto.
  Qed.

  Lemma split_valid_new_id: forall t i i',
      is_valid_id t i ->
      is_valid_id (split_in_tree i i' t) i'.
  Proof.
    unfold is_valid_id.
    intros t; induction t; intros i i' H; simpl in *.
    - contradiction.
    - unfold is_valid_id in *. simpl in *. auto.
    - apply in_app_iff in H. apply in_app_iff.
      destruct H as [H1 | H2];
        [ left; apply IHt1 | right; apply IHt2];
        assumption.
    - destruct H as [H | H]; try contradiction. rewrite H.
      rewrite Nat.eqb_refl.
      simpl.
      right. left.
      reflexivity.
  Qed.

  (* the output state of split is valid, and the new id is valid on that tree *)
  Theorem split_valid : forall t p id,
      is_valid_state (t, p) ->
      let (s', j) := split id (t, p) in
      is_valid_state s'.
  Proof.
    intros.
    unfold is_valid_state in *.
    destruct H as [Hs [Hids Hd]].
    repeat split.
    - apply split_valid_structure.
      assumption.
    - apply split_valid_ids.
      + simpl.
        apply greater_than_max_is_invalid_id.
        lia.
      + assumption.
    - apply split_valid_data;
        assumption.
  Qed.

  Theorem split_valid_id : forall t p id,
      is_valid_state (t, p) ->
      is_valid_id t id ->
      let (s', j) := split id (t, p) in
      is_valid_id (tree s') j.
  Proof.
    intros.
    unfold is_valid_state in *.
    destruct H as [Hs [Hids Hd]].
    apply split_valid_new_id.
    assumption.   
  Qed.

  Lemma split_param_unchanged : forall s id,
      let (s', j) := split id s in
      param s = param s'.
  Proof. reflexivity. Qed.

  (*** Split: get on resulting state *)

  Lemma split_get_unchanged_in_tree: forall t p i i' j o,
      i' <> j ->
      let t' := split_in_tree i i' t in
      get_compressed_data_in_tree j t' p o = get_compressed_data_in_tree j t p o.
  Proof.
    intros t. induction t; intros param i i' j o H; simpl in *.
    - reflexivity.
    - destruct o; simpl; auto.
    - rewrite IHt1 by assumption.
      rewrite IHt2 by assumption.
      reflexivity.
    - destruct (id =? i) eqn:I; simpl.
      + destruct (id =? j).
        * destruct o; auto.
          destruct (i' =? j); reflexivity.
        * apply Nat.eqb_neq in H.
          rewrite H.
          reflexivity.
      + destruct (id =? j); auto.
  Qed.

  (* i does not need to be valid, because the tree is unchanged if it is not *)
  Lemma split_get_new_leaf: forall t p i i' o,
      ~ is_valid_id t i' ->
      is_valid_tree_ids t ->
      is_valid_tree_structure t ->
      let t' := split_in_tree i i' t in
      get_compressed_data_in_tree i' t' p o = get_compressed_data_in_tree i t p o.
  Proof.
    intros t. induction t; intros param i i' o H Hids Hs; simpl in *.
    - reflexivity.
    - destruct o; simpl;
        apply IHt; solve_node_trivial.
    - rewrite IHt1; try solve_branch_trivial.
      rewrite IHt2; try solve_branch_trivial.
    - destruct (id =? i) eqn:I; simpl.
      + destruct (id =? i'); simpl.
        * destruct o; simpl.
          -- reflexivity.
          -- rewrite Nat.eqb_refl.
             reflexivity.
        * rewrite Nat.eqb_refl.
          reflexivity.
      + unfold is_valid_id in *. simpl in *.
        destruct (id =? i') eqn:I'; auto.
        apply Nat.eqb_eq in I'; try lia.
  Qed.

  (* when splitting a leaf i, the resulting new leaves have the same compressed data as i *)
  Theorem split_get_new_leaves : forall t p i o,
      is_valid_state (t, p) ->
      get_compressed_data i (t, p) = o ->
      let (s', j) := split i (t, p) in
      get_compressed_data i s' = o /\ get_compressed_data j s' = o.
  Proof.
    intros.
    unfold is_valid_state in H.
    simpl.
    unfold get_compressed_data in *. simpl in *.
    split.
    - destruct (contains_id t0 i) eqn:I; simpl.
      + rewrite split_get_unchanged_in_tree.
        * assumption.
        * apply contains_valid_id in I.
          apply valid_id_is_leq_max in I.
          lia.
      + apply not_contains_valid_id in I.
        rewrite <- split_on_invalid_id with (t:=t0); auto.
    - rewrite split_get_new_leaf.
      + assumption.
      + apply greater_than_max_is_invalid_id.
        lia.
      + tauto.
      + tauto.
  Qed.

  (* when splitting leaf i, all other leaves have unchanged data *)
  (* if i is invalid, the tree does not change and the property still holds *)
  Theorem split_get_unchanged: forall t p i j o,
      is_valid_state (t, p) ->
      let (s', k) := split i (t, p) in
      k <> j ->
      get_compressed_data j (t, p) = o ->
      get_compressed_data j s' = o.
  Proof.
    simpl.
    intros.
    unfold get_compressed_data in *. simpl in *.
    destruct (contains_id t0 i) eqn:I; simpl.
    - rewrite split_get_unchanged_in_tree.
      + assumption.
      + apply contains_valid_id in I.
        apply valid_id_is_leq_max in I.
        lia.
    - apply not_contains_valid_id in I.
      rewrite <- split_on_invalid_id with (t:=t0); auto.
  Qed.

  (** Delete properties *)

  Lemma delete_on_invalid_id : forall t id p,
      is_valid_tree_structure t ->
      ~ is_valid_id t id ->
      delete_in_tree id t p = t.
  Proof.
    intros t id param; induction t; intros Hs H; simpl in *; auto.
    - rewrite IHt; auto;
        destruct t0; simpl in *; try contradiction; congruence.
    - repeat rewrite is_stem_with_invalid_id; try solve_branch_trivial.
      rewrite IHt1; try rewrite IHt2; try tauto;
        try solve_branch_trivial.
    - unfold is_valid_id in *. simpl in *.
      destruct (_ =? _) eqn:I; try reflexivity.
      apply Nat.eqb_eq in I. lia.
  Qed.

  Lemma delete_is_stump : forall t id p,
      is_valid_tree_structure t ->
      delete_in_tree id t p = Stump ->
      t = Stump \/ t = Leaf id \/ (exists d, t = Node d (Leaf id)).
  Proof.
    intros t i param; induction t; intros Hs H; simpl in *.
    - left. reflexivity.
    - right. right.
      exists data.
      destruct (delete_in_tree i t0 param) eqn:D; try congruence.
      destruct t0 eqn:T0; try contradiction; specialize (IHt Hs H);
        destruct IHt as [k | [k | [d k]]]; try congruence.
    - destruct (is_stem_with_id i t1) eqn:B1; simpl in *.
      + subst.
        destruct t1; contradiction.
      + destruct (is_stem_with_id i t2) eqn:B2; simpl in *.
        * subst. contradiction.
        * congruence.
    - right. left.
      destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I. congruence.
      + congruence.
  Qed.

  Lemma delete_is_not_Stump : forall t p id,
      is_valid_tree_structure t ->
      t <> Stump ->
      is_stem_with_id id t = false ->
      delete_in_tree id t p <> Stump.
  Proof.
    intros t param i Hs Ht Hi.
    destruct t; simpl in *; try congruence.
    - destruct (delete_in_tree i t0 param) eqn:D; try congruence.
      apply delete_is_stump in D.
      + destruct D as [D | [D | [d D]]]; rewrite D in Hs, Hi; simpl in *;
          try contradiction;
          try rewrite Nat.eqb_refl in *;
          try congruence.
      + try solve_node_trivial.
    - destruct_stems;
        try congruence;
        destruct t1, t2; try contradiction; congruence.
    - rewrite Hi.
      congruence.
  Qed.

  Lemma delete_is_leaf : forall t p i j,
      is_valid_tree_structure t ->
      delete_in_tree i t p = Leaf j ->
      (t = Leaf j /\ i <> j) \/
        (exists l r, t = Branch l r /\
                       (is_stem_with_id i l = true /\ r = Leaf j \/
                          is_stem_with_id i r = true /\ l = Leaf j)).
  Proof.
    intros t param i j; induction t; intros Hs H; simpl in *; try congruence.
    - destruct (delete_in_tree i t0 param); congruence.
    - right.
      exists t1, t2.
      split; try reflexivity.
      destruct (is_stem_with_id i t1) eqn:B1.
      + left. split; congruence.
      + destruct (is_stem_with_id i t2) eqn:B2.
        * right. split; congruence.
        * congruence.          
    - left.
      destruct (id =? i) eqn:I.
      + apply Nat.eqb_eq in I. congruence.
      + apply Nat.eqb_neq in I.
        split; try assumption.
        injection H as H.
        lia.
  Qed.

  (*** Delete: validity of resulting state *)

  Lemma delete_ids : forall t p id,
      incl (get_all_ids (delete_in_tree id t p)) (get_all_ids t).
  Proof.
    intros t param i; induction t; simpl in *.
    - apply incl_refl.
    - destruct (delete_in_tree i t0 param) eqn:D; auto.
    - destruct (is_stem_with_id i t1); simpl.
      + apply incl_appr.
        apply incl_refl.
      + destruct (is_stem_with_id i t2); simpl.
        * apply incl_appl.
          apply incl_refl.
        * apply incl_app_app; auto.
    - destruct (id =? i); simpl.
      + apply incl_nil_l.
      + apply incl_refl.
  Qed.

  Lemma delete_ids_perm_in_tree : forall t p id,
      is_valid_id t id ->
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      Permutation (get_all_ids t) (id :: (get_all_ids (delete_in_tree id t p))).
  Proof.
    unfold is_valid_id, is_valid_tree_ids.
    intros t param i; induction t; intros Hid Hs Hids; simpl in *.
    - contradiction.
    - destruct (delete_in_tree i t0 param) eqn:D.
      destruct t0; try solve_node_trivial.
      all: simpl in *; apply IHt; try solve_node_trivial.
    - specialize (branch_id_valid_in_one _ _ i Hids) as XOR.
      destruct (is_stem_with_id i t1) eqn:S1; simpl.
      + apply get_all_ids_stem_with_id in S1.
        rewrite S1.
        simpl.
        apply Permutation_refl.
      + destruct (is_stem_with_id i t2) eqn:S2; simpl.
        * apply get_all_ids_stem_with_id in S2.
          rewrite S2.
          eapply perm_trans.
          apply Permutation_sym; apply Permutation_cons_append.
          apply Permutation_refl.
        * apply ListHelpers.NoDup_app_remove in Hids.
          specialize (in_app_or _ _ _ Hid) as H.
          destruct H as [H | H].
          -- rewrite delete_on_invalid_id with (t:= t2); try solve_branch_trivial.
             rewrite app_comm_cons.
             apply Permutation_app_tail.
             apply IHt1; try solve_branch_trivial.
          -- rewrite delete_on_invalid_id with (t:= t1); try solve_branch_trivial.
             eapply perm_trans.
             2: apply Permutation_sym; apply Permutation_middle.
             apply Permutation_app_head.
             apply IHt2; try solve_branch_trivial.
    - destruct Hid as [Hid|]; try contradiction.
      subst.
      rewrite Nat.eqb_refl.
      simpl.
      apply Permutation_refl.
  Qed.

  Lemma delete_ids_perm : forall s id,
      is_valid_id (tree s) id ->
      is_valid_state s ->
      Permutation (get_all_ids (tree s)) (id :: (get_all_ids (tree (delete id s)))).
  Proof.
    intros s id Hid [Hs [Hids Hd]].
    apply delete_ids_perm_in_tree; auto.
  Qed.
        
  Lemma delete_valid_ids : forall t p id,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_tree_ids (delete_in_tree id t p).
  Proof.
    intros t param i; induction t; intros Hs Hids; simpl in *.
    - constructor.
    - destruct (delete_in_tree i t0 param) eqn:D; simpl in *.
      + constructor.
      + apply IHt; solve_node_trivial.
      + apply IHt; solve_branch_trivial.
      + apply ListHelpers.NoDup_one.
    - destruct_stems.
      + eapply NoDup_app_remove_l. eauto.
      + eapply NoDup_app_remove_r. eauto.
      + unfold is_valid_tree_ids. simpl.
        apply NoDup_app.
        * apply IHt1; try solve_branch_trivial.
        * apply IHt2; try solve_branch_trivial.
        * intros a Ha1 Ha2.
          specialize (delete_ids t1 param i) as Dids1.
          specialize (delete_ids t2 param i) as Dids2.
          specialize (ListHelpers.in_subset _ _ _ Dids1 Ha1) as I1.
          specialize (ListHelpers.in_subset _ _ _ Dids2 Ha2) as I2.
          assert (Bid: is_valid_id (Branch t1 t2) a) by
            (unfold is_valid_id in *; simpl; apply in_app_iff; tauto).
          specialize (branch_id_valid_in_one _ _ a Hids) as XOR.
          tauto.
    - destruct (id =? i); simpl.
      + constructor.
      + apply ListHelpers.NoDup_one.
  Qed.
  
  Lemma delete_valid_data : forall t p id,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_tree_data t p ->
      is_valid_tree_data (delete_in_tree id t p) p.
  Proof.
    intros t param i; induction t; intros Hs Hids H; simpl in *; auto.
    - destruct (delete_in_tree i t0 param) eqn:D; simpl in *;
        try tauto;
        split;
        try apply Data.compress_valid;
        try apply IHt; solve_branch_trivial.
    - destruct_stems; try tauto.
      split;
        [apply IHt1 | apply IHt2];
        solve_branch_trivial.
    - destruct (id =? i); simpl; auto.
  Qed.

  Lemma delete_valid_structure : forall t p id,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_tree_structure (delete_in_tree id t p).
  Proof.
    intros t param i; induction t; intros Hs Hids; simpl in *; auto.
    - destruct (delete_in_tree i t0 param) eqn:D; simpl in *;
        apply IHt; solve_node_trivial.
    - destruct_stems; try solve_branch_trivial.
      apply branch_of_children_with_valid_structure.
      1, 2: apply delete_is_not_Stump; try solve_branch_trivial.
      + apply IHt1; solve_branch_trivial.
      + apply IHt2; solve_branch_trivial.
    - destruct (id =? i); auto.
  Qed.

  (* the output of delete is valid*)
  Theorem delete_valid : forall t p id,
    is_valid_state (t, p) ->
    let s' := delete id (t, p) in
    is_valid_state s'.
  Proof.
    intros t p id H.
    unfold is_valid_state, delete in *. simpl in *.
    repeat split.
    - apply delete_valid_structure; tauto.
    - apply delete_valid_ids; tauto.
    - apply delete_valid_data; tauto.
  Qed.

  Lemma delete_param_unchanged : forall s id,
      param s = param (delete id s).
  Proof. reflexivity. Qed.

  Lemma delete_invalid_id_tree : forall t p id,
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      ~ is_valid_id (delete_in_tree id t p) id.
  Proof.
    intros t param i; induction t; intros Hs Hids;
      unfold is_valid_tree_ids in *; simpl in *.
    - tauto.
    - destruct (delete_in_tree i t0 param) eqn:D; simpl in *; try tauto.
      all: apply IHt; try solve_node_trivial.
    - specialize (branch_id_valid_in_one _ _ i Hids) as XOR.
      destruct_stems;
        unfold is_valid_id in *; simpl in *.
      + apply get_all_ids_stem_with_id in B1.
        assert (I: In i (get_all_ids t1)) by (rewrite B1; simpl; auto).
        pose proof or_introl as OIL. specialize (OIL _ (is_valid_id t2 i) I).
        tauto.
      + apply get_all_ids_stem_with_id in B2.
        assert (I: In i (get_all_ids t2)) by (rewrite B2; simpl; auto).
        pose proof or_intror as OIR. specialize (OIR (is_valid_id t1 i) _ I).
        tauto.
      + rewrite in_app_iff.
        apply ListHelpers.NoDup_app_remove in Hids.
        assert (H1: ~ In i (get_all_ids (delete_in_tree i t1 param))) by
          (apply IHt1; solve_branch_trivial).
        assert (H2: ~ In i (get_all_ids (delete_in_tree i t2 param))) by
          (apply IHt2; solve_branch_trivial).
        tauto.
    - unfold is_valid_id in *.
      destruct (id =? i) eqn:I; simpl in *; try tauto.
      apply Nat.eqb_neq in I.
      lia.
  Qed.

  Theorem delete_invalid_id : forall t p id,
    is_valid_state (t, p) ->
    let s' := delete id (t, p) in
    ~ is_valid_id (tree s') id.
  Proof.
    intros t p i [Hs [Hids Hd]].
    unfold delete. simpl.
    apply delete_invalid_id_tree; auto.
  Qed.

  (*** Delete: get on resulting state *)

  Theorem delete_get_on_deleted : forall t p i,
      is_valid_state (t, p) ->
      let s' := delete i (t, p) in
      get_compressed_data i s' = None.
  Proof.
    intros t p i H.
    unfold delete. simpl.
    unfold get_compressed_data. simpl.
    destruct (is_stump (delete_in_tree i t p)) eqn:S.
    - apply is_Stump in S.
      rewrite S. simpl.
      reflexivity.
    - apply get_on_invalid_id_in_tree.
      + apply is_not_Stump.
        assumption.
      + apply delete_valid with (id:=i) in H.
        unfold delete, is_valid_state in H.
        tauto.
      + apply delete_invalid_id.
        assumption.
  Qed.

  Lemma delete_is_stump_but_not_stem_with_id : forall t p i,
      is_valid_tree_structure t ->
      is_stem_with_id i t = false ->
      delete_in_tree i t p = Stump ->
      t = Stump.
  Proof.
    intros t p i Hs Hb H.
    apply delete_is_stump in H; auto.
    destruct H as [H | [H | [d H]]]; rewrite H in *; simpl in *;
      try rewrite Nat.eqb_refl in *; congruence.
  Qed.

  Lemma delete_unchanged_in_tree : forall t p i j o o',
      is_valid_tree_structure t ->
      is_valid_tree_ids t ->
      is_valid_tree_data t p ->
      i <> j ->
      (forall d, o' = Some d -> Data.is_valid p d) ->
      get_compressed_data_in_tree j t p o' = o ->
      get_compressed_data_in_tree j (delete_in_tree i t p) p o' = o \/
        (delete_in_tree i t p = Stump).
  Proof.
    intros t param i j; induction t; intros o o' Hs Hids Hdata Hij Ho H;
      unfold is_valid_tree_ids in *; simpl in *; auto.
    - destruct (delete_in_tree i t0 param) eqn:D; simpl in *.
      1: right. reflexivity.
      1, 2: pose (o'' := match o' with
                         | Some a => Some (compress param a data)
                         | None => Some data
                         end);
      destruct Hdata as [Hdata Htdata];
      assert (Hs0: is_valid_tree_structure t0) by (solve_node_trivial);
      assert (Hd: (forall d, o'' = Some d -> is_valid param d))
        by (intros d Hd;
            destruct o' eqn:O'; injection Hd as Hd; subst; auto;
            apply Data.compress_valid; auto);
      specialize (IHt o o'' Hs0 Hids Htdata Hij Hd H);
      destruct IHt as [IHt | IHt]; try congruence.
      + left.
        destruct o'; auto.
        rewrite Data.compress_assoc; auto.
        assert (DATA: is_valid_tree_data (delete_in_tree i t0 param) param)
          by (apply delete_valid_data; try solve_node_trivial).
        rewrite D in DATA. simpl in DATA.
        tauto.
      + left. auto.
      + left.
        apply delete_is_leaf in D; try solve_node_trivial.
        destruct D as [[D Di] | [l [r [D [[D' D''] | [D' D'']]]]]];
          subst; simpl in *.
        * reflexivity.
        * rewrite get_on_invalid_id_in_tree with (t:=l) (i:=j); try solve_node_trivial.
          apply get_all_ids_stem_with_id in D'.
          unfold is_valid_id. rewrite D'.
          intros C. inversion C; auto.
        * rewrite get_on_invalid_id_in_tree with (t:=r) (i:=j); try solve_node_trivial.
          -- destruct (id =? j); auto.
             destruct o'; auto.
          -- apply get_all_ids_stem_with_id in D'.
             unfold is_valid_id. rewrite D'.
             intros C. inversion C; auto.
    - left.
      destruct_stems; simpl in *.
      + rewrite get_on_invalid_id_in_tree in H; try solve_branch_trivial.
        eapply invalid_id_in_stem_with_id; try solve_branch_trivial; eauto.
      + destruct (get_compressed_data_in_tree j t1 param o') eqn:G1; auto.
        rewrite get_on_invalid_id_in_tree in H; try solve_branch_trivial.
        eapply invalid_id_in_stem_with_id; try solve_branch_trivial; eauto.
      + apply ListHelpers.NoDup_app_remove in Hids.
        destruct (get_compressed_data_in_tree j t1 param o') eqn:G1.
        * assert (H1: get_compressed_data_in_tree j (delete_in_tree i t1 param) param o' = Some t0 \/
                      delete_in_tree i t1 param = Stump)
            by (apply IHt1; try solve_branch_trivial).
          destruct H1 as [H1 | H1].
          -- rewrite H1. auto.
          -- assert (T1: t1 = Stump)
               by (apply delete_is_stump_but_not_stem_with_id with (p:=param) (i:=i);
                   try solve_branch_trivial).
             subst. contradiction.
        * assert (H1: get_compressed_data_in_tree j (delete_in_tree i t1 param) param o' = None \/
                      delete_in_tree i t1 param = Stump)
            by (apply IHt1; try solve_branch_trivial).
          destruct H1 as [H1 | H1].
          -- rewrite H1.
             assert (H2: get_compressed_data_in_tree j (delete_in_tree i t2 param) param o' = o \/
                           delete_in_tree i t2 param = Stump)
               by (apply IHt2; solve_branch_trivial).
             destruct H2 as [H2 | H2]; auto.
             assert (T2: t2 = Stump)
               by (apply delete_is_stump_but_not_stem_with_id with (p:=param) (i:=i);
                   try solve_branch_trivial).
             subst.
             destruct t1; contradiction.
          -- assert (T1: t1 = Stump)
               by (apply delete_is_stump_but_not_stem_with_id with (p:=param) (i:=i);
                   try solve_branch_trivial).
             subst. contradiction.
    - destruct (id =? j) eqn:J; simpl in *.
      + apply Nat.eqb_eq in J. subst.
        apply Nat.eqb_neq in Hij.
        rewrite Nat.eqb_sym in Hij.
        rewrite Hij. simpl.
        rewrite Nat.eqb_refl.
        left.
        reflexivity.
      + destruct (id =? i); simpl.
        * right. reflexivity.
        * left.
          rewrite J.
          assumption.
  Qed.

  Theorem delete_get_unchanged : forall t p i j o,
      is_valid_state (t, p) ->
      i <> j ->
      get_compressed_data j (t, p) = o ->
      let s' := delete i (t, p) in
      get_compressed_data j s' = o.
  Proof.
    intros t param i j o [Hs [Hids Hd]] Hi H.
    unfold delete, get_compressed_data in *. simpl in *.
    pose proof delete_unchanged_in_tree as D.
    assert (O: (forall d : Data.t, None = Some d -> is_valid param d)) by congruence.
    specialize (D _ _ _ _ o None Hs Hids Hd Hi O H).
    destruct D as [D | D].
    - assumption.
    - apply delete_is_stump in D; try assumption.
      destruct D as [D | [D | [d D]]]; subst; simpl.
      + reflexivity.
      + rewrite Nat.eqb_refl. simpl.
        destruct (i =? j); reflexivity.
      + rewrite Nat.eqb_refl. simpl.
        apply Nat.eqb_neq in Hi.
        rewrite Hi.
        reflexivity.
  Qed.

End VT.
