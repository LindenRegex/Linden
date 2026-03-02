From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups Parameters LWParameters.
From Stdlib Require Import PeanoNat.
From Warblre Require Import Typeclasses Parameters Base.

(** * Backtracking trees *)

(* A tree represents all the possible paths that could be explored by a backtracking engine *)
(* Its nodes are made out of actions: manipulating groups, choosing between 2 branches, etc. *)
(* Branches of the tree are ordered by priority: the leftmost branch is the top priority behavior *)

(** * Chaining optional results  *)
(* in the future, maybe use an option monad *)

Definition seqop {X:Type} (o1 o2: option X) : option X :=
  match o1 with Some o => o1 | None => o2 end.

Lemma seqop_none:
  forall X (o1:option X), seqop o1 None = o1.
Proof. intros X o1. destruct o1 eqn:O; auto. Qed.

Definition seqop_list {X Y:Type} (l:list X) (f: X -> option Y) : option Y :=
  List.fold_left (fun (y:option Y) (x:X) => seqop y (f x)) l None.

Lemma app_cons:
  forall X (h:X) l, h::l = [h] ++ l.
Proof. intros. simpl. auto. Qed.

Lemma seqop_some:
  forall X Y l f r, List.fold_left (fun (y:option Y) (x:X) => seqop y (f x)) l (Some r) = Some r.
Proof. intros X Y l. induction l; intros; simpl; auto. Qed.

Lemma seqop_list_head_some:
  forall X Y (h:X) l f (r:Y),
    f h = Some r ->
    seqop_list (h::l) f = Some r.
Proof.
  intros X Y h l f r H. unfold seqop_list.
  simpl. rewrite H.
  rewrite seqop_some. auto.
Qed.

Lemma seqop_list_head_none:
  forall X Y (h:X) l (f:X -> option Y),
    f h = None ->
    seqop_list (h::l) f = seqop_list l f.
Proof. intros. unfold seqop_list. simpl. rewrite H. auto. Qed.

Lemma seqop_assoc:
  forall X (o1 o2 o3:option X),
    seqop o1 (seqop o2 o3) = seqop (seqop o1 o2) o3.
Proof. intros. unfold seqop. destruct o1; destruct o2; auto. Qed.

Definition option_flat_map {A B: Type} (f: A -> option B) (o: option A) : option B :=
  match o with
  | Some a => f a
  | None => None
  end.

(** * Backtracking trees  *)


Section Tree.
  Context {params: LindenParameters}.

  Inductive tree : Type :=
  | Mismatch
  | Match
  | Choice (t1 t2:tree)
  | Read (c:Character) (t:tree)
  | ReadBackRef (str: string) (t:tree)
  | Progress (t:tree)
  | AnchorPass (a: anchor) (t: tree)
  | GroupAction (g:groupaction) (t: tree)
  | LK (lk: lookaround) (tlk: tree) (t: tree) (* tlk is the lookaround tree. *)
  | LKFail (lk: lookaround) (tlk: tree)       (* Also records the lookaround tree *)
  .

  Definition tree_eq_dec : forall (t1 t2 : tree), { t1 = t2 } + { t1 <> t2 }.
  Proof.
    decide equality; try solve[repeat decide equality].
    - apply Character.eq_dec.
    - apply string_eq_dec.
  Qed.

  Definition tree_eqb (t1 t2:tree) : bool :=
  match tree_eq_dec t1 t2 with | left _ => true | _ => false end.

  (** ** Maximum group ID of a tree *)
  (* Maximum group ID of a list of group IDs *)
  Fixpoint max_gid_list (gl: list group_id) :=
    match gl with
    | [] => 0
    | gid::q => max gid (max_gid_list q)
    end.

  (* Maximum group ID of a groupaction *)
  Definition max_gid_groupaction (act: groupaction) :=
    match act with
    | Open gid => gid
    | Close gid => gid
    | Reset gl => max_gid_list gl
    end.

  (* Maximum group ID of a tree *)
  Fixpoint max_gid_tree (t: tree) :=
    match t with
    | Mismatch | Match => 0
    | Choice t1 t2 => max (max_gid_tree t1) (max_gid_tree t2)
    | Read _ t | ReadBackRef _ t | Progress t | AnchorPass _ t => max_gid_tree t
    | GroupAction act t => max (max_gid_groupaction act) (max_gid_tree t)
    | LK _ tlk t => max (max_gid_tree tlk) (max_gid_tree t)
    | LKFail _ tlk => max_gid_tree tlk
    end.


  (** * Greedy and Lazy Choice *)

  (* a choice operator which depends on the greediness of some quantifier *)
  Definition greedy_choice (greedy:bool) (t1 t2:tree) :=
    if greedy
    then Choice t1 t2
    else Choice t2 t1.

  (** * Tree Results  *)

  Definition leaf: Type := (input * group_map).

  Definition advance_idx (idx: nat) (dir: Direction) :=
    match dir with
    | forward => idx+1
    | backward => idx-1
    end.

  Definition advance_idx_n (idx: nat) (n: nat) (dir: Direction) :=
    match dir with
    | forward => idx + n
    | backward => idx - n
    end.

  (* returning the highest-priority result *)
  (* we also return the corresponding group map *)
  Fixpoint tree_res (t:tree) (gm:group_map) (inp:input) (dir: Direction): option leaf :=
    match t with
    | Mismatch => None
    | Match => Some (inp, gm)
    | Choice t1 t2 =>
        seqop (tree_res t1 gm inp dir) (tree_res t2 gm inp dir)
    | Read c t1 => tree_res t1 gm (advance_input' inp dir) dir
    | Progress t1 => tree_res t1 gm inp dir
    | GroupAction a t1 => tree_res t1 (GroupMap.update (idx inp) a gm) inp dir
    | LK lk tlk t1 =>
        match (positivity lk) with
        | true =>
            match tree_res tlk gm inp (lk_dir lk) with
            | None => None
            (* using the captures defined in the first branch of the lookahead *)
            | Some (_, gm') => tree_res t1 gm' inp dir
            end
        | false =>
            match tree_res tlk gm inp (lk_dir lk) with
            (* using previous captures *)
            | None => tree_res t1 gm inp dir
            | Some _ => None
            end
        end
    | LKFail _ _ => None
    | AnchorPass _ t => tree_res t gm inp dir
    | ReadBackRef br_str t => tree_res t gm (advance_input_n inp (length br_str) dir) dir
    end.

  (* initializing on a the empty group map *)
  Definition first_branch (t:tree) (str0: string) : option leaf :=
    tree_res t GroupMap.empty (init_input str0) forward.

  Definition first_leaf (t:tree) (inp:input) : option leaf :=
    tree_res t GroupMap.empty inp forward.

  (** * All Tree Results *)

  (* returns the ordered list of all results of a tree *)
  (* together with the corresponding group map *)
  Fixpoint tree_leaves (t:tree) (gm:group_map) (inp:input) (dir: Direction): list leaf :=
    match t with
    | Mismatch => []
    | Match => [(inp, gm)]
    | Choice t1 t2 =>
        tree_leaves t1 gm inp dir ++ tree_leaves t2 gm inp dir
    | Read c t1 => tree_leaves t1 gm (advance_input' inp dir) dir
    | Progress t1 => tree_leaves t1 gm inp dir
    | GroupAction a t1 => tree_leaves t1 (GroupMap.update (idx inp) a gm) inp dir
    | LK lk tlk t1 =>
        match (positivity lk) with (* Do we want to explore all the branches of the lookahead tree that succeed? *)
        | true =>
            match (tree_leaves tlk gm inp (lk_dir lk)) with
            | [] => []             (* should not happen *)
            (* using the captures defined in the first branch of the lookaround *)
            | (_, gm')::_ => tree_leaves t1 gm' inp dir
            end
        | false =>
            match (tree_leaves tlk gm inp (lk_dir lk)) with
            (* using previous captures *)
            | [] => tree_leaves t1 gm inp dir
            | _ => []              (* should not happen *)
            end
        end
    | LKFail _ _ => []
    | AnchorPass _ t => tree_leaves t gm inp dir
    | ReadBackRef br_str t => tree_leaves t gm (advance_input_n inp (length br_str) dir) dir
    end.


  (* Property that this definition coincides on the first element with the previous definition given a tree. *)
  Definition first_tree_leaf_prop (t: tree): Prop :=
    forall gm idx dir, tree_res t gm idx dir = hd_error (tree_leaves t gm idx dir).


  (* intermediate lemma about hd_error *)
  Lemma hd_error_app:
    forall A (l1 l2:list A),
      hd_error (l1 ++ l2) =
        match (hd_error l1) with
        | Some h => Some h
        | None => hd_error l2
        end.
  Proof.
    intros A l1 l2. induction l1; simpl; auto.
  Qed.

  (* Intermediate lemma for positive lookarounds *)
  Lemma first_tree_leaf_poslk:
    forall lk tlk t1,
      positivity lk = true -> first_tree_leaf_prop tlk -> first_tree_leaf_prop t1 ->
      first_tree_leaf_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hpos IHtlk IHt1.
    unfold first_tree_leaf_prop in *. intros gm idx dir. simpl. rewrite Hpos.
    specialize (IHtlk gm idx (lk_dir lk)). destruct (tree_res tlk gm idx (lk_dir lk)); destruct (tree_leaves tlk gm idx (lk_dir lk)); try discriminate; simpl in *. 2: reflexivity.
    injection IHtlk as <-; destruct l; auto.
  Qed.

  (* Intermediate lemma for negative lookarounds *)
  Lemma first_tree_leaf_neglk:
    forall lk tlk t1,
      positivity lk = false -> first_tree_leaf_prop tlk -> first_tree_leaf_prop t1 ->
      first_tree_leaf_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hpos IHtlk IHt1.
    unfold first_tree_leaf_prop in *. intros gm idx dir. simpl. rewrite Hpos.
    specialize (IHtlk gm idx (lk_dir lk)). destruct (tree_res tlk gm idx); destruct (tree_leaves tlk gm idx); try discriminate; auto.
  Qed.


  (* this definition coincides on the first element with the previous definition *)
  Theorem first_tree_leaf:
    forall t gm idx dir,
      tree_res t gm idx dir = hd_error (tree_leaves t gm idx dir).
  Proof.
    intros t. induction t; intros; try solve [simpl; auto].
    - simpl. rewrite IHt1. rewrite IHt2. rewrite hd_error_app. unfold seqop.
      destruct (hd_error (tree_leaves t1 gm idx dir)) eqn:HD; auto.
    - destruct (positivity lk) eqn:Hlkpos. + now apply first_tree_leaf_poslk. + now apply first_tree_leaf_neglk.
  Qed.

  (** * Group Map irrelevance  *)
  (* finding a match does not depend on the initial group map *)
  (* we could phrase a stronger theorem about how to relate the two results *)
  (* but for now we only need to differentiate when there is no results from when there is one *)

  (* Group map irrelevance property for a given tree. *)
  Definition leaves_group_map_indep_prop (t: tree): Prop :=
    forall gm1 gm2 inp1 inp2 dir1 dir2,
      tree_leaves t gm1 inp1 dir1 = [] -> tree_leaves t gm2 inp2 dir2 = [].

  (* Intermediate lemma for positive lookarounds *)
  Lemma leaves_group_map_indep_poslk:
    forall lk tlk t1,
      positivity lk = true -> leaves_group_map_indep_prop tlk -> leaves_group_map_indep_prop t1 ->
      leaves_group_map_indep_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hposlk IHtlk IHt1; unfold leaves_group_map_indep_prop in *; simpl.
    rewrite Hposlk. intros gm1 gm2 inp1 inp2 dir1 dir2 Hnil1.
    specialize (IHtlk gm1 gm2 inp1 inp2 (lk_dir lk) (lk_dir lk)). destruct (tree_leaves tlk gm1 inp1 _) as [|[inp' gm'] q]; simpl in *.
    1: { specialize (IHtlk eq_refl). now rewrite IHtlk. }
    destruct (tree_leaves tlk gm2 inp2 _) as [|[inp'0 gm'0] q0]; simpl in *. 1: reflexivity.
    eapply IHt1; eauto.
  Qed.

  (* Intermediate lemma for negative lookarounds *)
  Lemma leaves_group_map_indep_neglk:
    forall lk tlk t1,
      positivity lk = false -> leaves_group_map_indep_prop tlk -> leaves_group_map_indep_prop t1 ->
      leaves_group_map_indep_prop (LK lk tlk t1).
  Proof.
    intros lk tlk t1 Hposlk IHtlk IHt1; unfold leaves_group_map_indep_prop in *; simpl.
    rewrite Hposlk. intros gm1 gm2 inp1 inp2 dir1 dir2 Hnil1.
    destruct (tree_leaves tlk gm1 inp1 _) as [|[inp' gm'] q] eqn:Hnilsub1; simpl in *.
    1: { specialize (IHtlk gm1 gm2 inp1 inp2 (lk_dir lk) (lk_dir lk) Hnilsub1). rewrite IHtlk. eapply IHt1; eauto. }
    destruct (tree_leaves tlk gm2 inp2 _) as [|[inp'0 gm'0] q0] eqn:Hnilsub2; simpl in *. 2: reflexivity.
    exfalso. apply IHtlk with (gm2 := gm1) (inp2 := inp1) (dir2 := lk_dir lk) in Hnilsub2. congruence.
  Qed.


  Lemma leaves_group_map_indep:
    forall t gm1 gm2 inp1 inp2 dir1 dir2,
      tree_leaves t gm1 inp1 dir1 = [] -> tree_leaves t gm2 inp2 dir2 = [].
  Proof.
    intros t.
    induction t; intros; eauto.
    - simpl in H. inversion H.
    - simpl in H. simpl. apply app_eq_nil in H as [NIL1 NIL2].
      apply IHt1 with (gm2:=gm2) (inp2:=inp2) (dir2:=dir2) in NIL1. apply IHt2 with (gm2:=gm2) (inp2:=inp2) (dir2:=dir2) in NIL2.
      rewrite NIL1. rewrite NIL2. auto.
    - destruct (positivity lk) eqn:Hlkpos.
      + eapply leaves_group_map_indep_poslk; eauto.
      + eapply leaves_group_map_indep_neglk; eauto.
  Qed.


  (* Corollary: group map irrelevance in terms of tree_res *)
  (* A lemma about hd_error *)
  Lemma hd_error_none_nil {A}:
    forall l: list A, hd_error l = None <-> l = [].
  Proof.
    intro l. split; intro H.
    - destruct l. + reflexivity. + discriminate.
    - subst l. reflexivity.
  Qed.

  Lemma res_group_map_indep:
    forall t gm1 gm2 inp1 inp2 dir1 dir2,
      tree_res t gm1 inp1 dir1 = None -> tree_res t gm2 inp2 dir2 = None.
  Proof.
    intros. rewrite first_tree_leaf, hd_error_none_nil in *. eauto using leaves_group_map_indep.
  Qed.

  Lemma leaf_eq_dec (l1 l2: leaf): {l1 = l2} + {l1 <> l2}.
  Proof.
    decide equality.
    - apply (@EqDec.eq_dec _ Groups.GroupMap.EqDec_t).
    - apply input_eq_dec.
  Defined.

End Tree.
