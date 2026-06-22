
Require Import CData.

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* Arrays *)
Module Array.
  Definition t (A : Type) : Type := list A.

  (* Operations *)

  Definition length {A} (a: t A) : nat := length a.
  Definition In {A} (x: A) (a: t A) : Prop := In x a.

  Fixpoint make {A} (n : nat) (init : A) : t A :=
    match n with
    | 0 => []
    | S n' => init :: make n' init
    end.
  
  Definition get {A} (a : t A) (i : nat) : option A :=
    nth_error a i.

  Fixpoint set {A} (a : t A) (i : nat) (x : A) : t A :=
    match a, i with
    | [], _ => []
    | _ :: xs, 0 => x :: xs
    | y :: xs, S i' => y :: set xs i' x
    end.

  Fixpoint zipWith {A} {B} {C} (a: t A) (b: t B) (f : A -> B -> C) : t C :=
    match a, b with
    | [], _ => []
    | _, [] => []
    | a0 :: a', b0 :: b' => (f a0 b0) :: (zipWith a' b' f)
    end.

  (* Properties *)

  Lemma length_make {A} : forall (n : nat) (x : A),
      length (make n x) = n.
  Proof.
    induction n; intros; simpl; auto.
  Qed.

  Lemma length_set {A} : forall (a : t A) (i : nat) (x : A),
      length (set a i x) = length a.
  Proof.
    induction a; intros i x; simpl.
    - reflexivity.
    - destruct i; simpl; auto.
  Qed.

  Lemma in_make {A} : forall (x: A) (a: A) (size: nat),
      In x (make size a) -> x = a.
  Proof.
    induction size; intros H; simpl in *.
    - contradiction.
    - destruct H; auto.
  Qed.

  Lemma get_make {A} : forall (n : nat) (x : A) (i : nat),
      i < n ->
      get (make n x) i = Some x.
  Proof.
    induction n; intros x i H; simpl in *.
    - lia.
    - destruct i; simpl.
      + reflexivity.
      + apply IHn.
        lia.
  Qed.

  Lemma get_out_of_bounds {A} : forall (a: t A) n,
      get a n = None <-> length a <= n.
  Proof.
    revert A.
    apply nth_error_None.
  Qed.

  Lemma get_in_bounds {A} : forall (a: t A) i,
      i < length a <->
      (exists x, get a i = Some x).
  Proof.
    unfold get.
    split; intros; try destruct H as [h H].
    - apply nth_error_Some in H.
      destruct (nth_error a i) eqn:N; try congruence.
      eexists. eauto.
    - apply nth_error_Some.
      congruence.
  Qed.

  Lemma set_out_of_bounds {A} : forall (a: t A) (i: nat) (x: A),
      i >= length a ->
      set a i x = a.
  Proof.
    induction a; intros; simpl in *.
    - reflexivity.
    - destruct i; simpl in *.
      + lia.
      + rewrite IHa.
        * reflexivity.
        * lia.
  Qed.

  Lemma set_comm {A} : forall (a: t A) (i j: nat) (x y: A),
      i <> j ->
      set (set a i x) j y = set (set a j y) i x.
  Proof.
    induction a; intros; simpl in *; auto.
    destruct i; destruct j; auto.
    - congruence.
    - simpl.
      rewrite IHa; auto.
  Qed.

  Lemma set_overwrite {A} : forall (a: t A) (i: nat) (x y: A),
      set (set a i x) i y = set a i y.
  Proof.
    induction a; intros i x y; simpl in *.
    - reflexivity.
    - destruct i; simpl in *; auto.
      rewrite IHa.
      reflexivity.
  Qed.

  Lemma get_set_eq {A} : forall (a : t A) (i: nat) (x: A),
      i < length a ->
      get (set a i x) i = Some x.
  Proof.
    induction a; intros; simpl in *.
    - lia.
    - destruct i; simpl.
      + reflexivity.
      + apply IHa.
        lia.
  Qed.

  Lemma get_set_neq {A} : forall (a : t A) (i j: nat) (x: A),
      i <> j ->
      get (set a i x) j = get a j.
  Proof.
    induction a; intros; simpl in *.
    - destruct j; simpl; reflexivity.
    - destruct i; destruct j; simpl.
      + lia.
      + reflexivity.
      + reflexivity.
      + apply IHa.
        lia.
  Qed.

  Lemma set_get {A} : forall (a: t A) (i: nat) (x: A),
      get a i = Some x -> set a i x = a.
  Proof.
    induction a; intros i x H; simpl in *; auto.
    destruct i; simpl in *.
    - injection H as H. congruence.
    - rewrite IHa; auto.
  Qed.

  Lemma length_zipWith {A} {B} {C} : forall (a: t A) (b: t B) (f: A -> B -> C),
      length (zipWith a b f) = min (length a) (length b).
  Proof.
    induction a; intros b f; simpl.
    - reflexivity.
    - destruct b eqn:Bl; simpl.
      + reflexivity.
      + rewrite IHa.
        reflexivity.
  Qed.

  Lemma zipWith_assoc {A} : forall (a b c: t A) (f: A -> A -> A),
      (forall x y z, f x (f y z) = f (f x y) z) ->
      zipWith a (zipWith b c f) f = zipWith (zipWith a b f) c f.
  Proof.
    induction a; intros b c f Hf; simpl.
    - reflexivity.
    - destruct b eqn:B; simpl.
      + reflexivity.
      + destruct c eqn:C.
        * reflexivity.
        * rewrite Hf.
          rewrite IHa; auto.
  Qed.

  Lemma zipWith_neutral_r {A} {B} : forall (a: t A) (b: t B) (f: A -> B -> A),
      (forall x y, In y b -> f x y = x) ->
      length a <= length b ->
      zipWith a b f = a.
  Proof.
    induction a; intros b f Hf Hl; simpl.
    - reflexivity.
    - destruct b eqn:V; simpl in *.
      + lia.
      + rewrite IHa.
        * rewrite Hf; auto.
        * auto.
        * lia.
  Qed.

  Lemma zipWith_neutral_l {A} {B} : forall (a: t A) (b: t B) (f: A -> B -> B),
      (forall x y, In x a -> f x y = y) ->
      length a >= length b ->
      zipWith a b f = b.
  Proof.
    induction a; intros b f Hf Hl; simpl.
    - destruct b; simpl in *.
      + reflexivity.
      + lia.
    - destruct b eqn:V; simpl in *.
      + reflexivity.
      + rewrite IHa.
        * rewrite Hf; auto.
        * auto.
        * lia.
  Qed.
  
  Lemma zipWith_set_single {A} {B} {C} :
    forall (a: t A) (b b': t B) (f: A -> B -> C) (i: nat) (x: A) (y: B),
      get a i = Some x ->
      get b i = Some y ->
      length b = length b' ->
      (forall j, j <> i -> get b j = get b' j) ->
      zipWith a b f = set (zipWith a b' f) i (f x y).
  Proof.
    induction a; intros b b' f i x y Ha Hb Hl H; simpl in *; auto.
    destruct b eqn:LB; simpl in *.
    - destruct i; simpl in Hb; congruence.
    - destruct b' eqn:LB'; simpl in *.
      + congruence.
      + destruct i eqn:I; simpl in *.
        * injection Ha as Ha. injection Hb as Hb. subst.
          rewrite nth_error_ext with (l:=t0) (l':=t1); try congruence.
          intros n.
          specialize (H (S n)). simpl in H.
          auto.
        * erewrite <- IHa; eauto.
          -- specialize (H 0). simpl in H.
             injection H as H'; auto.
             congruence.
          -- intros j.
             specialize (H (S j)).
             auto.
  Qed.

  Lemma zipWith_set_l_overwrite_r {A} {B} : forall a b xa xb (f: A -> B -> B) (i: nat),
      get b i = Some xb ->
      (forall x, f x xb = xb) ->
      zipWith (set a i xa) b f = zipWith a b f.
  Proof.
    induction a; intros b xa xb f i Hb Hf; simpl in *.
    - reflexivity.
    - destruct b eqn:LB.
      + destruct i; simpl in *; congruence.
      + destruct i eqn:I; simpl in *.
        * injection Hb as Hb. subst.
          congruence.
        * erewrite IHa; eauto.
  Qed.

  Lemma zipWith_set_l_overwrite_l {A} {B} : forall a b xa xb (f: A -> B -> A) (i: nat),
      get b i = Some xb ->
      (forall x, f x xb = x) ->
      zipWith (set a i xa) b f = set (zipWith a b f) i xa.
  Proof.
    induction a; intros b xa xb f i Hb Hf; simpl in *.
    - reflexivity.
    - destruct b eqn:LB.
      + destruct i; simpl in *; congruence.
      + destruct i eqn:I; simpl in *.
        * injection Hb as Hb. subst.
          congruence.
        * erewrite IHa; eauto.
  Qed.

  Lemma zipWith_set_r_overwrite {A} {B} : forall a b xb (f: A -> B -> B) i,
    (forall x, f x xb = xb) ->
    zipWith a (set b i xb) f = set (zipWith a b f) i xb.
  Proof.
    induction a; intros b xb f i H; simpl in *; auto.
    destruct b eqn:AB; simpl in *; auto.
    destruct i eqn:I; simpl in *; try congruence.
    rewrite IHa; auto.
  Qed.
  
End Array.


(* Regsdata *)
Module RegsData.
  
  (* Definitions *)
  
  Inductive val : Type :=
  | Undefined
  | Invalid
  | Valid (v: nat).
  
  Inductive t' : Type :=
  | Complete (a_cp: Array.t val) (a_clk: Array.t val)
  | Incomplete (l: list (nat * val * val)).

  Definition t := t'.
  Definition p : Set := nat.

  Definition is_valid_index (p: p) (i: nat) : Prop :=
    i < p.

  Definition get_index (e: nat * val * val) : nat :=
    match e with
    | (i, _, _ ) => i
    end.

  Definition is_valid (p: p) (t: t) : Prop :=
    match t with
    | Complete a_cp a_clk =>
        Array.length a_cp = p /\ Array.length a_clk = p
    | Incomplete l =>
        length l < p /\ Forall (fun x => is_valid_index p (get_index x)) l
    end.

  Definition get_most_recent (old new : val) : val :=
    match new with
    | Undefined => old
    | _ => new
    end.
  
  Definition merge_arrays (a_old a_new : Array.t val) : Array.t val :=
    Array.zipWith a_old a_new get_most_recent.

  Fixpoint merge_new_list_old_array (a_old: Array.t val) (l_new: list (nat * val)) : (Array.t val) :=
    match l_new with
    | [] => a_old
    | (i, e) :: l' =>
        (* merge older updates *)
        let a' := merge_new_list_old_array a_old l' in
        (* overwrite older updates *)
        match e with
        | Undefined => a'
        | _ => Array.set a' i e
        end
    end.

  Fixpoint merge_new_array_old_list (l_old: list (nat * val)) (a_new: Array.t val) : (Array.t val) :=
    match l_old with
    | [] => a_new
    | (i, e) :: l' =>
        (* write e only if current value is undefined *)
        let a' :=
          match Array.get a_new i with
          | Some Undefined => Array.set a_new i e
          | _ => a_new
          end in
        (* merge older updates: can only overwrite if the value is undefined *)
        merge_new_array_old_list l' a'
    end.

  Definition list_to_array (size: nat) (l: list (nat * val)) : (Array.t val) :=
    merge_new_list_old_array (Array.make size Undefined) l.

  Definition all_to_cp (x : nat * val * val) : (nat * val) :=
    match x with
    | (i, cp, _) => (i, cp)
    end.

  Definition all_to_clk (x : nat * val * val) : (nat * val) :=
    match x with
    | (i, _, clk) => (i, clk)
    end.

  Definition compress (p: p) (old: t) (new: t): t :=
    match old, new with
    | Complete a_cp1 a_clk1, Complete a_cp2 a_clk2 =>
        Complete (merge_arrays a_cp1 a_cp2) (merge_arrays a_clk1 a_clk2)
    | Complete a_cp1 a_clk1, Incomplete l2 =>
        let a_cp := merge_new_list_old_array a_cp1 (map all_to_cp l2) in
        let a_clk := merge_new_list_old_array a_clk1 (map all_to_clk l2) in
        Complete a_cp a_clk
    | Incomplete l1, Complete a_cp2 a_clk2 =>
        let a_cp := merge_new_array_old_list (map all_to_cp l1) a_cp2 in
        let a_clk := merge_new_array_old_list (map all_to_clk l1) a_clk2 in
        Complete a_cp a_clk
    | Incomplete l1, Incomplete l2 =>
        let l := l2 ++ l1 in
        if Nat.leb p (length l)
        then
          let a_cp := list_to_array p (map all_to_cp l) in
          let a_clk := list_to_array p (map all_to_clk l) in
          Complete a_cp a_clk
        else Incomplete l
    end.

  Fixpoint get_first_such_that {A} {B} (l: list A) (b: B) (f: A -> B -> bool) : option A :=
      match l with
      | [] => None
      | a :: l' => if f a b
                   then Some a
                   else get_first_such_that l' b f
      end.

  Definition has_id (triple: nat * val * val) (i: nat) : bool :=
    match triple with
    | (j, _ , _) => i =? j
    end.
  
  Definition get_at (i: nat) (t: t): (option nat * option nat) :=
    match t with
    | Complete a_cp a_clk =>
        match Array.get a_cp i, Array.get a_clk i with
        | Some (Valid v_cp), Some (Valid v_clk) => (Some v_cp, Some v_clk)
        | Some (Valid v_cp), _ => (Some v_cp, None)
        | _, Some (Valid v_clk) => (None, Some v_clk)
        | _, _ => (None, None) (* i is out-of-bounds, or it's value is undefined or invalid *)
        end
    | Incomplete l =>
        match get_first_such_that l i has_id with
        | Some (j, cp, clk) =>
            match cp, clk with
            | Valid (v_cp), Valid (v_clk) => (Some v_cp, Some v_clk)
            | Valid (v_cp), _ => (Some v_cp, None)
            | _, Valid (v_clk) => (None, Some v_clk)
            | _, _ => (None, None) (* i is in the list, but its value is undefined or invalid *)
            end
        | None => (None, None) (* i is not in the list *)
        end
    end.

  (* Properties *)

  (* Validity *)

  Lemma get_most_recent_assoc : forall x y z,
      get_most_recent x (get_most_recent y z) = get_most_recent (get_most_recent x y) z.
  Proof.
    intros x y z.
    destruct z; destruct y; simpl; reflexivity.
  Qed.
  
  Lemma merge_arrays_length : forall a b,
      Array.length (merge_arrays a b) = min (Array.length a) (Array.length b).
  Proof.
    intros a b.
    unfold merge_arrays.
    apply Array.length_zipWith.
  Qed.

  Lemma merge_new_list_old_array_length : forall l a,
      Array.length a = Array.length (merge_new_list_old_array a l).
  Proof.
    intros l a.
    induction l as [ | [i e] l]; simpl.
    - reflexivity.
    - destruct e eqn:E;
        try rewrite Array.length_set;
        assumption.
  Qed.

  Lemma merge_new_array_old_list_length : forall l a,
      Array.length a = Array.length (merge_new_array_old_list l a).
  Proof.
    intros l.
    induction l as [ | [i e] l]; intros a; simpl.
    - reflexivity.
    - destruct (Array.get a i) eqn:V.
      + destruct v eqn:V'; auto.
        * rewrite <- IHl.
          symmetry.
          apply Array.length_set.
      + apply IHl.
  Qed.

  Lemma list_to_array_length : forall l size,
      Array.length (list_to_array size l) = size.
  Proof.
    intros.
    unfold list_to_array.
    rewrite <- merge_new_list_old_array_length.
    apply Array.length_make.
  Qed.

  Theorem compress_valid : forall x y p,
      is_valid p x ->
      is_valid p y ->
      is_valid p (compress p x y).
  Proof.
    intros x y p Hx Hy.
    destruct x as [cpx clkx | lx]; destruct y as [cpy clky | ly]; simpl in *.
    - destruct Hx as [Hcpx Hclkx]. destruct Hy as [Hcpy Hclky].
      split;
        rewrite merge_arrays_length;
        [rewrite Hcpx, Hcpy | rewrite Hclkx, Hclky];
        lia.
    - repeat rewrite <- merge_new_list_old_array_length.
      assumption.
    - repeat rewrite <- merge_new_array_old_list_length.
      assumption.
    - destruct (p <=? length (ly ++ lx)) eqn:L; simpl.
      + repeat rewrite list_to_array_length; auto.
      + split.
        * apply leb_complete_conv.
          assumption.
        * apply Forall_app.
          destruct Hx as [_ Hx]. destruct Hy as [_ Hy].
          split; assumption.
  Qed.

  (* Equivalence to merging complete forms *)

  Lemma merge_arrays_new_is_Undefined : forall a size,
      size = Array.length a ->
      merge_arrays a (Array.make size Undefined) = a.
  Proof.
    intros a size H.
    unfold merge_arrays.
    apply Array.zipWith_neutral_r.
    - intros x y Hin.
      unfold get_most_recent.
      apply Array.in_make in Hin.
      rewrite Hin.
      reflexivity.
    - rewrite Array.length_make.
      lia.
  Qed.

  Lemma list_to_array_get_valid : forall l size i n,
      i < size ->
      Array.get (list_to_array size ((i, Valid n) :: l)) i = Some (Valid n).
  Proof.
    unfold list_to_array.
    intros; simpl.
    apply Array.get_set_eq.
    rewrite <- merge_new_list_old_array_length.
    rewrite Array.length_make.
    assumption.
  Qed.

  Lemma list_to_array_get_invalid : forall l size i,
      i < size ->
      Array.get (list_to_array size ((i, Invalid) :: l)) i = Some (Invalid).
  Proof.
    unfold list_to_array.
    intros; simpl.
    apply Array.get_set_eq.
    rewrite <- merge_new_list_old_array_length.
    rewrite Array.length_make.
    assumption.
  Qed.

  Lemma list_to_array_get_out_of_bounds : forall l size i r,
      i >= size ->
      Array.get (list_to_array size ((i, r) :: l)) i = Array.get (list_to_array size l) i.
  Proof.
    unfold list_to_array.
    intros; simpl.
    rewrite Array.set_out_of_bounds.
    + destruct r; reflexivity.
    + rewrite <- merge_new_list_old_array_length.
      rewrite Array.length_make.
      assumption.
  Qed.

  Lemma list_to_array_get_undefined : forall l size i,
      i < size ->
      Array.get (list_to_array size ((i, Undefined) :: l)) i = Array.get (list_to_array size l) i.
  Proof.
    unfold list_to_array.
    intros; simpl.
    reflexivity.
  Qed.

  Lemma merge_arrays_from_list_defined: forall a l i r,
      r = Invalid \/ (exists n, r = Valid n) ->
      merge_arrays a (list_to_array (Array.length a) ((i, r) :: l)) =
        Array.set (merge_arrays a (list_to_array (Array.length a) l)) i r.
  Proof.
    unfold merge_arrays.
    intros a l i r H; simpl.
    destruct (Nat.leb (Array.length a) i) eqn:I.
    - (* i is out-of-bounds *)
      apply Nat.leb_le in I.
      unfold list_to_array. simpl.
      repeat rewrite Array.set_out_of_bounds.
      + destruct r; reflexivity.
      + rewrite Array.length_zipWith.
        rewrite <- merge_new_list_old_array_length.
        rewrite Array.length_make.
        lia.
      + rewrite <- merge_new_list_old_array_length.
        rewrite Array.length_make.
        lia.
    - (* i is in bounds *)
      apply Nat.leb_gt in I.
      apply Array.get_in_bounds in I.
      destruct I as [x A].
      erewrite Array.zipWith_set_single
        with (b':= list_to_array (Array.length a) l) (y:= r) (i:= i); eauto.
      + destruct H as [H | [n H]]; rewrite H; auto.
      + destruct H as [H | [n H]]; rewrite H;
          [apply list_to_array_get_invalid | apply list_to_array_get_valid];
          apply Array.get_in_bounds; eauto.
      + unfold list_to_array. simpl.
        destruct H as [H | [n H]]; rewrite H;
          rewrite Array.length_set;
          reflexivity.
      + unfold list_to_array.
        intros j Hij. simpl.
        destruct H as [H | [n H]]; rewrite H;
          apply Array.get_set_neq;
          auto.
  Qed.

  Lemma merge_arrays_from_list_undefined : forall a l i,
      merge_arrays a (list_to_array (Array.length a) ((i, Undefined) :: l)) =
        merge_arrays a (list_to_array (Array.length a) l).
  Proof.
    unfold merge_arrays.
    unfold list_to_array.
    intros a l i; simpl.
    reflexivity.
  Qed.

  Theorem merge_new_list_old_array_equiv : forall l a,
      merge_new_list_old_array a l =
        merge_arrays a (list_to_array (Array.length a) l).
  Proof.
    induction l; intros arr; simpl in *.
    - unfold list_to_array. simpl.
      symmetry.
      apply merge_arrays_new_is_Undefined; auto.
    - destruct a as [i e].
      destruct e eqn:E; rewrite IHl;
        try rewrite merge_arrays_from_list_undefined;
        try erewrite merge_arrays_from_list_defined;
        eauto.
  Qed.

  Lemma merge_arrays_old_is_Undefined : forall a,
      merge_arrays (Array.make (Array.length a) Undefined) a = a.
  Proof.
    intros a.
    unfold merge_arrays.
    apply Array.zipWith_neutral_l.
    - intros x y Hin.
      unfold get_most_recent.
      apply Array.in_make in Hin.
      rewrite Hin.
      destruct y; reflexivity.
    - rewrite Array.length_make.
      lia.
  Qed.

  Lemma merge_new_array_old_list_set_array_defined : forall l a r i,
      r = Invalid \/ (exists x, r = Valid x) ->
      merge_new_array_old_list l (Array.set a i r) =
        Array.set (merge_new_array_old_list l a) i r.
  Proof.
    induction l; intros arr r i H; simpl in *; auto.
    destruct a as [j e].
    destruct (i =? j) eqn:Hij.
    - apply Nat.eqb_eq in Hij. subst.
      destruct (Nat.leb (Array.length arr) j) eqn:J.
      + apply Nat.leb_le in J.
        assert (J': Array.length arr <= j) by (assumption).
        rewrite Array.set_out_of_bounds; auto.
        apply Array.get_out_of_bounds in J.
        rewrite J.
        rewrite Array.set_out_of_bounds; auto.
        rewrite <- merge_new_array_old_list_length.
        lia.
      + apply Nat.leb_gt in J.
        rewrite Array.get_set_eq; auto.
        destruct H as [H | [x H]]; rewrite H;
          destruct (Array.get arr j) eqn:A.
        * destruct v; auto.
          rewrite <- IHl; auto.
          rewrite Array.set_overwrite.
          reflexivity.
        * apply IHl; auto.
        * destruct v; try apply IHl; eauto.
          rewrite <- IHl; eauto.
          rewrite Array.set_overwrite.
          reflexivity.
        * apply IHl; eauto.
    - apply Nat.eqb_neq in Hij.
      rewrite Array.get_set_neq; auto.
      destruct (Array.get arr j) eqn:A;
        try destruct v;
        try rewrite Array.set_comm;
        auto.
  Qed.

  Theorem merge_new_array_old_list_equiv : forall l a,
      merge_new_array_old_list l a =
        merge_arrays (list_to_array (Array.length a) l) a.
  Proof.
    unfold list_to_array.
    induction l; intros arr; simpl in *.
    - symmetry.
      apply merge_arrays_old_is_Undefined.
    - destruct a as [i e].
      destruct (Array.get arr i) eqn:G.
      + unfold merge_arrays in *.
        destruct v eqn:V.
        * (* array has undefined, so list writes *)
          destruct e eqn:E; simpl in *;
            try (rewrite Array.zipWith_set_l_overwrite_l with (xb:=Undefined) (b:= arr); auto);
            rewrite <- IHl.
          1: rewrite Array.set_get; auto. (* Undefined *)
          all: apply merge_new_array_old_list_set_array_defined; eauto. (* Invalid and Valid *)
        * (* array is defined so list cannot overwrite *)
          destruct e eqn:E; simpl in *;
            try rewrite Array.zipWith_set_l_overwrite_r with (xb:= Invalid);
            auto.
        * (* array is defined so list cannot overwrite *)
          destruct e eqn:E; simpl in *;
            try rewrite Array.zipWith_set_l_overwrite_r with (xb:= Valid v0);
            auto.
      + (* i is out of bounds *)
        destruct e eqn:E; simpl in *; auto.
        all: apply Array.get_out_of_bounds in G;
          rewrite Array.set_out_of_bounds; auto;
          rewrite <- merge_new_list_old_array_length;
          rewrite Array.length_make;
          assumption.
  Qed.

  (* Associativity *)
  
  Lemma merge_arrays_assoc : forall x y z,
      merge_arrays x (merge_arrays y z) = merge_arrays (merge_arrays x y) z.
  Proof.
    intros x y z.
    unfold merge_arrays.
    apply Array.zipWith_assoc.
    apply get_most_recent_assoc.
  Qed.

  Lemma list_to_array_app : forall l l' p,
      list_to_array p (l ++ l') = merge_arrays (list_to_array p l') (list_to_array p l).
  Proof.
    induction l; intros l' p;
    unfold list_to_array in *; simpl in *.
    - rewrite merge_arrays_new_is_Undefined; auto.
      rewrite <- merge_new_list_old_array_length.
      rewrite Array.length_make.
      reflexivity.
    - destruct a as [i e].
      destruct e eqn:E; auto.
      all: rewrite IHl;
        unfold merge_arrays;
        symmetry;
        rewrite Array.zipWith_set_r_overwrite;
        auto.
  Qed.

  Theorem compress_assoc : forall x y z p,
      is_valid p x ->
      is_valid p y ->
      is_valid p z ->
      compress p x (compress p y z) = compress p (compress p x y) z.
  Proof.
    intros x y z p Hx Hy Hz.
    destruct x as [cpx clkx | lx], y as [cpy clky | ly], z as [cpz clkz | lz];
      destruct Hx as [Hx Hx']; destruct Hy as [Hy Hy']; destruct Hz as [Hz Hz'];
      repeat match goal with
        | [ |- ?x = ?x] => reflexivity
        | [ H : Array.length ?x = _ |- context[Array.length ?x]] => rewrite H
        | [ |- context[Init.Nat.min ?x ?x]] => rewrite Nat.min_id
        | [ |- context[merge_arrays _ (merge_arrays _ _)]] => rewrite merge_arrays_assoc
        | [ |- context[merge_new_list_old_array _ _]] => rewrite merge_new_list_old_array_equiv
        | [ |- context[merge_new_array_old_list _ _]] => rewrite merge_new_array_old_list_equiv
        | [ |- context[Array.length (merge_arrays _ _)]] => rewrite merge_arrays_length
        | [ |- context[Array.length (list_to_array _ _)]] => rewrite list_to_array_length
        | [ |- context[map _ (_ ++ _)]] => rewrite map_app
        | [ |- context[list_to_array _ (_ ++ _)]] => rewrite list_to_array_app
        | [ |- context[p <=? length (lz ++ ly)]] => destruct (p <=? length (lz ++ ly)) eqn:Plz
        | [ |- context[p <=? length (ly ++ lx)]] => destruct (p <=? length (ly ++ lx)) eqn:Pyx
        | _ => simpl in *
        end.
    
    all: repeat rewrite length_app in *; try rewrite Nat.add_assoc.
    
    1, 2: assert(T: (p <=? length lz + length ly + length lx) = true)
      by (rewrite Nat.leb_le in *; lia);
    rewrite T; reflexivity.

    destruct (p <=? length lz + length ly + length lx) eqn:L.
    - reflexivity.
    - rewrite app_assoc.
      reflexivity.
    
  Qed.

  Lemma get_at_eq_invalid : forall param i old clk l,
      is_valid param old ->
      is_valid param (Incomplete((i, Invalid, clk) :: l)) ->
      exists clk', get_at i (compress param old (Incomplete((i, Invalid, clk) :: l))) = (None, clk').
  Proof.
    intros param i old clk l Hold Hnew.
    destruct Hnew as [_ Hnew]. inversion Hnew; subst.
    unfold is_valid_index, get_index in *.
    destruct old eqn:OLD; simpl.
    - rewrite Array.get_set_eq.
      repeat match goal with | [|- context[match ?v with | _ => _ end] ] => destruct v end;
        eexists; eauto.
      simpl in Hold.
      rewrite <- merge_new_list_old_array_length.
      lia.
    - destruct (param <=? S (length (l ++ l0))) eqn:L; simpl.
      + rewrite list_to_array_get_invalid; try lia.
        repeat match goal with | [|- context[match ?v with | _ => _ end] ] => destruct v end;
          eexists; eauto.
      + rewrite Nat.eqb_refl.
        repeat match goal with | [|- context[match ?v with | _ => _ end] ] => destruct v end;
          eexists; eauto.
  Qed.

  Lemma get_at_eq_valid : forall param i old cp clk l,
      is_valid param old ->
      is_valid param (Incomplete((i, Valid cp, clk)::l)) ->
      exists clk', get_at i (compress param old (Incomplete((i, Valid cp, clk)::l))) =
                     (Some cp, clk').
  Proof.
    intros param i old cp clk l Hold Hnew.
    destruct Hnew as [_ Hnew]. inversion Hnew; subst.
    unfold is_valid_index, get_index in *.
    destruct old eqn:OLD; simpl.
    - rewrite Array.get_set_eq.
      repeat match goal with | [|- context[match ?v with | _ => _ end] ] => destruct v end;
        eexists; eauto.
      simpl in Hold.
      rewrite <- merge_new_list_old_array_length.
      lia.
    - destruct (param <=? S (length (l ++ l0))) eqn:L; simpl.
      + rewrite list_to_array_get_valid; try lia.
        repeat match goal with | [|- context[match ?v with | _ => _ end] ] => destruct v end;
          eexists; eauto.
      + rewrite Nat.eqb_refl.
        repeat match goal with | [|- context[match ?v with | _ => _ end] ] => destruct v end;
          eexists; eauto.
  Qed.
  
End RegsData.

