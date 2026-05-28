From Warblre Require Import List.
From Stdlib Require Import List Lia ZArith.
Import ListNotations.

(** * Lemmas on lists *)

(* Subtracting one to each element of a range is equivalent to subtracting one to the
   base of the range, provided that this base is at least 1. *)
Lemma decr_range: forall base l: nat,
  base >= 1 -> List.map (fun x => x-1) (List.List.Range.Nat.Length.range base l) =
    List.List.Range.Nat.Length.range (base-1) l.
Proof.
  intros base l.
  revert base.
  induction l as [|l IHl].
  - intros base Hb1. simpl. reflexivity.
  - intros base Hb1. simpl. f_equal.
    replace (base - 1 + 1) with (base + 1 - 1) by lia. apply IHl. lia.
Qed.


(* Provided i1 and i2 are valid indices in a list l, if skipn i1 l = skipn i2 l,
   then i1 = i2 (modulo conversions between Z and nat). *)
Lemma skipn_ind_inv {A: Type}:
  forall (i1 i2: Z) (l: list A),
    (0 <= i1 <= Z.of_nat (length l))%Z -> (0 <= i2 <= Z.of_nat (length l))%Z ->
    skipn (Z.to_nat i1) l = skipn (Z.to_nat i2) l ->
    i1 = i2.
Proof.
  intros i1 i2 l Hi1valid Hi2valid Hskipn.
  apply (f_equal (length (A := A))) in Hskipn.
  do 2 rewrite length_skipn in Hskipn.
  lia.
Qed.


(* Modulo conversions between Z and nat, if rev pref ++ next = str0, then
   skipn (length pref) str0 = next. *)
Lemma skipn_lenpref_input {A: Type}:
  forall (pref next: list A) (str0: list A) (endInd1: Z),
    rev pref ++ next = str0 ->
    Z.of_nat (length pref) = endInd1 ->
    next = skipn (Z.to_nat endInd1) str0.
Proof.
  intros pref next str0 endInd1 Hconcat Hlenpref.
  apply (f_equal (skipn (Z.to_nat endInd1))) in Hconcat.
  rewrite skipn_app in Hconcat.
  rewrite length_rev in Hconcat.
  replace (Z.to_nat endInd1 - length pref) with 0 in Hconcat by lia.
  simpl in Hconcat.
  replace (Z.to_nat endInd1) with (length pref) in Hconcat by lia.
  rewrite <- length_rev in Hconcat at 1.
  rewrite skipn_all in Hconcat.
  now replace (Z.to_nat endInd1) with (length pref) by lia.
Qed.

Lemma concat_nil_rev {A}:
  forall (l: list (list A)),
    concat l = [] -> concat (rev l) = [].
Proof.
  induction l; simpl; intros H.
  - easy.
  - apply app_eq_nil in H as [-> H2].
    now rewrite concat_app, IHl.
Qed.

Lemma cons_different {A}: forall (x: A) (l: list A), l <> x::l.
Proof.
  induction l.
  - discriminate.
  - now inversion 1.
Qed.

Lemma in_pair_exists_r:
  forall {A B} (x: A) (l: list (A * B)),
    In x (List.map fst l) <->
      exists y, In (x, y) l.
Proof.
  induction l as [|[a b] l]; simpl in *.
  1: split; intros H; repeat destruct H.
  split; intros H.
  - destruct H as [|]; subst.
    + exists b. now left.
    + rewrite IHl in H.
      destruct H. eauto.
  - destruct H as [y [|]].
    + injection H as <- <-. now left.
    + right. rewrite IHl. eauto.
Qed.

Lemma skipn_nil_length {A}:
  forall n (l: list A),
    skipn n l = [] -> length l <= n.
Proof.
  intros n l Hskipn.
  pose proof firstn_skipn n l. rewrite Hskipn in H.
  apply (f_equal (length (A := A))) in H. rewrite length_app in H.
  simpl in H. rewrite <- plus_n_O in H. rewrite <- H. apply firstn_le_length.
Qed.

(* extensionality for set-like lists *)
Definition list_ext {A} (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.
