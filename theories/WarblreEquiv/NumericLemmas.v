From Warblre Require Import Numeric.
From Stdlib Require Import Lia.

(** * Lemmas about Warblre's `non_neg_integer_or_inf` (NoI) *)

(* The plus one operation is injective *)
Lemma plus_one_inj:
  forall (n m: non_neg_integer_or_inf),
    (NoI.N 1 + n)%NoI = (NoI.N 1 + m)%NoI -> n = m.
Proof.
  intros n m Heq.
  destruct n; destruct m; simpl in *; try discriminate; auto.
  now injection Heq as ->.
Qed.


(* Lemma used in repeat matching *)
Lemma mini_plus_plusminus_one:
  forall (mini: nat) (plus: non_neg_integer_or_inf) max',
    max' = (NoI.N (S mini) + plus)%NoI ->
    (if (max' =? +∞)%NoI then +∞ else (max' - 1)%NoI) = (NoI.N mini + plus)%NoI.
Proof.
  intros mini plus max' ->. simpl.
  destruct plus. 2: reflexivity.
  simpl. f_equal. lia.
Qed.


Lemma noi_eqb_eq:
  forall x y: non_neg_integer_or_inf, (x =? y)%NoI = true <-> x = y.
Proof.
  intros [n|] [m|].
  - simpl. rewrite PeanoNat.Nat.eqb_eq. split. + auto. + intro H; injection H as <-; reflexivity.
  - simpl. split; discriminate.
  - simpl. split; discriminate.
  - split; auto.
Qed.

Lemma noi_eqb_neq:
  forall x y: non_neg_integer_or_inf, (x =? y)%NoI = false <-> x <> y.
Proof.
  intros x y. pose proof noi_eqb_eq x y as H.
  destruct (x =? y)%NoI.
  - split. + discriminate. + pose proof ((proj1 H) eq_refl). contradiction.
  - split. 2: reflexivity. intros _ Habs. now apply <- H in Habs.
Qed.


Lemma noi_decr:
  forall x: non_neg_integer_or_inf,
    (if (x =? +∞)%NoI then +∞ else (x - 1)%NoI) = (x - 1)%NoI.
Proof.
  intro x. now destruct x as [n|].
Qed.


Lemma noi_nonzero_succprec:
  forall x: non_neg_integer_or_inf,
    x <> NoI.N 0 -> x = (NoI.N 1 + (x - 1))%NoI.
Proof.
  intros [ [|n] | ]; simpl. 1: contradiction. 2: reflexivity.
  - intros _. f_equal. lia.
Qed.


(* Used in repeat matching proof *)
Lemma noi_add_diff:
  forall (x: non_neg_integer) (y: non_neg_integer_or_inf),
    (x <=? y)%NoI = true -> (NoI.N x + (y - x))%NoI = y.
Proof.
  intros x [n|] Hle. 2: reflexivity.
  simpl in *. f_equal. rewrite PeanoNat.Nat.leb_le in Hle. lia.
Qed.
