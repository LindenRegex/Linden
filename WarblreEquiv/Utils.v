From Stdlib Require Import List.
Import ListNotations.
From Warblre Require Import Typeclasses.

(** * Utilities (currently only boolean version of belonging to a list) *)

Module List.
  Definition inb {A} `{EqDec A} (x: A) (l: list A): bool :=
    if in_dec EqDec.eq_dec x l then true else false.

  Lemma inb_spec {A} `{EqDec A}:
    forall (x: A) (l: list A), inb x l = true <-> In x l.
  Proof.
    intros x l. unfold inb. destruct (in_dec _ x l).
    - tauto.
    - split. + discriminate. + contradiction.
  Qed.

  Lemma inb_cons {A} `{EqDec A}:
    forall (x a: A) (l: list A),
      inb x (a :: l) = orb (EqDec.eqb x a) (inb x l).
  Proof.
    intros; apply Bool.eq_iff_eq_true.
    rewrite Bool.orb_true_iff, !inb_spec, EqDec.inversion_true.
    firstorder.
  Qed.

  Definition Disjoint {A} (l1 l2: list A): Prop :=
    forall x: A, In x l1 -> ~In x l2.

  Lemma Disjoint_nil_r {A}:
    forall l: list A, Disjoint l nil.
  Proof.
    intros l x _. intro H. inversion H.
  Qed.

  Lemma Disjoint_nil_l {A}:
    forall l: list A, Disjoint nil l.
  Proof.
    intros l x H. inversion H.
  Qed.

  Lemma Disjoint_comm {A}:
    forall l1 l2: list A, Disjoint l1 l2 -> Disjoint l2 l1.
  Proof.
    intros l1 l2 Hdisj x Hin2 Hin1.
    unfold Disjoint, not in Hdisj. eauto using Hdisj.
  Qed.
End List.
