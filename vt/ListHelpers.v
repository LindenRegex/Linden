
From Stdlib Require Import Arith List Permutation.
Import ListNotations.

Lemma NoDup_one {A} : forall (x: A),
    NoDup [x].
Proof.
  intros x.
  constructor.
  - intros H.
    apply in_nil in H.
    contradiction.
  - constructor.
Qed.

Lemma NoDup_two {A} : forall (x y: A),
    x <> y ->
    NoDup [x; y].
Proof.
  intros x y H.
  constructor.
  - intros C; inversion C; subst; auto.
  - apply NoDup_one.
Qed.

Lemma not_NoDup_two {A} : forall (i: A),
    ~ NoDup [i; i].
Proof.
  intros i H.
  inversion H. subst.
  assert (I: In i [i]) by (constructor; reflexivity).
  tauto.
Qed.

Lemma NoDup_app_add {A} : forall l l' (a: A),
    ~ In a l ->
    ~ In a l' ->
    NoDup (l ++ l') ->
    NoDup (l ++ a :: l').
Proof.
  induction l; intros l' b Ha Ha' H; simpl in *; auto.
  - constructor; auto.
  - apply NoDup_cons_iff in H. destruct H as [H H'].
    constructor.
    + intros C.
      rewrite in_app_iff in *.
      destruct C as [C | C].
      * tauto.
      * apply in_inv in C.
        destruct C as [C | C]; try symmetry in C; tauto.
    + apply IHl; auto.
Qed.

Lemma NoDup_in_app {A} : forall l l' (a: A),
    NoDup (l ++ l') ->
    In a l ->
    ~ In a l'.
Proof.
  induction l; intros l' b H Ha; simpl.
  - inversion Ha.
  - rewrite <- app_comm_cons in H.
    apply NoDup_cons_iff in H. destruct H as [Hi H].
    apply in_inv in Ha.
    destruct Ha as [Ha | Ha].
    + rewrite Ha in *.
      rewrite in_app_iff in Hi.
      tauto.
    + apply IHl; auto.
Qed.

Lemma NoDup_app_comm {A} : forall (l l': list A),
    NoDup (l ++ l') -> NoDup (l' ++ l).
Proof.
  induction l; intros l' H; simpl in *.
  - rewrite app_nil_r.
    assumption.
  - apply NoDup_cons_iff in H. destruct H as [Hin H].
    rewrite in_app_iff in Hin.
    apply NoDup_app_add; auto.
Qed.

Lemma NoDup_app_remove {A} : forall (l l' : list A),
    NoDup (l ++ l') ->
    NoDup l /\ NoDup l'.
Proof.
  intros. split.
  - eapply NoDup_app_remove_r. eauto.
  - eapply NoDup_app_remove_l. eauto.
Qed.

Lemma Permutation_app_sym {A} : forall (l l' m : list A),
    Permutation (l ++ l') m ->
    Permutation (l' ++ l) m.
Proof.
  intros.
  econstructor.
  - apply Permutation_app_comm.
  - assumption.
Qed.

Lemma in_subset {A} : forall (a: A) l l',
    incl l l' ->
    In a l ->
    In a l'.
Proof.
  intros.
  unfold incl in *.
  auto.
Qed.
