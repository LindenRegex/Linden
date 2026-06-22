
From Stdlib Require Import Arith List Lia Permutation.
Import ListNotations.
From Stdlib Require Import Program.Equality.

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

Lemma fold_left_preserves {A} {B} :
  forall (l: list A) (acc: B) P f,
    P acc ->
    (forall a x, P a -> In x l -> P (f a x)) ->
    P (fold_left f l acc).
Proof.
  induction l as [|x xs IH]; intros acc P f H H'; simpl in *.
  - assumption.
  - apply IH.
    + apply H'; auto.
    + intros a x' HP Hin.
      apply H'; auto.
Qed.

Lemma fold_right_preserves {A} {B} :
  forall (l: list A) (acc: B) P f,
    P acc ->
    (forall a x, P a -> In x l -> P (f x a)) ->
    P (fold_right f acc l).
Proof.
  induction l as [|x xs IH]; intros acc P f H Hf; simpl in *.
  - assumption.
  - apply Hf.
    + apply IH; auto.
    + auto.
Qed.

Lemma in_smaller_than_max: forall l x acc,
    In x l ->
    x <= fold_left max l acc.
Proof.
  induction l; intros x acc H; simpl in *.
  - contradiction.
  - destruct H as [H|H].
    + subst.
      apply fold_left_preserves; lia.
    + auto.
Qed.

Lemma perm_incl {A} :
  forall (a b: list A),
    Permutation a b ->
    incl a b.
Proof.
  unfold incl.
  intros a b PERM.
  dependent induction PERM; intros n H; simpl in *.
  - tauto.
  - destruct H; auto.
  - destruct H as [H | [H | H]]; auto.
  - auto.
Qed.

Lemma incl_app_comm {A} : forall (l l' l'': list A),
    incl (l' ++ l'') l ->
    incl (l'' ++ l') l.
Proof.
  unfold incl.
  intros l l' l'' H x Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin | Hin];
    apply H; apply in_or_app; [right | left]; assumption.
Qed.

Lemma list_helper {A} : forall (l l' l'': list A) x,
    incl (x :: l'') l ->
    NoDup (x :: l'') ->
    Permutation l (l' ++ l'') ->
    In x l'.
Proof.
  intros l l' l'' x INCL NODUP PERM.
  assert (IN: In x l) by (apply INCL; simpl; tauto).
  assert (IN': In x (l' ++ l'')) by (eapply Permutation_in; eauto).
  apply in_app_or in IN'.
  apply NoDup_cons_iff in NODUP.
  tauto.
Qed.

Lemma Forall2_and {A B} (f g : A -> B -> Prop) :
  forall l l',
  Forall2 f l l' ->
  Forall2 g l l' ->
  Forall2 (fun x y => f x y /\ g x y) l l'.
Proof.
  intros l l' Hf Hg.
  induction Hf.
  - inversion Hg; constructor.
  - inversion Hg; subst.
    constructor.
    + auto.
    + auto.
Qed.

Lemma incl_app_equiv: forall (A : Type) (l m n : list A),
    incl l n /\ incl m n <-> incl (l ++ m) n.
Proof.
  split; intros.
  - apply incl_app; tauto.
  - apply incl_app_inv; tauto.
Qed.

Lemma in_not_in_neq {A}: forall (x y: A) l,
    In x l ->
    ~ In y l ->
    x <> y.
Proof.
  intros x y l Hx Hy Heq.
  apply Hy. congruence.
Qed.

Lemma Forall2_true_pred {A B} :
  forall (l : list A) (l' : list B) p,
    length l = length l' ->
    p ->
    Forall2 (fun x y => p) l l'.
Proof.
  induction l as [|x l IH]; intros l' p Hlen Hp.
  - destruct l'.
    + constructor.
    + simpl in *. lia.
  - destruct l'; simpl in Hlen.
    + congruence.
    + inversion Hlen.
      constructor.
      * assumption.
      * apply IH; [lia | assumption].
Qed.

Lemma perm_nd_in {A} : forall (l a b c d : list A),
    Permutation (a ++ c) l ->
    incl b a ->
    incl d c ->
    NoDup l ->
    (forall x, In x b -> ~ In x d).
Proof.
  intros l a b c d PERM IAB ICD ND.
  intros x Hb Hd.
  apply Permutation_sym in PERM.
  apply Permutation_NoDup in PERM; try assumption.
  unfold incl in *.
  apply IAB in Hb. apply ICD in Hd.
  eapply ListHelpers.NoDup_in_app; eauto.
Qed.

Lemma NoDup_app_not_incl_or_nil {A} :
  forall (a b : list A),
  NoDup (a ++ b) ->
  ~ incl a b \/ a = [].
Proof.
  intros a b Hnd.
  destruct a as [|x a].
  - right; reflexivity.
  - left.
    intro Hincl.
    assert (Hinb : In x b) by (apply Hincl; left; reflexivity).
    inversion Hnd; subst.
    apply H1.
    apply in_or_app.
    tauto.
Qed.

Lemma nodup3 {A}: forall (a b c: list A),
    NoDup (a ++ b ++ c) ->
    NoDup (a ++ c ++ b).
Proof.
    intros a b c Hnd.
    apply (Permutation_NoDup (l := a ++ b ++ c)).
    - apply Permutation_app_head.
      apply Permutation_app_comm.
    - auto.
Qed.

Lemma Forall2_notin_r {A} {B} {C} :
  forall (x : C) (l : list A) (l' : list B) (f: B -> C) p,
    Forall2 (fun z y => p z y /\ f y <> x) l l' ->
    ~ In x (map f l').
Proof.
  intros x l l' f p FORALL.
  dependent induction FORALL; simpl; tauto.
Qed.

Lemma notin_r_Forall2 {A} {B} {C}:
  forall (x : C) (l : list A) (l' : list B) (f: B -> C),
    ~ In x (map f l') ->
    length l = length l' ->
    Forall2 (fun z y => f y <> x) l l'.
Proof.
  induction l; intros l' f H Hl.
  - simpl in *.
    destruct l'; try constructor; simpl in *; congruence.
  - simpl in *. destruct l'; simpl in *.
    + lia.
    + constructor.
      tauto.
      auto.
Qed.
