From Linden Require Import LeavesEquivalence Parameters Tree.
From Stdlib Require Import List.
Import ListNotations.


(** * Flat mapping: definition and lemmas *)

(* a propositional version of flat_map *)
(* FlatMap lbase f lmapped means that lmapped corresponds to the list lbase where each element has been replaced by its image by f *)
Inductive FlatMap {X Y:Type} : list X -> (X -> list Y -> Prop) -> list Y -> Prop :=
| FM_nil: forall f,
  FlatMap [] f []
| FM_cons:
  forall lbase f lmapped x ly
    (FM: FlatMap lbase f lmapped)
    (HEAD: f x ly),
    FlatMap (x::lbase) f (ly ++ lmapped).

(* We could use the functional flat_map, but this would require using the function compute_tr that associates a tree to each regex and input. *)
(* The proof does not strictly rely on this function, it merely relies on the
existence of a unique tree associated to each regex and input. *)

(* Used in disjunction and free quantifier cases of contextual equivalence proof *)
Property FlatMap_app {X Y: Type}:
  forall (lbase1 lbase2 : list X) (f: X -> list Y -> Prop) (lmapped1 lmapped2: list Y),
    FlatMap lbase1 f lmapped1 ->
    FlatMap lbase2 f lmapped2 ->
    FlatMap (lbase1 ++ lbase2) f (lmapped1 ++ lmapped2).
Proof.
  intros lbase1 lbase2 f lmapped1 lmapped2 FM1 FM2.
  induction FM1.
  - auto.
  - rewrite <- app_assoc, <- app_comm_cons. constructor; auto.
Qed.

(* Determinism of a propositional function *)
Definition determ {A B: Type} (f: A -> B -> Prop) :=
  forall x y1 y2, f x y1 -> f x y2 -> y1 = y2.


(* Building up to flatmap_leaves_equiv_l *)

Lemma FlatMap_in {A B}:
  forall (l: list A) (f: A -> list B -> Prop) fl x fx,
    (* For a deterministic f, *)
    determ f ->
    (* if f flat maps l to fl, *)
    FlatMap l f fl ->
    (* and x is in l, *)
    In x l ->
    f x fx ->
    (* then all the elements of f(x) are in fl. *)
    Forall (fun y => In y fl) fx.
Proof.
  intros l f fl x fx DETERM FM INxl F.
  revert fl FM.
  induction l.
  1: inversion INxl.
  intros fl FM. destruct INxl.
  - subst a. inversion FM; subst.
    assert (ly = fx) by eauto (* using DETERM *). subst ly. clear HEAD FM F IHl.
    induction fx.
    + constructor.
    + constructor.
      * rewrite <- app_comm_cons. left. reflexivity.
      * eapply Forall_impl; eauto. simpl. tauto.
  - inversion FM; subst. specialize (IHl H lmapped FM0).
    eapply Forall_impl; eauto. simpl. intro. rewrite in_app_iff. tauto.
Qed.

(* Variant of the above lemma but using is_seen instead of In *)
Lemma FlatMap_in2 {params: LindenParameters}:
  forall f leaf fleaf seen fseen,
    (* For a deterministic f, *)
    determ f ->
    (* if f flat maps seen to fseen, *)
    FlatMap seen f fseen ->
    (* and leaf is in seen, *)
    is_seen leaf seen = true ->
    f leaf fleaf ->
    (* then all the elements of f(leaf) are in fseen. *)
    forall x, is_seen x fleaf = true -> is_seen x fseen = true.
Proof.
  intros f leaf fleaf seen fseen DET FM LEAFSEEN FLEAF x XLEAF.
  rewrite is_seen_spec in LEAFSEEN, XLEAF. rewrite is_seen_spec.
  specialize (FlatMap_in _ _ _ _ _ DET FM LEAFSEEN FLEAF) as ALLIN.
  rewrite Forall_forall in ALLIN. auto.
Qed.

(* Generalized version of flatmap_leaves_equiv_l *)
Lemma flatmap_leaves_equiv_l_seen {params: LindenParameters}:
  forall l1 l2 seen f fseen fl1 fl2,
    determ f ->
    leaves_equiv seen l1 l2 ->
    FlatMap l1 f fl1 ->
    FlatMap l2 f fl2 ->
    FlatMap seen f fseen ->
    leaves_equiv fseen fl1 fl2.
Proof.
  intros l1 l2 seen f fseen fl1 fl2 DET EQUIV FM1 FM2 FMSEEN.
  generalize dependent fl1. generalize dependent fl2. generalize dependent fseen.
  induction EQUIV; intros.
  - inversion FM2; subst. inversion FM1; subst. apply leaves_equiv_refl.
  - inversion FM1; subst. apply leaves_equiv_subseen; auto.
    eapply FlatMap_in2; eauto.
  - inversion FM2; subst. symmetry.
    apply leaves_equiv_subseen; auto.
    2: { symmetry. auto. }
    eapply FlatMap_in2; eauto.
  - inversion FM1; inversion FM2; subst.
    specialize (DET _ _ _ HEAD HEAD0). subst.
    apply leaves_equiv_app2; auto.
    + apply leaves_equiv_refl.
    + eapply IHEQUIV; eauto. constructor; auto.
Qed.

(* The lemma: for a deterministic f, flat mapping preserves leaves equivalence *)
Lemma flatmap_leaves_equiv_l {params: LindenParameters}:
  forall leaves1 leaves2 f leavesf1 leavesf2,
    determ f ->
    leaves_equiv [] leaves1 leaves2 ->
    FlatMap leaves1 f leavesf1 ->
    FlatMap leaves2 f leavesf2 ->
    leaves_equiv [] leavesf1 leavesf2.
Proof.
  intros.
  eapply flatmap_leaves_equiv_l_seen with (seen := []); eauto. constructor.
Qed.


(* Definition of equivalent leaf functions (that is, functions from leaves to lists of leaves) *)
Definition equiv_leaffuncts {params: LindenParameters} (f g: leaf -> list leaf -> Prop): Prop :=
  forall lf yf yg,
    f lf yf -> g lf yg ->
    leaves_equiv [] yf yg.

(* Flat mapping a list of leaves with equivalent leaf functions yields equivalent lists of leaves *)
Lemma flatmap_leaves_equiv_r {params: LindenParameters}:
  forall leaves f g leavesf leavesg,
    equiv_leaffuncts f g ->
    FlatMap leaves f leavesf ->
    FlatMap leaves g leavesg ->
    leaves_equiv [] leavesf leavesg.
Proof.
  intros leaves f g leavesf leavesg FGEQUIV FMF FMG.
  generalize dependent leavesg.
  induction FMF; intros; inversion FMG; subst.
  { apply leaves_equiv_refl. }
  apply leaves_equiv_app2.
  - eapply FGEQUIV; eauto.
  - rewrite app_nil_r. apply IHFMF in FM; auto.
    eapply leaves_equiv_monotony with (seen1:=[]); eauto.
    { intros x0 H. simpl in H. inversion H. }
Qed.


(* Conditionally equivalent leaf functions: two leaf functions f and g are said to be
equivalent conditionally on P when f(l) and g(l) are equivalent for all l *such that P(l) holds*. *)
(* Used in induction proof for quantifiers, because the induction is performed on
the length of the remaining string to match *)
Definition equiv_leaffuncts_cond {params: LindenParameters} (f g: leaf -> list leaf -> Prop) (P: leaf -> Prop): Prop :=
  forall l, P l ->
    forall yf yg, f l yf -> g l yg -> leaves_equiv [] yf yg.


(* Same as flatmap_leaves_equiv_r, but taking the condition into account *)
Lemma flatmap_leaves_equiv_r_prop {params: LindenParameters}:
  forall l f g fl gl P,
    equiv_leaffuncts_cond f g P ->
    Forall P l ->
    FlatMap l f fl ->
    FlatMap l g gl ->
    leaves_equiv [] fl gl.
Proof.
  intros l f g fl gl P EQFG PL FMF FMG.
  generalize dependent gl.
  induction FMF; intros; inversion FMG; subst.
  - reflexivity.
  - apply leaves_equiv_app2.
    + eapply EQFG; eauto. now inversion PL.
    + rewrite app_nil_r. apply IHFMF in FM; auto.
      * eapply leaves_equiv_monotony with (seen1 := []); eauto.
        intros x0 H. simpl in H. inversion H.
      * now inversion PL.
Qed.