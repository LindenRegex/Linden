From Stdlib Require Import Eqdep_dec List Permutation SetoidList Bool RelationClasses.

(** Canonical maps *)
(* Maps for which for all maps m1 and m2, we have Equal m1 m2 <-> m1 = m2. *)

Module ProofIrrelevance.
  Class InvDec (P: Prop) := {
      Pb: bool;
      Pb_P: Pb = true -> P;
      P_Pb: P -> Pb = true;
      inv: forall p: P, p = Pb_P (P_Pb p)
    }.

  Class Irrelevant (P: Prop) := {
      irrel: forall p0 p1: P, p0 = p1
    }.

  Lemma UIP_bool {b0 b1: bool} (p0 p1: b0 = b1): p0 = p1.
  Proof.
    destruct p0; symmetry; apply Eqdep_dec.UIP_refl_bool.
  Qed.

  Instance InvDec_Irrelevant {P} {ID: InvDec P} : Irrelevant P.
  Proof.
    constructor; intros.
    rewrite (inv p0), (inv p1).
    f_equal. apply UIP_bool.
  Qed.

  #[refine] Instance InvDec_lt a b : InvDec (lt a b) := {
      Pb := Nat.ltb a b
    }.
  Proof.
    - apply PeanoNat.Nat.ltb_lt.
    - apply PeanoNat.Nat.ltb_lt.
    - intros; apply Peano_dec.le_unique.
  Qed.
End ProofIrrelevance.

Import ProofIrrelevance ListNotations.

Section Sorted.
  Context {A: Type} (R: A -> A -> Prop).
  Context {ID: forall a0 a1, InvDec (R a0 a1)}.

  Definition HdRelb (a: A) (l: list A) :=
    match l with
    | [] => true
    | hd :: tl => (ID a hd).(Pb)
    end.

  Lemma HdRel_HdRelb : forall a (l: list A),
      HdRel R a l -> HdRelb a l = true.
  Proof.
    inversion 1; simpl; subst.
    - reflexivity.
    - apply (ID a b).(P_Pb); assumption.
  Defined.

  Lemma HdRelb_HdRel : forall a (l: list A),
      HdRelb a l = true -> HdRel R a l.
  Proof.
    destruct l as [ | a' l]; simpl; constructor.
    apply (ID  a a').(Pb_P); assumption.
  Defined.

  #[refine] Instance InvDec_HdRel a l : InvDec (HdRel R a l) := {
      Pb := HdRelb a l;
      P_Pb := HdRel_HdRelb a l;
      Pb_P := HdRelb_HdRel a l
    }.
  Proof.
    destruct p; simpl.
    - reflexivity.
    - f_equal.
      apply (ID a b).(inv).
  Qed.

  Fixpoint Sortedb (l: list A) :=
    match l with
    | [] => true
    | hd :: tl => Sortedb tl && (InvDec_HdRel hd tl).(Pb)
    end.

  Lemma Sorted_Sortedb : forall (l: list A),
      Sorted R l -> Sortedb l = true.
  Proof.
    fix IH 2.
    destruct 1 as [ | hd tl HR HS ]; simpl; subst.
    - reflexivity.
    - apply IH in HR.
      apply P_Pb in HS.
      rewrite HR, HS; reflexivity.
  Defined.

  Lemma Sortedb_Sorted : forall (l: list A),
      Sortedb l = true -> Sorted R l.
  Proof.
    fix IH 1.
    destruct l as [ | n l]; simpl.
    - constructor.
    - specialize (IH l).
      pose proof (InvDec_HdRel n l).(Pb_P).
      destruct (Sortedb l) eqn:HA; try discriminate.
      destruct (InvDec_HdRel n l).(Pb) eqn:HB; try discriminate.
      constructor; eauto.
  Defined.

  #[refine] Instance InvDec_Sorted l : InvDec (Sorted R l) := {
      Pb := Sortedb l;
      P_Pb := Sorted_Sortedb l;
      Pb_P := Sortedb_Sorted l
    }.
  Proof.
    revert l.
    fix IH 2; destruct p as [ | hd tl HS HR ]; simpl.
    - reflexivity.
    - specialize (IH _ HS).
      set (Sorted_Sortedb tl HS) as HPbS in *; clearbody HPbS.
      set (P_Pb HR) as HPbR; clearbody HPbR.
      set (Sortedb_Sorted tl) as PbPS in *; clearbody PbPS.
      set (InvDec_HdRel hd tl).(Pb_P) as PbPR; clearbody PbPR.
      destruct (Sortedb tl) eqn:HeqS; try discriminate.
      destruct (InvDec_HdRel hd tl).(Pb) eqn:HeqB; try discriminate.
      rewrite (Eqdep_dec.UIP_refl_bool _ HPbR), (Eqdep_dec.UIP_refl_bool _ HPbS) in *.
      unfold eq_ind_r, eq_sym; simpl; f_equal.
      + apply IH.
      + apply irrel.
  Qed.
End Sorted.

Lemma In_InA_iff [A] (l : list A) (x : A):
  In x l <-> InA eq x l.
Proof.
  split; eauto using In_InA, eq_equivalence.
  revert l x; induction l; simpl; inversion 1; subst; eauto.
Qed.

Lemma eqlistA_eq {A} (cmp: A -> A -> Prop) (l0 l1: list A) :
  (forall a0 a1, cmp a0 a1 -> a0 = a1) ->
  eqlistA cmp l0 l1 ->
  l0 = l1.
Proof.
  intros Hl; apply eqlistA_ind.
  - reflexivity.
  - intros * ->%Hl _ ->; reflexivity.
Qed.

From Stdlib Require Import FMapInterface FMapList FMapFacts.

Module Type OrderedTypeWithIrrelevance.
  Declare Module OT: OrderedType.
  Include OT.
  Parameter eq_leibniz : forall x y, OT.eq x y -> x = y.
  Parameter InvDec_lt: forall a0 a1, InvDec (OT.lt a0 a1).
End OrderedTypeWithIrrelevance.

Module Type S.
  Include FMapInterface.S.
  Axiom Equal_eq: forall {elt} (t0 t1: t elt), Equal t0 t1 <-> t0 = t1.
End S.

Module Make (X: OrderedTypeWithIrrelevance) <: S.
  Module M := FMapList.Make X.
  Module F := FMapFacts.Facts M.
  Include M.

  Lemma Equal_eq_this {elt} (t0 t1: t elt):
    Equal t0 t1 ->
    eqlistA (M.eq_key_elt (elt:=elt)) t0.(this) t1.(this).
  Proof.
    intros HEq.
    eapply SortA_equivlistA_eqlistA;
      eauto using sorted, Raw.PX.ltk_strorder, M.Raw.PX.eqke_equiv, M.Raw.PX.ltk_compat'.
    intros [k e].
    rewrite F.Equal_mapsto_iff in HEq; specialize (HEq k e).
    rewrite !F.elements_mapsto_iff in HEq.
    assumption.
  Qed.

  Lemma Equal_eq {elt} (t0 t1: t elt): Equal t0 t1 <-> t0 = t1.
  Proof.
    split; [ | intros ->; reflexivity ].
    intros HEq%Equal_eq_this%eqlistA_eq.
    - pose proof X.InvDec_lt.
      destruct t0, t1; simpl in *; destruct HEq.
      f_equal; apply (irrel (Irrelevant := InvDec_Irrelevant (ID := InvDec_Sorted _ _))).
    - intros [k0 e0] [k1 e1] [Hfst%X.eq_leibniz Hsnd]; simpl in *; congruence.
  Qed.

  Lemma equal_eq {elt} (cmp: elt -> elt -> bool) (t0 t1: t elt):
    (forall e0 e1, cmp e0 e1 = true <-> e0 = e1) ->
    equal cmp t0 t1 = true <-> t0 = t1.
  Proof.
    intros; rewrite <- (Equal_eq t0 t1), <- F.equal_iff, <- F.Equal_Equivb;
      reflexivity || eauto.
  Qed.
End Make.
