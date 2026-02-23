(* Defining Capture Group Registers *)
(* Keeping an index of when a group was opened and closed *)

From Stdlib Require Import List Lia.
Import ListNotations.
From Stdlib Require Import MSetList OrdersAlt PeanoNat FMapList.

From Linden Require Import Chars.
From Warblre Require Import Typeclasses.

(** * Group Manipulation  *)

Module GroupId <: OrderedTypeWithLeibniz.
  Include Nat.
  Lemma eq_leibniz : forall x y, Nat.eq x y -> x = y. Proof. trivial. Qed.
End GroupId.

Definition group_id : Type := GroupId.t.

(** ** Group Sets *)

Definition group_set : Type := list group_id.

(** ** Group actions *)
(* The possible operations done on group maps during matching *)
Inductive groupaction : Type :=
| Open (g: group_id)
| Close (g: group_id)
| Reset (gl: group_set)
.

(** ** Group Maps *)

From Linden Require CanonicalMaps.

(* Partial maps from group ids to capture ranges *)
Module GroupMap.

  (* Capture groups are represented by their range in the matched string. *)
  (* The start and end indices are inclusive and exclusive respectively. *)
  (* A group is considered open when it has no end index, and closed o.w. *)
  Record range : Type := Range { startIdx : nat; endIdx : option nat }.
  Instance range_EqDec : EqDec.type range := { eq_dec := ltac:(repeat decide equality) }.

  Module MapS <: CanonicalMaps.S.
    Module GroupId' <: CanonicalMaps.OrderedTypeWithIrrelevance.
      Module OT := OrdersAlt.Backport_OT GroupId.
      Include OT.
      Lemma eq_leibniz : forall x y, OT.eq x y -> x = y.
      Proof. intros; assumption. Qed.
      Instance InvDec_lt: forall a0 a1, CanonicalMaps.ProofIrrelevance.InvDec (OT.lt a0 a1).
      Proof. intros. apply CanonicalMaps.ProofIrrelevance.InvDec_lt. Qed.
    End GroupId'.
    Include CanonicalMaps.Make GroupId'.
  End MapS.

  Module Facts := FMapFacts.Facts MapS.

  Definition t := MapS.t range.

  Definition empty : t := MapS.empty range.

  Definition find : group_id -> t -> option range := MapS.find (elt := range).

  Definition add: group_id -> range -> t -> t := MapS.add (elt := range).

  Section ops.
    Variable currIdx : nat. (* The current index in the string being matched *)

    Definition open (gid : group_id) : t -> t :=
      MapS.add gid (Range currIdx None).

    (* Assumes, but does not check, the g is associated to an open range *)
    Definition close (gid : group_id) (gm : t) : t :=
      match find gid gm with
      | Some (Range startIdx _) =>
          if startIdx <=? currIdx then
            MapS.add gid (Range startIdx (Some currIdx)) gm
          else
            MapS.add gid (Range currIdx (Some startIdx)) gm
      | None => gm
      end.

    Definition reset : group_set -> t -> t :=
      List.fold_left (fun s gid => MapS.remove gid s).

    Definition update (op : groupaction) : t -> t :=
      match op with
      | Open g => open g
      | Close g => close g
      | Reset gs => reset gs
      end.
  End ops.

  Definition eqb: t -> t -> bool :=
    MapS.equal EqDec.eqb.

  Lemma eqb_eq t0 t1: eqb t0 t1 = true <-> t0 = t1.
  Proof. apply MapS.equal_eq, EqDec.inversion_true. Qed.

  #[refine] Instance EqDec_t: EqDec t :=
    { eq_dec t1 t2 := match eqb t1 t2 as b return eqb t1 t2 = b -> _ with
                     | true => fun Heq => left _
                     | false => fun Hneq => right _
                     end eq_refl }.
  Proof.
    - apply eqb_eq; assumption.
    - rewrite <- eqb_eq. congruence.
  Qed.

  (* MapsTo, In *)
  Definition MapsTo := MapS.MapsTo (elt := range).
  Definition In := MapS.In (elt := range).
End GroupMap.

Definition group_map : Type := GroupMap.t.
