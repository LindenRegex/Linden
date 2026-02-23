From Stdlib Require Import ZArith List.
From Linden Require Import Chars Groups Tree LWParameters Parameters.
From Warblre Require Import Notation Result Errors Parameters Base Patterns.
Import Notation.

(** * Equivalence between Linden group maps and Warblre MatchStates *)

Section GroupMapMS.
  Context {params: LindenParameters}.

  (* Expresses equivalence of a GroupMap.range and a CaptureRange. *)
  Inductive equiv_ranges: GroupMap.range -> CaptureRange -> Prop :=
  | Equiv_ranges:
      forall startIdx endIdx: nat,
      equiv_ranges (GroupMap.Range startIdx (Some endIdx)) (capture_range (Z.of_nat startIdx) (Z.of_nat endIdx)).
  (* Lifting above relation to option *)
  (* We also say that an unclosed group in the Linden sense is equivalent to an undefined range in the Warblre sense. *)
  Inductive equiv_ranges_opt: option GroupMap.range -> option CaptureRange -> Prop :=
  | Equiv_ranges_None: equiv_ranges_opt None None
  | Equiv_ranges_unclosed: forall idx, equiv_ranges_opt (Some (GroupMap.Range idx None)) None
  | Equiv_ranges_Some: forall lrange wrange, equiv_ranges lrange wrange -> equiv_ranges_opt (Some lrange) (Some wrange).
  

  (* A group map and a MatchState are said to be equivalent when they define the same capture groups. *)
  Definition equiv_groupmap_ms (gm: GroupMap.t) (ms: MatchState): Prop :=
    forall gid_prec: nat, equiv_ranges_opt (GroupMap.find (S gid_prec) gm) (List.nth gid_prec (MatchState.captures ms) None).

  (** * Definition of lists of open groups and equivalence with group maps *)
  (* This is needed to characterize Warblre continuations *)

  (* A list of open groups is a stack of pairs of a group ID and an opening index. *)
  Definition open_groups: Type := list (group_id * nat).

  (* Equivalence with group maps by double inclusion *)
  Definition group_map_equiv_open_groups (gm: GroupMap.t) (gl: open_groups): Prop :=
    forall (gid: group_id) (idx: nat),
      GroupMap.find gid gm = Some (GroupMap.Range idx None) <->
      In (gid, idx) gl.

  (* Absence of forbidden groups from the group map *)
  Definition no_forbidden_groups (gm: GroupMap.t) (forbidden_groups: list group_id) :=
    forall gid: group_id, In gid forbidden_groups -> GroupMap.find gid gm = None.

  (* Disjointness of open groups list with list of defined groups; needed for capture reset case *)
  Definition open_groups_disjoint (gl: open_groups) (def_groups: list group_id) :=
    forall gid idx, In (gid, idx) gl -> ~In gid def_groups.

End GroupMapMS.