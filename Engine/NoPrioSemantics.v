From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics PikeSubset.
From Warblre Require Import Base RegExpRecord.
From Linden Require Import StrictSuffix.
From Linden Require Import FunctionalSemantics.
From Linden Require Import ComputeIsTree.
From Linden Require Import Parameters.


(* A rephrasing of the semantics, where priority does not matter *)
(* It's a relation about leaves, not necessarily the first one *)
(* There are no actions, the shape of the regex determines the relation *)

Section NoPrioSemantics.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  Inductive noprio: input -> group_map -> regex -> input -> group_map -> Prop :=
  | np_eps:
    forall inp gm,
      noprio inp gm Epsilon inp gm
  | np_char:
    forall inp gm cd c nextinp
      (READ: read_char rer cd inp forward = Some (c, nextinp)),
      noprio inp gm (Regex.Character cd) nextinp gm
  | np_disj_left:
    forall inp gm r1 r2 nextinp nextgm
      (LEFT: noprio inp gm r1 nextinp nextgm),
      noprio inp gm (Disjunction r1 r2) nextinp nextgm
  | np_disj_right:
    forall inp gm r1 r2 nextinp nextgm
      (RIGHT: noprio inp gm r2 nextinp nextgm),
      noprio inp gm (Disjunction r1 r2) nextinp nextgm
  | np_seq:
    forall inp0 gm0 r1 r2 inp1 gm1 inp2 gm2
      (SEQ1: noprio inp0 gm0 r1 inp1 gm1)
      (SEQ2: noprio inp1 gm1 r2 inp2 gm2),
      noprio inp0 gm0 (Sequence r1 r2) inp2 gm2
  | np_quant_forced:
    forall inp0 gm0 r gidl min delta greedy inp1 gm1 inp2 gm2
      (RESET: gidl = def_groups r)
      (ITER: noprio inp0 (GroupMap.reset gidl gm0) r inp1 gm1)
      (LOOP: noprio inp1 gm1 (Quantified greedy min delta r) inp2 gm2),
      noprio inp0 gm0 (Quantified greedy (S min) delta r) inp2 gm2
  | np_quant_done:
    forall inp gm r greedy,
      noprio inp gm (Quantified greedy 0 (NoI.N 0) r) inp gm
  | np_quant_free:
    forall inp0 gm0 r greedy delta gidl inp1 gm1 inp2 gm2
      (RESET: gidl = def_groups r)
      (ITER: noprio inp0 (GroupMap.reset gidl gm0) r inp1 gm1)
      (PROGRESS: strict_suffix inp1 inp0 forward)
      (LOOP: noprio inp1 gm1 (Quantified greedy 0 delta r) inp2 gm2),
      noprio inp0 gm0 (Quantified greedy 0 (NoI.N 1 + delta)%NoI r) inp2 gm2
  | np_group:
    forall inp gm r gid nextinp nextgm
      (GROUP: noprio inp (GroupMap.open (idx inp) gid gm) r nextinp nextgm),
      noprio inp gm (Group gid r) nextinp (GroupMap.close (idx nextinp) gid nextgm)
  | np_anchor:
    forall inp gm a
      (ANCHOR: anchor_satisfied rer a inp = true),
      noprio inp gm (Anchor a) inp gm.
             
  (* LATER: there will be an issue if we want to add negative lookarounds: strict positivity *)
  (* We might want to declare an oracle version of this, since this reversal is used in engines when we already know about the values of deeper lookarounds. *)
  

  (** * NoPrio Tree Equivalence  *)
  
  (* TODO *)

End NoPrioSemantics.
