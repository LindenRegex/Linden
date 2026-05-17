From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics BooleanSemantics.
From Linden Require Import NFA.
From Linden Require Import PikeSubset.
From Linden Require Import Parameters.
From Warblre Require Import Base RegExpRecord.


Section TreeRep.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).
(** * Tree Rep Predicate  *)
(* A predicate showing that a tree is represented at a given point in the code *)
(* For a given input and boolean *)


Inductive tree_rep: tree -> code -> label -> input -> LoopBool -> Prop :=
| tr_match:
  forall code pc inp b
    (ACCEPT: get_pc code pc = Some Accept),
    tree_rep Match code pc inp b
| tr_jmp:
  forall code pc nextpc inp b t
    (JMP: get_pc code pc = Some (Jmp nextpc))
    (TR: tree_rep t code nextpc inp b),
    tree_rep t code pc inp b
| tr_begin:
  forall code pc inp b t
    (BEGIN: get_pc code pc = Some BeginLoop)
    (TR: tree_rep t code (S pc) inp CannotExit),
    tree_rep t code pc inp b
| tr_choice:
  forall code pc pc1 pc2 inp b t1 t2
    (FORK: get_pc code pc = Some (Fork pc1 pc2))
    (TR1: tree_rep t1 code pc1 inp b)
    (TR2: tree_rep t2 code pc2 inp b),
    tree_rep (Choice t1 t2) code pc inp b
| tr_read:
  forall code pc inp nextinp b cd c t
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char rer cd inp forward = Some (c, nextinp))
    (TR: tree_rep t code (S pc) nextinp CanExit),
    tree_rep (Read c t) code pc inp b
| tr_progress:
  forall code pc nextpc inp t
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc))
    (TR: tree_rep t code nextpc inp CanExit),
    tree_rep (Progress t) code pc inp CanExit
| tr_open:
  forall code pc gid inp b t
    (OPEN: get_pc code pc = Some (SetRegOpen gid))
    (TR: tree_rep t code (S pc) inp b),
    tree_rep (GroupAction (Open gid) t) code pc inp b
| tr_close:
  forall code pc gid inp b t
    (CLOSE: get_pc code pc = Some (SetRegClose gid))
    (TR: tree_rep t code (S pc) inp b),
    tree_rep (GroupAction (Close gid) t) code pc inp b
| tr_reset:
  forall code pc gidl inp b t
    (RESET: get_pc code pc = Some (ResetRegs gidl))
    (TR: tree_rep t code (S pc) inp b),
    tree_rep (GroupAction (Reset gidl) t) code pc inp b
| tr_anchor:
  forall code pc inp b a t
    (ANCHOR: get_pc code pc = Some (CheckAnchor a))
    (CHECK: anchor_satisfied rer a inp = true)
    (TR: tree_rep t code (S pc) inp b),
    tree_rep (AnchorPass a t) code pc inp b
| tr_anchorfail:
  forall code pc inp b a
    (ANCHOR: get_pc code pc = Some (CheckAnchor a))
    (CHECK: anchor_satisfied rer a inp = false),
    tree_rep Mismatch code pc inp b
| tr_readfail:
  forall code pc inp b cd
    (CONSUME: get_pc code pc = Some (Consume cd))
    (READ: read_char rer cd inp forward = None),
    tree_rep Mismatch code pc inp b
| tr_progressfail:
  forall code pc nextpc inp
    (ENDLOOP: get_pc code pc = Some (EndLoop nextpc)),
    tree_rep Mismatch code pc inp CannotExit.


(** * Tree Rep Determinism  *)
(* this is essential to allow memoization *)
(* If we end up on the same pc, we represent the same tree *)
(* meaning that we can safely memoize it and cut the lower priority thread *)

Ltac same_instr :=
  match goal with
  | [ H1 : get_pc ?code ?pc = ?i1, H2: get_pc ?code ?pc = ?i2 |- _ ] => rewrite H1 in H2; inversion H2; subst
  end.

(* Determinism of the tree representation *)
Theorem tree_rep_determ:
  forall code pc inp b t1 t2,
    tree_rep t1 code pc inp b ->
    tree_rep t2 code pc inp b ->
    t1 = t2.
Proof.
  intros code pc inp b t1 t2 H H0.
  generalize dependent t2.
  induction H; intros.
  - inversion H0; subst; auto; same_instr.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ TR) as EQT.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
  - inversion H1; subst; auto; same_instr.
    specialize (IHtree_rep1 _ TR1) as EQT1.
    specialize (IHtree_rep2 _ TR2) as EQT2.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr;
      rewrite READ0 in READ; inversion READ; subst.
    specialize (IHtree_rep _ TR) as EQT.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ TR) as EQT.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ TR) as EQT.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ TR) as EQT.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    specialize (IHtree_rep _ TR) as EQT.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr;
      rewrite CHECK0 in CHECK; inversion CHECK; subst.
    specialize (IHtree_rep _ TR) as EQT.
    subst. split; auto.
  - inversion H0; subst; auto; same_instr.
    rewrite CHECK0 in CHECK. discriminate.
  - inversion H0; subst; auto; same_instr.
    rewrite READ0 in READ. inversion READ.
  - inversion H0; subst; auto; same_instr.
Qed.


(** * Relation to actions_rep  *)

(* Actions rep to tree rep *)

(* NOTE: here the induction on ACT only serves when there are jmps. In the other case, IHACT is never needed *)
Theorem actions_tree_rep:
  forall actions code pc inp b t
    (SUBSET: pike_actions actions)
    (ACT: actions_rep actions code pc)
    (TREE: bool_tree rer actions inp b t),
    tree_rep t code pc inp b.
Proof.
  intros actions code pc inp b t SUBSET ACT TREE.
  generalize dependent code. generalize dependent pc.
  induction TREE; intros.
  (* Match *)
  - remember [] as emp. induction ACT; inversion Heqemp.
    + constructor. auto.
    + eapply tr_jmp; eauto.
  (* Progress *)
  - remember (Acheck strcheck :: cont) as checkcont.
    induction ACT; inversion Heqcheckcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. eapply tr_progress; eauto.
    eapply IHTREE; eauto. pike_subset.
  (* progress fail *)
  - remember (Acheck strcheck :: cont) as checkcont.
    induction ACT; inversion Heqcheckcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep.
    eapply tr_progressfail; eauto.
  (* close *)
  - remember (Aclose gid :: cont) as closecont.
    induction ACT; inversion Heqclosecont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. eapply tr_close; eauto.
    eapply IHTREE; eauto. pike_subset.
  (* epsilon *)
  - remember (Areg Epsilon :: cont) as epscont.
    induction ACT; inversion Heqepscont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply IHTREE; eauto. pike_subset.
  (* character *)
  - remember (Areg (Regex.Character cd) :: cont) as charcont.
    induction ACT; inversion Heqcharcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_read; eauto.
    eapply IHTREE; eauto. pike_subset.
  (* read fail *)
  - remember (Areg (Regex.Character cd) :: cont) as charcont.
    induction ACT; inversion Heqcharcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_readfail; eauto.
  (* disjunction *)
  - remember (Areg (Disjunction r1 r2) :: cont) as disjcont.
    induction ACT; inversion Heqdisjcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_choice; eauto.
    + eapply IHTREE1. pike_subset.
      eapply cons_bc with (pcmid:=end1); try constructor; eauto.
      eapply jump_bc; eauto.
    + eapply IHTREE2; eauto. pike_subset.
      repeat (econstructor; eauto).
  (* sequence *)
  - remember (Areg (Sequence r1 r2) :: cont) as seqcont.
    induction ACT; inversion Heqseqcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto).
  (* quantified, forced *)
  - pike_subset.
  (* quantified, done *)
  - remember (Areg (Quantified greedy 0 (NoI.N 0) r1) :: cont) as zerocont.
    induction ACT; inversion Heqzerocont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply IHTREE; eauto. pike_subset.
  (* quantified, free *)
  - destruct (destruct_delta (NoI.N 1 + plus)%NoI) as [DZ | [D1 | [DINF | [delta' [DUN N3]]]]].
    (* Zero repetitions *)
    + destruct plus; inversion DZ.
    (* Question Mark *)
    + destruct plus; inversion D1. subst.
      simpl in ACT.
      remember (Areg (Quantified greedy 0 (NoI.N 1) r1) :: cont) as qmarkcont.
      induction ACT; inversion Heqqmarkcont; subst;
        try solve[eapply tr_jmp; eauto]; clear IHACT.
      invert_rep. inversion NFA; subst.
      2: { in_subset. }
      destruct greedy; simpl.
      * eapply tr_choice; eauto.
        ** eapply tr_begin; eauto.
           eapply tr_reset; eauto.
           eapply IHTREE1; eauto. pike_subset.
           repeat (econstructor; eauto).
        ** eapply IHTREE2; eauto. pike_subset.
      * eapply tr_choice; eauto.
        ** eapply IHTREE2; eauto. pike_subset.
        ** eapply tr_begin; eauto.
           eapply tr_reset; eauto.
           eapply IHTREE1; eauto. pike_subset.
           repeat (econstructor; eauto).
    (* Star *)
    + destruct plus; inversion DINF. clear DINF.
      simpl in ACT.
      remember (Areg (Quantified greedy 0 +∞ r1) :: cont) as starcont.
      induction ACT; inversion Heqstarcont; subst;
        try solve[eapply tr_jmp; eauto]; clear IHACT.
      invert_rep. inversion NFA; subst.
      2: { in_subset. }
      destruct greedy; simpl.
      * eapply tr_choice; eauto.
        ** eapply tr_begin; eauto.
           eapply tr_reset; eauto.
           eapply IHTREE1; eauto. pike_subset.
           repeat (econstructor; eauto).
        ** eapply IHTREE2; eauto. pike_subset.
      * eapply tr_choice; eauto.
        ** eapply IHTREE2; eauto. pike_subset.
        ** eapply tr_begin; eauto.
           eapply tr_reset; eauto.
           eapply IHTREE1; eauto. pike_subset.
           repeat (econstructor; eauto).
    (* Unsupported *)
    + rewrite DUN in SUBSET. inversion SUBSET; subst.
      inversion H1; subst. inversion H0; subst; lia.
  (* group *)
  - remember (Areg (Group gid r1) :: cont) as groupcont.
    induction ACT; inversion Heqgroupcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_open; eauto.
    eapply IHTREE; eauto. pike_subset.
    repeat (econstructor; eauto).
  (* anchor *)
  - remember (Areg (Anchor a) :: cont) as anchorcont.
    induction ACT; inversion Heqanchorcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_anchor; eauto.
    eapply IHTREE; eauto. pike_subset.
  (* anchor fail *)
  - remember (Areg (Anchor a) :: cont) as charcont.
    induction ACT; inversion Heqcharcont; subst;
      try solve[eapply tr_jmp; eauto]; clear IHACT.
    invert_rep. inversion NFA; subst.
    2: { in_subset. }
    eapply tr_anchorfail; eauto.
Qed.


(** * Correctness of compilation with regards to tree_rep  *)

(* LATER: As a thought experiment, we could try to replace the invariant of the PikeVM, using actions_rep
   with an invariant that only uses tree_rep
   But to do so, we would need to initialize the invariant, and that would be more difficult than for actions_rep
*)

(* Theorem initialize_tree_rep: *)
(*   forall r inp t c endl, *)
(*     compile r 0 = (c, endl) -> *)
(*     bool_tree [Areg r] inp CanExit t -> *)
(*     tree_rep t c 0 inp CanExit. *)
(* Abort. *)


(** * Unicity of Memoized trees  *)

Lemma actions_rep_unicity:
  forall a1 a2 code pc t1 t2 inp b,
    pike_actions a1 ->
    pike_actions a2 ->
    actions_rep a1 code pc ->
    actions_rep a2 code pc ->
    bool_tree rer a1 inp b t1 ->
    bool_tree rer a2 inp b t2 ->
    t1 = t2.
Proof.
  intros. eapply actions_tree_rep in H1; eauto.
  eapply actions_tree_rep in H2; eauto.
  eapply tree_rep_determ; eauto.
Qed.

End TreeRep.
