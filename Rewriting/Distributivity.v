From Linden.Rewriting Require Import ProofSetup.

(** * Distributivity of sequence over disjunction *)
(* This distributivity is only valid in one direction depending on whether we
distribute on the right or on the left. *)

Module Right.
  Section EquivalenceProof.
    Context {params: LindenParameters}.
    Context (rer: RegExpRecord).

    Context (x0 x1 y: regex).
    Context (NO_GROUPS_IN_Y: def_groups y = []).

    Definition factored: regex :=
      Sequence (Disjunction x0 x1) y.

    Definition expanded: regex :=
      Disjunction (Sequence x0 y) (Sequence x1 y).

    Hint Rewrite NO_GROUPS_IN_Y : tree_equiv.

    Theorem factored_expanded_right_equiv: (* Proof using inversion on the is_tree predicate *)
      factored ≅[rer][forward] expanded.
    Proof.
      tree_equiv_inv; eauto using compute_tr_is_tree.
      reflexivity.
    Qed.

    Theorem factored_expanded_right_equiv_symb: (* Proof using symbolic evaluation *)
      factored ≅[rer][forward] expanded.
    Proof.
      tree_equiv_rw.
      compute_tr_simpl.
      reflexivity.
    Qed.
  End EquivalenceProof.
End Right.

Module LeftBackward.
  Section EquivalenceProof.
    Context {params: LindenParameters}.
    Context (rer: RegExpRecord).

    Context (x y0 y1: regex).
    Context (NO_GROUPS_IN_X: def_groups x = []).

    Definition factored: regex :=
      Sequence x (Disjunction y0 y1).

    Definition expanded: regex :=
      Disjunction (Sequence x y0) (Sequence x y1).

    Hint Rewrite NO_GROUPS_IN_X : tree_equiv.

    Theorem factored_expanded_left_equiv: (* Proof using inversion on the is_tree predicate *)
      factored ≅[rer][backward] expanded.
    Proof.
      tree_equiv_inv; eauto using compute_tr_is_tree.
      reflexivity.
    Qed.

    Theorem factored_expanded_left_equiv_symb: (* Proof using symbolic evaluation *)
      factored ≅[rer][backward] expanded.
    Proof.
      tree_equiv_rw.
      compute_tr_simpl.
      reflexivity.
    Qed.
  End EquivalenceProof.
End LeftBackward.

Module LeftForward.
  Section Counterexample.
    Context {params: LindenParameters}.
    Context (rer: RegExpRecord).
    Context (c: Parameters.Character).

    Let capture n := Group n (Character (CdSingle c)).

    Definition x := Disjunction (capture 1) Epsilon.
    Definition y0 := capture 2.
    Definition y1 := Epsilon.

    Definition factored: regex :=
      Sequence x (Disjunction y0 y1).

    Definition expanded: regex :=
      Disjunction (Sequence x y0) (Sequence x y1).

    Definition input := init_input [c].

    Arguments char_match {params} rer c !cd /.

    Theorem factored_expanded_left_nequiv:
      factored ≇[rer] expanded.
    Proof.
      tree_equiv_rw.
      exists forward, input, GroupMap.empty.
      compute_tr_cbv.
      inversion 1.
    Qed.
  End Counterexample.
End LeftForward.
