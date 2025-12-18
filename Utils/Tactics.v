Require Import Coq.Bool.Bool.

From Warblre Require Import Base.

(* Tactic for rewriting decidable equalities into propositional ones *)
Ltac eqdec := repeat match goal with
  | [ H: (?x ==? ?y)%wt = true |- _ ] => rewrite EqDec.inversion_true in H; subst
  | [ H: (?x ==? ?y)%wt = false |- _ ] => rewrite EqDec.inversion_false in H
  | [ |- context[(?x ==? ?y)%wt] ] => destruct (x ==? y)%wt eqn:?Heq
  | [ H: context[(?x ==? ?y)%wt] |- _ ] => destruct (x ==? y)%wt eqn:?Heq
end.

(* A tactic that turns boolean operators into propositional ones *)
Ltac boolprop := repeat match goal with
  | [ H: context[(?b1 && ?b2 = true)] |- _ ] => rewrite andb_true_iff in H
  | [ H: context[(?b1 && ?b2 = false)] |- _ ] => rewrite andb_false_iff in H
  | [ H: context[(?b1 || ?b2 = true)] |- _ ] => rewrite orb_true_iff in H
  | [ H: context[(?b1 || ?b2 = false)] |- _ ] => rewrite orb_false_iff in H
  | [ H: context[negb ?b1 = ?b2] |- _ ] => rewrite negb_true_iff in H || rewrite negb_false_iff in H
  | [ |- context[(?b1 && ?b2 = true)] ] => rewrite andb_true_iff
  | [ |- context[(?b1 && ?b2 = false)] ] => rewrite andb_false_iff
  | [ |- context[(?b1 || ?b2 = true)] ] => rewrite orb_true_iff
  | [ |- context[(?b1 || ?b2 = false)] ] => rewrite orb_false_iff
  | [ |- context[negb ?b1 = ?b2] ] => rewrite negb_true_iff || rewrite negb_false_iff

  (* split goals *)
  | [ H: (?p1 /\ ?p2) |- _ ] => destruct H
  | [ H: (?p1 \/ ?p2) |- _ ] => destruct H
end.

(* A tactic that, when given a hypothesis H: P -> Q, asks to prove P in one branch (running tactic tac first) and specializes H with the proven property in the other branch. *)
Ltac specialize_prove_impl H tac :=
  lazymatch type of H with
  | ?A -> ?B =>
      let Hint := fresh in
      assert A as Hint; [tac|specialize (H Hint); clear Hint]
  end.

Tactic Notation "specialize_prove" constr(H) := specialize_prove_impl H idtac.
Tactic Notation "specialize_prove" constr(H) "by" tactic1(tac) := specialize_prove_impl H tac.
