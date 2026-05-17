From Warblre Require Import Inst API Parameters RegExpRecord.
Import NaiveEngine.
From Linden Require Import Parameters.

(** * Instantiating the LindenParameters typeclass used in the development
using a naive instantiation of Warblre typeclasses *)

Instance character_class: Character.class := @Parameters.character_class parameters.

Lemma canonicalize_casesenst: forall rer chr, RegExpRecord.ignoreCase rer = false -> Character.canonicalize rer chr = chr.
Proof.
  intros rer chr Hcasesenst.
  unfold Character.canonicalize, character_class, Parameters.character_class, parameters, NaiveEngineParameters.Character.canonicalize.
  rewrite Hcasesenst. reflexivity.
Qed.

Instance naive_params: LindenParameters :=
  lindenParameters_of_warblre parameters canonicalize_casesenst.
