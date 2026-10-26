From Warblre Require Import Inst API Parameters RegExpRecord.
Import NaiveEngine.
From Linden Require Import Parameters.

(** * Instantiating the LindenParameters typeclass used in the development
using a naive instantiation of Warblre typeclasses *)

Instance character_class: Character.class := @Parameters.character_class parameters.

Instance naive_params: LindenParameters :=
  lindenParameters_of_warblre parameters.
