From Warblre Require Import Parameters RegExpRecord.
From Stdlib Require Import List.

(** * Typeclass containing parameters which our development depends on *)

Class LindenParameters := make {
  (* Three Warblre typeclasses, specifying: *)
  #[global] char:: Character.class; (* a type of characters, *)
  #[global] unicodeProp:: Parameters.Property.class (@Parameters.Character char); (* a type of Unicode properties, *)
  #[global] charset_class:: @CharSet.class char; (* and a type of character sets. *)

  (* As per the ECMA specification (22.2.2.7.3 Canonicalize ( rer, ch )), when we do not ignore case, canonicalization is the identity function. *)
  canonicalize_casesenst: forall rer chr, RegExpRecord.ignoreCase rer = false -> Character.canonicalize rer chr = chr;
}.