From Warblre Require Import Parameters RegExpRecord.
From Stdlib Require Import List.

(** * Typeclass containing parameters which our development depends on *)

Class LindenParameters := make {
  (* Three Warblre typeclasses, specifying: *)
  #[global] char:: Character.class; (* a type of characters, *)
  #[global] unicodeProp:: Parameters.Property.class (@Parameters.Character char); (* a type of Unicode properties, *)
  #[global] charset_class:: @CharSet.class char; (* and a type of character sets. *)
}.

Section OfWarblre.
  Context (p: Parameters).

  Definition lindenParameters_of_warblre : LindenParameters :=
    make
      (@Parameters.character_class p)
      (@Parameters.unicode_property_class p)
      (@Parameters.set_class p).

End OfWarblre.
