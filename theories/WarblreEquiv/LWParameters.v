From Warblre Require Import Parameters Typeclasses RegExpRecord Patterns Result Errors.
From Linden Require Import Parameters Utils.
From Stdlib Require Import List.
Import ListNotations.
Import Result.Notations.
Import Utils.List.

Local Open Scope bool_scope.


(** * Instantiation of Warblre typeclasses String, *Marker and Parameters *)

Section LWParameters.
  Context {params: LindenParameters}.

  (** ** Strings *)
  Definition string := list Character.

  Definition string_eq_dec : forall (x y : string), { x = y } + { x <> y }.
  Proof.
    decide equality. apply Character.eq_dec.
  Defined.
  #[export] Instance string_EqDec: EqDec string := EqDec.make string string_eq_dec.

  (* Adapted from String.substring: returns the substring of s starting at index n and of length m (or less if the string is not long enough). *)
  Fixpoint substring (s: string) (n m: nat): string :=
    match n, m, s with
    | 0, 0, _ => nil
    | 0, S m', nil => s
    | 0, S m', c::s' => c::substring s' 0 m'
    | S n', _, nil => s
    | S n', _, c::s' => substring s' n' m
    end.

  Definition advanceStringIndex (s: string) (i: nat) := S i.
  Definition getStringIndex (s: string) (i: nat) := i.
  (* Linden strings are just lists of characters *)
  Definition to_char_list (s: string): list Character := s.

  #[export] Instance string_String: String.class Character := {|
    String.type := string;
    String.eqdec := string_EqDec;
    String.length := @List.length Character;
    String.substring := substring;
    String.advanceStringIndex := advanceStringIndex;
    String.getStringIndex := getStringIndex;
    String.to_char_list := to_char_list
  |}.



  (** ** Type markers *)
  #[export] Instance char_marker: CharacterMarker Character := mk_character_marker Character.

  #[export] Instance string_marker: StringMarker string := mk_string_marker string.

  #[export] Instance unicode_marker: UnicodePropertyMarker Property := mk_unicode_property_marker Property.


  (** ** Parameters class *)

  #[export] Instance LWParameters: Parameters := {|
      Parameters.character_class := char;

      Parameters.set_class := charset_class;
      Parameters.string_class := string_String;
      Parameters.unicode_property_class := unicodeProp;

      Parameters.character_marker := char_marker;
      Parameters.string_marker := string_marker;
      Parameters.unicode_property_marker := unicode_marker
    |}.
  

  (* Some lemmas *)
  (* Lemma contains_all:
    forall c, CharSet.contains Characters.all c = true.
  Proof.
    intro c. rewrite CharSet.contains_spec. unfold Characters.all. rewrite CharSet.from_list_spec. apply char_all_in.
  Qed. *)

  Lemma from_list_contains_inb: forall (c: Character) (l: list Character), CharSet.contains (CharSet.from_list l) c = List.inb c l.
  Proof.
    intros c l.
    apply <- Bool.eq_iff_eq_true. rewrite List.inb_spec. apply CharSet.from_list_contains.
  Qed.

End LWParameters.
