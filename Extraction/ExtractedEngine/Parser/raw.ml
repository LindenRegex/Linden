(** * Raw regexes, as produced by the parser *)
(* Adapted from RegElk (https://github.com/LindenRegex/RegElk).
   Capture groups are not numbered yet: this is done when converting to Linden regexes. *)

exception Unsupported of string

(** * Characters *)

(* \d \D \w \W \s \S *)
type char_group =
  | Digit
  | NonDigit
  | Word
  | NonWord
  | Space
  | NonSpace

type char_class_elt =
  | CChar of char
  | CRange of char * char       (* e.g. "a-e" *)
  | CGroup of char_group        (* e.g. "\w" *)

(* the contents of [] or [^] *)
type char_class = char_class_elt list

type character =
  | Char of char
  | Dot
  | Group of char_group
  | Class of char_class
  | NegClass of char_class

(* What happens when two class elements are separated with a dash?
   If both are characters, it is a range.
   Otherwise, the dash is interpreted as a '-' character. *)
let make_range (e1 : char_class_elt) (e2 : char_class_elt) : char_class =
  match e1, e2 with
  | CChar c1, CChar c2 -> [CRange (c1, c2)]
  | _, _ -> [e1; CChar '-'; e2]

(** * Regexes *)

(* None represents infinity *)
type quantifier = {
    min : int;
    max : int option;
    greedy : bool;
  }

type lookaround =
  | Lookahead
  | NegLookahead
  | Lookbehind
  | NegLookbehind

type anchor =
  | BeginInput
  | EndInput
  | WordBoundary
  | NonWordBoundary

type raw_regex =
  | Raw_empty
  | Raw_character of character
  | Raw_alt of raw_regex * raw_regex
  | Raw_con of raw_regex * raw_regex
  | Raw_quant of quantifier * raw_regex
  | Raw_capture of raw_regex
  | Raw_lookaround of lookaround * raw_regex
  | Raw_anchor of anchor
  | Raw_backref of int
