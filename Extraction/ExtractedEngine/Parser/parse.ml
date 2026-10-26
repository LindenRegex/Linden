(** * Parsing strings into Linden regexes *)
(* The translation follows the one from Warblre regexes in
   theories/WarblreEquiv/RegexpTranslation.v *)

open Extracted

exception Parse_error of string

(** * Converting raw regexes to Linden regexes *)

let cd_of_group : Raw.char_group -> Chars.char_descr = function
  | Digit -> CdDigits
  | NonDigit -> CdNonDigits
  | Word -> CdWordChar
  | NonWord -> CdNonWordChar
  | Space -> CdWhitespace
  | NonSpace -> CdNonWhitespace

(* [coq_of_char] gives the representation of characters used by the engine *)
let cd_of_range coq_of_char (l : char) (h : char) : Chars.char_descr =
  if l > h then raise (Parse_error (Printf.sprintf "range out of order: %C-%C" l h));
  CdRange (coq_of_char l, coq_of_char h)

let rec cd_of_class coq_of_char (c : Raw.char_class) : Chars.char_descr =
  match c with
  | [] -> CdEmpty
  | [ CRange (l, h) ] -> cd_of_range coq_of_char l h
  | CRange (l, h) :: c' -> CdUnion (cd_of_range coq_of_char l h, cd_of_class coq_of_char c')
  | CChar x :: c' -> CdUnion (CdSingle (coq_of_char x), cd_of_class coq_of_char c')
  | CGroup g :: c' -> CdUnion (cd_of_group g, cd_of_class coq_of_char c')

let cd_of_character coq_of_char : Raw.character -> Chars.char_descr = function
  | Char x -> CdSingle (coq_of_char x)
  | Dot -> CdDot
  | Group g -> cd_of_group g
  | Class c -> cd_of_class coq_of_char c
  | NegClass c -> CdInv (cd_of_class coq_of_char c)

let lookaround_of_raw : Raw.lookaround -> Regex.lookaround = function
  | Lookahead -> LookAhead
  | NegLookahead -> NegLookAhead
  | Lookbehind -> LookBehind
  | NegLookbehind -> NegLookBehind

let anchor_of_raw : Raw.anchor -> Regex.anchor = function
  | BeginInput -> BeginInput
  | EndInput -> EndInput
  | WordBoundary -> WordBoundary
  | NonWordBoundary -> NonWordBoundary

(* Capture groups are numbered from 1, in the order of their opening parenthesis *)
let to_regex coq_of_char (r : Raw.raw_regex) : Regex.regex =
  let next_group = ref 1 in
  let rec convert (r : Raw.raw_regex) : Regex.regex =
    match r with
    | Raw_empty -> Epsilon
    | Raw_character c -> Character (cd_of_character coq_of_char c)
    | Raw_alt (r1, r2) ->
      let r1 = convert r1 in
      let r2 = convert r2 in
      Disjunction (r1, r2)
    | Raw_con (r1, r2) ->
      let r1 = convert r1 in
      let r2 = convert r2 in
      Sequence (r1, r2)
    | Raw_quant ({ min; max; greedy }, r1) ->
      let delta : Numeric.NoI.non_neg_integer_or_inf =
        match max with
        | None -> Inf
        | Some max when max < min ->
          raise (Parse_error (Printf.sprintf "numbers out of order in {%d,%d} quantifier" min max))
        | Some max -> N (max - min)
      in
      Quantified (greedy, min, delta, convert r1)
    | Raw_capture r1 ->
      let id = !next_group in
      incr next_group;
      Group (id, convert r1)
    | Raw_lookaround (lk, r1) -> Lookaround (lookaround_of_raw lk, convert r1)
    | Raw_anchor a -> Anchor (anchor_of_raw a)
    | Raw_backref n -> Backreference n
  in
  convert r

(** * Parsing *)

let raw_of_string (s : string) : Raw.raw_regex =
  let lexbuf = Lexing.from_string s in
  try Regex_parser.main Regex_lexer.token lexbuf with
  | Regex_parser.Error ->
    raise (Parse_error (Printf.sprintf "syntax error at position %d" (Lexing.lexeme_start lexbuf)))
  | Raw.Unsupported feature -> raise (Parse_error ("unsupported feature: " ^ feature))

(* Parses [s] into a Linden regex, using [coq_of_char] to represent characters *)
let parse (coq_of_char : char -> Parameters.Character.coq_type) (s : string) : Regex.regex =
  to_regex coq_of_char (raw_of_string s)
