open Extracted

(** * Characters: OCaml [int]s, the code points of the ASCII alphabet (0-127) *)

module CharSet = Stdlib.Set.Make (Stdlib.Int)

module AsciiChar = struct
  let eq_dec = Int.equal

  let from_numeric_value (n : int) : int = n
  let numeric_value (c : int) : int = c

  (* ASCII case folding, as in Warblre's naive instantiation. *)
  let canonicalize (rer : RegExpRecord.RegExpRecord.coq_type) (c : int) : int =
    if rer.RegExpRecord.RegExpRecord.ignoreCase && Char.code 'A' <= c && c <= Char.code 'Z'
    then c + 32
    else c

  let range lo hi = Stdlib.List.init (hi - lo + 1) (fun i -> lo + i)

  let all = range 0 127
  let line_terminators = [ 0x0A; 0x0D ]
  let digits = range (Char.code '0') (Char.code '9')
  let white_spaces = [ 0x09; 0x0B; 0x0C; 0x20 ]
  let ascii_word_characters =
    range (Char.code 'A') (Char.code 'Z')
    @ range (Char.code 'a') (Char.code 'z')
    @ digits @ [ Char.code '_' ]
end

module AsciiCharSet = struct
  let contains s c = CharSet.mem c s
  let range lo hi = CharSet.of_list (AsciiChar.range lo hi)

  (* The first argument is the erased error type, the second the error to return *)
  let unique _ err s =
    if CharSet.cardinal s = 1 then Result.Success (CharSet.choose s)
    else Result.Error err

  let filter s f = CharSet.filter f s
  let exist s f = CharSet.exists f s

  let exist_canonicalized rer s c =
    CharSet.exists (fun c' -> AsciiChar.canonicalize rer c' = c) s
end

(** * Instantiating the Linden parameters *)

let character_class : Parameters.Character.coq_class =
  let open Parameters.Character in
  {
    eq_dec = Obj.magic AsciiChar.eq_dec;
    from_numeric_value = Obj.magic AsciiChar.from_numeric_value;
    numeric_value = Obj.magic AsciiChar.numeric_value;
    canonicalize = Obj.magic AsciiChar.canonicalize;
    all = Obj.magic AsciiChar.all;
    line_terminators = Obj.magic AsciiChar.line_terminators;
    digits = Obj.magic AsciiChar.digits;
    white_spaces = Obj.magic AsciiChar.white_spaces;
    ascii_word_characters = Obj.magic AsciiChar.ascii_word_characters;
  }

let charset_class : Parameters.CharSet.coq_class =
  let open Parameters.CharSet in
  {
    empty = Obj.repr CharSet.empty;
    from_list = Obj.magic CharSet.of_list;
    union = Obj.magic CharSet.union;
    singleton = Obj.magic CharSet.singleton;
    size = Obj.magic CharSet.cardinal;
    remove_all = Obj.magic CharSet.diff;
    is_empty = Obj.magic CharSet.is_empty;
    elements = Obj.magic CharSet.elements;
    contains = Obj.magic AsciiCharSet.contains;
    range = Obj.magic AsciiCharSet.range;
    unique = Obj.magic AsciiCharSet.unique;
    filter = Obj.magic AsciiCharSet.filter;
    exist = Obj.magic AsciiCharSet.exist;
    exist_canonicalized = Obj.magic AsciiCharSet.exist_canonicalized;
  }

(* No Unicode properties: the property type is [unit] and matches no character *)
let property_class : Parameters.Character.coq_type Parameters.Property.coq_class =
  {
    Parameters.Property.unicode_property_eqdec = Obj.magic (fun () () -> true);
    code_points_for = (fun _ -> []);
  }

let params : Parameters0.coq_LindenParameters =
  {
    Parameters0.char = character_class;
    unicodeProp = property_class;
    charset_class;
  }

(** * Sets of seen pcs, as OCaml sets of (label, LoopBool) pairs *)
(* We could instead extract the verified list implementation, but this is a more natural representation *)

module SeenSet = Stdlib.Set.Make (struct
  type t = int * BooleanSemantics.coq_LoopBool
  let compare = compare
end)

let vmseen : SeenSets.coq_VMSeen =
  {
    SeenSets.initial_seenpcs = Obj.repr SeenSet.empty;
    add_seenpcs = (fun s pc b -> Obj.repr (SeenSet.add (pc, b) (Obj.obj s)));
    inseenpc = (fun s pc b -> SeenSet.mem (pc, b) (Obj.obj s));
  }

(** * Printing *)

(* Results are printed as in RegElk: one line #i:<slice> per capture group *)

(* The slice of [str] between two indices.
   Groups defined in lookbehinds have their indices reversed. *)
let slice (str : string) (i : int) (j : int) : string =
  Stdlib.String.sub str (min i j) (abs (j - i))

let string_of_range (str : string) (r : Groups.GroupMap.range option) : string =
  match r with
  | Some { startIdx; endIdx = Some endIdx } -> slice str startIdx endIdx
  | _ -> "Undefined"

(* Group 0 is the entire match: matches start at index 0 and end at [end_idx] *)
let print_groups (str : string) (max_group : int) (end_idx : int) (gm : Groups.GroupMap.t) : unit =
  Printf.printf "#0:%s\n" (slice str 0 end_idx);
  for i = 1 to max_group do
    Printf.printf "#%d:%s\n" i (string_of_range str (Groups.GroupMap.find i gm))
  done

(** * Running the engine *)

let coq_of_char (c : char) : Parameters.Character.coq_type =
  if Char.code c > 127 then invalid_arg "coq_of_char: not an ASCII character";
  Obj.repr (Char.code c)

let chars_of_string (s : string) : Parameters.Character.coq_type list =
  Stdlib.List.map coq_of_char (Stdlib.List.of_seq (Stdlib.String.to_seq s))

(* Building RER of a regex, with all flags off *)
let rer_of (r : Regex.regex) : RegExpRecord.RegExpRecord.coq_type =
  {
    RegExpRecord.RegExpRecord.ignoreCase = false;
    multiline = false;
    dotAll = false;
    unicode = ();
    capturingGroupsCount = Regex.max_group params r;
  }

(* Runs the PikeVM with [regex] on [str] and prints the result *)
let run (regex : Regex.regex) (str : string) : unit =
  if not (PikeSubset.is_pike_regex params regex) then
    prerr_endline "Error: unsupported by the PikeVM"
  else
  let input = Chars.Input (chars_of_string str, []) in
  let rer = rer_of regex in
  match FunctionalPikeVM.pike_vm_match params vmseen rer regex input with
  | FunctionalPikeVM.OutOfFuel -> print_endline "Out of fuel"
  | Finished None -> print_endline "NoMatch"
  | Finished (Some (inp, gm)) -> print_groups str rer.capturingGroupsCount (Chars.idx params inp) gm

(** * Asking the user for a regex and a string *)

let read_input (prompt : string) : string option =
  print_string prompt;
  flush stdout;
  try Some (read_line ()) with End_of_file -> None

let () =
  match read_input "Regex: " with
  | None -> print_endline "\nEnd of input, no regex given"
  | Some re ->
    match Parser.Parse.parse coq_of_char re with
    | exception Parser.Parse.Parse_error msg -> prerr_endline ("Error: cannot parse the regex: " ^ msg)
    | exception Invalid_argument _ -> prerr_endline "Error: the regex should be ASCII"
    | regex ->
      match read_input "Input string: " with
      | None -> print_endline "\nNo string given"
      | Some str ->
        try run regex str
        with Invalid_argument _ -> prerr_endline "Error: the input should be ASCII"
