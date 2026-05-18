(** Entry point for the OCaml side of the app. *)

module WarbleParams = Warblre_js.JsEngineParameters.JsParameters
module StringLike = Warblre_js.JsEngineParameters.JsStringLike
module V = LindenAPI

(** Cast Warblre's extracted regex type to our own extraction of it. *)
let warblre_Regex_to_viz
    : ('c, 's, 'p) Warblre_js.Extracted.Patterns.coq_Regex ->
      ('c, 's, 'p) V.Patterns.coq_Regex
  = Obj.magic

type warble_regex =
  (WarbleParams.character, WarbleParams.string, WarbleParams.property)
    V.Patterns.coq_Regex

(** Parse a JavaScript regex. *)
let parseRegex (str : string) : warble_regex =
  let module Parser = Warblre_js.Parser.Parser (WarbleParams) (StringLike) in
  let str = if str = "" then "(?:)" else str in (* regexpp rejects // *)
  warblre_Regex_to_viz (Parser.parseRegex ("/" ^ str ^ "/"))

(** Format an exception. *)
let error_message (e : exn) : string =
  Option.bind (Js.Exn.asJsExn e) Js.Exn.message
  |> Option.value ~default:"invalid regex"

let linden_params : V.lindenParameters =
  let module JsEngine = Warblre_js.Engines.Engine (WarbleParams) in
  V.lindenParameters_of_warblre (Obj.magic JsEngine.parameters)

(** Compute a map from subregex to index in pre-order traversal. *)
let numberSubregexes (root : V.regex) : (V.regex * int) list =
  let counter = ref 0 in
  let idMap = ref [] in
  let rec go (r : V.regex) : unit =
    idMap := (r, !counter) :: !idMap;
    incr counter;
    match r with
    | V.Epsilon | V.Character _ | V.Anchor _ | V.Backreference _ -> ()
    | V.Disjunction0 (r1, r2) | V.Sequence (r1, r2) -> go r1; go r2
    | V.Quantified0 (_, _, _, r1)
    | V.Lookaround (_, r1)
    | V.Group0 (_, r1) -> go r1
  in
  go root;
  !idMap

(** Clear `target`. *)
let clear (target : Dom.element) : unit =
  Webapi.Dom.Element.setInnerHTML target ""

type result = [ `Ok of TreeConvert.node | `Error of string ]

(** Parse `pattern`, render it into `regexView`, and build the tree. *)
let run (pattern : string) (flags : V.Extraction.regex_flags)
      (input : string) (startIdx : int) (fuel : int)
      (regexView : Dom.element) (onHover : RegexRender.hover) : result =
  clear regexView;
  let go () =
    let regex =
      let wregex = parseRegex pattern |> Obj.magic in
      let parsed = V.Extraction.linden_regex_of_warblre_regex linden_params wregex in
      V.Extraction.maybe_add_lazy_prefix linden_params flags parsed in
    let chars =
      input |> StringLike.of_string
      |> WarbleParams.String.list_from_string
      |> Obj.magic in
    let startIdx = BigInt.of_int startIdx in
    let fuel = BigInt.of_int fuel in
    let idMap = numberSubregexes regex in
    RegexRender.render_regex regex regexView idMap onHover;
    match V.Extraction.tree_of_linden_regex linden_params regex flags chars startIdx fuel with
    | V.Extraction.TETree tree -> `Ok (TreeConvert.to_tree idMap input tree)
    | V.Extraction.TEOutOfFuel -> `Error "out of fuel"
    | V.Extraction.TEBadFlags -> `Error "unsupported regex flag" in
  try go ()
  with e -> `Error (error_message e)
