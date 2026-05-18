(** Render a regex as a DOM tree. *)

module V = LindenAPI

(** Pretty-printing: regex pieces to their display strings. *)
module Pp = struct
  (** Quote a single character. *)
  let char_text (c : V.Character.coq_type) : string =
    let c : Js.String.t = Obj.magic c in
    let json = Js.Json.stringify (Js.Json.string c) in
    String.sub json 1 (String.length json - 2)

  let anchor_text : V.anchor -> string = function
    | V.BeginInput -> "^"
    | V.EndInput -> "$"
    | V.WordBoundary0 -> "\\b"
    | V.NonWordBoundary -> "\\B"

  let rec cd_text : V.char_descr -> string = function
    | V.CdEmpty -> "[]"
    | V.CdDot -> "."
    | V.CdAll -> {js|·|js}
    | V.CdSingle c -> char_text c
    | V.CdDigits -> "\\d"
    | V.CdNonDigits -> "\\D"
    | V.CdWhitespace -> "\\s"
    | V.CdNonWhitespace -> "\\S"
    | V.CdWordChar -> "\\w"
    | V.CdNonWordChar -> "\\W"
    | V.CdRange (a, b) -> char_text a ^ "-" ^ char_text b
    (* this engine has no \p{} support: its property type is uninhabited,
       so these two arms are unreachable *)
    | V.CdUnicodeProp _ -> "\\p"
    | V.CdNonUnicodeProp _ -> "\\P"
    | V.CdUnion _ as cd -> "[" ^ class_body cd ^ "]"
    | V.CdInv cd -> "[^" ^ class_body cd ^ "]"

  and class_body : V.char_descr -> string = function
    | V.CdUnion (a, b) -> cd_text a ^ class_body b
    | V.CdEmpty -> ""
    | cd -> cd_text cd

  let quant_suffix greedy (mn : BigInt.t) (delta : V.NoI.non_neg_integer_or_inf) : string =
    let mn = BigInt.to_int mn in
    let delta = match delta with
      | V.NoI.Inf -> None
      | V.NoI.N d -> Some (BigInt.to_int d) in
    let base = match mn, delta with
      | 0, None -> "*"
      | 1, None -> "+"
      | 0, Some 1 -> "?"
      | _, None -> "{" ^ string_of_int mn ^ ",}"
      | _, Some 0 -> "{" ^ string_of_int mn ^ "}"
      | _, Some d -> "{" ^ string_of_int mn ^ "," ^ string_of_int (mn + d) ^ "}" in
    let suffix = if greedy then "" else "?" in
    base ^ suffix

  let lk_marker : V.lookaround -> string = function
    | V.LookAhead -> "="
    | V.NegLookAhead -> "!"
    | V.LookBehind -> "<="
    | V.NegLookBehind -> "<!"
end

module D = Webapi.Dom

(** DOM element builders. *)
module Html = struct
  (** Append a text node carrying `t` to `parent`. *)
  let text (parent : Dom.element) (t : string) : unit =
    D.Element.appendChild (D.Document.createTextNode t D.document) parent

  (** Build an element: a `tag`, an optional class, attributes and text. *)
  let el ?cls ?(attrs = []) ?txt (tag : string) : Dom.element =
    let e = D.Document.createElement tag D.document in
    Option.iter (D.Element.setClassName e) cls;
    List.iter (fun (k, v) -> D.Element.setAttribute k v e) attrs;
    Option.iter (text e) txt;
    e

  let rx_span (id : int) : Dom.element =
    el "span" ~cls:"rx" ~attrs:[ ("data-regex-id", string_of_int id) ]

  let subscript (parent : Dom.element) (t : string) : unit =
    D.Element.appendChild (el "sub" ~txt:t) parent
end

(** Precedence: whether a subregex must be parenthesised. *)
module Prec = struct
  let levelOf : V.regex -> int = function
    | V.Disjunction0 _ -> 0
    | V.Sequence _ -> 1
    | V.Quantified0 _ -> 2
    | _ -> 3

  (** Whether `child` needs a (?:…) wrapper inside `parent`. *)
  let needs_parens ~strict (parent : V.regex) (child : V.regex) : bool =
    match parent with
    | V.Sequence _ | V.Disjunction0 _ | V.Quantified0 _ ->
      if strict then levelOf child <= levelOf parent
      else levelOf child < levelOf parent
    | _ -> false
end

type hover = first:int -> last:int -> Dom.mouseEvent -> unit

(** Render `root` into `target`.

    `idMap` is used to retrieve the IDs of subregexes; onHover is bound to each
    generated span. *)
let render_regex (root : V.regex) (target : Dom.element)
    (idMap : (V.regex * int) list) (onHover : hover) : unit =
  let open Pp in
  let open Html in
  let lastId = ref 0 in
  (* render `r` into a fresh .rx span -- parenthesised when `wrap` -- and
     append that span to `parent` *)
  let rec render_subregex ~wrap (r : V.regex) (parent : Dom.element) : unit =
    let firstId = List.assq r idMap in
    lastId := firstId;
    let span = rx_span firstId in
    if wrap then text span {js|⟨|js};
    render_into span r;
    if wrap then text span {js|⟩|js};
    D.Element.addMouseOverEventListener
      (let lastId = !lastId in
       fun e -> onHover ~first:firstId ~last:lastId e)
      span;
    D.Element.appendChild span parent
  (* write `r`'s rendering into `span`, recursing through render_subregex *)
  and render_into (span : Dom.element) (r : V.regex) : unit =
    let txt = text span in
    let nested ~strict r1 =
      render_subregex ~wrap:(Prec.needs_parens ~strict r r1) r1 span in
    match r with
    | V.Epsilon -> txt {js|𝜀|js}
    | V.Character cd -> txt (cd_text cd)
    | V.Anchor a -> txt (anchor_text a)
    | V.Backreference g -> txt ("\\" ^ BigInt.to_string g)
    | V.Sequence (r1, r2) -> nested ~strict:false r1; nested ~strict:true r2
    | V.Disjunction0 (r1, r2) ->
      nested ~strict:false r1; txt "|"; nested ~strict:true r2
    | V.Quantified0 (greedy, mn, delta, r1) ->
      nested ~strict:true r1; txt (quant_suffix greedy mn delta)
    | V.Group0 (gid, r1) ->
      txt "("; subscript span (BigInt.to_string gid);
      nested ~strict:false r1; txt ")"
    | V.Lookaround (lk, r1) ->
      txt ("(?" ^ lk_marker lk); nested ~strict:false r1; txt ")"
  in
  render_subregex ~wrap:false root target
