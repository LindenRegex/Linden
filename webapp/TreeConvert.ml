(** Conversion from Linden's tree type to graphs. *)

module V = LindenAPI
module A = LindenAPI.AnnotatedTrees
module GM = LindenAPI.GroupMap
module R = RegexRender

(** * Regex ID checks

    The matching process annotates tree nodes with actions that contains
    subregexes of the original regex, so we can find where an action came from
    by matching its regex against subregexes of the original one. *)

(** Check whether an `action` physically matches a specific `regex`. *)
let same (action : V.action) (regex : V.regex) : bool =
  match action, regex with
  | V.Areg (V.Quantified0 (_, _, _, lb)), V.Quantified0 (_, _, _, rb) -> lb == rb
  | V.Aclose gid, V.Group0 (g, _) -> BigInt.equal g gid
  | V.Areg ar, _ -> ar == regex
  | _ -> false

(** Compute the id of the first regex in `acts`. *)
let rec regex_id_of (idMap : (V.regex * int) list) (acts : V.actions)
    : int Js.Nullable.t =
  match acts with
  | [] -> Js.Nullable.null
  | V.Acheck _ :: rest -> regex_id_of idMap rest
  | a :: _ -> List.find_opt (fun (r, _) -> same a r) idMap
              |> Option.map snd |> Js.Nullable.fromOption

(** * Pretty-printing *)

let quote_char s = {js|‘|js} ^ s ^ {js|’|js}
let quote_str s = {js|“|js} ^ s ^ {js|”|js}
let matched : [ `Match | `Mismatch ] Js.Nullable.t = Js.Nullable.return `Match
let mismatched : [ `Match | `Mismatch ] Js.Nullable.t = Js.Nullable.return `Mismatch

let dir_str : V.direction -> string = function
  | V.Forward -> "Forward"
  | V.Backward -> "Backward"

(** Compute the label of a lookaround node *)
let lk_name : V.lookaround -> string = function
  | V.LookAhead -> "LookAhead"
  | V.LookBehind -> "LookBehind"
  | V.NegLookAhead -> "NegLookAhead"
  | V.NegLookBehind -> "NegLookBehind"

(** Compute the label of a group node *)
let group_label : V.groupaction -> string * string = function
  | V.Open g -> ("Open", BigInt.to_string g)
  | V.Close g -> ("Close", BigInt.to_string g)
  | V.Reset gs -> ("Reset", "{" ^ String.concat ", " (List.map BigInt.to_string gs) ^ "}")

(** Compute the label of a mismatch node *)
let fail_label : V.actions -> string * string = function
  | V.Acheck _ :: _ -> ("Progress", "")
  | V.Areg (V.Character cd) :: _ -> ("Read ", R.Pp.cd_text cd)
  | V.Areg (V.Anchor a) :: _ -> ("Anchor ", R.Pp.anchor_text a)
  | V.Areg (V.Backreference g) :: _ -> ("BackRef ", "\\" ^ BigInt.to_string g)
  | _ -> assert false

(** * Conversion *)

(** See `globals.d.ts` for documentation. *)
type group_state = { id : int; startIdx : int; endIdx : int Js.Nullable.t }
type engine_state = { idx : int; dir : string; groups : group_state array }
type node = {
  name : string;
  arg : string;
  result : [ `Match | `Mismatch ] Js.Nullable.t;
  hasGhostSubtree : bool;
  regexId : int Js.Nullable.t;
  pre : engine_state Js.Nullable.t;
  post : engine_state Js.Nullable.t;
  children : node array;
}

let state_js (a : A.annotation) : engine_state =
  let (V.Input (_, pref)) = a.A.inp in
  let group (id, (r : GM.range)) : group_state =
    { id = id |> BigInt.to_int;
      startIdx = r.GM.startIdx |> BigInt.to_int;
      endIdx = r.GM.endIdx |> Option.map BigInt.to_int |> Js.Nullable.fromOption } in
  { idx = List.length pref;
    dir = a.A.dir |> dir_str;
    groups = GM.MapS.this a.A.gm |> List.map group |> Array.of_list }

(** Remove layers of redundant annotations. *)
let rec unwrap (default : A.annotation) : A.tree -> A.annotation * A.tree = function
  | A.Annot (a, t) -> unwrap a t
  | bare -> (default, bare)

(** Convert an annotated tree. *)
let rec to_node (idMap : (V.regex * int) list) (default : A.annotation) (t : A.tree) : node =
  let ann, tree_node = unwrap default t in
  let pre = Js.Nullable.return (state_js ann) in
  let regex_id = regex_id_of idMap ann.A.acts in
  let make ?(result = Js.Nullable.null) ?(ghost = false) name arg subjs : node =
    let children = List.map (to_node idMap ann) subjs in
    let post = match children with
      | f :: _ -> f.pre
      | [] -> Js.Nullable.null in
    { name; arg; result; hasGhostSubtree = ghost; regexId = regex_id; pre; post;
      children = Array.of_list children } in
  match tree_node with
  | A.Mismatch ->
    let name, arg = fail_label ann.A.acts in
    make ~result:mismatched name arg []
  | A.Match ->
     make ~result:matched "Match" "" []
  | A.Choice (a, b) ->
     make "Choice" "" [ a; b ]
  | A.Progress c ->
     make "Progress" "" [ c ]
  | A.Read (ch, c) ->
     make "Read " (quote_char (R.Pp.char_text ch)) [ c ]
  | A.ReadBackRef (s, c) ->
    let text = String.concat "" (List.map R.Pp.char_text s) in
    make "BackRef " (quote_str text) [ c ]
  | A.AnchorPass (a, c) ->
     make "Anchor " (R.Pp.anchor_text a) [ c ]
  | A.GroupAction (g, c) ->
    let op, arg = group_label g in
    make (op ^ " ") arg [ c ]
  | A.LK (lk, tlk, c) ->
     make ~ghost:true (lk_name lk) "" [ tlk; c ]
  | A.LKFail (lk, tlk) ->
    make ~ghost:true ~result:mismatched (lk_name lk) "" [ tlk ]
  | A.Annot _ ->
     assert false

(** Entry point. *)
let to_tree (idMap : (V.regex * int) list) : A.tree -> node = function
  | A.Annot (root, _) as t -> to_node idMap root t
  | _ -> assert false
