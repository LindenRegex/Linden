(** Conversion from Linden's tree type to graphs. *)

module V = LindenAPI
module A = LindenAPI.AnnotatedTrees
module GM = LindenAPI.GroupMap
module R = RegexRender

let debug = false

(** * Regex ID checks

    The matching process annotates tree nodes with actions that contains
    subregexes of the original regex, so we can find where an action came from
    by matching its regex against subregexes of the original one. *)

(** Check whether an `action` physically matches a specific `regex`. *)
let same (action : V.action) (regex : V.regex) : bool =
  match action, regex with
  | V.Areg (V.Quantified0 (_, _, _, lb)), V.Quantified0 (_, _, _, rb) -> lb == rb
  | V.Aclose gid, V.Group0 (g, _) -> BigInt.equal g gid
  | V.Areg ar, r -> ar == r
  | _ -> false

(** Compute the id of the first regex in `acts`. *)
let rec regex_id_of (idMap : (V.regex * int) list) (acts : V.actions) : int option =
  match acts with
  | [] -> None
  | V.Acheck _ :: rest -> regex_id_of idMap rest
  | a :: _ -> List.find_opt (fun (r, _) -> same a r) idMap |> Option.map snd

(** * Redundancy checks *)

let same_regex (r0 : V.regex) (r1 : V.regex) : bool =
  match r0, r1 with
  | V.Quantified0 (lg, lm, ld, lb), V.Quantified0 (rg, rm, rd, rb) ->
     lg = rg && lm = rm && ld = rd && lb == rb
  | _, _ -> r0 == r1

let same_action (a0 : V.action) (a1 : V.action) : bool =
  match a0, a1 with
  | V.Areg r0, V.Areg r1 -> same_regex r0 r1
  | V.Aclose g0, V.Aclose g1 -> BigInt.equal g0 g1
  | V.Acheck i0, V.Acheck i1 -> i0 = i1
  | _, _ -> false

let rec same_actions (acts0 : V.actions) (acts1 : V.actions) : bool =
  match acts0, acts1 with
  | [], [] -> true
  | a0 :: r0, a1 :: r1 -> same_action a0 a1 && same_actions r0 r1
  | _, _ -> false

let same_match_state (idx, dir, acts) (idx', dir', acts') =
  idx = idx' && dir = dir' && same_actions acts acts'

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
type engine_state = { idx : int ; input : string ; dir : string; groups : group_state array }
type node = {
  name : string;
  arg : string;
  result : [ `Match | `Mismatch ] Js.Nullable.t;
  ghostDepth : int;
  hasGhostSubtree : bool;
  regexId : int Js.Nullable.t;
  redundant : bool;
  pre : engine_state;
  post : engine_state Js.Nullable.t;
  children : node array;
}

let state_js (input : string) (a : A.annotation) : engine_state =
  let (V.Input (suffix, prefix)) = a.A.inp in
  let group (id, (r : GM.range)) : group_state =
    { id = id |> BigInt.to_int;
      startIdx = r.GM.startIdx |> BigInt.to_int;
      endIdx = r.GM.endIdx |> Option.map BigInt.to_int |> Js.Nullable.fromOption } in
  let assert_same_input () =
    let module StringLike = Warblre_js.JsEngineParameters.JsStringLike in
    let module WarbleParams = Warblre_js.JsEngineParameters.JsParameters in
    let str (s: 'a list) = s |> Obj.magic |> WarbleParams.String.list_to_string |> StringLike.to_string in
    if debug then assert (str (List.rev prefix) ^ str suffix = input) in
  assert_same_input ();
  { idx = List.length prefix;
    input; dir = a.A.dir |> dir_str;
    groups = GM.MapS.this a.A.gm |> List.map group |> Array.of_list }

(** Remove layers of redundant annotations. *)
let rec unwrap (default : A.annotation) : A.tree -> A.annotation * A.tree = function
  | A.Annot (a, t) -> unwrap a t
  | bare -> (default, bare)

(** Record this match state in `seen` and return whether it was already there. *)
let check_seen (seen : (int * string * V.actions) list ref)
      (acts : V.actions) (pre : engine_state) : bool =
  let key = (pre.idx, pre.dir, acts) in
  let was_seen = List.exists (same_match_state key) !seen in
  if not was_seen then seen := key :: !seen;
  was_seen

(** Convert an annotated tree. *)
let rec to_node (idMap : (V.regex * int) list) (input : string)
          (seen : (int * string * V.actions) list ref) (parent_redundant : bool)
          (default : A.annotation) (ghostDepth : int) (t : A.tree) : node =
  let ann, tree_node = unwrap default t in
  let pre = state_js input ann in
  let regex_id = regex_id_of idMap ann.A.acts in
  let redundant = parent_redundant || (not (ann == default) && check_seen seen ann.A.acts pre) in
  let make ?(result = Js.Nullable.null) ?(hasGhostSubtree = false) name arg subjs : node =
    let loop = to_node idMap input seen redundant ann in
    let children = match subjs with
      | [] -> []
      | hd :: tl -> loop (ghostDepth + if hasGhostSubtree then 1 else 0) hd
                    :: List.map (loop ghostDepth) tl in
    let post = match children with
      | f :: _ -> Js.Nullable.return f.pre
      | [] -> Js.Nullable.null in
    { name; arg; result; ghostDepth; hasGhostSubtree;
      regexId = regex_id |> Js.Nullable.fromOption; redundant;
      pre; post; children = Array.of_list children } in
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
     make ~hasGhostSubtree:true (lk_name lk) "" [ tlk; c ]
  | A.LKFail (lk, tlk) ->
    make ~hasGhostSubtree:true ~result:mismatched (lk_name lk) "" [ tlk ]
  | A.Annot _ ->
     assert false

(** Entry point. *)
let to_tree (idMap : (V.regex * int) list) (input: string) : A.tree -> node = function
  | A.Annot (ann, _) as t ->
    to_node idMap input (ref []) false ann 0 t
  | _ -> assert false
