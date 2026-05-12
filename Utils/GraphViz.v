(** Utilities for visualizing Linden data in GraphViz format *)

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups StrictSuffix.
From Linden Require Import FunctionalUtils.
From Linden Require Import Tree Semantics.
From Linden Require Import Utils Parameters LWParameters.
From Warblre Require Import Base RegExpRecord.


From Stdlib Require Import String Ascii.
Open Scope string_scope.

Section GraphViz.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

Definition string_of_nat (n : nat) : string :=
  (fix aux (n : nat) (acc : string) (fuel : nat) : string :=
    match fuel with
    | 0 => acc
    | S fuel' =>
        let d := Nat.modulo n 10 in
        let c := ascii_of_nat (48 + d) in
        let next_n := Nat.div n 10 in
        let new_acc := String c acc in
        if (next_n == 0) then new_acc
        else aux next_n new_acc fuel'
    end) n "" (S n).

Definition ascii_of_char (c: Character) : ascii :=
  ascii_of_nat (Character.numeric_value c).

Definition string_of_string (s : LWParameters.string) : string :=
  String.concat "" (map (fun c => String (ascii_of_char c) "") s).

Definition newline : string := String (ascii_of_nat 10) "".
Definition quote : string := String (ascii_of_nat 34) "".
Definition quoted (s : string) : string := quote ++ s ++ quote.
Definition quoted_esc (s : string) : string := "\" ++ quote ++ s ++ "\" ++ quote.


Definition string_of_lk (lk: lookaround) : string :=
  match lk with
  | LookAhead => "LookAhead"
  | LookBehind => "LookBehind"
  | NegLookAhead => "NegLookAhead"
  | NegLookBehind => "NegLookBehind"
  end.


Fixpoint tree_to_dot_aux (t : tree) (id : nat) : (string * nat) :=
  let current_node := "node" ++ (string_of_nat id) in
  match t with
  | Mismatch =>
      (current_node ++ " [label=" ++ quoted "Mismatch" ++ ", shape=box, color=red];" ++ newline, id + 1)
  | Match =>
      (current_node ++ " [label=" ++ quoted "Match" ++ ", shape=doublecircle, color=green];" ++ newline, id + 1)
  | Choice t1 t2 =>
      let (s1, id1) := tree_to_dot_aux t1 (id + 1) in
      let (s2, id2) := tree_to_dot_aux t2 id1 in
      let label := current_node ++ " [label=" ++ quoted "Choice" ++ "];" ++ newline in
      let edge1 := current_node ++ " -> node" ++ (string_of_nat (id + 1)) ++ ";" ++ newline in
      let edge2 := current_node ++ " -> node" ++ (string_of_nat id1) ++ ";" ++ newline in
      (label ++ s1 ++ s2 ++ edge1 ++ edge2, id2)
  | Read c t' =>
      let (s, id') := tree_to_dot_aux t' (id + 1) in
      let label := current_node ++ " [label=" ++ quoted ("Read " ++ quoted_esc (String (ascii_of_char c) "")) ++ "];" ++ newline in
      let edge := current_node ++ " -> node" ++ (string_of_nat (id + 1)) ++ ";" ++ newline in
      (label ++ s ++ edge, id')
  | ReadBackRef str t' =>
      let (s, id') := tree_to_dot_aux t' (id + 1) in
      let label := current_node ++ " [label=" ++ quoted ("BackRef " ++ quoted_esc (string_of_string str)) ++ "];" ++ newline in
      let edge := current_node ++ " -> node" ++ (string_of_nat (id + 1)) ++ ";" ++ newline in
      (label ++ s ++ edge, id')
  | Progress t' =>
      let (s, id') := tree_to_dot_aux t' (id + 1) in
      let label := current_node ++ " [label=" ++ quoted "Progress" ++ "];" ++ newline in
      let edge := current_node ++ " -> node" ++ (string_of_nat (id + 1)) ++ ";" ++ newline in
      (label ++ s ++ edge, id')
  | AnchorPass a t' =>
      let (s, id') := tree_to_dot_aux t' (id + 1) in
      let anchor_label := match a with
        | BeginInput => "BeginInput"
        | EndInput => "EndInput"
        | WordBoundary => "WordBoundary"
        | NonWordBoundary => "NonWordBoundary"
        end in
      let label := current_node ++ " [label=" ++ quoted ("Anchor " ++ anchor_label) ++ "];" ++ newline in
      let edge := current_node ++ " -> node" ++ (string_of_nat (id + 1)) ++ ";" ++ newline in
      (label ++ s ++ edge, id')
  | GroupAction g t' =>
      let (s, id') := tree_to_dot_aux t' (id + 1) in
      let action_label := match g with
        | Open gid => "Open " ++ (string_of_nat gid)
        | Close gid => "Close " ++ (string_of_nat gid)
        | Reset gl => "Reset {" ++ (String.concat ", " (map string_of_nat gl)) ++ "}"
        end in
      let label := current_node ++ " [label=" ++ quoted action_label ++ "];" ++ newline in
      let edge := current_node ++ " -> node" ++ (string_of_nat (id + 1)) ++ ";" ++ newline in
      (label ++ s ++ edge, id')
  | LK lk tlk t' =>
      let (s_lk, id_lk) := tree_to_dot_aux tlk (id + 1) in
      let (s_next, id_next) := tree_to_dot_aux t' id_lk in
      let label := current_node ++ " [label=" ++ quoted (string_of_lk lk) ++ "];" ++ newline in
      let subgraph := "subgraph cluster_" ++ current_node ++ " {" ++ newline ++ s_lk ++ "graph [style=dotted];" ++ newline ++ "}" ++ newline in
      let edge_lk := current_node ++ " -> node" ++ (string_of_nat (id + 1)) ++ " [style=dashed];" ++ newline in
      let edge_next := current_node ++ " -> node" ++ (string_of_nat id_lk) ++ ";" ++ newline in
      (label ++ subgraph ++ s_next ++ edge_lk ++ edge_next, id_next)
  | LKFail lk tlk =>
      let (s, id') := tree_to_dot_aux tlk id in
      let subgraph := "subgraph cluster_" ++ current_node ++ " {" ++ newline ++ s ++ "label=" ++ quoted (string_of_lk lk) ++ "; graph [style=dotted];" ++ newline ++ "}" ++ newline in
      (subgraph, id')
  end.

Definition tree_to_dot (t : tree) : string :=
  let (body, _) := tree_to_dot_aux t 0 in
  "digraph G {" ++ newline ++ "node [fontname=" ++ quoted "Arial" ++ "];" ++ newline ++ body ++ "}".

Definition actions_to_dot (acts: list action) (inp: input) (dir: Direction): string :=
  let tree := compute_tr rer acts inp GroupMap.empty dir in
  tree_to_dot tree.

End GraphViz.


From Linden Require Import LazyPrefix.
From Linden Require Import Inst.
From Warblre Require Import Inst.

Section Playground.
  Example a_char := Regex.Character (CdSingle $"a").
  Example b_char := Regex.Character (CdSingle $"b").
  Example c_char := Regex.Character (CdSingle $"c").
  Example x_char := Regex.Character (CdSingle $"x").
  Example y_char := Regex.Character (CdSingle $"y").

  Definition r :=
    lazy_prefix (Disjunction
      (Sequence a_char (Sequence (Lookaround LookAhead b_char) c_char))
      (Sequence (Lookaround NegLookBehind (Sequence x_char y_char)) (Sequence b_char b_char))).
  Definition i := Input [$"x"; $"y"; $"b"; $"b"; $"c"] [$"p"].

  Definition rer := reg_exp_record
    (* IgnoreCase *)
    false
    (* Multiline *)
    false
    (* DotAll *)
    false
    (* Unicode *)
    tt
    (* CapturingGroupsCount *)
    0.


  (*
    Using the Redirect command you can generate a file with the output of the Compute command.
    Using `actions_to_dot` you can generate a GraphViz dot file that can be then visualized using
    the `/tools/viz.sh` script.

    If you compile this file with `dune`, the output file will be generated in `_build/default/*.dot.out`.
    Pass this file to `viz.sh` to show an image of your tree.
  *)

  (* Redirect "tree.dot" Compute actions_to_dot rer [Areg r] i forward. *)

End Playground.
