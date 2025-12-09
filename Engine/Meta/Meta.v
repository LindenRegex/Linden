(** * The Meta engine  *)

(* Individual regex engines have their own unique strengths and weaknesses. *)
(* Some may support only a subset of regex features, some may be more *)
(* efficient depending on some characteristics of the regex or the input. *)
(* Sometimes we may even want to skip regex engines entirely and just do a *)
(* substring search. The Meta engine exploits these features by *)
(* encapsulating heuristics that look for matches using strategies it deems *)
(* to be the most efficient. *)

Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree.
From Linden Require Import FunctionalUtils.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix Prefix.
From Linden Require Import EngineSpec MetaLiterals.
From Warblre Require Import Base RegExpRecord.


Section Meta.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

End Meta.
