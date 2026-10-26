From Linden Require Import PikeVM FunctionalPikeVM.
From Linden Require Import NFA PikeSubset.

(* Extracting to native OCaml types *)
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt.

Set Warnings "-extraction-default-directory".

(** * Extracting the NFA Compiler and the PikeVM interpreter *)

Separate Extraction NFA.compilation FunctionalPikeVM.pike_vm_match Regex.max_group PikeSubset.is_pike_regex.
