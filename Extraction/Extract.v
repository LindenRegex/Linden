From Linden Require Import PikeVM FunctionalPikeVM.
From Linden Require Import NFA.

Set Warnings "-extraction-default-directory".

(** * Extracting the NFA Compiler and the PikeVM interpreter *)

Separate Extraction NFA.compilation FunctionalPikeVM.pike_vm_match.
