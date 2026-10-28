From Stdlib Require Import List.
Import ListNotations.
From Linden Require Import FunctionalPikeVM Inst Regex Chars NFA PikeVM SeenSets.
From Linden.Semantics Require Import Examples.
From Warblre Require Import Inst Base RegExpRecord.
Require Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Open Scope string_scope.

Definition branch_a : regex := Regex.Character (CdSingle ($ "a")).
Definition branch_b : regex := Regex.Character (CdSingle ($ "b")).
Definition branch_capture := Disjunction (Group 1 branch_a) (Group 2 branch_b).
Definition branch_flags := rer_of branch_capture.

Example distinct_leads_compile:
  hd KillThread (NFA.compilation branch_flags true branch_capture) =
    Branch (CdSingle ($ "a")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example equal_leads_fork:
  hd KillThread (NFA.compilation branch_flags true
    (Disjunction branch_a branch_a)) = Fork 1 3.
Proof. vm_compute. reflexivity. Qed.

Example nullable_lead_forks:
  hd KillThread (NFA.compilation branch_flags true
    (Disjunction (Sequence (greedy_star branch_a) branch_b) branch_b)) = Fork 1 9.
Proof. vm_compute. reflexivity. Qed.

Definition branch_run (r: regex) (s: list Character.type) :=
  getres (pike_vm_loop (rer_of r) (NFA.compilation (rer_of r) true r)
    (pike_vm_initial_state (Input s [])) 200).
Definition reference_run (r: regex) (s: list Character.type) :=
  getres (pike_vm_loop (rer_of r) (NFA.compilation (rer_of r) false r)
    (pike_vm_initial_state (Input s [])) 200).

Example branch_captures_both_arms_and_failure:
  map (branch_run branch_capture) [[$ "a"]; [$ "b"]; [$ "c"]; []] =
  map (reference_run branch_capture) [[$ "a"]; [$ "b"]; [$ "c"]; []].
Proof. vm_compute. reflexivity. Qed.

Example repeated_branch_captures:
  branch_run (greedy_star branch_capture) [$ "a"; $ "b"; $ "a"] =
  reference_run (greedy_star branch_capture) [$ "a"; $ "b"; $ "a"].
Proof. vm_compute. reflexivity. Qed.

Example case_folded_leads_fork:
  let rer := RegExpRecord.make true false false tt 0 in
  hd KillThread (NFA.compilation rer true
    (Disjunction branch_a (Regex.Character (CdSingle ($ "A"))))) = Fork 1 3.
Proof. vm_compute. reflexivity. Qed.

(* loops whose body must start with a known character peek before entering *)
Example loop_branch_compile:
  hd KillThread (NFA.compilation branch_flags true (greedy_star branch_a)) =
    LoopBranch (CdSingle ($ "a")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example loop_branch_captures:
  map (branch_run (Sequence (greedy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]] =
  map (reference_run (Sequence (greedy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]].
Proof. vm_compute. reflexivity. Qed.

Example lazy_loop_branch_captures:
  map (branch_run (Sequence (lazy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]] =
  map (reference_run (Sequence (lazy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]].
Proof. vm_compute. reflexivity. Qed.
