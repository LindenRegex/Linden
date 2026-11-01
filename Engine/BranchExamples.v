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

(* overlapping alternatives still peek when the first must start with a known character *)
Example equal_leads_guard_first:
  hd KillThread (NFA.compilation branch_flags true
    (Disjunction branch_a branch_a)) = GuardFirst (CdSingle ($ "a")) 2 4.
Proof. vm_compute. reflexivity. Qed.

(* an alternative that cannot peek guards the next one on its leading character *)
Example nullable_lead_guards_second:
  hd KillThread (NFA.compilation branch_flags true
    (Disjunction (Sequence (greedy_star branch_a) branch_b) branch_b)) = GuardSecond (CdSingle ($ "b")) 2 10.
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

Example case_folded_leads_guard_first:
  let rer := RegExpRecord.make true false false tt 0 in
  hd KillThread (NFA.compilation rer true
    (Disjunction branch_a (Regex.Character (CdSingle ($ "A"))))) = GuardFirst (CdSingle ($ "a")) 2 4.
Proof. vm_compute. reflexivity. Qed.

(* loops whose body must start with a known character peek before entering *)
Example guard_first_compile:
  hd KillThread (NFA.compilation branch_flags true (greedy_star branch_a)) =
    GuardFirst (CdSingle ($ "a")) 2 6.
Proof. vm_compute. reflexivity. Qed.

(* a greedy loop followed by a different character needs a single thread *)
Example follow_branch_compile:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star branch_a) branch_b)) =
    Branch (CdSingle ($ "a")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example case_folded_follow_loops:
  let rer := RegExpRecord.make true false false tt 0 in
  hd KillThread (NFA.compilation rer true
    (Sequence (greedy_star branch_a) (Regex.Character (CdSingle ($ "A"))))) =
    GuardFirst (CdSingle ($ "a")) 2 6.
Proof. vm_compute. reflexivity. Qed.

(* under ignoreCase, the default check never finds descriptors disjoint, even distinct characters *)
Example case_folded_distinct_follow_guards:
  let rer := RegExpRecord.make true false false tt 0 in
  hd KillThread (NFA.compilation rer true (Sequence (greedy_star branch_a) branch_b)) =
    GuardFirst (CdSingle ($ "a")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example follow_branch_runs:
  map (branch_run (Sequence (greedy_star branch_a) branch_b)) [[$ "a"; $ "a"; $ "b"]; [$ "b"]; [$ "a"]] =
  map (reference_run (Sequence (greedy_star branch_a) branch_b)) [[$ "a"; $ "a"; $ "b"]; [$ "b"]; [$ "a"]].
Proof. vm_compute. reflexivity. Qed.

Example follow_branch_captures:
  map (branch_run (Sequence (greedy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]] =
  map (reference_run (Sequence (greedy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]].
Proof. vm_compute. reflexivity. Qed.

Example lazy_follow_branch_captures:
  map (branch_run (Sequence (lazy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]] =
  map (reference_run (Sequence (lazy_star (Group 1 branch_a)) branch_b)) [[$ "a"; $ "b"]; [$ "b"]; [$ "a"]].
Proof. vm_compute. reflexivity. Qed.

(* a lazy loop followed by a different character uses the same instruction:
   only one of its threads can survive *)
Example lazy_follow_branch_compile:
  hd KillThread (NFA.compilation branch_flags true (Sequence (lazy_star branch_a) branch_b)) =
    Branch (CdSingle ($ "a")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example lazy_follow_branch_runs:
  map (branch_run (Sequence (lazy_star (Group 1 branch_a)) (Group 2 branch_b))) [[$ "a"; $ "a"; $ "b"]; [$ "b"]; [$ "a"]; [$ "a"; $ "b"; $ "b"]] =
  map (reference_run (Sequence (lazy_star (Group 1 branch_a)) (Group 2 branch_b))) [[$ "a"; $ "a"; $ "b"]; [$ "b"]; [$ "a"]; [$ "a"; $ "b"; $ "b"]].
Proof. vm_compute. reflexivity. Qed.

(* a lead disjoint from what follows branches, on either side of an inversion *)
Definition branch_ac : regex := Regex.Character (CdRange ($ "a") ($ "c")).

Example range_follow_branch_compile:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star branch_ac) (Regex.Character (CdSingle ($ "d"))))) =
    Branch (CdRange ($ "a") ($ "c")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example inverted_follow_branch_compile:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star (Regex.Character (CdInv (CdSingle ($ "a"))))) branch_a)) =
    Branch (CdInv (CdSingle ($ "a"))) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example ranges_follow_branch_compile:
  hd KillThread (NFA.compilation branch_flags true
    (Sequence (greedy_star branch_ac) (Regex.Character (CdRange ($ "d") ($ "f"))))) =
    Branch (CdRange ($ "a") ($ "c")) 2 6.
Proof. vm_compute. reflexivity. Qed.

(* only a leading character is worth peeking at on every iteration: an
   overlapping range peeks at what follows to keep its exit instead *)
Example overlapping_range_guards_exit:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star branch_ac) branch_b)) =
    GuardSecond (CdSingle ($ "b")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example range_follow_branch_runs:
  map (branch_run (Sequence (greedy_star (Group 1 branch_ac)) (Regex.Character (CdSingle ($ "d"))))) [[$ "a"; $ "c"; $ "d"]; [$ "d"]; [$ "b"]] =
  map (reference_run (Sequence (greedy_star (Group 1 branch_ac)) (Regex.Character (CdSingle ($ "d"))))) [[$ "a"; $ "c"; $ "d"]; [$ "d"]; [$ "b"]].
Proof. vm_compute. reflexivity. Qed.

(* a disjunction leads with the union of its alternatives' leads *)
Definition branch_c : regex := Regex.Character (CdSingle ($ "c")).

Example union_follow_branch_compile:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star branch_b) (Disjunction branch_c branch_a))) =
    Branch (CdSingle ($ "b")) 2 6.
Proof. vm_compute. reflexivity. Qed.

Example union_body_branch_compile:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star (Disjunction branch_a branch_b)) branch_c)) =
    Branch (CdUnion (CdSingle ($ "a")) (CdSingle ($ "b"))) 2 10.
Proof. vm_compute. reflexivity. Qed.

Example union_body_guards_exit:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star (Disjunction branch_a branch_b)) branch_a)) =
    GuardSecond (CdSingle ($ "a")) 2 10.
Proof. vm_compute. reflexivity. Qed.

Example union_branch_runs:
  map (branch_run (Sequence (lazy_star (Disjunction (Group 1 branch_a) branch_b)) branch_c)) [[$ "a"; $ "b"; $ "c"]; [$ "c"]; [$ "a"]; [$ "b"; $ "a"]] =
  map (reference_run (Sequence (lazy_star (Disjunction (Group 1 branch_a) branch_b)) branch_c)) [[$ "a"; $ "b"; $ "c"]; [$ "c"]; [$ "a"]; [$ "b"; $ "a"]].
Proof. vm_compute. reflexivity. Qed.

(* what follows [$] can only be the end of the input, or a line terminator if multiline *)
Definition branch_end (r: regex) := Sequence (greedy_star r) (Anchor EndInput).

Example end_follow_branch_compile:
  map (fun r => hd KillThread (NFA.compilation branch_flags true (branch_end r))) [branch_a; Regex.Character CdWhitespace] =
    [Branch (CdSingle ($ "a")) 2 6; Branch CdWhitespace 2 6].
Proof. vm_compute. reflexivity. Qed.

Definition multiline_run (branches: bool) (r: regex) (s: list Character.type) :=
  let rer := RegExpRecord.make false true false tt (max_group r) in
  getres (pike_vm_loop rer (NFA.compilation rer branches r) (pike_vm_initial_state (Input s [])) 200).

Example multiline_end_follow_compile:
  let rer := RegExpRecord.make false true false tt 0 in
  map (fun r => hd KillThread (NFA.compilation rer true (branch_end r))) [branch_a; Regex.Character CdWhitespace] =
    [Branch (CdSingle ($ "a")) 2 6; Fork 1 5].
Proof. vm_compute. reflexivity. Qed.

Example multiline_end_follow_runs:
  map (multiline_run true (branch_end (Group 1 branch_a))) [[$ "a"; $ "010"; $ "a"]; [$ "a"; $ "a"]; [$ "a"; $ "b"]; []] =
  map (multiline_run false (branch_end (Group 1 branch_a))) [[$ "a"; $ "010"; $ "a"]; [$ "a"; $ "a"]; [$ "a"; $ "b"]; []].
Proof. vm_compute. reflexivity. Qed.

(* ab|ac|b: the first alternative only survives an [a] *)
Definition branch_keywords := Disjunction (Group 1 (Sequence branch_a branch_b))
  (Disjunction (Group 2 (Sequence branch_a branch_c)) branch_b).

Example keyword_guard_first_compile:
  hd KillThread (NFA.compilation branch_flags true branch_keywords) = GuardFirst (CdSingle ($ "a")) 2 7.
Proof. vm_compute. reflexivity. Qed.

Example overlapping_range_alternative_forks:
  hd KillThread (NFA.compilation branch_flags true (Disjunction branch_ac (Regex.Character (CdRange ($ "b") ($ "d"))))) =
    Fork 1 3.
Proof. vm_compute. reflexivity. Qed.

Example keyword_guard_first_runs:
  map (branch_run (Sequence (greedy_star branch_keywords) branch_c)) [[$ "a"; $ "b"; $ "a"; $ "c"; $ "c"]; [$ "b"; $ "c"]; [$ "a"; $ "c"]; [$ "a"]; []] =
  map (reference_run (Sequence (greedy_star branch_keywords) branch_c)) [[$ "a"; $ "b"; $ "a"; $ "c"; $ "c"]; [$ "b"; $ "c"]; [$ "a"; $ "c"]; [$ "a"]; []].
Proof. vm_compute. reflexivity. Qed.

(* what follows a loop sees through nullable parts of its continuation *)
Definition branch_nullable (r: regex) := Sequence (greedy_star branch_a) (Sequence r branch_c).

Example nullable_follow_branch_compile:
  map (fun r => hd KillThread (NFA.compilation branch_flags true (branch_nullable r)))
    [greedy_qmark branch_b; lazy_star branch_b; Epsilon; Quantified true 0 (NoI.N 0) branch_b] =
    [Branch (CdSingle ($ "a")) 2 6; Branch (CdSingle ($ "a")) 2 6; Branch (CdSingle ($ "a")) 2 6; Branch (CdSingle ($ "a")) 2 6].
Proof. vm_compute. reflexivity. Qed.

(* unless what is skipped or what follows it overlaps with the loop *)
Example nullable_follow_loops:
  map (fun r => hd KillThread (NFA.compilation branch_flags true r))
    [branch_nullable (greedy_qmark branch_a); Sequence (greedy_star branch_a) (greedy_star branch_b);
     Sequence (greedy_star branch_a) (Sequence (greedy_qmark branch_b) branch_a)] =
    [GuardFirst (CdSingle ($ "a")) 2 6; GuardFirst (CdSingle ($ "a")) 2 6; GuardFirst (CdSingle ($ "a")) 2 6].
Proof. vm_compute. reflexivity. Qed.

Example nullable_follow_branch_runs:
  map (branch_run (Sequence (lazy_star (Group 1 branch_a)) (Sequence (greedy_star (Group 2 branch_b)) (Disjunction branch_c (Anchor EndInput)))))
    [[$ "a"; $ "b"; $ "c"]; [$ "a"; $ "a"]; [$ "b"; $ "b"]; [$ "a"; $ "c"]; [$ "a"; $ "b"; $ "a"]; []] =
  map (reference_run (Sequence (lazy_star (Group 1 branch_a)) (Sequence (greedy_star (Group 2 branch_b)) (Disjunction branch_c (Anchor EndInput)))))
    [[$ "a"; $ "b"; $ "c"]; [$ "a"; $ "a"]; [$ "b"; $ "b"]; [$ "a"; $ "c"]; [$ "a"; $ "b"; $ "a"]; []].
Proof. vm_compute. reflexivity. Qed.

(* the body of an optional regex is followed by what follows it: (?:a(?:a)?)?b,
   as a{0,2}b unrolls, peeks at a before each a *)
Definition branch_upto_two := Sequence (greedy_qmark (Sequence (Group 1 branch_a) (greedy_qmark (Group 2 branch_a)))) branch_b.

Example optional_body_follow_branch_compile:
  nth 7 (NFA.compilation branch_flags true branch_upto_two) KillThread = Branch (CdSingle ($ "a")) 9 15.
Proof. vm_compute. reflexivity. Qed.

Example optional_body_follow_branch_runs:
  map (branch_run branch_upto_two) [[$ "a"; $ "a"; $ "b"]; [$ "a"; $ "b"]; [$ "b"]; [$ "a"; $ "a"; $ "a"; $ "b"]; [$ "a"]] =
  map (reference_run branch_upto_two) [[$ "a"; $ "a"; $ "b"]; [$ "a"; $ "b"]; [$ "b"]; [$ "a"; $ "a"; $ "a"; $ "b"]; [$ "a"]].
Proof. vm_compute. reflexivity. Qed.

(* without ignoreCase, \d, \s and \w are disjoint from the characters, ranges
   and classes that share none of their characters, and from their complements *)
Definition branch_w : regex := Regex.Character CdWordChar.
Definition branch_s : regex := Regex.Character CdWhitespace.
Definition branch_d : regex := Regex.Character CdDigits.
Definition branch_paren : regex := Regex.Character (CdSingle ($ "(")).
Definition branch_call := Sequence branch_w (Sequence (greedy_star branch_w) (Sequence (greedy_star branch_s) branch_paren)).

Example class_follow_branch_compile:
  NFA.compilation branch_flags true branch_call =
    [Consume CdWordChar; Branch CdWordChar 3 7; Data CdWordChar; BeginLoop; ResetRegs []; Consume CdWordChar; EndLoop 1;
     Branch CdWhitespace 9 13; Data CdWhitespace; BeginLoop; ResetRegs []; Consume CdWhitespace; EndLoop 7;
     Consume (CdSingle ($ "(")); Accept].
Proof. vm_compute. reflexivity. Qed.

Example class_follow_branches:
  map (fun r => hd KillThread (NFA.compilation branch_flags true r))
    [Sequence (greedy_star branch_d) branch_s; Sequence (greedy_star branch_s) branch_w;
     Sequence (greedy_star branch_d) (Regex.Character CdNonDigits); Sequence (greedy_star branch_ac) branch_s;
     Sequence (greedy_star (Regex.Character (CdInv (CdRange ($ "a") ($ "c"))))) branch_ac; Sequence (greedy_star branch_w) branch_d] =
    [Branch CdDigits 2 6; Branch CdWhitespace 2 6; Branch CdDigits 2 6; Branch (CdRange ($ "a") ($ "c")) 2 6;
     Branch (CdInv (CdRange ($ "a") ($ "c"))) 2 6; Fork 1 5].
Proof. vm_compute. reflexivity. Qed.

(* under ignoreCase, the default check gives up on classes *)
Example case_folded_class_follow_forks:
  let rer := RegExpRecord.make true false false tt 0 in
  map (fun r => hd KillThread (NFA.compilation rer true r))
    [Sequence (greedy_star branch_w) branch_s; Sequence (greedy_star branch_d) (Regex.Character (CdSingle ($ "a")))] =
    [Fork 1 5; GuardSecond (CdSingle ($ "a")) 2 6].
Proof. vm_compute. reflexivity. Qed.

Example class_follow_branch_runs:
  map (branch_run (Group 1 branch_call)) [[$ "a"; $ "1"; $ " "; $ "("]; [$ "a"; $ "("]; [$ " "; $ "("]; [$ "a"; $ " "]] =
  map (reference_run (Group 1 branch_call)) [[$ "a"; $ "1"; $ " "; $ "("]; [$ "a"; $ "("]; [$ " "; $ "("]; [$ "a"; $ " "]].
Proof. vm_compute. reflexivity. Qed.

(* a loop that cannot peek at its body peeks at a following character to keep
   its exit: .*c, [^a]*?c, (?:.|c)a *)
Definition branch_dot : regex := Regex.Character CdDot.
Definition branch_not_a : regex := Regex.Character (CdInv (CdSingle ($ "a"))).

Example exit_guard_compile:
  firstn 2 (NFA.compilation branch_flags true (Sequence (greedy_star branch_dot) branch_c)) =
    [GuardSecond (CdSingle ($ "c")) 2 6; Data (CdSingle ($ "c"))].
Proof. vm_compute. reflexivity. Qed.

Example lazy_exit_guard_compile:
  firstn 2 (NFA.compilation branch_flags true (Sequence (lazy_star branch_not_a) branch_c)) =
    [GuardSecondLazy (CdSingle ($ "c")) 2 6; Data (CdSingle ($ "c"))].
Proof. vm_compute. reflexivity. Qed.

Example second_alternative_guard_compile:
  firstn 2 (NFA.compilation branch_flags true (Sequence (Disjunction branch_dot branch_c) branch_a)) =
    [GuardSecond (CdSingle ($ "c")) 2 4; Data (CdSingle ($ "c"))].
Proof. vm_compute. reflexivity. Qed.

(* a class that follows does not guard *)
Example class_follow_forks:
  hd KillThread (NFA.compilation branch_flags true (Sequence (greedy_star branch_dot) branch_ac)) = Fork 1 5.
Proof. vm_compute. reflexivity. Qed.

Definition exit_guard_inputs := [[$ "a"; $ "c"; $ "c"]; [$ "c"]; [$ "a"]; []; [$ "c"; $ "a"; $ "c"; $ "b"]].

Example exit_guard_runs:
  map (branch_run (Sequence (greedy_star (Group 1 branch_dot)) (Group 2 branch_c))) exit_guard_inputs =
  map (reference_run (Sequence (greedy_star (Group 1 branch_dot)) (Group 2 branch_c))) exit_guard_inputs.
Proof. vm_compute. reflexivity. Qed.

Example lazy_exit_guard_runs:
  map (branch_run (Sequence (lazy_star (Group 1 branch_not_a)) (Group 2 branch_c))) exit_guard_inputs =
  map (reference_run (Sequence (lazy_star (Group 1 branch_not_a)) (Group 2 branch_c))) exit_guard_inputs.
Proof. vm_compute. reflexivity. Qed.

Example second_alternative_guard_runs:
  map (branch_run (greedy_star (Sequence (Disjunction (Group 1 branch_dot) (Group 2 branch_c)) branch_c))) exit_guard_inputs =
  map (reference_run (greedy_star (Sequence (Disjunction (Group 1 branch_dot) (Group 2 branch_c)) branch_c))) exit_guard_inputs.
Proof. vm_compute. reflexivity. Qed.

Example nested_exit_guard_runs:
  map (branch_run (Sequence (Disjunction (Sequence (greedy_star (Group 1 branch_dot)) branch_c) (Group 2 branch_a)) branch_b))
    exit_guard_inputs =
  map (reference_run (Sequence (Disjunction (Sequence (greedy_star (Group 1 branch_dot)) branch_c) (Group 2 branch_a)) branch_b))
    exit_guard_inputs.
Proof. vm_compute. reflexivity. Qed.
