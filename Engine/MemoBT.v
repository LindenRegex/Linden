(** * MemoBT algorithm  *)
(* A backtracking algorithm on the extended NFA, with memoization *)

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import Parameters SeenSets.
From Warblre Require Import Base RegExpRecord.

(* LATER: to be able to do multiple prefix acceleration,
   we would like to return the seen set when we haven't found a match,
   and prove that seen set does not allow to find any match.
   Then, we should be able to start looking from multiple possible
   start positions, sharing the seen set each time.
 *)

Section MemoBT.
  Context {params: LindenParameters}.
  Context {MS: MemoSet params}.
  Context (rer: RegExpRecord).

  (* configurations to be explored by the memoized backtracking engine *)
  Definition config: Type := label * group_map * LoopBool * input.
  Definition stack: Type := list config.

  (* states of the MemoBT algorithm *)
  Inductive mbt_state : Type :=
  | MBT (stk:stack) (ms: memoset)
  | MBT_final (res:option leaf) : mbt_state.

  Definition initial_state (inp:input) : mbt_state :=
    MBT [(0, GroupMap.empty, CanExit, inp)] initial_memoset.

  (** * MemoBT small-step semantics *)

  Inductive exec_result : Type :=
  | FoundMatch: leaf -> exec_result
  | Explore: stack -> exec_result.

  Definition Dead : exec_result := Explore [].

  (* Computes the next configurations to explore, ordered by priority *)
  Definition exec_instr (c:code) (conf:config) : exec_result :=
    match conf with
    | (pc, gm, b, i) =>
        match (get_pc c pc) with
        | None => Dead
        | Some instr =>
            match instr with
            | Accept => FoundMatch (i, gm)
            | Consume cd =>
                match read_char rer cd i forward with
                | None => Dead
                | Some (_, nextinp) => Explore [(pc+1, gm, CanExit, nextinp)]
                end
            | CheckAnchor a =>
                match anchor_satisfied rer a i with
                | false => Dead
                | true => Explore [(pc+1, gm, b, i)]
                end
            | Jmp next => Explore [(next, gm, b, i)]
            | Fork lbl1 lbl2 => Explore [(lbl1, gm, b, i); (lbl2, gm, b, i)]
            | SetRegOpen gid => Explore [(pc+1, GroupMap.open (idx i) gid gm, b, i)]
            | SetRegClose gid => Explore [(pc+1, GroupMap.close (idx i) gid gm, b, i)]
            | ResetRegs gidl => Explore [(pc+1, GroupMap.reset gidl gm, b, i)]
            | BeginLoop => Explore [(pc+1, gm, CannotExit, i)]
            | EndLoop next =>
                match b with
                | CannotExit => Dead
                | CanExit => Explore [(next, gm, b, i)]
                end
            | KillThread => Dead
            end
        end
    end.


  Inductive memobt_step (c:code) : mbt_state -> mbt_state -> Prop :=
  (* we exhausted all configurations, there is no match *)
  | mbt_nomatch: forall ms,
      memobt_step c (MBT [] ms) (MBT_final None)
  (* the memoization allows to skip the current configuration *)
  | mbt_skip:
    forall ms pc gm b i stk
      (SEEN: is_memo ms pc b i = true),
      memobt_step c (MBT ((pc,gm,b,i)::stk) ms) (MBT stk ms)
  (* a match is found, we discard the stack *)
  | mbt_match:
    forall pc gm b i stk ms leaf
      (UNSEEN: is_memo ms pc b i = false)
      (MATCH: exec_instr c (pc, gm, b, i) = FoundMatch leaf),
      memobt_step c (MBT ((pc,gm,b,i)::stk) ms) (MBT_final (Some leaf))
  (* we keep exploring, and add each handled configuration to the memoization set *)
  | mbt_explore:
    forall pc gm b i stk ms nextconfs
      (UNSEEN: is_memo ms pc b i = false)
      (EXPLORE: exec_instr c (pc, gm, b, i) = Explore nextconfs),
      memobt_step c (MBT ((pc,gm,b,i)::stk) ms) (MBT (nextconfs++stk) (memoize ms pc b i)).

  (** * MemoBT properties  *)

  Theorem memobt_deterministic:
     forall c mbs mbs1 mbs2
    (STEP1: memobt_step c mbs mbs1)
    (STEP2: memobt_step c mbs mbs2),
       mbs1 = mbs2.
  Proof.
    intros c mbs mbs1 mbs2 STEP1 STEP2. inversion STEP1; subst;
      inversion STEP2; subst; auto;
      try (rewrite MATCH0 in MATCH; inversion MATCH);
      try (rewrite EXPLORE in MATCH; inversion MATCH);
      try (rewrite EXPLORE0 in EXPLORE; inversion EXPLORE);
      try (rewrite UNSEEN in SEEN; inversion SEEN); auto.
  Qed.

  Theorem memobt_progress:
    forall c stk ms,
    exists mbts,
      memobt_step c (MBT stk ms) mbts.
  Proof.
    intros c stk ms. destruct stk.
    { exists (MBT_final None). constructor. }
    destruct c0 as [[[pc gm] b] i].
    destruct (is_memo ms pc b i) eqn:SEEN.
    { exists (MBT stk ms). constructor. auto. }
    destruct (exec_instr c (pc,gm,b,i)) eqn:EXEC.
    - exists (MBT_final (Some l)). constructor; auto.
    - exists (MBT (s++stk) (memoize ms pc b i)). constructor; auto.
  Qed.

End MemoBT.
