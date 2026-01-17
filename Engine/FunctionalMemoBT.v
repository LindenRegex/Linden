(* The MemoBT algorithm, expressed as a fuel-based function *)

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import MemoBT Correctness SeenSets.
From Linden Require Import Complexity.
From Linden Require Import Parameters.
From Linden Require Import FunctionalUtils FunctionalSemantics.
From Warblre Require Import Base RegExpRecord.

Section FunctionMemoBT.
  Context {params: LindenParameters}.
  Context {MS: MemoSet params}.
  Context (rer: RegExpRecord).
(** * Functional Definition  *)

(* a functional version of the small step *)
Definition memobt_func_step (c:code) (mbt:mbt_state) : mbt_state :=
  match mbt with
  | MBT_final _ => mbt
  | MBT stk ms =>
      match stk with
      | [] => MBT_final None (* mbt_nomatch *)
      | (pc,gm,b,i)::stk =>
          match (is_memo ms pc b i) with
          | true => MBT stk ms (* mbt_skip *)
          | false =>
              let nextms := memoize ms pc b i in
              match exec_instr rer c (pc, gm, b, i) with
              | FoundMatch leaf => MBT_final (Some leaf) (* mbt_match *)
              | Explore nextconfs => MBT (nextconfs ++ stk) nextms (* mbt_explore *)
              end
          end
      end
  end.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint memobt_loop (c:code) (mbt:mbt_state) (fuel:nat) : mbt_state :=
  match mbt with
  | MBT_final _ => mbt
  | _ =>
      match fuel with
      | 0 => mbt
      | S fuel =>
          memobt_loop c (memobt_func_step c mbt) fuel
      end
  end.


(* LATER: prove complexity bound of MemoBT *)
Definition complexity (r:regex) (inp:input) : nat :=
  (* LATER: derive from complexity of the MemoBT algorithm *)
  0.
Axiom memobt_complexity:
  forall (r:regex) (inp:input),
    (* for any supported regex r and input inp *)
    pike_regex r ->
    (* The initial state reaches a final state in at most (complexity r inp) steps. *)
    exists result, steps (memobt_step rer (compilation r))
                (initial_state inp) (complexity r inp) (MBT_final result).

(* an upper bound for the fuel necessary to compute a result *)
Definition memobt_fuel (r:regex) (inp:input) : nat :=
  complexity r inp.

Inductive matchres : Type :=
| OutOfFuel
| Finished: option leaf -> matchres.

Definition getres (mbt:mbt_state) : matchres :=
  match mbt with
  | MBT_final best => Finished best
  | _ => OutOfFuel
  end.

(* Functional version of the MemoBT *)
Definition memobt_match (r:regex) (inp:input) : matchres :=
  let code := compilation r in
  let fuel := memobt_fuel r inp in
  let mbtinit := initial_state inp in
  getres (memobt_loop code mbtinit fuel).

(** * Smallstep correspondence  *)

Inductive final_state: mbt_state -> Prop :=
| mfinal: forall best, final_state (MBT_final best).

Ltac match_destr:=
  match goal with
  | [ H : match ?x with _ => _ end = _  |- _ ] => let H := fresh "H" in destruct x eqn:H
  end.

Theorem func_step_correct:
  forall c mbt1 mbt2,
    memobt_func_step c mbt1 = mbt2 ->
    memobt_step rer c mbt1 mbt2 \/ final_state mbt1.
Proof.
  unfold memobt_func_step. intros c mbt1 mbt2 H.
  repeat match_destr; subst; try solve[left; constructor; auto].
  right. constructor.
Qed.

Corollary func_step_not_final:
  forall c stk ms,
    memobt_step rer c (MBT stk ms) (memobt_func_step c (MBT stk ms)).
Proof.
  intros c stk ms. specialize (func_step_correct c (MBT stk ms) _ (@eq_refl _ _)).
  intros [H|H]; auto. inversion H.
Qed.

Theorem loop_trc:
  forall c mbt1 mbt2 fuel,
    memobt_loop c mbt1 fuel = mbt2 ->
    trc_memo_bt rer c mbt1 mbt2.
Proof.
  intros c mbt1 mbt2 fuel H.
  generalize dependent mbt1. induction fuel; intros; simpl in H.
  { destruct mbt1; inversion H. constructor. constructor. }
  match_destr; subst.
  - econstructor; eauto. apply func_step_not_final. apply IHfuel. auto.
  - constructor.
Qed.


Lemma step_loop:
  forall c mbt1 mbt2 fuel,
    memobt_step rer c mbt1 mbt2 ->
    memobt_loop c mbt1 (S fuel) = memobt_loop c mbt2 fuel.
Proof.
  intros c mbt1 mbt2 fuel H. destruct H; simpl in *;
    now rewrite ?SEEN, ?UNSEEN, ?MATCH, ?EXPLORE.
Qed.

Theorem steps_loop:
  forall c mbt1 mbt2 fuel,
    steps (memobt_step rer c) mbt1 fuel (MBT_final mbt2) ->
    memobt_loop c mbt1 fuel = (MBT_final mbt2).
Proof.
  intros c mbt1 mbt2 fuel H. remember (MBT_final mbt2) as result.
  induction H; subst.
  - destruct n; simpl; auto.
  - destruct x.
    2: { inversion STEP. }
    erewrite step_loop; eauto.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem memobt_match_correct:
  forall r inp result,
    memobt_match r inp = Finished result ->
    trc_memo_bt rer (compilation r) (initial_state inp) (MBT_final result).
Proof.
  unfold memobt_match, getres. intros r inp result H.
  match_destr; inversion H; subst.
  eapply loop_trc; eauto.
Qed.


(* the function always terminates *)
Theorem memobt_match_terminates:
  forall r inp,
    pike_regex r ->
    exists result, memobt_match r inp = Finished result.
Proof.
  intros r inp SUBSET. unfold memobt_match, memobt_fuel.
  apply memobt_complexity with (r:=r) (inp:=inp) in SUBSET as [result TERM].
  exists result. apply steps_loop in TERM. rewrite TERM. auto.
Qed.

End FunctionMemoBT.
