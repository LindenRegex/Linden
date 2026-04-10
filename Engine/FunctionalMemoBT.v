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
  | MBT_final _ _ => mbt
  | MBT stk ms =>
      match stk with
      | [] => MBT_final None ms (* mbt_nomatch *)
      | (pc,gm,b,i)::stk =>
          match (is_memo ms pc b i) with
          | true => MBT stk ms (* mbt_skip *)
          | false =>
              let nextms := memoize ms pc b i in
              match exec_instr rer c (pc, gm, b, i) with
              | FoundMatch leaf => MBT_final (Some leaf) ms (* mbt_match *)
              | Explore nextconfs => MBT (nextconfs ++ stk) nextms (* mbt_explore *)
              end
          end
      end
  end.

(* looping the small step function until fuel runs out or a final state is reached *)
Fixpoint memobt_loop (c:code) (mbt:mbt_state) (fuel:nat) : mbt_state :=
  match mbt with
  | MBT_final _ _ => mbt
  | _ =>
      match fuel with
      | 0 => mbt
      | S fuel =>
          memobt_loop c (memobt_func_step c mbt) fuel
      end
  end.

(* an upper bound for the fuel necessary to compute a result *)
Definition memobt_fuel (r:regex) (inp:input) : nat :=
  mbt_complexity r inp.

Definition getres (mbt:mbt_state) : option leaf * memoset :=
  match mbt with
  | MBT_final best ms => (best, ms)
  | _ => (None, initial_memoset)
  end.

(* Functional version of the MemoBT *)
Definition memobt_match (r:regex) (inp:input) : option leaf * memoset :=
  let code := compilation r in
  let fuel := memobt_fuel r inp in
  let mbtinit := initial_state inp in
  getres (memobt_loop code (mbtinit initial_memoset) fuel).

(** * Smallstep correspondence  *)

Inductive final_state: mbt_state -> Prop :=
| mfinal: forall best ms, final_state (MBT_final best ms).

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
  forall c mbt1 mbt2 fuel ms,
    steps (memobt_step rer c) mbt1 fuel (MBT_final mbt2 ms) ->
    memobt_loop c mbt1 fuel = (MBT_final mbt2 ms).
Proof.
  intros c mbt1 mbt2 fuel ms H. remember (MBT_final mbt2 ms) as result.
  induction H; subst.
  - destruct n; simpl; auto.
  - destruct x.
    2: { inversion STEP. }
    erewrite step_loop; eauto.
Qed.

(* the function always terminates *)
Theorem memobt_loop_terminates:
  forall r inp,
    pike_regex r ->
    exists result ms, memobt_loop (compilation r) (initial_state inp initial_memoset) (memobt_fuel r inp) = MBT_final result ms.
Proof.
  intros r inp Hsubset. unfold memobt_fuel.
  pose proof memobt_complexity_empty_memoset rer r inp Hsubset as [result [finalms [TERM VAL]]].
  exists result. exists finalms. now apply steps_loop.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem memobt_match_correct:
  forall r inp result ms,
    pike_regex r ->
    memobt_match r inp = (result, ms) ->
    trc_memo_bt rer (compilation r) (initial_state inp initial_memoset) (MBT_final result ms).
Proof.
  unfold memobt_match, getres. intros r inp result ms Hsubset H.
  eapply loop_trc; eauto.
  pose proof memobt_loop_terminates r inp Hsubset as [result' [ms' Hres]].
  rewrite Hres in *.
  now injection H as <- <-.
Qed.

End FunctionMemoBT.
