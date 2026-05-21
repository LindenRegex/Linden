(* The MemoBT algorithm, expressed as a fuel-based function *)

From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Regex Chars Groups StrictSuffix.
From Linden Require Import Tree Semantics NFA.
From Linden Require Import BooleanSemantics PikeSubset.
From Linden Require Import MemoBT Correctness SeenSets.
From Linden Require Import Complexity.
From Linden Require Import Parameters LWParameters.
From Linden Require Import Prefix Tactics.
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

Inductive matchres : Type :=
| OutOfFuel
| Finished: option leaf -> memoset -> matchres.

Definition getres (mbt:mbt_state) : matchres :=
  match mbt with
  | MBT_final best ms => Finished best ms
  | _ => OutOfFuel
  end.

(* Functional version of the MemoBT *)
Definition memobt_match' (r:regex) (inp:input) (ms:memoset) : matchres :=
  let code := compilation r in
  let fuel := memobt_fuel r inp in
  let mbtinit := initial_state inp ms in
  getres (memobt_loop code mbtinit fuel).

Definition memobt_match (r:regex) (inp:input) : matchres :=
  memobt_match' r inp initial_memoset.

(* For the MemoBT, we can run prefix acceleration multiple times after each failed anchored search. *)
(* Instead of running MemoBT with a lazy prefix, we run it in anchored mode at each position where *)
(* the prefix matches. By reusing cache from each anchored run, this still executes in linear time. *)

Inductive matchres_unanchored : Type :=
| OutOfFuel_un
| Finished_un: option leaf -> memoset -> matchres_unanchored.

(* unanchored search for MemoBT with prefix acceleration *)
Function memobt_match_unanchored' {strs:StrSearch} (r:regex) (inp:input) (ms:memoset) (p:string)
  {measure (fun inp => remaining_length inp forward) inp}: matchres_unanchored :=
  (* we skip the initial input that does not match the prefix *)
  match (input_search p inp) with
  | None => Finished_un None ms (* if prefix is not present anywhere, then we cannot match *)
  | Some inp' =>
    match memobt_match' r inp' ms with
    | OutOfFuel => OutOfFuel_un
    | Finished (Some leaf) ms' => Finished_un (Some leaf) ms'
    | Finished None ms' =>
      match advance_input inp' forward with
      | Some inp'' => memobt_match_unanchored' r inp'' ms' p
      | None => Finished_un None ms' (* we already tried to match at every potential position *)
      end
    end
  end.
Proof.
  intros strs r [next pref] ms p [next' pref'] Hsearch result ms' Hres Hmatch [next'' pref''] Hinp''.
  destruct next' as [|c' next']; [discriminate|].
  inversion Hinp''; subst.
  eapply (strict_suffix_current (Input next'' (c' :: pref')) (Input next pref) forward).
  eapply input_search_strict_suffix in Hsearch as [<-|Hss]; ss_solve.
Defined.

Definition memobt_match_unanchored {strs:StrSearch} (r:regex) (inp:input) : matchres_unanchored :=
  memobt_match_unanchored' strs r inp initial_memoset (prefix (extract_literal rer r)).


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

Theorem memobt_match'_correct:
  forall r inp result ms ms',
    memobt_match' r inp ms = Finished result ms' ->
    trc_memo_bt rer (compilation r) (initial_state inp ms) (MBT_final result ms').
Proof.
  unfold memobt_match', getres. intros r inp result ms ms' H.
  match_destr; inversion H; subst.
  eapply loop_trc; eauto.
Qed.

(* when the function finishes, it returns the correct result *)
Theorem memobt_match_correct:
  forall r inp result ms,
    memobt_match r inp = Finished result ms ->
    trc_memo_bt rer (compilation r) (initial_state inp initial_memoset) (MBT_final result ms).
Proof.
  intros.
  now apply memobt_match'_correct.
Qed.


Lemma memobt_match'_terminates:
  forall r inp ms,
    pike_regex r ->
    validms ms (codesize r) inp ->
    exists result ms', memobt_match' r inp ms = Finished result ms'.
Proof.
  intros * SUBSET VALID. unfold memobt_match', memobt_fuel.
  eapply memobt_complexity with (rer:=rer) (r:=r) (inp:=inp) (2:=VALID) in SUBSET as [result [finalms [TERM VAL]]].
  exists result. exists finalms. apply steps_loop in TERM. now rewrite TERM.
Qed.

(* the function always terminates *)
Theorem memobt_match_terminates:
  forall r inp,
    pike_regex r ->
    exists result ms, memobt_match r inp = Finished result ms.
Proof.
  intros.
  apply memobt_match'_terminates; auto.
  exists []. apply mswf_init.
Qed.

End FunctionMemoBT.
