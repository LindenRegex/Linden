From Warblre Require Import Patterns Semantics RegExpRecord Notation Result Base Node Errors.
From Linden Require Import LWParameters Parameters Regex RegexpTranslation.
Import Notation.
Import Result.Notations.
Import Patterns.
From Stdlib Require Import List.
Import ListNotations.

Local Open Scope result_flow.
Local Open Scope bool_scope.

(** * Factorization of lookarounds as a pair of a Direction and a boolean (positivity) *)
(* Code for matching each of the four kinds of lookarounds is duplicated in Warblre.
We factorize it in this file *)

Section LKFactorization.
  Context {params: LindenParameters}.
  
  Definition lkCtx (lkdir: Direction) (pos: bool) :=
    match lkdir, pos with
    | forward, true => Lookahead_inner
    | forward, false => NegativeLookahead_inner
    | backward, true => Lookbehind_inner
    | backward, false => NegativeLookbehind_inner
    end.

  Definition to_lookaround (lkdir: Direction) (pos: bool) :=
    match lkdir, pos with
    | forward, true => LookAhead
    | forward, false => NegLookAhead
    | backward, true => LookBehind
    | backward, false => NegLookBehind
    end.

  Definition to_warblre_lookaround (dir: Direction) (pos: bool) :=
    match dir, pos with
    | forward, true => Patterns.Lookahead
    | forward, false => Patterns.NegativeLookahead
    | backward, true => Patterns.Lookbehind
    | backward, false => Patterns.NegativeLookbehind
    end.

  Lemma lkdir_to_lookaround:
    forall lkdir pos, lk_dir (to_lookaround lkdir pos) = lkdir.
  Proof.
    now intros [] [].
  Qed.

  Lemma positivity_to_lookaround:
    forall lkdir pos, positivity (to_lookaround lkdir pos) = pos.
  Proof.
    now intros [] [].
  Qed.


  (* Factorization of cases of Semantics.compileSubPattern corresponding to lookarounds. *)
  Definition lookaroundMatcher (compileSubPattern: Regex -> RegexContext -> RegExpRecord -> Direction -> Result Matcher CompileError) (lkdir: Direction) (pos: bool) (lkreg: Regex) (ctx: RegexContext) (rer: RegExpRecord) (direction: Direction): Result Matcher CompileError :=
    let! m =<< compileSubPattern lkreg (lkCtx lkdir pos :: ctx) rer lkdir in
    Success ((fun (x: MatchState) (c: MatcherContinuation) =>
      let d: MatcherContinuation := fun (y: MatchState) => Success (Some y) in
      let! r =<< m x d in
      if (pos && r == None) || (negb pos && r != None) then
        Success None
      else if pos then
        destruct! (Some y) <- r in
        let cap := MatchState.captures y in
        let input := MatchState.input x in
        let xe := MatchState.endIndex x in
        let z := match_state input xe cap in
        c z
      else
        c x): Matcher).

  (* This is indeed a factorization of said cases. *)
  Lemma lookaroundMatcher_fact:
    forall lkdir pos lkreg ctx rer dir c x,
      (match Semantics.compileSubPattern ((to_warblre_lookaround lkdir pos) lkreg) ctx rer dir with
       | Success m => Success (m x c)
       | Error e => Error e
       end) =
        (match lookaroundMatcher Semantics.compileSubPattern lkdir pos lkreg ctx rer dir with
         | Success m => Success (m x c)
         | Error e => Error e
         end).
  Proof.
    intros [|] [|] lkreg ctx rer dir c x; unfold lookaroundMatcher; simpl; destruct Semantics.compileSubPattern as [msub|]; simpl; try reflexivity.
    - destruct msub; simpl; auto. rewrite Bool.orb_false_r. reflexivity.
    - destruct msub; simpl; auto. rewrite Bool.orb_false_r. reflexivity.
  Qed.


  (** ** Some utility lemmas *)

  Lemma equiv_lookaround_dir_pos:
    forall wlk llk,
      equiv_lookaround wlk llk ->
      exists dir pos,
        wlk = to_warblre_lookaround dir pos /\
        llk = to_lookaround dir pos.
  Proof.
    intros wlk llk EQUIV. inversion EQUIV.
    - exists forward. exists true. split; reflexivity.
    - exists forward. exists false. split; reflexivity.
    - exists backward. exists true. split; reflexivity.
    - exists backward. exists false. split; reflexivity.
  Qed.

  Lemma lk_root_fact:
    forall wroot lkdir pos wr ctx,
      Root wroot (to_warblre_lookaround lkdir pos wr, ctx) ->
      Root wroot (wr, (lkCtx lkdir pos :: ctx)%list).
  Proof.
    intros wroot [] [] wr ctx ROOT; simpl;
    eauto using
      NodeProps.Zipper.Down.same_root_down0,
      NodeProps.Zipper.Down_Lookahead_inner,
      NodeProps.Zipper.Down_NegativeLookahead_inner,
      NodeProps.Zipper.Down_Lookbehind_inner,
      NodeProps.Zipper.Down_NegativeLookbehind_inner.
  Qed.

  Lemma lk_fact_countParens:
    forall wr lkdir pos ctx,
      StaticSemantics.countLeftCapturingParensBefore wr (lkCtx lkdir pos :: ctx) =
      StaticSemantics.countLeftCapturingParensBefore_impl ctx.
  Proof.
    intros wr [] [] ctx; simpl; rewrite PeanoNat.Nat.add_0_r; reflexivity.
  Qed.

End LKFactorization.
