From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import Chars.
From Linden Require Import Groups.
From Linden Require Import Parameters.
From Warblre Require Import Base.

(** * Abstract syntax tree of JavaScript regexes *)
(* This abstract syntax tree slightly differs from Warblre's AST in order to
make it simpler to express the semantics and for a bit more simplicity. *)
(* Nonetheless, all Warblre regexes can be expressed using this AST; see
WarblreEquiv/RegexpTranslation.v . *)

(** ** We use Warblre's directions *)

(** * Lookarounds *)
Inductive lookaround: Type :=
| LookAhead
| LookBehind
| NegLookAhead
| NegLookBehind.

Definition lk_dir (lk: lookaround): Direction :=
  match lk with
  | LookAhead | NegLookAhead => forward
  | LookBehind | NegLookBehind => backward
  end.

Definition positivity (lk: lookaround): bool :=
  match lk with
  | LookAhead | LookBehind => true
  | NegLookAhead | NegLookBehind => false
  end.

(** * Anchors *)
Inductive anchor: Type :=
| BeginInput
| EndInput
| WordBoundary
| NonWordBoundary.


Section Regex.
  Context {params: LindenParameters}.

  (** * Regex Syntax  *)
  Inductive regex : Type :=
  | Epsilon
  | Character (cd : char_descr)   (* includes character classes and dot *)
  | Disjunction (r1 r2 : regex)
  | Sequence (r1 r2 : regex)
  | Quantified (greedy:bool) (min: nat) (delta: non_neg_integer_or_inf) (r1: regex) (* means any number of repetitions of r1 between min and min+delta *)
  | Lookaround (lk: lookaround) (r: regex)
  | Group (id : group_id) (r : regex)
  | Anchor (a: anchor)
  | Backreference (id: group_id).

  Definition regex_eq_dec : forall (x y : regex), { x = y } + { x <> y }.
  Proof.
    decide equality.
    - apply char_descr_eq_dec.
    - decide equality. apply PeanoNat.Nat.eq_dec.
    - apply PeanoNat.Nat.eq_dec.
    - destruct greedy; destruct greedy0; auto. right. lia.
    - decide equality.
    - apply PeanoNat.Nat.eq_dec.
    - decide equality.
    - decide equality.
  Defined.

  (* Note that this "size of the regex" counts counted quantifier as being unfolded, so it might not be linear in the size of the textual representation of the regex *)
  Fixpoint regex_size (r: regex) : nat :=
    match r with
    | Epsilon => 1
    | Regex.Character _ => 1
    | Disjunction r1 r2 => 1 + regex_size r1 + regex_size r2
    | Sequence r1 r2 => 1 + regex_size r1 + regex_size r2
    | Quantified _ min delta r1 =>
        1 + min * regex_size r1 +
          (match delta with
          | NoI.Inf => regex_size r1
          | NoI.N n => n * regex_size r1
          end)
    | Lookaround _ r1 => 1 + regex_size r1
    | Group _ r1 => 1 + regex_size r1
    | Anchor _ => 1
    | Backreference _ => 1
    end.

  (** * Group Manipulation  *)

  (* getting all groups defined in a regex for the reset *)
  Fixpoint def_groups (r:regex) : list group_id :=
    match r with
    | Epsilon | Character _  => []
    | Sequence r1 r2 | Disjunction r1 r2 => def_groups r1 ++ def_groups r2
    | Quantified _ _ _ r1 => def_groups r1
    | Lookaround _ r => def_groups r
    | Group id r1 => id::(def_groups r1)
    | Anchor _ => []
    | Backreference _ => []
    end.

  Fixpoint max_group (r:regex) : group_id :=
    match r with
    | Epsilon | Character _  | Anchor _ | Backreference _ => 0
    | Sequence r1 r2 | Disjunction r1 r2 => max (max_group r1) (max_group r2)
    | Quantified _ _ _ r | Lookaround _ r => max_group r
    | Group id r => max id (max_group r)
    end.

  (** * Common Quantifiers  *)
  (* r* *)
  Definition greedy_star (r:regex) : regex :=
    Quantified true 0 NoI.Inf r.

  (* r*? *)
  Definition lazy_star (r:regex) : regex :=
    Quantified false 0 NoI.Inf r.

  (* r+ *)
  Definition greedy_plus (r:regex) : regex :=
    Quantified true 1 NoI.Inf r.

  (* r+? *)
  Definition lazy_plus (r:regex) : regex :=
    Quantified false 1 NoI.Inf r.

  (* r? *)
  Definition greedy_qmark (r:regex) : regex :=
    Quantified true 0 (NoI.N 1) r.

  (* r?? *)
  Definition lazy_qmark (r:regex) : regex :=
    Quantified false 0 (NoI.N 1) r.

End Regex.
