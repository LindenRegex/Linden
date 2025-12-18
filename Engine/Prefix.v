(** * Regex prefixes *)

(* Definition of what a regex prefix is, namely a known string with which *)
(* every match using that regex has to start with. This is used to *)
(* accelerate regex matching by allowing us to skip input positions that *)
(* do not contain this prefix. In some cases, this even allows us to skip *)
(* the entire regex engine and just use a substring search. *)

Require Import List Lia RelationClasses FunInd Recdef Arith.
Import ListNotations.

From Linden Require Import Regex Chars Semantics Tree FunctionalSemantics.
From Linden Require Import Parameters LWParameters.
From Linden Require Import StrictSuffix.
From Linden Require Import Tactics.
From Warblre Require Import Base RegExpRecord.

Section Prefix.
  Context {params: LindenParameters}.

Inductive starts_with: string -> string -> Prop :=
| sw_nil: forall s, starts_with [] s
| sw_cons: forall h t1 t2, starts_with t1 t2 -> starts_with (h :: t1) (h :: t2).

Definition starts_with_dec:
  forall s1 s2, { starts_with s1 s2 } + { ~ starts_with s1 s2 }.
Proof.
  induction s1 as [|h1 t1 IH]; intros s2.
  - eauto using sw_nil.
  - destruct s2 as [|h2 t2].
    + right. intros H. inversion H.
    + destruct (h1 ==? h2)%wt eqn:Heq; eqdec.
      * destruct (IH t2) as [Hsw|Hnsw].
        -- left. now constructor.
        -- right. intros H. now inversion H.
      * right. intros H. now inversion H.
Defined.

Hint Constructors starts_with : prefix.

Lemma starts_with_cons_iff: forall h1 t1 h2 t2,
  starts_with (h1 :: t1) (h2 :: t2) <-> h1 = h2 /\ starts_with t1 t2.
Proof.
  split; intros.
  - inversion H; auto.
  - destruct H. subst. auto with prefix.
Qed.

Instance StartsWithPreOrder : PreOrder starts_with.
Proof.
  split.
  - (* reflexive *)
    unfold Reflexive. intro s. induction s; auto with prefix.
  - (* transitive *)
    unfold Transitive. intros s1 s2 s3 H1.
    generalize dependent s3.
    induction H1; intros; inversion H; auto with prefix.
Qed.

Lemma starts_with_app_right:
  forall s1 s2 s3,
    starts_with s1 s3 -> starts_with s1 (s3 ++ s2).
Proof.
  intros s1 s2 s3 H.
  induction H; constructor; auto.
Qed.

Lemma starts_with_app_left:
  forall s1 s2 s3,
    starts_with (s1 ++ s2) s3 -> starts_with s1 s3.
Proof.
  intro s1.
  induction s1 as [| h t IH]; intros.
  - constructor.
  - inversion H.
    constructor.
    eapply IH. eauto.
Qed.

(** * Substring search *)

(* Typeclass describing a substring search routine and its specification *)
Class StrSearch := {
  str_search : string -> string -> option nat;

  (* the found position starts with the searched substring *)
  starts_with_ss: forall s ss i, str_search ss s = Some i -> starts_with ss (List.skipn i s);
  (* there is no earlier position that starts with the searched substring *)
  no_earlier: forall s ss i, str_search ss s = Some i -> forall i', i' < i -> ~ (starts_with ss (List.skipn i' s));
  (* if the substring is not found, it cannot appear at any position of the haystack *)
  not_found: forall s ss, str_search ss s = None -> forall i, i <= length s -> ~ (starts_with ss (List.skipn i s))
}.

Lemma str_search_bound {strs: StrSearch}:
  forall ss s i,
    str_search ss s = Some i ->
    i <= length s.
Proof.
  intros ss s i H.
  pose proof (starts_with_ss _ _ _ H) as Hsw.
  destruct (le_lt_dec i (length s)); [assumption|exfalso].
  destruct ss as [|c ss'].
  - destruct i; [lia|].
    apply (no_earlier _ _ _ H i ltac:(lia)). constructor.
  - assert (Hlen: length (skipn i s) = 0) by (rewrite skipn_length; lia).
    destruct (skipn i s); [inversion Hsw|discriminate].
Qed.

Lemma str_search_succ_cons {strs: StrSearch}:
  forall ss s i,
    str_search ss s = Some (S i) ->
    exists c t, s = c :: t.
Proof.
  intros ss s i H.
  destruct s as [|c t].
  - pose proof (no_earlier _ _ _ H i ltac:(lia)) as Hn.
    pose proof (starts_with_ss _ _ _ H) as Hp.
    now rewrite skipn_nil in Hn.
  - eauto.
Qed.

Lemma str_search_succ_next {strs: StrSearch}:
  forall ss c t i,
    str_search ss (c::t) = Some (S i) ->
    str_search ss t = Some i.
Proof.
  intros ss c t i H.
  pose proof (starts_with_ss _ _ _ H) as Hsw. simpl in Hsw.
  destruct (str_search ss t) as [j|] eqn:Hst; [f_equal|exfalso].
  - destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
    + (* i < j: H should have returned None then *)
      exfalso. eapply (no_earlier _ _ _ Hst); eauto.
    + (* i = j *)
      easy.
    + (* i > j: H should have returned S j *)
      exfalso.
      pose proof (starts_with_ss _ _ _ Hst).
      now apply (no_earlier _ _ _ H (S j) ltac:(lia)).
  - (* but H returned some result, contradiction from not_found *)
    assert (i <= length t). {
      pose proof (str_search_bound _ _ _ H) as Hbound.
      simpl in Hbound. lia.
    }
    eapply not_found; eauto.
Qed.

Lemma str_search_none_next {strs: StrSearch}:
  forall ss c t,
    str_search ss (c::t) = None ->
    str_search ss t = None.
Proof.
  intros ss c t H.
  destruct (str_search ss t) eqn:Hst; [|reflexivity].
  assert (S n <= length (c::t)) by (simpl; pose proof (str_search_bound _ _ _ Hst); lia).
  apply starts_with_ss in Hst.
  now pose proof (not_found _ _ H (S n) ltac:(lia)).
Qed.

(* Search from position i onwards in string s for substring ss *)
Function brute_force_str_search (ss s: string) (i: nat) {measure (fun i => S (length s) - i) i} : option nat :=
  match Nat.leb i (length s) with
  | true => match starts_with_dec ss (List.skipn i s) with
    | left _ => Some i
    | right _ => brute_force_str_search ss s (S i)
    end
  | false => None
  end.
Proof.
  intros. apply Nat.leb_le in teq. lia.
Defined.

Lemma brute_force_str_search_starts_with:
  forall ss s i j,
    brute_force_str_search ss s i = Some j ->
    starts_with ss (List.skipn j s).
Proof.
  intros ss s i j H.
  functional induction brute_force_str_search ss s i.
  - now injection H as <-.
  - eauto.
  - discriminate.
Qed.

Lemma brute_force_str_search_no_earlier:
  forall ss s i j,
    brute_force_str_search ss s i = Some j ->
    forall k, i <= k < j ->
    ~ starts_with ss (List.skipn k s).
Proof.
  intros ss s i j H k [Hik Hkj].
  functional induction brute_force_str_search ss s i.
  - injection H as <-. lia.
  - destruct (k ==? i)%wt eqn:Heq; eqdec.
    + assumption.
    + apply IHo; [assumption|lia].
  - discriminate.
Qed.

Lemma brute_force_str_search_not_found:
  forall ss s i,
    brute_force_str_search ss s i = None ->
    forall k, i <= k <= length s ->
    ~ starts_with ss (List.skipn k s).
Proof.
  intros ss s i H k [Hik Hks] Hsw.
  functional induction brute_force_str_search ss s i.
  - discriminate.
  - destruct (k ==? i)%wt eqn:Heq; eqdec.
    + contradiction.
    + eapply IHo; [assumption|lia].
  - apply Nat.leb_gt in e. lia.
Qed.

#[refine]
Instance BruteForceStrSearch: StrSearch := {
  str_search ss s := brute_force_str_search ss s 0
}.
  (* starts_with_ss *)
  - intros. eapply brute_force_str_search_starts_with; eauto.
  (* no_earlier *)
  - intros. eapply brute_force_str_search_no_earlier; eauto. lia.
  (* not_found *)
  - intros. eapply brute_force_str_search_not_found; eauto. lia.
Defined.

(* substring search operating on inputs rather than strings *)
Definition input_search {strs: StrSearch} (p: string) (inp: input): option input :=
  match str_search p (next_str inp) with
  | Some i => Some (advance_input_n inp i forward)
  | None => None
  end.

(* returned results are the initial input or strict prefixes of it *)
Lemma input_search_strict_suffix {strs: StrSearch}:
  forall i1 i2 p, input_search p i1 = Some i2 -> i2 = i1 \/ strict_suffix i2 i1 forward.
Proof.
  unfold input_search; intros until p.
  destruct str_search; intros [=]; eauto using advance_input_n_suffix.
Qed.

(* the returned match starts with the prefix *)
Lemma input_search_starts_with {strs: StrSearch}:
  forall i1 i2 p, input_search p i1 = Some i2 -> starts_with p (next_str i2).
Proof.
  unfold input_search.
  intros i1 i2 p H.
  destruct str_search as [n|] eqn:Hsearch; [|discriminate].
  injection H as <-.
  destruct i1. simpl.
  eauto using starts_with_ss.
Qed.

(* low inclusive, high exclusive *)
Definition input_between ilow ihigh i := ((i = ilow \/ strict_suffix i ilow forward) /\ strict_suffix ihigh i forward).

(* if strict_suffix i2 i1 forward, then next_str i2 is skipn k (next_str i1) for some k > 0 *)
Lemma strict_suffix_forward_skipn:
  forall i2 i1,
    strict_suffix i2 i1 forward ->
    exists k, k > 0 /\ k <= length (next_str i1) /\ next_str i2 = List.skipn k (next_str i1).
Proof.
  intros [next2 pref2] [next1 pref1] Hss.
  apply ss_fwd_diff in Hss as [diff [Hdiff [Hnext Hpref]]].
  exists (length diff). repeat split.
  - rewrite <-length_zero_iff_nil in Hdiff. lia.
  - subst. simpl. rewrite app_length. lia.
  - simpl. rewrite Hnext, skipn_app.
    replace (length diff - length diff) with 0 by lia.
    now rewrite skipn_all2 by lia.
Qed.

(* if we found some matching input, every input in between does not have the prefix *)
Lemma input_search_no_earlier {strs: StrSearch}:
  forall i1 i2 p,
    input_search p i1 = Some i2 ->
    forall i, input_between i1 i2 i ->
    ~ (starts_with p (next_str i)).
Proof.
  unfold input_search.
  intros i1 i2 p Hsearch.
  destruct str_search as [n|] eqn:Hstrsearch; [injection Hsearch as <-|discriminate].
  pose proof (no_earlier _ _ _ Hstrsearch) as Hne.
  intros i [[<- | Hssi1] Hss2] Hstarts.
  - specialize (Hne 0).
    assert (n <> 0). {
      intros ->.
      apply ss_neq in Hss2.
      now destruct i as [next ?], next.
    }
    apply Hne; [lia|assumption].
  - apply strict_suffix_forward_skipn in Hssi1 as [k [Hkpos [Hklen Hskip]]].
    specialize (Hne k).
    rewrite Hskip in Hstarts.
    assert (k < n). {
      (* since i1 advanced by n is a strict suffix of i, and i is i1 skipped by k, then k must be smaller than n *)
      destruct i1 as [next1 pref1], i as [next pref]. simpl in *.
      apply ss_fwd_diff in Hss2 as [diff [Hdiff [Hnext _]]]. subst.
      rewrite <-length_zero_iff_nil in Hdiff.
      apply f_equal with (f:=@length Character) in Hnext.
      rewrite app_length, !skipn_length in Hnext. lia.
    }
    now apply Hne.
Qed.

(* if there is no match, the prefix is not present in the input *)
Lemma input_search_not_found {strs: StrSearch}:
  forall i1 p, input_search p i1 = None ->
  forall i, i = i1 \/ strict_suffix i i1 forward ->
  ~ (starts_with p (next_str i)).
Proof.
  unfold input_search.
  intros i1 p Hsearch.
  destruct str_search eqn:Hstrsearch; [discriminate|].
  pose proof (not_found _ _ Hstrsearch) as Hnf.
  intros i [<- | Hssi1] Hstarts.
  - specialize (Hnf 0).
    apply Hnf; [lia|assumption].
  - apply strict_suffix_forward_skipn in Hssi1 as [k [Hklow [Hkhigh Hskip]]].
    specialize (Hnf k).
    rewrite Hskip in Hstarts.
    now apply Hnf.
Qed.

Section Literal.
  Context (rer: RegExpRecord).

(** * Literals *)

(* Until now we talked about strings. Now we introduce literals, which represent *)
(* information about the literal characters appearing in a regex. Given a regex *)
(* we want to under-approximate what we know about the leading characters of any *)
(* match on that regex. This is done by "literal extraction". We distinguish several *)
(* kinds of literals explained below.*)

Variant literal : Type :=
(* the entire match is exactly `s` *)
| Exact (s : string)
(* the match starts with `s` *)
| Prefix (s : string)
(* this indicates a match cannot exist, as opposed to Prefix [] which means we do not know anything about the match *)
| Impossible.

Notation Nothing := (Exact []).
Notation Unknown := (Prefix []).

Definition literal_eq_dec: forall (l1 l2: literal), { l1 = l2 } + { l1 <> l2 }.
Proof. decide equality; apply string_eq_dec. Defined.
#[export]
Instance literal_EqDec: EqDec literal := EqDec.make literal literal_eq_dec.

(* the string with which every match of that regex from which the literal was extracted starts *)
Definition prefix (l : literal) :=
  match l with
  | Exact s => s
  | Prefix s => s
  | Impossible => []
  end.

(* the concatenation of two literals *)
Definition chain_literals (l1 l2 : literal) : literal :=
  match l1 with
  | Exact s1 => match l2 with
    | Exact s2 => Exact (s1 ++ s2)
    | Prefix s2 => Prefix (s1 ++ s2)
    | Impossible => Impossible
  end
  | Prefix s1 => match l2 with
    | Impossible => Impossible
    | _ => Prefix s1
  end
  | Impossible => Impossible
  end.

Fixpoint repeat_literal (l: literal) (base: literal) (n: nat) : literal :=
  match n with
  | 0 => base
  | S n' => chain_literals l (repeat_literal l base n')
  end.

Lemma chain_literals_assoc:
  forall l1 l2 l3,
    chain_literals l1 (chain_literals l2 l3) = chain_literals (chain_literals l1 l2) l3.
Proof.
  destruct l1, l2, l3; simpl.
  all: rewrite ?app_assoc; reflexivity.
Qed.

Lemma chain_literals_impossible:
  forall l1 l2,
    chain_literals l1 l2 = Impossible <-> (l1 = Impossible \/ l2 = Impossible).
Proof.
  intros. split; intro H.
  - destruct l1, l2; (easy || auto).
  - destruct H as [H | H]; subst.
    + easy.
    + destruct l1; easy.
Qed.

(* the longest string that is a prefix of both strings *)
Fixpoint common_prefix (s1 s2 : string) : string :=
  match s1, s2 with
  | h1 :: t1, h2 :: t2 => if h1 == h2 then h1 :: common_prefix t1 t2 else []
  | _, _ => []
  end.

(* the common literal of two literals *)
Definition merge_literals (l1 l2 : literal) : literal :=
  match l1, l2 with
  | Impossible, l2 => l2
  | l1, Impossible => l1
  | l1, l2 =>
    if l1 == l2 then l1 else Prefix (common_prefix (prefix l1) (prefix l2))
  end.

Lemma starts_with_common_prefix: forall s1 s2,
  starts_with (common_prefix s1 s2) s1.
Proof.
  induction s1; simpl.
  - reflexivity.
  - destruct s2; eqdec; constructor; auto.
Qed.

(*
  The more general lemma:
    forall l1 l2 l3,
      starts_with (prefix l1) (prefix l2) ->
      starts_with (prefix (chain_literals l1 l3)) (prefix (chain_literals l2 l3))
  does not hold (consider l1 = Exact [], l2 = Impossible).
  Thus this lemma focuses instead on a specific case. *)
Lemma starts_with_chain_merge_literals: forall l1 l2 l3,
  l1 <> Impossible ->
  starts_with (prefix (chain_literals (merge_literals l1 l2) l3)) (prefix (chain_literals l1 l3)).
Proof.
  unfold merge_literals; intros l1 l2 l3 H.
  destruct l1, l2, l3; eqdec; simpl;
    try easy;
    try apply starts_with_common_prefix;
    solve[transitivity s; [apply starts_with_common_prefix|now apply starts_with_app_right]].
Qed.

Lemma common_prefix_comm:
  forall s1 s2,
    common_prefix s1 s2 = common_prefix s2 s1.
Proof.
  induction s1; destruct s2; simpl; eqdec; congruence.
Qed.

Lemma merge_literals_comm:
  forall l1 l2,
    merge_literals l1 l2 = merge_literals l2 l1.
Proof.
  unfold merge_literals; intros.
  destruct l1, l2; eqdec; try congruence; now rewrite common_prefix_comm.
Qed.

Lemma merge_literals_impossible:
  forall l1 l2,
    merge_literals l1 l2 = Impossible <-> (l1 = Impossible /\ l2 = Impossible).
Proof.
  unfold merge_literals; intros. split; intros.
  - destruct l1, l2; now eqdec.
  - destruct H; eqdec; subst; easy.
Qed.

(* extracting literals from a character description *)
Fixpoint extract_literal_char (cd: char_descr) : literal :=
  match cd with
  | CdEmpty => Impossible
  | CdSingle c => Exact [c]
  | CdRange l h => if l == h then Exact [l] else Unknown
  | CdUnion cd1 cd2 => merge_literals (extract_literal_char cd1) (extract_literal_char cd2)
  | CdDot | CdAll | CdDigits | CdNonDigits | CdWhitespace | CdNonWhitespace | CdWordChar
  | CdNonWordChar | CdUnicodeProp _ | CdNonUnicodeProp _ | CdInv _ => Unknown
  end.

(* extracting literals from a regex *)
(*
  TODO: this could benefit from a few improvements:
  - Support lookarounds by performing intersection of overlapping literals.
    For instance /(?=abc)p/ => None, /(?<=abc)c/ => 'c' (but not exact nor prefix). This would require thinking reconsidering what Exact and Prefix mean.
  - Support anchors by detecting impossible matches, e.g., /\b\B/ => Impossible.
  - Support backreferences by mapping group ids to literals, e.g., /(abc)\1/ => 'abcabc' (exact).
*)
Fixpoint extract_literal (r: regex) : literal :=
  if RegExpRecord.ignoreCase rer then Unknown else
  match r with
  | Epsilon => Nothing
  | Regex.Character cd => extract_literal_char cd
  | Disjunction r1 r2 => merge_literals (extract_literal r1) (extract_literal r2)
  | Sequence r1 r2 => chain_literals (extract_literal r1) (extract_literal r2)
  | Quantified _ min (NoI.N 0) r1 => repeat_literal (extract_literal r1) Nothing min
  | Quantified _ min _ r1 => repeat_literal (extract_literal r1) Unknown min
  | Lookaround _ r1 => Unknown
  | Group _ r1 => extract_literal r1
  | Anchor _ => Nothing
  | Backreference _ => Unknown
  end.

Definition extract_action_literal (a : action) : literal :=
  match a with
  | Areg r => extract_literal r
  | Acheck _ => Nothing
  | Aclose _ => Nothing
  end.

Fixpoint extract_actions_literal (acts : list action) : literal :=
  match acts with
  | [] => Nothing
  | a :: rest => chain_literals (extract_action_literal a) (extract_actions_literal rest)
  end.

Hint Unfold
  prefix
  chain_literals
  merge_literals
  common_prefix
  merge_literals
  extract_action_literal
  extract_actions_literal : prefix.
Hint Resolve
  starts_with_common_prefix : prefix.
Hint Rewrite
  common_prefix_comm
  merge_literals_comm : prefix.

Ltac destruct_i := destruct RegExpRecord.ignoreCase eqn:no_i_flag.

Lemma char_match_range_same: forall c l,
  RegExpRecord.ignoreCase rer = false ->
  char_match rer c (CdRange l l) = true -> c = l.
Proof.
  unfold char_match, char_match'. intros ? ? no_i_flag H.
  rewrite
    Character.numeric_pseudo_bij,
    CharSet.exist_canonicalized_equiv,
    CharSet.exist_spec in H.
  unfold CharSet.Exists in H.
  destruct H as [x [H1 H2]].
  assert (x = l). {
    rewrite CharSet.range_spec in H1.
    assert (Character.numeric_value x = Character.numeric_value l) as H3 by lia.
    assert (Character.from_numeric_value (Character.numeric_value x) = Character.from_numeric_value (Character.numeric_value l)) as H4 by auto.
    repeat rewrite Character.numeric_pseudo_bij in H4.
    assumption.
  } subst.
  repeat rewrite (canonicalize_casesenst rer _ no_i_flag) in H2.
  symmetry. apply EqDec.inversion_true. assumption.
Qed.

Lemma extract_actions_literal_regex:
  forall r, extract_actions_literal [Areg r] = extract_literal r.
Proof.
  intros.
  unfold extract_actions_literal. simpl. destruct extract_literal.
  1: simpl; rewrite app_nil_r.
  all: reflexivity.
Qed.

(** * Impossible literals matching *)

(* if the extracted literal from a character descriptor is Impossible, there can be no match *)
Lemma extract_literal_char_impossible_no_match:
  forall cd c,
    extract_literal_char cd = Impossible ->
    ~(char_match' rer c cd = true).
Proof.
  intros cd c Hextract Hmatch.
  induction cd;
    (* the cd does not produce Impossible *)
    try solve[discriminate].
  (* CdRange *)
  - simpl in Hextract. eqdec; discriminate.
  (* CdUnion *)
  - simpl in Hextract.
    apply merge_literals_impossible in Hextract as [Hcd1 Hcd2].
    simpl in Hmatch.
    apply Bool.orb_prop in Hmatch as [Hm1 | Hm2]; eauto.
Qed.

Lemma extract_literal_impossible_general:
  forall acts tree inp gm gm',
    is_tree rer acts inp gm' forward tree ->
    extract_actions_literal acts = Impossible ->
    tree_res tree gm inp forward = None.
Proof.
  intros acts tree inp gm gm' Htree Hextract.
  remember (forward) as dir.
  generalize dependent gm.
  induction Htree; intros; subst;
    (* the result is that of the rest of the actions *)
    try solve[simpl in *; destruct RegExpRecord.ignoreCase, (extract_actions_literal cont); eauto; easy].
  (* tree_done *)
  - discriminate.
  (* tree_char *)
  - (* there is a character to read *)
    unfold read_char in READ. destruct inp, next; [discriminate|].
    (* the character matches *)
    destruct char_match eqn:Hmatch; [|discriminate]. injection READ as <-. subst.
    apply chain_literals_impossible in Hextract as [Hcd | Hcont].
    + exfalso. simpl in Hcd.
      destruct_i; [discriminate|]. apply (extract_literal_char_impossible_no_match _ _ Hcd Hmatch).
    + simpl. unfold advance_input'. eauto.
  (* tree_disj *)
  - simpl in Hextract. simpl. unfold seqop.
    simpl in IHHtree1, IHHtree2. rewrite chain_literals_impossible in IHHtree1, IHHtree2.
    apply chain_literals_impossible in Hextract as [Hmerge | Hcont].
    + destruct_i; [discriminate|].
      apply merge_literals_impossible in Hmerge as [Hex1 Hex2].
      erewrite IHHtree1, IHHtree2; auto.
    + erewrite IHHtree1, IHHtree2; auto.
  (* tree_sequence *)
  - simpl in Hextract, IHHtree.
    destruct_i.
    + destruct extract_actions_literal; try easy.
      repeat rewrite chain_literals_impossible in IHHtree.
      eapply IHHtree; eauto.
    + rewrite chain_literals_assoc in IHHtree.
      eapply IHHtree; eauto.
  (* tree_quant_forced *)
  - simpl in Hextract |- *. destruct_i.
    + simpl in IHHtree. rewrite no_i_flag in IHHtree.
      repeat rewrite chain_literals_impossible in IHHtree, Hextract.
      destruct Hextract; [discriminate|rewrite H in IHHtree].
      eapply IHHtree; auto.
    + apply chain_literals_impossible in Hextract as [Hrep | Hcont].
      * destruct plus; [destruct n|];
          apply chain_literals_impossible in Hrep as [? | ?];
          eapply IHHtree; auto;
          simpl; rewrite no_i_flag;
          do 2 rewrite chain_literals_impossible; auto.
      * eapply IHHtree; auto.
        simpl; do 2 rewrite chain_literals_impossible; auto.
  (* tree_quant_free *)
  - assert (Hex: extract_actions_literal cont = Impossible). {
      simpl in Hextract. destruct RegExpRecord.ignoreCase, plus; now destruct extract_actions_literal.
    }
    unfold greedy_choice.
    destruct greedy.
    + simpl. unfold seqop.
      rewrite IHHtree1, IHHtree2; auto.
      simpl. rewrite Hex. destruct plus; [destruct n|]; destruct (extract_literal r1); destruct_i; reflexivity.
    + simpl. unfold seqop.
      rewrite IHHtree1, IHHtree2; auto.
      simpl. rewrite Hex. destruct plus; [destruct n|]; destruct (extract_literal r1); destruct_i; reflexivity.
  (* tree_group *)
  - simpl in *.
    destruct RegExpRecord.ignoreCase, (extract_actions_literal cont); eauto; try easy.
    rewrite chain_literals_impossible in IHHtree.
    eapply IHHtree; eauto.
  (* tree_lk *)
  - simpl in Hextract |- *.
    replace (if RegExpRecord.ignoreCase rer then Unknown else Unknown) with Unknown in Hextract by now destruct_i.
    destruct extract_actions_literal eqn:Heqex in Hextract; try easy.
    rewrite IHHtree2 by auto.
    destruct positivity.
    + destruct tree_res; eauto.
      destruct l. eauto.
    + now destruct tree_res.
  (* tree_backref *)
  - simpl in Hextract |- *.
    replace (if RegExpRecord.ignoreCase rer then Unknown else Unknown) with Unknown in Hextract by now destruct_i.
    destruct extract_actions_literal; try easy.
    erewrite <-read_backref_success_advance; eauto.
Qed.

(* if there is some result, the extracted literal cannot be Impossible *)
Lemma tree_res_cannot_be_impossible_literal:
  forall r cont inp gm gm' tree res,
    is_tree rer (Areg r :: cont) inp gm forward tree ->
    tree_res tree gm' inp forward = Some res ->
    extract_literal r <> Impossible.
Proof.
  intros r cont inp gm gm' tree res Htree Hres Hext.
  eapply extract_literal_impossible_general with (gm:=gm') in Htree; simpl.
  - now rewrite Htree in Hres.
  - now rewrite Hext.
Qed.

(* extracting Impossible means there can be no match *)
Theorem extract_literal_impossible:
  forall r tree inp,
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    extract_literal r = Impossible ->
    first_leaf tree inp = None.
Proof.
  intros.
  rewrite <- (extract_actions_literal_regex r) in *.
  eapply extract_literal_impossible_general; eassumption.
Qed.


(** * Prefix of literals matching *)

Lemma chain_literals_extract_char:
  forall rest s c cd,
    RegExpRecord.ignoreCase rer = false ->
    starts_with (prefix rest) s ->
    char_match rer c cd = true ->
    starts_with (prefix (chain_literals (extract_literal_char cd) rest)) (c :: s).
Proof.
  intros rest s c cd no_i_flag Hstart Hmatch.

  Ltac unfold_match H no_i_flag :=
    unfold char_match in H; rewrite (canonicalize_casesenst _ _ no_i_flag) in H.

  induction cd;
    (* there is no known literal *)
    try solve[simpl; destruct rest; constructor].
  (* CdSingle *)
  - unfold_match Hmatch no_i_flag.
    assert (c = c0). {
      simpl in Hmatch. rewrite (canonicalize_casesenst _ _ no_i_flag) in Hmatch.
      eqdec. reflexivity.
    } subst.
    simpl.
    destruct rest; simpl; eauto with prefix.
  (* CdRange *)
  - simpl. eqdec.
    2: destruct rest; constructor.
    apply char_match_range_same in Hmatch; auto. subst.
    destruct rest; simpl; eauto with prefix.
  (* CdUnion *)
  - unfold_match Hmatch no_i_flag. simpl in Hmatch.
    apply Bool.orb_prop in Hmatch. destruct Hmatch; simpl.
    + etransitivity.
      * eapply starts_with_chain_merge_literals.
        intro. eapply extract_literal_char_impossible_no_match; eauto.
      * eapply IHcd1. unfold char_match. rewrite canonicalize_casesenst; eauto.
    + simpl. rewrite merge_literals_comm.
      etransitivity.
      * eapply starts_with_chain_merge_literals.
        intro. eapply extract_literal_char_impossible_no_match; eauto.
      * eapply IHcd2. unfold char_match. rewrite canonicalize_casesenst; eauto.
Qed.

(* generalization of extract_literal_prefix on the group map and the list of actions *)
Lemma extract_literal_prefix_general:
  forall acts tree inp gm,
    is_tree rer acts inp Groups.GroupMap.empty forward tree ->
    (exists result, tree_res tree gm inp forward = Some result) ->
    starts_with (prefix (extract_actions_literal acts)) (next_str inp).
Proof.
  intros acts tree inp gm Htree [result Hleaf].
  remember (forward) as dir.
  generalize dependent result.
  generalize dependent gm.
  induction Htree; intros; subst;
  	(* eliminated cases when ignoreCase flag is true *)
    try (simpl; destruct_i; [destruct extract_actions_literal|]);
    (* the prefix is empty *)
    try solve[(constructor || simpl; destruct (extract_actions_literal cont); constructor)];
    (* the literal is that of the rest of the actions *)
    try solve[simpl in *;
      destruct (extract_actions_literal cont); eapply IHHtree; eauto with prefix];
    (* mismatch violating tree_res result *)
    try discriminate Hleaf.
  (* tree_char *)
  - (* there is a character to read *)
    unfold read_char in READ; destruct inp; destruct next; try discriminate READ; subst;
    (* the character matches *)
    destruct char_match eqn:Heqmatch; try discriminate READ; injection READ; intros; subst.
    apply chain_literals_extract_char; eauto.
  (* tree_disj *)
  - simpl in Hleaf. unfold seqop in Hleaf.
    destruct (tree_res t1) eqn:Heqres; simpl in *.
    + pose proof (tree_res_cannot_be_impossible_literal _ _ _ _ _ _ _ Htree1 Heqres).
      etransitivity; eauto using starts_with_chain_merge_literals.
    + simpl. rewrite merge_literals_comm.
      pose proof (tree_res_cannot_be_impossible_literal _ _ _ _ _ _ _ Htree2 Hleaf).
      etransitivity; eauto using starts_with_chain_merge_literals.
  (* tree_sequence *)
  - simpl. rewrite <-chain_literals_assoc.
    eauto.
  (* tree_quant_forced *)
  - simpl in IHHtree |- *. rewrite no_i_flag in IHHtree.
    destruct min.
    (* min = 0 *)
    + destruct plus. destruct n.
      (* max > 0 *)
      2, 3: rewrite <- chain_literals_assoc; eapply IHHtree; eauto.
      (* min = max = 0 *)
      simpl in *. destruct extract_actions_literal; destruct extract_literal; simpl;
      try rewrite app_nil_r;
      (eapply starts_with_app_left; eapply IHHtree; eauto) ||
      eauto.
      (* min > 0 *)
    + destruct plus. destruct n.
      all: rewrite <- chain_literals_assoc; eapply IHHtree; eauto.
  (* tree_quant_free *)
  - simpl.
    destruct plus; destruct extract_actions_literal; constructor.
Qed.

(* main theorem: every match starts with the extracted literal *)
Theorem extract_literal_prefix:
  forall r tree inp,
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    (exists result, first_leaf tree inp = Some result) ->
    starts_with (prefix (extract_literal r)) (next_str inp).
Proof.
  intros.
  rewrite <- (extract_actions_literal_regex r).
  eapply extract_literal_prefix_general; eassumption.
Qed.

Lemma is_none_iff_not_exists_some:
  forall {A: Type} (o: option A),
    o = None <-> ~ (exists x: A, o = Some x).
Proof.
  split; intro H.
  - intros [? ?]. now subst.
  - destruct o; [exfalso|]; eauto.
Qed.

(* the contrapositive of extract_literal_prefix *)
Corollary extract_literal_prefix_general_contra:
  forall acts tree inp,
    is_tree rer acts inp Groups.GroupMap.empty forward tree ->
    ~(starts_with (prefix (extract_actions_literal acts)) (next_str inp)) ->
    first_leaf tree inp = None.
Proof.
  intros.
  rewrite is_none_iff_not_exists_some.
  eauto using extract_literal_prefix_general.
Qed.

Corollary extract_literal_prefix_contra:
  forall r tree inp,
    is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
    ~(starts_with (prefix (extract_literal r)) (next_str inp)) ->
    first_leaf tree inp = None.
Proof.
  intro r; rewrite <- (extract_actions_literal_regex r).
  intros.
  eauto using extract_literal_prefix_general_contra.
Qed.


(** * Extracted literals size *)

Lemma chain_literals_length:
  forall l1 l2,
    length (prefix (chain_literals l1 l2)) <= length (prefix l1) + length (prefix l2).
Proof.
  destruct l1, l2; simpl; try rewrite app_length; lia.
Qed.

Lemma repeat_literal_length:
  forall l base n,
    length (prefix (repeat_literal l base n)) <=
      n * length (prefix l) + length (prefix base).
Proof.
  induction n; intros; simpl.
  - lia.
  - rewrite chain_literals_length.
    lia.
Qed.

Lemma common_prefix_length:
  forall s1 s2,
    length (common_prefix s1 s2) <= Nat.min (length s1) (length s2).
Proof.
  induction s1; destruct s2; simpl; try lia.
  eqdec; simpl.
  - specialize (IHs1 s2). lia.
  - lia.
Qed.

Lemma merge_literals_length:
  forall l1 l2,
    length (prefix (merge_literals l1 l2)) <= Nat.max (length (prefix l1)) (length (prefix l2)).
Proof.
  intros l1 l2; unfold merge_literals.
  destruct l1, l2; eqdec; try pose proof (common_prefix_length s s0); simpl; try lia.
Qed.

(* note: this will not hold true if support for backreferences is added.
    Consider /(abc)\1\1/. The extracted literal would be 'abcabcabc' which is not upperbounded by the regex size.
*)
(* The size of extracted literals is bounded by the size of the regex *)
Theorem extract_literal_size_bound:
  forall r,
    length (prefix (extract_literal r)) <= regex_size r.
Proof.
  induction r; simpl; destruct_i; simpl; try lia.
  (* Character *)
  - induction cd; simpl; try lia.
    + eqdec; simpl; lia.
    + pose proof (merge_literals_length (extract_literal_char cd1) (extract_literal_char cd2)); lia.
  (* Disjunction *)
  - pose proof (merge_literals_length (extract_literal r1) (extract_literal r2)); lia.
  (* Sequence *)
  - pose proof (chain_literals_length (extract_literal r1) (extract_literal r2)); lia.
  (* Quantified *)
  - induction min; (destruct delta; [destruct n|]); simpl;
      try pose proof (chain_literals_length (extract_literal r) (repeat_literal (extract_literal r) Nothing min));
      try pose proof (chain_literals_length (extract_literal r) (repeat_literal (extract_literal r) Unknown min));
      lia.
Qed.

End Literal.
End Prefix.
