From Stdlib Require Import List Lia Bool.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree.
From Linden Require Import Semantics PikeSubset.
From Linden Require Import Parameters LWParameters.
From Warblre Require Import Numeric Base RegExpRecord.

(* In order to annotate Fork instructions with Peeking information,
   we define a PeekingAnalysis, used during NFA compilation.
   This analysis depends on a single disjointness checker,
   that analyses if two character descriptor are disjoint,
   but may return an under-approximation (it's ok to say that two
   descriptors are non-disjoint even when they are).
 *)

Section PeekingAnalysis.

  Context {params: LindenParameters} (rer: RegExpRecord).

  Definition disjoint (cd1 cd2: char_descr) : Prop :=
    forall c, char_match rer c cd1 && char_match rer c cd2 = false.

  (* the compiler relies only on a sound check of disjointness *)
  (* sound meaning an under-approximation of disjointness is allowed *)
  Class Disjoint := {
      disjoint_checker: char_descr -> char_descr -> bool;
      checker_sound: forall cd1 cd2,
        disjoint_checker cd1 cd2 = true -> disjoint cd1 cd2
    }.

  (** * NoPeeking Trivial Disjointness Checker  *)
  (* the best way to deactivate the Peeking optimization is to provide
     the compiler with a disjointness checker that always return false.
     This is a sound checker *)

  Definition nopeek_checker (cd1 cd2:char_descr) : bool := false.

  Theorem sound_nopeek_checker:
    forall cd1 cd2, nopeek_checker cd1 cd2 = true -> disjoint cd1 cd2.
  Proof. unfold nopeek_checker. intros. inversion H. Qed.

  (* The NoPeeking Checker *)
  Definition nopeeking : Disjoint :=
    {| disjoint_checker := nopeek_checker; checker_sound := sound_nopeek_checker |}.


  (** * Practical Disjointness Checker *)
  (* the goal of this checker is not to be as precise as it can.
     the goal is to decide disjointness in few computations.
     It only compares single characters and ranges. *)

  (* the only kinds of character descriptors we compare *)
  Inductive comparable : Type :=
  | CompRange (low high:nat)
  | CompSet (cs:CharSet)
  | Uncomparable.

  (* abstract character descriptors as comparables *)
  (* only "simple" sets are modeled, not their negation *)
  Definition tocomp (cd: char_descr) : comparable :=
    match cd with
    | CdSingle c => CompRange (Character.numeric_value c) (Character.numeric_value c)
    | CdRange l h => CompRange (Character.numeric_value l) (Character.numeric_value h)
    | CdDigits => CompSet Characters.digits
    | CdWhitespace => CompSet (CharSet.union Characters.white_spaces Characters.line_terminators)
    | CdWordChar => CompSet (wordCharacters rer)
    | _ => Uncomparable
    end.

  (* when two character descriptors are the exact complement of one another *)
  Definition complements (cd1 cd2: char_descr) : bool :=
    match cd1, cd2 with
    | CdDigits, CdNonDigits | CdWhitespace, CdNonWhitespace | CdWordChar, CdNonWordChar => true
    | _, _ => false
    end.
  (* LATER: instead of these complements, we could add a comparable: the negation of a charset *)
  (* this would allow to see that, e.g., 9 is disjoint from CdNonDigit,
     by checking that 9 is infact inside Digits.  *)

  (* The following function assumes that ignoreCase is turned off.
     It computes disjointness of comparables, or exact complements descriptors *)
  Definition comparable_disjoint (cd1 cd2:char_descr) : bool :=
    match (tocomp cd1), (tocomp cd2) with
    | CompRange l1 h1, CompRange l2 h2 => Nat.ltb h1 l2 || Nat.ltb h2 l1
    | CompRange l h, CompSet s | CompSet s, CompRange l h =>
       forallb (fun e => orb (Nat.ltb (Character.numeric_value e) l) (Nat.ltb h (Character.numeric_value e))) (CharSet.elements s)
    | CompSet s1, CompSet s2 =>
        forallb (fun e => negb (CharSet.contains s2 e)) (CharSet.elements s1)
    | _, _ => complements cd1 cd2 || complements cd2 cd1
    end.

  (* the practical checker, on descriptors other than unions: the empty class, a
     descriptor and its inversion, distinct characters and, without ignoreCase,
     [comparable_disjoint] *)
  Definition atoms_disjoint (cd1 cd2: char_descr) : bool :=
    match cd1, cd2 with
    | CdEmpty, _ | _, CdEmpty => true
    | CdInv a, _ => if char_descr_eq_dec a cd2 then true else false
    | _, CdInv b => if char_descr_eq_dec cd1 b then true else false
    | CdSingle c, CdSingle d => negb (Character.canonicalize rer c == Character.canonicalize rer d)
    | _, _ => if RegExpRecord.ignoreCase rer then false else comparable_disjoint cd1 cd2
    end.

  (* when cd2 is a union, check that cd1 is disjoint with all branches of the union *)
  Fixpoint excludes (cd1 cd2: char_descr) : bool :=
    match cd2 with
    | CdUnion a b => excludes cd1 a && excludes cd1 b
    | _ => atoms_disjoint cd1 cd2
    end.

  Fixpoint practical_disjoint (cd1 cd2: char_descr) : bool :=
    match cd1 with
    | CdUnion a b => practical_disjoint a cd2 && practical_disjoint b cd2
    | _ => excludes cd1 cd2
    end.

  (** * Practical Checker Correctness  *)

  (* without ignoreCase, a class matches exactly its characters *)
  Lemma ec_contains: forall s x, RegExpRecord.ignoreCase rer = false ->
    CharSet.exist_canonicalized rer s x = CharSet.contains s x.
  Proof.
    intros s x IC. apply eq_true_iff_eq.
    rewrite CharSet.exist_canonicalized_equiv, CharSet.exist_spec, CharSet.contains_spec.
    split; [intros [e [I E]]|exists x; split]; try rewrite Character.canonicalize_casesenst in * by auto;
      try rewrite EqDec.inversion_true in * by auto; subst; auto.
  Qed.

  Lemma atoms_disjoint_sound: forall cd1 cd2, atoms_disjoint cd1 cd2 = true -> disjoint cd1 cd2.
  Proof.
    intros cd1 cd2 D x. destruct (char_match rer x cd1) eqn:M, (char_match rer x cd2) eqn:M2; auto. exfalso.
    unfold char_match in *.
    destruct cd1, cd2; cbn [atoms_disjoint] in D; try discriminate;
      repeat match type of D with context [char_descr_eq_dec ?a ?b] => destruct (char_descr_eq_dec a b); subst end;
      cbn [char_match'] in *; try discriminate.
    all: try (first [rewrite M in M2|rewrite M2 in M]; discriminate).
    all: try (rewrite ?EqDec.inversion_true in M, M2; rewrite <- M, <- M2, EqDec.reflb in D; discriminate).
    all: destruct (RegExpRecord.ignoreCase rer) eqn:IC; try discriminate.
    all: unfold comparable_disjoint, tocomp, complements in D;
      rewrite ?Character.canonicalize_casesenst, ?ec_contains, ?EqDec.inversion_true, ?CharSet.contains_spec,
        ?Character.numeric_pseudo_bij, ?CharSet.range_spec, ?CharSet.remove_all_spec in * by auto; subst.
    all: try (rewrite forallb_forall in D; match goal with I: CharSet.In ?y _ |- _ =>
      specialize (D y (proj2 (CharSet.elements_spec1 _ _) I)) end).
    all: rewrite ?orb_true_iff, ?negb_true_iff, <- ?not_true_iff_false, ?PeanoNat.Nat.ltb_lt, ?CharSet.contains_spec,
      ?CharSet.union_spec in *; intuition (try lia).
  Qed.

  Lemma practical_disjoint_sound: forall cd1 cd2, practical_disjoint cd1 cd2 = true -> disjoint cd1 cd2.
  Proof.
    assert (E: forall cd2 cd1, excludes cd1 cd2 = true -> disjoint cd1 cd2).
    { induction cd2; intros cd1 D; try exact (atoms_disjoint_sound _ _ D).
      apply andb_prop in D as [D1 D2]. intros x.
      change (char_match rer x (CdUnion ?a ?b)) with (char_match rer x a || char_match rer x b). rewrite andb_orb_distrib_r. now rewrite (IHcd2_1 _ D1), (IHcd2_2 _ D2). }
    induction cd1; intros cd2 D; try exact (E _ _ D).
    apply andb_prop in D as [D1 D2]. intros x.
    change (char_match rer x (CdUnion ?a ?b)) with (char_match rer x a || char_match rer x b). rewrite andb_orb_distrib_l. now rewrite (IHcd1_1 _ D1), (IHcd1_2 _ D2).
  Qed.

  (* the practical disjointness checker *)
  (* it is given priority 0: this is the default checker *)
  #[global] Instance practical_disjointness : Disjoint | 0 :=
    {| disjoint_checker := practical_disjoint; checker_sound := practical_disjoint_sound |}.

  (** * Strictly Nullable Analysis  *)
  (* this is used to analyze a sequence after a quantifier in the begins analysis below *)

  (* an under-approximating strictly nullable analysis to help analyze the sequence *)
  Fixpoint strictly_nullable (r:regex) : bool :=
    match r with
    | Epsilon | Lookaround _ _ | Anchor _ => true
    | Regex.Character _ | Backreference _ => false
    | Disjunction r1 r2 | Sequence r1 r2 => andb (strictly_nullable r1) (strictly_nullable r2)
    | Quantified _ _ _ r1 | Group _ r1 => strictly_nullable r1
    end.

  (* lifted to actions to facilitate the proofs *)
  Definition strictly_nullable_action (a:action) : bool :=
    match a with
    | Areg r => strictly_nullable r
    | Acheck _ | Aclose _ => true
    end.

  Definition strictly_nullable_actions (l:actions) : bool :=
    forallb strictly_nullable_action l.

  Ltac sn_ih IH := apply IH; simpl; repeat (apply andb_true_intro; split); auto.

  Lemma strictly_nullable_actions_leaves:
    forall act inp gm dir t,
      is_tree rer act inp gm dir t ->
      strictly_nullable_actions act = true ->
      forall gm', Forall (fun lf => fst lf = inp) (tree_leaves t gm' inp dir).
  Proof.
    unfold strictly_nullable_actions.
    intros act inp gm dir t TREE. induction TREE; intros SN gm'; simpl in *; try discriminate;
      repeat match goal with H: _ && _ = true |- _ => apply andb_prop in H as [? ?] end;
      try solve [auto | sn_ih IHTREE].
    - apply Forall_app. split; [sn_ih IHTREE1|sn_ih IHTREE2].
    - destruct dir; sn_ih IHTREE.
    - subst. destruct greedy; simpl; try apply Forall_app; split; try sn_ih IHTREE1; sn_ih IHTREE2.
    - destruct positivity; destruct tree_leaves as [|[]]; auto; sn_ih IHTREE2.
  Qed.

  Lemma strictly_nullable_leaves_no_adv:
    forall r inp gm dir t, strictly_nullable r = true ->
         is_tree rer [Areg r] inp gm dir t ->
         Forall (fun lf => fst lf = inp) (tree_leaves t gm inp dir).
  Proof.
    intros r SN inp gm dir t TREE.
    eapply strictly_nullable_actions_leaves; eauto.
    simpl. apply andb_true_iff. auto.
  Qed.

  (** * Begins Analysis  *)
  (* For quantifiers, to know if peeking is possible, we need to know what the
   sub-regex after the quantifier must begin with. *)

  (* returns a character descriptor that a regex must begin by matching *)
  (* None means that we can't know for sure what the regex begins with *)
  Fixpoint begins (r:regex) : option char_descr :=
    match r with
    | Regex.Character cd => Some cd
    | Group _ r1 => begins r1
    | Sequence r1 r2 =>
        match strictly_nullable r1 with
        | true => begins r2
        | false => begins r1
        end
    | Disjunction r1 r2 =>
        match begins r1, begins r2 with
        | Some cd1, Some cd2 => Some (CdUnion cd1 cd2)
        | _, _ => None
        end
    | _ => None
    end.

  (* lift to actions for the proof *)
  Fixpoint begins_actions (l:list action) : option char_descr :=
    match l with
    | [] => None
    | Areg r :: cont =>
        match begins r with
        | Some cd => Some cd
        | None => if strictly_nullable r then begins_actions cont else None
        end
    | _ :: cont => begins_actions cont
    end.

  Lemma begins_not_nullable:
    forall r cd, begins r = Some cd -> strictly_nullable r = false.
  Proof.
    induction r; simpl; intros d B; try discriminate; auto.
    - destruct (begins r1) eqn:B1, (begins r2) eqn:B2; try discriminate.
      erewrite IHr1; eauto.
    - destruct (strictly_nullable r1); auto. eapply IHr2; eauto.
    - eapply IHr; eauto.
  Qed.

  Lemma begins_actions_nullable:
    forall r l, strictly_nullable r = true -> begins_actions (Areg r :: l) = begins_actions l.
  Proof.
    intros r l SN. simpl. destruct (begins r) eqn:B.
    - apply begins_not_nullable in B. rewrite SN in B. inversion B.
    - rewrite SN. auto.
  Qed.

  Lemma read_char_union:
    forall c1 c2 inp, read_char rer (CdUnion c1 c2) inp forward = None ->
      read_char rer c1 inp forward = None /\ read_char rer c2 inp forward = None.
  Proof.
    intros c1 c2 [next pref] R. simpl in *. destruct next as [|h next]; auto.
    change (char_match rer h (CdUnion c1 c2)) with (char_match rer h c1 || char_match rer h c2) in R.
    destruct (char_match rer h c1), (char_match rer h c2); simpl in *; try discriminate; auto.
  Qed.

  Lemma begins_actions_seq:
    forall r1 r2 cont cd,
      begins_actions (Areg (Sequence r1 r2) :: cont) = Some cd ->
      begins_actions (Areg r1 :: Areg r2 :: cont) = Some cd.
  Proof.
    intros r1 r2 cont cd B. simpl in *.
    destruct (strictly_nullable r1) eqn:N1.
    - destruct (begins r1) eqn:B1; [apply begins_not_nullable in B1; congruence|]. auto.
    - destruct (begins r1); auto.
  Qed.

  Theorem begins_actions_correct:
    forall act inp gm t cd
      (TREE: is_tree rer act inp gm forward t)
      (BEG: begins_actions act = Some cd)
      (READ: read_char rer cd inp forward = None),
      tree_res t gm inp forward = None.
  Proof.
    intros act inp gm t cd TREE. generalize dependent cd. remember forward as dir eqn:F.
    induction TREE; intros d BEG READC; subst; simpl in BEG; simpl; try discriminate; eauto.
    - inversion BEG. subst. congruence.
    - destruct (begins r1) eqn:B1, (begins r2) eqn:B2.
      + inversion BEG. subst. apply read_char_union in READC as [R1 R2].
        rewrite (IHTREE1 eq_refl c), (IHTREE2 eq_refl c0); auto; simpl;
          try rewrite B1; try rewrite B2; auto.
      + apply begins_not_nullable in B1. rewrite B1 in BEG. simpl in BEG. inversion BEG.
      + apply begins_not_nullable in B2. rewrite B2, andb_false_r in BEG. inversion BEG.
      + destruct (strictly_nullable r1) eqn:SN1, (strictly_nullable r2) eqn:SN2; simpl in BEG; try discriminate.
        rewrite (IHTREE1 eq_refl d), (IHTREE2 eq_refl d); auto; simpl;
          try rewrite B1; try rewrite B2; try rewrite SN1; try rewrite SN2; auto.
    - apply (IHTREE eq_refl d); auto. simpl. apply (begins_actions_seq r1 r2 cont d). auto.
    - destruct (strictly_nullable r1) eqn:SN; try discriminate.
      apply (IHTREE eq_refl d); auto. rewrite begins_actions_nullable by auto. simpl. rewrite SN. auto.
    - destruct (strictly_nullable r1) eqn:SN; try discriminate. apply (IHTREE eq_refl d); auto.
    - destruct (strictly_nullable r1) eqn:SN; try discriminate.
      assert (T1: tree_res titer (GroupMap.reset (def_groups r1) gm) inp forward = None).
      { apply (IHTREE1 eq_refl d); auto. rewrite begins_actions_nullable by auto.
        simpl. rewrite SN. auto. }
      assert (T2: tree_res tskip gm inp forward = None).
      { apply (IHTREE2 eq_refl d); auto. }
      subst. destruct greedy; simpl; try rewrite T1; try rewrite T2; auto.
    - destruct positivity; destruct tree_res as [[]|]; auto;
        eapply res_indep; apply (IHTREE2 eq_refl d); auto.
  Qed.

  Corollary begins_correct:
    forall r cont inp gm t cd
      (TREE: is_tree rer (Areg r :: cont) inp gm forward t)
      (BEG: begins r = Some cd)
      (READ: read_char rer cd inp forward = None),
      tree_res t gm inp forward = None.
  Proof.
    intros. eapply begins_actions_correct; eauto. simpl. rewrite BEG. auto.
  Qed.

End PeekingAnalysis.
