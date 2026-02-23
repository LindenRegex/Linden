From Warblre Require Import Patterns Result Errors Coercions Notation Base StaticSemantics.
From Warblre Require Characters.
From Warblre Require EarlyErrors.
From Linden Require Import Regex LWParameters Parameters Chars Groups Tactics.
Import Notation.
Import Result.
Import Result.Notations.
Local Open Scope result_flow.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Lia.

(** * Syntactic equivalence between Warblre regexes and Linden regexes
and translation from Warblre to Linden regexes *)

Section RegexpTranslation.
  Context {params: LindenParameters}.

  (* NamedMap: relating named groups to indices  *)

  Definition patname_eq_dec : forall (x y : Patterns.GroupName), { x = y } + { x <> y }.
  Proof. decide equality. apply Character.eq_dec. Qed.
  Definition patname_eqb (n1 n2:Patterns.GroupName) : bool :=
    if patname_eq_dec n1 n2 then true else false.

  Definition namedmap : Type := list (Patterns.GroupName * nat).
  Definition nameidx (nm:namedmap) (name:Patterns.GroupName) : option nat :=
    SetoidList.findA (fun n => patname_eqb n name) nm.

  (* Computing the named map of a Warblre regex *)
  Fixpoint buildnm' (wr:Patterns.Regex) (nm:namedmap) (n:nat) : namedmap * nat :=
    match wr with
    | Patterns.Empty | Patterns.Char _ | Patterns.Dot | Patterns.AtomEsc _ | Patterns.CharacterClass _
    | Patterns.InputStart | Patterns.InputEnd | Patterns.WordBoundary | Patterns.NotWordBoundary => (nm,n)
    | Patterns.Disjunction wr1 wr2 | Patterns.Seq wr1 wr2 =>
                                       let (nm1,n1) := buildnm' wr1 nm n in
                                       buildnm' wr2 nm1 n1
    | Patterns.Lookahead wr1 | Patterns.NegativeLookahead wr1
    | Patterns.Lookbehind wr1 | Patterns.NegativeLookbehind wr1
    | Patterns.Quantified wr1 _ => buildnm' wr1 nm n
    | Patterns.Group None wr1 => buildnm' wr1 nm (S n)
    | Patterns.Group (Some name) wr1 => buildnm' wr1 ((name,S n)::nm) (S n)
    end.

  Definition buildnm (wr:Patterns.Regex) : namedmap :=
    fst (buildnm' wr [] 0).

  (* Computes the number of capture groups of the regex r. *)
  Fixpoint num_groups (r: regex): nat := (* actually len (def_groups r); TODO replace later or prove lemma *)
    match r with
    | Epsilon | Character _ => 0
    | Disjunction r1 r2 => num_groups r1 + num_groups r2
    | Sequence r1 r2 => num_groups r1 + num_groups r2
    | Quantified _ _ _ r1 => num_groups r1
    | Group _ r1 => S (num_groups r1)
    | Lookaround _ r1 => num_groups r1
    | Anchor _ | Backreference _ => 0
    end.

  (* Equivalence of greedy/lazy quantifier prefixes. *)
  Inductive equiv_greedylazy: (Patterns.QuantifierPrefix -> Patterns.Quantifier) -> bool -> Prop :=
  | Equiv_greedy: equiv_greedylazy Patterns.Greedy true
  | Equiv_lazy: equiv_greedylazy Patterns.Lazy false.

  (* Equivalence of quantifiers. *)
  Inductive equiv_quantifier: Patterns.QuantifierPrefix -> (bool -> regex -> regex) -> Prop :=
  | Equiv_star: equiv_quantifier Patterns.Star (fun greedy => Quantified greedy 0 +∞)
  | Equiv_plus: equiv_quantifier Patterns.Plus (fun greedy => Quantified greedy 1 +∞)
  | Equiv_question: equiv_quantifier Patterns.Question (fun greedy => Quantified greedy 0 (NoI.N 1))
  | Equiv_repexact: forall n, equiv_quantifier (Patterns.RepExact n) (fun greedy => Quantified greedy n (NoI.N 0))
  | Equiv_reppartialrange: forall n, equiv_quantifier (Patterns.RepPartialRange n) (fun greedy => Quantified greedy n +∞)
  | Equiv_reprange: forall mini maxi, mini <= maxi -> equiv_quantifier (Patterns.RepRange mini maxi) (fun greedy => Quantified greedy mini (NoI.N (maxi-mini))).

  (* Equivalence of lookarounds. *)
  Inductive equiv_lookaround: (Patterns.Regex -> Patterns.Regex) -> lookaround -> Prop :=
  | Equiv_lookahead: equiv_lookaround Patterns.Lookahead LookAhead
  | Equiv_neglookahead: equiv_lookaround Patterns.NegativeLookahead NegLookAhead
  | Equiv_lookbehind: equiv_lookaround Patterns.Lookbehind LookBehind
  | Equiv_neglookbehind: equiv_lookaround Patterns.NegativeLookbehind NegLookBehind.

  (* Equivalence of anchors. *)
  Inductive equiv_anchor: Patterns.Regex -> anchor -> Prop :=
  | Equiv_input_start: equiv_anchor Patterns.InputStart BeginInput
  | Equiv_input_end: equiv_anchor Patterns.InputEnd EndInput
  | Equiv_word_boundary: equiv_anchor Patterns.WordBoundary WordBoundary
  | Equiv_non_word_boundary: equiv_anchor Patterns.NotWordBoundary NonWordBoundary
  .


  (** ** Equivalence of AtomEscapes that correspond to character classes (not backreferences). *)
  (* CharacterClassEscape *)
  Inductive equiv_CharacterClassEscape: Patterns.CharacterClassEscape -> char_descr -> Prop :=
  | Equiv_esc_d: equiv_CharacterClassEscape Patterns.esc_d CdDigits
  | Equiv_esc_D: equiv_CharacterClassEscape Patterns.esc_D CdNonDigits
  | Equiv_esc_s: equiv_CharacterClassEscape Patterns.esc_s CdWhitespace
  | Equiv_esc_S: equiv_CharacterClassEscape Patterns.esc_S CdNonWhitespace
  | Equiv_esc_w: equiv_CharacterClassEscape Patterns.esc_w CdWordChar
  | Equiv_esc_W: equiv_CharacterClassEscape Patterns.esc_W CdNonWordChar
  | Equiv_UnicodeProp: forall p, equiv_CharacterClassEscape (Patterns.UnicodeProp p) (CdUnicodeProp p)
  | Equiv_UnicodePropNeg: forall p, equiv_CharacterClassEscape (Patterns.UnicodePropNeg p) (CdNonUnicodeProp p)
  .

  (* ControlEscape *)
  Inductive equiv_ControlEscape: Patterns.ControlEscape -> char_descr -> Prop :=
  | Equiv_esc_f: equiv_ControlEscape Patterns.esc_f (CdSingle Characters.FORM_FEED)
  | Equiv_esc_n: equiv_ControlEscape Patterns.esc_n (CdSingle Characters.LINE_FEED)
  | Equiv_esc_r: equiv_ControlEscape Patterns.esc_r (CdSingle Characters.CARRIAGE_RETURN)
  | Equiv_esc_t: equiv_ControlEscape Patterns.esc_t (CdSingle Characters.CHARACTER_TABULATION)
  | Equiv_esc_v: equiv_ControlEscape Patterns.esc_v (CdSingle Characters.LINE_TABULATION).

  (* AsciiControlEsc *)
  Inductive equiv_asciiesc: AsciiLetter -> char_descr -> Prop :=
  | Equiv_asciiesc:
    forall l n,
      n = NonNegInt.modulo (AsciiLetter.numeric_value l) 32 ->
      equiv_asciiesc l (CdSingle (Character.from_numeric_value n))
  .

  Definition unicodeCodePoint (head tail: Hex4Digits) :=
    (*>> 1. Let lead be the CharacterValue of HexLeadSurrogate. <<*)
    let lead := StaticSemantics.characterValue_Hex4Digits head in
    (*>> 2. Let trail be the CharacterValue of HexTrailSurrogate. <<*)
    let trail := StaticSemantics.characterValue_Hex4Digits tail in
    (*>> 3. Let cp be UTF16SurrogatePairToCodePoint(lead, trail). <<*)
    let cp := Unicode.utf16SurrogatePair lead trail in
    (*>> 4. Return the numeric value of cp. <<*)
    cp.

  (* CharacterEscape *)
  Inductive equiv_CharacterEscape: Patterns.CharacterEscape -> char_descr -> Prop :=
  | Equiv_ControlEsc: forall esc cd, equiv_ControlEscape esc cd -> equiv_CharacterEscape (Patterns.ControlEsc esc) cd
  | Equiv_AsciiControlEsc: forall l cd, equiv_asciiesc l cd -> equiv_CharacterEscape (Patterns.AsciiControlEsc l) cd
  | Equiv_esc_Zero: equiv_CharacterEscape Patterns.esc_Zero (CdSingle (Character.from_numeric_value 0))
  | Equiv_HexEscape: forall d1 d2: HexDigit, equiv_CharacterEscape (Patterns.HexEscape d1 d2) (CdSingle (Character.from_numeric_value (HexDigit.to_integer_2 d1 d2)))
  | Equiv_IdentityEsc: forall c, equiv_CharacterEscape (Patterns.IdentityEsc c) (CdSingle c)
  | Equiv_UnicodeEsc_Pair: forall head tail, equiv_CharacterEscape (Patterns.UnicodeEsc (Patterns.Pair head tail)) (CdSingle (Character.from_numeric_value (unicodeCodePoint head tail)))
  | Equiv_UnicodeEsc_Lonely: forall hex, equiv_CharacterEscape (Patterns.UnicodeEsc (Patterns.Lonely hex)) (CdSingle (Character.from_numeric_value (StaticSemantics.characterValue_Hex4Digits hex)))
  | Equiv_UnicodeEsc_CodePoint: forall c, equiv_CharacterEscape (Patterns.UnicodeEsc (Patterns.CodePoint c)) (CdSingle c)
  .


  (** ** Equivalence of character classes *)
  Inductive equiv_ClassEscape: Patterns.ClassEscape -> char_descr -> Prop :=
  | Equiv_esc_b: equiv_ClassEscape Patterns.esc_b (CdSingle Characters.BACKSPACE)
  | Equiv_esc_Dash: equiv_ClassEscape Patterns.esc_Dash (CdSingle Characters.HYPHEN_MINUS)
  | Equiv_CCharacterClassEsc: forall esc cd, equiv_CharacterClassEscape esc cd -> equiv_ClassEscape (Patterns.CCharacterClassEsc esc) cd
  | Equiv_CCharacterEsc: forall esc cd, equiv_CharacterEscape esc cd -> equiv_ClassEscape (Patterns.CCharacterEsc esc) cd.

  Inductive equiv_ClassAtom: Patterns.ClassAtom -> char_descr -> Prop :=
  | Equiv_SourceCharacter: forall c: Parameters.Character, equiv_ClassAtom (Patterns.SourceCharacter c) (CdSingle c)
  | Equiv_ClassEsc: forall esc cd, equiv_ClassEscape esc cd -> equiv_ClassAtom (Patterns.ClassEsc esc) cd.

  Inductive equiv_ClassRanges: Patterns.ClassRanges -> char_descr -> Prop :=
  | Equiv_EmptyCR: equiv_ClassRanges Patterns.EmptyCR CdEmpty
  | Equiv_ClassAtomCR: forall ca cacd t tcd, equiv_ClassAtom ca cacd -> equiv_ClassRanges t tcd -> equiv_ClassRanges (Patterns.ClassAtomCR ca t) (CdUnion cacd tcd)
  | Equiv_RangeCR:
    forall l h cl ch t tcd,
      equiv_ClassAtom l (CdSingle cl) -> equiv_ClassAtom h (CdSingle ch) ->
      Character.numeric_value cl <= Character.numeric_value ch ->
      equiv_ClassRanges t tcd ->
      equiv_ClassRanges (Patterns.RangeCR l h t) (CdUnion (CdRange cl ch) tcd).

  Inductive equiv_CharClass: Patterns.CharClass -> char_descr -> Prop :=
  | Equiv_NoninvertedCC: forall crs cd, equiv_ClassRanges crs cd -> equiv_CharClass (Patterns.NoninvertedCC crs) cd
  | Equiv_InvertedCC: forall crs cd, equiv_ClassRanges crs cd -> equiv_CharClass (Patterns.InvertedCC crs) (CdInv cd).


  (* equiv_regex' wreg lreg n means that the two regexes wreg and lreg are equivalent, where the number of left capturing parentheses before wreg/lreg is n. *)
  Inductive equiv_regex': Patterns.Regex -> regex -> nat -> namedmap -> Prop :=
  | Equiv_empty: forall (n: nat) nm, equiv_regex' Patterns.Empty Epsilon n nm
  | Equiv_char: forall (n: nat) (c: Parameters.Character) nm, equiv_regex' (Patterns.Char c) (Character (Chars.CdSingle c)) n nm
  | Equiv_dot: forall (n: nat) nm, equiv_regex' Patterns.Dot (Character Chars.CdDot) n nm
  | Equiv_backref: forall (n: nat) (gid: positive_integer) nm,
      equiv_regex' (Patterns.AtomEsc (Patterns.DecimalEsc gid)) (Backreference (positive_to_nat gid)) n nm
  | Equiv_named_backref: forall n nm name gid,
      nameidx nm name = Some gid ->
      equiv_regex' (Patterns.AtomEsc (Patterns.GroupEsc name)) (Backreference gid) n nm
  | Equiv_atom_CharacterClassEscape:
    forall (esc: Patterns.CharacterClassEscape) (cd: char_descr) (n: nat) nm,
      equiv_CharacterClassEscape esc cd ->
      equiv_regex' (Patterns.AtomEsc (Patterns.ACharacterClassEsc esc)) (Character cd) n nm
  | Equiv_atom_CharacterEscape:
    forall (esc: Patterns.CharacterEscape) (cd: char_descr) (n: nat) nm,
      equiv_CharacterEscape esc cd ->
      equiv_regex' (Patterns.AtomEsc (Patterns.ACharacterEsc esc)) (Character cd) n nm
  | Equiv_CharacterClass:
    forall (cc: Patterns.CharClass) (cd: char_descr) (n: nat) nm,
      equiv_CharClass cc cd ->
      equiv_regex' (Patterns.CharacterClass cc) (Character cd) n nm
  | Equiv_disj: forall n wr1 wr2 lr1 lr2 nm,
      equiv_regex' wr1 lr1 n nm -> equiv_regex' wr2 lr2 (num_groups lr1 + n) nm ->
      equiv_regex' (Patterns.Disjunction wr1 wr2) (Disjunction lr1 lr2) n nm
  | Equiv_seq: forall n wr1 wr2 lr1 lr2 nm,
      equiv_regex' wr1 lr1 n nm -> equiv_regex' wr2 lr2 (num_groups lr1 + n) nm ->
      equiv_regex' (Patterns.Seq wr1 wr2) (Sequence lr1 lr2) n nm
  | Equiv_quant:
    forall n wr lr wquant lquant wgreedylazy greedy nm,
      equiv_regex' wr lr n nm ->
      equiv_quantifier wquant lquant -> equiv_greedylazy wgreedylazy greedy ->
      equiv_regex' (Patterns.Quantified wr (wgreedylazy wquant)) (lquant greedy lr) n nm
  | Equiv_group: forall n wr lr nm,
      equiv_regex' wr lr (S n) nm ->
      equiv_regex' (Patterns.Group None wr) (Group (S n) lr) n nm
  | Equiv_named_group: forall name n wr lr nm,
      nameidx nm name = Some (S n) ->
      equiv_regex' wr lr (S n) nm ->
      equiv_regex' (Patterns.Group (Some name) wr) (Group (S n) lr) n nm
  | Equiv_lk: forall n wr lr wlk llk nm, equiv_regex' wr lr n nm -> equiv_lookaround wlk llk -> equiv_regex' (wlk wr) (Lookaround llk lr) n nm
  | Equiv_anchor: forall n wr lanchor nm, equiv_anchor wr lanchor -> equiv_regex' wr (Anchor lanchor) n nm
  .


  (* Equivalence of root regexes. *)
  Definition equiv_regex (wreg: Patterns.Regex) (lreg: regex) := equiv_regex' wreg lreg 0 (buildnm wreg).


  Section Lemmas.

    (* Two equivalent regexes have the same number of capturing groups. *)
    Lemma num_groups_equiv:
      forall wreg lreg n nm,
        equiv_regex' wreg lreg n nm ->
        num_groups lreg = countLeftCapturingParensWithin_impl wreg.
    Proof.
      intros wreg lreg n nm Hequiv.
      induction Hequiv as [
        n |
        n c |
        n |
        n |
        n |
        esc cd n Hequivesc |
        esc cd n Hequivesc |
        cc cd n Hequivcc |
        n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
        n wr1 wr2 lr1 lr2 Hequiv1 IH1 Hequiv2 IH2 |
        n wr lr wquant lquant wgreedylazy greedy Hequiv IH Hequivquant Hequivgreedy |
        name n wr lr Hequiv IH |
        name n wr lr Hequiv IH |
        n nm wr lr wlk llk Hequiv IH Hequivlk |
        n nm wr lanchor Hanchequiv]; simpl; try lia; try reflexivity.
      - inversion Hequivquant; inversion Hequivgreedy; auto.
      - inversion Hequivlk; auto.
      - inversion Hanchequiv; auto.
    Qed.
  End Lemmas.

  Section Buildnm_GSMatch.

    (** * Linking name maps and StaticSemantics.groupSpecifiersThatMatch *)
    (* Function mapping a RegexNode to a possible item in a name map *)
    Definition regexnode_nmitem (r0: Node.RegexNode) :=
      let (y, ctx0) := r0 in
      match y with
      | Patterns.Group (Some gs) inner =>
        [(gs, StaticSemantics.countLeftCapturingParensBefore y ctx0 + 1)]
      | _ => []
      end.

    Lemma buildnm'_spec:
      forall nm wr ctx n,
        n = StaticSemantics.countLeftCapturingParensBefore wr ctx ->
        buildnm' wr nm n =
          (List.rev (
            List.flat_map regexnode_nmitem (NodeProps.Zipper.Walk.walk wr ctx)
          ) ++ nm,
          n + StaticSemantics.countLeftCapturingParensWithin wr ctx).
    Proof.
      intros nm wr. revert nm.
      induction wr; simpl; try solve[intros; rewrite Nat.add_0_r; reflexivity].
      - intros nm ctx n Heqn. rewrite IHwr1 with (ctx := Node.Disjunction_left wr2 :: ctx).
        2: { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia. }
        rewrite IHwr2 with (ctx := Node.Disjunction_right wr1 :: ctx).
        2: { simpl. unfold countLeftCapturingParensWithin, countLeftCapturingParensBefore in *. lia. }
        f_equal. 2: unfold countLeftCapturingParensWithin; lia.
        rewrite flat_map_app, rev_app_distr, app_assoc. reflexivity.
      - intros nm ctx n Heqn. apply IHwr with (ctx := Node.Quantified_inner q :: ctx).
        simpl. unfold countLeftCapturingParensBefore in *. lia.
      - intros nm ctx n Heqn. rewrite IHwr1 with (ctx := Node.Seq_left wr2 :: ctx).
        2: { simpl. unfold StaticSemantics.countLeftCapturingParensBefore in *. lia. }
        rewrite IHwr2 with (ctx := Node.Seq_right wr1 :: ctx).
        2: { simpl. unfold countLeftCapturingParensWithin, countLeftCapturingParensBefore in *. lia. }
        f_equal. 2: unfold countLeftCapturingParensWithin; lia.
        rewrite flat_map_app, rev_app_distr, app_assoc. reflexivity.
      - (* Group: interesting case *)
        intros nm ctx n Heqn. destruct name as [name|].
        + rewrite IHwr with (ctx := Node.Group_inner (Some name) :: ctx).
          2: { simpl. unfold countLeftCapturingParensBefore in *. lia. }
          f_equal.
          2: { unfold countLeftCapturingParensWithin. lia. }
          rewrite rev_app_distr. simpl. rewrite <- app_assoc. simpl. f_equal.
          f_equal. f_equal. setoid_rewrite <- Heqn. lia.
        + rewrite IHwr with (ctx := Node.Group_inner None :: ctx).
          2: { simpl. unfold countLeftCapturingParensBefore in *. lia. }
          f_equal. unfold countLeftCapturingParensWithin in *. lia.
      - intros nm ctx n Heqn. apply IHwr with (ctx := Node.Lookahead_inner :: ctx).
        simpl. unfold countLeftCapturingParensBefore in *. lia.
      - intros nm ctx n Heqn. apply IHwr with (ctx := Node.NegativeLookahead_inner :: ctx).
        simpl. unfold countLeftCapturingParensBefore in *. lia.
      - intros nm ctx n Heqn. apply IHwr with (ctx := Node.Lookbehind_inner :: ctx).
        simpl. unfold countLeftCapturingParensBefore in *. lia.
      - intros nm ctx n Heqn. apply IHwr with (ctx := Node.NegativeLookbehind_inner :: ctx).
        simpl. unfold countLeftCapturingParensBefore in *. lia.
    Qed.

    Lemma buildnm_spec:
      forall wr,
        buildnm wr = List.rev (List.flat_map regexnode_nmitem (NodeProps.Zipper.Walk.walk wr nil)).
    Proof.
      intro wr. unfold buildnm.
      rewrite buildnm'_spec with (ctx := []) by reflexivity.
      rewrite app_nil_r. reflexivity.
    Qed.

    Lemma buildnm_gsmatch:
      forall l nm r ctx name,
        l = StaticSemantics.groupSpecifiersThatMatch r ctx name ->
        nm = buildnm (Node.zip r ctx) ->
        forall gid,
          In (name, gid) nm <->
          In gid (List.map (fun '(fst, snd) => StaticSemantics.countLeftCapturingParensBefore fst snd) l).
    Proof.
      intros l nm r ctx name -> -> gid.
      rewrite buildnm_spec.
      rewrite <- In_rev.
      rewrite in_flat_map.
      unfold groupSpecifiersThatMatch.
      rewrite in_map_iff. setoid_rewrite in_flat_map.
      split.
      - intros [[regsub ctxsub] [CHILD NMITEM]]. unfold regexnode_nmitem in NMITEM.
        destruct regsub; try solve[inversion NMITEM].
        destruct name0; try solve[inversion NMITEM].
        destruct NMITEM as [NMITEM | NMITEM]; try solve[inversion NMITEM].
        injection NMITEM as -> Heqgid.
        exists (regsub, Node.Group_inner (Some name) :: ctxsub).
        split. 1: { simpl. unfold countLeftCapturingParensBefore in *. lia. }
        eexists. split. 1: apply CHILD.
        simpl.
        destruct (string_eq_dec _ _). 2: contradiction.
        left. reflexivity.
      - intros [[reg_inner ctx_inner] [Heqgid [[regsub ctxsub] [CHILD GS]]]].
        destruct regsub; try solve[inversion GS].
        destruct name0; try solve[inversion GS].
        destruct (g ==# capturingGroupName name)%wt; try solve[inversion GS].
        unfold capturingGroupName in e. subst g.
        eexists. split. 1: apply CHILD.
        destruct GS as [GS|GS]; try solve[inversion GS].
        injection GS as <- <-. simpl.
        left. f_equal. simpl in Heqgid. unfold countLeftCapturingParensBefore in *. lia.
    Qed.

    Lemma unique_In_eq {A F} `{Ferr: Result.AssertionError F}:
      forall l: list A, length l = 1 ->
        forall x, List.List.Unique.unique l = Success x <-> In x l.
    Proof.
      intros l Hlen x. split; intro H.
      - rewrite List.List.Unique.success with (v := x) by auto. left. reflexivity.
      - destruct l as [|y l]; try discriminate. destruct l; try discriminate.
        simpl. destruct H. 2: inversion H.
        f_equal. auto.
    Qed.

    Lemma findA_filter {A B}:
      forall (f: A -> bool) (l: list (A * B)),
        SetoidList.findA f l =
        match List.filter (fun '(a, b) => f a) l with
        | [] => None
        | (a, b)::_ => Some b
        end.
    Proof.
      induction l; simpl; auto.
      destruct a as [a b].
      destruct (f0 a); auto.
    Qed.

    Lemma in_len1_eq {A}:
      forall (x y: A) (l: list A),
        length l = 1 -> In x l -> In y l -> x = y.
    Proof.
      intros x y [|a []]; try discriminate.
      intros _ Hxin Hyin.
      destruct Hxin as [ <- | [] ].
      destruct Hyin as [ <- | [] ].
      reflexivity.
    Qed.

    Lemma buildnm_gsmatch_unique {F} `{Ferr: Result.AssertionError F}:
      forall l nm r ctx name gs,
        l = StaticSemantics.groupSpecifiersThatMatch r ctx name ->
        length l = 1 ->
        nm = buildnm (Node.zip r ctx) ->
        List.List.Unique.unique l = Success gs ->
        nameidx nm name = Some (StaticSemantics.countLeftCapturingParensBefore (fst gs) (snd gs)).
    Proof.
      intros l nm r ctx name gs -> Hlen -> Heqgs.
      unfold nameidx.
      rewrite findA_filter.
      rewrite unique_In_eq in Heqgs by auto.
      apply in_map with (f := fun '(fst, snd) => countLeftCapturingParensBefore fst snd) in Heqgs.
      destruct gs as [reg_inner ctx_inner]; simpl in *.
      rewrite <- buildnm_gsmatch in Heqgs. 2: reflexivity. 2: reflexivity.
      destruct filter eqn:Hfilter.
      1: {
        exfalso. assert (In (name, countLeftCapturingParensBefore reg_inner ctx_inner) []). {
          setoid_rewrite <- Hfilter. apply filter_In. split; auto. unfold patname_eqb.
          destruct patname_eq_dec; auto.
        }
        inversion H.
      }
      assert (In p (filter (fun '(a, _) => patname_eqb a name) (buildnm (Node.zip r ctx)))). {
        rewrite Hfilter. left. reflexivity.
      }
      rewrite filter_In in H. destruct p as [name0 gid].
      destruct H as [Hin H].
      unfold patname_eqb in H.
      destruct patname_eq_dec; try discriminate. subst name0.
      rewrite buildnm_gsmatch in Hin. 3: reflexivity. 2: reflexivity.
      rewrite buildnm_gsmatch in Heqgs. 3: reflexivity. 2: reflexivity.
      f_equal.
      remember ((map (fun '(fst, snd) => countLeftCapturingParensBefore fst snd)
            (groupSpecifiersThatMatch _ ctx name))) as l0 in *.
      apply in_len1_eq with (l := l0); auto.
      rewrite Heql0, length_map. auto.
    Qed.
  End Buildnm_GSMatch.

  (* Translation function from Warblre to Linden. *)
  Section WarblreToLinden.

    Inductive wl_transl_error: Type :=
      | WlMalformed.

    Definition characterClassEsc_to_linden (esc: Patterns.CharacterClassEscape): char_descr :=
      match esc with
      | Patterns.esc_d => CdDigits
      | Patterns.esc_D => CdNonDigits
      | Patterns.esc_s => CdWhitespace
      | Patterns.esc_S => CdNonWhitespace
      | Patterns.esc_w => CdWordChar
      | Patterns.esc_W => CdNonWordChar
      | Patterns.UnicodeProp p => CdUnicodeProp p
      | Patterns.UnicodePropNeg p => CdNonUnicodeProp p
      end.

    Definition controlEsc_singleCharacter_numValue (esc: Patterns.ControlEscape): nat :=
      match esc with
      | Patterns.esc_f => Character.numeric_value Characters.FORM_FEED
      | Patterns.esc_n => Character.numeric_value Characters.LINE_FEED
      | Patterns.esc_r => Character.numeric_value Characters.CARRIAGE_RETURN
      | Patterns.esc_t => Character.numeric_value Characters.CHARACTER_TABULATION
      | Patterns.esc_v => Character.numeric_value Characters.LINE_TABULATION
      end.

    Definition asciiEsc_singleCharacter_numValue (l: AsciiLetter): nat :=
      NonNegInt.modulo (AsciiLetter.numeric_value l) 32.

    Definition characterEscape_singleCharacter_numValue (esc: Patterns.CharacterEscape): nat :=
      match esc with
      | Patterns.ControlEsc esc => controlEsc_singleCharacter_numValue esc
      | Patterns.AsciiControlEsc l => asciiEsc_singleCharacter_numValue l
      | Patterns.esc_Zero => Character.numeric_value Characters.NULL
      | Patterns.HexEscape d1 d2 => HexDigit.to_integer_2 d1 d2
      | Patterns.UnicodeEsc (Patterns.Pair head tail) => unicodeCodePoint head tail
      | Patterns.UnicodeEsc (Patterns.Lonely hex) => StaticSemantics.characterValue_Hex4Digits hex
      | Patterns.UnicodeEsc (Patterns.CodePoint c) => Character.numeric_value c
      | Patterns.IdentityEsc c => Character.numeric_value c
      end.

    Definition characterEscape_to_linden (esc: Patterns.CharacterEscape): char_descr :=
      let c := characterEscape_singleCharacter_numValue esc in
      CdSingle (Character.from_numeric_value c).

    Definition atomesc_to_linden (ae: Patterns.AtomEscape) (nm:namedmap): Result regex wl_transl_error :=
      match ae with
      | Patterns.DecimalEsc gid => Success (Backreference (positive_to_nat gid))
      | Patterns.ACharacterClassEsc esc =>
          let cd := characterClassEsc_to_linden esc in
          Success (Character cd)
      | Patterns.ACharacterEsc esc =>
          let cd := characterEscape_to_linden esc in
          Success (Character cd)
      | Patterns.GroupEsc gn =>
          match nameidx nm gn with
          | None => Error WlMalformed
          | Some gid => Success (Backreference gid)
          end
      end.

    Definition classEscape_to_linden (esc: Patterns.ClassEscape): char_descr :=
      match esc with
      | Patterns.esc_b => CdSingle Characters.BACKSPACE
      | Patterns.esc_Dash => CdSingle Characters.HYPHEN_MINUS
      | Patterns.CCharacterClassEsc esc => characterClassEsc_to_linden esc
      | Patterns.CCharacterEsc esc => characterEscape_to_linden esc
      end.

    Definition classEscape_singleCharacter_numValue (esc: Patterns.ClassEscape): Result nat wl_transl_error :=
      match esc with
      | Patterns.esc_b => Success (Character.numeric_value Characters.BACKSPACE)
      | Patterns.esc_Dash => Success (Character.numeric_value Characters.HYPHEN_MINUS)
      | Patterns.CCharacterClassEsc esc => Error WlMalformed
      | Patterns.CCharacterEsc esc => Success (characterEscape_singleCharacter_numValue esc)
      end.

    Definition classAtom_to_linden (ca: Patterns.ClassAtom): char_descr :=
      match ca with
      | Patterns.SourceCharacter c => CdSingle c
      | Patterns.ClassEsc esc => classEscape_to_linden esc
      end.

    Definition classAtom_singleCharacter_numValue (ca: Patterns.ClassAtom): Result nat wl_transl_error :=
      match ca with
      | Patterns.SourceCharacter c => Success (Character.numeric_value c)
      | Patterns.ClassEsc esc => classEscape_singleCharacter_numValue esc
      end.

    Fixpoint classRanges_to_linden (cr: Patterns.ClassRanges): Result char_descr wl_transl_error :=
      match cr with
      | Patterns.EmptyCR => Success CdEmpty
      | Patterns.ClassAtomCR ca t =>
          let cda := classAtom_to_linden ca in
          let! cdt =<< classRanges_to_linden t in
          Success (CdUnion cda cdt)
      | Patterns.RangeCR l h t =>
          let! cl =<< classAtom_singleCharacter_numValue l in
          let! ch =<< classAtom_singleCharacter_numValue h in
          let! cdt =<< classRanges_to_linden t in
          if cl <=? ch then
            Success (CdUnion (CdRange (Character.from_numeric_value cl) (Character.from_numeric_value ch)) cdt)
          else
            Error WlMalformed
      end.

    Definition charclass_to_linden (cc: Patterns.CharClass): Result char_descr wl_transl_error :=
      match cc with
      | Patterns.NoninvertedCC crs => classRanges_to_linden crs
      | Patterns.InvertedCC crs =>
          let! cd =<< classRanges_to_linden crs in
          Success (CdInv cd)
      end.

    Definition wquantpref_to_linden (qp: Patterns.QuantifierPrefix): Result (bool -> regex -> regex) wl_transl_error :=
      match qp with
      | Patterns.Star => Success (fun greedy => Quantified greedy 0 +∞)
      | Patterns.Plus => Success (fun greedy => Quantified greedy 1 +∞)
      | Patterns.Question => Success (fun greedy => Quantified greedy 0 (NoI.N 1))
      | Patterns.RepExact n => Success (fun greedy => Quantified greedy n (NoI.N 0))
      | Patterns.RepPartialRange n => Success (fun greedy => Quantified greedy n +∞)
      | Patterns.RepRange mini maxi =>
          if mini <=? maxi then
            Success (fun greedy => Quantified greedy mini (NoI.N (maxi-mini)))
          else
            Error WlMalformed
      end.

    (* checking that we get the expected index *)
    Definition assert_idx_eq (i1 i2:nat) : Result unit wl_transl_error :=
      if (Nat.eqb i1 i2) then Success tt else Error WlMalformed.

    Fixpoint warblre_to_linden (wr: Patterns.Regex) (n: nat) (nm:namedmap): Result regex wl_transl_error :=
      match wr with
      | Patterns.Empty => Success Epsilon
      | Patterns.Char chr => Success (Character (CdSingle chr))
      | Patterns.Dot => Success (Character CdDot)
      | Patterns.AtomEsc ae => atomesc_to_linden ae nm
      | Patterns.CharacterClass cc =>
          let! cd =<< charclass_to_linden cc in
          Success (Character cd)
      | Patterns.Disjunction wr1 wr2 =>
          let! lr1 =<< warblre_to_linden wr1 n nm in
          let! lr2 =<< warblre_to_linden wr2 (num_groups lr1 + n) nm in
          Success (Disjunction lr1 lr2)
      | Patterns.Quantified wr (Patterns.Greedy qp) =>
          let! quant =<< wquantpref_to_linden qp in
          let! lr =<< warblre_to_linden wr n nm in
          Success (quant true lr)
      | Patterns.Quantified wr (Patterns.Lazy qp) =>
          let! quant =<< wquantpref_to_linden qp in
          let! lr =<< warblre_to_linden wr n nm in
          Success (quant false lr)
      | Patterns.Seq wr1 wr2 =>
          let! lr1 =<< warblre_to_linden wr1 n nm in
          let! lr2 =<< warblre_to_linden wr2 (num_groups lr1 + n) nm in
          Success (Sequence lr1 lr2)
      | Patterns.Group None wr =>
          let! lr =<< warblre_to_linden wr (S n) nm in
          Success (Group (S n) lr)
      | Patterns.Group (Some name) wr =>
          match (nameidx nm name) with
          | Some idx =>
              let! _ =<< assert_idx_eq idx (S n) in
              let! lr =<< warblre_to_linden wr (S n) nm in
              Success (Group (S n) lr)
          | _ => Error WlMalformed
          end
      | Patterns.InputStart => Success (Anchor BeginInput)
      | Patterns.InputEnd => Success (Anchor EndInput)
      | Patterns.WordBoundary => Success (Anchor WordBoundary)
      | Patterns.NotWordBoundary => Success (Anchor NonWordBoundary)
      | Patterns.Lookahead wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround LookAhead lr)
      | Patterns.NegativeLookahead wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround NegLookAhead lr)
      | Patterns.Lookbehind wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround LookBehind lr)
      | Patterns.NegativeLookbehind wr =>
          let! lr =<< warblre_to_linden wr n nm in
          Success (Lookaround NegLookBehind lr)
      end.

    (* A version of warblre_to_linden that returns a dummy value in case of failure. *)
    Definition warblre_to_linden' (wr: Patterns.Regex) (n: nat) (nm: namedmap): regex :=
      match warblre_to_linden wr n nm with
      | Success r => r
      | Error _ => Epsilon
      end.

  End WarblreToLinden.

  Section TranslationSoundness.

    Lemma characterClassEsc_to_linden_sound:
      forall esc cd,
        characterClassEsc_to_linden esc = cd ->
        equiv_CharacterClassEscape esc cd.
    Proof.
      intro esc. destruct esc; simpl; try discriminate.
      all: intros cd <-; constructor.
    Qed.

    Lemma controlEsc_singleCharacter_numValue_sound:
      forall esc, equiv_ControlEscape esc (CdSingle (Character.from_numeric_value (controlEsc_singleCharacter_numValue esc))).
    Proof.
      intro esc. destruct esc; simpl; rewrite Character.numeric_pseudo_bij; constructor.
    Qed.

    Lemma asciiEsc_singleCharacter_numValue_sound:
      forall l, equiv_asciiesc l (CdSingle (Character.from_numeric_value (asciiEsc_singleCharacter_numValue l))).
    Proof.
      intro l. unfold asciiEsc_singleCharacter_numValue. constructor. reflexivity.
    Qed.

    Lemma characterEscape_to_linden_sound:
      forall esc cd,
        characterEscape_to_linden esc = cd ->
        equiv_CharacterEscape esc cd.
    Proof.
      intro esc. destruct esc; try discriminate; simpl; unfold characterEscape_to_linden; simpl.
      5: destruct seq; simpl.
      all: intros cd <-; try rewrite Character.numeric_pseudo_bij; try constructor.
      - apply controlEsc_singleCharacter_numValue_sound.
      - apply asciiEsc_singleCharacter_numValue_sound.
    Qed.

    Lemma atomesc_to_linden_sound:
      forall ae lr n nm,
        atomesc_to_linden ae nm = Success lr ->
        equiv_regex' (Patterns.AtomEsc ae) lr n nm.
    Proof.
      intro ae. destruct ae.
      - simpl. intros lr gid nm H. injection H as <-. constructor.
      - simpl. intros lr n nm.
        intro H. injection H as <-. constructor. apply characterClassEsc_to_linden_sound. auto.
      - simpl. intros lr n nm H. injection H as <-. constructor. apply characterEscape_to_linden_sound. auto.
      - simpl. intros lr n nm H. destruct (nameidx nm id) eqn:NAME; [|discriminate].
        inversion H. subst. constructor. auto.
    Qed.

    Lemma wquantpref_to_linden_sound:
      forall qp quant,
        wquantpref_to_linden qp = Success quant ->
        equiv_quantifier qp quant.
    Proof.
      intros qp quant H. destruct qp.
      1-5: injection H as <-; constructor.
      simpl in H. destruct Nat.leb eqn:Hle; try discriminate.
      injection H as <-. constructor. apply PeanoNat.Nat.leb_le. auto.
    Qed.

    Lemma classEscape_to_linden_sound:
      forall esc cda,
        classEscape_to_linden esc = cda ->
        equiv_ClassEscape esc cda.
    Proof.
      intros esc cda. destruct esc; simpl.
      - intros <-. constructor.
      - intros <-. constructor.
      - intros <-. constructor. apply characterClassEsc_to_linden_sound. auto.
      - intros <-. constructor. apply characterEscape_to_linden_sound. auto.
    Qed.

    Lemma classAtom_to_linden_sound:
      forall ca cda,
        classAtom_to_linden ca = cda ->
        equiv_ClassAtom ca cda.
    Proof.
      intro ca. destruct ca.
      - simpl. intros cda <-. constructor.
      - simpl. intros cda <-. constructor. apply classEscape_to_linden_sound. auto.
    Qed.

    Lemma characterEscape_singleCharacter_numValue_sound:
      forall esc clh,
        characterEscape_singleCharacter_numValue esc = clh ->
        equiv_CharacterEscape esc (CdSingle (Character.from_numeric_value clh)).
    Proof.
      intros esc clh. destruct esc; simpl.
      5: destruct seq; simpl.
      all: intros <-; try rewrite Character.numeric_pseudo_bij; constructor.
      - apply controlEsc_singleCharacter_numValue_sound.
      - apply asciiEsc_singleCharacter_numValue_sound.
    Qed.

    Lemma classEscape_singleCharacter_numValue_sound:
      forall esc clh,
        classEscape_singleCharacter_numValue esc = Success clh ->
        equiv_ClassEscape esc (CdSingle (Character.from_numeric_value clh)).
    Proof.
      intros esc clh. destruct esc; simpl; intro H.
      - injection H as <-. rewrite Character.numeric_pseudo_bij. constructor.
      - injection H as <-. rewrite Character.numeric_pseudo_bij. constructor.
      - discriminate.
      - injection H as <-. constructor. apply characterEscape_singleCharacter_numValue_sound. auto.
    Qed.

    Lemma classAtom_singleCharacter_numValue_sound:
      forall lh clh,
        classAtom_singleCharacter_numValue lh = Success clh ->
        equiv_ClassAtom lh (CdSingle (Character.from_numeric_value clh)).
    Proof.
      intros lh clh. destruct lh.
      - simpl. intro H. injection H as <-. rewrite Character.numeric_pseudo_bij. constructor.
      - simpl. intro H. constructor. apply classEscape_singleCharacter_numValue_sound. auto.
    Qed.

    Lemma classRanges_to_linden_sound:
      forall crs cd,
        classRanges_to_linden crs = Success cd ->
        equiv_ClassRanges crs cd.
    Proof.
      intro crs. induction crs.
      - simpl. intros cd H. injection H as <-. constructor.
      - simpl. intro cd.
        destruct classRanges_to_linden as [cdt|] eqn:Hcdt; try discriminate; simpl.
        intro H. injection H as <-.
        constructor; auto. apply classAtom_to_linden_sound. auto.
      - simpl. intro cd.
        destruct classAtom_singleCharacter_numValue as [cl|] eqn:Hcl; try discriminate; simpl.
        destruct (classAtom_singleCharacter_numValue h) as [ch|] eqn:Hch; try discriminate; simpl.
        destruct classRanges_to_linden as [cdt|] eqn:Hcdt; try discriminate; simpl.
        destruct Nat.leb eqn:Hle; try discriminate; simpl.
        apply PeanoNat.Nat.leb_le in Hle.
        intro H. injection H as <-. constructor; auto.
        1,2: apply classAtom_singleCharacter_numValue_sound; auto.
        apply Character.numeric_round_trip_order; auto.
    Qed.

    Lemma charclass_to_linden_sound:
      forall cc cd,
        charclass_to_linden cc = Success cd ->
        equiv_CharClass cc cd.
    Proof.
      intro cc. destruct cc.
      - simpl. intros cd H. constructor. apply classRanges_to_linden_sound. auto.
      - simpl. destruct classRanges_to_linden as [cdsub|] eqn:Hcdsub; simpl; try discriminate.
        intros cd H. injection H as <-. constructor. apply classRanges_to_linden_sound. auto.
    Qed.

    Theorem warblre_to_linden_sound:
      forall wr lr n nm,
        warblre_to_linden wr n nm = Success lr ->
        equiv_regex' wr lr n nm.
    Proof.
      intro wr. induction wr.
      - simpl. intros lr n nm H. injection H as <-. apply Equiv_empty.
      - simpl. intros lr n nm H. injection H as <-. apply Equiv_char.
      - simpl. intros lr n nm H. injection H as <-. apply Equiv_dot.
      - simpl. intros lr n nm H. apply atomesc_to_linden_sound. auto.
      - simpl. intros lr n nm.
        destruct charclass_to_linden as [cd|] eqn:Hcd; simpl; try discriminate.
        intro H. injection H as <-. constructor. apply charclass_to_linden_sound. auto.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lr1|] eqn:Hwl1; try discriminate. simpl.
        destruct (warblre_to_linden wr2 _) as [lr2|] eqn:Hwl2; try discriminate. simpl.
        intro H. injection H as <-.
        apply Equiv_disj; auto.
      - simpl. intros lr n nm.
        destruct q as [qp|qp].
        + destruct wquantpref_to_linden as [quant|] eqn:Hquant; try discriminate. simpl.
          destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
          intro H. injection H as <-.
          apply Equiv_quant; auto. 2: constructor.
          apply wquantpref_to_linden_sound. auto.
        + destruct wquantpref_to_linden as [quant|] eqn:Hquant; try discriminate. simpl.
          destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
          intro H. injection H as <-.
          apply Equiv_quant; auto. 2: constructor.
          apply wquantpref_to_linden_sound. auto.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lr1|] eqn:Hwl1; try discriminate. simpl.
        destruct (warblre_to_linden wr2 _) as [lr2|] eqn:Hwl2; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto.
      - simpl. intros lr n nm.
        destruct name as [name|]; simpl.
        2: { destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate.
             simpl. inversion 1. constructor. auto. }
        destruct (nameidx nm name) eqn:NAME; [|inversion 1].
        unfold assert_idx_eq. simpl. destruct (Nat.eqb n0 (S n)) eqn:IDX; [|inversion 1].
        apply PeanoNat.Nat.eqb_eq in IDX.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; [|inversion 1].
        simpl. inversion 1. subst. constructor; auto.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm H. injection H as <-. constructor. constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
      - simpl. intros lr n nm.
        destruct warblre_to_linden as [lrsub|] eqn:Hwl; try discriminate. simpl.
        intro H. injection H as <-. constructor; auto; constructor.
    Qed.

    Theorem warblre_to_linden_sound_root:
      forall wr lr,
        warblre_to_linden wr 0 (buildnm wr) = Success lr ->
        equiv_regex wr lr.
    Proof.
      intros wr lr. apply warblre_to_linden_sound with (wr := wr) (lr := lr) (n := 0).
    Qed.

  End TranslationSoundness.

  Section TranslationCompleteness.

    Lemma EarlyErrors_Down:
      forall wrout ctxout wrin ctxin,
        NodeProps.Zipper.Down (wrin, ctxin) (wrout, ctxout) ->
        EarlyErrors.Pass_Regex wrout ctxout ->
        EarlyErrors.Pass_Regex wrin ctxin.
    Proof.
      intros wrout ctxout wrin ctxin DOWN EE.
      inversion DOWN; subst; inversion EE; subst; auto.
    Qed.

    Lemma EarlyErrors_Downstar:
      forall x y,
        NodeProps.Zipper.Down_Star x y ->
        EarlyErrors.Pass_Regex (fst y) (snd y) ->
        EarlyErrors.Pass_Regex (fst x) (snd x).
    Proof.
      intros x y DOWN_STAR EE.
      induction DOWN_STAR.
      - destruct x as [wrin ctxin]. destruct y as [wrout ctxout]. eauto using EarlyErrors_Down.
      - auto.
      - auto.
    Qed.

    Lemma EarlyErrors_sub:
      forall wroot,
        EarlyErrors.Pass_Regex wroot nil ->
        forall wr ctx,
          Node.Root wroot (wr, ctx) ->
          EarlyErrors.Pass_Regex wr ctx.
    Proof.
      intros wroot EE wr ctx ROOT.
      apply NodeProps.Zipper.Down.root_is_top in ROOT.
      apply EarlyErrors_Downstar with (x := (wr, ctx)) (y := (wroot, [])); auto.
    Qed.

    Lemma Walk_Root:
      forall wroot r ctx,
        Node.Root wroot (r, ctx) ->
        In (r, ctx) (NodeProps.Zipper.Walk.walk (Node.zip wroot []) []).
    Proof.
      intros wroot r ctx ROOT. unfold Node.zip.
      apply NodeProps.Zipper.Down.root_is_top, NodeProps.Zipper.Walk.completeness in ROOT.
      unfold List.List.Exists.ExistValue in ROOT. destruct ROOT as [i INDEXING].
      unfold List.List.Indexing.Nat.indexing in INDEXING.
      destruct nth_error eqn:NTH_ERROR; try discriminate.
      injection INDEXING as ->. eauto using nth_error_In.
    Qed.

    Lemma earlyErrors_singletonCharacterEscape:
      forall ce cl,
        EarlyErrors.SingletonCharacterEscape ce cl ->
        characterEscape_singleCharacter_numValue ce = cl.
    Proof.
      intros ce cl EE. inversion EE; subst; simpl; auto.
    Qed.

    Lemma earlyErrors_translation_singletonClassAtom:
      forall l cl,
        EarlyErrors.SingletonClassAtom l cl ->
        classAtom_singleCharacter_numValue l = Success cl.
    Proof.
      intros l cl EE. inversion EE; subst; simpl; auto.
      auto using earlyErrors_singletonCharacterEscape.
    Qed.

    Lemma earlyErrors_pass_translation_crs:
      forall crs,
        EarlyErrors.Pass_ClassRanges crs ->
        exists cd, classRanges_to_linden crs = Success cd.
    Proof.
      intros crs EE. induction EE; simpl.
      - eexists. reflexivity.
      - destruct IHEE as [cdt IHEE]. rewrite IHEE. eexists. reflexivity.
      - destruct IHEE as [cdt IHEE]. rewrite IHEE.
        rewrite earlyErrors_translation_singletonClassAtom with (cl := cl); auto.
        rewrite earlyErrors_translation_singletonClassAtom with (cl := ch); auto.
        simpl. apply Nat.leb_le in H1. rewrite H1. eexists. reflexivity.
    Qed.

    Theorem earlyErrors_pass_translation':
      forall wroot: Patterns.Regex,
        (*EarlyErrors.Pass_Regex wroot nil ->*) (* This does not include the condition on the absence of duplicate groups when there are no backreferences *)
        earlyErrors wroot nil = Success false -> (* This does, and Warblre already proves that earlyErrors can never fail (section Safety in Warblre.props.EarlyErrors) *)
        forall wr ctx,
          Node.Root wroot (wr, ctx) ->
          exists lr, warblre_to_linden wr (StaticSemantics.countLeftCapturingParensBefore wr ctx) (buildnm wroot) = Success lr.
    Proof.
      intros wroot EE0. pose proof EarlyErrors.earlyErrors wroot EE0 as H.
      induction wr; simpl.
      - intros ctx _. eexists. reflexivity.
      - intros ctx _. eexists. reflexivity.
      - intros ctx _. eexists. reflexivity.
      - intros ctx Hroot.
        pose proof EarlyErrors_sub wroot H _ ctx Hroot as EE.
        inversion EE; subst. inversion H1; subst.
        + simpl. eexists. reflexivity.
        + simpl. eexists. reflexivity.
        + simpl. eexists. reflexivity.
        + simpl.
          destruct groupSpecifiersThatMatch as [|gs []] eqn:Heqgs; try discriminate.
          rewrite <- Heqgs in H0. erewrite buildnm_gsmatch_unique.
          3: apply H0.
          2: reflexivity.
          2: rewrite Hroot; reflexivity.
          2: rewrite Heqgs; reflexivity.
          eexists. reflexivity.
      - intros ctx Hroot.
        pose proof EarlyErrors_sub wroot H _ ctx Hroot as EE.
        inversion EE; subst. inversion H1; subst.
        + simpl. apply earlyErrors_pass_translation_crs in H0. destruct H0 as [cd CRS_SUCC].
          rewrite CRS_SUCC. eexists. reflexivity.
        + simpl. apply earlyErrors_pass_translation_crs in H0. destruct H0 as [cd CRS_SUCC].
          rewrite CRS_SUCC. eexists. reflexivity.
      - intros ctx Hroot.
        specialize (IHwr1 (Node.Disjunction_left wr2 :: ctx)).
        specialize_prove IHwr1 by eauto using NodeProps.Zipper.Down.same_root_down0, NodeProps.Zipper.Down_Disjunction_left.
        destruct IHwr1 as [lr1 IHwr1].
        specialize (IHwr2 (Node.Disjunction_right wr1 :: ctx)).
        specialize_prove IHwr2 by eauto using NodeProps.Zipper.Down.same_root_down0, NodeProps.Zipper.Down_Disjunction_right.
        destruct IHwr2 as [lr2 IHwr2].
        simpl in *. rewrite Nat.add_0_r in IHwr1. setoid_rewrite IHwr1. simpl.
        rewrite num_groups_equiv with (wreg := wr1) (n := @countLeftCapturingParensBefore (@LWParameters params) wr1 ctx) (nm := buildnm wroot).
        2: { apply warblre_to_linden_sound. auto. }
        rewrite Nat.add_comm. setoid_rewrite IHwr2. simpl. eexists. reflexivity.
      - intros ctx Hroot.
        pose proof EarlyErrors_sub wroot H _ ctx Hroot as EE.
        specialize (IHwr (Node.Quantified_inner q :: ctx)).
        specialize_prove IHwr by eauto using NodeProps.Zipper.Down.same_root_down0, NodeProps.Zipper.Down_Quantified_inner.
        destruct IHwr as [lrsub IHwr].
        inversion EE; subst. inversion H4; subst.
        + inversion H0; subst.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. apply Nat.leb_le in H1. rewrite H1. simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
        + inversion H0; subst.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
          * simpl. apply Nat.leb_le in H1. rewrite H1. simpl. simpl in IHwr. rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. simpl. eexists. reflexivity.
      - (* Sequence: similar to disjunction *)
        intros ctx Hroot.
        specialize (IHwr1 (Node.Seq_left wr2 :: ctx)).
        specialize_prove IHwr1 by eauto using NodeProps.Zipper.Down.same_root_down0.
        destruct IHwr1 as [lr1 IHwr1].
        specialize (IHwr2 (Node.Seq_right wr1 :: ctx)).
        specialize_prove IHwr2 by eauto using NodeProps.Zipper.Down.same_root_down0.
        destruct IHwr2 as [lr2 IHwr2].
        simpl in *. rewrite Nat.add_0_r in IHwr1. setoid_rewrite IHwr1. simpl.
        rewrite num_groups_equiv with (wreg := wr1) (n := @countLeftCapturingParensBefore (@LWParameters params) wr1 ctx) (nm := buildnm wroot).
        2: { apply warblre_to_linden_sound. auto. }
        rewrite Nat.add_comm. setoid_rewrite IHwr2. simpl. eexists. reflexivity.
      - (* Group *)
        intros ctx Hroot.
        specialize (IHwr (Node.Group_inner name :: ctx)).
        specialize_prove IHwr by eauto using NodeProps.Zipper.Down.same_root_down0.
        destruct IHwr as [lrsub IHwr].
        simpl in IHwr. rewrite Nat.add_comm in IHwr.
        pose proof EarlyErrors_sub wroot H _ ctx Hroot as EE.
        destruct name as [name|].
        + unfold earlyErrors in EE0.
          destruct List.List.Exists.exist eqn:Hdup; try discriminate.
          destruct s; try discriminate.
          apply EarlyErrors.groupSpecifiersThatMatch_singleton with (name := name) in Hdup.
          assert (Hpres: In (wr, Node.Group_inner (Some name) :: ctx) (groupSpecifiersThatMatch wroot [] name)). {
            unfold groupSpecifiersThatMatch. apply in_flat_map.
            exists (Patterns.Group (Some name) wr, ctx). split.
            - apply Walk_Root. auto. (* Follows from Hroot *)
            - unfold capturingGroupName. destruct EqDec.eq_dec; try contradiction.
            left. reflexivity.
          }
          remember (groupSpecifiersThatMatch wroot [] name) as l in *.
          destruct l as [|gs []].
          1: inversion Hpres. 2: { simpl in Hdup. lia. }
          rewrite buildnm_gsmatch_unique with (l := [gs]) (r := wroot) (ctx := nil) (gs := gs); auto.
          destruct Hpres as [Hpres | Hpres]; try solve[inversion Hpres].
          subst gs. simpl.
          unfold assert_idx_eq. rewrite Nat.add_comm. rewrite Nat.eqb_refl. simpl.
          setoid_rewrite IHwr. eexists. reflexivity.
        + setoid_rewrite IHwr. eexists. reflexivity.
      - intros ctx _. eexists. reflexivity.
      - intros ctx _. eexists. reflexivity.
      - intros ctx _. eexists. reflexivity.
      - intros ctx _. eexists. reflexivity.
      (* Lookarounds *)
      - intros ctx Hroot.
        specialize (IHwr (Node.Lookahead_inner :: ctx)).
        specialize_prove IHwr by eauto using NodeProps.Zipper.Down.same_root_down0, NodeProps.Zipper.Down_Lookahead_inner.
        destruct IHwr as [lrsub IHwr]. simpl in *.
        rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. eexists. reflexivity.
      - intros ctx Hroot.
        specialize (IHwr (Node.NegativeLookahead_inner :: ctx)).
        specialize_prove IHwr by eauto using NodeProps.Zipper.Down.same_root_down0, NodeProps.Zipper.Down_NegativeLookahead_inner.
        destruct IHwr as [lrsub IHwr]. simpl in *.
        rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. eexists. reflexivity.
      - intros ctx Hroot.
        specialize (IHwr (Node.Lookbehind_inner :: ctx)).
        specialize_prove IHwr by eauto using NodeProps.Zipper.Down.same_root_down0, NodeProps.Zipper.Down_Lookbehind_inner.
        destruct IHwr as [lrsub IHwr]. simpl in *.
        rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. eexists. reflexivity.
      - intros ctx Hroot.
        specialize (IHwr (Node.NegativeLookbehind_inner :: ctx)).
        specialize_prove IHwr by eauto using NodeProps.Zipper.Down.same_root_down0, NodeProps.Zipper.Down_NegativeLookbehind_inner.
        destruct IHwr as [lrsub IHwr]. simpl in *.
        rewrite Nat.add_0_r in IHwr. setoid_rewrite IHwr. eexists. reflexivity.
    Qed.

    Theorem earlyErrors_pass_translation:
      forall wr: Patterns.Regex,
        earlyErrors wr nil = Success false ->
        exists lr, warblre_to_linden wr 0 (buildnm wr) = Success lr.
    Proof.
      intros wr EE. apply earlyErrors_pass_translation' with (wroot := wr) (wr := wr) (ctx := []); auto.
      reflexivity.
    Qed.

    Corollary earlyErrors_pass_translation_exists:
      forall wr: Patterns.Regex,
        earlyErrors wr nil = Success false ->
        exists lr, equiv_regex wr lr.
    Proof.
      intros wr EE. apply earlyErrors_pass_translation in EE.
      destruct EE as [lr TRANSLATION].
      exists lr. apply warblre_to_linden_sound_root. auto.
    Qed.

    Corollary earlyErrors_pass_translation_nomonad:
      forall wr: Patterns.Regex,
        earlyErrors wr nil = Success false ->
        equiv_regex wr (warblre_to_linden' wr 0 (buildnm wr)).
    Proof.
      intros wr EE. apply earlyErrors_pass_translation in EE.
      destruct EE as [lr TRANSLATION].
      unfold warblre_to_linden'. rewrite TRANSLATION.
      apply warblre_to_linden_sound_root. auto.
    Qed.

  End TranslationCompleteness.

End RegexpTranslation.

Section SanityCheck.
  Context {params: LindenParameters}.

  (* Sanity check with regex a(?<a>a)*)
  Context (a: Parameters.Character).

  Definition wr1 := Patterns.Seq (Patterns.Char a) (Patterns.Group (Some [a]) (Patterns.Char a)).
  Definition lr1_res := warblre_to_linden wr1 0 (buildnm wr1).

  Lemma lr1_Success: exists lr, lr1_res = Success lr.
  Proof.
    compute.
    destruct patname_eq_dec. 2: contradiction.
    eexists. reflexivity.
  Qed.


  (* Sanity check with regex (?<a>a)\k<a>*)
  Definition wr2 := Patterns.Seq (Patterns.Group (Some [a]) (Patterns.Char a)) (Patterns.AtomEsc (Patterns.GroupEsc [a])).
  Definition lr2_res := warblre_to_linden wr2 0 (buildnm wr2).

  Lemma lr2_Success: exists lr, lr2_res = Success lr.
  Proof.
    compute.
    destruct patname_eq_dec. 2: contradiction.
    eexists. reflexivity.
  Qed.
End SanityCheck.
