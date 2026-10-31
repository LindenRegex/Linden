From Stdlib Require Import List Lia Bool.
Import ListNotations.

From Linden Require Import Regex Chars Groups.
From Linden Require Import Tree.
From Linden Require Import Semantics PikeSubset.
From Linden Require Import Parameters LWParameters.
From Warblre Require Import Base Numeric RegExpRecord.

Section Disjoint.
  Context {params: LindenParameters} (rer: RegExpRecord).

  (* no character matches both descriptors *)
  Definition cd_disjoint (cd1 cd2: char_descr) : Prop :=
    forall c, char_match rer c cd1 && char_match rer c cd2 = false.

  (* the compiler relies only on a sound check of disjointness *)
  Class Disjoint := {
    disjoint: char_descr -> char_descr -> bool;
    disjoint_sound: forall cd1 cd2, disjoint cd1 cd2 = true -> cd_disjoint cd1 cd2
  }.

  (* the numeric bounds of a character or a range *)
  Definition bounds (cd: char_descr) : option (nat * nat) :=
    match cd with
    | CdSingle c => Some (Character.numeric_value c, Character.numeric_value c)
    | CdRange l h => Some (Character.numeric_value l, Character.numeric_value h)
    | _ => None
    end.

  (* the classes whose characters the default check enumerates *)
  Definition class_set (cd: char_descr) : option CharSet :=
    match cd with
    | CdDigits => Some Characters.digits
    | CdWhitespace => Some (CharSet.union Characters.white_spaces Characters.line_terminators)
    | CdWordChar => Some (wordCharacters rer)
    | _ => None
    end.

  Definition complements (cd1 cd2: char_descr) : bool :=
    match cd1, cd2 with
    | CdDigits, CdNonDigits | CdWhitespace, CdNonWhitespace | CdWordChar, CdNonWordChar => true
    | _, _ => false
    end.

  Definition outside (l h: nat) (s: CharSet) : bool :=
    forallb (fun e => orb (Nat.ltb (Character.numeric_value e) l) (Nat.ltb h (Character.numeric_value e)))
      (CharSet.elements s).

  (* without ignoreCase: characters and ranges whose bounds do not overlap, a
     class and the characters and ranges that none of its characters falls in,
     two classes that share no character, and a class and its complement *)
  Definition sets_disjoint (cd1 cd2: char_descr) : bool :=
    match bounds cd1, bounds cd2, class_set cd1, class_set cd2 with
    | Some (l1, h1), Some (l2, h2), _, _ => Nat.ltb h1 l2 || Nat.ltb h2 l1
    | Some (l, h), _, _, Some s | _, Some (l, h), Some s, _ => outside l h s
    | _, _, Some s1, Some s2 => forallb (fun e => negb (CharSet.contains s2 e)) (CharSet.elements s1)
    | _, _, _, _ => complements cd1 cd2 || complements cd2 cd1
    end.

  (* the default check, on descriptors other than unions: the empty class, a
     descriptor and its inversion, distinct characters and, without ignoreCase,
     [sets_disjoint] *)
  Definition atoms_disjoint (cd1 cd2: char_descr) : bool :=
    match cd1, cd2 with
    | CdEmpty, _ | _, CdEmpty => true
    | CdInv a, _ => if char_descr_eq_dec a cd2 then true else false
    | _, CdInv b => if char_descr_eq_dec cd1 b then true else false
    | CdSingle c, CdSingle d => negb (Character.canonicalize rer c == Character.canonicalize rer d)
    | _, _ => if RegExpRecord.ignoreCase rer then false else sets_disjoint cd1 cd2
    end.

  (* without ignoreCase, a class matches its characters *)
  Lemma ec_contains: forall s x, RegExpRecord.ignoreCase rer = false ->
    CharSet.exist_canonicalized rer s x = CharSet.contains s x.
  Proof.
    intros s x IC. apply eq_true_iff_eq.
    rewrite CharSet.exist_canonicalized_equiv, CharSet.exist_spec, CharSet.contains_spec.
    split; [intros [e [I E]]|exists x; split]; rewrite ?Character.canonicalize_casesenst, ?EqDec.inversion_true in * by auto; subst; auto.
  Qed.

  Lemma atoms_disjoint_sound: forall cd1 cd2, atoms_disjoint cd1 cd2 = true -> cd_disjoint cd1 cd2.
  Proof.
    intros cd1 cd2 D x. destruct (char_match rer x cd1) eqn:M, (char_match rer x cd2) eqn:M2; auto. exfalso.
    unfold char_match in *.
    destruct cd1, cd2; cbn [atoms_disjoint] in D; try discriminate;
      repeat match type of D with context [char_descr_eq_dec ?a ?b] => destruct (char_descr_eq_dec a b); subst end;
      cbn [char_match'] in *; try discriminate.
    all: try (first [rewrite M in M2|rewrite M2 in M]; discriminate).
    all: try (rewrite ?EqDec.inversion_true in M, M2; rewrite <- M, <- M2, EqDec.reflb in D; discriminate).
    all: destruct (RegExpRecord.ignoreCase rer) eqn:IC; try discriminate.
    all: unfold sets_disjoint, outside, bounds, class_set, complements in D;
      rewrite ?Character.canonicalize_casesenst, ?ec_contains, ?EqDec.inversion_true, ?CharSet.contains_spec,
        ?Character.numeric_pseudo_bij, ?CharSet.range_spec, ?CharSet.remove_all_spec in * by auto; subst.
    all: try (rewrite forallb_forall in D; match goal with I: CharSet.In ?y _ |- _ =>
      specialize (D y (proj2 (CharSet.elements_spec1 _ _) I)) end).
    all: rewrite ?orb_true_iff, ?negb_true_iff, <- ?not_true_iff_false, ?PeanoNat.Nat.ltb_lt, ?CharSet.contains_spec,
      ?CharSet.union_spec in *; intuition (try lia).
  Qed.

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

  Lemma practical_disjoint_sound: forall cd1 cd2, practical_disjoint cd1 cd2 = true -> cd_disjoint cd1 cd2.
  Proof.
    assert (E: forall cd2 cd1, excludes cd1 cd2 = true -> cd_disjoint cd1 cd2).
    { induction cd2; intros cd1 D; try exact (atoms_disjoint_sound _ _ D).
      apply andb_prop in D as [D1 D2]. intros x.
      change (char_match rer x (CdUnion ?a ?b)) with (char_match rer x a || char_match rer x b). rewrite andb_orb_distrib_r. now rewrite (IHcd2_1 _ D1), (IHcd2_2 _ D2). }
    induction cd1; intros cd2 D; try exact (E _ _ D).
    apply andb_prop in D as [D1 D2]. intros x.
    change (char_match rer x (CdUnion ?a ?b)) with (char_match rer x a || char_match rer x b). rewrite andb_orb_distrib_l. now rewrite (IHcd1_1 _ D1), (IHcd1_2 _ D2).
  Qed.

  (* the descriptors whose characters can be enumerated, as sets *)
  Fixpoint cd_set (cd: char_descr) : option CharSet :=
    match cd with
    | CdEmpty => Some CharSet.empty
    | CdSingle c => Some (CharSet.singleton c)
    | CdUnion a b =>
        match cd_set a, cd_set b with Some s1, Some s2 => Some (CharSet.union s1 s2) | _, _ => None end
    | CdAll | CdInv _ => None
    | CdDot => Some (if RegExpRecord.dotAll rer then Characters.all
                    else CharSet.remove_all Characters.all Characters.line_terminators)
    | CdDigits => Some Characters.digits
    | CdNonDigits => Some (CharSet.remove_all Characters.all Characters.digits)
    | CdWhitespace => Some (CharSet.union Characters.white_spaces Characters.line_terminators)
    | CdNonWhitespace =>
        Some (CharSet.remove_all Characters.all (CharSet.union Characters.white_spaces Characters.line_terminators))
    | CdWordChar => Some (wordCharacters rer)
    | CdNonWordChar => Some (CharSet.remove_all Characters.all (wordCharacters rer))
    | CdUnicodeProp p => Some (CharSet.from_list (Property.code_points_for p))
    | CdNonUnicodeProp p => Some (CharSet.remove_all Characters.all (CharSet.from_list (Property.code_points_for p)))
    | CdRange l h => Some (CharSet.range (Character.from_numeric_value (Character.numeric_value l))
                                        (Character.from_numeric_value (Character.numeric_value h)))
    end.

  Lemma cd_set_match: forall cd s x, cd_set cd = Some s ->
    char_match rer x cd = true <-> exists e, CharSet.In e s /\ Character.canonicalize rer e = Character.canonicalize rer x.
  Proof.
    unfold char_match. induction cd; intros s x S; cbn in S |- *; try discriminate.
    13: { destruct (cd_set cd1) as [s1|], (cd_set cd2) as [s2|]; try discriminate. injection S as <-.
      rewrite orb_true_iff, IHcd1, IHcd2 by reflexivity. setoid_rewrite CharSet.union_spec. firstorder. }
    all: injection S as <-; unfold dot_matches; destruct (RegExpRecord.dotAll rer);
      rewrite ?CharSet.exist_canonicalized_equiv, ?CharSet.exist_spec; unfold CharSet.Exists;
      try setoid_rewrite EqDec.inversion_true; try setoid_rewrite CharSet.singleton_spec; try reflexivity.
    all: split; [discriminate + eauto|intros [e [I E]]; first [destruct (CharSet.empty_spec _ I)|subst; auto]].
  Qed.

  (* exact when one of the descriptors can be enumerated, but too slow for the compiler *)
  Definition exact_disjoint (cd1 cd2: char_descr) : bool :=
    match cd_set cd1, cd_set cd2 with
    | Some s, _ => forallb (fun e => negb (char_match rer e cd2)) (CharSet.elements s)
    | None, Some s => forallb (fun e => negb (char_match rer e cd1)) (CharSet.elements s)
    | None, None => false
    end.

  Lemma enumerated_disjoint: forall cd1 cd2 s, cd_set cd1 = Some s ->
    forallb (fun e => negb (char_match rer e cd2)) (CharSet.elements s) = true <-> cd_disjoint cd1 cd2.
  Proof.
    intros cd1 cd2 s S. rewrite forallb_forall. split.
    - intros F x. destruct (char_match rer x cd1) eqn:M; auto. apply (cd_set_match _ _ _ S) in M as [e [I E]].
      apply CharSet.elements_spec1, F, negb_true_iff in I. unfold char_match in *. rewrite <- E. exact I.
    - intros D e I. specialize (D e). apply CharSet.elements_spec1 in I.
      rewrite (proj2 (cd_set_match _ _ _ S)) in D by eauto. cbn in D. now rewrite D.
  Qed.

  (* exact disjointness meets the specification precisely when one of the
     descriptors can be enumerated, which all can but [CdAll], [CdInv] and their unions *)
  Theorem exact_disjoint_spec: forall cd1 cd2, cd_set cd1 <> None \/ cd_set cd2 <> None ->
    exact_disjoint cd1 cd2 = true <-> cd_disjoint cd1 cd2.
  Proof.
    intros cd1 cd2 FIN. unfold exact_disjoint.
    destruct (cd_set cd1) eqn:S1, (cd_set cd2) eqn:S2; rewrite ?(enumerated_disjoint _ _ _ S1), ?(enumerated_disjoint _ _ _ S2); try tauto.
    split; intros D c; rewrite andb_comm; apply D.
  Qed.

  Definition exact_disjointness : Disjoint := {|
    disjoint := exact_disjoint;
    disjoint_sound cd1 cd2 D := proj1 (exact_disjoint_spec cd1 cd2
      ltac:(unfold exact_disjoint in D; destruct (cd_set cd1), (cd_set cd2); [left|left|right|]; congruence)) D
  |}.
End Disjoint.

(* the compiler's default check of disjointness *)
#[global] Instance practical_disjointness {params: LindenParameters} (rer: RegExpRecord) : Disjoint rer :=
  {| disjoint := practical_disjoint rer; disjoint_sound := practical_disjoint_sound rer |}.

(* how a fork between a loop body and the loop exit, or between two
   alternatives, peeks at the next character: [Select cd] keeps the first
   thread where [cd] can be read and the second one elsewhere, [GuardFirst cd]
   keeps the first thread only where [cd] can be read and the second one
   always, and [GuardSecond cd] the second thread only where [cd] can be read
   and the first one always *)
Module Peek.
  Inductive peek {params: LindenParameters} :=
    Unguarded | Select (cd: char_descr) | GuardFirst (cd: char_descr) | GuardSecond (cd: char_descr).
End Peek.

Section NFA.
  Context {params: LindenParameters}.

  (** * NFA Bytecode *)
  (* the bytecode generated for the PikeVM algorithm *)

  Definition label : Type := nat.
  Definition lbl_eq_dec : forall (l1 l2 : label), { l1 = l2 } + { l1 <> l2 }.
  Proof. repeat decide equality. Defined.

  Inductive bytecode: Type :=
  | Accept
  | Consume: char_descr -> bytecode
  | CheckAnchor: anchor -> bytecode
  | Jmp: label -> bytecode
  | Fork: label -> label -> bytecode
  | ForkLazy: label -> label -> bytecode (* runs the second label first *)
  | SetRegOpen: group_id -> bytecode
  | SetRegClose: group_id -> bytecode
  | ResetRegs: list group_id -> bytecode
  | BeginLoop: bytecode
  | EndLoop: label -> bytecode    (* also contains the backedge instead of adding a jump *)
  | KillThread: bytecode         (* for unsupported features *)
  (* Peek without consuming: matching descriptor selects the first target;
     a mismatch (including end of input) selects the second. *)
  | Branch: char_descr -> label -> label -> bytecode
  (* Fork that peeks without consuming: the first label (a loop body or a first
     alternative) is only kept when the descriptor matches; the second is always
     kept, after the first for [GuardFirst] and before it for [GuardFirstLazy]. *)
  | GuardFirst: char_descr -> label -> label -> bytecode
  | GuardFirstLazy: char_descr -> label -> label -> bytecode
  (* Likewise, but the second label (a loop exit or a second alternative) is the
     one only kept when the descriptor matches. *)
  | GuardSecond: char_descr -> label -> label -> bytecode
  | GuardSecondLazy: char_descr -> label -> label -> bytecode
  (* The descriptor of the branching instruction just before; never executed. *)
  | Data: char_descr -> bytecode
  .

  Definition code : Type := list bytecode.

  Definition get_pc (c:code) (pc:label) : option bytecode :=
    List.nth_error c pc.

  (** * Bytecode Properties  *)
  Lemma get_prefix:
    forall c pc prev,
      get_pc (prev ++ c) (length prev + pc) = get_pc c pc.
  Proof.
    unfold get_pc. intros.
    rewrite nth_error_app2; try f_equal; lia.
  Qed.

  Corollary get_first:
    forall c prev,
      get_pc (prev ++ c) (length prev) = get_pc c 0.
  Proof.
    intros. replace (length prev) with (length prev + 0) by lia.
    apply get_prefix.
  Qed.

  (* the labels an instruction may continue at, in priority order *)
  Definition next_pcs (pc:label) (b:bytecode) : list label :=
    match b with
    | Consume _ | CheckAnchor _ | SetRegOpen _ | SetRegClose _ | ResetRegs _ | BeginLoop => [S pc]
    | Accept | KillThread | Data _ => []
    | Jmp l | EndLoop l => [l]
    | Fork l1 l2 | Branch _ l1 l2 | GuardFirst _ l1 l2 | GuardSecond _ l1 l2 => [l1; l2]
    | ForkLazy l1 l2 | GuardFirstLazy _ l1 l2 | GuardSecondLazy _ l1 l2 => [l2; l1]
    end.

  (** * NFA Compilation  *)

  Definition greedy_fork (greedy:bool) (l1 l2:label) :=
    if greedy
    then Fork l1 l2
    else ForkLazy l1 l2.

  (** [branches] enables the peeking instructions: a disjunction whose first
      alternative, or a loop whose body, must start with a known character or
      with a descriptor disjoint from the other side peeks instead of forking;
      otherwise one followed by a known character peeks at it to keep its exit. *)
  Context (rer: RegExpRecord) {DJ: Disjoint rer} (branches: bool).

  Definition union_descr (d1 d2: option char_descr) : option char_descr :=
    match d1, d2 with
    | Some cd1, Some cd2 => Some (CdUnion cd1 cd2)
    | _, _ => None
    end.

  (* Only a mandatory leading character qualifies, or one of either alternative.
     We deliberately do not look through nullable prefixes or quantifiers. *)
  Fixpoint lead_descr (r: regex) : option char_descr :=
    match r with
    | Regex.Character cd => Some cd
    | Disjunction r1 r2 => union_descr (lead_descr r1) (lead_descr r2)
    | Sequence r1 _ => lead_descr r1
    | Group _ r1 => lead_descr r1
    | _ => None
    end.

  (* the characters before which [$] succeeds, besides the end of the input *)
  Definition end_descr : char_descr :=
    if RegExpRecord.multiline rer
    then fold_right (fun c cd => CdUnion (CdSingle c) cd) CdEmpty Character.line_terminators
    else CdEmpty.

  (* like [lead_descr], but [$] also leads with [end_descr], and what is
     nullable leads with [fl], the follow of [r]: what follows a loop succeeds
     only where the next character, if any, is in its follow *)
  Fixpoint follow_descr (r: regex) (fl: option char_descr) : option char_descr :=
    match r with
    | Epsilon => fl
    | Regex.Character cd => Some cd
    | Disjunction r1 r2 => union_descr (follow_descr r1 fl) (follow_descr r2 fl)
    | Sequence r1 r2 => follow_descr r1 (follow_descr r2 fl)
    | Quantified _ 0 (NoI.N 0) _ => fl
    | Quantified _ 0 (NoI.N 1) r1 | Quantified _ 0 NoI.Inf r1 => union_descr (lead_descr r1) fl
    | Group _ r1 => follow_descr r1 fl
    | Anchor EndInput => Some end_descr
    | _ => None
    end.

  (* what follows a loop succeeds only where the next character, if any, is in
     [fl]: a loop peeks at its body's lead when it is disjoint from [fl], saving
     a thread, and otherwise only when it is a character, or else at [fl] when
     it is a character, to keep the exit; a disjunction forks like a greedy loop
     whose exit is its second alternative *)
  Definition loop_peek (r1: regex) (fl: option char_descr) : Peek.peek :=
    let guard := match lead_descr r1, fl with
                 | Some (CdSingle c), _ => Peek.GuardFirst (CdSingle c)
                 | _, Some (CdSingle c) => Peek.GuardSecond (CdSingle c)
                 | _, _ => Peek.Unguarded
                 end in
    match branches, lead_descr r1, fl with
    | true, Some cd1, Some cd2 => if disjoint rer cd1 cd2 then Peek.Select cd1 else guard
    | true, _, _ => guard
    | false, _, _ => Peek.Unguarded
    end.

  Definition loop_fork (greedy: bool) (p: Peek.peek) (body exit: label) : bytecode :=
    match p with
    | Peek.Unguarded => greedy_fork greedy body exit
    | Peek.Select cd => Branch cd body exit
    | Peek.GuardFirst cd => if greedy then GuardFirst cd body exit else GuardFirstLazy cd body exit
    | Peek.GuardSecond cd => if greedy then GuardSecond cd body exit else GuardSecondLazy cd body exit
    end.

  (* a peeking instruction keeps its descriptor in the next cell *)
  Definition pad (p: Peek.peek) : code :=
    match p with Peek.Unguarded => [] | Peek.Select cd | Peek.GuardFirst cd | Peek.GuardSecond cd => [Data cd] end.
  Definition gap (p: Peek.peek) : nat := length (pad p).

  (* [fl] describes what follows [r]; also returns the next fresh label *)
  Fixpoint compile (r:regex) (fl: option char_descr) (fresh:label) : code * label :=
    match r with
    | Epsilon => ([], fresh)
    | Regex.Character cd => ([Consume cd], S fresh)
    | Disjunction r1 r2 =>
        let p := loop_peek r1 (lead_descr r2) in
        let (bc1, f1) := compile r1 fl (S (gap p + fresh)) in
        let (bc2, f2) := compile r2 fl (S f1) in
        ([loop_fork true p (S (gap p + fresh)) (S f1)] ++ pad p ++ bc1 ++ [Jmp f2] ++ bc2, f2)
    | Sequence r1 r2 =>
        let (bc1, f1) := compile r1 (follow_descr r2 fl) fresh in
        let (bc2, f2) := compile r2 fl f1 in
        (bc1 ++ bc2, f2)
    | Quantified greedy 0 (NoI.N 0) r1 => ([], fresh)
    | Quantified greedy 0 (NoI.N 1) r1 =>
        let p := loop_peek r1 fl in
        let (bc1, f1) := compile r1 None (S (S (S (gap p + fresh)))) in
        ([loop_fork greedy p (S (gap p + fresh)) (S f1)] ++ pad p ++
         [BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop (S f1)], S f1)
    | Quantified greedy 0 (NoI.Inf) r1 =>
        let p := loop_peek r1 fl in
        let (bc1, f1) := compile r1 None (S (S (S (gap p + fresh)))) in
        ([loop_fork greedy p (S (gap p + fresh)) (S f1)] ++ pad p ++
         [BeginLoop; ResetRegs (def_groups r1)] ++ bc1 ++ [EndLoop fresh], S f1)
    | Group gid r1 =>
        let (bc1, f1) := compile r1 fl (S fresh) in
        ([SetRegOpen gid] ++ bc1 ++ [SetRegClose gid], S f1)
    | Anchor a => ([CheckAnchor a], S fresh)
    | _ => ([KillThread], S fresh) (* unsupported features *)
    end.

  (* adds an accept at the end of the code *)
  Definition compilation (r:regex) : code :=
    match (compile r None 0) with
    | (c,fresh) => c ++ [Accept]
    end.

  (* [leads c pc cd]: a thread at [pc] dies where the next character is not in [cd] *)
  Inductive leads (c: code) : label -> char_descr -> Prop :=
  | leads_consume: forall pc cd, get_pc c pc = Some (Consume cd) -> leads c pc cd
  | leads_jmp: forall pc l cd, get_pc c pc = Some (Jmp l) -> leads c l cd -> leads c pc cd
  | leads_open: forall pc g cd, get_pc c pc = Some (SetRegOpen g) -> leads c (S pc) cd -> leads c pc cd
  | leads_close: forall pc g cd, get_pc c pc = Some (SetRegClose g) -> leads c (S pc) cd -> leads c pc cd
  | leads_fork: forall pc b l1 l2 cd1 cd2, get_pc c pc = Some b -> next_pcs pc b = [l1; l2] \/ next_pcs pc b = [l2; l1] ->
      leads c l1 cd1 -> leads c l2 cd2 -> leads c pc (CdUnion cd1 cd2)
  | leads_loop: forall pc b l1 l2 cd1 cd2, get_pc c pc = Some b -> next_pcs pc b = [l1; l2] \/ next_pcs pc b = [l2; l1] ->
      get_pc c l1 = Some BeginLoop -> leads c (S (S l1)) cd1 -> leads c l2 cd2 -> leads c pc (CdUnion cd1 cd2)
  | leads_end: forall pc, get_pc c pc = Some (CheckAnchor EndInput) -> leads c pc end_descr.

  (* [c] is found in [C] from label [start] on *)
  Definition code_at (C c: code) (start: label) : Prop :=
    forall i x, nth_error c i = Some x -> get_pc C (i + start) = Some x.

  (** * Inductive NFA characterization *)
  (* like a representation predicate *)

  (* nfa_rep r code pc1 pc2 means that the bytecode for r is represented in code, from pc1 to pc2 (excluded)  *)
  Inductive nfa_rep : regex -> code -> label -> label -> Prop :=
  | nfa_rep_epsilon:
    forall c lbl,
      nfa_rep Epsilon c lbl lbl
  | nfa_rep_char:
    forall c cd lbl
      (CONSUME: get_pc c lbl = Some (Consume cd)),
      nfa_rep (Regex.Character cd) c lbl (S lbl)
  | nfa_rep_disj:
    forall c r1 r2 p start end1 end2
      (PEEK: p = loop_peek r1 (lead_descr r2))
      (FORK: get_pc c start = Some (loop_fork true p (S (gap p + start)) (S end1)))
      (PAD: code_at c (pad p) (S start))
      (NFA1: nfa_rep r1 c (S (gap p + start)) end1)
      (JMP: get_pc c end1 = Some (Jmp end2))
      (NFA2: nfa_rep r2 c (S end1) end2),
      nfa_rep
        (Disjunction r1 r2) c start end2
  | nfa_rep_seq:
    forall c r1 r2 start end1 end2
      (NFA1: nfa_rep r1 c start end1)
      (NFA2: nfa_rep r2 c end1 end2),
      nfa_rep (Sequence r1 r2) c start end2
  | nfa_rep_done:
    forall c r1 greedy lbl,
      nfa_rep (Quantified greedy 0 (NoI.N 0) r1) c lbl lbl
  | nfa_rep_qmark:
    forall c r1 greedy fl p start end1
      (PEEK: p = loop_peek r1 fl)
      (FORK: get_pc c start = Some (loop_fork greedy p (S (gap p + start)) (S end1)))
      (FOLLOW: forall cd, fl = Some cd -> leads c (S end1) cd)
      (PAD: code_at c (pad p) (S start))
      (BEGIN: get_pc c (S (gap p + start)) = Some (BeginLoop))
      (RESET: get_pc c (S (S (gap p + start))) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S (gap p + start)))) end1)
      (END: get_pc c end1 = Some (EndLoop (S end1))),
      nfa_rep (Quantified greedy 0 (NoI.N 1) r1) c start (S end1)
  | nfa_rep_star:
    forall c r1 greedy fl p start end1
      (PEEK: p = loop_peek r1 fl)
      (FORK: get_pc c start = Some (loop_fork greedy p (S (gap p + start)) (S end1)))
      (FOLLOW: forall cd, fl = Some cd -> leads c (S end1) cd)
      (PAD: code_at c (pad p) (S start))
      (BEGIN: get_pc c (S (gap p + start)) = Some (BeginLoop))
      (RESET: get_pc c (S (S (gap p + start))) = Some (ResetRegs (def_groups r1)))
      (NFA1: nfa_rep r1 c (S (S (S (gap p + start)))) end1)
      (END: get_pc c end1 = Some (EndLoop start)),
      nfa_rep (Quantified greedy 0 (NoI.Inf) r1) c start (S end1)
  | nfa_rep_group:
    forall c r1 gid start end1
      (OPEN: get_pc c start = Some (SetRegOpen gid))
      (NFA1: nfa_rep r1 c (S start) end1)
      (CLOSE: get_pc c end1 = Some (SetRegClose gid)),
      nfa_rep (Group gid r1) c start (S end1)
  | nfa_rep_anchor:
    forall c a lbl
      (CHECK: get_pc c lbl = Some (CheckAnchor a)),
      nfa_rep (Anchor a) c lbl (S lbl)
  | nfa_unsupported:
    forall c r lbl
      (UNSUPPORTED: ~ pike_regex r)
      (KILL: get_pc c lbl = Some KillThread),
      nfa_rep r c lbl (S lbl).

  (** * Compile Characterization  *)

  Lemma code_at_app:
    forall C a b start, code_at C (a ++ b) start -> code_at C a start /\ code_at C b (length a + start).
  Proof.
    intros C a b start H. split; intros i x N.
    - apply H. rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    - replace (i + (length a + start)) with (length a + i + start) by lia.
      apply H. rewrite nth_error_app2 by lia. now replace (length a + i - length a) with i by lia.
  Qed.

  (* correctness of the returned fresh label *)
  Lemma fresh_correct:
    forall r fl fresh l next,
      compile r fl fresh = (l, next) ->
      fresh + List.length l = next.
  Proof.
    intros r. induction r; intros fl fresh l next COMPILE; cbn [compile] in COMPILE;
      repeat match type of COMPILE with
      | context [match ?x with _ => _ end] => lazymatch x with compile _ _ _ => fail | _ => destruct x end
      | context [compile ?r' ?fl ?f] => let C := fresh "C" in
          destruct (compile r' fl f) eqn:C; first [apply IHr1 in C | apply IHr2 in C | apply IHr in C]
      end;
      inversion COMPILE; subst; unfold gap; simpl; repeat (rewrite length_app; simpl); lia.
  Qed.

  Lemma loop_fork_next:
    forall greedy p l1 l2 pc,
      next_pcs pc (loop_fork greedy p l1 l2) = [l1; l2] \/ next_pcs pc (loop_fork greedy p l1 l2) = [l2; l1].
  Proof. intros. destruct p, greedy; auto. Qed.

  Lemma lead_follow: forall r fl cd, lead_descr r = Some cd -> follow_descr r fl = Some cd.
  Proof.
    induction r; intros fl d LEAD; simpl in *; try discriminate; auto.
    destruct (lead_descr r1) eqn:L1, (lead_descr r2) eqn:L2; try discriminate.
    erewrite IHr1, IHr2; eauto.
  Qed.

  (* close a goal by a hypothesis that differs in its label, by arithmetic *)
  Local Ltac lbl := match goal with
    | H: get_pc ?C ?l = _ |- get_pc ?C ?l' = _ => refine (eq_rect l (fun k => get_pc C k = _) H l' ltac:(unfold gap; lia))
    | H: code_at ?C ?c ?l |- code_at ?C ?c ?l' => refine (eq_rect l (code_at C c) H l' ltac:(unfold gap; lia))
    | H: nfa_rep ?r ?C ?l ?e |- nfa_rep ?r ?C ?l' _ => refine (eq_rect l (fun k => nfa_rep r C k e) H l' ltac:(unfold gap; lia))
    | H: leads ?C ?l ?cd |- leads ?C ?l' ?cd => refine (eq_rect l (fun k => leads C k cd) H l' ltac:(unfold gap; lia))
    end.

  (* compiled code represents its regex and leads with its follow *)
  Theorem compile_nfa_rep_at:
    forall r fl start c endl C,
      compile r fl start = (c, endl) -> code_at C c start ->
      (forall cd, fl = Some cd -> leads C endl cd) ->
      nfa_rep r C start endl /\ forall cd, follow_descr r fl = Some cd -> leads C start cd.
  Proof.
    induction r; intros fl start c endl C COMP AT FOLLOW; cbn [compile follow_descr] in *;
      repeat match type of COMP with
      | context [match ?x with _ => _ end] => lazymatch x with compile _ _ _ => fail | _ => destruct x eqn:? end
      | context [compile ?r' ?fl ?f] => let C := fresh "C" in
          destruct (compile r' fl f) eqn:C; apply fresh_correct in C as ?
      end;
      injection COMP as <- <-; subst;
      repeat match goal with
      | H: code_at _ (_ ++ _) _ |- _ => apply code_at_app in H as [? ?]
      | H: code_at _ [?x] _ |- _ => specialize (H 0 x eq_refl)
      | H: code_at _ (?x :: ?l) _ |- _ => change (x :: l) with ([x] ++ l) in H
      end; cbn [length Nat.add] in *; unfold gap in *.
    (* the sub-regexes, the last one first, as it leads what precedes it *)
    all: repeat match goal with
      | IH: forall fl s c e C, compile ?r fl s = (c, e) -> _, CO: compile ?r _ _ = _ |- _ =>
          edestruct IH with (C := C) as [? ?]; [exact CO|lbl|first [exact FOLLOW|eassumption|solve [intros; first [discriminate
            |eapply leads_jmp; [lbl|eauto]|eapply leads_close; [lbl|eauto]]]]|]; clear IH
      end.
    all: split; try solve [econstructor; try reflexivity; try exact FOLLOW; try lbl; intro N; inversion N].
    all: intros d F; unfold union_descr in F; repeat match type of F with context [match ?x with _ => _ end] => destruct x eqn:? end;
      try discriminate; try injection F as <-.
    all: solve [eauto | apply leads_consume; lbl | apply leads_end; lbl | eapply leads_open; [lbl|eauto]
      | eapply leads_fork; [lbl|apply loop_fork_next|eauto..]
      | eapply leads_loop; [lbl|apply loop_fork_next|lbl|eauto using lead_follow|eauto]].
  Qed.

  Corollary compile_nfa_rep:
    forall r c endl suffix,
      compile r None 0 = (c, endl) -> nfa_rep r (c ++ suffix) 0 endl.
  Proof.
    intros. eapply compile_nfa_rep_at; eauto; [|discriminate].
    intros i x N. unfold get_pc. rewrite PeanoNat.Nat.add_0_r, nth_error_app1; auto. apply nth_error_Some. congruence.
  Qed.

  (** * Lifting the representation predicate to continuations  *)
  (* This is useful to relate the continuations used in the tree semantics to the code produced by the NFA compiler *)

  (* action_rep a c pc1 pc2 indicates that the bytecode for a is located in code c between labels pc1 and pc2  *)
  Inductive action_rep : action -> code -> label -> label -> Prop :=
  | areg_bc:
    forall r c pcstart pcend
      (NFA: nfa_rep r c pcstart pcend),
      action_rep (Areg r) c pcstart pcend
  | acheck_bc:
    forall c str pc pcnext
      (END: get_pc c pc = Some (EndLoop pcnext)),
      action_rep (Acheck str) c pc pcnext
  | aclose_bc:
    forall c gid pc
      (CLOSE: get_pc c pc = Some (SetRegClose gid)),
      action_rep (Aclose gid) c pc (S pc).

  (* continuation_rep cont c pc n means that the bytecode for cont is located in c at labels pc *)
  (* inside the representation of the continuation, there might be extra jump instructions *)
  (* this representation has to end on an accept instruction, at the end of the bytecode *)
  Inductive actions_rep : actions -> code -> label -> Prop :=
  | empty_bc:
    (* when the continuation is empty, it means we have nothing more to do and found a match *)
    (* in the bytecode, this means an accept *)
    forall c pc
      (ACCEPT: get_pc c pc = Some Accept),
      actions_rep [] c pc
  | cons_bc:
    forall a cont c pcstart pcmid
      (ACTION: action_rep a c pcstart pcmid)
      (CONT: actions_rep cont c pcmid),
      actions_rep (a::cont) c pcstart
  | jump_bc:
    forall cont c pcstart pc
      (CONT: actions_rep cont c pcstart)
      (JMP: get_pc c pc = Some (Jmp pcstart)),
      actions_rep cont c pc.

  (** * Stuttering  *)
  (* There are a few cases where the PikeVM takes more steps than the Pike Tree. *)
  (* These are stutter steps. *)
  (* They correspond to
    - being at a Jmp instruction, inserted for a disjunction
    - being at a BeginLoop instruction, inserted for a quantifier
  *)

  (* With the definitions below, we provide ways to know when a state is going to stutter *)

  (* returns true if that state will stutter *)
  (* or if we are at an unsupported feature *)
  Definition stutters (pc:label) (code:code) : bool :=
    match get_pc code pc with
    | Some (Jmp _) => true
    | Some BeginLoop => true
    | Some KillThread => true
    | _ => false
    end.

  Lemma loop_fork_no_stutter:
    forall greedy p l1 l2 pc code,
      get_pc code pc = Some (loop_fork greedy p l1 l2) -> stutters pc code = false.
  Proof. intros. unfold stutters. rewrite H. destruct p, greedy; auto. Qed.

  Lemma does_stutter:
    forall pc code, stutters pc code = true ->
              get_pc code pc = Some BeginLoop \/ (exists next, get_pc code pc = Some (Jmp next)) \/ get_pc code pc = Some KillThread.
  Proof.
    unfold stutters. intros. destruct get_pc; try destruct b; inversion H; eauto.
  Qed.

  Lemma doesnt_stutter_jmp:
    forall pc code next, stutters pc code = false -> get_pc code pc = Some (Jmp next) -> False.
  Proof.
    unfold stutters, not. intros. destruct get_pc; try destruct b; inversion H0. inversion H.
  Qed.

  Lemma doesnt_stutter_begin:
    forall pc code, stutters pc code = false -> get_pc code pc = Some BeginLoop -> False.
  Proof.
    unfold stutters, not. intros. destruct get_pc; try destruct b; inversion H0. inversion H.
  Qed.

  Lemma doesnt_stutter_kill:
    forall pc code, stutters pc code = false -> get_pc code pc = Some KillThread -> False.
  Proof.
    unfold stutters, not. intros. destruct get_pc; try destruct b; inversion H0. inversion H.
  Qed.

End NFA.


Ltac no_stutter :=
  match goal with
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (Jmp _) |- _ ] => exfalso; eapply doesnt_stutter_jmp; eauto
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (BeginLoop) |- _ ] => exfalso; eapply doesnt_stutter_begin; eauto
  | [ H : stutters ?pc ?code = false, H1: get_pc ?code ?pc = Some (KillThread) |- _ ] => exfalso; eapply doesnt_stutter_kill; eauto
  end.

Ltac stutter :=
  match goal with
  | [ H : stutters ?pc ?code = true, H1: get_pc ?code ?pc = Some (loop_fork _ _ _ _) |- _ ] =>
      rewrite (loop_fork_no_stutter _ _ _ _ _ _ H1) in H; discriminate
  | [ H : stutters ?pc ?code = true, H1: get_pc ?code ?pc = Some _ |- _ ] =>
      try solve[unfold stutters in H; rewrite H1 in H; inversion H]
  end.

Ltac locate_pc pc GET :=
  try match goal with PAD: code_at _ (pad ?p) _ |- _ =>
    unfold gap, pad in *; destruct p; try pose proof (PAD 0 _ eq_refl) as DATA; cbn [length Nat.add] in *
  end;
  repeat match goal with
  | H : get_pc ?cc ?l = Some ?j, G : get_pc ?cc pc = Some _ |- _ =>
      assert (pc = l \/ pc <> l) as [->|] by lia;
      [rewrite H in GET; injection GET as <-; clear H|clear H]
  end.

Ltac invert_rep :=
   match goal with
   | [ H : actions_rep _ _ (Areg _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep _ _ (Aclose _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep _ _ (Acheck _ :: _) _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : actions_rep _ _ [] _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep _ _ (Areg _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep _ _ (Aclose _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : action_rep _ _ (Acheck _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Epsilon) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Regex.Character _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Disjunction _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Sequence _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Quantified _ _ _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Group _ _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | [ H : nfa_rep _ _ (Anchor _) _ _ _ |- _ ] => inversion H; clear H; subst; try no_stutter
   | _ => try no_stutter
   end.
