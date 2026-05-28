From Stdlib Require Import List Lia.
Import ListNotations.

From Linden Require Import ListLemmas.
From Linden Require Import Utils Parameters LWParameters.
Import Utils.List.
From Warblre Require Import Base Typeclasses RegExpRecord Semantics Result Errors.

(** * Characters and Strings  *)

Section Chars.
  Context {params: LindenParameters}.
  Context (rer: RegExpRecord).

  (* In the semantics, the input string is represented with both the next characters to read
   and the reversed list of previously read characters (in case we change direction for a lookbehind) *)
  Inductive input : Type :=
  | Input (next: string) (pref: string).

  Definition input_eq_dec: forall (i1 i2: input), { i1 = i2 } + { i1 <> i2 }.
  Proof. decide equality; apply string_eq_dec. Defined.
  #[export] Instance input_EqDec: EqDec input := EqDec.make input input_eq_dec.


  (* Get the current string index from the input *)
  Definition idx (inp:input) : nat :=
    match inp with
    | Input next pref => List.length pref
    end.

  Definition next_str (i:input) : string :=
    match i with
    | Input s _ => s
    end.

  Definition pref_str (i:input) : string :=
  match i with
  | Input _ s => s
  end.

  Definition current_str (i:input) (dir: Direction) : string :=
    match i with
    | Input next pref =>
        match dir with forward => next | backward => pref end
    end.

  (* Remaining length of an input given a direction *)
  Definition remaining_length (inp: input) (dir: Direction): nat :=
    let '(Input next pref) := inp in
    match dir with
    | forward => length next
    | backward => length pref
    end.

  Definition input_str (i: input): string :=
    match i with
    | Input next pref => List.rev pref ++ next
    end.

  Definition total_length (inp: input) : nat :=
    let '(Input next pref) := inp in
    length next + length pref.

  (* Getting a substring from an input *)
  Definition substr (inp: input) (startIdx endIdx: nat): string :=
    List.firstn (endIdx-startIdx) (List.skipn startIdx (input_str inp)).

  Definition init_input (str:string) : input :=
    Input str [].

  Definition input_rewind (i: input) (dir: Direction) : input :=
    match dir with
    | backward => Input (input_str i) []
    | forward => Input [] (List.rev (input_str i))
    end.

  Definition input_reverse (i: input) : input :=
    let '(Input next pref) := i in
    Input pref next.

  Lemma input_reverse_involutive : forall i, input_reverse (input_reverse i) = i.
  Proof. now destruct i. Qed.

  Lemma input_reverse_surj :
    forall i, exists i', input_reverse i' = i.
  Proof.
    intro i. exists (input_reverse i). apply input_reverse_involutive.
  Qed.

  Lemma input_reverse_inj :
    forall i1 i2, input_reverse i1 = input_reverse i2 <-> i1 = i2.
  Proof.
    intros i1 i2. split; intros H.
    - apply f_equal with (f:=input_reverse) in H.
      now rewrite !input_reverse_involutive in H.
    - now rewrite H.
  Qed.

  Definition direction_reverse (dir: Direction) : Direction :=
    match dir with
    | forward => backward
    | backward => forward
    end.

  Lemma direction_reverse_involutive : forall dir, direction_reverse (direction_reverse dir) = dir.
  Proof. now destruct dir. Qed.


  (* Definition of when an input is compatible with (i.e. represents) a given input string str0. *)
  Inductive input_compat: input -> string -> Prop :=
  | Input_compat: forall next pref str0, List.rev pref ++ next = str0 -> input_compat (Input next pref) str0.

  Definition inb_canonicalized (c: Character) (l: list Character) :=
    inb (Character.canonicalize rer c) (List.map (Character.canonicalize rer) l).

  Lemma map_canonicalize_casesenst:
    RegExpRecord.ignoreCase rer = false ->
    forall l, List.map (Character.canonicalize rer) l = l.
  Proof.
    intro Hcasesenst.
    induction l; simpl; auto.
    rewrite canonicalize_casesenst, IHl by auto. auto.
  Qed.

  Lemma inb_canonicalized_casesenst:
    RegExpRecord.ignoreCase rer = false ->
    forall c l, inb_canonicalized c l = inb c l.
  Proof.
    intros Hcasesenst c l. unfold inb_canonicalized.
    rewrite canonicalize_casesenst by assumption.
    rewrite map_canonicalize_casesenst by assumption.
    reflexivity.
  Qed.


  Definition wordCharacters (rer: RegExpRecord): CharSet :=
    match Semantics.wordCharacters rer with
    | Success cs => cs
    | Error _ => Characters.ascii_word_characters
    end.

  (* Deciding whether a character is a word character, to check for word boundaries and for character classes \w and \W *)
  Definition word_char c := CharSet.contains (wordCharacters rer) c.

  (* Lemma for boolean version of In *)
  (* Lemma char_all_inb: forall c, inb c Character.all = true.
  Proof.
    intro c. rewrite inb_spec. apply char_all_in.
  Qed. *)


  (** * Character Descriptors  *)
  (* by character descriptors, we mean everything that can represent a single character *)
  (* the character itself, the dot, an escape, a character group like \d, character classes *)
  Inductive char_descr: Type :=
  | CdEmpty
  | CdDot
  | CdAll
  | CdSingle (c: Character)
  | CdDigits
  | CdNonDigits
  | CdWhitespace
  | CdNonWhitespace
  | CdWordChar
  | CdNonWordChar
  | CdUnicodeProp (p: Property)
  | CdNonUnicodeProp (p: Property)
  | CdInv (cd: char_descr)
  | CdRange (l h: Character)
  | CdUnion (cd1 cd2: char_descr).

  (* Whether dot matches a character *)
  Definition dot_matches (dotAll: bool) (c: Character): bool :=
    if dotAll then
      CharSet.exist_canonicalized rer Characters.all c
    else
      CharSet.exist_canonicalized rer (CharSet.remove_all Characters.all Characters.line_terminators) c.

  Fixpoint char_match' (ccan: Character) (cd: char_descr): bool :=
    match cd with
    | CdEmpty => false
    | CdDot =>
        dot_matches (RegExpRecord.dotAll rer) ccan
    | CdAll => true
    | CdSingle c' => ccan == Character.canonicalize rer c'
    | CdDigits => CharSet.exist_canonicalized rer Characters.digits ccan
    | CdNonDigits => CharSet.exist_canonicalized rer (CharSet.remove_all Characters.all Characters.digits) ccan
    | CdWhitespace => CharSet.exist_canonicalized rer (CharSet.union Characters.white_spaces Characters.line_terminators) ccan
    | CdNonWhitespace => CharSet.exist_canonicalized rer (CharSet.remove_all Characters.all (CharSet.union Characters.white_spaces Characters.line_terminators)) ccan
    | CdWordChar => CharSet.exist_canonicalized rer (wordCharacters rer) ccan
    | CdNonWordChar => CharSet.exist_canonicalized rer (CharSet.remove_all Characters.all (wordCharacters rer)) ccan
    | CdUnicodeProp p => CharSet.exist_canonicalized rer (CharSet.from_list (Property.code_points_for p)) ccan
    | CdNonUnicodeProp p => CharSet.exist_canonicalized rer (CharSet.remove_all Characters.all (CharSet.from_list (Property.code_points_for p))) ccan
    | CdInv cd' => negb (char_match' ccan cd')
    | CdRange l h =>
        let i := Character.numeric_value l in
        let j := Character.numeric_value h in
        let charSet := CharSet.range (Character.from_numeric_value i) (Character.from_numeric_value j) in
        CharSet.exist_canonicalized rer charSet ccan
    | CdUnion cd1 cd2 => char_match' ccan cd1 || char_match' ccan cd2
    end.

  Definition char_match (c: Character) (cd: char_descr) :=
    char_match' (Character.canonicalize rer c) cd.


  Lemma single_match:
    forall c1 c2, char_match c1 (CdSingle c2) = true <-> Character.canonicalize rer c1 = Character.canonicalize rer c2.
  Proof.
    intros c1 c2. simpl. apply EqDec.inversion_true.
  Qed.

  (* a character is in range of itself *)
  Lemma char_match_range_refl: forall c,
    char_match c (CdRange c c) = true.
  Proof.
    unfold char_match, char_match'. intros c.
    rewrite
      Character.numeric_pseudo_bij,
      CharSet.exist_canonicalized_equiv,
      CharSet.exist_spec.
    unfold CharSet.Exists.
    exists c. split.
    - rewrite CharSet.range_spec. now constructor.
    - apply EqDec.reflb.
  Qed.

  Definition char_descr_eq_dec : forall (cd1 cd2: char_descr), { cd1 = cd2 } + { cd1 <> cd2 }.
  Proof. decide equality; try apply Character.eq_dec; try apply Property.unicode_property_eqdec. Defined.


  (** * Reading Characters in the String *)

  (* read_char cd i dir returns None if the next character of i with direction dir is accepted by cd *)
  (* otherwise it returns the next input after reading the character, as well as the character actually read *)
  Definition read_char (cd:char_descr) (i:input) (dir: Direction) : option (Character * input) :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            match next with
            | [] => None
            | h::next' => if char_match h cd
                        then Some (h, Input next' (h::pref))
                        else None
            end
        | backward =>
            match pref with
            | [] => None
            | h::pref' => if char_match h cd
                        then Some (h, Input (h::next) pref')
                        else None
            end
        end
    end.

  Inductive ReadResult  : Type :=
  | CanRead
  | CannotRead.

  (* the function above is useful when defining trees *)
  (* however, the VMs do it differently: they will test the same character of the input multiple times before advancing *)
  (* instead, we use the two following functions to read and advance *)

  (* simply checks if the next character of the input corresponds to the given character descriptor *)
  Definition check_read (cd:char_descr) (i:input) (dir: Direction) : ReadResult :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            match next with
            | [] => CannotRead
            | h::next' => if char_match h cd
                        then CanRead
                        else CannotRead
            end
        | backward =>
            match pref with
            | [] => CannotRead
            | h::pref' => if char_match h cd
                        then CanRead
                        else CannotRead
            end
        end
    end.

  (* Advance input to the next or previous character depending on direction *)
  Definition advance_input (i:input) (dir: Direction) : option input :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            match next with
            | [] => None
            | h::next' => Some (Input next' (h::pref))
            end
        | backward =>
            match pref with
            | [] => None
            | h::pref' => Some (Input (h::next) pref')
            end
        end
    end.

  (* Same, but just return the input in case of failure *)
  Definition advance_input' (i: input) (dir: Direction): input :=
    match advance_input i dir with
    | Some nextinp => nextinp
    | None => i
    end.

  Lemma advance_input_success:
    forall i dir nexti,
      advance_input i dir = Some nexti ->
      advance_input' i dir = nexti.
  Proof.
    intros i dir nexti H. unfold advance_input'. rewrite H. reflexivity.
  Qed.

  Lemma advance_input'_undo:
    forall inp inp' dir,
      advance_input inp dir = Some inp' ->
      advance_input' inp' (direction_reverse dir) = inp.
  Proof.
    unfold advance_input'.
    intros [next pref] inp' [] H.
    - destruct next; [discriminate|now injection H as <-].
    - destruct pref; [discriminate|now injection H as <-].
  Qed.



  Lemma advance_input_not_self:
    forall inp dir,
      ~(advance_input inp dir = Some inp).
  Proof.
    intros [next pref] dir H.
    destruct dir; [destruct next|destruct pref]; inversion H; eapply cons_different; eauto.
  Qed.

  (* Advancing input several times *)
  Definition advance_input_n (i: input) (n: nat) (dir: Direction): input :=
    match i with
    | Input next pref =>
        match dir with
        | forward =>
            let nnext := List.skipn n next in
            let read := List.firstn n next in
            Input nnext (List.rev read ++ pref)
        | backward =>
            let npref := List.skipn n pref in
            let read := List.firstn n pref in
            Input (List.rev read ++ next) npref
        end
    end.

  (* the proof of equivalence between the two *)
  Theorem can_read_correct:
    forall i1 cd dir i2,
    (exists c, read_char cd i1 dir = Some (c, i2)) <->
      check_read cd i1 dir = CanRead /\ advance_input i1 dir = Some i2.
  Proof.
    intros i1 cd dir i2. split; intros.
    - destruct H as [c H].
      destruct i1. simpl. simpl in H. destruct dir.
      + destruct next. inversion H. destruct (char_match t cd); inversion H; auto.
      + destruct pref. inversion H. destruct (char_match t cd); inversion H; auto.
    - destruct i1. simpl. simpl in H. destruct dir.
      + destruct next; inversion H; inversion H1.
        exists t. destruct (char_match t cd); inversion H0. auto.
      + destruct pref; inversion H; inversion H1.
        exists t. destruct (char_match t cd); inversion H0. auto.
  Qed.

  Lemma read_char_success_advance:
    forall cd inp dir c nextinp,
      read_char cd inp dir = Some (c, nextinp) ->
      advance_input inp dir = Some nextinp.
  Proof.
    intros. destruct inp as [next pref]. destruct dir; simpl in *.
    - (* Forward *)
      destruct next as [|h next']; try discriminate.
      destruct char_match; try discriminate. now injection H as <- <-.
    - (* Backward *)
      destruct pref as [|h pref']; try discriminate.
      destruct char_match; try discriminate. now injection H as <- <-.
  Qed.

  Theorem cannot_read_correct:
    forall i cd dir,
      read_char cd i dir = None <-> check_read cd i dir = CannotRead.
  Proof.
    intros i cd dir. destruct i. simpl. destruct dir.
    - destruct next; split; auto.
      + destruct (char_match t cd); auto. inversion 1.
      + destruct (char_match t cd); auto. inversion 1.
    - destruct pref; split; auto.
      + destruct (char_match t cd); auto. inversion 1.
      + destruct (char_match t cd); auto. inversion 1.
  Qed.

  (* if we cannot read forward, we also cannot backward on the reverse input *)
  Lemma read_char_reverse_none:
    forall cd inp dir,
      read_char cd inp dir = None ->
      read_char cd (input_reverse inp) (direction_reverse dir) = None.
  Proof.
    intros cd [next pref] [] Hread.
    - destruct next as [|c' next]; simpl in *; now only 2: destruct char_match.
    - destruct pref as [|c' pref]; simpl in *; now only 2: destruct char_match.
  Qed.

  (* if we can read forward, we can also read backward on the reverse input *)
  Lemma read_char_reverse_some:
    forall cd inp dir c nextinp,
      read_char cd inp dir = Some (c, nextinp) ->
      read_char cd (input_reverse inp) (direction_reverse dir) = Some (c, input_reverse nextinp).
  Proof.
    intros cd [next pref] [] c nextinp Hread.
    - destruct next as [|c' next]; simpl in *; destruct char_match; try discriminate.
      now injection Hread as <- <-.
    - destruct pref as [|c' pref]; simpl in *; destruct char_match; try discriminate.
      now injection Hread as <- <-.
  Qed.


  Lemma advance_input_n_0:
    forall inp dir, advance_input_n inp 0 dir = inp.
  Proof.
    intros [next pref] dir. simpl. now destruct dir.
  Qed.

  (* advancing a cons input by n+1 is the same as advancing its tail by n *)
  Lemma advance_input_n_succ_forward:
    forall c next pref n, advance_input_n (Input (c :: next) pref) (S n) forward = advance_input_n (Input next (c::pref)) n forward.
  Proof.
    intros. simpl. now rewrite <-app_assoc.
  Qed.

  (* Inductive relation of next_inputs *)
  Inductive next_input : input -> input -> Direction -> Prop :=
  | nextin: forall i1 i2 dir (ADVANCE: advance_input i1 dir = Some i2),
      next_input i1 i2 dir.
End Chars.
