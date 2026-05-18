(** Rocq support for visualizing backtracking trees. *)

From Stdlib Require Import List.
Import ListNotations.

From Linden Require Import Regex Chars Groups Semantics StrictSuffix.
From Linden Require Import FunctionalSemantics Parameters LWParameters.
From Linden Require Tree.
From Warblre Require Import Base RegExpRecord.

Module AnnotatedTrees.
Section Annotated.
  Context {params: LindenParameters}.

  Record annotation :=
    { acts: actions; inp: input; gm: group_map; dir: Direction }.

  (** Like Linden's `tree`, but with extra annotation nodes. *)
  Inductive tree : Type :=
  (* Copy-pasted verbatim from Linden: *)
  | Mismatch
  | Match
  | Choice (t1 t2: tree)
  | Read (c: Character) (t: tree)
  | ReadBackRef (str: string) (t: tree)
  | Progress (t: tree)
  | AnchorPass (a: anchor) (t: tree)
  | GroupAction (g: groupaction) (t: tree)
  | LK (lk: lookaround) (tlk t: tree)
  | LKFail (lk: lookaround) (tlk: tree)
  (* Added: *)
  | Annot (a: annotation) (t: tree).

  (** Remove annotations. *)
  Fixpoint erase (a: tree) : Tree.tree :=
    match a with
    | Mismatch => Tree.Mismatch
    | Match => Tree.Match
    | Choice t1 t2 => Tree.Choice (erase t1) (erase t2)
    | Read c t => Tree.Read c (erase t)
    | ReadBackRef s t => Tree.ReadBackRef s (erase t)
    | Progress t => Tree.Progress (erase t)
    | AnchorPass an t => Tree.AnchorPass an (erase t)
    | GroupAction g t => Tree.GroupAction g (erase t)
    | LK lk tlk t => Tree.LK lk (erase tlk) (erase t)
    | LKFail lk tlk => Tree.LKFail lk (erase tlk)
    | Annot _ t => erase t
    end.

  (** Like `greedy_choice`, but returning an annotated tree.  *)
  Definition greedy_choice (greedy: bool) (a b: tree) : tree :=
    (* Copy-pasted verbatim from Linden: *)
    if greedy then Choice a b else Choice b a.

  Notation "x |> f" := (f x) (at level 40, only parsing).

  Context (rer: RegExpRecord).

  Section WithCoercion.
  (* Adding a coercion makes lk_result work without changes. *)
  Local Coercion erase : tree >-> Tree.tree.

  (** Like `compute_tree`, but annotate each node with the state that produced it. *)
  Fixpoint compute_tree (act: actions) (inp: input) (gm: group_map) (dir: Direction) (fuel:nat): option tree :=
    (* Copy-pasted verbatim from Linden: *)
    match fuel with
    | 0 => None
    | S fuel =>
        match act with
        (* tree_done *)
        | [] => Some Match
        (* tree_check, tree_check_fail *)
        | Acheck strcheck :: cont =>
            if (is_strict_suffix inp strcheck dir) then
              match (compute_tree cont inp gm dir fuel) with
              | Some treecont => Some (Progress treecont)
              | None => None
              end
            else Some Mismatch
        (* tree_close *)
        | Aclose gid :: cont =>
            match (compute_tree cont inp (GroupMap.close (idx inp) gid gm) dir fuel) with
            | Some treecont => Some (GroupAction (Close gid) treecont)
            | None => None
            end
        (* tree_epsilon *)
        | Areg Epsilon::cont => compute_tree cont inp gm dir fuel
        (* tree_char, tree_char_fail *)
        | Areg (Regex.Character cd)::cont =>
            match read_char rer cd inp dir with
            | Some (c, nextinp) =>
                match (compute_tree cont nextinp gm dir fuel) with
                | Some treecont => Some (Read c treecont)
                | None => None
                end
            | None => Some Mismatch
                end
        (* tree_disj *)
        | Areg (Disjunction r1 r2)::cont =>
            match (compute_tree (Areg r1 :: cont) inp gm dir fuel, compute_tree (Areg r2 :: cont) inp gm dir fuel) with
            | (Some t1, Some t2) => Some (Choice t1 t2)
            | _ => None
            end
        (* tree_sequence *)
        | Areg (Sequence r1 r2)::cont =>
            compute_tree (seq_list r1 r2 dir ++ cont) inp gm dir fuel
        (* tree_quant_forced *)
        | Areg (Quantified greedy (S min) delta r1)::cont =>
            let gidl := def_groups r1 in
            match compute_tree (Areg r1 :: Areg (Quantified greedy min delta r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel with
            | Some titer => Some (GroupAction (Reset gidl) titer)
            | None => None
            end
        (* tree_quant_done *)
        | Areg (Quantified greedy 0 (NoI.N 0) r1)::cont =>
            compute_tree cont inp gm dir fuel
        (* tree_quant_free *)
        | Areg (Quantified greedy 0 delta r1)::cont =>
            let gidl := def_groups r1 in
            match  (compute_tree (Areg r1 :: Acheck inp :: Areg (Quantified greedy 0 (noi_pred delta) r1) :: cont) inp (GroupMap.reset gidl gm) dir fuel, compute_tree cont inp gm dir fuel) with
            | (Some titer, Some tskip) =>  Some (greedy_choice greedy (GroupAction (Reset gidl) titer) tskip)
            | _ => None
            end
        (* tree_group *)
        | Areg (Group gid r1)::cont =>
            match compute_tree (Areg r1 :: Aclose gid :: cont) inp (GroupMap.open (idx inp) gid gm) dir fuel with
            | Some treecont => Some (GroupAction (Open gid) treecont)
            | _ => None
            end
        (* tree_lk, tree_lk_fail *)
        | Areg (Lookaround lk r1)::cont =>
            let treelk := compute_tree [Areg r1] inp gm (lk_dir lk) fuel in
            match treelk with
            | None => None
            | Some treelk =>
                match lk_result lk treelk gm inp with
                | Some gmlk =>
                  let treecont := compute_tree cont inp gmlk dir fuel in
                  match treecont with None => None | Some treecont =>
                    Some (LK lk treelk treecont)
                  end
                | None => Some (LKFail lk treelk)
                end
            end
        (* tree_anchor, tree_anchor_fail *)
        | Areg (Anchor a)::cont =>
          if anchor_satisfied rer a inp then
            let treecont := compute_tree cont inp gm dir fuel in
            match treecont with None => None | Some treecont =>
              Some (AnchorPass a treecont)
            end
          else
            Some Mismatch
        (* tree_backref, tree_backref_fail *)
        | Areg (Backreference gid)::cont =>
          match read_backref rer gm gid inp dir with
          | Some (br_str, nextinp) =>
            let tcont := compute_tree cont nextinp gm dir fuel in
            match tcont with None => None | Some tcont =>
              Some (ReadBackRef br_str tcont)
            end
          | None =>
            Some Mismatch
          end
        end
    end
      (* Added: *)
      |> (option_map (Annot (Build_annotation act inp gm dir))).
  End WithCoercion.

  (** Erasing annotations yields the original `compute_tree`. *)
  Lemma erase_compute_tree :
    forall n act inp gm dir,
      option_map erase (compute_tree act inp gm dir n)
      = FunctionalSemantics.compute_tree rer act inp gm dir n.
  Proof.
    induction n; intros act inp gm dir; [reflexivity|].
    cbn [compute_tree FunctionalSemantics.compute_tree].
    repeat (match goal with
            | _ => reflexivity
            | _ => rewrite <- IHn
            | _ => progress (cbn; unfold greedy_choice, Tree.greedy_choice)
            | |- context [match ?x with _ => _ end] => destruct x
            | |- context [compute_tree] => destruct compute_tree
            end).
  Qed.

  (* Whether subtrees match their annotations. *)
  Inductive wf : tree -> Prop :=
  | wf_mismatch : wf Mismatch
  | wf_match : wf Match
  | wf_choice t1 t2 : wf t1 -> wf t2 -> wf (Choice t1 t2)
  | wf_read c t : wf t -> wf (Read c t)
  | wf_backref s t : wf t -> wf (ReadBackRef s t)
  | wf_progress t : wf t -> wf (Progress t)
  | wf_anchorpass a t : wf t -> wf (AnchorPass a t)
  | wf_groupaction g t : wf t -> wf (GroupAction g t)
  | wf_lk lk tlk t : wf tlk -> wf t -> wf (LK lk tlk t)
  | wf_lkfail lk tlk : wf tlk -> wf (LKFail lk tlk)
  | wf_annot acts inp gm dir t fuel :
    wf t ->
    FunctionalSemantics.compute_tree rer acts inp gm dir fuel = Some (erase t) ->
    wf (Annot (Build_annotation acts inp gm dir) t).

  Hint Constructors wf : core.

  Lemma wf_compute_tree : forall fuel act inp gm dir t,
      compute_tree act inp gm dir fuel = Some t ->
      wf t.
  Proof.
    induction fuel; intros act inp gm dir t Hc; [discriminate Hc | ].
    pose proof (erase_compute_tree (S fuel) act inp gm dir) as Hec;
      rewrite Hc in Hec.
    repeat (match type of Hc with
            | _ => progress cbn in Hc
            | None = Some _ => discriminate Hc
            | Some _ = Some _ => injection Hc as Hc; subst
            | context [compute_tree ?a ?i ?g ?d ?ff] =>
                destruct (compute_tree a i g d ff) eqn:?
            | context [greedy_choice ?b _ _] => destruct b
            | context [match ?x with _ => _ end] => destruct x
            end).
    all: eauto 8.
  Qed.
End Annotated.
End AnnotatedTrees.

From Linden Require Import RegexpTranslation.
From Warblre Require Import Patterns.
From Warblre Require ExtractionSetup.

Module Extraction.
Import AnnotatedTrees.
Import ExtractionSetup.

Section Generic.
  Context {params: LindenParameters}.

  (** Translate a Warblre regex to Linden. *)
  Definition linden_regex_of_warblre_regex (wr: Patterns.Regex) : regex :=
    warblre_to_linden' wr 0 (buildnm wr).

  (** Compute the annotated tree for a given regex and input. *)
  Definition tree_of_linden_regex (r: regex) (input: string) (fuel: nat) : option tree :=
    let inp := init_input input in
    let rer := reg_exp_record false false false tt (max_group r) in
    compute_tree rer [Areg r] inp GroupMap.empty forward fuel.
End Generic.

Set Extraction Output Directory ".".
Extraction "LindenAPI.ml"
  tree_of_linden_regex linden_regex_of_warblre_regex lindenParameters_of_warblre.
End Extraction.
