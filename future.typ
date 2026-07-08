#import "@preview/cheq:0.3.1": checklist

#show link: underline
#show: checklist
#set text(size: 10pt)
#set raw(syntaxes: (
  "./regex.sublime-syntax",
  "./rocq.sublime-syntax",
))


= Valorisation: status & future work

== Done, need merging

- [ ] #link("https://github.com/LindenRegex/Linden/tree/mw/reverse-pikevm")[Reverse PikeVM] -- Extending PikeVM to read input from right to left. This is useful for avoiding the need to reverse the entire input. PR open #link("https://github.com/LindenRegex/Linden/pull/30")[here]. Zero blockers, just needs a review and merge.
- [ ] #link("https://github.com/LindenRegex/Linden/tree/mw/booltree-dir")[Lookarounds in bool_tree] -- Extending bool_tree semantics with lookarounds (non-oracle). Required adding a direction to bool_tree inductive which generates a large diff. PR open #link("https://github.com/LindenRegex/Linden/pull/31")[here]. Zero blockers, just needs a review and merge.
- [ ] #link("https://github.com/LindenRegex/Warblre/tree/mw/rocq-released")[Prepare Warblre release] -- We want to release Warblre to #link("https://rocq-prover.org/packages")[Rocq's opam repository] which will make it easier for dependents to install Warblre (plus we enforce some versioning of Warblre). Zero blockers, just needs to be done.
  - [ ] Follow instructions in `doc/Publishing.md` and release version v0.1.0
  - [ ] Close https://github.com/LindenRegex/Warblre/issues/14

== Needs a small amount of work to finish

- [ ] #link("https://github.com/LindenRegex/Linden/tree/mw/memobt-acc")[Prefix accelerated MemoBT] -- Performing prefix acceleration multiple times in the MemoBT regex engine. The proof of correctness is complete and the meta engine is updated to use this new version. `memobt_match_unanchored` in `FunctionalMemoBT.v` is the new unanchored search definition (with cache sharing) and `memobt_match_correct_unanchored` is the proof of its correctness (no admits).
  - [ ] The `matchres_unanchored` definition is a duplicate of `matchres`. It can be removed.
  - [ ] The proof of termination is admitted, namely `memobt_match_terminates_unanchored'`. By termination we mean that the fuel will be enough. The unanchored matching itself is not fuel based, its termination is proven on the fact that the input is decreasing on every recursive call. But between those recursive calls we call the anchored search function which is fuel based. We have a proof that the fuel we provide for the anchored search is sufficient, but the issue stems from the cache we share between each call.

    The unanchored search works the following way:

    1. We use prefix acceleration to find a point where we want to perform a search
    2. In that position we run the anchored MemoBT. If it found a match, great! Otherwise we retrieve the output memoset.
    3. We advance the input by one and once again use prefix acceleration to find the next position to run an anchored search, this time with the memoset we got from the previous run.

    The fuel for the anchored search comes from the proof of complexity of the MemoBT. We then use the complexity bound as the fuel. However, the theorem about fuel sufficiency has a precondition that the provided memoset is valid (with some WF definition of "valid"). When just doing an anchored search, we provide an empty memoset for which we can easily then show that it is valid. On the other hand, for the unanchored search we *share* the memoset that was produced from the previous run of an anchored search. So to prove termination we must prove that the memoset remains valid between runs. That is what was left admitted. Unclear if with the current setup this validity preservation is provable or requires changing the theorem statements in the complexity proofs.
- [ ] Release Linden to Rocq's opam repository. To do this we should follow how it was done with Warblre. If the GitHub actions work, do that. Otherwise we do the manual release process. The docs should be similarly pushed to Linden.

== Self-contained bigger tasks

- [ ] Refactor oracle proof -- Currently to prove the correctness of the PikeVM with oracles the bulk of the proof is in `PikeEquiv.v`. That is because the PikeTree has no concept of oracles but simply traverses the tree looking for match leaves. This makes the proof of PikeTree correctness trivial. One issue encountered here is that `OracleQuery i` instructions which were added to the instruction set of NFAs breaks tree unicity. Namely, before having two identical instructions (and some other conditions) meant that they were identified with the same tree. This is not true; the following two regexes despite having very different trees would both be represented with the `OracleQuery 0` instruction: ```re /(?=abc)/``` and ```re /(?<!xyz)/```. As a fix the `OracleQuery` instruction actually also stores the kind of lookaround it represents and the inside regex. So for the previous regex examples the instructions for them are actually `OracleQuery 0 LookAhead /abc/` and `OracleQuery 0 NegLookBehind /xyz/`. This extra information is only used for the unicity property needed for proofs.

  An alternative oracle proof approach would be to add oracles on the level of PikeTree. It would put less burden on `PikeEquiv.v`. This already takes care of a lot of other things. This change would move the work to `PikeTree.v` but not make it harder (nor easier). This does not solve the unicity problem. For that, we could weaken the property to some notion of tree equivalence rather than full propositional equality which the unicity theorem currently states.

  For the unicity we considered modifying the `tree` type to allow for oracles. We don't believe this is a good approach as-is: `tree` touches way too many things in the codebase to be modified. It is a fundamental type of the semantics.
- [ ] #link("https://github.com/LindenRegex/Linden/blob/527e84b8fa318670dd559abfc72f4f0ae185f6e2/Engine/PikeTree.v#L724")[Preservation of `All` leaves in PikeTree] -- We have extended the PikeVM the allow for the collection of all leaves (modulo group map) rather than just the highest priority one. As always, to prove this correct we do the same to the PikeTree. The equivalence of results between PikeVM and PikeTree is already proven in `PikeEquiv.v`. Now, to prove that the PikeVM returns what the tree semantics describe, we need to show that the PikeTree collects all leaves. Our definition of "all leaves" is the list extensionality of leaves mapped to inputs:

  ```rocq forall inp', In inp' (map get_inp (pike_tree_all_leaves r inp)) <-> In inp' (map get_inp (leaves (tree_of r inp)))```

  As usual, to show that the PikeTree indeed has a property, we do it by adding it to the invariant of the PikeTree execution. Then, we show that at the initial state this invariant holds (already proven) and that when the invariant holds and the PikeTree takes a step the invariant still holds in the new state (this is what was left admitted).

  As far as I see, completing this should not pose a large challenge. The first 5 admits from that theorem should be resolved with the same lemma and the last one talks about actually finding a match and appending it to the list of leaves.
- [ ] Tree and regex reversal -- The current proof of correctness of oracle creation relies on two admitted theorems. They talk about the relation between forward and backward trees (trees constructed with the forward and backward direction respectively), and the relation between trees on a regex and a tree on the reverse of that regex.

  The forward/backward tree relation is needed because lookbehinds in the base semantics are defined in terms of the backward direction of trees yet when we collect all the leaves needed for the oracle, we do it in a forward direction. The admitted theorem is:

  ```rocq
  Lemma tree_leaf_dir_reverse_regex:
    forall r dir inp1 inp2 gm2 t1 t2,
      has_backreferences r = false ->
      is_tree rer [Areg r] inp1 GroupMap.empty dir t1 ->
      is_tree rer [Areg r] inp2 GroupMap.empty (direction_reverse dir) t2 ->
      In (inp2, gm2) (tree_leaves t1 GroupMap.empty inp1 dir) ->
      exists gm1, In (inp1, gm1) (tree_leaves t2 GroupMap.empty inp2 (direction_reverse dir)).
  ```

  We exclude backreferences since for them this does not hold (consider the regex ```re /(a)\1/```, in the backward direction ```re \1``` is evaluated first and is undefined). All the definitions can be found in the `Semantics/Reverse.v` file.

  On the other hand, the regex reversal relation has to be established because when collecting all leaves for the oracle, we store positions where the matches end. But what we need is the position where the matches start. The admitted theorem is:

  ```rocq
  Theorem tree_leaf_regex_reverse :
    forall r inp1 inp2 gm2 t1 t2 dir,
      has_backreferences r = false ->
      is_tree rer [Areg r] inp1 GroupMap.empty dir t1 ->
      is_tree rer [Areg (regex_reverse r)] (input_reverse inp2) GroupMap.empty dir t2 ->
      In (inp2, gm2) (tree_leaves t1 GroupMap.empty inp1 dir) ->
      exists gm1, In (input_reverse inp1, gm1) (tree_leaves t2 GroupMap.empty (input_reverse inp2) dir).
  ```

  We believe that this theorem will be a corollary of the direction reverse theorem once combined with a lemma relating regex reversal and direction reversal (which is a much simpler to prove).

  All progress can be found on the branch #link("https://github.com/LindenRegex/Linden/tree/mw/oracle-pikevm")[mv/oracle-pikevm].

  I will now document various paths that were taken to attempt to prove `tree_leaf_dir_reverse_regex`, their issues, and potential solutions.

  1. Proving it directly by induction on one of the `is_tree` hypothesis. We naturally must generalize the theorem to a list of actions (because of constructors such as `seq`). We quickly realize that stating the generalization is hard. What do we do about the list of actions? One might think we should reverse it: this would be wrong. Consider the list of actions being `[Areg /a/; Areg /b/]`. All good, theorem holds. But for `[Areg /ab/]`, theorem breaks! That action produces `[Areg /b/; Areg /a/]` for the backward direction which we then reverse due to our generalized theorem statement giving us `[Areg /a/; Areg /b/]`. Both `is_tree` talk about the same list of (atomic) actions, which makes it not provable.

    As an alternative, we could try to instead generalize to all actions that can be generated by a regex with respect to some direction. Then the theorem considers only well formed lists of actions. In Victor Deng's work on regex complexity he defined such a predicate (given a regex and direction, tell me all possible actions that can be generated from it).

    Before, I have also explored alternative semantics for `is_tree` called `atomic_is_tree` where instead of operating on `list action` it operates on `list atomic_actions`. If a rule of `is_tree` would produce multiple actions at once, `atomic_is_tree` would append these actions as an atomic unit. Then, when reversing the actions for the generalized theorem, we reverse only the top level list of atomic actions leaving the atomic groupings untouched. I proved that `atomic_is_tree` produces the same tree as `is_tree`. Unfortunately, this did not work because we did not know what actions were in that atomic grouping together with the currently processed action. I imagine in the end we would need to similarly have some kind of well formedness on atomic actions.

  2. Denotational set semantics. We could have alternative semantics that would be denotational in terms of sets. This is a popular approach to defining regex semantics. Sometimes, it leads to easier proofs. For example, a similar theorem about the reversal of regexes is proven directly by induction on the regex: https://github.com/Agnishom/lregex/blob/ffff8240e1b46d635974a3c62c7856a19064920a/theories/Reverse.v. For Linden, having such alternative semantics which are proven to be equivalent to the `is_tree` semantics could be useful in the future as well. To prove the reversal theorem we would then jump between the denotational and `is_tree` semantics.

  3. Trees with continuations. In #link("https://github.com/LindenRegex/Linden/blob/mw/oracle-pikevm/Semantics/FlatMap.v")[FlatMap.v] we establish that we can continue matching by resuming from all `Match` leaves of a tree. We could extend the trees to incorporate this notion directly by making `Seq a b` nodes explicit in the tree by computing the tree for `a` and having `b` be a continuation from all `Match` leaves. This would induce some monadic structure on the trees potentially facilitating the proof by not having to consider a fully materialized tree at all times.

- [ ] Final algorithm -- Once the tree reversal theorems are done, we can define the final algorithm that does matching of captureless unrestricted lookarounds! Its correctness should be a direct consequence of all the theorems that have been set up. The main challenge here is that lookaround matching is done by handling one level of lookaround nesting at a time, which means the definition will be self-referential which might cause some termination annoyances.

  Since correctness of oracles is somewhat disconnected from the PikeVM, the final algorithm could be defined abstractly. Then, the PikeVM would just be a concrete instance. In the future if one would write, say, a MemoBT that collects all leaves and queries oracles, it too would fit the protocol.

- [ ] Capture reconstruction -- Implementing lookarounds in the PikeVM consists of three phases. 1. Constructing the oracles, 2. Running the PikeVM with oracles, 3. Reconstructing the capture groups in lookarounds. My work tackled the first and second phase. The third phase requires the PikeVM to track the input position where we last successfully queries to lookaround oracle. Then, we need to prove that from this position we can run the engine to extract the correct capture group values. I suspect this phase will be quite technical and will have to deal with the joining of group maps. I don't have much more insight, I have not even begun thinking about it.
- [ ] Bringing back the MemoBT -- For ease of development of the lookaround oracles, I removed all files referencing the MemoBT. This is because many parts (NFA, regex support predicate, proof pipeline) are shared between the MemoBT and the PikeVM. Since I was focusing on the PikeVM part, I did not want to bother fixing all definitions of the MemoBT. Things have now stabilized, so the MemoBT files should be restored. The commit removing all MemoBT things is: https://github.com/LindenRegex/Linden/commit/97b6cb72a8315a03ceb459cc8a7caad2bd3f1142

  I can immediately say that the main issue will be the `pike_regex` predicate (which will now say that the MemoBT accepts lookarounds) and the `OracleQuery` instruction in the NFA. For the regex predicate, I think there should be a separate `memobt_regex`. This will allow both regex engines to develop independently. We could define a helper module for defining regex predicates. For the new instruction, we could either add oracles to MemoBT (with no WF requirement on them, since they would never be called for now) or prove that we never run into this instruction during execution of the MemoBT.
- [ ] Prepare `Engine/` for the lazy-NFA -- New engine means more code sharing. It would be good to organize the `Engine/` directory in a way that is more principled.
- [ ] Multiple literals -- For prefix acceleration we extract a literal of the regex to then perform acceleration (skipping some input positions for which we know no match can exist). As a generalization, we can define the extraction to instead return a list of literals (disjunction over each). Then, restate the theorems in terms of a list of literals. Finally, the previous extraction should be an easy corollary of this more general extraction. The motivation is that we might want to have strategies that perform prefix acceleration based on multiple, not just one literal. This is especially useful for regexes such as ```re /alpaca|llama/``` where we can extract two literals "alpaca" and "llama", and then do a substring search for both. All progress can be found on #link("https://github.com/LindenRegex/Linden/tree/mw/multi-literals")[mw/multi-literals].

  Since now we are extracting multiple literals, we need to redefine what an "impossible" and "exact" regex means. If we return no literals (for example, an incorrect character range could generate no literals, like ```re /[c-a]/```) or all literals are `Impossible` then the regex is impossible (it can produce no matches). If we return at least one literal and for some `s` all literals are equal to `Exact s` then the regex is exact `s` (it can only produce matches `s`).

  To implement multiple literal extraction, I imagine we would define two model fixpoints that extract as many precise literals as possible. One from a character descriptor and the other from a regex. Then, we can define a typeclass which describes the class of prefix extractors. It essentially describes the class of all extractions that are potentially less precise than the model fixpoints. It would look something like this:

  ```rocq
  Class LiteralExtractor := {
    extract_cd : char_descr -> list literal;
    extract_regex : regex -> list literal;
    (* is_impossible is a predicate that describes the new definition of what an impossible list of literals is, as stated above *)
    (* extract_literals_* are the model fixpoints which are most general *)
    impossible_correct_cd :
      forall cd,
        is_impossible (extract_cd cd) ->
        is_impossible (extract_literals_cd cd);
    impossible_correct_regex:
      forall r,
        is_impossible (extract_regex r) ->
        is_impossible (extract_literals_regex r);
    (* is_exact anagously is the predicate for the exact case *)
    exact_correct_cd :
      forall cd s,
        is_exact (extract_cd cd) s ->
        is_exact (extract_literals_cd cd) s;
    exact_correct_regex :
      forall r s,
        is_exact (extract_regex r) s ->
        is_exact (extract_literals_regex r) s;
    (* for prefixes, we allow extractions to be less precise *)
    prefix_correct_cd :
      forall cd l,
        In l (extract_cd cd) ->
        exists l',
          In l' (extract_literals_cd cd) /\ starts_with (prefix l) (prefix l');
    prefix_correct_regex :
      forall r l,
        In l (extract_regex r) ->
        exists l',
          In l' (extract_literals_regex regex) /\ starts_with (prefix l) (prefix l');
  }
  ```

  Then, the impossible and exact theorem should be restated in terms of the new predicates and the new more general literal list extraction. As a corollary we should add that any instance of the `LiteralExtractor` typeclass gets the impossible/exact theorems, through the correctness axioms. As an alternative, we can only have the theorem parametrized by the typeclass and show that the general extraction also adheres to the typeclass (which is trivially true).

  The theorem about match prefixes must be restated too:


  ```rocq
  Theorem extract_literal_prefix:
    forall r tree inp,
      is_tree rer [Areg r] inp Groups.GroupMap.empty forward tree ->
      (exists result, first_leaf tree inp = Some result) ->
      exists l, In l (extract_literals_regex r) /\ starts_with (prefix l) (next_str inp).
  ```

  Now there must be at least one literal which described the prefix. This theorem implies the previous version when we extracted only a single literal: the existential `l` had only a single exhibition. The contrapositive now says that if none of the extracted prefixes are a prefix of the input, then there is no match.

- [ ] Multi-needle substring searches -- To take advantage of the multi literals, we can generalize the definition of substring searches to having multiple needles rather than just one. One should be careful with how this affects the complexity of algorithms using this multi-needle searching. Additionally, having multiple literals is not necessarily better, so a heuristic should be put in place to decide which literals are in practice useful.
