Equivalence between Warblre and Linden semantics
================================================

This part of the repository proves the equivalence between [the Warblre semantics](https://github.com/epfl-systemf/Warblre) and the semantics of this repository.

The proof is done as follows:
- We define a syntactic equivalence relation between Warblre and Linden regexes ([RegexpTranslation.v](RegexpTranslation.v)).
- We define equivalence relations between: Warblre `MatcherContinuation`s and lists of Linden actions; Warblre `Matcher`s and Linden regexes. ([EquivDef.v](EquivDef.v))
- We then prove that each Warblre `Matcher` that results from compiling some Warblre regex is equivalent to the syntactically equivalent Linden regex ([Equiv.v](Equiv.v)).

# Development structure

The development is organized as follows:

## Theorem files

- Equiv.v: core equivalence theorems
- EquivDef.v: definition of the equivalence relations between Warblre `MatcherContinuation`s and lists of Linden actions and between Warblre `Matcher`s and Linden regexes, and definition of equivalence between Linden and Warblre results
- EquivMain.v: end-to-end theorems stating that the result of Warblre's matching functions is equivalent to / can be reconstructed from the first branch of the corresponding Linden backtracking trees
- EquivLemmas.v: lemmas used while proving equivalence between Linden and Warblre

## Other important files

- GroupMapMS.v: definition of equivalence of Warblre `MatchState`s with Linden group maps
- RegexpTranslation.v: definition of syntactic equivalence between Warblre and Linden regexes, and translation from Warblre to Linden regexes
- ResultTranslation.v: translation from Linden results to Warblre results


## Auxiliary files

- CharDescrCharSet.v: equivalence between character descriptors and CharSets
- LWParameters.v: we instantiate the Warblre typeclasses (https://github.com/epfl-systemf/Warblre/blob/main/mechanization/spec/Parameters.v ) to be able to use the character axiomatization of Linden in Warblre.
- ListLemmas.v, WarblreLemmas.v: lemmas used in proofs
- LKFactorization.v: factorization of lookaround cases of regexp compilation in Warblre
- MSInput.v: linking Warblre MatchStates and Linden inputs
- NumericLemmas.v: lemmas about `non_neg_integer_or_inf` (NoI)
- Tactics.v: custom tactics used in the proofs
- Utils.v: utility lemmas (currently only boolean version of belonging to a list)

