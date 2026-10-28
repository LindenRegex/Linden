Linden: A Linear Dependable Engine for JavaScript Regular Expressions
=====================================================================

[Project Page](https://aurele-barriere.github.io/linden.html)

# Related Publication

**POPL2026** [Formal Verification for JavaScript Regular Expressions: A Proven Mechanized Semantics and Its Applications](https://dl.acm.org/doi/10.1145/3776710)

[Extended Version](https://arxiv.org/abs/2507.13091). Appendix A of the extended version provides a correspondence between paper definitions and the code.

Authors: [Aurèle Barrière](https://aurele-barriere.github.io/), [Victor Deng](https://victor-deng.fr/) and [Clément Pit-Claudel](https://pit-claudel.fr/clement/).

![Linden](etc/linden.png)

# About

This repository contains mechanized proofs, in Rocq, about JavaScript Regular Expressions.
This includes:
- a new *backtracking tree* semantics for JavaScript regexes, in folder `Semantics`.
- a proof that this semantics is equivalent to the [Warblre](https://github.com/epfl-systemf/Warblre) mechanization of JavaScript regexes, in folder `WarblreEquiv`.
- a proof of the PikeVM linear-time matching algorithm supporting a subset of JavaScript regexes, in folder `Engine`. The algorithm is adapted to fit JavaScript unique quantifier semantics, following section 4.1 of [Linear Matching of JavaScript Regular Expressions](https://dl.acm.org/doi/10.1145/3656431).
- proof of JavaScript regex *contextual equivalences*, in folder `Rewriting`.

# Usage

1. Create a local [opam](https://opam.ocaml.org/) switch:

   ```
   opam switch --no-install create .
   ```

2. Add needed dependency repositories:

   ```
   opam repo add rocq-released https://rocq-prover.org/opam/released
   ```

3. Install dependencies:

   ```
   opam install --deps-only .
   ```

4. Build all proofs with `dune build`.

## Branch instructions (development branch)

`NFA.compile rer branches` takes a flag. When `branches` is true, a disjunction
whose two alternatives must start with distinct characters (compared after
canonicalization) compiles to `Branch` instead of `Fork`: `Branch` peeks at the
current input without consuming it and continues on the only alternative that
can match; a mismatch, including end of input, selects the second one. The lead
analysis follows groups and the left side of a sequence, and conservatively
declines other forms. Likewise, a `?` or `*` loop whose body must start with a
known character compiles to `LoopBranch` (or `LoopBranchLazy`), which enters the body only when that
character can be read and always keeps the exit thread. When `branches` is
false, the bytecode is unchanged.

The PikeVM theorems hold for both settings. In the PikeTree semantics a step may
drop new trees that have no result (`keeps`), and `PikeEquiv.lead_dead` shows
that the thread a `Branch` or `LoopBranch` discards is such a tree. The MemoBT engine is
used with `branches` false.
