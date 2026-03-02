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

2. Pin the version of Warblre:

   ```
   opam pin add --no-action warblre.0.1.0 https://github.com/epfl-systemf/Warblre.git#1657babedb991424e225d689c3ee8b0e151e9f5d
   ```

3. Install dependencies:

   ```
   opam install --deps-only .
   ```

4. Build all proofs with `dune build`.
