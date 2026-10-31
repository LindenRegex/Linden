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
whose two alternatives must start with disjoint descriptors compiles to `Branch`
instead of `Fork`. The compiler is parametric in any sound check of
disjointness (`NFA.Disjoint`), whose specification `NFA.cd_disjoint` states
that no character matches both descriptors; its default,
`NFA.practical_disjoint`, only handles cheap cases: the empty class, a
descriptor and its inversion, distinct characters and, without ignoreCase,
characters and ranges whose bounds do not overlap, `\d`, `\s` and `\w` against
characters, ranges and classes that share none of their characters, and a
class against its complement, through unions. `Branch` peeks at the
current input without consuming it and continues on the only alternative that
can match; a mismatch, including end of input, selects the second one. The lead
analysis follows groups and the left side of a sequence, leads a disjunction
whose alternatives both have a lead with their union, and conservatively
declines other forms. Likewise, a `?` or `*` loop whose body must start with a
known character compiles to `GuardFirst` (or `GuardFirstLazy`), which enters the body only when that
character can be read and always keeps the exit thread; a disjunction whose
first alternative must start with a known character does likewise. When what
follows a loop must start with a disjoint descriptor, the loop compiles to
`Branch`, whatever its body starts with, greedy or lazy alike, and keeps a
single thread: at most one of its two threads can survive, so their priority
does not matter. What follows a loop also sees through nullable regexes and
leads `$` with the line terminators, if any. A loop that cannot peek at its
body but must be followed by a known character compiles to `GuardSecond` (or
`GuardSecondLazy`), which keeps the body and spawns the exit only before that
character; a disjunction does the same on its second alternative. The tree
representation of the code leaves the order of a choice open, and the seen
sets of the tree semantics compare trees up to that order. When `branches` is
false, the compiler emits no peeking instruction.

The PikeVM theorems hold for both settings and for any sound check of
disjointness. In the PikeTree semantics a step may drop new trees that have no
result (`keeps`). `PikeEquiv.loop_fork_step` shows that a forking instruction
only drops threads that its peek declares dead, and `PikeEquiv.loop_peek_sound`
that the threads `NFA.loop_peek` declares dead have no result, by
`PikeEquiv.lead_dead` for a body or an alternative and by `PikeEquiv.leads_dead`
for what follows a loop. The MemoBT engine is used with `branches` false.
