# Provenance

This repository is a standalone Agda formalization of Dana Scott's PROGIC
2013 extended abstract *Stochastic λ-calculi* (Journal of Applied Logic 12
(2014), 369–376). It is not a thin wrapper and not a reimplementation of an
independent formalization.

Dana S. Scott is a co-author with Lars Warren Ericson of the resulting
Carnegie Mellon University School of Computer Science technical report.
Ericson directed and reviewed the Agda development with AI-agent assistance.
Scott's coauthorship of the report is distinct from an independent external
audit of each Agda source file.

Sibling formalizations of related Scott papers:

- [`catskillsresearch/scott1964`](https://github.com/catskillsresearch/scott1964)
  — Measurement Structures and Linear Inequalities (1964)
- [`catskillsresearch/scott1972`](https://github.com/catskillsresearch/scott1972)
  — Continuous Lattices (LNM 274, 1972)
- [`catskillsresearch/scott1976`](https://github.com/catskillsresearch/scott1976)
  — Data Types as Lattices (PRG-5 / SIAM J. Comput. 5, 1976)
- [`catskillsresearch/scott1980`](https://github.com/catskillsresearch/scott1980)
  — PRG-19 neighborhood systems (1980/1981)
- [`catskillsresearch/scott1982`](https://github.com/catskillsresearch/scott1982)
  — Domains for denotational semantics / information systems (1982)
- [`catskillsresearch/scott2026`](https://github.com/catskillsresearch/scott2026)
  — Interpreting Lambda Calculus in Domain-Valued Random Variables (CSL 2026)

The 2013 abstract cites the 1976 graph model as [1] and later domain-theory
sources, but this repository imports none of the sibling libraries. The
report is being prepared as **CMU-CS-26-XXX** and will be cross-archived on
arXiv under cs.LO and math.LO.

The current library is bootstrap scaffolding: it proves Scott's pairing
function and `pair-ne-zero`. The numbered theorems of §§3–4 will be added
as the library grows.

The development lives in `src/Scott2013/`. There are no postulates. The
pairing module uses only `Agda.Builtin.Nat` and `Agda.Builtin.Equality`.
