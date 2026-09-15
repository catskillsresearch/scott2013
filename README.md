[![Agda](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott2013/build.yml?label=Agda)](https://github.com/catskillsresearch/scott2013/actions/workflows/build.yml)

# scott2013

Agda formalization of Dana Scott's **2013** *Stochastic λ-Calculi: An
Extended Abstract* (PROGIC 2013; J. Applied Logic 12 (2014), 369–376).

The accompanying report, *Formalization of Scott's Stochastic λ-Calculi in
Agda*, is by **Lars Warren Ericson** (independent researcher, d/b/a
Catskills Research Company) and **Dana S. Scott** (Computer Science
Department, Carnegie Mellon University, Emeritus). It is being prepared for
the Carnegie Mellon University School of Computer Science Technical Report
series as **CMU-CS-26-XXX**, with cross-archival to arXiv under cs.LO and
math.LO.

Scott expands the graph model of untyped λ-calculus — enumeration operators
on `P(ℕ)` — so that random combinators and random variables interpret
stochastic algorithms. The abstract records continuity of application
(Theorem 3.1), the largest-graph representation of continuous maps
(Theorem 3.2), λ-abstraction (Definition 3.3 and Theorems 3.4–3.8),
arithmetic combinators and a universal RE operator, the embedding of
countably based `T₀`-spaces into `P(ℕ)` (Theorems 3.10–3.12), and
random-variable application with probabilistic regular languages
(Theorems 4.2, 4.4, 4.5).

Standalone package — no dependency on the 1972/1976/1982/2026
formalizations. There is no Palomar packaging for this repository.

The development is checked with Agda `--safe` (locally Agda 2.6.3).

Original Agda and author-written docs are Apache-2.0. Scott's source PDF
`sources/ScottPROGIC2013.pdf` is **not** under that license; see `NOTICE`
and `sources/README.md`.

## Status

The library is a `--safe --without-K` development of the 2013 abstract:
Scott pairing and the graph model on `𝒫ℕ`, Theorems 3.1–3.8, the
arithmetic combinators and semantic RE interpreter (Definition 3.9),
the sequentializer (Definition 4.3), regular and probabilistic language
formers (Theorems 4.4–4.5), the `T₀` embedding and injectivity of
`𝒫ℕ` (Theorems 3.10–3.12), and random variables on Cantor space with
cylinder measure (Definition 4.1, Theorem 4.2, §5 coins). There are no
postulates. See `arxiv.md` §3.4 for the theorem inventory.

## Report and archival files

| File | Role |
|---|---|
| `arxiv.md` | CMU technical-report narrative and theorem inventory |
| `arxiv.pdf` | Built CMU report PDF for cross-archival |
| `docs/CMU_TECH_REPORT.md` | Report-number, build, and release checklist |
| `docs/ARXIV_SUBMISSION.md` | arXiv cross-archive metadata |
| `sources/ScottPROGIC2013.pdf` | Primary source PDF (Scott PROGIC 2013 / JAL 2014) |
| `src/Scott2013/` | Agda development |
| `PROVENANCE.md` | Relation to sibling Scott formalizations |

## Build

```bash
bash scripts/build_agda.sh
```

`scripts/build_agda.sh` typechecks `src/Scott2013.agda` and its imports
with `agda --safe`.

Rebuild the report PDF and arXiv zip:

```bash
bash scripts/build_arxiv_pdf.sh
```

## Source transcription

The PROGIC PDF is born-digital. The working copy is
`sources/ScottPROGIC2013.md` (text-layer extract, not vision OCR). See
`sources/README.md`.
