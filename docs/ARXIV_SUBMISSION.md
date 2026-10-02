# arXiv metadata

Copy-paste fields for the arXiv web form. Regenerate the PDF and zip with
`bash scripts/build_arxiv_pdf.sh` before uploading `dist/arxiv_submit.zip`.

## Title and author

**Title:** Formalization of Scott's Stochastic λ-Calculi in Agda

**Author:** Lars Warren Ericson. The author is grateful to Dana S. Scott
for passing on the paper.

## Abstract (plain text, under 1920 characters)

See the `## Abstract` section in `arxiv.md` (same text appears in the PDF
abstract).

## Categories

Use at submit time:

| Field | Use |
| --- | --- |
| **Primary** | `cs.LO` (Logic in Computer Science) |
| **Secondary / cross-list at submit** | `math.LO` (Logic) if the UI offers a Mathematics cross-list |

| System | Recommendation |
| --- | --- |
| **arXiv primary (submit)** | `cs.LO` |
| **arXiv secondary (submit, if offered)** | `math.LO` |

**MSC 2020** (semicolon-separated for arXiv): `03B40; 68Q87; 68V20`

- `03B40` — Combinatory logic and lambda calculus
- `68Q87` — Probability in computer science
- `68V20` — Formalization of mathematics (Agda / proof assistants)

**ACM 1998** (semicolon-separated): `F.4.1; F.3.2; I.2.3`

- `F.4.1` — Mathematical logic
- `F.3.2` — Semantics of programming languages
- `I.2.3` — Deduction and theorem proving

## Compiler

pdfLaTeX (`00README.json` sets `"compiler": "pdflatex"`).

## Repository

https://github.com/catskillsresearch/scott2013
