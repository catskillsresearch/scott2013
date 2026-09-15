# CMU School of Computer Science technical report

Publication checklist for *Formalization of Scott's Stochastic λ-Calculi in
Agda*.

## Report metadata

- **Series:** Carnegie Mellon University School of Computer Science Technical
  Report
- **Number:** `CMU-CS-26-XXX` (placeholder)
- **Date:** September 2026
- **Authors:** Lars Warren Ericson and Dana S. Scott
- **Institutional address:** School of Computer Science, Carnegie Mellon
  University, Pittsburgh, PA 15213
- **arXiv cross-archive:** `cs.LO` / `math.LO`

Lars Warren Ericson is an independent researcher, d/b/a Catskills Research
Company (`lars.ericson@catskillsresearch.com`). Dana S. Scott is affiliated with the
Computer Science Department, Carnegie Mellon University, Emeritus.

## Build

```bash
bash scripts/build_agda.sh
bash scripts/build_arxiv_pdf.sh
```

The build produces:

- `arxiv.pdf` — CMU-formatted report PDF;
- `arxiv.tex` — generated complete LaTeX source (gitignored);
- `agda-listings/` and `figures/` — generated report inputs (gitignored);
- `dist/arxiv_submit.zip` — pdfLaTeX-ready cross-archive bundle, including
  `cmu-titlepage2.sty`.

The title page uses the report-mode layout from CMU's
`cmu-titlepage2.sty`. The same generated document is intended for the CMU
series and arXiv cross-archive.

## Before public release

1. Replace every `CMU-CS-26-XXX` occurrence with the assigned CMU report
   number.
2. Replace the editorial placeholder in “Retrospective Remarks by Dana S.
   Scott” with Dana's approved text.
3. Confirm the author order, affiliations, September 2026 date, and
   correspondence email.
4. Run `bash scripts/build_agda.sh` and `bash scripts/build_arxiv_pdf.sh`.
5. Inspect the cover, abstract, numbered figures, List of Figures,
   acknowledgments, references, and Agda module appendix.
6. Upload `dist/arxiv_submit.zip` only after deleting prior arXiv submission
   files so the source set is replaced rather than merged.
