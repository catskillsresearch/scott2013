#!/usr/bin/env python3
"""Append Agda module index to arxiv.md → arxiv_with_code.md (build artifact)."""

from __future__ import annotations

from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GITHUB = "https://github.com/catskillsresearch/scott2013"

FILES = [
    "src/Scott2013.agda",
    "src/Scott2013/GraphModel/Basic.agda",
]

FILE_ROLES: dict[str, str] = {
    "src/Scott2013.agda": "Root import graph",
    "src/Scott2013/GraphModel/Basic.agda": "Scott pairing and graph-model encodings",
}


def github_blob(rel: str) -> str:
    return f"{GITHUB}/blob/main/{rel}"


def paper_title(arxiv_text: str) -> str:
    first = arxiv_text.splitlines()[0] if arxiv_text else "# Scott 2013"
    if first.startswith("# "):
        return first[2:].strip()
    return first.strip()


def narrative_body(arxiv_text: str) -> str:
    body = arxiv_text
    if body.startswith("# "):
        idx = body.find("\n---\n")
        if idx != -1:
            body = body[idx + len("\n---\n") :]
        else:
            body = body[body.find("\n") + 1 :]
    return body.rstrip()


def main() -> None:
    arxiv_path = ROOT / "arxiv.md"
    arxiv = arxiv_path.read_text(encoding="utf-8")
    title = paper_title(arxiv)
    body = narrative_body(arxiv)

    parts: list[str] = []
    parts.append(
        "<!-- AUTO-GENERATED: run scripts/generate_arxiv_with_code.sh to refresh -->\n"
        "<!-- AGENTS: do not read or grep this file. Use arxiv.md; see .cursorignore -->\n"
    )
    parts.append(f"# {title} — narrative + Agda module index\n\n")
    parts.append(
        "> **Generated artifact — not for agents.** Inventory and narrative live in "
        "[`arxiv.md`](arxiv.md). Regenerate with `scripts/generate_arxiv_with_code.sh`. "
        "This file is stale whenever it is older than `arxiv.md` or any listed `.agda` file.\n\n"
    )
    parts.append(
        f"*Generated {date.today().isoformat()} from `arxiv.md` and the module list "
        "in `scripts/generate_arxiv_with_code.py`.*\n\n"
    )
    parts.append(
        "**Review copy.** The narrative body matches [`arxiv.md`](arxiv.md) "
        "(excluding the title block through the first `---`). "
        "This file appends **Appendix A: Agda module index** with GitHub links "
        "to every library file (no inlined full source).\n\n"
    )
    parts.append("---\n\n")
    parts.append("## Document map\n\n")
    parts.append("| Part | Contents |\n")
    parts.append("| --- | --- |\n")
    parts.append("| **Narrative** | Full `arxiv.md` body with inline Agda gists |\n")
    parts.append("| **Appendix A** | Hyperlinked module index |\n\n")
    parts.append("---\n\n")
    parts.append("# Narrative (from arxiv.md)\n\n")
    parts.append(body)
    parts.append("\n\n---\n\n")
    parts.append("# Appendix A: Agda module index\n\n")
    parts.append(
        f"Checked by `bash scripts/build_agda.sh`. Complete sources: [{GITHUB}]({GITHUB}). "
        "Each subsection links to the corresponding file on GitHub.\n\n"
    )
    parts.append("| Role | File |\n")
    parts.append("| --- | --- |\n")
    for f in FILES:
        parts.append(f"| {FILE_ROLES[f]} | [`{f}`]({github_blob(f)}) |\n")
    parts.append(
        "\nPrimary source (PDF): [`sources/ScottPROGIC2013.pdf`]"
        f"({GITHUB}/blob/main/sources/ScottPROGIC2013.pdf) — Dana S. Scott, "
        "*Stochastic λ-calculi: An extended abstract* (J. Applied Logic 12, 2014; "
        "PROGIC 2013).\n\n"
    )

    total_lines = sum(len((ROOT / f).read_text().splitlines()) for f in FILES)
    parts.append(f"**Total:** {len(FILES)} modules, {total_lines} lines of Agda.\n\n")

    out = ROOT / "arxiv_with_code.md"
    out.write_text("".join(parts))
    print(f"wrote {out} ({total_lines} Agda lines indexed across {len(FILES)} files)")


if __name__ == "__main__":
    main()
