#!/usr/bin/env python3
"""Highlight paper listings from complete Agda modules.

`agda --latex` is run on each library file (as a literate wrapper, because
plain `.agda` is copied unhighlighted). The paper gist is then cut out of
that highlighted module, line by line, so colours come from the real unit
rather than from a postulated fragment.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC_ROOT = ROOT / "src"
HL_ROOT = ROOT / "build" / "agda-hl"

WRAPPER_HEAD = (
    "\\documentclass{article}\n"
    "\\usepackage{agda}\n"
    "\\begin{document}\n"
    "\\begin{code}\n"
)
WRAPPER_TAIL = "\\end{code}\n\\end{document}\n"

# How many source tokens may sit between two gist tokens (elided annotations).
TOKEN_GAP = 30

_SOURCES: dict[Path, list[str]] | None = None
_CHUNKS: dict[Path, list[str] | None] = {}
_MIRROR: Path | None = None


def _sources() -> dict[Path, list[str]]:
    global _SOURCES
    if _SOURCES is None:
        _SOURCES = {
            p: p.read_text(encoding="utf-8").splitlines()
            for p in sorted(SRC_ROOT.rglob("*.agda"))
        }
    return _SOURCES


def _tokens(line: str) -> list[str]:
    return [t.strip("(){}[]") for t in re.findall(r"\S+", line) if t.strip("(){}[]")]


def _same(a: str, b: str) -> bool:
    if a == b:
        return True
    a_suf = a.rsplit(".", 1)[-1]
    b_suf = b.rsplit(".", 1)[-1]
    return bool(a_suf) and a_suf == b_suf


def _stream(lines: list[str]) -> list[tuple[int, str]]:
    out: list[tuple[int, str]] = []
    for i, line in enumerate(lines):
        raw = line.strip()
        if not raw or raw.startswith("--"):
            continue
        for tok in _tokens(line):
            out.append((i, tok))
    return out


def _find_span(
    gt: list[str],
    stream: list[tuple[int, str]],
    prefer: int | None = None,
) -> tuple[list[int], int] | None:
    """Tight source span whose tokens cover `gt` in order, skipping elided tokens.

    A continuation of the previous excerpt line wins over an earlier copy of
    the same tokens. Otherwise the earliest tight span wins, so a declaration
    is preferred to a later use.
    """
    if not gt:
        return None
    cands: list[tuple[list[int], int, int]] = []
    for i, (ln, tok) in enumerate(stream):
        if not _same(tok, gt[0]):
            continue
        j = 1
        k = i
        lines = {ln}
        skipped = 0
        ok = True
        while j < len(gt):
            found = None
            gap = 0
            for t in range(k + 1, min(k + 1 + TOKEN_GAP, len(stream))):
                if _same(stream[t][1], gt[j]):
                    found = t
                    break
                gap += 1
            if found is None:
                ok = False
                break
            for t in range(k + 1, found + 1):
                lines.add(stream[t][0])
            skipped += gap
            k = found
            j += 1
        if not ok:
            continue
        ordered = sorted(lines)
        span = ordered[-1] - ordered[0]
        if span > 6:
            continue
        cands.append((ordered, skipped, span))
    if not cands:
        return None
    pool = cands
    if prefer is not None:
        near = [c for c in cands if 0 <= c[0][0] - prefer <= 4]
        if near:
            pool = near
    lines, skipped, _span = min(pool, key=lambda c: (c[2], c[1], c[0][0]))
    return lines, skipped


def _name_line(lines: list[str], gt: list[str], prefer: int | None) -> int | None:
    """Best source line that opens with the gist's first token."""
    best: tuple[tuple[int, int, int], int] | None = None
    for i, line in enumerate(lines):
        raw = line.strip()
        if not raw or raw.startswith("--"):
            continue
        toks = _tokens(line)
        if not toks or not _same(toks[0], gt[0]):
            continue
        shared = 0
        j = 0
        for tok in toks:
            if j < len(gt) and _same(tok, gt[j]):
                j += 1
                shared += 1
        dist = abs(i - prefer) if prefer is not None else i
        score = (shared, -dist, -i)
        if best is None or score > best[0]:
            best = (score, i)
    return None if best is None else best[1]


def _locate(code: str) -> list[tuple[Path, list[int]]] | None:
    """Map each gist line to source lines. None if any line cannot be found."""
    sources = _sources()
    streams = {p: _stream(lines) for p, lines in sources.items()}
    gist = [
        ln
        for ln in code.splitlines()
        if ln.strip() and not ln.strip().startswith("--")
    ]
    if not gist:
        return None

    # A line such as `field` occurs in many modules. Keep each gist with the
    # module that covers the most of its lines, and only leave that module when
    # a line is not in it.
    scores: dict[Path, int] = {p: 0 for p in sources}
    for line in gist:
        gt = _tokens(line)
        if not gt:
            continue
        for path, stream in streams.items():
            if _find_span(gt, stream) is not None:
                scores[path] += 1
    if not any(scores.values()):
        return None

    resolved: list[tuple[Path, list[int]]] = []
    prefer_file: Path | None = None
    prefer_line: int | None = None
    for line in gist:
        gt = _tokens(line)
        found: dict[Path, tuple[list[int], int]] = {}
        if gt:
            for path, stream in streams.items():
                pref = prefer_line if path == prefer_file else None
                hit = _find_span(gt, stream, pref)
                if hit is not None:
                    found[path] = hit
        if found:
            path = max(found, key=lambda p: (scores[p], -found[p][1], -len(found[p][0])))
            resolved.append((path, found[path][0]))
            prefer_file = path
            prefer_line = found[path][0][-1]
            continue
        gt = _tokens(line)
        if not gt:
            return None
        dominant = max(scores, key=lambda p: (scores[p], str(p)))
        pref = prefer_line if prefer_file == dominant else None
        idx = _name_line(sources[dominant], gt, pref)
        path = dominant
        if idx is None:
            for cand, lines in sources.items():
                idx = _name_line(lines, gt, None)
                if idx is not None:
                    path = cand
                    break
        if idx is None:
            return None
        resolved.append((path, [idx]))
        prefer_file = path
        prefer_line = idx
    return resolved


def _mirror() -> Path:
    global _MIRROR
    if _MIRROR is not None and (_MIRROR / "Scott2013.agda").is_symlink():
        return _MIRROR
    inc = HL_ROOT / "inc"
    if inc.exists():
        shutil.rmtree(inc)
    inc.mkdir(parents=True)
    subprocess.check_call(["cp", "-as", f"{SRC_ROOT}/.", str(inc)])
    _MIRROR = inc
    return inc


def _split_code(tex: str, n_src: int) -> list[str] | None:
    start = tex.find("\\begin{code}")
    end = tex.find("\\end{code}")
    if start < 0 or end < 0:
        return None
    body = tex[start:end].splitlines()[1:]
    chunks: list[str] = []
    i = 0
    while i < len(body):
        ln = body[i]
        if ln == "%" and i + 1 < len(body) and body[i + 1].startswith("\\\\[\\AgdaEmptyExtraSkip]"):
            chunks.append(ln + "\n" + body[i + 1])
            i += 2
            continue
        if ln == "%" and i + 1 < len(body) and body[i + 1].startswith("\\>"):
            i += 1
            ln = body[i]
        if ln.startswith("\\>"):
            chunk = [ln]
            i += 1
            while i < len(body) and body[i] != "\\\\":
                if (
                    body[i] == "%"
                    and i + 1 < len(body)
                    and body[i + 1].startswith("\\>")
                ):
                    i += 1
                    continue
                chunk.append(body[i])
                i += 1
            if i < len(body) and body[i] == "\\\\":
                chunk.append(body[i])
                i += 1
            chunks.append("\n".join(chunk))
            continue
        return None
    if len(chunks) != n_src:
        return None
    return chunks


def _highlight_module(path: Path) -> list[str] | None:
    if path in _CHUNKS:
        return _CHUNKS[path]
    if shutil.which("agda") is None:
        _CHUNKS[path] = None
        return None

    inc = _mirror()
    rel = path.relative_to(SRC_ROOT)
    link = inc / rel
    lagda = link.with_suffix(".lagda.tex")
    src = path.read_text(encoding="utf-8")
    if link.exists() or link.is_symlink():
        link.unlink()
    lagda.write_text(WRAPPER_HEAD + src + WRAPPER_TAIL, encoding="utf-8")
    out_dir = HL_ROOT / "out"
    out_dir.mkdir(parents=True, exist_ok=True)
    chunks: list[str] | None = None
    try:
        proc = subprocess.run(
            [
                "agda",
                "--safe",
                "--no-libraries",
                "--only-scope-checking",
                "--latex",
                f"--latex-dir={out_dir}",
                "-i",
                str(inc),
                str(lagda),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        produced = out_dir / rel.with_suffix(".tex")
        if proc.returncode != 0 or not produced.is_file():
            log = HL_ROOT / "logs" / (rel.as_posix().replace("/", "-") + ".log")
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text((proc.stdout or "") + "\n" + (proc.stderr or ""), encoding="utf-8")
            print(f"agda-hl: {rel} failed scope-check", file=sys.stderr)
        else:
            chunks = _split_code(produced.read_text(encoding="utf-8"), len(src.splitlines()))
            if chunks is None:
                print(f"agda-hl: {rel} LaTeX chunks did not match source lines", file=sys.stderr)
    finally:
        if lagda.exists():
            lagda.unlink()
        if not link.exists():
            link.symlink_to(path)

    _CHUNKS[path] = chunks
    return chunks


def _fragment(hits: list[tuple[Path, list[int]]]) -> str | None:
    modules: dict[Path, list[str]] = {}
    for path, _lines in hits:
        if path not in modules:
            chunks = _highlight_module(path)
            if chunks is None:
                return None
            modules[path] = chunks

    parts = ["\\begin{code}%"]
    seen: set[tuple[Path, int]] = set()
    prev: tuple[Path, int] | None = None
    for path, lines in hits:
        for n in lines:
            key = (path, n)
            if key in seen:
                continue
            seen.add(key)
            if prev is not None and not (prev[0] == path and n == prev[1] + 1):
                parts.append("%\n\\\\[\\AgdaEmptyExtraSkip]%")
            parts.append(modules[path][n])
            prev = key
    parts.append("\\end{code}")
    return "\n".join(parts) + "\n"


def highlight_agda_snippet(code: str, stem: str) -> Path | None:
    """Return a TeX fragment cut from the highlighted library module."""
    del stem  # listing name is only used by the caller for the output path
    hits = _locate(code)
    if not hits:
        return None
    body = _fragment(hits)
    if body is None or "\\AgdaKeyword" not in body and "\\AgdaFunction" not in body:
        return None
    return _write_frag(body)


def _write_frag(body: str) -> Path:
    frag_dir = HL_ROOT / "frags"
    frag_dir.mkdir(parents=True, exist_ok=True)
    # Caller copies this to the listings directory; a stable temp path is enough.
    dest = frag_dir / "snippet.tex"
    dest.write_text(body, encoding="utf-8")
    return dest


def highlight_to_listings_dir(code: str, listing_name: str, listings_dir: Path) -> Path | None:
    """Highlight and copy fragment next to the UTF-8 listing as `<stem>.tex`."""
    frag = highlight_agda_snippet(code, listing_name)
    if frag is None:
        print(f"agda-hl: {listing_name} uses listings fallback", file=sys.stderr)
        return None
    listings_dir.mkdir(parents=True, exist_ok=True)
    dest = listings_dir / (Path(listing_name).stem + ".tex")
    shutil.copy(frag, dest)
    return dest
