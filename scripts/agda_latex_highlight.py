#!/usr/bin/env python3
"""Highlight Agda listing snippets via `agda --latex` (literate wrappers).

Plain `.agda` is copied un-highlighted by this Agda build's LaTeX backend. Each
paper gist is wrapped as `.lagda.tex` and scope-checked with an iteratively
grown postulate prelude so abbreviated snippets still get agda.sty highlighting.
"""

from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AGDA_STY = ROOT / "agda.sty"
HL_ROOT = ROOT / "build" / "agda-hl"

NOT_IN_SCOPE = re.compile(r"Not in scope:\s*\n\s*([^\n]+?)\s*\n\s*at ", re.M)
MISSING_TYPE = re.compile(r"Missing type signature for left hand side ([^\n]+)", re.M)
DECLARED_NO_DEF = re.compile(
    r"The following names are declared but not accompanied by a\n"
    r"definition: ([^\n]+)",
    re.M,
)
MULTIPLE_DEF = re.compile(r"Multiple definitions of ([^\.\n]+)", re.M)


def _safe_modname(stem: str) -> str:
    h = hashlib.sha1(stem.encode()).hexdigest()[:8]
    body = re.sub(r"[^A-Za-z0-9]", "", Path(stem).stem) or "Snippet"
    if body[0].isdigit():
        body = "S" + body
    return f"HL{body}{h}"


def _fix_postulate_name(raw: str) -> str | None:
    name = raw.strip().split()[0] if raw.strip() else ""
    name = name.strip("`")
    if not name or name.startswith("Agda."):
        return None
    if name in {"Set", "Set₁", "Set₂", "Set₃", "Prop"}:
        return None
    return name


def missing_definitions(src: str) -> list[str]:
    typed: set[str] = set()
    defined: set[str] = set()
    for m in re.finditer(r"^([^\s:(){}]+)[ \t]*:", src, re.M):
        typed.add(m.group(1))
    for m in re.finditer(r"^([^\s:(){}]+)[ \t].*=", src, re.M):
        defined.add(m.group(1))
    for m in re.finditer(r"^([^\s:(){}]+)[ \t]*=", src, re.M):
        defined.add(m.group(1))
    skip = {
        "module",
        "open",
        "import",
        "mutual",
        "where",
        "field",
        "data",
        "record",
        "constructor",
        "postulate",
        "variable",
    }
    return sorted((typed - defined) - skip)


def _write_lagda(path: Path, mod: str, postulates: list[str], source: str, holes: str) -> None:
    post_block = ""
    if postulates:
        lines = []
        for n in postulates:
            # Operators need arrow types so infix uses parse; others can be Set₁.
            if "_" in n:
                slots = n.count("_")
                if slots >= 2:
                    lines.append(f"  {n} : Set₁ → Set₁ → Set₁")
                else:
                    lines.append(f"  {n} : Set₁ → Set₁")
            else:
                lines.append(f"  {n} : Set₁")
        post_block = "postulate\n" + "\n".join(lines) + "\n"
    # Do not textwrap/dedent the Agda source: indentation is meaningful.
    # Incomplete snippets need mutual so typed names can be closed by `= ?`
    # holes; those holes (and mutual) are stripped from the TeX fragment.
    if holes:
        visible = f"mutual\n{source}-- hl-holes\n{holes}"
    else:
        visible = source
    path.write_text(
        "\\documentclass{article}\n"
        "\\usepackage{agda}\n"
        "\\begin{document}\n"
        "\\begin{code}[hide]\n"
        "{-# OPTIONS --allow-unsolved-metas #-}\n"
        f"module {mod} where\n"
        "open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)\n"
        "open import Agda.Builtin.Equality using (_≡_; refl)\n"
        "open import Agda.Builtin.Bool using (Bool; true; false)\n"
        "open import Agda.Builtin.Unit using (⊤; tt)\n"
        f"{post_block}"
        "\\end{code}\n"
        "\\begin{code}\n"
        f"{visible}"
        "\\end{code}\n"
        "\\end{document}\n",
        encoding="utf-8",
    )


def highlight_agda_snippet(code: str, stem: str) -> Path | None:
    """Return path to a TeX fragment using agda.sty macros, or None on failure."""
    if not AGDA_STY.is_file() or shutil.which("agda") is None:
        return None

    source = code.rstrip("\n") + "\n"
    defined_here = set(re.findall(r"^([^\s:(){}]+)[ \t]*:", source, re.M))
    defined_here.update(re.findall(r"^([^\s:(){}]+)[ \t].*=", source, re.M))

    holes = "".join(f"{name} = ?\n" for name in missing_definitions(source))
    mod = _safe_modname(stem)
    work = HL_ROOT / mod
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True, exist_ok=True)
    shutil.copy(AGDA_STY, work / "agda.sty")

    lagda = work / f"{mod}.lagda.tex"
    postulates: list[str] = []
    seen: set[str] = set()
    last_err = ""

    for _ in range(40):
        _write_lagda(lagda, mod, postulates, source, holes)
        proc = subprocess.run(
            [
                "agda",
                "--no-libraries",
                "--only-scope-checking",
                "--latex",
                f"--latex-dir={work}",
                "-i",
                str(work),
                str(lagda),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        out = work / f"{mod}.tex"
        err = (proc.stdout or "") + "\n" + (proc.stderr or "")
        last_err = err
        if out.is_file() and "\\AgdaKeyword" in out.read_text(encoding="utf-8", errors="replace"):
            body = out.read_text(encoding="utf-8")
            body = re.sub(r"\\documentclass\{article\}\s*", "", body)
            body = re.sub(r"\\usepackage\{agda\}\s*", "", body)
            body = re.sub(r"\\begin\{document\}\s*", "", body)
            body = re.sub(r"\\end\{document\}\s*", "", body)
            # Drop prelude/postulates (hide) and keep only the paper listing block.
            body = re.sub(
                r"\\begin\{code\}\[hide\]%?\n.*?\\end\{code\}\n?",
                "",
                body,
                flags=re.S,
            )
            # Drop the mutual wrapper used only for scope-check.
            body = re.sub(
                r"^[^\n]*\\Agda(?:Deadcode\{\\AgdaKeyword\{mutual\}\}|Keyword\{mutual\})[^\n]*\n",
                "",
                body,
                flags=re.M,
            )
            # Drop `= ?` hole appendix (everything from the hl-holes marker).
            body = re.sub(
                r"^[^\n]*hl-holes[^\n]*\n.*?(?=\\end\{code\})",
                "",
                body,
                flags=re.S | re.M,
            )
            # mutual was the first line; drop the blank row it left behind.
            body = re.sub(r"(\\begin\{code\}%\n)\\\\\n", r"\1", body)
            frag = work / f"{mod}.frag.tex"
            frag.write_text(body.strip() + "\n", encoding="utf-8")
            return frag

        added = False
        for m in NOT_IN_SCOPE.finditer(err):
            name = _fix_postulate_name(m.group(1))
            if name and name not in seen and name not in defined_here:
                seen.add(name)
                postulates.append(name)
                added = True
        for m in MISSING_TYPE.finditer(err):
            name = _fix_postulate_name(m.group(1))
            if not name:
                continue
            if name in defined_here and f"{name} :" not in source and f"{name} : " not in source:
                source = f"{name} : Set₁\n" + source
                added = True
            elif name not in seen and name not in defined_here:
                seen.add(name)
                postulates.append(name)
                added = True
        for m in DECLARED_NO_DEF.finditer(err):
            for part in m.group(1).split(","):
                name = _fix_postulate_name(part)
                if name and f"{name} = ?" not in holes:
                    holes += f"{name} = ?\n"
                    added = True
        for m in MULTIPLE_DEF.finditer(err):
            name = _fix_postulate_name(m.group(1))
            if name and name in seen:
                postulates = [p for p in postulates if p != name]
                seen.discard(name)
                added = True
        # Parse failures often mean a used operator was postulated as a nullary Set₁.
        if (not added) and ("Could not parse" in err or "Parse error" in err):
            for m in re.finditer(r"Operators used in the grammar:\n((?:  .*\n)+)", err):
                for op in re.findall(r"\[(_[^\]\n]+_) ", m.group(1)):
                    if op not in seen and op not in defined_here:
                        seen.add(op)
                        postulates.append(op)
                        added = True
            # Bare operator tokens mentioned in "Problematic expression"
            for m in re.finditer(r"Not in scope:\s*\n\s*([^\n]*_[^\n]*)\s*\n", err):
                name = _fix_postulate_name(m.group(1))
                if name and name not in seen and name not in defined_here:
                    seen.add(name)
                    postulates.append(name)
                    added = True
        if not added:
            break

    (work / "agda-latex.log").write_text(last_err, encoding="utf-8")
    return None


def highlight_to_listings_dir(code: str, listing_name: str, listings_dir: Path) -> Path | None:
    """Highlight and copy fragment next to the UTF-8 listing as `<stem>.tex`."""
    frag = highlight_agda_snippet(code, listing_name)
    if frag is None:
        return None
    listings_dir.mkdir(parents=True, exist_ok=True)
    dest = listings_dir / (Path(listing_name).stem + ".tex")
    shutil.copy(frag, dest)
    return dest
