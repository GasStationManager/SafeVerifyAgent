"""Stage 0/1a: read the obligations out of the artifact.

Extraction decides whether there is anything to audit, so it gets its own
module and its own warning.

**Use Lean's real frontend.** Two weaker options fail the same way and
fail silently:

- a *regex over lines* collapses dense proofs. On the pattern real proofs
  actually use — `have h : T := ?_;` chained on one line — it finds
  **zero** obligations, and a claim that extracts to nothing is a claim
  the audit cannot help with.
- a *bare parse loop* cannot see `open`, so scoped notation fails to
  parse, the tactic block vanishes from the syntax tree, and the file
  reads as a proof with no steps in it — with no error surfaced.

So the frontend is the real path (`lean/ExtractLemmas.lean`), the regex
is a clearly-labelled fallback, and `ExtractionResult.degraded` says
which one ran. An obligation nobody extracted is an obligation nobody
audits: "did not parse" and "has no steps" must never look alike to a
caller.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from dataclasses import dataclass, field
from typing import List, Optional, Sequence

from .checkers import _elan
from .verdict import WHOLE_CLAIM, Obligation

LEAN_EXTRACTOR = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "lean", "ExtractLemmas.lean")

# Measured trust-surface markers. Counted, never interpreted: they are
# facts about the source, and they never decide what gets audited.
TRUST_SURFACE = (
    "native_decide", "addDecl", "mkProj", "Expr.proj", "unsafe",
    "implemented_by", "macro_rules", "elab ", "Expr.hash", "approxDepth",
    "@[implemented_by]", "partial def",
)

_HAVE_RE = re.compile(r"^\s*(have|obtain|suffices)\s+([A-Za-z_][\w']*)\s*:")
_DECL_RE = re.compile(r"^\s*(theorem|lemma|example)\s+([A-Za-z_][\w'.]*)")
_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
_LINE_COMMENT = re.compile(r"--[^\n]*")


@dataclass
class ExtractionResult:
    obligations: List[Obligation] = field(default_factory=list)
    degraded: bool = False
    errors: int = 0
    note: str = ""

    def __iter__(self):
        return iter(self.obligations)

    def __len__(self) -> int:
        return len(self.obligations)


def strip_comments(src: str) -> str:
    """Comments are the author's prose. Every measurement in this module
    runs over the stripped source, so nothing an author writes in words
    can move a number (DESIGN.md §4.1)."""
    return _LINE_COMMENT.sub("", _BLOCK_COMMENT.sub("", src))


def scan_trust_surface(text: str) -> List[str]:
    stripped = strip_comments(text)
    return sorted({m for m in TRUST_SURFACE if m in stripped})


def lean_available() -> bool:
    return _elan("lean") is not None


def extract(path: str, project_dir: Optional[str] = None,
            timeout_s: int = 600) -> ExtractionResult:
    """Obligations from `path`, through the frontend where possible."""
    if lean_available() and os.path.exists(LEAN_EXTRACTOR):
        try:
            return _extract_via_frontend(path, project_dir, timeout_s)
        except (subprocess.SubprocessError, OSError, ValueError) as exc:
            return _extract_via_regex(
                path, note=f"frontend extraction failed ({exc}); "
                           "FELL BACK TO REGEX — see module docstring")
    return _extract_via_regex(
        path, note="no Lean toolchain; FELL BACK TO REGEX — dense proofs "
                   "will under-extract, possibly to zero")


def extract_obligations(path: str, **kw) -> List[Obligation]:
    """Convenience wrapper for drivers that only want the list."""
    return list(extract(path, **kw).obligations)


def _extract_via_frontend(path: str, project_dir: Optional[str],
                          timeout_s: int) -> ExtractionResult:
    lean = _elan("lean")
    cmd = [lean, "--run", LEAN_EXTRACTOR, os.path.abspath(path)]
    if project_dir:
        lake = _elan("lake")
        if lake:
            cmd = [lake, "env"] + cmd
    p = subprocess.run(cmd, capture_output=True, text=True,
                       timeout=timeout_s, cwd=project_dir or None)
    data = json.loads(p.stdout or "{}")
    src = _read(path)
    obligations = [
        Obligation(id=str(o["id"]), statement=str(o.get("statement", "")),
                   kind=str(o.get("kind", "have")),
                   depends_on=[str(d) for d in o.get("depends_on", [])],
                   used=bool(o.get("used", True)),
                   anomalies=[str(a) for a in o.get("anomalies", [])])
        for o in data.get("obligations", [])
    ]
    return ExtractionResult(
        obligations=_with_whole_claim(obligations, src),
        errors=int(data.get("errors", 0)),
        note=("frontend reported elaboration errors; extraction may be "
              "partial" if data.get("errors") else ""),
    )


def _extract_via_regex(path: str, note: str) -> ExtractionResult:
    """The fallback. Loud on purpose — see the module docstring."""
    src = _read(path)
    stripped = strip_comments(src)
    out: List[Obligation] = []
    for line in stripped.splitlines():
        m = _HAVE_RE.match(line) or _DECL_RE.match(line)
        if m:
            out.append(Obligation(id=m.group(2),
                                  statement=line.strip(), kind=m.group(1)))
    return ExtractionResult(obligations=_with_whole_claim(out, src),
                            degraded=True, note=note)


def _with_whole_claim(obligations: Sequence[Obligation],
                      src: str) -> List[Obligation]:
    """The claim as a whole is ALWAYS an obligation.

    A proof can be entirely honest about a specification that is itself
    wrong, and nothing in a per-step decomposition covers that. Both
    extraction paths must name this obligation identically — when two
    parsers disagreed on its name in the predecessor, a guard that looked
    it up by name was silently inert.
    """
    out = [ob for ob in obligations if not ob.is_whole_claim]
    out.append(Obligation(
        id=WHOLE_CLAIM,
        statement="the claim as a whole, including its definitions",
        kind="final", anomalies=scan_trust_surface(src)))
    return out


def _read(path: str) -> str:
    with open(path, encoding="utf-8") as f:
        return f.read()
