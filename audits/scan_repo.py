"""The mechanical rung of an audit, over a whole repository.

Two scans, both over COMMENT-STRIPPED source, because a claimed proof's
comments were written by whoever submitted it: they are evidence about
the author, not about the proof.

    python3 audits/scan_repo.py /path/to/lean-project

**manifest** — `sorry`, `admit`, and `axiom` declarations. A claimed proof
with an undeclared hole is malformed, and that is a REJECT, not a
refutation: "you did not submit a proof" and "you submitted a proof and
it is wrong" are different findings that must not share a bucket.

**trust surface** — places the artifact reaches outside the ordinary
elaboration path (`native_decide`, `addDecl`, raw `Expr` construction or
projection, `macro`/`elab`, hash or depth comparisons standing in for
equality). These are MEASUREMENTS, not judgments. They refute nothing and
they do not decide what gets audited; they tell a reader where to look.

Neither scan can see specification drift — an honest proof of a wrong
definition has no hole and no trust surface. That is the coherence rung's
job, and it is why a clean report from this script is a beginning.
"""

from __future__ import annotations

import collections
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from safeverifyagent.extract import TRUST_SURFACE, strip_comments   # noqa: E402

MANIFEST = ("sorry", "admit", "sorryAx")
SKIP_DIRS = (".lake", ".git", "build", ".venv")


def lean_files(root):
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in files:
            if f.endswith(".lean"):
                yield os.path.join(base, f)


def main() -> int:
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    files = sorted(lean_files(root))
    trust = collections.Counter()
    where = collections.defaultdict(set)
    manifest = collections.Counter()
    mwhere = collections.defaultdict(set)
    lines = 0

    for path in files:
        with open(path, encoding="utf-8", errors="replace") as fh:
            src = fh.read()
        lines += src.count("\n")
        stripped = strip_comments(src)
        rel = os.path.relpath(path, root)
        for marker in TRUST_SURFACE:
            n = stripped.count(marker)
            if n:
                trust[marker] += n
                where[marker].add(rel)
        for marker in MANIFEST:
            n = len(re.findall(r"\b" + marker + r"\b", stripped))
            if n:
                manifest[marker] += n
                mwhere[marker].add(rel)
        for m in re.finditer(r"^\s*axiom\s+([\w.]+)", stripped, re.M):
            manifest["axiom-decl"] += 1
            mwhere["axiom-decl"].add(f"{rel}:{m.group(1)}")

    print(f"{len(files)} Lean file(s), {lines:,} lines\n")
    print("=== MANIFEST (holes / declared axioms) ===")
    if not manifest:
        print("  NONE — no sorry, no admit, no `axiom` declaration")
    for k, v in manifest.items():
        print(f"  {k}: {v}  e.g. {sorted(mwhere[k])[:3]}")
    print("\n=== TRUST SURFACE (comment-stripped) ===")
    if not trust:
        print("  NONE of the scanned markers")
    for k, v in trust.most_common():
        print(f"  {k:18} {v:5}  in {len(where[k])} file(s): {sorted(where[k])[:3]}")
    print("\nNeither scan sees specification drift. A clean report here is a "
          "beginning, not a verdict.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
