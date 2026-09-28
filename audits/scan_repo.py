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

**metaprogramming sites** (`--sites`, or always with `--md`) — every
`run_cmd`/`run_elab`/`run_meta`, `macro`, `macro_rules`, `elab`, `elab_rules`,
`syntax`/`declare_syntax_cat`, `notation` (and `infix`/`prefix`/`postfix`),
`set_option` (every one, including `set_option ... in` inside a proof),
`attribute [...]`, `#eval`, `initialize`, `simproc`, and every `def`/`abbrev`
carrying an implicit-use attribute (`@[simp]`, `@[instance]`, `@[reducible]`,
...) -- LISTED, one `file:line` plus the first three lines of the statement,
never just counted. A count says "28 run_cmd"; an auditor needs to know that
27 of them are `#print axioms`-style checks and which one is not. On NSE this
path had nothing to list; differential-geometry has 28 `run_cmd` sites.

    python3 audits/scan_repo.py ROOT [--sites] [--md SCAN.md]

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

from safeverifyagent.extract import TRUST_SURFACE, blank_comments, strip_comments   # noqa: E402

MANIFEST = ("sorry", "admit", "sorryAx")
SKIP_DIRS = (".lake", ".git", "build", ".venv")


def lean_files(root):
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in files:
            if f.endswith(".lean"):
                yield os.path.join(base, f)


# (category, regex over COMMENT-BLANKED source, anchored at a line start after
# indentation and the modifiers a command may carry)
_MOD = r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:local|scoped|private|protected|public|meta)[ \t]+)*"
SITE_KINDS = (
    ("run_cmd", re.compile(_MOD + r"(?:run_cmd|run_elab|run_meta)\b", re.M)),
    ("macro", re.compile(_MOD + r"macro\b", re.M)),
    ("macro_rules", re.compile(_MOD + r"macro_rules\b", re.M)),
    ("elab", re.compile(_MOD + r"(?:elab|elab_rules)\b", re.M)),
    ("syntax", re.compile(_MOD + r"(?:syntax|declare_syntax_cat)\b", re.M)),
    ("notation", re.compile(_MOD + r"(?:notation|infix|infixl|infixr|prefix|postfix)\b", re.M)),
    ("set_option", re.compile(r"\bset_option\b", re.M)),
    ("attribute", re.compile(_MOD + r"attribute[ \t]*\[", re.M)),
    ("#eval", re.compile(r"^[ \t]*#eval\b", re.M)),
    ("initialize", re.compile(_MOD + r"(?:initialize|builtin_initialize)\b", re.M)),
    ("simproc", re.compile(_MOD + r"(?:simproc|dsimproc|simproc_decl)\b", re.M)),
    ("implicit-use def", re.compile(
        r"^[ \t]*@\[(?P<attrs>[^\]]*\b(?:simp|instance|reducible|irreducible|csimp|"
        r"implemented_by|extern|gcongr|positivity|aesop|norm_cast|ext|default_instance|"
        r"macro_inline|inline|match_pattern)\b[^\]]*)\]\s*"
        r"(?:(?:private|protected|noncomputable|public|partial|unsafe)\s+)*(?:def|abbrev)\b", re.M)),
)


def sites(root, files, progress=True, nlines=3):
    """{category: [(rel, line, first-N-lines)]}, over comment-blanked source."""
    out = collections.defaultdict(list)
    for i, path in enumerate(files):
        with open(path, encoding="utf-8", errors="replace") as fh:
            src = blank_comments(fh.read())
        rel = os.path.relpath(path, root)
        lines = None
        for cat, rx in SITE_KINDS:
            for m in rx.finditer(src):
                if lines is None:
                    lines = src.split("\n")
                ln = src.count("\n", 0, m.start()) + 1
                block = [l.rstrip() for l in lines[ln - 1:ln - 1 + nlines]]
                # `open Lean in` / `set_option .. in` on the line above is part of
                # the statement: it decides what the command can see
                if ln >= 2 and re.match(r"^(?:open|set_option)\b.*\bin\s*$", lines[ln - 2]):
                    block = [lines[ln - 2].rstrip()] + block[:max(nlines - 1, 1)]
                out[cat].append((rel, ln, block))
        if progress and (i + 1) % 2000 == 0:
            print(f"[scan] sites: {i + 1:,}/{len(files):,} files", file=sys.stderr, flush=True)
    return out


def option_name(block):
    m = re.search(r"set_option\s+([\w.]+)(?:\s+(\S+))?", "\n".join(block))
    return (m.group(1) + (" " + m.group(2) if m.group(2) and m.group(2) != "in" else "")) if m else "?"


def render_sites(found):
    L = ["## Metaprogramming sites", "",
         "Every site, not a count: `file:line` and the first lines of the "
         "comment-stripped statement, for an auditor to classify.", "",
         "| category | sites | files |", "|---|---|---|"]
    for cat, _rx in SITE_KINDS:
        v = found.get(cat, [])
        L.append(f"| {cat} | {len(v):,} | {len({r for r, _l, _b in v}):,} |")
    so = found.get("set_option", [])
    if so:
        L += ["", "### set_option, by option and value", "", "| option | sites |", "|---|---|"]
        for k, n in collections.Counter(option_name(b) for _r, _l, b in so).most_common():
            L.append(f"| `{k}` | {n:,} |")
    for cat, _rx in SITE_KINDS:
        v = found.get(cat, [])
        L += ["", f"### {cat} ({len(v):,})", ""]
        if not v:
            L.append("none")
            continue
        for rel, ln, block in v:
            L.append(f"- `{rel}:{ln}`")
            L.append("  ```lean")
            L += ["  " + b for b in block]
            L.append("  ```")
    return L


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(prog="scan_repo.py")
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--sites", action="store_true",
                    help="list every metaprogramming site on stdout")
    ap.add_argument("--md", default=None, help="write the full report (with sites) here")
    ap.add_argument("--lines", type=int, default=3, help="statement lines shown per site")
    args = ap.parse_args(argv)
    root = args.root
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

    out = [f"{len(files)} Lean file(s), {lines:,} lines", "",
           "=== MANIFEST (holes / declared axioms) ==="]
    if not manifest:
        out.append("  NONE — no sorry, no admit, no `axiom` declaration")
    for k, v in manifest.items():
        out.append(f"  {k}: {v}  e.g. {sorted(mwhere[k])[:3]}")
    out += ["", "=== TRUST SURFACE (comment-stripped) ==="]
    if not trust:
        out.append("  NONE of the scanned markers")
    for k, v in trust.most_common():
        out.append(f"  {k:18} {v:5}  in {len(where[k])} file(s): {sorted(where[k])[:3]}")
    found = sites(root, files, nlines=args.lines) if (args.sites or args.md) else None
    if found is not None:
        out += ["", "=== METAPROGRAMMING SITES (comment-blanked; listed in full with --sites/--md) ==="]
        for cat, _rx in SITE_KINDS:
            v = found.get(cat, [])
            out.append(f"  {cat:18} {len(v):6,} site(s) in {len({r for r, _l, _b in v}):,} file(s)")
    tail = ["", "Neither scan sees specification drift. A clean report here is a "
            "beginning, not a verdict."]
    print("\n".join(out + tail))
    if args.sites:
        print("\n".join([""] + render_sites(found)))
    if args.md:
        md = [f"# Mechanical scan of `{os.path.abspath(root)}`", "",
              "Generated by `audits/scan_repo.py --md`. Manifest and trust surface over "
              "comment-stripped source; sites over comment-blanked source (line numbers "
              "kept).", "", "```"] + out + ["```", ""] + render_sites(found)
        with open(args.md, "w", encoding="utf-8") as fh:
            fh.write("\n".join(md + tail) + "\n")
        print(f"wrote {args.md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
