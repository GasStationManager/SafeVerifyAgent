"""The coverage ledger, in tiers, computed rather than typed.

The NSE final report stated coverage by hand, and the playbook's rule 13 is the
lesson it cost: TWO denominators, always (whole artifact versus cone), and
"named by some report" is not "read". A single percentage was quotable and
misleading. This script produces the tiered table from two inputs:

    python3 audits/ledger.py CONE.csv REPORTS_DIR [-o LEDGER.md] [--top 30]
        [--kinds theorem,lemma] [--glob '*.md'] [--no-modules]

CONE.csv is `audits/cone.py`'s output; REPORTS_DIR holds worker reports
(markdown, searched recursively).

TIERS, from loosest to tightest. Every count is of IN-CONE declarations of the
chosen kinds (theorems and lemmas by default), and every tier is a subset of
the one above it; the script checks that and says so if it fails.

  1. in cone              the denominator.
  2. in a NAMED file      the file is named by some report: a path ending in
                          `.lean` (with or without `:line`), matched on a path
                          COMPONENT boundary so `Solution.lean` does not match
                          inside `ComparatorSolution.lean`, or a dotted module
                          name that is exactly a module of the repo
                          (`--no-modules` turns that off). A LOOSE upper bound:
                          NSE measured a 138-theorem file counted as covered
                          because three reports cited one line of it. A bare
                          basename shared by several files counts for all of
                          them (it is an upper bound) and is reported.
  3. CITED at file:line   a `path:line` citation resolves to the declaration
                          containing that line. Tighter, still not "read".
  4. READ line by line    a report DECLARES it, one line per file:

                              READ-LINE-BY-LINE: path/to/File.lean
                              READ-LINE-BY-LINE: path/to/File.lean:120-340

                          at the start of a line (a list bullet and backticks
                          are allowed). The path follows the same resolution
                          as tier 2 but must name exactly ONE file; the optional
                          `:START-END` range restricts the claim to declarations
                          starting in it. Several paths on one line may be
                          separated by commas. An entry that does not resolve
                          is listed as an ERROR, never dropped: a claim of
                          reading that cannot be checked is itself a finding.
                          The convention is the report author's word; this
                          script only makes it countable. It is not evidence
                          that the reading happened -- the report is.

Then the never-named files (cone files with in-cone theorems that no report
names), largest first: the work queue.
"""

import argparse, collections, csv, fnmatch, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cone import FileIndex, load_cone_csv, truthy          # noqa: E402

PATH_CITE = re.compile(
    r"(?<![\w/.\-])((?:[\w.\-]+/)*[\w\-][\w.\-]*\.lean)\b"
    r"(?::(\d+(?:\s*[-–,]\s*\d+)*))?")
MODULE_TOK = re.compile(r"(?<![\w.])([A-Z][\w']*(?:\.[A-Z][\w']*)+)(?![\w.])")
READ_DECL = re.compile(r"^[ \t]*(?:[-*+][ \t]+)?`?READ-LINE-BY-LINE:[ \t]*(.+?)[ \t]*$", re.M)


def report_files(d, glob):
    out = []
    for base, _dirs, fns in os.walk(d):
        for fn in fns:
            if fnmatch.fnmatch(fn, glob):
                out.append(os.path.join(base, fn))
    return sorted(out)


def line_numbers(spec):
    """'533,435' / '454-470' -> [533, 435] / [454, 470]"""
    return [int(x) for x in re.findall(r"\d+", spec or "")]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="ledger.py")
    ap.add_argument("cone_csv")
    ap.add_argument("reports")
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--kinds", default="theorem,lemma")
    ap.add_argument("--glob", default="*.md")
    ap.add_argument("--top", type=int, default=30)
    ap.add_argument("--no-modules", action="store_true")
    args = ap.parse_args(argv)
    kinds = set(args.kinds.split(","))

    rows = load_cone_csv(args.cone_csv)
    byfile = collections.defaultdict(list)
    for r in rows:
        byfile[r["file"]].append(r)
    for v in byfile.values():
        v.sort(key=lambda r: r["line"])
    starts = {f: [r["line"] for r in v] for f, v in byfile.items()}
    idx = FileIndex(byfile)
    modules = {f[:-5].replace("/", "."): f for f in byfile}

    def counted(r):
        return truthy(r["in_cone"]) and r["kind"] in kinds

    incone = {f: [r for r in v if counted(r)] for f, v in byfile.items()}
    incone = {f: v for f, v in incone.items() if v}
    total = sum(len(v) for v in incone.values())

    reports = report_files(args.reports, args.glob)
    named = set()                 # files
    cited_decls = set()           # (file, line) of the containing declaration
    read_decls = set()
    read_files = set()
    ambiguous = collections.Counter()
    errors = []
    per_report = []

    import bisect

    def containing(f, ln):
        i = bisect.bisect_right(starts[f], ln) - 1
        return byfile[f][i] if i >= 0 else None

    for rp in reports:
        with open(rp, encoding="utf-8", errors="replace") as fh:
            txt = fh.read()
        rel_rp = os.path.relpath(rp, args.reports)
        mine, mine_read = set(), 0
        for m in PATH_CITE.finditer(txt):
            got = idx.resolve(m.group(1))
            if not got:
                continue
            if len(got) > 1:
                ambiguous[m.group(1)] += 1
            mine |= got
            if len(got) == 1 and m.group(2):
                f = next(iter(got))
                for ln in line_numbers(m.group(2)):
                    d = containing(f, ln)
                    if d is not None:
                        cited_decls.add((f, d["line"]))
        if not args.no_modules:
            for m in MODULE_TOK.finditer(txt):
                f = modules.get(m.group(1))
                if f:
                    mine.add(f)
        for m in READ_DECL.finditer(txt):
            for ent in re.split(r"\s*,\s*(?=[^\d])", m.group(1)):
                ent = ent.strip().strip("`").strip()
                if not ent:
                    continue
                pm = re.match(r"(.+?\.lean)(?::(\d+)\s*[-–]\s*(\d+))?$", ent)
                if not pm:
                    errors.append(f"{rel_rp}: `{ent}` is not a .lean path")
                    continue
                got = idx.resolve(pm.group(1))
                if len(got) != 1:
                    errors.append(f"{rel_rp}: `{ent}` "
                                  + ("matches no file in CONE.csv" if not got else
                                     f"is ambiguous ({len(got)} files)"))
                    continue
                f = next(iter(got))
                lo, hi = (int(pm.group(2)), int(pm.group(3))) if pm.group(2) else (0, 10**12)
                read_files.add(f)
                mine.add(f)
                for r in byfile[f]:
                    if lo <= r["line"] <= hi:
                        read_decls.add((f, r["line"]))
                mine_read += 1
        named |= mine
        per_report.append((rel_rp, len(mine), mine_read))

    def tier(pred_decl):
        files, n = set(), 0
        for f, v in incone.items():
            k = sum(1 for r in v if pred_decl(f, r))
            if k:
                files.add(f)
                n += k
        return files, n

    t_named = tier(lambda f, r: f in named)
    t_cited = tier(lambda f, r: (f, r["line"]) in cited_decls)
    t_read = tier(lambda f, r: (f, r["line"]) in read_decls)
    never = sorted(((len(v), f) for f, v in incone.items() if f not in named),
                   key=lambda x: (-x[0], x[1]))
    n_never = sum(n for n, _f in never)

    checks = []
    if t_named[1] + n_never != total:
        checks.append(f"named ({t_named[1]}) + never-named ({n_never}) != total ({total})")
    if not t_cited[0] <= t_named[0]:
        checks.append("a cited file is not a named file")
    if not t_read[0] <= t_named[0]:
        checks.append("a read file is not a named file")

    pct = (lambda n: f"{100.0 * n / total:.1f}%" if total else "-")
    L = [f"# Coverage ledger", "",
         f"Generated by `audits/ledger.py` from `{args.cone_csv}` and {len(reports)} report(s) "
         f"under `{args.reports}`. Counts are IN-CONE declarations of kind "
         f"{', '.join(sorted(kinds))}. Each tier is a subset of the one above; the "
         "definitions are in the script's docstring. Only the last tier says anything "
         "was read, and only because a report declares it.", "",
         "| tier | files | in-cone theorems | share |", "|---|---|---|---|",
         f"| 1. in cone | {len(incone):,} | {total:,} | 100% |",
         f"| 2. in a file some report NAMES (loose upper bound) | {len(t_named[0]):,} | "
         f"{t_named[1]:,} | {pct(t_named[1])} |",
         f"| 3. CITED at `file:line` (the containing declaration) | {len(t_cited[0]):,} | "
         f"{t_cited[1]:,} | {pct(t_cited[1])} |",
         f"| 4. declared READ LINE BY LINE | {len(t_read[0]):,} | {t_read[1]:,} | "
         f"{pct(t_read[1])} |",
         f"| never named | {len(never):,} | {n_never:,} | {pct(n_never)} |", ""]
    L.append("Self-check: " + ("tiers consistent (named + never-named = total; "
                               "cited and read files are named files)."
                               if not checks else "**FAILED** -- " + "; ".join(checks)))
    if ambiguous:
        L += ["", f"{sum(ambiguous.values()):,} citation(s) of {len(ambiguous):,} path(s) matched "
              "more than one file and were counted for all of them (tier 2 only): "
              + ", ".join(f"`{k}`" for k, _v in ambiguous.most_common(10))
              + (" ..." if len(ambiguous) > 10 else "")]
    if errors:
        L += ["", f"## READ-LINE-BY-LINE entries that did not resolve ({len(errors)})", ""]
        L += [f"- {e}" for e in errors]
    L += ["", f"## Never-named files, top {min(args.top, len(never))} of {len(never):,}", "",
          "| file | in-cone theorems |", "|---|---|"]
    L += [f"| `{f}` | {n} |" for n, f in never[:args.top]]
    L += ["", "## Reports", "", "| report | files named | READ-LINE-BY-LINE entries |",
          "|---|---|---|"]
    L += [f"| `{r}` | {n} | {k} |" for r, n, k in per_report]
    text = "\n".join(L) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text)
        print(f"wrote {args.out}")
    print("\n".join(L[:14]))
    if errors:
        print(f"{len(errors)} READ-LINE-BY-LINE entr{'y' if len(errors) == 1 else 'ies'} "
              f"did not resolve (listed in the ledger)", file=sys.stderr)
    return 1 if checks else 0


if __name__ == "__main__":
    raise SystemExit(main())
