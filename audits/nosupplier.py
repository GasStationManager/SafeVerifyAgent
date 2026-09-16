"""Which predicates does nobody ever SUPPLY?

W8 and W30 of the NSE deep audit found the same shape twice: a `structure` used
only in hypothesis position, with no declaration anywhere producing one, sitting
next to a weaker same-named twin that IS produced. The direction is safe -- a
theorem with an unsatisfiable hypothesis is vacuously fine, never false -- but it
means those theorems CANNOT BE REACHED, so a cone that counts them as live is
wrong. Finding the shape by hand cost a worker each time. This mechanises it.

    python3 audits/nosupplier.py /path/to/lean-project [-o OUT.csv] [--cone CONE.csv]

METHOD. For every declaration the signature is split at the last top-level `:`
into a BINDER region and a CONCLUSION. A predicate P is then:

  * HYPOTHESIS-USED in D  if P appears in D's binder region, or in a `variable`
    line in scope (section variables are hypotheses too -- missing them was the
    first bug this script had).
  * SUPPLIED by D          if P appears in D's CONCLUSION and NOT in its binders.
    The second clause is essential: `AxisymmetricResidualGrouping.lean:142`
    concludes an `ExtractionRegular` while assuming one at `:140`, which supplies
    nothing. Without that clause the script reports the opposite of the truth.

A predicate with hypothesis uses and zero suppliers is reported.

BOTH ERROR DIRECTIONS, stated because this number is quotable:

  * FALSE POSITIVES (reports "no supplier" when one exists). A supplier may build
    P without naming it: anonymous constructor `⟨...⟩` against an expected type,
    `obtain`/`refine` inside a proof, or an instance found by synthesis. So a hit
    is a CANDIDATE, to be confirmed by reading. This is why the script prints the
    anonymous-constructor count per hit.
  * FALSE NEGATIVES (stays silent when nothing supplies P). Suffix matching means
    a conclusion mentioning any `*.P` counts as supplying `P`, so a same-named
    twin in another namespace MASKS its sibling -- which is precisely the W30
    configuration. The script therefore reports FULLY QUALIFIED names and never
    merges namespaces.

A THIRD SHAPE THIS SCRIPT CANNOT SEE, measured against W8. `TailRates.flat_of_residuals`
(`GenericSupportedPolynomial.lean:130`) takes `hres : forall J m, JetRate l q (fs J) m (rho J - Lres m)`,
and W8 traced 5 hops to establish that nobody proves it. This script stays SILENT on
that, and correctly so by its own definition: `JetRate` *is* supplied, just never at
those arguments. So there are two distinct defects here and only the first is
mechanised:
  (a) a NAMED predicate nobody ever constructs        <- this script finds it
  (b) a supplied predicate used at ARGUMENTS nobody establishes  <- needs a
      per-callsite argument match, i.e. real elaboration. Not attempted.
Reporting (a) as "all such defects" would be the same count-for-surface error this
audit has made seven times. It is not.

So: a triage instrument that turns "read 1,620 lines" into "read 3 candidates".

VALIDATED against the two known cases before use: it flags
`HarmonicResidual.ExtractionRegular` (22 hypothesis sites, 6 files -- matching W30's
hand count of 21 sites in 5 other files plus its in-file use) and does NOT flag the
supplied twin `LocalResidualGrouping.ExtractionRegular`. An earlier version passed
neither: bare-suffix matching let the twin's supplier mask the strong one. Fixing that
ADDED 23 candidates, so the naive version hid 21% of its own output including the one
case known to be real.
"""

import argparse, collections, csv, os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from safeverifyagent.extract import blank_comments          # noqa: E402
from cone import decls_with_ns, IDENT, SKIP_DIRS            # noqa: E402

PRED_KINDS = ("structure", "class", "inductive", "def", "abbrev")
VARIABLE = re.compile(r"^[ \t]*variable\b(?P<rest>.*)$", re.M)
OPENERS, CLOSERS = "([{\u2983\u27e8", ")]}\u2984\u27e9"


def split_sig(body: str):
    """(binder_region, conclusion, proof) -- by bracket depth, not by regex."""
    depth, i, n = 0, 0, len(body)
    cut = None
    while i < n:
        c = body[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0:
            if body.startswith(":=", i):
                cut = i
                break
            if body.startswith("where", i) and (i == 0 or not body[i - 1].isalnum()):
                cut = i
                break
        i += 1
    sig, proof = (body[:cut], body[cut:]) if cut is not None else (body, "")
    # last top-level ':' separates the conclusion
    depth, last = 0, None
    for j, c in enumerate(sig):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif c == ":" and depth == 0 and not sig.startswith(":=", j):
            last = j
    if last is None:
        return sig, "", proof
    return sig[:last], sig[last + 1:], proof


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--min-hyp", type=int, default=1)
    args = ap.parse_args()

    files = {}
    for base, dirs, fns in os.walk(args.root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in sorted(fns):
            if fn.endswith(".lean"):
                p = os.path.join(base, fn)
                rel = os.path.relpath(p, args.root)
                files[rel] = blank_comments(open(p, encoding="utf-8",
                                                 errors="replace").read())

    # candidate predicates: Prop-valued structures/classes/defs
    preds, declared_at = {}, {}
    for rel, txt in files.items():
        for full, kind, line, body in decls_with_ns(txt):
            if kind not in PRED_KINDS:
                continue
            _b, concl, _p = split_sig(body)
            is_prop = kind in ("structure", "class") or "Prop" in concl
            if is_prop:
                preds[full] = kind
                declared_at[full] = (rel, line)

    suffix = collections.defaultdict(set)
    for full in preds:
        parts = full.split(".")
        for j in range(len(parts)):
            suffix[".".join(parts[j:])].add(full)

    # RESOLUTION, and why it differs from cone.py's on purpose.
    # cone.py resolves a token to EVERY contiguous run of its components, which
    # over-approximates -- the safe direction for reachability. Here that is the
    # FATAL direction: a fully qualified `LocalResidualGrouping.ExtractionRegular`
    # would also match its same-named twin `HarmonicResidual.ExtractionRegular`
    # via the bare suffix, marking the twin as supplied and HIDING the finding.
    # (Measured: it hid exactly the W30 result this script exists to find.)
    # So resolve MOST SPECIFICALLY: longest run that resolves at all, then narrow
    # by the file's namespace/`open` context. Under-approximating suppliers only
    # produces extra candidates to read, which is the safe direction here.
    def resolve(tok, ctx=()):
        parts = tok.split(".")
        for ln in range(len(parts), 0, -1):
            best = set()
            for i in range(0, len(parts) - ln + 1):
                best |= suffix.get(".".join(parts[i:i + ln]), frozenset())
            if best:
                if len(best) > 1 and ctx:
                    run = {".".join(parts[i:i + ln])
                           for i in range(0, len(parts) - ln + 1)}
                    narrow = {c for c in best
                              if any(c == f"{p}.{r}" for p in ctx for r in run)}
                    if narrow:
                        return narrow
                return best
        return set()

    hyp = collections.defaultdict(list)
    sup = collections.defaultdict(list)
    anon = collections.Counter()

    OPEN = re.compile(r"^[ \t]*open\b(?!\s+scoped)(?P<ns>[^\n]*)$", re.M)
    NSLINE = re.compile(r"^[ \t]*namespace[ \t]+([\w.\u03b1-\u03c9]+)", re.M)

    for rel, txt in files.items():
        ctx = set()
        for m in NSLINE.finditer(txt):
            parts = m.group(1).split(".")
            for j in range(len(parts)):
                ctx.add(".".join(parts[:j + 1]))
        for m in OPEN.finditer(txt):
            for t in re.findall(r"[\w.\u03b1-\u03c9]+", m.group("ns")):
                ctx.add(t)
        ctx = tuple(ctx)
        # section `variable` lines are hypotheses in scope for the whole file
        for m in VARIABLE.finditer(txt):
            for t in set(IDENT.findall(m.group("rest"))):
                for P in resolve(t, ctx):
                    hyp[P].append((rel, txt[:m.start()].count("\n") + 1, "variable"))
        for full, kind, line, body in decls_with_ns(txt):
            binders, concl, proof = split_sig(body)
            btoks, ctoks = set(IDENT.findall(binders)), set(IDENT.findall(concl))
            bres = set()
            for t in btoks:
                bres |= resolve(t, ctx)
            cres = set()
            for t in ctoks:
                cres |= resolve(t, ctx)
            for P in bres:
                if P != full:
                    hyp[P].append((rel, line, kind))
            for P in cres - bres:
                if P != full:
                    sup[P].append((rel, line, kind))
                    if "\u27e8" in proof:
                        anon[P] += 1

    rows = []
    for P, kind in sorted(preds.items()):
        h, s = hyp.get(P, []), sup.get(P, [])
        if len(h) >= args.min_hyp and not s:
            f, l = declared_at[P]
            rows.append({"predicate": P, "kind": kind, "declared": f"{f}:{l}",
                         "hypothesis_sites": len(h), "suppliers": 0,
                         "files_using": len({x[0] for x in h}),
                         "example_sites": "; ".join(f"{a}:{b}" for a, b, _ in h[:4])})
    rows.sort(key=lambda r: -r["hypothesis_sites"])

    print(f"{len(files):,} files, {len(preds):,} Prop-valued "
          f"structure/class/def candidates")
    print(f"{len(rows):,} have >={args.min_hyp} hypothesis use and NO supplier\n")
    for r in rows[:40]:
        print(f"  {r['hypothesis_sites']:4d} hyp sites, {r['files_using']:3d} files  "
              f"{r['predicate']}  ({r['declared']})")
    if args.out and rows:
        with open(args.out, "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f"\nwrote {args.out}")
    print("\nA hit is a CANDIDATE, not a finding: a supplier can build the "
          "predicate without naming it (anonymous constructor, synthesis).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
