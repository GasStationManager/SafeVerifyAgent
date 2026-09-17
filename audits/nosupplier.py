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
# A `variable` block CONTINUES across indented lines:
#     variable (D : AssemblyData Parameter) (s : StripData Associated)
#       (hn : PhysicalResidualNaturality.PositiveSupport ...)
# Matching only the first line missed `hn` entirely. That undercounts hypothesis
# sites, and worse, a predicate used ONLY inside such a block scores zero sites and
# is DROPPED from the candidate list -- i.e. the bug can hide a finding, which is
# the one direction this instrument must not fail in. Measured: it lost all uses in
# ActualParticularRealization.lean for two different predicates, and a worker caught
# it by reporting 4 using files where this script reported 3.
VARIABLE = re.compile(r"^[ \t]*variable\b(?P<rest>[^\n]*(?:\n[ \t]+[^\n]*)*)", re.M)
OPENERS, CLOSERS = "([{\u2983\u27e8", ")]}\u2984\u27e9"


HEADER = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom|example)\b"
    r"[ \t]*[^\s:({\[\u2983\u27e8]*")


def strip_header(body: str) -> str:
    """Drop `theorem P.of_wave` from the front of a declaration.

    Without this the declaration's OWN NAME is tokenised as part of its binder
    region, so `theorem SourceBounds.of_wave ... : SourceBounds ...` reads as a
    theorem that ASSUMES a `SourceBounds` -- and the `conclusion - binders` rule
    then throws away the supplier. That silently hides the single most idiomatic
    way a Lean structure is ever supplied: the namespaced smart constructor
    `P.of_foo` / `P.mk`. Measured: it produced 4 false positives in the first
    6 candidates a worker checked.
    """
    m = HEADER.match(body)
    return body[m.end():] if m else body


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



# ---------------------------------------------------------------------------
# TWO FALSE-POSITIVE ROUTES, MECHANISED AS ANNOTATIONS (not as exclusions).
#
# Worker verification of the first 17 candidates produced 5 false positives, and
# 4 of them were one of exactly two shapes:
#
#   route 4  P is a FIELD of structure S, and S is constructed somewhere, so
#            constructing S supplies P. (BandCharts <- AssemblyData;
#            MovingField <- LocalData, built at MeanStateRegularity.lean:435.)
#   route 2  P is built inside a PROOF under a type ascription,
#            `have h : P ... := by ... exact <...>`. (SupportedTriple at
#            MovingMomentBounds.lean:337; PressureRecovery.Hypotheses at :436.)
#
# These are reported as HINTS and never remove a candidate. Reason: auto-excluding
# on them would need a wide text window around the ascription, and a wide window
# starts calling things supplied that are not -- which HIDES findings, the one
# direction this instrument must not fail in. So the candidate still appears and
# the hint tells the reader where to look.
#
# The hint is deliberately imprecise in a known way: an ascription can be a base
# construction (`Hypotheses` built from ten separate binders -- a real supplier) or
# mere CLOSURE under an operation from existing `P`s (`have hp : UnitPeriods (f*g)`
# proved by `rw [hpf x k, hpg x k]` -- supplies nothing). Only reading separates
# them. Measured on the known set: hints cover 4 of 4 remaining false positives,
# and are absent on the two clearest true findings.
# ---------------------------------------------------------------------------

FIELD_LINE = re.compile(r"^[ \t]+(?!--)([A-Za-z_][\w'!?\u2080-\u2089]*)\s*:\s*(.+)$", re.M)
ASCRIPTION = re.compile(
    r"\b(?:have|let|show|suffices)\b[^:\n]{0,80}?:(?!=)\s*"
    r"(?P<ty>(?:(?!:=)[\s\S]){1,250}?):=(?=(?P<rhs>[\s\S]{0,220}))")
CONSTRUCTS = re.compile(r"\u27e8|\bconstructor\b|\brefine\b|\bmk\b")


def struct_fields(body: str):
    """Field (name, type) pairs of a `structure ... where` block."""
    if "where" not in body:
        return []
    return [(m.group(1), m.group(2))
            for m in FIELD_LINE.finditer(body.split("where", 1)[1])]


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
            _b, concl, _p = split_sig(strip_header(body))
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
            binders, concl, proof = split_sig(strip_header(body))
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
            # AMBIGUOUS RESOLUTION MUST NOT CREDIT A SUPPLIER.
            # 7 predicates in this artifact are named exactly `Budget`, 8 `Regular`,
            # 8 `Data`. When a file writes the bare short name and the namespace/open
            # context cannot single one out, the old code credited a supplier to ALL
            # of them -- which is the twin-masking bug in a subtler form, and it hid a
            # genuine ESCALATE: `EulerAllOrderCorrectionBudget.Budget` never became a
            # candidate at all, because three files supplying OTHER `Budget` twins
            # (PacketForwardInitializedExactLifted:52, PacketParentJoinedBudget:27,
            # StaticEulerCorrection:48) were credited to it. A reader found it instead.
            # Fix: credit a supplier only when the token resolves UNAMBIGUOUSLY. That
            # over-reports candidates, which is the safe direction here.
            for t in ctoks:
                r = resolve(t, ctx)
                if len(r) != 1:
                    continue
                for P in r - bres:
                    if P != full:
                        sup[P].append((rel, line, kind))
                    if "\u27e8" in proof:
                        anon[P] += 1

    # --- annotation pass: the two known false-positive routes (see comment above)
    field_parent = collections.defaultdict(set)
    for rel, txt in files.items():
        for full, kind, _line, body in decls_with_ns(txt):
            if kind not in ("structure", "class"):
                continue
            parts = full.split(".")
            ctx = tuple(".".join(parts[:j + 1]) for j in range(len(parts)))
            for _fname, ftype in struct_fields(body):
                for t in set(IDENT.findall(ftype)):
                    for P in resolve(t, ctx):
                        if P != full:
                            field_parent[P].add(full)

    asc = collections.defaultdict(list)
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
        for full, _kind, line, body in decls_with_ns(txt):
            _b, _c, proof = split_sig(strip_header(body))
            if not proof:
                continue
            for m in ASCRIPTION.finditer(proof):
                for t in set(IDENT.findall(m.group("ty"))):
                    for P in resolve(t, ctx):
                        if P != full:
                            asc[P].append(f"{rel}:{line}")

    def supplied_ancestor(P, seen=None):
        seen = seen if seen is not None else set()
        for S in field_parent.get(P, ()):
            if S in seen:
                continue
            seen.add(S)
            if sup.get(S):
                return S
            got = supplied_ancestor(S, seen)
            if got:
                return got
        return None

    rows = []
    for P, kind in sorted(preds.items()):
        h, s = hyp.get(P, []), sup.get(P, [])
        if len(h) >= args.min_hyp and not s:
            f, l = declared_at[P]
            anc = supplied_ancestor(P)
            hints = asc.get(P, [])
            rows.append({"predicate": P, "kind": kind, "declared": f"{f}:{l}",
                         "hypothesis_sites": len(h), "suppliers": 0,
                         "files_using": len({x[0] for x in h}),
                         "hint_supplied_parent": anc or "",
                         "hint_in_proof_ascription": "; ".join(hints[:2]),
                         "hint": "route4" if anc else ("route2?" if hints else ""),
                         "example_sites": "; ".join(f"{a}:{b}" for a, b, _ in h[:4])})
    rows.sort(key=lambda r: -r["hypothesis_sites"])

    print(f"{len(files):,} files, {len(preds):,} Prop-valued "
          f"structure/class/def candidates")
    nh = sum(1 for r in rows if r["hint"])
    print(f"{len(rows):,} have >={args.min_hyp} hypothesis use and NO supplier")
    print(f"{nh:,} of those carry a false-positive HINT (route4 supplied parent, or "
          f"route2 in-proof ascription); the other {len(rows) - nh:,} carry none and "
          f"are the higher-confidence set\n")
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
