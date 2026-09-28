"""Which predicates does nobody ever SUPPLY?

W8 and W30 of the NSE deep audit found the same shape twice: a `structure` used
only in hypothesis position, with no declaration anywhere producing one, sitting
next to a weaker same-named twin that IS produced. The direction is safe -- a
theorem with an unsatisfiable hypothesis is vacuously fine, never false -- but it
means those theorems CANNOT BE REACHED, so a cone that counts them as live is
wrong. Finding the shape by hand cost a worker each time. This mechanises it.

    python3 audits/nosupplier.py /path/to/lean-project [-o OUT.csv]

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

GENERALISED 2026-09-28 for the NAMED-HYPOTHESIS convention (differential-geometry
states it: "a missing result is named rather than `sorry`-ed"). Under that
convention an open result is a Prop-valued `def`/`structure`/`class` carried as
a hypothesis and discharged later by a `..._holds` theorem, so a predicate that
is never discharged on the headline route is a `sorry` `#print axioms` cannot
see. Four additions, each a column:

    python3 audits/nosupplier.py ROOT [-o OUT.csv] [--md OUT.md] [--cone CONE.csv]
        [--convention named-hypothesis] [--all]

  * EFFECTIVE SUPPLY (the `status` and `chain` columns). A supplier that itself
    assumes another predicate supplies nothing unless that one is supplied too:
    `theorem p_holds (h : QFrontier) : PFrontier` discharges `PFrontier` only
    conditionally. Suppliers are read as Horn clauses `P <= Q1 /\ ... /\ Qn`
    (the Qi are the supplier's UNAMBIGUOUSLY resolved binder predicates; section
    `variable`s are not counted, since Lean 4 includes a variable in a theorem
    only when its statement names it) and `effective` is their least fixpoint.
    A Prop `inductive` is supplied by its constructors, read the same way, so a
    predicate whose every constructor needs an instance of itself -- closure
    without a base case -- is unsupplied. `chain` names the first refutation:
    `P <= F.lean:10 needs Q; Q: no supplier`.
      status = no_supplier          nothing names P in a conclusion (the original set)
               no_supplier_in_cone  (--cone) suppliers exist, none of them in cone
               conditional          suppliers exist, none effective
               supplied             effective (only listed with --all)
    Ambiguous binder tokens are left OUT of a clause body, so `conditional` is a
    LOWER bound: a supplier that needs an unsupplied predicate named by an
    ambiguous short name is still counted effective.
  * ROUTE-4 CHAINING (the `hint` / `hint_supplied_parent` columns). A predicate
    that is a field of structure S (or that S `extends`) is supplied by building
    S, but only if S is itself effectively supplied, transitively. `route4`
    names the supplied ancestor chain; `route4-refuted` names the chain that
    was walked and found no supplied ancestor at any level. Still a hint: it
    never removes a candidate, and route 4 is not credited in `effective`.
  * `--cone CONE.csv`: hypothesis sites are counted in cone
    (`hypothesis_sites_in_cone`; a `variable` line counts if its file holds an
    in-cone declaration), suppliers likewise (`suppliers_in_cone`), and the
    fixpoint is recomputed from in-cone suppliers only (`effective_in_cone`).
    Rows are then selected and sorted by in-cone sites. Declarations are
    matched to CONE.csv by (file, line), so the CONE.csv must come from the
    same `cone.py` parser; the script prints how many sites failed to match.
  * `unique_short_name`: no other predicate shares P's last component. The NSE
    audit measured this instrument's NEGATIVES as reliable only for such
    predicates (the ambiguous-resolution fix refuses credit on a shared short
    name, and an earlier version credited a twin's supplier to P). A
    `supplied` row with `unique_short_name = False` is flagged
    `negative_reliable = False`.
  * `--convention named-hypothesis` also lists `def`/`abbrev`s WITHOUT a
    written `: Prop` whose body opens with a proposition former (`∀`, `∃`, `¬`,
    `Nonempty`, ...) -- `shape = prop_inferred` -- and adds `conditional`
    rows. The markdown summary then gives Prop-valued defs and classes used as
    binders their own sections, since the convention may carry a missing result
    as any of them. Every row has a `shape`: predicate (declared `: Prop`),
    class, bundle (a data `structure`/`inductive`, whose hits are only
    interesting if the route needs an instance), prop_inferred.
"""

import argparse, collections, csv, os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from safeverifyagent.extract import blank_comments          # noqa: E402
from cone import decls_with_ns, IDENT, IMPORT, SKIP_DIRS, closures, module_name  # noqa: E402

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




EXTENDS = re.compile(r"\bextends\b(?P<rest>[\s\S]*?)(?:\bwhere\b|:=|$)")
PROP_FORMER = re.compile(
    r"^\s*:=\s*(?:by\s+exact\s+)?(?:∀|∃|¬|∀ᶠ|∃ᶠ|"
    r"Nonempty\b|IsEmpty\b|Function\.(?:Injective|Surjective|Bijective)\b)")
CTOR = re.compile(r"^[ \t]*\|[ \t]*([A-Za-z_][\w'!?]*)(?P<rest>[^\n]*(?:\n[ \t]+(?!\|)[^\n]*)*)", re.M)
OPEN = re.compile(r"^[ \t]*open\b(?!\s+scoped)(?P<ns>[^\n]*)$", re.M)
NSLINE = re.compile(r"^[ \t]*namespace[ \t]+([\w.α-ω]+)", re.M)


def progress(msg):
    print(msg, file=sys.stderr, flush=True)


def file_ctx(txt):
    ctx = set()
    for m in NSLINE.finditer(txt):
        parts = m.group(1).split(".")
        for j in range(len(parts)):
            ctx.add(".".join(parts[:j + 1]))
    for m in OPEN.finditer(txt):
        for t in re.findall(r"[\w.α-ω]+", m.group("ns")):
            ctx.add(t)
    return tuple(ctx)


def lean_files(root):
    out = []
    for base, dirs, fns in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in fns:
            if fn.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(base, fn), root))
    return sorted(out)


def load_cone(path):
    """{(file, line): in_cone} and the set of files holding an in-cone decl."""
    at, files = {}, set()
    with open(path, newline="", encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            on = r["in_cone"].strip().lower() in ("true", "1")
            at[(r["file"], int(r["line"]))] = on
            if on:
                files.add(r["file"])
    return at, files


def fixpoint(clauses, heads):
    """Least fixpoint of Horn clauses [(head, frozenset(body), label)].
    Returns (effective set, {head: label of the first clause that fired})."""
    eff, why = set(), {}
    waiting = collections.defaultdict(list)
    need = []
    q = collections.deque()
    for i, (h, body, lab) in enumerate(clauses):
        need.append(len(body))
        for b in body:
            waiting[b].append(i)
        if not body:
            q.append(i)
    while q:
        i = q.popleft()
        h, _b, lab = clauses[i]
        if h in eff:
            continue
        eff.add(h)
        why[h] = lab
        for j in waiting.get(h, ()):
            need[j] -= 1
            if need[j] == 0:
                q.append(j)
    return eff, why


def explain(P, by_head, eff, sup_all, depth=0, seen=None, note=lambda P: ""):
    """First refutation chain of an ineffective P, as one line. `note(Q)` is
    appended at the leaf: a route-2/route-4 hint there means the whole chain
    may be a false positive, since a conditional row inherits its leaf's."""
    seen = set() if seen is None else seen
    if P in seen:
        return f"{P}: (cycle)"
    seen.add(P)
    cl = by_head.get(P, [])
    if not cl:
        return (f"{P}: no supplier" if not sup_all.get(P) else f"{P}: no supplier in cone") + note(P)
    h, body, lab = cl[0]
    missing = sorted(b for b in body if b not in eff)
    if not missing:
        return f"{P}: effective"
    if missing == [P]:
        return f"{P} <= {lab} needs {P} itself: closure without a base case"
    head = f"{P} <= {lab} needs {', '.join(missing[:3])}"
    if depth >= 4:
        return head + "; ..."
    return head + "; " + explain(missing[0], by_head, eff, sup_all, depth + 1, seen, note)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="nosupplier.py")
    ap.add_argument("root")
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--md", default=None,
                    help="markdown summary (default: OUT with .md when -o is given)")
    ap.add_argument("--min-hyp", type=int, default=1)
    ap.add_argument("--cone", default=None, help="CONE.csv from audits/cone.py")
    ap.add_argument("--convention", choices=("default", "named-hypothesis"),
                    default="default")
    ap.add_argument("--all", action="store_true",
                    help="also list supplied predicates (for negative_reliable)")
    ap.add_argument("--top", type=int, default=40)
    args = ap.parse_args(argv)
    named = args.convention == "named-hypothesis"
    cone_at, cone_files = load_cone(args.cone) if args.cone else ({}, set())

    files = lean_files(args.root)
    nf = len(files)

    def read(rel):
        with open(os.path.join(args.root, rel), encoding="utf-8", errors="replace") as fh:
            return blank_comments(fh.read())

    # ---- pass 1: candidate predicates, structure fields, inductive constructors
    preds, declared_at, shape = {}, {}, {}
    pred_files = collections.defaultdict(set)
    mod_idx = {module_name(rel): i for i, rel in enumerate(files)}
    imports = [[] for _ in files]
    raw_fields = []      # (structure, ctx, [type text])
    raw_ctors = []       # (inductive, ctx, rel, line, [ctor text])
    for fi, rel in enumerate(files):
        txt = read(rel)
        imports[fi] = sorted({mod_idx[m] for m in IMPORT.findall(txt) if m in mod_idx})
        for full, kind, line, body in decls_with_ns(txt):
            if kind not in PRED_KINDS:
                continue
            hb = strip_header(body)
            if kind == "inductive":
                # the signature ends where the constructors begin; otherwise the
                # last `:` is a constructor's and the type reads as its result
                hb = re.split(r"\n[ \t]*\||\bwhere\b", hb, maxsplit=1)[0]
            _b, concl, rest = split_sig(hb)
            is_prop = "Prop" in IDENT.findall(concl)
            sh = None
            if kind == "class":
                sh = "class"
            elif is_prop:
                sh = "predicate"
            elif kind == "structure":
                sh = "bundle"
            elif kind == "inductive":
                sh = "bundle"
            elif named and kind in ("def", "abbrev") and not concl.strip() \
                    and PROP_FORMER.match(rest):
                sh = "prop_inferred"
            if sh is None:
                continue
            preds[full] = kind
            shape[full] = sh
            declared_at[full] = (rel, line)
            pred_files[full].add(fi)
            parts = full.split(".")
            ctx = tuple(".".join(parts[:j + 1]) for j in range(len(parts)))
            if kind in ("structure", "class"):
                types = [t for _n, t in struct_fields(body)]
                m = EXTENDS.search(hb.split(":=", 1)[0])
                if m:
                    types.append(m.group("rest"))
                raw_fields.append((full, ctx + file_ctx(txt), fi, types))
            elif kind == "inductive":
                ctors = [(c.group(1), c.group("rest")) for c in CTOR.finditer(body)]
                raw_ctors.append((full, ctx + file_ctx(txt), fi, rel, line, ctors))
        if (fi + 1) % 2000 == 0:
            progress(f"[nosupplier] pass 1: {fi + 1:,}/{nf:,} files")

    suffix = collections.defaultdict(set)
    for full in preds:
        parts = full.split(".")
        for j in range(len(parts)):
            suffix[".".join(parts[j:])].add(full)
    short_count = collections.Counter(p.rsplit(".", 1)[-1] for p in preds)

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
    #
    # And, since 2026-09-28, only among predicates IN SCOPE: declared in the
    # citing file's import closure, the rule cone.py already used. Without it a
    # bare `RiemannianMetricComplete` in a file that cannot even see
    # `DifferentialGeometry.Geometry.RiemannianMetricComplete` still counted as
    # a hypothesis site of it (and, being ambiguous, supplied nothing), which
    # inflated the top differential-geometry candidate's site count.
    scope = closures(imports)
    nbytes = (len(files) + 7) // 8
    rcache = {}
    cur = {"fi": None, "bits": b""}

    def in_scope(c):
        bits = cur["bits"]
        return any(bits[m >> 3] >> (m & 7) & 1 for m in pred_files[c])

    def resolve(tok, ctx=(), fi=None, ns=()):
        """`ns`: the declaration's namespace chain, innermost first. Lean
        resolves a bare name against the innermost namespace that has it before
        it looks at `open`s or the root (`ResolveName.resolveUsingNamespace`),
        so a twin in an enclosing namespace is not a candidate when the inner
        one exists."""
        if fi is not None and fi != cur["fi"]:
            cur["fi"] = fi
            cur["bits"] = scope[fi].to_bytes(nbytes, "little")
            rcache.clear()
        key = (tok, ctx, ns)
        r = rcache.get(key)
        if r is not None:
            return r
        parts = tok.split(".")
        r = set()
        for ln in range(len(parts), 0, -1):
            best = set()
            for i in range(0, len(parts) - ln + 1):
                best |= {c for c in suffix.get(".".join(parts[i:i + ln]), ()) if in_scope(c)}
            if best:
                run = {".".join(parts[i:i + ln])
                       for i in range(0, len(parts) - ln + 1)}
                if len(best) > 1 and ns:
                    for p in ns:
                        hit = {c for c in best if any(c == f"{p}.{r_}" for r_ in run)}
                        if hit:
                            best = hit
                            break
                if len(best) > 1 and ctx:
                    narrow = {c for c in best
                              if any(c == f"{p}.{r_}" for p in ctx for r_ in run)}
                    if narrow:
                        best = narrow
                r = best
                break
        r = frozenset(r)
        if len(rcache) < 2_000_000:
            rcache[key] = r
        return r

    # ---- pass 2: hypothesis sites, suppliers (as clauses), ascription hints
    hyp = collections.defaultdict(list)       # P -> [(rel, line, kind, in_cone)]
    sup = collections.defaultdict(list)       # P -> [(rel, line, kind, in_cone)]
    clauses = []                              # (P, body, label, in_cone)
    asc = collections.defaultdict(list)
    unmatched = 0
    for fi, rel in enumerate(files):
        txt = read(rel)
        ctx = file_ctx(txt)
        file_in_cone = rel in cone_files
        # section `variable` lines are hypotheses in scope for the whole file
        for m in VARIABLE.finditer(txt):
            ln = txt.count("\n", 0, m.start()) + 1
            for t in set(IDENT.findall(m.group("rest"))):
                for P in resolve(t, ctx, fi):
                    hyp[P].append((rel, ln, "variable", file_in_cone))
        for full, kind, line, body in decls_with_ns(txt):
            if args.cone:
                on = cone_at.get((rel, line))
                if on is None:
                    unmatched += 1
                    on = False
            else:
                on = False
            binders, concl, proof = split_sig(strip_header(body))
            fp = full.split(".")
            ns = tuple(".".join(fp[:k]) for k in range(len(fp) - 1, 0, -1))
            bres, unamb = set(), set()
            for t in set(IDENT.findall(binders)):
                r = resolve(t, ctx, fi, ns)
                bres |= r
                if len(r) == 1:
                    unamb |= r
            for P in bres:
                if P != full:
                    hyp[P].append((rel, line, kind, on))
            # AMBIGUOUS RESOLUTION MUST NOT CREDIT A SUPPLIER.
            # 7 predicates in the NSE artifact are named exactly `Budget`, 8
            # `Regular`, 8 `Data`. When a file writes the bare short name and the
            # namespace/open context cannot single one out, the old code credited a
            # supplier to ALL of them -- which is the twin-masking bug in a subtler
            # form, and it hid a genuine ESCALATE: `EulerAllOrderCorrectionBudget.Budget`
            # never became a candidate at all, because three files supplying OTHER
            # `Budget` twins (PacketForwardInitializedExactLifted:52,
            # PacketParentJoinedBudget:27, StaticEulerCorrection:48) were credited to
            # it. A reader found it instead. Fix: credit a supplier only when the
            # token resolves UNAMBIGUOUSLY. That over-reports candidates, which is
            # the safe direction here.
            for t in set(IDENT.findall(concl)):
                r = resolve(t, ctx, fi, ns)
                if len(r) != 1:
                    continue
                for P in r - bres:
                    if P != full:
                        sup[P].append((rel, line, kind, on))
                        clauses.append((P, frozenset(unamb - {P}),
                                        f"{rel}:{line}", on))
            if proof:
                for m in ASCRIPTION.finditer(proof):
                    for t in set(IDENT.findall(m.group("ty"))):
                        for P in resolve(t, ctx, fi, ns):
                            if P != full:
                                asc[P].append(f"{rel}:{line}")
        if (fi + 1) % 2000 == 0:
            progress(f"[nosupplier] pass 2: {fi + 1:,}/{nf:,} files")

    # inductive constructors are suppliers of their own type. A constructor whose
    # arguments include the inductive itself yields a clause `Ind <= Ind /\ ...`,
    # which the fixpoint can only fire once some other constructor has: so a
    # predicate with only recursive constructors (closure without a base case)
    # comes out unsupplied, as it should.
    for ind, ctx, fi, rel, line, ctors in raw_ctors:
        ip = ind.split(".")
        ns = tuple(".".join(ip[:k]) for k in range(len(ip) - 1, 0, -1))
        on = cone_at.get((rel, line), False)
        for cname, text in ctors:
            b, c, _p = split_sig(text)
            depth, cut = 0, None
            for j, ch in enumerate(c):
                if ch in OPENERS:
                    depth += 1
                elif ch in CLOSERS:
                    depth -= 1
                elif ch == "\u2192" and depth == 0:
                    cut = j
            args_text = b + " " + (c[:cut] if cut is not None else "")
            body = set()
            for t in set(IDENT.findall(args_text)):
                r = resolve(t, ctx, fi, ns)
                if len(r) == 1:
                    body |= r
            sup[ind].append((rel, line, "constructor", on))
            clauses.append((ind, frozenset(body), f"{rel}:{line} ctor {cname}", on))

    # structure containment (route 4), resolved now that `preds` is complete
    field_parent = collections.defaultdict(set)
    for S, ctx, fi, types in raw_fields:
        sp = S.split(".")
        ns = tuple(".".join(sp[:k]) for k in range(len(sp) - 1, 0, -1))
        for ftype in types:
            for t in set(IDENT.findall(ftype)):
                for P in resolve(t, ctx, fi, ns):
                    if P != S:
                        field_parent[P].add(S)

    eff, _w = fixpoint([(h, b, l) for h, b, l, _o in clauses], preds)
    by_head = collections.defaultdict(list)
    for h, b, l, _o in clauses:
        by_head[h].append((h, b, l))
    for h in by_head:
        by_head[h].sort(key=lambda c: len([x for x in c[1] if x not in eff]))
    if args.cone:
        cl_in = [(h, b, l) for h, b, l, o in clauses if o]
        eff_in, _w = fixpoint(cl_in, preds)
        by_head_in = collections.defaultdict(list)
        for c in cl_in:
            by_head_in[c[0]].append(c)
        for h in by_head_in:
            by_head_in[h].sort(key=lambda c: len([x for x in c[1] if x not in eff_in]))
    sup_all = {P: v for P, v in sup.items() if v}

    def route4(P, E):
        """(verdict, chain) walking containing structures up to a supplied one."""
        parents = field_parent.get(P)
        if not parents:
            return "", ""
        seen, frontier, paths = {P}, [(P, [P])], []
        while frontier:
            nxt = []
            for x, path in frontier:
                for S in sorted(field_parent.get(x, ())):
                    if S in seen:
                        continue
                    seen.add(S)
                    if S in E:
                        return "route4", " <- ".join(path + [S]) + " (supplied)"
                    paths.append(path + [S])
                    nxt.append((S, path + [S]))
            frontier = nxt
        longest = max(paths, key=len)
        return "route4-refuted", (" <- ".join(longest) +
                                  f" (no supplied container at any level; {len(seen) - 1} walked)")

    E = eff_in if args.cone else eff

    def leaf_note(Q):
        v, _c = route4(Q, E)
        h = asc.get(Q)
        bits = ([f"route4 via {_c.split(' <- ')[1].split(' ')[0]}"] if v == "route4" else []) \
            + ([f"route2? {h[0]}"] if h else [])
        return f" [hint: {'; '.join(bits)}]" if bits else ""

    rows = []
    for P, kind in sorted(preds.items()):
        h = hyp.get(P, [])
        s = sup.get(P, [])
        h_in = sum(1 for x in h if x[3])
        s_in = sum(1 for x in s if x[3])
        sites = h_in if args.cone else len(h)
        if P in E:
            status = "supplied"
        elif not s:
            status = "no_supplier"
        elif args.cone and s_in == 0:
            status = "no_supplier_in_cone"
        else:
            status = "conditional"
        keep = sites >= args.min_hyp and (
            args.all or status in ("no_supplier", "no_supplier_in_cone")
            or (status == "conditional" and named))
        if shape[P] == "prop_inferred" and not named:
            keep = False
        if not keep:
            continue
        f, l = declared_at[P]
        verdict, chain4 = route4(P, E)
        hints = asc.get(P, [])
        if status == "supplied":
            chain = ""
        elif args.cone:
            chain = explain(P, by_head_in, eff_in, sup_all, note=leaf_note)
        else:
            chain = explain(P, by_head, eff, sup_all, note=leaf_note)
        uniq = short_count[P.rsplit(".", 1)[-1]] == 1
        rows.append({
            "predicate": P, "kind": kind, "shape": shape[P], "declared": f"{f}:{l}",
            "status": status,
            "hypothesis_sites": len(h), "hypothesis_sites_in_cone": h_in if args.cone else "",
            "suppliers": len(s), "suppliers_in_cone": s_in if args.cone else "",
            "files_using": len({x[0] for x in h}),
            "declared_in_cone": cone_at.get((f, l), "") if args.cone else "",
            "unique_short_name": uniq,
            "negative_reliable": (uniq if status == "supplied" else ""),
            "chain": chain,
            "hint_supplied_parent": chain4 if verdict == "route4" else "",
            "route4_chain": chain4,
            "hint_in_proof_ascription": "; ".join(hints[:2]),
            "hint": "; ".join(x for x in (verdict, "route2?" if hints else "") if x),
            "example_sites": "; ".join(f"{a}:{b}" for a, b, _k, _o in
                                       (sorted(h, key=lambda x: not x[3]) if args.cone else h)[:4]),
            "example_suppliers": "; ".join(f"{a}:{b}" for a, b, _k, _o in s[:3]),
        })
    key = "hypothesis_sites_in_cone" if args.cone else "hypothesis_sites"
    rows.sort(key=lambda r: (r["status"] == "supplied", -int(r[key] or 0), r["predicate"]))

    by_status = collections.Counter(r["status"] for r in rows)
    print(f"{nf:,} files, {len(preds):,} candidate predicates "
          f"({', '.join(f'{k} {v:,}' for k, v in collections.Counter(shape.values()).most_common())})")
    if args.cone:
        print(f"cone: {args.cone}; {unmatched:,} declaration sites did not match a "
              f"CONE.csv row (0 expected: a CONE.csv from a different cone.py parser "
              f"silently drops sites)")
    print("rows by status: " + ", ".join(f"{k} {v:,}" for k, v in by_status.most_common()))
    nh = sum(1 for r in rows if {"route4", "route2?"} & set(r["hint"].split("; "))
             and r["status"] != "supplied")
    print(f"{nh:,} non-supplied rows carry a false-positive HINT (route4 supplied "
          f"container, or route2 in-proof ascription); those without one are the "
          f"higher-confidence set")
    leafh = sum(1 for r in rows if r["status"] == "conditional" and "[hint:" in r["chain"])
    if by_status.get("conditional"):
        print(f"{leafh:,} of {by_status['conditional']:,} conditional rows end their chain at a "
              f"HINTED leaf (the leaf may be supplied after all, and the row with it)")
    amb = sum(1 for r in rows if r["status"] != "supplied" and not r["unique_short_name"])
    print(f"{amb:,} non-supplied rows have an AMBIGUOUS short name")
    if args.all:
        un = sum(1 for r in rows if r["status"] == "supplied" and not r["unique_short_name"])
        print(f"{un:,} 'supplied' verdicts are on ambiguous short names: negatives "
              f"there are unreliable")
    print()
    for r in [r for r in rows if r["status"] != "supplied"][:args.top]:
        print(f"  {int(r[key] or 0):4d} {'in-cone ' if args.cone else ''}hyp sites  "
              f"{r['status']:20s} {r['predicate']}  ({r['declared']})")
    if args.out:
        with open(args.out, "w", newline="", encoding="utf-8") as fh:
            flds = list(rows[0].keys()) if rows else ["predicate"]
            w = csv.DictWriter(fh, fieldnames=flds)
            w.writeheader()
            w.writerows(rows)
        print(f"\nwrote {args.out}")
    md = args.md or (os.path.splitext(args.out)[0] + ".md" if args.out else None)
    if md:
        write_md(md, rows, args, key, by_status, len(preds), shape, unmatched, named)
        print(f"wrote {md}")
    print("\nA hit is a CANDIDATE, not a finding: a supplier can build the "
          "predicate without naming it (anonymous constructor, synthesis).")
    return 0


def write_md(path, rows, args, key, by_status, npred, shape, unmatched, named):
    live = [r for r in rows if r["status"] != "supplied"]
    L = ["# No-supplier report", "",
         f"Generated by `audits/nosupplier.py` over `{args.root}`"
         + (f" with `--cone {args.cone}`" if args.cone else "")
         + (f" and `--convention {args.convention}`" if named else "") + ".", "",
         "A row is a CANDIDATE: a predicate used as a hypothesis that no declaration "
         "effectively supplies BY NAME. Anonymous constructors, instance synthesis and "
         "in-proof `have` constructions are invisible here (the `hint` column points "
         "at the last), so every row is confirmed by reading before it is quoted. "
         "Method and both error directions: the script's docstring.", "",
         f"- candidate predicates: {npred:,} "
         f"({', '.join(f'{k} {v:,}' for k, v in collections.Counter(shape.values()).most_common())})",
         "- rows: " + ", ".join(f"{k} {v:,}" for k, v in by_status.most_common())]
    if args.cone:
        L.append(f"- declaration sites unmatched in CONE.csv: {unmatched:,}")
    if by_status.get("conditional"):
        L.append(f"- conditional rows whose chain ends at a hinted leaf (weaker): "
                 f"{sum(1 for r in live if r['status'] == 'conditional' and '[hint:' in r['chain']):,}"
                 f" of {by_status['conditional']:,}")
    L.append(f"- rows on an ambiguous short name (negative unreliable, positive still "
             f"a candidate): {sum(1 for r in live if not r['unique_short_name']):,}")
    L += ["", f"## Top {min(args.top, len(live))} by "
          f"{'in-cone ' if args.cone else ''}hypothesis sites", ""]
    L += table(live[:args.top], key)
    if named:
        for title, pick in (("Prop-valued predicates only (bundles excluded)",
                             lambda r: r["shape"] != "bundle"),
                            ("Prop-valued defs used as binders",
                             lambda r: r["kind"] in ("def", "abbrev")),
                            ("Classes used as binders", lambda r: r["shape"] == "class")):
            sel = [r for r in live if pick(r)]
            L += ["", f"## {title} ({len(sel):,})", ""]
            L += table(sel[:args.top], key) if sel else ["none"]
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(L) + "\n")


def table(rows, key):
    out = ["| sites | status | predicate | shape | declared | suppliers | unique | hint | chain |",
           "|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        ch = r["chain"].replace("|", "\\|")
        hint = r["hint"] + (f": {r['route4_chain']}" if r["route4_chain"] else "")
        if len(hint) > 160:
            hint = hint[:157] + "..."
        if len(ch) > 220:
            ch = ch[:217] + "..."
        sup = f"{r['suppliers']}" + (f" ({r['suppliers_in_cone']} in cone)"
                                     if r["suppliers_in_cone"] != "" else "")
        out.append(f"| {r[key]} | {r['status']} | `{r['predicate']}` | {r['shape']} | "
                   f"`{r['declared']}` | {sup} | {'yes' if r['unique_short_name'] else 'NO'} | "
                   f"{hint} | {ch} |")
    return out


if __name__ == "__main__":
    raise SystemExit(main())
