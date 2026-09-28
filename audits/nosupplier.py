"""Which predicates does nobody ever SUPPLY?

W8 and W30 of the NSE deep audit found the same shape twice: a `structure` used
only in hypothesis position, with no declaration anywhere producing one, sitting
next to a weaker same-named twin that IS produced. The direction is safe -- a
theorem with an unsatisfiable hypothesis is vacuously fine, never false -- but it
means those theorems CANNOT BE REACHED, so a cone that counts them as live is
wrong. Finding the shape by hand cost a worker each time. This mechanises it.

    python3 audits/nosupplier.py /path/to/lean-project [-o OUT.csv]

METHOD. For every declaration the signature is split at the FIRST top-level `:`
into a BINDER region and a CONCLUSION (note N4 below; it was the last `:` until
2026-09-28), and the conclusion is read by polarity: `∀` binders and `→`
antecedents inside it are hypotheses too. A predicate P is then:

  * HYPOTHESIS-USED in D  if P appears in D's binder region or in a hypothesis
    position of its conclusion, or in a `variable`
    line in scope (section variables are hypotheses too -- missing them was the
    first bug this script had).
  * SUPPLIED by D          if P appears in what D's CONCLUSION asserts and NOT in
    its hypotheses (or by one of the other mechanisms of notes N1-N5).
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

FIXED 2026-09-28 (second pass). A reader verified 48 differential-geometry
candidate rows (`audits/dg-intake/workers/nosupplier-verify-1.md`) and found 44
false positives with named causes; that report was the test oracle. Each fix
has a regression shape in `tests/test_audit_tools.py` (`InstrumentFixesTest`,
all eight of which fail on the previous version). Agreement with the reader
went 4/48 -> 45/48 (the 4 true negatives stay unsupplied); rows by status
(--cone, --all) went supplied 1,186 / no_supplier 157 / conditional 146 /
no_supplier_in_cone 142 -> supplied 1,429 / no_supplier 49 / conditional 35 /
no_supplier_in_cone 97 (the cone itself also changed, C1 in `cone.py`).

  N4  `split_sig` cut at the LAST depth-0 `:`, so `∃ σ : P, ∀ v : D, …` read
      `P` as a hypothesis site and `D` as supplied (the reader counted 7,987 of
      145,545 signatures with more than one top-level colon). The binder
      region now ends at the FIRST depth-0 `:`, and the conclusion is read by
      POLARITY (`polarize`): `∀` binders and `→` antecedents are hypotheses
      (sites, and the Horn body of what they scope over), `∃` witnesses and
      conjuncts are supplied. Connectives are split only in front of the first
      binder, whose scope runs to the end of its bracket. `split_sig` is shared
      with `cone.py` (`dead`) and `junkvalue.py`, which read the true binder
      region now too. Row flipped by it alone: #23.
  N4b A `let`/`have` in a statement owns the next `:=`; `split_sig` used to cut
      the signature there and lose the conclusion (#33).
  N2  Dot notation: `(solutions p).IsSolutionOn`, `(c.X).SmoothOn`,
      `T.str.SplitData` are looked up in the namespace of the RECEIVER'S TYPE
      (Lean's generalized field notation), never the enclosing namespace.
      Receiver types come from binders, `∀/∃/have` locals, `variable` lines,
      structure fields, `extends` parents and declaration result types
      (pass 1 now records those for every declaration). An unreadable receiver
      falls back to the in-scope `*.Name` candidates; if more than one, the
      use is AMBIGUOUS: counted in `hypothesis_sites_ambiguous` for each,
      credited to none. A receiver of a library type (`Set`, `ℝ`, a type
      variable) resolves only in that namespace. On DG: 8,949 dot uses typed, 62,418 on a library type,
      3,492 untyped with one candidate, 392 untyped and ambiguous.
  N6  The same rule stops twins sharing sites or credit: an ambiguous BARE
      token is now also a site of none of its candidates (it keeps a row
      listed, so no finding is dropped), and `c.projection.ImmersedOn` is no
      longer credited to `ProductCurve.ImmersedOn` because the enclosing
      namespace is `ProductCurve` (#15).
  N3  Statement defs: `def S : Prop := ∀ …, ∃ a : P, …` yields the clause
      `P <= S ∧ (hypotheses in P's scope inside the body)`, one unfolding per
      def; chains of statement defs compose through the fixpoint. Also for
      `abbrev`. Rows #3, 4, 17, 20, 34 name it directly.
  N5  Whole-body match: a declaration whose conclusion contains, as one
      asserted sub-proposition, the BODY of a Prop `abbrev`/`def` (namespace
      prefixes dropped, parameters and bound names as consistent wildcards,
      at least 6 tokens and 3 distinct concrete names) supplies it (#28, #32).
  N1  In-proof constructions are route-2 SUPPLIERS now, not hints:
      `have/let/obtain/suffices … : T`, `show T`, `(e : T)` with `e` not a
      bare binder list, `{ … : T }`, `T.mk`. A construction of a predicate the
      declaration already assumes (in its binders or statement) is closure,
      not supply, and stays a `route2?` hint. The clause body is the
      declaration's hypotheses, so a construction inside a theorem that
      itself needs an unsupplied predicate stays conditional (#14 stays
      unsupplied that way). The site line is the construction's own line.
  N7  Found while checking the above: a conclusion `¬ P` credited P (the old
      crude reading), and so did `P ↔ Q`. `¬ P` now supplies nothing, and
      `A ↔ B` supplies A under B's predicates and B under A's -- and nothing
      when the other side names no project predicate (`P g ↔ ∀ x, …` is an
      unfolding lemma). `∨` is still credited to both sides.
  A   The application form of route 2 (a `fun` passed as an argument, a
      `refine { … }` after `apply T`: #44, #45) is inferred as "the proof
      applies T, which assumes P, and the proof does not assume P" -- and is
      a HINT only (`route2-apply?` in `hint`). Crediting it (54,433 clauses)
      flipped 3 of the 4 reader-confirmed unsupplied predicates to supplied
      (a structure field's type read as a lemma, `.subseq`, a smart
      constructor that itself needs the predicate): the hiding direction.
  P   Two regexes (a nested-quantifier ascription scan and a bound-name scan)
      backtracked catastrophically on long proofs; both are linear now.

The `hint` column names the mechanism that credited a supply (`supplied via
route2-have at F.lean:L`, or `suppliers: concl 3, stmt-def 1` for a row that
is not effective), and `supplied_by` is the clause that fired. Mechanism
labels in `chain` are in brackets. Clauses on DG by mechanism: concl 22,447, route2-have 11,544,
route2-let 2,541, stmt-def 2,024, concl-iff 1,030, route2-show 284, def-body
194, route2-ascription 179, route2-obtain 71, route2-suffices 19, route2-mk 19,
abbrev-body 9, route2-record 1.
Suppliers found this way are CANDIDATE credits as much as the old candidates
were: a `have h : P := sorry` or an `(e : P)` that elaborates to something
else would be credited. The reader-confirmed negatives are the check that
they do not over-credit on this artifact; a sample of 16 newly supplied
predicates outside the 48 read correct.

Remaining disagreements with the reader (3 of 48): #40 is route 4 (a supplied
structure `extends` it), deliberately not credited; #44 and #45 are the
application form above, pointed at by the `route2-apply?` hint. Two reader
details disagree with the source rather than the verdict: #7 is supplied by
`CurveMap.Field.smoothOn_X` (`Connection.lean:131`), not by
`ProductCurve.field_smoothOn_X`, which concludes the `ProductCurve.Field`
twin; and #16's `let X := @SmoothCutCapTransition.mk …` rebuilds a
`∀ X : SmoothCutCapTransition` hypothesis (closure), the supplier being
`BufferedSmoothCutCapTransition.lean:45`.

Newly UNSUPPLIED (were supplied before): the `¬`/`↔`/polarity fixes remove
false credits (`FiniteHorn` was "supplied" by `¬ Nonempty (FiniteHorn g)`;
`IsCanonicalReturningComponent` only ever appears negated), and C1 in
`cone.py` moved some suppliers out of the cone (`datumIsometry`'s only
supplier `datumIsometry.refl` has no use anywhere).
"""

import argparse, collections, csv, os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from safeverifyagent.extract import blank_comments          # noqa: E402
from cone import (decls_with_ns, IDENT, IMPORT, SKIP_DIRS, closures, module_name,  # noqa: E402
                  binder_names, _SID)

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


def _idch(ch):
    return ch.isalnum() or ch in "_'!?."


# `let`/`have` inside a STATEMENT own the next depth-0 `:=` (N4b).
_KW_LET = re.compile(r"(?<![\w'.!?])(?:letI|haveI|let|have)(?![\w'!?])")


def split_sig(body: str):
    """(binder_region, conclusion, proof) -- by bracket depth, not by regex.

    The binder region ends at the FIRST depth-0 `:` (every binder is
    bracketed, so the first depth-0 colon is the signature's), and the
    definition's `:=` is the first depth-0 `:=` after it that no `let`/`have`
    inside the statement owns. See notes N4 and N4b in the module docstring.
    """
    depth, i, n = 0, 0, len(body)
    colon = cut = None
    pending = 0
    while i < n:
        c = body[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0:
            if c == ":" and body.startswith(":=", i):
                if pending:
                    pending -= 1
                    i += 2
                    continue
                cut = i
                break
            if c == ":":
                if colon is None:
                    colon = i
            elif c == "w" and body.startswith("where", i) and (i == 0 or not _idch(body[i - 1])) \
                    and (i + 5 >= n or not _idch(body[i + 5])):
                cut = i
                break
            elif colon is not None and c in "lh" and _KW_LET.match(body, i):
                pending += 1
        i += 1
    sig, proof = (body[:cut], body[cut:]) if cut is not None else (body, "")
    if colon is None:
        return sig, "", proof
    return sig[:colon], sig[colon + 1:], proof


def find_top(s, tok, start=0, stop_nl=False):
    """First index >= start where `tok` occurs at bracket depth 0 relative to
    `start`; None if the enclosing bracket closes first."""
    depth, i, n = 0, start, len(s)
    while i < n:
        c = s[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
            if depth < 0:
                return None
        elif depth == 0:
            if s.startswith(tok, i):
                if not tok[0].isalpha() or ((i == 0 or not _idch(s[i - 1]))
                                            and (i + len(tok) >= n or not _idch(s[i + len(tok)]))):
                    return i
            if stop_nl and c == "\n":
                return None
        i += 1
    return None


def split_top(s, sep):
    out, depth, last, i, n = [], 0, 0, 0, len(s)
    while i < n:
        c = s[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            out.append(s[last:i])
            i += len(sep)
            last = i
            continue
        i += 1
    out.append(s[last:])
    return out


def binder_start(s):
    """Index of the first depth-0 binder (`∀ ∃ Π λ fun let have`), or len(s).
    A binder's scope runs to the end of the enclosing bracket, so `A ∧ ∃ f : X
    → Y, B ∧ C` is `A ∧ (∃ f : X → Y, (B ∧ C))`: the `→` and the second `∧`
    are not top-level connectives of the whole."""
    depth, n = 0, len(s)
    for i, c in enumerate(s):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and i:
            if c in "\u2200\u2203\u03a0\u03bb":
                return i
            if c in "flh" and (not _idch(s[i - 1])) and _BINDER_WORD.match(s, i):
                return i
    return n


_BINDER_WORD = re.compile(r"(?:fun|letI|let|haveI|have)(?![\w'!?])")


def split_scoped(s, sep):
    """`split_top`, but only among the connectives in front of the first
    depth-0 binder (see `binder_start`)."""
    q = binder_start(s)
    parts = split_top(s[:q], sep)
    parts[-1] += s[q:]
    return parts


def match_close(s, i):
    """Index of the bracket closing the opener at `i`, or None."""
    depth = 0
    for j in range(i, len(s)):
        c = s[j]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
            if depth == 0:
                return j
    return None


def strip_parens(s):
    s = s.strip()
    while s.startswith("(") and match_close(s, 0) == len(s) - 1:
        s = s[1:-1].strip()
    return s


_QUANT = re.compile(r"(∀ᶠ|∃ᶠ|∀|∃!|∃|Π)")


def polarize(s):
    """Split a proposition into (neg, pos, units, iffs) by POLARITY (note N4).

    `neg`: text in hypothesis position -- `∀`/`Π` binders and the antecedents
    of `→`. `pos`: `(text, scope)` for what the proposition ASSERTS -- the
    final consequent, each `∧` conjunct, and `∃` witness binders (an `∃ a : P`
    builds a `P`) -- where `scope` is the tuple of `neg` texts it sits under:
    `∃ σ : M, ∀ v : D, Q` supplies M outright and Q only given a D.
    `units`: every positive sub-proposition met on the way down, outermost
    first, for whole-statement matching (note N5). `iffs`: `(A, B, scope)` for
    each asserted `A ↔ B`, which supplies A only given B and B only given A
    (note N7). A `¬ P` asserts nothing about P and yields nothing. `let`/`have`
    bindings in a statement are neither. `∨` stays in `pos`, the crude reading
    the conclusion always had (a disjunction is credited to both)."""
    neg, pos, units, iffs = [], [], [], []
    _polarize(s, (), neg, pos, units, iffs, 0)
    return neg, pos, units, iffs


def _polarize(s, scope, neg, pos, units, iffs, lvl):
    for _ in range(200):
        s = strip_parens(s)
        if not s:
            return
        units.append(s)
        m = _QUANT.match(s)
        if m:
            k = find_top(s, ",", m.end())
            if k is None:
                break
            q = m.group(1)
            if q in ("\u2200", "\u03a0"):
                neg.append(s[m.end():k])
                scope = scope + (s[m.end():k],)
            elif q in ("\u2203", "\u2203!"):
                pos.append((s[m.end():k], scope))
            s = s[k + 1:]
            continue
        m = _KW_LET.match(s)
        if m:
            k = find_top(s, ":=", m.end())
            if k is None:
                break
            e = [x for x in (find_top(s, ";", k + 2), find_top(s, "\n", k + 2)) if x is not None]
            if not e:
                break
            s = s[min(e) + 1:]
            continue
        if s.startswith("\u00ac"):
            return
        parts = split_scoped(s, "\u2194")
        if len(parts) == 2:
            iffs.append((parts[0], parts[1], scope))
            return
        parts = split_scoped(s, "\u2192")
        if len(parts) > 1:
            neg.extend(parts[:-1])
            scope = scope + tuple(parts[:-1])
            s = parts[-1]
            continue
        parts = split_scoped(s, "\u2227")
        if len(parts) > 1 and lvl < 32:
            for p in parts:
                _polarize(p, scope, neg, pos, units, iffs, lvl + 1)
            return
        break
    pos.append((s, scope))


# ---------------------------------------------------------------------------
# LOCALS AND DOT NOTATION (note N2). `(c.X).SmoothOn J` is generalized field
# notation: Lean looks `SmoothOn` up in the namespace of the TYPE of `c.X`,
# never in the enclosing namespace or `open`s. So the receiver's type is
# computed where that is cheap (a binder, a field, a declaration's result
# type), and otherwise the use is AMBIGUOUS, which neither pools a site onto
# every `*.SmoothOn` nor credits one of them as supplied.
# ---------------------------------------------------------------------------
_BIND_OPEN = re.compile(r"[(\[{⦃]\s*((?:%s\s+)*%s)\s*:(?!=)" % (_SID, _SID))
_BIND_Q = re.compile(r"(?:∀|∃!?|Π)\s*((?:%s\s+)*%s)\s*:(?!=)" % (_SID, _SID))
_BIND_HAVE = re.compile(r"(?<![\w'.])(?:have|haveI|let|letI|obtain|set)\s+(%s)\s*:(?!=)" % _SID)


def local_types(text, out=None):
    """{local name: its type text}, first binding wins."""
    out = {} if out is None else out
    for m in _BIND_OPEN.finditer(text):
        e = match_close(text, m.start())
        ty = text[m.end():e] if e is not None else text[m.end():m.end() + 300]
        for nm in m.group(1).split():
            out.setdefault(nm, ty)
    for rx, stop in ((_BIND_Q, ","), (_BIND_HAVE, ":=")):
        for m in rx.finditer(text):
            k = find_top(text, stop, m.end())
            ty = text[m.end():k] if k is not None and k - m.end() < 600 else text[m.end():m.end() + 300]
            for nm in m.group(1).split():
                out.setdefault(nm, ty)
    return out


def type_head(ty):
    """The head identifier of a type: after the last top-level `→`, under
    any leading `∀ … ,`. `ι → ProductCurve Q` has head `ProductCurve`."""
    if not ty:
        return None
    for _ in range(8):
        t = strip_parens(split_top(ty, "→")[-1])
        m = _QUANT.match(t)
        if m:
            k = find_top(t, ",", m.end())
            if k is None:
                return None
            ty = t[k + 1:]
            continue
        t = t.lstrip("@")
        m = IDENT.match(t)
        return m.group(0) if m else None
    return None


def dot_uses(text):
    """[(token, receiver)]: `receiver` is the parenthesised expression text for
    `(e).Name`, the empty string for an unreadable receiver (`x.1.Name`,
    leading-dot `.Name`), and None for an ordinary token."""
    out = []
    for m in IDENT.finditer(text):
        s = m.start()
        if s > 0 and text[s - 1] == ".":
            recv = ""
            if s > 1 and text[s - 2] == ")":
                depth, j = 0, s - 2
                while j >= 0:
                    if text[j] in CLOSERS:
                        depth += 1
                    elif text[j] in OPENERS:
                        depth -= 1
                        if depth == 0:
                            break
                    j -= 1
                if j >= 0:
                    recv = text[j + 1:s - 2]
            out.append((m.group(0), recv))
        else:
            out.append((m.group(0), None))
    return out


# ---------------------------------------------------------------------------
# IN-PROOF CONSTRUCTIONS (note N1): route-2 suppliers.
# ---------------------------------------------------------------------------
_CONSTRUCT_KW = re.compile(r"(?<![\w'.])(have|haveI|let|letI|obtain|suffices|show)(?![\w'!?])")
_COLON = re.compile(r"\s:(?![=:])")
_BARE = re.compile(r"^\s*[^\s.()]+(?:\s+[^\s.()]+)*\s*$")
# tactic words and generic dot-tails that name a project declaration only by
# accident (`refine` -> `HasStageSeed.refine`); shared with cone.py's C1 fix
APPLY_STOP = frozenset("""trans symm mono at mk le lt refl mp mpr cast comp map
    exact apply refine intro intros constructor use exists show have let obtain
    rcases cases induction simp rw calc congr ext funext subst unfold change
    specialize aesop omega linarith positivity norm_num ring field_simp gcongr
    filter_upwards exfalso contradiction trivial rfl decide by fun from with
    left right some none of_eq id""".split())
_MK = re.compile(r"@?(?P<t>%s(?:\.%s)*)\.mk(?![\w'!?])" % (_SID, _SID))


def _type_end(s, i, kw):
    """End of a type that starts at `i`: the depth-0 `:=`, `from`, `by`
    (for `suffices`/`show`), `;`, `<;>`, or a line that is not indented deeper
    than the line the construction starts on."""
    ls = s.rfind("\n", 0, i) + 1
    ind = len(s[ls:]) - len(s[ls:].lstrip(" "))
    depth, j, n = 0, i, len(s)
    while j < n and j - i < 3000:
        c = s[j]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
            if depth < 0:
                return j
        elif depth == 0:
            if s.startswith(":=", j) or c == ";" or s.startswith("<;>", j):
                return j
            if c == "\n":
                k = j + 1
                while k < n and s[k] == " ":
                    k += 1
                if k - j - 1 <= ind and k < n and s[k] != "\n":
                    return j
            if kw in ("suffices", "show") and c in "fb" and (j == 0 or not _idch(s[j - 1])):
                for w in ("from", "by"):
                    if s.startswith(w, j) and (j + len(w) >= n or not _idch(s[j + len(w)])):
                        return j
        j += 1
    return j


def constructions(proof):
    """[(type_text, mechanism, offset)] of every place a proof builds a term
    AT A WRITTEN TYPE: `have/let/obtain/suffices … : T`, `show T`,
    `(e : T)` with `e` not a bare binder list, `{ … : T }`, and `T.mk`."""
    out = []
    for m in _CONSTRUCT_KW.finditer(proof):
        kw = m.group(1)
        if kw == "show":
            st = m.end()
        else:
            k = find_top(proof, ":", m.end(), stop_nl=True)
            if k is None or proof.startswith(":=", k) or k - m.end() > 200:
                continue
            st = k + 1
        e = _type_end(proof, st, kw)
        ty = proof[st:e]
        if ty.strip():
            out.append((ty, "route2-" + kw.rstrip("I"), m.start()))
    # `(e : T)`: from each ` : `, back to the bracket that encloses it (a
    # bounded backward scan; a regex over the whole proof backtracked
    # catastrophically on long proofs)
    for m in _COLON.finditer(proof):
        depth, j = 0, m.start()
        while j >= 0 and m.start() - j < 400:
            c = proof[j]
            if c in CLOSERS:
                depth += 1
            elif c in OPENERS:
                if depth == 0:
                    break
                depth -= 1
            j -= 1
        if j < 0 or m.start() - j >= 400 or proof[j] != "(":
            continue
        e = proof[j + 1:m.start()]
        if not e.strip() or _BARE.match(e) or "\n" in e.strip():
            continue
        pre = proof[max(0, j - 12):j]
        if re.search(r"(?:fun|\u03bb|\u2200|\u2203|\u03a0)\s*$", pre):
            continue
        close = match_close(proof, j)
        if close is None:
            continue
        out.append((proof[m.end():close], "route2-ascription", j))
    i = proof.find("{")
    while i >= 0:
        close = match_close(proof, i)
        if close is not None and close - i < 6000:
            body = proof[i + 1:close]
            k = None
            parts = split_top(body, ":")
            if len(parts) > 1:
                # the last depth-0 `:` that is not part of `:=`
                acc = 0
                for p in parts[:-1]:
                    acc += len(p) + 1
                    if not body.startswith(":=", acc - 1):
                        k = acc - 1
            if k is not None and find_top(body, ":=") is not None and find_top(body, ":=") < k:
                ty = body[k + 1:]
                between = body[:k].rsplit(":=", 1)[-1]
                if ":=" not in ty and not re.search(r"(?:fun|λ|∀|∃)\b|↦|=>", between) \
                        and "|" not in ty and "//" not in ty:
                    out.append((ty, "route2-record", i))
        i = proof.find("{", i + 1)
    for m in _MK.finditer(proof):
        out.append((m.group("t"), "route2-mk", m.start()))
    return out


# ---------------------------------------------------------------------------
# WHOLE-STATEMENT MATCHING (note N5): a Prop `abbrev`/`def` is supplied by a
# declaration that states its unfolded BODY.
# ---------------------------------------------------------------------------
_NTOK = re.compile(r"%s|\d+|\S" % IDENT.pattern)
_BOUND = re.compile(r"(?:\u2200|\u2203!?|fun|\u03bb|\u03a0)\s*\(?\s*(%s(?:\s+%s)*)" % (_SID, _SID))


def norm_tokens(text, wild=()):
    """Token sequence with namespace prefixes dropped (`Metric.closedBall` ->
    `closedBall`), dotted locals split (`δ.chart` -> `δ . chart`), and the
    names in `wild` plus every name bound inside `text` turned into `?name`."""
    bound = set(wild)
    for m in _BOUND.finditer(text):
        bound.update(m.group(1).split())
    out = []
    for m in _NTOK.finditer(text):
        t = m.group(0)
        if IDENT.fullmatch(t):
            parts = t.split(".")
            while len(parts) > 1 and parts[0][:1].isupper() and parts[0] not in bound:
                parts = parts[1:]
            for j, p in enumerate(parts):
                if j:
                    out.append(".")
                out.append("?" + p if p in bound else p)
        else:
            out.append(t)
    return out


def match_tokens(pat, toks):
    """Whole-sequence match; `?x` in `pat` binds one identifier consistently."""
    if len(pat) != len(toks):
        return False
    env = {}
    for a, b in zip(pat, toks):
        if a.startswith("?") and len(a) > 1:
            if b == "." or not (b[0].isalpha() or b[0] in "_?"):
                return False
            if env.setdefault(a, b) != b:
                return False
        elif a != b:
            return False
    return True


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

    # ---- pass 1: every declaration's name and result-type head (for dot
    # notation), candidate predicates, structure fields and parents,
    # inductive constructors, and the bodies of Prop-valued defs
    preds, declared_at, shape = {}, {}, {}
    pred_files = collections.defaultdict(set)
    all_files = collections.defaultdict(set)
    decl_ret, field_ret = {}, {}
    parents_raw = collections.defaultdict(list)
    fctx = [()] * nf
    body_pats = collections.defaultdict(list)   # token count -> [(A, pattern)]
    mod_idx = {module_name(rel): i for i, rel in enumerate(files)}
    imports = [[] for _ in files]
    raw_fields = []      # (structure, ctx, [type text])
    raw_ctors = []       # (inductive, ctx, rel, line, [ctor text])

    def ret_entry(h, locs):
        parts = h.split(".")
        if len(parts) > 1 and parts[0] in locs:
            head = type_head(locs[parts[0]])
            if head:
                return ("dot", head, tuple(parts[1:]))
            return None
        return ("name", h)

    for fi, rel in enumerate(files):
        txt = read(rel)
        fctx[fi] = file_ctx(txt)
        imports[fi] = sorted({mod_idx[m] for m in IMPORT.findall(txt) if m in mod_idx})
        flocs = {}
        for m in VARIABLE.finditer(txt):
            local_types(m.group("rest"), flocs)
        for full, kind, line, body in decls_with_ns(txt):
            all_files[full].add(fi)
            hb = strip_header(body)
            fp = full.split(".")
            ns = tuple(".".join(fp[:k]) for k in range(len(fp) - 1, 0, -1))
            if kind == "inductive":
                # the signature ends where the constructors begin; otherwise the
                # last `:` is a constructor's and the type reads as its result
                hb = re.split(r"\n[ \t]*\||\bwhere\b", hb, maxsplit=1)[0]
            _b, concl, rest = split_sig(hb)
            if kind not in ("structure", "class", "inductive") and concl.strip() \
                    and full not in decl_ret:
                h = type_head(concl)
                if h:
                    e = ret_entry(h, local_types(_b, dict(flocs)))
                    if e:
                        decl_ret[full] = (e, fi, ns)
            if kind not in PRED_KINDS:
                continue
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
            ctx = tuple(".".join(fp[:j + 1]) for j in range(len(fp)))
            if kind in ("structure", "class"):
                slocs = local_types(_b, dict(flocs))
                fields = struct_fields(body)
                for fname, ftype in fields:
                    h = type_head(ftype)
                    e = ret_entry(h, slocs) if h else None
                    if e:
                        field_ret.setdefault(f"{full}.{fname}", (e, fi, (full,) + ns))
                types = [t for _n, t in fields]
                m = EXTENDS.search(hb.split(":=", 1)[0])
                if m:
                    types.append(m.group("rest"))
                    for par in split_top(m.group("rest"), ","):
                        h = type_head(par)
                        if h:
                            parents_raw[full].append((h, fi, (full,) + ns))
                raw_fields.append((full, ctx + fctx[fi], fi, types))
            elif kind == "inductive":
                ctors = [(c.group(1), c.group("rest")) for c in CTOR.finditer(body)]
                raw_ctors.append((full, ctx + fctx[fi], fi, rel, line, ctors))
            elif sh in ("predicate", "prop_inferred") and rest.startswith(":="):
                bt = re.sub(r"^\s*by\s+exact\b", "", rest[2:])
                if not bt.lstrip().startswith("by"):
                    wild = binder_names(_b) | set(flocs)
                    pat = norm_tokens(strip_parens(bt), wild)
                    conc = [t for t in pat if t[:1].isalpha() and not t.startswith("?")]
                    if len(pat) >= 6 and len(set(conc)) >= 3:
                        body_pats[len(pat)].append((full, pat))
        if (fi + 1) % 2000 == 0:
            progress(f"[nosupplier] pass 1: {fi + 1:,}/{nf:,} files")

    suffix = collections.defaultdict(set)
    for full in preds:
        parts = full.split(".")
        for j in range(len(parts)):
            suffix[".".join(parts[j:])].add(full)
    short_count = collections.Counter(p.rsplit(".", 1)[-1] for p in preds)
    all_suffix = collections.defaultdict(list)
    for full in all_files:
        parts = full.split(".")
        for j in range(len(parts)):
            all_suffix[".".join(parts[j:])].append(full)

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

    # ---- dot notation (note N2): the receiver's TYPE names the namespace.
    scache = {}

    def sres(tok, fi, ns):
        """Static (import-scope-free) resolution of a type or function name to
        one declaration: innermost namespace first, then the root, then the
        declaring file's `namespace`/`open` context. None unless unique."""
        key = (tok, fi, ns)
        if key in scache:
            return scache[key]
        cand = all_suffix.get(tok, ())
        r = None
        if len(cand) == 1:
            r = cand[0]
        elif cand:
            for p in ns:
                if f"{p}.{tok}" in all_files:
                    r = f"{p}.{tok}"
                    break
            else:
                if tok in all_files:
                    r = tok
                else:
                    hit = {c for c in cand if any(c == f"{p}.{tok}" for p in fctx[fi])}
                    r = next(iter(hit)) if len(hit) == 1 else None
        scache[key] = r
        return r

    lcache = {}

    def lineage(T):
        """T and the structures it `extends`, transitively."""
        r = lcache.get(T)
        if r is None:
            r, seen, q = [], {T}, [T]
            while q and len(r) < 16:
                x = q.pop(0)
                r.append(x)
                for h, fi2, ns2 in parents_raw.get(x, ()):
                    y = sres(h, fi2, ns2)
                    if y and y not in seen:
                        seen.add(y)
                        q.append(y)
            lcache[T] = r
        return r

    def name_in(T, f):
        for X in lineage(T):
            if f"{X}.{f}" in all_files:
                return f"{X}.{f}"
        return None

    ecache = {}

    def static_entry(ent, depth=0):
        if ent is None or depth > 6:
            return None
        key = (ent, depth)
        if key in ecache:
            return ecache[key]
        (e, fi2, ns2) = ent
        if e[0] == "name":
            r = sres(e[1], fi2, ns2)
        else:
            r = sres(e[1], fi2, ns2)
            for f in e[2][:-1]:
                r = member(r, f, depth + 1) if r else None
            r = name_in(r, e[2][-1]) if r else None
        ecache[key] = r
        return r

    def member(T, f, depth=0):
        """Type of `x.f` for `x : T` -- a field or a declaration `T.f`."""
        if T is None:
            return None
        for X in lineage(T):
            nm = f"{X}.{f}"
            if nm in field_ret:
                return static_entry(field_ret[nm], depth + 1)
            if nm in decl_ret:
                return static_entry(decl_ret[nm], depth + 1)
        return None

    class Ctx:
        """Resolution context of one declaration: file, namespaces, locals."""
        __slots__ = ("ctx", "fi", "ns", "locs", "memo")

        def __init__(self, ctx, fi, ns, locs):
            self.ctx, self.fi, self.ns, self.locs, self.memo = ctx, fi, ns, locs, {}

    def rtype(expr, C, depth=0):
        """Declared type (full name) of a receiver expression, or None."""
        if depth > 4:
            return None
        m = IDENT.match(expr.strip().lstrip("@(↑ "))
        if not m:
            return None
        parts = m.group(0).split(".")
        if parts[0] in C.locs:
            T, rest = tfull(C.locs[parts[0]], C, depth + 1), parts[1:]
        else:
            T, rest = None, []
            for k in range(len(parts), 0, -1):
                g = sres(".".join(parts[:k]), C.fi, C.ns)
                if g:
                    T, rest = static_entry(decl_ret.get(g)), parts[k:]
                    break
        for f in rest:
            T = member(T, f) if T and not T.startswith("~") else None
        return T

    def tfull(ty, C, depth=0):
        h = type_head(ty)
        if not h or depth > 4:
            return None
        parts = h.split(".")
        if len(parts) > 1 and parts[0] in C.locs:
            R = rtype(".".join(parts[:-1]), C, depth + 1)
            return name_in(R, parts[-1]) if R and not R.startswith("~") else None
        r = sres(h, C.fi, C.ns)
        if r is None and h not in all_suffix:
            # no project declaration has this name at all: a library type
            # (`Set`, `ℝ`) or a type variable. Marked, so a dot use on it is
            # looked up in THAT namespace only and never falls back to a
            # same-named project predicate.
            return "~" + h
        return r

    stats = collections.Counter()

    def resolve_text(text, C):
        """[(candidates, ambiguous, dot)] per distinct token use in `text`.
        `ambiguous` means more than one candidate survived: such a use is a
        site of NONE of them (it is counted apart) and supplies none."""
        out = []
        for tok, recv in set(dot_uses(text)):
            key = (tok, recv)
            got = C.memo.get(key)
            if got is None:
                parts = tok.split(".")
                name, rexpr, mem = None, None, ()
                if recv is not None:
                    # `(e).a.b`: `a` is a member of e's type, `b` is looked up in a's
                    name, rexpr, mem = parts[-1], recv, parts[:-1]
                elif len(parts) > 1 and parts[0] in C.locs:
                    name, rexpr = parts[-1], ".".join(parts[:-1])
                if name is None:
                    r = resolve(tok, C.ctx, C.fi, C.ns)
                    got = (r, len(r) > 1, False)
                else:
                    T = rtype(rexpr, C) if rexpr else None
                    for f in mem:
                        T = member(T, f) if T and not T.startswith("~") else None
                    r = frozenset()
                    if T:
                        for X in ([T[1:]] if T.startswith("~") else lineage(T)):
                            if f"{X}.{name}" in preds:
                                r = frozenset([f"{X}.{name}"])
                                break
                    if r:
                        stats["dot_typed"] += 1
                        got = (r, False, True)
                    elif T and T.startswith("~"):
                        stats["dot_library_type"] += 1
                        got = (frozenset(), False, True)
                    else:
                        r = resolve(name, (), C.fi, ())
                        if r:
                            stats["dot_untyped_ambiguous" if len(r) > 1 else "dot_untyped_unique"] += 1
                        got = (r, len(r) > 1, True)
                C.memo[key] = got
            out.append(got)
        return out

    def split_res(res):
        """(all candidates, unambiguous singletons, ambiguous candidates)"""
        allc, una, amb = set(), set(), set()
        for r, a, _d in res:
            allc |= r
            if a:
                amb |= r
            elif len(r) == 1:
                una |= r
        return allc, una, amb

    # ---- pass 2: hypothesis sites, suppliers (as clauses), in-proof
    # constructions, statement-def unfolding and whole-body matches
    hyp = collections.defaultdict(list)       # P -> [(rel, line, kind, in_cone)]
    hyp_amb = collections.defaultdict(list)   # P -> sites where P was one of several
    sup = collections.defaultdict(list)       # P -> [(rel, line, mechanism, in_cone)]
    clauses = []                              # (P, body, label, in_cone)
    asc = collections.defaultdict(list)
    unmatched = 0
    mech_n = collections.Counter()

    def add_supplier(P, body, rel, ln, mech, on):
        sup[P].append((rel, ln, mech, on))
        clauses.append((P, frozenset(body - {P}), f"{rel}:{ln} [{mech}]", on))
        mech_n[mech.split(" ", 1)[0]] += 1

    decl_hyp = {}
    apps = []
    sncache = {}

    def scoped_name(t, prefixes, fi):
        """The declaration `t` names by its full spelling or under one of the
        declaration's namespaces / the file's `open`s, in import scope."""
        key = (t, prefixes, fi)
        if key in sncache:
            return sncache[key]
        if fi != cur["fi"]:
            resolve("", (), fi)            # switch the scope bitset to this file
        bits = cur["bits"]
        r = None
        for c in [t] + [f"{p}.{t}" for p in prefixes]:
            fs = all_files.get(c)
            if fs and any(bits[m >> 3] >> (m & 7) & 1 for m in fs):
                r = c
                break
        sncache[key] = r
        return r

    def iff_clauses(iffs, C, excl, body, rel, ln, mech, on):
        """`A ↔ B` supplies A under B and B under A (note N7) -- and only when
        the other side names a project predicate to condition on: `P g ↔ ∀ x,
        <library statement>` is an unfolding lemma, not a proof that P holds."""
        for A, B, scope in iffs:
            ra, rb = split_res(resolve_text(A, C)), split_res(resolve_text(B, C))
            for x, y in ((ra, rb), (rb, ra)):
                if not y[1]:
                    continue
                for P in x[1]:
                    if P not in excl and P not in y[0]:
                        add_supplier(P, body | y[1] | scope_una(scope, C), rel, ln,
                                     mech + "-iff", on)

    def scope_una(scope, C):
        """Unambiguous predicates among the hypotheses an asserted item sits
        under (the `scope` of a `polarize` item)."""
        if not scope:
            return frozenset()
        key = ("\x00scope",) + scope
        got = C.memo.get(key)
        if got is None:
            got = frozenset(split_res(resolve_text("\n".join(scope), C))[1])
            C.memo[key] = got
        return got

    def credit_pos(pos, C, excl, body, rel, ln, mech, on, hint=None):
        """Supplier clauses for the asserted items of a statement: each is
        credited under `body` plus the hypotheses in its own scope."""
        for text, scope in pos:
            for r, a, _d in resolve_text(text, C):
                for P in r:
                    if P in excl:
                        if hint is not None and not a:
                            hint(P)
                        continue
                    if a or len(r) != 1:
                        if hint is not None:
                            hint(P)
                        continue
                    add_supplier(P, body | scope_una(scope, C), rel, ln, mech, on)

    for fi, rel in enumerate(files):
        txt = read(rel)
        ctx = fctx[fi]
        file_in_cone = rel in cone_files
        flocs = {}
        vblocks = []
        for m in VARIABLE.finditer(txt):
            local_types(m.group("rest"), flocs)
            vblocks.append((txt.count("\n", 0, m.start()) + 1, m.group("rest")))
        # section `variable` lines are hypotheses in scope for the whole file
        VC = Ctx(ctx, fi, (), flocs)
        for ln, rest in vblocks:
            res = resolve_text(rest, VC)
            for r, a, _d in res:
                for P in r:
                    (hyp_amb if a else hyp)[P].append((rel, ln, "variable", file_in_cone))
        for full, kind, line, body in decls_with_ns(txt):
            if args.cone:
                on = cone_at.get((rel, line))
                if on is None:
                    unmatched += 1
                    on = False
            else:
                on = False
            hb = strip_header(body)
            binders, concl, proof = split_sig(hb)
            neg, pos, units, iffs = polarize(concl) if concl.strip() else ([], [], [], [])
            fp = full.split(".")
            ns = tuple(".".join(fp[:k]) for k in range(len(fp) - 1, 0, -1))
            locs = dict(flocs)
            local_types(binders, locs)
            local_types(concl, locs)
            C = Ctx(ctx, fi, ns, locs)
            # hypotheses: the binder region AND the negative positions of the
            # statement (`∀ h : P, …`, `P → …`) -- the same thing to Lean
            hres = resolve_text(binders, C)
            buna = split_res(hres)[1]
            if neg:
                hres = hres + resolve_text("\n".join(neg), C)
            bres, unamb, _amb = split_res(hres)
            for r, a, _d in hres:
                for P in r:
                    if P != full:
                        (hyp_amb if a else hyp)[P].append((rel, line, kind, on))
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
            credit_pos(pos, C, bres | {full}, buna, rel, line, "concl", on)
            iff_clauses(iffs, C, bres | {full}, buna, rel, line, "concl", on)
            # N5: a declaration stating a Prop def/abbrev's BODY supplies it
            for u in units if body_pats else ():
                toks = norm_tokens(u)
                cands = body_pats.get(len(toks))
                if not cands:
                    continue
                for A, pat in cands:
                    if A != full and A not in bres and match_tokens(pat, toks):
                        add_supplier(A, unamb, rel, line,
                                     f"{preds[A]}-body {A.rsplit('.', 1)[-1]}", on)
            # N3: `def S : Prop := ∀ …, ∃ a : P, …` -- S supplies what its body
            # asserts, under what its body assumes
            if full in preds and preds[full] in ("def", "abbrev") \
                    and shape[full] in ("predicate", "prop_inferred") and proof.startswith(":="):
                bt = re.sub(r"^\s*by\s+exact\b", "", proof[2:])
                if not bt.lstrip().startswith("by"):
                    n2, p2, _u2, i2 = polarize(bt)
                    local_types(bt, C.locs)
                    nall = split_res(resolve_text("\n".join(n2), C))[0] if n2 else set()
                    mech = f"stmt-def {full.rsplit('.', 1)[-1]}"
                    credit_pos(p2, C, nall | {full}, frozenset([full]), rel, line, mech, on)
                    iff_clauses(i2, C, nall | {full}, frozenset([full]), rel, line, mech, on)
            decl_hyp.setdefault(full, frozenset(unamb))
            # N1 (application form): a proof that APPLIES a theorem T with a
            # hypothesis P it does not itself assume must have built a P
            # somewhere -- a `fun` passed as the argument, a `refine { … }`
            # after `apply T`. Resolved later, once every T's hypotheses are
            # known; only by full name or namespace/`open` context, never by
            # bare suffix (the cone's C1 bug), and never a tactic word.
            if proof and len(proof) > 2:
                seen_t = set()
                for m in IDENT.finditer(proof):
                    t = m.group(0)
                    if t in seen_t or t in APPLY_STOP or (m.start() and proof[m.start() - 1] == "."):
                        continue
                    seen_t.add(t)
                    if t.split(".", 1)[0] in C.locs:
                        continue
                    T = scoped_name(t, ns + ctx, fi)
                    if T and T != full:
                        apps.append((T, bres, unamb, rel, line, on, full))
            # N1: route-2 constructions inside the proof
            if proof and len(proof) > 2:
                cons = constructions(proof)
                if cons:
                    local_types(proof, C.locs)
                    base = len(body) - len(proof)
                for ty, mech, off in cons:
                    n3, p3, _u3, i3 = polarize(ty)
                    nall3 = split_res(resolve_text("\n".join(n3), C))[0] if n3 else set()
                    ln = line + body.count("\n", 0, base + off)
                    # ambiguous, or closure of something the declaration
                    # already assumes: a hint only
                    credit_pos(p3, C, bres | nall3 | {full}, unamb, rel, ln, mech, on,
                               hint=lambda P, _s=f"{rel}:{ln}": asc[P].append(_s)
                               if P != full else None)
                    if i3:
                        iff_clauses(i3, C, bres | nall3 | {full}, unamb, rel, ln, mech, on)
        if (fi + 1) % 2000 == 0:
            progress(f"[nosupplier] pass 2: {fi + 1:,}/{nf:,} files")

    # A HINT, not a supplier: measured on differential-geometry, crediting it
    # flipped 3 of the 4 reader-confirmed UNSUPPLIED predicates to supplied
    # (a structure field's type named as a "theorem", `.subseq`, a smart
    # constructor that itself needs the predicate), which is the direction
    # that hides a finding. It still recovered both application-only suppliers
    # the reader found, so it is kept as a pointer, preferring in-cone sites.
    apply_hint = collections.defaultdict(list)
    for T, bres_d, unamb_d, rel, line, on, full in apps:
        for P in decl_hyp.get(T, ()):
            if P not in bres_d and P != full:
                apply_hint[P].append((not on, f"{rel}:{line} via {T.rsplit('.', 1)[-1]}"))

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
            clauses.append((ind, frozenset(body), f"{rel}:{line} [ctor {cname}]", on))

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

    eff, why = fixpoint([(h, b, l) for h, b, l, _o in clauses], preds)
    by_head = collections.defaultdict(list)
    for h, b, l, _o in clauses:
        by_head[h].append((h, b, l))
    for h in by_head:
        by_head[h].sort(key=lambda c: len([x for x in c[1] if x not in eff]))
    if args.cone:
        cl_in = [(h, b, l) for h, b, l, o in clauses if o]
        eff_in, why_in = fixpoint(cl_in, preds)
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
    WHY = why_in if args.cone else why

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
        ha = hyp_amb.get(P, [])
        h_in = sum(1 for x in h if x[3])
        ha_in = sum(1 for x in ha if x[3])
        s_in = sum(1 for x in s if x[3])
        sites = h_in if args.cone else len(h)
        sites_amb = ha_in if args.cone else len(ha)
        if P in E:
            status = "supplied"
        elif not s:
            status = "no_supplier"
        elif args.cone and s_in == 0:
            status = "no_supplier_in_cone"
        else:
            status = "conditional"
        # an ambiguous use is a site of none of its candidates (note N2) but
        # still keeps a row listed: dropping it would hide a finding
        keep = sites + sites_amb >= args.min_hyp and (
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
        # which MECHANISM credited the supply (a reader checks that one first)
        mechs = collections.Counter(re.sub(r" .*", "", x[2]) for x in s
                                    if (x[3] or not args.cone))
        if status == "supplied":
            fired = WHY.get(P, "")
            mech_txt = "supplied via " + fired.split(" [", 1)[-1].rstrip("]") + \
                " at " + fired.split(" [", 1)[0] if " [" in fired else "supplied"
        elif mechs:
            mech_txt = "suppliers: " + ", ".join(f"{k} {v}" for k, v in mechs.most_common())
        else:
            mech_txt = ""
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
            "hint": "; ".join(x for x in (verdict, "route2?" if hints else "", mech_txt,
                                          ("route2-apply? " + min(apply_hint[P])[1])
                                          if status != "supplied" and apply_hint.get(P) else "")
                              if x),
            "example_sites": "; ".join(f"{a}:{b}" for a, b, _k, _o in
                                       (sorted(h, key=lambda x: not x[3]) if args.cone else h)[:4]),
            "example_suppliers": "; ".join(f"{a}:{b}" for a, b, _k, _o in s[:3]),
            "hypothesis_sites_ambiguous": len(ha),
            "hypothesis_sites_ambiguous_in_cone": ha_in if args.cone else "",
            "supplied_by": WHY.get(P, "") if status == "supplied" else "",
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
    print("supplier clauses by mechanism: " + ", ".join(f"{k} {v:,}" for k, v in mech_n.most_common()))
    print("dot-notation uses: " + ", ".join(f"{k} {v:,}" for k, v in sorted(stats.items())))
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
