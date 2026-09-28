"""Which theorems divide by something the signature never says is nonzero?

Mathlib defines `x / 0 = 0` and `(0 : R)inv = 0`. So a theorem stated about a
quantity with an UNCONSTRAINED denominator silently degenerates when that
denominator is zero: the whole channel becomes 0 and the statement collapses to
`0 = 0`. It is never FALSE -- it just stops saying anything, and no type records
that. Two instances were found by hand in one block of the NSE audit:

  * `PeriodicPhaseAssembly.transportPhase` carries `Kr / K`; the EIGHT theorems
    stated without `K != 0` (:492,499,508,520,535,567,722,734) degenerate at
    K = 0 -- including `:734`, which advertises "exact values on the entire
    sampling interval".
  * `BasePrefixIdentity`'s swirl channel runs through `C inv` (:119,:255) with
    `C : R` unconstrained in EVERY signature (:86,112,133,158,237,262).

In both cases the degenerate value is excluded ONE LAYER UP by a caller, so this
is a statement-hygiene defect, not a soundness one. That is exactly why it needs
a mechanical pass: reading the theorem alone cannot reveal it, and reading the
caller is a different file.

    python3 audits/junkvalue.py /path/to/lean-project [-o OUT.csv] [--all-conclusions]

SCOPE, deliberately narrow. Only flags a denominator that is a SINGLE IDENTIFIER
bound in the same signature as a bare scalar (`(K : R)`, `{C : R}`), with no
nonzero constraint derivable from that signature (see the numbered changes
below for what "derivable" now covers). That is the shape of both known
instances. Deliberately NOT flagged:

  * numeric literals (`/ 2`) -- never zero;
  * projections (`s.epsilon n`, `A.ell`) -- these are usually certified by the
    STRUCTURE, e.g. `StripData` carries `epsilon_pos : forall n, 0 < epsilon n`
    (WeightedClasses.lean:35) and `ParentPacketFrames` carries `ell_pos`. A
    worker's claim that an `epsilon` division was unguarded was REFUTED exactly
    this way, so flagging projections would reproduce a known false positive;
  * compound expressions -- too noisy to be actionable.

So this UNDER-reports on purpose. A hit is a statement worth one grep; a miss is
not a clean bill of health.

OUTPUT columns: `file,line,decl,denominator,class_hint,statement`.
`class_hint` pre-sorts a reader's C/D split (change 11): `exact-value` when the
conclusion is an equation whose sides mention the quantity (the denominator, or
the hiding definition for a "(via X)" row), `property` otherwise.

BEHAVIOUR CHANGES after the differential-geometry triage (JUNKVALUE-TRIAGE.md,
290 rows read, 117 classed B = scanner false positive, patterns P1-P12).

Measured on differential-geometry @ 7a48598d. Baseline (the scanner before these
changes): 617 rows. Now: 177 rows (54 statement-level, 123 "via"), and 339 with
`--all-conclusions`. `--ablate KEY[,KEY...]` switches changes off for
measurement; switching ALL of them off (`P1,P2,P3,P4,P6,P7,P8,P9,P12,NZ`)
reproduces the 617-row CSV exactly, row for row. "+n" below is the rows that come
back when that ONE change is switched off from the final scanner; "-n" the rows
that change ADDS (a guard read too generously before, or a real argument found
by position). Changes overlap, so the numbers do not sum to 617 - 177.
Of the 117 reader-classified B rows, 116 are no longer emitted (the one left
is P5, below).

   1. [P4] preimage `f ⁻¹' S` is not an inverse (`INV` refuses a trailing `'`).
      +4 (PrismMap:196, IntervalCompletionSpace:53, SmoothCompletionCharts:20,96).
   2. [P6] `/ Real.sin u` is a qualified name, not a division by `Real`
      (`DIV`/`INV` refuse an identifier continued by `.`, and `INV` one preceded
      by `.`, so `N.scale⁻¹` is a projection too). A scalar binder must be a
      binder: identifiers only before the colon, and the bracket must open a
      binder group (start of signature, after a closing bracket, or after
      `∀`/`∃`/`fun`/`λ`/`Π`) -- `(-Real.cos u / Real.sin u : ℝ)` and
      `(B v t / B t t : ℝ)` are ascriptions. Names are matched as whole tokens,
      which also FIXES a miss: `\bε'\b` never matched a primed binder.
      +5 (Transitivity:130,155,253 on `Real`, GradientRegularity:51 on `B`, and
      `enlarge_constants` read `C2` inside `{C1' C2' : ℝ}`); -5 (primed
      binders: ModelHandle:4367,4638,4651, LayerAffineMap:170 twice).
   3. [P8] a `by` block is a proof, not part of a value. A `by` inside a term is
      blanked to its enclosing bracket or a depth-0 comma; for a definition
      whose value is `:= by ...` only its `have`/`obtain`/`suffices`/`show`/
      `calc`/`rcases` steps are blanked, because `let`/`exact`/`refine` still
      build the value (blanking the whole block hid two reader-A hits,
      CylinderCapRounding:28,44). Also applied to statements. +3.
   4. [P9] a division under an `if` branch that excludes the zero is not a junk
      site: `if q = 0 then r else sinh (q*r) / q`, `if r ≤ 0 then 0 else
      exp (-1/r)`, `if (4/3 : ℝ) ≤ s then 2 / s - 2 else ...`,
      `if h : q ≠ 0 then ... / q`. A disjunctive condition guards the else
      branch, a conjunctive one the then branch. Applied to definition bodies
      and to statements. +40. NOTE: this removes `diffQuot`
      (`if h = 0 then 0 else (...) / h`, DifferenceQuotient.lean:15) as a hiding
      definition altogether -- 136 of the 617 baseline rows were "via diffQuot",
      and 6 reader-C rows (SubstitutionNonSmoothChartBilinear:710,
      DifferenceQuotient:115, TestFunction/Sobolev:153,
      DifferenceQuotientProductWeakLimit:36, TestFunction/Integration:26,163)
      go on this change alone. Its value at h = 0 is 0 BY DEFINITION, not by
      junk arithmetic, which is what the pattern says.
   5. [P7] a definition that guards its own parameter is not risky: the same
      nonzero test (changes 6, 7 and 13 included) runs on the definition's
      binders (`FlowTo.scale ... (hc : 0 < c)`), and a Prop-valued definition
      whose body has a depth-0 conjunct `0 < d` guards `d`. +0 alone: its 8
      triage rows are all also P1 collisions or P8 proof-only divisions.
   6. [P3] structure-field guard. One pass over the project builds the table of
      structures (and classes) with a field `name : 0 < p` / `p ≠ 0` / `p > 0` /
      `k ≤ p` on an EXPLICIT parameter `p`. A binder `(N : NormalizedNeck g δ k)`,
      also `∀ W : S ..., ` or `(N : ∀ n, S (g n) (eps n) (k n))`, then makes the
      argument at that position positive (by POSITION, not by name); under a
      `∀ i,` every instance `eps p` of `eps i` is positive. A field
      `scale_pos : 0 < scale` makes `N.scale` positive. When two structures
      share a short name, a position counts only if every one of them guards it.
      +21 alone (and 19 more reader-B rows are also non-equalities, change 10).
   7. [P2, P10] one step of order chaining over the signature. Seeds: `0 < t`,
      `t > 0`, `k ≤ t`/`k < t` with a positive literal, and change 6. Nonneg:
      `0 ≤ t` plus the seeds. Then `A ≤ x`, `A < x`, `x ≥ A`, `x > A`, `c * A ≤ x`
      with A positive, or `A < x` with A nonneg, make x positive; `A < x⁻¹` with A
      nonneg, `A ≤ x⁻¹` with A positive, and `0 < x⁻¹` make x positive (P10). A
      side with an arithmetic operator next to it does not count
      (`a - l ≤ r` says nothing of r). ONE step only. +20 (ablation key `P2`).
   8. [P1] a hiding definition is resolved, not matched by short name. A
      reference in a conclusion counts only if (a) the bare name is not a local
      binder of the theorem and the definition's namespace is an ancestor of
      the theorem's (or is opened anywhere in the file, or is the root), (b) a
      qualified name is a namespace-relative suffix of the definition's full
      name, or (c) dot notation `F.scale` has a receiver `F` whose binder type
      head is the definition's namespace (`F : FlowTo ..` for `FlowTo.scale`;
      `N.scale` with `N : NormalizedNeck ..` is a field, and
      `u.steklovAverage` with `u : timeL2 ..` is `timeL2.steklovAverage`, not
      the dividing `Lp` one). A `private` definition is never matched outside
      its file.
   9. [P1] a hiding definition's parameter is mapped by ARGUMENT POSITION at the
      call site (explicit parameters; dot notation fills the first explicit
      parameter of the receiver's type; `@f` counts every parameter). The
      argument must be a single identifier (compound arguments follow the
      "compound expressions" rule above), and the denominator column now names
      the THEOREM's identifier, not the definition's parameter. An implicit
      risky parameter, and a definition whose text names a
      `variable`-bound identifier (an explicit `variable` can shift positions),
      fall back to the old by-name match. Changes 8+9 (key `P1`): +18, -9 (the
      9 are real arguments the by-name match could not see, e.g.
      `neckBuffer ε` where the definition's parameter is called δ:
      NeckRebaseStability:562,1073, PointwiseChart:21,65,93).
  10. [P12] mode 2 (theorems that USE a dividing definition) now applies the
      same equality-conclusion filter as mode 1. `--all-conclusions` restores
      the old behaviour (mode 2 unfiltered; mode 1 has always been filtered).
      +162, the largest single effect, as the triage predicted (160 of its 260
      mode-2 rows were non-equalities).
  11. `class_hint` column (see OUTPUT above). Under `--all-conclusions` the 290
      triaged rows split A 44 exact-value / 28 property, C 32 / 41, B 1 / 3
      (rows still emitted): it pre-sorts properties out, it does NOT separate
      a C identity from an A exact value -- that needs the caller.
  12. The signature splitter is vendored (a frozen copy of
      `nosupplier.split_sig` @ a83e437: last depth-0 colon) instead of imported,
      so this scanner's numbers do not move when another instrument's parser is
      edited. Measured: the pre-change scanner run against an in-progress
      first-colon `split_sig` emitted 744 rows instead of 617 (the conclusion
      then includes `∀ x : T,` binders and `let` bodies). Adopting that split
      here is a separate decision, with its own triage.
  13. [NZ] NONZERO patterns use real token boundaries. `\b` after a primed
      name (`0 < ε'`) never matched, so every primed guard was invisible; with
      no LEFT boundary `r ≠ 0` matched inside `hr ≠ 0` / `x - r ≠ 0`, and
      `1 ≤ δ` inside `ε⁻¹ + 1 ≤ δ⁻¹`. A literal may be a fraction
      (`7 / 4 ≤ ρ`, `(1 : ℝ) / 2 ≤ c`, `(4 / 3 : ℝ) ≤ s`), which the old
      pattern accepted only by reading its denominator. `x * r ≠ 0` and
      `x / r ≠ 0` still guard r. +1, -1 (RecenteringChart:76 now also flags
      δ, whose only "guard" was `ε⁻¹ + 1 ≤ δ⁻¹`).

KNOWN MISSES, still false positives (documented, not fixed):

  * P5 -- nonzero forced by an equation: `hac : a ≠ c` with
    `hx : c + α/2‖x‖² = a` forces α ≠ 0 (QuadraticLevelScaling.lean:103). Not
    syntactic; the ONE reader-B row still emitted.
  * P11 -- a nonempty open interval: `p.1 ∈ Ioo (R - h) R` forces h > 0
    (AnnulusEnergy.lean:60). Not implemented; that row is gone only because its
    conclusion is not an equation (change 10).
  * Transitivity deeper than one step, a guard on a compound
    (`eps p + 1 ≤ δ`), and a positive field compared through arithmetic.
  * The "semantic" test (an identity that stays true at the junk point, a
    numerator that vanishes under the hypotheses, a clamped definition) is
    still not attempted; those remain C noise, tagged `property` or dropped by
    change 10 when they are not equations, still `exact-value` when they are.

AND STILL NOT DONE: transitive risk (an abbrev passing its own scalar param to a
risky def, e.g. `abbrev AxisSpace I eps := CoefficientSpace I (weight eps)`).
Two-level indirection is MISSED -- which is exactly how
AxisCoefficientSpace.lean:434,437 escaped, found by a reader instead. One-level
indirection IS covered.
"""

import argparse, collections, csv, os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from safeverifyagent.extract import blank_comments              # noqa: E402
from cone import decls_full, SKIP_DIRS, IDENT                   # noqa: E402

OPENERS, CLOSERS = "([{⦃⟨", ")]}⦄⟩"

# --- vendored signature splitter (change 12) --------------------------------
HEADER = re.compile(
    r"^(?:(?:omit|include|open|set_option)\b[^\n]*?\bin[ \t]+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|public\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+"
    r"|scoped\s+|local\s+|meta\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom|example)\b"
    r"[ \t]*[^\s:({\[⦃⟨]*")


def strip_header(body: str) -> str:
    """Drop `theorem P.of_wave` (and its modifiers) from the front of a declaration."""
    m = HEADER.match(body)
    return body[m.end():] if m else body


def split_sig(body: str):
    """(binder_region, conclusion, rest) by bracket depth: the body is cut at the
    first depth-0 `:=` or `where`, and the LAST depth-0 `:` of what precedes it
    separates the conclusion. (Frozen copy of nosupplier.split_sig @ a83e437.)"""
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


# --- lexical pieces -----------------------------------------------------------
# The character class MUST include Greek: this artifact names its scales
# `epsilon`, `alpha`, `kappa` with the actual letters, and an ASCII-only class made
# the pass blind to `(eps-inv) ^ m` in `AxisWeightEstimates.weight` -- i.e. blind to
# the single most common denominator name in an analysis library. That miss was
# caught by a READER finding two content-free statements the tool had passed
# (AxisCoefficientSpace.lean:434,437).
_ID = r"[A-Za-z_α-ωΑ-Ω][\w'₀-₉α-ωΑ-Ω]*"
_IDC = r"[\w'!?₀-₉]"            # a character that continues an identifier
# `/ x` or `x⁻¹` where x is a single identifier. Change 2 (P6): not `/ Real.sin`
# and not `N.scale⁻¹`. Change 1 (P4): not the preimage `f ⁻¹' S`.
DIV = re.compile(r"/\s*(" + _ID + r")(?!" + _IDC + r"|\.)")
_INV_BASE = r"(?<!" + _IDC + r")(?<!\.)(" + _ID + r")\s*⁻¹"
INV = re.compile(_INV_BASE + r"(?!')")
# the pre-change forms, kept only for `--ablate P4` / `--ablate P6`
_OLD_DIV = re.compile(r"/\s*(" + _ID + r")")
_OLD_INV = re.compile(r"(" + _ID + r")\s*\u207b\u00b9")
_OLD_INV_NO_PREIMAGE = re.compile(r"(" + _ID + r")\s*\u207b\u00b9(?!')")
_SCALAR_T = r"(?:ℝ≥0|ℝ|ℂ|NNReal)"
_BINDER_KW = re.compile(r"(?:∀|∃!?|fun|λ|Π)\s*$")
_WORD_OPS = "+-*/^•⁻·"

# A triage worker measured 13 of 38 sampled hits as false positives of ONE kind:
# the signature already said `1 <= k` or `4 <= k`, which implies nonzero. Those forms
# must count as constraints. `0 < x⁻¹` is change 7 (P10).
_OLD_NONZERO = [r"{name}\s*\u2260\s*0", r"0\s*<\s*{name}\b", r"0\s*\u2260\s*{name}\b",
                r"{name}\s*>\s*0", r"0\s*<\s*\|{name}\|",
                r"[1-9]\d*\s*\u2264\s*{name}\b", r"{name}\s*\u2265\s*[1-9]\d*",
                r"[1-9]\d*\s*<\s*{name}\b", r"{name}\s*>\s*[1-9]\d*"]
# Change 13: the same forms with real token boundaries. `\b` after a primed name
# (`0 < ε'`) never matches, so every `ε'` guard was invisible; and with no LEFT
# boundary `r ≠ 0` matched inside `hr ≠ 0` / `x - r ≠ 0` and `1 ≤ N` inside
# `x - 1 ≤ N`, reading an unrelated fact as a guard.
_L = r"(?<![\w'.!?\d])(?<![-+*/^\u2022\u00b7]\s)(?<![-+*/^\u2022\u00b7])"
# a name on the LEFT of `≠ 0` / `> 0` may follow `*` or `/`: `x * r ≠ 0` and
# (junk-value arithmetic) `x / r ≠ 0` both force r ≠ 0, which is all this asks.
# a positive literal, possibly a fraction or ascribed: `2`, `3 / 2`, `(1 : ℝ) / 2`,
# `(4 / 3 : ℝ)`. (The old `[1-9]\d* ≤ x` read `3 / 2 ≤ x` through its
# denominator `2`, which was right by accident; change 13's left boundary needs
# the fraction spelled out.)
_PLIT1 = r"(?:\(\s*)?[1-9]\d*(?:\.\d+)?(?:\s*:\s*[^()]*\))?"
POSLIT = _PLIT1 + r"(?:\s*/\s*" + _PLIT1 + r")?"
_N = r"(?<![\w'.!?\d])(?<![-+^]\s)(?<![-+^])" + r"{name}(?![\w'!?])"
_NR = r"{name}(?![\w'!?])"
NONZERO = [_N + r"\s*\u2260\s*0(?![\d.])", _L + r"0\s*<\s*" + _NR, _L + r"0\s*\u2260\s*" + _NR,
           _N + r"\s*>\s*0(?![\d.])", _L + r"0\s*<\s*\|{name}\|",
           _L + POSLIT + r"\s*\u2264\s*" + _NR, _N + r"\s*\u2265\s*[1-9]",
           _L + POSLIT + r"\s*<\s*" + _NR, _N + r"\s*>\s*[1-9]",
           _L + r"0\s*<\s*{name}\s*\u207b\u00b9"]


def _depth_scan_end(s, start, stop_comma=True):
    """Index where a region starting at `start` ends: its enclosing bracket closes
    (depth < 0), or a depth-0 comma when `stop_comma`, or the end of `s`."""
    depth, i, n = 0, start, len(s)
    while i < n:
        c = s[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
            if depth < 0:
                return i
        elif c == "," and depth == 0 and stop_comma:
            return i
        i += 1
    return n


_BY = re.compile(r"(?<![\w'.!?])by(?![\w'!?])")
_TAC_VALUE = re.compile(r"\s*:=\s*by(?![\w'!?])")
# tactic steps whose text is a PROOF, never part of the value being built
_TAC_PROOF = re.compile(r"^([ \t]*)(?:[\u00b7.][ \t]*)?(?:have|haveI|obtain|suffices|show|calc|rcases)"
                        r"(?![\w'!?])", re.M)


def strip_by(text: str) -> str:
    """Change 3 (P8): blank proof text, keeping positions.

    A `by` inside a term (`(by norm_num)`, `⟨x, by simp⟩`) is a proof: blanked to
    its enclosing bracket or a depth-0 comma. A definition whose whole value is
    `:= by ...` still BUILDS its value there (`let k := fun t => ... t / a`,
    `exact`, `refine`), so only its proof steps -- a `have`/`obtain`/
    `suffices`/`show`/`calc` line and every more-indented line under it -- are
    blanked. Measured: blanking the whole `:= by` block hid two reader-A hits
    (`cylinderCapCoordinates`, CylinderCapRounding.lean:28,44)."""
    if "by" not in text:
        return text
    out = list(text)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    skip_to = 0
    m = _TAC_VALUE.match(text)
    if m:
        blank(m.end() - 2, m.end())                      # the `by` itself
        for h in _TAC_PROOF.finditer(text, m.end()):
            if h.start() < skip_to:
                continue
            ind = len(h.group(1).expandtabs())
            end = text.find("\n", h.end())
            while end != -1:
                nxt = text.find("\n", end + 1)
                line = text[end + 1:nxt if nxt != -1 else len(text)]
                if line.strip() and len(line) - len(line.lstrip()) <= ind:
                    break
                end = nxt
            end = len(text) if end == -1 else end
            blank(h.start(), end)
            skip_to = end
    pos = 0
    for b in _BY.finditer(text):
        if b.start() < pos or out[b.start()] == " ":
            continue
        end = _depth_scan_end(text, b.end())
        blank(b.start(), end)
        pos = end
    return "".join(out)


# --- change 2: binders are binders -------------------------------------------
def scalar_binder(sig: str, name: str) -> bool:
    """Is `name` introduced in `sig` by a bracketed binder of scalar type?"""
    rx = re.compile(r"([({⦃])\s*((?:" + _ID + r"\s+)*)(?<!" + _IDC + r")" + re.escape(name)
                    + r"(?!" + _IDC + r")((?:\s+" + _ID + r")*)\s*:\s*" + _SCALAR_T
                    + r"\s*[)}⦄]")
    for m in rx.finditer(sig):
        before = sig[:m.start()].rstrip()
        if not before or before[-1] in ")]}⦄" or _BINDER_KW.search(before):
            return True
    return False


# --- changes 6-7: what a signature says is positive ---------------------------
_LIT = re.compile(r"^\(?\s*(\d+(?:\.\d+)?)(?:\s*/\s*(\d+(?:\.\d+)?))?\s*(?::\s*[^)]*)?\)?$")


def literal_value(s: str):
    m = _LIT.match(s.strip())
    if not m:
        return None
    v = float(m.group(1))
    if m.group(2):
        d = float(m.group(2))
        return None if d == 0 else v / d
    return v


def _norm(t: str) -> str:
    t = " ".join(t.split())
    while t.startswith("(") and t.endswith(")") and _balanced(t[1:-1]):
        t = t[1:-1].strip()
    return t


def _balanced(s):
    d = 0
    for c in s:
        if c in OPENERS:
            d += 1
        elif c in CLOSERS:
            d -= 1
            if d < 0:
                return False
    return d == 0


_TERM = _ID + r"(?:\.[A-Za-z_]\w*)*(?:[ \t]+" + _ID + r"(?:\.[A-Za-z_]\w*)*)*"
# a seed term must stand alone: no operator on either side, and not a prefix of
# a longer application (`0 < a - b` says nothing about `a`)
_TEND = r"(?![\w'.!?]|[ \t]*[-+*/^\u2022\u00b7\u207b(\w])"
_TBEG = r"(?<![\w'.!?\d])(?<![-+*/^\u2022\u00b7]\s)(?<![-+*/^\u2022\u00b7])"
_POS_SEED = [re.compile(_TBEG + r"0\s*<\s*(" + _TERM + r")" + _TEND),
             re.compile(_TBEG + r"(" + _TERM + r")\s*>\s*0(?![\d.])"),
             re.compile(_TBEG + POSLIT + r"\s*[<\u2264]\s*(" + _TERM + r")" + _TEND),
             re.compile(_TBEG + r"0\s*<\s*\|(" + _TERM + r")\|")]
_NNEG_SEED = [re.compile(_TBEG + r"0\s*\u2264\s*(" + _TERM + r")" + _TEND),
              re.compile(_TBEG + r"(" + _TERM + r")\s*\u2265\s*0(?![\d.])")]


def parse_args(s: str, i: int):
    """Explicit arguments of an application whose head ends at `i`: identifiers,
    numerals and bracketed groups, until something else. Named arguments
    `(x := v)` are skipped. Returns [(text, is_named)]."""
    out, n = [], len(s)
    if s.startswith(".{", i):
        k = s.find("}", i)
        i = k + 1 if k > 0 else i
    while True:
        j = i
        while j < n and s[j] in " \t\n":
            j += 1
        if j >= n:
            break
        c = s[j]
        if c in "([{⦃⟨":
            depth, k = 0, j
            while k < n:
                if s[k] in OPENERS:
                    depth += 1
                elif s[k] in CLOSERS:
                    depth -= 1
                    if depth == 0:
                        break
                k += 1
            grp = s[j:k + 1]
            if c == "(" and re.match(r"\(\s*" + _ID + r"\s*:=", grp):
                i = k + 1
                continue                       # named argument
            if c in "[{":
                break                          # set-builder / instance: not an argument
            out.append(grp)
            i = k + 1
            continue
        m = IDENT.match(s, j)
        if m and not re.match(r"(?:then|else|with|fun|at|in|if|by|do|from|using)$", m.group(0)):
            out.append(m.group(0))
            i = m.end()
            continue
        m = re.compile(r"\d+(?:\.\d+)?").match(s, j)
        if m:
            out.append(m.group(0))
            i = m.end()
            continue
        break
    return out


class Structures:
    """Change 6 (P3): structures whose fields guard a parameter or a field."""

    def __init__(self):
        self.params = collections.defaultdict(list)   # short -> [set(positions)]
        self.fields = collections.defaultdict(list)   # short -> [set(field names)]

    def add(self, full, body):
        rest = strip_header(body)
        binders, _t, fields = split_sig(rest)
        explicit = [nm for nm, kind, _t in binder_list(binders) if kind == "explicit"]
        if not fields.lstrip().startswith("where") and not fields.lstrip().startswith(":="):
            fields = ""
        pos, fpos = set(), set()
        for k, p in enumerate(explicit):
            if _field_guard(fields, p):
                pos.add(k)
        for m in re.finditer(r"^[ \t]+(?:\(\s*)?[\w'!?]+[ \t]*:[ \t]*0[ \t]*<[ \t]*(" + _ID
                             + r")[ \t]*\)?[ \t]*$", fields, re.M):
            fpos.add(m.group(1))
        short = full.split(".")[-1]
        self.params[short].append(pos)
        self.fields[short].append(fpos)

    def guarded_positions(self, short):
        sets = self.params.get(short)
        if not sets:
            return set()
        return set.intersection(*sets)

    def positive_fields(self, short):
        sets = self.fields.get(short)
        if not sets:
            return set()
        return set.intersection(*sets)


def _field_guard(fields, p):
    e = re.escape(p)
    b = r"(?!" + _IDC + r")"
    forms = [r"0\s*<\s*" + e + b, e + b + r"\s*≠\s*0", r"0\s*≠\s*" + e + b,
             e + b + r"\s*>\s*0", r"[1-9]\d*\s*[≤<]\s*" + e + b]
    line = r"^[ \t]+(?:\(\s*)?[\w'!?]+[ \t]*:[ \t]*(?:%s)[ \t]*\)?[ \t]*$"
    return any(re.search(line % f, fields, re.M) for f in forms)


def binder_list(binders: str):
    """[(name, kind, type_head)] of the leading bracketed binder groups; kind is
    explicit / implicit / inst, type_head the last component of the first
    identifier of the binder's type."""
    out, i, n = [], 0, len(binders)
    while i < n:
        while i < n and binders[i] in " \t\n":
            i += 1
        if i >= n or binders[i] not in "({[⦃":
            break
        c = binders[i]
        depth, k = 0, i
        while k < n:
            if binders[k] in OPENERS:
                depth += 1
            elif binders[k] in CLOSERS:
                depth -= 1
                if depth == 0:
                    break
            k += 1
        grp = binders[i + 1:k]
        kind = {"(": "explicit", "{": "implicit", "⦃": "implicit", "[": "inst"}[c]
        ci = grp.find(":")
        names = grp[:ci] if ci >= 0 else ("" if c == "[" else grp)
        typ = grp[ci + 1:] if ci >= 0 else grp
        head = IDENT.search(typ)
        head = head.group(0).split(".")[-1] if head else ""
        for nm in names.split():
            if re.fullmatch(_ID, nm):
                out.append((nm, kind, head))
        if c == "[" and not names.strip():
            out.append(("_inst", kind, head))
        i = k + 1
    return out


class Facts:
    """What a signature says is nonzero (NONZERO + changes 6 and 7)."""

    def __init__(self, sig: str, structs: Structures = None, chain: bool = True,
                 old_nonzero: bool = False):
        self.sig = sig
        self.old_nonzero = old_nonzero
        self.structs = structs
        self.chain = chain
        self._pos = self._nneg = None
        self._pat = []

    def is_pos(self, term):
        return term in self.pos or any(p.fullmatch(term) for p in self._pat)

    def is_nneg(self, term):
        return term in self.nneg or any(p.fullmatch(term) for p in self._pat)

    def _seed(self):
        sig = self.sig
        pos, nneg = set(), set()
        if self.chain:
            for rx in _POS_SEED:
                for m in rx.finditer(sig):
                    pos.add(_norm(m.group(1)))
            for rx in _NNEG_SEED:
                for m in rx.finditer(sig):
                    nneg.add(_norm(m.group(1)))
        if self.structs is not None:
            for m in re.finditer(r"(?:(" + _ID + r")(?:\s+" + _ID + r")*\s*:\s*"
                                 r"(?:∀([^,:]*),\s*)?@?(" + IDENT.pattern + r"))", sig):
                head = m.group(3).split(".")[-1]
                bound = set(re.findall(_ID, m.group(2) or ""))
                gp = self.structs.guarded_positions(head)
                fp = self.structs.positive_fields(head)
                if not gp and not fp:
                    continue
                if gp:
                    args = parse_args(sig, m.end())
                    for k in gp:
                        if k < len(args):
                            a = _norm(args[k])
                            words = a.split()
                            if bound & set(words):
                                # `O : ∀ i, S (eps i)`: every instance `eps p` is positive
                                self._pat.append(re.compile(r"\s".join(
                                    r"\S+" if w in bound else re.escape(w) for w in words)))
                            else:
                                pos.add(a)
                if fp:
                    # every name bound by this binder group
                    names = re.findall(_ID, sig[m.start():m.start(3)].split(":")[0])
                    for b in names:
                        for f in fp:
                            pos.add(b + "." + f)
        self._pos, self._nneg = pos, nneg | pos

    @property
    def pos(self):
        if self._pos is None:
            self._seed()
        return self._pos

    @property
    def nneg(self):
        if self._nneg is None:
            self._seed()
        return self._nneg

    def nonzero(self, name: str) -> bool:
        e = re.escape(name)
        sig = self.sig
        if self.old_nonzero:
            pats = _OLD_NONZERO
        else:
            pats = NONZERO if self.chain else NONZERO[:-1]
        if any(re.search(p.format(name=e), sig) for p in pats):
            return True
        if self.structs is not None and self.is_pos(name):
            return True
        return self.chain and self._chained(name)

    def _lhs_candidates(self, before: str):
        """Terms that END `before` (the text left of a relation): the last one,
        two or three identifiers (an application `eps n`), each accepted plain
        or behind a positive literal coefficient `k *`, and refused when an
        arithmetic operator sits in front (`a - l ≤ r` says nothing of r)."""
        out = []
        m = re.search(r"(" + _TERM + r")\s*$", before)
        if not m:
            return out
        starts = [w.start() + m.start(1) for w in re.finditer(r"\S+", m.group(1))]
        end = m.start(1) + len(m.group(1).rstrip())
        for st in starts[::-1][:3]:
            term = " ".join(before[st:end].split())
            head = before[:st]
            prev = head.rstrip()[-1:]
            coeff = re.search(r"(\d+(?:\.\d+)?)\s*\*\s*$", head)
            if coeff:
                before_c = head[:coeff.start()].rstrip()[-1:]
                if float(coeff.group(1)) > 0 and not (before_c and before_c in _WORD_OPS):
                    out.append(term)
            elif prev and prev in _WORD_OPS:
                continue
            else:
                out.append(term)
        return out

    def _chained(self, name: str) -> bool:
        sig = self.sig
        e = re.escape(name)
        nb = r"(?!" + _IDC + r"|\.)"
        no_op = r"(?!\s*[-+*/^\u2022\u00b7])"
        # A (<|≤) name, and the P10 forms A (<|≤) name⁻¹
        for m in re.finditer(r"(\u2264|<)\s*(?<!" + _IDC + r")" + e + nb
                             + r"(?:\s*\u207b\u00b9)?" + no_op, sig):
            for term in self._lhs_candidates(sig[:m.start()]):
                if self.is_pos(term) or (m.group(1) == "<" and self.is_nneg(term)):
                    return True
        # name (≥|>) A
        for m in re.finditer(r"(?<!" + _IDC + r")(?<!\.)(?<![-+*/^\u2022\u00b7]\s)" + e + nb
                             + no_op + r"\s*(\u2265|>)\s*(" + _TERM + r")" + _TEND, sig):
            term = _norm(m.group(2))
            if self.is_pos(term) or (m.group(1) == ">" and self.is_nneg(term)):
                return True
        return False


# --- change 4: if-guards --------------------------------------------------------
_IF = re.compile(r"(?<![\w'.!?])if(?![\w'!?])")


def _find_kw(s, kw, start):
    """First depth-0 `kw` (then/else) from `start`, skipping nested if..then..else."""
    depth, i, n, nested = 0, start, len(s), 0
    rx_kw = re.compile(r"(?<![\w'.!?])(if|then|else)(?![\w'!?])")
    while i < n:
        c = s[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
            if depth < 0:
                return None
        elif depth == 0 and c in "ite":
            m = rx_kw.match(s, i)
            if m and (i == 0 or not re.match(_IDC + r"|\.", s[i - 1])):
                w = m.group(1)
                if w == "if":
                    nested += 1
                elif w == kw and nested == 0:
                    return i
                elif w == "else" and nested:
                    nested -= 1
                i = m.end()
                continue
        i += 1
    return None


def _split_top(s, seps):
    parts, depth, cur, i = [], 0, 0, 0
    while i < len(s):
        c = s[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and c in seps:
            parts.append(s[cur:i])
            cur = i + 1
        i += 1
    parts.append(s[cur:])
    return parts


def _cond_side(cond, name):
    """'else' if the condition holding implies name may be 0 but its failure
    implies name ≠ 0; 'then' if the condition implies name ≠ 0; else None."""
    cond = _norm(re.sub(r"^\s*" + _ID + r"\s*:\s*", "", cond.strip()))
    e = re.escape(name)
    b = r"(?!" + _IDC + r"|\.)"
    zero_then = [r"^" + e + b + r"\s*=\s*0$", r"^0\s*=\s*" + e + b + r"$",
                 r"^" + e + b + r"\s*≤\s*0$", r"^0\s*≥\s*" + e + b + r"$"]
    nz_then = [r"^" + e + b + r"\s*≠\s*0$", r"^0\s*≠\s*" + e + b + r"$",
               r"^0\s*<\s*" + e + b + r"$", r"^" + e + b + r"\s*>\s*0$",
               r"^" + e + b + r"\s*<\s*0$", r"^0\s*>\s*" + e + b + r"$"]
    ors = _split_top(cond, "∨")
    if len(ors) > 1:
        return "else" if any(_cond_side(p, name) == "else" for p in ors) else None
    ands = _split_top(cond, "∧")
    if len(ands) > 1:
        return "then" if any(_cond_side(p, name) == "then" for p in ands) else None
    c = cond.strip()
    if any(re.match(p, c) for p in zero_then):
        return "else"
    if any(re.match(p, c) for p in nz_then):
        return "then"
    m = re.match(r"^(.*?)\s*(≤|<)\s*" + e + b + r"$", c)
    if m:
        v = literal_value(m.group(1))
        if v is not None and (v > 0 or (v == 0 and m.group(2) == "<")):
            return "then"
    m = re.match(r"^" + e + b + r"\s*(≥|>)\s*(.*)$", c)
    if m:
        v = literal_value(m.group(2))
        if v is not None and (v > 0 or (v == 0 and m.group(1) == ">")):
            return "then"
    return None


def guarded_spans(text, name):
    spans = []
    for m in _IF.finditer(text):
        t = _find_kw(text, "then", m.end())
        if t is None:
            continue
        el = _find_kw(text, "else", t + 4)
        if el is None:
            continue
        end = _depth_scan_end(text, el + 4)
        side = _cond_side(text[m.end():t], name)
        if side == "then":
            spans.append((t, el))
        elif side == "else":
            spans.append((el, end))
    return spans


def junk_sites(text: str, *, if_guard=True, ablate=frozenset()):
    """{name: [positions]} of divisions / inversions by a single identifier that
    no enclosing if-branch guards (change 4)."""
    sites = collections.defaultdict(list)
    if "P6" in ablate:
        rxs = (_OLD_DIV, _OLD_INV if "P4" in ablate else _OLD_INV_NO_PREIMAGE)
    else:
        rxs = (DIV, INV if "P4" not in ablate else re.compile(_INV_BASE))
    for rx in rxs:
        for m in rx.finditer(text):
            nm = m.group(1)
            if nm[0].isdigit():
                continue
            sites[nm].append(m.start(1))
    if not if_guard or "if" not in text:
        return dict(sites)
    out = {}
    for nm, ps in sites.items():
        spans = guarded_spans(text, nm)
        left = [p for p in ps if not any(a <= p < b for a, b in spans)]
        if left:
            out[nm] = left
    return out


# --- P12 / change 10-11: which conclusions carry a value -----------------------
# ONE filter, and a REJECTED second one. Two triage workers disagreed here and the
# disagreement is the useful part.
#
# KEPT -- require an EQUALITY conclusion. A bound, regularity, measurability, support
# or compactness claim does not "collapse to 0 = 0" in any interesting way: `0 <= 0`
# and `ContDiff of 0` are still the intended content. This was the largest false-positive
# group in a 41-hit triage that came back A=1 B=36 C=4 D=0 (ParabolicSupport:18,
# SpatialSupportScaling:18,36, RadialKernelBounds:33, ActivationCone:363,
# ParentChoiceInitialSupport:20,28, ...). Both triage workers agree on this one.
# Change 10: it now applies to mode 2 as well (P12: 160 of the 260 mode-2 rows in
# the differential-geometry triage were non-equalities).
#
# REJECTED -- the "denominator must reach only ONE side" rule. One worker measured it
# holding on 41 of 41 hits and recommended it. A second worker produced the
# counterexample and it is decisive: in `PulseCovariance:74`,
# `INT gaussian b m r = r * sqrt(pi / b)`, the divisor `b` occurs on BOTH sides -- in the
# LHS integrand and in the RHS square root -- yet the statement IS content-free at b = 0,
# because both sides independently collapse to 0. That is the audit's sharpest junk-value
# finding, and this filter would have deleted it. Same for
# `WholeSpaceGaussianTimeKernel.lean:41`, where `t` is on both sides and both vanish.
# The correct test is semantic (evaluate both sides at the junk point and ask whether ANY
# term survives) and is not available to a syntactic pass, so no symmetry filter is applied
# and the resulting false positives are accepted.
NOT_A_VALUE = re.compile(r"ContDiff|Differentiable|Measurable|Integrable|HasCompactSupport"
                         r"|tsupport|IsOpen|IsCompact|Continuous|Tendsto|MemClass|JetRate"
                         r"|≤|≥|<|>|∈|⊆")
_OPEN, _CLOSE = OPENERS, CLOSERS


def _top_eq(concl):
    depth = 0
    for i, ch in enumerate(concl):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif (ch == "=" and depth == 0 and i > 0
              and concl[i - 1] not in "<>=!:≠≤≥"
              and (i + 1 >= len(concl) or concl[i + 1] not in "=>")):
            return i
    return None


def informative(concl: str, name: str = None) -> bool:
    """Is this an EQUALITY of values, i.e. could a collapse to 0 = 0 empty it?"""
    eq = _top_eq(concl)
    if eq is None:
        return False
    return not NOT_A_VALUE.search(concl[:eq])


def class_hint(concl: str, quantity: str) -> str:
    """Change 11: `exact-value` if the conclusion is an equation (as `informative`
    reads it) and the equation's own sides -- the depth-0 clause holding the
    `=`, cut at `,` `→` `∧` `∨` `↔` -- mention the quantity; else `property`."""
    if not informative(concl):
        return "property"
    eq = _top_eq(concl)
    stops = ",→∧∨↔"
    depth, lo = 0, 0
    for i in range(eq - 1, -1, -1):
        ch = concl[i]
        if ch in _CLOSE:
            depth += 1
        elif ch in _OPEN:
            depth -= 1
        elif depth == 0 and ch in stops:
            lo = i + 1
            break
    depth, hi = 0, len(concl)
    for i in range(eq + 1, len(concl)):
        ch = concl[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif depth == 0 and ch in stops:
            hi = i
            break
    clause = concl[lo:hi]
    rx = r"(?<!" + _IDC + r")" + re.escape(quantity) + r"(?!" + _IDC + r")"
    return "exact-value" if re.search(rx, clause) else "property"


# --- risky definitions ---------------------------------------------------------
_OPEN_KW = re.compile(r"(?<![\w'.!?])open(?:\s+scoped)?\s+([^\n]*)")


def opened_namespaces(txt):
    """Every name any `open` in the file mentions (over-approximation: more
    resolution, never less)."""
    out = set()
    for m in _OPEN_KW.finditer(txt):
        for tok in re.split(r"[\s()]+", m.group(1)):
            if tok == "in":
                break
            if tok and IDENT.fullmatch(tok):
                out.add(tok)
    return out


class RiskyDef:
    __slots__ = ("full", "short", "ns", "file", "private", "params", "risky",
                 "by_name", "line")

    def __init__(self, **kw):
        for k, v in kw.items():
            setattr(self, k, v)


def risky_defs(files, *, ablate=frozenset(), structs=None, decls=None):
    """Definitions whose BODY divides by / inverts one of their own scalar params.

    This is the half that matters. Both known instances hide the division behind a
    definition, so a scan of theorem STATEMENTS alone finds only 5 of the 8
    `transportPhase` theorems and NONE of the `BasePrefixIdentity` swirl ones:
    `:492`'s conclusion is merely `ContDiff R inf (transportPhase F phi gap K Kr)`,
    with the `Kr / K` living inside `transportPhase`. Same blind spot class as the
    `nosupplier.py` W8 case -- a syntactic instrument cannot see through a
    definition -- so the fix is to find the definition first, then flag its users.

    Returns {short name: [RiskyDef]} (changes 8-9 resolve among them).
    """
    out = collections.defaultdict(list)
    for rel, txt in files.items():
        for full, kind, line, body, _h, _vt, vbound in (decls[rel] if decls else decls_full(txt)):
            if kind not in ("def", "abbrev"):
                continue
            sig_all = strip_header(body)
            binders, typ, rhs = split_sig(sig_all)
            if "P8" not in ablate:
                rhs = strip_by(rhs)
            sites = junk_sites(rhs, if_guard="P9" not in ablate, ablate=ablate)
            if not sites:
                continue
            params = binder_list(binders)
            facts = Facts(binders + " : " + typ, structs, chain="P2" not in ablate,
                          old_nonzero="NZ" in ablate)
            risky = set()
            for nm in sites:
                ok = (scalar_binder(binders, nm) if "P6" not in ablate else
                      bool(re.search(_OLD_SCALAR.format(name=re.escape(nm)), binders)))
                if not ok:
                    continue
                if "P7" not in ablate:
                    if facts.nonzero(nm):
                        continue
                    if typ.strip() == "Prop" and _prop_guard(rhs, nm):
                        continue
                risky.add(nm)
            if not risky:
                continue
            kinds = {nm: k for nm, k, _t in params}
            body_toks = set(IDENT.findall(sig_all))
            by_name = bool(vbound & body_toks) or any(kinds.get(nm) != "explicit" for nm in risky)
            out[full.split(".")[-1]].append(RiskyDef(
                full=full, short=full.split(".")[-1],
                ns=full.rsplit(".", 1)[0] if "." in full else "",
                file=rel, private=bool(re.match(r"(?:@\[[^\]]*\]\s*)*private\b", body)),
                params=params, risky=risky, by_name=by_name, line=line))
    # NOT DONE: transitive risk (an abbrev passing its own scalar param to a
    # risky def). See the module docstring.
    return dict(out)


# The pre-change scalar-binder regex, kept only for `--ablate P6`.
_OLD_SCALAR = (r"[({{⦃]\s*(?:[^:()]*\b{name}\b[^:()]*)\s*:\s*"
               r"(?:ℝ|ℂ|NNReal|ℝ≥0)\s*[)}}⦄]")


def _prop_guard(rhs, nm):
    """Change 5: a depth-0 conjunct of a Prop body is itself a nonzero fact."""
    body = rhs.lstrip()
    if body.startswith(":="):
        body = body[2:]
    for part in _split_top(body, "∧"):
        p = part.strip()
        f = Facts(p)
        if re.fullmatch(r"\S+\s*(?:<|>|≠|≤|≥)\s*\S+", p) and f.nonzero(nm):
            return True
    return False


# --- theorem side ----------------------------------------------------------------
_LOCAL_Q = re.compile(r"[∀∃]!?\s*((?:" + _ID + r"\s*)+)(?=[,:∈<>≤≥])")


def local_binders(sig):
    out = set()
    for m in re.finditer(r"[(\[{⦃]\s*((?:" + _ID + r"\s+)*" + _ID + r")\s*:(?!=)", sig):
        out.update(m.group(1).split())
    for m in _LOCAL_Q.finditer(sig):
        out.update(m.group(1).split())
    return out


def binder_type_head(sig, x):
    m = re.search(r"[(\[{⦃∀∃]\s*(?:" + _ID + r"\s+)*(?<!" + _IDC + r")" + re.escape(x)
                  + r"(?!" + _IDC + r")(?:\s+" + _ID + r")*\s*:\s*(?:∀[^,:]*,\s*)?@?("
                  + IDENT.pattern + r")", sig)
    return m.group(1).split(".")[-1] if m else None


def resolve(tok, d, *, file, thm_ns, locals_, opened, sig):
    """Change 8: does token `tok` in a theorem name definition `d`?
    Returns (resolved, receiver_head) -- receiver_head set for dot notation."""
    if d.private and d.file != file:
        return False, None
    parts = tok.split(".")
    if len(parts) == 1:
        if tok in locals_:
            return False, None
        if not d.ns:
            return True, None
        if thm_ns == d.ns or thm_ns.startswith(d.ns + "."):
            return True, None
        # namespace-relative: `ns` of the def ends with an opened name, or an
        # ancestor of the theorem's namespace + opened name
        if any(d.ns == o or d.ns.endswith("." + o) for o in opened):
            return True, None
        return False, None
    if parts[0] in locals_:
        if len(parts) != 2:
            return False, None
        head = binder_type_head(sig, parts[0])
        dns_last = d.ns.split(".")[-1] if d.ns else None
        if head and dns_last and head == dns_last:
            return True, head
        return False, None
    if d.full == tok or d.full.endswith("." + tok):
        return True, None
    return False, None


def _simple_arg(a):
    a = _norm(a)
    return a if re.fullmatch(_ID, a) else None


def mapped_args(concl, end, d, receiver, at):
    """Change 9: {risky param: argument text} at one call site."""
    args = parse_args(concl, end)
    if at:
        plist = [nm for nm, _k, _t in d.params]
    else:
        plist = [(nm, t) for nm, k, t in d.params if k == "explicit"]
        if receiver:
            # the receiver fills the first explicit parameter of its type
            for idx, (nm, t) in enumerate(plist):
                if t == receiver:
                    plist = plist[:idx] + plist[idx + 1:]
                    break
            else:
                return {}
        plist = [nm for nm, _t in plist]
    out = {}
    for idx, nm in enumerate(plist):
        if nm in d.risky and idx < len(args):
            out[nm] = args[idx]
    return out


def scan(root, *, all_conclusions=False, ablate=frozenset()):
    files = {}
    for base, dirs, fns in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        for fn in sorted(fns):
            if fn.endswith(".lean"):
                p = os.path.join(base, fn)
                with open(p, encoding="utf-8", errors="replace") as fh:
                    files[os.path.relpath(p, root)] = blank_comments(fh.read())
    decls = {rel: decls_full(txt) for rel, txt in files.items()}

    structs = Structures()
    for rel, ds in decls.items():
        for full, kind, _line, body, _h, _vt, _vb in ds:
            if kind in ("structure", "class"):
                structs.add(full, body)
    st = None if "P3" in ablate else structs

    rows = []
    scalar = (scalar_binder if "P6" not in ablate else
              (lambda s, n: bool(re.search(_OLD_SCALAR.format(name=re.escape(n)), s))))
    # --- mode 1: the division is in the statement
    for rel, ds in decls.items():
        for full, kind, line, body, _h, _vt, _vb in ds:
            if kind not in ("theorem", "lemma"):
                continue
            binders, concl, _proof = split_sig(strip_header(body))
            if "P8" not in ablate:
                concl = strip_by(concl)
            sig = binders + " : " + concl
            facts = Facts(sig, st, chain="P2" not in ablate, old_nonzero="NZ" in ablate)
            sites = junk_sites(concl, if_guard="P9" not in ablate, ablate=ablate)
            for nm in sorted(sites):
                if not scalar(sig, nm):
                    continue            # not a bare scalar binder here
                if facts.nonzero(nm):
                    continue            # constrained: fine
                if not informative(concl, nm):
                    continue
                rows.append({"file": rel, "line": line, "decl": full,
                             "denominator": nm,
                             "class_hint": class_hint(concl, nm),
                             "statement": " ".join(concl.split())[:160]})
    # --- mode 2: definitions that hide the division, and their users
    risky = risky_defs(files, ablate=ablate, structs=st, decls=decls)
    ndefs = sum(len(v) for v in risky.values())
    print(f"{ndefs:,} definitions divide by one of their own scalar parameters "
          f"(the shape that hides from a statement-level scan)\n")
    for rel, ds in decls.items():
        opened = None
        for full, kind, line, body, _h, _vt, _vb in ds:
            if kind not in ("theorem", "lemma"):
                continue
            binders, concl, _p = split_sig(strip_header(body))
            if "P8" not in ablate:
                concl = strip_by(concl)
            hits = [m for m in IDENT.finditer(concl) if m.group(0).split(".")[-1] in risky]
            if not hits:
                continue
            sig = binders + " : " + concl
            if opened is None:
                opened = opened_namespaces(files[rel])
            locals_ = local_binders(sig)
            thm_ns = full.rsplit(".", 1)[0] if "." in full else ""
            facts = Facts(sig, st, chain="P2" not in ablate, old_nonzero="NZ" in ablate)
            found = collections.OrderedDict()
            for m in hits:
                tok = m.group(0)
                at = m.start() > 0 and concl[m.start() - 1] == "@"
                for d in risky[tok.split(".")[-1]]:
                    if "P1" in ablate:
                        cands = {nm: nm for nm in d.risky}
                    else:
                        ok, recv = resolve(tok, d, file=rel, thm_ns=thm_ns, locals_=locals_,
                                           opened=opened, sig=sig)
                        if not ok:
                            continue
                        if d.by_name:
                            cands = {nm: nm for nm in d.risky}
                        else:
                            cands = {nm: _simple_arg(a) for nm, a in
                                     mapped_args(concl, m.end(), d, recv, at).items()}
                    for _pnm, arg in cands.items():
                        if not arg or arg[0].isdigit():
                            continue
                        if scalar(sig, arg) and not facts.nonzero(arg):
                            found.setdefault(d.short, set()).add(arg)
            for dname, bare in found.items():
                if not all_conclusions and "P12" not in ablate and not informative(concl):
                    continue
                rows.append({"file": rel, "line": line, "decl": full,
                             "denominator": f"{'/'.join(sorted(bare))} (via {dname})",
                             "class_hint": max((class_hint(concl, q) for q in [dname, *bare]),
                                               key=lambda h: h == "exact-value"),
                             "statement": " ".join(concl.split())[:160]})
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--all-conclusions", action="store_true",
                    help="mode 2 keeps non-equality conclusions (pre-change 10 behaviour)")
    ap.add_argument("--ablate", default="",
                    help="comma-separated changes to switch off, for measurement: "
                         "P1,P2,P3,P4,P6,P7,P8,P9,P12,NZ")
    args = ap.parse_args()
    ablate = frozenset(a.strip() for a in args.ablate.split(",") if a.strip())

    rows = scan(args.root, all_conclusions=args.all_conclusions, ablate=ablate)
    byfile = collections.Counter(r["file"] for r in rows)
    print(f"{len(rows):,} theorem statements divide by / invert a bare scalar "
          f"binder with no nonzero constraint in the same signature")
    print(f"across {len(byfile):,} files. Top files:\n")
    for f, n in byfile.most_common(15):
        print(f"  {n:4d}  {f}")
    if args.out:
        with open(args.out, "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=["file", "line", "decl", "denominator",
                                               "class_hint", "statement"])
            w.writeheader()
            w.writerows(rows)
        print(f"\nwrote {args.out}")
    print("\nA hit is NOT a defect: the caller may exclude zero, which is the "
          "case in both known instances. It is a statement that does not say "
          "what it appears to say on its own.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
