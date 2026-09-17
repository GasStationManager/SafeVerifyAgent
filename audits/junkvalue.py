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

    python3 audits/junkvalue.py /path/to/lean-project [-o OUT.csv]

SCOPE, deliberately narrow. Only flags a denominator that is a SINGLE IDENTIFIER
bound in the same signature as a bare scalar (`(K : R)`, `{C : R}`), with no
`!= 0` / `0 <` / `0 !=` / `0 <=`-plus-`!=` constraint anywhere in that signature.
That is the shape of both known instances. Deliberately NOT flagged:

  * numeric literals (`/ 2`) -- never zero;
  * projections (`s.epsilon n`, `A.ell`) -- these are usually certified by the
    STRUCTURE, e.g. `StripData` carries `epsilon_pos : forall n, 0 < epsilon n`
    (WeightedClasses.lean:35) and `ParentPacketFrames` carries `ell_pos`. A
    worker's claim that an `epsilon` division was unguarded was REFUTED exactly
    this way, so flagging projections would reproduce a known false positive;
  * compound expressions -- too noisy to be actionable.

So this UNDER-reports on purpose. A hit is a statement worth one grep; a miss is
not a clean bill of health.
"""

import argparse, collections, csv, os, re, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from safeverifyagent.extract import blank_comments              # noqa: E402
from cone import decls_with_ns, SKIP_DIRS                       # noqa: E402
from nosupplier import split_sig, strip_header                  # noqa: E402

# `/ x` or `x inv`, where x is a single identifier.
# The character class MUST include Greek: this artifact names its scales
# `epsilon`, `alpha`, `kappa` with the actual letters, and an ASCII-only class made
# the pass blind to `(eps-inv) ^ m` in `AxisWeightEstimates.weight` -- i.e. blind to
# the single most common denominator name in an analysis library. That miss was
# caught by a READER finding two content-free statements the tool had passed
# (AxisCoefficientSpace.lean:434,437).
_ID = r"[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][\w'\u2080-\u2089\u03b1-\u03c9\u0391-\u03a9]*"
DIV = re.compile(r"/\s*(" + _ID + r")")
INV = re.compile(r"(" + _ID + r")\s*\u207b\u00b9")
# a binder introducing that identifier as a bare scalar
SCALAR_BINDER = r"[({{\u2983]\s*(?:[^:()]*\b{name}\b[^:()]*)\s*:\s*(?:\u211d|\u2102|NNReal|\u211d\u22650)\s*[)}}\u2984]"
# A triage worker measured 13 of 38 sampled hits as false positives of ONE kind:
# the signature already said `1 <= k` or `4 <= k`, which implies nonzero. Those forms
# must count as constraints.
NONZERO = [r"{name}\s*\u2260\s*0", r"0\s*<\s*{name}\b", r"0\s*\u2260\s*{name}\b",
           r"{name}\s*>\s*0", r"0\s*<\s*\|{name}\|",
           r"[1-9]\d*\s*\u2264\s*{name}\b", r"{name}\s*\u2265\s*[1-9]\d*",
           r"[1-9]\d*\s*<\s*{name}\b", r"{name}\s*>\s*[1-9]\d*"]


# ONE filter, and a REJECTED second one. Two triage workers disagreed here and the
# disagreement is the useful part.
#
# KEPT -- require an EQUALITY conclusion. A bound, regularity, measurability, support
# or compactness claim does not "collapse to 0 = 0" in any interesting way: `0 <= 0`
# and `ContDiff of 0` are still the intended content. This was the largest false-positive
# group in a 41-hit triage that came back A=1 B=36 C=4 D=0 (ParabolicSupport:18,
# SpatialSupportScaling:18,36, RadialKernelBounds:33, ActivationCone:363,
# ParentChoiceInitialSupport:20,28, ...). Both triage workers agree on this one.
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
                         r"|\u2264|\u2265|<|>|\u2208|\u2286")
_OPEN, _CLOSE = "([{\u2983\u27e8", ")]}\u2984\u27e9"


def informative(concl: str, name: str) -> bool:
    """Is this an EQUALITY of values, i.e. could a collapse to 0 = 0 empty it?"""
    depth, eq = 0, None
    for i, ch in enumerate(concl):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif (ch == "=" and depth == 0 and i > 0
              and concl[i - 1] not in "<>=!\u2260\u2264\u2265"
              and (i + 1 >= len(concl) or concl[i + 1] != "=")):
            eq = i
            break
    if eq is None:
        return False
    return not NOT_A_VALUE.search(concl[:eq])


def risky_defs(files):
    """Definitions whose BODY divides by / inverts one of their own scalar params.

    This is the half that matters. Both known instances hide the division behind a
    definition, so a scan of theorem STATEMENTS alone finds only 5 of the 8
    `transportPhase` theorems and NONE of the `BasePrefixIdentity` swirl ones:
    `:492`'s conclusion is merely `ContDiff R inf (transportPhase F phi gap K Kr)`,
    with the `Kr / K` living inside `transportPhase`. Same blind spot class as the
    `nosupplier.py` W8 case -- a syntactic instrument cannot see through a
    definition -- so the fix is to find the definition first, then flag its users.
    """
    out = {}
    for rel, txt in files.items():
        for full, kind, line, body in decls_with_ns(txt):
            if kind not in ("def", "abbrev", "noncomputable def"):
                continue
            sig_all = strip_header(body)
            binders, _concl, rhs = split_sig(sig_all)
            names = set(DIV.findall(rhs)) | set(INV.findall(rhs))
            for nm in names:
                if nm[0].isdigit():
                    continue
                if re.search(SCALAR_BINDER.format(name=re.escape(nm)), binders):
                    out.setdefault(full.split(".")[-1], set()).add(nm)
    # NOT DONE: transitive risk (an abbrev passing its own scalar param to a risky
    # def, e.g. `abbrev AxisSpace I eps := CoefficientSpace I (weight eps)`). A
    # working implementation cost >15 min on 2,659 files and was cut. Consequence,
    # stated so the output is not mistaken for complete: two-level indirection is
    # MISSED -- which is exactly how AxisCoefficientSpace.lean:434,437 escaped, found
    # by a reader instead. One-level indirection IS covered.
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("-o", "--out", default=None)
    args = ap.parse_args()

    rows = []
    for base, dirs, fns in os.walk(args.root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in sorted(fns):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(base, fn)
            rel = os.path.relpath(path, args.root)
            txt = blank_comments(open(path, encoding="utf-8", errors="replace").read())
            for full, kind, line, body in decls_with_ns(txt):
                if kind not in ("theorem", "lemma"):
                    continue
                sig_all = strip_header(body)
                binders, concl, _proof = split_sig(sig_all)
                sig = binders + " : " + concl
                names = set(DIV.findall(concl)) | set(INV.findall(concl))
                for nm in sorted(names):
                    if nm[0].isdigit():
                        continue
                    if not re.search(SCALAR_BINDER.format(name=re.escape(nm)), sig):
                        continue            # not a bare scalar binder here
                    if any(re.search(p.format(name=re.escape(nm)), sig) for p in NONZERO):
                        continue            # constrained: fine
                    if not informative(concl, nm):
                        continue
                    rows.append({"file": rel, "line": line, "decl": full,
                                 "denominator": nm,
                                 "statement": " ".join(concl.split())[:160]})
    # --- mode 2: definitions that hide the division, and their users
    files = {}
    for base, dirs, fns in os.walk(args.root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in sorted(fns):
            if fn.endswith(".lean"):
                p = os.path.join(base, fn)
                files[os.path.relpath(p, args.root)] = blank_comments(
                    open(p, encoding="utf-8", errors="replace").read())
    risky = risky_defs(files)
    print(f"{len(risky):,} definitions divide by one of their own scalar parameters "
          f"(the shape that hides from a statement-level scan)\n")
    for rel, txt in files.items():
        for full, kind, line, body in decls_with_ns(txt):
            if kind not in ("theorem", "lemma"):
                continue
            binders, concl, _p = split_sig(strip_header(body))
            sig = binders + " : " + concl
            for dname, params in risky.items():
                if not re.search(r"\b" + re.escape(dname) + r"\b", concl):
                    continue
                bare = [nm for nm in params
                        if re.search(SCALAR_BINDER.format(name=re.escape(nm)), sig)
                        and not any(re.search(q.format(name=re.escape(nm)), sig)
                                    for q in NONZERO)]
                if bare:
                    rows.append({"file": rel, "line": line, "decl": full,
                                 "denominator": f"{'/'.join(sorted(bare))} (via {dname})",
                                 "statement": " ".join(concl.split())[:160]})

    byfile = collections.Counter(r["file"] for r in rows)
    print(f"{len(rows):,} theorem statements divide by / invert a bare scalar "
          f"binder with no nonzero constraint in the same signature")
    print(f"across {len(byfile):,} files. Top files:\n")
    for f, n in byfile.most_common(15):
        print(f"  {n:4d}  {f}")
    if args.out and rows:
        with open(args.out, "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f"\nwrote {args.out}")
    print("\nA hit is NOT a defect: the caller may exclude zero, which is the "
          "case in both known instances. It is a statement that does not say "
          "what it appears to say on its own.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
