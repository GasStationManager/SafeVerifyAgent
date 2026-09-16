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

# `/ x` or `x inv`, where x is a single identifier
DIV = re.compile(r"/\s*([A-Za-z_][\w'\u2080-\u2089]*)\b")
INV = re.compile(r"\b([A-Za-z_][\w'\u2080-\u2089]*)\s*\u207b\u00b9")
# a binder introducing that identifier as a bare scalar
SCALAR_BINDER = r"[({{\u2983]\s*(?:[^:()]*\b{name}\b[^:()]*)\s*:\s*(?:\u211d|\u2102|NNReal|\u211d\u22650)\s*[)}}\u2984]"
NONZERO = [r"{name}\s*\u2260\s*0", r"0\s*<\s*{name}\b", r"0\s*\u2260\s*{name}\b",
           r"{name}\s*>\s*0", r"0\s*<\s*\|{name}\|"]


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
