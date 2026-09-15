"""Which declarations can the headline theorems possibly depend on?

An artifact with 38,503 theorems cannot be audited theorem by theorem without a
denominator, and "all of them" is the wrong denominator: a claimed proof is only
as strong as the cone below its *headline* theorems, and a defect in a
declaration nothing references cannot make a false theorem true.

So this builds a NAME-level dependency graph over the whole repository and
reports what the seeds reach.

    python3 audits/cone.py /path/to/lean-project \
        --seed Euler.euler_breakdown_R3 --seed ... [-o OUT.csv]

Method, and both of its error directions, stated plainly because a reachability
number is quotable and therefore dangerous:

* Declarations are parsed with a `namespace`/`section` stack, so a node is a
  fully qualified name. A reference is any identifier token in a declaration's
  body that resolves to a declared name — exactly, or by matching a SUFFIX of
  one (which is how `open` and namespace-relative naming appear in source).
* Suffix matching OVER-approximates: `add` resolves to every `*.add`. That is
  the safe direction for a cone, since it only makes the audited set bigger.
* It UNDER-approximates in one specific and important way: uses that are never
  written down. Instance synthesis, the ambient `@[simp]` set, `gcongr`,
  `positivity`, and `aesop` extensions are all invisible here. So
  "not in the cone" means "no NAMED reference chain from the seeds" — a strong
  triage signal, never a proof of dead code. The script prints how many
  out-of-cone declarations carry an implicit-use attribute, which is the size of
  that blind spot.

Use it to prioritise, and to state coverage honestly: "N of M in-cone theorems
read" is a claim about the right M.
"""

import argparse, collections, csv, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from safeverifyagent.extract import blank_comments   # noqa: E402

SKIP_DIRS = (".lake", ".git", "build", ".venv")
SEC = "\x00"
IDENT = re.compile(
    r"[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_\u2019!?\u2080-\u2089\u03b1-\u03c9\u0391-\u03a9']*"
    r"(?:\.[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_!?\u2080-\u2089\u03b1-\u03c9\u0391-\u03a9']*)*")
NS = re.compile(r"^[ \t]*(namespace|section|end)\b[ \t]*([\w.\u03b1-\u03c9]*)", re.M)
DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom|example)\b"
    r"[ \t]*(?P<name>[^\s:({\[\u2983\u27e8]*)", re.M)
IMPLICIT_USE = re.compile(r"@\[[^\]]*(simp|gcongr|positivity|bound|aesop|norm_cast|ext)")


def decls_with_ns(text):
    events = [("d", m.start(), m) for m in DECL_START.finditer(text)]
    events += [("n", m.start(), m) for m in NS.finditer(text)]
    events.sort(key=lambda e: e[1])
    stack, out, pending = [], [], None
    for typ, pos, m in events:
        if typ == "d":
            if pending:
                out.append(pending + (pos,))
            ns = [s for s in stack if s != SEC]
            pending = (".".join(ns + [m.group("name") or "_anon"]),
                       m.group("kind"), text[:m.start()].count("\n") + 1, m.start())
        else:
            kw, nm = m.group(1), m.group(2)
            if kw == "namespace":
                stack.append(nm or SEC)
            elif kw == "section":
                stack.append(SEC)
            elif nm:
                for _ in nm.split("."):
                    if stack:
                        stack.pop()
            elif stack:
                stack.pop()
    if pending:
        out.append(pending + (len(text),))
    return [(".".join(p for p in full.split(".") if p), kind, line, text[st:en])
            for full, kind, line, st, en in out]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--seed", action="append", required=True)
    ap.add_argument("-o", "--out", default=None)
    args = ap.parse_args()

    decls = {}
    for base, dirs, files in os.walk(args.root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in sorted(files):
            if fn.endswith(".lean"):
                p = os.path.join(base, fn)
                rel = os.path.relpath(p, args.root)
                with open(p, encoding="utf-8", errors="replace") as fh:
                    decls[rel] = decls_with_ns(blank_comments(fh.read()))

    byfull, suffix = set(), collections.defaultdict(set)
    for ds in decls.values():
        for full, _k, _l, _b in ds:
            byfull.add(full)
    for full in byfull:
        parts = full.split(".")
        for j in range(len(parts)):
            suffix[".".join(parts[j:])].add(full)

    cache, edges = {}, collections.defaultdict(set)
    for ds in decls.values():
        for full, _k, _l, body in ds:
            tgt = edges[full]
            for t in set(IDENT.findall(body)):
                r = cache.get(t)
                if r is None:
                    r = {t} if t in byfull else suffix.get(t, frozenset())
                    cache[t] = r
                tgt |= r
            tgt.discard(full)

    missing = [s for s in args.seed if s not in byfull]
    if missing:
        print("SEED NOT FOUND: %s\n(a seed that does not resolve makes every "
              "number below meaningless)" % missing, file=sys.stderr)
        return 2
    seen, stack = set(), list(args.seed)
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        stack.extend(edges.get(x, ()))

    rows, blind = [], 0
    kinds = collections.Counter()
    for rel, ds in decls.items():
        for full, kind, line, body in ds:
            on = full in seen
            kinds[(kind, on)] += 1
            if not on and IMPLICIT_USE.search(body):
                blind += 1
            rows.append({"file": rel, "line": line, "kind": kind,
                         "name": full, "in_cone": on})

    tot = len(rows)
    inc = sum(1 for r in rows if r["in_cone"])
    print(f"{tot:,} declarations, {inc:,} in the cone of {len(args.seed)} seed(s) "
          f"({100.0 * inc / tot:.1f}%)")
    for (kind, on), v in sorted(kinds.items()):
        print(f"  {kind:10} {'in ' if on else 'out'} {v:7,}")
    print(f"\nblind spot: {blind:,} out-of-cone declarations carry an "
          f"implicit-use attribute (@[simp] and friends), so they can still be "
          f"used without being named. 'Out of cone' is triage, not dead code.")
    if args.out:
        with open(args.out, "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
