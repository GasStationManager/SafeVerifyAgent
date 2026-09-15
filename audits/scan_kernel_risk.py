"""The KERNEL-RISK rung of an audit, over a whole repository.

`scan_repo.py` asks "does this artifact reach outside the ordinary elaboration
path". This script asks a different question, for a different adversary:

    the artifact ALREADY passed a mechanical checker. Which of its proofs would
    a bug in the LEAN KERNEL be able to turn into a fake?

That question is not answered by counting `sorry`. It is answered by locating
the places where the kernel must actually *compute* something, rather than merely
match a proof term against a type. Three families are known-fragile and get
their own census:

1. **recursive inductive types** — recursor/`brecOn` reduction, indexed families,
   higher-order (reflexive) recursive arguments, nested inductives, `Acc.rec`
   and `WellFounded.fix` unfolding, hand-supplied motives.
2. **`Nat` delegated to GMP** — the kernel does not iota-reduce numerals, it calls
   out to GMP for `add/sub/mul/div/mod/beq/ble/pow/gcd/…`. Anything that makes the
   kernel evaluate a numeral (`decide`, `rfl` on arithmetic, `norm_num`
   certificates, `Nat.choose`) rides that path.
3. **custom metaprogramming** — `macro`/`elab`/`syntax`/`set_option`/`attribute`,
   which can change what a symbol MEANS between two files.

Everything here is a MEASUREMENT with a `file:line`. Nothing here is a verdict:
a `decide` over `Fin 4` and a `decide` over a 40-digit numeral are the same
marker and wildly different risks, and only a reader can tell them apart. The
output is a work list, and `INVENTORY.csv` is the coverage ledger — one row per
declaration, so "audited 300 theorems" can be checked against "the file has
38,503".

    python3 audits/scan_kernel_risk.py /path/to/lean-project [-o OUTDIR]
"""

from __future__ import annotations

import argparse
import collections
import csv
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from safeverifyagent.extract import blank_comments   # noqa: E402

SKIP_DIRS = (".lake", ".git", "build", ".venv")

# --- repo-level markers -----------------------------------------------------
# (name, regex). Counted over comment-stripped source, with file:line.
MARKERS = (
    # vector 3 — metaprogramming. In a proof artifact these should all be ZERO;
    # each one is a place where a later file can mean something else by the
    # same notation than the file that was reviewed.
    ("metaprog", r"^[ \t]*(?:macro|macro_rules|syntax|elab|elab_rules|notation|infixl|infixr|prefix|postfix)\b"),
    ("run_cmd", r"\b(?:run_cmd|#eval|#reduce|Lean\.Elab|Lean\.Meta|MetaM|TacticM|CommandElabM)\b"),
    ("set_option", r"\bset_option\b"),
    ("skipKernelTC", r"\bdebug\.skipKernelTC\b"),
    ("attribute", r"^[ \t]*attribute\b"),
    ("local_instance", r"attribute\s*\[[^\]]*local instance[^\]]*\]"),
    # trust surface proper
    ("native_decide", r"\bnative_decide\b"),
    ("unsafe", r"\bunsafe\b"),
    ("extern", r"@\[extern"),
    ("implemented_by", r"implemented_by"),
    ("opaque", r"^[ \t]*opaque\b"),
    ("axiom_decl", r"^[ \t]*axiom\b"),
    ("sorry", r"\bsorry\b|\badmit\b|\bsorryAx\b"),
    ("partial_def", r"\bpartial def\b"),
    # vector 1 — recursion the kernel has to reduce
    ("inductive", r"^[ \t]*inductive\b"),
    ("deriving", r"\bderiving\b"),
    ("termination_by", r"\btermination_by\b"),
    ("decreasing_by", r"\bdecreasing_by\b"),
    ("wf_fix", r"\bWellFounded\.fix\w*\b|\bAcc\.rec\b|\bWellFounded\b"),
    ("explicit_rec", r"\b[A-Z]\w*(?:\.\w+)*\.rec\b|\brecOn\b|\bbrecOn\b"),
    ("motive", r"\(motive\s*:="),
    # vector 2 — numerals the kernel has to evaluate
    ("decide", r"(?<![\w.])decide\b"),
    ("nat_prim", r"\bNat\.(?:pow|div|mod|sub|gcd|log2|shiftLeft|shiftRight|land|lor|xor|testBit|binaryRec|beq|ble|decEq|decLt|decLe)\b"),
    ("bignum7", r"(?<![\w.\d])\d{7,}(?![\w])"),
    ("bigpow", r"\b\d+\s*\^\s*\d{3,}\b"),
    ("choose_fact", r"\bNat\.(?:choose|factorial|ascFactorial|descFactorial)\b"),
)

# --- declaration-level features --------------------------------------------
DECL_START = re.compile(
    r"^(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+"
    r"|unsafe\s+|scoped\s+|local\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|instance|class"
    r"|opaque|axiom|example)\b"
    r"[ \t]*(?P<name>[^\s:({\[\u2983\u27e8]*)", re.M)

FEATURES = (
    ("decide", r"(?<![\w.])decide\b"),
    ("norm_num", r"\bnorm_num\b"),
    ("omega", r"\bomega\b"),
    ("simp", r"\bsimp\b"),
    ("rfl", r"\brfl\b"),
    ("native", r"\bnative_decide\b"),
    ("rec", r"\b[A-Z]\w*(?:\.\w+)*\.rec\b|\brecOn\b"),
    ("induction", r"\binduction\b"),
    ("termination_by", r"\btermination_by\b"),
    ("wf", r"\bWellFounded\b|\bAcc\.rec\b"),
    ("bignum", r"(?<![\w.\d])\d{7,}(?![\w])"),
    ("pow", r"\^"),
    ("choose_fact", r"\bNat\.(?:choose|factorial)\b|\bchoose\b"),
    ("finset", r"Finset\.|Fintype\.|\u2211|\u220f"),
    ("nat_prim", r"\bNat\.(?:pow|div|mod|sub|gcd|beq|ble|decEq)\b"),
)


def lean_files(root):
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for f in sorted(files):
            if f.endswith(".lean"):
                yield os.path.join(base, f)


def parse_decls(text):
    """Top-level declarations of one comment-stripped file, with bodies.

    A body is "everything up to the next top-level declaration", which is
    deliberately coarse: it over-attributes `end`/`variable` lines to the
    preceding declaration and never under-attributes a tactic block. For a
    census whose job is to find where to LOOK, a false positive costs a read
    and a false negative costs the audit.
    """
    ms = list(DECL_START.finditer(text))
    out = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        out.append((m.group("kind"), m.group("name") or "_anon",
                    text[:m.start()].count("\n") + 1, text[m.start():end]))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("-o", "--outdir", default=None,
                    help="write INVENTORY.csv and *_SITES.md here")
    args = ap.parse_args()

    marker_rx = [(n, re.compile(p, re.M)) for n, p in MARKERS]
    feat_rx = [(n, re.compile(p)) for n, p in FEATURES]

    files = list(lean_files(args.root))
    lines = 0
    counts = collections.Counter()
    sites = collections.defaultdict(list)
    kinds = collections.Counter()
    rows = []

    for path in files:
        with open(path, encoding="utf-8", errors="replace") as fh:
            src = fh.read()
        lines += src.count("\n")
        rel = os.path.relpath(path, args.root)
        text = blank_comments(src)
        srclines = text.split("\n")
        for name, rx in marker_rx:
            for m in rx.finditer(text):
                ln = text[:m.start()].count("\n") + 1
                counts[name] += 1
                sites[name].append((rel, ln, srclines[ln - 1].strip()[:160]))
        for kind, dname, ln, body in parse_decls(text):
            kinds[kind] += 1
            row = {"file": rel, "kind": kind, "name": dname, "line": ln,
                   "lines": body.count("\n")}
            for fname, rx in feat_rx:
                row[fname] = len(rx.findall(body))
            rows.append(row)

    print(f"{len(files)} Lean file(s), {lines:,} lines, "
          f"{len(rows):,} declarations")
    print("  " + ", ".join(f"{v:,} {k}" for k, v in kinds.most_common()))
    print("\n=== KERNEL-RISK MARKERS (comment-stripped) ===")
    for name, _ in MARKERS:
        n = counts[name]
        flag = "  " if n else "ZERO"
        where = sorted({s[0] for s in sites[name]})
        print(f"  {flag} {name:16} {n:6}  in {len(where)} file(s)"
              + (f": {where[:2]}" if where else ""))
    print("\nA marker is a place to LOOK, never a verdict: `decide` over `Fin 4` "
          "and `decide` over a 40-digit numeral are the same marker.")

    if args.outdir:
        os.makedirs(args.outdir, exist_ok=True)
        inv = os.path.join(args.outdir, "INVENTORY.csv")
        with open(inv, "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        print(f"\nwrote {inv}  ({len(rows):,} rows — the coverage ledger)")
        for name, _ in MARKERS:
            if not sites[name]:
                continue
            p = os.path.join(args.outdir, f"SITES_{name}.md")
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(f"# `{name}` sites ({counts[name]})\n\n")
                for rel, ln, txt in sites[name]:
                    fh.write(f"- `{rel}:{ln}` — `{txt}`\n")
        print(f"wrote per-marker site lists to {args.outdir}/SITES_*.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
