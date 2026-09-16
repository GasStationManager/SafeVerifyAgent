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
    # Dot notation is half of this surface and the first generation of this
    # regex could not see it: `j.factorial` is `Nat.factorial j`, and an
    # auditor measured 892 factorial terms where this marker reported 6.
    # `.choose` is deliberately NOT here: it is dominated by `Classical.choose`
    # / `Exists.choose`, so it lives in the ambiguous `dot_choose` FEATURE
    # column instead of a marker that looks like a verdict.
    ("choose_fact", r"\bNat\.(?:choose|factorial|ascFactorial|descFactorial)\b"
                    r"|\.(?:factorial|ascFactorial|descFactorial)\b"),
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
    # `choose_fact` was ONE polluted column and an auditor broke it in both
    # directions at once: the regex `Nat\.(choose|factorial)|\bchoose\b` is
    # BLIND to dot notation (`n.factorial`, 892 terms, of which it saw 6) while
    # also counting `Classical.choose`, `h.choose_spec` and the `choose`
    # TACTIC. One number cannot answer "does the kernel compute a binomial".
    # So it is now three columns, and the ambiguous one is named ambiguous:
    # `dot_choose` is `n.choose k` (Nat) AND `h.choose` (Classical) and only a
    # reader can tell them apart -- which is the honest state of affairs.
    ("nat_choose", r"\bNat\.choose\b"),
    ("factorial", r"\bNat\.factorial\b|\.factorial\b"),
    ("dot_choose", r"\.choose\b|(?<![\w.])choose\b"),
    ("finset", r"Finset\.|Fintype\.|\u2211|\u220f"),
    ("nat_prim", r"\bNat\.(?:pow|div|mod|sub|gcd|beq|ble|decEq)\b"),
)



# --- the defeq workload -----------------------------------------------------
# A `rfl` proof is not a COMPUTATION marker, so none of the regexes above see
# it, and it is the one obligation the kernel must discharge by deciding a
# DEFINITIONAL EQUALITY: delta, beta, iota, projection, and structure eta.
# On openai/NavierStokesAndEuler this turned out to be the largest kernel
# surface in the artifact (541 in-cone theorems) while every explicit
# computation marker was tiny -- so it gets measured.
_OPEN, _CLOSE = "([{\u2983\u27e8", ")]}\u2984\u27e9"


def split_decl(body):
    """(statement, proof, kind) for one declaration body.

    Splits at the first TOP-LEVEL `:=`, standalone `by`, or standalone `where`,
    skipping bracketed regions. Both refinements were forced by measurement:
    a naive "first `:=`" split mis-reads a named argument (`(B := B)`) as the
    start of the proof, and it reads a structure-instance proof
    (`theorem foo : P where\n  field _ := rfl`) as a `rfl` proof. Those two
    bugs cost 15 false negatives and 3 false positives out of 541 -- found by
    an auditor who counted independently and disagreed.
    """
    i, depth, n = 0, 0, len(body)

    def standalone(tok, i):
        if not body.startswith(tok, i):
            return False
        before = i == 0 or not (body[i - 1].isalnum() or body[i - 1] == "_")
        j = i + len(tok)
        after = j >= n or not (body[j].isalnum() or body[j] == "_")
        return before and after

    while i < n:
        c = body[i]
        if c in _OPEN:
            depth += 1
        elif c in _CLOSE:
            depth -= 1
        elif depth == 0:
            if body.startswith(":=", i):
                return body[:i], body[i:], "term"
            if standalone("by", i):
                return body[:i], body[i:], "tactic"
            if standalone("where", i):
                return body[:i], body[i:], "where"
        i += 1
    return body, "", "none"


_BARE_RFL = re.compile(r":=\s*(?:by\s+)?rfl\b")

# A `rfl` that CLOSES a tactic block is a defeq obligation too, and it is the
# harder one to bound: `_BARE_RFL` measures theorems whose whole proof is
# `rfl`, so the STATEMENT displays exactly what the kernel must decide. When
# `rfl` closes a block after `simp`/`unfold`/`rw`, the goal it faces is one no
# longer visible in the source, so no statement-level screen can bound its
# iota/delta depth. Measured separately, and reported separately, because a
# bound proved for the first class is NOT a bound for the second.
# Found by the `ns-transition-ramp` auditor, who noticed the census saw 1 of
# its file's 19 proof-closing `rfl`s.
_CLOSING_RFL = re.compile(
    r"(?:^[ \t]*rfl[ \t]*$)|(?:;[ \t]*rfl[ \t]*$)|(?:<;>[ \t]*rfl\b)"
    r"|(?:\bexact[ \t]+rfl\b)", re.M)

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
            stmt, proof, pkind = split_decl(body)
            bare_rfl = (kind in ("theorem", "lemma") and pkind == "term"
                        and bool(_BARE_RFL.match(proof.strip())))
            if bare_rfl:
                counts["bare_rfl_proof"] += 1
                sites["bare_rfl_proof"].append(
                    (rel, ln, f"{dname}  [statement: {len(stmt.strip())} chars]"))
            closing_rfl = 0
            if kind in ("theorem", "lemma") and not bare_rfl:
                closing_rfl = len(_CLOSING_RFL.findall(proof))
                if closing_rfl:
                    counts["closing_rfl"] += 1
                    sites["closing_rfl"].append(
                        (rel, ln, f"{dname}  [{closing_rfl} closing rfl, "
                                  f"statement: {len(stmt.strip())} chars]"))
            row = {"file": rel, "kind": kind, "name": dname, "line": ln,
                   "lines": body.count("\n"), "stmt_chars": len(stmt.strip()),
                   "proof_kind": pkind, "bare_rfl": int(bare_rfl),
                   "closing_rfl": closing_rfl}
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
    print(f"\n=== DEFEQ WORKLOAD ===\n     bare_rfl_proof   "
          f"{counts['bare_rfl_proof']:6}  theorems proved by `rfl` alone")
    print(f"     closing_rfl      {counts['closing_rfl']:6}  further theorems "
          "whose TACTIC block is closed by `rfl`")
    print("  The kernel must decide these by DEFINITIONAL EQUALITY, which is "
          "where structure eta,\n  `Fin`/`Matrix.cons` literal indices, and an "
          "iota chain at a closed argument would\n  appear. No computation "
          "marker sees them. Sorted sites: SITES_bare_rfl_proof.md,\n"
          "  SITES_closing_rfl.md -- and the two are NOT interchangeable: a "
          "bare `rfl`'s statement\n  displays exactly what the kernel must "
          "decide, while a `rfl` closing a block faces a goal\n  `simp`/`rw` "
          "already rewrote, so no statement-level screen bounds its depth.")
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
        for name, _ in list(MARKERS) + [("bare_rfl_proof", ""),
                                         ("closing_rfl", "")]:
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
