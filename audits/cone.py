"""Which declarations can the headline theorems possibly depend on?

An artifact with 38,503 theorems cannot be audited theorem by theorem without a
denominator, and "all of them" is the wrong denominator: a claimed proof is only
as strong as the cone below its *headline* theorems, and a defect in a
declaration nothing references cannot make a false theorem true.

So this builds a NAME-level dependency graph over the whole repository and
reports what the seeds reach. Everything in this file is NAME-level: a node is
a fully qualified name as the source spells it (one per declaring file), an
edge is a token that resolves to one. No elaboration happens anywhere, so nothing here can see an
instance, a coercion, an auto-bound implicit or a `simp` lemma that is used
without being written down. Three subcommands, all on that one graph:

    python3 audits/cone.py ROOT --seed Euler.euler_breakdown_R3 [--seed ...] \
        [-o CONE.csv] [--unsupplied NAMES.txt]
    python3 audits/cone.py route (--root ROOT SEED... | --cone CONE.csv) -o ROUTE.md
    python3 audits/cone.py join CONE.csv CITATIONS.csv -o OUT.csv \
        [--unsupplied NAMES.txt --root ROOT]

The first form is the original CLI and still writes the original six columns
first (`file,line,kind,name,in_cone,in_import_closure`); the columns after them
are what `route` and `join` read:

  depth, via          BFS depth from the nearest seed (seeds are 0) and the BFS
                      parent that pulled the name in. Blank when out of cone.
  consumers           how many OTHER names reference this one, under the same
                      resolution rules as the cone and restricted to the import
                      closure (a reference only counts where the referencing
                      file imports, transitively, the file declaring the name).
  consumers_in_cone   the same, counting only in-cone referencers.
  above_seed          the name reaches a seed through the graph: it is built ON
                      TOP of the headline (a paper-facing restatement, say).
  orphan_file         the declaring file is imported by no file in the repo and
                      is not a library root (lakefile), so a default build may
                      not even compile it.
  in_default_build    the declaring file is in the import closure of a library
                      root. Without a readable lakefile this is every file.
  dead                `direct` if a binder of the declaration names a predicate
                      from `--unsupplied`, `chain` if every one of its (>= 1)
                      consumers is dead. Blank otherwise, and blank for every
                      row when `--unsupplied` was not given.

`route` lists the in-cone declarations in dependency order from the seeds
downward (depth, then file, then line), which is the order a reader walks.
`join` attaches those columns to a list of citations (`file,line` plus any
columns, which pass through) and classifies each cited declaration:

  why = route       in the cone
        dead        out of cone, and `dead` is set (see above)
        orphan      out of cone, in a file nothing imports
        above_seed  out of cone, and it reaches a seed
        wrapper     out of cone otherwise. Note what this means: an out-of-cone
                    name can have NO in-cone consumer (one would pull it in), so
                    every out-of-cone declaration already has "zero consumers
                    or only out-of-cone consumers" and falls here unless an
                    earlier rule caught it. `consumers` says which of the two.
        unknown     the citation did not resolve to a declaration (file not in
                    CONE.csv, or the line precedes the file's first declaration)

The precedence is the order above. `dead` and `orphan` outrank `above_seed`
because both say something stronger: the declaration cannot be applied, or may
not be compiled at all.

Method, and both of its error directions, stated plainly because a reachability
number is quotable and therefore dangerous:

* Declarations are parsed with a `namespace`/`section` stack, so a node is a
  fully qualified name. A reference is any identifier token in a declaration's
  body that resolves to a declared name — exactly, or by matching a SUFFIX of
  one (which is how `open` and namespace-relative naming appear in source).
* Suffix matching OVER-approximates: `add` resolves to every `*.add`. That is
  the safe direction for a cone, since it only makes the audited set bigger.
  It is the UNSAFE direction for `consumers`, which it inflates: a consumer
  count is an upper bound, so "0 consumers" is strong and "3 consumers" is weak.
* It is then CUT BACK by the one sound fact available without a build: a Lean
  file can only cite declarations from modules it imports. So a token in file
  `F` resolves only to names declared in `F` or in `F`'s import closure. This
  is not a heuristic, it is the module system, and it is what separates
  "nobody names it" from "it is not even in scope". Measured on
  openai/NavierStokesAndEuler it removed 5,018 declarations (33,163 -> 28,145),
  including a whole cluster that only *looked* reachable because a bare `.zero`
  token matched it.
* A dotted token is resolved by EVERY suffix of itself, not just the whole
  token, because Lean's dot notation writes the callee against a local: `hx.foo`
  is a use of `Something.foo`. Resolving only the whole token made the cone
  UNDER-approximate, which is the dangerous direction — a worker caught it by
  finding `toEvolution` in the cone while the field it calls was not. Fixed:
  A second worker then found the mirror case, a TRAILING projection
  (`initialDatum_finite_lifespan.choose`), so the resolver now tries every
  contiguous run of components. Measured on the same artifact and seeds, the two
  fixes together grew the cone from 28,145 to 38,369 declarations and recovered
  an entire finiteness spine that had read as dead; one declaration this audit
  had already dismissed as unreachable came back.
* Fixes made for differential-geometry (2026-09-28), each of which changes
  numbers against the NSE runs, and each in a stated direction:
  - A node is now a (name, FILE) pair. A name declared in several files (a
    `private` helper copied between files; `_anon` instances) used to be one
    node, so a reference to one copy reached all of them: 298 in-cone
    declarations lay OUTSIDE the seed's import closure, which the module
    system makes impossible. That invariant (`in_cone` implies
    `in_import_closure`) now holds and is worth re-checking on every run.
  - `theorem _root_.Foo.bar` inside a namespace is named `Foo.bar` (70 in DG).
  - Identifiers use Lean's alphabet (`ℓ`, subscripts, `ĉ`), not ASCII+Greek.
  - `public import` / `meta import` (the Lean module system) were not read as
    imports, so such a file's scope was only itself: UNDER-approximation.
  - `noncomputable section` / `public section` were not scope openers, so their
    `end` popped the enclosing namespace and misnamed everything after it.
  - `variable` binders were tokenised into the PRECEDING declaration's body
    (the body ran to the next declaration). They now belong to every
    declaration that follows in the same scope: the right owner, and an
    over-approximation (Lean only includes the variables a declaration uses).
  - `attribute [instance] foo` lines were likewise tokenised into the
    declaration ABOVE them; their names are now ambient tokens of every later
    declaration in scope, which is where the attribute can take effect.
  - A declaration's body now ENDS at the next column-0 command (`run_cmd`,
    `#eval`, `attribute`, `open`, `set_option`, `notation`, `end`, ...)
    instead of running to the next declaration. Otherwise a `run_cmd` listing
    names to check made the declaration above it "use" every one of them,
    which is harmless for the cone and fatal for `consumers`. The declaration's
    own name in its header is no longer tokenised either (it made every
    `X.foo` a consumer of every other `*.foo` in scope).
* It still UNDER-approximates in one specific and important way: uses that are
  never written down. Instance synthesis, the ambient `@[simp]` set, `gcongr`,
  `positivity`, and `aesop` extensions are all invisible here. So
  "not in the cone" means "no NAMED reference chain from the seeds" — a strong
  triage signal, never a proof of dead code. The script prints how many
  out-of-cone declarations carry an implicit-use attribute, which is the size of
  that blind spot.

Measured on differential-geometry @ 7a48598d, seed `poincare_conjecture`: the
NSE-era script put 85,747 of 158,549 declarations in the cone, this one
85,255. Of the 670 declarations only the old cone had, 555 were copies of a
name declared in several files and the other 115 were reached only through a
trailing command (`open X (a b c)` lists, `attribute` lines) attributed to the
declaration above it. 178 are new: 12 reached through names the old
tokeniser split (`zeroExtendₗᵢ` read as `zeroExtend`, an UNDER-approximation),
10 renamed by the scope fixes, and the rest not traced one by one (the
candidates are `variable`/`attribute` tokens now owned by the declarations
that follow them).

`--shadow-locals` (opt-in) also drops tokens a declaration binds locally
(`obtain ⟨C, hC⟩`, `intro x`, signature binders): Lean resolves those to the
local, so they name no declaration. On DG it moves the cone only 85,255 ->
85,116, so bound variables are NOT what makes this cone 54% of the repository;
dot-notation tails (`h.symm`, `x.trans`, `.C`) resolving to every same-named
declaration in scope are. It is opt-in because its binder reading is flat per
declaration (see `local_names`), which is the under-approximating direction.

C1 (2026-09-28, from a reader's NOSUPPLIER verification): generic identifiers
resolved by short name. `f.trans` reached `MetricComparisonOn.trans`, the
`refine` TACTIC reached `HasStageSeed.refine`, `rw [..] at h` reached
`ExponentialRadiusScaleBounds.at` (3,137 consumers), and `.symm`/`.mono` gave
`BInter.symm` 2,251 and `TerminalParentRegionConvexity.mono` 152 -- which is
how four dead legacy predicates showed large "in-cone" site counts. Now a
single-component run that is a dot-notation TAIL (not the token's first
component, or any component of a token written right after a `.`, as in
`(e).symm.trans` or leading-dot `.refl _`) is not resolved when it is shorter
than 4 characters or in GENERIC_TAILS (`trans symm mono at mk le lt refl mp mpr
cast comp map`); a BARE token that is a tactic word (TACTIC_WORDS) or in
GENERIC_TAILS resolves only to a declaration of exactly that full name; and a
GENERIC_TAILS/tactic word as the leading component of a dotted token
(`trans.toFoo`, a local) is not a receiver. A run with a qualifier
(`MetricComparisonOn.trans`, `Qual.trans`) always resolves. RESCUE: a withheld
candidate `Foo.t` is kept when the same declaration names `Foo` (a binder
`h : Foo`, a `have`, its statement) -- without it, a spot check of 10
departed declarations found 3 genuinely used by dot notation on a hypothesis
(`w.forward.transition.trans` for `StageTransition.trans`, `hnetProp.mono`,
`(hslots j).mono` for `curvOrderAtMost.mono`). The run prints how many edges
were withheld and how many rescued. Measured on differential-geometry, seed
`poincare_conjecture`: 667,418 edges withheld, 12,311 rescued; the cone went
85,255 -> 85,019 (236 declarations left, none entered); consumers of
`HasStageSeed.refine` 4,028 -> 7, `MetricComparisonOn.trans` 1,815 -> 113,
`BInter.symm` 2,251 -> 29, `StageTransition.trans` 2,499 -> 1, and
`ExponentialRadiusScaleBounds.at` and `TerminalParentRegionConvexity.mono`
left the cone. A second sample of 10 departed declarations had no
fully qualified use in cone and no in-cone declaration naming the parent type
with that tail. On the synthetic regression project (`tests/test_audit_tools.py`,
`Reg`) the cone went 7 -> 4 (`Legacy`, `Legacy.trans`, `Legacy.refine` left;
`Qual.trans` and the rescued `Step.trans`, `Step` stayed); on `Demo` it is unchanged
(8). The cone is STILL 53.6% of the artifact: longer generic tails (`.subseq`
keeps 734 consumers and keeps the dead `MetricCompactnessAssumptions`
interface in cone via `HasStageSeed.subseq`) are untouched, so this removes
the worst noise, not the bulk of the over-approximation.
DIRECTION: this is the first rule here that can UNDER-approximate. A genuine
dot use of a project lemma with a generic tail -- `h.trans h'` for `h : Foo`
with a project `Foo.trans`, or leading-dot `.refl _` whose expected type is a
project structure -- is no longer an edge unless the declaration names `Foo`
(the rescue above). `--generic-names` restores the
old resolution and reproduces the pre-C1 CONE.csv byte for byte, so the two
can be diffed; a declaration whose membership depends on the difference is
checked by reading.

Use it to prioritise, and to state coverage honestly: "N of M in-cone theorems
read" is a claim about the right M.

Cost: two streaming passes over the source (the second re-reads each file
rather than holding 300 MB of text), import closures as bitsets, and a per-file
resolution cache. Progress goes to stderr.
"""

import argparse, bisect, collections, csv, os, re, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from safeverifyagent.extract import blank_comments   # noqa: E402

SKIP_DIRS = (".lake", ".git", "build", ".venv")
SEC = "\x00"
# Lean's identifier alphabet (`Lean.isLetterLike`, `isSubScriptAlnum`): ASCII
# letters, Greek except `λ`/`Π`/`Σ`, Coptic, polytonic Greek, the letterlike
# block (`ℓ`, `ℝ`), mathematical alphanumerics, and -- in the Lean this repo
# pins -- Latin-1/Extended letters (`ĉ`). The first version knew only ASCII and
# basic Greek, so `rescale_memℓp` tokenised as `rescale_mem` and resolved to
# nothing: an UNDER-approximation, on 15 declaration names in differential-geometry.
_ID0 = (r"A-Za-z_\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1\u03a4-\u03a9"
        r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u024f"
        r"\U0001d49c-\U0001d59f")
_ID1 = _ID0 + r"0-9!?'\u2019\u2080-\u209c\u1d62-\u1d6a"
IDENT = re.compile(r"[%s][%s]*(?:\.[%s][%s]*)*" % (_ID0, _ID1, _ID0, _ID1))
NS = re.compile(
    r"^[ \t]*(?:(?:noncomputable|public|private)[ \t]+)*"
    r"(namespace|section|end|mutual)\b[ \t]*([\w.α-ω]*)", re.M)
DECL_START = re.compile(
    r"^(?:(?:omit|include|open|set_option)\b[^\n]*?\bin[ \t]+)*"
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|public\s+|noncomputable\s+|nonrec\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|meta\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom|example)\b"
    r"[ \t]*(?P<name>[^\s:({\[⦃⟨]*)", re.M)
# A column-0 command that is not a declaration ENDS the declaration above it.
TERMINATOR = re.compile(
    r"^(?:run_cmd|run_elab|run_meta|#[a-z_]+|attribute\b|open\b|export\b|variable\b|"
    r"universe\b|set_option\b|include\b|omit\b|initialize\b|builtin_initialize\b|"
    r"(?:local\s+|scoped\s+)?(?:macro|macro_rules|syntax|elab|elab_rules|notation|"
    r"infix|infixl|infixr|prefix|postfix|declare_syntax_cat|simproc|dsimproc)\b)", re.M)
VARIABLE = re.compile(r"^[ \t]*variable\b(?P<rest>[^\n]*(?:\n[ \t]+[^\n]*)*)", re.M)
# `attribute [instance] foo` / `attribute [local simp] foo` makes `foo` usable
# WITHOUT being named by what follows. Its names are therefore treated like a
# `variable` block: ambient tokens of every later declaration in scope.
ATTRIBUTE = re.compile(r"^attribute[ \t]*\[[^\]]*\](?P<rest>[^\n]*(?:\n[ \t]+[^\n]*)*)", re.M)
IMPORT = re.compile(r"^(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([\w.]+)", re.M)
IMPLICIT_USE = re.compile(r"@\[[^\]]*(simp|gcongr|positivity|bound|aesop|norm_cast|ext)")
THEOREM_KINDS = ("theorem", "lemma")
# C1 (see the docstring): generic identifiers that resolve by short name to an
# unrelated project declaration. A single-component run that is NOT the leading
# component of its token (a dot-notation tail or projection: `f.trans`,
# `h.symm.le`) is skipped when shorter than 4 characters or in GENERIC_TAILS;
# a bare token that is a tactic word or in GENERIC_TAILS resolves only to a
# declaration of exactly that full name.
GENERIC_TAILS = frozenset("trans symm mono at mk le lt refl mp mpr cast comp map".split())
TACTIC_WORDS = frozenset("""refine exact apply intro intros constructor use exists show
    have let obtain rcases rintro cases induction simp rw calc congr ext funext subst
    unfold change specialize aesop omega linarith nlinarith positivity norm_num ring
    field_simp gcongr filter_upwards exfalso contradiction trivial rfl decide
    left right exact_mod_cast push_cast norm_cast split_ifs by_cases by_contra
    choose lift set generalize revert clear rename refine' convert""".split())


_SID = r"[%s][%s]*" % (_ID0, _ID1)
_NOT_PROJ = r"(?<![.\w])"      # `And.intro a b` is a term, `intro a b` a tactic
# (x y : T) {x : T} ⦃x : T⦄ [inst : C] -- names before the colon. Applied to the
# SIGNATURE and `variable` blocks only: in a proof, `(f x : T)` is an
# ascription, and reading `f` as bound there would drop a real reference.
_BINDER = re.compile(r"[(\[{\u2983]\s*((?:%s\s+)*%s)\s*:(?!=)" % (_SID, _SID))
_LOCAL_PATTERNS = (
    # have h : / let x := / set x := / obtain h : / generalize h : / suffices h :
    re.compile(_NOT_PROJ + r"(?:have|let|set|obtain|generalize|suffices|haveI|letI)\s+(%s)\s*(?::|:=)" % _SID),
    # intro a b / intros / rintro ⟨a, b⟩ / ext x / funext x -- to the end of the tactic
    re.compile(_NOT_PROJ + r"(?:intro|intros|rintro|ext|funext|introv)\b([^\n;:=|]*)"),
    # obtain ⟨a, b⟩ ... / rcases e with ⟨a, b⟩ / set x := e with hx
    re.compile(_NOT_PROJ + r"obtain\s+(\u27e8[^\n]*?\u27e9)"),
    re.compile(r"\bwith\s+(\u27e8[^\n]*?\u27e9|(?:%s[ \t]*)+)(?=[ \t]*(?:$|:=|;))" % _SID, re.M),
    # choose f hf using
    re.compile(_NOT_PROJ + r"choose!?\s+((?:%s\s+)+)using" % _SID),
    # fun x y => / fun ⟨a, b⟩ => / fun (x : T) => / λ x ↦
    re.compile(_NOT_PROJ + r"(?:fun|\u03bb)\s+([^\n]*?)(?:=>|\u21a6)"),
    # ∀ x y, / ∃ x ∈ s, / ∑ i in s, ...
    re.compile(r"[\u2200\u2203\u2211\u220f\u22c3\u22c2]!?\s*((?:%s\s*)+)(?=[,:\u2208<>\u2264\u2265])" % _SID),
)


def _names(seg, out):
    seg = re.sub(r":[^)\]}\u2984]*", " ", seg)   # `(x : T)`: only `x` is bound
    for t in IDENT.findall(seg):
        if "." not in t:
            out.add(t)


def body_tokens(body, start=0):
    """Identifier tokens of `body[start:]`; a token written right after a `.`
    (dot notation on an expression, or leading-dot `.refl`) is returned with
    that `.` in front, so the resolver knows its first component is a tail."""
    out = set()
    for m in IDENT.finditer(body, start):
        t = m.group(0)
        if m.start() > 0 and body[m.start() - 1] == ".":
            t = "." + t
        out.add(t)
    return out


def binder_names(text):
    out = set()
    for m in _BINDER.finditer(text):
        _names(m.group(1), out)
    return out


def local_names(body):
    """Single-component names a declaration binds locally: signature binders,
    and `intro`/`obtain`/`fun`/`∀`/`have h :` names in its body. Lean resolves
    a bare name to a local before any global, so such a token names no
    declaration. FLAT per declaration: a name bound anywhere in it counts as
    bound everywhere in it, which is the one way this can drop a real
    reference (a global `C` written in the same declaration that binds a local
    `C` elsewhere). That is why it is opt-in (`--shadow-locals`)."""
    cut = body.find(":=")
    out = binder_names(body if cut < 0 else body[:cut])
    for rx in _LOCAL_PATTERNS:
        for m in rx.finditer(body):
            _names(m.group(1), out)
    return out


def progress(msg):
    print(msg, file=sys.stderr, flush=True)


def decls_full(text):
    """[(full_name, kind, line, body, header_end, var_tokens, var_bound)].

    `body` runs from the declaration keyword to the next declaration or column-0
    command; `header_end` is the offset in `body` just past the declared name;
    `var_tokens` is the frozenset of identifier tokens of every `variable` block
    and every `attribute [..] names` line in scope at the declaration, and
    `var_bound` the names those `variable` blocks bind.
    """
    events = [("d", m.start(), m) for m in DECL_START.finditer(text)]
    events += [("n", m.start(), m) for m in NS.finditer(text)]
    events += [("t", m.start(), m) for m in TERMINATOR.finditer(text)]
    events += [("v", m.start(), m) for m in VARIABLE.finditer(text)]
    events += [("a", m.start(), m) for m in ATTRIBUTE.finditer(text)]
    order = {"n": 0, "v": 1, "a": 1, "t": 2, "d": 3}
    events.sort(key=lambda e: (e[1], order[e[0]]))
    stack, vstack, out, pending = [], [[]], [], None
    line, lpos = 1, 0
    vtoks = vbound = frozenset()

    def recompute():
        s, b = set(), set()
        for lvl in vstack:
            for toks, bound in lvl:
                s |= toks
                b |= bound
        return frozenset(s), frozenset(b)

    for typ, pos, m in events:
        line += text.count("\n", lpos, pos)
        lpos = pos
        col0 = (pos == 0 or text[pos - 1] == "\n") and not text[pos].isspace()
        if typ == "d":
            if pending:
                out.append(pending + (pos,))
            ns = [s for s in stack if s != SEC]
            nm = m.group("name") or "_anon"
            # `theorem _root_.Foo.bar` inside a namespace declares `Foo.bar`
            full = nm[len("_root_."):] if nm.startswith("_root_.") else ".".join(ns + [nm])
            pending = (full,
                       m.group("kind"), line, m.start(), m.end() - m.start(), vtoks, vbound)
            continue
        if col0 and pending and (typ == "t" or typ == "n" or typ == "v"):
            out.append(pending + (pos,))
            pending = None
        if typ == "a":
            if col0:
                vstack[-1].append((frozenset(IDENT.findall(m.group("rest"))), frozenset()))
                vtoks, vbound = recompute()
        elif typ == "v":
            vstack[-1].append((frozenset(IDENT.findall(m.group("rest"))),
                               frozenset(binder_names(m.group("rest")))))
            vtoks, vbound = recompute()
        elif typ == "n":
            kw, nm = m.group(1), m.group(2)
            if kw == "namespace":
                stack.append(nm or SEC)
                vstack.append([])
            elif kw in ("section", "mutual"):
                stack.append(SEC)
                vstack.append([])
            else:  # end
                for _ in (nm.split(".") if nm else [None]):
                    if stack:
                        stack.pop()
                    if len(vstack) > 1:
                        vstack.pop()
                vtoks, vbound = recompute()
    if pending:
        out.append(pending + (len(text),))
    return [(".".join(p for p in full.split(".") if p), kind, line, text[st:en], hdr, vt, vb)
            for full, kind, line, st, hdr, vt, vb, en in out]


def decls_with_ns(text):
    """[(full_name, kind, line, body)] -- the original interface."""
    return [(f, k, l, b) for f, k, l, b, _h, _v, _vb in decls_full(text)]


def lean_files(root):
    out = []
    for base, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        for fn in sorted(files):
            if fn.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(base, fn), root))
    return sorted(out)


def read_blank(root, rel):
    with open(os.path.join(root, rel), encoding="utf-8", errors="replace") as fh:
        return blank_comments(fh.read())


def lib_roots(root, modules):
    """Library root modules from lakefile.toml / lakefile.lean, or None.

    Reads `[[lean_lib]] name/roots/globs` (TOML) and `lean_lib X where roots :=
    #[...]` (Lean). A glob `X.+` or `X.*` makes every module under `X` a root.
    Regex-level, deliberately: an unreadable lakefile returns None and every
    file is then treated as built, which errs toward NOT calling a file an
    orphan.
    """
    roots, globs = set(), []
    t = os.path.join(root, "lakefile.toml")
    l = os.path.join(root, "lakefile.lean")
    if os.path.exists(t):
        txt = open(t, encoding="utf-8", errors="replace").read()
        for block in re.split(r"^\s*\[\[", txt, flags=re.M)[1:]:
            if not block.startswith("lean_lib"):
                continue
            nm = re.search(r'^\s*name\s*=\s*"([^"]+)"', block, re.M)
            rs = re.search(r"^\s*roots\s*=\s*\[([^\]]*)\]", block, re.M)
            gs = re.search(r"^\s*globs\s*=\s*\[([^\]]*)\]", block, re.M)
            if rs:
                roots |= set(re.findall(r'"([^"]+)"', rs.group(1)))
            elif nm:
                roots.add(nm.group(1))
            if gs:
                globs += re.findall(r'"([^"]+)"', gs.group(1))
    elif os.path.exists(l):
        txt = open(l, encoding="utf-8", errors="replace").read()
        for m in re.finditer(r"lean_lib\s+«?([\w.]+)»?([^\n]*(?:\n[ \t]+[^\n]*)*)", txt):
            rs = re.search(r"roots\s*:=\s*#\[([^\]]*)\]", m.group(2))
            if rs:
                roots |= set(re.findall(r"`«?([\w.]+)", rs.group(1)))
            else:
                roots.add(m.group(1))
            gs = re.findall(r"\.(?:andSubmodules|submodules)\s*`«?([\w.]+)", m.group(2))
            globs += [g + ".+" for g in gs]
    else:
        return None
    for g in globs:
        base = g.rstrip("+*").rstrip(".")
        roots |= {m for m in modules if m == base or m.startswith(base + ".")}
    return roots


def closures(imports):
    """Import closure of every module as a bitset (bit i = module i), from
    `imports[i]` = the in-repo modules module i imports. Lean imports are
    acyclic; a cycle would be a broken build, and is tolerated."""
    nf = len(imports)
    closure = [None] * nf
    for s in range(nf):
        if closure[s] is not None:
            continue
        stack = [(s, 0)]
        onstack = {s}
        while stack:
            x, i = stack[-1]
            if i < len(imports[x]):
                stack[-1] = (x, i + 1)
                y = imports[x][i]
                if closure[y] is None and y not in onstack:
                    onstack.add(y)
                    stack.append((y, 0))
            else:
                stack.pop()
                onstack.discard(x)
                c = 1 << x
                for y in imports[x]:
                    if closure[y] is not None:
                        c |= closure[y]
                closure[x] = c
    return closure


def module_name(rel):
    return rel[:-5].replace(os.sep, ".").replace("/", ".")


class Graph:
    """The name-level graph of one repository. See the module docstring."""

    def __init__(self, root, unsupplied=None, quiet=False, shadow_locals=False,
                 generic_names=False):
        self.root = root
        say = (lambda *_: None) if quiet else progress
        t0 = time.time()
        self.files = lean_files(root)
        nf = len(self.files)
        self.mod = [module_name(rel) for rel in self.files]
        mod_idx = {m: i for i, m in enumerate(self.mod)}

        # ---- pass 1: declarations and imports, no bodies kept
        self.decls = []            # (file_idx, line, kind, node, implicit_use)
        self.names, self.name_id = [], {}
        name_mods = []             # name_id -> list of module indices
        # A NODE is (name, file). A name declared in several files -- a
        # `private` helper copied between files, `_anon` instances of one
        # namespace -- is one node per file, and a reference reaches only the
        # copies in its scope. Merging them (the NSE-era behaviour) pulled 298
        # declarations from OUTSIDE the seed's import closure into the
        # differential-geometry cone, which the module system makes impossible.
        self.node_name, self.node_file, node_of = [], [], {}
        name_nodes = []            # name_id -> [(node, file_idx)]
        imports = [[] for _ in range(nf)]
        for fi, rel in enumerate(self.files):
            txt = read_blank(root, rel)
            imports[fi] = sorted({mod_idx[m] for m in IMPORT.findall(txt) if m in mod_idx})
            for full, kind, line, body, _h, _v, _vb in decls_full(txt):
                nid = self.name_id.get(full)
                if nid is None:
                    nid = self.name_id[full] = len(self.names)
                    self.names.append(full)
                    name_mods.append([])
                    name_nodes.append([])
                if fi not in name_mods[nid]:
                    name_mods[nid].append(fi)
                node = node_of.get((nid, fi))
                if node is None:
                    node = node_of[(nid, fi)] = len(self.node_name)
                    self.node_name.append(nid)
                    self.node_file.append(fi)
                    name_nodes[nid].append((node, fi))
                self.decls.append((fi, line, kind, node, bool(IMPLICIT_USE.search(body))))
            if (fi + 1) % 2000 == 0:
                say(f"[cone] pass 1: {fi + 1:,}/{nf:,} files")
        self.imports = imports
        self.name_mods = name_mods
        self.name_nodes = name_nodes
        nn = len(self.node_name)
        say(f"[cone] pass 1 done: {nf:,} files, {len(self.decls):,} declarations, "
            f"{len(self.names):,} names, {nn:,} (name, file) nodes ({time.time() - t0:.0f}s)")

        suffix = collections.defaultdict(list)
        for nid, full in enumerate(self.names):
            parts = full.split(".")
            for j in range(len(parts)):
                suffix[".".join(parts[j:])].append(nid)
        self.suffix = {k: tuple(v) for k, v in suffix.items()}

        self.closure = closures(imports)
        self.importers = [0] * nf
        for fi in range(nf):
            for y in imports[fi]:
                self.importers[y] += 1
        roots = lib_roots(root, self.mod)
        if roots is None:
            self.built = (1 << nf) - 1
            self.lib_roots = None
        else:
            self.lib_roots = sorted(r for r in roots if r in mod_idx)
            b = 0
            for r in self.lib_roots:
                b |= self.closure[mod_idx[r]]
            self.built = b
        root_set = set(self.lib_roots or ())
        self.orphan = [self.importers[i] == 0 and self.mod[i] not in root_set
                       for i in range(nf)]

        # ---- pass 2: edges, per file, scope-filtered
        edges = [set() for _ in range(nn)]
        self.c1_removed = 0            # edges only the C1 filter dropped
        self.c1_rescued = 0            # ... kept because the parent type is named
        self.direct_dead = set()
        unsup_names = set(unsupplied or ())
        unsup = {self.name_id[n] for n in unsup_names if n in self.name_id}
        if unsup_names:
            from nosupplier import split_sig          # lazy: nosupplier imports us
        for fi, rel in enumerate(self.files):
            txt = read_blank(root, rel)
            bits = self.closure[fi].to_bytes((nf + 7) // 8, "little")
            cache = {}

            def res2(t):
                """(nodes a token reaches, nodes only the C1 filter kept it from)"""
                r = cache.get(t)
                if r is None:
                    key = t
                    # a token written right after a `.` (`(e).symm.trans`,
                    # `.refl _`) is dot notation all the way: its first
                    # component is a tail too, not a receiver or namespace
                    tail_tok = t.startswith(".")
                    if tail_tok:
                        t = t[1:]
                    parts = t.split(".")
                    cands, gen = set(), set()
                    # every CONTIGUOUS run of components: `hx.foo` is a use of
                    # `Something.foo` (leading receiver), and `h.choose` is a use
                    # of `h` (trailing projection). Missing either made the cone
                    # too small, which is the direction that loses live code.
                    if len(parts) == 1 and not tail_tok and (t in TACTIC_WORDS or t in GENERIC_TAILS):
                        # C1: a bare tactic word / generic name only by full name
                        nid0 = self.name_id.get(t)
                        if nid0 is not None:
                            cands.add(nid0)
                        gen.update(self.suffix.get(t, ()))
                    else:
                        for i in range(len(parts)):
                            for j in range(i + 1, len(parts) + 1):
                                got = self.suffix.get(".".join(parts[i:j]), ())
                                if (not generic_names and j == i + 1 and (
                                        ((i > 0 or tail_tok)
                                         and (len(parts[i]) < 4 or parts[i] in GENERIC_TAILS))
                                        # a generic word as the RECEIVER of a
                                        # dotted token (`trans.toFoo`) is a
                                        # local, not every `*.trans`
                                        or (i == 0 and len(parts) > 1 and (
                                            parts[0] in GENERIC_TAILS
                                            or parts[0] in TACTIC_WORDS)))):
                                    gen.update(got)      # C1: a generic dot tail
                                else:
                                    cands.update(got)
                    if generic_names:
                        cands |= gen
                    gen -= cands
                    inscope = lambda cs: frozenset(
                        node for c in cs for node, m in name_nodes[c]
                        if bits[m >> 3] >> (m & 7) & 1)
                    r = (inscope(cands), inscope(gen) if gen else frozenset())
                    cache[key] = r
                return r

            def res(t):
                return res2(t)[0]

            for full, _kind, _line, body, hdr, vtoks, vbound in decls_full(txt):
                nid = node_of[(self.name_id[full], fi)]
                tgt = edges[nid]
                toks = body_tokens(body, hdr) | vtoks
                if shadow_locals:
                    loc = local_names(body[hdr:]) | vbound
                    if loc:
                        kept = set()
                        for t in toks:
                            head, _dot, rest = t.lstrip(".").partition(".")
                            if t.startswith("."):
                                kept.add(t)        # dot notation: never a local
                                continue
                            if head not in loc:
                                kept.add(t)
                            elif rest:
                                kept.add("." + rest)   # `C.foo`, local `C`: `foo` still counts, as a tail
                        toks = kept
                dropped = set()
                for t in toks:
                    kept, gen = res2(t)
                    tgt |= kept
                    if gen:
                        dropped |= gen
                if dropped:
                    # C1 rescue: `h.mono` IS a use of `Foo.mono` when `h : Foo`,
                    # and the declaration then almost always spells `Foo`
                    # (a binder, a `have`, its statement). Keep a withheld
                    # candidate whose parent's short name the declaration
                    # names; drop the rest.
                    dropped -= tgt
                    comps = {c for t in toks for c in t.lstrip(".").split(".")}
                    for n in dropped:
                        par = self.names[self.node_name[n]].rsplit(".", 2)
                        if len(par) >= 2 and par[-2] in comps:
                            tgt.add(n)
                            self.c1_rescued += 1
                tgt.discard(nid)
                if dropped:
                    self.c1_removed += len(dropped - tgt - {nid})
                if unsup:
                    binders, _c, _p = split_sig(body[hdr:])
                    for t in set(IDENT.findall(binders)) | vtoks:
                        if self._specific(t, res) & unsup:
                            self.direct_dead.add(nid)
                            break
            if (fi + 1) % 2000 == 0:
                say(f"[cone] pass 2: {fi + 1:,}/{nf:,} files")
        self.edges = edges
        self.unsupplied_given = bool(unsup_names)
        self.unsupplied_missing = sorted(n for n in unsup_names if n not in self.name_id)
        cons = [0] * nn
        for s in range(nn):
            for t in edges[s]:
                cons[t] += 1
        self.consumers = cons
        say(f"[cone] graph built: {sum(cons):,} name-level edges ({time.time() - t0:.0f}s)")

    def _specific(self, tok, res):
        """Names a binder token denotes, MOST-specifically: the longest run of
        its components that resolves in scope. Used for `dead`, where the
        over-approximating rule would call a theorem dead because a bare
        `Budget` also matches an unsupplied twin."""
        parts = tok.split(".")
        for ln in range(len(parts), 0, -1):
            got = set()
            for i in range(len(parts) - ln + 1):
                run = ".".join(parts[i:i + ln])
                got |= {self.node_name[n] for n in res(run)} & set(self.suffix.get(run, ()))
            if got:
                return got if len(got) == 1 else set()   # ambiguous: no verdict
        return set()

    def seed_nodes(self, seeds):
        missing = [s for s in seeds if s not in self.name_id]
        if missing:
            raise KeyError(missing)
        return [n for s in seeds for n, _f in self.name_nodes[self.name_id[s]]]

    def cone(self, seeds):
        depth, via = {}, {}
        q = collections.deque()
        for n in self.seed_nodes(seeds):
            if n not in depth:
                depth[n] = 0
                via[n] = None
                q.append(n)
        while q:
            x = q.popleft()
            for y in sorted(self.edges[x]):
                if y not in depth:
                    depth[y] = depth[x] + 1
                    via[y] = x
                    q.append(y)
        return depth, via

    def reaches(self, seeds):
        """Names with a reference path TO a seed (reverse BFS)."""
        rev = [[] for _ in self.node_name]
        for s, ts in enumerate(self.edges):
            for t in ts:
                rev[t].append(s)
        seen = set()
        q = collections.deque(self.seed_nodes(seeds))
        while q:
            x = q.popleft()
            for y in rev[x]:
                if y not in seen:
                    seen.add(y)
                    q.append(y)
        return seen

    def dead(self):
        """{node: 'direct'|'chain'}. `chain`: every consumer (>= 1) is dead.
        Least fixpoint, so a cycle of names consuming only each other is NOT
        called dead -- the safe direction for a label that tells a reader to
        skip something."""
        out = {n: "direct" for n in self.direct_dead}
        live = list(self.consumers)
        q = collections.deque(out)
        while q:
            x = q.popleft()
            for t in self.edges[x]:
                live[t] -= 1
                if live[t] == 0 and self.consumers[t] > 0 and t not in out:
                    out[t] = "chain"
                    q.append(t)
        return out

    def rows(self, seeds):
        depth, via = self.cone(seeds)
        seed_scope = 0
        for n in self.seed_nodes(seeds):
            seed_scope |= self.closure[self.node_file[n]]
        above = self.reaches(seeds)
        dead = self.dead() if self.unsupplied_given else {}
        cic = [0] * len(self.node_name)
        for s in depth:
            for t in self.edges[s]:
                cic[t] += 1
        out = []
        for fi, line, kind, nid, imp in self.decls:
            d = depth.get(nid)
            out.append({
                "file": self.files[fi], "line": line, "kind": kind,
                "name": self.names[self.node_name[nid]], "in_cone": d is not None,
                "in_import_closure": bool(seed_scope >> fi & 1),
                "depth": "" if d is None else d,
                "via": "" if d is None or via[nid] is None
                       else self.names[self.node_name[via[nid]]],
                "consumers": self.consumers[nid], "consumers_in_cone": cic[nid],
                "above_seed": nid in above and d is None,
                "orphan_file": self.orphan[fi],
                "in_default_build": bool(self.built >> fi & 1),
                "dead": dead.get(nid, ""),
                "_implicit": imp,
            })
        return out


def read_names(path):
    """Unsupplied predicate names: one per line (`#` comments), or a
    NOSUPPLIER.csv, whose `no_supplier` and `conditional` rows are taken.
    `no_supplier_in_cone` rows are NOT: those predicates are supplied, just
    not on the route, so a declaration assuming one is not dead."""
    with open(path, encoding="utf-8") as fh:
        head = fh.readline()
        fh.seek(0)
        if head.startswith("predicate,"):
            out = []
            for r in csv.DictReader(fh):
                if r.get("status", "no_supplier") in ("no_supplier", "conditional"):
                    out.append(r["predicate"])
            return out
        out = []
        for ln in fh:
            ln = ln.split("#", 1)[0].strip()
            if ln:
                out.append(ln)
        return out


def write_csv(path, rows):
    rows = [{k: v for k, v in r.items() if not k.startswith("_")} for r in rows]
    with open(path, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


# ---------------------------------------------------------------------------
def cmd_cone(argv):
    ap = argparse.ArgumentParser(prog="cone.py")
    ap.add_argument("root")
    ap.add_argument("--seed", action="append", required=True)
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--unsupplied", default=None,
                    help="file of unsupplied predicate names (one per line, or "
                         "NOSUPPLIER.csv) -> fills the `dead` column")
    ap.add_argument("--shadow-locals", action="store_true",
                    help="drop tokens the declaration binds locally (tighter; see local_names)")
    ap.add_argument("--generic-names", action="store_true",
                    help="resolve generic dot tails and tactic words by short name "
                         "(the pre-C1 behaviour; wider, for comparison)")
    args = ap.parse_args(argv)
    uns = read_names(args.unsupplied) if args.unsupplied else None
    g = Graph(args.root, unsupplied=uns, shadow_locals=args.shadow_locals,
              generic_names=args.generic_names)
    try:
        rows = g.rows(args.seed)
    except KeyError as e:
        print("SEED NOT FOUND: %s\n(a seed that does not resolve makes every "
              "number below meaningless)" % e.args[0], file=sys.stderr)
        return 2
    kinds = collections.Counter((r["kind"], r["in_cone"]) for r in rows)
    blind = sum(1 for r in rows if not r["in_cone"] and r["_implicit"])
    tot = len(rows)
    inc = sum(1 for r in rows if r["in_cone"])
    print(f"{tot:,} declarations, {inc:,} in the cone of {len(args.seed)} seed(s) "
          f"({100.0 * inc / tot:.1f}%)")
    print(f"C1: {g.c1_removed:,} name-level edges NOT added because they came only from "
          f"a generic dot tail (<4 chars or {' '.join(sorted(GENERIC_TAILS))}) or a bare "
          f"tactic word" + (" (--generic-names: they were added)" if args.generic_names else
                              f"; {g.c1_rescued:,} kept because the declaration names the "
                              f"candidate's parent type"))
    for (kind, on), v in sorted(kinds.items()):
        print(f"  {kind:10} {'in ' if on else 'out'} {v:7,}")
    print(f"\nblind spot: {blind:,} out-of-cone declarations carry an "
          f"implicit-use attribute (@[simp] and friends), so they can still be "
          f"used without being named. 'Out of cone' is triage, not dead code.")
    orph = sorted({r["file"] for r in rows if r["orphan_file"]})
    unbuilt = sorted({r["file"] for r in rows if not r["in_default_build"]})
    print(f"\nlibrary roots: {g.lib_roots if g.lib_roots is not None else 'no lakefile read'}; "
          f"{len(orph):,} orphan file(s) (imported by nothing, not a root); "
          f"{len(unbuilt):,} file(s) outside the default build")
    for f in orph[:10]:
        print(f"  orphan: {f}")
    if uns is not None:
        dd = collections.Counter(r["dead"] for r in rows if r["dead"])
        print(f"\ndead (from {len(uns):,} unsupplied names; "
              f"{len(g.unsupplied_missing):,} not declared in this repo): "
              f"{dd.get('direct', 0):,} declarations direct, {dd.get('chain', 0):,} by chain; "
              f"in cone: {sum(1 for r in rows if r['dead'] and r['in_cone']):,}")
    if args.out:
        write_csv(args.out, rows)
        print(f"wrote {args.out}")
    return 0


def load_cone_csv(path):
    with open(path, newline="", encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh))
    for r in rows:
        r["line"] = int(r["line"])
    return rows


def truthy(v):
    return str(v).strip().lower() in ("true", "1", "yes")


def cmd_route(argv):
    ap = argparse.ArgumentParser(prog="cone.py route")
    ap.add_argument("seeds", nargs="*")
    ap.add_argument("--root", default=None)
    ap.add_argument("--cone", default=None, help="reuse a CONE.csv (seeds are its depth-0 rows)")
    ap.add_argument("-o", "--out", required=True)
    ap.add_argument("--max-depth", type=int, default=None)
    ap.add_argument("--shadow-locals", action="store_true")
    ap.add_argument("--generic-names", action="store_true")
    args = ap.parse_args(argv)
    if args.cone:
        rows = load_cone_csv(args.cone)
        if "depth" not in rows[0]:
            print("CONE.csv has no `depth` column: re-run cone.py (it predates `route`)",
                  file=sys.stderr)
            return 2
        seeds = sorted({r["name"] for r in rows if r["depth"] == "0"})
        if args.seeds and set(args.seeds) != set(seeds):
            print(f"seeds {args.seeds} differ from the CONE.csv's depth-0 rows {seeds}",
                  file=sys.stderr)
            return 2
    else:
        if not (args.root and args.seeds):
            print("route needs --root ROOT SEED... or --cone CONE.csv", file=sys.stderr)
            return 2
        seeds = args.seeds
        g = Graph(args.root, shadow_locals=args.shadow_locals,
                  generic_names=args.generic_names)
        try:
            rows = g.rows(seeds)
        except KeyError as e:
            print("SEED NOT FOUND: %s" % e.args[0], file=sys.stderr)
            return 2
    inc = [r for r in rows if truthy(r["in_cone"])]
    for r in inc:
        r["depth"] = int(r["depth"])
    inc.sort(key=lambda r: (r["depth"], r["file"], r["line"]))
    if args.max_depth is not None:
        shown = [r for r in inc if r["depth"] <= args.max_depth]
    else:
        shown = inc
    bydepth = collections.Counter(r["depth"] for r in inc)
    bykind = collections.Counter(r["kind"] for r in inc)
    files = collections.OrderedDict()
    for r in inc:
        f = files.setdefault(r["file"], [r["depth"], 0, 0])
        f[1] += 1
        f[2] += r["kind"] in THEOREM_KINDS
    L = [f"# Route from {', '.join('`%s`' % s for s in seeds)}", "",
         "Generated by `audits/cone.py route`. NAME-level: a row is a declaration some "
         "name-level reference chain from the seeds reaches (see `cone.py`'s docstring "
         "for both error directions). Order is BFS depth from the seeds, then file, then "
         "line: the order a reader walks. `via` is the BFS parent that first pulled the "
         "row in, i.e. one reason it is here, not the only one.", "",
         f"**{len(inc):,}** in-cone declarations "
         f"({sum(bykind[k] for k in THEOREM_KINDS):,} theorems/lemmas) in **{len(files):,}** files; "
         f"max depth {max(bydepth) if bydepth else 0}.", "",
         "| depth | declarations |", "|---|---|"]
    L += [f"| {d} | {n:,} |" for d, n in sorted(bydepth.items())]
    L += ["", "| kind | in cone |", "|---|---|"]
    L += [f"| {k} | {n:,} |" for k, n in bykind.most_common()]
    L += ["", "## Files in route order", "",
          "First depth at which the file is entered, in-cone declarations, in-cone theorems.", "",
          "| first depth | file | in-cone decls | in-cone theorems |", "|---|---|---|---|"]
    L += [f"| {v[0]} | `{f}` | {v[1]} | {v[2]} |" for f, v in files.items()]
    L += ["", "## Declarations", ""]
    if args.max_depth is not None:
        L += [f"(depth <= {args.max_depth} shown: {len(shown):,} of {len(inc):,})", ""]
    L += ["| depth | file:line | name | kind | consumers | via |", "|---|---|---|---|---|---|"]
    for r in shown:
        L.append(f"| {r['depth']} | `{r['file']}:{r['line']}` | `{r['name']}` | {r['kind']} "
                 f"| {r['consumers']} | {('`%s`' % r['via']) if r['via'] else ''} |")
    with open(args.out, "w", encoding="utf-8") as fh:
        fh.write("\n".join(L) + "\n")
    print(f"{len(inc):,} in-cone declarations, max depth {max(bydepth) if bydepth else 0}; "
          f"wrote {args.out}")
    return 0


class FileIndex:
    """Resolve a cited path to a CONE.csv file: exact, else the longest
    component-boundary suffix that names exactly one file."""

    def __init__(self, files):
        self.files = set(files)
        self.by_suffix = collections.defaultdict(set)
        for f in files:
            parts = f.split("/")
            for i in range(len(parts)):
                self.by_suffix["/".join(parts[i:])].add(f)

    def resolve(self, path):
        """(set of matching files) -- empty if none; >1 means ambiguous."""
        p = path.strip().strip("`").replace("\\", "/")
        while p.startswith("./"):
            p = p[2:]
        if p in self.files:
            return {p}
        parts = p.split("/")
        for i in range(len(parts)):
            got = self.by_suffix.get("/".join(parts[i:]))
            if got:
                return set(got)
        return set()


def cmd_join(argv):
    ap = argparse.ArgumentParser(prog="cone.py join")
    ap.add_argument("cone_csv")
    ap.add_argument("citations")
    ap.add_argument("-o", "--out", required=True)
    ap.add_argument("--unsupplied", default=None)
    ap.add_argument("--root", default=None,
                    help="needed with --unsupplied: the graph is rebuilt to compute `dead`")
    ap.add_argument("--shadow-locals", action="store_true",
                    help="with --root: build the graph as `cone.py --shadow-locals` did")
    ap.add_argument("--generic-names", action="store_true",
                    help="with --root: build the graph as `cone.py --generic-names` did")
    args = ap.parse_args(argv)
    rows = load_cone_csv(args.cone_csv)
    need = ("consumers", "consumers_in_cone", "above_seed", "orphan_file")
    if any(k not in rows[0] for k in need):
        print(f"{args.cone_csv} lacks {need}: re-run cone.py (it predates `join`)",
              file=sys.stderr)
        return 2
    dead_of = {}
    if args.unsupplied:
        if not args.root:
            print("--unsupplied needs --root (dead-ness is computed from source)",
                  file=sys.stderr)
            return 2
        g = Graph(args.root, unsupplied=read_names(args.unsupplied),
                  shadow_locals=args.shadow_locals, generic_names=args.generic_names)
        dead_of = {(g.files[g.node_file[n]], g.names[g.node_name[n]]): v
                   for n, v in g.dead().items()}
    elif "dead" in rows[0]:
        dead_of = {(r["file"], r["name"]): r["dead"] for r in rows if r["dead"]}
    byfile = collections.defaultdict(list)
    for r in rows:
        byfile[r["file"]].append(r)
    for v in byfile.values():
        v.sort(key=lambda r: r["line"])
    starts = {f: [r["line"] for r in v] for f, v in byfile.items()}
    idx = FileIndex(byfile)

    with open(args.citations, newline="", encoding="utf-8") as fh:
        rd = csv.DictReader(fh)
        cites = list(rd)
        fields = list(rd.fieldnames or [])
    if "file" not in fields or "line" not in fields:
        print("CITATIONS.csv needs `file` and `line` columns", file=sys.stderr)
        return 2
    add = ["lean_name", "decl_kind", "decl_file", "decl_line", "in_cone",
           "in_import_closure", "consumers", "consumers_in_cone", "dead", "why"]
    fields += [a for a in add if a not in fields]
    why_n = collections.Counter()
    for c in cites:
        for a in add:
            c[a] = ""
        files = idx.resolve(c["file"])
        m = re.match(r"\s*(\d+)", c.get("line") or "")
        r = None
        if len(files) == 1 and m:
            f = next(iter(files))
            i = bisect.bisect_right(starts[f], int(m.group(1))) - 1
            if i >= 0:
                r = byfile[f][i]
        if r is None:
            c["why"] = "unknown"
            if len(files) > 1:
                c["decl_file"] = "AMBIGUOUS: " + "; ".join(sorted(files)[:3])
            why_n["unknown"] += 1
            continue
        dead = dead_of.get((r["file"], r["name"]), "")
        c.update(lean_name=r["name"], decl_kind=r["kind"], decl_file=r["file"],
                 decl_line=r["line"], in_cone=r["in_cone"],
                 in_import_closure=r["in_import_closure"], consumers=r["consumers"],
                 consumers_in_cone=r["consumers_in_cone"], dead=dead)
        if truthy(r["in_cone"]):
            w = "route"
        elif dead:
            w = "dead"
        elif truthy(r["orphan_file"]):
            w = "orphan"
        elif truthy(r["above_seed"]):
            w = "above_seed"
        else:
            w = "wrapper"
        c["why"] = w
        why_n[w] += 1
    with open(args.out, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=fields)
        w.writeheader()
        w.writerows(cites)
    print(f"{len(cites):,} citations: " +
          ", ".join(f"{k} {v:,}" for k, v in why_n.most_common()))
    print(f"wrote {args.out}")
    return 0


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    if argv and argv[0] == "join":
        return cmd_join(argv[1:])
    if argv and argv[0] == "route":
        return cmd_route(argv[1:])
    return cmd_cone(argv)


if __name__ == "__main__":
    raise SystemExit(main())
