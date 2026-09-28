"""The STATEMENT rung for a BARE claim: a dossier of what the headline says.

PLAYBOOK §1.1: when there is no independently authored challenge and no
Comparator run, "is this the theorem that was claimed?" is the whole first
job, and no checker can answer it. What a tool CAN do is put everything the
answer depends on in one place, so the reader compares words with words
instead of words with memory:

* the theorem's source text, its binders one per line (hypotheses and
  instance arguments), its conclusion, and the `variable`s, `open`s,
  `universe`s and `set_option`s in scope — including the project-wide
  `leanOptions` in the lakefile, which change elaboration without appearing
  in the file;
* every constant and notation the signature mentions, resolved by SOURCE
  to the declaration it names (project, then `.lake/packages/*`, or a
  Mathlib checkout given with `--mathlib`, then the toolchain's `Init`),
  with its docstring, its own binders, `extends`, and fields — ONE level
  down, deliberately: the reader decides where to dig;
* for each class in the signature, the instances that derive another class
  from it and need nothing else (`SimplyConnectedSpace ⟹ PathConnectedSpace`),
  followed a bounded number of steps — a source grep, labelled as such,
  which is exactly the kind of fact a reader otherwise asserts from memory;
* optionally (the Lean rung), `#check @name`, `#print name`,
  `#print axioms name` and `#print` of each resolved constant, when a
  toolchain and the project's build are present. When it does not run the
  dossier says so and why, at the top of the section.

Then `--reference REF.md`: a file the auditor writes BEFORE reading the Lean,
stating the claim in words, one clause per list item. The tool pairs each
reference clause with the Lean clause it matched (word overlap after
camel-case splitting, a small synonym table and notation expansion) and
lists what matched nothing ON EITHER SIDE. A matched pair is a pointer for a
human, not a judgement; an unmatched clause is the finding.

Source resolution is text, not elaboration: it can pick the wrong
overload of a name, miss a declaration produced by a macro, and it does not
know which `open` Lean actually used. Every resolution names the file and
line it came from so it can be checked with `sed -n`, and ambiguity is
printed rather than resolved.

    python3 audits/statement.py PROJECT MODULE THEOREM \\
        [--mathlib DIR] [--toolchain-src DIR] [--reference REF.md] \\
        [--no-lean] [-o OUT.md]
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                ".."))

from safeverifyagent.extract import blank_comments   # noqa: E402

SKIP_DIRS = {".git", ".lake", "build", ".venv", "_tmp",
             # a dependency's tests and examples are not what its users import
             "MathlibTest", "test", "tests", "Archive", "Counterexamples",
             "docs", "scripts", "examples"}


DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "class inductive", "class",
              "structure", "inductive", "instance", "opaque", "axiom",
              "irreducible_def", "example")
# Declarations a signature can mention by name and that the index holds;
# theorems are looked up only in the claim's own file.
INDEX_KINDS = tuple(k for k in DECL_KINDS
                    if k not in ("theorem", "lemma", "instance", "example"))
MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe",
             "nonrec", "public", "scoped", "local", "meta")
DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:" + "|".join(MODIFIERS) + r")[ \t]+)*"
    r"(?P<kind>" + "|".join(k.replace(" ", r"[ \t]+") for k in DECL_KINDS)
    + r")\b[ \t]*(?P<name>[^\s:({\[⦃]+)?")
NAMESPACE_RE = re.compile(r"^[ \t]*namespace[ \t]+(\S+)")
SECTION_RE = re.compile(r"^[ \t]*(?:noncomputable[ \t]+)?section\b[ \t]*(\S*)")
END_RE = re.compile(r"^[ \t]*end\b[ \t]*(\S*)[ \t]*$")
OPEN_RE = re.compile(r"^[ \t]*open\b(?P<rest>[^\n]*)$")
VARIABLE_START_RE = re.compile(r"^[ \t]*variable\b")
UNIVERSE_RE = re.compile(r"^[ \t]*universe\b(?P<rest>[^\n]*)$")
SET_OPTION_RE = re.compile(r"^[ \t]*set_option[ \t]+(\S+)[ \t]+(\S+)"
                           r"(?P<in>[ \t]+in\b)?")
NOTATION_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:scoped|local)[ \t]+)*"
    r"(?:notation3?|infixl|infixr|infix|prefix|postfix)\b[^\n]*?"
    r"\"(?P<tok>[^\"]+)\"[^\n]*?=>[ \t]*(?P<target>[^\n]+)$")

OPEN_BR = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSE_BR = set(OPEN_BR.values())

LEAN_KEYWORDS = {
    "fun", "λ", "forall", "∀", "∃", "exists", "let", "have", "show", "from",
    "by", "if", "then", "else", "match", "with", "do", "at", "in", "Type",
    "Sort", "Prop", "Type*", "Sort*", "∑", "∏", "⋃", "⋂"}
# Notation so common that resolving it every time is noise.
SKIP_SYMBOLS = {"→", "↔", "∧", "∨", "¬", "=", "≠", "≤", "<", "≥", ">", ":",
                ":=", ",", ".", "×", "∈", "∉", "⊆", "+", "*", "-", "/", "^",
                "↦", "=>", "|", "∘", "•", "@", "_", "..", "·", "$", "<|",
                "|>"}

IDENT_START = re.compile(r"[^\W\d]|_", re.UNICODE)


# ---------------------------------------------------------------------------
# Lean source structure
# ---------------------------------------------------------------------------

@dataclass
class Scope:
    """What is in force at one line of a file."""
    namespace: str = ""
    opens: List[str] = field(default_factory=list)
    variables: List[Tuple[int, str]] = field(default_factory=list)
    set_options: List[Tuple[int, str]] = field(default_factory=list)
    universes: List[Tuple[int, str]] = field(default_factory=list)


def _frames_at(blank_lines: Sequence[str], upto: int) -> Scope:
    """Walk `namespace`/`section`/`end` to line `upto` (0-based, exclusive)
    and report what is in scope there. `open … in` and `set_option … in`
    scope over one command and are handled by the caller."""
    # frame: [kind, name, opens, variables, set_options, universes]
    stack: List[list] = [["root", "", [], [], [], []]]
    i = 0
    while i < upto:
        line = blank_lines[i]
        m = NAMESPACE_RE.match(line)
        if m:
            stack.append(["namespace", m.group(1), [], [], [], []])
            i += 1
            continue
        m = SECTION_RE.match(line)
        if m and not line.lstrip().startswith("end"):
            stack.append(["section", m.group(1), [], [], [], []])
            i += 1
            continue
        m = END_RE.match(line)
        if m and len(stack) > 1:
            stack.pop()
            i += 1
            continue
        m = OPEN_RE.match(line)
        if m and not re.search(r"\bin\s*$", m.group("rest")):
            names = [t for t in m.group("rest").split()
                     if t not in ("scoped", "hiding", "renaming")
                     and not t.startswith("(")]
            stack[-1][2].extend(names)
        if VARIABLE_START_RE.match(line):
            text = [line.strip()]
            j = i + 1
            while j < upto and blank_lines[j].startswith((" ", "\t")) \
                    and blank_lines[j].strip():
                text.append(blank_lines[j].strip())
                j += 1
            joined = " ".join(text)
            if not re.search(r"\bin\s*$", joined):
                stack[-1][3].append((i + 1, joined))
            i = j
            continue
        m = SET_OPTION_RE.match(line)
        if m and not m.group("in"):
            stack[-1][4].append((i + 1, line.strip()))
        m = UNIVERSE_RE.match(line)
        if m:
            stack[-1][5].append((i + 1, line.strip()))
        i += 1
    sc = Scope()
    sc.namespace = ".".join(f[1] for f in stack if f[0] == "namespace")
    for f in stack:
        sc.opens += f[2]
        sc.variables += f[3]
        sc.set_options += f[4]
        sc.universes += f[5]
    return sc


def _decl_end(blank_lines: Sequence[str], start: int) -> int:
    """0-based exclusive end of the declaration whose header is `start`:
    the next non-blank line at column 0 that is not a continuation."""
    for j in range(start + 1, len(blank_lines)):
        ln = blank_lines[j]
        if not ln.strip() or ln[0] in " \t":
            continue
        if re.match(r"(\||where\b|termination_by|decreasing_by|deriving\b|"
                    r"\)|\]|\})", ln):
            continue
        return j
    return len(blank_lines)


def _docstring_above(raw_lines: Sequence[str], start: int) -> Tuple[str, int]:
    """The `/-- … -/` above a header, skipping attribute lines and a
    `variable … in` line. Returns (docstring, first line index used)."""
    j = start - 1
    while j >= 0 and (raw_lines[j].strip().startswith("@[")
                      or re.match(r"\s*(variable|open|set_option)\b.*\bin\s*$",
                                  raw_lines[j])):
        j -= 1
    first = j + 1
    if j < 0 or not raw_lines[j].rstrip().endswith("-/"):
        return "", first
    k = j
    while k >= 0 and "/--" not in raw_lines[k]:
        if "/-" in raw_lines[k] and "/--" not in raw_lines[k]:
            return "", first
        k -= 1
    if k < 0:
        return "", first
    doc = "\n".join(raw_lines[k:j + 1]).strip()
    doc = re.sub(r"^/--\s*", "", doc)
    doc = re.sub(r"\s*-/$", "", doc)
    return doc.strip(), k


def _prefix_lines(raw_lines: Sequence[str], start: int) -> List[str]:
    """`variable … in` / `open … in` / `set_option … in` lines directly
    above a header (through attributes): they change what the header
    means and are printed with it."""
    out = []
    _, first = _docstring_above(raw_lines, start)
    j = start - 1
    while j >= 0:
        ln = raw_lines[j]
        if first <= j < start and not re.match(
                r"\s*(variable|open|set_option)\b.*\bin\s*$", ln):
            j -= 1                         # docstring / attribute lines
            continue
        if ln.strip().startswith("@["):
            j -= 1
            continue
        if re.match(r"\s*(variable|open|set_option)\b.*\bin\s*$", ln):
            out.append(ln.strip())
            j -= 1
            continue
        break
    return list(reversed(out))


def split_signature(text: str) -> Tuple[str, str]:
    """(signature, rest) at the first top-level `:=`, ` where`, or `|`
    (after the header line) — bracket depth tracked."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth = max(0, depth - 1)
        elif depth == 0:
            if text.startswith(":=", i):
                return text[:i].rstrip(), text[i:]
            if re.match(r"\swhere\b", text[i:i + 7]):
                return text[:i].rstrip(), text[i:]
            if c == "|" and text[:i].rfind("\n") >= 0 and \
                    text[text[:i].rfind("\n") + 1:i].strip() == "":
                return text[:i].rstrip(), text[i:]
        i += 1
    return text.rstrip(), ""


@dataclass
class Binder:
    kind: str          # explicit | implicit | instance | strict
    names: List[str]
    type: str
    text: str

    @property
    def label(self) -> str:
        return {"explicit": "()", "implicit": "{}", "instance": "[]",
                "strict": "⦃⦄"}[self.kind]


def parse_binders(sig_after_name: str) -> Tuple[List[Binder], str]:
    """Binders up to the top-level `:`; the remainder is the type. With no
    top-level `:` (a structure with `extends`), the remainder after the
    binders is returned instead, starting with the non-binder token."""
    s = sig_after_name
    binders: List[Binder] = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
            continue
        if c in "([{⦃":
            depth = 0
            j = i
            while j < n:
                if s[j] in OPEN_BR:
                    depth += 1
                elif s[j] in CLOSE_BR:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = s[i + 1:j].strip()
            text = s[i:j + 1]
            kind = {"(": "explicit", "{": "implicit", "[": "instance",
                    "⦃": "strict"}[c]
            if kind == "implicit" and inner.startswith("{"):
                kind, inner = "strict", inner.strip("{}").strip()
            names, typ = [], inner
            colon = _top_level_colon(inner)
            if colon is not None:
                head, typ = inner[:colon].strip(), inner[colon + 1:].strip()
                names = head.split()
            elif kind != "instance":
                names, typ = inner.split(), ""
            if ":=" in typ and kind == "explicit":
                typ = typ.split(":=")[0].strip()
            binders.append(Binder(kind, names, typ, " ".join(text.split())))
            i = j + 1
            continue
        if c == ":":
            return binders, s[i + 1:].strip()
        if s.startswith("extends", i):
            return binders, s[i:].strip()
        # a bare identifier binder (`variable (X) in`-style): skip a token
        m = re.match(r"\S+", s[i:])
        i += m.end() if m else 1
    return binders, ""


def _top_level_colon(s: str) -> Optional[int]:
    depth = 0
    for i, c in enumerate(s):
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth -= 1
        elif c == ":" and depth == 0 and not s.startswith(":=", i):
            return i
    return None


def tokens(text: str) -> List[str]:
    """Identifiers and symbolic tokens of a Lean expression."""
    out = []
    for raw in re.split(r"[\s()\[\]{}⦃⦄⟨⟩,]+", text):
        if not raw:
            continue
        if raw in LEAN_KEYWORDS or raw.rstrip("*") in LEAN_KEYWORDS:
            continue
        if IDENT_START.match(raw):
            # `Foo.bar.{u}` → `Foo.bar`; `x.1` stays whole
            out.append(re.sub(r"\.\{.*$", "", raw).rstrip(".:"))
        elif raw in SKIP_SYMBOLS or re.fullmatch(r"[\d.]+", raw):
            continue
        else:
            # a symbol glued to something (`∞`, `≃ₜ`, `𝓡`): keep as-is
            out.append(raw)
    return out


def is_ident(tok: str) -> bool:
    return bool(IDENT_START.match(tok)) and tok not in LEAN_KEYWORDS


# ---------------------------------------------------------------------------
# The source index
# ---------------------------------------------------------------------------

@dataclass
class DeclHit:
    root_label: str
    path: str
    line: int                      # 1-based header line
    kind: str
    full_name: str
    header: str                    # signature text (raw, comment-free)
    doc: str
    text: str                      # the declaration, raw, capped
    prefix: List[str]
    binders: List[Binder]
    type: str
    extends: List[str]
    fields: List[Tuple[str, str]]
    body: str                      # after `:=`, for def/abbrev
    scope: Scope

    @property
    def cite(self) -> str:
        return f"{self.root_label}:{self.path}:{self.line}"


class SourceIndex:
    """Declaration lookup over a list of source roots.

    Three greps per root, once: declaration headers of the kinds a
    signature can name (`INDEX_KINDS`), `instance` headers, and
    notation/infix declarations. Everything after that is dictionary
    lookups plus reading the files a hit lands in — namespaces are
    computed per file, by walking `namespace`/`section`/`end`.
    """

    def __init__(self, roots: Sequence[Tuple[str, str]]):
        self.roots = [(lbl, os.path.abspath(d)) for lbl, d in roots
                      if d and os.path.isdir(d)]
        self._files: Dict[str, Tuple[List[str], List[str]]] = {}
        self._decl_cache: Dict[str, List[DeclHit]] = {}
        self._heads: Optional[Dict[str, List[Tuple[str, str, int]]]] = None
        self._insts: Optional[List[Tuple[str, str, int, str]]] = None
        self._notes: Optional[List[Tuple[str, str, int, str]]] = None
        self._scopes: Dict[Tuple[str, int], Scope] = {}

    def file(self, path: str) -> Tuple[List[str], List[str]]:
        if path not in self._files:
            with open(path, encoding="utf-8", errors="replace") as f:
                raw = f.read()
            self._files[path] = (raw.split("\n"),
                                 blank_comments(raw).split("\n"))
        return self._files[path]

    def scope_at(self, path: str, i: int) -> Scope:
        key = (path, i)
        if key not in self._scopes:
            self._scopes[key] = _frames_at(self.file(path)[1], i)
        return self._scopes[key]

    def _grep(self, pattern: str) -> List[Tuple[str, str, int, str]]:
        """(root label, abs path, 1-based line, line text), PCRE."""
        hits = []
        for lbl, d in self.roots:
            p = subprocess.run(
                ["grep", "-rnP", "--include=*.lean",
                 *[f"--exclude-dir={x}" for x in sorted(SKIP_DIRS)],
                 pattern, d], capture_output=True, text=True)
            for ln in p.stdout.splitlines():
                m = re.match(r"^(.*?\.lean):(\d+):(.*)$", ln)
                if m:
                    hits.append((lbl, m.group(1), int(m.group(2)),
                                 m.group(3)))
        return hits

    def _build(self) -> None:
        mods = "|".join(MODIFIERS)
        kinds = "|".join(k.replace(" ", r"\s+") for k in INDEX_KINDS)
        pre = r"^\s*(@\[[^\]]*\]\s*)*((" + mods + r")\s+)*"
        self._heads = {}
        for lbl, path, line, text in self._grep(pre + r"(" + kinds + r")\s"):
            m = DECL_RE.match(text)
            if m and m.group("name"):
                last = re.sub(r"\.\{.*$", "", m.group("name")).split(".")[-1]
                self._heads.setdefault(last, []).append((lbl, path, line))
        self._insts = self._grep(pre + r"instance\b")
        self._notes = self._grep(
            pre + r"(notation3?|infixl|infixr|infix|prefix|postfix)\b.*\"")

    def rel(self, lbl: str, path: str) -> str:
        for l2, d in self.roots:
            if l2 == lbl:
                return os.path.relpath(path, d)
        return path

    def abspath(self, lbl: str, rel: str) -> str:
        return os.path.join(dict(self.roots)[lbl], rel)

    def decl_at(self, lbl: str, path: str, line: int) -> Optional[DeclHit]:
        raw, blank = self.file(path)
        i = line - 1
        m = DECL_RE.match(blank[i]) if i < len(blank) else None
        if not m:
            return None
        kind = re.sub(r"\s+", " ", m.group("kind"))
        name = re.sub(r"\.\{.*$", "", (m.group("name") or "").strip())
        sc = self.scope_at(path, i)
        full = name[len("_root_."):] if name.startswith("_root_.") else (
            f"{sc.namespace}.{name}" if sc.namespace and name else name)
        end = _decl_end(blank, i)
        text_blank = "\n".join(blank[i:end]).rstrip()
        after = text_blank[m.end():]
        sig, rest = split_signature(after)
        binders, typ = parse_binders(sig)
        extends: List[str] = []
        if kind in ("class", "structure"):
            me = re.search(r"\bextends\b(.*)$", typ, re.S)
            if me:
                extends = [" ".join(e.split())
                           for e in _split_top(me.group(1), ",")
                           if e.strip()]
                typ = typ[:me.start()].strip()
        fields: List[Tuple[str, str]] = []
        body = ""
        if kind in ("class", "structure") and rest.lstrip().startswith(
                "where"):
            fields = _fields(rest.lstrip()[len("where"):])
        elif rest.startswith(":="):
            body = rest[2:].strip()
        doc, first = _docstring_above(raw, i)
        cap = min(end, i + 60)
        text = "\n".join(raw[first:cap]).rstrip()
        if cap < end:
            text += f"\n  … ({end - cap} more lines)"
        return DeclHit(lbl, self.rel(lbl, path), line, kind, full,
                       " ".join((m.group(0) + sig).split()), doc, text,
                       _prefix_lines(raw, i), binders, typ, extends, fields,
                       body, sc)

    def find_decl(self, full_name: str) -> List[DeclHit]:
        if full_name in self._decl_cache:
            return self._decl_cache[full_name]
        if self._heads is None:
            self._build()
        out = []
        for lbl, path, line in self._heads.get(full_name.split(".")[-1], []):
            h = self.decl_at(lbl, path, line)
            if h and h.full_name == full_name:
                out.append(h)
        self._decl_cache[full_name] = out
        return out

    def find_notation(self, tok: str) -> List[Tuple[str, str, int, str, str]]:
        """(label, rel path, line, declaration line, target) for a
        notation/infix whose quoted token is `tok`."""
        if self._notes is None:
            self._build()
        out = []
        for lbl, path, line, text in self._notes:
            if tok.strip() not in text:
                continue
            m = NOTATION_RE.match(self.file(path)[1][line - 1])
            if m and m.group("tok").strip() == tok.strip():
                out.append((lbl, self.rel(lbl, path), line, text.strip(),
                            m.group("target").strip()))
        return out

    def derived_instances(self, cls: DeclHit) -> List[Tuple[str, str, str]]:
        """FORGETFUL instances out of `cls`: `[cls X] ⊢ D X` on the SAME
        carrier, needing no instance beyond cls's own parameter classes
        (e.g. `TopologicalSpace`) — counting the `variable`s in scope,
        which Lean adds to an instance's binders. (derived class,
        citation, header line). Heuristic, by source."""
        if self._insts is None:
            self._build()
        short = cls.full_name.split(".")[-1]
        own_heads = {_head(b.type) for b in cls.binders
                     if b.kind == "instance"}
        rx = re.compile(r"\[\s*(?:\w+\s*:\s*)?(?:" + re.escape(cls.full_name)
                        + "|" + re.escape(short) + r")\s")
        out, seen = [], set()
        cls_file = self.abspath(cls.root_label, cls.path)
        for lbl, path, line, text in self._insts:
            direct = bool(rx.search(text))
            if not direct:
                # `instance : D X` inside `namespace cls` with
                # `variable [cls X]` — only in files that could hold it
                if path != cls_file and short not in text and \
                        f"namespace {short}" not in "\n".join(
                            self.file(path)[1][:line]):
                    continue
            edge = self._instance_edge(lbl, path, line, cls, short,
                                       own_heads)
            if edge and (edge[0], path, line) not in seen:
                seen.add((edge[0], path, line))
                out.append(edge)
        return out

    def _instance_edge(self, lbl, path, line, cls, short, own_heads):
        raw, blank = self.file(path)
        if re.match(r"\s*(private\s+)?(local|scoped)\b|\s*private\s+local",
                    blank[line - 1]):
            return None                  # not visible to the claim
        end = _decl_end(blank, line - 1)
        text = " ".join(" ".join(blank[line - 1:end]).split())
        k = text.find("instance")
        if k < 0:
            return None
        after = text[k + len("instance"):]
        after = re.sub(r"^\s*\(priority\s*:=\s*[^)]*\)", "", after)
        if not after.lstrip().startswith((":", "(", "[", "{", "⦃")):
            after = re.sub(r"^\s*[^\s:(\[{⦃]+", "", after, count=1)
        sig, _ = split_signature(after)
        binders, concl = parse_binders(sig)
        sc = self.scope_at(path, line - 1)
        var_binders: List[Binder] = []
        for _, v in sc.variables:
            bs, _ = parse_binders(v[len("variable"):])
            var_binders += bs
        cm = re.match(r"^([\w.']+)\s+([\w'.]+)\s*$", concl.strip())
        if not cm:
            return None
        derived, carrier = cm.group(1), cm.group(2)
        if derived.split(".")[-1] == short:
            return None
        inst = [b for b in binders + var_binders if b.kind == "instance"]
        mine = [b for b in inst if _head(b.type) in (short, cls.full_name)
                and _args(b.type) == [carrier]]
        if not mine:
            return None
        # the carrier must be a TYPE variable: `[Nonempty s] : Foo s` with
        # `{s : AffineSubspace R P}` is about a coercion, not the carrier
        ctype = [b.type for b in binders + var_binders
                 if carrier in b.names and b.type]
        if ctype and not re.match(r"(Type|Sort)\b", ctype[-1]):
            return None
        # every other instance binder must be on the carrier and be one
        # cls itself takes; any other assumption makes this not forgetful
        for b in inst:
            if b in mine:
                continue
            if carrier not in _args(b.type) and b in binders:
                return None
            if carrier in _args(b.type) and _head(b.type) not in own_heads:
                return None
        # explicit value binders mean the conclusion is about something else
        if any(b.kind == "explicit" and b.names and b.type and
               not re.match(r"(Type|Sort)\b", b.type) for b in binders):
            return None
        return (derived, f"{lbl}:{self.rel(lbl, path)}:{line}",
                raw[line - 1].strip() + (" …" if end - (line - 1) > 1
                                         else ""))


def _head(t: str) -> str:
    t = t.strip()
    c = _top_level_colon(t)
    if c is not None:
        t = t[c + 1:].strip()
    return t.split()[0] if t.split() else ""


def _args(t: str) -> List[str]:
    t = t.strip()
    c = _top_level_colon(t)
    if c is not None:
        t = t[c + 1:].strip()
    return t.split()[1:]


def _split_top(s: str, sep: str) -> List[str]:
    out, depth, cur = [], 0, []
    for c in s:
        if c in OPEN_BR:
            depth += 1
        elif c in CLOSE_BR:
            depth -= 1
        if c == sep and depth == 0:
            out.append("".join(cur))
            cur = []
        else:
            cur.append(c)
    out.append("".join(cur))
    return out


def _fields(body: str) -> List[Tuple[str, str]]:
    """Fields of a structure/class body (comment-blanked): `name : type`
    at the body's base indentation, continuation lines joined."""
    lines = [ln for ln in body.split("\n")]
    base = None
    out: List[Tuple[str, str]] = []
    for ln in lines:
        if not ln.strip():
            continue
        if re.match(r"\s*\S+\s*::\s*$", ln):
            continue                      # `where mk ::`: the constructor
        ind = len(ln) - len(ln.lstrip())
        if base is None:
            base = ind
        if ind == base:
            m = re.match(r"\s*(?:(?:protected|private)\s+)?"
                         r"(\(?[^\s:()]+(?:\s+[^\s:()]+)*\)?)\s*:\s*(.*)$", ln)
            if re.match(r"\s*\S+\s*::", ln):
                continue                          # the constructor's name
            if m and not ln.strip().startswith(("|", "--")):
                out.append((m.group(1).strip("()"), m.group(2).strip()))
            elif out:
                out[-1] = (out[-1][0], out[-1][1] + " " + ln.strip())
        elif out and ind > base:
            out[-1] = (out[-1][0], out[-1][1] + " " + ln.strip())
    return [(n, " ".join(t.split())) for n, t in out]


# ---------------------------------------------------------------------------
# The dossier
# ---------------------------------------------------------------------------

@dataclass
class Resolution:
    token: str
    candidates: List[str]
    hits: List[DeclHit]
    notation: List[Tuple[str, str, int, str, str]] = field(
        default_factory=list)


@dataclass
class Statement:
    module: str
    theorem: str
    decl: DeclHit
    project_options: List[str]
    resolutions: List[Resolution]
    derived: Dict[str, List[Tuple[str, str, str, int]]]
    lean: Dict[str, str]
    lean_note: str
    roots: List[Tuple[str, str]]
    unsearched: List[str]


def module_path(project: str, module: str) -> Optional[str]:
    rel = module.replace(".", os.sep) + ".lean"
    for base in (project, os.path.join(project, "src")):
        p = os.path.join(base, rel)
        if os.path.exists(p):
            return p
    return None


def project_lean_options(project: str) -> List[str]:
    """`leanOptions` from `lakefile.toml` (or `lakefile.lean`): options
    in force in EVERY file of the project, and invisible in any of them."""
    out = []
    t = os.path.join(project, "lakefile.toml")
    if os.path.exists(t):
        sec = None
        with open(t, encoding="utf-8") as f:
            for ln in f:
                s = ln.strip()
                if s.startswith("["):
                    sec = s
                    continue
                if sec == "[leanOptions]" and "=" in s and \
                        not s.startswith("#"):
                    out.append(f"lakefile.toml [leanOptions]: {s}")
                elif sec and sec.startswith("[[lean_lib]]") and \
                        s.startswith("leanOptions"):
                    out.append(f"lakefile.toml [[lean_lib]]: {s}")
    ll = os.path.join(project, "lakefile.lean")
    if os.path.exists(ll):
        with open(ll, encoding="utf-8") as f:
            txt = f.read()
        for m in re.finditer(r"⟨`([\w.]+),\s*([^⟩]+)⟩", txt):
            out.append(f"lakefile.lean leanOptions: {m.group(1)} = "
                       f"{m.group(2).strip()}")
    return out


def toolchain_src(project: str) -> Optional[str]:
    tc = os.path.join(project, "lean-toolchain")
    if not os.path.exists(tc):
        return None
    with open(tc) as f:
        name = f.read().strip()
    san = name.replace("/", "--").replace(":", "---")
    d = os.path.expanduser(f"~/.elan/toolchains/{san}/src/lean")
    return d if os.path.isdir(d) else None


def candidates_for(tok: str, sc: Scope) -> List[str]:
    """Names `tok` could mean at a point with scope `sc`, in the order
    Lean tries namespaces (innermost first), then `open`s, then root."""
    out = []
    parts = sc.namespace.split(".") if sc.namespace else []
    for k in range(len(parts), 0, -1):
        out.append(".".join(parts[:k]) + "." + tok)
    for o in sc.opens:
        out.append(f"{o}.{tok}")
    out.append(tok)
    seen, uniq = set(), []
    for c in out:
        if c not in seen:
            seen.add(c)
            uniq.append(c)
    return uniq


def build(project: str, module: str, theorem: str,
          mathlib: Optional[str] = None, tc_src: Optional[str] = None,
          run_lean: bool = True, derive_depth: int = 2,
          lean_timeout: int = 1200) -> Statement:
    project = os.path.abspath(project)
    src = module_path(project, module)
    if src is None:
        raise SystemExit(f"module {module} not found under {project}")
    roots: List[Tuple[str, str]] = [("project", project)]
    pk = os.path.join(project, ".lake", "packages")
    unsearched = []
    if mathlib:
        roots.append(("mathlib", mathlib))
    if os.path.isdir(pk):
        for d in sorted(os.listdir(pk)):
            if mathlib and d == "mathlib":
                continue
            roots.append((d, os.path.join(pk, d)))
    elif not mathlib:
        unsearched.append("no `.lake/packages` and no `--mathlib`: "
                          "dependencies were NOT searched")
    tc_src = tc_src or toolchain_src(project)
    if tc_src:
        roots.append(("lean", tc_src))
    else:
        unsearched.append("toolchain source (Init/Std) not found for this "
                          "project's `lean-toolchain`: core names were NOT "
                          "searched (pass --toolchain-src)")
    idx = SourceIndex(roots)

    # the theorem itself — in THIS file, by namespace-qualified name
    raw, blank = idx.file(src)
    decl = None
    short = theorem.split(".")[-1]
    for k, ln in enumerate(blank):
        m = DECL_RE.match(ln)
        if m and (m.group("name") or "").split(".")[-1] == short:
            h = idx.decl_at("project", src, k + 1)
            if h and h.full_name == theorem:
                decl = h
                break
    if decl is None:
        raise SystemExit(f"{theorem} not declared in {src}")

    sc = decl.scope
    for p in decl.prefix:
        m = re.match(r"open\s+(.*)\s+in$", p)
        if m:
            sc.opens += m.group(1).split()
    bound = {n for b in decl.binders for n in b.names}
    for _, v in sc.variables:
        bs, _ = parse_binders(v[len("variable"):])
        bound |= {n for b in bs for n in b.names}
    universes = set()
    for _, u in sc.universes:
        universes |= set(u.split()[1:])
    toks: List[str] = []
    for b in decl.binders:
        toks += tokens(b.type)
    toks += tokens(decl.type)
    seen = set()
    resolutions = []
    for t in toks:
        if t in seen or t in bound or t in universes:
            continue
        seen.add(t)
        cands = candidates_for(t, sc) if is_ident(t) else []
        hits: List[DeclHit] = []
        for c in cands:
            hits += idx.find_decl(c)
        if not hits and cands and t.split(".")[0] in bound:
            continue          # a projection on a bound name: `x.1`
        res = Resolution(t, cands, hits)
        if not hits:
            # notation: `ℝ`, `≃ₜ`. Resolve the target's head constant.
            res.notation = idx.find_notation(t)
            for n in res.notation:
                tgt = tokens(n[4])
                if tgt and is_ident(tgt[0]):
                    # the target is resolved where the NOTATION is declared
                    nsc = idx.scope_at(idx.abspath(n[0], n[1]), n[2] - 1)
                    for c in candidates_for(tgt[0], nsc):
                        res.hits += idx.find_decl(c)
                    if res.hits:
                        break
        resolutions.append(res)

    derived: Dict[str, List[Tuple[str, str, str, int]]] = {}
    hyp_heads = {_head(b.type) for b in decl.binders if b.kind == "instance"}
    for r in resolutions:
        for h in r.hits[:1]:
            # only classes ASSUMED by the claim: what they give for free is
            # what a reader must not ask the statement to say twice
            if h.kind not in ("class", "class inductive") or \
                    r.token not in hyp_heads:
                continue
            frontier, depth = [h], 1
            chain: List[Tuple[str, str, str, int]] = []
            done = {h.full_name}
            while frontier and depth <= derive_depth:
                nxt = []
                for c in frontier:
                    # a class's `extends` parents are instances too (the
                    # parent projections), with no `instance` line to grep
                    parents = [(_head(e), c.cite, f"extends {e}")
                               for e in c.extends if _head(e)]
                    for d, cite, hdr in parents + idx.derived_instances(c):
                        chain.append((f"{c.full_name} ⟹ {d}", cite, hdr,
                                      depth))
                        for cand in candidates_for(d, c.scope):
                            ds = [x for x in idx.find_decl(cand)
                                  if x.kind.startswith("class")]
                            if ds and ds[0].full_name not in done:
                                done.add(ds[0].full_name)
                                nxt.append(ds[0])
                                break
                frontier, depth = nxt, depth + 1
            if chain:
                derived[h.full_name] = chain

    lean, note = {}, ""
    if run_lean:
        lean, note = lean_rung(project, module, theorem,
                               [r.hits[0].full_name for r in resolutions
                                if r.hits], lean_timeout)
    else:
        note = "not run: --no-lean"
    return Statement(module, theorem, decl, project_lean_options(project),
                     resolutions, derived, lean, note, idx.roots, unsearched)


def _lake() -> Optional[str]:
    for c in (shutil.which("lake"), os.path.expanduser("~/.elan/bin/lake")):
        if c and os.path.exists(c):
            return c
    return None


def lean_rung(project: str, module: str, theorem: str,
              consts: Sequence[str], timeout: int) -> Tuple[Dict[str, str],
                                                            str]:
    """`#check`/`#print`/`#print axioms` through the project's own build.
    Runs only if the module's `.olean` exists: building a Mathlib project
    is not this tool's decision to make."""
    lake = _lake()
    if lake is None:
        return {}, "not run: no `lake` (install elan)"
    olean = os.path.join(project, ".lake", "build", "lib", "lean",
                         module.replace(".", os.sep) + ".olean")
    if not os.path.exists(olean):
        return {}, (f"not run: the project is not built (no "
                    f"`{os.path.relpath(olean, project)}`); run `lake build "
                    f"{module}` (and `lake exe cache get` for Mathlib) first")
    cmds = [("check", f"#check @{theorem}"), ("print", f"#print {theorem}"),
            ("axioms", f"#print axioms {theorem}")]
    for c in dict.fromkeys(consts):
        cmds.append((f"print {c}", f"#print {c}"))
    marks = []
    body = [f"import {module}"]
    for key, cmd in cmds:
        mark = f"SVA_MARK_{len(marks)}"
        marks.append((key, mark))
        body += [f'#eval IO.println "{mark}"', cmd]
    # outside the project: the audited repo is read-only to the auditor
    fd, path = tempfile.mkstemp(prefix="sva_statement_", suffix=".lean")
    with os.fdopen(fd, "w") as f:
        f.write("\n".join(body) + "\n")
    try:
        p = subprocess.run([lake, "env", "lean", path], cwd=project,
                           capture_output=True, text=True, timeout=timeout)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return {}, f"not completed: exceeded {timeout}s"
    finally:
        os.unlink(path)
    # Messages are reported per command, in order; split on the marks.
    res: Dict[str, str] = {}
    pos = [(out.find(m), k) for k, m in marks]
    if any(p0 < 0 for p0, _ in pos):
        return {"raw": out[-4000:]}, (f"ran (exit {p.returncode}) but the "
                                      "output could not be split; raw tail")
    pos.append((len(out), None))
    for (a, k), (b, _) in zip(pos, pos[1:]):
        chunk = out[a:b].split("\n", 1)
        res[k] = chunk[1].strip() if len(chunk) > 1 else ""
    return res, f"ran: `lake env lean` in the project (exit {p.returncode})"


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

def _rev(path: str) -> str:
    """` @ <commit>` when the root is a git checkout: a dossier names the
    exact source it read."""
    try:
        p = subprocess.run(["git", "-C", path, "rev-parse", "--short=12",
                            "HEAD"], capture_output=True, text=True,
                           timeout=10)
    except (OSError, subprocess.SubprocessError):
        return ""
    return f" @ {p.stdout.strip()}" if p.returncode == 0 else ""


def _q(s: str) -> str:
    return "`" + s.replace("`", "ˋ") + "`"


def render(st: Statement) -> List[str]:
    d = st.decl
    L = [f"# Statement dossier: `{st.theorem}`", "",
         f"- module: `{st.module}` — `{d.path}:{d.line}`",
         f"- kind: `{d.kind}`",
         "- source roots searched: " + ", ".join(
             f"{lbl} (`{p}`{_rev(p)})" for lbl, p in st.roots)]
    for u in st.unsearched:
        L.append(f"- **not searched:** {u}")
    L.append(f"- Lean rung: {st.lean_note}")
    L += ["", "Resolution below is by SOURCE TEXT (grep plus namespace "
          "tracking), not elaboration: every resolved name carries a "
          "`root:path:line` to check with `sed -n`, and more than one hit "
          "is printed as ambiguity rather than resolved.", "",
          "## 1. Source text", "", "```lean"]
    L += d.prefix + [d.text, "```", ""]
    if d.doc:
        L += ["Docstring:", "", "> " + d.doc.replace("\n", "\n> "), ""]

    L += ["## 2. Hypotheses and instance arguments", "",
          "| # | binder | names | type |", "|---|---|---|---|"]
    for k, b in enumerate(d.binders, 1):
        L.append(f"| {k} | {b.label} {b.kind} | "
                 f"{', '.join(b.names) or '—'} | {_q(b.type)} |")
    L += ["", f"**Conclusion:** {_q(' '.join(d.type.split()))}", ""]

    sc = d.scope
    L += ["## 3. Scope at the declaration", "",
          f"- namespace: `{sc.namespace or '(root)'}`",
          "- open: " + (", ".join(f"`{o}`" for o in sc.opens) or "none")]
    L.append("- `variable`s in scope (they become binders if used): "
             + ("none" if not sc.variables else ""))
    for ln, v in sc.variables:
        L.append(f"  - line {ln}: {_q(v)}")
    us = set()
    for _, u in sc.universes:
        us |= set(u.split()[1:])
    sig_text = " ".join(b.type for b in d.binders) + " " + d.type
    used = sorted(set(re.findall(r"(?:Type|Sort)\s+([a-zA-Z_]\w*)", sig_text))
                  | set(x for grp in re.findall(r"\.\{([^}]*)\}", sig_text)
                        for x in grp.replace(",", " ").split()))
    auto = "`Type*`/`Sort*` in the signature introduce fresh universe " \
        "parameters" if re.search(r"(?:Type|Sort)\*", sig_text) else ""
    L.append("- universe parameters: declared " + (", ".join(
        f"`{u}`" for u in sorted(us)) or "none") + "; used in the signature "
        + (", ".join(f"`{u}`" for u in used) or "none")
        + (f"; {auto}" if auto else ""))
    L.append("- `set_option`s in force: " + (
        "none" if not (sc.set_options or st.project_options or any(
            p.startswith("set_option") for p in d.prefix)) else ""))
    for ln, s in sc.set_options:
        L.append(f"  - file line {ln}: `{s}`")
    for p in d.prefix:
        if p.startswith("set_option"):
            L.append(f"  - on this declaration: `{p}`")
    for s in st.project_options:
        L.append(f"  - project-wide, {s}")
    L.append("")

    L += ["## 4. What the signature's names resolve to", "",
          "One level down: each declaration's own binders, `extends`, "
          "fields or body. Follow a field's type by hand, or run the Lean "
          "rung.", ""]
    for r in st.resolutions:
        L.append(f"### {_q(r.token)}")
        L.append("")
        for n in r.notation:
            L.append(f"- notation: `{n[3]}` — {n[0]}:{n[1]}:{n[2]} "
                     f"→ {_q(n[4])}")
        if not r.hits:
            if r.candidates:
                L.append("- **not resolved by source** (tried: "
                         + ", ".join(f"`{c}`" for c in r.candidates) + ")")
            elif not r.notation:
                L.append("- **not resolved by source** (no notation "
                         "declaration found for this token)")
            L.append("")
            continue
        if len({h.full_name for h in r.hits}) > 1 or len(r.hits) > 1:
            L.append(f"- **{len(r.hits)} candidate declarations** — "
                     "ambiguity by source; the first is the innermost "
                     "namespace match, which is Lean's usual preference")
        for h in r.hits[:3]:
            L.append(f"- `{h.kind} {h.full_name}` — {h.cite}")
            if h.doc:
                L.append("  - doc: " + " ".join(h.doc.split()))
            bl = " ".join(b.text for b in h.binders)
            if bl:
                L.append(f"  - binders: {_q(bl)}")
            if h.type:
                L.append(f"  - type: {_q(' '.join(h.type.split()))}")
            if h.prefix:
                L.append("  - prefixed by: " + "; ".join(
                    _q(p) for p in h.prefix))
            if any(v for v in h.scope.variables) and not bl:
                L.append("  - binders come from `variable`s in scope: "
                         + "; ".join(_q(v) for _, v in
                                     h.scope.variables[-3:]))
            if h.extends:
                L.append("  - extends: " + ", ".join(_q(e)
                                                     for e in h.extends))
            for fn, ft in h.fields:
                L.append(f"  - field {_q(fn)} : {_q(ft)}")
            if h.body:
                b = " ".join(h.body.split())
                L.append("  - body: " + _q(b[:400] + (" …" if len(b) > 400
                                                       else "")))
        if len(r.hits) > 3:
            L.append(f"- … and {len(r.hits) - 3} more")
        L.append("")

    if st.derived:
        L += ["## 5. Instances derived from the signature's classes", "",
              "Instances that turn one class into another on the same "
              "carrier and need nothing beyond the class's own parameters, "
              "found by SOURCE GREP (followed "
              f"{max(x[3] for v in st.derived.values() for x in v)} step(s)). "
              "Absence here is not absence in Lean.", "",
              "| from | step | where | instance |", "|---|---|---|---|"]
        for c, chain in st.derived.items():
            for step, cite, hdr, depth in chain:
                L.append(f"| `{c}` | {step} (depth {depth}) | {cite} | "
                         f"{_q(hdr)} |")
        L.append("")

    L += ["## 6. Lean rung", "", st.lean_note, ""]
    for k, v in st.lean.items():
        L += [f"**{k}**", "", "```", v or "(no output)", "```", ""]
    return L


# ---------------------------------------------------------------------------
# Reference pairing
# ---------------------------------------------------------------------------

STOP = {"a", "an", "the", "is", "are", "be", "of", "to", "and", "with",
        "space", "type", "that", "which", "it", "let", "then", "every", "any",
        "inst", "for", "in", "on", "as", "its", "has", "there", "exists",
        "some", "we", "i", "e", "ie", "one", "by", "or", "if", "u", "v",
        "nonempty", "prop", "true", "without", "no"}
# words → the words Lean spells them with. Extend with --synonyms.
SYNONYMS = {
    "hausdorff": ["t2"], "t2": ["t2"], "manifold": ["charted"],
    "homeomorphic": ["homeomorph"], "homeomorphism": ["homeomorph"],
    "three": ["3"], "four": ["4"], "two": ["2"], "dimensional": [],
    "compactness": ["compact"], "topological": ["topological"],
    "boundaryless": ["boundary"],
    "s3": ["sphere", "3"], "s^3": ["sphere", "3"], "s³": ["sphere", "3"],
    "euclidean": ["euclidean"], "r3": ["euclidean", "3"],
    "r4": ["euclidean", "4"], "ℝ³": ["euclidean", "3"],
    "ℝ⁴": ["euclidean", "4"],
}
SUPER = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")


def words(text: str, synonyms: Dict[str, List[str]] = SYNONYMS) -> List[str]:
    """Content words, camel-case split, stemmed a little, synonyms
    applied. Numerals kept: a dimension is content."""
    t = text.translate(SUPER)
    for k in sorted(synonyms, key=len, reverse=True):
        if any(ch in k for ch in "^³⁴ℝ"):
            t = t.replace(k, " " + " ".join(synonyms[k]) + " ")
    t = re.sub(r"([a-z])([A-Z])", r"\1 \2", t)
    t = re.sub(r"(\d)([A-Z])", r"\1 \2", t)
    t = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1 \2", t)
    out = []
    for w in re.split(r"[^\w]+|_", t.lower()):
        if not w or w in STOP:
            continue
        m = re.fullmatch(r"([a-z]+)(\d+)", w)
        pieces = [w] if not m or w in synonyms else [m.group(1), m.group(2)]
        if w in ("t2", "t1", "t0", "t3", "t4", "t5"):
            pieces = [w]
        for p in pieces:
            if p in synonyms:
                out += synonyms[p]
                continue
            for suf in ("ness", "ity"):
                if p.endswith(suf) and len(p) > len(suf) + 3:
                    p = p[:-len(suf)]
            if p.endswith("s") and len(p) > 4 and not p.endswith("ss"):
                p = p[:-1]
            if p not in STOP and not (len(p) == 1 and p.isalpha()):
                out.append(p)
    if not out:
        # `Space X` / "X is a space": when the generic word is ALL there
        # is, it is the content
        out = [w for w in re.split(r"[^\w]+", t.lower())
               if w in ("space", "type")]
    return out


@dataclass
class Clause:
    label: str
    text: str
    words: List[str]
    side: str                      # "hyp" | "concl"


def parse_reference(path: str) -> List[Clause]:
    """List items of the reference file are its clauses. An item under a
    heading containing 'conclusion', or starting 'Conclusion'/'Then', is
    the conclusion side."""
    out: List[Clause] = []
    side = "hyp"
    with open(path, encoding="utf-8") as f:
        for ln in f:
            h = re.match(r"^\s*#+\s*(.*)", ln)
            if h:
                side = "concl" if re.search(r"conclu", h.group(1), re.I) \
                    else "hyp"
                continue
            m = re.match(r"^\s*(?:[-*+]|\d+[.)])\s+(.*\S)", ln)
            if not m:
                continue
            text = m.group(1)
            lab = re.match(r"^\**\(?([A-Za-z]{0,3}\d+[a-z]?)[.:)]\**\s*(.*)",
                           text)
            label = lab.group(1) if lab else f"R{len(out) + 1}"
            body = lab.group(2) if lab else text
            s = "concl" if re.match(r"^\W*(conclusion|then)\b", body, re.I) \
                else side
            out.append(Clause(label, body, words(body), s))
    return out


def lean_clauses(st: Statement) -> List[Clause]:
    """One clause per binder plus the conclusion, with each token's notation
    target and resolved declaration name mixed into its words."""
    expand: Dict[str, str] = {}
    for r in st.resolutions:
        # the resolved name's LAST component: its namespace is where it
        # lives, not what it says
        extra = [n[4] for n in r.notation] + [h.full_name.split(".")[-1]
                                              for h in r.hits[:1]]
        expand[r.token] = " ".join(extra)
    bound = {n.lower() for b in st.decl.binders for n in b.names}

    def ws(t: str) -> List[str]:
        extra = " ".join(expand.get(x, "") for x in tokens(t))
        return [w for w in words(t + " " + extra) if w not in bound]

    out = []
    for k, b in enumerate(st.decl.binders, 1):
        out.append(Clause(f"L{k}", b.text, ws(b.type or " ".join(b.names)),
                          "hyp"))
    t = st.decl.type
    out.append(Clause("L-concl", " ".join(t.split()), ws(t), "concl"))
    return out


def pair(ref: List[Clause], lean: List[Clause]):
    """Each Lean clause goes to the reference clause it overlaps best —
    most shared words, then Jaccard — so `simply connected` beats
    `connected` for `SimplyConnectedSpace`, and an explanatory tail on a
    reference clause does not cost it the match. A reference clause is
    matched when some Lean clause chose it. Conclusion pairs with
    conclusion only."""
    chosen: Dict[str, List[Tuple[Clause, float, List[str]]]] = {}
    lean_unmatched = []
    for lc in lean:
        best = None
        L = set(lc.words)
        for rc in ref:
            if (rc.side == "concl") != (lc.side == "concl"):
                continue
            R = set(rc.words)
            sh = R & L
            if not sh:
                continue
            j = len(sh) / len(R | L)
            if best is None or (len(sh), j) > (len(best[2]), best[1]):
                best = (rc, j, sorted(sh))
        if best is None:
            lean_unmatched.append(lc)
        else:
            chosen.setdefault(best[0].label, []).append((lc, best[1],
                                                         best[2]))
    return chosen, lean_unmatched


def render_pairing(st: Statement, ref: List[Clause], ref_path: str
                   ) -> List[str]:
    lean = lean_clauses(st)
    chosen, lean_un = pair(ref, lean)
    L = ["## 7. Reference pairing", "",
         f"Reference: `{ref_path}` — written before reading the Lean. "
         "Pairing is by word overlap after camel-case splitting, notation "
         "expansion and a small synonym table; a pair is a pointer for a "
         "human, not a verdict. **The unmatched lists are the output.**", "",
         "| ref | reference clause | Lean clause(s) | shared words | note |",
         "|---|---|---|---|---|"]
    ref_un = []
    for rc in ref:
        ms = chosen.get(rc.label, [])
        if not ms:
            ref_un.append(rc)
            L.append(f"| {rc.label} | {rc.text} | **none** | | |")
            continue
        for lc, j, sh in ms:
            rn = set(re.findall(r"\d+", " ".join(rc.words)))
            ln = set(re.findall(r"\d+", " ".join(lc.words)))
            note = ""
            if rn and ln and not rn <= ln:
                note = (f"numerals differ: reference {sorted(rn)}, Lean "
                        f"{sorted(ln)} — check the dimension convention")
            L.append(f"| {rc.label} | {rc.text} | {lc.label} "
                     f"{_q(lc.text)} | {', '.join(sh)} | {note} |")
    L += ["", "### Reference clauses with no Lean counterpart", ""]
    if not ref_un:
        L.append("none")
    for rc in ref_un:
        L.append(f"- **{rc.label}** {rc.text}")
        R = set(rc.words)
        near = [(lc, sorted(R & set(lc.words))) for lc in lean
                if R & set(lc.words)]
        for lc, sh in near:
            L.append(f"  - shares {', '.join(sh)} with {lc.label} "
                     f"{_q(lc.text)}, which paired elsewhere")
        in_sig = {h.full_name for r in st.resolutions for h in r.hits[:1]}
        for src, chain in st.derived.items():
            for step, cite, hdr, depth in chain:
                target = step.split("⟹")[-1].strip()
                tw = set(words(target))
                if target in in_sig or not tw:
                    continue
                if tw <= R | {"path"}:
                    L.append(f"  - possibly implied: {step} ({cite}, "
                             f"depth {depth}; source grep, unverified)")
        if not near:
            L.append("  - no Lean clause shares a content word: a human "
                     "must decide whether it is carried implicitly (by a "
                     "definition's meaning) or missing")
    L += ["", "### Lean clauses with no reference counterpart", ""]
    if not lean_un:
        L.append("none")
    for lc in lean_un:
        L.append(f"- **{lc.label}** {_q(lc.text)} — an assumption the "
                 "reference did not state, or bookkeeping (a carrier type, "
                 "a structure the reference takes for granted)")
    L.append("")
    return L


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("project")
    ap.add_argument("module")
    ap.add_argument("theorem", help="fully qualified name")
    ap.add_argument("--mathlib", help="a Mathlib source checkout, used when "
                    "the project has no .lake/packages/mathlib")
    ap.add_argument("--toolchain-src", help="Lean's src/lean (Init, Std)")
    ap.add_argument("--reference", help="REF.md written before reading")
    ap.add_argument("--no-lean", action="store_true",
                    help="skip the Lean rung")
    ap.add_argument("--derive-depth", type=int, default=2)
    ap.add_argument("-o", "--out", help="write the dossier here")
    a = ap.parse_args(argv)
    st = build(a.project, a.module, a.theorem, mathlib=a.mathlib,
               tc_src=a.toolchain_src, run_lean=not a.no_lean,
               derive_depth=a.derive_depth)
    lines = render(st)
    if a.reference:
        lines += render_pairing(st, parse_reference(a.reference),
                                a.reference)
    text = "\n".join(lines).rstrip() + "\n"
    if a.out:
        os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
        with open(a.out, "w", encoding="utf-8") as f:
            f.write(text)
        print(f"wrote {a.out}")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
