"""The checker ensemble — real adapters, and tiers that mean something.

## The tiers, and what each one actually buys

| tier | adapter | what it establishes |
|---|---|---|
| quick | `LeanElaborate` | the file elaborates; its axioms are in the whitelist |
| medium | `Lean4Lean` | a second kernel, in Lean, re-checks a module's declarations |
| high | `Comparator` | the solution proves the SAME STATEMENT as an independently authored challenge, within an axiom budget, accepted by the kernel — and by every external kernel configured |
| high | `ConLeche` (`--verified`) | an independent checker, written in Lean with its own term representation and proven in Lean not to accept a proof of `False`, accepts the `lean4export` stream |
| high-trusted | `ConLeche` (`--trusted`) | the same checker with its certification-only checks off: independent, but OUTSIDE the proven theorem |

**The members are not equally independent, and the ensemble must not
pretend they are.** nanoda is a from-scratch Rust kernel. Lean4Lean is a
port: its own README says it is "derived directly from the C++ kernel
implementation, and as such likely shares some implementation bugs with
it (it's not really an independent implementation)". So a Lean4Lean
*agreement* with Lean is weak evidence and a Lean4Lean *disagreement* is
strong — asymmetric, and any likelihood ratio computed over these
verdicts has to carry that rather than counting heads.

`leanchecker` is deliberately **not** a tier. It ships with the toolchain
and replays an olean, but it is Lean's own kernel running again: it
shares every blind spot of the thing it is checking. Counting it as a
second opinion is exactly the elaborator-common-mode failure this design
exists to avoid.

## What comparator adds that a checker cannot

A bare checker answers "does this proof check?". Comparator answers "does
this proof check, AND is it a proof of the statement I asked about?" —
it compares the declarations appearing in the challenge's statement
against the solution's environment. That closes an attack a checker is
blind to by construction: a solution that redefines what the words in the
statement mean.

Which puts a boundary on this module worth stating plainly: **comparator
needs a challenge.** Given a claimed proof with no independently authored
statement, it can bound axioms and re-check the kernel, but it cannot
tell you the specification drifted — there is nothing to drift from.
That is the common case, and it is exactly why the coherence rung is not
optional.

## Binaries

Discovery is by environment variable, falling back to conventional
locations; see `available()`. Nothing here installs anything, and every
adapter degrades to `ERROR` (never to a verdict) when its binary is
missing.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence

# Axioms a Lean proof may use without comment. Anything else is reported.
WHITELIST = ("propext", "Classical.choice", "Quot.sound")

# Comparator's own words. Exit status alone is ambiguous — a rejected
# solution and a project that would not build both exit non-zero — and
# collapsing them is how an adapter reports "everything is broken" as
# "everything is refuted".
_OK_MARK = "your solution is okay"
_INFRA_MARKS = (
    "no configuration file", "error: [root]", "command not found",
    "no such file", "cannot find", "child exited with",
)

ACCEPT = "accept"
REJECT = "reject"
ERROR = "error"          # infrastructure failed — NOT a verdict either way
DECLINED = "declined"    # the checker says it does not support the input —
                         # a statement about the checker, NOT a verdict
TIMEOUT = "timeout"      # a cost anomaly, and its own signal

_ERROR_RE = re.compile(r"^\S+:\d+:\d+: error", re.MULTILINE)
_AXIOM_RE = re.compile(r"depends on axioms: \[([^\]]*)\]")


@dataclass
class Verdict:
    checker: str
    tier: str
    outcome: str
    axioms: List[str] = field(default_factory=list)
    detail: str = ""
    seconds: float = 0.0
    # Which mode of the checker produced this verdict, when the checker
    # has modes whose guarantees differ (con-leche: `verified` is the
    # mode its theorem is about, `trusted` is not). Empty otherwise.
    mode: str = ""

    @property
    def informative(self) -> bool:
        """`error` and `timeout` are NOT folded into accept or reject.

        Treating an infrastructure failure as either is how an ensemble
        manufactures agreement it did not earn. A member that could not
        run has not voted.
        """
        return self.outcome in (ACCEPT, REJECT)


@dataclass
class EnsembleResult:
    verdicts: List[Verdict]

    @property
    def informative_verdicts(self) -> List[Verdict]:
        return [v for v in self.verdicts if v.informative]

    @property
    def disagreement(self) -> bool:
        """Did the informative checkers split?

        Only ever meaningful across checkers that do not share an
        implementation. An ensemble of one cannot disagree, and an
        ensemble of two that share a kernel can only disagree by
        accident.
        """
        return len({v.outcome for v in self.informative_verdicts}) > 1

    @property
    def unanimous_accept(self) -> bool:
        vs = self.informative_verdicts
        return bool(vs) and all(v.outcome == ACCEPT for v in vs)

    @property
    def unanimous_reject(self) -> bool:
        vs = self.informative_verdicts
        return bool(vs) and all(v.outcome == REJECT for v in vs)

    @property
    def off_whitelist(self) -> List[str]:
        out: set = set()
        for v in self.verdicts:
            out |= set(v.axioms) - set(WHITELIST)
        return sorted(out)

    @property
    def tiers_run(self) -> List[str]:
        return sorted({v.tier for v in self.verdicts})

    def summary(self) -> str:
        """Every report must say which tiers ran. A verdict whose
        ensemble is unstated cannot be read later."""
        parts = [f"{v.checker}{'[' + v.mode + ']' if v.mode else ''}"
                 f"={v.outcome}" for v in self.verdicts]
        s = f"tiers[{','.join(self.tiers_run)}]: " + ", ".join(parts)
        if self.disagreement:
            s = "disagreement: " + s
        if self.off_whitelist:
            s += f"; off-whitelist axioms: {', '.join(self.off_whitelist)}"
        return s


# ---------------------------------------------------------------------------
# Adapters
# ---------------------------------------------------------------------------

def _elan(name: str) -> Optional[str]:
    """Find a Lean toolchain binary, elan layout included."""
    found = shutil.which(name)
    if found:
        return found
    for base in (os.path.expanduser("~/.elan/bin"), "/root/.elan/bin"):
        cand = os.path.join(base, name)
        if os.path.exists(cand):
            return cand
    return None


@dataclass
class LeanElaborate:
    """Quick tier: elaborate the file, read the axioms it prints."""

    name: str = "lean"
    tier: str = "quick"
    timeout_s: int = 900

    def check(self, path: str, project_dir: Optional[str] = None) -> Verdict:
        lean = _elan("lean")
        if lean is None:
            return Verdict(self.name, self.tier, ERROR, detail="no lean on PATH")
        cmd = [lean, os.path.abspath(path)]
        if project_dir:
            lake = _elan("lake")
            if lake is None:
                return Verdict(self.name, self.tier, ERROR,
                               detail="project_dir given but no lake on PATH")
            cmd = [lake, "env"] + cmd
        t0 = time.time()
        try:
            p = subprocess.run(cmd, capture_output=True, text=True,
                               timeout=self.timeout_s, cwd=project_dir or None)
        except subprocess.TimeoutExpired:
            return Verdict(self.name, self.tier, TIMEOUT, seconds=self.timeout_s,
                           detail="elaboration exceeded the budget")
        return self.read_output(p.stdout + p.stderr,
                                seconds=round(time.time() - t0, 1))

    def read_output(self, out: str, seconds: float = 0.0) -> Verdict:
        """Split out so the parse is testable without a toolchain — which
        is the point of the parse-output-never-exit-codes rule."""
        axioms: List[str] = []
        for m in _AXIOM_RE.finditer(out):
            axioms += [a.strip() for a in m.group(1).split(",") if a.strip()]
        errs = _ERROR_RE.findall(out)
        return Verdict(
            self.name, self.tier, REJECT if errs else ACCEPT,
            axioms=sorted(set(axioms)), seconds=seconds,
            detail=(f"{len(errs)} elaboration error(s)" if errs
                    else "elaborated cleanly"),
        )


@dataclass
class Lean4Lean:
    """Medium tier: a second kernel implementation, in Lean.

    Two things this adapter has to get right, both learned by running it
    and reading the output:

    **Exit status is not the verdict.** `lean4lean` exits 0 while
    printing "lean4lean found a problem in <mod>". An adapter that reads
    the exit code records a caught unsoundness as a clean pass. (The
    comparator adapter had the mirror-image bug, mapping a failed build
    onto `reject`. Two adapters, two opposite errors, one lesson: parse
    what the tool says, never how it exited.)

    **Aim matters.** Without `--fresh` it checks the named module only
    and assumes its imports are correct — so pointed at an exported
    result it can honestly report "checked 2 declarations" while the
    defect sits one import away. Which is the argument for checking per
    obligation rather than per artifact.
    """

    binary: str
    name: str = "lean4lean"
    tier: str = "medium"
    timeout_s: int = 3600

    @classmethod
    def discover(cls, root: Optional[str] = None) -> Optional["Lean4Lean"]:
        root = root or os.environ.get("SVA_LEAN4LEAN", "")
        if not root:
            return None
        b = os.path.join(root, ".lake/build/bin/lean4lean")
        return cls(binary=b) if os.path.exists(b) else None

    def check_module(self, project_dir: str, module: str,
                     fresh: bool = False) -> Verdict:
        lake = _elan("lake")
        if lake is None:
            return Verdict(self.name, self.tier, ERROR, detail="no lake on PATH")
        args = [lake, "env", self.binary]
        if fresh:
            args.append("--fresh")
        args.append(module)
        t0 = time.time()
        try:
            p = subprocess.run(args, capture_output=True, text=True,
                               cwd=project_dir, timeout=self.timeout_s)
        except subprocess.TimeoutExpired:
            return Verdict(self.name, self.tier, TIMEOUT,
                           detail=f"exceeded {self.timeout_s}s on {module}")
        return self.read_output((p.stdout + p.stderr).strip(),
                                returncode=p.returncode,
                                seconds=round(time.time() - t0, 1))

    def read_output(self, out: str, returncode: Optional[int] = None,
                    seconds: float = 0.0) -> Verdict:
        low = out.lower()
        if "found a problem" in low:
            return Verdict(self.name, self.tier, REJECT, seconds=seconds,
                           detail=out[:400])
        if "checked" in low and "declaration" in low:
            return Verdict(self.name, self.tier, ACCEPT, seconds=seconds,
                           detail=out[:200])
        return Verdict(self.name, self.tier, ERROR, seconds=seconds,
                       detail=out[:400] or f"exit {returncode}")


@dataclass
class Comparator:
    """High tier: challenge/solution comparison, axiom budget, kernel
    replay, plus any external kernels configured.

    `external_kernels` is how nanoda enters — an independent Rust kernel,
    the only member of this ensemble that does not share Lean's
    implementation, and therefore the only one whose agreement with the
    builtin kernel is evidence of anything.
    """

    binary: str
    lean4export: str
    landrun: Optional[str] = None
    nanoda: Optional[str] = None
    name: str = "comparator"
    tier: str = "high"
    timeout_s: int = 3600

    @classmethod
    def discover(cls, root: Optional[str] = None,
                 nanoda_dir: Optional[str] = None) -> Optional["Comparator"]:
        root = root or os.environ.get("SVA_COMPARATOR", "")
        nanoda_dir = nanoda_dir or os.environ.get("SVA_NANODA", "")
        if not root:
            return None
        b = os.path.join(root, ".lake/build/bin/comparator")
        e = os.path.join(
            root, ".lake/packages/lean4export/.lake/build/bin/lean4export")
        if not (os.path.exists(b) and os.path.exists(e)):
            return None
        nanoda = (os.path.join(nanoda_dir, "target/release/nanoda_bin")
                  if nanoda_dir else "")
        return cls(binary=b, lean4export=e, landrun=shutil.which("landrun"),
                   nanoda=nanoda if nanoda and os.path.exists(nanoda) else None)

    @staticmethod
    def stage(files: Dict[str, str], toolchain: str,
              lean_libs: Sequence[str] = ("Challenge", "Solution")) -> str:
        """Write a minimal lake project comparator can build.

        Comparator drives `lake build` inside the project, so a bare
        directory of `.lean` files is not enough: without a lakefile it
        fails before it ever compares anything. The toolchain is pinned
        by the CALLER, because an artifact's Lean version is part of the
        artifact.
        """
        d = tempfile.mkdtemp(prefix="sva-cmp-")
        for rel, content in files.items():
            path = os.path.join(d, rel)
            os.makedirs(os.path.dirname(path) or d, exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
        libs = "\n".join(f'[[lean_lib]]\nname = "{n}"\n' for n in lean_libs)
        with open(os.path.join(d, "lakefile.toml"), "w") as f:
            f.write(f'name = "svaudit"\nversion = "0.1.0"\n\n{libs}')
        with open(os.path.join(d, "lean-toolchain"), "w") as f:
            f.write(toolchain.strip() + "\n")
        return d

    def check_pair(
        self, project_dir: str, challenge_module: str, solution_module: str,
        theorem_names: Sequence[str],
        permitted_axioms: Sequence[str] = WHITELIST,
        definition_names: Sequence[str] = (),
        use_nanoda: bool = True,
    ) -> List[Verdict]:
        """One verdict for the builtin kernel and one per external kernel,
        so a caller can see WHICH member dissented rather than only that
        somebody did."""
        cfg: Dict[str, object] = {
            "challenge_module": challenge_module,
            "solution_module": solution_module,
            "theorem_names": list(theorem_names),
            "permitted_axioms": list(permitted_axioms),
        }
        if definition_names:
            cfg["definition_names"] = list(definition_names)
        externals = {}
        if use_nanoda and self.nanoda:
            externals["nanoda"] = [self.nanoda]
        if externals:
            cfg["external_kernels"] = externals

        lake = _elan("lake")
        if lake is None:
            return [Verdict(f"{self.name}/kernel", self.tier, ERROR,
                            detail="no lake on PATH")]
        fd, cfg_path = tempfile.mkstemp(suffix=".json", dir=project_dir)
        with os.fdopen(fd, "w") as f:
            json.dump(cfg, f, indent=1)
        env = dict(os.environ)
        env["COMPARATOR_LEAN4EXPORT"] = self.lean4export
        if self.landrun:
            env["COMPARATOR_LANDRUN"] = self.landrun
        if self.nanoda:
            env["COMPARATOR_NANODA"] = self.nanoda
        t0 = time.time()
        try:
            p = subprocess.run([lake, "env", self.binary, cfg_path],
                               capture_output=True, text=True, cwd=project_dir,
                               timeout=self.timeout_s, env=env)
            out, rc = (p.stdout + p.stderr).strip(), p.returncode
        except subprocess.TimeoutExpired:
            out, rc = "comparator exceeded the budget", None
        finally:
            os.unlink(cfg_path)
        return self.read_output(out, rc, sorted(externals),
                                seconds=round(time.time() - t0, 1))

    def read_output(self, out: str, returncode: Optional[int],
                    externals: Sequence[str] = (),
                    seconds: float = 0.0) -> List[Verdict]:
        members = ["kernel"] + list(externals)
        if returncode is None:
            return [Verdict(f"{self.name}/{m}", self.tier, TIMEOUT,
                            detail=out[:400]) for m in members]
        low = out.lower()
        if returncode == 0 and _OK_MARK in low:
            outcome = ACCEPT
        elif any(mark in low for mark in _INFRA_MARKS) and _OK_MARK not in low:
            # Infrastructure, not a verdict. A member that could not run
            # has not voted, and `informative` keeps it out of the
            # disagreement count rather than manufacturing one.
            outcome = ERROR
        else:
            outcome = REJECT
        # Comparator reports one exit status for the whole run. A
        # rejection naming a kernel is attributed to it; otherwise the
        # verdict is the run's, and saying so beats inventing per-member
        # detail the tool did not give us.
        vs = []
        for m in members:
            named = m != "kernel" and m in low
            vs.append(Verdict(
                f"{self.name}/{m}", self.tier, outcome, seconds=seconds,
                detail=(f"named in comparator output: {out[:300]}" if named
                        else out[:300] or f"exit {returncode}")))
        return vs


# con-leche's verdict lines (Main.lean, `con-leche: …`). The mode tag in
# parentheses is printed on EVERY verdict line precisely so a `--trusted`
# run cannot be mistaken for a `--verified` one in a log; the adapter
# reads it back and refuses a line whose mode is not the one it asked for.
_CL_ACCEPT_RE = re.compile(
    r"^con-leche: accepted (\d+) declarations \((--verified|--trusted)\)",
    re.MULTILINE)
_CL_LINE_RE = re.compile(r"^con-leche: (.*)$", re.MULTILINE)
_CL_MODE_RE = re.compile(r"\((--verified|--trusted)\)")
_CL_OOM = "INTERNAL PANIC: out of memory"

TRUSTED_TIER = "high-trusted"


def _local_bin(name: str) -> Optional[str]:
    cand = os.path.join(os.path.expanduser("~/.local/bin"), name)
    return cand if os.path.exists(cand) else None


def _bin_or_repo(value: str, rel: str) -> Optional[str]:
    """An environment variable may name the binary or the repo it was
    built in; accept either, and nothing that does not exist."""
    if not value:
        return None
    if os.path.isdir(value):
        value = os.path.join(value, rel)
    return value if os.path.isfile(value) else None


def stream_axioms(ndjson_path: str) -> List[str]:
    """Names of every `axiom` record in a `lean4export` NDJSON stream.

    These are the axioms the stream DECLARES. For an export filtered to
    one theorem's cone (`lean4export Mod -- name`) that is the axioms
    the cone reaches, which is what `#print axioms` reports; for a
    whole-module export it is a superset (Init declares `sorryAx` and
    the `ofReduce*` family whether anything uses them or not). Read off
    the stream itself, never off the checker's output: con-leche does
    not print them, and a list the checker did not produce should not
    be attributed to it.
    """
    names: Dict[int, str] = {0: ""}
    axiom_ids: List[int] = []
    with open(ndjson_path, "r", encoding="utf-8") as f:
        for line in f:
            if '"in":' in line:
                try:
                    o = json.loads(line)
                except ValueError:
                    continue
                if "in" not in o:
                    continue
                if isinstance(o.get("str"), dict):
                    pre = names.get(o["str"]["pre"], "")
                    s = o["str"]["str"]
                    names[o["in"]] = f"{pre}.{s}" if pre else s
                elif isinstance(o.get("num"), dict):
                    pre = names.get(o["num"]["pre"], "")
                    i = o["num"]["i"]
                    names[o["in"]] = f"{pre}.{i}" if pre else str(i)
            elif '"axiom":' in line[:12]:
                try:
                    axiom_ids.append(json.loads(line)["axiom"]["name"])
                except (ValueError, KeyError, TypeError):
                    continue
    return sorted({names.get(i, f"<name #{i}>") for i in axiom_ids})


@dataclass
class ConLeche:
    """High tier: con-leche, an external checker for `lean4export` NDJSON.

    Written in Lean with its own term representation (not `Lean.Expr`),
    so it shares no code path with Lean's C++ kernel, with Lean4Lean's
    port of it, or with nanoda. In `--verified` mode (the default) it is
    proven, in Lean, that every environment it accepts has a model in a
    set theory with an omega-chain of Grothendieck universes — hence no
    accepted proof of `False` (`ConLeche.model_exists`,
    `no_False_declaration`).

    What that theorem does NOT cover, and this adapter must not let a
    reader forget (ReadingGroup note `papers/con-leche-repo/notes.md`,
    con-leche `OVERVIEW.md` §9):

    * `--trusted` mode — same checker bodies with certification-only
      checks off. Reported under tier `high-trusted`, which is not the
      formal tier, so `Finding` refuses to file it `formal`.
    * the frontend: the byte-level corollary covers one JSON template;
      the projection rewrite and model generation are reviewed, not
      proven, to preserve meaning;
    * runtime `Nat` (fast Nat operations use Lean's runtime bignums),
      the compiled binary, IO and the compiler;
    * any non-acceptance: exit 1 and 2 carry no theorem.

    And one thing about axioms: it accepts only `propext`,
    `Classical.choice`, `Quot.sound`; an unused `sorryAx` declaration is
    ignored and a use of it declines; the `ofReduce*`/`trustCompiler`
    axioms are replaced by definitions of the same type; any other
    axiom declines. So an accept already bounds the axioms — but the
    list recorded here is read from the stream, not from the checker.

    **Parse the verdict line, never the exit code alone.** Exit 1 is both
    a reject and the Lean runtime's out-of-memory panic
    (`INTERNAL PANIC: out of memory` on stderr); only the stderr tells
    them apart. Exit 2 (declined) is a statement about the CHECKER and
    is not a vote. The verdict line names the mode it ran in, and a
    line that names the other mode is an error, not a verdict.
    """

    binary: str
    lean4export: Optional[str] = None
    name: str = "con-leche"
    timeout_s: int = 7200

    @classmethod
    def discover(cls, repo: Optional[str] = None) -> Optional["ConLeche"]:
        """`$CON_LECHE` (the binary, or the repo it was built in), then
        PATH, then `~/.local/bin`, then a given repo's build output."""
        b = (_bin_or_repo(os.environ.get("CON_LECHE", ""),
                          ".lake/build/bin/con-leche")
             or shutil.which("con-leche") or _local_bin("con-leche")
             or (_bin_or_repo(repo, ".lake/build/bin/con-leche")
                 if repo else None))
        return cls(binary=b, lean4export=find_lean4export()) if b else None

    @staticmethod
    def tier_for(verified: bool) -> str:
        return "high" if verified else TRUSTED_TIER

    # -- export ----------------------------------------------------------

    def export(self, project_dir: str, module: str,
               decls: Sequence[str] = (), out_path: Optional[str] = None,
               timeout_s: int = 7200) -> str:
        """Run `lean4export` in the project's lake env; return the NDJSON
        path. `decls` restricts the export to those declarations and
        their transitive dependencies (`lean4export Mod -- d1 d2`), which
        is both far smaller and what makes `stream_axioms` mean "axioms
        the cone reaches".

        The exporter's output format tracks the Lean version, so it must
        be built at the PROJECT's toolchain (con-leche `scripts/
        selfcheck.sh`: the lean4export commit whose `lean-toolchain`
        equals the project's). The module must already be built.
        Raises `RuntimeError` on failure — an export that did not happen
        is an infrastructure fact, and `check` never sees it.
        """
        exe = self.lean4export or find_lean4export()
        if exe is None:
            raise RuntimeError("no lean4export (set $LEAN4EXPORT)")
        lake = _elan("lake")
        if lake is None:
            raise RuntimeError("no lake on PATH")
        if out_path is None:
            fd, out_path = tempfile.mkstemp(prefix="sva-export-",
                                            suffix=".ndjson")
            os.close(fd)
        args = [lake, "env", exe, module]
        if decls:
            args += ["--"] + list(decls)
        with open(out_path, "w", encoding="utf-8") as out:
            p = subprocess.run(args, stdout=out, stderr=subprocess.PIPE,
                               text=True, cwd=project_dir, timeout=timeout_s)
        if p.returncode != 0 or os.path.getsize(out_path) == 0:
            os.unlink(out_path)
            raise RuntimeError(f"lean4export exit {p.returncode}: "
                               f"{p.stderr.strip()[:400]}")
        return out_path

    # -- check -----------------------------------------------------------

    def check(self, ndjson_path: str, verified: bool = True,
              jobs: Optional[int] = None,
              scan_axioms: bool = True) -> Verdict:
        mode = "--verified" if verified else "--trusted"
        args = [self.binary, mode]
        if jobs is not None:
            args.append(f"--jobs={int(jobs)}")
        args.append(ndjson_path)
        try:
            axioms = stream_axioms(ndjson_path) if scan_axioms else []
        except OSError:
            axioms = []          # the checker will say so, and we parse it
        t0 = time.time()
        try:
            p = subprocess.run(args, capture_output=True, text=True,
                               timeout=self.timeout_s)
        except subprocess.TimeoutExpired:
            return Verdict(self.name, self.tier_for(verified), TIMEOUT,
                           axioms=axioms, mode=mode.lstrip("-"),
                           seconds=self.timeout_s,
                           detail=f"exceeded {self.timeout_s}s")
        except OSError as e:
            return Verdict(self.name, self.tier_for(verified), ERROR,
                           mode=mode.lstrip("-"), detail=str(e))
        return self.read_output(p.stdout, p.stderr, p.returncode,
                                verified=verified, axioms=axioms,
                                seconds=round(time.time() - t0, 1))

    def read_output(self, stdout: str, stderr: str,
                    returncode: Optional[int], verified: bool = True,
                    axioms: Sequence[str] = (),
                    seconds: float = 0.0) -> Verdict:
        """Split out so the parse is testable without the binary.

        The outcome is the PARSED verdict line, cross-checked against the
        exit code; where the two disagree, or the line names the wrong
        mode, the result is `error` — the adapter does not pick one.
        """
        want = "--verified" if verified else "--trusted"
        tier = self.tier_for(verified)
        mode = want.lstrip("-")
        out = (stdout or "") + ("\n" if stdout and stderr else "") + (
            stderr or "")

        def v(outcome: str, detail: str) -> Verdict:
            scope = ("" if verified else
                     " [--trusted: outside con-leche's proven theorem]")
            return Verdict(self.name, tier, outcome, axioms=sorted(axioms),
                           detail=detail[:400] + scope, seconds=seconds,
                           mode=mode)

        if _CL_OOM in out:
            # Exit 1, like a reject — and not one. A resource blow-out
            # is its own signal (DESIGN §3), and no verdict either way.
            return v(ERROR, f"out of memory (exit {returncode}): "
                            "the Lean runtime's panic, not a reject")
        lines = _CL_LINE_RE.findall(out)
        m = _CL_ACCEPT_RE.search(out)
        verdict_lines = [l for l in lines if _CL_MODE_RE.search(l)]
        if not verdict_lines:
            if returncode == 3 or lines:
                return v(ERROR, "; ".join(lines) or f"exit {returncode}")
            return v(ERROR, f"no verdict line (exit {returncode}): "
                            f"{out.strip()[:300]}")
        line = verdict_lines[-1]
        seen_mode = _CL_MODE_RE.search(line).group(1)
        if seen_mode != want:
            return v(ERROR, f"asked for {want}, verdict line says "
                            f"{seen_mode}: {line}")
        if m:
            kind, want_rc = ACCEPT, 0
            detail = f"accepted {m.group(1)} declaration records ({want})"
        elif (line.startswith("declined:")
              or line.startswith("not implemented yet:")):
            kind, want_rc = DECLINED, 2
            detail = f"declined — the checker does not support: {line}"
        elif line.startswith("invalid:"):
            kind, want_rc = REJECT, 1
            detail = line
        elif line.startswith("internal error:") or returncode == 3:
            kind, want_rc = ERROR, 3
            detail = line
        else:
            return v(ERROR, f"unrecognised verdict line (exit "
                            f"{returncode}): {line}")
        if returncode is not None and returncode != want_rc:
            return v(ERROR, f"verdict line and exit code disagree "
                            f"(exit {returncode}): {line}")
        return v(kind, detail)


def find_lean4export() -> Optional[str]:
    """`$LEAN4EXPORT` (binary or repo), PATH, `~/.local/bin`, or the copy
    comparator bundles under `$SVA_COMPARATOR`."""
    b = (_bin_or_repo(os.environ.get("LEAN4EXPORT", ""),
                      ".lake/build/bin/lean4export")
         or shutil.which("lean4export") or _local_bin("lean4export"))
    if b:
        return b
    cmp_root = os.environ.get("SVA_COMPARATOR", "")
    return _bin_or_repo(
        os.path.join(cmp_root, ".lake/packages/lean4export") if cmp_root
        else "", ".lake/build/bin/lean4export")


# ---------------------------------------------------------------------------
# The ensemble
# ---------------------------------------------------------------------------

def quick_ensemble(path: str,
                   project_dir: Optional[str] = None) -> EnsembleResult:
    """What the cheap rung can honestly run on a bare file.

    One member, and the name says so. This is not an ensemble in the
    sense the design means; calling the result "unanimous" would be true
    and misleading, which is why `disagreement` is False here for the
    boring reason and `summary()` prints the membership.
    """
    return EnsembleResult([LeanElaborate().check(path, project_dir)])


def module_ensemble(project_dir: str, module: str, source_path: str,
                    l4l: Optional[Lean4Lean] = None) -> EnsembleResult:
    """Every available checker, pointed at the SAME module. This one may
    legitimately disagree."""
    vs = [LeanElaborate().check(source_path, project_dir)]
    l4l = l4l or Lean4Lean.discover()
    if l4l:
        vs.append(l4l.check_module(project_dir, module))
    return EnsembleResult(vs)


def scan_modules(l4l: Lean4Lean, project_dir: str,
                 modules: Sequence[str]) -> Dict[str, Verdict]:
    """One verdict per module — deliberately NOT an `EnsembleResult`.

    Disagreement means *checkers differing about the same object*. Two
    modules getting different verdicts is not disagreement, it is a
    development with one bad module in it, and wrapping this in an
    ensemble would report a spurious dissent — inflating the single
    component the whole architecture is gated on.
    """
    return {m: l4l.check_module(project_dir, m) for m in modules}


def available() -> Dict[str, bool]:
    """What this environment can actually run, for a runner to report
    rather than assume. A report that does not say which tiers were
    available cannot be read later."""
    c = Comparator.discover()
    return {
        "lean": _elan("lean") is not None,
        "lean4lean": Lean4Lean.discover() is not None,
        "comparator": c is not None,
        "landrun": bool(c and c.landrun),
        "nanoda": bool(c and c.nanoda),
        "con-leche": ConLeche.discover() is not None,
        "lean4export": find_lean4export() is not None,
    }
