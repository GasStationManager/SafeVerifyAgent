"""Who audits: the agent layer, and the seam other families plug into.

Three adapters, and the difference between them is not cosmetic:

| adapter | how it runs | tools? |
|---|---|---|
| `ClaudeCliModel` | `claude -p`, one subprocess per call | **yes** |
| `GenericCliModel` | any one-shot CLI (`codex exec`, `gemini -p`, …) | depends on the CLI |
| `AnthropicApiModel` | the Messages API, official SDK | **no** |

**Tool capability decides which rungs an adapter may serve, and the
driver enforces it.** The check rung's whole job is to RUN the ensemble
on an obligation — elaborate it, read the axioms, compare kernels. A
text-in/text-out model cannot do any of that, and asked to anyway it will
produce a confident description of a run that never happened. So
`tool_capable` is a hard gate: a text-only adapter may serve the
coherence rung (reconstructing an argument is reading and thinking, which
is exactly what it can do) and is REFUSED for the check rung.

That is also why the CLI adapter is the default rather than the SDK one,
which is the reverse of what you would guess.

**Why a CLI seam at all**, when one adapter would do: same-family
authorship is a confound no amount of `n` removes — an auditor reading an
artifact from its own family is not an independent test. Cross-family
staffing is the only fix, and every other frontier agent ships a one-shot
CLI. `GenericCliModel` makes a second family a config line rather than a
fork; `spec` strings make it a command-line argument.
"""

from __future__ import annotations

import json
import subprocess
import uuid
from dataclasses import dataclass, field
from typing import Any, Dict, Optional, Sequence

DEFAULT_CLAUDE_MODEL = "claude-opus-5"

# Tools a worker legitimately needs: read the artifact, search it, and run
# the checkers. Deliberately no Write/Edit — an auditor that can modify
# the artifact it is auditing is a different and much worse thing, and
# "you do not repair the proof" should be enforced, not just asked for.
WORKER_TOOLS = ("Read", "Grep", "Glob", "Bash")


class ModelError(RuntimeError):
    pass


@dataclass
class Reply:
    text: str
    cost_usd: float = 0.0
    turns: int = 0
    model: str = ""
    raw: Dict[str, Any] = field(default_factory=dict)


class Model:
    """One call, text in and text out.

    Deliberately tiny. Anything richer starts encoding one provider's
    request shape into the harness, which is what turns a cross-family
    run into a fork instead of a flag.
    """

    family: str = "unknown"
    tool_capable: bool = False

    def complete(self, system: str, user: str,
                 cwd: Optional[str] = None) -> Reply:  # pragma: no cover
        raise NotImplementedError


@dataclass
class ClaudeCliModel(Model):
    """`claude -p` — a one-shot Claude Code agent per call.

    Tool-capable, which is the point: the check rung needs to actually
    run Lean, and this adapter gives a worker Read/Grep/Glob/Bash without
    the harness having to implement a tool loop.

    Two things this gets right that are easy to miss:

    * **A fresh `--session-id` per call.** Without one the subprocess can
      land in the caller's own session, so workers meant to be
      independent share history — and worker isolation is load-bearing
      here: auditors that can see each other's findings can talk each
      other into a verdict.
    * **`is_error` is the verdict on the RUN, not on the audit.** A
      non-zero exit or an error result means this worker did not vote; it
      must never be folded into a finding, for the same reason an
      ensemble member that could not run has not voted.
    """

    model: str = DEFAULT_CLAUDE_MODEL
    binary: str = "claude"
    timeout_s: int = 1800
    allowed_tools: Sequence[str] = WORKER_TOOLS
    tool_capable: bool = True

    @property
    def family(self) -> str:
        return f"claude-cli/{self.model}"

    def complete(self, system: str, user: str,
                 cwd: Optional[str] = None) -> Reply:
        argv = [
            self.binary, "-p", user,
            "--model", self.model,
            "--output-format", "json",
            # Fresh id per call: workers must not share a session.
            "--session-id", str(uuid.uuid4()),
        ]
        if system:
            argv += ["--append-system-prompt", system]
        if self.allowed_tools:
            argv += ["--allowed-tools", *self.allowed_tools]
        try:
            p = subprocess.run(argv, capture_output=True, text=True,
                               timeout=self.timeout_s, cwd=cwd)
        except subprocess.TimeoutExpired as exc:
            raise ModelError(f"claude -p exceeded {self.timeout_s}s") from exc
        if not p.stdout.strip():
            raise ModelError(f"claude -p produced no output: {p.stderr[:400]}")
        try:
            data = json.loads(p.stdout)
        except json.JSONDecodeError as exc:
            raise ModelError(
                f"claude -p output was not JSON: {p.stdout[:400]}") from exc
        if data.get("is_error"):
            raise ModelError(
                f"claude -p failed: {str(data.get('result'))[:400]}")
        return Reply(
            text=str(data.get("result", "")),
            cost_usd=float(data.get("total_cost_usd") or 0.0),
            turns=int(data.get("num_turns") or 0),
            model=self.model, raw=data,
        )


@dataclass
class GenericCliModel(Model):
    """Any one-shot CLI: `codex exec`, `gemini -p`, and whatever is next.

    `argv` is a template; the literal token `{prompt}` is replaced by the
    full prompt. Most such CLIs have no separate system-prompt channel,
    so the system text is prepended — which is lossy, and is why the
    reply records the family that produced it.

    Tool capability is declared by the CALLER, because only the caller
    knows how that CLI was configured. It defaults to False: guessing
    "yes" would let a text-only agent be handed the check rung, which is
    precisely the failure this gate exists to prevent.
    """

    name: str
    argv: Sequence[str]
    timeout_s: int = 1800
    tool_capable: bool = False

    @property
    def family(self) -> str:
        return f"cli/{self.name}"

    def complete(self, system: str, user: str,
                 cwd: Optional[str] = None) -> Reply:
        prompt = f"{system}\n\n{user}" if system else user
        argv = [prompt if a == "{prompt}" else a for a in self.argv]
        try:
            p = subprocess.run(argv, capture_output=True, text=True,
                               timeout=self.timeout_s, cwd=cwd)
        except subprocess.TimeoutExpired as exc:
            raise ModelError(f"{self.name} exceeded {self.timeout_s}s") from exc
        if p.returncode != 0 and not p.stdout.strip():
            raise ModelError(f"{self.name} failed: {p.stderr[:400]}")
        return Reply(text=p.stdout, model=self.name)


@dataclass
class AnthropicApiModel(Model):
    """The Messages API, official SDK. Text only — see the module note on
    why that bars it from the check rung."""

    model: str = DEFAULT_CLAUDE_MODEL
    max_tokens: int = 16000
    tool_capable: bool = False

    def __post_init__(self) -> None:
        import anthropic                       # optional dependency
        self._client = anthropic.Anthropic()

    @property
    def family(self) -> str:
        return f"anthropic-api/{self.model}"

    def complete(self, system: str, user: str,
                 cwd: Optional[str] = None) -> Reply:
        # Streaming: an audit of a dense obligation is a long output, and
        # a non-streaming call at this max_tokens risks an HTTP timeout
        # rather than an answer.
        with self._client.messages.stream(
            model=self.model, max_tokens=self.max_tokens, system=system,
            thinking={"type": "adaptive"},
            messages=[{"role": "user", "content": user}],
        ) as stream:
            message = stream.get_final_message()
        if message.stop_reason == "refusal":
            raise ModelError(
                "auditor declined: "
                f"{getattr(message.stop_details, 'category', None)}")
        return Reply(
            text="".join(b.text for b in message.content if b.type == "text"),
            model=self.model,
        )


# ---------------------------------------------------------------------------
# Spec strings, so the auditor family is a command-line argument
# ---------------------------------------------------------------------------

def resolve(spec: str) -> Model:
    """Build a model from a spec string.

        claude-cli                 `claude -p` at the default model
        claude-cli:claude-opus-5   `claude -p`, model pinned
        api:claude-opus-5          the Messages API (coherence rung only)
        cli:<name>:<argv...>       any one-shot CLI; `{prompt}` is the slot

    e.g. `cli:codex:codex:exec:{prompt}` or `cli:gemini:gemini:-p:{prompt}`.
    """
    head, _, rest = spec.partition(":")
    if head == "claude-cli":
        return ClaudeCliModel(model=rest or DEFAULT_CLAUDE_MODEL)
    if head == "api":
        return AnthropicApiModel(model=rest or DEFAULT_CLAUDE_MODEL)
    if head == "cli":
        name, _, argv = rest.partition(":")
        if not name or not argv:
            raise ModelError(
                f"cli spec needs a name and argv: {spec!r} "
                "(e.g. cli:codex:codex:exec:{prompt})")
        return GenericCliModel(name=name, argv=argv.split(":"))
    raise ModelError(
        f"unknown model spec {spec!r}; expected claude-cli[:model], "
        "api[:model], or cli:<name>:<argv...>")


def require_tools(model: Model, rung: str) -> None:
    """Refuse to hand a tool-less model a rung that needs to RUN things.

    Asked to run an ensemble it cannot run, a text-only model does not
    fail — it describes a plausible run that never happened, and that
    description is indistinguishable from a real one in the report. This
    is the same rule as `Verdict.informative`, one layer up: something
    that could not run has not voted.
    """
    if rung == "check" and not model.tool_capable:
        raise ModelError(
            f"{model.family} has no tools, so it cannot run the check "
            "rung — it could only describe a checker run it never "
            "performed. Use a tool-capable adapter (claude-cli), or run "
            "the check rung mechanically and pass its result in.")
