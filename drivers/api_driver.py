"""Reference driver: planner + parallel workers on the Messages API.

Status: SKELETON. The plumbing is real and the prompts are the shipped
ones, but this has not been run end-to-end against a claimed proof — see
DESIGN.md §10 before quoting anything it produces.

Why a driver at all, when `drivers/claude_code/` can do the same work
with no API code: this one is reproducible and scriptable, which is what
a benchmark run needs. The Claude Code path is for auditing something
today.

Both drivers render their prompts through `safeverifyagent.prompts`. Do
not paraphrase a prompt into this file — see `prompts.py` for why, and
`tests/test_prompts.py` for the test that enforces it.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import sys
from typing import Any, List, Optional, Sequence

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from safeverifyagent import checkers, prompts                # noqa: E402
from safeverifyagent.aggregate import aggregate, gated_out   # noqa: E402
from safeverifyagent.verdict import (                        # noqa: E402
    BARE, CLEAN, INFORMAL, PAIRED, STATED, UNDETERMINED, WHOLE_CLAIM,
    ClaimVerdict, Finding, Obligation,
)

# The default auditor. The family is a PARAMETER rather than a constant
# because same-family authorship is a known confound: an auditor reading
# an artifact produced by its own family is not an independent test
# (DESIGN.md §7). Cross-family runs are a configuration, not a fork.
DEFAULT_MODEL = "claude-opus-5"
MAX_PARALLEL_WORKERS = 8


class Model:
    """The seam a second model family plugs into.

    Deliberately tiny: one call, text in and text out. Anything richer
    would start encoding one provider's request shape into the harness,
    which is the thing that makes cross-family runs a fork instead of a
    flag.
    """

    def complete(self, system: str, user: str) -> str:  # pragma: no cover
        raise NotImplementedError


class AnthropicModel(Model):
    """Reference implementation, on the official SDK."""

    def __init__(self, model: str = DEFAULT_MODEL, max_tokens: int = 16000):
        import anthropic                       # imported lazily: optional dep
        self.client = anthropic.Anthropic()
        self.model = model
        self.max_tokens = max_tokens

    @property
    def family(self) -> str:
        return "anthropic/" + self.model

    def complete(self, system: str, user: str) -> str:
        # Streaming because an audit of a dense obligation is a long
        # output, and a non-streaming call at this max_tokens risks an
        # HTTP timeout rather than an answer.
        with self.client.messages.stream(
            model=self.model,
            max_tokens=self.max_tokens,
            system=system,
            thinking={"type": "adaptive"},
            messages=[{"role": "user", "content": user}],
        ) as stream:
            message = stream.get_final_message()
        if message.stop_reason == "refusal":
            raise RuntimeError(
                f"auditor declined: {getattr(message.stop_details, 'category', None)}")
        return "".join(b.text for b in message.content if b.type == "text")


# --------------------------------------------------------------------------
# Stages
# --------------------------------------------------------------------------

def plan(model: Model, artifact_path: str, intake: str,
         extracted: Sequence[Obligation]) -> List[Obligation]:
    """Stage 1. The planner reads; it does not invent (see planner.md)."""
    text = model.complete(
        system="You are the planner stage of a proof auditor.",
        user=prompts.render(
            "planner", artifact_path=artifact_path, intake=intake,
            extracted=json.dumps([ob.__dict__ for ob in extracted], indent=1)),
    )
    return _parse_plan(text, fallback=extracted)


def audit_obligation(model: Model, ob: Obligation, artifact_path: str,
                     intake: str, found: Sequence[Finding]) -> List[Finding]:
    """Stage 2 for one obligation: check rung, then coherence rung.

    The gate is per obligation and nothing else: a refutation on some
    OTHER obligation never stops this one from being audited. That is
    what keeps the fan-out complete, and complete coverage is the whole
    reason this design fans out rather than searching.
    """
    out: List[Finding] = []
    avail = checkers.available()

    check_text = model.complete(
        system="You are the check rung of a proof auditor.",
        user=prompts.render(
            "check", obligation_id=ob.id, statement=ob.statement,
            context=", ".join(ob.depends_on) or "(none)",
            artifact_path=artifact_path,
            checkers_available=json.dumps(avail)),
    )
    check = _parse_finding(check_text, ob.id, "check", intake)
    out.append(check)

    if gated_out(out, ob.id, "coherence"):
        return out

    coh_text = model.complete(
        system="You are the coherence rung of a proof auditor.",
        user=prompts.render(
            "coherence", obligation_id=ob.id, statement=ob.statement,
            context=", ".join(ob.depends_on) or "(none)",
            artifact_path=artifact_path,
            check_summary=check.ensemble or check.note or "(not run)"),
    )
    out.append(_parse_finding(coh_text, ob.id, "coherence", intake))
    return out


def run(artifact_path: str, extracted: Sequence[Obligation],
        intake: str = BARE, model: Optional[Model] = None,
        toolchain: Optional[str] = None) -> ClaimVerdict:
    """The whole pipeline. Fan-out is the point: every obligation is
    dispatched, so coverage is a property of the design rather than of
    what happened to get scheduled first."""
    model = model or AnthropicModel()
    obligations = plan(model, artifact_path, intake, extracted)
    live = [ob for ob in obligations if ob.used or ob.is_whole_claim]

    findings: List[Finding] = []
    with concurrent.futures.ThreadPoolExecutor(MAX_PARALLEL_WORKERS) as pool:
        futures = {
            pool.submit(audit_obligation, model, ob, artifact_path, intake, []): ob
            for ob in live
        }
        for fut in concurrent.futures.as_completed(futures):
            ob = futures[fut]
            try:
                findings.extend(fut.result())
            except Exception as exc:          # a worker that died did not vote
                findings.append(Finding(
                    ob.id, "check", UNDETERMINED, INFORMAL,
                    note=f"worker failed: {exc}", intake=intake))

    return aggregate(
        live, findings, intake=intake,
        checkers_available=checkers.available(), toolchain=toolchain,
        auditor_family=getattr(model, "family", None),
    )


# --------------------------------------------------------------------------
# Parsing the agents' answers
# --------------------------------------------------------------------------

def _json_block(text: str) -> Optional[Any]:
    start = text.find("{")
    end = text.rfind("}")
    if start < 0 or end <= start:
        return None
    try:
        return json.loads(text[start:end + 1])
    except json.JSONDecodeError:
        return None


def _parse_plan(text: str, fallback: Sequence[Obligation]) -> List[Obligation]:
    data = _json_block(text)
    if not data or "obligations" not in data:
        # The extractor's reading is the ground truth for what EXISTS, so
        # falling back to it loses the planner's dependency analysis but
        # never loses an obligation.
        return list(fallback)
    out = [Obligation(
        id=str(o["id"]), statement=str(o.get("statement", "")),
        kind=str(o.get("kind", "have")),
        depends_on=[str(d) for d in o.get("depends_on", [])],
        used=bool(o.get("used", True)),
        anomalies=[str(a) for a in o.get("anomalies", [])],
    ) for o in data["obligations"]]
    if not any(ob.is_whole_claim for ob in out):
        # Always an obligation: the defect is often in a definition
        # rather than in any step.
        out.append(Obligation(WHOLE_CLAIM, "the claim as a whole",
                              kind="final"))
    return out


def _parse_finding(text: str, obligation: str, rung: str,
                   intake: str) -> Finding:
    data = _json_block(text) or {}
    outcome = str(data.get("outcome", UNDETERMINED))
    evidence = str(data.get("evidence", INFORMAL))
    if rung == "coherence" and evidence == "formal":
        # The prompt forbids it; the type would raise. Downgrade and say
        # so rather than crashing a whole run on one bad field.
        evidence = INFORMAL
        data["note"] = f"[downgraded from formal] {data.get('note', '')}"
    return Finding(
        obligation=obligation, rung=rung,
        outcome=outcome if outcome in (CLEAN, "refuted", UNDETERMINED)
        else UNDETERMINED,
        evidence=evidence if evidence in ("formal", STATED, INFORMAL)
        else INFORMAL,
        note=str(data.get("note", ""))[:2000],
        tier=data.get("tier"), ensemble=data.get("ensemble"),
        disagreement=bool(data.get("disagreement", False)),
        intake=intake,
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("artifact")
    ap.add_argument("--intake", choices=(BARE, PAIRED), default=BARE)
    ap.add_argument("--model", default=DEFAULT_MODEL)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()

    from safeverifyagent.extract import extract_obligations
    obligations = extract_obligations(a.artifact)
    v = run(a.artifact, obligations, intake=a.intake,
            model=AnthropicModel(a.model))
    print(json.dumps(v.to_dict(), indent=1) if a.json else v.headline())
    for r in v.residue:
        print(f"  residue: {r}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
