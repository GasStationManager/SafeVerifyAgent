"""Driver: planner + parallel workers, over any model adapter.

    python3 drivers/audit.py Claimed.lean --model claude-cli
    python3 drivers/audit.py Claimed.lean --model cli:codex:codex:exec:{prompt}

The fan-out is the design: every obligation is dispatched, so coverage is
a property of the harness rather than of what happened to be scheduled
first. See DESIGN.md §6.

Prompts are rendered through `safeverifyagent.prompts` — the same
renderer the Claude Code driver uses. Do not paraphrase one into this
file; `tests/test_prompts.py` enforces it.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import sys
from typing import List, Optional, Sequence

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from safeverifyagent import checkers, models, prompts        # noqa: E402
from safeverifyagent.aggregate import LADDER, aggregate, gated_out  # noqa: E402
from safeverifyagent.extract import extract                  # noqa: E402
from safeverifyagent.verdict import (                        # noqa: E402
    BARE, CLEAN, INFORMAL, PAIRED, STATED, UNDETERMINED, WHOLE_CLAIM,
    ClaimVerdict, Finding, Obligation,
)

MAX_PARALLEL_WORKERS = 6

SYSTEM = {
    "planner": "You are the planner stage of a proof auditor.",
    "check": "You are the check rung of a proof auditor.",
    "coherence": "You are the coherence rung of a proof auditor.",
}


def plan(model: models.Model, artifact: str, intake: str,
         extracted: Sequence[Obligation]) -> List[Obligation]:
    """Stage 1. The planner READS the decomposition; it does not invent
    one (see prompts/planner.md)."""
    reply = model.complete(
        SYSTEM["planner"],
        prompts.render("planner", artifact_path=artifact, intake=intake,
                       extracted=json.dumps([ob.__dict__ for ob in extracted],
                                            indent=1)),
        cwd=os.path.dirname(os.path.abspath(artifact)),
    )
    return _parse_plan(reply.text, fallback=extracted)


def audit_obligation(model: models.Model, ob: Obligation, artifact: str,
                     intake: str) -> List[Finding]:
    """Stage 2 for ONE obligation: check rung, then coherence rung.

    The gate is per obligation and nothing else — a refutation on some
    other obligation never stops this one being audited, which is what
    keeps the fan-out complete.
    """
    out: List[Finding] = []
    cwd = os.path.dirname(os.path.abspath(artifact))
    common = dict(obligation_id=ob.id, statement=ob.statement,
                  context=", ".join(ob.depends_on) or "(none)",
                  artifact_path=os.path.abspath(artifact))

    check = None
    if model.tool_capable:
        reply = model.complete(SYSTEM["check"], prompts.render(
            "check", checkers_available=json.dumps(checkers.available()),
            **common), cwd=cwd)
        check = _parse_finding(reply.text, ob.id, "check", intake)
        out.append(check)
        if gated_out(out, ob.id, "coherence"):
            return out

    reply = model.complete(SYSTEM["coherence"], prompts.render(
        "coherence",
        check_summary=(check.ensemble or check.note if check
                       else "(not run: auditor has no tools)"),
        **common), cwd=cwd)
    out.append(_parse_finding(reply.text, ob.id, "coherence", intake))
    return out


def run(artifact: str, intake: str = BARE,
        model: Optional[models.Model] = None) -> ClaimVerdict:
    model = model or models.ClaudeCliModel()
    result = extract(artifact)
    if result.degraded:
        # An obligation nobody extracted is an obligation nobody audits,
        # and a short list looks exactly like an easy file.
        print(f"!! DEGRADED EXTRACTION: {result.note}", file=sys.stderr)

    obligations = plan(model, artifact, intake, list(result))
    live = [ob for ob in obligations if ob.used or ob.is_whole_claim]
    print(f"auditing {len(live)} obligation(s) with {model.family}",
          file=sys.stderr)

    findings: List[Finding] = []
    with concurrent.futures.ThreadPoolExecutor(MAX_PARALLEL_WORKERS) as pool:
        futures = {pool.submit(audit_obligation, model, ob, artifact, intake): ob
                   for ob in live}
        for fut in concurrent.futures.as_completed(futures):
            ob = futures[fut]
            try:
                findings.extend(fut.result())
            except Exception as exc:
                # A worker that died did not vote. Recording it as
                # `undetermined` keeps it out of both verdicts and into
                # the residue, where an unaudited obligation belongs.
                findings.append(Finding(
                    ob.id, "check" if model.tool_capable else "coherence",
                    UNDETERMINED, INFORMAL,
                    note=f"worker failed: {exc}"[:500], intake=intake))
                print(f"   worker on {ob.id} failed: {exc}", file=sys.stderr)

    return aggregate(live, findings, intake=intake,
                     checkers_available=checkers.available(),
                     auditor_family=model.family)


# --------------------------------------------------------------------------
# Parsing what the agents returned
# --------------------------------------------------------------------------

def _json_block(text: str):
    """The report block an agent ends its reply with.

    Prefer the LAST fenced ```json block: an auditor reasons in prose
    first (which is the point — a verdict with no reconstruction behind
    it is worth nothing), and that prose routinely contains braces, set
    literals and Lean terms. Taking the outermost `{...}` span swallows
    all of it and parses nothing. Falls back to the widest brace span
    only when there is no fence at all.
    """
    fences = re.findall(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL)
    for candidate in reversed(fences):
        try:
            return json.loads(candidate)
        except json.JSONDecodeError:
            continue
    start, end = text.find("{"), text.rfind("}")
    if start < 0 or end <= start:
        return None
    try:
        return json.loads(text[start:end + 1])
    except json.JSONDecodeError:
        return None


def _parse_plan(text: str, fallback: Sequence[Obligation]) -> List[Obligation]:
    data = _json_block(text)
    if not data or "obligations" not in data:
        # The extractor is the ground truth for what EXISTS, so falling
        # back to it loses the planner's dependency analysis but never
        # loses an obligation.
        return list(fallback)
    out = [Obligation(
        id=str(o["id"]), statement=str(o.get("statement", "")),
        kind=str(o.get("kind", "have")),
        depends_on=[str(d) for d in o.get("depends_on", [])],
        used=bool(o.get("used", True)),
        anomalies=[str(a) for a in o.get("anomalies", [])],
    ) for o in data["obligations"] if o.get("id")]
    if not any(ob.is_whole_claim for ob in out):
        out.append(Obligation(WHOLE_CLAIM, "the claim as a whole",
                              kind="final"))
    return out


def _parse_finding(text: str, obligation: str, rung: str,
                   intake: str) -> Finding:
    data = _json_block(text) or {}
    outcome = str(data.get("outcome", UNDETERMINED)).lower()
    evidence = str(data.get("evidence", INFORMAL)).lower()
    if rung == "coherence" and evidence == "formal":
        # The prompt forbids it and the type would raise. Downgrade and
        # say so, rather than losing a whole run to one bad field.
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
        disagreement=bool(data.get("disagreement", False)), intake=intake,
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("artifact")
    ap.add_argument("--intake", choices=(BARE, PAIRED), default=BARE)
    ap.add_argument("--model", default="claude-cli",
                    help="claude-cli[:model] | api[:model] | cli:<name>:<argv>")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()

    model = models.resolve(a.model)
    for rung in LADDER:
        if rung == "check" and not model.tool_capable:
            print(f"note: {model.family} has no tools; the check rung will "
                  "be SKIPPED and listed in the residue rather than "
                  "described by a model that could not run it.",
                  file=sys.stderr)
    v = run(a.artifact, intake=a.intake, model=model)
    if a.json:
        print(json.dumps(v.to_dict(), indent=1))
    else:
        print(v.headline())
        for f in v.findings:
            print(f"  [{f.rung}] {f.obligation}: {f.outcome} "
                  f"({f.evidence}) — {f.note[:120]}")
        for r in v.residue:
            print(f"  residue: {r}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
