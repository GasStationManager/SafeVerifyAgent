"""Stage 3: the conjunction, and the residue.

A claimed proof is sound only if every obligation is sound, so
aggregation is an AND — which is the easy half. The half worth writing
carefully is what an ACCEPT is allowed to claim.

An ACCEPT here means *no attack in this configuration landed*: over this
ensemble, at this toolchain, under this intake shape. It does not mean
the proof is correct. The `residue` is the computed difference between
those two sentences, and it is a list rather than a sentence so that
whatever consumes the verdict cannot skim past it.
"""

from __future__ import annotations

from typing import Dict, Iterable, List, Optional, Sequence

from .verdict import (
    ACCEPT, BARE, CLEAN, ESCALATE, FORMAL, REFUTE, REFUTED, REJECT,
    UNDETERMINED, ClaimVerdict, Finding, Obligation,
)

# Rungs, cheapest first. The order is the ladder; the gate is per
# obligation (see `gated_out`), never across obligations.
LADDER = ("check", "coherence")


def gated_out(findings: Sequence[Finding], obligation: str,
              rung: str) -> bool:
    """Should `rung` be skipped for this obligation?

    Only because a CHEAPER rung on the SAME obligation already refuted
    it. An LLM audit of a lemma the ensemble has already killed is the
    spend the ladder exists to avoid — and that is the only saving the
    ladder is allowed to make. A refutation elsewhere never gates
    anything here, which is what keeps the fan-out complete.
    """
    if rung not in LADDER:
        return False
    cheaper = LADDER[:LADDER.index(rung)]
    return any(f.obligation == obligation and f.rung in cheaper
               and f.outcome == REFUTED for f in findings)


def aggregate(
    obligations: Sequence[Obligation],
    findings: Sequence[Finding],
    intake: str = BARE,
    manifest_ok: bool = True,
    manifest_note: str = "",
    checkers_available: Optional[Dict[str, bool]] = None,
    toolchain: Optional[str] = None,
    auditor_family: Optional[str] = None,
    stop_on_first_refutation: bool = False,
) -> ClaimVerdict:
    """Fold per-obligation findings into one claim-level verdict."""
    findings = list(findings)
    residue: List[str] = []
    escalations: List[str] = []

    # --- REJECT is not a refutation ---------------------------------------
    # "You did not submit a proof" and "you submitted a proof and it is
    # wrong" are different findings. Collapsing them lets a malformed
    # submission be reported as a caught exploit.
    if not manifest_ok:
        return ClaimVerdict(
            verdict=REJECT, intake=intake, findings=findings,
            residue=[manifest_note or "manifest violation: undeclared hole"],
            checkers_available=dict(checkers_available or {}),
            toolchain=toolchain, auditor_family=auditor_family,
            stop_on_first_refutation=stop_on_first_refutation,
            coverage=coverage_of(obligations, findings),
        )

    refuted = sorted({f.obligation for f in findings if f.outcome == REFUTED})

    # --- what an ACCEPT would not cover -----------------------------------
    for f in findings:
        if f.disagreement:
            escalations.append(
                f"{f.obligation}: checkers disagree ({f.ensemble or f.note}) "
                "— establishes nothing, and is a checker-bug candidate")
        if f.outcome == UNDETERMINED:
            escalations.append(
                f"{f.obligation}/{f.rung}: undetermined — {f.note or 'no reading reached'}")
            residue.append(
                f"{f.obligation}: the {f.rung} rung reached no reading; "
                "this obligation is unaudited, not clean")
        elif f.outcome == CLEAN and f.evidence != FORMAL:
            residue.append(
                f"{f.obligation}/{f.rung}: clean on {f.evidence} evidence "
                "— revocable, and dependent on unaudited checker trust")

    seen = {(f.obligation, f.rung) for f in findings}
    for ob in obligations:
        for rung in LADDER:
            if (ob.id, rung) in seen or gated_out(findings, ob.id, rung):
                continue
            residue.append(f"{ob.id}: the {rung} rung never ran")
    for name, ok in sorted((checkers_available or {}).items()):
        if not ok:
            residue.append(f"tier unavailable in this run: {name}")
    if intake == BARE:
        residue.append(
            "BARE claim: no independently authored statement, so no tier "
            "established that this proves the intended theorem")

    # --- the verdict -------------------------------------------------------
    if refuted:
        verdict = REFUTE
    elif escalations:
        verdict = ESCALATE
    else:
        verdict = ACCEPT

    return ClaimVerdict(
        verdict=verdict, intake=intake, findings=findings,
        residue=residue, refuted=refuted, escalations=escalations,
        coverage=coverage_of(obligations, findings),
        checkers_available=dict(checkers_available or {}),
        toolchain=toolchain, auditor_family=auditor_family,
        stop_on_first_refutation=stop_on_first_refutation,
    )


def coverage_of(obligations: Sequence[Obligation],
                findings: Iterable[Finding]) -> Dict[str, List[int]]:
    """Per rung, `[audited, expected]`.

    `expected` excludes obligations the ladder legitimately gated out, so
    a short denominator means work that was *dispatched and did not come
    back* rather than work the design chose not to do. Reporting one
    number for both would hide the difference between a saving and a gap.
    """
    findings = list(findings)
    out: Dict[str, List[int]] = {}
    for rung in LADDER:
        audited = sum(1 for f in findings if f.rung == rung)
        expected = sum(1 for ob in obligations
                       if not gated_out(findings, ob.id, rung))
        out[rung] = [audited, expected]
    return out
