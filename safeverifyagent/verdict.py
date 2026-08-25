"""Verdict types: what an audit says, and what it may not say.

The evidence ceiling lives here rather than in a prompt, because a rule
an agent is merely *asked* to follow is a rule that holds until the agent
is having a bad day. `Finding.__post_init__` refuses the combinations the
design forbids.
"""

from __future__ import annotations

from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional

# --- evidence levels -------------------------------------------------------
# `FORMAL` is permanent: an accept filed at this level is not meant to be
# revisited. That is exactly why nothing cheap may reach it — the premise
# of the whole exercise is that a checker may be wrong, and a checker bug
# disclosed next month has to be able to reopen the accept it produced.
FORMAL = "formal"
STATED = "stated"
INFORMAL = "informal"
EVIDENCE = (FORMAL, STATED, INFORMAL)

# The only tier permitted to file a `formal` ACCEPT.
FORMAL_TIER = "high"

# --- per-obligation outcomes ----------------------------------------------
CLEAN = "clean"                  # the attack came back empty
REFUTED = "refuted"              # the attack landed
UNDETERMINED = "undetermined"    # could not reach a reading — NOT clean
OUTCOMES = (CLEAN, REFUTED, UNDETERMINED)

# --- claim-level verdicts --------------------------------------------------
ACCEPT = "ACCEPT"
REFUTE = "REFUTE"
REJECT = "REJECT"        # malformed input — never a refutation
ESCALATE = "ESCALATE"
VERDICTS = (ACCEPT, REFUTE, REJECT, ESCALATE)

# --- intake shapes ---------------------------------------------------------
BARE = "bare"
PAIRED = "paired"

# The obligation covering the claim as a whole. Always present, because
# the defect is often in a definition rather than in any step.
WHOLE_CLAIM = "claim"


class AuditError(RuntimeError):
    pass


@dataclass
class Obligation:
    """One unit of the flat decomposition."""

    id: str
    statement: str
    kind: str = "have"                        # have | lemma | theorem | final
    depends_on: List[str] = field(default_factory=list)
    used: bool = True                         # does anything downstream need it?
    anomalies: List[str] = field(default_factory=list)   # measured, never read

    @property
    def is_whole_claim(self) -> bool:
        return self.id == WHOLE_CLAIM


@dataclass
class Finding:
    """One rung's result on one obligation."""

    obligation: str
    rung: str                                 # "check" | "coherence"
    outcome: str
    evidence: str
    note: str = ""
    tier: Optional[str] = None
    ensemble: Optional[str] = None            # EnsembleResult.summary()
    disagreement: bool = False
    intake: str = BARE

    def __post_init__(self) -> None:
        if self.outcome not in OUTCOMES:
            raise AuditError(f"outcome must be one of {OUTCOMES}")
        if self.evidence not in EVIDENCE:
            raise AuditError(f"evidence must be one of {EVIDENCE}")
        if self.outcome == CLEAN and self.evidence == FORMAL:
            # A clean run is only ever as good as the checker that ran it.
            if self.tier != FORMAL_TIER:
                raise AuditError(
                    f"a clean result cannot be filed formal from tier "
                    f"{self.tier!r}: `formal` is permanent, and an accept "
                    f"from below the {FORMAL_TIER!r} tier has to stay "
                    "revocable. File it 'stated'.")
            if self.intake == BARE and self.obligation == WHOLE_CLAIM:
                # With no independently authored statement, "proves the
                # intended theorem" is not a checkable proposition —
                # certifying it asserts more than the input contains.
                raise AuditError(
                    "this claim is BARE, so the whole-claim obligation "
                    "cannot be closed formally at any tier. Close it "
                    "'stated' and let the residue say why, or supply a "
                    "challenge.")
        if self.rung == "coherence" and self.evidence == FORMAL:
            # A reader who could not reconstruct an argument has not
            # executed a witness. Judgment prunes; it does not certify.
            raise AuditError(
                "a coherence finding is a judgment, not a certificate: "
                "never file it formal, in either direction.")


@dataclass
class ClaimVerdict:
    """The audit's output. `residue` is not decoration — see `aggregate`."""

    verdict: str
    intake: str
    findings: List[Finding] = field(default_factory=list)
    residue: List[str] = field(default_factory=list)
    refuted: List[str] = field(default_factory=list)
    escalations: List[str] = field(default_factory=list)
    coverage: Dict[str, List[int]] = field(default_factory=dict)
    checkers_available: Dict[str, bool] = field(default_factory=dict)
    stop_on_first_refutation: bool = False
    toolchain: Optional[str] = None
    auditor_family: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    def headline(self) -> str:
        s = f"{self.verdict} ({self.intake} claim)"
        if self.refuted:
            s += f" — refuted: {', '.join(self.refuted)}"
        if self.residue:
            s += f" — {len(self.residue)} item(s) of residue"
        return s
