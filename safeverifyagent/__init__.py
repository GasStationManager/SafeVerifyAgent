"""SafeVerifyAgent — audit a claimed Lean 4 proof.

The stance is a referee's rather than an author's: this package never
proves anything. A claimed proof is a conjunction, so it is unsound if
SOME obligation is unsound, and the job is to find one or run out of ways
to look.

See DESIGN.md. The short version:

    intake -> planner -> one worker per obligation (check, then
    coherence) -> aggregate

Public surface:

    checkers   the mechanical ensemble, and what it may not conclude
    verdict    Obligation / Finding / ClaimVerdict, evidence ceiling enforced
    aggregate  the conjunction, and the residue an ACCEPT does not cover
    prompts    one renderer, shared by every driver
"""

from . import aggregate, checkers, prompts, verdict          # noqa: F401
from .aggregate import aggregate as aggregate_findings       # noqa: F401
from .verdict import (                                       # noqa: F401
    ACCEPT, BARE, CLEAN, ESCALATE, PAIRED, REFUTE, REFUTED, REJECT,
    UNDETERMINED, WHOLE_CLAIM, AuditError, ClaimVerdict, Finding, Obligation,
)

__version__ = "0.1.0"
