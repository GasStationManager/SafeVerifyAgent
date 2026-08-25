"""The evidence ceiling, enforced in code rather than asked for in prose.

A rule an agent is merely instructed to follow holds until the agent is
having a bad day. These are the combinations the design forbids.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from safeverifyagent.verdict import (                        # noqa: E402
    BARE, CLEAN, FORMAL, PAIRED, REFUTED, STATED, WHOLE_CLAIM, AuditError,
    Finding,
)


class TestEvidenceCeiling(unittest.TestCase):
    def test_a_cheap_tier_cannot_close_formally(self):
        """`formal` is permanent, and this whole audit exists because the
        checkers may be wrong: a bug disclosed next month has to be able
        to reopen the accept it produced."""
        with self.assertRaises(AuditError):
            Finding("h1", "check", CLEAN, FORMAL, tier="quick")

    def test_the_high_tier_may(self):
        f = Finding("h1", "check", CLEAN, FORMAL, tier="high")
        self.assertEqual(f.evidence, FORMAL)

    def test_a_bare_claims_whole_obligation_never_closes_formally(self):
        """With no independently authored statement, 'proves the intended
        theorem' is not a checkable proposition — certifying it asserts
        more than the input contains."""
        with self.assertRaises(AuditError):
            Finding(WHOLE_CLAIM, "check", CLEAN, FORMAL,
                    tier="high", intake=BARE)

    def test_a_paired_claims_whole_obligation_may(self):
        f = Finding(WHOLE_CLAIM, "check", CLEAN, FORMAL,
                    tier="high", intake=PAIRED)
        self.assertEqual(f.evidence, FORMAL)

    def test_a_step_of_a_bare_claim_may_still_close_formally(self):
        """The kernel really did accept that step; it is the CLAIM node
        the bare shape cannot certify."""
        f = Finding("h1", "check", CLEAN, FORMAL, tier="high", intake=BARE)
        self.assertEqual(f.evidence, FORMAL)

    def test_a_refutation_may_be_formal_from_any_tier(self):
        """A re-executed witness is a fact about the statement, not a
        report from a checker that might be wrong."""
        f = Finding("h1", "check", REFUTED, FORMAL, tier="quick")
        self.assertEqual(f.outcome, REFUTED)

    def test_coherence_is_never_formal_in_either_direction(self):
        for outcome in (CLEAN, REFUTED):
            with self.assertRaises(AuditError):
                Finding("h1", "coherence", outcome, FORMAL, tier="high")

    def test_bad_enum_values_are_refused(self):
        with self.assertRaises(AuditError):
            Finding("h1", "check", "probably-fine", STATED)
        with self.assertRaises(AuditError):
            Finding("h1", "check", CLEAN, "vibes")


if __name__ == "__main__":
    unittest.main()
