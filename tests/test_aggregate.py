"""The conjunction, the residue, and the distinctions that must survive it."""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from safeverifyagent.aggregate import aggregate, gated_out   # noqa: E402
from safeverifyagent.verdict import (                        # noqa: E402
    ACCEPT, BARE, CLEAN, ESCALATE, INFORMAL, PAIRED, REFUTE, REFUTED, REJECT,
    STATED, UNDETERMINED, WHOLE_CLAIM, Finding, Obligation,
)


def obs(*ids):
    return [Obligation(i, f"statement of {i}") for i in ids]


def clean(ob, rung="check"):
    return Finding(ob, rung, CLEAN, STATED, tier="quick")


class TestVerdicts(unittest.TestCase):
    def test_a_refuted_obligation_refutes_the_claim(self):
        v = aggregate(obs("h1", WHOLE_CLAIM),
                      [Finding("h1", "coherence", REFUTED, INFORMAL)])
        self.assertEqual(v.verdict, REFUTE)
        self.assertEqual(v.refuted, ["h1"])

    def test_malformed_input_is_reject_and_never_a_refutation(self):
        """'You did not submit a proof' and 'you submitted a proof and it
        is wrong' are different findings; collapsing them lets a broken
        file be reported as a caught exploit."""
        v = aggregate(obs("h1"), [], manifest_ok=False,
                      manifest_note="undeclared sorry at h1")
        self.assertEqual(v.verdict, REJECT)
        self.assertEqual(v.refuted, [])

    def test_disagreement_escalates_rather_than_refuting(self):
        f = Finding("h1", "check", UNDETERMINED, INFORMAL,
                    disagreement=True, ensemble="lean=accept, lean4lean=reject")
        v = aggregate(obs("h1"), [f])
        self.assertEqual(v.verdict, ESCALATE)
        self.assertEqual(v.refuted, [])
        self.assertTrue(any("checker-bug candidate" in e
                            for e in v.escalations))

    def test_a_clean_sweep_accepts(self):
        o = obs("h1", WHOLE_CLAIM)
        fs = [clean(x.id, r) for x in o for r in ("check", "coherence")]
        v = aggregate(o, fs, intake=PAIRED)
        self.assertEqual(v.verdict, ACCEPT)


class TestResidue(unittest.TestCase):
    def test_a_bare_claim_always_carries_the_statement_gap(self):
        o = obs("h1", WHOLE_CLAIM)
        fs = [clean(x.id, r) for x in o for r in ("check", "coherence")]
        v = aggregate(o, fs, intake=BARE)
        self.assertEqual(v.verdict, ACCEPT)
        self.assertTrue(any("BARE claim" in r for r in v.residue))

    def test_a_non_formal_accept_is_listed_as_revocable(self):
        v = aggregate(obs("h1"), [clean("h1")], intake=PAIRED)
        self.assertTrue(any("revocable" in r for r in v.residue))

    def test_an_unavailable_tier_is_named(self):
        v = aggregate(obs("h1"), [clean("h1")],
                      checkers_available={"comparator": False, "lean": True})
        self.assertTrue(any("comparator" in r for r in v.residue))
        self.assertFalse(any(r.endswith("lean") for r in v.residue))

    def test_undetermined_is_not_clean(self):
        """The distinction the whole coherence rung turns on: a rung that
        reached no reading did not audit the obligation."""
        f = Finding("h1", "coherence", UNDETERMINED, INFORMAL,
                    note="statement opaque")
        v = aggregate(obs("h1"), [f])
        self.assertTrue(any("unaudited, not clean" in r for r in v.residue))

    def test_a_rung_that_never_ran_is_residue_not_silence(self):
        v = aggregate(obs("h1"), [clean("h1", "check")])
        self.assertTrue(any("coherence rung never ran" in r
                            for r in v.residue))


class TestLadderGate(unittest.TestCase):
    def test_a_refuted_check_gates_that_obligations_coherence_rung(self):
        fs = [Finding("h1", "check", REFUTED, "formal", tier="high")]
        self.assertTrue(gated_out(fs, "h1", "coherence"))

    def test_a_refutation_elsewhere_gates_nothing(self):
        """The saving is WITHIN an obligation. If a refutation on h1
        could gate h2, the fan-out would stop being complete and coverage
        would go back to being a fact about scheduling."""
        fs = [Finding("h1", "check", REFUTED, "formal", tier="high")]
        self.assertFalse(gated_out(fs, "h2", "coherence"))

    def test_a_gated_rung_is_not_counted_as_missing_coverage(self):
        o = obs("h1", "h2")
        fs = [Finding("h1", "check", REFUTED, "formal", tier="high"),
              clean("h2", "check"), clean("h2", "coherence")]
        v = aggregate(o, fs)
        # h1's coherence rung was gated by its own check, so the
        # coherence denominator is 1, not 2.
        self.assertEqual(v.coverage["coherence"], [1, 1])
        self.assertEqual(v.coverage["check"], [2, 2])

    def test_a_dispatched_rung_that_never_reported_shortens_the_numerator(self):
        o = obs("h1", "h2")
        v = aggregate(o, [clean("h1", "check"), clean("h1", "coherence"),
                          clean("h2", "check")])
        self.assertEqual(v.coverage["coherence"], [1, 2])


if __name__ == "__main__":
    unittest.main()
