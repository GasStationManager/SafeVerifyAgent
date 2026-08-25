"""The ensemble's parsing rules, and what it may not conclude.

Every test here runs without a Lean toolchain, on recorded output. That
is deliberate: the rule these adapters exist to enforce is *parse the
tool's output, never its exit code*, and a rule about parsing is exactly
the kind you can pin with fixtures.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from safeverifyagent import checkers as C                    # noqa: E402


class TestExitCodesAreNotVerdicts(unittest.TestCase):
    def test_lean4lean_exits_zero_while_reporting_a_problem(self):
        """The bug that would invert a verdict: lean4lean exits 0 and
        prints 'found a problem'. An adapter reading the exit code
        records a caught unsoundness as a clean pass."""
        v = C.Lean4Lean(binary="x").read_output(
            "lean4lean found a problem in Collatz.Limit", returncode=0)
        self.assertEqual(v.outcome, C.REJECT)

    def test_lean4lean_clean_run_is_an_accept(self):
        v = C.Lean4Lean(binary="x").read_output(
            "checked 2 declarations", returncode=0)
        self.assertEqual(v.outcome, C.ACCEPT)

    def test_lean4lean_unrecognised_output_is_error_not_a_verdict(self):
        v = C.Lean4Lean(binary="x").read_output("", returncode=1)
        self.assertEqual(v.outcome, C.ERROR)
        self.assertFalse(v.informative)

    def test_comparator_build_failure_is_error_not_reject(self):
        """The mirror-image bug: comparator exits non-zero when it merely
        fails to BUILD. Mapping that onto `reject` reports 'everything is
        broken' as 'everything is refuted'."""
        vs = C.Comparator("b", "e").read_output(
            "error: no configuration file found", returncode=1)
        self.assertEqual([v.outcome for v in vs], [C.ERROR])
        self.assertFalse(vs[0].informative)

    def test_comparator_accept_needs_both_the_mark_and_a_zero_exit(self):
        ok = C.Comparator("b", "e").read_output(
            "your solution is okay", returncode=0)
        self.assertEqual(ok[0].outcome, C.ACCEPT)
        # Same words, non-zero exit: not an accept.
        bad = C.Comparator("b", "e").read_output(
            "your solution is okay", returncode=2)
        self.assertEqual(bad[0].outcome, C.REJECT)

    def test_comparator_reports_one_verdict_per_member(self):
        vs = C.Comparator("b", "e").read_output(
            "nanoda rejected the export", returncode=1, externals=["nanoda"])
        self.assertEqual([v.checker for v in vs],
                         ["comparator/kernel", "comparator/nanoda"])
        self.assertIn("named in comparator output", vs[1].detail)


class TestEnsembleSemantics(unittest.TestCase):
    def _r(self, *pairs):
        return C.EnsembleResult(
            [C.Verdict(n, t, o) for n, t, o in pairs])

    def test_an_uninformative_member_has_not_voted(self):
        """Folding an infrastructure failure into either verdict is how
        an ensemble manufactures agreement it did not earn."""
        r = self._r(("lean", "quick", C.ACCEPT),
                    ("lean4lean", "medium", C.ERROR))
        self.assertTrue(r.unanimous_accept)
        self.assertFalse(r.disagreement)
        self.assertEqual(len(r.informative_verdicts), 1)

    def test_a_timeout_is_not_a_reject(self):
        r = self._r(("comparator/kernel", "high", C.TIMEOUT))
        self.assertFalse(r.unanimous_reject)
        self.assertFalse(r.unanimous_accept)

    def test_disagreement_needs_an_informative_split(self):
        r = self._r(("lean", "quick", C.ACCEPT),
                    ("lean4lean", "medium", C.REJECT))
        self.assertTrue(r.disagreement)
        self.assertIn("disagreement", r.summary())

    def test_an_ensemble_of_one_cannot_disagree(self):
        r = self._r(("lean", "quick", C.ACCEPT))
        self.assertFalse(r.disagreement)

    def test_the_summary_always_names_the_tiers_that_ran(self):
        """A verdict whose ensemble is unstated cannot be read later."""
        r = self._r(("lean", "quick", C.ACCEPT),
                    ("comparator/nanoda", "high", C.ACCEPT))
        self.assertIn("tiers[high,quick]", r.summary())

    def test_off_whitelist_axioms_are_surfaced(self):
        r = C.EnsembleResult([C.Verdict(
            "lean", "quick", C.ACCEPT,
            axioms=["propext", "Lean.ofReduceBool"])])
        self.assertEqual(r.off_whitelist, ["Lean.ofReduceBool"])
        self.assertIn("off-whitelist", r.summary())


class TestElaborationParsing(unittest.TestCase):
    def test_axioms_are_read_off_the_files_own_output(self):
        out = ("'thm' depends on axioms: [propext, Classical.choice]\n")
        v = C.LeanElaborate().read_output(out)
        self.assertEqual(v.outcome, C.ACCEPT)
        self.assertEqual(v.axioms, ["Classical.choice", "propext"])

    def test_an_elaboration_error_rejects(self):
        v = C.LeanElaborate().read_output("Claim.lean:4:2: error: unknown id")
        self.assertEqual(v.outcome, C.REJECT)

    def test_leanchecker_is_not_a_member(self):
        """Excluded on purpose: it is Lean's own kernel running twice, so
        counting it as a second opinion is the common-mode failure this
        ensemble is built to avoid."""
        self.assertNotIn("leanchecker", C.available())


if __name__ == "__main__":
    unittest.main()
