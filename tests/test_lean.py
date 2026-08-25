"""Tests that need a real Lean toolchain.

Skipped without one, so `python3 -m unittest discover -s tests` still
passes on a bare checkout. Install with elan (see README) to run them.

These cover the two claims the rest of the suite cannot reach with
fixtures: that extraction through Lean's frontend actually works, and
that the quick tier's verdicts are what it says they are.
"""

import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from safeverifyagent import checkers as C                    # noqa: E402
from safeverifyagent.extract import (                        # noqa: E402
    _extract_via_regex, extract, lean_available,
)

DENSE = """theorem dense (a b c : Nat) : a + b + c = c + b + a := by
  have k1 : a + b = b + a := ?_; have k2 : b + c = c + b := ?_
  have k3 : a + (b + c) = (a + b) + c := ?_; have k4 : True := ?_
  all_goals first | omega | trivial
"""

ONE_LINE = ("theorem oneline (a b : Nat) : a + b = b + a := by "
            "have k1 : a + b = b + a := ?_; have k2 : True := ?_; "
            "all_goals first | omega | trivial\n")


def write(tmp, name, src):
    path = os.path.join(tmp, name)
    with open(path, "w", encoding="utf-8") as f:
        f.write(src)
    return path


@unittest.skipUnless(lean_available(), "needs a Lean toolchain (elan)")
class TestExtraction(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="sva-lean-")

    def ids(self, result):
        return [o.id for o in result if not o.is_whole_claim]

    def test_the_frontend_path_runs_and_is_not_degraded(self):
        path = write(self.tmp, "Dense.lean", DENSE)
        r = extract(path)
        self.assertFalse(r.degraded, r.note)
        self.assertEqual(r.errors, 0)

    def test_chained_haves_are_all_found(self):
        """`have h : T := ?_;` chained on one line is what dense real
        proofs use, and it is where a line-oriented parser loses steps."""
        path = write(self.tmp, "Dense.lean", DENSE)
        self.assertEqual(self.ids(extract(path)),
                         ["dense", "k1", "k2", "k3", "k4"])

    def test_the_regex_fallback_loses_every_have_after_the_first_on_a_line(self):
        """Measured, not assumed: the fallback finds k1 and k3 and misses
        k2 and k4. An obligation nobody extracted is an obligation nobody
        audits, which is why `degraded` has to be loud."""
        path = write(self.tmp, "Dense.lean", DENSE)
        self.assertEqual(self.ids(_extract_via_regex(path, note="test")),
                         ["dense", "k1", "k3"])

    def test_a_fully_inline_proof_defeats_the_regex_entirely(self):
        path = write(self.tmp, "OneLine.lean", ONE_LINE)
        self.assertEqual(self.ids(extract(path)), ["oneline", "k1", "k2"])
        # Not one `have` survives: the whole proof is on the theorem line.
        self.assertEqual(self.ids(_extract_via_regex(path, note="test")),
                         ["oneline"])

    def test_suffices_is_extracted_with_its_binder_name(self):
        path = write(self.tmp, "S.lean",
                     "theorem s (a : Nat) : a = a := by\n"
                     "  suffices hs : a = a by exact hs\n  rfl\n")
        by_id = {o.id: o for o in extract(path)}
        self.assertIn("hs", by_id)
        self.assertEqual(by_id["hs"].kind, "suffices")

    def test_statements_are_source_text_not_syntax_dumps(self):
        """The consumer is an auditor reading mathematics, so an
        s-expression would be the wrong artifact."""
        path = write(self.tmp, "Dense.lean", DENSE)
        by_id = {o.id: o for o in extract(path)}
        self.assertEqual(by_id["k1"].statement, "a + b = b + a")

    def test_the_whole_claim_obligation_is_always_present(self):
        path = write(self.tmp, "Dense.lean", DENSE)
        self.assertIn("claim", [o.id for o in extract(path)])


@unittest.skipUnless(lean_available(), "needs a Lean toolchain (elan)")
class TestQuickTier(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="sva-lean-")

    def test_a_sound_proof_is_accepted_with_no_axioms(self):
        path = write(self.tmp, "Good.lean",
                     "theorem good : 1 + 1 = 2 := by rfl\n#print axioms good\n")
        v = C.LeanElaborate().check(path)
        self.assertEqual(v.outcome, C.ACCEPT)
        self.assertEqual(v.axioms, [])

    def test_a_file_that_does_not_elaborate_is_rejected(self):
        path = write(self.tmp, "Bad.lean", "theorem bad : 1 + 1 = 3 := by rfl\n")
        self.assertEqual(C.LeanElaborate().check(path).outcome, C.REJECT)

    def test_an_axiom_leak_elaborates_clean_and_is_caught_by_the_scan(self):
        """The exploit class the cheap rung exists for: `native_decide`
        compiles without complaint and leaks an axiom. ACCEPT from the
        elaborator is not the end of the question."""
        path = write(self.tmp, "Leaky.lean",
                     "theorem leaky : (2:Nat) ^ 10 = 1024 := by native_decide\n"
                     "#print axioms leaky\n")
        r = C.quick_ensemble(path)
        self.assertTrue(r.unanimous_accept)         # the elaborator is happy
        self.assertTrue(r.off_whitelist)            # and the scan is not
        self.assertIn("off-whitelist", r.summary())


if __name__ == "__main__":
    unittest.main()
