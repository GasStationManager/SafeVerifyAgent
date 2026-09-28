"""con-leche as an ensemble member: the parse, and what it may not claim.

The fixture half runs everywhere, on verdict lines recorded from the real
binary (con-leche `ae0c0c4`, built at Lean v4.33.0) and on two real
`lean4export` streams (lean4export `15f6055`, v4.33.0) of this module:

    theorem good (a b : Nat) : a + b = b + a := Nat.add_comm a b
    axiom myAx : 1 = 2
    theorem usesAx : 1 = 2 := myAx

exported as `lean4export Tiny -- good` and `-- usesAx`. The live half
runs the binary on those streams and is skipped when no con-leche is
discoverable (`$CON_LECHE`, PATH, `~/.local/bin`).
"""

import os
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from safeverifyagent import checkers as C                    # noqa: E402
from safeverifyagent import verdict as V                     # noqa: E402

FIX = os.path.join(os.path.dirname(__file__), "fixtures", "conleche")
GOOD = os.path.join(FIX, "good.ndjson")
CUSTOM_AXIOM = os.path.join(FIX, "custom_axiom.ndjson")

# Recorded verbatim from the binary.
ACCEPT_V = "con-leche: accepted 38 declarations (--verified)\n"
ACCEPT_T = "con-leche: accepted 38 declarations (--trusted)\n"
DECLINE_AXIOM = ("con-leche: not implemented yet: non-standard axiom (myAx) "
                 "[at axiom myAx, fold position 15] (--verified) t=0.0s\n")
DECLINE_SORRY = ("con-leche: not implemented yet: use of the sorryAx axiom in "
                 "value of usesSorry [at theorem usesSorry, fold position 297]"
                 " (--verified) t=0.1s\n")
DECLINE_PARSE = "con-leche: declined: unsafe axiom (--verified)\n"
REJECT_V = ("con-leche: invalid: type mismatch in theorem addOk "
            "[at theorem addOk, fold position 30] (--verified) t=0.0s\n")
MALFORMED = ("con-leche: /tmp/bad.ndjson:1: expected ':' after a key "
             "(byte 1)\n")
NO_FILE = ("uncaught exception: no such file or directory (error code: 2)\n"
           "  file: /nonexistent.ndjson\n")
USAGE = "con-leche: unknown option --bogus\nusage: con-leche [--verified|...\n"
# OVERVIEW.md §0: the Lean runtime's own panic, then exit(1).
OOM = "INTERNAL PANIC: out of memory\n"


def cl():
    return C.ConLeche(binary="con-leche")


class TestVerdictLineIsTheVerdict(unittest.TestCase):
    def test_accept_needs_the_line_and_exit_zero(self):
        v = cl().read_output(ACCEPT_V, "", 0)
        self.assertEqual(v.outcome, C.ACCEPT)
        self.assertIn("38", v.detail)
        # Same words, wrong exit: the adapter does not choose one.
        self.assertEqual(cl().read_output(ACCEPT_V, "", 1).outcome, C.ERROR)

    def test_exit_zero_alone_is_not_an_accept(self):
        self.assertEqual(cl().read_output("", "", 0).outcome, C.ERROR)

    def test_invalid_is_a_reject(self):
        v = cl().read_output("", REJECT_V, 1)
        self.assertEqual(v.outcome, C.REJECT)
        self.assertTrue(v.informative)

    def test_out_of_memory_exits_one_and_is_not_a_reject(self):
        """Exit 1 is shared by a reject and the runtime's OOM panic
        (OVERVIEW.md §0); only stderr tells them apart."""
        v = cl().read_output("", OOM, 1)
        self.assertEqual(v.outcome, C.ERROR)
        self.assertFalse(v.informative)
        self.assertIn("out of memory", v.detail)

    def test_uncaught_exception_exit_one_is_not_a_reject(self):
        """Measured: a missing input file exits 1 with no verdict line."""
        self.assertEqual(cl().read_output("", NO_FILE, 1).outcome, C.ERROR)

    def test_decline_is_a_statement_about_the_checker(self):
        for line in (DECLINE_AXIOM, DECLINE_SORRY, DECLINE_PARSE):
            v = cl().read_output("", line, 2)
            self.assertEqual(v.outcome, C.DECLINED, line)
            self.assertFalse(v.informative)

    def test_decline_line_with_reject_exit_is_error(self):
        self.assertEqual(cl().read_output("", DECLINE_AXIOM, 1).outcome,
                         C.ERROR)

    def test_malformed_input_and_usage_are_errors(self):
        self.assertEqual(cl().read_output("", MALFORMED, 3).outcome, C.ERROR)
        self.assertEqual(cl().read_output("", USAGE, 3).outcome, C.ERROR)

    def test_a_verdict_line_in_the_other_mode_is_refused(self):
        v = cl().read_output(ACCEPT_T, "", 0, verified=True)
        self.assertEqual(v.outcome, C.ERROR)
        self.assertIn("--trusted", v.detail)
        v = cl().read_output(ACCEPT_V, "", 0, verified=False)
        self.assertEqual(v.outcome, C.ERROR)


class TestModeAndTier(unittest.TestCase):
    def test_verified_is_high_tier(self):
        v = cl().read_output(ACCEPT_V, "", 0, verified=True)
        self.assertEqual((v.tier, v.mode), ("high", "verified"))

    def test_trusted_is_not_the_formal_tier(self):
        v = cl().read_output(ACCEPT_T, "", 0, verified=False)
        self.assertEqual(v.outcome, C.ACCEPT)
        self.assertEqual((v.tier, v.mode), (C.TRUSTED_TIER, "trusted"))
        self.assertNotEqual(v.tier, V.FORMAL_TIER)
        self.assertIn("outside", v.detail)

    def test_a_trusted_accept_cannot_be_filed_formal(self):
        v = cl().read_output(ACCEPT_T, "", 0, verified=False)
        with self.assertRaises(V.AuditError):
            V.Finding("h1", "check", V.CLEAN, V.FORMAL, tier=v.tier,
                      intake=V.PAIRED)

    def test_summary_names_the_mode(self):
        r = C.EnsembleResult([cl().read_output(ACCEPT_T, "", 0,
                                               verified=False)])
        self.assertIn("con-leche[trusted]=accept", r.summary())
        self.assertIn("high-trusted", r.summary())


class TestStreamAxioms(unittest.TestCase):
    def test_axioms_are_read_off_the_stream(self):
        self.assertEqual(C.stream_axioms(CUSTOM_AXIOM), ["myAx"])
        self.assertEqual(C.stream_axioms(GOOD), [])

    def test_hierarchical_and_numeric_names_resolve(self):
        d = tempfile.mkdtemp(prefix="sva-cl-")
        p = os.path.join(d, "s.ndjson")
        with open(p, "w") as f:
            f.write('{"in":1,"str":{"pre":0,"str":"nd"}}\n'
                    '{"in":2,"str":{"pre":1,"str":"_native"}}\n'
                    '{"in":3,"num":{"pre":2,"i":7}}\n'
                    '{"ie":0,"sort":0}\n'
                    '{"axiom":{"isUnsafe":false,"levelParams":[],'
                    '"name":3,"type":0}}\n')
        self.assertEqual(C.stream_axioms(p), ["nd._native.7"])

    def test_off_whitelist_axiom_surfaces_in_the_ensemble(self):
        v = cl().read_output("", DECLINE_AXIOM, 2, axioms=["myAx"])
        self.assertEqual(C.EnsembleResult([v]).off_whitelist, ["myAx"])


class TestDiscovery(unittest.TestCase):
    def test_env_var_may_name_the_binary_or_the_repo(self):
        d = tempfile.mkdtemp(prefix="sva-cl-")
        b = os.path.join(d, ".lake/build/bin/con-leche")
        os.makedirs(os.path.dirname(b))
        open(b, "w").close()
        old = os.environ.get("CON_LECHE")
        try:
            os.environ["CON_LECHE"] = d
            self.assertEqual(C.ConLeche.discover().binary, b)
            os.environ["CON_LECHE"] = b
            self.assertEqual(C.ConLeche.discover().binary, b)
        finally:
            if old is None:
                os.environ.pop("CON_LECHE", None)
            else:
                os.environ["CON_LECHE"] = old

    def test_available_reports_con_leche(self):
        a = C.available()
        self.assertIn("con-leche", a)
        self.assertIn("lean4export", a)


LIVE = C.ConLeche.discover()


@unittest.skipUnless(LIVE, "needs a con-leche binary ($CON_LECHE)")
class TestLive(unittest.TestCase):
    def test_real_accept(self):
        for verified in (True, False):
            v = LIVE.check(GOOD, verified=verified, jobs=1)
            self.assertEqual(v.outcome, C.ACCEPT, v.detail)
            self.assertEqual(v.mode, "verified" if verified else "trusted")

    def test_real_custom_axiom_declines(self):
        v = LIVE.check(CUSTOM_AXIOM, jobs=1)
        self.assertEqual(v.outcome, C.DECLINED, v.detail)
        self.assertEqual(v.axioms, ["myAx"])

    def test_missing_input_is_error(self):
        v = LIVE.check(os.path.join(FIX, "does-not-exist.ndjson"))
        self.assertEqual(v.outcome, C.ERROR)


def _exporter_toolchain():
    exe = C.find_lean4export()
    if not exe:
        return None
    tc = os.path.join(os.path.dirname(os.path.realpath(exe)),
                      "..", "..", "..", "lean-toolchain")
    if not os.path.exists(tc):
        return None
    with open(tc) as f:
        return f.read().strip()


@unittest.skipUnless(LIVE and _exporter_toolchain() and C._elan("lake"),
                     "needs con-leche, lake and a lean4export built in a "
                     "repo whose lean-toolchain is readable")
class TestLiveExport(unittest.TestCase):
    def test_export_then_check(self):
        d = tempfile.mkdtemp(prefix="sva-cl-proj-")
        with open(os.path.join(d, "lean-toolchain"), "w") as f:
            f.write(_exporter_toolchain() + "\n")
        with open(os.path.join(d, "lakefile.toml"), "w") as f:
            f.write('name = "tiny"\n\n[[lean_lib]]\nname = "Tiny"\n')
        with open(os.path.join(d, "Tiny.lean"), "w") as f:
            f.write("theorem good (a b : Nat) : a + b = b + a := "
                    "Nat.add_comm a b\naxiom myAx : 1 = 2\n"
                    "theorem usesAx : 1 = 2 := myAx\n")
        lake = C._elan("lake")
        subprocess.run([lake, "build", "Tiny"], cwd=d, check=True,
                       capture_output=True)
        good = LIVE.export(d, "Tiny", decls=["good"])
        self.assertEqual(LIVE.check(good, jobs=1).outcome, C.ACCEPT)
        bad = LIVE.export(d, "Tiny", decls=["usesAx"])
        v = LIVE.check(bad, jobs=1)
        self.assertEqual((v.outcome, v.axioms), (C.DECLINED, ["myAx"]))


if __name__ == "__main__":
    unittest.main()
