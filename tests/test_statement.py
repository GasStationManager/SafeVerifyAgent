"""The statement rung (`audits/statement.py`) on a small synthetic project.

Everything but the last class runs without Lean: source resolution is the
part that must work on a project nobody has built. The Lean rung is tested
live when a toolchain is on PATH, and its absence is tested everywhere —
a rung that did not run has to say so.
"""

import os
import sys
import tempfile
import textwrap
import unittest

HERE = os.path.dirname(__file__)
sys.path.insert(0, os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "..", "audits"))

import statement as S                                         # noqa: E402
from safeverifyagent.extract import lean_available            # noqa: E402

CLAIM = """\
import Demo.Defs

set_option autoImplicit false

open Lib.Top

namespace Demo.Claims

universe u

/-- The headline. -/
theorem main_claim (X : Type u) [Space X] [T2Space X] [SimplyJoinedSpace X]
    (h : X = X) :
    Nonempty (X ≃ₕ Ball 3) := by
  sorry

end Demo.Claims
"""

LIB = """\
namespace Lib.Top

/-- A space: a type with a notion of open set. -/
class Space (X : Type _) where
  /-- The open sets. -/
  isOpen : (X → Prop) → Prop
  isOpen_univ : isOpen (fun _ => True)

/-- Points can be separated. -/
class T2Space (X : Type _) [Space X] : Prop where
  t2 : ∀ x y : X, x ≠ y → True

variable {X : Type _} [Space X]

variable (X) in
/-- Any two points are joined. -/
class JoinedSpace : Prop where
  joined : ∀ x y : X, True

/-- Inhabited, as a class parent. -/
class InhabitedSpace (X : Type _) [Space X] : Prop where
  ne : Nonempty X

/-- Joined, with no holes. -/
class SimplyJoinedSpace (X : Type _) [Space X] : Prop
    extends InhabitedSpace X where
  nonempty : Nonempty X

namespace SimplyJoinedSpace
variable [SimplyJoinedSpace X]
instance (priority := 100) : JoinedSpace X := ⟨fun _ _ => trivial⟩
end SimplyJoinedSpace

/-- Not forgetful: it needs an extra assumption, and must not be listed. -/
class Fancy (X : Type _) : Prop where
  f : True
instance [SimplyJoinedSpace X] [Fancy X] : Inhabited (Fancy X) := ⟨⟨trivial⟩⟩

/-- A homeomorphism, for the test. -/
structure Homeo (X Y : Type _) [Space X] [Space Y]
    extends Nonempty (X → Y) where
  cont : True

infixl:25 " ≃ₕ " => Homeo

/-- The standard ball. -/
def Ball (n : Nat) : Type := Fin (n + 1)

instance (n : Nat) : Space (Ball n) := ⟨fun _ => True, trivial⟩

end Lib.Top
"""

REFERENCE = """\
# Reference

## Hypotheses

- H1. X is a space.
- H2. X is Hausdorff.
- H3. X is joined.
- H4. X is simply joined.
- H5. X is compact.

## Conclusion

- C1. X is homeomorphic to the 3-ball.
"""


def write(root, rel, text):
    p = os.path.join(root, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(text)
    return p


def make_project():
    d = tempfile.mkdtemp(prefix="sva-stmt-")
    proj = os.path.join(d, "proj")
    write(proj, "lakefile.toml", textwrap.dedent("""\
        name = "Demo"

        [leanOptions]
        autoImplicit = false
        maxSynthPendingDepth = 3

        [[lean_lib]]
        name = "Demo"
        """))
    write(proj, "lean-toolchain", "leanprover/lean4:v0.0.0-none\n")
    write(proj, "Demo/Claim.lean", CLAIM)
    write(proj, "Demo/Defs.lean", "import Lib.Top\n")
    lib = os.path.join(d, "lib")
    write(lib, "Lib/Top.lean", LIB)
    # a test directory in the dependency must NOT be searched
    write(lib, "MathlibTest/Decoy.lean",
          'namespace Lib.Top\nclass Space (X : Type) : Prop where\n'
          '  decoy : True\nend Lib.Top\n')
    return d, proj, lib


class Base(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp, cls.proj, cls.lib = make_project()
        cls.st = S.build(cls.proj, "Demo.Claim", "Demo.Claims.main_claim",
                         mathlib=cls.lib, run_lean=False)
        cls.md = "\n".join(S.render(cls.st))

    def res(self, tok):
        return next(r for r in self.st.resolutions if r.token == tok)


class TestTheSignature(Base):
    def test_source_text_and_docstring(self):
        self.assertIn("theorem main_claim", self.md)
        self.assertIn("The headline.", self.md)

    def test_every_binder_is_listed(self):
        kinds = [(b.kind, b.type) for b in self.st.decl.binders]
        self.assertEqual(kinds, [
            ("explicit", "Type u"), ("instance", "Space X"),
            ("instance", "T2Space X"), ("instance", "SimplyJoinedSpace X"),
            ("explicit", "X = X")])
        self.assertEqual(" ".join(self.st.decl.type.split()),
                         "Nonempty (X ≃ₕ Ball 3)")

    def test_scope_universes_and_options(self):
        sc = self.st.decl.scope
        self.assertEqual(sc.namespace, "Demo.Claims")
        self.assertIn("Lib.Top", sc.opens)
        self.assertIn("`u`", self.md)
        self.assertIn("set_option autoImplicit false", self.md)
        # project-wide options are invisible in the file; the dossier
        # must still show them
        self.assertIn("maxSynthPendingDepth = 3", self.md)

    def test_lean_rung_says_it_did_not_run(self):
        self.assertIn("not run", self.st.lean_note)
        self.assertIn("## 6. Lean rung", self.md)

    def test_lean_rung_reports_missing_build(self):
        _, note = S.lean_rung(self.proj, "Demo.Claim",
                              "Demo.Claims.main_claim", [], 10)
        self.assertTrue(note.startswith("not run"), note)


class TestResolution(Base):
    def test_class_resolves_through_open_with_doc_and_fields(self):
        h = self.res("Space").hits
        self.assertEqual([x.full_name for x in h], ["Lib.Top.Space"])
        self.assertIn("open set", h[0].doc)
        self.assertEqual([f for f, _ in h[0].fields],
                         ["isOpen", "isOpen_univ"])

    def test_test_directories_are_not_searched(self):
        self.assertTrue(all("MathlibTest" not in x.path
                            for x in self.res("Space").hits))

    def test_notation_resolves_to_its_structure(self):
        r = self.res("≃ₕ")
        self.assertEqual(r.notation[0][4], "Homeo")
        self.assertEqual(r.hits[0].full_name, "Lib.Top.Homeo")
        self.assertEqual(r.hits[0].extends, ["Nonempty (X → Y)"])
        self.assertEqual([f for f, _ in r.hits[0].fields], ["cont"])

    def test_def_body_one_level_down(self):
        h = self.res("Ball").hits[0]
        self.assertEqual(h.body, "Fin (n + 1)")

    def test_variable_in_prefix_is_shown(self):
        h = S.SourceIndex([("lib", self.lib)]).find_decl(
            "Lib.Top.JoinedSpace")[0]
        self.assertEqual(h.prefix, ["variable (X) in"])

    def test_every_resolution_cites_a_line(self):
        for r in self.st.resolutions:
            for h in r.hits:
                self.assertRegex(h.cite, r":\d+$")

    def test_forgetful_instances_only(self):
        steps = [s for chain in self.st.derived.values()
                 for s, *_ in chain]
        self.assertIn("Lib.Top.SimplyJoinedSpace ⟹ JoinedSpace", steps)
        self.assertFalse(any(s.endswith("⟹ Inhabited") for s in steps),
                         steps)
        # an `extends` parent is an instance with no `instance` line
        self.assertIn("Lib.Top.SimplyJoinedSpace ⟹ InhabitedSpace", steps)

    def test_unsearched_core_is_admitted(self):
        self.assertTrue(any("Init" in u for u in self.st.unsearched))


class TestPairing(Base):
    def setUp(self):
        self.ref = os.path.join(self.tmp, "REF.md")
        write(self.tmp, "REF.md", REFERENCE)
        self.clauses = S.parse_reference(self.ref)
        self.chosen, self.lean_un = S.pair(self.clauses,
                                           S.lean_clauses(self.st))
        self.out = "\n".join(S.render_pairing(self.st, self.clauses,
                                              self.ref))

    def test_reference_parse(self):
        self.assertEqual([c.label for c in self.clauses],
                         ["H1", "H2", "H3", "H4", "H5", "C1"])
        self.assertEqual(self.clauses[-1].side, "concl")

    def test_simply_joined_beats_joined(self):
        """The substring trap: `joined` is inside `SimplyJoinedSpace`, and
        the pairing must not let it hide the more specific clause."""
        self.assertIn("H4", self.chosen)
        self.assertNotIn("H3", self.chosen)

    def test_unmatched_on_both_sides_are_listed(self):
        self.assertIn("H2", self.chosen)            # Hausdorff ↔ T2Space
        self.assertNotIn("H5", self.chosen)         # compact: nothing
        un = self.out.split("### Reference clauses with no Lean")[1]
        self.assertIn("H3", un)
        self.assertIn("H5", un)
        self.assertIn("possibly implied: Lib.Top.SimplyJoinedSpace ⟹ "
                      "JoinedSpace", un)
        self.assertEqual(sorted(c.label for c in self.lean_un),
                         ["L1", "L5"])

    def test_numeral_mismatch_is_flagged(self):
        # reference says 3-ball; Lean says `Ball 3` = Fin (3 + 1): same
        # numeral, so no flag here; flag appears only when they differ
        self.assertIn("C1", self.chosen)


class TestWords(unittest.TestCase):
    def test_camel_case_and_digits(self):
        self.assertEqual(S.words("T2Space M"), ["t2"])
        self.assertEqual(S.words("SimplyConnectedSpace"),
                         ["simply", "connected"])
        self.assertIn("3", S.words("a topological 3-manifold"))
        self.assertIn("charted", S.words("a manifold"))
        self.assertEqual(S.words("S³"), ["sphere", "3"])


@unittest.skipUnless(lean_available(), "needs a Lean toolchain (elan)")
class TestLeanRungLive(unittest.TestCase):
    def test_check_print_axioms(self):
        import subprocess
        d = tempfile.mkdtemp(prefix="sva-stmt-live-")
        write(d, "lakefile.toml",
              'name = "Live"\n\n[[lean_lib]]\nname = "Live"\n')
        tc = subprocess.run(["lean", "--version"], capture_output=True,
                            text=True).stdout
        import re
        m = re.search(r"version (\d+\.\d+\.\d+)", tc)
        write(d, "lean-toolchain", f"leanprover/lean4:v{m.group(1)}\n")
        write(d, "Live.lean", textwrap.dedent("""\
            namespace Live
            /-- A class. -/
            class Good (X : Type) : Prop where
              ok : True
            theorem claim (X : Type) [Good X] : True := sorry
            end Live
            """))
        lake = S._lake()
        p = subprocess.run([lake, "build", "Live"], cwd=d,
                           capture_output=True, text=True)
        if p.returncode != 0:
            self.skipTest("could not build: " + p.stderr[-300:])
        st = S.build(d, "Live", "Live.claim", run_lean=True)
        self.assertTrue(st.lean_note.startswith("ran"), st.lean_note)
        self.assertIn("sorryAx", st.lean["axioms"])
        self.assertIn("Live.claim", st.lean["check"])
        self.assertIn("print Live.Good", st.lean)


if __name__ == "__main__":
    unittest.main()
