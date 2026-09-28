"""The audit instruments, on a synthetic project whose ground truth is known.

`audits/` holds the mechanical rung: cone, route, join, no-supplier, scan and
ledger. Each was validated by hand against the NSE artifact; these tests pin
the SHAPES that validation depended on, on a project small enough that every
answer is known in advance (playbook rule 11: positive controls before a
sweep). No Lean toolchain is needed: every tool here reads source.

The project, `Demo`:
  * `seed_thm` (Solution.lean) is the headline. It uses `good_holds`, `helper`
    and `cone_lemma outer_holds.i`.
  * `wrapper_thm` (Solution.lean) restates something and nobody calls it; a
    `run_cmd` below it names it, which must NOT count as a use.
  * `dead_thm` takes `Never`, a structure nothing constructs; `only_for_dead`
    is used only by it, so it dies by chain.
  * `Display.lean` is imported by the library root BESIDE the solution, and its
    `paper_thm` is built on top of the seed.
  * `Orphan.lean` is imported by nothing.
  * `OpenFrontier` is a named open result discharged only from `Never`
    (conditional); `Inner` is supplied only inside `Outer` (route 4 positive);
    `Never` sits inside `Box`, which nobody builds (route 4 refuted);
    `Other.Inner` in `Twin.lean` is a SUPPLIED twin of the unsupplied
    `Demo.Inner`, the NSE masking configuration.
"""

import csv
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
AUDITS = os.path.join(HERE, "..", "audits")

FILES = {
    "lakefile.toml": '''name = "demo"

[[lean_lib]]
name = "Demo"
''',
    "Demo.lean": "import Demo.Solution\nimport Demo.Display\n",
    "Demo/Basic.lean": '''namespace Demo

/-- A predicate that IS supplied. -/
structure Good : Prop where
  ok : True

theorem good_holds : Good := ⟨trivial⟩

theorem good_user (h : Good) : True := trivial

/-- A missing result, carried by name and never discharged. -/
structure Never : Prop where
  ok : True

/-- A named open result, discharged only from `Never`. -/
def OpenFrontier : Prop := True

theorem openFrontier_holds (h : Never) : OpenFrontier := trivial

/-- Contains `Never`; nobody builds it, so route 4 is refuted. -/
structure Box : Prop where
  inner : Never

theorem helper : True := trivial

structure Inner : Prop where
  ok : True

/-- Route 4 positive: `Inner` is only ever built inside an `Outer`. -/
structure Outer : Prop where
  i : Inner

theorem outer_holds : Outer := ⟨⟨trivial⟩⟩

theorem cone_lemma (h : Inner) : True := trivial

class HasOpen : Prop where
  ok : True

theorem class_user [HasOpen] : True := trivial

def InferredOpen := ∀ n : Nat, n = n

theorem inferred_user (h : InferredOpen) : True := trivial

inductive Chain : Nat → Prop
  | step (n : Nat) (h : Chain n) : Chain (n + 1)

theorem chain_user (h : Chain 3) : True := trivial

/-- Only `dead_thm` uses this, so it dies with it. -/
theorem only_for_dead : True := trivial

theorem dead_thm (h : Never) : True := only_for_dead

theorem frontier_user (h : OpenFrontier) : True := trivial

end Demo
''',
    "Demo/Solution.lean": '''import Demo.Basic

namespace Demo

theorem seed_thm : True := by
  have := good_holds
  have := cone_lemma outer_holds.i
  exact helper

theorem wrapper_thm : True := helper

end Demo

open Lean in
run_cmd do
  for n in [``Demo.seed_thm, ``Demo.wrapper_thm] do
    pure ()

set_option maxHeartbeats 400000 in
theorem Demo.after_opt : True := trivial

macro "demo_tac" : tactic => `(tactic| trivial)
''',
    "Demo/Twin.lean": '''namespace Other

structure Inner : Prop where
  ok : True

theorem inner_holds : Inner := ⟨trivial⟩

theorem uses_inner (h : Inner) : True := trivial

theorem _root_.Demo.rooted : True := trivial

end Other
''',
    "Demo/Display.lean": '''import Demo.Solution
import Demo.Twin

namespace Demo

/-- The paper's Theorem 1, restated beside the solution. -/
theorem paper_thm : True := seed_thm

attribute [simp] paper_thm

@[simp] def displayDef : Nat := 3

end Demo
''',
    "Demo/Orphan.lean": '''import Demo.Basic

theorem Demo.orphan_thm : True := Demo.helper
''',
}


def run(*args, check=True):
    p = subprocess.run([sys.executable, *args], capture_output=True, text=True)
    if check and p.returncode != 0:
        raise AssertionError(f"{args} exited {p.returncode}\n{p.stdout}\n{p.stderr}")
    return p


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def rows(path):
    with open(path, newline="", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


class AuditToolsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.root = os.path.join(cls.tmp.name, "demo")
        for rel, text in FILES.items():
            p = os.path.join(cls.root, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(text)
        cls.out = os.path.join(cls.tmp.name, "out")
        os.makedirs(cls.out)
        cls.uns = os.path.join(cls.out, "UNS.txt")
        with open(cls.uns, "w") as fh:
            fh.write("# from nosupplier\nDemo.Never\n")
        cls.cone = os.path.join(cls.out, "CONE.csv")
        run(os.path.join(AUDITS, "cone.py"), cls.root, "--seed", "Demo.seed_thm",
            "-o", cls.cone, "--unsupplied", cls.uns)
        cls.C = {r["name"]: r for r in rows(cls.cone)}

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def tool(self, name):
        return os.path.join(AUDITS, name)

    # ---------------------------------------------------------------- cone
    def test_cone_membership_and_depth(self):
        C = self.C
        self.assertEqual(C["Demo.seed_thm"]["depth"], "0")
        self.assertEqual(C["Demo.helper"]["depth"], "1")
        self.assertEqual(C["Demo.good_holds"]["depth"], "1")
        self.assertEqual(C["Demo.Good"]["depth"], "2")
        self.assertEqual(C["Demo.Good"]["via"], "Demo.good_holds")
        for n in ("Demo.wrapper_thm", "Demo.dead_thm", "Demo.paper_thm", "Demo.orphan_thm"):
            self.assertEqual(C[n]["in_cone"], "False", n)

    def test_run_cmd_is_not_a_consumer(self):
        """A `run_cmd` listing names to check made the declaration above it
        'use' them all, which is harmless for a cone and fatal for a consumer
        count: `wrapper_thm` would stop looking like a wrapper."""
        self.assertEqual(self.C["Demo.wrapper_thm"]["consumers"], "0")
        self.assertEqual(self.C["Demo.seed_thm"]["consumers"], "1")   # paper_thm only

    def test_same_line_set_option_in_declaration_is_parsed(self):
        self.assertIn("Demo.after_opt", self.C)

    def test_root_prefixed_name(self):
        self.assertIn("Demo.rooted", self.C)
        self.assertNotIn("Other._root_.Demo.rooted", self.C)

    def test_display_orphan_and_dead_columns(self):
        C = self.C
        self.assertEqual(C["Demo.paper_thm"]["above_seed"], "True")
        self.assertEqual(C["Demo.wrapper_thm"]["above_seed"], "False")
        self.assertEqual(C["Demo.orphan_thm"]["orphan_file"], "True")
        self.assertEqual(C["Demo.orphan_thm"]["in_default_build"], "False")
        self.assertEqual(C["Demo.paper_thm"]["orphan_file"], "False")
        self.assertEqual(C["Demo.dead_thm"]["dead"], "direct")
        self.assertEqual(C["Demo.only_for_dead"]["dead"], "chain")
        self.assertEqual(C["Demo.openFrontier_holds"]["dead"], "direct")
        self.assertEqual(C["Demo.seed_thm"]["dead"], "")
        self.assertEqual(C["Demo.helper"]["dead"], "")   # has live consumers

    # ---------------------------------------------------------------- join
    def test_join_classifies_each_citation(self):
        cit = os.path.join(self.out, "CIT.csv")
        dead_line = int(self.C["Demo.dead_thm"]["line"]) + 1     # inside its body
        with open(cit, "w") as fh:
            fh.write("file,line,claim\n"
                     "Demo/Solution.lean,7,seed body\n"
                     "Solution.lean,10,wrapper\n"
                     f"./Demo/Basic.lean,{dead_line},dead\n"
                     "Display.lean,7,paper\n"
                     "Demo/Orphan.lean,3,orphan\n"
                     "Demo/Basic.lean,1,before any declaration\n"
                     "Nope.lean,3,missing\n")
        j = os.path.join(self.out, "J.csv")
        run(self.tool("cone.py"), "join", self.cone, cit, "-o", j)
        got = {r["claim"]: r for r in rows(j)}
        self.assertEqual(got["seed body"]["why"], "route")
        self.assertEqual(got["seed body"]["lean_name"], "Demo.seed_thm")
        self.assertEqual(got["wrapper"]["why"], "wrapper")
        self.assertEqual(got["wrapper"]["consumers"], "0")
        self.assertEqual(got["dead"]["why"], "dead")
        self.assertEqual(got["dead"]["lean_name"], "Demo.dead_thm")
        self.assertEqual(got["paper"]["why"], "above_seed")
        self.assertEqual(got["orphan"]["why"], "orphan")
        self.assertEqual(got["before any declaration"]["why"], "unknown")
        self.assertEqual(got["missing"]["why"], "unknown")
        # extra columns pass through, and --unsupplied recomputes from source
        j2 = os.path.join(self.out, "J2.csv")
        run(self.tool("cone.py"), "join", self.cone, cit, "-o", j2,
            "--unsupplied", self.uns, "--root", self.root)
        self.assertEqual([r["why"] for r in rows(j2)], [r["why"] for r in rows(j)])

    # ---------------------------------------------------------------- route
    def test_route_is_in_dependency_order(self):
        r1 = os.path.join(self.out, "ROUTE.md")
        r2 = os.path.join(self.out, "ROUTE2.md")
        run(self.tool("cone.py"), "route", "--root", self.root, "Demo.seed_thm", "-o", r1)
        run(self.tool("cone.py"), "route", "--cone", self.cone, "-o", r2)
        a, b = read(r1), read(r2)
        self.assertEqual(a, b)
        i = [a.index(f"`{n}`") for n in ("Demo.seed_thm", "Demo.helper", "Demo.Good")]
        self.assertEqual(i, sorted(i))
        self.assertNotIn("Demo.wrapper_thm", a)

    # ---------------------------------------------------------- nosupplier
    def nosupplier(self, *extra, name="NS"):
        out = os.path.join(self.out, name + ".csv")
        run(self.tool("nosupplier.py"), self.root, "-o", out, *extra)
        return {r["predicate"]: r for r in rows(out)}, out

    def test_nosupplier_default(self):
        R, out = self.nosupplier("--all")
        self.assertEqual(R["Demo.Never"]["status"], "no_supplier")
        self.assertEqual(R["Demo.Never"]["hint"], "route4-refuted")
        self.assertIn("Demo.Box", R["Demo.Never"]["route4_chain"])
        self.assertEqual(R["Demo.Good"]["status"], "supplied")
        self.assertEqual(R["Demo.Good"]["unique_short_name"], "True")
        self.assertEqual(R["Demo.Good"]["negative_reliable"], "True")
        # the masking trap: a supplied twin must not supply Demo.Inner
        self.assertEqual(R["Demo.Inner"]["status"], "no_supplier")
        self.assertEqual(R["Demo.Inner"]["unique_short_name"], "False")
        self.assertEqual(R["Demo.Inner"]["hint"], "route4")
        self.assertIn("Demo.Outer (supplied)", R["Demo.Inner"]["route4_chain"])
        self.assertEqual(R["Other.Inner"]["status"], "supplied")
        self.assertEqual(R["Other.Inner"]["negative_reliable"], "False")
        # closure without a base case
        self.assertEqual(R["Demo.Chain"]["status"], "conditional")
        self.assertIn("closure without a base case", R["Demo.Chain"]["chain"])
        # a named open result discharged only from an unsupplied one
        self.assertEqual(R["Demo.OpenFrontier"]["status"], "conditional")
        self.assertIn("needs Demo.Never", R["Demo.OpenFrontier"]["chain"])
        self.assertNotIn("Demo.InferredOpen", R)     # only under the convention
        self.assertTrue(os.path.exists(out[:-4] + ".md"))

    def test_nosupplier_default_rows_are_the_original_set(self):
        R, _ = self.nosupplier(name="NS0")
        self.assertIn("Demo.Never", R)
        self.assertNotIn("Demo.OpenFrontier", R)     # conditional: convention only
        self.assertNotIn("Demo.Good", R)

    def test_nosupplier_named_hypothesis_convention(self):
        R, out = self.nosupplier("--convention", "named-hypothesis", name="NSN")
        self.assertEqual(R["Demo.InferredOpen"]["shape"], "prop_inferred")
        self.assertEqual(R["Demo.OpenFrontier"]["status"], "conditional")
        self.assertEqual(R["Demo.HasOpen"]["shape"], "class")
        md = read(out[:-4] + ".md")
        self.assertIn("## Prop-valued defs used as binders", md)
        self.assertIn("## Classes used as binders", md)
        self.assertIn("Demo.HasOpen", md.split("## Classes used as binders")[1])

    def test_nosupplier_cone(self):
        R, _ = self.nosupplier("--cone", self.cone, "--convention", "named-hypothesis",
                               name="NSC")
        # only `cone_lemma` (in cone) takes a hypothesis on the route
        self.assertEqual(set(R), {"Demo.Inner"})
        self.assertEqual(R["Demo.Inner"]["hypothesis_sites_in_cone"], "1")
        self.assertEqual(R["Demo.Inner"]["hint"], "route4")

    # ---------------------------------------------------------------- scan
    def test_scan_lists_sites(self):
        md = os.path.join(self.out, "SCAN.md")
        p = run(self.tool("scan_repo.py"), self.root, "--md", md)
        self.assertIn("run_cmd", p.stdout)
        text = read(md)
        sec = text.split("### run_cmd (1)")[1].split("###")[0]
        self.assertIn("`Demo/Solution.lean:15`", sec)
        self.assertIn("open Lean in", sec)
        self.assertIn("``Demo.seed_thm", sec)
        self.assertIn("`Demo/Solution.lean:22`", text.split("### macro (1)")[1])
        self.assertIn("maxHeartbeats 400000", text)
        self.assertIn("`Demo/Display.lean:9`", text.split("### attribute (1)")[1])
        self.assertIn("`Demo/Display.lean:11`", text.split("### implicit-use def (1)")[1])

    # -------------------------------------------------------------- ledger
    def test_ledger_tiers(self):
        helper_line = self.C["Demo.helper"]["line"]
        rep = os.path.join(self.out, "reports")
        os.makedirs(rep, exist_ok=True)
        with open(os.path.join(rep, "w1.md"), "w") as fh:
            fh.write(f"Read `Demo/Solution.lean:5` and the helper at Basic.lean:{helper_line}.\n"
                     "Not a match: ComparatorSolution.lean\n"
                     "READ-LINE-BY-LINE: Demo/Solution.lean\n"
                     "- READ-LINE-BY-LINE: `Nope.lean`\n")
        out = os.path.join(self.out, "LEDGER.md")
        run(self.tool("ledger.py"), self.cone, rep, "-o", out)
        text = read(out)
        incone = [r for r in self.C.values()
                  if r["in_cone"] == "True" and r["kind"] in ("theorem", "lemma")]
        n = len(incone)
        n_sol = sum(1 for r in incone if r["file"] == "Demo/Solution.lean")
        self.assertIn(f"| 1. in cone | 2 | {n} | 100% |", text)
        # both files named -> nothing never-named
        self.assertIn(f"| 2. in a file some report NAMES (loose upper bound) | 2 | {n} |", text)
        # cited: seed_thm (Solution:5) and helper (Basic:22)
        self.assertIn("| 3. CITED at `file:line` (the containing declaration) | 2 | 2 |", text)
        self.assertIn(f"| 4. declared READ LINE BY LINE | 1 | {n_sol} |", text)
        self.assertIn("tiers consistent", text)
        self.assertIn("`Nope.lean` matches no file", text)


if __name__ == "__main__":
    unittest.main()
