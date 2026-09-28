"""`audits/junkvalue.py` on tiny synthetic projects, one per false-positive pattern.

The differential-geometry triage (`audits/dg-intake/JUNKVALUE-TRIAGE.md`) read 290
of the scanner's hits and classed 117 as scanner false positives, in named
patterns P1-P12. Each test below reproduces one pattern on a fixture small enough
that the right answer is known, and pairs it with a CONTROL: the same shape with
the guard removed must still be flagged, because the point of the fix is to stop
reporting guarded divisions, not to stop reporting divisions (playbook rule 11).
No Lean toolchain is needed: the scanner reads source.
"""

import contextlib
import csv
import io
import os
import subprocess
import sys
import tempfile
import textwrap
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
AUDITS = os.path.join(HERE, "..", "audits")
sys.path.insert(0, AUDITS)
import junkvalue  # noqa: E402


def run(files, **kw):
    """Scan a project made of `files` ({relpath: source}); return the rows."""
    with tempfile.TemporaryDirectory() as root:
        for rel, src in files.items():
            path = os.path.join(root, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(textwrap.dedent(src))
        with contextlib.redirect_stdout(io.StringIO()):
            return junkvalue.scan(root, **kw)


def hits(rows):
    return {(r["decl"].split(".")[-1], r["denominator"]) for r in rows}


class PositiveControl(unittest.TestCase):
    """The NSE shape (`transportPhase` carrying `Kr / K`) is still caught."""

    SRC = {"Demo/Phase.lean": """
        namespace Demo

        def transportPhase (Kr K : ℝ) : ℝ := Kr / K

        theorem transportPhase_value (Kr K : ℝ) : transportPhase Kr K = Kr / K := rfl

        theorem transportPhase_guarded (Kr K : ℝ) (hK : K ≠ 0) :
            transportPhase Kr K = Kr / K := rfl

        end Demo
        """}

    def test_both_modes_flag_the_unguarded_theorem(self):
        h = hits(run(self.SRC))
        self.assertIn(("transportPhase_value", "K"), h)
        self.assertIn(("transportPhase_value", "K (via transportPhase)"), h)
        self.assertFalse({x for x in h if x[0] == "transportPhase_guarded"})

    def test_class_hint_is_exact_value(self):
        rows = run(self.SRC)
        self.assertEqual({r["class_hint"] for r in rows}, {"exact-value"})


class P3StructureField(unittest.TestCase):
    """A binder of a structure with a `0 < param` field guards that param,
    by POSITION."""

    STRUCT = """
        namespace Demo

        structure Neck (g : ℕ) (δ : ℝ) (k : ℕ) where
          delta_pos : 0 < δ
          scale : ℝ
          scale_pos : 0 < scale

        structure Pair (a b : ℝ) where
          b_pos : 0 < b

        def buf (δ : ℝ) : ℝ := δ⁻¹ + 1

        end Demo
        """

    def test_structure_binder_guards(self):
        rows = run({"Demo/S.lean": self.STRUCT, "Demo/T.lean": """
            namespace Demo
            theorem guarded (g k : ℕ) (δ : ℝ) (N : Neck g δ k) : buf δ = δ⁻¹ + 1 := rfl
            theorem in_concl (g k : ℕ) (δ : ℝ) :
                ∀ N : Neck g δ k, buf δ = δ⁻¹ + 1 := fun _ => rfl
            theorem control (g k : ℕ) (δ : ℝ) : buf δ = δ⁻¹ + 1 := rfl
            end Demo
            """})
        h = hits(rows)
        self.assertFalse({x for x in h if x[0] in ("guarded", "in_concl")})
        self.assertIn(("control", "δ"), h)
        self.assertIn(("control", "δ (via buf)"), h)

    def test_position_not_name(self):
        # `Pair b a` guards its SECOND argument, which here is `a`.
        h = hits(run({"Demo/S.lean": self.STRUCT, "Demo/T.lean": """
            namespace Demo
            theorem pos (a b : ℝ) (P : Pair b a) : a / a + 1 / b = 2 := sorry
            end Demo
            """}))
        self.assertEqual(h, {("pos", "b")})

    def test_positive_field_projection_chains(self):
        # `N.scale` is positive by `scale_pos`; `N.scale ≤ r` then guards r (P3 + P2).
        h = hits(run({"Demo/S.lean": self.STRUCT, "Demo/T.lean": """
            namespace Demo
            theorem proj (g k : ℕ) (δ r : ℝ) (N : Neck g δ k) (h : N.scale ≤ r) :
                1 / r = r⁻¹ := sorry
            end Demo
            """}))
        self.assertEqual(h, set())


class P1NameCollision(unittest.TestCase):
    DEFS = {"Demo/Radial.lean": """
        namespace Demo.Radial
        private def gamma (a : ℝ → ℝ) (r : ℝ) := a r / r ^ 2
        def gam (a r : ℝ) : ℝ := a / r
        theorem same_file (f : ℝ → ℝ) (r : ℝ) : gamma f r = f r / r ^ 2 := rfl
        end Demo.Radial
        """,
            "Demo/Flow.lean": """
        namespace Demo
        def FlowTo.scale (F : FlowTo) (c : ℝ) : ℝ := F.t / c
        end Demo
        """}

    def test_private_def_not_matched_outside_its_file(self):
        h = hits(run({**self.DEFS, "Demo/Use.lean": """
            namespace Demo.Radial
            theorem other_file (gamma : ℝ → ℝ) (r : ℝ) : gamma r = r := rfl
            theorem other_file2 (f : ℝ → ℝ) (r : ℝ) : gamma f r = f r := sorry
            end Demo.Radial
            """}))
        self.assertIn(("same_file", "r (via gamma)"), h)
        self.assertFalse({x for x in h if x[0].startswith("other_file")})

    def test_local_binder_shadows(self):
        h = hits(run({**self.DEFS, "Demo/Use.lean": """
            namespace Demo.Radial
            theorem curve (gam : ℝ → ℝ → ℝ) (a r : ℝ) : gam a r = a := sorry
            end Demo.Radial
            """}))
        self.assertEqual({x for x in h if x[0] == "curve"}, set())

    def test_namespace_must_be_in_scope(self):
        # `open` is read file-wide (an over-approximation: more resolution,
        # never less), so the unopened case lives in a file of its own.
        h = hits(run({**self.DEFS, "Demo/Else.lean": """
            namespace Elsewhere
            theorem unrelated (a r : ℝ) : gam a r = a := sorry
            end Elsewhere
            """, "Demo/Use.lean": """
            namespace Opened
            open Demo.Radial
            theorem opened (a r : ℝ) : gam a r = a := sorry
            theorem qualified (a r : ℝ) : Demo.Radial.gam a r = a := sorry
            end Opened
            """}))
        self.assertEqual({x for x in h if x[0] != "same_file"},
                         {("opened", "r (via gam)"), ("qualified", "r (via gam)")})

    def test_dot_notation_needs_the_receiver_type(self):
        h = hits(run({**self.DEFS, "Demo/Use.lean": """
            namespace Demo
            structure Neck where
              scale : ℝ
            theorem field (N : Neck) (c : ℝ) : N.scale = c := sorry
            theorem dot (F : FlowTo) (c : ℝ) : F.scale c = F.t / c := sorry
            end Demo
            """}))
        self.assertNotIn(("field", "c (via scale)"), h)
        self.assertIn(("dot", "c (via scale)"), h)

    def test_parameter_mapped_by_position(self):
        # `gam a r` divides by its SECOND argument. Matching by name read `r`
        # below as the divisor (constrained, so missed the real one, `s`).
        h = hits(run({**self.DEFS, "Demo/Use.lean": """
            namespace Demo.Radial
            theorem swapped (r s : ℝ) (hr : 0 < r) : gam r s = r / s := sorry
            theorem guarded (r s : ℝ) (hs : 0 < s) : gam s r * 0 = gam r s * 0 := sorry
            end Demo.Radial
            """}))
        self.assertIn(("swapped", "s (via gam)"), h)
        self.assertNotIn(("swapped", "r (via gam)"), h)
        self.assertEqual({x for x in h if x[0] == "guarded"}, {("guarded", "r (via gam)")})


class P9IfGuard(unittest.TestCase):
    def test_branch_excluding_zero(self):
        h = hits(run({"Demo/H.lean": """
            namespace Demo
            def hsn (q r : ℝ) : ℝ := if q = 0 then r else Real.sinh (q * r) / q
            def rho (r : ℝ) : ℝ := if r ≤ 0 then 0 else Real.exp (-1 / r)
            def sig (s : ℝ) : ℝ := if (4 / 3 : ℝ) ≤ s then 2 / s - 2 else -(3 / 8) * s
            def dq (h : ℝ) (v : ℝ → ℝ) : ℝ → ℝ := fun x =>
              if h = 0 then 0 else
                (v (x + h) - v x) / h
            def bad (q r : ℝ) : ℝ := if r = 0 then 1 else r / q
            theorem t1 (q r : ℝ) : hsn q r = hsn q r := rfl
            theorem t2 (r : ℝ) : rho r = rho r := rfl
            theorem t3 (s : ℝ) : sig s = sig s := rfl
            theorem t4 (h : ℝ) (v : ℝ → ℝ) : dq h v = dq h v := rfl
            theorem t5 (q r : ℝ) : bad q r = bad q r := rfl
            theorem t6 (q r : ℝ) : (if q = 0 then r else r / q) = r / q := sorry
            end Demo
            """}))
        self.assertEqual(h, {("t5", "q (via bad)"), ("t6", "q")})


class P2Transitive(unittest.TestCase):
    def test_one_step_order_chaining(self):
        h = hits(run({"Demo/T.lean": """
            namespace Demo
            structure Neck (δ : ℝ) where
              delta_pos : 0 < δ
            theorem le (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) : 1 / r = r⁻¹ := sorry
            theorem lt (s₁ s₂ : ℝ) (h1 : 0 < s₁) (h2 : s₁ < s₂) : 1 / s₂ = s₂⁻¹ := sorry
            theorem coeff (r L : ℝ) (hr : 0 < r) (h : 2 * r ≤ L) : 1 / L = L⁻¹ := sorry
            theorem nneg (a b : ℝ) (ha : 0 ≤ a) (h : a < b) : 1 / b = b⁻¹ := sorry
            theorem field (eps δ : ℝ) (N : Neck eps) (h : eps ≤ δ) : 1 / δ = δ⁻¹ := sorry
            theorem family (eps : ℕ → ℝ) (δ : ℝ) (N : ∀ n, Neck (eps n))
                (h : ∀ n, eps n ≤ δ) : 1 / δ = δ⁻¹ := sorry
            theorem inst (eps : ℕ → ℝ) (p : ℕ) (δ : ℝ) (O : ∀ i, Neck (eps i))
                (h : eps p ≤ δ) : 1 / δ = δ⁻¹ := sorry
            theorem inv (R δ : ℝ) (hR : 0 ≤ R) (h : R < δ⁻¹) : 1 / δ = δ⁻¹ := sorry
            theorem ctl_minus (l x r : ℝ) (hl : 0 < l) (h : x - l ≤ r) : 1 / r = r⁻¹ := sorry
            theorem ctl_nneg (a b : ℝ) (ha : 0 ≤ a) (h : a ≤ b) : 1 / b = b⁻¹ := sorry
            theorem ctl_coeff (x r L : ℝ) (hr : 0 < r) (h : x - 2 * r ≤ L) : 1 / L = L⁻¹ := sorry
            theorem ctl_ge (l δ : ℝ) (hl : 0 < l) (h : δ ≥ l - 1) : 1 / δ = δ⁻¹ := sorry
            theorem ge (l δ : ℝ) (hl : 0 < l) (h : δ ≥ l) : 1 / δ = δ⁻¹ := sorry
            end Demo
            """}))
        self.assertEqual(h, {("ctl_minus", "r"), ("ctl_nneg", "b"), ("ctl_coeff", "L"),
                             ("ctl_ge", "δ")})


class P7SelfGuardedDef(unittest.TestCase):
    def test_def_binders_and_prop_body(self):
        h = hits(run({"Demo/S.lean": """
            namespace Demo
            def scaleBy (c : ℝ) (hc : 0 < c) : ℝ := 1 / c
            def recog (d : ℝ) (k : ℕ) : Prop := 0 < d ∧ 2 * ⌊d⁻¹⌋₊ + 4 ≤ k
            def recogBad (d : ℝ) (k : ℕ) : Prop := 2 * ⌊d⁻¹⌋₊ + 4 ≤ k
            theorem a (c : ℝ) (hc : 0 < c) (x : ℝ) : scaleBy c hc = x := sorry
            theorem b (d x : ℝ) (k : ℕ) : recog d k = (x = x) := sorry
            theorem c (d x : ℝ) (k : ℕ) : recogBad d k = (x = x) := sorry
            end Demo
            """}))
        self.assertEqual(h, {("c", "d (via recogBad)")})


class CheapPatterns(unittest.TestCase):
    def test_p4_preimage_is_not_an_inverse(self):
        h = hits(run({"Demo/P.lean": """
            namespace Demo
            theorem pre (p q : ℝ) (f : ℝ → ℝ → ℝ) (S : Set ℝ) :
                f p q ⁻¹' S = f p q ⁻¹' S := rfl
            theorem ctl (p q : ℝ) : q⁻¹ = 1 / q := sorry
            end Demo
            """}))
        self.assertEqual(h, {("ctl", "q")})

    def test_p6_qualified_name_and_ascription(self):
        h = hits(run({"Demo/Q.lean": """
            namespace Demo
            theorem cot (u : ℝ) (hu : Real.sin u ≠ 0) :
                exp (u : ℂ) = (((-Real.cos u / Real.sin u : ℝ) : ℂ) - I) := sorry
            theorem proj (u : ℝ) (N : Foo) : N.scale⁻¹ = u := sorry
            end Demo
            """}))
        self.assertEqual(h, set())

    def test_p8_division_only_in_a_proof(self):
        h = hits(run({"Demo/E.lean": """
            namespace Demo
            def enlarge (C2 : ℝ) (W : Foo) : Foo := by
              have hinv : C2⁻¹ ≤ C2⁻¹ := le_rfl
              exact W
            def built (a : ℝ) : ℝ := by
              have h : 0 < 1 / a := sorry
              let k : ℝ → ℝ := fun t => 1 + t / a
              exact k 1
            theorem e1 (C2 : ℝ) (W : Foo) : enlarge C2 W = W := sorry
            theorem e2 (a : ℝ) : built a = built a := rfl
            theorem e3 (K x : ℝ) : x = x + (Classical.choose (by exact ⟨1 / K, trivial⟩)) := sorry
            end Demo
            """}))
        self.assertEqual(h, {("e2", "a (via built)")})


class NonzeroTokenBoundaries(unittest.TestCase):
    """Change 13: `0 < ε'` is a guard on ε'; `hr ≠ 0` is not a guard on r."""

    def test_primes_and_left_boundaries(self):
        h = hits(run({"Demo/N.lean": """
            namespace Demo
            theorem primed (ε' : ℝ) (h : 0 < ε') : 1 / ε' = ε'⁻¹ := sorry
            theorem prefixed (r hr : ℝ) (h : hr ≠ 0) : 1 / r = r⁻¹ := sorry
            theorem minus (x N : ℝ) (h : x - 1 ≤ N) : 1 / N = N⁻¹ := sorry
            theorem product (x r : ℝ) (h : x * r ≠ 0) : 1 / r = r⁻¹ := sorry
            theorem frac (ρ : ℝ) (h : 7 / 4 ≤ ρ) : 1 / ρ = ρ⁻¹ := sorry
            theorem frac2 (c : ℝ) (h : (1 : ℝ) / 2 ≤ c) : 1 / c = c⁻¹ := sorry
            theorem frac3 (s : ℝ) (h : (4 / 3 : ℝ) ≤ s) : 1 / s = s⁻¹ := sorry
            end Demo
            """}))
        self.assertEqual(h, {("prefixed", "r"), ("minus", "N")})


class P12EqualityFilter(unittest.TestCase):
    SRC = {"Demo/C.lean": """
        namespace Demo
        def cutoff (a b δ : ℝ) (x : ℝ) : ℝ := x / δ
        theorem smooth (a b δ : ℝ) : ContDiff ℝ ⊤ (cutoff a b δ) := sorry
        theorem compact (a b δ : ℝ) : IsCompact {x | cutoff a b δ x ≤ 1} := sorry
        theorem value (a b δ x : ℝ) : cutoff a b δ x = x / δ := rfl
        theorem unrelated (a b δ x y : ℝ) : y = y ∧ cutoff a b δ x ≤ 1 := sorry
        end Demo
        """}

    def test_mode2_applies_the_equality_filter(self):
        h = hits(run(self.SRC))
        self.assertEqual({x[0] for x in h}, {"value", "unrelated"})

    def test_all_conclusions_keeps_old_behaviour(self):
        rows = run(self.SRC, all_conclusions=True)
        hint = {(r["decl"].split(".")[-1], r["denominator"]): r["class_hint"] for r in rows}
        self.assertEqual(hint[("smooth", "δ (via cutoff)")], "property")
        self.assertEqual(hint[("compact", "δ (via cutoff)")], "property")
        self.assertEqual(hint[("value", "δ (via cutoff)")], "exact-value")
        # an equation that does not mention the quantity is not an exact value OF it
        self.assertEqual(hint[("unrelated", "δ (via cutoff)")], "property")

    def test_cli_flag_and_columns(self):
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "Demo"))
            with open(os.path.join(root, "Demo/C.lean"), "w", encoding="utf-8") as fh:
                fh.write(textwrap.dedent(self.SRC["Demo/C.lean"]))
            out = os.path.join(root, "out.csv")
            for flag, n in (([], 3), (["--all-conclusions"], 5)):
                p = subprocess.run([sys.executable, os.path.join(AUDITS, "junkvalue.py"), root,
                                    "-o", out, *flag], capture_output=True, text=True)
                self.assertEqual(p.returncode, 0, p.stderr)
                with open(out, encoding="utf-8") as fh:
                    rows = list(csv.DictReader(fh))
                self.assertEqual(len(rows), n)
                self.assertEqual(list(rows[0]),
                                 ["file", "line", "decl", "denominator", "class_hint", "statement"])


class AblationRestoresBaseline(unittest.TestCase):
    """Every change can be switched off; all of them off is the old scanner.
    (On differential-geometry @ 7a48598d that reproduces the 617-row CSV
    exactly, which is how the per-change effects in the docstring were read.)"""

    def test_ablating_everything_brings_back_the_false_positives(self):
        src = {"Demo/H.lean": """
            namespace Demo
            def hsn (q r : ℝ) : ℝ := if q = 0 then r else Real.sinh (q * r) / q
            theorem t1 (q r : ℝ) : hsn q r = hsn q r := rfl
            theorem le (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) : 1 / r = r⁻¹ := sorry
            end Demo
            """}
        self.assertEqual(hits(run(src)), set())
        allx = frozenset("P1 P2 P3 P4 P6 P7 P8 P9 P12 NZ".split())
        self.assertEqual(hits(run(src, ablate=allx)),
                         {("t1", "q (via hsn)"), ("le", "r")})


if __name__ == "__main__":
    unittest.main()
