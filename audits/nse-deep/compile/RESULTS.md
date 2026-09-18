# Targeted `lake env lean` verification results

Run under the "no full build, per-file checks only" constraint, against the 1,264 NSE modules +
8,758 Mathlib oleans already built. NSE source never modified (`git status` verified empty).

| check | file | result |
|---|---|---|
| E-A4 sample (3 files) | `Flatness`, `StressAlgebra`, `JetBounds` | **PASS** — exit 0, 0 errors under `-DautoImplicit=false -DwarningAsError=true` |
| P5b redundant guards | `p5b_check.lean` | **VERIFIED** — exit 0 |
| P8 filter vacuity | `p8_check.lean` | **VERIFIED** — exit 0 |
| junk-value collapse | `p8_check.lean` | **VERIFIED** — exit 0 |

## What each one now establishes, by kernel rather than by reading

**P5b — the redundant `field_simp` guards are genuinely redundant.** `p5b_check.lean` restates two
`StressAlgebra` identities with the guards *removed* and both compile:
`lag_no_hphi` drops `hphi : phi <> 0` entirely, and `angular_no_hR_hL` drops **both** `hR` and `hL`,
retaining only `hE`. Each needs one `rcases eq_or_ne _ 0` and then the original `field_simp; ring`.
The audit had derived this by hand; it is now checked.

**P8 — filter vacuity is real.** `powerFlat_bot_any` proves
`NavierStokes.Flatness.PowerFlat (⊥ : Filter alpha) q f` **for arbitrary `q` and `f`**, discharged by
`⟨0, le_refl 0, by simp⟩`. So every `PowerFlat` claim is vacuously true at the bottom filter, exactly as
predicted — and the guard's correct placement at `BlowupImplication.lean:78,95` (`[NeBot l]`) is what makes
this benign.

**The junk-value collapse is real, and wider than stated.** `rhs_zero_at_b_zero` proves the right-hand side
of `integral_gaussian_scaled` is `0` at `b = 0`, and `rhs_zero_of_b_neg` proves it is `0` for **every**
`b < 0` (via `Real.sqrt_eq_zero_of_nonpos`). The audit had asserted both; both are now checked.

## What is NOT reachable under this constraint
`#print axioms` on the headline theorems. `NavierStokes/ComparatorSolution.olean`,
`Euler/Solution.olean` and `NavierStokes/ComparatorR3Theorem.olean` are **not built** — they sit at the top
of the import tree and the full build was stopped at 1,264 of ~2,659 modules. Axiom provenance for the
headline results therefore remains **unverified by this audit**; see the blockers section of the report.
