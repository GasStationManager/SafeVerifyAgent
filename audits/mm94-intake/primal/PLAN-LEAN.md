# Formalising the a₀ = 2 primal construction on top of the artifact

Target (Lean, on top of `openai/math` commit `adc7f1241`, files in `lean/Audit/Primal/`,
untracked, no artifact file modified):

  theorem two_cat_degeneration (N : ℕ) (hN : 420 ∣ N) :
    DegClass (5^258 * Cat N * S 2 2 ^ (15*N) * matrixClass 2 ^ (68*N))
             (Cat N * matrixClass 2 ^ (30*N) * matrixClass (M₁ N) ^ 40 *
                      matrixClass (M₂ N) ^ 28 * matrixClass (M₃ N) ^ 18)
  theorem exactRankExponent_le_primal_two : exactRankExponent ≤ 3 * log 3 / log (10/3)

where `TensorClass` is the artifact's semiring of tensors modulo mutual restriction,
`S a b := ∏_{π ∈ S₃} classOf (C(a,b)^π)`, `M₁ = C(N, 7N/10)`, `M₂ = C(N, 9N/14)`,
`M₃ = N!/((N/3)!)³` (as `Fintype.card (ExactWords counts)`), and `DegClass c d` means some
representatives are related by a `PolynomialRestrictionDegeneration` (degree-tracked, so
Bini's interpolation applies).

## Files and milestones

| file | content | status |
|---|---|---|
| `Deg.lean` | `Deg` (∃ PRD), `Approx` (∃ PolynomialApproximation); closure: refl, of_restrict, trans, product, power, cyclic, swapYZ, pullback; `Deg.toApprox` (compose), `Approx.rank_power` | M1 |
| `Classes.lean` | `DegClass`, `ApproxClass` on `TensorClass`; well-definedness, mul, pow, trans; `classOf_power`; `sym6` and its class `S`; identities S(1,b) = matrixClass b², S(a,b) = S(b,a), permutation invariance; scalar copies = natCast | M2 |
| `Separation.lean` | Prop 3.1 as a PRD: shifted (nonnegative) weight maps, identity with X^c · separationPolynomial by agreement at all t ≠ 0 | M3 |
| `Steps.lean` | single-factor E step: `Deg (⟨5M⟩ ⊗ (C(a,b) ⊗ B_X(2))^{⊗N}) (⟨M⟩ ⊗ B_X(M) ⊗ C(a,b+1)^{⊗c₊} ⊗ C(a,b−1)^{⊗c₋})` up to reindexing; single-factor F step likewise; class-level E and F | M4 |
| `Two.lean` | the a₀ = 2 assembly by `ring` in `TensorClass`; catalyst iteration; rank bound via `rank_power`; the exponent limit | M5 |

Dependencies: M1 → M2, M3, M4 → M5. M2 and M3 are independent of each other.

## Artifact lemmas relied on (all already proved there)
`Tensor.PolynomialRestrictionDegeneration` (+ `cyclic`, `compose`),
`Tensor.PolynomialApproximation` (+ `product`, `pullback`, `cyclic`, `restrict`, `power`,
`rank_power`, `ofRankAtMost`), `DeterminantFiltration.degeneration`,
`sourceTensor_coordinate_change`, `sourceTensor_product`, `Sector.restriction`,
`retained_eq_three_branches`, `branchFamily_labels`, `sharedFirstTensor_pullback_labels`,
`exactType_power_pullback`, `separationPolynomial_eval`, `separationPolynomial_coeff_zero`,
`separationPolynomial_degree`, `separationTarget_eq_directSum`,
`pairingTriple_matrixCoefficients`, `matrixClass_mul`, `matrixClass_pow`, `classOf_product`,
`classOf_directSum`, `classOf_reindex`, `rank_mul_le`, `exactRankExponent_le_logb`,
`convolution` rank ≤ a+b−1, `ComplexTypeEntropy` multinomial bounds.

## Status (2026-10-09)

Built and checked on the artifact checkout (`openai/math` at `adc7f1241`, Lean 4.34.1, the
artifact's own Mathlib), as files added under `lean/Audit/Primal/` (copies in `lean/` here);
no artifact file is modified. Every statement compiles; proofs were written by twelve Opus
workers (two or three per file, on private copies) and merged. `#print axioms` on each headline theorem:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

| file | lines | content | status |
|---|---|---|---|
| `Deg.lean` | 500 | `Deg`/`Approx`; refl, of_restrict, of_pullback, trans, product, power, cyclic, swapYZ; `toApprox`, `rank_power` | proved |
| `Classes.lean` | 428 | `DegClass`/`ApproxClass` on `TensorClass`; `sym6class`, `S a b`, `dotX`; permutation invariance, product/power/copies, `sym6class_dot`, `S_one`, `S_comm`, `rank_S_le`, monotonicity, `DegClass.sym6` | proved |
| `Separation.lean` | 260 | Prop 3.1 as a `PolynomialRestrictionDegeneration` of order `2M² − M` (shifted weight maps, identity with `X^c · separationPolynomial` by agreement at all `t ≠ 0`); `deg_separation` | proved |
| `Steps.lean` | 418 | shared-first sums, word tensors of an exact type, the separated target as a class, the symmetrised separation round; Lemma 4.1 (`deg_filtration`) and Lemma 4.2 (`deg_sector`) as single-leg degenerations; `Estep`, `Fstep` | proved |
| `Two.lean` | 553 | `two_cat_degeneration` (the a₀ = 2 certificate as a catalytic degeneration), `exactRankExponent_le_of_catalytic` (Bini + catalyst removal), `exponent_le_logb` (ν ≤ log_{B_m} rank L_m for every m ≥ 1), rank monotonicity, the slack lemma; multinomial entropy bounds and the bootstrap limit `exactRankExponent_le_primal_two` | proved |

The two statements that matter, as they stand in `Two.lean` (`N = 210 m`):

```
theorem two_cat_degeneration (m : ℕ) :
    DegClass (Cat m * L m) (Cat m * matrixClass (B m))
  -- Cat m = ⟨M₁^120 M₂^84 M₃^54⟩ · S 2 3^(14N) · S 2 4^(9N) · S 2 2^(5N)
  -- L m   = 5^258 · S 2 2^(15N) · matrixClass 2^(68N)
  -- B m   = 2^(30N) · M₁^40 · M₂^28 · M₃^18,  M₁ = C(N,.7N), M₂ = C(N,9N/14), M₃ = N!/((N/3)!)³

theorem exponent_le_logb {m : ℕ} (hm : 1 ≤ m) :
    exactRankExponent ≤ Real.logb (B m) (rank (L m))
```

Both check with the standard axioms only (`#print axioms` output in `AXIOMS.txt`).
The bootstrap on the `matrixClass 2^(68N)` factor (Schönhage: for every τ > ν there is a
fixed `u` with `R(n) ≤ (u n)^τ`), the entropy lower bounds on `M₁, M₂, M₃` from the
artifact's `abs_log_multinomial_sub_entropy_le`, and the limit `m → ∞` give

```
theorem exactRankExponent_le_primal_two :
    exactRankExponent ≤ 90 * Real.log 3 / (β - 68 * Real.log 2)
  -- β = 30 log 2 + 40 H(7/10) + 28 H(9/14) + 18 log 3;  numerically 2.7375
```

All of it is proved: `exactRankExponent_le_primal_two` depends on `[propext, Classical.choice,
Quot.sound]` only (`AXIOMS.txt`, final section). Numerically the right-hand side is 2.7375
(β = 83.252, β − 68 log 2 = 36.118, 90 log 3 = 98.875).

### Rebuilding

```
cd <openai-math checkout>/lean && export PATH="$HOME/.elan/bin:$PATH"
mkdir -p Audit/Primal && cp <this dir>/lean/*.lean Audit/Primal/
for f in Deg Classes Separation Steps; do
  lake env lean -o .lake/build/lib/lean/Audit/Primal/$f.olean \
    -i .lake/build/lib/lean/Audit/Primal/$f.ilean Audit/Primal/$f.lean
done
lake env lean Audit/Primal/Two.lean      # ~1 min; then #print axioms as in AXIOMS.txt
```

(`lake env lean` only accepts files under the lake root; imports need the `.olean`s above.)

### What the formalisation does and does not say

- It proves, inside the artifact's own definitions, that the explicit tensor chain of
  `PRIMAL.md` §4 exists as a degree-tracked degeneration, and that it bounds the artifact's
  `exactRankExponent` (the exponent of exact rank of `⟨n,n,n⟩`, which the artifact's
  `Main.lean` relates to ω). The degenerations are the artifact's (`DeterminantFiltration.
  degeneration`, `Sector.restriction`, `separationPolynomial`); the shifted leg maps of
  `Separation.lean`, the class-level symmetrisation and the catalyst/Bini/Schönhage
  bookkeeping are new.
- It does NOT improve on the paper: 2.7375 is the paper's own a₀ = 2 intermediate bound,
  made primal. The a₀ → ∞ limit (9/4) is not formalised; each a₀ would be one more LP
  certificate assembled the same way (`Estep`/`Fstep` are stated for all `a, b, h, counts`).
- Numeric evaluation of `90 log 3 / (β − 68 log 2)` to a decimal is not formalised beyond
  `beta_sub_pos` (positivity of the denominator with crude log bounds).
