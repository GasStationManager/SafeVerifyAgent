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
