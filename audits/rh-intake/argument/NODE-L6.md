# NODE-L6: the lower bound on the theta-lift scalars λ_j

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `LTD/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/`
- `DP/` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`
- `FDU` = `Development/AbelianVarietyTheory/Definitions/Divisors/FormalDegreeUpperC.lean`
- `IPF` = `DP/InnerProductFormula.lean`; `ACI` = `DP/AdelCOfInnerProductFormula.lean`
- `RLK` = `Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/RealLowestKTypeCoeffSquareIntegrable.lean`
- `ECL` = `TPS/EveryCharacterOfLiteratureOfVWin.lean`

## 0. Verdict (short)

- **What λ_j is.** λ_j is the **Rallis inner-product scalar**. It is the eigenvalue l > 0 by which θ∘θ* acts on a Hecke-type part
  of the target forms (`AdelC`, `FDU:47-50`; `PThmA`, `Formalism/LocalToGlobal/IndefiniteReal/LinksLemmas.lean:265-266`).
  It is not the constant c of `ThetaIntegralsAgree`.
- **The formula is exact.** For that scalar the Lean proves an exact product formula (`ACI:59-62`):

  l = ∏_ρ dim K-type · dim(c.W) · vol(ν,𝓕) · ∏_ρ hook(p,a⁺)·hook(q,a⁻) · ‖f‖² / d^S
      · ∏_ρ ∫|⟨v, π_ρ(g)v⟩|² dg · |L^S|.

  Here L^S is a partial Euler product with Satake parameters at s₀ = (1+t)/2, and d^S = ∏_{v∉S} ∏_{i=t+1}^{nV} (1 − χ_v^i q_v^{−i})^{−1}.
- **Only the hook products are kept as the main term.** They enter exactly: `DeltaNorm` is the Fock norm of the
  highest-weight vector δ, and `hook_term`/`sum_logHook_eq` identify it with logHook. Every other factor is bounded
  crudely, by exp(±O(r f)), by 1/(2^{nV} nV!), or by the Harish-Chandra formal degree with loss r² log(…).
  All of these go into 8·f·nV²·Lp (`numeric_bound`, `DP/FormOfClassSums.lean:126-136`).
- **Regime.** The L-value is evaluated **deep in the absolutely convergent range**, so its lower bound is elementary:
  - each local parameter satisfies |x| ≤ N(w)^{(r−1)/2 − (1+t)/2} ≤ N(w)^{−3}, using t ≥ r+5 (`Ranks.rank_add_five_le`);
  - this gives |L^S| ≥ exp(−2 r f) (`eulerOff_lower`, `DP/IntegralEqClassSumOfHom.lean:212-224`).
  - Nothing GRH-strength is involved.
- **Precision.** The loss is ≈ f·nV²·Lp ≈ x^{4.5}·x^{797}·x^{ε} = poly(x). The budget is x^3·b with b = e^{x^ε}, so the
  loss is negligible eventually in x. The relative-x^{−4} requirement holds with enormous room.
- **Judgement: yes**, proved from recognisable mathematics (Rallis inner product formula, Harish-Chandra formal degree,
  Euler product in its convergent range). It is conditional on seven named literature theorems, all supplied on the root
  path by closed in-tree theorems. Several sub-suppliers were not opened (§3).

## 1. Statement

`LambdaLowerBound₂` (`TPS/Realised.lean:126`):

  `Closed FamHyp fun Fm CH => EventuallyAtPoints Fm fun _ _ _ p => ∀ C, (p.S true).L6 (p.N C CH)`

`IndefData.L6` (`IS:325-326`): `∀ j p v, N.l6 j ≤ Real.log (S.lam j Bs.μ0 p v)`.

What λ = S.lam is (`RowLatticeBoundForBasis`, `IS:310-317`): λ_{j,t,p,v} > 0, and θ_j is a λ-similitude on Zpart(j,t,p)
for the archimedean majorants: maj_{XW_j,v}(θx, θy) = λ·maj_{XT_j,v}(x, y).

On the live path λ = `lam3`, and the Lean pins it down at three kinds of point:
- **at the base place v₀:** for x ∈ Wp3 j p, θθ*x = λ·x (`PThmA`);
- **at v ≠ v₀:** by Galois conjugation of the rational lift (`GalOut`, `FDU:85-93`; `LowForm`,
  `Development/AbelianVarietyTheory/Definitions/Divisors/RealisedChainTorusEq.lean:103-107`);
- **on an empty part:** λ is *defined* to be exp(l6m) (`zero_part_eigenvalue_convention`, `scal_abs`,
  `Formalism/LocalToGlobal/IndefiniteReal/ZeroPartEigenvalueConvention.lean:210-213`).

In mathematics, for every family in the closed class, eventually in x, at every point, for all j < m, every Hecke type p
and every infinite place v:

  log λ_{j,p,v}  ≥  Σ_{ρ ∈ Tau} logHook(k+j, a⁺_{j+1,ρ})  −  Csz · f · nV² · Lp,    with Csz ≥ 8.

The terms are as follows.
- **logHook** (`Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean:9-11`):

  logHook(n, a) = Σ_{i<n} log Γ(a_i + n − i) − Σ_{i<l<n} log(a_i − a_l + l − i).

  For a partition a with n rows this is log ∏_i ℓ_i! − log ∏_{i<l}(ℓ_i − ℓ_l) with ℓ_i = a_i + n − 1 − i. That is the
  **hook-length product** H(a) = |a|!/dim S^a. `hook_term` (`DP/HookLogSumSubSizeTermLeLowerBound.lean:38-75`) proves it
  equals log `hookOf` for the antitone weight a⁺ = aPl. On the parent side, `Numbers.lean:245` writes it as log hookProd(apDiag).
  `sum_logHook_eq` (`:78-89`) proves Σ_ρ logHook = `hookPlus` (`DP/TypePartBase.lean:39-40`).
- **Lp** = log(b · rd_E · g₀ g₁ · nV) (`Formalism/LocalToGlobal/Divisibility/Numbers.lean:72`; `Lpr`/`Lp`). It is ≈ x^ε.
- **The ranks** (`Formalism/LocalRingCardinality/Params.lean:6-46`): r = k+m−1, nV = r+t, f = 2·ord ≤ k, t ≥ r+5.
  The rank of V is r. The doubling normaliser runs over i ∈ (t, nV].
- **The rows:** p = k+j rows on the plus side and q = m−j rows on the minus side (`sigW`).

How the parts fit together:
- `IndefScale.num` (`IS:229`) has l6 = l6m − C·l6u.
- `lamLow_of_hypotheses_alt_alt` (`TPS/LamLowOfPublished.lean:18-35`) proves L6 with the realised `F.Zsc`, whose l6m is
  Σ logHook − Csz f nV² Lp.
- The `C·l6u` slot is 0 there (`show _ - C * 0 ≤ _`, `:33`).

## 2. Argument

1. **Rallis scalar at v₀** (`adelC_of_innerProductFormula`, `ACI:249-257`; `scalar_of_form_key_lowC`, `:214-245`).
   - For x in the type part typePart(i, σ, t, P, ev) ≠ ⊥, θ(θ*x) = l·x.
   - l is computed by expanding ⟨θ*U₁, θ*U₂⟩ with the following ingredients:
     - unfolding (`InnerProductFormulaC`, `IPF:110-129`), in which the doubling-type integral is ν(𝓕)·∫∑ over cosets × the real group;
     - `FockCoefficientC` (`RLK:125-135`): the Weil-representation coefficient of the Fock test vector factors as
       fock(δ,δ) · ∏_ρ⟨e′, π_ρ(g)e⟩ · ⟨w′,w⟩ · (finite coefficient);
     - `DeltaNorm` (`IPF:147-149`): fock(δ,δ) = ∏_ρ hook(p,a⁺)·hook(q,a⁻), **exact**;
     - `FiniteZetaC` (`FDU:58-68`): the finite coset sum equals |P.H| · ‖f‖² · L^S(x)/d^S. The Satake-type parameters satisfy
       |x_{w,a}| ≤ N w^{(r−1)/2−(1+t)/2}. The source is `FiniteZetaL` (`RLK:139-153`): an L^S value at s = (1+t)/2 with
       parameters ≤ N^{(r−1)/2}, which is the trivial bound;
     - `LevelIndexNormC` (`RLK:155-159`): index · ‖f‖² = ∏_{v∈S} d_v^{−1}, **exact**;
     - `MassLower` (`IPF:176-178`): mass ≥ 1/(w_E^{nV} nV!);
     - `FormalDegreeUpperC` (`FDU:71-82`): log(∫|⟨e, π(g)e⟩|²)^{−1} ≤ 2 + r² log(2√2 r² nV (deg+2)), from the
       Harish-Chandra formula.
2. **Numeric step** (`scalar_bound_lowC`, `ACI:52-88`). It takes logs and applies `numeric_bound`:
   - log dimK ≥ 0 and log dim ≥ 0;
   - |L^S| ≥ e^{−2rf} (`eulerOff_lower`);
   - d^S and ∏ d_v are ≤ e^{4rf} (`dOff_bound`, `dLoc_bound`: |χ q^{−i}| ≤ q^{−2}, summed);
   - the mass and formal-degree bounds above.
   The result is log l ≥ mainTerm − 8 f nV² Lp, with mainTerm = Σ_ρ[logHook(p,a⁺) + logHook(q,a⁻)] (`LiftFormsMainTerm.lean:41-43`).
3. **Base place** (`l6m_le_log_lam3_base_place`, `DP/LogLiftEigenvalueLowerBoundBasePlace.lean`).
   - `lowB` = hookPlus − 8 f nV² Lp (`RealisedChainTorusEq.lean:95-96`) ≤ mainTerm − 8 f nV² Lp, because the q-side hooks
     are ≥ 0. That side is dropped.
   - `LowTop` then gives lowB ≤ log λ at v₀.
4. **Other places** (`l6m_le_log_lam3_other_places`, `DP/LogLiftEigenvalueLowerBoundOtherPlaces.lean`).
   `LowForm` with Galois conjugation (`ConjRatLift5`/`GalOut`) gives e^{lowB}·maj_v(x,x) ≤ ‖w_v‖² = λ·maj_v(x,x).
5. **Matching to the accounting** (`main_le_lowB`, `DP/HookLogSumSubSizeTermLeLowerBound.lean:91-104`).
   Σ logHook − Csz f nV² Lp ≤ lowB for Csz ≥ 8, because Σ logHook = hookPlus exactly.

### Which parts are exact and which are bounds

| factor | kind | loss in log |
|---|---|---|
| hook(p, a⁺) (main term, ≈ k·f·b·x^ε) | **exact identity** (`DeltaNorm`, `hook_term`, `sum_logHook_eq`) | 0 |
| hook(q, a⁻) (minus side, q ≤ m rows) | dropped, since ≥ 0 | conservative; ≈ m·b·x^ε at most (my estimate) |
| index·‖f‖² vs ∏ d_v | exact identity, then d ≤ e^{4rf} | ≤ 4rf |
| L^S(s₀), s₀ − (r−1)/2 ≥ 3 | bound (convergent Euler product) | ≤ 2rf |
| d^S normaliser | bound | ≤ 4rf |
| unitary mass | bound | ≤ nV log(w_E nV) |
| formal degree (Harish-Chandra) | bound | ≤ f(2 + r² log(r² nV deg)) |
| dimK, dim, vol(𝓕) | ≥ 1, or absorbed | ≤ 0 |

All of these losses are ≤ 8 f nV² Lp ≈ x^{802+ε}. That is poly(x) ≪ x^3·b = x^3 e^{x^ε}, but only eventually in x.

### The regime

- t ≈ x^{398.5} ≫ r ≈ x^{4.5}, so s₀ = (1+t)/2 lies about x^{398}/2 to the right of the edge (r−1)/2 of absolute convergence.
- The L-value is 1 + O(2^{−x^{398}}) in truth. The Lean uses only the crude bound e^{−2rf}.
- No critical-strip L-value is involved anywhere in L6.

### Nonvanishing

- AdelC gives l > 0 with θθ* = l on typePart. So θ* is injective on that part, and θ maps onto it.
- RowLatticeBoundForBasis therefore makes each θ_j a nonzero-scale similitude on Zpart, hence injective on the relevant forms.
- What it does not give is that the parts are nonzero. typePart ≠ ⊥ is a hypothesis, and an empty part gets λ := e^{l6m}
  by convention.
- So L6 makes each step injective on its part, but does not by itself make the iterated lift nonzero. That still needs the
  type parts to be nonempty and the starting vector to lie in them (cf. NODE-GLOBALCHAIN "nonvanishing").

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `adelC_of_siegelWeil_of_doubling_alt` | `LTD/FinitenessInputsRealData.lean:13-28` | the 7 premises plus the parameter choice and StdV give AdelC | core (assembly) |
| 2 | `twistedThetaLift_innerProductFormula_of_hypotheses` (hCusp, hWS, DM) | not opened | InnerProductFormulaC (unfolding of ⟨θφ,θφ⟩) | core, Rallis inner product formula, **not opened** |
| 3 | `finiteZetaIntegral_eulerProduct_of_partialL`, `finiteZetaIntegral_thetaLift_eq_partialLValue` (hCusp, hBZ, hUnr) | not opened | FiniteZetaC: finite doubling zeta = L^S/d^S with bounded parameters | core, standard (PS–Rallis unramified computation); **not opened** |
| 4 | `formalDegreeRealPlaceUpperBound_of_harishChandra` (hFD) | not opened | FormalDegreeUpperC | standard (Harish-Chandra) |
| 5 | `fockVector_matrixCoefficient_formula`, `deltaNorm_all` | `DP/FinitenessInputsRealData.lean:44` | FockCoefficientC; DeltaNorm (hook norm of δ) | core: this is where the exact main term comes from; **body not opened** |
| 6 | `thetaLevelIndex_mul_schwartzNorm_formula`, `unitaryMassLowerBound_of_orthonormalLatticeFrames` | not opened | LevelIndexNormC; MassLower | standard |
| 7 | `scalar_bound_lowC`, `numeric_bound`, `eulerOff_lower`, `dOff_bound` | `ACI:52`; `FormOfClassSums.lean:126`; `IntegralEqClassSumOfHom.lean:212-252` | numeric bounds | glue, proved |
| 8 | `conjugatesOfRationalThetaLift_from_characterisation` (ConjRatLift5) | not opened | Galois conjugation of the rational lift to v ≠ v₀ | core for v ≠ v₀ |
| 9 | `hook_term`, `sum_logHook_eq`, `main_le_lowB` | `DP/HookLogSumSubSizeTermLeLowerBound.lean:38-104` | hook-length identity | glue, proved |

The seven `Published.*` premises, with their in-tree suppliers on the root path (the `O` argument is ignored;
`ECL:265-541`, fields at `ECL:675-681`):

| premise | statement (one line) | closed supplier |
|---|---|---|
| CuspRapidDecay | smooth, moderate-growth cusp forms on U(V)(𝔸) decay rapidly (`.../AutomorphicForms₂/ExistsNormLeHeightPow.lean:28`) | `GlobalTheory.RapidDecay.cuspRapidDecay` |
| WeilSiegelFormulaUnitary | Weil convergence when wittIdx B = 0 or rk A + witt < rk B; Siegel–Weil (Eisenstein sum = theta average) when 2 rk A < rk B (`.../TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:56`) | `UpperTheory.Lit.Sw47.weilUnitary` |
| SiegelWeilUnitaryConvergent | Siegel–Weil in the convergent range for Fock vectors (`.../SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18`) | `UpperTheory.Lit.Sw47.convergent`. **Unused** on this path (`_hSWc`) |
| DoublingMethodLocalZetaIntegrals = `ResidueKilled.DM` | Siegel Eisenstein series continue with finite-order poles; doubling basic identity for Re s > rk/2; zeta continues (`.../DmOfHyp.lean:13`) | `ResidueKilled.dm_of_two` (cuspRapidDecay, `PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation`, trivial) |
| UnramifiedDoublingGL | unramified GL_n doubling integral = L(s+½,π)L(s+½,π^∨)/d_n(s) for Re s ≫ 0 (`.../PairwiseDisjointCell.lean:314`) | `GlobalTheory.UnramDoublingProof.unramifiedDoublingGL` |
| BernsteinZelevinskyFiniteness | irreducible ⇒ admissible; Jacquet modules and inductions have finite length; contragredient of an induction (`.../HasFiniteLengthOfIsIrreducible.lean:49`) | `PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds` |
| FormalDegreeCompactDual | Harish-Chandra: d(π_λ) = ∏_{a<b}\|λ_a−λ_b\|/∏_{a<b}(b−a) for the compact-dual Haar measure (`.../FormalDegreeCompactDualIff.lean:8`) | `PositivityTheory.RgFd.B.formalDegreeCompactDual` |

None of these looked stronger than the published theorem it is named after. The ranges match Weil's: m > 2n for
U(n,n) × U(m) Siegel–Weil, and "∃ s₀" for the unramified computation. I did not open the suppliers' proofs.

## 4. Oddities

1. **Empty parts.** λ is *defined* as exp(l6m) where the part is ⊥ (`ZeroPartEigenvalueConvention.lean:210-213`), so L6
   holds there by convention. This is harmless for the norm comparison, since there are no vectors, but it means L6 does
   not assert any nonvanishing.
2. **The q-side hook is discarded.** `lowB` uses `hookPlus` only, while the proved bound has both hooks. This is
   conservative for a lower bound. If the accounting needed the q-side hook to cancel something, it is lost; I did not
   see it being needed.
3. **The L-value factor is wasted.** The L-value is evaluated at an absurdly convergent point and bounded by e^{−2rf},
   though it is 1 + o(1). This is harmless.
4. **"Eventually" carries real weight.** The loss f nV² Lp ≈ x^{802} is below x^3 e^{x^ε} only for astronomically large
   x. That is legitimate inside `EventuallyAtPoints` / `Closed`.
5. **A premise is passed but unused.** SiegelWeilUnitaryConvergent is a premise of the theorem but is never used.
6. **λ is not the ThetaIntegralsAgree constant c.** It is the Rallis θθ* eigenvalue. There is no tower relation between
   b+2 and b here.

## 5. Coverage

Read:
- `TPS/LamLowOfPublished.lean` (all); `TPS/Realised.lean:100-160`; `IS:180-330`;
- `LTD/FinitenessInputsRealDataThree.lean` (all); `LTD/FinitenessInputsRealData.lean:1-40`;
- `FDU` (all); `RealisedChainTorusEq.lean:80-120`; `IPF:1-180`; `ACI:52-132, 214-259`; `RLK:120-175`;
- `LiftFormsMainTerm.lean:1-80`; `TypePartBase.lean:20-70`;
- `DP/LiftEigenvalueLowerBoundOfWeakCharacterisation.lean`; `DP/LogLiftEigenvalueLowerBound{BasePlace,OtherPlaces}.lean`;
- `DP/HookLogSumSubSizeTermLeLowerBound.lean:30-104`; `IntegralEqClassSumOfHom.lean:205-252`; `FormOfClassSums.lean:120-150`;
- `Params.lean:1-46`; `KernelPlaceMeanBound.lean:1-30`; `ZscOfNum.lean:55-75`; `ZeroPartEigenvalueConvention.lean:205-230`;
- `LinksLemmas.lean:262-272`;
- the seven Published definitions; `DmOfHyp.lean:1-40`; `SurjectiveAndLowWeightOfUnramifiedExponents.lean:15-35`;
- `ECL` (the supplier lines).

Not opened:
- the bodies of children 2–6 and 8, including the proofs of the Rallis inner product formula, the finite zeta = L^S
  identity with its parameter bound, the Fock/hook norm of δ, and Galois conjugation;
- the proofs of the Published suppliers.
