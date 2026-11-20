# NODE-HS: the Hilbert–Samuel package behind `UAt` / `LowAt`

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `HBW/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/`
- `DP/` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
- `CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`
- `MB/` = `Development/WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/`
- `HSS` = `GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsArith.lean`

## 0. Verdict (short)

1. **The published, asymptotic theorems are not where HSAt comes from.**
   - `ArithHilbertSamuel` is a faithful rendering of the nef arithmetic Hilbert–Samuel theorem for small sections
     (Gillet–Soulé / Zhang / Moriwaki). It is stated with real Mathlib schemes, it is per variety, and it uses `=o[atTop]`.
   - `HSUse` (ArithKleiman ∧ G7 ∧ ArithmeticVolumeNef) has the same per-variety asymptotic shape.
   - **Neither is used to prove `HSAt`.** `ArithHilbertSamuel` (`PublishedHodgeBundleTheorems.q9`) is consumed elsewhere.
     `HSUse` enters only through `DeepStR`, which feeds `HeightAt`, not `HSAt`.
2. **HSAt is route (i): an effective, finite-level theorem proved in the tree.**
   - It is `GeoBound`/`SlopeBound` (`HermSysHypOneLeLambdaZero.lean:243-293`).
   - Shape: if a section ring has short spanning families in degrees 0, D and T, plus a Bergman/multiplication bound β
     and a frame bound Λ, then the arithmetic degree of the degree-T section lattice satisfies an explicit inequality
     `HSClaimS 26 …` (`HSClaim.lean:16-22`).
   - It is applied at one tensor power, lenT = ⌈PP²·dim²·k/m⌉ (`CXC:44`). There is no n → ∞ limit.
   - `SlopeBound` is proved with no hypotheses (`SlopeLowerBoundTopLatticeOffHypersurfaceStatement.lean:8`).
3. **Route (iii) also applies: the size of "the error" is fixed by definition.**
   - unitE = B0·log log x (`ZON:66`), with B0 = f·m·b·x^ε (`Divisibility/Numbers.lean:74`;
     `DataParams₂.lean:228` with `DataArith.lean:198-200`), and b = exp(x^ε) (`DataParams₂.lean:29`).
   - So the "additive B0·log log x" error is **≥ f·m·e^{x^ε}·x^ε·log log x**. It is not small in absolute terms.
   - `SizeAt` requires b ≤ unitE (`CXC:75`), and this is proved (`SizeBoundStatement.lean:260`).
   - HSAt's error constants are R = 4000·b + 2·Cp·zBase² and A = 26(26·dim² + 2·zed·lenT)
     (`TPS/HilbertSamuelLowerBoundOfComponents.lean:89-90`). They are absorbed because unitE ≥ b.
4. **Where uniformity across the varieties really sits: `DeepStR` → `VolumeTheoremX`.**
   - `VolumeTheoremX` (`.../TowerExistence/GoodTowerExistsX.lean:28-36`) states: there is **one C** for all abelian CM
     fields E, hosts, data, levels and towers, with `MeanSlope II C (hostRd E) (hostLval H)`.
   - That is a uniform arithmetic-volume (Kudla / Bruinier–Burgos–Kühn type) lower bound for the mean slope of
     unitary Shimura varieties of every signature. For general signature it is not a published theorem.
   - Its proof (`final_theorem_of_inputs_right`) was not opened.

## 1. Statements

### (a) `ArithHilbertSamuel` (`Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/SmallSecTensTriv.lean:14-19`)
```lean
∀ k [CommRing k] (X : Scheme) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
    (∀ᶠ m in atTop, ((L.pow m).tens N).smallSec.Finite) ∧
    (fun m => log #smallSec(L^m ⊗ N) − a/(D+1)!·m^(D+1)) =o[atTop] (m^(D+1))
```
- **In words.** Let X be an integral arithmetic variety of relative dimension D, L a nef C^∞ hermitian line bundle with
  arithmetic self-intersection a, and N any hermitian line bundle. Then
  log #{s ∈ H⁰(L^m⊗N) : sup-norm ≤ 1} = a·m^{D+1}/(D+1)! + o(m^{D+1}).
- **Quantifiers.** The o() is inside ∀X ∀L ∀N, so the rate depends on the variety and the bundles, exactly as in the
  literature. It is faithful: Gillet–Soulé, and Zhang/Moriwaki for nef.
- **The objects are real Arakelov objects.**
  - `HermLB` (`ExistsIsClosedImmersionGenericPoint.lean:659-669`): a line bundle on a Mathlib `Scheme`, a metric on the
    complex points for each σ, with C^∞ (`cInf`) and conjugation compatibility.
  - `IsSelfInter` (`:820`) and `IsArithHeight` (`:800-818`): the height of the generic point, defined by the
    vertical / point / recursion axioms (div plus archimedean integral). This is a Gillet–Soulé-style characterisation.
  - `IsNef` (`:823-835`): semipositive, plus non-negative degree on vertical and horizontal curves.
  - I did not unfold `IsArithVar` (Development side), `Weight`, `SemiPos` or `smallSec` beyond its line (`:763`).
- **Proof** (`DP/ArithHilbertSamuelOfPrincipalisation.lean:11-14`):
  Principalisation → `arCalc_of_principalisation`, `ampleArithHilbertSamuel_of_principalisation`, and
  `semiPull_of_principalisation`, then `arithHilbertSamuel_nef_of_ample`.
  - So the proof goes: ample HS (from principalisation / resolution), then nef by perturbation and pull-back.
  - Not opened further.
  - On the root path `Principalisation` is `principalisation_closed`, which ignores `O`
    (`TPS/EveryCharacterOfLiteratureOfVWin.lean:253-256`).

### `HSUse` (`MB/MoriwakiBigTheorem/HSChain.lean:372-374`)
HSUse is the conjunction of three statements:
- **`ArithKleiman`** (`StatementsArithKleiman.lean:9-15`): for a nef, conjugation-invariant hermitian line A on a
  multihomogeneous arithmetic variety P (an ideal of `MvPolynomial` over ℤ), if every arithmetic curve has A-degree ≥ 0,
  then the top self-intersection is ≥ 0.
- **`G7`** (`HSS:437-444`): limsup_n #smallSections(n) / (n^{D+1}/(D+1)!) ≤ the top self-intersection.
- **`ArithmeticVolumeNef`** (`HSS:446`) = `ArithmeticHilbertSamuelUpperBound`, not unfolded.

All three are per variety and asymptotic.

`hsUse_outright` and `moriwakiBig_outright` (`MB/MoriwakiBigTheorem/Outright.lean:9-15`) instantiate
`hsChain resK (arith_intersection_system_of_poincare_lelong poincareLelong resK) DenseCurves.main`. `hsChain` is a
180-step chain of `…HilbertSamuel.*.proof` lemmas (`HSChain.lean:330-366`). Its visible steps include:
- resolution (`resolution_exists_of_resolution_statement hResK`, s169);
- a Kodaira/Kleiman step (s155);
- the L² Gram lattice (s146-148);
- the block χ-covolume (s170);
- `TensorPowerL2Degree` using `theoremHSMBlock hAIS hResK` (s171);
- `ArithmeticVolumeNef` (s180).

### (b) `HSAt` (`CXC:153-156`)
```lean
def HSAt (PP C) (u1) : Prop := ∃ A R, 0 < A ∧ 0 ≤ R ∧ A·log(max A 1) + R ≤ C·unitE p ∧
  ∀ Z, binT·dg(u1,Z)·(lenT·ht(u1,Z) − 3(dim+1)|ht| − A·log(2+|ht|) − R) ≤ degC(uM, Z)
```
- **In words.** On each component Z of a deep cover Y:
  deĝ(lattice of weight-uM cusp forms) ≥ C(lenT−1, dim)·deg_Z(u1)·(lenT·h_Z(u1) − O(dim)|h| − A·log(2+|h|) − R).
- **Quantifiers** (`TPS/LiftLambdaBound.lean:18-31, 59`), via `CoverHeightSum` = `CoversCondition` = `LiftsCondition`:
  - ∀ family satisfying FamHyp, ∃ C ≥ 0, ∃ x0, ∀ x ≥ x0, ∀ ι, ∀ points p with `RowsTAlt`, ∀ layers i with i+1 < m,
    ∀ good covers Y, ∀ u1 with `Quo`, HSAt holds.
  - The proof sets **C = 10000 + 2·Cp** (`TPS/HilbertSamuelLowerBoundOfComponents.lean:36`).
  - Cp comes from `twisted_bundle_degree_lower_bound` (`HBW/TwistedBundleDegreeLowerBound.lean:78`), which has the form
    ∃ Cp ∀ D T j Y …. So the constant is uniform, and the statement is not vacuous (route (iv) excluded).

**How HSAt is obtained (route (i) plus the definitional scale of (iii)):**
- `hilbertSamuel_of_component_estimates_alt` (`TPS/HilbertSamuelLowerBoundOfComponents.lean:25-109`) takes
  `HSClaimS 26 lenT dim n 1 Λ β ΛD ΛT J dg ht rkC degC` from `exists_degree_parameters_bound_alt_alt`
  (`TPS/ExistsDegreeParametersBound.lean:84`). Here:
  - log n, log β, log dg ≤ PP;
  - log Λ, log ΛD, log ΛT ≤ PP·κ (+…).

  It then converts to HSAt by real arithmetic (`deg_bound_of_claim_numbers`, `hilbertSamuel_ALogA_le`), together with
  the twisted-degree bound `htwz`.
- The HSClaimS comes from `hilbertSamuel_estimate_at_level` (`HBW/ExistsDegreeParametersBound.lean:33-75`). It builds a
  data record `h.data f₁ f₂ th k`, checks `GeoHyp` (`hermitian_geometric_hypothesis_holds`), and applies
  `hilbertSamuel_component_short_basis_bound` = `hsClaimS_component_geo` (`DP/HilbertSamuelComponentShortBasisBound.lean:26-37`).
- That in turn is `arithmeticHilbertSamuelBound` = `geoBound_of_quoted'` (`DP/ArithmeticHilbertSamuelBound.lean:19-20`):
  `explicit_arithmetic_hilbertSamuel_bound hQ (bertiniNumberField…) heightTie slopeLowerBound_topLattice_offHypersurface`.
- `HSClaimS` itself (`HSClaim.lean:16-22`) is an explicit inequality for deg/d: (1−z)(T·h − 3(D+1)|h| − J − 26D²·log(e^ρ·T)
  − (T+D+1)·log β − (T+D²)(hsG+2)) − z(T·log(2e^ρ√β) + log ΛD + log ΛT) ≤ deg/d.
  - This is the shape of a Chow-form / short-monomials argument (Bertini to choose D+1 good sections, then products of
    short vectors off a hypersurface). Effective lower bounds of this type exist in the literature: Zhang's
    Chow-form proof, Bost, David–Philippon. **I infer this**; I did not read `SlopeTop.slopeBound`.
- **The size of the precision is set by definitions.** In HSAt the slack is R ≈ 4000·b. b = e^{x^ε} is the scale itself,
  and the bound succeeds only because unitE ≥ b is built into the numeric datum (B0 contains the factor b).
- **The parent's "covers of a fixed variety" (ii) is partly right, but for `HeightAt`, not `HSAt`.**
  - `height_lower_bound_general_alt` (`TPS/HeightLowerBoundGeneral.lean:21-22`) consumes `DeepStR`.
  - `DeepStR` (`Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ModelSmall.lean:63-66`):
    ∃ C, ∀ D T j Y good, `MeanAll` holds, i.e. the component-mean of the volume slope `compVolSlope` is ≥ −C·errX
    (`SemiposAtOfPositive.lean:91-101`).
  - It comes from `deepStR_of_volume` (`.../GeometryProofs/DeepStROfVolume.lean:21-27`), using `GoodTowerExistsX` and
    `VolumeTheoremX`.
  - So for heights the uniform-in-variety input is **one uniform theorem over towers**, not an n → ∞ limit made uniform.

### (c) Proof skeletons
- **`hsUse_outright`.**
  1. Resolution (`resK`) and Poincaré–Lelong give an arithmetic intersection system.
  2. `hsChain` gives (a) Moriwaki-type bigness (`MoriwakiBig.of_found`), (b) G7 and (c) the nef HS upper bound. Its
     steps use resolution to pass to a smooth model (s169), Kleiman/Kodaira for nefness from section counts (s155), and
     an L² Gram-lattice / block χ-covolume computation for tensor powers (s146-171).
  3. Nef Riemann–Roch (`NefRR`) enters only later, in `deepStR_of_volume`.
- **`arithHilbertSamuel_of_principalisation`.** As above: principalisation → the ample case → nef via `semiPull` and
  `arCalc`.

### (d) Trivial instantiations
- **`nrmK` does have a Gram frame on the live path** (assuming `p.fw` is over `p.T`, which I infer from the types).
  - `nrmK` = `normW (T.U(i+1)) (xiR D) (T.V(i+1)) (T.dict(i+1)) (wtZ (wtA κ_i) n)` (`NormNegCmConstantEqAtAllEmbeddings.lean:283-284`),
    which is `Gk p i` (`CXC:30`).
  - `GramAt` includes `GoodW … (Gk p i)` (`CXC:54-56`), and `GoodW` starts with `HasGram (normW …)` (`IPM:806-807`).
  - So `muCore` is not the junk 0, provided `covering_gram_of_prints hP` holds. Its proof was not read.
- The proof records lower bounds 1 ≤ dimFlag, 1 ≤ dg and rkC > 0 (`TPS/HilbertSamuelLowerBoundOfComponents.lean:55-104`),
  so neither the dimension nor the rank is degenerate.
- **Oddity.** `hilbertSamuel_estimate_at_level` fixes `th : R.L.Sec := 0` and a `Consts` field `0`
  (`HBW/ExistsDegreeParametersBound.lean:52-53`). A section chosen as 0 inside the geometric data should be checked: if
  `GeoHyp` or `ClaimS` does not depend on it, this is harmless.
- **Correction to the parent.** `low_of_cover_hypotheses` (`TPS/LowOfCoverHypotheses.lean:16-32`) is **not** a descending
  induction. Each layer is handled separately: the top layer by `LowDef`, and every other layer by one cover Y
  (`lowAt_of_cover`).

## 2. Children (ranked)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `VolumeTheoremX` / `final_theorem_of_inputs_right` (via `good_tower_volume_theorem_bis`) | `.../TowerExistence/GoodTowerExistsX.lean:28`; `MB/HilbertSamuelApplications/GoodTowerVolumeTheoremBis.lean:9-19` | one C for all unitary Shimura towers: MeanSlope ≥ −C(log rd E, L'/L) | core, uniform beyond the literature; proof not read |
| 2 | `SlopeTop.slopeBound` (`SlopeBound`) and `geoBound_of_abstract` | `DP/SlopeLowerBoundTopLatticeOffHypersurfaceStatement.lean:8`; `DP/ExplicitArithmeticHilbertSamuelBoundStatement.lean:13` | effective finite-level HS lower bound (`HSClaimS`) | core; standard-shaped (Chow form / short monomials); proof not read |
| 3 | `hermitian_geometric_hypothesis_holds`, `short_generator_norm_comparison`, `hilbertSamuel_bergman_frame_bound_alt` | `HBW/ExistsDegreeParametersBound.lean:62`; `HBW/ShortGeneratorNormComparison.lean:117` | supply GeoHyp: short spanning families of norm ≤ e^{PPκ}, Bergman β | core; not read |
| 4 | `twisted_bundle_degree_lower_bound` | `HBW/TwistedBundleDegreeLowerBound.lean:78` | ∃ uniform Cp, twisted-degree comparison | core-ish |
| 5 | `hsChain` / `hsUse_outright` / `moriwakiBig_outright` | `HSChain.lean:330-374`; `Outright.lean:9-15` | asymptotic HS, Moriwaki bigness, Kleiman | standard (Gillet–Soulé, Moriwaki); 180 sub-lemmas not read |
| 6 | `arithHilbertSamuel_of_principalisation` | `DP/ArithHilbertSamuelOfPrincipalisation.lean:11` | nef arithmetic HS from ample HS | standard; not on the HSAt path |
| 7 | `deg_bound_of_claim_numbers`, `hilbertSamuel_ALogA_le` | used at `TPS/HilbertSamuelLowerBoundOfComponents.lean:91,106` | real-number conversion from HSClaimS to HSAt | glue |
| 8 | `sizeAt_of` | `SizeBoundStatement.lean:260` | 1 ≤ b ≤ unitE ≤ x^A·b, … | glue (the definitional scale) |

## 3. Oddities
1. "B0·log log x" sounds like a mild error, but B0 = f·m·e^{x^ε}·x^ε. The HS slack R ≈ 4000·e^{x^ε} fits only because of
   this.
2. The literature-shaped Props (`ArithHilbertSamuel`, `HSUse`) are not the source of the needed precision. The effective
   in-tree `SlopeBound` and the uniform `VolumeTheoremX` are.
3. `th := 0` in the geometric data (see (d)).
4. All `*_of_literature O` suppliers relevant here ignore `O` (for example `EveryCharacterOfLiteratureOfVWin.lean:447-558`).
   They are claimed as in-tree proofs of Kawamata–Viehweg, resolution, principalisation, Nadel, and others.

## 4. Coverage
Read:
- `SmallSecTensTriv.lean:1-60`; `DP/ArithHilbertSamuelOfPrincipalisation.lean`; `Outright.lean`;
  `HSChain.lean:1-40, 330-380`; `StatementsArithKleiman.lean`; `HSS:1-32, 255-290, 400-450`;
- `TPS/HilbertSamuelLowerBoundOfComponents.lean:1-120`; `TPS/ExistsDegreeParametersBound.lean`;
  `HBW/ExistsDegreeParametersBound.lean`; `HSClaim.lean`; `DP/HilbertSamuelComponentShortBasisBound{,Statement}.lean`;
  `DP/ArithHilbertSamuelBoundOfQuotedTheoremsStatement.lean`; `DP/ArithmeticHilbertSamuelBound.lean`;
  `HermSysHypOneLeLambdaZero.lean:230-293`; `WellChosen.lean:1-80`;
- `TPS/LiftLambdaBound.lean:15-60`; `CXC:15-175`; `TPS/{SizeAltBis,SizeAltBisStatement}.lean`;
  `SizeBoundStatement.lean:255-300`; `DataParams₂.lean:1-40, 222-230`; `Numbers.lean:70-76`; `ZscOfNum.lean:20-35`;
  `DataArith.lean:198-202`;
- `TPS/TopCovolSlim2Use.lean:16-25`; `TPS/TopCovolG.lean:39-61`; `TPS/HeightLowerBoundGeneral.lean`; `ModelSmall.lean:63-68`;
  `SemiposAtOfPositive.lean:60-105`; `IsHomogeneousCompIdeal.lean:280-288`; `AhSlimU.lean`; `DeepStROfUse.lean`;
  `DeepStROfVolume.lean:21-46`; `GoodTowerExistsX.lean:22-37`; `GoodTowerVolumeTheoremBis.lean`;
  `AbelianCmCompLawsBoundStatement.lean:16-17`;
- `TPS/LowOfCoverHypotheses.lean`; `TPS/ShortVectorsSpanCuspLattice.lean:33-45, 135`; `IPM:20-40, 800-812`;
  `NormNegCmConstantEqAtAllEmbeddings.lean:278-290`; `ExistsIsClosedImmersionGenericPoint.lean:655-835` (parts);
  `EveryCharacterOfLiteratureOfVWin.lean:245-262, 325, 405-558, 781-812` (grep).

Not opened:
- `SlopeTop.slopeBound`; `geoBound_of_abstract`; `hermitian_geometric_hypothesis_holds`;
- `final_theorem_of_inputs_right`; `top_meanAll`; `covering_gram_of_prints`;
- the 180 `hsChain` sub-lemmas; `IsArithVar`;
- `deg_bound_of_claim_numbers`.
