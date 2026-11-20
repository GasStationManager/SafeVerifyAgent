# NODE-VOLUME: `VolumeTheoremX`, `SlopeBound`, `FlatDegree`, `low_of_cover_hypotheses`

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `DT/` = `Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/`
- `DPf/` = `Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/`
- `GP/` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `DivP/` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`
- `CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`
- `SPP` = `Development/AbelianVarietyTheory/Definitions/Divisors/SemiposAtOfPositive.lean`

## 0. Verdict (short)

1. **`VolumeTheoremX` has no main term.** It gives only a lower bound, and the error is the size of a main term:
   mean slope of L_u ≥ −C·[(log B + log rd E + |L′/L(1,χ_d)|)·‖u‖₁ + min(p,q)·spread(u)].
   - This is an "O(log rd + |L′/L|) per unit of weight" bound.
   - Since |logΩ| ≤ log rd E + |L′/L| + O(1), the bound is **no sharper than the logΩ main term itself**.
   - The constant C really does sit outside every quantifier (`GoodTowerExistsX.lean:28-36`).
     It is C = 2·max(Ch + Cu/2, 0) + 17, and Ch, Cu are global constants (`DPf/VolumeTheoremOfInputs.lean:34`).
   - The theorem is weak, and it is sufficient for its one use.
2. **The varieties are positive-dimensional.**
   - The tower lives on full flag bundles over unitary Shimura varieties. Each has relative dimension
     |Ψ|·N(N−1)/2 = |Ψ|·(pq + p(p−1)/2 + q(q−1)/2) (`DT/CompactGapsGE.lean:15`).
   - The theorem requires q ≥ 1 and p ≥ 2q+1.
   - On the live path the signatures are (k+j−1, m−j) with 1 ≤ j ≤ m−1 and k ≥ f ≥ m, so this is genuine
     higher-dimensional arithmetic intersection theory.
   - Uniformity comes from a structural formula: intersection numbers = vol·(flag-variety height polynomial) plus a
     linear form in unknown constants α, β, up to O(log B/B). The unknown linear coefficient is then bounded below by
     **uniform lower bounds for heights of points** (Zhang's successive-minima inequality plus explicit small sections),
     each of size bigLam = log(B·rd E) + |L′/L|.
3. **`SlopeBound` is an explicit, self-contained Chow-form determinant argument, proved in-tree.**
   - Its slack is ≈ T·log β + O(b). This is absorbed because b = e^{x^ε} dominates every polynomial parameter.
4. **`FlatDegree` is where logΩ enters exactly.** It is Chowla–Selberg for the CM elliptic curve by ℚ(√−d). It applies
   because the Hodge type is pulled back from K = ℚ(√−d): multiplicity p at embeddings above the fixed embedding of K, q
   at the others (`IsTypeFn`). The flat section's period is r·z₊^p = ρ·z₋^q (`frame_function_cm_value`).
5. **Precision on the live path is modest.**
   - The volume theorem is consumed only through `Budget`: lenT·errX ≤ 83400·unitE.
   - It is proved by real arithmetic from lenT·‖u′‖₁ ≤ 834·f·m·b and errX ≤ ~11·L·‖u′‖₁.
   - Here unitE = f·m·b·L·log log x with L = x^ε, so the volume error uses unitE/log log x of the allowance.
   - The trivial bound (short generators of norm ≤ e^{PP·κ}) would cost PP·κ ≈ PP·f·r·b. That is too much, so the
     volume theorem is weak but not vacuous.

## 1. Statement

### `VolumeTheoremX` (`Development/AutomorphicSpectrum/Statements/TowerExistence/GoodTowerExistsX.lean:28-36`)
```lean
∃ C ≥ 0, ∀ E [NumberField, CM, abelian over ℚ] (H : Host E) (D : Datum H) Xo l c Y T (o : GoodOrigin Y T) (II),
  IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3·D.q+1 ≤ D.p+D.q →
  T.bad.card ≤ 4·|CMType H|·(p+q)² →
    T.Proportional ∧ T.VolEq ∧ T.T1 II ∧ T.ThmB II hhFl ∧ T.T2 II C (hostRd E) (hostLval H) ∧ T.MeanSlope II C (hostRd E) (hostLval H)
```
**Quantifiers.**
- The order is ∃C, then ∀(field, host, datum, level, coefficients, model, tower T, good origin o, intersection theory II).
- T and o are universally quantified, so there is no "for some tower" escape. Existence of a good tower is the separate
  `GoodTowerExistsX`.
- II ranges over every function satisfying the axioms `IsFullIntersectionSystem` (`ReciprocityTheory/.../InterNamed.lean:37`).
  These are multilinearity, push-forward, mixed contraction and the `IsIntersectionFamily` axioms.

**Objects.**
- `RootTower Ψ N` (`DT/Proportional.lean:10-26`): an index j (= p, by `TowerOrigin.j_eq`), components `Comp`, a bad-prime
  set, and for each B ∈ ℕ and component c a `RootModel` (`DT/Birational.lean:11-41`).
  - A RootModel is an arithmetic variety (a multiprojective ideal, `IsArithVar … (dimFl+1)`), with smooth hermitian
    lines x_{τ,i} (Chern roots) and an ample A.
  - The link to the Shimura model Y is `GoodOrigin`/`RootOrigin` (`DT/GoodOrigin.lean:55`;
    `.../GlobalGeometry/TowerOrigin.lean:18-99`). This provides a `HodgeCpt` 𝔐, a flag `Fl`, and root lines that are Hodge
    lines (`hodge : Fl.IsHodgeLine r …`).
  - **I infer** that M B c is a model of the full flag bundle of the Lie algebra (rank N = p+q at each τ) over a component
    of the toroidal compactification. B indexes the set of primes ≤ B at which the model or metric is adjusted (`InS`).
  - The dimension count fits this reading: per τ, pq + p(p−1)/2 + q(q−1)/2 = N(N−1)/2.
- `slope B c u` (`DT/Proportional.lean:62-63`) = PP(c₁(L_u)^{dim+1}) / ((dim+1)·vol(c)·flagDeg u).
  - So it is the normalised height h_{L_u}(X_c)/((dim+1)·deg_{L_u}X_c) of the automorphic line bundle L_u = −Σ u_{τ,i}·x_{τ,i}.
  - It is a genuine arithmetic self-intersection, not a lattice-of-sections proxy.
- **`MeanSlope C rd Lval`** (`DT/HeckeSectionsIsotropicCommutatorPairingPower.lean:91-93`): for every regular dominant
  weight u with gaps ≥ g (`WeightHyp`, `DT/CompactGapsGE.lean:73`) and every B ≥ max(128, bigB0(u,g), #bad):
  (1/#Comp)·Σ_c slope(B,c,u) ≥ −C·[bigLam(B)·‖u‖₁ + min(j, N−j)·spread(u)].
  - bigLam(B) = log(B·rd E) + |Lval| (`DT/CompactGapsGE.lean:81`).
  - rd E = |disc E|^{1/[E:ℚ]} and Lval = Re L′/L(1, (·/d)) (`.../GlobalGeometry/TowerOrigin.lean:121-127`).
- `T2` is the same bound for the total PB(u) before dividing by volume.
- `ThmB` (`:52-55`) is the structural statement: for each monomial of top degree,
  |PPt(m) − volT·(hh(m) − Σ_τ(α_τ−β_τ)·Sh_j(m) − Σ_τ β_τ·Tot(m))| ≤ C_T·log B/B, with **∃α, β** and a tower-dependent C_T.

**Main term and error.**
- There is **no main term** in MeanSlope or T2. Only the lower bound −C·bigLam·‖u‖₁ − C·min(p,q)·spread is asserted.
- In `DeepStR` (`SPP:40-47`) this appears as `MeanAll (ell D) C`. There errX = (log bndB + log rd E + |L′/L|)·‖u‖₁ + q·spread(u),
  and B = bndB(u,g) = 4|Ψ|N²(1+‖u‖_∞/g). `deepStR_of_volume` (`GP/DeepStROfVolume.lean:21-58`) instantiates exactly this.

**Escape and strength (question (a)).**
- No existential escape was seen. The real content is a weak inequality.
- Compare the error with logΩ = γ + log(π/v) − L′/L(1,χ_d):
  - log rd E ≥ ½·log d, because ℚ(√−d) ⊂ E;
  - so bigLam ≥ |logΩ| − O(1).
  - The error per unit weight is therefore at least the main-term coefficient. The theorem says nothing about the value
    of logΩ.
- On live parameters (`HostNum`, `Divisors/QuoIff.lean:18-31`):
  - log rd E ≤ 2L, where L = x^ε (`DivP/BudgetOfSizeAndWeight.lean:34-47`, from log|disc E| ≤ 4fL);
  - |logΩ| ≤ 3L (`WtNum.om`);
  - ell = log rd E + |L′/L| ≤ 9L (`ell_le`, `:49`);
  - log bndB ≤ L + 22.
- So the error is ≈ 11L per unit weight, against a main term ≤ 3L per unit weight. Same order; no saving.

## 2. Argument

### `final_theorem_of_inputs_right` → `goodTower_volume_of_reduced` (`GP/FinalTheoremOfInputsRight.lean:28-39`)
→ `good_tower_volume_theorem` (`DPf/GoodTowerVolumeTheorem.lean:36-49`)
→ `volumeTheoremX_of_inputs` (`DPf/VolumeTheoremOfInputs.lean:28-90`).

**Level 1 (`volumeTheoremX_of_inputs`).** Fix C = 2·max(Ch+Cu/2, 0) + 17, where (Ch, Cu) come from `NineGeoU`
(`exists_geometric_height_constants`). Then, for each (E, …, T, o, II), the abstract tower axioms are verified from the
geometry, and the abstract theorem `tower_weil_inputs_combined` is applied.

The axioms verified:
- Proportional, VolEq;
- I1, I2 (convergence as the metric parameter t → 0);
- A1 (semipositivity), M1/M2/ANef (nefness at primes in and outside S_B);
- I5/I6 (point heights ≥ −C·log(B/s) and Zariski-dense small points);
- I7, I8 (antisymmetry under simple reflections not equal to j);
- Prop6 (exact B-change formula, contributions of primes in (B₀, B]);
- PropA (Galois symmetry of CM types);
- PropF: |h| ≤ C′·N·bigLam for the linear coefficient, supplied by `good_tower_real_extra hFD`, i.e. from **FlatDegree**;
- SlopeLower: test polynomial ≥ −C·|Ψ|·min(j,N−j)·bigLam·…, supplied by `slope_lower_base_settings` from Zhang's lower
  bound `ZhangLowerX` and `base_setting_of_good_tower` (NineGeoU).

**Level 2 (`chain_tower`, `DPf/TowerWeilInputsCombined.lean:22-53`).**
1. I3 and T1: the slope is the t → 0 limit.
2. `tower_weil_theorem` → ThmW: on walls the B-heights are O(log B/B). This uses successive minima lower and upper bounds.
3. `tower_theorem_B` → ThmB, using `hhFl` (the height polynomial of the flag variety; `PB.FlagHeight`) and I8, I9:
   - every top intersection number equals vol·hh up to a linear form in α_τ, β_τ;
   - averaged over the Galois group (PropA, ThmBA) this becomes one α and one β.
4. `test_height_bound`: SlopeLower and PropF ⇒ `LowerBoundAtBase`, i.e. the unknown coefficient A₀ ≥ −C·bigLam(B₀).
5. `tower_T2`: Prop6 transports the B₀ → ∞ identity back to finite B, giving T2.
6. `mean_slope_proportional_volume` gives T2 ⇒ MeanSlope, using VolEq.

**Level 3 (where uniformity really comes from; `GP/ExistsGeometricHeightConstants.lean`, `GP/CuspHeightUpper.lean:1-80`).**
- `HtU` (`.../GeometryStatements/NineGeoU.lean:32-35`): for every algebraic point P of the model,
  h_{MUc}(P) ≥ −Ch·f·j′·bigLam(B) − (p/q)·KA.
- The proof (`htU_of_given`):
  - take a point over a number field (`small_points_over_number_field`);
  - choose a basis adapted to the CM-type eigenspaces of the Lie algebra (`adapted_family_exists_on_eigenspace`);
  - bound archimedean contributions by a section whose log-norm is ≤ the regularised weight (`cusp_intersection_height`,
    `cusp_intersection_finite`);
  - bound finite contributions by `phiDeg_fibLat_le_of_isOFamily_of_isAdapted` (from FlatDegree, hence the L′/L and
    log rd terms).
- `MeanU` bounds the mean of the potential U by Cu·f·j′·bigLam.
- Zhang's inequality then turns pointwise lower bounds into a lower bound for the height of the variety.
- So the "uniform volume theorem" is, at bottom, **uniform lower bounds for heights of points**. Those are uniform
  because they come from explicit sections, plus symmetric-function bookkeeping on flag bundles.

### Answer to (b)
- Case (2): positive-dimensional. The live path has q = m−j ≥ 1 and p = k+j−1 ≥ 2q+1 (`deepStR_of_volume` derives
  hq1 and hq3; `Ranks.sigW`, `Formalism/LocalRingCardinality/Params.lean:45`).
- The 0-dimensional definite case (j = m, q = 0) occurs only in `LowDef`, outside VolumeTheoremX.
- Uniformity is not from reduction to CM points. It comes from (i) ThmB's structural shape, which leaves only two scalar
  unknowns, and (ii) lower bounds of size bigLam on those unknowns, from point heights.
- There is an upper side (MeanU, `cusp_volume_sum`), but MeanSlope uses only the lower side.

## 3. `SlopeBound` (question (c))

### Statement (`Development/AbelianVarietyTheory/Definitions/Divisors/HermSysHypOneLeLambdaZero.lean:243-253`; `HSClaim.lean:16-22`)
**Data.** A "hermitian section system" S over a number field F (`Sys`, `S.Hyp`):
- graded pieces V_0, V_D, V_T of a section ring of dimension D, with a multiplication action by N linear forms;
- integral lattices M_j and norms;
- short spanning families with norms ≤ Λ₀, Λ_D, Λ_T;
- a multiplication bound β.

**Hypotheses.** f is an irreducible multihomogeneous polynomial of multidegree (δ, …, δ) in D+1 groups of N variables:
the Chow form, with δ = degree. Q ≠ 0, and off {Q = 0} every specialisation s is "flat" (`FlatAt`). This means the
determinant of coordinates factors as c·∏_p lin(y_p) over the δ intersection points.

**Conclusion.** rank V_T > 0, and `ClaimS` holds with h = ht(f)/((D+1)δ), d = rank V_T, R = C(T−1, D),
z = 1 − Rδ/d:

(1−z)·[T·h − 3(D+1)|h| − J − 26D²·log(e^ρ·T) − (T+D+1)·log β − (T+D²)(hsG+2)]
  − z·[T·log(2e^ρ√β) + log Λ_D + log Λ_T] ≤ deĝ(M_T)/d.

**Proof (`DivP/SlopeLowerBoundTopLatticeOffHypersurface.lean:106-258`, read through the `have` chain).**
1. Pick a generic s₀ with Q(s₀) ≠ 0 that maximises the "deep rank".
2. Take d columns spanning V_T (`exists_short_columns_det_ne_zero_hilbertSamuel`), of three kinds:
   - C(T−1,D)·δ columns of the form (short vector of V_0)·(monomial of type α in s)·(word);
   - deep-rank columns from V_D times monomials;
   - the rest short vectors of V_T.
3. The coordinate determinant det(c, col), as a polynomial in the (D+1)×N variables, is divisible by f^{expo}. This is
   proved by specialisation: at each flat s, det = γ·∏ linear forms, which vanishes on the zeros of f.
4. Therefore ht(det) = expo·ht(f) + ht(G′) ≥ expo·ht(f) − (Mahler/Gelfond-type lower bound for G′)
   (`multiformHeight_lowerBound`).
5. deĝ(M_T) ≥ ht(det) − Σ_k log(column norms) (`lattice_degree_ge_height_polynomialVectors_det`).
6. Count: Σ_k t_k = R·T + …; and log norms ≤ T·log√β + log Λ_j.

This is the classical Chow-form / "products of short vectors" effective lower bound, in the style of Philippon and
Soulé–Zhang. **I infer** this attribution. It is explicit and has no limit, so it is uniform automatically.

### Shape against the trivial bound and the live slack
- Main term: (1−z)·T·h. Since z ≈ O(D²/T), this is T·ĥ/((D+1)deg), the arithmetic Hilbert–Samuel leading term for slopes.
- Error per unit T: about log β + 26D²·log(T)/T + (hsG+2). The term (T+D+1)·log β is linear in T, so the bound beats the
  trivial bound only when h ≫ log β.
- In HSAt the slack constants are R = 4000·b + 2Cp·zBase² and A = 26(26·dim² + 2·zed·lenT)
  (`TPS/HilbertSamuelLowerBoundOfComponents.lean:89-90`, from NODE-HS). The constraint is A·log A + R ≤ C·unitE.
- Live sizes, in terms of x:
  - L = x^ε, b = e^L (`Formalism/LocalRingCardinality/DataParams₂.lean:27-29`);
  - unitE = f·m·b·L·log log x (`WtNum.unit`);
  - PP·lenT·dim²·L ≤ b and PP²·r·m·k·dim³ ≤ b (`WtNum.what₂`);
  - f²r⁵ ≤ PP ≤ b (`pp_bounds`);
  - f = [E:ℚ]/2 ≈ x^{2+8ε}, with m ≤ f ≤ k (`Ranks`, `Params.lean:20-21`).
- Hence R/unitE ≈ 4000/(f·m·x^ε·log log x), which is far below 1. **The HS precision demanded is modest:** the error
  budget exceeds the HS error by a factor ≈ f·m·x^ε·log log x.

## 4. `FlatDegree` / `chowla_selberg_period` (question (d))

**Definitions.**
- `FlatDegree logOm` (`Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean:745-755`):
  for every component Z and every τ, a `FlatSec` exists. Every flat section s has
  deg s = flatDegVal = (p−q)/2·logOm + q·(log d − log rd E).
- `FlatSec Z τ` = `ConstSec` of weight `flatWt τ` with defect `flDefect_vw`. This is a nowhere-vanishing section of a
  parallel (determinant-type) automorphic line bundle at τ whose C^∞ norm is constant, with prescribed valuations
  (`deg_eq_toFrame`, `:711`).
- The Prop actually proved is `Fl.FlatDegree` (`.../GeometryStatements/FlatDegree.lean:12-21`).
  - Inputs: for every (E, H, D, l, Xo, c), a CM-type function ty with `IsTypeFn H p q ty`, a frame function φ and log
    norms N.
  - Conclusion: N is adelic and N.deg = (p−q)/2·Re(CM.logOm E χ) + q·(2·log√d − log rd E).

**Why one elliptic curve suffices.**
- `IsTypeFn` (`ReciprocityTheory/.../ToroidalCompactification/IsHolPeriods.lean:13-14`): the multiplicity of τ: E → ℂ is
  p if τ(√−d) = √−d and q otherwise. The CM type / Hodge signature is pulled back from K = ℚ(√−d).
- The flat section is the Gram determinant of an O_E-basis e of the hermitian lattice. `frame_function_cm_value`
  (`GP/FrameFunctionCmValueStatement.lean`) gives an algebraic r ≠ 0 with **r·z₊^p = ρ·z₋^q**, where z_± are the periods
  of the CM elliptic curves `Curve0 H (±√−d)`.
- So the period of the determinant line is a product of periods of the elliptic curve with CM by K and of its conjugate.
  Chowla–Selberg for that one curve then governs it.
- **I infer** from the types (not from a stated isogeny lemma) that the points are isogenous to E₀ ⊗ (O_E-module).
  The Lean states only the period relation.

**Proof (`GP/FlatDegreeHolds.lean:72-118`).**
1. `chowla_selberg_period` for both square roots ρ = ±√−d (`GP/ChowlaSelbergPeriodStatement.lean:9`): a `Curve0` with
   period x = γ + log(2π/√d) − L′/L(1,χ_d), the same x for both.
2. `frame_function_cm_value`.
3. `frame_function_cm_height` (p-adic norms) and `gram_det_ne_zero_local_basis_cofinite`.
4. `hermitian_metric_log_norm_formula` gives the degree.
5. `flatDegree_logOm_re` converts: Re CM.logOm = x − log rd E + log√d.

`chowla_selberg_period` itself (`exists_curve0_hasPeriod`) was not opened.

## 5. `low_of_cover_hypotheses` (question (iv); `TPS/LowOfCoverHypotheses.lean:16-36`)

This confirms NODE-HS: it is **not an induction**.
- C = max(CD, 2(CF+CU)+9).
- Top layer (i+1 = m): the result is `LowDef` directly.
- Every other layer: take one deep cover Y from `DeepEx` and apply `lowAt_of_cover` with Ring, Maps, Rk, Gmin, Flat
  and ULow on that Y.
- `Deep T j` (`.../Divisors/NormNegCmConstantEqAtAllEmbeddings.lean:162-200`) is the same layer-j moduli space with a
  larger coefficient field c′ ⊇ c and deeper level. `Good` requires level 15^e·g₀g₁, complex uniformisations,
  trivial central character on Γ, and |τ(ξ₀)| = xiR D.
- The chain is: muCore ≥ μ(latDeep) − 2b ≥ (maps) μ(Gs(−c₀)) ≥ (Flat) μ(uM) − mainT − C·unitE ≥ (U) −mainT − C·unitE.
- VolumeTheoremX enters only in the last step (UAt), via DeepStR → HeightAt → `uniform_lower_bound_of_sums'`.

## 6. Children

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `tower_theorem_B`, `tower_weil_theorem` | via `DPf/TowerWeilInputsCombined.lean:35-38` | intersection numbers on the tower = vol·hh_flag + linear form in (α, β), up to O(log B/B); walls → 0 | core (Kudla / Maillot–Rössler shaped; not read) |
| 2 | `cusp_height_upper` / `htU_of_given`, `cusp_intersection_height`, `phiDeg_fibLat_le_of_isOFamily_of_isAdapted` | `GP/CuspHeightUpper.lean` | uniform lower bound for point heights, −Ch·f·j′·bigLam | core: the uniformity source |
| 3 | `slope_lower_base_settings` (`ZhangLowerX`), `base_setting_of_good_tower`, `test_height_bound` | `DPf/SlopeLowerBaseSettingsStatement.lean:8`; `GP/BaseSettingOfGoodTowerStatement.lean:24` | point heights ⇒ test-polynomial lower bound ⇒ A₀ ≥ −C·bigLam | core (Zhang: standard) |
| 4 | `PropFTop_holds`, `good_tower_real_extra` | `GP/PropFTopHoldsStatement.lean:7`; `DPf/GoodTowerRealExtraStatement.lean:16` | linear coefficient \|h\| ≤ C·N·bigLam, from FlatDegree | core-ish |
| 5 | `SlopeTop.slopeBound` | `DivP/SlopeLowerBoundTopLatticeOffHypersurface.lean:106` | effective Chow-form slope bound (§3) | core; standard-shaped; skeleton read |
| 6 | `Fl.flatDegree`, `frame_function_cm_value`, `hermitian_metric_log_norm_formula` | `GP/FlatDegreeHolds.lean:72` | flat-section degree = (p−q)/2·logΩ + q(log d − log rd E) | core-ish; skeleton read |
| 7 | `chowla_selberg_period` → `exists_curve0_hasPeriod` | `GP/ChowlaSelbergPeriodStatement.lean:9` | Chowla–Selberg | standard; not opened |
| 8 | `abelian_cm_comp_laws_bound`, `good_datum_parameters` | used `GP/DeepStROfVolume.lean:24,27` | transfer of the RootTower MeanSlope to `compVolSlope` on Y; rd = hostRd, L = hostLval | glue? not read; **must be checked**, since the tower ↔ Shimura identification sits here |
| 9 | `budgetAt`, `sizes`, `l1_u_le`, `ell_le`, `log_rd` | `DivP/BudgetOfSizeAndWeight.lean:34-316` | lenT·errX ≤ 83400·unitE | glue (read) |
| 10 | `exists_good_root_tower` (GoodTowerExistsX) | `DPf/GoodTowerVolumeTheorem.lean:47` | a good tower exists | core-ish; not read |

## 7. Oddities

1. **"Volume theorem" with no volume.** MeanSlope or T2 is a one-sided bound whose error, −C·bigLam·‖u‖₁, is at least
   the size of the logΩ main term. The name oversells it. The precise structural content is in ThmB, which has ∃α, β
   and a tower-dependent constant, and is used only internally.
2. **The allowance is larger than the natural size.**
   - In the application, μ(uM) has natural size ≈ L·‖u‖ ≈ f·m·b·L (`sizes`: lenT·‖u′‖₁ ≤ 834·f·m·b).
   - The allowed error is unitE = f·m·b·L·log log x, which is log log x times larger.
   - The step `main` in `budgetAt` uses only log log x ≥ 1 (`HostNum.big`). So **UAt asserts nothing about the sign or
     size of μ(uM) beyond its own order of magnitude.**
   - The arithmetic of LowAt then rests on mainT. Whether mainT ≫ unitE depends on (p−q)·anchor ~ k·b against
     m·b·log log x. For the final DIV comparison, the parent must check that the k·w·logΩ cancellation (NODE-DIV)
     leaves m·a_t·logΩ ≈ m·x·b·L **above** m·B0·x^{Cε} = f·m²·b·x^{(1+C)ε}, with f ≈ x^{2+8ε}. As written this looks
     reversed unless |TT| or a normalisation compensates. **Escalate (feeds E9).**
3. II is any function satisfying the axioms. VolumeTheoremX is therefore a theorem about every such II.
   `ArithIntersectionSystemStatement` (∃ II) is a premise of `deepStR_of_volume`; its supplier was not located by a
   one-line search.
4. The tower ↔ Shimura-variety link is in the GoodOrigin data (dozens of fields), not in VolumeTheoremX. RootTower and
   RootModel by themselves are abstract arithmetic varieties.
5. `FlatDegree` is an exact formula supplied by Chowla–Selberg, which is plausible for a determinant-type character. The
   isogeny to E₀-powers is implicit (§4).
6. C = 2·max(Ch+Cu/2, 0) + 17 and 83400 are arbitrary but harmless.

## 8. Coverage

Read:
- `GoodTowerExistsX.lean` (all); `DT/HeckeSectionsIsotropicCommutatorPairingPower.lean` (all); `DT/Proportional.lean:1-139`;
  `DT/CompactGapsGE.lean` (all); `DT/Birational.lean:1-120`; `DT/GoodOrigin.lean` (all); `.../GlobalGeometry/TowerOrigin.lean:1-127`;
- `GP/FinalTheoremOfInputsRight{,Statement}.lean`; `DPf/GoodTowerVolumeTheorem{,Statement}.lean`;
  `DPf/VolumeTheoremOfInputs{,Statement}.lean`; `DPf/TowerWeilInputsCombined{,Statement}.lean`;
  `DPf/SlopeLowerBaseSettingsStatement.lean` (statement); `GP/BaseSettingOfGoodTowerStatement.lean` (statement);
  `DPf/GoodTowerRealExtraStatement.lean` (statement);
- `.../GeometryStatements/NineGeoU.lean` (all); `GP/ExistsGeometricHeightConstants.lean`; `GP/CuspHeightUpper.lean:1-80`;
  `GP/DeepStROfVolume.lean`; `SPP:55-110`;
- `CXC:15-160`; `BudgetAt.lean`; `QuoIff.lean:14-60`; `DivP/BudgetOfSizeAndWeight.lean:34-60, 109-175, 246-316`;
  `DataParams₂.lean:9-40`; `Params.lean:1-60`; `TPS/HeightLowerBoundGeneral.lean`; `TPS/BudgetStatement.lean`;
  `TPS/BudgetAltAlt.lean`; `TPS/LowOfCoverHypotheses.lean`;
- `HermSysHypOneLeLambdaZero.lean:180-293`; `HSClaim.lean`; `DivP/SlopeLowerBoundTopLatticeOffHypersurface{,Statement}.lean`
  (proof skeleton lines 106-223);
- `ExistsFlatSecRankZero.lean:700-770`; `GP/FlatDegreeHolds.lean`; `GeometryStatements/FlatDegree.lean`;
  `IsHolPeriods.lean:1-40`; `GP/FrameFunctionCmValueStatement.lean`; `GP/ChowlaSelbergPeriodStatement.lean`;
- `InterNamed.lean`; `ArithmeticHilbertSamuelLowerBound.lean:86-92`; `NormNegCmConstantEqAtAllEmbeddings.lean:69, 162-200`.

Not opened:
- `tower_theorem_B`, `tower_weil_theorem`, `tower_T2`, `test_height_bound`;
- `abelian_cm_comp_laws_bound`, `good_datum_parameters`, `exists_good_root_tower`;
- `exists_curve0_hasPeriod`, `hermitian_metric_log_norm_formula`;
- `geoBound_of_abstract` / `explicit_arithmetic_hilbertSamuel_bound`; `lowAt_of_cover`; `covering_low_defect_alt`;
- the GoodOrigin/RootOrigin field suppliers.
