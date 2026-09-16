# VariableGaugeMean.lean — CONSUMER + CONSTANT cross-check (read-only, SOURCE-LEVEL)

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5).
Target: `NavierStokes/VariableGaugeMean.lean`, 3004 lines, namespace `NavierStokes.VariableGaugeMean`,
190 declarations in INVENTORY.csv (156 theorem, 33 def, 1 structure; `in_cone` True for 169, False for 21).
**No Mathlib, no `lake build` on this box. Every claim below is SOURCE-LEVEL / UNBUILT.**
Every file:line was re-derived with `sed -n 'Np'` on the ORIGINAL file before it entered this report.

---

## (1) IMPORTERS

**12 files import `NavierStokes.VariableGaugeMean` directly.** `grep -rn 'import NavierStokes.VariableGaugeMean'`:

| direct importer | import line | total VGM refs in file |
|---|---|---|
| `NavierStokes/CorrectionStep.lean` | NavierStokes/CorrectionStep.lean:39 | 340 |
| `NavierStokes/CorrectionInitialization.lean` | NavierStokes/CorrectionInitialization.lean:16 | 305 |
| `NavierStokes/CorrectionInitializationNoOptions.lean` | NavierStokes/CorrectionInitializationNoOptions.lean:16 | 305 |
| `NavierStokes/OffplaneCorrectionExtensions.lean` | NavierStokes/OffplaneCorrectionExtensions.lean:2 | 92 |
| `NavierStokes/GaugeMomentBalances.lean` | NavierStokes/GaugeMomentBalances.lean:2 | 85 |
| `NavierStokes/GaugeStateCoherence.lean` | NavierStokes/GaugeStateCoherence.lean:2 | 65 |
| `NavierStokes/LocalRankDefect.lean` | NavierStokes/LocalRankDefect.lean:2 | 64 |
| `NavierStokes/PhysicalMeanJetBounds.lean` | NavierStokes/PhysicalMeanJetBounds.lean:2 | 38 |
| `NavierStokes/MovingMomentBounds.lean` | NavierStokes/MovingMomentBounds.lean:1 | 36 |
| `NavierStokes/DirectAngularDiagonal.lean` | NavierStokes/DirectAngularDiagonal.lean:4 | 9 |
| `NavierStokes/BaseRankPatch.lean` | NavierStokes/BaseRankPatch.lean:4 | 2 |
| `NavierStokes/WaveEdgeExtension.lean` | NavierStokes/WaveEdgeExtension.lean:4 | 1 |

(the "refs" column is the total number of `VariableGaugeMean.<name>` + open-scope bare `<name>` hits for the
190 target names in that file, method as in section 2.)

**Transitive reach: 235 files** reach the target through the import graph (reverse closure of the `import`
edges over all 2659 `.lean` files), including the root `NavierStokes.lean`. So the module sits inside the
main library closure, not in a side branch.

Files that `open` the namespace (13, some are only *transitive* importers, e.g. `GaugeAliasDecay.lean`,
`GaugeMassPreservation.lean`, `ActualCycleExcluded.lean`): `CorrectionStep.lean` (24 open sites),
`CorrectionInitialization.lean` (8), `CorrectionInitializationNoOptions.lean` (8), `GaugeAliasDecay.lean` (4),
`MovingMomentBounds.lean` (2), and 1 each in `ActualCycleExcluded.lean`, `GaugeMassPreservation.lean`,
`ActualIntermediateDebtBounds.lean`, `GaugeExcludedBounds.lean`, `MeanLocalDefectBounds.lean`,
`CrossBasedMeanComposition.lean`, `ActualParticularMeanGain.lean`, `CorrectionAnalyticStep.lean`.
No `export`/`alias` re-exports the namespace (checked).

---

## (2) CONSUMERS BY NAME

Method: for each of the 190 names, count `VariableGaugeMean\.<name>` (word-bounded, any file except the
target) plus bare `<name>` **only in the 13 files that `open ... VariableGaugeMean`**. Short/ambiguous names
are flagged in the `ambig` check: `ambig` = number of OTHER files that also declare a decl of the same name
in INVENTORY. For the names in the table below `ambig` is 0 except `rankPotential`(2), `meanPressure`(2),
`streamPotential`(2), `temporalPotential`(1), `pressureSource`(10), `density`(5), `compactPrimitive`(2),
`physicalToChartTZ`(1) — for those the *qualified* count is the trustworthy number (`density` and
`meanPressure` in fact have bare=0, i.e. every external use is qualified).

Top 25 by total uses:

| name | uses | qual | bare | files | consumer decls | of which in_cone | top consuming files (count) |
|---|---|---|---|---|---|---|---|
| qLength | 436 | 181 | 255 | 44 | 220 | 142 | CorrectionStep(58); CorrectionInitialization(47); CorrectionInitializationNoOptions(47) |
| GaugeData | 228 | 122 | 106 | 29 | 212 | 120 | CorrectionStep(40); CorrectionInitialization(29); CorrectionInitializationNoOptions(29) |
| reconstructState | 306 | 119 | 187 | 44 | 184 | 120 | CorrectionInitialization(72); CorrectionInitializationNoOptions(72); CorrectionStep(27) |
| SupportedGauge | 160 | 86 | 74 | 25 | 117 | 72 | CorrectionInitialization(22); CorrectionInitializationNoOptions(22); GaugeStateCoherence(16) |
| pressureAliasState | 108 | 60 | 48 | 17 | 63 | 33 | CycleStateCoherence(22); CorrectionStep(15); GaugeExcludedBounds(11) |
| rankIncrementState | 85 | 56 | 29 | 14 | 49 | 33 | LocalRankDefect(27); CorrectionStep(17); RankStateBounds(10) |
| temporalStageState | 158 | 52 | 106 | 16 | 78 | 49 | CorrectionStep(35); CorrectionInitialization(30); CorrectionInitializationNoOptions(30) |
| temporalAliasState | 99 | 38 | 61 | 17 | 71 | 40 | CorrectionStep(25); CorrectionInitialization(12); CorrectionInitializationNoOptions(12) |
| similarityGauge | 45 | 37 | 8 | 10 | 16 | 8 | TemporalStateCoherence(12); GaugeStateCoherence(6); RankStateCoherence(6) |
| rankPotential | 42 | 37 | 5 | 11 | 35 | 19 | ActualMeanPotentialRealization(11); ActualMeanPhysicalData(9); LocalRankDefect(7) |
| meanPressure | 32 | 32 | 0 | 6 | 20 | 10 | GaugeStateCoherence(9); OffplaneCorrectionExtensions(9); GaugeMomentBalances(5) |
| rankStageState | 99 | 31 | 68 | 16 | 59 | 39 | CorrectionStep(34); CorrectionInitialization(13); CorrectionInitializationNoOptions(13) |
| temporalIncrementState | 98 | 30 | 68 | 12 | 53 | 33 | CorrectionStep(29); CorrectionInitialization(15); CorrectionInitializationNoOptions(15) |
| streamPotential | 34 | 27 | 7 | 7 | 23 | 13 | OffplaneCorrectionExtensions(11); GaugeMassPreservation(7); TemporalStateCoherence(7) |
| temporalPotential | 30 | 27 | 3 | 8 | 22 | 11 | ActualMeanPotentialRealization(11); ActualMeanPhysicalData(7); CorrectionStep(3) |
| qLength_pos | 33 | 20 | 13 | 18 | 30 | 28 | CorrectionStep(6); ActualWaveRegularityData(4); GaugeAliasDecay(4) |
| pressureSource | 17 | 14 | 3 | 4 | 9 | 6 | CycleContinuationInvariant(5); GaugeStateCoherence(5); OffplaneCorrectionExtensions(4) |
| qLength_reference_bounds | 29 | 10 | 19 | 10 | 29 | 21 | CorrectionInitialization(4); CorrectionInitializationNoOptions(4); CorrectionStep(4) |
| density | 10 | 10 | 0 | 5 | 8 | 3 | GaugeRadialResidualBounds(4); GaugeMomentBalances(2); PhysicalMeanJetBounds(2) |
| physicalToChartTZ | 8 | 8 | 0 | 4 | 6 | 6 | PhysicalMeanJetBounds(5); ActualMeanPhysicalData(1); ActualMeanPotentialRealization(1) |
| compactAlias | 14 | 7 | 7 | 3 | 9 | 5 | GaugeAliasDecay(7); OffplaneCorrectionExtensions(6); GaugeStateCoherence(1) |
| compactPrimitive | 7 | 7 | 0 | 2 | 4 | 4 | OffplaneCorrectionExtensions(6); LocalRankDefect(1) |
| freezeSlow_contDiff | 10 | 6 | 4 | 7 | 10 | 9 | GaugeMassPreservation(3); GaugeStateCoherence(2); GaugeAliasDecay(1) |
| qLength_contDiffOn | 17 | 5 | 12 | 11 | 17 | 11 | CorrectionInitialization(4); CorrectionInitializationNoOptions(4); ActualCoreSupport(1) |
| temporalAtIndex_contDiffOn | 11 | 4 | 7 | 7 | 8 | 7 | CorrectionStep(3); GaugeMassPreservation(3); DirectAngularDiagonal(1) |

Consuming-file ranking over all names: `CorrectionStep.lean` (340), `CorrectionInitialization.lean` (305),
`CorrectionInitializationNoOptions.lean` (305), `GaugeAliasDecay.lean` (97), `OffplaneCorrectionExtensions.lean` (92),
`GaugeMomentBalances.lean` (85), `GaugeMassPreservation.lean` (83), `TemporalStateCoherence.lean` (73),
`GaugeStateCoherence.lean` (65), `LocalRankDefect.lean` (64). 74 distinct files consume at least one name.

**Declarations with ZERO external uses: 103 of 190** (no qualified use anywhere, no bare use in any
`open`-ing file). Of those 103, **85 are `in_cone == True`** in INVENTORY.csv, i.e. the cone marking is much
wider than the actual external consumer surface. (Some of the 103 are used *internally* in the target file —
see the two `meanClass_*` cases below.)

### In-cone consumers of the named "State"/"class" theorems

Every consumer line and every enclosing-declaration line below was `sed`-verified.

| target theorem (target line) | consumer site | enclosing consumer decl (line) | in_cone |
|---|---|---|---|
| `reconstructState_pressure_change_class` (2822) | `CorrectionStep.lean:4647` | `reconstructedMeanStage_pressure_change_mem` (4620) | **True** |
| " | `CorrectionStep.lean:7557` | `gaugeWaveStage_pressure_from_covariance` (7544) | **True** |
| `temporalIncrementState_classes` (2837) | `CorrectionInitialization.lean:3216` | `zeroMean_temporal_increment_bounds` (3182) | **True** |
| " | `CorrectionStep.lean:5205` | `gaugeTemporalStage_constructed` (5169) | **True** |
| " | `CorrectionInitializationNoOptions.lean:3227` | `zeroMean_temporal_increment_bounds` (3193) | False |
| `temporalIncrementState_supportedGauge` (2975) | `CorrectionInitialization.lean:3490` | `temporal_bounds` (3460) | **True** |
| " | `CorrectionStep.lean:5211` | `gaugeTemporalStage_constructed` (5169) | **True** |
| " | `CorrectionStep.lean:5352` | `next_preserve_masses` (5322) | **True** |
| " | `CorrectionStep.lean:8075` | `meanStages_constructed` (8021) | **True** |
| " | `CorrectionStep.lean:5467` | `finish_mean_stages` (5417) | False |
| " | `CorrectionInitializationNoOptions.lean:3501` | `temporal_bounds` (3471) | False |
| `compactAlias_q_supportedGauge` (2623) | `GaugeAliasDecay.lean:308` and `:309` | `compactAlias_finiteJets_local` (283) | **True** |
| `meanClass_streamGamma` (2703) | **NO external use** — only `VariableGaugeMean.lean:2762` | `meanClass_temporalStreamGamma` (2750), itself 0 external uses | (target in_cone True) |
| `meanClass_scaledTemporalStreamBeta` (2776) | **NO external use** — only `VariableGaugeMean.lean:2858` | `temporalIncrementState_classes` (2837) | (target in_cone True) |

Verbatim anchors:
- `NavierStokes/CorrectionStep.lean:4647`: `  have hp := reconstructState_pressure_change_class U g ha hd hcL hcR ε L hε hεone hL hell`
- `NavierStokes/CorrectionInitialization.lean:3216`: `  obtain ⟨hβ, hϑ, hγ⟩ := temporalIncrementState_classes U g ha hd hcL hcR ε L hε hεone hL hell`
- `NavierStokes/CorrectionStep.lean:5205`: `  obtain ⟨hR, hT, hZ⟩ := temporalIncrementState_classes U g ha hd hcL hcR ε L hε hεone hL hell`
- `NavierStokes/GaugeAliasDecay.lean:308`: `    ⟨(hleft _ hx).trans (compactAlias_q_supportedGauge U ha hab hd M (vector direction) f x hx hn).1,`
- `NavierStokes/VariableGaugeMean.lean:2762`: `  meanClass_streamGamma U ha hab hd hcL hcR ε L hε hεone hL`
- `NavierStokes/VariableGaugeMean.lean:2858`: `  have hB := meanClass_scaledTemporalStreamBeta U ha g.radial.inner_lt_outer hd hcL hcR ε L hε hεone hL`

**Disagreement with the framing:** `meanClass_streamGamma` and `meanClass_scaledTemporalStreamBeta` are NOT
consumed in-cone by any *other* file. `meanClass_streamGamma`'s only client chain
(`meanClass_temporalStreamGamma`, VariableGaugeMean.lean:2750) is itself externally dead. So of the six named
theorems only four have external consumers.

---

## (3) NUMERIC CONSTANT CROSS-CHECK

Statement scan: for each of the 190 decls the block text up to the first `:=` was scanned for numerals
(`\d+` and `\d+ / \d+`). Result: **the statements are essentially constant-free.** There is no `2001/1000`,
no `1/1000`-style rational, and no explicit decimal anywhere in the file (`grep -nE '[0-9]+ */ *[0-9]+|[0-9]{3,}'`
returns only nine lines, all `1 / 2`). The constants of the estimates are existentially quantified
(`∃ K : ℝ, 0 ≤ K ∧ ...`). What DOES appear in statements:

| kind | file:line | verbatim (trimmed) |
|---|---|---|
| `1 / 2` (chart hypothesis `h < 1/2`) | VariableGaugeMean.lean:879 | `theorem qLength_chart {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)` |
| same | :896, :905, :917, :944 | `(hh1 : h < 1 / 2)` in `cutoff_chart`, `density_chart`, `physicalMeanPressure_naturality`, `physicalStreamPotential_naturality` |
| `2 * h` (gauge coordinate) | :881, :898, :907, :921, :923, :948, :950 | e.g. :881 `qLength (2 * h) (slowToChartTZ h n s) = chartScale n * qLength (2 * h) s := by` |
| pressure weight `2 * A h + 1 / 2` | :924 | `      (fieldOnPhysicalTZ h n i (2 * CoordinateAlgebra.A h + 1 / 2) f) z =` |
| pressure output weight `2 * A h` | :925 | `    fieldOnPhysicalTZ h n i (2 * CoordinateAlgebra.A h)` |
| stream weight `A h - 1 / 2` | :952 | `    fieldOnPhysicalTZ h n i (CoordinateAlgebra.A h - 1 / 2)` |
| `(2 : ℝ) ^ m` | :731 | `    ‖iteratedFDeriv ℝ j (fun x => f x * g x) z‖ ≤ (2 : ℝ) ^ m * A * B := by` |
| `1 + (2 : ℝ) ^ m * B` | :827 | `        ‖iteratedFDeriv ℝ j (compactPrimitive d a b M ell v f) z‖ ≤ K * (1 + (2 : ℝ) ^ m * B) * A := by` |
| `1 + B` | :1265 | `        K * (1 + B) * A * logWeight cL cR a b p (z.1 / ell z.2.1) := by` |
| `d ^ 2 * cL`, `d ^ 2 * cR`, `a ^ d`, `b ^ d` | :1143 | `      K * A * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (z.1 / l ^ d) := by` |
| class shift `α + 1` | :2784 | `    MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) (α + 1)` |
| class shift `α + 1` | :2853 | `      (α + 1) (temporalIncrementState g h index axial c u).radial ∧` |
| `= 1` (density normalisation) | :113 | `    (∫ r, density a b hab ell (r, (s, Y))) = 1 := by` |
| `logLength a b / 2` | :1079, :1106 | `∀ z : ℝ × E, z.1 / l ∈ Ioo a b → logPosition a (z.1 / l) ≤ logLength a b / 2 →` |

`/ 4` occurs only inside proofs (`:40` `rw [show l * a / 4 = ...`, `:2017` `let c := Real.sqrt U.qlo * a / 4`),
not in any statement.

### Consumer instantiation checks (the off-by-one hunt)

1. **Pressure naturality weights.** Producer `VariableGaugeMean.lean:917-926` maps degree
   `2 * CoordinateAlgebra.A h + 1 / 2` to `2 * CoordinateAlgebra.A h`. Consumer
   `PhysicalMeanJetBounds.lean:885` (`exact he.trans (VariableGaugeMean.physicalMeanPressure_naturality hh hh1 ha hab hd n`)
   sits in `CoherentFamily.reconstructPressure`, whose input family is
   `CoherentFamily h (2 * CoordinateAlgebra.A h + 1 / 2) N Δ U ℝ` and whose output family is
   `CoherentFamily h (2 * CoordinateAlgebra.A h) N Δ U ℝ`, and which feeds
   `fieldOnPhysicalTZ h n (...) (2 * CoordinateAlgebra.A h + 1 / 2) (D.native n)` into the lemma.
   **MATCH.**
2. **Stream naturality weights.** Producer `:944-953` maps `CoordinateAlgebra.A h` to `CoordinateAlgebra.A h - 1 / 2`.
   Consumer `PhysicalMeanJetBounds.lean:912` sits in `CoherentFamily.reconstructStream`, input family degree
   `CoordinateAlgebra.A h`, output family degree `CoordinateAlgebra.A h - 1 / 2`, feeding
   `fieldOnPhysicalTZ h n (...) (CoordinateAlgebra.A h) (D.native n)`. **MATCH.**
   (Consistent with `stream_unit_factor`, `:939`: `ChartScales.Q n ^ (-(CoordinateAlgebra.A h - 1 / 2))`.)
3. **The `α + 1` radial shift.** Producer `temporalIncrementState_classes` gives
   `MeanClass ... (α + 1) (...).radial ∧ MeanClass ... α (...).angular ∧ MeanClass ... α (...).axial` (:2853-2858 region).
   Consumers pack exactly that triple into `IncrementBounds`, whose definition is
   `MeanIncrementBounds.lean:392-395`: `structure IncrementBounds (s : StripData D) (H : ℝ) (h : Triple D) : Prop where` /
   `  radial : MeanClass s (H + 1) h.radial` / `  angular : MeanClass s H h.angular` / `  axial : MeanClass s H h.axial`.
   So `α := H`, radial `α+1 = H+1`. **MATCH, no off-by-one.** At `CorrectionInitialization.lean:3216`
   the instantiating `α` is `1 - ChartScales.kappa`, coming from `zeroMean_reconstructed_bounds`
   (`CorrectionInitialization.lean:2125`, conclusion index `1 - ChartScales.kappa`), and the enclosing
   conclusion is `IncrementBounds ... (1 - ChartScales.kappa)`. **MATCH.**
4. **`d ^ 2 * cL` / `a ^ d` weight rescaling.** `transportGauge_finiteJets` (:1252, weight
   `logWeight cL cR a b p`) is instantiated inside `compactPrimitive_q_finiteJets_global` at
   `VariableGaugeMean.lean:1565` (`obtain ⟨KT, hKT, hbT⟩ := transportGauge_finiteJets (S := PressureStream.Plane) hceU haU habU hcLU hcRU hLU p m`)
   with `hcLU : 0 < d ^ 2 * cL`, `hcRU : 0 < d ^ 2 * cR`, `haU : 0 < a ^ d`, `habU : a ^ d < b ^ d` (:1552-1555),
   and the derived bound at :1595 is
   `        KT * (1 + B) * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p`,
   which is exactly the weight shape produced by `normalizeSource_gauge_finiteJets` (:1143). **MATCH.**

**Verdict: NO CONSTANT MISMATCH FOUND.** No `2001/1000`-shaped literal exists in this file at all, and the
three constant-carrying interfaces that could drift (naturality degrees, the `+1` radial class shift, the
`d^2`/`^d` weight rescaling) are instantiated consistently at every consumer site checked.

---

## (4) LEAF-HYPOTHESIS TRACE

Reference bug shape: `TailRates.flat_of_residuals`, `NavierStokes/GenericSupportedPolynomial.lean:130`, whose
`hres` has no supplier. **None of the four theorems below has that shape**: every named Prop-valued
hypothesis of the artifact has at least one repo declaration that PROVES an instance, and for three of the
four I found the actual discharge at a real call site.

Suppliers used repeatedly below (all sed-verified):
- `SupportedGauge` (def `VariableGaugeMean.lean:67`) — suppliers: `VariableGaugeMean.lean:137` `theorem density_supported ...`;
  `CorrectionInitialization.lean:2075` `theorem zeroMean_gr_supportedGauge {a b : ℝ} {V : Set S} (hV : IsOpen V)`;
  19 decls conclude `SupportedGauge` (17 in the target file).
- `MeanClass` — 277 decls repo-wide conclude a `MeanClass`, e.g. `ActualCycleExcluded.lean:138`
  `private theorem meanClass_sub ...` (`MeanClass s β (f - g)` from two `MeanClass`),
  `MeanIncrementBounds.lean:758` `theorem gr_change_mem (hκ : 2 * κ ≤ 9 / 10) :` concluding
  `MeanClass s H (gr o b (updated m h) W - gr o b m W)`.
- `PhysicalMeanDomain.PeriodicOn` — 30 suppliers, e.g. `VariableGaugeMean.lean:1921`
  `theorem meanPressure_periodicOn {a b : ℝ} (hab : a < b) (d M : ℝ) (ell : S → ℝ)`.
- `RadialAlias.RadiallySupported` — 61 suppliers, e.g. `MeanChartCompatibility.lean:97`
  `theorem pull_supported {l a b : ℝ} (hl : 0 < l) (C : E →L[ℝ] F) (u : ℝ)`.
- `ContDiffOn ℝ ∞ ...` / `ContDiff ℝ ∞ ...`: Mathlib predicates, suppliers abundant in-file
  (`qLength_contDiffOn` :179, `transportGauge_contDiffOn` :1242 region). UNBUILT (no Mathlib to check).

### 4.1 `temporalIncrementState_classes` (VariableGaugeMean.lean:2837-2869)

Hypotheses: `hh : 0 ≤ h`; `hscale : ∀ n, ChartScales.S n ≤ L n`; `hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D`;
`heps : c.operators.epsilon = ε`; `hθ`,`hz : ContDiffOn`; `hpθ`,`hpz : PhysicalMeanDomain.PeriodicOn`;
`hsz : SupportedGauge ...`; `hcθ`,`hcz : MeanClass ... α (u.thetaResidual c / u.axialResidual c)`.

Discharge at the in-cone consumer `CorrectionInitialization.lean:3182 zeroMean_temporal_increment_bounds`:
`hcθ/hcz` from `zeroMean_reconstructed_bounds` (:2125), smoothness from `zeroMean_raw_smooth`, periodicity from
`zeroMean_raw_periodic`, `SupportedGauge` from `zeroMean_raw_supported`, `heps` from `ho.epsilon_eq` — all real
suppliers. `hscale` and `hgap` are re-assumed there (`CorrectionInitialization.lean:3183-3184`), but they DO
have concrete suppliers further out:
- `hgap`: `CommonBaseContext.lean:30` `    (H : IndexBounds h index K) (n : ℕ) : ChartScales.nativeIndex h n ≤ index n + K := by`
  (`IndexBounds` structure at `CommonBaseContext.lean:25`), and `IndexBounds` is itself PROVEN for concrete
  data at `CorrectionInitialization.lean:3876` `    CommonBaseContext.IndexBounds h (index h) (gap h) :=`
  and `ActualCycleGeometry.lean:64` (`index_bounds`).
- `hscale`: instantiated with concrete `L` at `ActualCycleGeometry.lean:22`
  (`noncomputable def similarityData : ActualCycleExcluded.SimilarityData where`), field
  `ActualCycleGeometry.lean:40` `  slow := BaseContextAssembly.slowScale` with proof
  `ActualCycleGeometry.lean:42` `  slow_scale := fun _ => le_max_right _ _` discharging
  `ActualCycleExcluded.lean:43` `  slow_scale : ∀ n, ChartScales.S n ≤ slow n`; the index field
  `ActualCycleGeometry.lean:38` `  index_lower := CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le`
  discharges `ActualCycleExcluded.lean:39` `  index_lower : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap`.
**Verdict: ALL LEAVES SUPPLIED (no orphan hypothesis).**

### 4.2 `reconstructState_pressure_change_class` (VariableGaugeMean.lean:2822-2836)

Hypotheses: `hf`,`hg : ContDiffOn` of `u.gr c` / `v.gr c`; `hsf`,`hsg : SupportedGauge ... (u.gr c n)`;
`hclass : MeanClass ... α (u.gr c - v.gr c)`.
Discharge at `CorrectionStep.lean:4620 reconstructedMeanStage_pressure_change_mem`:
`hf/hg/hsf/hsg` from `state_gr_moving_regular`, and the difference-class hypothesis is PROVEN, not assumed:
`CorrectionStep.lean:4645` `  have hgr : MeanClass stageStrip H (v.gr c - u.gr c) := by`, closed at
`CorrectionStep.lean:4646` `    simpa only [State.gr, hme, hce] using gr_change_mem ho hb hu.velocity hi hH u.covariance hcov hκ`
with supplier `MeanIncrementBounds.lean:758` `theorem gr_change_mem (hκ : 2 * κ ≤ 9 / 10) :`.
A second, independent supplier of the same shape: `ActualCycleExcluded.lean:138` `private theorem meanClass_sub`.
**Verdict: ALL LEAVES SUPPLIED.**

### 4.3 `meanClass_streamGamma` (VariableGaugeMean.lean:2703-2733)

Hypotheses: `hf : ∀ n, ContDiffOn ...`; `hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n)`;
`hclass : MeanClass (movingStripData ...) α f`.
Only client `VariableGaugeMean.lean:2762` (`meanClass_streamGamma U ha hab hd hcL hcR ε L hε hεone hL`) inside
`meanClass_temporalStreamGamma` (:2750) discharges all three from suppliers:
`temporalAtIndex_contDiffOn` (:2549), `temporalAtIndex_supportedGauge` (:2537),
`meanClass_temporalAtIndex_moving` (:2512). So each hypothesis has a supplier — but the whole branch is
**externally dead** (`meanClass_temporalStreamGamma` has 0 external uses).
**Verdict: ALL LEAVES SUPPLIED; branch unused outside the file.**

### 4.4 `transportGauge_finiteJets` (VariableGaugeMean.lean:1252-1399)

Its "hypotheses" are the antecedents under the `∃ K`: `IsOpen U`, `ContDiffOn ℝ ∞ ell U`, `∀ s ∈ U, 0 < ell s`,
`∀ s ∈ U, ell s ≤ L`, `ContDiff ℝ ∞ f`, `RadialAlias.RadiallySupported c e f`, `SupportedGauge a b ell U f`,
the weighted jet bound `∀ j ≤ m, ∀ R, ... ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A * logWeight cL cR a b p (R / ell z.2.1)`,
and the cutoff jet bound `∀ j ≤ m, ‖iteratedFDeriv ℝ j (normalizedCutoff a b ell) z‖ ≤ B`.
No external consumer; the single client is in-file, `VariableGaugeMean.lean:1565`, inside
`compactPrimitive_q_finiteJets_global`, where EVERY antecedent is discharged by a proved supplier:
- `ContDiffOn` of the gauge: `hellpow` from `qLength_contDiffOn` (:1557-1560);
- `RadiallySupported`: `normalizeSource_supported` (:1589 `have hgs : RadialAlias.RadiallySupported (c ^ d) (e ^ d) g := normalizeSource_supported hc hce hd hs`);
- `SupportedGauge`: `normalizeSource_supportedGauge` (:1197 / used :1590);
- the weighted jet bound: `normalizeSource_gauge_finiteJets` (:1135, used via `hbN`, :1602-1604);
- the cutoff bound `B`: `normalizedCutoff_q_finiteJets` (:1521, obtained at
  `VariableGaugeMean.lean:1562` `  obtain ⟨B, hB, hbB⟩ := normalizedCutoff_q_finiteJets U.coord_pos U.coord_lt_one U.qlo_pos d a b`,
  applied `(fun k hk => hbB k hk zU ⟨hz, hzU⟩)`).
**Verdict: NO ORPHAN HYPOTHESIS — the `logWeight` jet premise, which is the analogue of `hres`, HAS a
supplier (`normalizeSource_gauge_finiteJets`) and is actually used.**

---

## Residue (not checked / not checkable here)

1. **UNBUILT.** No Mathlib, no `lake build`. Nothing here says the file compiles, that the cited suppliers
   typecheck, or that the instantiations elaborate with the same implicit arguments. Constant "MATCH"
   verdicts are syntactic (identical source text of the degree/weight expressions), not elaborated-term
   equality.
2. **Bare-name attribution is heuristic.** Bare hits are counted only in the 13 files that `open` the
   namespace, but `open` is section-scoped; a bare hit outside the open's section may be misattributed, and a
   name shadowed by a local `have`/`let`/field of the same spelling inflates counts. Names with `ambig > 0`
   (`pressureSource` 10, `density` 5, `rankPotential` 2, `meanPressure` 2, `streamPotential` 2,
   `compactPrimitive` 2, `temporalPotential` 1, `physicalToChartTZ` 1, `meanClass_streamGamma` 1 —
   also declared in `PhysicalMeanDomain.lean`) are reported by qualified count where possible.
3. **Dot-notation / projection uses are NOT counted** (`h.radial`, `d.gauge`, `x.qLength`-style generalized
   field notation, `.1`/`.2` projections of target theorems), so real coupling is ≥ the numbers reported.
   Uses through `variable`-bound section hypotheses and through structure fields are likewise uncounted.
4. **Statement/proof split** uses the FIRST `:=` in the declaration block; a `:=` inside a structure-instance
   type or a default value would truncate a statement early. Spot checks on the 14 constant-bearing lines
   found no such case, but the split is not proven correct for all 190 blocks.
5. **Declaration boundaries** for "enclosing consumer decl" come from INVENTORY.csv line numbers plus
   next-decl-minus-one; `private`/nested/`where`-block decls could mis-attribute a consumer line. Every
   enclosing decl cited in section 2 was individually sed-verified to be a `theorem` header line.
6. **`in_cone` semantics** are taken from INVENTORY.csv/CONE.csv as given; I did not re-derive the cone.
7. Transitive importer count (235) counts files reaching the target through `import` edges only; `lake`
   default-target reachability was not checked.
8. I did not audit whether the suppliers themselves are vacuous (e.g. whether `IndexBounds` for
   `CommonWindow.index` is provable only under further unproven premises beyond `0 ≤ h`), only that a
   declaration exists whose conclusion is the required Prop.
