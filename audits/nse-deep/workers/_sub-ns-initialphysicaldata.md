# Worker report: `NavierStokes/InitialPhysicalData.lean`

Target: `/home/gsm/.openclaw/workspace/repos/NSE/NavierStokes/InitialPhysicalData.lean`
(openai/NavierStokesAndEuler @ f9e8bc5). Read-only source audit; **no `lake build`** (no Mathlib
on disk, so nothing here is machine-checked — see Residue).
Toolchain pin: `leanprover/lean4:v4.34.0-rc2`, mathlib rev `85e3a25e006c` (`lake-manifest.json`).

## Scope

Exact counts (regex on decl-starting lines, file has 2854 lines):

| kind | count |
|---|---|
| `theorem` | 177 |
| `def` (all `noncomputable`) | 48 |
| `abbrev` | 5 |
| **total** | **230** |
| `structure` / `inductive` / `instance` / `axiom` / `opaque` / `example` | **0** |

Sections (21): `NativePotential`, `GermBounds`, `NativeCopies`, `Labels`, `SourceBounds`,
`ActualSupport`, `SupportedCells`, `PhysicalSupport`, `PhysicalFamilies`, `NativeProfiles`,
`SourceCharts`, `ActualRegularity`, `PhysicalData`, `LiteralCopies`, `PhysicalCopyIdentities`,
`ExactExteriorSupport`, `PhysicalCoordinates`, `PrimaryFieldIdentities`, `GlobalPrimaryPotential`,
`GlobalPrimaryPressure`, `FiniteAggregation`, `FullSlowDomain`.

**What the file is for.** It builds the *initial data* of the claimed blowup: a complex-valued
"copy family" of wave amplitudes (`potentialFamily`, `pressureFamily`, :364/:373), bundles the
already-proved support / regularity / uniform-jet facts into two `WaveData` records
(`potentialWaveData` :1269, `pressureWaveData` :1299), defines the two delivered fields
`potential B N0` (:892) and `pressure B N0` (:895), and then proves the *bridging identities*:
on every valid chart the constructed infinite copy sum equals a **finite** sum of the
pre-existing per-label fields `ActualPrimaryCoherence.cartesianPotential / physicalPressure`
(top theorems `potential_eq_active` :2515, `curl_eq_active` :2547, `pressure_eq_active` :2556,
`velocity_chart` :2572, `pressure_chart` :2595 and their `_slow` variants :2754-:2849).
There are essentially **no new analytic estimates** here (no `∀ε∃δ`, no interpolation): the
estimate content is imported; this file is an *identification / assembly* layer. That matches
the parent's prior: kernel-trust risk LOW, risk concentrated in index/quantifier/junk-value
bookkeeping.

**Sampling scheme.** Every line of the file was displayed and read at least at statement level
(19 overlapping windows covering 1-2854). Verified *line-by-line with the proof mechanism
re-derived* (≈1400 lines): 1-430, 430-660, 660-835, 835-1005, 1005-1140, 1139-1345, 1345-1530,
1528-1680, 1680-1790, 1905-2092, 2092-2144, 2144-2372, 2372-2620, 2617-2854. Read at
statement + tactic-pattern level with spot checks (≈300 lines): 1790-1905 (`graph_cartesian_forward`,
`polarPoint_common_forward`) and 1909-1975 (the two `*_periodized_of_chart` twins, which are
structurally identical to `potential_periodized` :1636 that I did verify).
Pattern coverage rather than prefix coverage: the file has only these distinct proof patterns, and
I checked ≥1 instance of each — term-mode structure instances (`where` records: 7),
`simp only [ite_eq_left h]`/`dite_eq_left` if-elimination (41 occurrences), `change ... ; rfl` defeq
chains (60 `change`, 57 `rfl`), germ/`filter_upwards` arguments (5), `tsum` manipulation (19
`tsum` occurrences: `tsum_mul_right`, `tsum_const_smul''`, `ContinuousLinearMap.map_tsum`,
`tsum_congr`), arithmetic closers (`nlinarith` 4, `linarith` 11, `norm_num` 13, `omega` 3,
`field_simp` 1, `ring` 2), and the only two `calc` chains in the file (:2285, :2432) — **both**
read in full. Tactic census: `exact` 143, `apply` 80, `simp only` 63, `simpa` 37, `by_cases` 20,
`by_contra` 11, `decide` **0**.

## Per-declaration findings

`P/p` = the potential/pressure mirror pair is verified together (statements identical up to
`ComplexVector` vs `ℂ`, shift `-h` vs `-(2·A h)`, and `cutNativeVelocity` vs `cutNativePressure`);
that collapses ~60 declarations into ~30 rows. Verdicts: OK / UNCLEAR / KERNEL-RISK / SUSPICIOUS.

| decl | file:line | statement in my words | proof mechanism | verdict |
|---|---|---|---|---|
| `attribute [local instance] Classical.propDecidable` | :28 | make every `Prop` decidable in this file | attribute | OK (see Kernel-risk §3) |
| `potentialCoefficient` | :40 | def: `inverseCarrier(freq n) • normalCoefficient(normal, amplitude)` — the vector potential coefficient of the cut wave | def | OK |
| `potentialCoefficient_zero` | :47 | amplitude `= 0` ⇒ coefficient `= 0` | `simp` through `normalCoefficient`/`normalCross` | OK |
| `potentialCoefficient_zero_germ` | :53 | amplitude vanishes near `x` ⇒ coefficient vanishes near `x` | `filter_upwards` + previous | OK |
| `potentialCoefficient_local` | :59 | coefficient is in the local-wave class with weight `fullEnvelope`, exponent 1 | combines `inverse_carrier_local` (exp 1/2) with `normalCoefficient_class` (exp 1/2) via `unweighted_smul`, then `he : 1/2+1/2 = 1` rewrite; final `congr` closed by `push_cast; ring` on `I * (1/f) = I/f` | OK — exponent addition is explicit and correct |
| `potentialCoefficient_uniform` | :88 | coefficient is in the *uniform* class over all signed labels | `uniformClass_of_local_germs` + `actual_input_cover` case split (cell hit ∨ zero germ) | OK |
| `uniform_of_germ_or_zero` | :114 | if `g0` is locally `f0` or locally `0` at each point of the domain, it inherits `f0`'s uniform class | **constants**: `obtain ⟨C,hC,p,hb⟩ := hf.bounds m` **before** `intro i n x` (:125-127) ⇒ `C` independent of the object; zero branch uses `majorant_nonneg` | OK — mode-B (quantifier order) explicitly correct |
| `copyAmplitude` / `copyPressureCoefficient` / `copyPotentialCoefficient` | :141/:145/:149 | per-frequency copies of the cut native velocity/pressure/potential | defs via `copied A ...` | OK |
| `copyAmplitude_germ` … `copyPressure_zero_germ` (6) | :156-:199 | on a cell the copy equals the full cut coefficient; off the cell it vanishes near the point | `copySum_germ` / `zero_germ_of_support` composed with `nativeOfFull.continuous.continuousAt` | OK |
| `copyPotential_uniform` P/p | :201/:211 | copies inherit the uniform class | `uniform_of_germ_or_zero` + cell case split | OK |
| `bandLabel`, `bandLabel_injective`, `active`, `selected`, `selected_label/_band/_eq` | :227-:247 | `active` = range of `bandLabel`; `selected` is a chosen preimage, and it is *the* preimage by injectivity | `Exists.choose` + `bandLabel_injective` | OK — `choose` is safe **because** injectivity gives `selected_eq` (:246) |
| `gap` | :249 | `nativeIndex h L.1 - CommonWindow.index h L.1` (**ℕ** subtraction) | def | OK, but see `commonIndex_gap` |
| `commonIndex_gap` | :1834 | `nativeIndex - gap L = CommonWindow.index` | `Nat.sub_sub_self (CommonWindow.index_le_native …)` | OK — truncated-ℕ trap is discharged with the real inequality, not assumed |
| `geometry`, `selectedCarrier`, `carrier`, `carrier_bandLabel`, `selectedCarrier_center` | :252-:278 | carrier data per band; on `active` bands it is the selected label's carrier, else a **zero dummy carrier** (`0 0 0 (fun _=>0) (fun _=>0)`) | `dite` on `L ∈ active` | OK — junk branch only ever consumed by `carrier_center` :742 / `carrier_integer` :752 / `carrier_frequencies` :1126, each of which proves the *needed bound* in the junk branch too (`abs_zero`, `⟨0, …⟩`, `1 ≤ phaseSize`) |
| `sourceChoice` | :282 | `Option`-valued: `some (selected L, k)` iff band is active **and** harmonic index `= 1`, else `none` | nested `dite`/`ite` | OK; harmonic gate is a modelling choice, see Escalation E3 |
| `sourceFamily` | :287 | `if n = band(I) then (match sourceChoice with some l => f l n x | none => 0) else 0` | def | OK — see D-analysis |
| `sourceFamily_eq_some` / `_eq_zero` | :296/:303 | the two elimination lemmas for that `if` | `simp only [sourceFamily, ite_eq_left/ite_eq_right, …]` | OK. `ite_eq_left`/`ite_eq_right` are core `Lean` v4.34 (`Init/Core.lean:1179/1188`, the renamed `if_pos`/`if_neg`); they hold for **any** `Decidable` instance, hence are unaffected by :28 |
| `sourceFamily_uniform` | :313 | the padded family inherits the uniform class | `∃C` pulled out **before** `intro I n x` (:326-328); the two junk branches are closed by `majorant_nonneg` (a bound on `0` needs the majorant `≥ 0`, which is proved, not assumed) | OK |
| `nativePotentialSource` / `nativePressureSource` | :340/:343 | the two padded native sources | `sourceFamily` applied at `(x, 0)` | OK — the `θ=0` slot is justified later by `potentialCoefficient_angle` :1881 (coefficient is angle-independent) |
| `*_uniform` P/p | :346/:355 | uniform class for the two sources | `uniform_slice` + `mono_weight` + `fullEnvelope_le_one` | OK |
| **`potentialFamily`** | **:364** | copy family with `amplitude k I x = if 0 < x.1.1 then Q(band)^(-h) • rotatedSource … else 0` | record | OK **as analysed below**, not vacuous |
| **`pressureFamily`** | **:373** | same with shift `-(2·A h)` and no rotation | record | OK, same analysis |
| `strip_flat_geometry` | :388 | the moving strip has a flat-geometry certificate with explicit constants `(edgeExp/4, 1, logLength, logPosition)` | `movingStrip_flatGeometry` + `epsilon_pos`/`epsilon_le_one`/`one_le_slowScale` | OK — constants are closed forms, no dependence on the bounded object |
| `native_source_bounds` | :404 | uniform class ⇒ `LocalSourceBounds` with `α=1` | supplies `⟨1/2, …⟩`, `⟨1, le_rfl, 1, …⟩`; last goal `max 1 (S n) ≤ 1 * S n ^ 1` closed by `S_ge_one` for `n ≥ 1` | OK — absolute constants (`1`), so no hidden dependence |
| `nativePotentialSource_bounds` P/p | :418/:423 | instances of the above | term | OK |
| `near_self` | :434 | a label is "near" its own cell band | `label_large` + `omega` | OK |
| `copyPoint_self`, `copied_self` | :437/:448 | at the label's own band the copy map is the identity on the slow factor and the scale factor is `Q^a/Q^a = 1` | `div_self (rpow_pos …).ne'` | OK — division is by a proved-positive quantity |
| `attached_pair_support` | :457 | nonzero raw velocity/pressure ⇒ radius in `Ioo(left,right)`, `chartQ ∈ Ioo(1/2,2)`, slow core, clock core | contrapositives of `nativeExtension_outside`, `spatialMask_*` | OK |
| `cut_pair_support` | :488 | same for the *cut* pair | reduces to previous | OK |
| `slowInput`, `slowInput_continuous`, `nativeAt` | :513-:521 | slow coordinate of a lift point; native point at band/frequency | defs | OK |
| `copyAmplitude_nativeAt` P/p | :523/:529 | copy at the own band and lifted point `= cutNativeVelocity/Pressure (nativeAt …)` | `copied_self` + `rfl` | OK — this is the identification that makes the junk-free branch meaningful |
| `sourceFamily_nonzero` | :535 | `sourceFamily f I n x ≠ 0` ⇒ ∃ label with `bandLabel l = I.1`, harmonic `= 1`, `n = band`, `f (l,k) n x ≠ 0` | 3 nested `by_cases`, each junk branch closed by exhibiting the value `0` | OK — the *only* direction used downstream is "nonzero ⇒ information", which is the safe direction for a junk branch |
| **`potential_amplitude_data`** P/p | **:550/:572** | amplitude `≠ 0` ⇒ ∃ label, band matches, harmonic `= 1`, **`0 < x.1.1`**, and the cut native field `≠ 0` | `by_contra` on `0 < x.1.1` (`ite_eq_right`), then `sourceFamily_nonzero`, then `copyAmplitude_nativeAt` | OK — the key lemma; time-positivity is *extracted from* nonvanishing rather than assumed |
| `baseCells`, `slowCell`, `slowCell_closed`, `cells`, `cells_bandLabel` | :589-:630 | support cells = native rectangle ∩ slow-core preimage; `slowCell = ∅` on inactive bands | `dite`; closedness by `preimage` of a closed set | OK — `∅` junk branch is only used to derive `False` (:985, :948, :963) |
| `potentialCells` P/p | :632/:641 | `SupportCells` instance | `potential_amplitude_data` + `cut_pair_support` + `cells_bandLabel` | OK |
| `innerRadius`, `outerRadius`, `innerRadius_pos` | :656-:659 | `left/4`, `2·right`, positivity | `div_pos` | OK |
| `cut_pair_mask` | :662 | nonzero cut pair ⇒ spatial mask `≠ 0` | contrapositive through `rawVelocity`/`rawPressure_zero_of_velocity_zero` | OK |
| `cut_pair_domain` | :677 | nonzero cut pair (+ `0 < t`) ⇒ cylindrical image in `strip.domain` | `nativeStrip_mem` | OK |
| **`cut_pair_annulus`** | :685 | nonzero cut pair ⇒ `liftXY x` in `annulus innerRadius outerRadius` and `‖liftZT x‖ ≤ 2` | `nativeRadius = radius/√q`, `1/2 ≤ √q ≤ 2` from `1/2 < q < 2` (`Real.le_sqrt`, `Real.sqrt_le_left`), then two `nlinarith` | OK — I re-derived both: `radius < right·√q ≤ 2·right` and `left/2 ≤ left·√q < radius ≤ 2‖·‖ ⇒ left/4 ≤ ‖·‖`. Both use `radius_le_two_norm`/`norm_le_radius`, correct directions |
| `liftXY_common`, `liftZT_common`, `slowInput_common` | :729-:740 | the lift's plane part is `scaledRadial`; the others are `rfl` | `rfl`/library | OK |
| `carrier_center`, `carrier_integer`, `gap_bound`, `gap_native` | :742-:768 | carrier centre formula; `carrier·angular ∈ ℤ`; `gap ≤ CommonWindow.gap`; `gap ≤ nativeIndex` | `dite` split (junk branch handled), `omega`, `Nat.sub_le` | OK |
| `physicalPosition_graph`, `physicalScale_graph` | :770/:787 | the three physical coordinates of the graph point are `(radius, w.2 2, 1 - w.1)` after descaling; scale is `physicalQ/Q n` | `fin_cases` + `rpow_add`/`mul_div_cancel₀` with `Q_pos` | OK — **this is where "time" gets its meaning**: the slow time coordinate is `(1 - w.1)/Q n` |
| `spatialMask_physical` | :796 | mask at the lifted point = physical mask of the band label | `nativePoint_mask` + previous two | OK |
| `width_physical` | :819 | on the clock core the `eta` offset from the carrier centre is `≤ slots.radius` | `carrier_center` + `width_on_core` | OK |
| **`potential_support`** P/p | :832/:861 | `SupportData` (gap bounds, integer angular mode, geometry support, mask support) | all four fields via `potential_amplitude_data` + `cut_pair_annulus`/`cut_pair_mask`; band index converted by `congrArg (·.val.1) hl` | OK — index conversions `cellBand l.2 ↔ I.1.val.1` are always *proved*, never assumed |
| **`potential`** | **:892** | delivered velocity potential `= vectorSum potentialFamily innerRadius h slots.radius` | def | OK. `vectorSum` (`PhysicalCopyBounds.lean:622`) `= ∑ i, realCoordinate i ((f i).sum …)` so the field is **real**-valued via `Complex.re` |
| **`pressure`** | **:895** | delivered pressure `= (pressureFamily.sum …).re` | def | OK |
| `copyPotential`, `copyPotential_field` | :898/:911 | `CopyPotential` record; its `.field` is `rfl`-equal to `potential` | record + `rfl` | OK |
| `profileRegion`, `profileRegion_open`, `carrierProfiles`, `profileRegion_contains` | :919-:983 | phase-profile domain per band (`∅` if inactive); polynomial jets of `(F,G)` with a **uniform** `C,p`; the slot-slow point lies in the region | `∃C` again pulled out **before** `intro i j hj x hx` (:951-953); inactive branch derives `False` from `x ∈ ∅` | OK |
| `potentialCarrier` P/p | :987/:995 | `CarrierBounds` instance | records | OK |
| `sourceStrip`, `potentialSource`, `pressureSource`, `*_bounds` | :1009-:1032 | pulled-back strip and the two rotated/pulled sources with their `LocalSourceBounds` | `sourceBounds_rotated` / `_pullback` | OK |
| `cut_pair_source_domain` | :1034 | nonzero cut pair ⇒ lift point in `sourceStrip.domain` | `cut_pair_annulus` + `linarith` on `inner/2 < ‖·‖ < outer+1` | OK |
| `potential_source_domain` P/p | :1048/:1054 | amplitude `≠ 0` ⇒ in `sourceStrip.domain` | previous | OK |
| **`sourceStrip_time`** | **:1060** | `x ∈ sourceStrip.domain ⇒ 0 < x.1.1` | `nativeStrip_time` | OK — **this is the lemma that makes the `else 0` branch unreachable on the source domain** |
| `potential_amplitude_source` P/p | :1063/:1072 | on `sourceStrip.domain` the amplitude **equals** the honest formula (no `if`) | `simp only [potentialFamily, ite_eq_left (sourceStrip_time hx)]` | OK — junk branch eliminated by a *proof*, not by fiat |
| `identitySourceChartOn` | :1083 | generic `CommonChart` whose map is `id` and whose formula only needs to hold on a strip | `positive_jets` supplied with `⟨1, le_rfl, 0, …⟩` (`S^0 = 1`), closure condition from `SupportData.tsupport_geometry` + `continuousWithinAt.mem_closure` | OK |
| `potentialChart` P/p | :1112/:1119 | the two charts with shifts `-h`, `-(2·A h)` | previous | OK — shift arguments match the family definitions at :369/:377 exactly |
| `carrier_frequencies` | :1126 | `|angular|,|axial|,|radial| ≤ phaseSize` | `dite` split; junk branch uses `abs_zero` + `1 ≤ phaseSize` | OK |
| `nativePast`, `sourceFamily_smooth`, `nativePotentialSource_smooth` P/p | :1143-:1170 | `ContDiffOn ∞` of the padded sources on `{0 < x.1} ∩ {0 < x.2.1.1}` | case split; both junk branches are `contDiffOn_const` | OK |
| **`paddedPast`, `paddedPast_open`, `paddedPast_map`** | :1172-:1183 | `cylindricalDomain inner outer ∩ {0 < x.1.1}`, **open**, maps into `nativePast` | `isOpen_lt` + `Real.sqrt_pos` of `sum_sq_pos` | OK — openness matters: it is what lets a `ContDiffOn` on `paddedPast` be upgraded locally |
| **`potential_amplitude_smooth`** P/p | **:1185/:1203** | amplitude is `C^∞` on `paddedPast` | builds smoothness of `rotationMap ∘ liftXY` and `source ∘ cylindricalMap`, then `.congr` with `ite_eq_left ht` where `ht : 0 < x.1.1 := hx.2` | OK — the `if` is **not** claimed smooth; smoothness is claimed only on the open set where the condition holds. Discontinuity at `x.1.1 = 0` is avoided, not hidden |
| `commonLift_mem_paddedPast` | :1214 | `w ∈ preterminal` + annulus ⇒ the lift is in `paddedPast` | `graph_time_pos` + `linarith` | OK — `preterminal` (`{w | w.1 < 1}`) is what supplies `0 < x.1.1` |
| `potentialSmooth` P/p | :1227/:1245 | `SmoothData` instance | `SmoothNear.of_open paddedPast_open` + carrier-profile smoothness | OK |
| `potentialWaveData` / `pressureWaveData` | :1269/:1299 | the two `WaveData` records (`alpha = 1`, `shift = -h` / `-(2·A h)`, `harmonics = 1`, `slowBound = 2`, `gapBound = CommonWindow.gap h`) | records referencing all the above | OK — every numeric field is a closed form; `slow_nonneg`, `frequency_one_le`, `width_nonneg` all discharged |
| `potentialWaveData_vector` / `pressureWaveData_pressure` | :1327/:1330 | the records' fields are `rfl`-equal to `potential`/`pressure` | `rfl` | OK — no silent quantity change between the bundled object and the delivered field |
| `potential_smooth` / `pressure_smooth` | :1333/:1338 | `ContDiffOn ℝ ∞ (potential B N0) preterminal` | `WaveData.vector_smooth` with `h_pos`, `h_lt_half` | OK on its face; the *content* lives in `PhysicalStageBounds` (out of scope) |
| `positiveIndex`, `positiveIndex_band` | :1349/:1352 | wave index `(bandLabel l, +1)`; its band is `cellBand l.2` (`rfl`) | `rfl` | OK |
| `copyAmplitude_summable` | :1355 | the copy sum over frequencies is summable | local finiteness of `copyCells` ⇒ finite support | OK — genuine summability, needed at :1416/:1634 |
| `cut_amplitude_self` P/p | :1364/:1390 | at the own band the cut coefficient **equals** the tsum of its copies | `periodized_cut_eq` + `chartCoefficients_amplitude_copies`; `coefficientScale_eq` | OK |
| `potentialCoefficient_self` | :1409 | same for the potential coefficient, moving the CLM inside the tsum | `ContinuousLinearMap.map_tsum` **with** the summability hypothesis | OK — CLM/tsum exchange is justified, not assumed |
| **`nativePotentialSource_active`** P/p | **:1418/:1426** | at `(positiveIndex l, k)` and `n = cellBand l.2` the padded source **is** the honest copy coefficient | `sourceFamily_eq_some … rfl (l,k)` + `dite_eq_left hl` | OK — **anti-vacuity**: the `none`/`0` branch is *not* taken at the indices that carry the construction |
| `dynamics_copyPoint_self`, `polarPoint`, `polarPoint_fst`, `slotPoint_polar`, `phase_polar` | :1434-:1479 | identification of the dynamics' copy point and of the phase in a polar chart | `chart_nativePoint`, `phase_germ … .eq_of_nhds`, `div_self (actual_carrier_ne_zero)` | OK — the division at :1471 is by a proved-nonzero carrier |
| `copyPotential_fast` P/p | :1487/:1495 | nonzero copy coefficient ⇒ the point is in the clock core | contrapositive of the zero germ, `.eq_of_nhds` | OK |
| `potential_amplitude_active` P/p | :1510/:1520 | with `0 < x.1.1`: amplitude `= Q^(-h) • (rotationMap … (copyPotentialCoefficient …)) i` | `ite_eq_left ht` + `nativePotentialSource_active` | OK |
| `potential_term` P/p | :1528/:1541 | the family's `term` at `positiveIndex l` unfolds to `commonWave` of the selected carrier | `change … ; rw [carrier_bandLabel]; rfl` | OK — band, gap and harmonic (`1`) arguments all match the definitions |
| `potential_commonWave` P/p | :1553/:1589 | that `commonWave` equals `(Q^(-h) • rot(coef)) i * carrier(freq, phase)(polarPoint …)` | `graph_time_pos` supplies `0 < t`; `by_cases` on the coefficient being `0` (then both sides `0`); else `phase_polar` after `copyPotential_fast` | OK — the zero case is *proved* zero on both sides, not asserted |
| `potential_rotated_sum` | :1623 | tsum of rotated copies = rotated full coefficient (component `i`) | `R.map_tsum` with summability from `potentialCoefficient_self` | OK |
| **`potential_periodized`** P/p | :1636/:1652 | the periodized (tsum over `k`) family at `positiveIndex l` = `Q^shift • coefficient · phase-carrier` | `simp_rw [potential_term, potential_commonWave, liftXY_common]`, then `tsum_mul_right`, `tsum_const_smul''`, `potential_rotated_sum` | OK — `tsum_mul_right`/`tsum_const_smul''` are unconditional Mathlib lemmas (both sides junk-`0` when not summable), and the one exchange that *does* need summability (`map_tsum`) has it |
| `physicalX`, `cut_pair_physicalX` | :1673/:1676 | `physicalX w = pos₀²/(2·physicalQ)`; nonzero cut pair ⇒ `physicalX w ∈ Ioo(activeLeft, activeRight)` | `physicalPosition_graph` + `profileRadius_sq`, `left² = 2·activeLeft` via `Real.sq_sqrt`, two `nlinarith` | OK — I re-derived: from `left < r < right` and `r > 0`, `(r-left)(r+left) > 0` and `(right-r)(right+r) > 0` give `left² < r² < right²`, then `/2` with the two `sq_sqrt` identities |
| `potential_amplitude_zero_exterior` P/p | :1711/:1723 | outside the active `physicalX` interval the amplitude at the canonical lift is `0` | `by_contra` + `cut_pair_physicalX` | OK |
| `copy_sum_zero_of_amplitudes_zero` | :1735 | all amplitudes zero at the canonical lifts ⇒ `f.sum = 0` | `globalWave_eq_zero` + `tsum_zero` + `finsum_zero` | OK — the hypothesis is stated at `commonLift h I.1.val.1 (f.gap I.1) w`, and for both families `f.gap = gap` by definition (:366/:374), so the instantiation at :1749/:1758 matches |
| `potential_zero_exterior` P/p | :1743/:1752 | the delivered fields vanish outside the active interval | previous + `vectorSum` | OK |
| `normal_withCutoff`, `cut_normal_lifted` | :1763/:1768 | the cutoff does not change the `normal` datum; lifted normal identification | `rfl` + `chart_normal_lifted` | OK |
| `graph_cartesian_forward` | :1784 | the graph of a cylindrical-chart point equals the "common graph" map of `z` | `commonLift_formula` (needs `d ≤ nativeIndex`, supplied by `gap_native`), `radius_polar`, `abs_of_pos hr` | OK (spot-checked; `abs_of_pos` uses `0 < z.2 0`) |
| `polarPoint_common_forward` | :1811 | same for the polar point, both components | `polarPoint_fst` + `cylinderAt_physical_forward` | OK (spot-checked) |
| `liftedPotential_eq_mode`, `physicalPotential_eq_mode` | :1841/:1861 | the lifted vector potential is `HarmonicCalculus.vectorMode` of `potentialCoefficient`; the physical potential is `Q^(-h) •` that mode | `cut_normal_lifted` + `referencePotential_eq_on` (needs `frequency ≠ 0`, supplied) | OK |
| `potentialCoefficient_angle` / `_polar`, `pressureCoefficient_polar` | :1881/:1889/:1998 | the coefficients do not depend on the angular slot ⇒ evaluating at `θ = 0` is harmless | `tsum_congr` + `copyPotentialCoefficient_angle` | OK — this retro-justifies the `(x, 0)` in `nativePotentialSource` :341 |
| `potential_periodized_of_chart` P/p | :1909/:1943 | the periodized value is chart-independent (any valid polar chart `j`, not only `chooseChart`) | `commonWave_charts_agree` using the **integer** angular mode from `carrier_integer` | OK (statement-level + mechanism; identical to :1636 which I verified) |
| `potential_periodized_mode` P/p | :1976/:2007 | periodized = `Q^shift • rotate(vectorMode …)` | `rotateCoefficient_vectorMode`, `potentialCoefficient_polar`, `smul_mul_assoc` | OK |
| `potential_periodized_cartesian` | :2027 | `Re(periodized) = cartesianPotential l.1 l.2 w i` on a valid chart with `0 < z.2 0` | `polarPoint_common_forward` + `rotateCoefficient_chart_re` + `globalPotential_forward` | OK |
| `pressure_periodized_physical` | :2066 | same for pressure; the two `Q` exponents **cancel** | `rpow_add` + `neg_add_cancel` + `rpow_zero` (:2086) | OK — explicit exponent bookkeeping `-(2·A h) + (2·A h) = 0` |
| `scaledRepresentative`, `_spec`, `exists_scaledRepresentative` | :2092-:2140 | a positive-radius representative `z` with `(z.1, chart z.2) = w`, angle in the chart window | `chart_radius_pos`, `arctan` bounds, `polar_chart`/`unscale_radial` | OK — gives a *constructive* witness, so the "positive radius" hypotheses downstream are not vacuous |
| `cartesianPotential_zero_of_common_zero` | :2144 | coefficient `= 0` at the graph point ⇒ the **pre-existing** cartesian potential is `0` at `w` | axis case via `globalCartesianPotential_zero_germ`; else via a representative + `physicalPotential_eq_mode` | OK — **important**: the off-annulus branch of the main identity proves *both* sides are zero |
| `potentialCoefficient_zero_off_annulus`, `pressureCoefficient_zero_off_annulus` | :2178/:2298 | off the annulus every copy vanishes, so the coefficient does | `tsum_congr … tsum_zero` + `cut_pair_annulus` contrapositive | OK |
| **`potential_periodized_eq`** | **:2200** | `Re(periodized at positiveIndex l) = cartesianPotential l.1 l.2 w i` **everywhere on `preterminal`** (annulus or not, axis included) | `by_cases` on annulus: inside → chart representative; outside → both sides `0` | OK — the strongest statement of the file; no vacuity in either branch |
| `physicalPressureCoefficient(_invariant)`, `physicalPressure_mode/_periodic`, `space_pack`, `physicalPressure_eq_of_chart_eq` | :2227-:2296 | pressure is `2π`-periodic in the angle, hence chart-representative-independent | `mode_fullTurn` with the **integer** angular mode; `calc` chain (:2285) I read in full: `f(z.2 0, z.2 1) → f(z'.2 0, z'.2 1)` via `periodic_value_of_polar_eq` and `hrad : z.2 0 = z'.2 0` from `radius_polar` + `abs_of_pos` on both sides | OK — the `calc` does not change the quantity: the endpoints are the same function `f` at two arguments proved equal-modulo-`2π` |
| `physicalPressure_zero_of_common_zero` | :2317 | cut pressure `= 0` ⇒ physical pressure `= 0` | `piece_physical_pressure` + `mul_eq_zero` resolved by `rpow_pos … .ne'` | OK — no division by a possibly-zero factor |
| **`pressure_periodized_eq`** | **:2345** | `Re(periodized) = physicalPressure l.1 l.2 z` for `z.1 < 1`, `0 < z.2 0` | annulus split as above + `physicalPressure_eq_of_chart_eq` | OK |
| `primaryIndex`, `_injective`, `eq_primaryIndex_of_data` | :2376-:2389 | `primaryIndex (label, sign) = positiveIndex (sign, label)`; injective; any index with a matching band and harmonic `= 1` **is** a `primaryIndex` | `bandLabel_injective`; `Subtype.ext` on the harmonic | OK — `SignedLabel = Fin 2 × Label` (`ActualPrimaryBounds.lean:33`), and the `(l.2, l.1)` swaps at :2377/:2406/:2533/:2772/:2808 are consistently *sign-first*. I checked this pairing at every occurrence; no transposition bug |
| `periodized_nonzero_copy` | :2391 | periodized `≠ 0` ⇒ some frequency term `≠ 0` | `by_contra!` + `tsum_zero` | OK |
| `potential_periodized_index` P/p | :2398/:2408 | periodized `≠ 0` ⇒ the index is a `primaryIndex` | previous + `potential_amplitude_data` | OK |
| **`periodized_sum_eq_active`** | **:2418** | the `finsum` over all indices collapses to a **finite** `Finset.sum` over `activeLabels … n` | `calc` (:2432, read in full): `finsum_eq_sum_of_support_subset` (support ⊆ image, via `hsource` + `activeLabels_cover`) then `Finset.sum_image` with injectivity | OK — both `calc` steps keep the same quantity; the support-subset side condition is proved, and `Finset.image` de-duplication is harmless because `primaryIndex` is injective |
| `potential_sum_eq_active` P/p | :2446/:2456 | instances | previous + `SupportData.periodized_support` | OK |
| `vectorSum_apply` | :2466 | `vectorSum f … w i = ((f i).sum …).re` | `Fin.sum_univ_three` + `fin_cases` + `simp` | OK (relies on `coordinateVector` being the standard basis; `realCoordinate_apply` is `rfl`) |
| `graph_smooth_of_strip`, `spatialCurl_finset_sum`, `primary_cartesianCurl_sum` | :2474-:2511 | graph is `C^∞` where the strip is met; curl of a finite sum is the sum of curls (needs differentiability of each term) | `graph_smoothAt`; `fderiv_fun_sum` **with** the per-term differentiability hypothesis | OK — termwise differentiation is justified, not assumed |
| **`potential_eq_active`** | **:2515** | `potential B N0 w = ∑_{l ∈ activeLabels … n} cartesianPotential l.2 l.1 w` for `w ∈ preterminal` with the graph in the strip | `vectorSum_apply`, `potential_sum_eq_active`, `map_sum` twice, then `potential_periodized_eq` termwise | OK |
| `potential_germ_eq_active`, `curl_eq_active` | :2537/:2547 | the same finite family represents the potential on a whole **neighbourhood**, so the curl may be taken termwise | `filter_upwards` on `preterminal_open` ∩ continuity of the graph; then `spatialCurl_congr` | OK — the germ upgrade is the right way to get the curl identity; both open sets are genuinely open |
| `pressure_eq_active` | :2556 | pressure version (hypotheses `z.1 < 1`, `0 < z.2 0`) | `pressure_sum_eq_active` + `pressure_periodized_eq` | OK — `ht : z.1 < 1` is passed where `w ∈ preterminal` is expected: **defeq**, since `preterminal = {w | w.1 < 1}` (`PhysicalWaveSum.lean:386`) |
| **`velocity_chart`**, **`pressure_chart`** | **:2572/:2595** | the finite sum of the per-label piece velocities/pressures at the common-graph point equals `Q n ^ (A h)` (resp. `Q n ^ (2 A h)`) times the frame-rotated curl of `potential` (resp. `pressure`) | `curl_eq_active`/`pressure_eq_active`, `map_sum`, `Finset.mul_sum`, then `piece_cartesian_velocity`/`piece_physical_pressure` termwise | OK **at this file's level**; the per-term scaling identity is imported (see Escalation E4) |
| `physicalX_eq_profileRadius_sq` | :2617 | `physicalX w = profileRadius(slowCoords)²/2` | `graph_q_eq` positivity, `mul_pow`, `Real.sq_sqrt`, `field_simp` with both `≠ 0` side conditions | OK — the only `field_simp` in the file, and both denominators are proved nonzero |
| `graph_mem_strip_of_activeX` | :2644 | `physicalX ∈ Ioo(activeLeft, activeRight)` (+ slow carrier) ⇒ graph in `strip.domain` | `sq_lt_sq₀` both directions with `0 ≤ r` and `left/right > 0`, `Real.sq_sqrt` | OK — converse direction of :1676, and the nonnegativity of `r` is proved (`radius_nonneg`), which `sq_lt_sq₀` needs |
| `potential_periodized_activeX` P/p | :2685/:2696 | periodized `≠ 0` ⇒ `physicalX` in the active interval | `periodized_nonzero_copy` + `cut_pair_physicalX` | OK |
| `periodized_sum_eq_active_of_support` | :2707 | the finite-collapse identity holds if *whenever some term is nonzero* the graph is in the strip | `by_cases` on `∃ I, … ≠ 0`; the all-zero case makes both sides `0` (using `hz` for **all** `I`, so the RHS terms vanish too) | OK — a genuinely weaker hypothesis, correctly handled; not a vacuity |
| `potential_sum_eq_active_slow` P/p | :2728/:2740 | instances of the above | + `graph_mem_strip_of_activeX` | OK |
| `potential_eq_active_slow`, `potential_germ_eq_active_slow`, `curl_eq_active_slow`, `pressure_eq_active_slow`, `velocity_chart_slow`, `pressure_chart_slow` | :2754-:2849 | same six top identities with `graph ∈ strip.domain` replaced by "slow-chart membership only" | as the non-`_slow` versions | OK |

Verdict counts over the 230 declarations: **OK 230, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0**
(as *local* verdicts: "the stated proposition follows from the cited imported facts by the
mechanism shown"). The three items I still want an expert to answer are in Escalations; none of
them is a defect *inside* this file's reasoning.

## Kernel-risk assessment

Repo-wide the parent found zero `native_decide`/`axiom`/`unsafe`/`partial`/`macro`/`elab`/
`syntax`/`set_option`. I re-ran the scan on this file: **all zero**, plus zero `sorry`, zero
`admit`, zero `termination_by`, zero `Acc.rec`, zero `decide`.

**(1) Recursive inductives / recursors / `Acc.rec` / structure eta.**
The file declares **no** `inductive` and **no** `structure`; it declares 7 *anonymous-constructor
records* of foreign structures (`potentialCells` :632, `pressureCells` :641, `potentialCarrier`
:987, `pressureCarrier` :995, `identitySourceChartOn` :1083, `potentialChart` :1112,
`pressureChart` :1119, `copyPotential` :898, `potentialWaveData` :1269, `pressureWaveData` :1299)
plus `where`-style instances for `potential_support` :832 / `pressure_support` :861. These are
plain structure-instance terms; the kernel checks them field by field (each field is a proof term
of an already-elaborated type). Structure eta is used implicitly by `rfl` lemmas such as
`copyPotential_field` :911, `potentialWaveData_vector` :1327, `pressureWaveData_pressure` :1330 —
eta for structures is a *definitional* rule in Lean 4 core, cheap, no recursion. Recursion appears
only through `Finset.sum` / `tsum` / `finsum`, which are library constants applied to abstract
arguments: the kernel never unfolds them to a fixpoint here, because no proof asks for a closed
value. `Fin.sum_univ_three` (:2470) and `fin_cases` (4 sites: :774, :2117, :2263, :2471) do force
tiny `Fin 3` / `Fin 2` case enumerations — bounded by 3 branches.

**(2) GMP `Nat` numeral arithmetic.** Largest integer literal anywhere in the file is **4**
(`4 ≤ …` band lower bound, `/4` in `innerRadius`). Numeral census: `0`×211, `1`×121, `2`×105,
`3`×33, `4`×4, nothing else. There is no `Nat.pow`, no `^` with a numeral base and large numeral
exponent (all `^` are `Real.rpow`/`zpow` with symbolic exponents `-h`, `-(2·A h)`, `p`, or `2`),
no `decide`, no `Nat.gcd`/`Nat.mod` chains, no `norm_num` on anything bigger than `4` (the 13
`norm_num` calls all prove things like `0 < 4`, `1/2 + 1/2 = 1`, `(0:ℝ) ≤ 2`). Peak kernel bignum
work: **nil**. `omega` (3 sites: :435, :765, plus one inside `near_self`) produces linear-arithmetic
certificates over ℕ with coefficients ≤ 4.

**(3) Custom metaprogramming.** None. No `macro`, `elab`, `syntax`, `notation`, `attribute` other
than the one at :28, no `set_option` (so no `maxHeartbeats`/`maxRecDepth` inflation and no
`debug.skipKernelTC` hiding here).

**The `Classical.propDecidable` local instance (:28) — what it actually affects.**
There are exactly **8 `if`-condition occurrences in definitions** (7 distinct conditions) in the file, and I enumerated all of them
plus all 20 `by_cases`/2 `split_ifs`/2 `classical`:

* `L ∈ active` — `carrier` :268, `sourceChoice` :283, `slowCell` :599, `profileRegion` :920.
  `active = Set.range bandLabel` (:234), so membership is an unbounded `∃`; **these four `dite`s
  can only get their instance from :28.** This is the real effect of the attribute.
* `I.1.2.val = 1` :284 (equality in `ℤ`, since `Harmonic H = ↥(Finset.Icc (-H) H)`,
  `PhysicalWaveSum.lean:343`) and `n = I.1.1.val.1` :290 (`ℕ`): decidable anyway; with :28 at
  default priority the classical instance may well shadow `instDecidableEqNat`/`Int.instDecidableEq`.
  Harmless — see next paragraph.
* `0 < x.1.1` :368, :376 (order on `ℝ`): `Real.decidableLT` exists in Mathlib but is itself
  classical/noncomputable, so nothing changes either way.

Does any `decide` get its instance from :28? **No — the file contains zero `decide`
occurrences** (regex `\bdecide\b`), zero `Decidable.decide`, zero `by decide`. Therefore the
classical instance can never reach the kernel as a *computation*; it only appears inside proof
terms as an opaque `Classical.propDecidable p` argument. Every place the `if`s are eliminated uses
`ite_eq_left` / `ite_eq_right` / `dite_eq_left` / `dite_eq_right` (41 occurrences), which in Lean core
v4.34 (`Init/Core.lean:1179-1216`) are proved by `match h with | isTrue _ => rfl | isFalse h' =>
absurd …` — i.e. they hold for an **arbitrary** `Decidable` instance and need no evaluation. All
these defs are already marked `noncomputable`, so the instance also does not create a
compilation obligation. The two `classical` tactic calls (:2430, :2720) add a local
`DecidableEq (WaveIndex 1)` for `Finset.image`/`by_cases`; again no kernel evaluation, and
`Finset.image`'s deduplication is mathematically irrelevant because `primaryIndex` is proved
injective (:2379) and `Finset.sum_image` is applied with that injectivity (:2444).

**Bottom line:** the kernel has to perform **no** risky computation to accept this file. Its work
is proof-term type-checking of ~2850 lines of elaborated terms, with `simp only`/`nlinarith`
certificates of trivial numeric size. Kernel-trust risk: **negligible**, confirmed by census
rather than assumed.

## Escalations

Ranked; each is a question the *rest of the development* must answer, not an error I found here.

**E1 (medium, modelling / cross-file). The two fields are *defined* to be identically zero for
lifted-time `≤ 0`, i.e. at and beyond the terminal time `t = 1`; is any downstream statement
applied across that boundary?**
`potentialFamily.amplitude` :368 and `pressureFamily.amplitude` :376 are `if 0 < x.1.1 then … else 0`.
Chasing the coordinate: `paddedPast = cylindricalDomain ∩ {0 < x.1.1}` :1172; `commonLift_mem_paddedPast`
:1214 obtains `0 < x.1.1` from `PhysicalMeanJetBounds.graph_time_pos` (`PhysicalMeanJetBounds.lean:226`),
whose proof is `graph_slow` + `div_pos (sub_pos.mpr hw)` with `hw : w.1 < 1` — and
`preterminal = {w | w.1 < 1}` (`PhysicalWaveSum.lean:386`), `physicalPosition_graph` :784 shows the
slow time is `(1 - w.1)/Q n`. (The projection identification is `rfl`-level:
`slowFast x = ((x.1.1, x.1.2.2.2), x.2)`, `PhysicalClassBounds.lean:623`, and
`cylindricalMap x = (cartesianRadius …, slowFast x)`, ibid.:637, so `(graph … w).2.1.1` *is*
`(commonLift … w).1.1`.) So the `else 0` branch is exactly `t ≥ 1`, and the docstring at :890
admits it ("zero on the unused future side"). Consequently `potential B N0` is discontinuous
across `t = 1` and every regularity claim here is confined to the **open** set `preterminal`.
*Precise question for an expert:* does any later file assert smoothness / the Navier-Stokes
equation / an energy identity for `potential B N0` on a set that is not contained in
`{w | w.1 < 1}`, or take a limit as `t → 1⁻` of a quantity that needs two-sided regularity?
*What would settle it:* grep every consumer of `InitialPhysicalData.potential` /
`.pressure` / `.potentialWaveData` (17 hits repo-wide) and check each domain hypothesis is
`⊆ preterminal`. In `ActualCandidateAssembly.lean:925-927` the consumer does
`(potential_smooth B N0).mono (fun _ hw => hw.1)`, i.e. it *narrows* the domain — consistent.

**E2 (medium, junk-value, resolved *inside* this file — record it as checked, not as a defect).**
The `else 0` branches are safe here for a checkable reason, and I want the parent's summary to say
*why* rather than "author says so":
(a) every theorem that reads the amplitude's *value* carries `0 < x.1.1` or `w ∈ preterminal` and
eliminates the `if` by `ite_eq_left` with a **proof** of the condition (:1069, :1078, :1200, :1212,
:1517, :1526, :1568, :1602);
(b) every theorem that reads the amplitude's *support* uses only the direction
"`amplitude ≠ 0` ⇒ information" (`potential_amplitude_data` :550 even *extracts* `0 < x.1.1` from
nonvanishing), which is exactly the direction a junk branch cannot corrupt;
(c) no consumer needs the value in the junk region: `sourceStrip_time` :1060 proves the source
domain implies `0 < x.1.1`, so on the chart domain the junk branch is unreachable.
*Residual question:* is there a consumer of the `CommonChart`/`SmoothData`/`SupportData` records
that instantiates them at a point with `x.1.1 ≤ 0`? That must be answered by whoever audits
`LocalPhysicalCopyBounds`/`PhysicalStageBounds` (the records' *own* field types are out of scope
here; I verified only that the fields supplied match those types syntactically).

**E3 (low-medium, modelling). The construction lives on exactly one harmonic.**
`sourceChoice` :284 returns `some` only when `I.1.2.val = 1`, and `Harmonic 1 = ↥(Finset.Icc (-1) 1)`
= `{-1, 0, 1}`. So amplitudes at harmonics `0` and `-1` are identically `0`, and the "wave sum" is
a single positive-frequency mode per band, made real by `Complex.re` (`vectorSum`,
`PhysicalCopyBounds.lean:622`; `pressure` :896). That is a legitimate convention (real part of a
single complex mode = the physical real wave), but it means the *reality* of the field comes from
`re`, not from a `±` conjugate pair. *Question:* does any later step compute `∂_θ` or a product of
two such fields and implicitly assume the `-1` harmonic is present (e.g. treating `Re(A e^{iφ})`
as if it were `A e^{iφ}` in a quadratic term)? *What would settle it:* check the nonlinear-term
files for `re` of a product vs product of `re`.

**E4 (low, cross-file exponent bookkeeping).** The top identities carry explicit rescalings:
`velocity_chart` :2581 has `Q n ^ (A h)` with `A h = 1/2 + h` (`CoordinateAlgebra.lean:18`) while
the potential family's own shift is `-h` (:369); `pressure_chart` :2604 has `Q n ^ (2·A h)`
against the family shift `-(2·A h)` (:377). For the pressure I could verify the cancellation
inside this file (`rpow_add` + `neg_add_cancel` at :2086). For the velocity the balance
`(-h) + (curl gains 1) = A h`? is *not* proved here; it is imported as
`ActualPrimaryCoherence.piece_cartesian_velocity` (used at :2593/:2833).
*Precise question:* does `piece_cartesian_velocity` really produce `Q ^ (A h)` from a potential
scaled by `Q ^ (-h)` under `spatialCurl` — i.e. is the curl's scaling exponent `+1/2` from
`D h = 1/2 - h` plus `-h`, giving `A h`? *What would settle it:* read
`ActualPrimaryCoherence.piece_cartesian_velocity` and `PhysicalCurlCovariance` and check the
`rpow` arithmetic there; a sign or a factor-2 slip in that single lemma would make the delivered
velocity the curl of a *differently* scaled potential, which is precisely failure mode A.

**E5 (low, anti-vacuity, cross-file).** Nothing in this file proves that the delivered fields are
*nonzero anywhere*. The strongest positive statements are identifications
(`potential_periodized_eq` :2200, `nativePotentialSource_active` :1418) — if
`ActualPrimaryCoherence.cartesianPotential` were identically `0`, every theorem here would still
hold, trivially. *What would settle it:* a lower bound / nonvanishing statement for
`ActualPrimary.attachedRawVelocity` or `cartesianVelocity` somewhere in the development. Whoever
audits `ActualPrimary*` should be asked for one explicitly.

## Residue (what I could not check, and why)

1. **Nothing is machine-checked.** No Mathlib on disk, `lake build` forbidden. So I cannot rule
   out that the file does not compile at all (a misnamed lemma, a failing `simp only`, a
   `nlinarith` that times out). Everything above is "the argument is *mathematically* the one
   claimed", not "Lean accepts it". Where I could, I verified that non-obvious lemma names really
   exist with the semantics used — e.g. `ite_eq_left`/`dite_eq_left` are core v4.34
   (`Init/Core.lean:1179/1204`, deprecated aliases `if_pos`/`dif_pos`), and `Real.sqrt_le_left`
   `: √x ≤ y ↔ x ≤ y ^ 2` (`Mathlib/Data/Real/Sqrt.lean:221` in an on-disk copy) matches its use at
   :698. I did **not** verify the ~180 project-internal lemma names this file imports.
2. **Structure field types.** The records at :632-:1325 supply fields to structures defined in
   `PhysicalCopyBounds`, `LocalPhysicalCopyBounds`, `PhysicalStageBounds`, `PeriodizedWaveBounds`,
   `LabelSumBounds`, `PhaseJetBounds`. I checked that the *supplied* proofs prove what their names
   claim, and that quantifier order is preserved where the file re-packages a bound (:125, :326,
   :951). I did **not** read those structure definitions, so a mode-B defect *inside* a structure
   (e.g. `SupportData` demanding `∀x∃C` where the mathematics needs `∃C∀x`) would not be visible
   from here. That is the single biggest blind spot of this scope.
3. **Imported analytic content.** `copyPotential_uniform`'s ancestors (`actual_local_inputs`,
   `inverse_carrier_local`, `fullEnvelope_le_one`), `commonWave_charts_agree`,
   `referencePotential_eq_on`, `globalPotential_forward`, `piece_cartesian_velocity`,
   `piece_physical_pressure`, `activeLabels_cover`, `graph_*` — all out of scope.
4. **Two passages read at statement + mechanism level only** (not re-derived line by line):
   :1790-:1832 (`graph_cartesian_forward`, `polarPoint_common_forward` coordinate algebra) and
   :1909-:1975 (the `*_periodized_of_chart` twins). Both are structurally duplicated elsewhere in
   the file at passages I did verify (:1636 resp. :2027), so a defect there would most likely be a
   *typo-level* coordinate slip rather than a structural error — but I did not check the
   `swapCylinder`/`commonGraph.map` component algebra of :1806-:1809 symbol by symbol.
5. **`vectorSum_apply` :2466** depends on `PhysicalWaveSum.coordinateVector` being the standard
   basis of `ProblemStatement.Space`; I read `realCoordinate_apply` (`rfl`) but not
   `coordinateVector` itself.
