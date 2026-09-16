# Worker report: `ns-variable-gauge-mean`

Target: `NavierStokes/VariableGaugeMean.lean` (3,004 lines, 190 declarations) in
`openai/NavierStokesAndEuler` @ `f9e8bc5`, clone `/home/gsm/.openclaw/workspace/repos/NSE`.
Read-only. **No Mathlib, no `lake build` on this box: every claim below is SOURCE-LEVEL and
UNBUILT.** All `file:line` citations were re-derived from the original (non-stripped) file with
`sed`/Python indexing and printed before being written down.

## Headline

**OK with two REFUTED premises in the brief and one instrument NOTE. No kernel risk, no
never-proved leaf hypothesis, no constant mismatch.**

1. **REFUTED — this file is not "estimate mass".** The brief says the target is "long
   `nlinarith`/`calc` chains over constructed constants". It is not. The whole file contains
   **17 lines with `nlinarith`** (every one a one-line `lt_div_iff₀`/`div_lt_iff₀` interval
   juggle, e.g. `VariableGaugeMean.lean:1320-1321`), **10 `calc` blocks** (longest is 4 steps,
   `:1612-1620`), **4 `field_simp`**, **1 `convert!`** (`:493`), **2 `norm_num`**. The mass is
   *structural*: fiber-localisation, germ rewriting, `ContDiffOn` composition, support
   propagation, and `MeanClass` transfer. Constants are assembled in exactly **16** `∃ K`
   theorems, and I read all 16 line-by-line.
2. **REFUTED — "asserted interchange of limits" is not possible here.** The file contains
   **zero** `Tendsto`, `atTop`, `iSup`, `⨆`, `⨅`, `limUnder`, `Cauchy`, `IsLittleO` (grep over
   all 3,004 lines). No limit is taken anywhere, so no swap can be asserted. The only
   quantifier-order question that exists is "is the constant fixed before the point?", and it is
   (§Findings F4/F5).
3. **NOTE — the brief's count.** The brief says "138 declarations that are `in_cone = True`".
   `INVENTORY.csv` for this file gives **169 in-cone declarations** = 138 in-cone *theorems* +
   30 in-cone `def`s + 1 in-cone `structure`; 21 declarations are `in_cone = False`. The 138 is
   the theorem count, not the declaration count. All 190 are `in_import_closure = True`.
4. **Kernel-risk: this file is the cheapest surface in the artifact.** Zero `inductive`, zero
   recursor application, zero `termination_by`, zero `WellFounded`, zero `deriving`, zero
   `decide`, zero `Nat.pow/div/mod/gcd`. **Largest closed numeral in scope = `5`**
   (`:2471`, `hclass.bounds (m + 5)`). Peak kernel numeral work is comparing naturals below 10.

## Scope

| Item | Count |
|---|---|
| Declarations in file (`INVENTORY.csv`) | 190 (156 theorem, 33 def, 1 structure) |
| `in_cone = True` | 169 (138 theorem + 30 def + 1 structure) |
| `in_cone = False` | 21 |
| **Read line-by-line, whole body** | **110** |
| Read partially (full statement + part of body) | 25 |
| Statement/grep only | 55 |
| Target lines actually displayed and read | 2,088 / 3,004 (69.5%) |
| Other files opened to check supplier statements | 11 |

Supplier files read at the cited lines: `WeightedRadialPrimitive.lean` (206-227, 378-400,
575-600), `RadialPullback.lean` (25-44, 578-594), `MeanRankUpdate.lean` (753-786),
`PhysicalCoordinateBounds.lean` (35-37), `SimilarityCoordinates.lean` (124-127),
`SimilarityHomogeneity.lean` (68-73), `MeanChartCompatibility.lean` (690-696, 742-747),
`WeightedClasses.lean` (60-136, 332-345, 402-408), `UniformFourierAlias.lean` (611-630),
`LocalSignedRequest.lean` (109-121), `ActualSignedGeometry.lean` (25-47),
`CorrectionInitialization.lean` (3414, 3955-3960).

### Sampling scheme (stated honestly)

I enumerated the distinct proof patterns mechanically (per-declaration tactic-feature table built
from the file text), then:

* **read EVERY instance** of the pattern that can hide a mathematical error, namely the
  **16 constant-assembly (`∃ K … refine ⟨K', …⟩`) theorems**, **all 10 `calc` blocks**, **all 4
  `field_simp`**, the **1 `convert!`**, **all 9 `:= rfl` sites and all 5 in-proof bare `rfl`
  lines**, and the **3 exponent/unit-factor lemmas** (`:917`, `:937`, `:944`);
* read **one full instance of each remaining pattern** (support propagation, germ/fiber-local
  rewriting, `ContDiffOn` composition, `MeanClass` transfer, naturality `coverPull`,
  `periodicOn`);
* the 55 grep-only declarations are all short (median 8 lines) instances of patterns audited
  elsewhere: `*_contDiffOn`, `*_fiberLocal`, `*_supportedGauge`, `*_periodicOn`,
  `meanClass_*` one-liners. Their statements were read; their bodies were not.
* I did **not** re-derive the audit's `in_cone` column or the import graph; the consumer census
  was delegated to a helper and every claim of it that I use below I re-verified myself.

## (A) What the file does, and who uses it

`VariableGaugeMean` builds the **similarity-dependent mean gauge**: instead of a fixed radial
annulus `[a,b]`, the cutoff/density/primitive endpoints are multiplied by a *slow-variable*
length `ell s`, and in the concrete case `ell = qLength coord = sqrt (coordinateQ coord ·)`
(`:172-173`). It defines `radialRatio`, `cutoff`, `density`, `SupportedGauge`,
`compactPrimitive`, `pressureSource`, `meanPressure`, `streamPotential`, `compactAlias`
(`:58-92`), packages the gauge in `structure GaugeData` (`:502`) plus the state constructors
`reconstructState`/`temporalIncrementState`/`temporalStageState`/`rankStageState`
(`:517-583`), and then proves, for the moving gauge: (i) it agrees with the fixed-endpoint
operator on each frozen slow fiber, (ii) smoothness (`ContDiffOn`), (iii) support
(`SupportedGauge`), (iv) periodicity, (v) chart naturality with explicit `Q n` unit factors, and
(vi) **uniform weighted all-order jet bounds** whose constant precedes every frequency, source,
amplitude and evaluation point. The technical core is
`transportGauge_finiteJets` (`:1252`) → `compactPrimitive_q_finiteJets_global` (`:1535`) →
`compactPrimitive_q_finiteJets` (`:1666`), lifted to the artifact's `MeanClass` bookkeeping by
`meanClass_compactPrimitive` (`:1692`) and the `meanClass_*` family, and finally exported as the
State theorems `reconstructState_pressure_change_class` (`:2822`),
`temporalIncrementState_classes` (`:2837`), `temporalIncrementState_supportedGauge` (`:2975`),
`temporalIncrementState_divergence_zero` (`:2959`).

**Consumers** (12 direct importers, 74 consuming files; I re-verified each line below):

| Consumer | Uses |
|---|---|
| `NavierStokes/CorrectionStep.lean:4647`, `:7557` | `reconstructState_pressure_change_class` |
| `NavierStokes/CorrectionStep.lean:5205`; `CorrectionInitialization.lean:3216`; `CorrectionInitializationNoOptions.lean:3227` | `temporalIncrementState_classes` |
| `CorrectionStep.lean:5211,:5352,:5467,:8075`; `CorrectionInitialization.lean:3490`; `…NoOptions.lean:3501` | `temporalIncrementState_supportedGauge` |
| `NavierStokes/ActualInitialMeanEquation.lean:118` | `temporalIncrementState_divergence_zero` |
| `NavierStokes/GaugeRadialResidualBounds.lean:110` | `reconstructState_radial_identity` |
| `NavierStokes/GaugeAliasDecay.lean:688` | `temporalAxialDifference_eq_dividedAlias` |
| `NavierStokes/MeanStageContinuation.lean:319-402,:564-606` | `GaugeData`, `temporalPotential`, `rankPotential`, `*_periodicOn`, `fderiv_apply_supportedGauge`, `divideRadius_*` |
| `RankStateCoherence.lean:464-486`; `TemporalStateCoherence.lean:513-560`; `CycleStateCoherence.lean:47`; `GaugeExcludedBounds.lean:155`; `GaugeAliasDecay.lean:673-781`; `GaugeMomentBalances.lean:153-164`; `ActualInitialMean.lean:49-67` | `similarityGauge`, `temporalStageState`, `rankStageState`, `pressureAliasState`, `qLength` |

Heaviest textual consumers: `CorrectionStep.lean` (340 references), `CorrectionInitialization.lean`
and `CorrectionInitializationNoOptions.lean` (305 each). 103 of the 190 declarations have no
external use at all — they are internal scaffolding, which is consistent with `in_cone = True`
because a headline theorem reaches them *through* the exported State theorems.

## (B) Per-declaration / per-pattern findings

| # | Site (`VariableGaugeMean.lean:` unless noted) | What I checked | Verdict |
|---|---|---|---|
| F1 | `:31,:37,:43` scale lemmas | `unfold; rw [show …]; ring`; `physicalCutoff_scale` correctly cancels `l^d` on both `rpow` factors | OK |
| F2 | `:58-92` the 9 gauge `def`s | each is a plain composition; `density` carries the `(ell z.2.1)⁻¹` Jacobian factor, `compactPrimitive` uses the *fiber* endpoints `ell z.2.1 * a`, `ell z.2.1 * b` | OK |
| F3 | `:343 compactPrimitive_reference`, `:384 compactPrimitive_contDiffOn`, `:2115 compactPrimitive_radial_identity`, `:2365 meanPressure_sub_on`, `:628/:673 *_coverPull` | the file's central move: freeze the slow fiber (`freezeSlow`), transport the fixed-endpoint theorem, come back with `*_fiberLocal … (fun _ _ => rfl)`. Applied consistently; `ContDiffOn.congr` used in the right direction at `:396` | OK |
| F4 | **all 16** `∃ K` theorems: `:414,:465,:772,:816,:1073,:1100,:1134,:1252,:1400,:1473,:1521,:1535,:1666,:215,:226,:2594` | the witness is built **before** `refine`/`intro`, so it cannot depend on the later binders. Sharpest instance: `:1288 let K := leftK + rightK + midK`, `:1297 refine ⟨K, hKK, ?_⟩`, `:1298 intro U hU ell hell hl hu M v f hf hs hsg A B hA hB z hz hR hin hcut j hj` — `K` precedes `U, ell, M, v, f, A, B, z, j` and depends only on `(p, m, a, b, c, e, cL, cR, L)` | OK |
| F5 | `NavierStokes/WeightedClasses.lean:111-113` `MemClass.bounds` | verbatim: `bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n x, x ∈ s.domain → ∀ j : ℕ, j ≤ m → …`. Constant chosen after the derivative order `m` only, before the band index `n` and the point `x`. This is the legitimate "fix the loss in terms of `m`, choose the rest afterwards" shape | OK |
| F6 | `:1252 transportGauge_finiteJets` (148 lines, the file's largest) | full audit. 3-way split on `logPosition ≤ ρ/2` / `≥ logLength − ρ/2` / middle is exhaustive; `hρL : ρ ≤ logLength a b / 2` (`WeightedRadialPrimitive.lean:593`) is exactly what the two `by linarith` at `:1345`/`:1369` need to meet the suppliers' `logLength a b / 2` thresholds (`:1079`, `:1106`); the middle branch's arithmetic `massK·A + 2^m·B·massK·A ≤ midK·(1+B)·A·δ` with `midK = massK(1+2^m)/δ` reduces to `1 + 2^m B ≤ (1+2^m)(1+B)`, which is `:1387`, and is true | OK |
| F7 | `:1535 compactPrimitive_q_finiteJets_global` (93 lines) | full audit. `Q := ((min 1 d)^p)⁻¹` at `:1567` is **exactly** the constant of `RadialPullback.lean:581 logWeight_power_forward`; used in the *forward* direction at `:1617-1619`. Final `_ = _ := by ring` matches `K = KP*KT*(1+B)*KN*Q` | OK |
| F8 | `:1134 normalizeSource_gauge_finiteJets` (63 lines) | `Q := ((min 1 d⁻¹)^p)⁻¹` at `:1148` is **exactly** `RadialPullback.lean:589 logWeight_power_reverse`, used in the *reverse* direction at `:1191`. The forward/reverse pair is not swapped — this was the sharpest available off-by-one trap and it is clean | OK |
| F9 | `:726 product_jet_bound` (the only combinatorial proof) | `∑_{i<j+1} C(j,i)·A·B = 2^j·A·B ≤ 2^m·A·B` via `Nat.sum_range_choose j` (`:748`) and `pow_le_pow_right₀ (by norm_num) hj` (`:751`). Leibniz input is `JetBounds.norm_iteratedFDeriv_mul_le_on` | OK |
| F10 | `:973 iteratedFDeriv_supportedGauge_fiber`, `:1005 iteratedFDeriv_zero_outsideGauge` | the load-bearing "support ⇒ all jets vanish outside" pair. Note `:1010` hypothesis is `z.1 ∉ Ioo (…)` (open) while the support is on `Icc` (closed); this is sound only because continuity is passed (`:1013`), and it is | OK |
| F11 | `:2284 cutoffRadialDerivative_interior_support` (56 lines) | trisection `cU=(2a^d+b^d)/3`, `eU=(a^d+2b^d)/3` (`:2290-2291`) pulled back by `d⁻¹` with `Real.rpow_rpow_inv`/`rpow_inv_rpow`; both `le_of_not_gt` branches use the matching one-sided vanishing lemma | OK |
| F12 | `:2629 localBandJets_compactAlias` (49 lines) | `⟨(2:ℝ)^m * B * K * C, by positivity, k, ?_⟩` (`:2652`); the `hp.trans_eq (by ring)` at `:2669` is `2^m·B·(K·(C·ε^α·L^k)) = (2^m·B·K·C)·ε^α·L^k`, correct (rpow treated as an atom) | OK |
| F13 | `:493-496` the only `convert!` | `convert! hp using 1; ring`. The LHS unification is pure delta of `physicalPast` (`:243-245` is literally `pastIntegral M v (normalizeSource d c f) (liftChart (powerChart d c) z)`), the `ring` closes `KP*KN*(e^d−c^d)*A = KP*(KN*A*(e^d−c^d))` | OK |
| F14 | the 4 `field_simp`: `:1040`, `:1388`, `:1981`, `:2189` | `:1040` `(M·l)(s − z.1/l) = M(l·s − z.1)`, needs `l ≠ 0` (passed as `hl`). `:1981` `C·ε^α·g^k = (C/δ·ε^α·g^k)·δ`, needs `δ ≠ 0` from `hδ : 0 < δ`. Both are true identities | OK |
| F15 | `:1035-1071` change of variable under the integral | `radialSlice_scaled` + `integral_scaled` + `mul_div_cancel₀`: `∫_{l·a}^{z.1} F = l • ∫_a^{z.1/l} F(l·s)`. The endpoint substitution and the `M ↦ M·l` frequency rescaling are consistent between `pastIntegral_scaled` (`:1043`) and `futureIntegral_scaled` (`:1058`) | OK |
| F16 | `:2013 meanClass_divideRadius_moving` | `c := sqrt U.qlo * a / 4` (`:2017`) so `2c = sqrt(qlo)·a/2 ≤ sqrt(qlo)·a ≤ z.1`; `RadialPullback.lean:38 positiveRadius_eq_self` needs exactly `2 * ℓ ≤ x`. The `/4` is the right constant, with margin | OK |
| F17 | `:2458 meanClass_temporalInverse_moving`, `:2471 hclass.bounds (m + 5)` | `UniformFourierAlias.lean:614` demands verbatim `(∀ j ≤ m + 5, ∀ p ∈ A, ∀ Y, …)`. The `+5` headroom matches the supplier exactly (a `+4` sibling exists at `:629` for `realCentered`, and is not used here) | OK |
| F18 | `:2784`/`:2853` the `α + 1` index shift | comes from `hi.band_smul hb` with `hb : BandBound st 1 ε` (`:2793-2796`), and `WeightedClasses.lean:335-336 band_smul : MemClass s w α f → BandBound s β a → MemClass s w (α + β) (fun n x => a n • f n x)`. One factor of `ε n` ⇒ exactly one power. Not an off-by-one | OK |
| F19 | `:617-624 meanPressure_congr_endpoints` | `subst a'; subst b'; rfl`. After the substitutions the two sides differ **only** in the proof terms `hab, hab' : a < b`, so this `rfl` is discharged by Lean's **definitional proof irrelevance**. It is the only non-delta definitional identification in the file | NOTE |
| F20 | `:2810 reconstructState_pressure_class` | `in_cone = False`, and grep over all 2,659 files finds **no** use outside this file. Only the *change* version (`:2822`) is consumed | NOTE / see E1 |
| F21 | `:2837 temporalIncrementState_classes` hypotheses | `hell : ∀ n, g.length n = qLength coord` (`:2806`) and `heps : c.operators.epsilon = ε` (`:2842`) are the two coupling hypotheses that stop a silent constant mismatch. Both have real suppliers (§C) | OK |

## (C) Numeric constants in statements, and consumer agreement

Exhaustive numeral census of the file (comment text stripped per line): the only integer literals
anywhere in the 3,004 lines are `0` (443×), `1` (74×), `2` (76×), `3` (4×), `4` (3×), `5` (2×).
There is **no** multi-digit literal and **no** decimal literal. Constants in *theorem statements*
are therefore only these, and they are:

| Constant, verbatim | Site | Consumer / supplier agreement |
|---|---|---|
| `1 / 2` in `hh1 : h < 1 / 2` | `:879`, `:896`, `:905`, `:917`, `:944` | `ActualSignedGeometry.lean:30-31` builds `standardSlowRegion {h} (hh : 0 < h) (hh1 : h < 1 / 2) : LocalSignedRequest.SlowRegion (2 * h)` and discharges `coord_lt_one := by linarith` (`:41`). `h < 1/2 ⟺ 2h < 1` — matches `SlowRegion.coord_lt_one` (`LocalSignedRequest.lean:115`) exactly |
| `2 * h` as the coordinate | `:881`, `:898`, `:907`, `:921`, `:923`, `:948`, `:950` | producer `similarityGauge … length := fun _ => qLength (2 * h)` (`:513`); consumers `MeanStageContinuation.lean:321` and `:362` require `hell : ∀ n, g.length n = VariableGaugeMean.qLength (2 * F.data.h)`; `ActualCurrentWaveSupport.lean:99,:104,:344` also use `qLength (2 * h)`. **No site uses `qLength h`.** |
| `2 * CoordinateAlgebra.A h + 1 / 2` → `2 * CoordinateAlgebra.A h` | `:924` → `:925` | `MeanChartCompatibility.lean:742-744 pressure_unit_factor : Q n ^ (-(2 * A h + 1/2)) / chartScale n = Q n ^ (-(2 * A h))`, and `chartScale n = Q n ^ (-(1/2 : ℝ))` (`MeanChartCompatibility.lean:690`). `−(2A+1/2) + 1/2 = −2A` ✓ |
| `CoordinateAlgebra.A h` → `CoordinateAlgebra.A h - 1 / 2` | `:951` → `:952` | `:937-942 stream_unit_factor : Q n ^ (-A h) / chartScale n = Q n ^ (-(A h - 1/2))`; `−A + 1/2 = −(A − 1/2)` ✓. The sign is right *only* because `chartScale = Q^(−1/2)`, not `Q^(+1/2)`; I checked the definition |
| `-1` and `-CoordinateAlgebra.D h` chart exponents | `:860-861` | matched by `SimilarityHomogeneity.lean:68-71 coordinateQ_scale_h : coordinateQ (2*h) (Q*τ, Q ^ D h * z) = Q * coordinateQ (2*h) (τ,z)`, applied with `Q := (Q n)⁻¹` at `:882-883`; the `sqrt` then produces exactly `chartScale n` (`:890-893`) |
| `d ^ 2 * cL`, `d ^ 2 * cR`, `a ^ d`, `b ^ d` | `:1143`, `:1595` | identical to `RadialPullback.lean:580` / `:590`. The `d^2` on the edge constants is the supplier's, not invented here |
| `(2 : ℝ) ^ m` | `:731`, `:827` | `product_jet_bound`'s own conclusion, consumed at `:1381`, `:848`, `:2665`, always as `2^m` |
| `m + 5` | `:2471`, `:2478` | `UniformFourierAlias.lean:614` requires `∀ j ≤ m + 5` |
| `/ 3` trisection, `/ 4`, `/ 2`, `+ 1` | `:1268`, `:2017`, `:2290-2291`, `:1491` | proof-internal witnesses, not in any statement; each verified in F11/F16 and in `qLength_reference_bounds` (`:1473-1503`) |

**Verdict: NO constant mismatch between this file and any consumer.** The `2001/1000`-vs-`2/1`
shape cannot occur here for a structural reason worth stating: the coupling is carried by a
*hypothesis* (`hell : ∀ n, g.length n = qLength coord`, `heps : c.operators.epsilon = ε`), so
Lean's elaborator unifies `coord` with `2 * h` at the instantiation site. A mismatch would be a
type error, not a silent wrong constant.

### Leaf-hypothesis trace (the `TailRates.flat_of_residuals` shape)

I checked the three exported results and the technical core. **No hypothesis without a supplier.**

* `temporalIncrementState_classes` (`:2837`): `hell` ← `CorrectionInitialization.lean:3960`
  `@[simp] theorem gauge_length (n : ℕ) : gauge.length n = VariableGaugeMean.qLength (2 * h) := rfl`
  (the gauge itself is built at `:3955-3958` with `length _ := VariableGaugeMean.qLength (2 * h)`),
  repackaged as the structure field `gauge_length : ∀ n, g.length n = qLength coord`
  (`CorrectionInitialization.lean:3414`) and used at `:3216`, `:3490`. `heps` ← discharged by
  `rfl` at `CorrectionInitialization.lean:3505`. `hcθ/hcz` (the input `MeanClass`) ← proved,
  not assumed, at the call sites.
* `reconstructState_pressure_change_class` (`:2822`): `hclass` is discharged at the consumer
  `CorrectionStep.lean:4647` (the surrounding `have` at `:4645-4646` produces it).
* `transportGauge_finiteJets` (`:1252`): its two quantitative premises both have suppliers *in
  this file* — the weighted source premise from `normalizeSource_gauge_finiteJets` (`:1134`,
  used at `:1600`) and the cutoff-jet premise `B` from `normalizedCutoff_q_finiteJets` (`:1521`,
  used at `:1562`, consumed at `:1602`).
* Contrast with the real defect elsewhere: `NavierStokes/GenericSupportedPolynomial.lean:130`
  takes `hres` with nobody proving it. Nothing of that shape occurs in this file.

**Disagreement with my own helper:** the consumer helper reported `meanClass_streamGamma` as
"dead; no external consumer". That is wrong and I am not repeating it. It is consumed *inside*
the file at `:2762` by `meanClass_temporalStreamGamma`, which is consumed at `:2861` by
`temporalIncrementState_classes`, which is consumed at `CorrectionStep.lean:5205`. Its
`in_cone = True` is correct. Same for `meanClass_scaledTemporalStreamBeta` (used at `:2858`).

## (D) Kernel-risk assessment (vectors 1/2/3)

### Vector (1): recursive inductives, recursors, iota reduction — **NIL**

| Probe (regex over all 3,004 lines) | Hits |
|---|---|
| `\binductive\b` | 0 |
| `\bstructure\b` | 1 — `:502 structure GaugeData (S : Type) where` (2 fields, non-recursive, no indices) |
| `\.rec\b`, `Acc\.rec`, `Nat\.rec` | 0 / 0 / 0 |
| `termination_by`, `WellFounded`, `let rec`, `match` | 0 / 0 / 0 / 0 |
| `\bderiving\b`, `Decidable`, `\bdecide\b` | 0 / 0 / 0 |

`GaugeData` is a plain product; its projections reduce by structure-eta, not by a recursor. There
is **no iota reduction anywhere in this file's proof terms** that originates in the file itself.
Cross-check: the audit's own `SITES_inductive.md`, `SITES_termination_by.md`,
`SITES_explicit_rec.md`, `SITES_deriving.md`, `SITES_wf_fix.md`, `SITES_motive.md` and
`DECIDE_SITES.md` all contain **zero** mentions of `VariableGaugeMean` — my sweep agrees with the
instrument.

The only definitional-equality checks the kernel must actually perform for this file are:

* **5 alias `rfl`s**: `:207-208 cutoff_q_eq_kernel`, `:210-211 density_q_eq_kernel`,
  `:872-873 physicalToChartTZ_swap`, `:1517-1519 normalizedCutoff_q_eq_kernel`,
  `:2590-2592 cutoffRadialDerivative_q_eq_kernel`. Each is an *equality of functions* closed by
  `rfl`, so the kernel must delta-unfold both sides and match under eta. I traced `:208` by hand:
  LHS `physicalCutoff d a b (z.1 / sqrt (coordinateQ coord z.2.1))`; RHS goes through
  `MeanRankUpdate.chartKernel coord g = (g ∘ PhysicalCoordinateBounds.inverseCoordinates coord) ∘ chartInput`
  (`MeanRankUpdate.lean:781-782`), `inverseCoordinates a p = (qCoord a p, p.2)` and
  `qCoord a p = coordinateQ a (p.1, p.2.2)` (`PhysicalCoordinateBounds.lean:35-37`), with
  `chartInput : ChartPoint →L[ℝ] ModelPoint` re-ordering `(R,((T,Z),Y)) ↦ (T,(R,Z))`
  (`MeanRankUpdate.lean:756-761`). The reduction is **delta + beta + structure projection only**
  (the `ContinuousLinearMap` `prod`/`comp`/`fst`/`snd` coercions), with no recursor and no
  numeral. `coordinateQ` is a `dite` over `Classical.choose` (`SimilarityCoordinates.lean:124-127`)
  and is never *reduced*, only matched syntactically. These 5 sites are exactly the ones the
  audit's `SITES_bare_rfl_proof.md` lists for this file — instrument agrees.
* **5 in-proof `rfl` lines**: `:624`, `:894`, `:903`, `:1448`, `:2239`. Four of these close a goal
  after an explicit `rw` chain and are delta/beta only. `:624` is different and is the one item I
  flag: it relies on **definitional proof irrelevance** to identify two distinct proof terms of
  `a < b` (F19). That is a sound rule of Lean's theory, but it is a genuine trust dependency
  distinct from delta reduction, and it is the only one in the file.

### Vector (2): `Nat` arithmetic delegated to GMP — **effectively NIL**

* `Nat.pow`, `Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.factorial`: **0 occurrences**.
* `Nat.choose` appears symbolically at `:733` and `:737` (`(j.choose i : ℝ)`, `j` a variable) and
  is eliminated by the library lemma `Nat.sum_range_choose j` at `:748` — no closed binomial
  coefficient is ever computed.
* Every power is either a `Real.rpow`/`Monoid.npow` on reals with a **symbolic** exponent
  (`(2:ℝ)^m`, `a^d`, `d^2`, `ε n ^ α`, `((min 1 d)^p)⁻¹`) or `Finset.range (j+1)` with symbolic
  `j`. `Finset.univ` sums are over `Fin (m+1)` with symbolic `m` (`:1276-1285`).
* **Largest closed numeral in scope: `5`**, at `:2471 obtain ⟨C, hC, k, hb⟩ := hclass.bounds (m + 5)`
  and `:2478 have hin : ∀ i ≤ m + 5, …`. Runner-up `4` at `:40` (`l * a / 4`) and `:2017`; `3` at
  `:1268`, `:2290-2291`.
* **Peak kernel numeral work, as a value:** the largest natural literal the kernel can be asked
  to evaluate here is `5`; the largest `Nat` comparison is `Nat.lt_succ_of_le hj` style on
  symbolic `j ≤ m` (`:1299`). Total closed-numeral arithmetic in this file is bounded by
  operations on values `< 10` — i.e. below any plausible GMP threshold, and the audit's
  `BIGNUM_SITES.md` and `SITES_bignum7.md` contain zero mentions of this file.

### Vector (3): custom metaprogramming — **NIL**

Zero `macro`/`elab`/`syntax`/`notation`/`run_cmd`/`#eval`/`set_option`/`native_decide`/`axiom`/
`opaque`/`unsafe`/`partial def`/`sorry` in the file (re-checked here, not taken on faith:
`sorry` = 0, `set_option` = 0, `@[simp]`-style attributes = 0 in this file). 34 `noncomputable`
markers, which *remove* compilation rather than add trusted code. The only non-standard tactic
in the file is `convert!` (`:493`, `:495`), which is `congr!`-based Mathlib, not local metacode.

**Conclusion for this scope:** a Lean 4 kernel bug in recursor/iota reduction or in GMP `Nat`
arithmetic could not turn any proof in this file into a fake, because the file exercises neither.
The only kernel rules it leans on are delta/beta/eta, structure-projection reduction, and (once,
at `:624`) `Prop` proof irrelevance.

## Escalations

**E1. Is the absolute pressure class of the reconstructed state ever needed?**
Question for an expert: `reconstructState_pressure_class` (`:2810`) proves
`MeanClass … α (reconstructState g c u).pressure` and is used **nowhere** in the repository
(`in_cone = False`; grep over 2,659 files returns only its own definition). Downstream only ever
uses the *difference* version `reconstructState_pressure_change_class` (`:2822`) at
`CorrectionStep.lean:4647,:7557`. Does the NS argument need an absolute (not just incremental)
weighted-class bound on the reconstructed pressure at any stage? Evidence that would settle it:
either (a) a downstream declaration whose hypotheses include a `MeanClass … (…).pressure` for the
reconstructed state — in which case this lemma should be wired in and its absence is a gap in the
chain — or (b) an explicit statement in the top-level theorem's proof that only pressure
*differences* enter the closing estimate. I can rule out (a) at source level for the current
tree; I cannot judge (b) without reading the top-level closure.

**E2. Do the 5 alias `rfl`s really reduce, or are they `Eq.refl` accepted for a subtler reason?**
Question: for `:208`, `:211`, `:1519`, `:2592`, confirm that the kernel closes the goal by
delta/beta/proj reduction of `ContinuousLinearMap` coercions only, and not by an `Eq.refl` whose
type was already unified during elaboration in a way the kernel re-checks differently. Evidence
that would settle it: with Mathlib available, `set_option pp.all true` on the elaborated term
plus `#print axioms` on each of the four theorems, or `whnf`/`isDefEq` traces showing the
reduction path. **Not checkable on this box (no Mathlib, no build) — UNBUILT.**

**E3. Proof irrelevance at `:624`.**
Question: is `meanPressure_congr_endpoints` (`:617-624`) intended to be a proof-irrelevance
identity, and is that acceptable to the reviewers' trusted-kernel model? It is the single place in
this file where two syntactically different terms (`hab`, `hab' : a < b`) are identified
definitionally. Evidence: Lean 4 core's definitional proof irrelevance rule is part of the
accepted theory, so this is a *classification* question rather than a defect; a reviewer who
excludes proof irrelevance from the trusted base must re-prove this lemma by `Subsingleton.elim`
or by making `meanPressure` not take `hab`.

**E4. `hclass.bounds (m + 5)` headroom.**
Question: is every supplier of a `MeanClass` used in this file genuinely all-order
(`∀ m, ∃ C, …`), so that asking for `m + 5` is always possible? Source-level the answer is yes by
the shape of `MemClass.bounds` (`WeightedClasses.lean:111`), but an expert should confirm no
consumer instantiates a *finite-order* surrogate class and then hits `:2471`. Evidence: a census
of the constructors of `MemClass`/`MeanClass` showing none is built from a bounded-order bound.

## Residue — what I could NOT check

1. **Nothing was machine-checked.** No Mathlib, no `lake build`, no `lake env lean` on this box.
   Every verdict above is a source-level reading. **UNBUILT.**
2. I cannot confirm that `positivity`, `field_simp`, `nlinarith`, `linarith`, `ring`, `simp only`
   and `convert!` actually close their goals. I verified the *mathematical content* of each such
   step by hand (F6, F7, F8, F12, F13, F14, F16), but a tactic can fail for reasons invisible in
   the source, and conversely a tactic could be closing a *different* goal than the one I
   reconstructed from the surrounding `rw` chain.
3. **55 of 190 declarations were statement/grep-only** (listed here for the record):
   `cutoff_eq_scaled, density_eq_scaled, density_integral, radialRatio_contDiffOn,
   cutoff_contDiffOn, density_contDiffOn, density_supported, pressureSource_supported,
   physicalPast_contDiff, physicalTotal_contDiff, compactPrimitive_fiberLocal,
   physicalPast_fiberLocal, physicalTotal_fiberLocal, freezeSlow_contDiff, meanPressure_eq_fixed,
   streamPotential_eq_fixed, normalizedCutoff, transportGauge, normalizedCutoff_contDiffOn,
   meanClass_pressureMass_moving, chartKernel_unweighted_moving, inverseLength_unweighted_moving,
   density_meanClass_moving, pressureSource_q_contDiffOn, meanPressure_q_contDiffOn,
   meanPressure_q_supportedGauge, meanClass_pressureSource, meanClass_meanPressure,
   compactPrimitive_periodicOn, pressureSource_periodicOn, meanPressure_periodicOn,
   streamPotential_periodicOn, meanClass_streamBeta, fderiv_eq_on_radialFiber,
   graphDr_eq_on_radialFiber, divideRadius_fiberLocal, divideRadius_contDiffOn,
   deriv_physicalCutoff_scale, cutoffRadialDerivative_contDiffOn, SupportedGauge.sub,
   meanClass_temporalAtIndex_moving, temporalAtIndex_fiberLocal, temporalAtIndex_supportedGauge,
   temporalAtIndex_contDiffOn, temporalAtIndex_fast_cancellation_on, cutoffRadialDerivativeModel,
   cutoffRadialDerivativeModel_contDiffOn, cutoffRadialDerivative_q_eq_kernel,
   cutoffRadialDerivative_q_finiteJets, compactAlias_q_contDiffOn, compactAlias_q_supportedGauge,
   meanClass_dividedCompactAlias, streamPotential_supportedGauge, reconstructState_radial_identity,
   temporalAxialDifference_eq_dividedAlias`.
   None of them assembles a new constant (they are `def`s, `*_contDiffOn`, `*_fiberLocal`,
   `*_supportedGauge`, `*_periodicOn` and `meanClass_*` one-liners); but I have not read their
   bodies and a defect could hide in one.
4. **The suppliers are out of scope and unaudited by me.** The correctness of this file is
   conditional on `WeightedRadialPrimitive` (the `weight`/`zeta`/plateau machinery, in particular
   `transport_past_left_uniform` at `:721` and `middle_weight_lower_bound` at `:217`),
   `RadialPullback`, `PhysicalMeanDomain`, `TransportPrimitive`, `MeanChartCompatibility`,
   `MeanRankUpdate`, `UniformFourierAlias`, `WeightedClasses` and `SimilarityCoordinates`
   (whose `coordinateQ` is a `Classical.choose` of `exists_positive_solution`). I read only the
   *statements* I cite from them.
5. I did not verify `movingStripData`'s field values (e.g. that `st.epsilon = ε` and
   `st.zeta = …`) beyond observing that `rfl`/`exact he` at `:1983` and `:2796` typechecked in the
   accepted build. If `movingStripData` were mis-wired, several `MeanClass` transfers would be
   about the wrong strip. This is the largest single unchecked assumption in my scope.
6. I did not audit the secondary target `NavierStokes/HarmonicResidual.lean` myself; it was
   delegated to a separate worker (`workers/ns-harmonic-residual.md`).
7. **Instrument NOTE, offered to the audit rather than to the artifact:**
   `audits/nse-deep/SITES_choose_fact.md` is titled "`choose_fact` sites (6)" and lists 6 rows,
   but the `choose_fact` column of `INVENTORY.csv` has **534 hits across 321 declarations**,
   including `VariableGaugeMean.lean:726` (2) and `:1252` (2). The site file appears to be a
   `Nat.factorial`-only subset, and `Nat.sum_range_choose` (e.g. `:748`) is absent from it.
   Do not read that file as the binomial/factorial census; read the column.

## Verdict counts

| Verdict | Count | Items |
|---|---|---|
| OK | 17 | F1-F18 minus F19/F20 |
| NOTE | 4 | F19 (proof irrelevance), F20 (unused `reconstructState_pressure_class`), brief's 138-vs-169 count, `SITES_choose_fact.md` subset |
| REFUTED | 2 | "estimate mass / long `nlinarith` chains"; "asserted interchange of limits" (impossible: 0 limit operators) |
| KERNEL-RISK | 0 | — |
| ESCALATE | 4 | E1-E4 |
| UNCLEAR | 0 | — |


## Secondary target: `NavierStokes/HarmonicResidual.lean` (delegated, then re-verified by me)

I delegated the secondary file to a worker; its full report is
`workers/ns-harmonic-residual.md` (verdicts OK 54 / NOTE 4 / UNCLEAR 1 / ESCALATE 2 /
KERNEL-RISK 0, 173/173 declarations read). I re-derived its load-bearing claims myself before
relaying them, and I **enlarge one of them**:

* **CONFIRMED and ENLARGED — a structure with no supplier, shadowed by a weaker twin.**
  `NavierStokes/HarmonicResidual.lean:1461 structure ExtractionRegular` requires **global**
  support separation, verbatim at `:1472-1473`:
  `disjoint : ∀ l ∈ labels n, ∀ j ∈ labels n, l ≠ j → Disjoint (tsupport ((blockFamily l).oscillation n)) (tsupport ((blockFamily j).oscillation n))`.
  `NavierStokes/LocalResidualGrouping.lean:210` declares a **same-named** structure that is
  identical field-for-field except `:220-222`, which asks only for
  `Disjoint (liftDomain U ∩ tsupport …) (liftDomain U ∩ tsupport …)` — i.e. separation only inside
  the valid lifted domain. So the `HarmonicResidual` version is *strictly stronger*.
  **Nothing in the 2,659-file repository ever constructs `HarmonicResidual.ExtractionRegular`**
  (grep: every occurrence is a hypothesis `(h : …)`; the single occurrence in conclusion position,
  `AxisymmetricResidualGrouping.lean:142`, is a transfer that already assumes one at `:140`).
  The **weaker** twin, by contrast, **is** produced by a real theorem:
  `ActualInitialization.lean:848-849 theorem initial_extraction_regular (B N0 n : ℕ) : LocalResidualGrouping.ExtractionRegular strip.domain (ActualPrimary.commonContext B) …`,
  and is consumed at `ActualCycleResidualBounds.lean:269,:311,:702`.
  **My enlargement:** the worker localised the unsupplied cluster to three in-file theorems. It is
  much wider — `HarmonicResidual.ExtractionRegular` is assumed at **21 sites in 5 other files**:
  `AxisymmetricResidualGrouping.lean:140,:167,:196,:218,:238,:266`;
  `CorrectionStep.lean:1410,:1424,:1520,:1533,:3122,:9250,:9258`;
  `PhysicalResidualJetBounds.lean:129,:694`; `HarmonicWaveInteraction.lean:1123,:1124`;
  `HarmonicMeanInteraction.lean:619,:620`; plus `HarmonicResidual.lean:1479,:1492,:1512,:1545,:1600`.
  **Direction of safety:** the *live* chain is the `LocalResidualGrouping` one, which assumes
  *less* and therefore proves *more*, so no false theorem results; the `HarmonicResidual` cluster
  is a superseded parallel copy. `CorrectionStep.lean:9250/:9258` (Harmonic version) sitting
  directly beside `:9268/:9276` (LocalResidualGrouping version) is visible evidence of an
  incomplete migration. This is **not** the `flat_of_residuals` defect shape — it is dead weight,
  not a conditional claim — but it does mean `in_cone = True` on that cluster is a false positive.
* **CONFIRMED — kernel surface nil.** My own sweep of `HarmonicResidual.lean` reproduces the
  worker: 0 `inductive`, 0 `.rec`, 0 `termination_by`, 0 `WellFounded`, 0 `deriving`, 0 `decide`,
  0 `Nat.pow`, 0 `Tendsto`. **Largest closed numeral = 3** (38 occurrences, all `Fin 3`). The only
  arithmetic tactic call in the file is `:1567 have he : 2 ^ stage + 2 ^ stage = 2 ^ (stage + 1) := by omega`
  — symbolic exponent, true identity, no closed-numeral work. (Whether `omega` really discharges a
  symbolic-exponent power is elaborator behaviour I cannot check: UNBUILT.)
* **CONFIRMED — the brief's pattern list does not fit that file either:** 0 `nlinarith`,
  1 `field_simp`, 2 `convert`, 1 `calc`, 0 `Tendsto`.
* **CONFIRMED — the in-cone count discrepancy is systematic, not a one-off.** The parent brief said
  "112 in-cone" for `HarmonicResidual.lean`; `INVENTORY.csv` gives **112 in-cone theorems** and
  **161 in-cone declarations** (of 173: 124 theorem, 40 def, 6 structure, 3 abbrev). Exactly the
  same relationship as this file's 138 vs 169. The audit's briefs quote in-cone *theorem* counts;
  the instrument is right, the wording is what misleads.
