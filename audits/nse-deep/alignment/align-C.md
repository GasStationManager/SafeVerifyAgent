# align-C — paper §6/§7/§8 vs. the Lean formalization

Auditor slice: Sections 6, 7, 8 of the published PDF (auxiliary torus and support
separation; oscillatory realization and correction of the residual stress;
compactly supported mean corrections).

Repos read-only. Lean cites as `file:line`, paper as `p<page>`.

**Seed-JSON noise corrected by reading the body.** Four of the seeded entries in
`paper-statements.json` were captured off section prose or a symbol table and are
*not* the numbered statements: `6.6` (captured p62 = §6 intro; the real
Proposition 6.6 is the class algebra, p71–72), `7.7` (captured p73 = §7 intro;
the real Lemma 7.7 is the exact-curl lemma, p86), `8.1` (captured p20 = symbol
table; the real Proposition 8.1 is the mean momentum equations, p89), `8.2`
(captured p88 = §8 intro; the real Lemma 8.2 is the compact radial primitive,
p90). All rows below are against the body text.

---

## 1. Summary table

| # | kind | page | Lean counterpart(s) `file:line` | class | one-line how |
|---|---|---|---|---|---|
| 6.1 | Lemma (slot separation) | p65 | `NavierStokes/SlotGeometry.lean:282` `exists_common_radius`, `:410` `exists_oriented_slots`, `:454` `colored_labels_have_slots`; `NavierStokes/SlotColoring.lean:167` `colorData_proper`, `:446` `physical_labels_have_auxiliary_slots`; `NavierStokes/PartitionedCovariance.lean:297` `masks_force_adjacency`, `:323` `SlotSystem.cross_product_zero` | **LEAN STRONGER** | explicit rational centers on `Y₂=0`, explicit 2250-colour palette, explicit `∆max` (`nativeGap`); the paper's `Kγ∩Kγ'≠∅ ⇒ Rᵃᵇˢ⁺ disjoint` is closed by `masks_force_adjacency`, which derives `|ℓ−ℓ'|≤4` from the dyadic line-mask supports |
| 6.2 | Lemma (common torus) | p67 | `NavierStokes/TorusCoverDegree.lean:208` `card_fiber`, `:247` `pairwise_disjoint_sheetRectangles`, `:274` `covering_bijOn_sheetRectangle`, `:296` `card_liftedRectangles`, `:302` `card_liftedRectangles_le`; `NavierStokes/TorusAverages.lean:94` `integral_torusCovering_iterate`; `NavierStokes/TorusCoverLattice.lean:59` `indexHom_range_index` | **LEAN STRONGER / partly ROUTED AROUND** | `14^Δ` is an exact count plus a sheetwise bijection (paper only claims "consists of `14^Δℓ` disjoint lifts"); Haar agreement (6.19) is proved; the *derivative-factor* and *operation-preservation* clauses are dispersed (see §2) |
| 6.3 | Lemma (number of relevant labels) | p68 | `NavierStokes/LabelCounting.lean:231` `pointwise_count`, `:164` `compact_chart_count`, `:173` `bounded_radial_count`, `:259` `number_of_relevant_labels`, `:285` `..._restrict` | **EXACT** (but **off the headline path**) | all three bounds with the paper's quantifier order; `LabelCounting.lean` is reached only through `PaperAdditionalResults.lean`, not through `ComparatorSolution` |
| 6.4 | Definition (`Mα`, `Sα`) | p69 | `NavierStokes/WeightedClasses.lean:107` `MemClass`, `:116` `MeanClass`, `:122` `UnweightedClass`, `:147` `of_separate_bounds`, `:131` `BandBound` | **LEAN WEAKER (definition is broader)** | the Lean class is the *size bound only*: `∂θf=0`, common-torus descent/(6.20), zero-extension across the shell, and support containment are **not** part of the class |
| 6.5 | Definition (`Wα`) | p70 | `NavierStokes/WeightedClasses.lean:118` `WaveClass` (weight `√ζ·P`) | **LEAN WEAKER (definition is broader)** | same omissions as 6.4, plus `supp(aγ,m|Eγ)⊂Ωγ` and the cut-off/"no divisibility" conventions carried separately |
| 6.6 | Proposition (class algebra) | p71 | `NavierStokes/WeightedClasses.lean:204` `add`, `:299` `bilinear`, `:413` `WaveClass.bilinear_mean`, `:440` `MeanClass.bilinear`, `:450` `MeanClass.bilinear_wave`, `:228` `fderiv`, `:256` `directional`, `:335` `band_smul`, `:476` `MemClass.graphDerivative`, `:498` `graphIterate`; `NavierStokes/PartitionedCovariance.lean:323` (cross-label) | **EXACT, assembled** | every row of (6.30)–(6.32) exists, but as separate lemmas; there is no single statement of the (6.32) table |
| 7.1 | Lemma (phase + frame) | p75 | `NavierStokes/PhaseCalculus.lean:44,103,109,148,166,212,289,301`; `NavierStokes/BasePhaseGeometry.lean:464` `LargeBand`, `:474` `exists_large_band`, `:732` `phase_estimates`, `:842` `modal_errors`, `:875` `damping_error`, `:1069` `frame_jets`, `:1088` `coefficient_jets` | **EXACT** | (7.9) normal/normal-motion, (7.10) `diag(λ,−λ)+E`, (7.11) damping, single band threshold chosen *after* all constants and before band/label/point |
| 7.2 | Proposition (pulse inverse) | p77 | `NavierStokes/PrimaryODE.lean:380` `energy_bound`, `:528` `homogeneous_forward_bound`, `:209` reconstruction; `NavierStokes/TangentODE.lean:279` uniqueness, `:323`; `NavierStokes/CommonCoverSolve.lean:968`; `NavierStokes/LinearWaveBounds.lean:896` | **EXACT (spot-checked)** | Volterra solution on the whole finite interval, exact reconstruction into (7.5), propagator bound `≤C·P(v)/P(w)` uniform in every nonzero harmonic |
| 7.3 | Corollary (domain independent of `M`) | p80 | `NavierStokes/PrimaryODE.lean:526` `homogeneous_forward_bound` ("the same forward propagator constant applies to every nonzero harmonic"), `:378`, `:999`, `:1107`; `NavierStokes/BasePhaseGeometry.lean:474` `exists_large_band` | **EXACT in substance / NO SINGLE COUNTERPART** | the two facts the corollary asserts are theorems; the corollary itself ("no shrinking of `q*`") is not restated as one declaration |
| 7.4 | Lemma (homogeneous pulse) | p80 | `NavierStokes/PulseGrowth.lean` (draft Lemma 8.5, `netGrowth`); `NavierStokes/PrimaryCovarianceBounds.lean:526` `canonicalPrimaryPulse_x_radial`, `:535` `canonicalPrimaryPulse_ratio`, `:554` `canonicalPrimaryPulse_bounds`; `NavierStokes/GrowingMode.lean:429` (ratio error of (7.21)); `NavierStokes/GaussianEnvelope.lean` (7.16) | **EXACT (spot-checked)** | `cP ≤ x ≤ CP` and `y/x = c₀√(1+s²)+O(S⁻¹)` present as the canonical-pulse bounds |
| 7.5 | Proposition (positive amplitudes) | p82 | `NavierStokes/Covariance.lean:29–221` (exact model); `NavierStokes/PulseCovariance.lean`; `NavierStokes/PrimaryCovarianceBounds.lean:321` `normalizedPair_entry_error`, `:337` `ZeroOrderBounds`, `:385` `compact_chart_pair_bounds`, `:639` `compact_native_primary_bounds`, `:724` `scalar_cone_model`; `NavierStokes/FlatCovariance.lean`; `NavierStokes/SmoothCovariance.lean` | **EXACT, but split — read the two disclaimers** | the *perturbed* statement (det gap, `‖H⁻¹‖`, positive weights with the flat weight retained) is `compact_chart_pair_bounds`; `Covariance.lean` and `SmoothCovariance.lean` each disclaim covering the manuscript's integrated columns, so citing either alone would understate what is proved and overstate what each file does |
| 7.6 | Proposition (linear inverse `LΣ`) | p84 | `NavierStokes/SignedCovariance.lean:377` `chartStress`, `:382` `physical_signed_scale`, `:409` `physical_signed_cross_covariance`, `:623` `increment_wave_class`, `:656` `signed_square_class`, `:731` `balanced_native_signed_square_class` | **EXACT** | `B(W₀ᵃˢ, Lᵃˢσ)=σ` proved at the assembled physical level with the constructed squared partition; `C(ηβLΣ)∈M_{2α−1}` is `signed_square_class` |
| 7.7 | Lemma (exact curls) | p86 | `NavierStokes/OscillatoryCurl.lean:160` `wave_eq`, `:188` `wave_divergence_free`, `:224` `wave_tsupport_subset`; `NavierStokes/CurlClassBounds.lean:758` `curlRemainder_waveClass`, `:774` `realizedCoefficient_waveClass`; `NavierStokes/CurlGeometry.lean:74` (double cross) | **EXACT** | `Cm∈W_{α+1/2}`, `rm∈W_{α+1/2−κ}`, exact divergence-freeness of `curl∗Am` including after phase evaluation |
| 7.8 | Corollary (covariance expansion) | p87 | `NavierStokes/SignedCovariance.lean:409` + `:656`/`:696`; `NavierStokes/HarmonicCovariance.lean`; `NavierStokes/CrossBasedMeanComposition.lean` ("retains its literal difference and its radial divergence") | **EXACT in substance / NO SINGLE COUNTERPART** | the algebraic expansion (7.41) is trivial given `B(W₀,LΣ)=Σ`; the three class bounds (7.42) exist individually; I found no one declaration stating (7.41)+(7.42) together |
| 8.1 | Proposition (mean momentum equations) | p89 | `NavierStokes/MeanIncrementBounds.lean` (equation (32)); `NavierStokes/LiftedMeanResidual.lean:820` `MeanHypotheses`, `:1174` `angularMean_fullResidual`, `:1188` `angularMean_fullGoodResidual`; suppliers `NavierStokes/ActualInitialization.lean:1400`, `NavierStokes/CycleMeanEquation.lean:523` `next_meanHypotheses`, `:548` | **EXACT (hypothesis structure IS supplied)** | the angular mean of the full residual equals (8.3) exactly; `MeanHypotheses` is constructed for the actual initial state and propagated through the cycle |
| 8.2 | Lemma (compact radial primitive) | p90 | `NavierStokes/RadialPrimitive.lean`; `NavierStokes/WeightedRadialPrimitive.lean`; `NavierStokes/PressureStream.lean:383,406`; `NavierStokes/UniformFourierAlias.lean:1134` `meanClass_alias_superflat`, `:1230` `realMeanClass_alias_superflat`, `:1278` `..._of_integratedMean_zero`, `:1309` `radial_..._of_integratedMean_zero` | **EXACT** | (8.7) exact with the alias retained; (8.8) as "for every jet order `m` and every flatness order `N`, eventually `‖D^j A_e f‖ ≤ C ε^N`", matching the paper's "no estimate uniform in `p`" |
| 8.3 | Proposition (pressure, axial velocity) | p92 | `NavierStokes/PressureStream.lean:36` `rho` (integral one, constructed), `:154` `pressureSource`, `:181` `pressureSource_mass_zero`, `:383` `meanPressure`, `:406` `meanPressure_radial_residual`, `:321` `stream_divergence_zero`, `:437` ff. | **EXACT** | the bump is *constructed* with `∫ρ=1` (no normalization premise); (8.13) retains the alias with its sign; (8.14)'s divergence-freeness is an identity, not an estimate |
| 8.4 | Proposition (integrated equations) | p94 | `NavierStokes/IntegratedMeanBalances.lean:639` `integrated_angular_balance`, `:674` `integrated_axial_balance`, `:735` `integrated_axial_reconstructed`, `:833`/`:843` positive-half-line versions, `:931` `integrated_axial_constructed_pressure` | **EXACT** | (8.16) with `M_θ=0`, `M_z=0` as hypotheses and `c_ρ` kept inside `∂_Z` |
| 8.5 | Corollary (covariance targets) | p95 | `NavierStokes/SignedStressPrimitive.lean:1014` `axial_bump_identity`, `:1030` `axial_bump_constructed_pressure_identity`, `:1047`/`:1066` improved classes; `NavierStokes/LocalSignedRequest.lean:591` `requestedStress` | **EXACT (spot-checked)** | the compactly supported signed-stress primitive with the bump subtraction and the two bump identities |
| 8.6 | Lemma (fast-time inverse) | p95 | `NavierStokes/TorusInverse.lean:195` `vector`, `:234` `reciprocal_symbol_bound`, `:301` `directionalInverse`, `:323` `directionalInverse_solves`, `:503` `inverse_derivativeWord_bound`, `:574` `inverse_zero_mean`, `:586` `zero_mean_series_has_smooth_inverse`; `NavierStokes/SmoothFourierData.lean:351` `rapid_coefficient`, `:368` `coefficient_seminorm_bound`, `:494` `inverse_solves_smooth_torus`, `:566` `inverse_solves_smooth_periodic`; `NavierStokes/ParametricTorusInverse.lean`, `NavierStokes/SmoothFamilyTorusInverse.lean` | **LEAN WEAKER (two narrow points)** | (a) **uniqueness is not proved** — only existence of a zero-mean smooth solution; (b) the `C^m ≤ C‖F‖_{C^{m+4}}` bound is not stated with that exponent: the composite available is `C^{m+5}` (multiplier costs one weight, summability uses `weight⁻⁴` rather than the paper's `(1+|k|)⁻³`) |
| 8.7 | Lemma (five-row moment inverse) | p97 | `NavierStokes/FiveProfileMoments.lean:260` `Coeff`/`Debt`, `:263` `GoodExponent`, `:267` `good_outgoing`, `:273`/`:274` power lists, `:300` `linearEquiv`, `:342` `normalizedMap`, `:358` `normalizedMap_identity`, `:706` `normalizationLinearMap`, `:805` `compact_parameter_repair`; `NavierStokes/PowerMomentMatrix.lean:*`; `NavierStokes/SmoothPowerMomentMatrix.lean` | **LEAN STRONGER / restated** | the linear solve is a `≃L[ℝ]` (existence + uniqueness + continuity at once); Lean additionally carries the *quadratic* self-interaction that the paper defers to Lemma 8.8; the power lists are stated in a squared-radius variable (§2) |
| 8.8 | Lemma (updated defects) | p98 | `NavierStokes/MeanIncrementBounds.lean` (the exact residual difference), `NavierStokes/DefectIncrementBounds.lean:314`, `NavierStokes/MeanLocalDefectBounds.lean` (whole file), `NavierStokes/MomentRepair*.lean` | **EXACT (spot-checked)** | (8.26)/(8.27) as an exact difference identity; `MeanLocalDefectBounds` imposes the base bounds only on the azimuthal potential's support, exactly as the paper's last paragraph requires |

---

## 2. Per-statement notes (non-EXACT rows, and EXACT rows where the comparison hinges on wording)

### 6.1 — LEAN STRONGER, with the one implication that had to be checked

Paper (p65): *"there exist centers `cγ` and a radius `r0 > 0`, **common to all labels and
independent of the band**, such that the enlarged rectangles in (6.10) are injectively
parametrized and `γ≠γ′, Kγ ∩ Kγ′ ≠ ∅ ⟹ Rᵃᵇˢ⁺_γ ∩ Rᵃᵇˢ⁺_γ′ = ∅`."*

Lean's capstone (`SlotColoring.lean:446`) quantifies in the paper's order —
`∃ r, 0 < r ∧ ∀ L M, Adj D L M → Disjoint (liftedSupport …) (liftedSupport …)` —
so `r` precedes the labels and the band. Injectivity of the padded parametrization
is the second conjunct of `SlotGeometry.exists_oriented_slots` (`:410`).

The one place the Lean could have been weaker is the *antecedent*. `SlotColoring.Adj`
(`:116`) is not "`Kγ∩Kγ′≠∅`"; it is a five-field structure that **assumes**
`L.1 ≤ M.1 + 4` and `M.1 ≤ L.1 + 4` alongside `physicalBox` overlap, and `physicalBox`
carries no dyadic cutoff. Taken alone that would prove disjointness only for pairs
already known to be within four bands. It is closed elsewhere:

```
-- NavierStokes/PartitionedCovariance.lean:297
theorem masks_force_adjacency {D q x L M} (hq : 0 < q) (hL : 1 ≤ L.1) (hM : 1 ≤ M.1)
    (hne : L ≠ M) (hmL : physicalMask D L q x ≠ 0) (hmM : physicalMask D M q x ≠ 0) :
    SlotColoring.Adj D L M
```
with `physicalMask = dyadicMask (L.1) q * physicalSlowMask D L.1 …`, and the proof reads
`|ℓ−ℓ'| ≤ 4` off `lineMask_support`. So the paper's implication is proved in full, and
`SlotSystem.cross_product_zero` (`:323`) delivers the consequence the paper actually uses
(vanishing cross-label products). **Not a finding.**

Two further points where Lean exceeds the paper: the centers are *explicit* rationals
`((i+1)/((m+1)6^D), 0)` rather than obtained from a Baire/density argument, and the
colouring is *constructed* (`colorData_proper`, "This is a constructed coloring, not a
coloring hypothesis", 2250 colours) rather than obtained by greedy colouring of a
countable graph. `SlotGeometry.colored_labels_have_slots` (`:454`) does take the colouring as a
hypothesis, and its own docstring says so — but `SlotColoring` supplies it.

### 6.2 — LEAN STRONGER on the count; the other clauses are dispersed

Paper: *"each change `H ↦ Yi` has uniformly bounded derivative factors, and `RH_γ` consists
of `14^{Δℓ} ≤ 14^{Δmax}` disjoint lifts of `Rγ`. Haar averages on the absolute, common, and
band tori agree whenever the function is a pullback… Radial integration at fixed `(z,t)`,
torus translation, averaging, and directional Fourier inversion on zero-mean functions
preserve common-torus descent and introduce no new dyadic band."*

Lean proves *more* than "consists of `14^Δ` disjoint lifts": `card_fiber` gives
`Nat.card {x // torusCovering^[d] x = p} = 14^d` exactly, `pairwise_disjoint_sheetRectangles`
gives disjointness, and `covering_bijOn_sheetRectangle` gives a bijection of each sheet onto
the native rectangle. Haar agreement (6.19) is `TorusAverages.integral_torusCovering_iterate`
(`:94`), proved from measure-preservation rather than assumed.

The "uniformly bounded derivative factors" and "preserve descent / introduce no new dyadic
band" clauses I did **not** find as a single statement. Their working forms are
`ChartScales` (the `c_{i0} = T_g^{−Δ}c_i`, `M_{i0} = Λ_g^{−Δ}M_i` comparisons),
`CommonCoverClass` ("adjacent-band changes give estimates whose constants precede the band,
copy, and source"), `CopySolveCompatibility` ("equality is proved first for the actual
coefficient/forcing paths and then for the constructed Volterra inverse"), and
`TorusInverse.inverse_preserves_parameter_support`. I class the composite clause as
ROUTED AROUND rather than missing: the repo carries the needed facts per operation instead
of as a blanket preservation lemma.

### 6.3 — EXACT, but not on the headline path

`LabelCounting.number_of_relevant_labels` (`:259`) is a faithful transcription, including
the quantifier order that matters:

```
(∃ C > 0, ∀ D q : ℝ, ∀ x : Position, … ncard ≤ C)                       -- sup over (r,z,t)
∧ (∀ B, IsCompact B → ∃ C > 0, ∀ n, 1 ≤ n → … ≤ C * S n ^ 9)            -- C_B S_ℓ⁹
∧ (∀ I, IsBounded I → ∃ C > 0, ∀ n, 1 ≤ n → ∀ Z T, … ≤ C * S n ^ 3)     -- sup_{Z,T}, C_{I_R} S_ℓ³
```
The pointwise constant is independent of `D`, `q`, `x` and the band; the radial constant is
chosen before `Z,T`. `normalizedBox A L` takes an arbitrary enlargement factor `A`, matching
"the same bounds hold for fixed-factor enlargements". `number_of_relevant_labels_restrict`
adds the admissible-label family `Γ`.

**Provenance note, not a strength finding:** every declaration in `LabelCounting.lean` is
marked `in_cone=False, in_import_closure=False` in the prior audit's `CONE.csv`. The file is
imported only by `NavierStokes/PaperAdditionalResults.lean`, which reaches `NavierStokes.lean`
through `PaperResults` but not through `ComparatorSolution`. So this is a paper-facing lemma
formalized *beside* the headline chain. That is exactly what the counting lemma's role in
the paper is (it bounds radial-integration sums), so an expert should decide whether the
headline route really avoids needing it, or whether the working chain uses some other,
possibly weaker, counting device. `LabelCountingFinite` *is* in the closure.

### 6.4 / 6.5 — LEAN WEAKER as definitions (the class is broader than the paper's)

Paper Definition 6.4: *"A smooth coefficient `f = f(R,Z,T,H)` belongs to `Mα` if it
**descends to each applicable common torus with representatives satisfying (6.20)**,
**extends smoothly by zero outside the active radial shell**, and on `Xa<X<Xb` satisfies
`∂θ f = 0`, `∀I ∃C,b,d : |∂^I f| ≤ C ε^α S^b ζ δ^{-d}`."*

Lean:
```
-- NavierStokes/WeightedClasses.lean:107
structure MemClass (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ) (f : ℕ → D → E) : Prop where
  weight_nonneg : ∀ n x, x ∈ s.domain → 0 ≤ w n x
  smooth        : ∀ n, ContDiffOn ℝ ∞ (f n) s.domain
  bounds        : ∀ m, ∃ C ≥ 0, ∃ p, ∀ n x ∈ s.domain, ∀ j ≤ m,
                    ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s w α C p n x
abbrev MeanClass s α f := MemClass s (fun _ x => s.zeta x) α f            -- weight ζ
abbrev WaveClass s P α f := MemClass s (fun n x => √(s.zeta x) * P n x) α f -- weight √ζ·P
```
So `Mα`/`Wα` in Lean are **the size bound and nothing else**. Absent: `∂θ f = 0`; descent
to the common torus and the compatibility identity (6.20); smooth zero extension outside
the shell; for `Wα` also `supp(aγ,m|Eγ) ⊂ Ωγ`, the cut-off support `Ωᶜᵘᵗ_γ`, and the
"continuation beyond `v=0,Ls` has no envelope bound" convention. The separate-degree form
of (6.24) is accepted by `of_separate_bounds` (`:147`), so the common-degree `growth =
S·max(1,δ⁻¹)` is not itself a weakening.

Direction of the difference: a broader class makes *membership* claims weaker and
*closure* claims (6.30)–(6.32) stronger. The places where the missing conditions are
load-bearing are (i) the `m+m'=0` case of (6.31) ("after temporal cutoff") and (ii) the
cross-label vanishing `(∂^I wγ)(∂^J wγ') = 0`. Lean gets (ii) from the geometry
(`PartitionedCovariance.cross_product_zero`) rather than from class membership, and
support/angular-invariance conditions are tracked in the "Actual…" files as separate
predicates (`ActualSignedFamilySupport`, `CopyAngularInvariance`,
`ActualWaveCoefficientPeriodicity`). This is a *bookkeeping* difference, not a gap I can
exhibit — but a reader who assumes "Lean proved `f ∈ Mα`" means the paper's Definition 6.4
is being over-read by several conditions.

### 6.6 — EXACT, assembled from parts

Every row is present: sums `add` (`:204`); `MαMβ⊂Mα+β` `MeanClass.bilinear` (`:440`);
`MαWβ⊂Wα+β` `MeanClass.bilinear_wave` (`:450`); the `m+m'=0` case `WaveClass.bilinear_mean`
(`:413`, proved from `(√ζ P)² ≤ ζ`, "no derivative identity for the envelope `P` is
postulated"); the (6.32) table from `directional` (`∂_{R,Z,T}: Cα→Cα`), `band_smul` with
`BandBound s 1` (`Dz=ε∂Z: Cα→Cα+1`), `BandBound s 0` (`c_{i0}N_{i0}: Cα→Cα`) and
`MemClass.graphDerivative`/`graphIterate` (`Dr: Cα→Cα−κ`). The κ in the last is supplied by
`ChartScales.radialCoefficient_inv_upper`, and `ExponentLedger.lean:14` records `κ=10⁻⁵`,
matching published (6.2). No single declaration states the table.

### 7.1 — EXACT, and the uniformity survives

The uniformity claim is the substance of Lemma 7.1 ("a sufficiently small `q*>0`, **common
to all labels and fixed derivative orders**"), and it is honoured structurally:

```
-- NavierStokes/BasePhaseGeometry.lean:474
theorem exists_large_band (h M u T : ℝ) (hh : 0 < h) (hM : 1 ≤ M) (N0 : ℕ) :
    ∃ N ≥ N0, ∀ n ≥ N, LargeBand h M u n ∧ T ≤ ChartScales.S n
```
"All constants are fixed before this threshold. An arbitrary previous band cutoff and
arbitrary additional slow-scale requirement are allowed." `phase_estimates` (`:732`) then
gives `‖nΦ − B_s(s(v),K)‖ ≤ phaseConstant M / S` and `‖n'_Φ‖ ≤ phaseConstant M / S` with the
constant depending only on the compact reference data `M`, not on the label `i`, the point
`q`, the pulse coordinate `v`, or the band. `modal_errors` (`:842`) is (7.10)'s `E`;
`damping_error` (`:875`) is (7.11); `frame_jets`/`pulse_jets`/`coefficient_jets`
(`:1069`–`:1088`) are the every-fixed-derivative clause under the *same* `LargeBand`
hypothesis.

Single-valuedness in `θ` is `PhaseCalculus.harmonic_theta_periodic` (`:212`); the phase
defect is an **exact identity** (`backwardMaterialOp_phase`, `:166`) in which every term
carries a factor `b` or `ε`, so "`Eik = O(εS^C)`" is an estimate on the coefficients rather
than a separate assertion. `ActualPhaseDefect.lean:565` ("The exact small factor is the
target-band viscosity") is the applied form.

### 7.5 — EXACT, but the file-level disclaimers must be read together

Two files carry explicit self-limitation notices that would mislead if cited singly:

- `NavierStokes/Covariance.lean:17` — *"The actual integrated columns in the manuscript
  include approximation errors. **This file does not identify those columns with the exact
  model**, or prove the Gaussian, parameter-derivative, or flat-edge estimates."*
- `NavierStokes/SmoothCovariance.lean` — *"No assertion here supplies smoothness or error
  estimates for the manuscript's integrated columns. No assertion concerns extension
  through a zero-amplitude edge, where the strict cone hypotheses fail."*

The perturbed statement the paper actually proves *is* elsewhere:
`PrimaryCovarianceBounds.normalizedPair_entry_error` (`:321`) gives the `O(1/r) = O(S⁻¹ᐟ²)`
direction error of the *actual integrated* columns (paper's `|eσ| ≤ CS_*^{-1/2}` in (7.28)),
and `compact_chart_pair_bounds` (`:385`) converts a compact strict-cone margin into a
determinant gap, an entry bound, and the lower bound
`inverseLower * √(S n) * ζ ≤ weights H T j`. That is (7.29)/(7.25) with `R = √S_*` and the
flat weight `ζ` retained as a factor — consistent with (7.29)'s `c√S_*|T| ≤ yσ ≤ C√S_*|T|`
and `|T| ≍ ζ`. (The p82 rendering `yσ ≥ c √︁S∗ζ` is ambiguous in the extracted text between
`c√(S_*ζ)` and `c√S_*·ζ`; only the latter is consistent with (7.29), and it is what Lean
proves. I am not reporting a discrepancy here.) The shell-edge extension is
`FlatCovariance.lean`, which is precisely the case `SmoothCovariance` disclaims.
Uniformity: the constants come out of `∃ N ≥ 4, ∃ detGap entryBound inverseLower, ∀ n ≥ N,
∀ p ∈ K, ∀ P …`, i.e. before the band, the slow point and the pulse pair.

### 7.3 and 7.8 — EXACT in substance, no single counterpart

Both are "collect what was just proved" statements in the paper. Their content is present
(7.3: `homogeneous_forward_bound`'s "the same forward propagator constant applies to every
nonzero harmonic" plus `exists_large_band`'s "arbitrary previous band cutoff … allowed";
7.8: `physical_signed_cross_covariance` plus the three class bounds), but neither corollary
is restated as one declaration. This is a presentation difference, not a strength
difference — I flag it only so that "there is no `Corollary 7.8` in the Lean" is not
mistaken for a gap.

### 8.6 — LEAN WEAKER, twice, narrowly

Paper (p95): *"Then `Nφ = F` has a **unique** smooth zero-mean solution `φ = N⁻¹F`. This
solution is given by the following Fourier series and satisfies the displayed norm bound
for every integer `m ≥ 0`: … `‖N⁻¹F‖_{C^m_y} ≤ C_m ‖F‖_{C^{m+4}_y}`."*

**(a) Uniqueness is not proved.** Lean's strongest statement is existential:
```
-- NavierStokes/TorusInverse.lean:586
theorem zero_mean_series_has_smooth_inverse (d : Direction) {a} (ha : Rapid a)
    (hmean : (∫ z, torusSeries a z ∂torusMeasure) = 0) :
    ∃ u : Torus → ℂ, Continuous u ∧ (∫ z, u z ∂torusMeasure) = 0 ∧ ContDiff ℝ ∞ (lift u) ∧
      ∀ x, fderiv ℝ (lift u) x (vector d) = series a x
```
I searched for a uniqueness companion (`grep` over `NavierStokes/*.lean` for
`zero_mean.*uniq`, `inverse.*uniq`, `uniq.*inverse`) and found none for this operator. The
repo *routes around* it: `NavierStokes/TemporalMeanUpdate.lean:245` says
*"uniqueness. Both sides are the actual Fourier-defined inverse."* — i.e. wherever the paper
would invoke uniqueness of `N⁻¹`, Lean instead rewrites both sides to the same constructed
series. That is legitimate and load-bearing nowhere I could see, but it means the paper's
"unique" is an unverified word.

**(b) The `m+4` exponent is not what Lean proves.** Lean's chain is
`inverse_derivativeWord_bound` (`:503`): `‖D^w(N⁻¹F)‖ ≤ C‖ω‖^{|w|} · coeffSeminorm(|w|+1, a)`,
then `SmoothFourierData.coefficient_seminorm_bound` (`:368`):
`coeffSeminorm p (coefficient f) ≤ 3^{p+4}·C·Σ weight⁻⁴` with `C` bounding derivatives of
pure order `p+4`. Composing at `p = m+1` needs derivatives of order `m+5`, because Lean
takes summability from `weight⁻⁴` (`summable_weight_inv_four`, `:343`) rather than the
paper's two-dimensional `(1+|k|)⁻³`. The paper's own use ("only a finite loss of torus
derivatives", p64; "a fixed finite regularity bound would give only a fixed finite flatness
order", p92) needs finiteness, not the number 4, so this is inert — but `C^{m+4}` as written
is not verified.

Everything else in 8.6 is EXACT and in places stronger: the directions match the paper's
`vr = (1,−bg)`, `vt = (bg,1)` with `bg = √2−1` (`TorusInverse.vector`, `:195`); the
Diophantine bound `|1/symbol| ≤ 6·weight` (`:234`) is the explicit form of (6.7);
`inverse_preserves_parameter_support` (`:566`) is the "preserves slow and radial support"
clause; `hasDerivAt_parameter_inverse` (`:541`) is "commutes with every slow coefficient
derivative"; `SmoothFourierData.inverse_solves_smooth_torus` (`:494`) removes the
coefficient-sequence hypothesis, so the Lean statement really is about an arbitrary smooth
zero-mean torus function.

### 8.7 — LEAN STRONGER, with the power list restated in a different variable

Paper: *"There are three fixed azimuthal bump profiles and two fixed axial bump profiles
supported in this interval with the following property. At each `(Z,T)`, for arbitrary
scalar targets `(P, Jθ, Jz)`, their physical rescalings have a **unique linear combination**
`(∆v, γd)` satisfying [five equations]."*

Lean upgrades "unique linear combination" to a continuous linear **equivalence**:
```
-- NavierStokes/FiveProfileMoments.lean:300
noncomputable def linearEquiv (P : Patch) (b : ℝ) (hb : GoodExponent b) : Coeff ≃L[ℝ] Coeff
-- Coeff := (Fin 2 → ℝ) × (Fin 3 → ℝ)   two axial + three angular amplitudes
```
invertibility coming from two Vandermonde/generalized-power determinants
(`PowerMomentMatrix`, "Rolle induction proves uniqueness of an exponential sum at as many
ordered nodes as there are distinct real exponents"). The paper's `λ > 0` hypothesis appears
exactly as `good_outgoing (lam) (hlam : 0 < lam) : GoodExponent (−1/2 − lam)` (`:267`), with
`GoodExponent b := b ≠ −1/2 ∧ b ≠ 1/2 ∧ b ≠ 3/2` (`:263`) — the three coincidences that would
collapse a power list. The paper's `|a(η)| ≥ a₀ > 0` becomes `hA : A ≠ 0` pointwise in
`normalizationLinearMap` (`:706`), with the uniform constant recovered by compactness
(`compact_normalization_bound`, `:752`). The bumps are constructed with disjoint supports in
disjoint halves of the patch (`bumps_disjoint`, `u_mul_e`), and support containment in the
open patch is proved (`u_tsupport_patch`, `e_tsupport_patch`).

Lean is strictly stronger in one respect: `normalizedMap` (`:342`) is the **nonlinear** map,
`linearEquiv + quadraticCLM`, and `normalizedMap_identity` (`:358`) is an exact identity —
i.e. the self-interaction terms `∫(e)²`, `∫x⁻¹(e)²`, `∫(u)²` that the paper defers to Lemma
8.8's `(Jθ)new`/`(Jz)new` are folded into the solve, with `smooth_solver_jet_bound` (`:887`)
and `MomentRepairPicard*` supplying the nonlinear branch.

**Restatement to be aware of:** the paper's power lists are "angular `2, −2−2λ, −2λ`, axial
`1, 1−2λ`" in the variable `x = r/√q`; Lean's are `angularPowers b = ![1/2, b, b−1]` and
`axialPowers b = ![0, b+1/2]`, whose *differences* are exactly half the paper's. That is the
signature of a squared-radius change of variable (`s = r²/2`, with the measure absorbed).
I did **not** verify the change of variables; I verified only that both lists consist of
distinct reals under `λ > 0`, which is what both arguments use.

---

## 3. Findings worth an expert (ranked)

**F1 (medium). Lemma 8.6's "unique" is unverified, and the `C^{m+4}` constant is not what
Lean proves.** `TorusInverse` proves existence of a smooth zero-mean solution of `Nφ = F`
and a finite-derivative-loss bound, but no uniqueness statement for the directional torus
inverse exists in the repo (searched `NavierStokes/*.lean`). The repo avoids needing it by
rewriting both sides to the same constructed series
(`TemporalMeanUpdate.lean:245`). Separately, the composite norm bound available is
`‖N⁻¹F‖_{C^m} ≲ ‖F‖_{C^{m+5}}`, not the paper's `C^{m+4}`, because Lean sums against
`weight⁻⁴` (`SmoothFourierData.lean:343`) rather than the paper's `(1+|k|)⁻³`.
*Is the stronger form used downstream?* No: the paper's own uses (p64, p92) need only that
the loss is finite and independent of the flatness order `p`. *Is the stronger form true?*
Yes on both counts — uniqueness is elementary (two zero-mean solutions differ by a
zero-mean function killed by `N`, whose every nonzero Fourier coefficient must vanish since
`vt·k ≠ 0`), and `m+4` is the standard count. So this is an *unformalized-but-true* item,
worth an expert only to confirm that no consumer secretly needs uniqueness as an identity
between two *differently constructed* inverses.

**F2 (medium). Definitions 6.4 / 6.5 are formalized as size bounds only.**
`WeightedClasses.MemClass` omits `∂θ f = 0`, common-torus descent with (6.20), smooth zero
extension outside the active shell, and (for `Wα`) the support conditions
`supp(aγ,m|Eγ) ⊂ Ωγ`, `supp aᶜᵘᵗ ⊂ Ωᶜᵘᵗ_γ`. Those conditions are the ones that make
Proposition 6.6's `(∂^I wγ)(∂^J wγ′) = 0` and the `m+m′=0` product rule true, and in the
paper they are part of *membership*, so that "`w ∈ Wα`" is a strong hypothesis. In Lean
they are tracked as separate predicates in the "Actual…" files and the geometry supplies
the cross-label vanishing directly. The expert question is narrow and mechanical: **for each
place where the paper writes `∈ Mα` or `∈ Wα` as a hypothesis and then uses a
support/descent/angular-invariance consequence, does the corresponding Lean site carry that
consequence as its own hypothesis?** I verified this for the cross-label product
(`PartitionedCovariance.cross_product_zero`) and for the curl lemma
(`CurlClassBounds.curlRemainder_waveClass`, which takes the `nΦ` bounds explicitly). I did
not verify it for the residual and correction-cycle sites.

**F3 (low–medium, provenance not strength). Lemma 6.3 is formalized off the headline path.**
`LabelCounting.lean` — the only counterpart to the label-counting lemma, and a faithful one
— is imported solely by `PaperAdditionalResults.lean`; all 22 of its declarations are
`in_cone=False, in_import_closure=False` in the prior audit's cone census. The lemma's role
in the paper is to bound the number of labels met by a radial integral (p68: "the sum over
these labels therefore permits polynomial growth in `S*`"). Either the headline chain
genuinely avoids that sum, or it bounds it by some other device. Worth ten minutes of an
expert's time to say which.

**F4 (low). Two covariance files carry disclaimers that make Proposition 7.5 look weaker
than it is — and a third file is what actually proves it.** `Covariance.lean` says it "does
not identify those columns with the exact model"; `SmoothCovariance.lean` says it supplies
no error estimates for the integrated columns and says nothing about the zero-amplitude
edge. A reviewer sampling those two files would conclude that only the exact 2×2 model was
formalized. The perturbed statement is `PrimaryCovarianceBounds.compact_chart_pair_bounds`
(`:385`) together with `FlatCovariance.lean` for the edge. I record this as a *navigation*
hazard, not a defect: I checked and the substance is there.

**F5 (low). No single-declaration counterpart to Corollary 7.3, Corollary 7.8, or the
(6.32) operator table.** All three are "collection" statements. Their content is proved.
This matters only for anyone auditing by statement-count.

**No NO-COUNTERPART gaps found in this slice, and no case where Lean proves something
weaker while the paper's stronger form is load-bearing or doubtful.** In particular I found
no instance of the "false-as-stated paper lemma with a weaker Lean version sufficing"
pattern. Where Lean and the paper differ, Lean is more often the stronger of the two
(6.1, 6.2, 8.7).

---

## 4. What I did not check

- **Proof correctness.** Nothing below the statement level was read, and I did not re-check
  kernel trust, axioms, or `sorry` counts (prior audits cover those).
- **Statements I spot-checked rather than read line by line:** 7.2, 7.4, 8.5, 8.8. For each I
  located the named construction and its principal identity/estimate and confirmed the shape,
  but I did not read every clause of the paper statement against every Lean conjunct. 7.4's
  Gaussian envelope (7.16) and the `CIS^{bI}P(v)` derivative bounds in particular were
  confirmed only by file-level inspection of `GaussianEnvelope`/`PrimaryCovarianceBounds`.
- **The `autoImplicit` hazard.** Prior audit A4 records that the `NavierStokes` library
  builds with Lean's default `autoImplicit := true`, so a mistyped identifier in a
  *statement* binds as a fresh implicit instead of erroring. Every Lean statement quoted here
  was read as text; none was re-elaborated with `-DautoImplicit=false`. A statement in my
  slice could be about a fresh variable while reading correctly.
- **The change of variables behind 8.7's power lists** (`x = r/√q` vs. the squared-radius
  variable Lean uses). I confirmed distinctness of both lists under `λ>0` and that the
  differences scale by exactly `1/2`; I did not verify the Jacobian bookkeeping.
- **Lemma 6.2's "uniformly bounded derivative factors" and "introduce no new dyadic band"
  clauses** as a single statement. I located working forms (`ChartScales`,
  `CommonCoverClass`, `CopySolveCompatibility`, `TorusInverse.inverse_preserves_parameter_support`)
  but did not confirm they jointly cover the clause.
- **Whether the hypothesis structures other than `MeanHypotheses` are supplied.** I checked
  `LiftedMeanResidual.MeanHypotheses` (supplied at `ActualInitialization.lean:1400`,
  propagated by `CycleMeanEquation.next_meanHypotheses`) and
  `SlotColoring.Adj` (supplied by `PartitionedCovariance.masks_force_adjacency`). I did not
  check `PrimaryCovarianceBounds.ZeroOrderBounds`, `PulseCovariance.PulseBounds`,
  `PhaseJetBounds.FrameJets`/`PolynomialJets`, or `IntegratedMeanBalances.SmoothShell`
  against FINDINGS.md's P1 list of 45 unsupplied predicates.
- **Numerical constants** beyond `κ = 10⁻⁵`, `J_g = [[3,1],[1,5]]`, `|det J_g| = 14`,
  `Λg = 4−√2`, `Tg = 4+√2`, `bg = √2−1`, which I did confirm.

---

## 5. Draft → published numbering correspondences established

The brief's expectation that "the draft numbering seems to be CLOSE to the published one"
is **wrong for this slice**: the draft's §8 is the published §6 *and* §7.

| Lean docstring cites (draft) | Published | Evidence |
|---|---|---|
| `Definition 8.1` — "the graph is `Y(r,t) = r^d • vr + t • vt`" (`GraphCalculus.lean:10`, `PhysicalGraphBounds.lean:18`) | **(6.3)** / §6.1, the physical evaluation map | identical formula |
| `§8.1` — "the manuscript fixes `κ = 10⁻⁵` in §8.1 and again in §10.2" (`ExponentLedger.lean:14`) | **(6.2)**, `κs = 10⁻⁵` | identical constant |
| `Lemma 8.3` — "the rational centers required in Lemma 8.3 for the specific covering matrix `J = [[3,1],[1,5]]`" (`SlotGeometry.lean:15`) | **Lemma 6.1** | centers `cγ`, radius `r0`, injective padded slots, disjointness |
| `§8.2` (`GaussianTailFlat.lean:11`) | **(7.16)**, the Gaussian pulse envelope | `P(v)` two-sided Gaussian bounds |
| `Lemma 8.4`, `equation (27)` (`TangentProjection.lean:12`, `TangentODE.lean:216,279,323`, `PrimaryODE.lean:209`, `CommonCoverSolve.lean:968`) | **Lemma 7.1** / **(7.5)** | frame orthogonal to `nΦ`; the projected amplitude equation with the moving-normal term |
| `equation (25)` (`PhaseCalculus.lean:20`) | **(6.6)** | `t* = −ε∂T + ciNi`, `Dr`, `Dz` |
| `equation (26)` (`PhaseCalculus.lean:16,108,265`) | **(7.3)/(7.4)** | the phase and `nΦ`; "the comparison vector `B(s,K)`" is (7.9)'s reference normal |
| `Lemma 8.5` — `netGrowth` (`PulseGrowth.lean:9`) | **Lemma 7.4** | homogeneous pulse growth/decay |
| `equation (28)` (`GrowingMode.lean:429`) | **(7.21)** | "positive radial amplitude and the ratio error" |
| `Lemma 8.7`, `equation (29)` (`Covariance.lean:12`, `TorusAverages.lean:623,653`) | **Proposition 7.5** | two signed covariance columns, cone condition, positive squared amplitudes |
| `Section 8.3` (`Covariance.lean:206`) | **§7.3** / **(7.1)** | "the ratio condition stated in Section 8.3" = the `u*` cone choice |
| `Lemma 8.8` — `normalized_double_cross` (`CurlGeometry.lean:9,74`) | **Lemma 7.7** | `−n×(n×t)/|n|² = t` when `n·t = 0` |
| `Lemma 9.2` (`CurlClassBounds.lean:757`) | **Lemma 7.7** (the class half) | "Lemma 9.2's curl remainder, with the original wave weight unchanged" |
| `Proposition 9.3` (`LinearWaveBounds.lean:896`) | **Proposition 7.2** | "at the coefficient level: the actual harmonic residual" |
| `equation (32)` (`MeanIncrementBounds.lean:10,1115`, `LiftedMeanResidual.lean:1172`, `DefectIncrementBounds.lean:314`) | **(8.3)** | the three mean momentum lines |
| `equation (33)` (`PressureStream.lean:382`) | **(8.12)** | `pm = T0(gr − ρP)` |
| `equation (34)` (`IntegratedMeanBalances.lean:638,733`) | **(8.16)** | the two integrated tangential balances |
| `Section 10.2` (`SignedCovariance.lean:384`, `ExponentLedger.lean:14`) | **(7.35)**/§7.3 physical assembly | "Section 10.2's chart stress `Q^{2A}σ/ε`" |
| `Lemma 3.6` (`PowerMomentMatrix.lean:12`) | used by **Lemma 8.7** | generalized-power evaluation matrix |
| `Definition 9.6` (`RadialPrimitive.lean:*`) | **(8.4)/(8.5)** | "the scalar, unshifted part of Definition 9.6" |
| `Proposition 9.6` | **Proposition 9.6** (outside this slice) | cited by both, apparently unshifted |

Two draft citations in my slice's files point **outside** the published §6–§8 and should not
be mapped into it: `LoopMoments.lean:11` (draft Lemma 6.1, `avg`/`angleMeasure`) and
`RadialModulation.lean:18` (draft Proposition 6.2, `phasePoint (n X η) := (X, η, n·log X)`)
are similarity-profile material, i.e. published §4, not published §6. The brief's seed list
associated them with §6; that association is a numbering artefact.
