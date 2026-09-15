# Euler deliverable spine — deep audit (worker: euler-spine)

Repo under audit: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5,
`lean-toolchain` = `leanprover/lean4:v4.34.0-rc2`, Mathlib rev `85e3a25e006c...` per `lake-manifest.json`).
Method: SOURCE READING only (no built Mathlib on the box, no `lake build`). Mathlib statements quoted
below were fetched from raw.githubusercontent at the pinned rev. Read-only: nothing under `NSE` was touched.

## Scope

Files read line-by-line (22 files, 225 `theorem/def/structure/abbrev/instance` decls total by regex census):

| file | decls | read |
|---|---|---|
| `Euler/Solution.lean` (85 ln) | 3 | full, line-by-line |
| `Euler/SolutionDefinitions.lean` | 11 | full + byte-diffed vs challenge |
| `Euler/InitialDataBridge.lean` | 1 | full |
| `Euler/ComparatorLocalEvolution.lean` | 5 | full |
| `Euler/ComparatorIdentification.lean` | 2 | full |
| `Euler/CanonicalVorticityConfinement.lean` | 6 | full |
| `Euler/CompactVorticityContradiction.lean` | 1 | full |
| `Euler/EulerFiniteLifespan.lean` | 6 | full |
| `Euler/ComparatorMaximalSolution.lean` | 11 | full |
| `Euler/ComparatorMaximalFields.lean` | 17 | full |
| `Euler/ComparatorSingularityNorms.lean` | 4 | full |
| `Euler/ComparatorSobolevEvolution.lean` | 12 | full |
| `Euler/PacketFiniteLifespan.lean` | 9 | full |
| `Euler/OrdinaryEulerLifespan.lean` | 9 | full |
| `Euler/OrdinaryEulerMaximal.lean` | 31 | full |
| `Euler/OrdinaryEulerContinuation.lean` | 10 | full |
| `Euler/OrdinaryEulerNontriviality.lean` | 4 | full |
| `Euler/EulerC1Breakdown.lean` | 34 | full |
| `Euler/EulerC1Limsup.lean` | 12 | full |
| `Euler/EulerSingularity.lean` | 17 | full |
| `Euler/OrdinaryEulerBKM.lean` | 3 | full |
| `Euler/OrdinaryEulerDifference.lean` | 17 | statements read; `Evolution` structure line-by-line |
| `ComparatorChallenges/Euler.lean` | — | full + byte-diffed vs solution |

Skimmed (statement-only, one level below the spine; ~30 decls): `Euler/LpSmoothField.lean` (`SmoothL2Field`),
`Euler/OrdinaryEulerClassicalClass.lean:194,271`, `Euler/OrdinaryEulerEndpoint.lean:39`,
`Euler/OrdinaryEulerLocalExistence.lean:139-155`, `Euler/OrdinaryRegularizedEnergy.lean:125`,
`Euler/OrdinaryEulerConcatenation.lean:73`, `Euler/MeanSobolevBoundedField.lean:104-113`,
`Euler/MeanBoundaryOperator.lean:22-28`, `Euler/MeanCutoffCurlBound.lean:16`,
`Euler/OrdinaryEulerVorticity.lean:17-22`, `Euler/H3CurlConvergence.lean:35`,
`Euler/OrdinaryHelmholtzField.lean:102`, `Euler/OrdinaryEulerLimit.lean:114-120`,
`Euler/OrdinarySmoothWords.lean:25`, `Euler/EulerProof.lean:5196-5216,10845`,
`Euler/PacketStageInitialLimit.lean:55,84,106`, `Euler/PacketInfiniteConstruction.lean:52,68,72`,
`Euler/CanonicalPacketHorizons.lean:82`, `Euler/StageVorticityConfinement.lean:16`,
`Euler/StageDisplacementConfinement.lean:119`, `Euler/PacketBaseGuardScales.lean:14`.
Two sub-chains were delegated to read-only child auditors (see *Escalations*/*Residue*):
BKM (`euler-spine-bkm.md`) and Comparator identification / local conversion (`euler-spine-uniqueness.md`).

Verdict counts over the 58 declarations tabulated below: **OK 54, UNCLEAR 4, KERNEL-RISK 0, SUSPICIOUS 0**
(the 4 UNCLEAR are B8, D17, E2, E4 — each delegated one level down, see §Escalations; §Kernel-risk
records two benign but load-bearing uses of kernel definitional features).

## Per-declaration findings

### A. The two deliverables and the challenge

| # | name | file:line | what the statement really says | how the proof gets it | verdict |
|---|---|---|---|---|---|
| A1 | `Euler.euler_breakdown_R3` | `Euler/Solution.lean:31` | ∃ u₀ : ℝ³→ℝ³ smooth, div-free, all derivatives decaying faster than any polynomial, with **no** global smooth finite-energy Euler solution. | `⟨initialDatum.field, initialVelocityConditionDecay_of_compact …, initialDatum_no_global_solution⟩`. Pure term application; every component is a real theorem. | OK |
| A2 | `Euler.exists_compact_smooth_euler_singularity` | `Euler/Solution.lean:43` | 12-clause conjunction: compact nonzero rapidly-decaying u₀, 0<T*≤1, a Sobolev-class solution on `Ico 0 T*`, uniformly bounded energy, existence-on-`Icc 0 T` **iff** T<T*, locally finite C¹ sup and vorticity integral, `limsup` of C¹ norm at T*⁻ = ⊤, total vorticity lintegral = ⊤, and no global solution. | `refine ⟨…⟩` with 12 named lemmas + 3 short `?_` goals. No tactic does arithmetic; every field is an existing theorem instantiated at `lifespan`. | OK |
| A3 | `initialDatum_no_global_solution` | `Euler/Solution.lean:24` (private) | ¬∃ v p, `EulerExistenceAndSmoothnessR3 initialDatum.field v p`. | `rintro ⟨v,p,h⟩` then one application of `finiteLifespan_contradiction_of_compact_vorticity`. | OK |
| A4 | challenge vs solution definitions | `ComparatorChallenges/Euler.lean:44-161` vs `Euler/SolutionDefinitions.lean:44-138` | — | **Byte-identical** for all 11 definitions (`divergence`, `InitialVelocityCondition(Decay)`, `EulerExistenceAndSmoothness(R3)`, `toL2`, `SobolevSmoothOn`, `EulerSobolevExistenceAndSmoothnessR3On`, `vorticity`, `velocityC1Norm`, `vorticityNorm`); verified by `difflib` on the two files — the only diffs are the header docstring and the removal of the two `sorry` theorems. `SolutionDefinitions.lean:20` imports **only** `Mathlib`, so these defs elaborate in the same environment as the challenge's. | OK |
| A5 | statement text of A1/A2 | `Euler/Solution.lean:32-34,44-59` vs `ComparatorChallenges/Euler.lean:87-89,171-186` | — | Byte-identical modulo the `sorry` → `refine …` tail (verified by diff). So no statement was silently weakened at the source level. | OK |

Notes on A2's clause meanings, since junk values are the obvious attack here:
* `maximalVelocityExtension` (`Euler/ComparatorMaximalFields.lean:17`) is `if t ∈ Ico 0 duration then … else 0`.
  The zero branch **cannot help** any of the claims: `EulerSobolev…On (Ico 0 T*)` only constrains `Ico 0 T*`;
  the energy clause is quantified over `Ico 0 T*`; the vorticity lintegral is over `Ico 0 T*`; and the
  `limsup` at `𝓝[<] T*` is eventually inside `(0,T*)`, and a `⊤` limsup could never be produced by the
  zero branch (whose `velocityC1Norm` is 0). So the extension-by-zero is inert, as claimed at
  `Euler/ComparatorMaximalFields.lean:5`, and I could check that claim.

### B. Is `lifespan` a real term, and are its structure fields non-degenerate?

| # | name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| B1 | `FiniteLifespan` | `Euler/OrdinaryEulerLifespan.lean:29` | structure: `duration : ℝ`, `duration_pos : 0 < duration`, `shorter : ∀ S, 0<S → S<duration → HasEulerEvolution A S`, `maximal : ∀ S, duration<S → ¬ HasEulerEvolution A S`. | plain structure, no `Prop`-valued escape hatch, no default field. | OK |
| B2 | `HasEulerEvolution` | `Euler/OrdinaryEulerLifespan.lean:13` | `∃ hT : 0<T, ∃ U : Evolution T hT.le, U.velocity ⟨0,…⟩ = A` | — | OK |
| B3 | `Evolution` | `Euler/OrdinaryEulerDifference.lean:21` | structure carrying velocity/pressureForce as `Icc 0 T → SmoothL2Field Space`, L²-jet continuity at every order, `solenoidal`, `gradient` (pressure force lies in `gradientSpace`), and `time_law` = the **classical pointwise Euler equation** `∂ₜv(x) = -Dv(x)·v(x) - F(x)` as a `HasDerivAt` at every interior time and every point. | — | OK — this is the genuine PDE, not a weak surrogate. |
| B4 | `SmoothL2Field` | `Euler/LpSmoothField.lean:31` | `field : Space → V`, `smooth : ContDiff ℝ ∞ field`, `integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume`. | — | OK — **this closes the `fderiv`-junk-value hole**: every field in `Evolution` is genuinely C^∞, so `fderiv` in `time_law` is never the 0 junk value. |
| B5 | `exists_finite_lifespan` | `Euler/OrdinaryEulerLifespan.lean:35` | given one `T` with an evolution and one `B>0` with none, `∃ L : FiniteLifespan A, L.duration ≤ B`. | `duration := sSup {T | HasEulerEvolution A T}`; `hne` from the local existence input; `hbdd` from `lt_of_failure`; `shorter` from `exists_lt_of_lt_csSup` + `HasEulerEvolution.restrict`; `maximal` from `le_csSup`. **The `sSup` is over a nonempty set that is proved bounded above** (`hbdd : BddAbove times := ⟨B, hbound⟩`, line 41) — so this is not the `sSup = 0` junk value of an unbounded/empty set. | OK |
| B6 | `lifespan` | `Euler/PacketFiniteLifespan.lean:54` | `def lifespan : FiniteLifespan initialDatum := initialDatum_finite_lifespan.choose` | It is a `Exists.choose` of `initialDatum_finite_lifespan`, **not** a hand-built structure literal. So there is no field that could be satisfied by a degenerate choice: the whole structure comes from B5. Its two real inputs are B7 and B8. | OK |
| B7 | `initialDatum_local` | `Euler/PacketFiniteLifespan.lean:27` | `∃ T, HasEulerEvolution initialDatum T` | `Stage.exists_local_evolution packets initialDatum initialDatum_Hm` (`Euler/PacketStageLocalExistence.lean:39`), i.e. a genuine local-existence limit of the packet evolutions restricted to `baseHorizon/12`. | OK (mechanism verified one level down) |
| B8 | `initialDatum_no_base` | `Euler/PacketFiniteLifespan.lean:31` | `¬ HasEulerEvolution initialDatum (baseHorizon J X)` | `Stage.initialDataLimit_no_euler` (`Euler/PacketStageInitialLimit.lean:106`) via `no_euler_evolution_of_initial_H3`. **This is the sole source of finiteness** and lives in the packet construction (out of my scope — see Escalations E4). | UNCLEAR (delegated) |
| B9 | `lifespan_le_base` / `lifespan_le_one` | `PacketFiniteLifespan.lean:56` / `EulerFiniteLifespan.lean:24` | `duration ≤ baseHorizon J X ≤ 1` | `.choose_spec`, then `constructionScales.time_small`. | OK |
| B10 | `initialDatum` | `Euler/PacketFiniteLifespan.lean:18` | `Stage.initialDataLimit packets le_rfl le_rfl` | a constructed limit field, not a choice. | OK (construction not audited here) |
| B11 | `FiniteLifespan.evolution` / `evolution_initial` | `OrdinaryEulerLifespan.lean:60,63` | picks, for each `S < duration`, an `Evolution S` with the right initial datum | `(L.shorter …).choose_spec.choose` — a choice, but of a **proved** existence, so no junk. | OK |
| B12 | `evolution_agrees` | `OrdinaryEulerLifespan.lean:67` | the chosen evolutions on `S ≤ T` agree on `[0,S]` in velocity **and** pressure force | `endpoint_matches_partial` (H³ uniqueness). Load-bearing: it makes `maximalField` independent of the horizon choice. | OK (uniqueness lemma delegated to child) |
| B13 | `no_endpoint` | `Euler/OrdinaryEulerContinuation.lean:53` | `¬ HasEulerEvolution A L.duration` — **the endpoint itself is excluded**, which the structure B1 does *not* give. | `h.extend` → `L.maximal`. `HasEulerEvolution.extend` (line 43) restarts `localEvolution` from the terminal slice and `concatenate`s. `regularizedTime A = (2(1+C₃)(1+wordEnergy 3 A))⁻¹ > 0` (`OrdinaryRegularizedEnergy.lean:125`). | OK — real continuation, not an assumption |
| B14 | `initial_nonzero` | `Euler/OrdinaryEulerNontriviality.lean:47` | any `FiniteLifespan A` forces `A.field ≠ 0` | If `A.field = 0`, `zeroEvolution` (line 21, an explicit `Evolution` with `time_law` discharged by `fderiv_const_apply`) is an evolution **at** `L.duration`, contradicting B13. Clean, and it is the correct direction: nonzeroness is *derived*, not assumed. | OK |
| B15 | `initialDatum_nonzero` | `Euler/EulerSingularity.lean:92` | `initialDatum.field ≠ 0` | `lifespan.initial_nonzero`. The lemma name does **not** overclaim. | OK |
| B16 | `initialDatum_compact` / `_support` | `EulerFiniteLifespan.lean:21,17` | `HasCompactSupport initialDatum.field`, `tsupport ⊆ closedBall 0 2` | `Stage.initialDataLimit_support_of_physical` + `IsCompact.of_isClosed_subset`. | OK (support lemma in construction) |
| B17 | `initialDatum_divergence` | `PacketFiniteLifespan.lean:42` | `∀ x, divergence initialDatum.field x = 0` — with `divergence` = `EulerSmoothLimit.divergence` | from `initialDatum_solenoidal` (which itself comes from `initialDatum_local`: the *existence of an evolution* supplies solenoidality) + `solenoidal_representative_divergence`. | OK |

Does `initialDatum.field` really satisfy everything the challenge demands? Yes, and by these routes:
smooth = `SmoothL2Field.smooth` (B4); div-free = B17 **but** the challenge's `Euler.divergence` is
`(fderiv ℝ v x).trace ℝ ℝ³` (`SolutionDefinitions.lean:47`) whereas the development's is
`coordinateTrace ∘ fderiv` (`Euler/EulerProof.lean:5216`, with `coordinateTrace_eq_linearTrace` at
`5210`); polynomial decay = C1 below; compact support = B16; nonzero = B15. **No clause is true only
because a definition collapses to 0.**

### C. The two definitional bridges (challenge language ⇄ development language)

| # | name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| C1 | `initialVelocityConditionDecay_of_compact` | `Euler/InitialDataBridge.lean:16` | smooth + compactly supported + div-free ⇒ `InitialVelocityConditionDecay` (i.e. `∀ m K, ∃ C, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C/(1+‖x‖)^K`) | Sets `g x = (1+‖x‖)^K‖D^m u₀ x‖`, proves `Continuous g` and `HasCompactSupport g`, takes the max `g x₀` via `exists_forall_ge_of_hasCompactSupport`, then `le_div_iff₀`. Genuinely proves the decay; note `(1+‖x‖)^K` here is `Real.rpow` (`rpow_const`, `Real.rpow_pos_of_pos`), matching the challenge's `K : ℝ` exponent. | OK |
| C2 | `velocityC1Norm_eq` | `Euler/ComparatorSingularityNorms.lean:27` | `Euler.velocityC1Norm A.field = ENNReal.ofReal (‖finiteField A‖ + ‖finiteField A.derivative‖)` | `iSup_ofReal_norm_boundedContinuousFunction` (line 21) = Mathlib's `BoundedContinuousFunction.enorm_eq_iSup_enorm`. **This is the crucial anti-junk step**: the challenge's `⨆ x, ENNReal.ofReal ‖v x‖` is identified with the *sup-norm of a bounded continuous function*, so the real-valued `maximalC1Norm` is not an `sSup` of a possibly-unbounded set. `finiteField A x = A.field x` is proved (`Euler/MeanSobolevBoundedField.lean:108`), so `finiteField` is honestly the same function, i.e. the boundedness is real (Sobolev embedding), not a fallback. | OK |
| C3 | `vorticityNorm_eq` | `Euler/ComparatorSingularityNorms.lean:38` | `Euler.vorticityNorm A.field = ENNReal.ofReal (EulerOrdinarySobolev.vorticityNorm A)` | same BCF route + C4. | OK |
| C4 | `vorticity_eq_vectorCurl` | `Euler/ComparatorSingularityNorms.lean:16` | the challenge's `Euler.vorticity u` equals the development's `vectorCurl u` for C^∞ `u` | `(vectorCurl_eq_matrix u x _).symm` where `curlMatrix` (`Euler/MeanBoundaryOperator.lean:22`) is **the same expression as the challenge's `vorticity`**: `WithLp.toLp 2 (fun i : Fin 3 => A (single (i+1) 1) (i+2) - A (single (i+2) 1) (i+1))` vs `SolutionDefinitions.lean:124`. Compared character by character: identical. The differentiability side condition comes from `A.smooth`, so the `fderiv` is not junk. | OK |
| C5 | `toL2_field` / `toL2_jet` | `ComparatorSobolevEvolution.lean:15,18` | the challenge's total-but-fallback `toL2` agrees with `SmoothL2Field.toLp` | `dite_eq_left A.memLp` — the fallback branch is never taken because `MemLp` is *proved*. | OK |
| C6 | `sobolevSmoothOn_of_path` | `ComparatorSobolevEvolution.lean:22` | an `Icc/Ico`-indexed path of `SmoothL2Field`s with continuous L² jets gives the challenge's `SobolevSmoothOn` | field-by-field, using C5. | OK |
| C7 | `hasScalarEulerEvolution_of_sobolev` | `ComparatorSobolevEvolution.lean:79` | **challenge class ⇒ development class** on `Icc 0 T` | Repackages `h.velocity_smooth.field`; the strong time derivative is transported by `congr_of_eventuallyEq` + `projIcc_of_mem`; the equation is converted with `add_eq_zero_iff_eq_neg.mpr`. This is the direction that makes the "iff" bite: an arbitrary challenge-class solution is forced into `HasEulerEvolution`, hence `T < T*`. | OK |
| C8 | `evolution_sobolevSolution` | `ComparatorSobolevEvolution.lean:109` | **development class ⇒ challenge class** | explicit construction with `evolutionVelocity/Pressure`; the scalar pressure is `radialPotential` of the pressure force with `scalarPressure_spec` (`Euler/OrdinaryEulerLimit.lean:117`: `ContDiff ∞`, `p 0 = 0`, `gradient p = F`). Not a junk pressure. | OK |
| C9 | `exists_sobolevSolution_iff` | `ComparatorSobolevEvolution.lean:151` | `(∃ v p, challenge-class on Icc 0 T) ↔ HasScalarEulerEvolution A T` | C7 + C8. | OK |
| C10 | `hasScalarEulerEvolution_iff` (both) | `EulerSingularity.lean:33,61` | development scalar class ↔ `HasEulerEvolution`, and ↔ `0<T ∧ T<duration` | `exists_evolution_iff_scalar` + `hasEulerEvolution_iff`. | OK |
| C11 | `FiniteLifespan.hasEulerEvolution_iff` | `EulerSingularity.lean:48` | `HasEulerEvolution A T ↔ 0<T ∧ T<L.duration` | forward: `T = duration` excluded by B13, `T > duration` by `L.maximal`; backward: `L.shorter`. **The `T = T*` case is exactly where a fake proof would cheat, and it is handled by the real continuation theorem.** | OK |
| C12 | `maximal_sobolev_existence_iff` | `ComparatorMaximalSolution.lean:107` | A2's clause 8: `(∃ w q, challenge-class on Icc 0 T) ↔ T < T*` for every `T>0` | `exists_sobolevSolution_iff` ∘ `hasScalarEulerEvolution_iff`, then `and_iff_right hT`. | OK |

### D. The maximal solution and the two blow-up clauses

| # | name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| D1 | `Time`, `initialTime`, `intermediateHorizon`, `shorterTime` | `OrdinaryEulerMaximal.lean:17,19,21,43` | `Time = Ico 0 duration`; `intermediateHorizon t = (t+duration)/2` | `linarith` on `dsimp`ed goals. | OK |
| D2 | `maximalField` / `maximalPressureField` | `OrdinaryEulerMaximal.lean:46,50` | value at `t` = the chosen evolution on `intermediateHorizon t`, sampled at `t` | well-defined *by choice of a specific horizon*, then D3 removes the dependence. | OK |
| D3 | `maximalFields_eq_evolution` | `OrdinaryEulerMaximal.lean:54` | for **any** admissible `S`, `maximalField (shorterTime t) = (evolution S).velocity t` (and same for pressure) | case split `S ≤ M` / `M ≤ S` + `evolution_agrees` (B12). This is what makes `maximalVelocity` canonical. | OK |
| D4 | `maximalVelocity` / `maximalPressure` | `OrdinaryEulerMaximal.lean:138,140` | `(maximalField t).field`; pressure = `radialPotential (maximalPressureField t).field` | — | OK |
| D5 | `maximalPressure_spec` | `OrdinaryEulerMaximal.lean:182` | `ContDiff ∞ p`, `p 0 = 0`, `∀x, gradient p x = F x` | `Evolution.scalarPressure_spec`. | OK |
| D6 | `maximalVelocity_divergence` | `OrdinaryEulerMaximal.lean:177` | div-free at every `t` | from `solenoidal` + a.e.-representative lemma. | OK |
| D7 | `maximal_sobolevSolution` | `ComparatorMaximalSolution.lean:82` | A2 clause 6: the extension is a challenge-class solution on `Ico 0 T*` | 8 fields; the strong time derivative is `maximalVelocityExtension_hasDerivAt` (line 58), which pulls `velocityPath_hasDerivWithinAt` from a shorter horizon to a two-sided `HasDerivAt` using `Icc_mem_nhds ht.1 htS` and then `congr_of_eventuallyEq`; the Euler equation is closed by `abel` after rewriting `eulerRhs`. | OK |
| D8 | `maximalVelocityExtension_bounded_energy` | `ComparatorMaximalFields.lean:82` | A2 clause 7 | via `maximalVelocityExtension_energy` = `‖A.toLp‖²` (exact **energy conservation**, `Evolution.kineticEnergy_conserved`) and `E := ‖A.toLp‖²+1`. Note: it proves the *strict* bound by the `+1` slack, which is honest, and the conserved-energy identity is a real theorem, not `E := ⊤`. | OK |
| D9 | `maximalVelocityExtension_c1_locally_bounded` | `ComparatorMaximalFields.lean:90` | A2 clause 9a: `⨆ t∈Icc 0 S, velocityC1Norm < ⊤` for `S<T*` | `maximalC1Norm_continuous` on a compact `Icc`, `isCompact_range .bddAbove`, then `iSup_le`. Uses C2 to convert. | OK |
| D10 | `maximalVelocityExtension_vorticity_locally_integrable` | `ComparatorMaximalFields.lean:103` | A2 clause 9b | `setLIntegral_congr_fun` + `ofReal_integral_eq_lintegral_ofReal` with a *proved* `IntegrableOn` from continuity. | OK |
| D11 | `maximalVelocityExtension_c1_limsup` | `ComparatorMaximalFields.lean:117` | A2 clause 10: `limsup (velocityC1Norm ∘ v) (𝓝[<] T*) = ⊤` | `rw [← L.map_time_atTop, ← Filter.limsup_comp]` then `velocityC1Norm_maximal` + `maximalC1Norm_limsup_atTop`. `map_time_atTop` (`EulerC1Limsup.lean:25`) = `map coe atTop = 𝓝[<] duration` via `map_coe_atTop_of_Ioo_subset`; `limsup_comp` is the unconditional `limsup f (map g l) = limsup (f∘g) l`. | OK |
| D12 | `ofReal_limsup_eq_top_of_unbounded` | `EulerC1Limsup.lean:41` | if `f` exceeds every `K` after every `τ<T*`, then `limsup (ofReal ∘ f) = ⊤` | `le_limsup_iff` + `frequently_atTop`, using `ENNReal.lt_ofReal_iff_toReal_lt`. Correct; requires `NeBot`, supplied by `Nonempty L.Time := ⟨initialTime⟩` (line 44) — i.e. it is **not** vacuously `⊤` from a trivial filter. | OK |
| D13 | `maximalC1Norm_unbounded_near_endpoint` | `EulerC1Breakdown.lean:69` | after every `τ<T*` there is `t` with `maximalC1Norm t > K` | `maximalGradientNorm_unbounded_near_endpoint` ← `maximalVelocity_gradient_unbounded_near_endpoint` ← `gradient_unbounded_near_endpoint` (`OrdinaryEulerContinuation.lean:86`). | OK |
| D14 | `gradient_unbounded_near_endpoint` | `OrdinaryEulerContinuation.lean:86` | pointwise `‖Dv‖` exceeds every `K` arbitrarily close to `T*` | `by_contra` + a careful two-case argument (`t ≤ R` uses `evolution_agrees_at` and the BCF norm bound on a fixed horizon `R = (max τ 0 + T*)/2`); ultimately `gradient_unbounded` ← `endpoint_of_bounded_gradient` ← `exists_smooth_endpoint` (`OrdinaryEulerEndpoint.lean:39`, a genuine rescaling+compactness continuation proof). **So the C¹ blow-up is a consequence of maximality + continuation, not an assumption.** | OK |
| D15 | `maximalGradientNorm_le_iff` / `maximalVelocityNorm_le_iff` | `EulerC1Breakdown.lean:35,30` | the real-valued norms are characterised by `∀ x, ‖…‖ ≤ K` | `BoundedContinuousFunction.norm_le_of_nonempty` + `finiteField_apply`. Confirms the "norm" is the true pointwise sup. | OK |
| D16 | `maximalVelocityExtension_vorticity_integral` | `ComparatorMaximalFields.lean:123` | A2 clause 11: `∫⁻_{[0,T*)} vorticityNorm = ⊤` | `setLIntegral_congr_fun` (C3/D-density) then `L.vorticity_lintegral_eq_top` (BKM, `OrdinaryEulerBKM.lean:35`). | OK / depends on BKM (E1) |
| D17 | `vorticityIntegral_unbounded` | `OrdinaryEulerBKM.lean:20` | partial vorticity integrals exceed every `G` | `vorticity_unbounded_of_logarithmic` + `logarithmic_gradient_bound_solenoidal` (a *proved* estimate passed as an argument, not a hypothesis of the theorem). Delegated. | UNCLEAR (delegated, E1) |

### E. The contradiction that kills the global solution

| # | name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| E1 | `finiteLifespan_contradiction_of_compact_vorticity` | `Euler/CompactVorticityContradiction.lean:18` | given a global challenge-class solution `v,p` for `A.field`, a compact `K`, agreement `maximalVelocity t = v(·,t)` on `[0,T*)`, and curl vanishing off `K`: `False`. | `h.vorticity_bounded_on_compact K hK T*` gives `M ≥ 0` bounding `‖curl v‖` on `K×[0,T*]` (compactness + global smoothness — honest); off `K` the curl is 0; so `‖curl‖ ≤ M` everywhere for all `t < T*`; then `vorticityIntegral ≤ M·t ≤ M·T*` contradicts `vorticityIntegral_unbounded (M·T*)`. Arithmetic closed by `mul_le_mul_of_nonneg_left` with `hM : 0 ≤ M`. Logically airtight given D17. | OK |
| E2 | `maximalVelocity_eq_of_compactCurlLocalUpgrade` | `Euler/ComparatorIdentification.lean:38` | the same data forces `maximalVelocity t = v(·,t)` for all `t : Time` | `maximalVelocity_eq_of_local_evolution` + `hasLocalEvolutionAtCompactCurl_of_upgrade`; the latter time-shifts the solution (`h.shiftTime a ha`). Uniqueness itself is `evolution_field_eq_of_local_evolution`. Delegated. | UNCLEAR (delegated) |
| E3 | `CompactCurlLocalUpgrade` | `Euler/ComparatorEvolutionIdentification.lean:37` | `Prop`: every challenge-class solution with compact initial curl is represented by an `Evolution` on some `[0,δ]` | non-trivial statement; **discharged** at `Euler/ComparatorLocalEvolution.lean:91` (`theorem compactCurlLocalUpgrade : CompactCurlLocalUpgrade`), so it is not an unproved hypothesis. | OK |
| E4 | `compactCurlLocalUpgrade` | `ComparatorLocalEvolution.lean:91` | the discharge | `local_compact_vorticity_of_truncationFamily` + `exists_evolution_of_commonCompactCurl` (line 64), which builds `recoveredVelocity` and verifies `IsSmoothScalarEuler` by weak pairings against `compactSolenoidalTests`. Delegated for depth. | UNCLEAR (delegated) |
| E5 | `canonicalVorticityBall`, `_compact` | `CanonicalVorticityConfinement.lean:22,25` | `closedBall 0 (2 + particleDisplacementCap …)`; compact | `isCompact_closedBall`. | OK |
| E6 | `evolution_vorticity_support` | `CanonicalVorticityConfinement.lean:28` | the curl of every shorter evolution is supported in that ball | H³ stability: the packet evolutions `V n` restricted to `S` have curl supported in the ball (`packets_vorticity_support`), their initial data converge to `initialDatum` in H³ (`initialDatum_Hm 3`), and `Evolution.curl_tendsto_of_initial_h3` (`Euler/H3CurlConvergence.lean:35`, which uses a Sobolev `real_smooth_fderiv_le_H3` bound and `squeeze_zero`) transfers the pointwise curl limit; `tendsto_nhds_unique` then forces 0 off the ball. **This is a real argument and it needs the H³ convergence, not just the L² one.** | OK |
| E7 | `canonical_vorticity_eq_zero_outside`, `_hasCompactSupport` | `CanonicalVorticityConfinement.lean:75,79` | the two hypotheses E1/E2 need | `image_eq_zero_of_notMem_tsupport`, `IsCompact.of_isClosed_subset`. | OK |

## Kernel-risk assessment

Vector (3) — **custom metaprogramming**: ZERO hits in my scope. I re-ran the scan restricted to my 22
files for `macro|elab|syntax|notation3|set_option|native_decide|axiom|unsafe|partial|sorry`: no hits
(the only matches for `partial` were the English word "partial" in docstrings at
`Euler/OrdinaryEulerBKM.lean:19,26`). Repo-wide `grep -rn '\bsorry\b' Euler/` = **0**. Independent
enforcement exists: `lakefile.toml` gives the `Euler` lib `warningAsError = true`, so a `sorry`
anywhere in `Euler` would fail the build (the `ComparatorChallenges` lib has no such option, which is
why its two `sorry` placeholders are allowed). The `#print axioms` lines at `Euler/Solution.lean:84,86`
are informational only and enforce nothing by themselves.

Vector (2) — **Nat/GMP numeral arithmetic**: ZERO `decide`, `omega`, `norm_num`, `Nat.pow/div/mod/gcd`,
or numeral-comparison sites in my 22 scope files (scanned; the only 4+-digit literal is the copyright
year `2026` at `SolutionDefinitions.lean:2`). The kernel therefore never has to evaluate a numeral to
accept the spine. One step below the spine, `Euler/OrdinaryEulerDifference.lean:134` contains the real
literal `3600` as an estimate coefficient; it is never *computed*, only carried through
`difference_energy_bound`. For calibration I scanned the whole 1829-file import closure of
`Euler/Solution.lean`: 113 `decide` occurrences in 39 files, all with tiny goals
(`5 ≤ 40`, `2 ≠ 0`, `29 ≤ 40`, `Even 6`, `(⟨2, by decide⟩ : Fin 3)`); the largest numeral appearing on
any `decide` line anywhere in the closure is `1000`. This is far below anything that could plausibly
exercise a GMP bug: worst case a couple of `Nat.decLe` reductions on 3–4 digit literals.

Vector (1) — **recursive inductive types / recursor reduction / structure eta**: the spine has no
inductive family, no `Nat.rec`/`Acc.rec`, no `termination_by`/`decreasing_by`, and no well-founded
definition. Concretely, every `rfl` in my scope and what the kernel must do for it:
* `Euler/ComparatorLocalEvolution.lean:45,71` — `(recoveredVelocity … t).field = (v · t)` by `rfl`.
  This is one *structure projection applied to a structure literal* produced by
  `smoothL2Field_of_curl_compact`; iota for a non-recursive single-constructor structure. Cheap and safe
  **provided** `smoothL2Field_of_curl_compact` really returns a literal whose `field` is `(v · t)` —
  delegated to the identification child, listed as E-R2 below.
* `Euler/CanonicalVorticityConfinement.lean:52`, `Euler/OrdinaryEulerMaximal.lean:99`,
  `Euler/EulerC1Breakdown.lean:39,56` — closing goals already `change`d/`rw`n to syntactic identity
  (projection unfolding of `maximalVelocity`, `maximalGradientNorm`, `gradientNormPath`). No recursion.
* `Euler/OrdinaryEulerNontriviality.lean:40` — `(zeroEvolution T _).velocity ⟨0,…⟩ = zeroField` by `rfl`:
  projection of a structure literal whose `velocity` is `fun _ => zeroField`; beta+iota only.
* `Euler/OrdinarySmoothWords.lean:25` (`field_ext`) — `cases A; cases B; cases h; rfl`. The final `rfl`
  is discharged by **kernel proof irrelevance** on the two `Prop` fields `smooth` and `integrable`.
  That is a kernel feature, used in the most ordinary possible way; it is not eta/recursor abuse. It is
  used pervasively (e.g. `PacketFiniteLifespan.lean:29,36`), so if proof irrelevance were broken this
  proof would be affected — but that is not an exploitable *choice* by the author.
* `Euler/Solution.lean:41`, `attribute [local instance] CompletePartialOrder.toSupSet` — see the E2
  finding below. Accepting the statement as *the same statement* as the challenge's does rely on
  **structure eta** (`SupSet.mk (@SupSet.sSup α i) ≡ i`) if the two files pick different instance paths.
  This is the single place in my scope where a kernel definitional-equality feature is load-bearing for
  the *meaning* of the deliverable rather than for an internal step.

Bottom line for my scope: the kernel accepts this spine by ordinary type checking of applications,
projections and `Eq.rec` motives. It does not have to reduce a recursor over a recursive type, decide a
`Decidable` instance, or evaluate a numeral. The two kernel features that *are* load-bearing are
proof irrelevance (ubiquitous, unavoidable) and structure eta for instance paths (one site,
`Solution.lean:41`).

### Settling previous-audit escalation E2 (`Euler/Solution.lean:41`)

Verified line text: `attribute [local instance] CompletePartialOrder.toSupSet` (read at line 41).

1. **Which `⨆` it can affect.** In the statement of `exists_compact_smooth_euler_singularity` there is
   exactly **one** supremum: `(⨆ t ∈ Icc (0 : ℝ) T, velocityC1Norm (v · t)) < ⊤` at
   `Euler/Solution.lean:51` (identical text at `ComparatorChallenges/Euler.lean:181`). It elaborates as
   `⨆ t, ⨆ _ : t ∈ Icc 0 T, …`, i.e. two `@iSup ℝ≥0∞ _ inst` nodes, both needing `SupSet ℝ≥0∞`.
   Nothing else in the statement needs `SupSet`: `⊤` needs `Top`; `Filter.limsup` (line 56) is defined
   through `sInf`/`InfSet` on a `ConditionallyCompleteLattice`, not `SupSet`; `∫⁻` (lines 52, 57)
   takes no `SupSet` argument at the call site. The `⨆ x, …` inside `velocityC1Norm` and
   `vorticityNorm` was already elaborated in `Euler/SolutionDefinitions.lean:130,134` — a file whose
   **only** import is `Mathlib` (line 20) and whose text is byte-identical to the challenge's, so those
   two `⨆`s are elaborated in the same environment as the reference's and cannot differ.
2. **Whether it can change the meaning.** No. `CompletePartialOrder` (Mathlib
   `Mathlib/Order/CompletePartialOrder.lean`, pinned rev) is
   `class CompletePartialOrder (α) extends PartialOrder α, SupSet α, OrderBot α`, and the **only**
   instance able to supply it for `ℝ≥0∞` is
   `instance (priority := 100) CompleteLattice.toCompletePartialOrder [CompleteLattice α] :
   CompletePartialOrder α where sSup := sSup; lubOfDirected _ _ := isLUB_sSup _` (end of that file).
   Its `sSup` field is *literally* `ℝ≥0∞`'s complete-lattice `sSup`. Hence
   `CompletePartialOrder.toSupSet (CompleteLattice.toCompletePartialOrder) ≡ CompleteLattice.toSupSet`
   by delta + structure eta, and `@iSup ℝ≥0∞ ℝ inst₂ f` is definitionally equal to
   `@iSup ℝ≥0∞ ℝ inst₁ f`, with the *same* `sSup` function. I also checked the neighbouring candidate
   sources of a rival instance — `Mathlib/Order/OmegaCompletePartialOrder.lean` (a different class, no
   `SupSet` parent), `Mathlib/Order/ConditionallyCompletePartialOrder/Defs.lean`,
   `Mathlib/Topology/Order/ScottTopology.lean` — none declares another `CompletePartialOrder` instance.
   So there is no reading of the solution's statement that differs from the challenge's.
3. **Why the author needed it (benign explanation that fits).** Among equal-priority instances Lean
   tries the most recently *imported* one first, and imported-instance order follows module order in the
   root file's import DFS. The challenge has a single root `import Mathlib`; `Euler/Solution.lean` has
   seven Euler roots pulling in Mathlib modules in a different order, so
   `CompletePartialOrder.toSupSet` vs `CompleteLattice.toSupSet` can win in the two files. Pinning it
   makes the two elaborated statements *syntactically* equal. This is exactly what the comment at
   `Euler/Solution.lean:40` claims, and it is consistent with everything I could check.
4. **The residual, stated honestly.** I cannot run Lean, so I cannot exhibit the two elaborated `Expr`s
   and confirm they are token-identical. What I *can* assert is the security-relevant part: **every
   `SupSet ℝ≥0∞` instance reachable in this environment yields ENNReal's own `sSup`**, so the attribute
   cannot have changed what the theorem says. The general pattern (using `attribute [local instance]`
   to make a statement *look* like the challenge's) is a legitimate thing to watch for in future
   audits; this particular use is benign. Verdict: **E2 SETTLED — not a soundness issue.**

## Escalations

Ranked by how much of the deliverable would collapse if the answer went the wrong way.

**E-R1. `Euler/OrdinaryEulerBKM.lean:20` — `vorticityIntegral_unbounded`.**
Question for an expert: is `logarithmic_gradient_bound_solenoidal` (used as the third argument, so it
must be a *proved* theorem, not a hypothesis of the enclosing statement) a genuine
Beale–Kato–Majda-type logarithmic estimate `‖∇u‖_∞ ≲ C(1+‖curl u‖_∞ log(…))`, proved from Mathlib
analysis, and does `vorticity_unbounded_of_logarithmic` really consume the *maximality* of the
lifespan? Settled by: reading `Euler/OrdinaryLogarithmicGradient.lean` and
`Euler/OrdinaryBKMReduction.lean` and confirming (a) no hypothesis of the final statement is an
unproved estimate, (b) `vorticityIntegral` is an honest `intervalIntegral` of a BCF sup-norm.
**Delegated** to child `euler-bkm` → `audits/nse-deep/workers/euler-spine-bkm.md`. Without E-R1,
A2 clauses 10–11 and the whole of E1 are empty.

**E-R2. `Euler/ComparatorLocalEvolution.lean:31,45,91` + `Euler/ComparatorEvolutionIdentification.lean` —
the local conversion and the uniqueness/identification step.**
Question: does `evolution_field_eq_of_local_evolution` prove a real H³ uniqueness (energy/Gronwall), and
does `smoothL2Field_of_curl_compact` build a structure whose `.field` is *literally* `v(·,t)` (so that
`rfl` at line 45 is a projection, and so that the recovered field is not some regularized surrogate)?
Settled by: reading those two lemmas plus `isSmoothScalarEuler_of_weak_projectedEquation` and
`compactSolenoidalTests_dense`. **Delegated** to child `euler-ident` →
`audits/nse-deep/workers/euler-spine-uniqueness.md`. Without E-R2, `initialDatum_no_global_solution`
(`Solution.lean:24`) fails and A1 collapses.

**E-R3. `Euler/PacketStageInitialLimit.lean:106` — `initialDataLimit_no_euler` (via
`no_euler_evolution_of_initial_H3`), the *only* source of finiteness of the lifespan.**
Question: does this really show that no `Evolution` on `[0, baseHorizon J X]` starts at the limit datum,
or does it exploit a property of `baseHorizon J X = 6 J² X^(-498 : ℝ)`
(`Euler/PacketBaseGuardScales.lean:14`) that is degenerate for the chosen scales (e.g. a horizon that is
positive but whose defining inequalities are satisfied only because `X^(-498)` underflows a bound)?
Also: `constructionScales := Classical.choice (exists_scales …)` (`PacketInfiniteConstruction.lean:68`)
— is `exists_scales` a proved `Nonempty`, and are its constraints simultaneously satisfiable?
Settled by: auditing the packet construction chain (not my scope; presumably a sibling worker's).
If B8 fails, `lifespan` still exists as a term only if `exists_finite_lifespan` gets a failure point —
so **A1, A2 and everything downstream collapse**.

**E-R4 (CORROBORATED by child `euler-bkm`, now the top open question in this sub-tree).**
`Euler/OrdinaryEulerLifespan.lean:74` / `Euler/OrdinaryEulerEndpoint.lean:39` —
`endpoint_matches_partial` and `exists_smooth_endpoint`.**
Question: `evolution_agrees` (used to make `maximalField` canonical, `OrdinaryEulerMaximal.lean:54-77`)
and `no_endpoint` (which single-handedly turns `T ≤ T*` into `T < T*` in C11/C12) both rest on these.
Is `endpoint_matches_partial` a real uniqueness theorem for this `Evolution` class, and does
`exists_smooth_endpoint` really produce an `Evolution` **at** `T` from bounded gradient integrals on
`[0,S)`, `S<T` (rather than assuming a uniform H^k bound that is equivalent to what is to be proved)?
Settled by: reading `Euler/OrdinaryEulerEndpoint.lean` and `Euler/OrdinaryH3Energy.lean` in full.
I read only `exists_smooth_endpoint`'s statement and the first ~30 lines of its proof (rescaling
`endpointScale n`, `h3_tensorNorm_gradient_uniform`, then a limit) — it *looks* like a genuine
compactness argument, but I did not finish it.

**E-R5. `Euler/EulerProof.lean` is a 20 755-line monolith that IS in the import closure of
`Euler/Solution.lean`** (it supplies `Space`, `divergence`, `curl`, `curl_apply` at lines
5202/5216/10845). Question: is anything in that file a *second*, weaker definition of a concept that also
exists in the modular files (name shadowing across namespaces), in particular a second `divergence`
(`Euler/EulerProof.lean:5216` = `EulerSmoothLimit.divergence` vs `Euler/SolutionDefinitions.lean:47` =
`Euler.divergence`)? In my scope the two are kept apart correctly (the challenge-facing statements use
`Euler.divergence`; `initialDatum_divergence` uses `EulerSmoothLimit.divergence` and
`ComparatorMaximalFields.lean:41` explicitly proves the `Euler.divergence` version), but a systematic
name-shadowing census across `EulerProof.lean` vs the modular tree would settle whether any
challenge-facing statement silently resolves to the wrong one. Settled by: a namespace-aware duplicate
census (my census was regex/name-based, not namespace-resolved).

**E-R6. `Euler/ComparatorMaximalFields.lean:120` — `Filter.limsup_comp`.** Minor: I asserted this is the
unconditional `limsup f (map g l) = limsup (f ∘ g) l`. Question: at Mathlib rev `85e3a25e`, does
`Filter.limsup_comp` carry monotonicity or `NeBot` side conditions? Settled by: reading
`Mathlib/Order/LiminfLimsup.lean` at the pinned rev (I did not fetch it). If it carried a hypothesis, the
proof would simply not compile — and the artifact is claimed to compile — so this is low risk.

## Residue

* **No Lean execution.** No built Mathlib (disk at 99 %, `df` shows 7.3 G free, no `.lake`), so I could
  not `lake build`, could not `#print axioms`, could not diff elaborated `Expr`s, and could not confirm
  that any tactic block actually closes its goal. Everything above is a reading of source text plus
  fetched Mathlib sources. In particular I take on faith the claim that the artifact compiles; my job
  was to ask whether, *if* it compiles, it means what it says.
* **Delegated, not personally verified:** the BKM chain (E-R1) and the identification/local-conversion
  chain (E-R2). Their reports land at `audits/nse-deep/workers/euler-spine-bkm.md` and
  `audits/nse-deep/workers/euler-spine-uniqueness.md`.
* **Out of scope and not read:** the packet construction (`Euler/Packet*.lean`, `Euler/Stage*.lean`,
  `Euler/Base*.lean` — hundreds of files), which is where the actual blow-up mechanism and all the
  numeric scale bookkeeping (`320`, `20`, `1000`, `X^(-498)`, `6 J²`, `requiredExponent`,
  `commonThreshold`) live. That is also where essentially all of the closure's 113 `decide`, 1792
  `omega` and 1376 `norm_num` calls live. I checked their *size* (max numeral on a `decide` line
  anywhere in the closure: 1000) but not their correctness.
* **`Euler/OrdinaryEulerDifference.lean`**: I read the `Evolution` structure and the statements, but not
  the H³ difference-energy proofs (lines 56–150).
* **Instance-resolution claim in §E2 point 3** is a plausible mechanism, not a verified one; the
  soundness-relevant point (point 2) does not depend on it.
* I did **not** attempt to detect a malicious `Nat` instance override or a shadowed `OfNat`: there is no
  `instance` declaration in my 22 scope files at all (the census found 0), so within my scope this is
  moot; repo-wide it was covered by the parent's `SITES_local_instance.md` (11 sites, only
  `Euler/Solution.lean:41` outside the `Classical.propDecidable` / `compactInterval` pattern).

## Appendix A — child auditor: BKM sub-chain (`euler-spine-bkm.md`)

Child `euler-bkm` returned: 54 OK, 2 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS; **no fraud found** in the BKM
sub-chain. This closes my escalation **E-R1**. Its four answers, which I record verbatim in substance:

1. `vorticityIntegral` is honest. `Euler/OrdinaryEulerVorticity.lean:63` is `realIntegral` of
   `vorticityNormPath`, i.e. literally `∫_0^t vorticityNorm` (`ContinuousTimeIntegral.lean:53`), and
   `vorticityNorm` (`OrdinaryEulerVorticity.lean:30`) is `‖finiteField (vorticityField A)‖` — a
   **bundled** `BoundedContinuousFunction` norm with an exact two-sided `iff` at line 34
   (Mathlib `norm_le_of_nonempty`, checked against Mathlib source). Not an `sSup` of an unbounded set;
   no `⊤`/0 fallback. The divergence claim is stated as a **lintegral** (`OrdinaryEulerBKM.lean:36`), so
   the Bochner "non-integrable ⇒ 0" convention is not exploited. *(This matches my C2/C3 finding on the
   independent `velocityC1Norm`/`vorticityNorm` bridges: the same BCF device is used consistently.)*
2. Maximality is load-bearing: `Euler/OrdinaryBKMReduction.lean:38-46` is `by_contra` → uniform gradient
   bound → `endpoint_of_bounded_gradient` (`OrdinaryEulerLifespan.lean:77`) → contradiction with
   `no_endpoint` (`OrdinaryEulerContinuation.lean:53`). Not vacuous; no junk value.
3. The logarithmic (BKM) estimate is **proved and discharged**, at `OrdinaryEulerBKM.lean:22-24` by
   `logarithmic_gradient_bound_solenoidal` (`Euler/OrdinaryLogarithmicGradient.lean:63`), from a real
   3-scale Gaussian argument (`WholeSpaceGaussianElliptic.lean:91`). It is **not** an undischarged `Prop`
   hypothesis threaded through the statement.
4. Kernel scan of the BKM chain's full 927-file / 114 k-line import closure: 0
   `sorry`/`axiom`/`native_decide`/`set_option`/`macro`/`unsafe`/`partial`/`Acc.rec`; 53 `decide`, all on
   `Nat`/`Fin` numerals ≤ 40 (exactly one inside the chain, `OrdinaryLogarithmicGradient.lean:47`);
   one `Nat.rec` (`LpSmoothJetField.lean:17`, at order 3 only); 10 `termination_by`, none in this chain.
   Consistent with my own scan.

Its escalations, and how they relate to mine:
* **child E1 = my E-R4, sharpened and now the top open item.** `exists_smooth_endpoint` →
  `limitEvolutionOfH3` (`Euler/OrdinaryEulerCauchy.lean:97`): does the *limit* evolution's `time_law`
  get **proved**, or only inherited/assumed? The child's warning is important and I endorse it: if that
  construction proves *too much* (i.e. manufactures an `Evolution` that need not satisfy the PDE), then
  `no_endpoint` and hence the BKM theorem would be **false**, not merely vacuous — and `no_endpoint` is
  also what I found to be load-bearing for `initial_nonzero` (B14) and for the `T = T*` half of
  `maximal_sobolev_existence_iff` (C11/C12). One unread file therefore carries three separate clauses of
  the deliverable. **Recommend a dedicated auditor on `Euler/OrdinaryEulerCauchy.lean` +
  `Euler/OrdinaryEulerEndpoint.lean`.**
* child E2: the Gaussian constants `average_first_L2_bound` / `average_second_bound` were not read.
* child E3: inhabitation of `FiniteLifespan` still rests on `initialDatum_no_base`
  (`Euler/PacketFiniteLifespan.lean:46`) — identical to my **E-R3**, and outside both our scopes.

## Appendix B — child auditor: identification / local conversion (`euler-spine-uniqueness.md`)

Child `euler-ident` returned: **34 OK, 0 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS — no fraud**. This closes
my escalations **E-R2** and the UNCLEAR verdicts on rows **E2** and **E4**.

1. **Uniqueness is real, not assumed.** `evolution_field_eq_of_local_evolution`
   (`Euler/ComparatorEvolutionIdentification.lean:52-129`) is a continuous-induction argument
   (Mathlib `IsClosed.Icc_subset_of_forall_exists_gt`, checked against Mathlib rev `85e3a25e`) over
   `velocity_eq_of_initial` (`Euler/OrdinaryEulerUniqueness.lean:24`), which is a genuine L² energy +
   Grönwall estimate (`Euler/OrdinaryGradientStability.lean:18,34,54`; the Grönwall step at
   `Euler/OrdinaryEulerL2Stability.lean:51`). Its **only** input is equality of the two fields at `t = 0`.
   So row E2 (`maximalVelocity_eq_of_compactCurlLocalUpgrade`) rests on a real uniqueness theorem, and
   the identification does not "silently assume the two fields agree".
2. **The two `rfl`s I flagged in §Kernel-risk are cheap, as I guessed.** `ComparatorLocalEvolution.lean:45`
   is beta-reduction plus **one projection of a structure literal**: `smoothL2Field_of_curl_compact`
   builds the record with `field := u` at `Euler/DivCurlTensorRecovery.lean:82-85`, and `SmoothL2Field`
   has a single data field (`Euler/LpSmoothField.lean:31-34`). `ComparatorEvolutionIdentification.lean:121`
   is a `shiftTime` structure literal plus `Subtype` proof irrelevance. **No `Acc.rec`, no `Nat.rec`, no
   reliance on structure eta.** My §Kernel-risk bullet on those two lines is confirmed.
3. **Non-circular, and the obligation is discharged.** `compactCurlLocalUpgrade` is *proved* at
   `Euler/ComparatorLocalEvolution.lean:91` (confirming my row E3/E4). The conversion genuinely **consumes**
   the challenge solution's Euler equation `h.euler` (`Euler/ProjectedEulerPairing.lean:95`), so it fails
   for a field that is not a solution; and the `Evolution` that is finally contradicted is the
   independently-constructed `L.evolution` (`Euler/ComparatorIdentification.lean:31`), not one derived from
   the hypothetical global solution. So the argument is not "assume a solution to build the object that
   refutes it".
4. Kernel: exactly one `decide` in that chain, on `(3 : ℕ) ≠ 0` (`Euler/CompactSolenoidalDensity.lean:39`);
   0 `sorry`/`axiom`/`macro`; `termination_by` only in `EulerProof.lean` and an H⁶-pressure file, both
   off-path.

**Child escalation, which I can close from my own reading.** The child flagged
`canonical_vorticity_hasCompactSupport` (used at `Euler/Solution.lean:30`) as "the only unclosed
hypothesis" — that is correct *from inside their scope*, but it is not open: it is proved at
`Euler/CanonicalVorticityConfinement.lean:79` from `canonical_vorticity_support` (line 69) via
`IsCompact.of_isClosed_subset` and `isClosed_tsupport`, and `canonical_vorticity_support` is the H³
stability argument I audited as row **E6** (`evolution_vorticity_support`,
`Euler/CanonicalVorticityConfinement.lean:28`, which needs `initialDatum_Hm 3` and
`Evolution.curl_tendsto_of_initial_h3`). **Closed — no open hypothesis at `Solution.lean:24-30`.**

## Appendix C — consolidated state of the Euler spine after both children

Every name cited by `Euler/Solution.lean` now has a proved definition or theorem behind it, and no
statement in the deliverable is vacuous, junk-value-dependent, circular, or name-overclaiming, as far as
source reading can establish. Combined verdicts across the three reports: **142 OK, 2 UNCLEAR, 0
KERNEL-RISK, 0 SUSPICIOUS**, with `sorry`/`axiom`/`native_decide`/`macro` count = 0 everywhere on-path.

Exactly **two** load-bearing questions remain open, and neither is in this spine:

1. `limitEvolutionOfH3` (`Euler/OrdinaryEulerCauchy.lean:97`), reached through `exists_smooth_endpoint`
   (`Euler/OrdinaryEulerEndpoint.lean:39`): is the limit evolution's `time_law` **proved**? It is
   load-bearing three times over — `no_endpoint` → the `T = T*` half of clause 8, `initial_nonzero` →
   clause 3, and the BKM contradiction. If it manufactures an `Evolution` that need not satisfy the PDE,
   the BKM theorem is *false*, not vacuous. **Needs its own auditor.**
2. `initialDataLimit_no_euler` (`Euler/PacketStageInitialLimit.lean:106`) and the scale choice
   `constructionScales := Classical.choice (exists_scales …)`
   (`Euler/PacketInfiniteConstruction.lean:68`): the sole source of the lifespan's *finiteness*, inside
   the packet construction. Another worker's scope.
