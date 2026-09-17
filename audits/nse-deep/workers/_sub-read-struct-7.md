# _sub-read-struct-7 -- structural read (READ-ONLY, NSE @ f9e8bc5)

Scope: 4 previously-unnamed structural files. Classification per rubric OK/NOTE/UNCLEAR/ESCALATE/KERNEL-RISK.

## 1. NavierStokes/LocalizedGaussianBounds.lean (565 lines, 23 decls)

VERDICT: essentially CLEAN. 1 structure, constructed 3 independent ways. No kernel risk. Junk-value
guards are all in-signature or safe-direction. This file is a useful POSITIVE CONTROL.

Detail:
- `structure UniformComplementJets` LocalizedGaussianBounds.lean:259-264 (Prop, fields `smooth`+`bounds`).
  NOT an unsupplied hypothesis: it is CONCLUDED without assuming itself at
  :276 `of_zero_germs` (from zero germs off the cells), :289 `of_germs` (from
  `LabelSumBounds.UniformClass` of a comparison family g), :464 `uniform_source_complement_of_zero`,
  :510 `uniform_source_complement_of_harmonicSupport`, :532 `uniform_source_complement_of_excluded_class`.
  It is also DESTRUCTED at :268 `.each` -> `ComplementJets` and consumed at :417/:431. Base case exists,
  so no closure-without-base-case. OK.
- Two routes are non-trivial, not just "source = 0": :510 goes through `InputSupportOn` +
  `sourceFamily_zero_germ_on` (support-based, source may be nonzero on the cells), and :532 transfers a
  genuinely nonzero excluded harmonic tail via `of_germs` (hypothesis `he : UniformClass ... angleLift
  (excludedSource ...)`, :547-548). So the complement supply is not only the zero-source shortcut at
  :130 / :464. OK.
- Junk-value sweep. Statements contain `/` only as numeral literals (`1/2`, `1/5`, `c*ell/25`,
  `c*ell/50`, :155/:160/:179/:219) -- no unconstrained denominator. The one inverse in the
  cone is `(s.delta x)`inv inside `StripData.growth` = `slow n * max 1 (s.delta x)inv`
  (WeightedClasses.lean:50-51). It is GUARDED TWICE: `max 1 _` and `delta_pos` on the domain
  (WeightedClasses.lean:40). At delta = 0 the junk value 0 gives growth = slow >= 1, which SHRINKS the
  majorant, i.e. strengthens every bound -- safe direction. Positive control, OK.
- `s.epsilon n ^ alpha` is rpow with `epsilon_pos` (WeightedClasses.lean:35) in-structure. OK.
- NOTE (shape 3, hypothesis side, non-fatal): the weight in the load-bearing theorems is
  `fun n x => Real.sqrt (s.zeta x) * W n x` (:82-83, :377-380) and `StripData` only requires
  `zeta_nonneg` (WeightedClasses.lean:43), never zeta > 0; `domain` may also be empty
  (:32-33 no nonemptiness). Degenerate `zeta = 0` / `domain = {}` makes the hypotheses
  `LocalJets ... amplitude` say "all jets <= 0" and makes the conclusions vacuous. Direction is safe
  (these are universally quantified over `s`), and real StripData witnesses with positive data exist in
  bulk (e.g. ActualPrimaryBounds.lean:29-31, ActualInitialMean.lean:27, BaseContextAssembly.lean:154),
  so this is a NOTE not an ESCALATE.
- `indexedCutoffError` :346-349 is defeq to `LinearWaveBounds.excludedSlotError`
  (LinearWaveBounds.lean:740-742) = `CopyData.localGaussian` (PeriodizedWaveBounds.lean:785-786); the
  L x I re-indexing at :398-400 therefore typechecks honestly, no silent substitution. OK.
- KERNEL RISK: none. No `inductive`, no `.rec`/`Acc.rec`, no `termination_by`, no `deriving`, no
  `decide`, no metaprogramming. Largest numeral in the file: 50 (:160, :219, :236).

Tally file 1: 23 decls read -- OK 22 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 2. NavierStokes/ActualWaveCoefficientPeriodicity.lean (223 lines, 20 decls)

VERDICT: CLEAN and demonstrably LOAD-BEARING. The one Prop-def is genuinely supplied from outside
itself; the one exact division in the cone is guarded by a proven positivity, not by a junk value.

Detail:
- Prop-def `NativeSourcesPeriodic` :159-164 appears in hypothesis position at :172 only. It IS
  CONCLUDED elsewhere without assuming itself: ActualCyclePeriodicity.lean:496-501
  `native_sources_periodic`, proved from `H : CycleAnalyticInvariant ...` + `Periodic x` + `Ordered l n`
  via `copies_source_ordered` (ActualCyclePeriodicity.lean:462 chain). NOT an unsupplied hypothesis. OK.
- Both capstones of this file are actually USED: :168 `particular_coefficients` at
  ActualCyclePeriodicity.lean:513-515 and :203 `signed_coefficients` at :517-518, inside
  `ActualCyclePeriodicity.step` (the cycle-invariant propagation). So this file is in the live cone. OK.
- JUNK-VALUE SWEEP, sharpest item in my block and it comes out CLEAN. `particular_phase` :136-155 is an
  EXACT identity whose content passes through `angularMode / (ChartScales.carrier h n : R)` (:149-150),
  and the phase field it compares is literally `absolutePhase ... / ChartScales.carrier h n`
  (CorrectionInitialization.lean:5290). The denominator is NOT constrained in `particular_phase`'s own
  signature -- but it is a CLOSED TERM, and `0 < (chartCoefficients j L).frequency n = carrier h n` is a
  THEOREM: CorrectionInitialization.lean:5305-5307 (`Scaling.carrier_frequency_pos` of
  `ChartScales.epsilon_pos h n`); cf. ChartScales.lean:246-248 `1 <= epsilon * carrier^2`. So no
  `x/0 = 0` collapse is possible here. This is the useful POSITIVE CONTROL the brief asked for: a
  division-carrying exact identity whose divisor is provably nonzero by a closed-term theorem. OK.
- Vacuity witness check on the translation content. `TranslationOn Omega z f := forall x in Omega,
  f (x+z) = f x` (ActualWaveRegularity.lean:172-173), and the shift is
  `pointDeck k = (0,(0, TorusAverages.latticePoint k))` :26-27 with
  `latticePoint k = ((k.1 : R),(k.2 : R))`, Frequency = Z x Z (TorusAverages.lean:140,
  TorusInverse.lean:21). So for k != 0 the shift is a NONZERO unit-lattice vector -- the statements are
  not the trivial `f (x+0) = f x`. `latticePoint_injective` TorusAverages.lean:146 confirms. OK.
- NOTE (shape 2/3, non-degeneracy not certified by the type, but a witness exists). The whole content of
  :168 sits on `ParticularWaveAssembly.modes v.residualBand`, and
  `modes N = (Finset.Icc (-N) N).erase 0` (ParticularWaveAssembly.lean:24). Hence `modes 0 = {}`: if
  `v.residualBand = 0` then `hsource` :172 is vacuous, the assembled sums at :101/:120 are empty sums,
  the block velocity/pressure are identically 0, and all three conclusions hold trivially. Nothing in the
  signature of :168 forbids `residualBand = 0` (`CycleCoefficients` carries no positivity for it).
  WITNESS that the live instance is non-degenerate: `ActualInitialization.lean:135  residualBand := 2`,
  so `modes 2 = {-2,-1,1,2}` (4 modes) at the call site ActualCyclePeriodicity.lean:513. Downgraded from
  ESCALATE to NOTE because of that explicit witness.
- Statement `/` occurrences elsewhere in the file: none (only the in-proof :143/:149-150 above).
  `conjugatePair_translation ... 1 m` :217/:219/:221 pins the pairing index to the literal 1; harmless.
- KERNEL RISK: none. No `inductive`/`structure`, no `.rec`, no `termination_by`, no `deriving`, no
  `decide`. Largest numeral: 3 (`Fin 3` :95) / 2 (`Fin 2` via imports). Arithmetic is over R and Z with
  no big literals.

Tally file 2: 20 decls read -- OK 19 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 3. NavierStokes/ActualExteriorPrefix.lean (161 lines, 14 decls)

VERDICT: CLEAN, and the strongest positive result in my block: the structure IS constructed for the
actual candidate, AND the domain it lives on is PROVABLY NONEMPTY by an explicit in-artifact witness.

Detail:
- `structure ExteriorStages B Nr A D P : Prop` :56-65 (5 EqOn fields). Used as a hypothesis at
  LocalAngularGrowth.lean:31, ActualPhysicalPrefixFields.lean:442 and :479. NOT an unsupplied hypothesis:
  it is CONSTRUCTED at ActualCandidateAssembly.lean:701-724 `exteriorStages`, by `refine <5 goals>` from
  the concrete `potentialStages / directStages / pressureStages B N0 hN`, using
  `initialPotential_exterior`, `positive_exterior` (:688-699), `direct_exterior` and
  `initialPressure_exterior`. No `ExteriorStages` hypothesis is in scope there (only
  `hN : geometricThreshold <= N0`). So the whole `ExteriorStages.*` namespace :103-157 is live.
- VACUITY WITNESS (the thing that could have killed this file). All 11 in-cone conclusions are `EqOn ...
  (exteriorDomain Nr)` or germs at `w in exteriorDomain Nr`, and
  `exteriorDomain Nr = (preterminal \ ActualPolarCoverage.active) INTER physicalSublevel h (Q Nr)`
  :23-25. If `active` swallowed `preterminal`, every theorem here would be an empty-set statement. It
  does not: LocalAngularGrowth.lean:81-124 `exists_ray_interval` proves, FOR EVERY Nr, a delta > 0 with
  `(1 - tau, BaseAngularGrowth.ray innerRadius tau) in exteriorDomain Nr` for all tau in (0, delta) --
  an explicit point, with the `not in active` leg discharged at :118-124 from
  `innerRadius = activeLeft/2 < activeLeft` (:71-77). So `exteriorDomain Nr` is a nonempty open set for
  every Nr. This is an EXHIBITED witness, not an opinion. OK.
- `exteriorDomain_open` :36-44 is what turns EqOn into germs (:47-51); the openness argument is honest
  (open complement of a closed Icc pullback + open sublevel). OK.
- `uncutPrefix_eqOn_first` :71-85 is the only real computation: `Finset.sum_eq_single 0` over
  `range (J+1)`, correct and non-vacuous (0 is in range (J+1), discharged at :83-84). Note the
  conclusion is only for prefix length `J+1`, never 0 -- honest, since `uncutPrefix A 0` is an empty sum
  and would NOT equal the potential. Good hygiene, not a defect. OK.
- JUNK-VALUE SWEEP: no `/` and no inverse anywhere in any statement of this file. Nothing to collapse. OK.
- Mild over-strength (shape 6 candidate, but NOT a finding): `potential_succ`/`direct_zero`/`pressure_succ`
  :60-65 are asked for ALL k while the consumers only need k <= J+1 (:107, :111, :117). Since the
  structure is actually constructed at ActualCandidateAssembly.lean:701 for all k, no weaker twin is
  being bypassed. Reported for completeness only.
- KERNEL RISK: none. `ExteriorStages` is a Prop-valued single-constructor structure (no large recursor,
  no `deriving`), no `inductive`, no `termination_by`, no `decide`, no metaprogramming. Largest numeral
  in the file: 1 (all indices are variables); no numeric arithmetic at all.

Tally file 3: 14 decls read -- OK 14 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 4. Euler/MeanPacketData.lean (139 lines, 21 decls)

VERDICT: sound and constructed, but it carries my ONE substantive finding: the record admits a
BOUNDARY-DEAD parameter regime (`Bc = L = r = 0`) and one of the two concrete witnesses in the artifact
IS that regime, so the boundary-localization / core-split channel of this record is exercised only by the
induction-stage witness. Both witnesses are cited below, so this is NOTE, not ESCALATE.

Detail:
- `structure Data` :25-64 (36 fields: 5 coefficient paths, 5 scalars, 5 scalar guards, 2 sign lower
  bounds, 2 inverse identities, 2 time-derivative identities, 2 field equations, `curvature_upper`,
  `small`). IT IS CONSTRUCTED: `EulerParentPacketFrames.Parent.meanData`
  ParentPacketSourceData.lean:54-89, field-by-field from a `Parent` plus `LowBounds G`
  (ParentPacketSourceData.lean:19-36). `LowBounds` is in turn constructed twice:
  (a) `lowBoundsOfPhysical` ParentPacketPhysicalCoefficients.lean:88-118 (from the actual physical
      gradient/pressure-force), and
  (b) `packetBaseLowBounds` BasePacketSetup.lean:66-67. So no unsupplied hypothesis anywhere in the chain.
- **FINDING (shape 2/4, degenerate witness).** `initialLowBounds_values` BaseEulerState.lean:56-62 proves
  BY `rfl` that the base witness has `Be = initialCoefficientCost`, **`Bc = 0`, `L = 0`, `r = 0`**, `K =
  initialCoefficientCost` (and BasePacketSetup.lean:72-73 re-proves `L = 0` by rfl). Feed that through
  `meanData` and, inside MeanPacketData.lean:
    * `core_lower` :50 becomes VACUOUS -- no `x` satisfies `‖ℓ • x‖ < 0`;
    * `r_le_quarter` :47 and `L_lower` :45 become `0 ≤ 1/4` and `C1*0 ≤ 0`;
    * the boundary term of `small` :64, `boundaryLocalizationC2*Bc*r^3*T`, is IDENTICALLY 0, so the
      smallness guard degenerates to `K*(T^2/2) + Be*T ≤ 1/2`;
    * `solver` :113-117 and `evolution` :120-128 are then run with boundary budget `D.L = 0`, i.e. the
      harmonic boundary correction is bounded by ZERO in that instance.
  So for the base packet the entire boundary-localization apparatus
  (`boundaryLocalizationC1/C2`, the core/exterior split at radius r) is a null channel. This is exactly
  the "survives because a quantity is identically 0" shape, and nothing in `Data` :38-48 forbids it:
  `Bc_nonneg`, `r_nonneg`, `K_nonneg` allow 0 and there is no lower bound on `r` or `L`.
- WHY IT IS ONLY A NOTE: a NON-DEGENERATE witness also exists, exhibited explicitly. `Stage`
  (PacketInductionStage.lean:23-55) carries `low : LowBounds parent` (:26) with
  `boundary_eq : low.L = boundaryLocalizationC1*low.Bc + 1` (:45, so `L >= 1`) and
  `radius_eq : low.r = baseRadius S.X` (:46, `baseRadius_pos`), plus
  `core_bound : low.Bc <= gradientConstant*S.X^1000 + ...` (:42). And `Stage S 0` IS BUILT:
  `Scales.firstStage` BaseInductionStage.lean:22-94, with `low := S.first.lowBounds S.j_one` (:38),
  `boundary_eq := rfl` (:52), `radius_eq := hlow.2.2.1` (:53); the family is then
  `stages` PacketInfiniteConstruction.lean:39-41 and `packets` :72. So `r > 0`, `L >= 1` Data does exist
  in the artifact -- the degenerate regime is a second, extra instance, not the only one. Anyone reading
  a `Data`-level estimate must still check WHICH witness is in play before claiming the boundary term
  does work.
- JUNK-VALUE SWEEP: this file is the cleanest kind. `/` occurs only with numeral denominators (:47 `1/4`,
  :64 `T^2/2` and `1/2`). The only inversions in the cone are BUILT SAFE:
  (i) instead of using a Mathlib inverse of `F.field t x` (which would silently be junk when F is not
      invertible), the record carries a SEPARATE field `FInv` :36 plus BOTH identities
      `inverse_left` :51 and `inverse_right` :52 -- so invertibility is certified by the type, not
      assumed one layer up. `opInv_left/right` :77-81 export it;
  (ii) `frameLower := meanFrameCoercivity D.T D.opInv` :130 unfolds to `((‖FInv‖+1)^2)⁻¹`
      (MeanFrameCoefficients.lean:21) -- the `+1` makes the inverse unconditionally positive, and
      `meanFrameCoercivity_pos` (MeanFrameCoefficients.lean:23-25) is proved with no hypotheses, so
      `frame_lower` :134 (`frameLower*‖v‖^2 <= ‖solenoidalFrame ...‖^2`) is a genuine, non-vacuous
      coercivity, not `0 <= something`. POSITIVE CONTROL: guards in-signature/in-term throughout.
- NOTE (opacity, not a defect): `evolution` :120-128 is `Classical.choice (sourceMeanSolver_strong ...)`
  (MeanSourceStrongInverse.lean:18-...). It is a `def`, so it is deterministic, but nothing beyond the
  `StrongMeanEvolution` interface can be known about it; no uniqueness lemma is offered here.
- `Data.ℓ_le_one` :30 is NOT used in this file (`solver`/`evolution` take only `ℓ`, `ℓ_pos`) but it IS
  used downstream (MeanPacketSobolevData.lean:94,104; PacketInitializedInitial.lean:126;
  PacketParentLabelBudgets.lean:97), so it is not a dead field.
- KERNEL RISK: none in this file. No `inductive`, no `.rec`, no `termination_by`, no `deriving`, no
  `decide`. `Data` is a plain (non-Prop) single-constructor structure. Largest numeral in the file: 4
  (`1/4` :47); exponents are 2 and 3. (For context only, outside my files, the same chain carries
  `S.X^1000` PacketInductionStage.lean:42, `^80` :34, `2000 <= D` and `1000000*geometryConstant*δ <= 1`
  PacketInductionScales.lean:89,94 -- all symbolic real arithmetic, no `decide`, so still no kernel risk.)

Tally file 4: 21 decls read -- OK 19 / NOTE 2 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## Block summary (4 files, 72 decls)

No ESCALATE, no KERNEL-RISK anywhere in this block. All three structures and the one Prop-def are
CONSTRUCTED by declarations that do not assume them:
`UniformComplementJets` (LocalizedGaussianBounds.lean:259) <- :276/:289;
`NativeSourcesPeriodic` (ActualWaveCoefficientPeriodicity.lean:159) <- ActualCyclePeriodicity.lean:496;
`ExteriorStages` (ActualExteriorPrefix.lean:56) <- ActualCandidateAssembly.lean:701;
`EulerMeanPacketProvider.Data` (Euler/MeanPacketData.lean:25) <- ParentPacketSourceData.lean:54.
So the "closure without a base case" pattern does NOT extend to these four files.
Most important finding: the `Bc = L = r = 0` witness for `Data` (BaseEulerState.lean:56-62) makes the
boundary-localization channel of Euler/MeanPacketData.lean:45,47,50,64 a null channel in that instance.
Second: `ParticularWaveAssembly.modes 0 = {}` (ParticularWaveAssembly.lean:24) would make
ActualWaveCoefficientPeriodicity.lean:168 an empty-sum triviality; the live call site is saved only by
`residualBand := 2` (ActualInitialization.lean:135).
