# NSE deep audit - EulerProof.lean jet region: reverse-dependency analysis

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5), READ-ONLY.
Method: source-level (grep + python) declaration graph. No `lake build` was run, so nothing here is kernel-checked.

## 0. Headline theorems and file wiring

| item | location |
|---|---|
| `Euler.euler_breakdown_R3` | `Euler/Solution.lean:33` |
| `Euler.exists_compact_smooth_euler_singularity` | `Euler/Solution.lean:43` |
| `EulerPacketInduction.exists_compact_smooth_euler_singularity` (inner form) | `Euler/EulerSingularity.lean:133` |
| placeholder/reference copies (Mathlib-only, not part of the proof) | `ComparatorChallenges/Euler.lean:85`, `:170` |
| root file | `Euler.lean` = `import Euler.EulerSingularity` (does NOT pull in `Euler/Solution.lean`) |

Import facts (computed over all 2659 `.lean` files):
* `Euler/EulerProof.lean` imports **only Mathlib** (no repo imports). 32 repo modules import it.
* `Euler.EulerProof` IS in the transitive import closure of `Euler.Solution` (1829 repo modules) and of `Euler.EulerSingularity` (1770).
* `ComparatorChallenges/Euler.lean` imports only Mathlib -> its closure contains no repo module (it is the reference/placeholder file).

So the file is compiled on the headline path. The interesting question is per-declaration use, below.

## 1. Graph construction (4 variants, to bracket the answer)

Parsed all 1829 modules in the headline import closure into **16221 declarations**
(`theorem|lemma|def|abbrev|instance|inductive|structure|class|axiom|opaque`), tracking the
`namespace`/`end` stack, `open` lines (incl. multi-line continuations) and `variable` blocks.
Edge `A -> B` iff an identifier token in A's body (comments stripped) resolves to B, where a token
`x.y.z` is matched against declaration full names by longest suffix, and B's module must be in A's
import closure.

| variant | short-name (`k=1`) rule | reachable decls (from `Euler/Solution.lean` pair) | of which in EulerProof.lean (/1239) |
|---|---|---|---|
| LOOSE | any decl with that short name | 11053 | 779 |
| MID | ns visible (enclosing ns prefixes + `open`s) or a sub-namespace of a visible ns | 8768 | 653 |
| STRICT | ns visible only | 2110 | 474 |
| MID+var-scope (primary) | as MID, plus `variable` blocks attributed to the FOLLOWING decls (correct Lean scoping) | 8782 | **653** |

The LOOSE variant demonstrably produces false edges (worked example in section 5), so the
primary numbers below are the MID+var-scope graph; STRICT is the conservative lower bound.

## 2. (a) Verdict per item in the region of interest

Shortest dependency chain from a headline theorem (chains are BFS-shortest in the primary graph):

### `EulerSpatialSobolevInverse.SpatialJet`  (EulerProof.lean:3064, `inductive`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/PacketFiniteLifespan.lean:42 EulerPacketInduction.initialDatum_divergence
    3. Euler/OrdinarySmoothLimit.lean:74 EulerOrdinarySobolev.SmoothLimitData.field
    4. Euler/OrdinarySmoothLimit.lean:27 EulerOrdinarySobolev.SmoothLimitData
    5. Euler/SmoothFieldSobolevTime.lean:40 EulerSmoothFieldSobolevTime.sobolevPath
    6. Euler/MeanOrbitSobolev.lean:71 EulerMeanSmoothRepresentative.ordinarySobolev
    7. Euler/CylinderSobolevSpace.lean:78 EulerCylinderSobolevSpace.ofJet
    8. Euler/EulerProof.lean:3064 EulerSpatialSobolevInverse.SpatialJet
### `EulerSpatialSobolevInverse.CoefficientJet`  (EulerProof.lean:3073, `inductive`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/EulerFiniteLifespan.lean:21 EulerPacketInduction.initialDatum_compact
    3. Euler/EulerFiniteLifespan.lean:17 EulerPacketInduction.initialDatum_support
    4. Euler/PacketInitialDatumSupport.lean:41 EulerPacketInduction.Stage.initialDataLimit_support_of_physical
    5. Euler/PacketInductionStage.lean:23 EulerPacketInduction.Stage
    6. Euler/BaseFirstPacketChoice.lean:90 EulerBaseDatum.FirstPacketChoice.parent
    7. Euler/ParentEulerSobolevChild.lean:32 EulerParentPacketFrames.SobolevData.child
    8. Euler/AllOrderDriftEquation.lean:33 EulerAllOrderDriftCorrection.ApproximationResidual
    9. Euler/SobolevCoefficientPressure.lean:79 EulerSobolevCoefficientPressure.coefficientSobolevOperator
    10. Euler/EulerProof.lean:3073 EulerSpatialSobolevInverse.CoefficientJet
### `EulerSpatialSobolevInverse.CoefficientJet.productConstant`  (EulerProof.lean:3196, `def`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/EulerFiniteLifespan.lean:21 EulerPacketInduction.initialDatum_compact
    3. Euler/EulerFiniteLifespan.lean:17 EulerPacketInduction.initialDatum_support
    4. Euler/PacketInitialDatumSupport.lean:41 EulerPacketInduction.Stage.initialDataLimit_support_of_physical
    5. Euler/PacketInductionStage.lean:23 EulerPacketInduction.Stage
    6. Euler/BaseFirstPacketChoice.lean:90 EulerBaseDatum.FirstPacketChoice.parent
    7. Euler/ParentEulerSobolevChild.lean:32 EulerParentPacketFrames.SobolevData.child
    8. Euler/AllOrderDriftEquation.lean:33 EulerAllOrderDriftCorrection.ApproximationResidual
    9. Euler/SobolevCoefficientPressure.lean:79 EulerSobolevCoefficientPressure.coefficientSobolevOperator
    10. Euler/EulerProof.lean:3196 EulerSpatialSobolevInverse.CoefficientJet.productConstant
### `EulerSpatialSobolevInverse.SpatialJet.multiply`  (EulerProof.lean:3223, `def`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/EulerFiniteLifespan.lean:21 EulerPacketInduction.initialDatum_compact
    3. Euler/EulerFiniteLifespan.lean:17 EulerPacketInduction.initialDatum_support
    4. Euler/PacketInitialDatumSupport.lean:41 EulerPacketInduction.Stage.initialDataLimit_support_of_physical
    5. Euler/PacketInductionStage.lean:23 EulerPacketInduction.Stage
    6. Euler/BaseFirstPacketChoice.lean:90 EulerBaseDatum.FirstPacketChoice.parent
    7. Euler/ParentEulerSobolevChild.lean:32 EulerParentPacketFrames.SobolevData.child
    8. Euler/AllOrderDriftEquation.lean:33 EulerAllOrderDriftCorrection.ApproximationResidual
    9. Euler/SobolevCoefficientPressure.lean:79 EulerSobolevCoefficientPressure.coefficientSobolevOperator
    10. Euler/EulerProof.lean:3223 EulerSpatialSobolevInverse.SpatialJet.multiply
### `EulerSpatialSobolevInverse.CoefficientJet.pressureConstant`  (EulerProof.lean:3283, `def`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/EulerFiniteLifespan.lean:21 EulerPacketInduction.initialDatum_compact
    3. Euler/EulerFiniteLifespan.lean:17 EulerPacketInduction.initialDatum_support
    4. Euler/PacketInitialDatumSupport.lean:41 EulerPacketInduction.Stage.initialDataLimit_support_of_physical
    5. Euler/PacketInductionStage.lean:23 EulerPacketInduction.Stage
    6. Euler/BaseFirstPacketChoice.lean:90 EulerBaseDatum.FirstPacketChoice.parent
    7. Euler/ParentEulerSobolevChild.lean:32 EulerParentPacketFrames.SobolevData.child
    8. Euler/AllOrderDriftBudget.lean:19 EulerAllOrderDriftCorrection.Budget
    9. Euler/CorrectionEnergyMajorants.lean:109 EulerCorrectionEnergyMajorants.combinedConstant
    10. Euler/CorrectionEnergyData.lean:21 EulerCorrectionEnergyData.SpatialBudget
    11. Euler/EulerProof.lean:3283 EulerSpatialSobolevInverse.CoefficientJet.pressureConstant
### `EulerSpatialSobolevInverse.SpatialJet.solvePressure`  (EulerProof.lean:3315, `def`) - **NOT-REACHED**
    no chain; see NOT-REACHED evidence below
### `EulerSpatialSobolevInverse.SpatialJet.word`  (EulerProof.lean:3393, `def`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/PacketFiniteLifespan.lean:42 EulerPacketInduction.initialDatum_divergence
    3. Euler/OrdinarySmoothLimit.lean:74 EulerOrdinarySobolev.SmoothLimitData.field
    4. Euler/OrdinarySmoothLimit.lean:27 EulerOrdinarySobolev.SmoothLimitData
    5. Euler/SmoothFieldSobolevTime.lean:40 EulerSmoothFieldSobolevTime.sobolevPath
    6. Euler/MeanOrbitSobolev.lean:71 EulerMeanSmoothRepresentative.ordinarySobolev
    7. Euler/CylinderSobolevSpace.lean:78 EulerCylinderSobolevSpace.ofJet
    8. Euler/EulerProof.lean:3393 EulerSpatialSobolevInverse.SpatialJet.word
### `EulerJetProductBounds.levelNorm`  (EulerProof.lean:4697, `def`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/EulerFiniteLifespan.lean:21 EulerPacketInduction.initialDatum_compact
    3. Euler/EulerFiniteLifespan.lean:17 EulerPacketInduction.initialDatum_support
    4. Euler/PacketInitialDatumSupport.lean:41 EulerPacketInduction.Stage.initialDataLimit_support_of_physical
    5. Euler/PacketInductionStage.lean:23 EulerPacketInduction.Stage
    6. Euler/BaseFirstPacketChoice.lean:90 EulerBaseDatum.FirstPacketChoice.parent
    7. Euler/ParentEulerSobolevChild.lean:32 EulerParentPacketFrames.SobolevData.child
    8. Euler/AllOrderDriftBudget.lean:19 EulerAllOrderDriftCorrection.Budget
    9. Euler/CorrectionEnergyMajorants.lean:109 EulerCorrectionEnergyMajorants.combinedConstant
    10. Euler/CorrectionEnergyData.lean:21 EulerCorrectionEnergyData.SpatialBudget
    11. Euler/SobolevGevreyOperators.lean:18 EulerSobolevGevreyOperators.weightedNorm
    12. Euler/H6Pressure.lean:72 EulerH6Pressure.blockNorm
    13. Euler/EulerProof.lean:4697 EulerJetProductBounds.levelNorm
### `EulerJetProductBounds.boundLevel`  (EulerProof.lean:4706, `def`) - **ON-PATH**
    1. Euler/Solution.lean:33 Euler.euler_breakdown_R3
    2. Euler/EulerFiniteLifespan.lean:21 EulerPacketInduction.initialDatum_compact
    3. Euler/EulerFiniteLifespan.lean:17 EulerPacketInduction.initialDatum_support
    4. Euler/PacketInitialDatumSupport.lean:41 EulerPacketInduction.Stage.initialDataLimit_support_of_physical
    5. Euler/PacketInductionStage.lean:23 EulerPacketInduction.Stage
    6. Euler/BaseFirstPacketChoice.lean:90 EulerBaseDatum.FirstPacketChoice.parent
    7. Euler/ParentEulerSobolevChild.lean:32 EulerParentPacketFrames.SobolevData.child
    8. Euler/AllOrderDriftBudget.lean:19 EulerAllOrderDriftCorrection.Budget
    9. Euler/CorrectionEnergyMajorants.lean:109 EulerCorrectionEnergyMajorants.combinedConstant
    10. Euler/CorrectionEnergyData.lean:21 EulerCorrectionEnergyData.SpatialBudget
    11. Euler/EulerProof.lean:4706 EulerJetProductBounds.boundLevel

### Inductive constructors / eliminators
`SpatialJet.zero/.succ` and `CoefficientJet.zero/.succ` and `match`/`induction` eliminations do occur
inside **56 reachable declarations**, including outside EulerProof.lean, e.g.
`Euler/CylinderSmoothOrbit.lean:63 EulerCylinderSmoothOrbit.spatialJet` (builds `.zero`/`.succ`),
`Euler/CoefficientPathSmooth.lean:99 EulerCoefficientPath.coefficientJet`,
`Euler/ConstantCorrectionData.lean:43 EulerConstantCorrection.jet`,
`Euler/CylinderSobolevSpace.lean:91 word_has_jet`, and in-file
`EulerProof.lean:3086 truncate`, `:3093 sobolevNorm`, `:3098 nonneg`, `:3105 value_norm_le`,
`:3112 truncate_norm_le`, `:3122 lower_norm_le`. So the two inductive families are genuinely
constructed and eliminated on the headline path, not merely mentioned.

### NOT-REACHED evidence for `SpatialJet.solvePressure` (EulerProof.lean:3315, `termination_by` 3331)
* In the primary graph **no reachable declaration anywhere contains the token `solvePressure`** (0 hits over 8782 reachable decls).
* `solvePressure` has 24 consumers repo-wide (all in the graph):
  `EulerProof.lean:3333 solvePressure_norm_le`, `:4615/:4636/:4658 EulerPressureJetIdentities.SpatialJet.pressure_word_*`,
  `:5057 pressure_level_recurrence`, `:5120/:5170 EulerPressureGevrey.pressure_*_majorant`,
  `:10299 exists_smooth_pressure`, `:12971 pressure_shifted_weighted_bound`,
  plus `Euler/SobolevCoefficientPressure.lean:107 pressureSobolevOperator` (+`:117`,`:125`),
  `Euler/H6PressureInverse.lean:16/29/72/105`, `Euler/UnshiftedPressure.lean:94`,
  `Euler/H6PressureConstants.lean:171`, `Euler/GevreyPressureTransport.lean:23/64`,
  `Euler/GevreyPressureShifted.lean:33`, `Euler/DriftPreservingTransport.lean:52`,
  `Euler/H6NonlinearPressure.lean:34`, `Euler/NonlinearPressureLower.lean:18`,
  `Euler/SobolevGevreyOperators.lean:109`.
  **None of these 24 is reachable.**
* Backward closure of `solvePressure` = **177 declarations, none reachable**. Its 35 maximal (unused) roots
  include named-looking results that grep confirms are cited nowhere else in the repo, e.g.
  `Euler/AllOrderLiftedCorrection.lean:74 exists_smooth_lifted_correction` (1 grep hit = its own decl),
  `Euler/AllOrderSmoothPressure.lean:49 exists_smooth_pressure_graph` (1 hit),
  `Euler/GraphPressurePotential.lean:63 coercive_pressure_has_graph_potential` (1 hit),
  `Euler/AllOrderDriftFinite.lean:63 Budget.family` (1 hit),
  `Euler/SobolevCoefficientPressure.lean:125 pressureSobolevOperator_bound` (1 hit).
  i.e. a whole ~177-declaration coercive-pressure-solve development hangs off nothing.
* In the LOOSE graph `solvePressure` *appears* reachable, but the connecting edge is provably spurious
  (section 5), so the LOOSE positive should be discarded.

Summary table:

| item | EulerProof.lean line | verdict (primary) | STRICT | LOOSE |
|---|---|---|---|---|
| `inductive SpatialJet` | 3064 | ON-PATH | reached | reached |
| `inductive CoefficientJet` | 3073 | ON-PATH | reached | reached |
| `CoefficientJet.productConstant` (term. 3202) | 3196 | ON-PATH | reached | reached |
| `SpatialJet.multiply` (term. 3233) | 3223 | ON-PATH | NOT reached | reached |
| `CoefficientJet.pressureConstant` (term. 3291) | 3283 | ON-PATH | reached | reached |
| `SpatialJet.solvePressure` (term. 3331) | 3315 | **NOT-REACHED** | NOT reached | reached (spurious) |
| `SpatialJet.word` (term. 3399) | 3393 | ON-PATH | reached | reached |
| `EulerJetProductBounds.levelNorm` (term. 4703) | 4697 | ON-PATH | reached | reached |
| `EulerJetProductBounds.boundLevel` (term. 4712) | 4706 | ON-PATH | reached | reached |

Manually verified (read the source, qualified names, no guessing) edges carrying these verdicts:
* `Euler/SobolevCoefficientPressure.lean:79 coefficientSobolevOperator` body uses
  `CoefficientJet ...`, `SpatialJet.multiply K`, `K.productConstant`, `SpatialJet.multiply_norm_le` -> covers `CoefficientJet`, `multiply`, `productConstant`.
* `Euler/CorrectionEnergyData.lean:21 structure SpatialBudget` fields `inverse_five`/`inverse_six` use
  `(EulerH6Pressure.CoefficientJet.restrict ...).pressureConstant`, field `metric_base` uses
  `EulerJetProductBounds.boundLevel` -> covers `pressureConstant`, `boundLevel` (fully qualified, collision-free).
* `Euler/H6Pressure.lean:72 blockNorm` body: `levelNorm period J (n + r)` -> covers `levelNorm`.
* `Euler/MeanSmoothRepresentative.lean:79 exists_smooth_representative` body calls
  `EulerSmoothPressureRepresentative.exists_smooth_representative` (= `EulerProof.lean:10280`, fully qualified) -> the `SpatialJet` / `SpatialJet.word` route.
* `Euler/H6Pressure.lean:21`/`:86` define `EulerH6Pressure.SpatialJet.restrict` / `CoefficientJet.restrict`
  directly over `EulerSpatialSobolevInverse.SpatialJet` / `...CoefficientJet` (fully qualified).

## 3. (b) Reachable vs dead weight in EulerProof.lean

* declarations parsed in `Euler/EulerProof.lean`: **1239**
* reachable from `Euler.euler_breakdown_R3` + `Euler.exists_compact_smooth_euler_singularity` (primary graph): **653 (52.7%)**
* unreachable: **586 (47.3%)**  [STRICT bound: 474 reachable / 765 unreachable; LOOSE: 779 / 460]
* region of interest lines 3060-4720: **102 declarations, 63 reachable, 39 unreachable**.

Example dead declarations (unreachable, primary graph):
* `EulerProof.lean:366` EulerGevrey.triangular_inverse_polynomial_radius (theorem)
* `EulerProof.lean:1469` EulerLiftedPressure.coefficientOperator_comp_apply (theorem)
* `EulerProof.lean:2908` EulerSpatialSobolevInverse.coefficientValueNormedGroup (instance)
* `EulerProof.lean:4806` EulerJetProductBounds.leibnizConvolution_succ (theorem)
* `EulerProof.lean:5653` EulerSobolev.compact_iteratedFDeriv_norm_le (theorem)
* `EulerProof.lean:7671` EulerCylinderTransport.pureFieldDerivative_le_H5 (theorem)
* `EulerProof.lean:8817` EulerMixedCylinderTransport.prefixed_commutator_pointwise_le (theorem)
* `EulerProof.lean:11016` EulerVectorCalculus.compact_solenoidal_extension (theorem)
* `EulerProof.lean:13212` EulerPacketGrowth.cooperative_nonneg (theorem)
* `EulerProof.lean:14613` EulerPacketGrowth.reduction_of_order_derivative_relative (theorem)
* `EulerProof.lean:16159` EulerPacketRay.velocityThird (def)
* `EulerProof.lean:17649` EulerPacketFrameRenewal.target_sqrt_identity (theorem)

Unreachable declarations inside the region 3060-4720 (all 39):
* `EulerProof.lean:3166` EulerSpatialSobolevInverse.SpatialJet.sub_norm_le
* `EulerProof.lean:3315` EulerSpatialSobolevInverse.SpatialJet.solvePressure
* `EulerProof.lean:3333` EulerSpatialSobolevInverse.SpatialJet.solvePressure_norm_le
* `EulerProof.lean:3837` EulerNoncompactTransport.cutoff_product_transport
* `EulerProof.lean:3852` EulerNoncompactTransport.weak_divergence_integral_noncompact
* `EulerProof.lean:3921` EulerNoncompactTransport.metric_transport_noncompact_by_parts
* `EulerProof.lean:3947` EulerNoncompactTransport.aestronglyMeasurable_apply
* `EulerProof.lean:3956` EulerNoncompactTransport.metricEnergy_integrable
* `EulerProof.lean:3976` EulerNoncompactTransport.transportDirection_aestronglyMeasurable
* `EulerProof.lean:3982` EulerNoncompactTransport.metricTransport_integrable
* `EulerProof.lean:4009` EulerNoncompactTransport.metricCorrection_pointwise_bound
* `EulerProof.lean:4030` EulerNoncompactTransport.metricCorrection_integrable
* `EulerProof.lean:4047` EulerNoncompactTransport.metric_transport_H1_bound
* `EulerProof.lean:4087` EulerNoncompactTransport.metric_transport_L2_H1_bound
* `EulerProof.lean:4120` EulerMetricEnergyEvolution.metric_energy_hasDerivAt
* `EulerProof.lean:4132` EulerMetricEnergyEvolution.metric_energy_evolution
* `EulerProof.lean:4146` EulerMetricEnergyEvolution.energy_derivative_bound
* `EulerProof.lean:4162` EulerMetricEnergyEvolution.regularized_metric_norm_hasDerivAt
* `EulerProof.lean:4175` EulerMetricEnergyEvolution.regularized_metric_norm_evolution
* `EulerProof.lean:4233` EulerLiftedMetricEvolution.liftedTransport_memLp
* `EulerProof.lean:4253` EulerLiftedMetricEvolution.liftedTransport
* `EulerProof.lean:4259` EulerLiftedMetricEvolution.liftedTransport_ae
* `EulerProof.lean:4269` EulerLiftedMetricEvolution.metric_transport_inner_eq
* `EulerProof.lean:4286` EulerLiftedMetricEvolution.metric_transport_inner_bound
* `EulerProof.lean:4305` EulerLiftedMetricEvolution.metricFamily
* `EulerProof.lean:4311` EulerLiftedMetricEvolution.lifted_regularized_energy_evolution
* `EulerProof.lean:4376` EulerRepresentativeMetricEvolution.liftedTransport_memLp
* `EulerProof.lean:4396` EulerRepresentativeMetricEvolution.liftedTransport
* `EulerProof.lean:4402` EulerRepresentativeMetricEvolution.liftedTransport_ae
* `EulerProof.lean:4412` EulerRepresentativeMetricEvolution.metric_transport_inner_eq
* `EulerProof.lean:4430` EulerRepresentativeMetricEvolution.metric_transport_inner_bound
* `EulerProof.lean:4460` EulerRepresentativeMetricEvolution.metricFamily
* `EulerProof.lean:4466` EulerRepresentativeMetricEvolution.lifted_regularized_energy_evolution
* `EulerProof.lean:4533` EulerPressureJetIdentities.gradientSpace_translation_derivative
* `EulerProof.lean:4564` EulerPressureJetIdentities.SpatialJet.word_mem_gradientSpace
* `EulerProof.lean:4577` EulerPressureJetIdentities.SpatialJet.word_mem_divergenceFreeSpace
* `EulerProof.lean:4615` EulerPressureJetIdentities.SpatialJet.pressure_word_projected_equation
* `EulerProof.lean:4636` EulerPressureJetIdentities.SpatialJet.pressure_word_inverse
* `EulerProof.lean:4658` EulerPressureJetIdentities.SpatialJet.pressure_word_norm_le

Note the contiguous dead blocks `EulerNoncompactTransport` (3837-4087), `EulerMetricEnergyEvolution`
(4120-4175), `EulerLiftedMetricEvolution` (4233-4311), `EulerRepresentativeMetricEvolution`
(4376-4466) and `EulerPressureJetIdentities` (4533-4658): ~500 consecutive lines of the region carry
no reachable declaration.

## 4. (c) Use outside EulerProof.lean (repo-wide grep, EulerProof.lean excluded)

| pattern | hits | files |
|---|---|---|
| `EulerSpatialSobolevInverse.SpatialJet` | 100 | 15 |
| `EulerSpatialSobolevInverse.CoefficientJet` | 136 | 31 |
| `SpatialJet (any)` | 226 | 46 |
| `CoefficientJet (any)` | 378 | 84 |
| `productConstant` | 126 | 32 |
| `multiply(jet-qualified)` | 30 | 8 |
| `pressureConstant` | 81 | 33 |
| `solvePressure` | 22 | 10 |
| `word(jet)` | 30 | 15 |
| `levelNorm` | 22 | 9 |
| `boundLevel` | 76 | 20 |

* `EulerSpatialSobolevInverse` and `EulerJetProductBounds` namespaces are declared ONLY in `Euler/EulerProof.lean`;
  the two jet inductives are unique in the repo (no duplicate `inductive SpatialJet` / `CoefficientJet`).
* `SpatialJetField` (`Euler/PacketCylinderSpatialJet.lean:17`) is a DIFFERENT structure - do not confuse it
  with `SpatialJet`; likewise `EulerH6Pressure.CoefficientJet.restrict` is a wrapper *around* this
  `CoefficientJet`, defined at `Euler/H6Pressure.lean:86`.
* `solvePressure` does have 22 external hits in 10 files, but every one of those consumer declarations is
  itself unreachable (section 2).

## 5. LIMITS - which way each answer can be wrong

Over-approximation (edges that are not real => an item can be called ON-PATH when it is dead):
* Short-name / dot-notation collisions. WORKED EXAMPLE: the LOOSE graph made
  `Euler/ParentEulerSobolevChild.lean:32 SobolevData.child -> Euler/CommonPressureRepresentative.lean:67 graphPressure`.
  Reading the source, line 49 is `simp only [ExactLiftedPacket.graphPressure, map_smul]` - a *different*
  `graphPressure` (a field of `ExactLiftedPacket`). This single false edge is what makes `solvePressure`
  look reachable in LOOSE. The MID/STRICT namespace filter rejects it.
* Names in `simp only [...]`/`unfold` lists and in statements of theorems that are themselves only
  *stated* count as uses; a decl "reached" this way may still be irrelevant to the kernel proof term.
* Structure fields are not parsed as declarations, so a token `X.foo` may bind to an unrelated global `foo`.
* Reaching a *statement* is not proof-relevance: a def can appear only in a hypothesis of a reachable
  lemma that is applied with that hypothesis discharged elsewhere.

Under-approximation (missing edges => an item can be called NOT-REACHED when it is used):
* `simp`/`aesop`/`omega`/`positivity`/`measurability` close goals with lemmas that are never named
  (`@[simp]`, `@[instance]`, default `simp` set). Such uses are invisible to grep. `solvePressure` is a
  `def`, so it cannot be pulled in by a `simp` set on its own, but a *definitional unfolding*
  (`simp [Foo]` where `Foo` unfolds to it, `rfl`, `decide`) could.
* Instance resolution and `attribute [instance]`, anonymous instances, `deriving` clauses.
* `export`/`alias`/notation/`local notation` renaming, and `open ... in` scoped opens (my `open` parse
  drops the `... in` tail).
* Mathlib-side declarations are outside the graph, so a route through a Mathlib lemma applied to a
  project def is not modelled.
* Elaboration-time metaprogramming, `Nat.rec`-style compiler-generated equation lemmas
  (`foo.eq_def`, `foo.induct`) that name a def indirectly.

Direction of the two headline claims:
* "8 of the 9 region items are ON-PATH" is robust: it rests on fully-qualified, hand-read references
  (section 2), so it survives the strictest filter (7 of 9 even under STRICT; `multiply` is qualified in
  `Euler/H6Pressure.lean:302` and `SobolevCoefficientPressure.lean:82`, so its STRICT miss is a
  false negative of that variant).
* "`solvePressure` + a 177-declaration pressure-solve development is dead weight" is the fragile claim.
  It is supported by three independent facts (0 reachable decls mention it; all 24 consumers unreachable;
  the 35 subtree roots have exactly 1 grep hit each = their own declaration), but it could still be wrong
  if some reachable proof uses one of those 177 lemmas through a `simp` set / instance / unfolding.
  It cannot be settled without `lake build` + `#print axioms` / `lake exe graph`-style kernel evidence.
* The 653/586 reachable/dead split for the whole file is the least precise number: it varies 474-779
  across variants (i.e. the dead fraction is somewhere between 37% and 62%). Only the trend is safe:
  roughly HALF of `Euler/EulerProof.lean` is not on the dependency path of the headline theorems.
