
# _sub-read-struct-6 -- structural files audit (NSE @ f9e8bc5), READ-ONLY

Method: source read + cross-file grep. No `lake build` (0 .olean, pinned toolchain).
All line numbers are at commit f9e8bc5.

---

## FILE 1/4 -- NavierStokes/NaturalAxisRange.lean (252 lines, 26 decls: 1 structure, 1 instance, 24 thms)

VERDICT: **OK 24 / NOTE 2 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0**. Mathematically this file
is clean: I re-derived every numeral by hand and each is exact, not slack (see below).

### The structure (shape-1 test: is it ever constructed?)
`Parameters (h j : ℝ) : Prop` -- NaturalAxisRange.lean:13-17, fields `h_pos : 0 < h`,
`h_le : h <= 1/100`, `j_pos : 0 < j`, `j_le : j <= 1/20`.
CONSTRUCTED: yes -- `ofSmall` (NaturalAxisRange.lean:20-21) from
`NaturalAxisData.SmallParameters` (NaturalAxisData.lean:41-45), plus a `CoeOut` instance at :23.
`SmallParameters` itself is constructed from real profile data with an explicit witness at
MatchingConeBounds.lean:986-988 (`h := F.data.h` with `hh : F.data.h <= 1/1000`,
`j := min (jcap/2) (1/2000)`), and at MatchingDebtBounds.lean:898. So NOT an unsupplied
hypothesis; the hypothesis set is inhabited (witness: h = 1/2000, j = 1/2000).

### NOTE 1 (shape 6, INVERTED -- the stronger twin is the one always supplied)
This whole file is a re-derivation of NaturalAxisData.lean:47-378 with `SmallParameters`
(h,j <= 1/1000) replaced by the weaker `Parameters` (h <= 1/100, j <= 1/20). ~14 twin pairs
exist, e.g. `Z_at_root_lower` (Range:133 vs Data:205), `exists_cutoff_parameters`
(Range:212 vs Data:341), `ideal_prefix_cutoff_parameters` (Range:220 vs Data:355),
`ideal_prefix_root_positive` (Range:231 vs Data:370), `exists_unique_root` (Range:121 vs Data:176).
Direction is SAFE (weaker hypothesis = stronger theorem). But the widened range is never
exercised: every call site in the artifact reaches `Parameters` through `ofSmall`
(AppendixJoiningResults.lean:79, NominalProfile.lean:49 and :2666, ActivationContinuation.lean:789
and :1891, NaturalCore.lean:501, ReferenceBounds.lean:488, :1069, :1119, ActivationCone.lean:871,
:939, LeadingStressWeights.lean:1010, ActiveAnnulusWeight.lean:1065). NO site builds a
`Parameters` directly. So the docstring claim at :12 ("The complete printed range") is not
realised in the dependency closure -- the closure only ever uses the h,j <= 1/1000 corner.
This is the third instance of the strong/weak-twin pattern: it is now a named pattern, but with
the polarity reversed from the two earlier ones (here the SPARE is the weak one, and it is the
one carrying the downstream lemmas).

### NOTE 2 (empty-antecedent cutoff guarantee, direction safe)
`low_Z_has_H_margin` (:173-191) obtains `m > 0` from `IsCompact.exists_forall_le'` (:189) on
`K = Icc (-1) 1 inter {eta | |Z| <= j/10}` (:178). Mathlib's `exists_forall_le'` is happy with
`K = empty`, so if the low-Z set is empty then `m` is arbitrary and `exists_sigma` (:193) /
`exists_cutoff_parameters` (:212) return a sigma satisfying a vacuously-true implication.
Not a defect (the implication is exactly the wanted guarantee) but the theorems carry no content
on an empty low-Z set. `K` nonempty is never certified here.

### Numerals re-derived independently (all exact, none slack)
* `D h = 1/2 - h` (Data:27), `A h = 1/2 + h` (Data:28): `D_bounds` 49/100 <= D < 1/2 (:25) and
  `A_bounds` 1/2 < A <= 51/100 (:33) are exact at h = 1/100. OK.
* `L h eta = 1 - 2 h eta^2` (Data:30): `L_lower_bound` 49/50 (:41) exact at h=1/100, eta^2=1. OK.
* `neg_W_lower_bound` 287/100 (:51): I get -W = 3 - 8 h eta^2 + 2 D j eta, so
  -W >= 3 - 8/100 - j (using 2D < 1) >= 3 - 0.08 - 0.05 = 2.87. EXACT, not slack. OK.
* `base_source_lower` (:242): the claimed identity -W - h(1 - 2 eta U) = 3 - h + j eta (:245)
  is correct (the 8 h eta^2 terms cancel and 2 j eta (D + h) = j eta); bound 29/10 < 3 - 1/100
  - 1/20 = 2.94. OK.
* `H_left_neg` (:70): U j (-j/4) = 0 so H = -D j/4 < 0. `H_right_pos` (:75):
  H(-j/5) = (j/5)(1 - D - j^2/25) > 0. Both correct; `intermediate_value_Ioo` at :126 is applied
  with the correct orientation (-j/4 < -j/5 for j > 0, hab at :124). OK.
* `root_unique` (:105) is a genuine argument via `cross_identity` (Data:154), not a trick. OK.

### Junk-value sweep (division / inverse in statements)
Statements divide only by literal constants (4, 5, 10, 20, 50, 100). The one real quotient is
`chi h j sigma eta = H^2 / (H^2 + sigma^2)` (Data:38): if sigma = 0 AND H = 0 this is
Lean's 0/0 = 0, but every use in this file carries `0 < sigma` in the same signature
(`exists_sigma` :199, `exists_cutoff_parameters` :214, `chi_contDiff` needs `hsigma` at Data:277).
`(lt_div_iff0 hden)` at :209 is guarded by `hden : 0 < H^2 + sigma^2` (:207). CLEAN.

### Kernel risk
None. No `inductive` (the only new type is a `Prop`-valued `structure`, i.e. a one-constructor
`Prop`), no `.rec`, no `termination_by`, no `deriving`, no `decide`, no `native_decide`.
Largest numeral in the file: 100 (as `1/100`, `49/100`, `51/100`, `99/100`) and 400 (:203).
No big-numeral integer arithmetic.

---

## FILE 2/4 -- NavierStokes/SmoothParameterIntegral.lean (315 lines, 20 decls: 3 Prop-defs, 1 plain def, 16 thms)

VERDICT: **OK 19 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0**. This is a genuine,
load-bearing generic analysis library (dominated differentiation under the integral sign for
`iteratedFDeriv` in the parameter). It proves what it says; nothing here is dead or vacuous.

### The three Prop-defs, shape-1 test (each one IS constructed, with file:line)
1. `LocallyDominated F mu` -- :33-36. CONCLUDED at
   `LocallyDominatedDeriv.toLocallyDominated` :272-277, and constructed directly at real call
   sites: ParametricFlatFactor.lean:202, PhysicalMeanDomain.lean:685, MeanMomentBounds.lean:~183.
2. `LocallyDominatedOn F mu s` -- :127-130. CONCLUDED inside
   `contDiffOn_integral_Ioc_of_continuous_jet` :239-250 (from joint jet continuity on a compact
   `closedBall x eps times Icc a b`, via `IsCompact.exists_bound_of_continuousOn` :246 with the
   CONSTANT majorant `fun _ => C`). Not merely hypothetical.
3. `LocallyDominatedDeriv F mu` -- :267-270. CONSTRUCTED at ShapeTransition.lean:566 and :1057,
   RenormalizedHeatMoment.lean:63, EvenSmoothDescent.lean:67, FlatPrimitiveFactor.lean:236.

The consumer side is also live: `contDiffOn_intervalIntegral_of_continuous_jet` (:252) is applied
at ParametricRephase.lean:221, UniformAngularReset.lean:574, MeanRankUpdate.lean:1517,
ProfileHistories.lean:94, ActivationHolomorphic.lean:151, ReferencePath.lean:147,
NaturalCore.lean:178, WaveStateRegularity.lean:36. So no unsupplied-hypothesis defect anywhere
in this file: this is the OPPOSITE of the dead-predicate shape.

### Why it is not vacuous (and where the junk-value risk WOULD have been)
The Bochner integral of a non-integrable function is `0` in Mathlib, so a Taylor-coefficient
family defined as `fun x k => integral (jet F k x)` could silently be the zero family. That hole
is closed: `integrable_jet` (:40-46) / `integrable_jetOn` (:132-138) derive genuine integrability
of every order `k` FROM `h_dom` in the same signature, and the k=0 instance gives integrability
of `F x` itself (`‖jet F 0 x t‖ = ‖F x t‖`). Domination is therefore not decoration -- remove it
and the statements would degenerate to `0 = 0`. Checked and CLEAN.
No division and no inverse appears anywhere in this file, so the junk-value sweep is empty.

### NOTE (benign, empty-interval degeneracy)
`contDiffOn_integral_Ioc_of_continuous_jet` (:227) carries no `a <= b`: if `b < a` then
`Ioc a b = empty`, the integral is `0`, and the conclusion is trivially true. The wrapper
`contDiffOn_intervalIntegral_of_continuous_jet` (:252) does take `hab : a <= b`, and all call
sites pass `zero_le_one` or a real proof, so nothing downstream rests on the degenerate case.
Also `a = b` is admitted and is likewise trivial. Direction safe; recorded only for completeness.

### Correctness spot-checks
* The curry map in `hasFDerivAt_integral_jet` (:49-82) is the right one:
  `continuousMultilinearCurryLeftEquiv` (:55-56) is a `LinearIsometryEquiv`, which is what makes
  the majorant transport at :67-71 (`LinearIsometryEquiv.norm_map`) legitimate -- no constant is
  lost. Commuting the integral with it at :75-80 uses
  `ContinuousLinearEquiv.integral_comp_comm`, which is valid because the equiv is continuous
  linear; the integrability side condition is discharged by `integrable_jet`. OK.
* Order bookkeeping at :157-161 (`(1 : WithTop ENat) + k <= infinity`) is the real
  `ContDiffAt.iteratedFDeriv_right` requirement, not a weakened `k <= infinity`. OK.
* `iteratedFDeriv_integralOn` (:207) correctly bridges `iteratedFDerivWithin` to
  `iteratedFDeriv` through `iteratedFDerivWithin_of_isOpen` (:213) plus `hs.uniqueDiffOn` (:216) --
  the open-set hypothesis `hs` is genuinely needed and genuinely used. OK.
* `[ProperSpace H]` (:222) is needed for `isCompact_closedBall` (:242) and is real, not cosmetic.

### Kernel risk
None. No `inductive`, no `structure`, no `.rec`, no `termination_by`, no `deriving`, no
metaprogramming, no `decide`/`native_decide`. Only natural-number arithmetic is `k + 1`.
Largest numeral in the file: `1` (in `(m := 1)` / `(1 : WithTop ENat)`). Nothing to report.

---

## FILE 3/4 -- NavierStokes/FourierAlias.lean (743 lines, 54 decls: 1 Prop-def, 5 data defs, 1 abbrev, ~47 thms)

VERDICT: **OK 50 / NOTE 4 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0**. The load-bearing file of
my four. I checked the two things that could kill it -- the `M` inverse (junk value) and the
uniform-in-M jet bound -- and BOTH are sound. Details below, because the second one looked wrong
at first sight and is not.

### JUNK-VALUE SWEEP: `M` inverse. RESULT: CLEAN (this is the checked-and-passed case)
`(-M⁻¹) ^ p` carries the whole integration-by-parts gain and appears at :381, :396, :410, :546,
:576-584, and as `|M|⁻¹` at :566, :592, :630, :657, :686, :706. In Mathlib `(0 : ℝ)⁻¹ = 0`, so an
unguarded `M` would collapse every IBP identity to `alias = 0` (p >= 1) and make every decay bound
`‖...‖ <= C * 0 = 0` -- i.e. exactly the failure mode found elsewhere in this artifact. Each
statement carries `M <> 0` IN ITS OWN SIGNATURE:
* `totalIntegral_sourceJet` :375 `hM : M <> 0`; `cutoffAlias_sourceJet` :390 `hM`;
  `iteratedFDeriv_cutoffAlias_sourceJet` :404 `hM`; `cutoffAlias_fourierSourceJet` :545 `hM`.
* `cutoffAlias_arbitrary_order` :565 quantifies `forall M : R, M <> 0 -> ...` INSIDE the
  conclusion (the constant `C` is chosen before `M`, which is the right order and is what the
  docstring at :558-559 claims).
* `cutoffAlias_superflat` :685 `hM : eventually (M n <> 0)`;
  `radial_cutoffAlias_superflat` discharges it for real at :735 from
  `ChartScales.radialCoefficient_pos`.
No other division or inverse occurs in any statement of this file. So the two junk-value defects
found in the last block do NOT recur here.

### The Prop-def, shape-1 test
`TorusPeriodic (f : Plane -> F)` :31-32. CONSTRUCTED, not just assumed:
`totalIntegral_periodic` :165, `cutoffAlias_periodic` :176, `iteratedFDeriv_periodic` :229 all
conclude it, and :317 constructs one from nothing -- `periodic_finiteJet_bound hc (fun _ _ _ => rfl)`
for `fun z => deriv chi z.1`, which is Y-independent so `rfl` proves periodicity. Live.

### NOTE 1 -- exact same-statement twin predicate under two names
`FourierAlias.TorusPeriodic` (:31-32) is character-for-character the same statement as
`SmoothFourierData.UnitPeriodic` (SmoothFourierData.lean:62-63), and
`ParametricTorusInverse.Periodic f` (ParametricTorusInverse.lean:25) unfolds to
`forall p, UnitPeriodic (slice f p)`. The file relies on this: at :613-616 and :594-595 a
`ParametricTorusInverse.Periodic` is fed straight into `cutoffAlias_periodic` / `cutoffAlias_zero_mean`,
which are stated with `forall U, TorusPeriodic (fun Y => f (U, Y))`. That is sound (they are
definitionally identical), but it is the "same-named twin in another namespace" hazard the rubric
warns about, here benign. Recorded so a future auditor does not have to re-derive it.

### NOTE 2 -- a uniform-in-M bound that is CORRECT for a subtle reason (do not flag it)
`cutoffAlias_finiteJet_bound` :307-356 produces `C = 2^m * (B * (A * (b - a)))` with NO
`M`-dependence, and quantifies `forall M : R, forall v : Plane` afterwards (:312). This looks
false: writing the alias in the equivalent form `integral_a^b f (s, Y + (M (s - U)) v) ds`, the
U-derivative produces factors of `M`. It is nevertheless right, because `totalIntegral` is DEFINED
in shifted coordinates, `totalIntegral M v f z = integral over u of f (shift M v z u)`
(TransportPrimitive.lean:121, `shift M v z u = (z.1 + u, z.2 + (M * u) • v)`): the `M u` offset
depends on the integration variable ONLY, so differentiating in `z` never differentiates `M u` and
no factor of `M` is generated. `TransportPrimitive.iteratedFDeriv_totalIntegral_norm_le`
(TransportPrimitive.lean:720-726) therefore legitimately gives `C * (b - a)` uniformly in `M`.
(The two forms agree by the compact-support cancellation
`integral d_1 f = -M integral d_2 f . v`, which is the same identity the IBP uses.) VERIFIED OK.
The `2^m` factor is the honest Leibniz sum `sum over i of choose j i = 2^j` (:341-342) then
monotonised in `j <= m` (:347-348). No constant is lost through the curry isometry.

### Non-vacuity: EXPLICIT WITNESS for the capstone hypothesis set
`radial_cutoffAlias_superflat` :722-739 needs simultaneously: `hab : a <= b`, `hchi` smooth,
`hf` smooth, `hp : Periodic f`, `hm : ZeroMean f`, `hs : RadiallySupported a b f`,
`hleft : chi = 0 on (-inf, a]`, `hright : chi = 1 on [b, inf)`, `hh : 0 < h`.
WITNESS: a = 0, b = 1, h = 1; chi = any smooth 0-to-1 transition on [0,1] (Mathlib
`smoothTransition`); f (U, Y) = phi U * exp (2 pi i Y.1) with phi smooth, supported in (0,1),
phi <> 0. Check each: smooth YES; `Periodic` YES since exp (2 pi i (x + k1)) = exp (2 pi i x)
and there is no Y.2 dependence; `ZeroMean` YES since integral_0^1 exp (2 pi i x) dx = 0 (this is
`mean f p = coefficient (slice f p) 0`, ParametricTorusInverse.lean:41-44);
`RadiallySupported 0 1` YES since support f subset {U in (0,1)}; hleft/hright YES by construction;
0 < 1 YES. All nine hold at once with f <> 0, so the statement is NOT vacuous, and `f = 0` is not
forced anywhere. Also `vector .radial = (1, 1 - sqrt 2) <> 0` (TorusInverse.lean:195-196), so the
transverse direction is genuinely non-degenerate -- had `vector d = 0`, `directionalPartial d`
would be identically 0 and `inverse_solves` (ParametricTorusInverse.lean:528) would force f = 0.
Checked; it does not.

### NOTE 3 -- `a = b` degenerates the constant to 0, harmlessly
With `a = b` the constant at :319 is `2^m * (B * (A * 0)) = 0`, i.e. the theorems assert the alias
jets vanish. That is consistent (a continuous f with `RadiallySupported a a f` gives
`totalIntegral = 0`), not a defect; all downstream users pass a genuine `a < b`.

### NOTE 4 -- cosmetic
`TorusPeriodic` is declared `noncomputable def ... : Prop` (:31); `noncomputable` on a `Prop`-valued
def is a no-op. Same for `TorusPeriodic`-adjacent `torusMean`/`sliceMean` (:35, :38) where it is
meaningful. No effect on correctness.

### Other checks passed
* `cutoffAlias_supported_on_transition` :184-200 does NOT need `c <= d`: if `d < c` the two cutoff
  hypotheses are contradictory on `[d, c]` (chi = 0 and chi = 1), so nothing is smuggled in. The
  `deriv chi = 0` steps at :190-192 and :196-198 use `Filter.EventuallyEq.deriv_eq` correctly
  (locally constant on a NEIGHBOURHOOD, from `eventually_lt_nhds` / `eventually_gt_nhds`).
* `inverse_frequency_eventually_small` :628-652 and `inverse_frequency_power_le_epsilon` :655-674:
  the rpow bookkeeping is right (`epsilon^kappa = epsilon^(kappa/2) * epsilon^(kappa/2)` at
  :641-645 needs `epsilon > 0`, supplied by `ChartScales.epsilon_pos`; the exponent-ge step at
  :671-673 needs `epsilon <= 1`, supplied by `ChartScales.epsilon_le_one`). Both real side
  conditions are actually discharged, not assumed. `kappa = 1/100000 > 0` (ChartScales.lean:24) is
  checked by `norm_num` at :734.
* External dependency I did NOT re-verify (out of my file set):
  `ChartScales.slow_power_epsilon_tendsto_zero` (ChartScales.lean:275-281), which asserts
  `S n ^ a * epsilon h n ^ b -> 0` for EVERY real `a` and every `b > 0`. It is a real proof (via
  `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`), not an axiom; `grep` finds no `sorry`/`axiom` in
  ChartScales.lean or FourierAlias.lean.

### Kernel risk
None from this file: it declares no `inductive`, no `structure`, no `.rec`, no `termination_by`,
no `deriving`, no `decide`. It USES the imported `inductive Direction` (TorusInverse.lean:190-193,
two constructors, `deriving DecidableEq`) -- trivial. Recursion is only `Nat.rec` via
`induction p` (:502, :529) and `Function.iterate` (`sourceJet`, RadialAlias.lean:172), all
structural. Largest numeral appearing in this file: `4` (:737, `eventually_ge_atTop 4`); the only
other numerals are `0`, `1`, `2` (`(2 : R) ^ m`). Nothing for the kernel to grind on.

---

## FILE 4/4 -- Euler/PacketCylinderTermBudget.lean (121 lines, 19 decls: 1 structure, 5 defs, 13 thms)

VERDICT: **OK 18 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0**. Clean and fully live.
Small file, but I traced the structure and all five cost defs out of the file, because the whole
point of the file is to be a hypothesis carrier.

### The structure, shape-1 test: CONSTRUCTED, and every field is PROJECTED
`structure CoefficientBudget (C : CoefficientData P T O)` -- :16-26. NOT a `Prop`: it is
Type-valued and carries data (`Rc`, `amplitude`) plus three uniform Gevrey jet bounds
(`inverse_bound` :21, `strain_bound` :23, `normal_bound` :25), each of the shape
`‖iteratedFDeriv n (translateCoefficientPath ...) a‖ <= amplitude * majorant Rc 0 n`.
* CONSTRUCTED with real content at **PacketSourceCoefficientBudget.lean:87-111**
  (`sourceCoefficientBudget`), where `Rc := Rc`, `amplitude := C`, and -- worth noting --
  `normal_bound` (:106-111) is DERIVED from the inverse-frame hypothesis `hI` via
  `normalCoefficient_derivative_bound ... D.m0_unit`, i.e. only two of the three bounds have to be
  supplied by the caller. Transported by `CoefficientBudget.of_raw_eq`
  (PacketSourceCoefficientBudget.lean:40-61), which carries all three fields.
* Real instantiations: `forwardCoefficientBudget` (PacketForwardCoefficientBudgets.lean:19-22) and
  `joinedCoefficientBudget` (PacketJoinedCoefficientBudgets.lean:20-25), both fed from a
  `NormalBudget`. Consumers: PacketKnownTermBounds.lean, PacketInitializedCanonicalRadius.lean:21,
  PacketInitializedRadiusPolynomial.lean:533, PacketAngularPressureStepBound.lean:26,
  PacketUnweightedAdvection.lean:13, and ~15 more.
* I specifically checked for a DEAD FIELD, since `strain_bound` is not used inside this file
  (`slow_bound` :92 uses `inverse_bound`, `fast_bound` :106 uses `normal_bound`). It is not dead:
  `B.strain_bound` is projected at **PacketCylinderLinearTermBudget.lean:48** (the linear-part
  bound) and at PacketSourceCoefficientBudget.lean:58. All three fields are live.

### The five cost defs are all consumed, and the docstring claim is actually proved
`multiplierCost` :32, `slowCost` :33, `fastCost` :34, `linearCost` :35, `termCost` :36. The file's
docstring ("A single coefficient cost bounds every elementary nonlinear packet term") is realised
in PacketKnownTermBounds.lean:18-45: `KnownTerm.amplitude` maps each of the 7 constructors of
`KnownTerm` (PacketKnownDecomposition.lean:21-29) to one of these costs, and
`KnownTerm.amplitude_le` (:40) proves `k.amplitude B <= B.termCost` using exactly my file's four
`twice_*_le` lemmas (:70, :75, :78, :83). So all 13 theorems here are load-bearing, none decorative.

### NOTE (shape 3, examined and found HARMLESS -- the slack is deliberate)
`Rc_nonneg` (:19) and `amplitude_nonneg` (:20) both admit ZERO, and nothing in the type rules that
out. I checked what breaks:
* `majorant R d n = R ^ (n + d) * ((n + d)!)^2` (Euler/EulerProof.lean:196-197). With `Rc = 0` and
  `d = 0`, `majorant 0 0 n = 0` for every `n >= 1` (and `= 1` at `n = 0`), so a budget with
  `Rc = 0` DEMANDS that all coefficient jets of order >= 1 vanish. With `amplitude = 0` it demands
  the coefficient paths vanish identically.
* Both degeneracies therefore make the structure HARDER to inhabit and make the derived costs
  SMALLER, i.e. they strengthen `slow_bound` / `fast_bound` rather than trivialising them. This is
  the opposite polarity from the "non-degeneracy assumed but not certified" defect: there is no
  collapse to inspect.
* And the one place a zero cost could have hurt -- `one_le_termCost` (:64) -- is protected by
  design: `termCost = 2 * (1 + multiplierCost + slowCost)` (:36), so even at
  `amplitude = Rc = 0` we get `linearCost = 1` and `termCost = 2 >= 1`. The `1 +` and the leading
  `2 *` are exactly the slack that makes `one_le_termCost` and all four `twice_*_le` lemmas hold
  unconditionally. Verified by hand: `2*slowCost <= 2*(1+m+s)` needs `m >= 0` (:70-73 uses
  `multiplierCost_nonneg`), `2*linearCost = 2+2m <= 2+2m+2s` needs `s >= 0` (:78-81), and
  `fastCost <= slowCost` is just `3 <= 9` times a nonneg (:49-53). All correct.

### Junk-value sweep
No division and no inverse in any statement of this file. The imported constants are
polynomial, not rational: `sobolevCoefficientRadius (Fin 4) Rc = 4 * (max 1 4 * Rc) = 16 * Rc`
(ParameterSobolevCoefficient.lean:38-39) and
`sobolevCoefficientAmplitude (Fin 4) 6 Rc C = 2^6 * C * sum_{k<=6} (16 Rc)^k (k!)^2`
(:43-44) -- no denominators anywhere, so no `x/0` channel. CLEAN.
`productBlockConstant P` (Euler/CylinderPathProductBounds.lean:48-49) is
`card (SobolevWord 6) * sobolevProductConstant P 6`, also product-only; the ambient
`[Fact (0 < P)]` (:14) is genuinely inhabited for the real period
(`instance period_pos : Fact (0 < period)`, Euler/PacketTerminalDatum.lean:21), so this file's
theorems are reachable and not blocked on an uninstantiable class.

### Satisfiability of `slow_bound` / `fast_bound` hypotheses
`hp : forall t, g t * h t <= b t` with `g, h, b` strictly positive continuous on `Icc 0 T` is
satisfied by `g = h = b = 1` (a valid `C(Icc 0 T, R)` with `0 < 1`), together with
`hR : 0 <= R` and `hRc : 16 * B.Rc <= R` (take `R = 16 * B.Rc`). The `WordBound` premises are
supplied for genuinely nonzero fields downstream at PacketKnownTermBounds.lean:66+, so these two
theorems are not merely satisfiable-by-zero.

### Kernel risk
None in this file: the `structure` is non-recursive and generates only the usual projections and
`.rec`; no `deriving`, no `decide`, no `termination_by`, no metaprogramming, no big numerals
(largest literal in the file is `9` at :33; `6` and `Fin 4` are indices). ADJACENT, outside my
files, for the record: `Fintype.card KnownTerm = 15 := by decide`
(Euler/PacketKnownDecomposition.lean:31) is a `decide` on a `deriving Fintype` -- tiny (15
elements), no risk, but it is a `decide` in the cone.
