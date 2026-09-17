# Worker _sub-read-struct-tail1 -- structural tail (READ-ONLY, NSE @ f9e8bc5)

## 1. Euler/ParentParticleInverse.lean (100 lines, 13 decls) -- CLEAN
Declares `structure ParticleInverse (A : Parent)` (`:17-21`: field/left_inverse/right_inverse/continuous).
CLOSURE-WITH-BASE-CASE: the two closure defs `ParticleInverse.restrictTime` (`:82`) and
`ParticleInverse.child` (`:90`) both consume an `I : ParticleInverse A` and produce another, so alone they
supply nothing -- BUT genuine base constructors exist outside the file:
`Euler/BaseEulerInput.lean:37 solutionInverse` (from `(...).particleInverse`),
`Euler/BaseStaticEuler.lean:109 baseInverse`, `Euler/BaseEulerParent.lean:119`, and
`Euler/BaseEulerState.lean:41 initialInverse`. So NOT an unsupplied hypothesis.
Junk-value sweep: the only inverses are `A.ell⁻¹` (`:33,:36`) inside `packetPosition_contDiff`, a pure
rewrite of `A.packetPosition_apply` -- it is an equality of the *definition* to itself, and `Parent.ell` is
positive by the Parent structure anyway; no unguarded division in any statement.
KERNEL RISK: none -- no inductive/rec/termination_by/deriving/decide/Fin; largest numeral = `80` in the
adjacent `k^80` callers, in-file largest numeral is `1` (`:92 hnext1`). OK.
Note (minor, not a defect): `field_initial` (`:49`) is the only theorem here that is not `include I` because
`I` is in its statement.
VERDICT: 13 decls read, OK 13 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 2. Euler/TransversePacketForcing.lean (108 lines, 15 decls) -- OK, one NOTE
Declares `structure Forcing (D : Data U) (raw : VectorField)` (`:25-31`) and
`structure InitialData (D : Data U)` (`:33-36`), plus `InitialData.zero` (`:38`), 4 abbrevs (`:65-76`) and
5 theorems (`:78-104`) that only re-export `EulerSourceCylinderEquation` lemmas.
BOTH structures ARE constructed, and non-degenerately, so no unsupplied hypothesis and no
only-degenerate-witness problem:
 * `Forcing`: degenerate witness `Euler/TransversePacketPrimaryMatching.lean:25 zeroForcing` (raw = 0) BUT
   live non-degenerate ones exist: `Euler/PacketJoinedSourceProfiles.lean:31 joinedSource_meanForcing`,
   `Euler/PacketSourceProfiles.lean:30/35`, `Euler/PacketConstructedProfiles.lean:32/38`,
   `Euler/PacketProfilesRegularity.lean:49/58`, plus closure ops
   (`TransversePacketHomogeneity.lean:23 smul`, `TransversePacketIntervalForcing.lean:27 initial`).
 * `InitialData`: degenerate witness is the in-file `.zero` (`:38-43`, `value := 0`); non-degenerate
   alternatives `Euler/PacketTerminalInitialData.lean:20 initialData`,
   `Euler/TransversePacketEndpoint.lean:108 terminalInitial`,
   `Euler/TransversePacketPrimaryMatching.lean:36 endpointData` / `:41 forwardInitial`,
   `Euler/TransversePacketLocalHistory.lean:22`.
NOTE (`:29 raw_eq`): `Forcing` is an EXACT identification of the prescribed `raw` with `pointField ...`, so
`Forcing P D raw` is essentially a proposition about `raw`; downstream files therefore use
`Nonempty (Forcing P D raw)` (e.g. `Euler/PacketJoinedSourceEquations.lean:86,104`,
`Euler/TransversePacketProvider.lean:152`) and `TransversePacketJoinedProvider.lean:26 path_unique` shows the
witness is unique. Harmless, but it means these 5 theorems say nothing until a caller EXHIBITS the identity;
they do (see the meanForcing/highForcing defs above).
Junk-value sweep: ZERO `/` or `⁻¹` anywhere in the file. All positivity side-conditions the abbrevs feed
(`D.T_pos.le`, `D.frameLower_pos`, `D.normalLower_pos`) are FIELDS of `Data`, i.e. in-signature guards --
a useful positive control.
KERNEL RISK: none (no inductive/rec/termination_by/deriving/decide/Fin/metaprogramming). Largest numeral in
file: `2` (`:2`-side `hp : 2 ≤ p` is in callers; in-file max literal is `0`). OK.
VERDICT: 15 decls read, OK 14 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 3. Euler/SmoothTimeFieldJoint.lean (84 lines, 8 decls) -- OK (1 NOTE)
Declares the Prop-def `SmoothTimeField.TimeDerivative T hT A A₁` (`:31-32`: `A₁` is the within-Icc time
derivative of the extended field), plus `realField` (`:20`), `jointDerivative` (`:34`) and 5 theorems.
HYPOTHESIS-ONLY PREDICATE, BUT IT HAS A BASE CASE: `TimeDerivative` is only ever a hypothesis in this file
(`:46`, `:73`). Its whole algebra elsewhere is closure-shaped (`Euler/SmoothTimeFieldChain.lean:42
congr_fields`, `:55 bilinear`, `:67 applyField`, `:91 compDisplacement`;
`Euler/ParentPacketRestriction.lean:27 restrictInitial`; `Euler/SmoothPhysicalGraphFlow.lean:66`;
`Euler/ChildParticleTime.lean:74`), all of which consume a `TimeDerivative`. The BASE CASES exist and are
real: `Euler/BaseEulerParent.lean:66 displacement_time` and `:74 velocity_time` prove
`SmoothTimeField.TimeDerivative I.T I.T_pos.le I.displacement I.velocity` from
`displacementFamily_time_derivative`, assuming NO TimeDerivative. It is then stored as a genuine field
`Euler/ParentPacketFrames.lean:31 displacement_time`. So NOT an unsupplied hypothesis.
TWIN WARNING (relevant to the rubric): there is a DIFFERENT same-named predicate
`EulerPacketCylinderField.TimeDerivative` with its own algebra (`Euler/PacketTimeAlgebra.lean:16 zero`,
`:20 add`, `:25 smul`, `:32`, `:41`) and its own base (`Euler/StaticCylinderField.lean:49 field_time`,
`Euler/PacketProfileRegularity.lean:15`). Do not merge the two when counting witnesses; both are supplied.
NOTE (`:46-47`, `:73-74`): the two joint-regularity theorems are stated on `t ∈ Ioo 0 T` with only
`hT : 0 ≤ T` in scope (`:18`), so at `T = 0` the hypothesis set on `t` is EMPTY and both theorems are
vacuously true. They are not FALSE and are ∀-quantified over `t`, so no defect: every live caller has
`T_pos` (e.g. `I.T_pos.le` at `BaseEulerParent.lean:66`, `D.T_pos.le`). Recorded as a T=0 degeneracy only.
Junk-value sweep: ZERO `/` and ZERO `⁻¹` in the file.
KERNEL RISK: none -- no inductive/rec/termination_by/deriving/decide/Fin/Type-valued if/metaprogramming.
Largest numeral in the file: `1` (`:73 ContDiffAt ℝ 1`). Benign by inspection.
VERDICT: 8 decls read, OK 7 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 4. Euler/PacketSourceEquations.lean (102 lines, 6 decls) -- OK (1 NOTE)
Declares `structure SourceCoefficientAgreement (M : MeanPacketProvider.Data) (D : TransverseProvider.Data U)
: Prop` (`:16-19`: the mean provider's inverse deformation `M.FInv`/strain `M.M` agree with the transverse
provider's clamped ones), plus 5 theorems that transport the mean/high/primary jet equations across that
agreement (`:25`, `:32`, `:40`, `:56`, `:85`).
CONSTRUCTED, and on the live path: `Euler/BaseFirstPacket.lean:24 firstPacketAgreement`,
`Euler/ParentPacketSourceData.lean:113` (a `where`-style instance for `(G.meanData H) (G.transverseData ...)`),
plus the re-exports `Euler/PacketInitialInput.lean:115 agreement`,
`Euler/ParentGeometryForwardChoice.lean:49 agreement`, `Euler/ParentGeometryForwardChoiceNoOptions.lean:74`.
So NOT an unsupplied hypothesis; ~70 downstream files consume it.
NOTE -- EXACT IDENTITY `= 0` at `:85-89` (`source_primary_equation`): this is one of the "exact identity, not
a bound" shapes. Its content rests on `Iprimary : InitialData P D` (`:23`) and on
`homogeneousForcing D` = the ZERO forcing (`Euler/PacketPrimaryRegularity.lean:53`, built from
`Field.zero P D.T`). So the RHS is 0 *by design* (homogeneous solution of the linear system), and the LHS
degenerates to `0 = 0` exactly when `Iprimary = InitialData.zero`
(`Euler/TransversePacketForcing.lean:38`). This is NOT a defect: the theorem is ∀-quantified over
`Iprimary`, and non-degenerate InitialData witnesses exist (`Euler/TransversePacketEndpoint.lean:108`,
`Euler/PacketTerminalInitialData.lean:20`, `Euler/TransversePacketPrimaryMatching.lean:36/41`). Recorded
because the same shape elsewhere was a real defect.
Junk-value sweep: the two `/`-looking hits (`:18`, `:28`) are the identifier `FInv`, NOT division. ZERO real
division and ZERO `⁻¹` in the file. `hT : M.T = D.T` (`:22`) is an in-signature equality (used via
`include hT`, `:39/:55/:84`) and `D.clamp`/`M.clamp` are total (`projIcc`), so no junk-value channel.
KERNEL RISK: none -- no inductive (the `structure ... : Prop` compiles to a structure, not an inductive
family), no rec/termination_by/deriving/decide/Fin/metaprogramming. Largest numeral: `2` (`:40,:56 hp : 2 ≤ p`).
Benign.
VERDICT: 6 decls read, OK 5 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 5. Euler/PacketForwardRadiusPolynomial.lean (193 lines, 8 decls) -- OK; a GOOD POSITIVE CONTROL on junk values
Declares `def canonicalRadius` (`:110`), `structure RadiusPrimitives (W : ℝ) : Prop` (`:114-135`, 21 fields --
a pure "everything is ≤ W" primitive bundle), and 5 arithmetic theorems (`:17 source_radius_le`,
`:63 inverse_nonneg`, `:67 common_le`, `:83 grade_sum_le`, `:137 canonicalRadius_le_envelope`,
`:188 canonicalRadius_power`).
CONSTRUCTED: `RadiusPrimitives` is supplied on the live path by
`Euler/ParentForwardRadiusPolynomial.lean:40` and `:112`, `Euler/ParentShortForwardRadius.lean:40/:113`,
`Euler/BasePacketUniformCosts.lean:43`, `Euler/ParentForwardUniformCosts.lean:35`, and closed under
weakening by `Euler/PacketSourceUniformEnvelope.lean:119 mono`. Not an unsupplied hypothesis.
TWIN WARNING: an identically named `EulerPacketRadiusPolynomial.RadiusPrimitives` exists at
`Euler/PacketInitializedRadiusPolynomial.lean:537` (with its own `mono` at
`Euler/PacketInitializedParameterBounds.lean:68` and its own supplier at
`Euler/ParentInitializedRadiusPolynomial.lean:143`). Both are supplied; do not count one for the other.
JUNK-VALUE SWEEP -- two inverse fields, both properly guarded, and the guards are IN-SIGNATURE:
 * `:118 mean_inverse_time : M.T⁻¹ ≤ W`. `M : EulerMeanPacketProvider.Data` (`:104`) carries a `T_pos`
   FIELD (used artifact-wide as `M.T_pos.le`, e.g. `Euler/PacketSourceProfiles.lean:27`), so `M.T > 0` comes
   with the argument itself -- `M.T⁻¹` is never Lean's junk `0`. Clean.
 * `:134 delta_inverse : δ⁻¹ ≤ W`. Here `δ : ℝ` (`:108`) is NOT constrained inside the structure, so
   `RadiusPrimitives` alone is satisfiable with `δ = 0` (then `δ⁻¹ = 0 ≤ W` for free, since `W ≥ 1` by
   `:115 one`). BUT both consumers carry `hδ : 0 < δ` in their OWN signature (`:137`, `:188`) and actually
   USE it (`terminal_cost_le δ W ξ hδ H.delta_inverse` at `:145`, `jetRadius_le δ W hδ ...` at `:169`).
   So this is a POSITIVE CONTROL for the junk-value pattern: the weak spot is in the structure, the guard is
   in the same signature as every theorem that inverts. No layer-hopping.
WITNESS/VACUITY: `canonicalRadius_le_envelope`'s hypothesis set is jointly satisfiable in the obvious way --
take `δ = 1`, `ξ = 0`, and `W` large enough to dominate the 20 finite costs (`W := max 1 (...)`); `:115 one`
`1 ≤ W`, `:116/:117` `T ≤ 1` are the only non-`≤ W` demands and both hold for the short-time data used at
`ParentShortForwardRadius.lean:40`. The named suppliers above are the actual witnesses.
KERNEL RISK: none -- no inductive/rec/termination_by/deriving/decide/`Fin.cases`/metaprogramming. `Fin 4`
and `Fin n` appear only as index types with n = 4 (`:36,:37,:41,:61,:112,:146,:167`), far below the n > 22
threshold. Largest numeral in the file: `108` (`:101`), then `64` (`:57`), `27` (`:100`); all are
real-literal coefficients inside `nlinarith`/`gcongr` arithmetic, no `decide`, no big-numeral Nat/Int
arithmetic. Benign by inspection.
VERDICT: 8 decls read, OK 8 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 6. Euler/MeanMollifierLimit.lean (58 lines, 7 decls) -- CLEAN
Declares the Prop-def `ScalarWeakHarmonicOn U f` (`:14-16`: `∀ φ` smooth compactly supported with
`tsupport φ ⊆ U`, `∫ f * Δφ = 0`), the mollifier `interiorMollifier n : ContDiffBump 0` (`:18-24`), and 5
theorems (`:26`, `:31`, `:35`, `:42`, `:50`).
CONSTRUCTED: `ScalarWeakHarmonicOn` is not merely a hypothesis -- `Euler/MeanHarmonicComponents.lean:26
scalarWeakHarmonicOn_of_vector_tests` PROVES it from a vector-valued test-function hypothesis (a genuinely
different predicate), i.e. a real base case; `Euler/MeanL2Scaling.lean:33` and
`Euler/MeanWeakHarmonicScaling.lean:13` are rescaling closures on top. Consumed at
`Euler/MeanMollificationHarmonic.lean:63/90/115`, `Euler/MeanWeakHarmonicInterior.lean:16`.
NON-DEGENERACY: `interiorMollifier n` has `rIn = cutoffScale n / 16`, `rOut = cutoffScale n / 8` with
`cutoffScale n = ((n:ℝ)+1)⁻¹ > 0` (`Euler/EulerProof.lean:3742,3749`), so both radii are STRICTLY positive
for every `n` -- the bump is never the degenerate zero-radius one, and `rIn_pos`/`rIn_lt_rOut` are discharged
in-file (`:21-24`). `:35 interiorMollifier_shape` is the exact `rOut = 2*rIn` relation, true by construction,
not by a junk value.
Junk-value sweep: all 6 `/` occurrences are numeric literals (`1/16`, `1/8`, `1/4`, `:19,:20,:26,:27,:33,:37`)
-- no division by a variable anywhere, no `⁻¹` in any statement.
KERNEL RISK: none -- no inductive/rec/termination_by/deriving/decide/metaprogramming; `Fin` does not occur.
Largest numeral: `16` (`:19,:37`). Benign.
VERDICT: 7 decls read, OK 7 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 7. Euler/BaseFirstPacketScales.lean (106 lines, 8 decls) -- OK; the SHARPEST POSITIVE CONTROL in my block
Declares `literalInitialError` (`:18`), `literalInitialPressureCost` (`:20`),
`structure FirstScaleGuards (J D : ℕ) (X : ℝ) : Prop` (`:53-68`, 10 guard fields), and 5 theorems.
CONSTRUCTED, AND WITH A SATISFIABILITY PROOF, NOT AN OPINION: `:70 eventually_firstScaleGuards` proves
`∀ᶠ X in atTop, FirstScaleGuards J D X` for any `J ≥ 1`, `D ≥ 2000` with
`firstFrequencyPower < D*(theta/100)`. Since `atTop` on ℝ is `NeBot`, that is an existence proof for the
whole 10-field guard bundle at once -- exactly the "exhibit a witness" standard. Consumed as a FIELD at
`Euler/PacketInductionScales.lean:96 first`, and at `:151` together with `48000 ≤ X`; its API lives in
`Euler/BaseLiteralFirstPacket.lean:15-87`.
JUNK-VALUE SWEEP -- one inverse, guarded IN THE SAME STRUCTURE:
 * `:59 radius_frequency : (baseRadius X)⁻¹ ≤ (X^D)^(3/4:ℝ)` and the standalone
   `:43 literal_radius_frequency_bound`. `baseRadius X = X^(-1000 : ℝ)`
   (`Euler/PacketBaseGuardScales.lean:16`), an rpow, so `baseRadius X = 0` would need `X = 0`; but
   `X` is pinned by the SAME structure's field `:54 x_one : 1 ≤ X`, and the standalone theorem carries
   `hX : 1 ≤ X` in its own signature (`:43`). So `(baseRadius X)⁻¹ = X^1000 > 0` -- never Lean's junk `0`,
   and `:55 radius_small : baseRadius X ≤ 1/4` is likewise a real constraint (it forces `X^1000 ≥ 4`).
   This is the cleanest in-signature guard I saw: the non-degeneracy is a FIELD of the same Prop-structure.
 * all remaining `/` are literals: `1/4` (`:18,:28,:55,:64,:81`), `3/4` (`:44,:50,:59`), `1/2` (`:68`),
   `theta/100` (`:71`), `(baseHorizon J X)^2/2` (`:65`). No variable denominator anywhere.
NOT VACUOUS: `literalInitialPressureCost D X = 2*C*X^(-1010)*(X^1000*firstRatio) + literalInitialError D X`
with `firstRatio > 0` (`firstRatio_pos`, used `:88,:91`) and `literalInitialError D X = (X^D)^(-1/4) > 0` for
`X > 1`, so `:64 pressure_small` and `:68 localized` constrain strictly positive quantities -- no
identically-zero collapse.
KERNEL RISK: none real, but the numerals are the largest in my block -- `2000` (`:43,:46,:70`, and
`(2000:ℝ) ≤ D` via `exact_mod_cast` at `:46`), `1010` (`:21,:33,:34,:61`), `1000` (`:21,:33,:61,:67,:87,:92`),
`100` (`:71`). Every one is an EXPONENT of a variable real (`X^1000`, `X^(-1010:ℝ)`) or a cast bound, so the
kernel never evaluates them; the only decision procedures are `omega` on `2000 ≤ D → 0 < D` (`:73`) and
`norm_num`/`positivity`/`linarith` -- no `decide`, no `native_decide`, no `Nat.rec`/`Acc.rec`, no `Fin`, no
`deriving`, no `termination_by`. Benign by inspection.
VERDICT: 8 decls read, OK 8 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 8. NavierStokes/Flatness.lean (131 lines, 9 decls) -- OK with 3 NOTEs; the only file in my block with real texture
Declares the Prop-def `PowerFlat l q f` (`:24-25`: `∀ n, ∃ C ≥ 0, ∀ᶠ x in l, |f x| ≤ C*|q x|^n`) and 8
lemmas (`:30`, `:38`, `:48`, `:62`, `:79`, `:101`, `:118`, `:126`).
JUNK-VALUE SWEEP -- the file DIVIDES BY A VARIABLE in four statements, and EVERY guard is IN-SIGNATURE.
This is the strongest positive control I found:
 * `:32 |x / scale ^ loss| ≤ C*|scale|^n` -- guarded by `:31 hscale : scale ≠ 0`, same signature, and the
   proof needs it (`abs_pos.mpr hscale` at `:34`).
 * `:40 PowerFlat l q (fun x => f x / q x ^ loss)` -- guarded by `:39 hq : ∀ᶠ x in l, q x ≠ 0`, same
   signature, used at `:44-45`.
 * `:81 hg : ∀ᶠ x in l, |g x| ≤ D / |q x| ^ loss` -- guarded by `:80 hq : ∀ᶠ x in l, q x ≠ 0`; the proof
   really needs it (`:87 hden : |q x|^loss ≠ 0`, `:96 div_self hden`). Note `loss = 0` makes it vacuous-ish
   (`D/1`), which is fine and intended.
 * `:128 div_pow_tendsto_zero` -- `hq_ne : ∀ᶠ x in l, q x ≠ 0` in its own signature (`:127`).
   No unguarded division, no `⁻¹`. Nothing here degenerates through `x/0 = 0`.
NOTE 1 -- FILTER VACUITY (worth escalating to the NavierStokes-side auditors, not a defect here): `l` is an
arbitrary filter with NO `[NeBot l]` anywhere in the file, so `PowerFlat ⊥ q f` holds for EVERY `f`, and
`:118 tendsto_zero` / `:126 div_pow_tendsto_zero` are trivially true at `l = ⊥`. The upstream geometric
hypothesis bundle `NavierStokes/BaseResidual.lean:350 structure PhysicalApproach` ALSO has no `NeBot` field
(all 6 fields are `∀ᶠ`/`Tendsto`, satisfiable with `carrier := ∅`, `l := ⊥`). The guard does exist, and it is
in-signature, at the place where flatness is finally converted into a contradiction:
`NavierStokes/BlowupImplication.lean:78 no_eventual_bound_of_profile` and `:95
no_continuous_extension_of_profile` both carry `[NeBot l]` plus `Tendsto q l (𝓝[>] 0)`. So: guarded, but the
guard is several layers from the definition -- the same shape the rubric calls out.
NOTE 2 -- RUBRIC ITEM 6, STRONGER HYPOTHESIS THAN USED, AND THE FILE ADMITS IT: `:62 PowerFlat.mul` assumes
`hg : PowerFlat l q g` but uses ONLY `hg 0`, i.e. plain eventual boundedness (`:66 hg 0`, `:69`); the
docstring `:60-61` states this outright ("Only boundedness of the second factor, the `n = 0` case of its
flatness, is used"). Its weaker-hypothesis twin `:79 mul_of_power_bound` sits directly below it and IS the one
actually used downstream (`NavierStokes/ResidualStability.lean:204`), while I found NO use of `:62
PowerFlat.mul` anywhere in the artifact. So this is a self-documented instance of the pattern, direction-safe.
NOTE 3 -- NAT TRUNCATED SUBTRACTION in a hypothesis: `:105 |f x| ≤ C*|q x|^(exponent j - loss)` uses ℕ-sub,
so when `loss > exponent j` the exponent silently becomes `0` and the stage bound degenerates to plain
boundedness. Harmless here because the proof only instantiates at `j` with `n + loss ≤ exponent j`
(`:108-110`, `Nat.le_sub_of_add_le`), where no truncation occurs. Worth recording as the ℕ analogue of the
junk-value shape.
DEAD DECL (not a defect, but relevant to the "who constructs it" question): `:101
powerFlat_of_stage_bounds` -- the intended non-degenerate BASE constructor of `PowerFlat` -- has ZERO uses in
the artifact (grep: only its own definition line). The bases actually used are
`NavierStokes/ResidualStability.lean:41 scalarFlat_zero` (DEGENERATE, `f ≡ 0`) and, non-degenerately, the
`AllJetsFlat` chain bottoming out at `NavierStokes/BaseResidual.lean:1624 baseResidual_allJetsFlat`
(`AllJetsFlat l (cartesianChart h ·).1 (baseResidual a h C d)`, proved from real jet-rate estimates, assuming
no flatness). So a non-degenerate witness DOES exist; `PowerFlat` is not an only-degenerate predicate.
Everything else in `NavierStokes/ResidualStability.lean:27-47` (`mono`, `const_mul`, `sum`) is closure.
KERNEL RISK: none -- no inductive/rec/`Acc.rec`/`Nat.rec`/`termination_by`/`deriving`/`decide`/
`native_decide`/`Fin`/Type-valued `if`/metaprogramming. All exponents are variables (`n`, `loss`,
`exponent j`), so no big-numeral arithmetic. Largest numeral in the file: `1` (`:120 hf 1`). Benign.
VERDICT: 9 decls read, OK 6 / NOTE 3 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## BLOCK SUMMARY (structural tail, 8 files, 74 decls)
NO ESCALATE, NO KERNEL-RISK flag anywhere in the tail. Explicitly: `Acc.rec` 0, `native_decide` 0, `decide` 0,
no `Fin n` with n > 22 (max n = 4), no `termination_by`, no `deriving`, no metaprogramming, no Type-valued
`if`. Largest numeral in the whole block: `2000` (`Euler/BaseFirstPacketScales.lean:43`), used only as an
exponent bound on a real variable.
No unsupplied hypothesis: all 6 structures and 2 Prop-defs in the block have a base constructor with
file:line (`ParticleInverse` -> `BaseEulerInput.lean:37`; `Forcing`/`InitialData` ->
`PacketJoinedSourceProfiles.lean:31` / `TransversePacketEndpoint.lean:108`; `TimeDerivative` ->
`BaseEulerParent.lean:66`; `SourceCoefficientAgreement` -> `BaseFirstPacket.lean:24`; `RadiusPrimitives` ->
`ParentForwardRadiusPolynomial.lean:40`; `FirstScaleGuards` -> `BaseFirstPacketScales.lean:70` (an
`∀ᶠ ... atTop` satisfiability proof); `ScalarWeakHarmonicOn` -> `MeanHarmonicComponents.lean:26`;
`PowerFlat` -> `BaseResidual.lean:1624` non-degenerately, and `ResidualStability.lean:41` degenerately).
No variable-shadowed instance guard: I checked every `[Fact (0 < P)]`/`[Fact (0 < period)]` section variable
against the theorem signatures in these files; no theorem re-binds `P`/`period`/`δ` as its own argument.
Two same-name TWIN pairs to keep separate when counting witnesses: `TimeDerivative`
(`SmoothTimeField` vs `EulerPacketCylinderField`) and `RadiusPrimitives` (`EulerPacketForwardRadius` vs
`EulerPacketRadiusPolynomial`); both members of both pairs are supplied.
The single most useful thing found: the FILTER-VACUITY chain in `NavierStokes/Flatness.lean:24` ->
`BaseResidual.lean:350 PhysicalApproach` (no `NeBot l` at either place) -> guarded only at
`BlowupImplication.lean:78/95 [NeBot l]`. Direction-safe, but it is a multi-layer guard, not an in-signature
one, and it governs the entire NavierStokes flatness half.
