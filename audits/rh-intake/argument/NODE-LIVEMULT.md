# NODE-LIVEMULT: the live MultEq (`multEq_of_sides`), the PrimRows3 witness, live GalD, and pole information in the live Rallis chain

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the line. *(inferred)* = my reading. Nothing compiled or run.
Abbreviations as in NODE-LIVEPATH / MULTEQ / DETSIG / SWRANGE (`LTD/`, `TPS/`, `FRA`, `HTV`, `EPT`). New ones:
- `TEX` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/TraceEqXOfGeomExpansionX.lean` (live MultEq proof)
- `RSH` = `Development/AbelianVarietyTheory/Definitions/Divisors/RangeShape.lean` (GapG, LocalPC)
- `TFX` = `Development/AbelianVarietyTheory/Definitions/Divisors/TestFnConstTermVanishX.lean` (IsPCG, SpecTraceX, EllTraceX, EllipticPartX)
- `ETM` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllTraceOfMiddleX.lean`
- `DSC` = `Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/DiscreteSeriesCharacter.lean`
- `TB` = `TPS/TwistedBundle.lean`; `BWE` = `TPS/BwitExists.lean`; `CPI` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ColumnParamsInstanceData.lean`
- `GFN` = `Development/WeilBound/RepresentationTheoryGL/EisensteinResidues/AnisotropicGlobalForms/GlobalFormAtFrameLatNc.lean`; `DMH` = `…/AnisotropicGlobalForms/DmOfHyp.lean`

Tags: **[proved, read]**, **[proved, stmt]**, **[hyp]**, **[Published]**, **[not found]**.

## 0. Verdicts

| Q | Answer |
|---|---|
| 1(a) live MultEq | **The same predicate MULTEQ read.** `GlobalTheory.CuspMult.MultEq` has exactly one definition (FRA:118; grep `def MultEq\b` over the tree). The live chain concludes `MultEq R.toRealDat` (`LTD/TwistedMultiplicityOne.lean:21-22`; `LTD/UnitaryThetaCorrespondenceOfHyp.lean:15`). "Good" is the same `IsGoodRep`, and it is turned into a `NoFixed` type vector by the same `exists_typeVector_of_good_level_representation` (TEX:540). The groups, rank and archimedean models are as in MULTEQ §1: U(Y₀) vs U(W_i), same rank r (TEX:504-507), M₀ arbitrary with parameter `parA`, the W_i model fixed. **One difference:** the live gap hypothesis is `GapG` (consecutive HC entries differ by ≥ 100 r⁴, RSH:19-20, from `Given.gapR`), where MULTEQ had `Gap` (≥ r). |
| 1(b) proof | **A direct comparison of two simple trace formulas, one for each inner form.** There is no stabilisation and no Arthur multiplicity formula. `multEq_of_sides` (TEX:555-558) = `multEq_of_trCusp'` (TEX:537-553) ∘ `trCusp'_of_steps` (TEX:366-480) ∘ `traceEqX_of_geomExpansionX` (TEX:301-333) ∘ `geomExpansionX_of_parts` (TEX:282-299) ∘ `realStableX` (TEX:248-280). All of these were **read**. The "sides" are: (spectral) tr R(f) = Σ_i m_cusp(σ_i⊗M)·tr σ_i(f_f) (`SpecTraceX`, TFX:244-255); (geometric) tr R(f) = ∫ Σ_{δ: charpoly irreducible} f(x⁻¹δx) (`EllTraceX`, TFX:267-274; `ellKernel`, EPT:290-291) = Σ_P vol(T_P)·∏_v Φ_v·∏_w Φ_w (`EllipticPartX`, TFX:213-227). The test function is a pseudo-coefficient of M at every real place, e_τ·h·e_τ at the type places, an Iwahori coset function of a strictly regular torus element at an auxiliary split place U, and spherical elsewhere (`IsTestFin`, `…/ExistsAuxiliaryPlaceNotMemFinset.lean:431-437`). Published inputs: CuspRapidDecay, HarishChandraFinite, DixmierMalliavin, GreenCuspidal, DiscreteSeriesClassification, CuspTraceClass, GeometricLemma, ZelevinskyPolynomialRing. HarishChandraAnalyticity and Flath are bound as `_` and unused (`LTD/UnitaryThetaCorrespondenceOfHyp.lean:16`). LocalPC, RealStable and EllipticPart are in-tree theorems. Each is matched in §1.3. None is visibly stronger than the literature. |
| 1(c) counterexamples | **No shape escapes. Not ESCALATE.** (i) The dropped sign is **no longer dropped.** `dsChar` carries (−1)^{halfDim ε} with halfDim = p·q (DSC:173-177). `realStableX` sums it over the stable class with `finsum_discreteSeriesCharacter_eq_weylCharacter`, which assumes `Odd n` (stmt). The live rank is odd: r = k+m−1 with k and m even (`odd_r`, `Formalism/LocalToGlobal/HeckeThetaElements/DefsWt.lean:147-153`, read; used at TEX:516). (ii) Inner-form sign at ∞: for p+q odd both pq and p′q′ are even, so the stable orbital integrals of f_M and f_{M′} agree (TEX:330-333 uses only PhiReal, which depends on λ). (iii) Endoscopic and Speh parameters: the comparison never uses parameters. The only place endoscopy could enter is the κ-terms of elliptic tori with reducible characteristic polynomial. Those are killed by the type (`NonFieldTypeVanishingX`, used at ETM:166-167), and the remaining tori (P irreducible) have K(T)=1 (MULTEQ §2.3). (iv) Non-tempered at ∞: `LocalPC` requires tr π(f_M)=0 for **every** unitary irreducible π ≇ M (RSH:28; TFX:25-26). That is true for GapG-regular λ *(inferred: by Salamanca-Riba, with gaps ≫ 1 every unitary representation of that infinitesimal character is an A_𝔟(λ), i.e. discrete series; Clozel–Delorme gives the rest)*. |
| 2 witness | **Partly confirmed.** At the consumer the PrimRows3 is about `(selI …).Rl`, and the package/lattices/metrics are built from the **same term** `selI Fm (d3_a hc) x hx h i` (`TPS/Wire4F.lean:59-63`). `selI` is `fun … => (selB …).Q` (`TPS/TieTwRecOf.lean:29-30`). On the bundle side, `of_wit_alt` proves `PrimRows3 b.B.Q.Rl b.B.Q.F` (`TPS/CountsIrreducibilityConstants.lean:73-74`) from `w.y.intersectionNumber_baseChange.prim`. That is `Holds x.R x.F`, and it is tied to b in two steps: by **definitional** equality (the realisation `y : RealInAlt x …` is indexed by the same `x`), and then by the **propositional** field `eq : realPackageOfBundle b = realPackageOfRealInput y` (TB:44-48; `TPS/HermWCellLastMulMulVecEqOfInWb.lean:20-24`). The constructor is `bwit_exists_alt` (BWE:53-78). It sets b.B := cast (boundedRealisationOfInput y), the bundle's P := `divisionPairOfAdelicFormsFaceColumnsData x`, and `Holds x.R x.F` := `a.intersectionNumber_baseChange` (BWE:73-76). That `a : TwArgs` is built by `twArgs_exists` (CPI:153-162). There `Holds (newR z.R lam err) (reFace z.F Dc Sp Zsc)` is obtained **by transport** (`reFace_zero_part_conventions_chosen_again`, CPI:156, stmt) from `t.r.intersectionNumber_baseChange`, the Holds carried by the weighted point's record. **Not traced:** (α) the transport lemma's proof; (β) that the point record's Holds is the one built by `primRows3_of_parts`; (γ) that `selB` at a point is the `b.B` of the linked bundle (the `linkedAt_hPA_prmR` step). |
| 3 GalD | **Matches MULTEQ.** `real_data_weight_vector_family_alt` = `Stage4.stage4_alt` (`LTD/RealDataWeightVectorFamily.lean:18-35, 40-41`, read) → `twisted_scalar_conjugation_invariance` → `ScalConj.twisted_scalar_conjugation` (`LTD/TwistedScalarConjugationInvariance.lean:9-11, 23-24`, read) → `conjugate_baseLevel_of_howeUnramifiedCorrespondence` = `ScalConjRow.galD_of_inputs`, the lemma MULTEQ §2.5 read. The LTD wrapper takes ten Published arguments but passes on only `HoweUnram` (:10-11). **It proves `(R.toCx3 F).GalD F.cr false`**: Galois equivariance of the rational theta lift plus Rallis at the conjugate datum, for the same `R F` that `primRows3_of_parts` receives (`LTD/RealDataWeightVectorFamilyCore.lean:29, 33-34`). |
| 4 poles | **Nothing live needs pole information.** In the live Rallis chain the weakened DM is destructured as `⟨hDM1, -, hDM3⟩`, so the `True` slot is discarded (GFN:61). Holomorphy at s₀ = (rank B − rank A)/2 = t/2 comes from the **Siegel–Weil leaf**: `SiegelWeilUnitaryConvergent` gives `EisValueAt … s₀`, i.e. `HolValueAt E(g,·) s₀ (thetaMean)` (hEV, GFN:51). `doubling_zeta_value_at_eisenstein_holomorphic_point` (GFN:100-101, stmt) turns that into `HolValueAt` of the doubling zeta integral Z(s) = ∫ E(ι(g,1),s)⟨g u₁,u₂⟩ at s₀. To do so it uses DM's first conjunct: meromorphic continuation, a finite-order `EisRegularAt` at every point, and moderate growth (DMH:18). The function continued "by the identity theorem" in HIE2 is this Z(s), from Re s > rank A/2 (where it converges, GFN:84-97). It is regular at s₀ because E is (Ichino's / Kudla–Rallis's holomorphy at s₀ in Weil's convergent range is part of the leaf's conclusion). The L-value l at t/2 is a separate `HolValueAt` hypothesis from the caller (SWRANGE §1.2). |

## 1. Statement

### 1.1 Live MultEq
The Lean says (`LTD/UnitaryThetaCorrespondenceOfHyp.lean:15-18`):
`unitary_theory_of_harishChandra_langlands_alt : HCAnalyticity → DSClassification → CuspRapidDecay → HCFinite → CuspTraceClass → DixmierMalliavin → Flath → ZelevinskyPolynomialRing → GeometricLemma → GreenCuspidal → ∀ … (R : RealDat D A Ks) (F : Face D A), Given R F → MultEq R`.

`MultEq` is FRA:118-126 exactly as in MULTEQ §1 Q1(a). `Given` (`…/TwistedInnerProducts/RealLowestKTypeCoeffSquareIntegrable.lean:28-35`, read) bundles `core`, `params`, `types`, `guard` and **`gapR`**: 100 r⁴ ≤ λ_n − λ_{n+1}.

### 1.2 TRCusp′ (TEX:353-362, read)
For V, V′ of the same **odd** rank, assume:
- every consecutive HC gap is ≥ 100 r⁴ (`GapG`);
- M on V and M′ on V′ are discrete-series models with the same λ;
- T is a `NoFixed` type;
- the local isometries j_v are lattice-compatible, and Φ is the induced finite-adelic isomorphism.

Then for every irreducible admissible σ with a T-type vector, m_cusp^{DS}(σ⊗M) = m_cusp^{DS}(σ∘Φ⁻¹⊗M′). This is MULTEQ's TRCusp (HTV:39-48) with Gap replaced by GapG.

### 1.3 The sides and their inputs
| input | file:line | statement (math) | real theorem | status |
|---|---|---|---|---|
| `LocalPC` | RSH:22-39 | for odd r, GapG λ and every DS model D of U(p,q) with parameter λ, ∃ f ∈ C_c^∞, bi-K-finite, with: tr D(f)=1; tr π(f)=0 for every unitary irreducible π ≇ D; O_s(f)=0 at regular s with non-compact centraliser; O_s(f)=conj(dsChar(ε,λ)(θ))/vol at compact regular s | Clozel–Delorme pseudo-coefficients; the "all unitary π" clause holds for strongly regular λ *(inferred)* | proved in-tree (`localPC_holds`, via `…/LocalPseudoCoefficientExistenceUnitaryGroupStatement.lean:7-8`), proof not read |
| `SpecTraceX` | TFX:244-255 | for f a test datum, tr R(f) = Σ_i m_cusp^{DS}(σ_i, M)·tr σ_i(f_f) over a finite family covering every σ that contributes | the cuspidal spectral side, given vanishing constant terms (Deligne–Kazhdan / Arthur) | `SpecX.main ds tc` (`…/DivisorProofs/HasDSComp.lean:114`, stmt) |
| `EllTraceX` | TFX:267-274 | tr R(f) = ∫_{G(F)\G(𝔸)} Σ_{δ∈G(F), charpoly δ irreducible} f(x⁻¹δx) | simple trace formula | proved, read at top level (ETM:92-173, 186-189); see §2 |
| `EllipticPartX` | TFX:213-227 | that integral = Σ_P vol(T_P)·∏_v Φ_v(f_v)·∏_w Φ_w(f_w) (local sums over XSet) | Kottwitz-type expansion with K(T)=1 | `ellipticT` (no Published input), not opened |
| `realStableX` | TEX:207-213, 248-280 | at real w, Σ_{q∈XSet} O_q(f_M) = PhiReal = conj(χ_{F_λ})/vol | Σ_{W_K\W} Θ_{π}(wγ) = (−1)^{pq}·Weyl numerator / Δ; (−1)^{pq} = 1 since pq is even when p+q is odd | proved, read |
| `Separation` | HTV:73-81 | if Σ a_i tr σ_i(f_f) = 0 for all admissible f_f (any element of e_τ𝓗e_τ at S, any strictly regular Iwahori coset at U, spherical elsewhere), then a_i = 0 for every σ_i with a T-type vector | linear independence of characters: e_τ𝓗e_τ-modules at S, Hecke eigenvalues off S, Jacquet exponents at U *(inferred: injectivity of the Jacquet/weight map on the Iwahori block of GL_r)* | `trace_separation_of_iwahori_trace` ← IwahoriTrace, `exponentsSeparate gl ze` (stmt) |
| `SpecFin` | HTV:50-58 | finite multiplicities; finitely many σ with K-fixed vectors and m ≠ 0 | Harish-Chandra finiteness | `cuspidal_spectrum_finiteness_of_decay_harishChandra` (stmt) |

## 2. Argument

### 2.1 `multEq_of_trCusp'` (TEX:537-553, read)
- From IsGoodRep it gets a NoFixed type T and a type vector (:540).
- It writes Φ as ⊗_v j_v up to an inner automorphism b (:541).
- It obtains odd rank, GapG and equal λ (`params_match'`, :502-533, read). The rank is r for both groups (:504-507), oddness is `odd_r` (:516), and GapG comes from `hG.gapR` (:519).
- It rewrites both multiplicities as `mCuspDS` (:550-551), applies TRCusp′ (:552), and transports by b (:553).

### 2.2 `trCusp'_of_steps` (TEX:366-480, read)
1. Choose the auxiliary split place U ∉ S (:369), the local Haar measures with vol K_v = 1, and the archimedean pseudo-coefficients f_∞, f′_∞ (`exists_testArch`, :394-395).
2. Use SpecFin to get finite families σ₁ (on V) and σ₂ (on V′) of every σ with level-K fixed vectors and m ≠ 0. Merge them into one family τ_i containing σ (`exists_family`, :399-406).
3. For every admissible f_f, apply SpecTraceX on V and on V′ (:456, :464) and TraceEqX (:466, equal geometric sides). This gives Σ_i (m_V(τ_i) − m_{V′}(τ_i′))·tr τ_i(f_f) = 0 (:448-469).
4. Separation gives a_{j₀} = 0 for the index of σ (:473), hence equal multiplicities (:474-480).

### 2.3 Geometric side (ETM:92-173, read)
- Constant-term vanishing of f (from NoFixed, `ParabolicAndConstTermX`) makes R(f) a cuspidal operator, so the trace is the integral of the kernel (:104-110).
- **The auxiliary place U forces regular support:** f(x⁻¹δx) ≠ 0 ⇒ δ regular semisimple (`isRegularSemisimple_of_testFunction_ne_zero hIw`, :128-129). So central and other non-regular terms, including the identity term, are absent *legitimately*: f_U is an Iwahori coset function of a strictly regular torus element.
- Regular classes with reducible characteristic polynomial vanish in two cases (:162-173): `NonFieldTypeVanishingX` when IsNonFieldAniso (the elliptic tori from U(a)×U(r−a), killed by the type at v_a), and `HyperZeroX` otherwise (non-elliptic: centraliser non-compact at every real place, and the pseudo-coefficient's non-compact orbital integrals are 0, ETM:25-58).

### 2.4 TraceEqX (TEX:301-333, read)
Both expansions are Σ_P torVol·∏_v Φ_v·∏_ρ PhiReal(λ). The finite-place factors agree because j_v is a lattice-compatible isomorphism (`stableOrbitalIntegral_preserved_latticeIsometry`, :333). The real-place factors agree because PhiReal depends only on (P, λ).

### 2.5 Witness chain (Q2)
Consumer to producer:
1. W4F:59-63: `prows : PrimRows3 (selI …).Rl (selI …).F` goes into `CovolumeOntoIsometryConditions (selI …).Rl …`, and `packageOfPrimitiveLinks (selI …) … hP` builds the package. Same variable.
2. `AllRealisationsPrimitive` (`TPS/IndefiniteRealisationChoice.lean:46-49`) is PrimRows3 of `selI` at each point.
3. `PrimitivityBundleCondition b := PrimRows3 b.B.Q.Rl b.B.Q.F` (`TPS/CountsIrreducibilityConstants.lean:73-74`) is supplied by `of_wit_alt`.
4. `BundleWitness.y : TwistedBundle b x`, whose fields are `intersectionNumber_baseChange : Holds x.R x.F`, `y : RealInAlt x b.R b.S` and `eq` (TB:44-48, 57-61).
5. `Holds` = {prim : PrimRows3 R F, aux, ok, sep} (`…/AutomorphicMembership/StableIffCarrierEq.lean:87-91`).
6. `bwit_exists_alt` (BWE:53-78) takes `hM : ∀ q, MultEq q.x.what₂.r.z.R.toRealDat`. So MultEq also enters here directly, as `MultiplicityCondition`.
7. `twArgs_exists` (CPI:153-162): Holds of the re-faced, κ/λ-updated datum is obtained from the point record's Holds by transport.

## 3. Children

| # | name | file:line | statement | status | weight |
|---|---|---|---|---|---|
| 1 | `trCusp'_of_steps` + `multEq_of_trCusp'` | TEX:366, 537 | inner-form multiplicity equality from two simple trace formulas | proved, read | core |
| 2 | `localPC_holds` | via RSH:36 | pseudo-coefficient with trace 0 on all other unitary irreducibles (GapG) | proved, stmt | core; standard (Clozel–Delorme) |
| 3 | `ellTrace_of_middleX`, `hyperX` | ETM:92, 25 | simple TF: only regular classes with irreducible charpoly survive | proved, read (top) | core; standard (Arthur / Deligne–Kazhdan shape) |
| 4 | `nonFieldT` (NonFieldTypeVanishingX) | TFX:145-156 (def) | type at v_a kills elliptic tori with reducible charpoly | proved, not opened | core (this is the step that removes endoscopy) |
| 5 | `ellipticT` (EllipticPartX) | TFX:213 | product form of the elliptic terms | proved, not opened | core (Hasse principle, product formula; MULTEQ §2.3) |
| 6 | `trace_separation_of_iwahori_trace` | `…/TraceSeparationOfIwahoriTraceStatement.lean:13` | Separation | proved, stmt | core |
| 7 | `realStableX` + `finsum_discreteSeriesCharacter_eq_weylCharacter` | TEX:248; `…/FinsumDiscreteSeriesCharacterEqWeylCharacterStatement.lean:15-19` | stable sum of DS characters = GL character for odd n | proved, read / stmt | standard (Harish-Chandra) |
| 8 | `reFace_zero_part_conventions_chosen_again` | CPI:156 (use) | Holds survives the κ/λ update and re-facing | proved, stmt | core link for Q2 |
| 9 | `galD_of_inputs` | as MULTEQ §2.5 | GalD | proved, stmt | core for v ≠ v₀ |
| 10 | `doubling_zeta_value_at_eisenstein_holomorphic_point` | GFN:100 (use) | E holomorphic at s₀ ⇒ zeta integral holomorphic at s₀ | proved, stmt | glue |

## 4. Oddities

1. **Correction to MULTEQ Oddity 1.** The (−1)^{pq} sign is present in `dsChar` (DSC:176-177) and is absorbed by a lemma that assumes odd rank. The live rank is odd by `odd_r`. Consistent.
2. **The live MultEq needs no parameter theory.** Endoscopy is excluded on the geometric side (child 4), not by an appeal to Arthur. The correctness of MultEq therefore rests on children 3–6. The most delicate are `NonFieldTypeVanishingX`, which needs the descent formula O_γ^G = O_γ^M(f^{(P)}) at v_a, and `Separation`, which needs the Iwahori-block weights at U to separate representations. Neither proof body was read.
3. **`LocalPC` asks for tr π(f)=0 on all unitary π ≇ M,** not only tempered π. That is true only because GapG is huge (100 r⁴). With MULTEQ's weaker `Gap` it could fail (non-tempered A_𝔮(λ) has gaps 1 along 𝔩). The live code uses GapG.
4. **The identity term is removed by regular support at U, not by an error** (ETM:128-129). This is legitimate.
5. **The witness PrimRows3 is a transported Holds.** It concerns `newR z.R lam err` with the re-faced face (CPI:157-162), not z.R itself. What the slope inequality later uses is `(selI …).Rl` (W4F:61). Whether that equals the witness's x.R goes through `selB` and `linkedAt_hPA_prmR`, which I did not trace.
6. `twisted_scalar_conjugation` takes DM, SiegelEisensteinContinuation and eight other Published arguments and ignores all of them except HoweUnram (`LTD/TwistedScalarConjugationInvariance.lean:10-11`). This is harmless.
7. `sec_of_dm` recovers SiegelEisensteinContinuation from DM, and DM is itself built from SiegelEisensteinContinuation (`DMH:24-27`; `LTD/RealDataWeightVectorFamily.lean:20`). This is circular-looking but harmless, since the root supplies SEC as a closed theorem (SWRANGE §2.3).

## 5. Coverage

**Read:**
- PROTOCOL, NODE-LIVEPATH, NODE-MULTEQ, NODE-DETSIG, NODE-SWRANGE;
- `LTD/`: TwistedLocalMultiplicityEq.lean (all), TwistedMultiplicityOne.lean (all), UnitaryThetaCorrespondenceOfHyp.lean (all), RealDataWeightVectorFamilyCore.lean:12-46, RealDataWeightVectorFamily.lean (all), TwistedScalarConjugationInvariance.lean (all), HeckeFormOfDoubling.lean:10-27, GlobalFormOfSiegelWeil.lean:12-24, GlobalFormFrameLattice.lean (all);
- TEX (all); RSH:1-80; TFX (all); HTV (all); ETM (all); EPT:270-300; DSC:150-190 (and the def/theorem outline); `Given` (RLK:20-45); DefsWt.lean:147-153;
- the statement files LocalPseudoCoefficientExistenceUnitaryGroup, FinsumDiscreteSeriesCharacterEqWeylCharacter, CompactRealPlaceTorusClassesSignVectors, ExistsTypeVectorOfGoodLevelRepresentation;
- `IsTestFin` (`…/ExistsAuxiliaryPlaceNotMemFinset.lean:431-456`);
- `TPS/`: ExistsBaseLatticeOfPrime.lean:1-83, HermWCellLastMulMulVecEqOfInWb.lean (all), TwistedBundle.lean (all), ExBLIsLinkedPrmR.lean (all), ExBLIsLinkedPrmRStatement:18-30, BwitExistsStatement (theorem), BwitExists.lean:36-80, ExistsSelectionPairLocalLanglands.lean:69-88 (plus greps 40-47), Wire4F.lean:26-85, IndefiniteRealisationChoice.lean:36-52, TieTwRecOf.lean:20-60, CountsIrreducibilityConstants.lean:73-80;
- StableIffCarrierEq.lean:87-91; TwArgs.lean:30-50; ExistsSelectedRealization.lean:189-233; CPI:150-169; DMH (all); GFN:35-161; IntegrandSZero.lean:98-126.

**Greps run:**
- `def MultEq\b|theorem multEq_of_sides\b|namespace GlobalTheory.CuspMult\b|structure Given\b`; `multEq_of_sides`;
- `def (LocalPC|GapG|dsChar|SpecTraceX|Separation|EllTraceX|EllipticPartX|IsPCG|SpecFin|IsTestDataX|IsTestArchGX)`; `theorem …(localPseudoCoefficientExistence_unitaryGroup|trace_separation_of_iwahori_trace|exists_typeVector_of_good_level_representation|cuspidal_spectrum_finiteness_of_decay_harishChandra|finsum_discreteSeriesCharacter_eq_weylCharacter|…)`;
- `def (ellKernel|PPol|RopG|termOrb|mCuspDS)|ellipticSideDirect|ellipticT|SpecX`; `theorem odd_r`;
- `structure BundleWitness|intersectionNumber_baseChange\s*:|def realPackageOfRealInput|structure RealPackage`; `(structure|def|abbrev) Holds\b`; `TwistedBundle\b`; `BundleWitness`;
- `geometric_parameter_uniform_alt`; `intersectionNumber_baseChange :=` (under ThetaPairLifts); `exBL_isLinked_prmR_alt`; `exists_selected_realization_alt`; `exists_selection_pair_local_langlands_alt`; `selection_group_ambient_tie`; `column_params_instance_data`; `twArgs_exists`;
- `def AllRealisationsPrimitive|def PrimitivityBundleCondition|def SlotPrimitivityCondition`; `IndefiniteRealisationChoice'`; `classSel`;
- `real_data_weight_vector_family_alt`; `conjugate_baseLevel_of_howeUnramifiedCorrespondence`; `globalFormAt_frameLat_of_siegelWeil`; `globalFormAt_frameLat_nc`; `def GlobalForm\b`.

**Not opened:**
- proof bodies of `localPC_holds`, `SpecX.main`, `ellipticT`, `nonFieldT`, `parabolicT`, `trace_separation_of_iwahori_trace`/`exponentsSeparate`, `hasTypeVec_of_goodRep`, `dsChar_finsum_eq_glChar`;
- `reFace_zero_part_conventions_chosen_again`;
- the chain from MemberE to `t.r.intersectionNumber_baseChange`;
- `linkedAt_hPA_prmR` and the choice of `selB`;
- `doubling_zeta_value_at_eisenstein_holomorphic_point`; `sec_of_dm`.
