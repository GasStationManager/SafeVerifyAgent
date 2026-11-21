# NODE-LOOSE: five loose ends of the slope-chain write-up

Paths are relative to `.../scratchpad/art/lean/src`. Nothing was compiled. "The Lean says" means I read the cited lines.
Abbreviations:
- `SLP` = `Formalism/SharpRestriction/AdmissibleParameterJoins/SumLogPrimeFactorsLe.lean`
- `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`
- `TDN` = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- `SRI` = `Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/SlopeRamifiedInducedPrimeField.lean`

| item | verdict |
|---|---|
| L1 rescaling identity | **closed**: proved from `NprimeDef`. The slack is floor rounding, two-sided. |
| L2 factor 2 | **closed** at the arithmetic level. One normalisation is carried by a Published input. |
| L3 `HypLow2` | **closed**: an exact identity, proved for an orthogonally induced lattice. |
| L4 (i) eO | **closed**: eO = v_O(p) ≥ 2 is forced by `HidaSetting`. |
| L4 (ii) Pr | **closed**: proved and charged, not offset. |
| L4 (iii) index | **closed**: no off-by-one. |
| L5 `BuRational` | **closed**: the same B_u and bases in all three clauses. Proved in `block_eq`. |

No defect was found.

## L1. μ(N_u) = μ(NuLat_u) + Σ_w sz(w, sg) ± C·X″

**Who supplies `LinkMu`.**
- Every theorem in the tree with conclusion `LinkMu` reduces to `J.linkMu` (`SLP:728`). I found them by grep:
  - `SLP:729` and `SLP:776` (`linkMu_of_linkDIV`, used at `Development/.../CharacterBoxes/DesWin.lean:31`);
  - `.../LinkedMeasures/SlopeId.lean:46-53` (`linkMu_of_sizes` and `linkMu_of_full`, used in `FinalAll.lean:40`, `RemainingBoundFinal.lean:29` and `BrestFinalAll.lean:52`).
- I did not walk the live path down from `shape_closed_link_n_of_green`. Every supplier I found is the same theorem.

**Proof chain.** `linkMu` → `nprimeMuR_at` (`:694`) → `nprimeMu_at` (`:448`) → `round_le` (`:401`) → `mu_diff` (`:380`) → `mu_frac` (`:73`) → `mu_smul_ideal` (`:30-71`).
- `mu_smul_ideal` is the standard fact. It uses `covol_eq_relIndex_mul_covol` and `twist_index` ([M : 𝔟M] = N𝔟^{rk}), which gives
  μ(𝔟·M) = μ(M) − 2·log N𝔟/n.
- `log_absNorm_Iu` (`:358`) then gives the **exact** identity
  μ(N_u) − μ(NuLat_u) = Σ_w 2·lw·⌊e_w·sg(u,w)⌋.

**The slack.**
- sz = 2·lw·e·sg has no floor. So the only error is |⌊e·sg⌋ − e·sg| ≤ 1 at each w with sg ≠ 0 (`round_le`).
- The ramification index e is *inside* the floor and costs nothing extra.
- `sg_eq_zero` (`:431`, from `ZeroAbove`) restricts the support to primes ≤ X″, together with T, g₀, g₁, d and the primes dividing DGam.
- Chebyshev (Σ_{p≤N} log p ≤ N log 4) then gives the bound 2(X″·log 4 + log T + log g₀g₁ + log d + log DGam) ≤ C·X″.

**Direction.** The bound is an absolute value, so the lower bound the chain needs is included. The C·X″ reappears as c·X″ in Lo5, which NODE-ACCOUNT rates ≪ budget.

## L2. The factor 2 in the covolume main term

There is one conversion, and it is definitional.
- `degW_eq` (`Development/.../Foundations/IsProbabilityMeasureMuPart.lean:826`, `rfl`): **degW = rank·μ/2**. Here μ = `slope_sq` = `muDef` (`:32`), the same μ = 2·slope + const as the chain.
- `flatDegVal` (`.../Foundations/ExistsFlatSecRankZero.lean:751`): a flat section has deg = (p−q)/2·logΩ + q(log d − lrd).
  - `deg` = `lineDeg` (`:514`). By `sum_log_eq` (`:516`), lineDeg = −(1/[F:ℚ])·(Σ_w log c_w + Σ_{σ:F→ℂ} log c_σ). That is an average over **all complex embeddings**.
  - Check on a rank-one lattice: μ(𝒪s) = −(2/n)·Σ_σ log|s|_σ = 2·lineDeg. This is consistent.
- `twice_twist_ge` (`Development/.../DivisorProofs/FlatBoundOfAnchor.lean:76`) has the conclusion −mT − C·E ≤ **2**·(Σ_τ w_τ·c1_τ − …).
  - c1_τ ≈ −(p−q)/2·logΩ, from `hc1`.
  - So the μ-shift is 2·Σ w(−(p−q)/2)logΩ = −Σ_τ(p−q)·w_τ·logΩ = −mainT.
  - It is used in `flat_at_of_split_covering` (`.../HodgeBundleWeights/FlatAtOfSplitCovering.lean:28-90`), together with `degW_eq`, to give `FlatAt` (`CXC:135`).
- mainT = Σ_ρ(p_j−q_j)·w_{jρ}·logΩ = l3m (`ZscOfNum.lean:64-66`). By `show` (`AnchorBoundStatement.lean:112-117`), w_{jρ} = (D.hc t).e_i, the HC weight.
  - It is indexed by τ ∈ Psi (one embedding per conjugate pair, i.e. per real place of the totally real subfield), not per complex embedding.
- `LowAt` (`CXC:96`) is muCore ≥ −mainT, in μ units. `L3` compares lcv/D with l3 = mainT + C·l3u, and RecAt (`CXC:57`) gives lcv/D ≤ −μ.
- **So the units are μ throughout.** That is what ACCOUNT's k·w·logΩ cancellation against hK's nν·logΩ needs.

**Residual.** The statement that the *degree of the twisted cusp-form lattice* shifts by rank·Σ w·c1 is part of the Published input `flatLine_thetaRoot_twist_twistingSection` (`hP.p5`, AbelianDeRham; `.../FlatLineThetaRootTwistTwistingSectionStatement.lean:14`). The compatibility between lineDeg and degW sits inside that premise. The arithmetic around it is consistent.

## L3. `HypLow2`: μ(Mram) = μ(M) − f·log(T−1)/(T−2)

**What the objects are.**
- M = (fm u).lat 0.
- Mram = M ∩ ramSub (`DataForms.lean:241-245`). `ramified_sub_eq_inf_norm_ker` (`SRI:325`) identifies ramSub with ⋂_v ker(Nm_v). Here Nm_v is the norm (trace) operator of the diamond group G = ∏_{v∈vT}(ℤ/T)^×, with f factors, each of order T−1. So Mram is the part of M that is primitive at T.
- MuH (the N_u-side copy, `LocalQuadraticParts.lean:445`) has the same μ by the isometry nuIn (`ram_slopes`, `LocalRingCardinality/Lemmas.lean:59`).

**Why the index is exact.**
- `slope_formula_of_slice` (`SRI:341`) builds an orthogonal induced decomposition M = ⊕_{g∈G} Wh. Its inputs are `horth` and `hLc`, which come from `metric_disjoint_support_orthogonal` and `diamond_isometry_at_infinity`; I did not read those bodies.
- On this decomposition Mram = Wh ⊗ (the sum-zero lattice). That lattice has Gram matrix ⊗_i(I+J) on (T−2)-blocks (`szGram`, `Columns/SliceIntegralDeltaNeBot.lean:40-46`), and det(I+J) = T−1.
- `slope_ramified_induced` (`SRI:81`) gives μ(Mram) = μ(M) − log det(szGram)/rk.
- `log_det_szGram_div` (`:684`) gives f·log(T−1)/(T−2).
- The rank clause du = ((T−2)/(T−1))^f·duS matches.

**Verdict.** This is an equality, not a bound (`adm26` clause 2, `LocalQuadraticParts.lean:621-626`). It is proved via `division_rank_slopes_of_lines` (`LinkMin.lean:495`) and `slopeLine_tied`. The chain needs only "≥".

## L4. Non-degeneracy

**(i) eO.**
- `Sys.eO_spec`: p ~ vp^{eO} (`FGS:272`). The live system is `Sys.mk (D.gat u w hg) …` (`SysAt`, `WJS:178-183`), with D.gat = `gatOfLevelP … hS` (`GatIs`, `StdSubAtOfRing.lean:57-64`).
- `HidaSetting` (`UnramifiedQuadraticSetting.lean:12-33`) contains `w_sq`: w² = p in O. Also j : W → O is finite and injective (by `ι_comp` and `frac_alt`), and p is a uniformiser of W.
- *Proof (I infer, standard):* units contract in an integral extension of an integrally closed W, so p is not a unit in O. Hence eO = v_O(p) = 2·v_O(w) ≥ 2, and eO = 2 in the unramified-quadratic case.
- The family valuation `vUnit` = addVal p (`IsResidueClassZero.lean:412-416`) is the same eO.
- So the eO = 0 branch (`low_term_bound_of_eO_eq_zero_of_aux0`) is dead on the live path.

**(ii) `NumCmp`.**
- Supplier: `numCmpF_fixed` (`PlaneCountTheoremWithConstants.lean:1828`) → `numeric_comparison_of_constants` (`GrowthBounds/ProofLW.lean:207`, proved).
- The Pr clause is `price_bound_large_primes` (`MV/PriceBoundLargePrimes.lean:117`). It uses r = 1 at large p (`LatTied`).
- The term n′·r·j(t+1)/2 is **not offset**. It is charged in the family price:
  Pr_fam = Σ_{non-V tops}(fill − b) + Pr1·nP·(w″ + η + cG + Nm), with j(t+1)/2 ≤ Nm = N(m) (`ne_Nm`, `:104`; `IsResidueClassZero.lean:262-268`).
- Pr enters only through max(gU − Pr, g0⁺). So a large Pr only weakens the Hecke branch, and x^{403} ≪ a = x·e^{x^ε}.

**(iii) Index.**
- `PI j` (`FGS:417`) uses ν_{j+1}.
- `EntB j` and `PlaceB j` (`MV/PlaceB.lean:14-28`) use gv/g0v at **j+1**, i.e. gB/gA/cap at j+1.
- So do `Conclusion2` (`FGS:650`) and `main_ind`'s h1/h2. At step j, every number refers to the target level j+1.

## L5. `BuRational`

**Statement** (`RhoDetPrimeEqMuTildeMulChiPow.lean:364`):

  Bu_u(jN φ, jEE x) = embLL(Bk_u φ x),

where Bk_u : N_u.V →ₗ[K] Dual_K(RR.V) (`DataArith.lean` DivData). The pairing is bilinear, not sesquilinear, because sEE is conjugate-linear (`→ₗ⋆`).

**Proofs.**
- It is proved by `buRational_of` (`.../RationalColumns/BuRationalOf.lean:25`).
- `block_eq` (`TDN:1245`) combines it with `BesselId` (Bu = a·besS(Uφ, VF)) and proves
  [besS(U oM_j, V oE_k)] = (bE→oE)ᵀ·[Bk_u]^{(Nu u).b → RR.dualB}_{embLL}·a⁻¹(bN→oM).
- `blockReal_at_of` (`TDN:1283`) takes v = mk(embLL), with ε = id or conj, so that this is the Ball top block of `MatK_at` (`TDN:807`).

**Same object in all three clauses.** `FrameReal_at` (`TDN:519`) states `LatGeom` with exactly D.div.Bk, (Nu u).b, (Nu u).X, RR.dualB, RR.dualX and RR.dualL. Inside it:
- the integrality clause (map ≤ cc) is `OneMapIntoCC`;
- the height clause is htMap((Nu u).b, X, dualB, dualX, Bk) ≤ h;
- the frame block uses toMatrix (Nu u).b dualB (Bk u) (`frameReal_at_of`, `TDN:679`).

**Note (not a misfit).** The frame's Y and Y′ are change-of-basis matrices to Petersson-orthonormal bases of Mu u and EE. They are not the HLat frames X. `LatGeom` asks only that they be invertible, so the frame enters only through its ℂ-linear structure and its Gram bounds.

## Coverage

Read:
- `SLP:28-75, 352-494, 586-800`; `GTI:60-80, 145-165`; `SlopeId.lean` (all); `DesWin.lean:20-45`;
- `FGS:20-90, 262-300, 395-425, 715-775`; `MV/PlaceB.lean` (all); `ProofLW.lean` (all); `PriceBoundLargePrimes.lean:1-140`;
- `IsResidueClassZero.lean:240-268, 410-440`; `WJS:150-200, 360-375`; `AdmissibleEntriesOfKernelLaw.lean:1-100`;
- `UnramifiedQuadraticSetting.lean:10-45`; `DataG.lean:150-185`; `StdSubAtOfRing.lean:50-90`;
- `ClaimGaFree.lean:60-90`; `DataDIVDefs.lean:1-30`; `LocalQuadraticParts.lean:600-640`; `LinkMin.lean:440-560`; `Lemmas.lean:40-80`;
- `DataForms.lean:225-250`; `SRI:30-120, 279-362`; `SlopeLineRamifiedFormula.lean`; `SlopeFormulaOfCharacterFinite.lean`; `RamifiedLatticePropsOfModel.lean:1-40`;
- `SliceIntegralDeltaNeBot.lean:40-50, 684-688`; `CXC:15-160`; `ExistsFlatSecRankZero.lean:700-760`;
- `IsProbabilityMeasureMuPart.lean:20-40, 800-826`; `FlatBoundOfAnchor.lean` (both files); `FlatAtOfSplitCovering.lean:20-140`;
- `ZscOfNum.lean:60-68`; `AnchorBoundStatement.lean:95-120`;
- `RhoDetPrimeEqMuTildeMulChiPow.lean:340-380`; `BuRationalOf.lean` (all); `DataArith.lean` DivData;
- `FrameTraceRatioFinEquiv.lean:60-101, 197-222`; `QuadraticLogDerivCongr.lean:180-200`; `TDN:519-620, 679-880, 1085-1135, 1180-1400`.

Not opened:
- the bodies of `metric_disjoint_support_orthogonal`, `diamond_isometry_at_infinity`, `induced_of_slice` and `T2.kron_mu`;
- the Published `flatLine_thetaRoot…` premise;
- the live path from `shape_closed_link_n_of_green` down to the `LinkMu` suppliers.
