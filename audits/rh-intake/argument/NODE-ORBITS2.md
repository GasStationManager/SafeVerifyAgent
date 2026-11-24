# NODE-ORBITS2: the orbit decomposition of K0(u,u′), the non-main families, and their uniformity over word pairs

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own computation or inference. [NODE] means taken from that node and not re-read. Nothing from the tree was compiled or run. My one script is `.../scratchpad/orbits2/vand_ratio.py`, run with `python3 -I`, standard library only.

Abbreviations:
- `PB` = `Formalism/HermitianCurvature/StatementPB.lean`
- `RC` = `Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsConc.lean`; `RO` = `…/CokernelGLCounts/RowsOther.lean`
- `CLO/` = `Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/`; `FST/` = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/`; `RPC/` = `…/CokernelGLCounts/RankPointCounts/`
- `LSF` = `FST/LinkSFinalP.lean`; `TSO` = `FST/ThmSOwn.lean`; `SHO` = `FST/RootLatticeThresholds/SzHypOf.lean`
- `CP` = `Formalism/SharpRestriction/CuspSpanNormBounds/CntPartners.lean`; `TCI` = `Formalism/SharpRestriction/CuspSpanNormBounds/ThresholdCubicInequalitySignPattern.lean`
- `DWP` = `CLO/GaugeLatticeShifts/DistinctWordsDistinctParameters.lean`; `KOD` = `RPC/KappaOffDiagonal.lean`
- `FPE` = `Formalism/SharpRestriction/CuspSpanNormBounds/BruhatCellsKronecker/FamilyPacketOfEquivalentStatement.lean`; `CSB` = `Formalism/FlagUnipotentLattices/CardSubmodulesAndLinearEquivBounds.lean`
- `SZ` = `Formalism/HermitianCurvature/StatementSz.lean`; `SJ` = `Formalism/HermitianCurvature/StatementJ.lean`
- `FM/` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`

## 0. Verdict

**No ESCALATE.** Every non-main bound is pointwise in (u, u′), and the Lean's statements carry the pair-dependence explicitly. The content bodies of several leaves remain unread (§6).

1. **What a word is.** The Lean says (`Formalism/SharpRestriction/CuspSpanNormBounds/DataS.lean:19-31`):
   - a word is an injective letter string u ∈ {0,1}^{k−2};
   - all words share one discrete series σ, since `hcW_v`: (hcW u τ).v = (hc τ).v;
   - all words share one isotropic flag e (`CLO/TermOp.lean:117-118`, FrameTie);
   - a word changes the **U(W)-type** at every real place: u_{l+1} = v_l − ½ − Del·[letter_l], inside gaps v_l − v_{l+1} = 4·Del;
   - a word also changes the anisotropic Bessel vector z_u, with h(z_u, z_u) = −T_u for the type prime T_u. Every T_u ≡ 1 mod (g₀g₁)² (`TCI:222-224`), so at the level primes all words look the same.
2. **Why the cross term is never above random.**
   - The identity orbit and every degenerate orbit (G = 0) are **exactly 0** for u ≠ u′. This is Schur's lemma: their stabiliser at ∞ contains a full U(k), and the operator-valued orbital integral is a U(k)-intertwiner between the inequivalent types π_u′ and π_u (§2.2).
   - Every surviving orbit has G ≠ 0. Its total is bounded by the Bessel/Schur-orthogonality inequality for σ, which does not see which words are involved.
   - So words that differ in one letter are not more coherent than random: the only coherent term, the identity, is killed by the one-letter change of highest weight. The bound is not a cancellation; it is an upper bound.
3. **The diagonal is weak on purpose.**
   - The main-term precision 1 + δ (δ ≤ b⁻⁷) needs a letter l with de(l) ≠ de′(l) (`SZ:592-611`, `SJ:418-427`). For u = u′ no such letter exists.
   - The diagonal therefore uses a crude route with constant Γ = e^{CGam·m⁵ f log b}.
   - This is enough, because d_u ≤ C₀·D*/Γ² (`SZ:105-106`), so ‖K0(u,u) − 1‖² ≤ Γ·d_u²/D* ≤ C₀·d_u/Γ (§4).
4. **Uniformity.** The pair enters only through four routes:
   - (i) the normalisation dd = d_u·d_u′/D*;
   - (ii) the ratio bounds T_u/T_u′ ≤ A and Weyl-dimension ratio ≤ A^k, with one family constant A = e^{7/4}·C₀ (`Sizes3b`, `TCI:226-236`; `FST/RootLatticeThresholds/SzHypFam.lean:67, 78-92`);
   - (iii) the congruence and primality conditions `Stand`, which hold for all pairs by construction (`TCI:188-224`);
   - (iv) the first differing letter l, which enters only the main-term δ, through a statement quantified over all (de, de′, l) (`SizesMain`).

   My check of (ii): the extremal pair (first half 0 / second half 1 against the reverse) has log(vand ratio)/k → 0.34. That is far below log A ≥ 1.75 (§3).
5. **Correction to NODE-THMS §1.** The diagonal constant in `DiagRow` is (D.mem u).A.GamP = e^{CGam·m⁵ f log b} = Γ itself (`SHO` hΓ, read in `sizesAt_of`). It is not the gamB = e^{CB·m⁵ f log b} of RowMainEqC. The constraint max(CB, C4) + 1 ≤ CGam (`RC:102`) makes the inner constant smaller than Γ.

## 1. Statement: the orbit decomposition, as the Lean does it

**The groups.**
- G = U(V) over E/F, of signature (k + r, r + 1) at the f real places.
- The Bessel subgroup is R_u = U(W_u) ⋉ N, where N is the unipotent radical of the **common** isotropic flag e and W_u = ⟨e, e′, z_u⟩^⊥ is definite of rank k [PAIRB].
- The double unfolding of ⟨P_u T, P_u′ T′⟩ runs over R_u(F)\G(F)/R_u′(F), refined by lattice classes. A **term** t (`GTerm`, `CLO/TermOp.lean:76-91`) consists of:
  - a row lattice Λ ∈ what₂(u) and a column lattice Λ′ ∈ what₂(u′);
  - a class of (x ∈ G(𝔸), γ ∈ U(V)(E)) with γΛ′ = Λ and γ(u′-flag) admissible (`PD`, `CLO/TermDef.lean:142-144`), modulo N_Λ(F) × N_Λ′(F′) (`GRel`, `TermOp.lean:81-82`).

  So the "double cosets" are those of the **arithmetic** Bessel unipotent groups N_Λ on both sides (`NLam`). The compact parts are not divided out.
- The term operator is the archimedean orbital integral OO_t = ∫_{Ω_t} rk1(W_u(x), W_u′(γ⁻¹x)) dμ∞ (`TermOp.lean:28-30, 149-151`), times level factors.

**The invariant.** G(t) = Gval(F, γF′) = |D_{r+1}|² − TT′·|D_r|², computed from the leading minors of the (r+1)×(r+1) relative-position matrix Ẑ_{ab} = h(γf′_b, f_a) [THMB §1; `TermDef.lean:32`].

**The classification** (`CLO/FourParts.lean:152-168`; abstract version `PB:45-53`):

| class | Lean definition | meaning | bound for u ≠ u′ | where |
|---|---|---|---|---|
| identity | relevant ∧ `InSF`: γF′ ≡ F mod the flag (`FourParts.lean:17-21`) | γ carries the u′-Bessel datum onto the u-datum | **= 0** (`IdZero`) | `PB:99`; supplier `IdCellOffC_outright` (`ClosedVolumeStatements/FullExistsTiedHolds.lean:34`) |
| degenerate | relevant ∧ G = 0 ∧ ¬InS | singular relative position | **each term = 0** (`KppTermZero`) | `RO:17`; `KppOffC` `RC:67-71`; supplier `KppOffC_holds` (`FullExistsTiedHolds.lean:36-41`) |
| generic | G ≠ 0 ∧ generic | open cells, Lattice saturated at the level | main term | — |
| non-generic | G ≠ 0 ∧ ¬generic | lattice not saturated along the frame [PAIRB] | RowNG | — |

Then K = K0 + part(deg) (`PB:120-123`), K0 = part(id) + part(gen) + part(ng) (`PB:61`), and for u ≠ u′ we have K0 = part(gen) + part(ng).

**The norm expansion.** ‖K0‖² ≤ Pg·Γ₁·Σ_i‖vecPart_i‖² (`NormSqBoundOfEqualIota`, `PB:133-137`), with Pg = ∏_v(1 + 3/q_v) (`PgC`, `RC:41`). Expanding the right side gives a sum over **same-row pairs** (t, t′), split by corank s₀ (`PB:65-79`):

| pair family | Lean | bound (× dd) | constant |
|---|---|---|---|
| corank ≥ 2, both G ≠ 0 | `RowBig` (`PB:101`) | e^{−(1/3)kf log k} | `epsL`, `RC:45` |
| corank 1, generic, non-scalar | `RowNotScalar` (`PB:103`) | e^{−(1/3)kf log k} | `epsL` |
| corank 1, generic, scalar (main) | `RowMain` (`PB:107`) | (1+δ)·e1, δ ≤ b⁻⁷ | `PB:229-231` |
| corank 1, non-generic | `RowNG` (`PB:109`) | 2^{−(k−2r−5)}·e^{C4 m⁵ f log b} | `epsNG`, `RC:49-50` |

Inside the loops (`FPE:125-133, 381-389`), the corank-s pairs split further:
- `clsND s`: the β-datum is non-degenerate;
- `clsDeg s`: degenerate β;
- `clsOne`: generic, corank 1, non-scalar.

Each class gets a `RowBound`: Σ_{pairs} wP ≤ massRows(u)·dimπ_u·B (`FPE:109-111`), with:
- B_ND(s) = ndRow(s)·d_u′/D*;
- B_Deg(s) = degRow(s);
- B_One = oneB·d_u′/D* (`FPE:372-389`).

The abstract assembly is `PairBound` (`PB:220-238`): the four row bounds together with `SizeNumbers` give ‖K0‖² ≤ (1 + b⁻⁶)·dd.

## 2. Argument: each family as mathematics

### 2.1 Identity orbit (IdZero)
- The supplier is `IdCellOffC_holds idOffConjC_holds idOffLiftC_holds`.
- The step I read is `idOffIneq_of_lift` (`DWP:808-838`). If t is an identity term, the conjugate t.pt⁻¹·h·t.pt of every h in the compact U(W_u)(ℝ) at one place v acts on π_u′ as a U(k)-conjugate A*·M·A of M (`IdOffLift`, `DWP:801-806`).
- So the orbital integral intertwines π_u|_{U(k)} with π_u′ ∘ Ad(A).
- `tens_inequiv` / `hcType_inequiv` (`DWP:470-506`) is Schur's lemma for irreducible U(k)-types with distinct highest weights: the dominance relation goes both ways, so the weights are equal, which is a contradiction.
- Distinct highest weights is `uS_ne` (`DWP:727-745`): a differing letter l gives u_{l+1} differing by Del at **every** place τ.

### 2.2 Degenerate orbits (G = 0): KppOff
`kppTermZero_of_cut` (`KOD:93-108`) runs as follows.
1. `RelRepC`: a relevant term with G = 0 has a representative with Gval = 0 (`KOD:33-36`).
2. `CovRepC`: the orbital integral commutes with the pointwise stabiliser of X⁺(F) + X⁺(γF′) at ∞ (`KOD:38-48`).
3. `SchurNFC`: an operator P : π_u′ → π_u with that commutation is 0 when uS u τ ≠ uS u′ τ (`KOD:50-56`). It is proved as `schurNFC := schurNFC_of (schurCoreA_of schur_lemma_unitary_distinct_params) (geomB_of leviTens wfrSpan cplxNF)` (`RPC/SchurNFCOf.lean:34-36`).

The geometric content is `GeomB` (`RPC/SchurCoreA.lean:72-83`):
- when G = 0, for **every** M ∈ ∏_v U(k), the pointwise stabiliser contains an h that acts by M on π_u and by C·M·C* on π_u′;
- that is, the stabiliser contains a full U(k) conjugate of U(W_u).
- *(mine)* So G = 0 means that γW_u′ and W_u share the whole definite k-space, and Schur kills the term exactly as for the identity.

I did not open `cplxNF`, `leviTens` or `wfrSpan`, the linear-algebra proof that G = 0 forces this.

Diagonal version (`KppDiagC`, `RC:73-78`, from `kppDiagC_of_cut`, `RC:192-206`): ‖part(deg)‖² ≤ d_u·e^{−kf log k}, through `PairsDeg` (`RO:24-25`) and the Gelfand–Graev matrix bound. Its supplier `PairsDegCutC` (`RC:186-190`) was not opened.

### 2.3 Corank ≥ 2 and non-scalar pairs: LoopRowS
- **Statement** (`TSO:1015-1023`): for every aF, every family member and every pair (u, u′) with `Cnt.Hyp … u u′ … (aF ·)`, RowBig and RowNotScalar hold with ε = e^{−(1/3)kf log k}.
- **Supplier** `loop_rows_closed_gap` (`FM/LoopRowsOfLargeGapDiscreteSeries.lean:121-209`, read). It is glue around `loopRowBounds_along_family_largeGaps` (`FM/LoopRowBoundsAlongFamilyLargeGapsStatement.lean:13`) → `rows_along_family` (`FM/LoopRowBoundsAlongFamilyLargeGaps.lean:25-43`, read).
- That theorem has four inputs:
  - `rowCounts_uniform_constants_families` (inputs SiegelMassRatio and A);
  - `amplitude_bounds_uniform_large_gap_families` (inputs SiegelMassRatio, GapIn.Hyp, ThmBpDS, A, C1);
  - `CritLevelGap.along_family`, which consumes `Published.DiscreteSeriesUpqExists` and `Published.FormalDegreeCompactDual` (`FM/AlongFamilyOfMassRatio.lean:83`, grep line);
  - `admissible_family_satisfies_row_estimates`.

  Its per-pair inputs are `wordPairTermInjective`, `wordPairBetaLattice` (supplied by `beta_l_unique`) and `TermVolumeSmallCellBound` (supplied by `stabiliserCovolume_relevantTerm_le_heightPow`).
- **The constants** are C ≥ C₀(CT, A, C0, CGam, U): they depend on the family constants and on A, never on the pair.

**The shapes** (`CSB:694-760`, read):
- ndRow(s) = (2/g)^{(s−1)kf}·(kv)^{kf}·Ξ(s)·C^{kf}·H^{C(s+m)m²}·(Csf)^{6sf}·Γ.
  - Here Ξ(s) = `XiB D large₂ u C` is the relative count of corank-s cells. It depends on the row word u only, through NT(u) ≤ b^{Cmf}.
  - It is constrained by `XiHyp`: (kv)^{kf}Ξ(s) ≤ H^C·C^{skf}.
  - `NonDegSum` gives Σ_{s≥2} ndRow ≤ g^{−kf/2}.
- degRow(s) has (2/g)^{(s−2)kf} and the Siegel factor (C/k)^{kf}·e^{Cm⁶ f log b}. `DegSum` gives a sum ≤ e^{−kf log k/2}·Γ⁻².
- oneB = C^f·H^{Cm³}·Γ·e^{Cm⁶ f log b}·√((C·g^{−(2r+1)}k^{−r})^{kf}) (`FPE:374-377`). `SingleRowBound` gives ≤ e^{−kf log k}.
- The T-ratio of the pair enters `SmallTerm` (`CSB:731-737`) as √(T′/T) ≤ √A.

**Where the saving comes from** *(mine, consistent with [PAIRB])*: a corank-s Levi datum at the level primes g₀, g₁ costs g^{−(s−1)k} per place, through the χ₂-twisted sum over the congruence subgroup. That cost is the same for all words, because T_u ≡ 1 mod g² for every u.

### 2.4 Non-generic corank 1: RowNG
- **Statement** (`RC:86-90`). Its only pair hypothesis is `Stand D u u′` (`CP:25-31`): T_u and T_u′ are odd primes split in E, coprime to g₀g₁, with T_u ≡ T_u′ mod g₀g₁. `Stand_of` (`TCI:188-224`) proves it for **every** pair, from d9: every T_w ≡ 1 mod (g₀g₁)².
- **The mechanism** [PAIRB §2(3), THMB]. A local q^{−(k−2r−5)} saving comes from the rarity of non-saturated lattices, with a hermitian-quadric Gauss sum in the second type. It is paid against Theorem B's global sum e^{Cb m⁵ f log b}.
- Theorem B's constants are quantified before T, T′, u, u′, with T, T′ ≤ b^{Ch(2r+2)} [THMB §1]. Both u ≠ u′ (cut) and u = u′ (separating gap) are covered [THMB Level 1].
- So RowNG is uniform in the pair. I did not re-open its bodies in this pass.

### 2.5 The main term: RowMain, with its pair-dependent δ
- The off-diagonal RowMain((1+δ)e1) is produced inside `theoremS_rec` from `SizesAt … u u′` (`FST/TheoremSRecursion.lean:113-124`, read).
- The pair-dependent clause is `J.SzHyp` (`SJ:418-427`). It requires:
  - words de, de′;
  - a letter l with 1 ≤ l, l + 2 ≤ k and **de(l) ≠ de′(l)**;
  - T, T′ ≥ b^{cT·m};
  - the column counts and ChoiceOfT (d_w ≍ D*/Γ²) for both words;
  - Th = (max thrSet)^{−1/f}.
- `SizesToRecursion` (`SJ:429-437`) and `SizesMain` (`SZ:592-611`) state, with k0 depending only on constants, that under SzHyp:
  - Th ≥ k^{cExp};
  - C·(r+1)·(C/Th)^f ≤ b⁻⁷.

  This is the δ ≤ b⁻⁷ that `PairBound` needs (`PB:229`).
- **The mechanism** (`SZ:195-226, 545-562`; `FM`-side `beta_bound`, `Formalism/HermitianCurvature/HermitianCurvatureProofs/SixteenMulLeTwoPow.lean:79-103`, read):
  - thrSet is built from sup_Y of g^m·be(Y) over the **cut window at l**, 5/2 ≤ v_l + Y ≤ Del/2.
  - Here be = ka^{−(m−1)}·√|P(Y)P(Y+1)/q(Y)|, with P(Y) = ∏_s(Y + λ_s) and q(Y) = −TT′·∏_i(Y + ½ + u_i)(Y + ½ + u′_i).
  - `BetaOnCut` gives g^m·be ≤ 160·tv·√k·√((v_l + Y)/Del) on that window.
  - *(mine)* The reason: at index l+1 one word has the factor y = v_l + Y and the other has y − Del. So the ratio carries (y(y+1))/(y·(Del − y)) ≈ y/Del, whose square root is the √(y/Del) of the Lean. For two equal letters this factor is ≈ 1 or ≈ y²/Del², so the window gives no saving. The precision of the main term is therefore **made at the first letter where the words differ**, and its size, √(y/Del), is the same whichever letter that is.
  - `sizes_to_recursion` (`…/SupremumAIsMajorant.lean:323`) and `size_bounds_conclusion` (`SixteenMulLeTwoPow.lean:335-337`, read: an assembly of nine named lemmas) are proved. The bodies of `BetaOnCut`'s supplier `beta_bound_on_boundary`, `final_smallness` and `theta_power_bound` are unread.
- The main inequality itself is the mass identity × `EnergyAbs` [PAIRB §2(1); COUNTS]: ∫HS²(OO) ≤ 1/d_σ for **any** pair of Bessel vectors. *(mine)* That is why it cannot exceed random for close words.

## 3. Uniformity, family by family, at the worst pair

| family | depends on the pair through | worst pair | check by the Lean's inequality |
|---|---|---|---|
| identity | highest weights uS u τ vs uS u′ τ | one-letter neighbours | = 0 whenever any letter differs (`uS_ne`). Uniform |
| degenerate G = 0 | same | one-letter neighbours | = 0 (`kppTermZero_of_cut`). Uniform |
| corank ≥ 2 ND | Ξ(s) via u; d_u′/D*; A through C₀(A) | maximal Weyl-ratio pair | *(mine)* max log vand(u′)/vand(u) ≈ 0.34·k (k = 800), against A^k with log A ≥ 1.75. Absorbed into C^{kf}, which is beaten by (2/g)^{kf} with g ≥ (kb)⁸ |
| degenerate β (in loops) | same | same | (C/k)^{kf} Siegel factor; `DegSum` holds for all Params/XiHyp |
| non-scalar corank 1 | √(T′/T) ≤ √A (`SmallTerm`) | extreme T-ratio | T/T′ ∈ [e⁻¹, e] (`TWords`, `SZ:579-590`) |
| non-generic | T, T′ inside Theorem B | T, T′ at b^{cT m} or b^{Ch m} | constants fixed before T, T′; killed by 2^{−(k−2r−5)} since k ≥ 8Cn m⁵ f log b |
| main term δ | first differing letter l; T, T′ | l at either end (1 or k−2) | `SizesMain` quantifies over all l with 1 ≤ l, l+2 ≤ k; `exists_continuousLinearMap_tens_update` (`SHO:148-166`) shows the first differing letter always satisfies this |
| main term constant | none (Bessel inequality) | — | ≤ 1/d_σ for any pair of unit Bessel vectors |

**Word-count issue.**
- |W| can be as large as 2^{k−2}. None of the bounds above is an average, and none involves |W|.
- Each is a statement ∀ u u′ with constants chosen before D (`LSF:27-31`: C₄, CA, C, k0, Cn, C′₀, Cl₀ are quantified before D and the words).
- The pair hypotheses are discharged ∀ u u′ by:
  - `count_hypotheses_of_sizes` (`TCI:230-236`);
  - `Stand_of`;
  - `sizesAt_of` / `thrRow_holds` (`SHO:178-286`; `FST/RootLatticeThresholds/ThresholdLevels.lean:14-23`);
  - `hA_of_ranks` (`SzHypFam.lean:119-124`).

**Script** `vand_ratio.py` *(mine)*. It is the model of `Sz.Cfg.u` (`SZ:201-202`) with Del = 50. Taking (max − min) of log vand over all words, divided by k, gives 0.112, 0.137, 0.162, 0.182 and 0.197 at k = 6, 8, 10, 12 and 14. For the half/half extremal pair it gives 0.286, 0.326 and 0.340 at k = 50, 200 and 800. This is consistent with an A^k bound, A = e^{0.35}. The Lean uses A ≥ e^{1.75}.

## 4. The diagonal clause

- **Lean.** `DiagC` (`RC:98-103`) is assembled by `diagC_of_rows` (`RC:215-249`, read). It reuses `PairBoundAbstract` with:
  - IdOne: the identity part is exactly 1 (`RO:48`; `idOne_of_cell`, `RC:277-283`);
  - A = gamB = e^{CB m⁵ f log b}, from RowMainEqC (`RC:92-96`);
  - ε = epsL and ε′ = epsNG, from the same row suppliers applied to (u, u).
- **Numerics.** `DiagNumC` (`RC:208-213`) says (√(Pg(gamB + 2ε)) + √(Pg(ε + ε′)))² ≤ GamP, which with max(CB, C4) + 1 ≤ CGam is elementary.
- The live supplier of `DiagC` was not traced in this pass; NODE-THMS named `diagonal_positive_final` and `kernel_diagonal_positive`. I read the RowMainEqC route only at the level of its defining Props, `GenCutP` and `StepAnalyticGP` (`FST/RowsPos.lean:19-49`). It is a point sum through `PN.PointSumInput` with e^{CB m⁵ f log b}, i.e. Theorem B, not the SizesMain recursion.
- **Why it is weaker.** The precision 1+δ comes from the cut at a differing letter (§2.5), and SzHyp demands de(l) ≠ de′(l). For u = u′ there is no cut, so only the e^{O(m⁵ f log b)} route is available.
- **Why it suffices** *(mine)*.
  - ChoiceOfT (`SZ:105-106`) gives d_u ≤ C₀·D*/Γ² with Γ = GamP.
  - So ‖K0(u,u) − 1‖² ≤ Γ·d_u²/D* ≤ C₀·d_u/Γ, i.e. e₀ ≈ C₀/Γ = C₀·e^{−CGam m⁵ f x^ε}, astronomically below the x^{−C_H} that Bost needs.
  - The diagonal off-identity sum has true size about d_u²/D*, the random level. A loss of Γ against it is affordable precisely because d_u/D* ≈ Γ⁻².
  - Adding the degenerate part: ‖K(u,u) − 1‖ ≤ √(C₀d_u/Γ) + √(d_u·e^{−kf log k}).

## 5. Published inputs on this chain

| input | statement (read?) | literature | verdict |
|---|---|---|---|
| `Published.FormalDegreeCompactDual` (`Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/FormalDegreeCompactDualIff.lean:8-22`, read) | for a discrete series of U(p,q) with HC parameter λ, ‖w‖⁴/∫\|⟨w, σ(g)w⟩\|² = ∏_{a<b}\|λ_a − λ_b\|/∏_{a<b}(b − a), with Haar measure normalised through the compact dual | Harish-Chandra's formal-degree formula (Discrete series II), compact-dual normalisation (Hecht–Schmid) | match |
| `Published.DiscreteSeriesUpqExists` | name only (`FM/AlongFamilyOfMassRatio.lean:83`); body not read | Harish-Chandra existence | presumed match, not checked |
| SiegelMassRatio | in-tree `siegelMassRatio := siegelMassRatio_of_LI hermRepUnram liStat` (`Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SiegelMassRatioOfLI.lean:59`, grep line); `hermRepUnram` is in-tree (`FM/HermRepUnram.lean:7`) | Siegel / Gan–Hanke–Yu mass formula | in-tree here; [THMB §9.7] says sibling leaves import `PublishedTheorems.*`, not re-traced |

**Content with no published match** on the Theorem-S chain (all in-tree, all proved by named theorems):
- `SizesMain` / `SizesToRecursion`: the main-term precision δ ≤ b⁻⁷, uniform in k. Assembly read (`SixteenMulLeTwoPow.lean:115-135, 335-337`); the nine sub-lemmas unread.
- Theorem B rotated [THMB]: uniform in k through b.
- The Ξ(s) counts and `TermVolumeSmallCellBound`: unread.
- `GeomB` for G = 0: unread proof.

The **compression formula** (DecGap ← `germ_jet_zero` [FORMULAGAP]) and the rank-uniform count (`countingTheorem_of_volumeStep` [THMS §3]) are on the **counting** side, not on Theorem S. I did not read them in this pass. None of these is a Published field, so none exceeds a Published statement.

## 6. Children and updated status

| leaf | file:line | content | status |
|---|---|---|---|
| `Terms`, classes, K0, Row* | PB:15-111 | term system | definitions, read |
| `PairBound` / `PairBoundAbstract` | PB:170-238; GOB:525 [PAIRB] | assembly + numerics | proved, read [PAIRB] |
| GTerm, PD, Gval classes | `CLO/TermOp.lean:76-151`; `CLO/TermDef.lean:142-171`; `CLO/FourParts.lean:17-168` | double cosets of N_Λ × N_Λ′, refined by lattices | definitions, read |
| `uS_ne` (distinct words ⇒ distinct U(k)-types at every place) | DWP:727-745 | letter shifts u_{l+1} by Del | **proved, read** |
| `hcType_inequiv`, `tens_inequiv` | DWP:470-506 (read), 508ff (statement) | Schur for distinct highest weights | proved; first read |
| IdZero (`idOffIneq_of_lift`) | DWP:801-838 | identity orbit = 0 | proved, read; `idOffLiftC_holds`, `idOffConjC_holds` unread |
| KppOff (`kppTermZero_of_cut`, `schurNFC`) | KOD:33-110; `RPC/SchurNFCOf.lean:20-36`; `RPC/SchurCoreA.lean:16-83` | G = 0 orbits = 0 by Schur | proved; assembly read; `cplxNF`, `leviTens`, `wfrSpan`, `covariantRepZero_of_lemmaV` unread |
| KppDiag | RC:73-78, 186-206 | deg ≤ d_u e^{−kf log k} | proved from `PairsDegCutC`; supplier unread |
| LoopRowS supplier | `FM/LoopRowsOfLargeGapDiscreteSeries.lean:121-209`; `FM/LoopRowBoundsAlongFamilyLargeGaps.lean:25-43` | corank ≥ 2 / non-scalar ≤ e^{−kf log k/3}dd | proved; glue read; `rowCounts_uniform…`, `amplitude_bounds…`, `admissible_family…`, Ξ and `TermVolumeSmallCellBound` suppliers unread |
| ndRow / degRow / oneB and sums | CSB:694-760; FPE:372-389 | level saving, Siegel factor | shapes read; `NonDegSum`/`DegSum`/`SingleRowBound` proved [PAIRB], bodies unread |
| pair hypotheses (`Cnt.Hyp`, `Stand`, `Sizes3b`) | CP:25-48; TCI:188-236; SzHypFam.lean:67-124 | ratio ≤ A, congruences | definitions + discharges read; `family_level_ratio_bound` (vand ratio) unread, tested *(mine)* |
| RowNG | RC:86-90 | NG ≤ 2^{−(k−2r−5)}e^{C4m⁵fL}dd | proved [SLEAVES/PAIRB/THMB]; not re-read |
| RowMain off-diagonal δ: `SzHyp`, `SizesMain`, `SizesToRecursion` | SJ:418-437; SZ:195-226, 545-611; SHO:148-286 | δ ≤ b⁻⁷ from the cut at the first differing letter | statements read; `size_bounds_conclusion` assembly read; `beta_bound_on_boundary`, `final_smallness`, `theta_power_bound`, `sizes_to_recursion` unread |
| `thrRow_holds` | ThresholdLevels.lean:14-23 | Th exists for every pair | proved, read (positivity leaf unread) |
| NormBound / EnergyAbs | [PAIRB; COUNTS] | Bessel inequality | EnergyAbs body read [COUNTS]; mass identities unread |
| DiagC | RC:98-103, 208-249 | ‖K0(u,u) − 1‖² ≤ Γ d_u²/D* | assembly read; live supplier and RowMainEqP/DiagNumC suppliers unread |
| `OOLintSumC_holds`, `KExpansionC_holds` | `FullExistsTiedHolds.lean:28-32` (call lines); TheoremSConclusion.lean:83-93 | convergence / unfolding | proved by named theorems; bodies unread |
| carrierP | `FM/OffK0Closed.lean:663-670` | carrier side | proved, assembly read; leaves unread |
| Theorem B | [THMB] | singular orbital integrals | proved; leaves unread [THMB] |

## 7. Oddities

1. **The diagonal and off-diagonal main terms use different machinery** (Theorem B point sum vs the cut recursion). The off-diagonal precision is structurally unavailable for u = u′, because SzHyp needs a differing letter. This is coherent, but it means the near-tightness constant 1 + b⁻⁶ lives entirely in `SizesMain` plus `EnergyAbs`.
2. **Uniformity is bought by the word design.** The letters shift a single coordinate by Del, which is ≫ k, f, log b (`Hyp.hDel`: (k f log b)^{CDel} ≤ Del, `SZ:577`), inside gaps of 4·Del. So every pair of distinct words is "equally different" at its first differing letter. Close words are not a special case.
3. **NODE-THMS's "Γ_P = e^{C_B m⁵ f log b}" should read GamP = e^{CGam m⁵ f log b} = Γ** (§0.5).
4. `ThresholdAtPlaces` asks only for the existence of a greatest threshold, which is trivially finite. All the content is in `SizesMain`'s lower bound Th ≥ k^{cExp}.
5. I saw nothing false as literally read.

## 8. Coverage

Read in this pass:
- PROTOCOL; MAIN-ARGUMENT §0, §5.3, §7, §9.10; NODE-THMS (all), PAIRB (all), SLEAVES (all), THMB (all); NONVAN, FORMULAGAP, HIGHERRANK, ADMB2 (opening sections); TFLOOR (grep for T_u).
- Lean:
  - PB:1-260; RC:1-300; RO:1-80;
  - `CLO/TermOp.lean:20-175`; `CLO/TermDef.lean:1-230`; `CLO/FourParts.lean:1-170`; `DataS.lean:10-80`;
  - DWP:440-520, 720-898; KOD:1-125; `RPC/SchurNFCOf.lean`; `RPC/SchurCoreA.lean:1-100`; `FullExistsTiedHolds.lean:28-60`;
  - CP:1-120; TCI:150-300; LSF:1-140; TSO:660-676, 1010-1026;
  - `FM/LoopRowsOfLargeGapDiscreteSeries.lean:1-30, 121-209`; `FM/LoopRowBoundsAlongFamilyLargeGaps{,Statement}.lean`;
  - FPE:100-140, 370-400; CSB:690-765; `FST/RowsPos.lean:1-80`;
  - `FST/TheoremSConclusion.lean`; `FST/TheoremSClosedP.lean:20-130`; `FST/TheoremSRecursion.lean:100-130`;
  - SJ:330-470; SZ:105-106, 195-226, 545-611; SHO:34-57, 148-334; `ThresholdLevels.lean`; `SzHypFam.lean:20-130`;
  - `SixteenMulLeTwoPow.lean:1-135, 330-337`; `FM/OffK0Closed.lean:640-697`; `FormalDegreeCompactDualIff.lean`.
- Grep lines only: `AlongFamilyOfMassRatio.lean:83`, `SiegelMassRatioOfLI.lean:35, 59`, `HermRepUnram.lean:7`, `MassLand.lean:14`.

Not opened: the unread bodies listed in §6, `IdBlocks`/`IdCellOffCHoldsOfVol`, the RowNG chain (relied on [PAIRB/THMB]), and the live `DiagC` supplier.
