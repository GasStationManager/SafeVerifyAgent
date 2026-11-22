# NODE-TU: what T_u is, how −a_t·log T_u enters DIV, what pays for it, and Count5

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(mine)* = my own computation or inference. [NODE] = taken from that node, not re-read. Nothing was compiled or executed.

Abbreviations (new ones marked *):
- `MB` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`; `QSB` = `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`; `INP` = `Formalism/LocalToGlobal/Divisibility/Inputs.lean`
- `JL` = `Formalism/SharpRestriction/GlobalSchurBounds/JointsL.lean`; `STL` = `Formalism/SharpRestriction/GlobalSchurBounds/StandardLattice.lean`; `GAL` = `.../GlobalSchurBounds/GeneralLinearActions/GapAtLeast.lean`; `DK` = `Formalism/LocalRingCardinality/DataKernels.lean`
- *`RDP` = `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean` (the D7 record)
- *`FSN` = `Formalism/LocalToGlobal/Columns/FiniteSumNonzeroLargeDepth.lean` (the Bessel/branching functional)
- *`AHF` = `Formalism/LocalToGlobal/Columns/AbelianHostFieldConditions.lean`
- *`IPF` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/IpAtNonnegOfDatFramed.lean`; *`FB` = `Development/AbelianVarietyTheory/Definitions/Divisors/FactorBounds.lean`; *`EHN` = `.../DivisorProofs/ExistsHtNumsOfKerSideLastSide.lean`
- *`PFZ` = `Formalism/SharpRestriction/GlobalSchurBounds/ProductFirstZerothParts.lean`; *`AGP` = `Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean`; *`DGi` = `Formalism/SharpRestriction/AdmissibleParameterJoins/DIVfromGLi.lean`; *`WDS` = `Formalism/SharpRestriction/Divisibility/WeightDegreeSizes.lean`
- *`T3E` = `Formalism/SharpRestriction/GlobalSchurBounds/TheoremThreeOfExplicitAndCompact.lean`; *`FP5` = `.../GlobalRankLatticeProofs/FamilyPartFiveOfExplicitConstants.lean`; *`LMin` = `.../GlobalSchurBounds/LinkMin.lean`; *`LPk` = `.../GlobalSchurBounds/LinkPk.lean`; *`PHR` = `Formalism/SharpRestriction/ParamsHeightRankConstant.lean`

## 0. Verdict

**No ESCALATE on the three stated criteria.** T_u has a two-sided pin, the main term matches by hand, and Count5's supplier delivers the stated precision. **One item is flagged for a human reader (§4.1).** The whole archimedean saving −Σ_t a_t·log T rests on one family-level *statement*, `Conclusion6`. It asserts that the T-scaled last map is integral at the primes above T and also has archimedean norm² ≤ T^{−deg}. In the ledger nothing else pays for T, apart from two terms that are smaller by a factor m/k or B₀/(|TT|·a). So the ledger is monotone in T, and only the window T ≈ T* stops a larger T from proving ASK ≤ Main − (huge).

1. **T_u is a genuine rational prime, not a normalisation.** The Lean says:
   - `T : ℕ`, `T_prime : T.Prime` (DK:104-108).
   - f places v above T, each with residue field of size T: `card_vT = R.f`, `card_Fv v = T` (DK:112, 119).
   - an element π_T ∈ O_E with π_T·π̄_T = T (`piT_norm`, AHF:227; `T_prime`, AHF:224).
   - So T splits completely in F, and each place above T is a norm from E. It is the "type prime" of ADM11: the same `(D.mem u).A.T` appears in `TwistedColumnBoundAtT` (AGP:20-23) and in `sg_atT` (WDS:887-901).
2. **Its *size* is a formal-degree ratio, and it is pinned from both sides.**
   - The D7 record carries `T_win`: T* ≤ T ≤ (1 + 1/(fk))·T* (RDP:153-154).
   - T* = Xu·Γ^{−2/(fk)} and Xu = (D*/d*_u)^{1/(fk)} (DK:157, 159).
   - D* = vol(Y₀)·idxSig(g₀,g₁)·∏_ρ dsig(ρ), and d*_u = massI(k)·idxPi(g₀,g₁)·∏_ρ dimV(uCol_u(ρ)) (GAL:80-99).
   - So log T = (1/(fk))·log(target mass × level index × archimedean formal degrees ÷ the same for the source) − 2logΓ/(fk) + O(1/(fk)).
   - The defining identity is clause 1 of `TorusPairsWithVariant` (STL:533-540) and of `VandermondeCountExplicit` (T3E:158-174): D*Γ^{−2}/2 ≤ d*_u·(T^k − 1)^f ≤ e·D*Γ^{−2}.
   - *(mine)* (T^k − 1) is the index of the mirabolic in GL_k(F_T). So d*_u(T^k − 1)^f is the mass-formula dimension of the level-T source, and **T is chosen so that this source dimension matches the target D*/Γ²** (the Theorem-S window).
   - Upper bounds: log T ≤ logXu + 1 (T3E:171) and `TuSize`, log T ≤ CTu·m·L (PHR:180-182). The brief's reading is therefore half right: log T_u *is* a log formal-degree ratio per unit fk, but T acts as a real level prime.
3. **How −a_t·log T enters, as the Lean says.**
   - The Bessel/branching functional is `brAt t := (∏_τ t_τ^{−nBr(λ_τ, sg_τ)})·brStd` (FSN:137), with nBr = |λ| − |sg| (FSN:57).
   - `brC` takes t_τ = τ(π̄_T) (FSN:197-198). The evaluation points are the row points "tilded" by π_T (`tilQ`, FSN:204-205; `evzC`, FSN:212-213).
   - `periodFun_le` (IPF:26-35) uses |s(τ(π̄_T))|² = T (IPF:37-45). It proves |Ptil|² ≤ T^{−Σ nBr}·∏cBr²κ·‖ψ∘til‖²·‖F‖², which is the term `lastLog` (FB:84-87, IPF:82).
   - `LastSide` (FB:62-74) turns this into hPn ≤ −Σ_τ nτ·log T + …, with nτ = a_t − (Nn−k)/2 − D₀ at tops (INP:284-296). That gives hA = −Σ_t a_t·log T + error (INP:188-190). The term appears **once per top, not once per lift**.
   - In D5 the −a·log T of hu and of rhs cancel (INP:188-203). It survives in (L1) only through h(u) = the height of B_u (the `hTie` [DIVKEY]). So the saving is the archimedean norm of the last map and nothing else.
4. **Product formula.** Dividing by π̄_T^{nBr} is a scalar change. By itself it changes the archimedean side by −nBr·log T, and the side above T by exactly +nBr·log T. The Lean charges the T-adic side only:
   - m·EatT per place above T, as the source exponent sg = −m·EatT (`sg_atT`, WDS:887-901). This needs ETpi·log T ≤ C·B₀ (`WeightBudgetBound`, PFZ:323-328). Here ETpi = 2Σ_τ Wt + fN + |tops|(t+1)(m+1)/4 (PFZ:307-309) carries no a_t;
   - the floor term c·|TT|·m·(a/k + b′)·log T in Lo5 (QSB:12-14).
   - Both are ≪ Σ_t a_t·log T, by factors B₀/(|TT|·a) ≈ m/x and m/k.
   - So the Lean does **not** pay for the scaling. It claims instead that the π̄^{−nBr}-scaled values are already integral. That is `Conclusion6` (PFZ:334-343): `Pt` maps (fm u).lat m into ptLat (PtilIntegral) **and** ‖Pt x‖²_v ≤ ptB·‖x‖²_v with ptB = ∏_τ T^{−deg τ}·be_τ² (PFZ:332).
   - Together with `PeriodClassSumWeyl` (WDS:723-727; at T, vDG = 0, AGP:107-111), this is the T-adic divisibility that, under the product formula, must replace the payment.
   - `Conclusion6` is supplied only through `product_first_zeroth_parts.KudlaFamilyStatement` (premise `s10`, LPk:229 and its signature line), and through the closed-class field `pt0` (AGP:303). I did not trace it further.
5. **Main-term identity: checked by hand, it matches (§2.3).** Count5 is used in the right direction: it is a lower bound on log T, used where −a·log T sits on the upper side.
6. **Count5's supplier is an explicit computation, not limit multiplicity.**
   - The chain is `countF_fam` (JL:1152-1155) → `countF_of`/`count_at_of` (JL:20-142) → `PartFiveFamilyBounds` ← `family_part_five_of_explicit_constants` (FP5:483-484) ← `division_level_prime_family` (LMin:425-426). The last takes MassRatio₂, BaseVolumeEqualsMass and SigmaDegreeTwoSidedBoundOfGap as inputs (LMin:734).
   - The bound proved is lowS ≤ logXuD with error 11·L (T3E:142-148), i.e. log(D*/d*_u) to absolute error 11·f·k·L.
   - `count_at_of` then adds +1 (T window), +2 (Γ, via `logGam_le`) and La ≥ L, which gives cCount = max C 0 + 2 (JL:85-125).
   - The precision needed is relative 1/m ≈ x^{−1/2} on log T. That is achievable because D*/d*_u is a product of exact mass ratios, level indices and Weyl dimensions, with two-sided formal-degree bounds dsig ∈ [(1−ε₀)dimV, …] (STL:399-404). No counting error enters.

## 1. Statement

**Count5** (QSB:27-31), with the Lean's mean over ρ ∈ Fin f:
 log T(u) ≥ Σ_j (1/f)Σ_ρ log(w_{jρ}·v/π) + m·lg − cCount(La + m²La/k), log T(u) ≤ cCount·m·L, |log T(u) − log T(u′)| ≤ cCount·log k. Here lg = log g₀ + log g₁ (JL:96-98).

**DIV** (MB:118-121): μCC + h(u) − Fo ≤ Σ_t [m(ph(a_t) − a_t logΩ) − a_t·log T(u)] + errors.

**Main** (MB:107-109): Σ_j Σ_t a_t(log a_t − 1 − γ + LpL − (1/f)Σ_ρ log w_{jρ}).

**Supplier of the lower bound** (T3E:142-148, `Conclusion5Sharp` in the StandardLattice sense, not PFZ's):
 lowS := Σ_j (1/f)Σ_ρ log(w_{jρ}v/π) + m·lg − 11L ≤ logXuD(u) = (1/(fk))·log(D*/d*_u) (GAL:88, 99).

## 2. Argument (reconstruction)

### 2.1 The mechanism, in words *(mine, built on the Lean lines of §0)*

1. **Source and target.** The source space at word u is a space of level-T forms: Mram = Mu0 ∩ ⋂_v ker(Σ_{c∈F_v^×} ρ_T(c)) (DK:146-152), i.e. the vectors on which no place-v torus character is trivial. Its mass-formula dimension is ≈ d*_u·(T^k − 1)^f. The target has mass D*.
2. **Choice of T.** Theorem S (frame, RANK) needs d_u ≍ D*/Γ². That fixes T^{fk} ≈ D*/(d*_u Γ²) (§0.2).
3. **The last map.** It evaluates the top Bessel coefficient at points translated by π_T and divides by π̄_T^{nBr}.
   - Suppose the coefficient extracted (`coefLast`, top exponent b, FSN:87-96) is homogeneous of degree nBr in the new row, and the translated point carries π̄_T there. Then the value is π̄_T^{nBr}·(an integral value), and the scaled map is integral at T *by homogeneity*. This is my reading of `Conclusion6`'s PtilIntegral. I did not open `DecoSet.til` to confirm which of π, π̄ lands in that row.
   - Archimedean side: ‖Pt x‖² ≤ T^{−deg}·be²·‖x‖² is then the same statement as |value at the translated point|² ≤ be²·‖x‖². That is a pointwise evaluation bound, since the translated points are points of the level-T class set over which ‖x‖² is summed (`tilC` maps into `DecoSet … (Pr.vT u) …`, FSN:204-210).
4. **What this means for the height.** The height of B_u drops by Σ_t a_t·log T, and no T-adic denominator appears.
5. **What limits it.** Nothing in the height. The limit is the rank: a larger T inflates the source dimension like T^{fk}, and the frame's rank match fails.
6. **Count5.** It converts the pinned log T into its value: (1/(fk))·log(D*/d*_u).
   - *(inferred)* D*/d*_u is, per archimedean place ρ, the Weyl/formal-degree ratio for adjoining m rows of weights w_{jρ} to a k-column. That gives ∏_j (w_{jρ}·v/π)^k up to bounded factors (the v/π from the vol(Y₀)/massI ratio and the (2π)-normalisation of dsig).
   - It also contains a level-index ratio idxSig/idxPi ≈ ∏_i g_i^{f·m(2k+m−1)/2}, by `Conclusion4a`/`Conclusion4b` (STL:406-418).
   - Dividing by fk gives Σ_j (1/f)Σ_ρ log(w_{jρ} v/π) + m·lg·(1 + O(m/k)). The O(m/k) is the source of the m²L/k term *(mine)*.

### 2.2 One-lift model *(mine)*

Work at one top τ and one lift (m = 1), with a Fock jet of order a. The Fock/Bergman normalisation gives |a-th coefficient|² ≤ (a!/Ω^a)·‖f‖². Its log is ph(a) − a·logΩ + O(log a), which is hB (INP:192-193).

The last functional adds −a·log T (hA). With log T ≥ (1/(fk))·log(D*/d*_u) and D*/d*_u ⊇ ∏_ρ (w v/π)^k, the archimedean side per top is:

 ph(a) − a·logΩ − a·mean_ρ log(w v/π) − a·lg + a·lg(Ee) = a log a − a − a·logΩ − a·log(v/π) − a·mean log w.

The direction is consistent: Count5 lowers an upper bound. A *larger* true log T would only make DIV stronger, and that is why the upper pin (T_win) matters.

### 2.3 Main-term identity by hand *(mine)*

**Prime side.** Use (y/n − 1)₊ = (1/2πi)∫_{(c)} (y/n)^s ds/(s(s−1)). The residues at s = 1 and s = 0 give x − 1, which checks the formula. Then, with y = a/w:

 Σ_n Λ(n)(y/n − 1)₊ = (1/2πi)∫ (−ζ′/ζ)(s)·y^s/(s(s−1)) ds.

- At s = 1 there is a double pole, with −ζ′/ζ = 1/(s−1) − γ + …. Expanding y^s/s = y[1 + (s−1)(log y − 1) + …] gives the residue y(log y − 1) − γy.
- At s = 0 the residue is ζ′/ζ(0) = log 2π, which is O(1). The zeros give −Σ_ρ y^ρ/(ρ(ρ−1)).

The χ-part −Σ Λ(n)χ(n)(y/n − 1)₊ has a simple pole at s = 1 from 1/(s−1), with residue +y·L′/L(1,χ). Then (a/n − w)₊ = w·(y/n − 1)₊ gives

 Σ_n Λ(n)(1−χ(n))(a/n − w)₊ = a(log(a/w) − 1 − γ + L′/L(1,χ)) + O(w) + (zeros).

This is MAIN (FPN:89-91 [LEDGER]).

**Archimedean side, per (t, j).** Take logΩ = γ + log(π/v) − LpL (DP2:224 [LEDGER]):

 ph(a) − a·logΩ − a(mean log(w v/π) + lg) + a·lg
 = a log a − a − aγ − a·log(π/v) + a·LpL − a·mean log w − a·log(v/π)
 = a(log a − 1 − γ + LpL − mean log w).

- **v and π cancel exactly**: log(π/v) + log(v/π) = 0.
- **The signs match**: −1, −γ, and +L′/L on both sides, with LpL = Re L′/L(1, (·/d)) tied to ell(chC) [DIVKEY].
- This agrees with `key_identity5` (LoC:105-107 [LEDGER]).

**Precision.** The Count5 slack ΣA·cCount·La ≈ |TT|·a·x^ε is ≈ x^{1/2+2ε}·U, the "x/m" family [LEDGER §2a]. The supplier's 11L + 3 sits inside that.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `ColumnsAtT` fields T, T_prime, card_vT, card_Fv, Mram, Xu, Tstar | DK:104-159 | T prime, f places of norm T; T* = (D*/d*_u)^{1/(fk)}Γ^{−2/(fk)} | defines T_u | glue (read) |
| `T_win` | RDP:153-154 | T* ≤ T ≤ (1+1/(fk))T* | upper and lower pin | definition field |
| `piT_norm`, `T_prime` | AHF:224, 227 | π_T π̄_T = T | the archimedean size T^{1/2} per embedding | glue |
| `brAt`, `brC`, `tilQ`, `evzC`, `PtilFF` | FSN:137, 197-219 | the scaled Bessel functional at π_T-translated points | source of T^{−nBr} | definition (read) |
| `periodFun_le` | IPF:26-88 | \|Ptil\|² ≤ T^{−ΣnBr}·c²κ·‖ψ‖²‖F‖² | archimedean −a log T | glue: the scalar factor is trivial; `LastMapNorm` is an input |
| `LastSide`, `lastLog`, `exists_htNums_of_kerSide_lastSide` | FB:62-87; EHN:11-25 | hPn ≤ −Σ nτ log T + … | packages into hA | glue |
| **`Conclusion6`** | PFZ:332-343 | Pt is T-integral **and** ‖Pt x‖² ≤ ∏T^{−deg}be²‖x‖² | **the product-formula payment, asserted** | **core, input via s10 / pt0** |
| `Conclusion5Sharp` (PFZ), `TwistedColumnBoundAtT`, `ColGe0_atT`, `sg_atT`, `admissible_at_twist_places` | PFZ:315-318; AGP:20-23, 92-111; DGi:34-60; WDS:887-901 | the column chain at T loses only m·EatT | T-adic cost actually charged | core inputs (h5, h5T) |
| `WeightBudgetBound` / ETpi | PFZ:307-328 | ETpi·log T ≤ C·B₀ | bounds that cost | input |
| `TorusPairsWithVariant`, `lowB`, `Conclusion5` (STL) | STL:524-540 | d*_u(T^k−1)^f ≈ D*Γ^{−2}; lowB ≤ logXu | Count5 data | hypotheses of `count_at_of` |
| `count_at_of`, `countF_of`, `countF_fam` | JL:20-142, 144-160, 1152-1155 | Count_at with cCount = C+2 | Count5 | glue (read) |
| `VandermondeCountExplicit`, lowS | T3E:142-174, 199-200 | explicit dimension-ratio bounds, error 11L | Count5 content | standard-type (mass formula, Weyl dimension); supplied by `division_level_prime_family` (LMin:425-426) from three named inputs; body of `part_five_family_of_mass_volume` not read |
| `duStarP`, `DstarP`, `logXu` | GAL:80-99 | mass × index × Weyl/formal degrees | what log T measures | definition |

## 4. Oddities

1. **The ledger is monotone in T.** With the inputs held fixed, increasing log T by Δ lowers the DIV bound by Σ_t a_t·Δ ≈ |TT|·a·Δ. It raises the costs only by m·ETpi·Δ (≤ C·B₀·Δ/log T) and c·|TT|·m(a/k + b′)·Δ.
   - Only `T_win` (and the matching `VandermondeCountExplicit` clause 1) stops a larger T.
   - So everything rests on `Conclusion6` holding at *this* T, and on the frame's rank match being the true reason a larger T is unavailable.
   - **Ten-minute check for an expert.** Is it true that, for level-T (mirabolic, Mram) source forms, the top Bessel coefficient at a π_T-translated CM point is divisible by π̄_T^{deg} with deg ≈ a_t ≈ x·b, while T ≈ e^{mL} (so a ≪ T)? The homogeneity reading of §2.1 makes it plausible. It depends on which of π, π̄ the translation inserts. I did not read `DecoSet.til`.
2. `cOf_eq` (RDP:150-151): c_u·c̄_u·T_u = T_{u₀}. The T's of different words differ by norms from E. This is consistent with the variation clause |log T(u) − log T(u′)| ≤ C·log k.
3. NONVAN called T_u "the norm of the word's anisotropic vector". That is compatible: π_T π̄_T = T.
4. REVIEW2 B6 asked for "what bounds T above". The answer is T_win: T ≤ (1+1/(fk))·T*, so log T ≤ logXu + 1. A crude form, log T ≤ CTu·m·L, also exists.

## 5. Coverage

**Read:**
- JL:1-160, 1150-1156; STL:300-420, 474-662; GAL:55-101; DK:98-247; RDP:150-158; AHF (grep lines 188, 224, 227);
- FSN:40-230; IPF:1-120; FB:1-90; EHN (grep and lines 11-25); INP:180-300;
- PFZ:240-345, 560-575 and the definition list; AGP:1-115 (and the grep hits 247-305); DGi:25-60; WDS:715-740, 880-905;
- T3E:140-205; FP5:483-500 and the definition list; LMin:425-445, 728-738; LPk:205-232; PHR:175-190;
- MB:100-165; QSB:10-35; `RowPinD.lean`:1-40; `PeriodPointConditions.lean`:20-45.

**Greps:**
- `hPn :=|t1 :=`; `HtNums`; `def LastSide`; `def nBr|def cBr|def kapBr|lastLog`;
- `def brC|def brAt|coefOpLe_brAt|LastMapNorm|PtilFF`;
- `Conclusion5Sharp|TwistedColumnBoundAtT|ColGe0_atT|sg_atT|period_geTU`; `PeriodClassSumWeyl`; `product_first_zeroth_parts.(Stmt|ConclusionOnFamily|Conclusion6)`;
- `def TuSize`; `T_win|T_prime|piT_norm`; `family_part_five_of_explicit_constants|division_level_prime_family|countF_fam`; `VandermondeCountExplicit`.

**Not opened:**
- `DecoSet.til` (which of π, π̄ the translation inserts); `LastMapNorm`'s content; `OrthNormLogBound`;
- the bodies of `part_five_family_of_mass_volume`, `ramified_rank_lines_of_free`, `gapB_ev`;
- the producers of s10/`KudlaFamilyStatement` (product_first_zeroth_parts) and of PerDec0;
- the frame/RANK use of d_u ≍ D*/Γ².
