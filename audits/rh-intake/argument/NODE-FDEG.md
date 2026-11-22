# NODE-FDEG: formal-degree normalisation of T*, and the true T-adic loss per lift

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(mine)* = my own computation or inference. [NODE] = taken from that node and not re-read. Nothing was compiled or executed.

Abbreviations as in NODE-TFLOOR/TU/TDIV/SHARP (`GAL`, `T3E`, `STL`, `DK`, `PFZ`, `AGP`, `DE`, `INP`). New ones:
- `DCD` = `Formalism/LocalRingCardinality/DataCD.lean`; `DTi` = `Formalism/LocalRingCardinality/DataTies.lean`; `SSE` = `Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean`
- `TTG` = `Formalism/SharpRestriction/GlobalSchurBounds/TheoremThreeFamilyOfGappedMultiplicity.lean`; `HCF` = `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeGap/HCFdegRGapHolds.lean`
- `SM` = `Formalism/HermitianLattices/StatementMass.lean`; `GL5` = `Formalism/LocalToGlobal/GlobalTheory/GL5/DiscreteSeriesOfFormalDegree.lean`; `TuS` = `Formalism/SharpRestriction/GlobalSchurBounds/TuSizeOfRealPlaceSecondLayer.lean`
- `PubF` = `Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/FormalDegreeOfParameter.lean`; `PubH` = `.../PublishedTheorems/GlobalTheta/HcFormalDegreeOfDiscreteSeriesFormalDegree.lean`
- `ILB` = `Formalism/LocalToGlobal/HermitianForms/IsLocBasis.lean`; `TStep` = `Formalism/LocalToGlobal/HermitianForms/TiedStep.lean`
- `GTw` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LevelChainSharpColumnValuationOwnChainIff.lean`; `FSt` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/FormsStable.lean`
- `UKS` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExtInOfValIn.lean`; `PKL` = `.../GlobalInterpolation/LevelChainSharpColumnValuationOfPointKernelLiftL.lean`; `DLD` = `Formalism/LocalRingCardinality/DataLatDefs.lean`; `Par` = `Formalism/LocalRingCardinality/Params.lean`

## 0. Verdict

**Part A: no ESCALATE. The normalisation is consistent, and TFLOOR's open premise is in fact proved in-tree.**
1. **One Haar measure throughout.** The formal degree dsig, the archimedean factor of vol(Y₀), and the Haar measure behind massI are all taken for the same `CDHaar` measure. That measure is fixed by its density at the identity relative to a Lie-algebra Lebesgue measure, and its compact case is the probability measure. This is the compact-dual (Harish-Chandra) normalisation (DCD:51-61; `cdScaleTie` DTi:10-15; `VolTie`/`IsVolMeas` STL:241-263). The counting theorem uses a second consistent pair: d_v and vol are both taken for the bare `muG` (LP:84; GA:108-109).
2. **dsig equals dimV(rowLam) exactly inside the proof.** The live producer of `SigmaDegreeTwoSidedBoundOfGap` is `explicit_bound_family` (TuS:20, TTG:200).
   - It runs through `theorem_three_of_gap_bound`, whose hypothesis `hf` is the *equality* fdegOf = fdegHC (TTG:68-76).
   - `hf` is supplied in-tree by `hCFdegRGap_holds` → `fdeg_cd_gap` → `fdCons_cd` (HCF:83-111; body of `fdCons_cd` unread). The `Published` props (PubF, PubH) state the same formula but are not on this path.
   - The two-sided bound is a weakening made only for export (TTG:99-123).
   - So NODE-TFLOOR oddity 1 is resolved: log T* − Lam5 = O(L) in truth (§2.1).
3. **The masses do not cancel, and they need not.**
   - The source and target are *different-rank* groups: definite U(k) at level T, and indefinite U(r) with r = k+m−1. They are not inner forms of one group.
   - vol(Y₀) = massI(r) is the inner-form step. It is exact in the compact-dual normalisation and is proved in-tree from root premises (GL5:57-110).
   - massI(r)/massI(k) is then a telescoped product of m−1 Siegel mass ratios (SM:40-42). That leaves m−1 values L(M, η^M) with M ∈ (k, r], each ≈ 1 (STL:296-298), plus the explicit v/π and factorial factors.
   - The factorials cancel exactly against the HC/Weyl denominators facProd. I re-derived `LemmaFiveOneIdentity` (T3E:126-138) from these definitions.
   - T* depends on the weights, on v = |d_E|^{1/2f}/2 and on g₀g₁. It does not depend only on the weights.
4. **Level T matches TDIV's lattice.**
   - (T^k−1) is the index of the stabiliser of a nonzero row vector in GL_k(F_v) (`LevelIndexAtPlace`, STL:446-451), i.e. the mirabolic, on the source side only.
   - The level-T structure (`StepLevel`, ILB:58-82) is a lattice Lb with [Lb^#:Lb] = T^{2f}, together with a nonzero functional fT : Lb^#/Lb → (size T).
   - For Lb = N ⊕ O·z0 (TDIV) this has index (T^k−1)/(T−1)·(T−1) = T^k−1 *(mine)*.

**Part B: no ESCALATE, but SHARP's carrier is not established. A sign check is needed (§2.3).**
- **What the Lean asserts is an upper bound only.** `Conclusion5Sharp` (PFZ:315-318; GTw:324-327) and `TwistedColumnBoundAtT` (AGP:20-23) say that c·colT is integral at w | T once v_w(c) ≥ e_w·m·ET.
- **What it books per step.** The live per-step producer is `ukSharp` (UKS:155-198). It books e_i = Σ_{non-top v} λ_{i+1}(τ_v)₀ + f·N(i) + Σ_τ sDiv_i(τ) (UKS:171-172).
- **How the step map is built.** It is K_i = ρ·divDe∘unf∘sharp (DK:57-65): multiply by ∏de_i^{sSharp}, then divide by ∏de_{i+1}^{sDiv}, with sDiv − sSharp = (t+1)/2 (DK:41-47, 225).
- **What the model says.** In a Sym^a model with both levels at level-T points, a det^s twist moves the valuation by exactly ±s on every monomial. The booked term sDiv ≈ w therefore cancels against sharp's sSharp, down to (t+1)/2 per τ. That is the same T^{(t+1)/2} as the U-commutation (PFZ:291-294).
- **What is left.** The only remaining weight-sized term is the non-top top-coordinate comparison, which is sharp only on extremal vectors.
- **Consequence for SHARP.** If the cancellation is real, the true T-loss per lift is poly(x)·log T, not ≈ W·log T. That is a factor ≈ b/poly below the ≳ U·x^{1/2}/m per lift that SHARP needs.
- **Why this is not an ESCALATE.**
  - The sign convention of `ValTied.lat` (TStep:118-123) and the T-adic content of `unf` were not traced, so the shortfall is not proved.
  - A second carrier exists: SHARP's covolume q-part (sign unsettled).

## 1. Statement (what was read)

**Measures.**
- `CDHaar` (DCD:57-61):
  - cd P Q is a Haar measure on U(P,Q);
  - cd N 0 is a probability measure;
  - cd P Q and cd (P+Q) 0 have the same density c at 1 against `IsOmegaLeb` Lebesgue measures on the Lie algebras.
  - `IsOmegaLeb` (DCD:42-46) requires λ⊗λ ∘ (X,Y) ↦ X + iY to be Lebesgue measure on M_N(ℂ). That fixes λ for every real form, so this is the compact-dual transfer.
  - It is unique (`cd_eq`, `.../PlaceModelImp.lean:33`), and its existence is proved (`nonempty_cdHaar`, `.../NonemptyCompactDualHaar.lean:235-249`).
- `cdScaleTie` (DTi:10-15): cdScale·muG = (D.cd.cd P Q) transported to U(J_ε). `cdScaleOf` is the Haar scalar factor (SSE:207-230).
- `dsigTie` (DTi:17-21): any formal degree of the DS with parameter lamSH, taken w.r.t. cdScale·muG, equals D.dsig τ. Both ties are fields of `Ties` (DTi:38-40).
- `IsVolMeas`/`VolTie` (STL:241-263): D.vol W = μ(fund), where μ gives {h_f ∈ Stab(L̂₀), h_∞ ∈ ∏B_ρ} the measure ∏ D.cd.cd P Q (B_ρ).
- `VolumeEqMass₂` (STL:275-279): vol = massI(rank) for definite W, and for indefinite W with P ≥ 2.
- `BaseVolumeEqualsMass` (T3E:89): volY0 = massI(r).

**Mass formula.**
- massI(M) = Σ_classes 1/|Aut| for the standard O_E-lattice of rank M (GAL:20-22; SM:11-16).
- `massRatioRightSide` (SM:40-42) = [(M−1)!·(v/π)^M]^f / √((2v)^f) · lValEta(M), where:
  - v = |d_E|^{1/2f}/2 (SM:27-28);
  - lValEta = ∏_P eulerFac (SM:30-38), i.e. L^{fin}(M, η^M) for E/F unramified.
- *(mine)* This gives |d_E|^{M/2−1/4}·((M−1)!)^f/(2π)^{Mf}·L(M, η^M). That has the shape of the Gan–Hanke–Yu ratio for unimodular lattices.
- `MassRatio₂` (STL:288-290) is supplied by `siegel_mass_ratio_family` (GL5:18-24) ← `SiegelMassBounds.siegel_mass_ratio`, whose body I did not read.

**Formal degree.**
- fdegHC(λ) = ∏|λ_a−λ_b| / ∏(b−a) (UpqRep:233-235; StatementDS:19-21).
- `dimV_eq_fdegHC` (STL:320-327); `prod_gap_eq_facProd` (STL:305-318).
- `SigmaDegreeTwoSidedBoundOfGap` (T3E:76-81).
- Its proof `theorem_three_rows_of_real_place` (TTG:131-193) takes cdScaleTie and dsigTie and applies `theorem_three_of_gap_bound` with hf = `hCFdegRGap_holds cd s hc` (TTG:125-129). There, fdegOf(muCD) = dimVlam is `fdCons_cd` (HCF:106), and muCD = s·muG by `muCD_eq_smul` (HCF:29-34).

**D\*, d\*_u and the counts.**
- D* = volY0·idxSig·∏dsig, and d*_u = massI(k)·idxPi·∏dimV(u) (GAL:82-99). The record ties these to the field values D.what₂.Dstar and duStar (`DataExtra.lean:89-91`).
- **Source dimension.**
  - `ClassNumberFormula₂`: #cls0 = massI(k)·idxPi·(T^k−1)^f (STL:453-456).
  - `Mu0Tie`: finrank Mu0 = #cls0·∏dimV(u) (STL:458-461).
  - Together these give `Conclusion4f`: finrank Mu0 = d*_u·(T^k−1)^f, *exactly*, when stabilisers are trivial (STL:463-472).
  - Mram is cut out from Mu0 by the torus kernels (DK:146-152).
- **Target dimension.**
  - `WordCountBound`: |Dall − D*| ≤ e^{−c r f log r}·D* (PlaceDegreeData:384-391).
  - The counting theorem's main term is ∏d_v·vol·e(1), with d_v and vol both taken for muG (LP:82-95; GA:203-206, 108-109).
  - The instance's measure is tied to D through `instTie_of_record`, which uses VolTie and cdScaleTie (`.../FlagStabilizerTensors/CountT.lean:45-49`).
  - The count is conditional on Siegel–Weil [NONVAN, COUNT].
- **Level T.**
  - `StepLevel` (ILB:58-82): Lb ⊂ Lb^#, T·Lb^# ⊆ Lb, [Lb^#:Lb] = T^{2f}; fT ≠ 0 on Lb^# killing Lb, with values in a module of size T; Uloc = Stab(Lb) ∩ Stab(fT) at T.
  - It is carried by `ClsTied` at every level i ≤ m (TStep:70-89).

**T-adic step (Part B).**
- ColumnChain step (DK:41-70): `sharp` multiplies by ∏_τ de_i^{sSharp}, `divDe` divides by ∏_τ de_{i+1}^{sDiv}, and Kmap = ρ·divDe∘unf∘sharp.
  - sDiv_i(τ) = e_i(τ) − N(i)/2 and sSharp = e_i − N(i+1)/2 (Par:71-73), with N(j) = k + j(t+1) (Par:36).
  - The record forces sDiv − sSharp = (t+1)/2 (DK:225, grep line).
- de_i(z, τ) = τ(det C)·det(frame z at τ), with C*C = gram and C carrying the self-dual lattice to O^N (TStep:97-100). So de has no class dependence.
- `UKSharp` (FSt:313-316): T^{2ΣWt + fN}·Uprod_{i+1}∘KT_i maps S_i(w) into S_{i+1}(w) at seen w.
- `WtBounds` (FSt:307-311): 0 ≤ sDiv_i(τ) ≤ Wt_τ; detShift(λ_{i+1}) = −sDiv_i; at non-tops λ_{i+1}(τ)₀ ≤ Wt_τ.
- Uprod runs over the top places only (VVT, DLD:71-75).
- Wtau = max over levels i ≤ m and coordinates (top row excepted) of |λ_i(τ)_a − i(t+1)/2| (DE:98-101). It is a **max coordinate**, not a sum.
- Consumer: `admissible_at_twist_places` (AGP:92-111) gives valuation ≥ sg = −m·EatT at w | T.

## 2. Argument

### 2.1 A: θ recomputed from the definitions *(mine)*

1. **The exact log identity.** log(D*/d*_u) = log(massI r/massI k) + log(idxSig/idxPi) + Σ_ρ log(dsig_ρ·facProd(k)/vand(u_ρ)).
2. **Telescoping the mass ratio.** Telescope with `massRatioRightSide` over M ∈ (k, r]:
   - Σ M = (m−1)k + m(m−1)/2, which gives the coefficient of f·log(v/π);
   - there are m−1 factors of (2v)^{−f/2};
   - Σ f·log(M−1)! = Σ_ρ log(facProd r/facProd k);
   - the lValEta terms remain.
   This reproduces T3E:130-138 term by term. Together with `IndexProductFormulasAndRatio` (T3E:105-113) for the g-part, `LemmaFiveOneIdentity` is an exact identity.
3. **Substituting the exact formal degree.** Use dsig = dimV(rowLam) (§0 A2):
   - vand(rowLam) = vand(v)·∏_{a,j}(v_a + b_j)·∏_{j<j′}(b_{j′} − b_j);
   - vand(u) = ∏_{l≥1}(u₀ − u_l)·vand(u_{1..k−1}), with u_l = v_{l−1} − ½ (−Δ);
   - log vand(u_{1..k−1}) − log vand(v) = O(k log k) (T3E:176-181).
4. **The size of each residual piece.** I use DataB (STL:500-516) and RowsA (T3E:115-121). Lam5₀ − logXu is the sum of:
   - log(v/π) + O(m²L/k), from R1;
   - ≤ m/x + O(mL/k), from w versus b and the (k−1)/k factor;
   - −O(m²L/k), from the b-gaps;
   - mean_ρ log(u₀ − ū) ∈ [log(4kΔ), log(2a)] ⊂ [0, L + log 2x];
   - ≈ f·2^{−k}, from the lValEta terms.
5. **Result.** With m²L ≤ k (DataB) and log v ≤ L, I get **|θ| ≤ 2L + O(log x)**. This agrees with TFLOOR's 0 ≤ θ ≲ 3L, independently.
6. **Consequence.** log T ∈ [logXu − 2logΓ/(fk), logXu + 1], so **log T* − Lam5 = O(L)**. SHARP's rigidity requirement is met. Because dsig = fdegHC is what the in-tree proof actually establishes, this holds as a fact about the tree, not as an assumption.

**Haar consistency.** dsig and vol(Y₀) both use D.cd, and the count's d_v and vol both use muG. The products d·vol are therefore normalisation-free and equal. No mismatch is possible on this path. The only place a mismatch could enter is `instTie_of_record`/`rowsTiePT'_of` (count instance ↔ D), whose body I did not read.

### 2.2 A: the level-T index *(mine, on ILB:58-82, STL:446-451)*

At a split place v | T (π-component), take N′ unimodular of rank k−1 and L = N′ ⊕ O·e_last, and set Lb = N′ ⊕ O·π e_last. Then L/Lb ≅ O/π, of size T.
- Stab_{GL_k(O_v)}(Lb) is the stabiliser of a hyperplane mod π, of index (T^k−1)/(T−1).
- Fixing fT, a nonzero functional on Lb^#/Lb whose π-part is a line over F_T, gives a further index T−1.

The total is **T^k − 1**: the mirabolic index of `LevelIndexAtPlace`. The other condition, Lb^#/Lb of order T² per v, matches h(z0, z0) = T in TDIV.

What I did not trace: the theorem that turns Uloc's index into `ClassNumberFormula₂` (a Prop with GBig/SplitsF premises), and its producer.

### 2.3 B: the mechanism, the model and the size

**Booked per step at a seen place** (UKS:171-187): e_i = Σ_{v non-top} λ_{i+1}(τ_v)₀ + f·N(i) + Σ_τ sDiv_i(τ), with e_i ≤ 2ΣWt + fN(m). The m steps compose to m·ETpi. ETpi adds |tops|(t+1)(m+1)/4, which is the accumulated U-shift T^{(t+1)/2} per step at tops (PFZ:291-294, 307-309).

**Rank-one / Sym^a model** *(mine)*. Take one split π̄-place, with a level-T point L = πO (or N ⊕ O·z0). Then L^# = π̄^{−1}O, the dual coordinate is Y = π̄y, and a monomial y^α is integral iff c·π̄^{−α_N} ∈ O.
1. **Twist by det^s.** A twist by det^s raises every exponent by s (on a line, y^n ↦ y^{n+s}). Re-expressed in the dual coordinates it changes the valuation by exactly s on **every** monomial, so no cancellation inside the map can shrink it. Applied alone, divDe's det^{−sDiv} therefore costs sDiv ≈ e_i(τ) ≈ w_{iτ}. That is what `ukSharp` books.
2. **The compensating twist.** K_i also contains sharp's det^{+sSharp} at the *source* point. That point is again a level-T point with the same [Lb^#:Lb] = T^{2f} (ClsTied at every level). The two twists move the valuation in opposite directions, so the net det contribution per τ is |sDiv − sSharp| = (t+1)/2. This is exactly the exponent of the U-commutation (PFZ:291-294), which is independent evidence that the step shifts T-adic normalisation by (t+1)/2 per place.
3. **What carries weight w.** The remaining weight-sized booking is the non-top top-coordinate term, i.e. the lattice comparison B_w ⊂ T^{−(2Wt+t)}·S (PFZ:257-258, 272-273). In the Sym^a model this inclusion is sharp only on the extremal monomial y_last^{λ₀}. It costs a heavy-component vector the full λ₀ only if that vector has extremal last-row degree at non-top thick places.

**Quantitative comparison** *(mine; U = |TT|·m·b·δ/2, log T ≥ (m/2)x^ε, W = Σ_τ w ≈ δnb [SHARP])*:

| quantity per lift | size | ÷ (U·x^{1/2}/m) |
|---|---|---|
| booked EatT·log T | ≈ 2δnb·(m/2)x^ε | ≈ 2(n/\|TT\|)·x^{ε}·(m/x^{1/2}) = x^{O(ε)} ≥ 1 |
| true det part, model: f(t+1)/2·log T | poly(x)·m·x^ε | ≈ poly(x)/b → 0 |
| true top-coordinate part, if λ₀ ≈ w at thick non-top τ | ≈ W·log T | x^{O(ε)}, enough |
| true top-coordinate part, if λ₀ = poly (u₀ ≤ 12kΔ at level 0, STL:505-512) | poly·log T | → 0 |

So the booked m·EatT is of the size the barrier needs, with margin x^{O(ε)}. The true loss reaches that size **only if** one of two things holds:
- (a) sharp's det^{+sSharp} does *not* compensate divDe at level-T points. That would require the source-point dual-lattice convention to differ from the target's, or `unf` to undo it.
- (b) The heavy component carries an extremal coordinate ≈ w_{iτ} at the non-top thick places at every level.

I could settle neither from what I read.
- If both fail, the true composed T-adic valuation on the heavy component is ≈ m·f·(t+1)/2 + O(m·poly), against the booked m·EatT ≈ 2mδnb.
- The chain would then rest its m-family on the covolume q-part (SHARP §2.3, sign unsettled), or a proved hypothesis would have to be false.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `CDHaar`, `IsOmegaLeb`, `cd_eq` | DCD:42-61; PlaceModelImp:33 | compact-dual Haar on U(P,Q), unique | the one measure | definition (read) |
| `cdScaleTie`, `dsigTie`, `VolTie` | DTi:10-21; STL:241-263 | dsig and vol w.r.t. D.cd | consistency | record ties (fields of `Ties`) |
| `fdCons_cd` via `hCFdegRGap_holds` | HCF:83-111 | fdeg(muCD) = dimV(λ) exactly under the gap | dsig = HC value | **core, in-tree, body unread** |
| `theorem_three_rows_of_real_place` | TTG:131-193 | two-sided dsig bound from the equality | supplier h3 | glue (read) |
| `siegel_mass_ratio`, `vol_indef`, `volume_eq_mass_rank_two` | GL5:18-110 | massI ratios; vol(U(P,Q)) = massI(P+Q) | D* = massI(r)·… | standard (Siegel/GHY; Prasad); premises hU, hG at `link_gl` (LinkGl:14-25) |
| `LevelIndexAtPlace`, `ClassNumberFormula₂`, `Mu0Tie`, `Conclusion4f` | STL:446-472 | source dim = d*_u·(T^k−1)^f exactly | the T-index | hypotheses; producers not traced |
| `StepLevel`, `ClsTied` | ILB:58-88; TStep:70-89 | level-T lattice + functional at every level | same lattice as TDIV | definition (read) |
| `Conclusion5Sharp`, `TwistedColumnBoundAtT` | PFZ:315-318; GTw:324-327; AGP:20-23 | denominator of colT at T ≤ m·ET | booked T-loss | **core; upper bound only** |
| `ukSharp` ← `levelChainSharpColumnValuation_of_pointKernelLiftLaws` | UKS:155-198; PKL:21-25 | per-step exponent = sDiv + top coord + fN | the per-step loss | core; inputs KerLaws/ValTie/KerTie/StabUnit unread |
| `Kmap`, `sharp`, `divDe`, `sDiv`, `sSharp` | DK:41-70, 225; Par:71-73 | step = det^{sSharp} · unf · det^{−sDiv} | mechanism | definition (read) |

## 4. Oddities

1. **SHARP's "pinned from below" is a property of the definition EatT, not of the mathematics.** Conclusion5Sharp is an upper bound on denominators. The per-step booking charges divDe's det^{−sDiv} (≈ w) and does not credit sharp's det^{+sSharp}, although sDiv − sSharp is only (t+1)/2 (DK:225).
   - *Ten-minute check:* in `ValTied.lat` (TStep:118-123), does multiplying by de_i^{s} at a level-T point change the valuation by +s or −s? Is it the same sign at levels i and i+1?
   - If the source gain and the target loss have opposite signs, the true per-lift T-loss is poly(x)·log T. In that case Ee_T cannot carry the √x barrier.
2. **The brief's "inner forms" premise does not hold.** Source and target have ranks k and r. The L-value product does not cancel. It reduces to m−1 values L(M, η^M), M > k, each ≈ 1 (STL:296-298).
3. **The exported Prop is weaker than what the proof establishes.** `SigmaDegreeTwoSidedBoundOfGap` exports only a two-sided bound, while the proof has the equality. A reader of statements alone would conclude, as TFLOOR did, that the rigidity is unproved.
4. `Published.DiscreteSeriesFormalDegree`/`FormalDegreeOfParameter` (PubH:11-29; PubF:11-14) duplicate the in-tree `fdCons_cd`. They are not on the live h3 path, as far as the chain I read goes.

## 5. Coverage

**Read:**
- Nodes: PROTOCOL; NODE-TFLOOR, TU, TDIV, SHARP, NONVAN, COUNT (all); COUNTS, ADM11 (grep for mass/T lines).
- Lean:
  - DCD:1-63; DTi:1-54; DataS:1-60; SSE:195-236; PlaceModelImp:25-35; NonemptyCompactDualHaar:1-80, 235-251; PubH, PubF (all);
  - GAL (all); T3E:1-210; STL:190-545; SM (all);
  - LP:78-100; GA:108-109, 200-256; PlaceDegreeData:375-400; CountT:30-60; DataExtra:75-96;
  - LMin:420-446 (and grep 690-737); LXL:36-80; TuS:1-35; LinkGl:10-33; GL5:15-130;
  - TTG:1-230; HCF:1-113; TheoremThreeUnderScaleOfGeneral:25-58; UpqRep:225-240; StatementDS:10-30;
  - DK:20-70, 98-161; ILB:58-88; TStep:70-100;
  - PFZ:20-110, 228-330; GTw:280-335; FSt:280-330; UKS:1-60, 150-200; PKL (all); DLD:71-75; Par:36, 71-77; DE:98-104; AGP:1-115; INP:280-300; FSN:50-60.

**Greps run:**
- `cdScale`; `(structure|class|def|abbrev) CDHaar`; `CDHaar`;
- `def (massRatioRightSide|lValEta|mass|fDeg|SiegelMassRatio)`; `def fdegHC|lamSH|epsSH`; StandardLattice `def (VolTie|…|Conclusion4b)`;
- `RowsTieP|rowsTiePT'_of`; `what₂.Dstar =`; `FamGLmin`; `explicit_bound_family`; `hCFdegRGap_holds`; `DiscreteSeriesDegreeBoundsAllScales`;
- `structure ClsTied`; `structure StepLevel`; `Conclusion5Sharp`; `ukSharp|UKSharp`; `def Wtau`; `sDiv`; `def gramN`; `def VVT`.

**Not opened:**
- the bodies of `fdCons_cd`, `muCD_eq_cd_vol`, `siegel_mass_ratio` and `instTie_of_record`/`instTie_of_inst`;
- the producer of `ClassNumberFormula₂`;
- `extIn_K`, `KerLaws`/`intP`/`bar` and `unf`'s T-adic content;
- `levelChainSharpColumnValuation_of_stability`; `ValTied.lat`'s sign convention.
