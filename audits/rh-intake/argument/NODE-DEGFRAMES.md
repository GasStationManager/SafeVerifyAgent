# NODE-DEGFRAMES: the Hodge-to-`homN` transport of the flat degree, the non-compactness link (RootOrigin/GoodOrigin), and the direction of μ(uM)

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own computation or inference. [NODE] means taken from that node and not re-read. Nothing was compiled or executed.

Abbreviations:
- `USN` = `Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/UnfSectionNormBoundAtHeight.lean` (statement wrapper: `…/UnfSectionNormBoundAtHeightStatement.lean`)
- `ECS` = `Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/ExistsConstSectionKroneckerChar.lean`
- `KPF` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/KroneckerCharacterPeriodFormula.lean`
- `KFB` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/KroneckerCharacterFrameBound{,Statement}.lean`
- `ICM` = `Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsConstMul.lean`
- `FDS` = `Development/AutomorphicSpectrum/Statements/GeometryStatements/FlatDegree.lean`; `FDH` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/FlatDegreeHolds.lean`
- `FCN` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/FrameFunctionCmNumberFieldStatement.lean`; `HMS` = `Development/AutomorphicSpectrum/Proofs/AdelicProofs/HermitianMetricLogNormFormulaStatement.lean`
- `EFS` = `Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean`; `NFE` = `Development/AbelianVarietyTheory/Definitions/Foundations/NotFlatExistsOfIsEmpty.lean`
- `IPM` = `Development/AbelianVarietyTheory/Definitions/Foundations/IsProbabilityMeasureMuPart.lean`
- `CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`; `NNC` = `Development/AbelianVarietyTheory/Definitions/Divisors/NormNegCmConstantEqAtAllEmbeddings.lean`
- `GO` = `Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/GoodOrigin.lean`; `TO` = `Development/AutomorphicSpectrum/Definitions/GlobalGeometry/TowerOrigin.lean`; `HL` = `Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsHodgeLine.lean`
- `GTX` = `Development/AutomorphicSpectrum/Statements/TowerExistence/GoodTowerExistsX.lean`; `GTV` = `Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/GoodTowerVolumeTheorem.lean`; `DSV` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/DeepStROfVolume.lean`
- `KUC` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/KoecherPrincipleUnitConstant.lean`

## 0. Verdict

**No ESCALATE.** The transport is an exact identity with zero residual. The covolume's main coefficient (p_j − q_j)·w·logΩ is confirmed as far as the transport is concerned. No inequality on this chain is used in the wrong direction.

1. **A. The weight factor is not cancelled and not left over. It is matched term by term.**
   - `lieFacZ` uses the **signed** weight sum ΣG, not |G| (IPM:664-665). The flat weight has −1 on each of the p directions at τ and +1 on each of the q directions at τ̄, so ΣG = q − p (`sum_flatWt`, NFE:159). Hence lieFacZ(flatWt) = (2πx)^{(p−q)/2} (USN:194-196).
   - In the uniformisation frame, the Lean's Hodge Gram matrix of a Lie frame is (2πx)·YᴴY, i.e. the factor 2πx per direction (`exists_gram_det`, USN:38-39, 55-65). The `HasInfNorm` value is log|φ| + ½log det Γ − ½log det Δ (ICM:59-63). It therefore contains +(p/2)·log(2πx) from the p directions and −(q/2)·log(2πx) from the q directions.
   - `homN_eq_exp_hodge` (USN:121-209) proves homN(s) = exp(HasInfNorm value) at every frame point.
   - **Consequence.** The Hodge-metric degree and the homN degree are literally equal. No term in |wt|·log(2πx) or q·w·log(2πx) survives, and nothing has to be booked.
   - **Correction to NORMS/QPART.** NORMS wrote "(2πx)^{−|wt|/2}" and QPART §4.1 said lieFacZ "does not distinguish p from q". In fact the factor is (2πx)^{−ΣG/2} with signed G. It distinguishes p from q exactly through the sign of the weight, which is all the Hodge metric does.
2. **`degree_frames` is not the Hodge→homN transport.** It is a finite-place relabelling (KPF:104-146). It subtracts C = q·(logIdeal 𝔇_E − log|d|_p) from N.fin and uses Σ_p C = [c.F:ℚ]·q·(log d − lrd E) (`corr`, KPF:47-102). This converts FDS's "(p−q)/2·logΩ + q(log d − lrd E)" into KFB's "(p−q)/2·logΩ" for the shifted norms. The archimedean side is untouched.
3. **B. Non-compactness is handled in two different places.**
   - On the covolume side (M_j, uM), cusp forms are sections on the *open* model that are holomorphic in the uniformisations. Boundedness and Koecher-type statements are proved in-tree, under the hypotheses [E:ℚ]/2 > 1 or > 2.
   - On the volume side (VolumeTheoremX), RootOrigin supplies a normal compactifying cover X → Y with a semi-abelian extension. Its interior is the abelian locus. The Hodge lines there are hermitian with log-singular potential and a smooth regularisation t → 0.
   - The link between the two, i.e. that the cusp-form lattice's degree is governed by the compactified volume, sits in `abelian_cm_comp_laws_bound` and `hermitian_geometric_hypothesis_holds`. I did not read either.
   - No Published statement of Lan, Koecher, Mumford proportionality or Burgos–Kramer–Kühn type was seen as a *direct* premise. The hypothesis bundle `Top.Given` (resolution, Fargues–Hodge–Tate, GAGA, toroidal level/Hecke compatibility, semi-abelian extension, …) is used, and its supplier was not traced.
4. **C. μ(uM) is bounded from below only, and that is the direction DIV needs.** uM is the reduced weight: the layer weight minus its parallel anchor part, minus c₀·(Hodge weight) (CXC:34; NNC:61-67).

## 1. Statement

### 1.1 The transport (A)
The chain from `FlatDegree_holds` to EFS's `FlatDegree` is as follows *(read)*.
1. `Fl.flatDegree` (FDS:12-19; FDH:60-118): HasNorms ⇒ N.deg = (p−q)/2·Re logΩ + q(log d − lrd E).
2. `degree_frames` (KPF:104-146): HasInfNorm ∧ HasFinNorm ⇒ N.deg = (p−q)/2·Re logΩ.
3. `degree_of_flatOnModel` and `kronecker_character_frame_bound` (KFB:20-24; Statement:13-14) restate 2.
4. `exists_constSec` (ECS:40-91) builds a `ConstSec` of weight flatWt τ and defect 0. Its cInf σ is exp(t σ), with t σ the HasInfNorm value (ECS:57-62, 82). It obtains `norm_inf` from `unf_section_norm_bound_at_height` = `homN_eq_exp_hodge` (ECS:83-86; USN:121). The conclusion is s.deg = (p−q)/2·Re CM.logOm (ECS:45, 91).
5. EFS then adds the defect q(log d − lrd E) back (`deg_eq_toFrame`, [QPART]) to give flatDegVal (EFS:751-754).

**`homN_eq_exp_hodge`, in words.** Let s be an algebraic section of weight flatWt τ that is read by the frame function φ, and let U be a uniformisation with |τ′(ξ₀)| = x for every τ′. Then at every tested frame point z:

  lieFacZ(x, flatWt)·ptN(s)(z) = exp(log|φ(v, w)| + ½log det Γ(v) − ½log det Δ(w)).

Here Γ and Δ are the Hodge Gram matrices of the p frame vectors at τ and of the q frame vectors at τ̄ (USN:121; ICM:59-63).

### 1.2 The three precision pieces (B)
These are restated from [VOLUME], [HS] and [QPART]. I re-read only the CXC definitions.
- **SlopeBound / HSAt** (CXC:153-156) is applied on each component Z of a deep cover Y (layer j, deeper level, larger coefficient field). It says
  binT·deg_Z(u1)·(lenT·h_Z(u1) − 3(dim+1)|h| − A·log(2+|h|) − R) ≤ deĝ(lattice of weight-uM integral cusp forms on Z),
  with A·log A + R ≤ C·unitE and unitE = B₀·log log x. It is proved in-tree by an effective Chow-form / products-of-short-vectors argument at one tensor power lenT [HS; VOLUME §3].
- **VolumeTheoremX** (GTX:28-36) has one C for all abelian CM E, hosts, data, towers T and good origins o, under q ≥ 1 and 3q+1 ≤ p+q. Its MeanSlope clause is: the component-mean of the normalised height of L_u on the flag-bundle model is ≥ −C·[(log(B·rd E) + |L′/L(1,χ_d)|)·‖u‖₁ + min(p,q)·spread(u)]. It is one-sided and has no main term [VOLUME §1].
- **FlatDegree** (EFS:751-754) is exact: every flat section has degree (p−q)/2·logΩ + q(log d − lrd E).

### 1.3 uM and the bounds on it (C)
- Gk = wtZ(wtA κ, n) is the layer weight (CXC:28). Gs(s) = Gk + s·hodgeWt (CXC:30; NNC:61).
- uM = laOf − parWt(anchor) − c₀·hodgeWt (CXC:34; NNC:63-67). The anchor is the (k−1)-th weight entry at each τ, so uM has that entry equal to 0 (NNC:63).
- FlatAt: μ(Gs(−c₀)) ≥ μ(uM) − mainT − C·unitE (CXC:135-136). UAt: μ(uM) ≥ −C·unitE (CXC:138).

## 2. Argument

### 2.1 The transport, read *(USN:160-209)*
1. Two Hodge Gram determinants:
   - det Γ = (2πx)^p·A², with A = ∏_i |t_{τ,i}|, the diagonal of the Borel frame t at τ;
   - det Δ = (2πx)^q·B² at τ̄.

   Here x = ‖relab(τ)(ξ₀)‖ = ‖relab(τ̄)(ξ₀)‖ (USN:160-171). Both come from Γ = π·Hm(Dv, Dv) with Hm diagonal, with entries 2‖ξ₀‖ in the unitary frame (USN:57-65).
2. ptN(s) = pnorm_flat = |φ|·∏√(dmin ratios) = |φ|·A·B⁻¹ (USN:89-99, 176-189). The q minors enter inverted (USN:186-189).
3. lieFacZ = exp((p−q)/2·log(2πx)) (USN:194-196, via sum_flatWt = q − p).
4. The final `ring` (USN:199-209) checks
   (p−q)/2·log 2πx + log|φ| + log A − log B = log|φ| + ½[p·log 2πx + 2log A] − ½[q·log 2πx + 2log B].

   This is an identity, so **the residual is 0.**

### 2.2 The same computation by hand, for a general weight *(mine)*
Write G = (G_{τ,i}) for a weight on the Lie directions.
- A section f of weight G scales like ∏_{τ,i} t_{τ,i}^{G_{τ,i}} under v_{τ,i} ↦ t·v_{τ,i}. Check: horizGen = (det frame)⁻¹ has model weight −1 (EFS:303-307).
- So its frame-independent Hodge norm is ‖f‖_H = |f(v)|·∏_{τ,i}‖v_{τ,i}‖_H^{−G_{τ,i}}.
- In the uniformisation, ‖v‖²_H = 2πx·‖v‖²_model for **every** direction: p-type at τ and q-type at τ̄ alike. The polarisation form is positive on all of Lie(A); only the weight distinguishes the two kinds.
- Hence ‖f‖_H = (2πx)^{−ΣG/2}·‖f‖_model = lieFacZ(G)·ptN. That is exactly homN (IPM:680-681).

**Per direction the exponent of 2πx is −G_{τ,i}/2.**
- For the flat weight: +½ on each of the p directions, −½ on each of the q directions, total (p−q)/2.
- For (κ_big on p, κ_small on q) it is −(Σκ_big + Σκ_small)/2, with the signs of the entries.
- The single factor lieFacZ is the right one because it is multiplicative in G (`lieFacZ_add`, IPM:672-674). It also tensors correctly under the FlatAt twist uM + parWt(anchor), so the twist adds no weight residual.

**Size check in rank one** *(mine)*. Take K, 𝒪_K and ξ₀ = −1/√−d (N𝔠_K = 1).
- Tr(ξ₀·x·ȳ) is a principal polarisation on 𝒪_K (E(1, ω) = ∓1).
- H = 2|ξ₀|·zw̄ = zw̄/area, and the Lean's Hodge Gram is π·H = π/area(𝒪_K) = 2π/√d = 2πx.
- With the (i/2π)-normalised Faltings metric, ‖∂_z‖² = π/area, so log‖dz‖² = log(area/π). That is the quantity whose conjugate mean is logΩ (NORMS §2.6, checked to 8 decimals).
- So the 2πx of lieFacZ is the conversion from the uniformisation coordinate to the Chowla–Selberg normalisation, not an extra factor. Without it the flat degree would lose (p−q)/2·log(2π/(N𝔠√d)) per section, an O(1)·(p−q) shift of the logΩ coefficient. With it, the shift is 0.

### 2.3 Where x drops out of the CM evaluation
- The `HasInfNorm` value at a CM point is evaluated by `frame_function_cm_number_field` (FCN:9). Its value is log|s r| + p/2(log n + ½log d) − q/2(log n′ + ½log d) + ½log|s(det gram_e)|.
  - n and n′ are Lie norms of the Chowla–Selberg curves, with mean −log n = γ + log(2π/√d) − L′/L (FDH:68-73, 98-103).
  - gram_e is the hermitian Gram of an 𝒪_E basis.
  - No x appears. The ξ₀-scaling lives in the algebraic gram_e and r, whose archimedean and finite contributions cancel in HMS by the product formula (HMS:8, t-relation hypotheses).
- The two descriptions of the same intrinsic `IsHodgeGram` (CM data in FCN, uniformisation in USN) are linked only through that shared definition. FCN's proof (`InfPlace.hasInfNorm_value`) was **not opened**.
- `rescale` (NFE:150-157) shows that a ConstSec's degree depends on x only through lieFacZ. FlatCore.Laws and Deep.Good.xiAbs pin x = xiR = |τ(ξ₀)| (USN hypothesis at :121; NNC:189-202), so only the true x is ever used.

### 2.4 Is the main coefficient confirmed? *(mine, combining §2.1 with [QPART §1.3])*
1. Per flat section, the degree in the homN metric is (p−q)/2·logΩ + q(log d − lrd E), exactly.
2. The twist by ∏_τ s_τ^{anc_τ} (parWt = Σ(−w)·flatWt, EFS:159-160) and the factor 2 of slope_sq give 2·Σanc·(p−q)/2·logΩ = Σ(p−q)·anc·logΩ = mainT. That equals l3m_j definitionally (AnchorAt, [COVOL]).
3. **So the coefficient (p_j − q_j)·w·logΩ is confirmed, with residual 0 from the transport.**

What remains:
- the booked q-term +2q·W·(log d − lrd E), the twist loss and the m₀·(½log 2π + lrd E) scalar loss, all absorbed in (11CA+83)·unitE [QPART];
- the unproved-by-me correctness of FCN and HMS.

### 2.5 B: the non-compactness link

**(i) What the covolume lattices are.**
- cuspW(G) = algebraic sections secZ(G) on the moduli Xo whose pull-back to every good complex uniformisation is holomorphic (IPM:425-427).
- Integrality is v(f) ≥ 0 on a set of valuations (latW, [COVOL]).
- No boundary or q-expansion condition appears in the definition. Cuspidality and boundedness enter through:
  - `cusp_forms_rapid_decay` in ExactRatio [QPART];
  - in-tree Koecher statements:
    - `koecher_principle_flagDomain_frequencies_nonneg`: if [E:ℚ]/2 > 1 and the section's norm is bounded on the thick region, its Fourier frequencies are ≥ 0 (`…/IwasawaDecomposition/KoecherPrincipleFlagDomainFrequenciesNonnegStatement.lean:6`, statement only);
    - `koecher_principle_unit_constant` (KUC:23-33): on a good deep cover with [E:ℚ]/2 > 2, a bounded invertible weight-0 section is a constant multiple of the component idempotent. Its proof ignores its `PublishedHodgeBundleTheorems` premise (`intro _`, KUC:24) and uses the in-tree `exists_eq_smul_idem_of_bdd`.
- *(mine)* The hypothesis "[E:ℚ]/2 > 1 or 2", i.e. more than one or two CM places, plays the role of Koecher's codimension condition. That fits Res_{F/ℚ}U(p,q) with [F:ℚ] ≥ 2, the Hilbert-type situation where the boundary has codimension ≥ 2. On live hosts f ≈ x^{2+8ε} [VOLUME], so this holds.

**(ii) The deep cover** (NNC:162-202; [VOLUME §5]).
- `Deep T j` is the same layer-j Shimura variety, with:
  - a coefficient field c′ ⊇ c;
  - deeper level, with pd = 15^e and level K at g₀·g₁·pd;
  - complex uniformisations U σ;
  - trivial central character on Γ;
  - |τ(ξ₀)| = xiR;
  - geometrically connected components (FnAlgClosed).
- *(mine)* On such a cover every component carries a nowhere-vanishing flat section of each flatWt τ (FlatExistsAt requires Nonempty on every Z, EFS:746-747). That is what lets the anchor part of the weight be removed exactly at cost flatDegVal.
- RingAt (CXC:116-117) charges ≤ 2b for passing from the layer lattice to the cover. MapsAt, RkAt and GminAt (CXC:119-131) compare Gk with Gs(−c₀) on Y. So one cover per layer, with no induction [HS; VOLUME].

**(iii) The volume side** (GO:55-65; TO:58-119; HL:33-139).
- GoodOrigin = TowerOrigin + smooth + flat + reference models + ampleness. Each RootOrigin contains:
  - a `HodgeCpt` 𝔐 (HL:33-74): a normal scheme X with f : X → Y.X, generically a finite cover (IsCover, Fl.deg), a semi-abelian scheme t with SABMap t → Y.t, Lie lattices patched at S, and full p^R-torsion.
  - 𝔐.Interior z :⇔ centre z ∈ abLocus(t.G), the locus where the group is proper (HL:96-97; `…/ToroidalCompactification/IsGrpPullback.lean:14-15`). *(mine)* So X plays the role of a toroidal-type compactification of a cover, with the Mumford/Faltings–Chai/Lan semi-abelian extension. The Lean does not name it or tie it to a fan.
  - Hodge lines `sing r` whose SecNorm equals the graded Hodge norm only at interior points (`IsHodgeLine`, HL:135-139);
  - a log-singular relation `fund_sing` with potential Sys.ph on the open part (TO:98-100);
  - a regularised smooth family `fund_reg` for 0 < t ≤ t₀ (TO:101-102).
- The t → 0 convergence axioms I1–I3 and the semipositivity and nef axioms are verified inside `volumeTheoremX_of_inputs` [VOLUME §2].
- *(mine)* This is Burgos–Kramer–Kühn in spirit (log-singular metrics as limits of smooth ones), but no BKK, Mumford-proportionality or Lan statement appears as a premise of GoodOrigin. `T.Proportional` and `VolEq` are tower axioms derived in-tree [VOLUME].

**(iv) Inputs.**
- `goodTower_and_volume` (GTV:36-49) and `deepStR_of_volume` (DSV:21-58) take `Top.Given` (GO:67-72) and **use** its components: ResK (resolution), FarguesHodgeTate, GagaSections and PB.Inputs (GTV:41-44).
- Given also contains ToroidalLevelCompatibility, ToroidalHeckeCompatibility, SemiAbelianHomExtension, SlopeBoundSt, Prov.HS and others.
- DSV also takes NefRR, ArithIntersectionSystemStatement and BirationalPullbackPushforwardFormula.
- Their Lean statements and suppliers were **not read**, so I cannot match them to Lan's toroidal theory. Existence of a good origin is `exists_good_root_tower` (GTV:46-47), not opened.

**(v) Why one side suffices.**
- DIV uses only L3: lcv(M_j)/D ≤ l3 [COVOL].
- The chain is lcv/D ≤ −μ(latGood) ≤ −muCore + … ≤ −μ(latDeep) + 2b ≤ −μ(Gs(−c₀)) + … ≤ −μ(uM) + mainT + C·unitE ≤ mainT + 2C·unitE (CXC:116-138; [VOLUME §5]).
- Every link is a **lower** bound on a slope. VolumeTheoremX (mean slope ≥ −C·…) enters only through UAt, a lower bound on μ(uM) [VOLUME §5; HS]. An upper volume bound would only be needed for a two-sided covolume statement, which DIV never uses.

### 2.6 C: the direction of the μ(uM) bound *(mine)*
- −μ(uM) appears with coefficient +1 in the upper bound for lcv(M_j). So an upper bound on lcv needs a lower bound on μ(uM), and UAt supplies exactly that (CXC:138).
- **The direction is right.**
- As QPART says, the cost is that the q-term cannot be isolated as a *true* lower bound on lcv(M_j). That would need μ(uM) ≤ …, which is not in the tree. This does not affect validity.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `homN_eq_exp_hodge` | USN:121-209 | lieFacZ·ptN = exp(log\|φ\| + ½log det Γ − ½log det Δ) | the transport; residual 0 | core (read to the end) |
| `exists_gram_det` | USN:33-87 | Hodge Gram in the uniformisation frame = (2π‖ξ₀‖)·YᴴY | source of 2πx per direction | core (read) |
| `sum_flatWt`, `lieFacZ`, `homN` | NFE:159; IPM:664-681 | ΣG(flatWt) = q − p; signed weight factor | definitions | definition (read) |
| `exists_constSec` | ECS:40-91 | flat ConstSec with deg = (p−q)/2·Re logΩ | builds EFS's flat section | glue (read) |
| `degree_frames`, `corr`, `shift` | KPF:16-146 | finite-place shift by q(log d − lrd E) | relabelling between FDS and KFB | glue (read) |
| `frame_function_cm_number_field` (`hasInfNorm_value`) | FCN:9 | Hodge value at a CM point via n, n′, gram_e | where x disappears | core; **proof not opened** |
| `koecher_principle_unit_constant` | KUC:23-33 | bounded weight-0 units are constant ([E:ℚ]/2 > 2) | boundary control | standard (Koecher); proved in-tree |
| `koecher_principle_flagDomain_frequencies_nonneg` | `…KoecherPrincipleFlagDomainFrequenciesNonnegStatement.lean:6` | bounded ⇒ nonnegative frequencies | boundary control | standard; statement only |
| `RootOrigin`, `HodgeCpt`, `GoodOrigin` | TO:58-119; HL:33-139; GO:55-65 | compactifying cover with semi-abelian extension and log-singular Hodge lines | non-compactness on the volume side | definition (read) |
| `Top.Given` | GO:67-72 | bundle of geometric inputs | used by GTV and DSV | **suppliers not traced** |
| `abelian_cm_comp_laws_bound`, `hermitian_geometric_hypothesis_holds`, `exists_good_root_tower` | DSV:24; [HS]; GTV:47 | the tower ↔ cusp-form-lattice link | where the open/compact comparison sits | **definition to unfold; not read** |

## 4. Oddities
1. **Earlier wording corrected.** "(2πx)^{−|wt|/2}" (NORMS) should read (2πx)^{−ΣG/2} with signed G. QPART §4.1's open point is closed: there is no sign problem.
2. **The name `degree_frames` misleads.** It is a finite-place relabelling; the real transport is `homN_eq_exp_hodge`.
3. Two independent descriptions of `IsHodgeGram`, by CM data (FCN) and by the uniformisation (USN), are reconciled only by both being proved for the same definition. A wrong constant in either proof would make a proved lemma false, not shift DIV silently.
4. `koecher_principle_unit_constant` discards its Published premise (KUC:24). This is harmless.
5. Toroidal compactification never appears by name in RootOrigin. "Interior = proper locus" plus the semi-abelian extension is the only trace.

## 5. Coverage
**Audit files read:** PROTOCOL; MAIN-ARGUMENT §0, §5, §9.8-§9.10; NODE-QPART, NORMS, COVOL, HS and VOLUME in full; NODE-DIVKEY and NODE-STEPE by grep (logΩ, covolume, lieFac).

**Lean read:**
- USN:1-211; the USN statement file; ECS:1-93; KPF:1-148; the KFB grep lines 13-14, 20, 24;
- ICM:59-84; FDS:1-21; FDH:55-118; FCN:9; HMS:8;
- EFS:140-160, 300-350, 440-460, 505-520, 740-760; NFE:150-175; IPM:420-430, 655-690;
- CXC:15-50, 100-175; NNC:55-100, 160-202;
- GO:1-74; TO:1-128; HL:1-140; IsGrpPullback.lean:10-20;
- GTX:18-37; GTV:30-49; DSV:21-60; KUC:1-35.

**Greps run:**
- `degree_frames|exists_constSec|degree_of_flatOnModel|kronecker_character_frame_bound`;
- `unf_section_norm_bound_at_height`; `FlatCore.*Laws`; `sum_flatWt|def flatWt|modelWt_flatWt|ConstSec|def deg|flatDegVal`;
- `structure RootOrigin|TowerOrigin`; `HodgeCpt`; `abLocus`; `frame_function_cm_number_field`;
- `koecher` (case-insensitive); `def uM`; `Gs|Gk|cZero|anchor`; `exists_good_root_tower|GoodTowerExistsX`.

**Not opened:**
- `InfPlace.hasInfNorm_value`; `deg_eq_of_local_two_curves`;
- `abelian_cm_comp_laws_bound`; `good_datum_parameters`; `exists_good_root_tower`; `hermitian_geometric_hypothesis_holds`;
- the Koecher proofs; the suppliers of `Top.Given`, `NefRR`, `ArithIntersectionSystemStatement` and `BirationalPullbackPushforwardFormula`;
- `cusp_forms_rapid_decay`.
