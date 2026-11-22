# NODE-INDEXBUDGET: the global r-budget behind `HasIndexBound` (WeightAlgebra.Concl → theorem_zero_of_refined_inputs → Heights)

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.

Abbreviations:
- `WA` = `Formalism/SharpRestriction/Divisibility/WeightAlgebra.lean`
- `HIB` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasIndexBoundOfRuns.lean`
- `ONL` = `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean`
- `RCT` = `Development/AbelianVarietyTheory/Definitions/Divisors/RealisedChainTorusEq.lean`
- `FTK` = `Development/AbelianVarietyTheory/Definitions/Jets/EmbShortThLeThetaPlain.lean`
- `SCP` = `Formalism/SharpRestriction/Divisibility/AbelianOpenPart/OEOsInjective.lean` (`scalOfP`)
- `SO` = `Formalism/DivisorInequality/StatementObj.lean`
- `GPB/` = `Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/`
  - `TZ` = `GPB/TheoremZeroOfRefinedInputs.lean`, `CB4` = `GPB/CombBound4Of.lean`, `PIC` = `GPB/PublishedIntClosHolds.lean`
  - `WPS` = `GPB/WeightedPrimeSumBound.lean`, `LPF` = `GPB/LiftIndexPowFourLeDegree.lean`, `TSL` = `GPB/TheoremZeroSplitOfLocal.lean`, `JWM` = `GPB/JWMggWMem.lean`
- `CI4` = `Development/AbelianVarietyTheory/Definitions/HeightFunctions/ConclOfInputs4.lean`
- `HP/` = `Development/AbelianVarietyTheory/Proofs/HeightProofs/`
  - `ETR` = `HP/ExistsThresholdRunHolds.lean`, `I4R` = `HP/IndexBoundChosenFamilyOfIntrinsicHypotheses.lean`
  - `INR` = `HP/ExistsIndexBoundHypothesesWithNetAllValuedPoints.lean`, `EPH` = `HP/ExistsPrimeDataCurveLiftingHeightBounds.lean`
  - `ACM` = `HP/AuxiliaryCuspFormConstantMonotone.lean`, `HIL` = `HP/HeightInequalitiesIndefiniteLiftIndex.lean`
- `HT/` = `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/`
  - `HTM` = `HT/HtMain.lean`, `NNF` = `HT/NlNonnegFin.lean`, `HDD` = `HT/HDiscDefs.lean`, `HDA` = `HT/HDiscA.lean`, `HDB` = `HT/HDiscB.lean`, `HTD` = `HT/HtDefs.lean`
- `LAM` = `Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/` (`IntegralFormsLogSupNormLowerBoundAbsolute.lean`, `MeanLogSupNormLowerBoundCmFrameNonvanishing.lean`)
- `WF` = `Formalism/SharpRestriction/Divisibility/WeightFamilies.lean`

## 0. Verdicts

**No ESCALATE.**
- The argument is not circular. The index budget uses no covolume of M_j, no LowAt/HSAt and no Rallis scalar.
- It fits the error budget, but only at the "m·B0" level that NODE-ACCOUNT already marks TIGHT. It is not small by a power of x.
- One correction to NODE-TWSET: **the budget does not bound the theta-image index idx(M_j : θ_jT_j) at all.** It bounds a different, twist-independent sublattice (§2a, Q5).

| Q | Answer | Status |
|---|---|---|
| 1 | r(λ) = C(T−1, dimY)·(Ila(λ) + Net term) + Gauss content of M_ka at λ + len_λ(Qm/⟨th_i⟩). It bounds the **λ-adic index of Θ in M_ka**. Here M_ka is the lattice of integral cusp forms of weight ka on layer j, and Θ is the span of explicit products (T-fold products of short weight-wL forms) × (short weight-wF forms) (WA:156-159). The constant β is rk(M_ka)·f·m·b·de2. | Concl, HIB and TZ were read in full |
| 2 | Mechanism (i)+(iii), not (ii). It is a **Noether-normalisation plus discriminant-height argument on a generic curve.** Ila is the index of the restricted forms th′_i in the integral sections of a generic complete-intersection curve over K_λ(T). It is bounded via 2·Ila ≤ ord_λ(Δ) + (correction), where Δ = det of the trace form of the th′_i (HDD:28-32, HDA:20-24). Σ_λ ord_λ(Δ)·log Nλ is then bounded by the product formula and Mahler-measure heights: Hadamard (del·log del) + Σ log sup‖th′_i‖ + the height of an auxiliary section (HDB:24-33). The Gauss-content piece uses the same mechanism (a nonzero determinant polynomial and the product formula), with a lower bound for sup norms of nonzero integral forms (LAMwAt) proved by evaluation at a CM point. | top level and HT reductions read; `disc_product`, `heights_arith`, `deepCore`, `quotC` statement only or not opened |
| 2′ | Circularity. Three quantities enter the slope: lcv(M_j) (COVOL), λ_j (not on this path), and the index. BoundsMu takes **index bounds and lcv(M_j) as separate hypotheses** (SO:52-77). The index bound's inputs are sup-norm upper bounds of explicit generators, the CM-point lower bound LAMwAt, and numeric page conditions. None of them mentions lcv, LowAt or slope. | read (inputs listed in §3) |
| 3 | Per layer Σ_v lw·r ≤ nZ·f·m·b·de2. In ON it enters divided by |P:U|·D, and nZ/|P:U| ≤ 3D, so the cost is ≤ 12·f·m·b (ONL:769-800, 851-864). This goes into E1 = CE·x^ε(B0+Nc). Summed over m layers it is ≈ f·m²·b·x^{O(ε)} ≈ m·B0 ≈ x^{3+O(ε)}b. That is budget size, the same order as the covolume error (NODE-ACCOUNT §3(ii)). f ≈ x^{2+8ε} is **not** x^{O(ε)}. de2 ∈ [x^{−ε}, 1] is dropped (ONL:791-794). An a·log a-type term **does** occur, ka.size·(1+log ka.size)·PP0 from LAMwAt and del·log del from Hadamard. It is not fatal: every such term carries a factor rz, rq or del with C(T−1,dimY)·del ≤ rk and rz, rq ≤ 22·dimY²·rk/T, and T ≥ x^{Bx}·PPv⁴·dimY³·k·f/(m·de2) (WA:417). So size·log(size)/T ≲ m·b·de2·x^{O(ε)}/x^{Bx}. log(size) ≈ x^ε, not log(a!). | the numerics are proved (`sumGC4` → `sumGP4` → `pvs_core4`); I checked the shape, not every constant |
| 4 | Literature: Krull–Akizuki / finiteness of the integral closure of a DVR (`PublishedIntClos`, proved in-tree, PIC:14-18, 273-275); Hadamard's inequality, Gauss's lemma / product formula, Mahler-measure height of polynomials *(inferred inside `disc_product`, `heights_arith`, not opened)*; Chowla–Selberg (logΩ, via LAM). **No** Kudla–Rapoport, Gross–Keating, Bost/Gillet–Soulé, arithmetic Hilbert–Samuel or Faltings height is used on this path. | |
| 5 | The budget holds at **every** place, but for lix(Ms, Th), where Th = the explicit product lattice Θ, not for θT. The step Th → θ_j(μ)T_j(μ) goes through the mirabolic projection chain Th ≤ σ·ThK, Th0, eJ, X₃ ⊆ Im = e·θ′(Mt). It needs LeafTW1/TW2 (ONL:284-294), and those are stated only at w ∈ Tw, for the twisted tuple μ(w). So twisting is what makes the theta image contain the test lattice (up to ε0 ≤ 2/p²). The global budget pays only for "test lattice vs integral lattice". There is no redundancy. | ONL:405-450, 605-650 read; suppliers of TW1/TW2 not opened |

## 1. Statements

**`Concl X S ka wL wF T nus β`** (WA:424-434, read). There is r : {finite places λ of K_O} → ℝ≥0 with Σ' r(λ)·log Nλ ≤ β, such that for every λ, every e ∈ ℤ with T·nus(λ) ≤ e, and every K_λ-subspace V′ ⊆ (M_ka)_λ ⊗ K_λ:

  len_{O_λ}( (M_ka,λ ∩ V′) / (Θ_λ ∩ V′) ) ≤ e·dim V′ + r(λ).

The objects:
- M_ka = `Msup ka` = `B.Mlat j ka` embedded (WA:143). These are the cusp forms F of weight ka with vAt_{λ,y}(F) ≥ 0 at all chart points y (WA:111).
- Θ = `Theta` (WA:156-159) = ⟨W⟩^T·Thc_F + ⟨W⟩^{T−dimY}·Thc_0 + Thc_K, with:
  - W = sW·⟨short weight-wL forms⟩ (WA:145);
  - Thc_w = s·(g₀g₁)^{f·r·n_w}·⟨short forms⟩ (WA:147-149).
- The scalars sW, sF, s0, sK (SCP:72-82) are nnW·QS^·q^·d^·pde^(·). They are absorbed by e: `eLa` = ⌈T(nus + [bad])⌉ (WA:194-195), and in ON by e0 = (E − v(σ))/ram.
- qlen = `Module.length` of the quotient (WA:186-187).

**`hasIndexBound_of_runs`** (HIB:129-190, read). For the realised OnObj O, `HasIndexBound O` holds. HasIndexBound (RCT:77-78) = ∃ Th1 a r1 r2 de2, `LatticeIndexBoundAtPairs` (ONL:262-271). The proof sets Th1 := O.Th (HIB:184). The chain:
- `exists_rem_of_concl` (HIB:51-87) transports Concl to the coordinate lattices.
- O.Ms i = spanK(M_ka) and O.Th v i = spanK{F : F ∈ Θ} (FTK:65-69, `FormTieK.Ms_eq/Th_eq`).
- β = rk·a·b·c·d with (a,b,c,d) = (f, m, b, de2) (HIB:149).
- de2 = L.de2 (HIB:184), the thick density, with 0 < de2 ≤ 1 (DP2:136-140).
- Conclusion: for all v and all W, lix(cut W Ms, cut W Th) ≤ E(v)·dim W + ρ(v), with Σ_{v∈S′} lw·ρ ≤ nZ·f·m·b·de2 for every finite S′. Here nZ = rk.
- Two remainders r1, r2 (pde vs non-pde places) come from the two runs (HIB:136-170).

**`theorem_zero_of_refined_inputs`** (TZ:8-31, read) proves `Conclusion1OfComb4` (CB4:74-101): under HypC, LatAt, sup/L², LAMwAt, QAt, Tied*, Deep*, Share*, PolyDom4, and (for j < m) ∃Qf with CombBound4 ∧ **Heights**, we get Concl(…, rk·f·m·b·de2).
- For j < m: r := rLa (PIC:371-376), the local inequality is `localBound` (JWM:149-185), and the sum is `rLa_tsum_le_comb` (TSL:69-89) followed by `sumGC4` (LPF:405-422).
- For j = m (top layer, used: HIB uses j = i+1 ≤ m), TZ:30 returns the hypothesis `ConclAtM`. It is discharged in `inputs4_of_inputsR` (I4R:13-49) by `theorem_zero_of_named_inputs` (not opened) with the definite-case Heights.

**r(λ) = rLa** (PIC:371-376):

  r(λ) = C(T−1, dimY)·( Ila(λ) + [j<m]·T·c/(2·iet)·Net(λ) ) + gaussC(M_ka, zc, λ) + len_λ( Qm / ⟨th_i⟩ ).

- **Ila(λ)** (PIC:328-329) = len_{Op}( A0 / ⟨tL_i⟩ ∩ A0 ).
  - A0 = `ballO` = the elements of the section-sheaf quotient over the generic curve OsK whose order at each closed point ζ is ≥ −c(ζ), where c(ζ) = e_ζ·vAt(g0) (PIC:313-326, 350-364).
  - tL_i = restrictions of the weight-wF forms th′_i (PIC:291-294).
  - `InBasis` (PIC:296-297) says the tL_i form a K_λ(T)-basis.
  - So Ila is the index of the restricted forms in the integral sections of a generic curve at λ.
- **Net(λ)** (PIC:333-334) = Σ_ζ e_ζ·f_ζ·vAt(et). This is the λ-divisor of the auxiliary form et along the curve.
- **gaussC** is the λ-Gauss content of the coefficients zc of the polynomial zPoly(w, alz, th0) (TiedZ, WPS:~105-108). Its determinant `detPoly` is ≠ 0.
- **Qm/⟨th_i⟩** is the length of a quotient of M_ka by MggK, controlled by `QAt` (WPS:41-54).

**`Heights Qf Gc PH Prw Pet`** (PIC:378-387):

  2·Σ_λ Ila·log Nλ ≤ del·log del + 2·Σ_i meanLogSup(th′_i) + (8/3)dimY(dimY+4)·del·Prw·|wL| + 2(dimY+4)(dimY+1)·del·(2Gc+6PH)·|wL|.

There is an analogous bound for Σ Net·log N/iet.

## 2. Argument

**(a) Where the index of θT is actually bounded (Q5).** `local_bound` (ONL:405-450, read) bounds idx_v(M_j, θ_j(t)T_j(t)) at a place v by
  (E − v(σ) + v(|U|))·dW + (r + nZ·v(|U|))/|P:U| + ram·ε0.
It does so by chaining five steps:
1. lix(Ms, Th1 = Th) ≤ E·dim + r. This is the budget.
2. Th ≤ σ·ThK (LeafLemmaS).
3. |U|·(ThK ∩ eig) ≤ Th0 (LeafData).
4. eJ = e(ThJ), and lix(Ms∩Zg, X₃) ≤ lix(Ms∩Zg, eJ) + ram·ε0 (LeafTW1).
5. X₃ ⊆ Im = e·θ′(Mt), where φ(θ(t)T(t)) = ImageLattice (LeafTW2, TjId; ONL:213-214, 241-246).

`on_core` applies `local_bound` only for w ∈ Tw with t = μ(w) (ONL:640-659). Step 1 is twist-independent and holds at all v. Steps 4-5 are twist-dependent hypotheses at Tw. *(inferred)* At a W1 place the untwisted image θ(μ0)T(μ0) does not contain the projected test lattice; the twist ψ_w is chosen so that it does, at cost ε0 ≤ 2/p² per place (ONL:293-294). Off Tw nothing is needed, because the untwisted index is 0 by the definition of Tw (NODE-TWSET).

**(b) The local inequality (`localBound`, JWM:149-185; statement read, proof via `localIdx` not opened).** *(inferred from its hypotheses)*
- ka = wF + T·wL (`hka`), and forms of weight ka are expanded in the monomials secPow(al)·sec0^{T−|al|}·th′_i with |al| < a0 = T − dimY (`hCM`), plus the rz extra elements zK.
- *(inferred)* This is a Noether normalisation. The dimY + 1 forms w generate a polynomial subring, and the th′_i are a basis of the section module over it on the generic curve.
- So the local index of Θ in M_ka ∩ V′ is at most:
  - e·dim V′ (the depth T·ν, i.e. the w's may vanish to order ν at λ);
  - plus (number of monomials) × (index of the basis on the curve) = C(T−1, dimY)·Ila (`hLB`), plus pole-order terms (`hLP`, i.e. the Net term);
  - plus the Gauss content of the zK-polynomial;
  - plus the MggK quotient length.

**(c) Why Σ_λ Ila·log Nλ is globally bounded (the Heights supplier).** The chain:
- `inputsNet_recPlus` (INR:79-140) gets `Heights` from `exists_primeData_curve_lifting_heightBounds`. Its proof `exists_primeData_heights_of` (ACM:96-200) applies `heights_indefinite` (j < m, HIL:197-413) or `heights_definite` (j = m, not opened).
- `heights_indefinite` builds a `Data` record d (generic frames, CM base point, generic section `genericSection_of_axioms`). It then applies `Data.heights` (HTM:33-159), whose Ila clause comes from `disc` (NNF:141-160) → `disc_one` (NNF:86-139):
  1. **Local** (`disc_lattice`, HDA:20-24): 2·IL(λ) ≤ ord_λ(Δ) + 2·NlaG(λ). Here Δ = det[Σ_c Tr(b_k b_l)] is the discriminant of the trace form of the del restricted forms, over the function field KTf (HDD:28-32). gOrd is the λ-adic order of an element of K(T) via the uniformiser and units of the Gauss-valuation ring (HDD:22-26). *(inferred)* This is disc(sublattice) = idx²·disc(integral closure), with disc(integral closure) ≥ the conductor correction NlaG.
  2. **Global** (`disc_global`, HDB:24-33): Σ_λ (ord_λ Δ + 2NlaG)·log Nλ/[K:ℚ] ≤ del·log del + 2Σ_k meanLog sup(th′_k) + 2D·aG·(log(N+1)+½) + 2·Hgt(ta′). *(inferred, `disc_product` not opened)* Product formula for Δ ∈ K(T)^×: finite orders = −(archimedean log|Δ|), averaged over the sphere (`blockSphereProb`, HTD:56-58), i.e. a Mahler measure, plus the polynomial height h0. Hadamard then gives |Δ| ≤ del^{del/2}·Π sup²(th′_k).
  3. Hgt(ta′) is bounded by h_seven (`HSeven.lean:22-45`, statement read): ≤ (D+4)·HL + del·PI4·D·|wL| + … Here HL is bounded by HgtMM + … and `HeightMinMaxFormula` gives HgtMM = Σ_c h0(F_c) + del·H_N/2 (`HeightMinMaxFormula.lean:19-25`). `sum_logHeight_upper_bound` (`SumLogHeightUpperBound.lean:78-90`) gives Σ h0(F_c) ≤ (D+2)·del·(PP0′·|wL| + sup + log(N+1) + 1), which uses `HtLAM`.

**The integral model and the section.**
- The "model" is not a regular model of a Shimura variety. It is the family of valuations vAt_{λ,y} at the points of `ModuliIntegralCharts` (WA:97-111); integrality is defined by them.
- The relevant 1-dimensional object is the generic curve OsK over K_λ(T), with its DVR points (`PublishedIntClos`).
- The "section" is the discriminant Δ ∈ K(T) of the restricted weight-wF forms. For the Gauss-content piece it is the nonzero determinant polynomial detPoly(zc) (`deepCore`, `LogSupSumLeOfNonvanishingDetLimit.lean:590`, not opened).

**(d) The archimedean inputs** (all hypotheses of `heights_indefinite`, threaded from `PageOK`/`GenOK`; HIL:197-201 binder list):
- TiedW, TiedTh: log sup‖w_k‖, log sup‖th′_i‖ ≤ Gc·|w| (WPS:~95-104);
- EtArch and the frame lower bound −log√(Σ‖w_k‖²) ≤ tableLineDegreeFive·DF + c·φ (archimedean no-common-zero);
- LAMwAt (WPS:37-39): meanLogSup F ≥ −PP0·(1+log|ka|)·|ka| for every nonzero integral F, with PP0 = C·(fr + L + log d_E + |logΩ|)² (WF:30-31).
  - LAMwAt is proved (`lamwAt_absolute` → `meanLogSup_lowerBound`, LAM files, read at the top level) by evaluating F at a good CM point. A nonzero algebraic frame-polynomial value G gets local lower bounds at every prime and an archimedean bound via Chowla–Selberg (`lamDegSt_logOm`). This is a Liouville/product-formula argument.

**(e) Size (Q3).** `sumGC4` (LPF:405-422) is a closed theorem: binomial·(ΣIla + Net) + rz·(2Gc + Prw + PP0·(1+log|ka|) + 1.5(Pd+PO))·|ka| + 2rq·PPv·|ka| ≤ rk·f·m·b·de2. The terms close as follows:
- ShareRd: C(T−1, dimY)·del ≤ rk (WPS:92).
- ShareRhoP/T: rq, rz ≲ 22·dimY²·rk/T (CB4:12, WPS:96).
- |wL| ≤ 2|ka|/T and |ka| ≤ CK·k·f·b (WA:348, H4 WA:400-401).
- H3: T ≥ x^{Bx}·PPv⁴·dimY³·k·f/(m·de2) (WA:417).
- Hence every term is ≲ rk·(polylog)·k·f·b/T ≤ rk·m·b·de2·x^{O(ε)−Bx}.
- de2 enters only by forcing T to be larger. All "log" factors are log|ka| ≈ x^ε, log del ≤ 1041·Zb³, or PPv = C·(f·r·L)^A. These are polynomial in f·r and in L = x^ε. **No factorial and no Σ_p v_p(a!)·log p appears.** The a·log a-type loss of a weight-a form is diluted by the T-fold product structure.

## 3. Children

| # | Name | file:line | Statement | Role | Weight / status |
|---|---|---|---|---|---|
| 1 | `exists_rem_of_concl`, `exists_rem_of_tie` | HIB:51, 95 | Concl ⇒ coordinate-lattice index bound with Σ lw·ρ ≤ nZ·f·m·b·de2 | transport | glue; read |
| 2 | `local_bound`, `on_core` | ONL:405, 605 | idx(M_j, θ(μ)T(μ)) ≤ depth + r/|P:U| + ε0, at Tw | combines the budget with the twist | core; read |
| 3 | LeafTW1/TW2 suppliers (`leafTW2_of_isRec`, TwistSt) | `DivisorProofs/GoodLiftOntoOfBase.lean:65`; `ExportSt.lean:40` | twisted θ-image contains the projected test lattice | what twisting buys | core; **not opened** |
| 4 | `localBound` (→ `localIdx`, `lenBase_all`, `lenPoleL_all`) | JWM:149 | local index of Θ in M_ka ≤ e·dim + rLa | Noether normalisation count | core; statement read |
| 5 | `disc_lattice` | HDA:20 | 2·IL ≤ ord_λ(disc) + 2·NlaG | local discriminant/index | standard (disc = idx²·disc); statement read |
| 6 | `disc_global` / `disc_product` / `heights_arith` | HDB:24; HtArith.lean:7 | Σ ord(disc)·log N ≤ Hadamard + sup norms + auxiliary heights | product formula + Hadamard | standard; statement read, bodies not opened |
| 7 | `h_seven`, `HeightMinMaxFormula`, `sum_logHeight_upper_bound` | HSeven:22; HMM:19; SLHU:78 | auxiliary-section heights ≤ sup norms + LAM terms | closes Hgt(ta′) | core-ish; statements read |
| 8 | `lamwAt_absolute` ← `meanLogSup_lowerBound` | LAM:28; LAM-CM:49 | nonzero integral forms have meanLogSup ≥ −PP0(1+log|w|)|w| | CM-point Liouville | core; top level read, `cmPoint_lowerBound_free`, `localLowerBound_cmPoint…`, `archimedeanHypothesis…` statement only |
| 9 | `deepC`/`deepCore`; `quotC` ← `QAt` (`recursive_page_lattice_bound`) | TSL:13; `LogSupSumLe…:590` | Gauss-content and quotient-length sums | other two r pieces | statements only; QAt supplier not opened |
| 10 | `sumGC4` → `sumGP4` → `pvs_core4` | LPF:405 | the numerics close to rk·f·m·b·de2 | size | proved; shape checked |
| 11 | `theorem_zero_of_named_inputs`, `heights_definite` | used I4R:47, EPH | top layer j = m | definite case | **not opened** |
| 12 | `integralClosure_dvr'` (`PublishedIntClos`) | PIC:14, 273 | integral closure of a DVR in a finite reduced algebra is finite, with DVR localisations | Krull–Akizuki | standard; proved in-tree |

## 4. Oddities

1. **NODE-TWSET §2(c)-(d) is slightly misstated.**
   - What the budget shows: "the λ-adic index of the explicit product lattice Θ in M_ka is ≤ depth·dim + r(λ), with Σ r·log N ≤ rk·f·m·b·de2".
   - What it does not show: "the theta-type test forms span M_j". The theta lift θ_jT_j plays no part in it.
   - Θ is built from short cusp forms, and the word "Theta" is a name only.
   - The step to θ_jT_j is the twist-dependent mirabolic chain (TW1/TW2), and its suppliers were not opened. That chain, not the budget, is where any arithmetic content about congruence primes in W1 lives.
2. **The budget is at budget size, with no x^{−δ} margin** (§0, Q3). It sits in the same "m·B0" bucket as the covolume error. Any constant blow-up in CE is fatal only together with the other tight terms.
3. **Nat.choose(T−1, dimY) multiplies Ila.** This is fine because ShareRd makes binomial·del ≤ rk. ShareRd is a hypothesis carried in from `sharesAt_all` (`cuspFormBasisShares_{in,}definite_liftIndex`, statement only). If del were the full rank of weight-wF forms, ShareRd would be a nontrivial dimension inequality, (T−1 choose dimY)·dim S_wF ≤ dim S_{wF+T·wL}. *(inferred)* That is a Hilbert-function lower bound.
4. Concl at the top layer j = m is a hypothesis field (`ConclAtM`, CB4:44-47) of Inputs4. It is discharged by `theorem_zero_of_named_inputs` (not opened), not by TZ.
5. de2 plays no role in the ON estimate: it is bounded by 1 (ONL:791-794). It matters only upstream, through T in H3.
6. `PublishedIntClos` is named "Published" but is proved in-tree (PIC:273-275). It is standard.

## 5. Coverage

Read:
- PROTOCOL; NODE-TWSET, NODE-LARGETW (all); NODE-COVOL §0-1 head; NODE-HS §0-1(a); NODE-CONGMOD §2a; NODE-SLOPE §2(d); NODE-ACCOUNT §1-3(ii).
- NODE-VOLUME: grep only.
- WA:128-450; HIB:1-194; RCT:60-110; FTK:30-110; SCP:60-100; SO:40-80.
- ONL:140-420, 420-520, 600-900; TZ (all); CB4:1-101; PIC:1-40, 270-404; WPS:1-120.
- LPF:360-424; TSL:69-110; JWM:149-185; CI4:1-120; ETR:1-80; I4R:13-49; INR:1-140; EPH; ACM:80-200; HIL:197-413.
- HTM:1-159; NNF:86-160; HDD:1-36; HDA:20-40; HDB:24-40; HTD:40-70; HSeven:22-45; SLHU:78-90; HMM:19-25.
- WF:18-40; LAM files (both: 33 lines; :49-91); MeanLogSupNormLowerBoundOfCoreLawsStatement.

Greps run:
- `def HasIndexBound|def LatticeIndexBoundAtPairs|theorem on_of_leaves`; `structure FormTieK|def scalOfP|structure OnObj`;
- `def Conclusion1OfComb4|theorem sumGC4|theorem rLa_tsum_le_comb|theorem localBound|def rLa|def Heights|def PolyDom4|…`;
- `theorem inputs4_of_inputsR|inputsNet_recPlus`; `exists_primeData_heights`; `theorem heights |genericSection_of_axioms|HtLAM|FinitePlaceHyp|HtConcl|LAMwAt`;
- `theorem disc |h_seven|HeightMinMaxFormula|sum_logHeight_upper_bound|h_six|heights_arith`; `disc_global|disc_lattice|def De|NlaG|gOrd`;
- `def PPv|PP0v|RRv`; `ShareRd|ShareRhoP|DeepLogD|zBase|a0`; `LeafTW2|HasTwistBound`; `meanLogSupNorm_lower_bound_of_coreLaws`.

Not opened:
- `localIdx`, `lenBase_all`, `lenPoleL_all`, `disc_product`, `disc_at`, `heights_arith`, `deepCore`, `quotC`/QAt supplier, `theorem_zero_of_named_inputs`, `heights_definite`;
- the TW1/TW2 suppliers, `cuspFormBasisShares_*`, `exists_admissible_thetaLatticeGenerators`;
- the CM-point lemmas inside LAM, `pvs_core4` body.
