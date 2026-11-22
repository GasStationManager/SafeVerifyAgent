# NODE-ADM11: the divisibility losses E (adm11), the floor (NprimeMuR), and adm2 on every branch

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(inferred)* = my reading. [NODE] = taken from that node, not re-read. Nothing was compiled or run.

Abbreviations:
- `LQP` = `Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean`; `WDS` = `Formalism/SharpRestriction/Divisibility/WeightDegreeSizes.lean`
- `DE` = `Formalism/LocalRingCardinality/DataErr.lean`; `DDD` = `Formalism/LocalRingCardinality/DataDIVDefs.lean`
- `DP` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/`; `OLS` = `DP/OtherLossSum.lean`; `LSP` = `DP/LossSumPrimes.lean`
- `GI` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`
- `EL` = `Formalism/SharpRestriction/ElevenLe.lean`; `PC` = `Formalism/SharpRestriction/ParConsts.lean`; `PRQ` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean`
- `SLP` = `Formalism/SharpRestriction/AdmissibleParameterJoins/SumLogPrimeFactorsLe.lean`; `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `AGP` = `Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean`; `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- `SRB` = `Formalism/SharpRestriction/GrowthBounds/AdmissibleIntegers/StatementsOfRemainingBound.lean`; `SOP` = `Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean`
- `IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`; `MOK` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/ModelsOK.lean`
- `TS` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean`

## 0. Verdict

**No ESCALATE.** All three links close, with the following findings.

**A. adm11.**
- It is proved on the live path by an honest sum over prime classes.
- Every loss component is bounded per lift by an explicit multiple of B0 = f·m·b·L, with L = x^ε (`hB : L.B0 = f*m*b*L := rfl`, OLS:460).
- deLoss does **not** close by summing x^{798}·log p over primes. It closes through one parameter, etaSz (η):
  - N(j−1)N(j) ≤ N(m)² ≤ η (OLS:267-272);
  - the per-prime deLoss times log p is ≤ 4·f·η·L (OLS:287-298);
  - the sum is over at most X″ primes, and X″·η ≤ b (OLS:494). This gives ≤ 70·f·L·b ≤ 35·B0.
- X″·η ≤ b comes from SizeEta (x·t·η ≤ w″, EL:84-85). On the live path that holds because η = 2m⌈x^{ch}⌉ (PRQ:22, :112) and `scale_poly_comparison` gives b^{1/2}·x^{ch+1224} ≤ w″ (GI/SzRowEtaBounds.lean:14, 81-83, 98-104).
- That is exactly the comparison poly(x)·e^{x^{ε/3}} ≤ e^{x^ε/2}.
- The threshold is existential ("sufficiently large", from `log_add_rpow_mul_log_pow_le_rpow`), not a numeral. It depends only on (ε, the constant record C, cD, ch). It is uniform over every host D and record L satisfying `Val` (PRQ:124-126). Whether C depends on ψ was not traced.

**B. `nprimeMuR_at`.**
- The slope formula is exact: μ(N_u) − μ(NuH_u) = Σ_{w∈supp} 2·lwP(w)·⌊e_w·sg(u,w)⌋ (`mu_diff`, SLP:380-397).
- The floor costs ≤ 2·lwP per place with sg ≠ 0. Those places lie over primes ≤ X″, or over T, g0, g1, d, or a prime dividing DGam. So the total is ≤ 2(log 4 + 3 + CT + CG)·X″ (SLP:401-492, 694-709).
- The direction is the one Bost needs:
  - a fractional ideal 𝔭^{−k} with k > 0 raises the slope (`mu_smul_ideal`, SLP:33, 58);
  - ⌊e·sg⌋ ≤ e·sg, so N_u is at most the ideal lattice;
  - the lower bound used is μ(N_u) ≥ μ(NuH) + Σ sz(sg) − C·X″;
  - the divisibility is required only at the weaker exponent ⌊e·sg⌋. The Lean in fact proves it unrounded (`valuation_bound_of_unrounded`, LQP:218-221).

**C. adm2 on every branch.**
- `admissible_level_two` (AGP:214-236) splits every place w three ways: resChar w = T_u, resChar w ∈ {g0, g1}, or else.
- The else-branch goes through `WJS.Conclusion1`, whose proof `baseChange_preserves_unitary_of` (SRB:162-192) and the helper `first_clause_cases` (SRB:25-95) split further by prime class. Every branch has a supplier (§2c table).
- `Ties9` (WJS:84-87) is **parameter matching only**: LatTied, VramDef, FDef. Neither `LatTied` (IRZ:430-456) nor `NP` (IRZ:464-472) mentions the chain fields Lv, Ch of the LatInst.
- `Conclusion1`'s conclusion `ColGe` is about the **actual** column maps (D.mem u).C.col and (D.chTw u μ).col (WJS:23-35). The auxiliary local chain enters only through `CmpV` (WJS:156-159), i.e. `CmpLite` (MOK:46-54). CmpLite requires the local chain to intertwine with the actual global chain steps K_j.
- So no chain object, zero or not, can make adm2 vacuous. NODE-LOSS's zero-chain alarm is closed on the adm2/OneMapIntoCC path.
- What remains open is upstream: the producers of the binders twU/ModelsOK, aPt0…aAtG and pdv were not traced here.

## 1. Statement

### A. adm11 (LQP:315-321)
```lean
def adm11 (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D,
    |(∑ w ∈ L.supp, SizeData₂.sz w (L.E u j w)) - (∑ t, (L.aT t : ℝ)) * Real.log (∏ g ∈ L.gTypes, (g : ℝ))| ≤ C * L.B0 ∧
    ∑ w ∈ L.supp.filter (fun w => resChar w ∉ L.gTypes), |SizeData₂.sz w (L.E u j w)| ≤ C * L.B0
```
In words: for every word u and every lift j, with sz(w, y) = 2·lwP(w)·e_w·y:
- the total weighted loss Σ_w sz(E_{u,j}(w)) equals ΣA·log(g0·g1) up to C·B0;
- the part away from the two level primes g0, g1 is ≤ C·B0 in absolute value.

The ΣA·log g main term is the m·ΣA·lg of EComp5 (L4), which cancels Count5 [LEDGER L7].

E is pinned: `EDef`: E_{u,j}(w) = Eval(u, j, w) (DE:171-172). Eval (DE:159-169) is defined by cases on p = resChar w:
- p = T_u: EatT (DE:103-107);
- otherwise v_p(DGam) plus:
  - p = g_i: EatG = F_TypeG + vNN + c_g·f·(N(m)² + m²η) (DE:91-94);
  - p = d (ramD): EatD (DE:116-117);
  - (inertClass or signal) and p ≤ X″:
    - EatC if inertClass with hP = 0 (DE:121-123);
    - else EatI (DE:147-155);
  - anything else: 0.

EatI's terms:
1. max(0, Σ_{kindA} FOrb/nP), the kindA orbit term;
2. γ_p·|topsBC|·(b + η + 1 + 3Sc), errF;
3. c6·Σ_{kindBC} w/p;
4. |kindBC|·N(j−1)·N(j)·(log_p(4·nP·Nm·a) + 1), the rank-logarithm part of deLoss;
5. dl1·|kindBC|·Nm²·log_p(2a) + dl2·|topsBC|·log_p(2a)², the digit-sum part of deLoss;
6. EatX, nonzero only at IsCs primes (DE:139-143).

### B. NprimeMuR (GTI:69-70)
```lean
def NprimeMuR (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| ≤ C * L.sc.X'' D.R.n
```
Here N_u = Iu·NuLat_u with Iu = ∏_{w∈supp} 𝔭_w^{−⌊e_w·sg(u,w)⌋} (`Iu`, `NprimeDef`, DDD:16-25).

### C. adm2 (LQP:206-210)
For every u, every place w, every φ ∈ NuLat_u and every F ∈ M̃(μ(w)) ∩ V0, the period perCol_u(j_N φ, F) = embLL(y) with y = 0 or v_w(y) ≥ ⌊e_w·sg(u,w)⌋. This is the clause that `val2AllAtRF` turns into Bk_u(N_u) ⊆ cc [GATIE U5-U7].

## 2. Argument

### 2a. adm11: the producer, read to the bottom

**Live chain.**
1. `complement_two_of_items c` (TS:46). Here c is the binder `aC2` of `shape_closed_link_n_of_green` (TS:34).
2. `aC2` is supplied by `divisionSecondComplement_constructedPoints` (GI/DivisionSecondComplementConstructedPoints.lean:9-12).
3. Then `admissibleConstants_closed_under_sizeBounds` (DP/AdmissibleConstantsClosedUnderSizeBounds.lean:10-18).
4. Then `admissibleComplementTwo_along_family` → `familySecondComplementInputs_of_tuSize_of_dGamSize` (DP/AdmissibleComplementTwoAlongFamily.lean:18-40).
   - *(inferred)* That the AllRows row `aC2` is the one consumed at TS:34 was not re-traced; the names and types match.
5. `secondComplement_family_of_inputs` (WDS:690-693) and `secondComplement_of_inputs` (WDS:677-681) are glue. They reduce adm11 to `C2atG` (g primes) and `C2off` (all other places) through `secondComplement_of_split` (WDS:359-393), which gives constant 2·Cg + (CT + CG + Cd + CI).

**The eight inputs** (`SecondComplementInputs`, WDS:673-675) and what each pays:

| # | input | content | live producer (read) | bound |
|---|---|---|---|---|
| 1 | LevelPrimeNotTypePrime | g_i ≠ T_u | family field `T_ne_g` | — |
| 2 | NormDecompositionCond | Σ_{w∣g_i} sz(vNN) = (Σ_τ nuAbs)·log g_i (WDS:402-404) | `normDecompositionCond_famP` (statement only) | exact |
| 3 | DegreeCountBound | \|Σ_τ nuAbs − fockDeg − ΣA\| ≤ errG (WDS:413-415) | `exists_degreeCountBound_of_eps_lt_one_div_52` (statement; body not read) | errG ≈ 2Σw_j + C·f(kSc + m t η + kN) + \|TT\|b′/x ≲ f·b |
| 4 | TypePrimeSizeBound | (errG + 2v_g(DGam) + 2c_g f(N² + m²η))·log g ≤ Cg·B0 (WDS:417-421) | `typePrime_sizes_le_budget_family` (DP/TypePrimeSizesLeBudgetFamily.lean, skimmed: log g ≤ (CYL+1)·L at :114) | ≈ f·b·L ≤ B0 |
| 5 | LevelPrimeBudget | at T_u: sz(EatT) summed ≤ CT·B0 | `admissible_off_type_level_budget` (DP/AdmissibleOffTypeFamilyBound.lean:38-55) | EatT ≤ 12fb (:13-36); log T ≤ CTu·m·L (TuSize) ⇒ ≤ 12·CTu·B0 |
| 6 | StabiliserLogBound | 2 log DGam ≤ CG·B0 (WDS:539) | `exists_nonneg_const_discriminant_term_le_budget_family` (DP/…FamilyA.lean:10-19, from DGamSize) | log DGam ≈ 2fN(m)log(fN) ≈ x^{404} [CHAININD] ≪ B0 |
| 7 | DiscriminantOffsetBound | 2 log d·\|EatD\| ≤ Cd·B0 (WDS:541-542) | `offDiagonalRamified_bound_const_four` (DP/OffDiagonalRamifiedBoundAlongFamily.lean:10-41) | log d ≤ L, \|EatD\| ≤ 2fb ⇒ ≤ 4·B0 |
| 8 | InertPrimeLossBound | for every finite set P of inertClass/signal primes ≤ X″: Σ 2 log p·\|EatCI\| ≤ CI·B0 (WDS:544-547) | `inertPrimes_loss_log_sum_admissible` (DP/InertPrimesLossLogSumAdmissible.lean:12-47) = `loss_sum_primes` (EatC) + `inertLoss_primeSum` (EatI) | below |

**How `C2off_of` (WDS:601-671) assembles the off-g part.**
- At T_u it uses input 5.
- At the other places, `Eval_off` (WDS:563-585) gives |Eval| ≤ hOff = v_p(DGam) + [ramD]|EatD| + [inert/signal, p ≤ X″]|EatCI|.
- `sum_by_prime` (WDS:484-504) folds places over p using Σ_{w∣p} lwP·e_w ≤ log p (`factEtaMean`).
- `sum_val_log_le` (WDS:506-530) gives Σ_p log p·v_p(DGam) ≤ log DGam.
- So **split primes and primes > X″ carry only v_p(DGam)**, which input 6 covers in one stroke. The places over a prime are counted with weight log p, not log N(v) per place.

**`C2atG_of`** (WDS:433-478) at g_i:
- Σ_{w∣g_i} sz(E) = 2(v_g(DGam) + F_TypeG + er)·log g + (Σ nuAbs)·log g;
- by `DegreeCountBound`, Σ nuAbs = fockDeg + ΣA ± errG;
- the fockDeg part cancels against F_TypeG.
- So |… − ΣA·log g| ≤ (errG + 2v_g + 2er)·log g ≤ Cg·B0.

**EatC** (`bound_one`, LSP:13-101; `loss_sum_primes`, :103-111, C = 18(1/ε + 1), x0 = 2):
- Σ_{p≤X″} 2 log p·|EatC| ≤ 2·X″·3f·N(m)²·log a + 2·Σ_τ w_j·log a·(Σ 1/(p²−1)) (`ConjLoss.sum_primes_le`, statement only).
- It uses X″·N(m)² ≤ b (LSP:58-62, from the family's `P.teta` t·η ≤ w″/x and N(m)² ≤ η) and log a ≤ (1/ε + 1)·L (LSP:72-78).

**EatI** (`eatI_bound`, OLS:209-333; `sum_eatI`, OLS:447-497, constant 424, doubled to 848 for the weight 2 log p in `inertLoss_primeSum`, DP/InertLossPrimeSum.lean:11-20, x0 = 0). Per prime p ≤ X″ (≤ b) and per lift, times log p:

| component | per-prime bound × log p (Lean) | count/weight | total per lift | vs B0 = f·m·b·L |
|---|---|---|---|---|
| kindA FOrb (`first_term`, OLS:174-205) | 6·f·m·b·(log p/p). Uses w ≤ 3(b′+η) at Bool-false positions (OLS:115-147) and (k−1)(b′+η) ≤ m·b (`nums`.1) | Σ_{p≤X″} log p/p ≤ 3L (`primeLogSum` with p ≤ b, OLS:467, 492) | 18·B0 | ✓ |
| errF γ_p·\|topsBC\|·(b+η+1+3Sc) (t2, OLS:274-279) | 12·f·b·(log p/p) ≤ 12·f·m·b·log p/p | same | 36·B0 | ✓. The real size is ≈ \|TT\|·b·log X″ ≈ \|TT\|·b·x^{ε/3}, below the bound because \|TT\| ≤ f and log X″ < L |
| c6·Σw/p, c6 = 12 (t3, OLS:281-286) | 108·f·m·b·(log p/p) (w ≤ 9b) | same | 324·B0 | ✓. This is the largest constant; real size ≈ 12·f·b·x^{ε/3} |
| deLoss rank logs, \|kindBC\|·N(j−1)N(j)·(log_p(…)+1) (t4, OLS:287-298) | 4·f·η·L. Uses N(j−1)N(j) ≤ Nm² ≤ η and log(4·nP·Nm·a) ≤ 3L | ≤ \|S\| ≤ X″ primes (`hcard`, OLS:461-466) | ≤ 4·f·L·X″·η ≤ 4·f·L·b (OLS:494) | ≤ 2·B0 (m ≥ 2) |
| deLoss digit sums dl1 = 5, dl2 = 4 (t5, t6, OLS:299-323) | 10·f·η·L + 32·f·η·L | same | ≤ 42·f·L·b | ≤ 21·B0 |
| EatX at IsCs (`eatX_bound`, OLS:382-436) | 9·f·b·k·log p/p³ + 24·f·η·L | k·Σ_{IsCs} log p/p³ ≤ 2, since IsCs p ≡ ±1 mod 2^e, 2^e ≥ x², k ≤ x⁵ (`sum_cube_le`, `cube_sizes`, OLS:335-380, 438-445) | 18·f·b + 24·f·L·b | ≤ 21·B0 |

Total: Σ_p |EatI|·log p ≤ (378 + 9 + 35)·B0 ≤ 424·B0 (the `linarith` at OLS:497).

**The deLoss check the brief asked for.**
- With the Lean's own bounds t ≤ x^{401}, k ≤ x⁵ and m ≤ x (GI/SzRowEtaBounds.lean:22, 61-63), N(j) = k + j(t+1) (DP/AdmissibleOffTypeFamilyBound.lean:19) is ≤ ≈ x^{402}. So the real deLoss is ≈ f·x^{804}·log a per prime per lift. That is a little above ENGINE's x^{798}, which is immaterial.
- Summed with log p over p ≤ X″ ≈ x^{3+8ε}e^{x^{ε/3}}, it gives ≈ x^{809+O(ε)}·e^{x^{ε/3}}.
- The Lean replaces x^{804} by η and closes with X″·η ≤ b.
- Unfolded: X″·η = (a/w″)·η, and x·t·η ≤ w″ (SizeEta clause 4, `nums` OLS:81-83). So X″·η ≤ a/x = b.
- On the live path η = m·h0v = 2m⌈x^{ch}⌉ (PRQ:22, `eta_eq` PRQ:112), ch ≥ 401 (SzRowEtaBounds:13). SizeNodes forces ch ≈ 1300 [COUNT].
- x·t·η ≤ y·x^{405} ≤ y·x^{1224} ≤ w″, with y = x^{ch} (SzRowEtaBounds:98-104). The last step is `scale_poly_comparison` with κ = 1/2: b^{1/2}·x^{ch+1224} ≤ w″(n) for n ≤ x³ (GI/ScalePolynomialQuantitiesComparison.lean:9, 53-58).
- Since w″ = b/(x·n·X′), this is x^{ch+1228}·e^{x^{ε/3}} ≤ e^{x^ε/2}: **the poly(x)·e^{x^{ε/3}} ≤ e^{x^ε} comparison, with room b^{1/2}**.

**Threshold and uniformity.**
- `sum_eatI` holds for every (D, L) with `SizesAt L` (no x0). `inertLoss_primeSum` then has x0 = 0 beyond the family's x1. `SizesAt` is the family field `sizes : ∀ x > x1, SizesAt (L x i)` (PC:44).
- On the live constructor it is `szRow_sizesAt` (GI/SzRowElevenLeSplitBound.lean:38-46), consumed at GI/SzRowNumAt.lean:30.
- Its form is SzRow (PRQ:124-126): ∀ ε ∈ (0, 1/52), ∀ C with Std C, ∃ c1, ∀ cD ≥ c1, ∃ c2, ∀ ch ≥ c2, ∃ x0, **∀ D L** with L.ε = ε, x ≥ x0, Val C cD ch L ⇒ P.
- So x0 is existential, built by max of finitely many "sufficiently large" lemmas (e.g. `log_add_rpow_mul_log_pow_le_rpow`, ScalePolynomialQuantitiesComparison.lean:11-21). It is uniform in the host D and the record L.
- *(inferred)* This is the uniformity the Landau windows need: the host changes with x, and the bound must hold at every x ≥ x0 of every window.
- Whether the constant record C (`FC`) is chosen depending on ψ was not traced. For a fixed ψ, uniformity in ψ is not needed *(inferred)*.

### 2b. The floor: `nprimeMuR_at` (SLP:694-709)
1. `mu_diff` (SLP:380-397) gives μ(N_u) − μ(NuH_u) = Σ_{w∈supp} 2·lwP(w)·⌊ur(sg)⌋ exactly. It uses `mu_frac`/`mu_smul_ideal` (SLP:30-71: μ(𝔟·M) = μ(M) − 2 log N𝔟/[LL:ℚ], slope = −log covol/rank) and log N(Iu) = −Σ ⌊ur sg⌋·log N𝔭_w (`log_absNorm_Iu`, SLP:358-378).
2. `round_le` (SLP:401-429): since |⌊y⌋ − y| ≤ 1, |μ(N_u) − μ(NuH) − Σ sz(sg)| ≤ 2·Σ_{w: sg≠0} lwP(w).
3. `sg_eq_zero` (SLP:431-446): sg = 0 at w if p > X″, p ∉ {T, g0, g1, d} and p ∤ DGam (by ZeroAbove and F_above). So the places with sg ≠ 0 lie over P = {primes ≤ X″} ∪ {T, g0, g1, d} ∪ primeFactors(DGam).
4. `nprimeMu_at` (SLP:448-492) bounds Σ_{w over P} lwP ≤ Σ_{p∈P} log p (`sum_lwP_le`, SLP:276-301). With θ(N) ≤ N log 4 (`sum_log_primes_le`, primorial ≤ 4^N, SLP:324-337) this is ≤ X″ log 4 + log T + log g0 + log g1 + log d + log DGam.
5. `nprimeMuR_at`: with log g, log d ≤ X″ (SLP:544-561), log T ≤ CT·X″ and log DGam ≤ CG·X″, the total is ≤ 2(log 4 + 3 + CT + CG)·X″. `linkMu` (SLP:728-749) packages this for the family.

Size: X″ = x·n·X′ ≈ x^{3+8ε}e^{x^{ε/3}} ≪ b. One floor per place, on the total exponent over all lifts and tops; the floor is not multiplied by |TT|·m (confirms GATIE oddity 5).

Direction:
- sz(sg) − 2lwP ≤ 2lwP·⌊e·sg⌋ ≤ sz(sg), so the lattice is at most the ideal one and loses ≤ 2lwP of slope per place.
- L2 uses the lower side, and LoU's C·X″ pays for it [GATIE]. This is the inequality Bost needs: a larger lattice means smaller covolume and larger slope; the floor lowers it by a bounded amount.
- The integrality side asks only for v_w ≥ ⌊e·sg⌋, which is weaker than the proved unrounded e·sg (LQP:218-221).

### 2c. adm2: the branches, each with its supplier
Top split, `admissible_level_two` (AGP:224-236):

| branch (p = resChar w) | exponent sg(u,w) | supplier of the valuation bound | file:line |
|---|---|---|---|
| p = T_u (the word's type prime) | sg = −m·EatT ≤ 0 (`sg_atT`, WDS:887-901) | `admissible_at_twist_places`: Conclusion5Sharp (`ColGe0_atT`) at μ0 and `TwistedColumnBoundAtT` at μ ≠ μ0, both at −m·EatT, then `period_geTU` with vDG = 0 (T ∤ DGam) | AGP:92-111; binders `p10`, `dgt` of Adm2InU (AGP:309-311) |
| p ∈ {g0, g1} (level primes) | sg = Σ_j(F − E) (`sg_atG`, WDS:1007-1016). By `SgAtG` (WDS:1002-1005) it is ≤ −Σ vNN − C1·errC, so a lower bound of negative order is needed | `admissible_at_generator_places` ← `atG_coreU` ← `UsedTuplesBoundByConstant` (period of Mram vectors ≥ −Σ vNN − C1·errC) | AGP:113-169, 25-28; binder `atG` (AGP:312-313) |
| everything else | sg + vDG ≤ totS (AGP:188-193: gainD ≤ gainS via `gainLe_of_fills`, E = ES via EDef) | `admissible_off_twist_places` → `WJS.Conclusion1` (`hS.2.1` of Serv), then `period_geTU` subtracts vDG | AGP:171-196, 236 |

Inside `Conclusion1` (`baseChange_preserves_unitary_of`, SRB:162-192). InNP (WJS:62-65) splits into the served (GIdx) case and the VV = ∅ case. ServedHasModel (WDS:845-847) gives VV ≠ ∅ ⇒ GIdx.

| sub-branch | gain part | supplier | file:line |
|---|---|---|---|
| **GIdx, x ∈ NP** (inertClass, p ≥ 5, not level, ∤T, served orbits VV ≠ ∅) | Σ gainS ≤ Σ gainP | `kernel_valuation_served`: TupleLatticeValuation (= `first_in_local_models` from UAt = `unitBoundAtTwistedPlaces`, span induction on NP generators) on the local chain reW(Fm.Gy, LC), then **CmpV** to the actual columns. Uses `ht.tied` only through LatTied_tw | WJS:348-370, 303-310; SRB:111-151, 168; UAt from `unit_bound_of_sum_over_primes … stmt_proved … hSys` (SOP:191-193) |
| VV = ∅, not (inertClass ∨ signal) or Exc (cond., g) | gainS = 0 | lowS from `ColumnValuationAwayFromTypePrimes` | SRB:171-175 |
| VV = ∅, inertClass with hP = 0, or p > X″ | gainS = 0 (gainP's own case) | lowS as above | SRB:176-180 |
| VV = ∅, signal, or inertClass with hP ≠ 0 (IsCs included: g0S = 0 there), p ≤ X″ | Σ g0S (= gainS since VV = ∅) | `OrbitsWithoutOperator` (WJS:211-217) = `n` of `four_orbit_conditions_of_proof` → [SIGNAL/ORBIT] `noOp_of`/`split_bound_eleven_one` | SRB:181-192; SOP:205-210 |

The lowS part (`first_clause_cases`, SRB:25-95), by prime class:

| class | lowS exponent | supplier |
|---|---|---|
| ramD (p = d) | Σ(F − EatD − vDG) + vDG | `LossAtDiscriminant` (WJS:226-230) = `d` (SOP:205) |
| inertClass, hP = 0, p ≤ X″ | Σ(F − EatC − vDG) + vDG | `MediumInertPrimeLengthBound` (WJS:218-224) = `c` |
| signal or inertClass hP ≠ 0, p ≤ X″ | g0S + lowS ≥ lowS | `OrbitsWithoutOperator` = `n` |
| everything else (split, p > X″, non-inert) | F = 0 there (SRB:86-91), so exponent −(m − 1)·vDG ≤ 0 | `RestElse` ← `remaining_primes_of_admitted` from `IntegralKernelValuation` (each K_i integral up to vDG, WJS:113-123) = `it` (SOP:205) |

**No branch lacks a supplier.** At split primes, primes > X″ and the type primes the exponent is ≤ 0, and the content there is integrality up to v_p(DGam) or up to −m·EatT. Positive exponents occur only at inertClass/signal places ≤ X″ (gain) and wherever F > 0.

**Ties9 versus zeroCh.**
- `Ties9 D L X Y c` = ⟨∃ hT, LatTied hT X Y; c.VramDef Y; L.FDef⟩ (WJS:84-87). On the live path it is `local_compatibility_family` (WJS:588-590), from family fields `gatT`, `latTied`, `lat.vram`, `fdef`.
- `LatTied` (IRZ:430-456) constrains only Fl, vOf and gat: m, t, the caps = fillG, the tops, a, b, and positions = Frobenius translates. `LatTied_congr`/`LatTied_tw` (WJS:297-307) show it depends only on vOf and Fl.
- `NP` (IRZ:464-472) uses only vOf (through yProd), gat and Vram; `NP_tw` is `rfl` (WJS:293-295).
- Hence `serv_re` (SOP:98-107) moves Conclusion1 from reY(Fm.Gy, LC) to Fm.Gy by `{ hT with }`. Serv is proved for the chain LC from twU, and stated for Fm.Gy (WJS:252-255).
- Conclusion1's conclusion `ColGe` is about the actual column maps (WJS:23-35), so the chain of Fm.Gy, zero or not, is irrelevant to it.
- The tie of the auxiliary chain to the actual maps is `CmpV` (WJS:156-159). It is obtained through `cmpV_of_cmpLite` from `ModelsOK` (MOK:56-62, `rowTwU_of_models`, `Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryWeightModels.lean:15-31`).
- `CmpLite` (MOK:46-54) demands three things:
  - cmp_0 = c.cmp;
  - cmp_{j+1}(K_j x) = Kz_j(cmp_j x) for the **actual** twisted chain (D.chTw u μ).K;
  - local vGeLat at level m ⇒ global VGe.
- *(inferred)* With a zero local chain, CmpLite would force the actual chain images to have unbounded valuation. That is not a vacuous route.
- NODE-LOSS's `zeroCh (Fm.Gy x i)` sits on the LinkG branch (admG1, loss and colength clauses) [LOSS, SLOPESN §0.4]. It feeds neither adm2 nor OneMapIntoCC. **The alarm is closed on the live adm2 path.** The colength clause it feeds is chain-independent, since NP ignores Ch.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `sum_eatI`, `eatI_bound`, `eatX_bound`, `first_term` | OLS:447, 209, 382, 174 | Σ_{p≤X″}\|EatI\|·log p ≤ 424·B0 | pays errF, c6, kindA, deLoss, EatX | core (read) |
| `bound_one`/`loss_sum_primes` | LSP:13, 103 | Σ 2 log p\|EatC\| ≤ 18(1/ε+1)·B0 | inertClass hP = 0 | glue (read; `ConjLoss.sum_primes_le` statement only) |
| `C2off_of`, `C2atG_of`, `secondComplement_of_split` | WDS:601, 433, 359 | assembly into adm11 | — | glue (read) |
| `exists_degreeCountBound_of_eps_lt_one_div_52`, `normDecompositionCond_famP` | DP/…Statement.lean:8 | Σ nuAbs = fockDeg + ΣA ± errG; vNN valuation identity | the ΣA·log g main term at g primes | **core, bodies not read** |
| `szRow_eta_bounds`, `scale_poly_comparison` | GI/SzRowEtaBounds.lean:11; GI/ScalePolynomialQuantitiesComparison.lean:9 | η ≤ b/(t³fk³), x·t·η ≤ w″; poly·X′ ≤ b^{1/2} | makes X″·η ≤ b | core (read; `log_add_rpow_mul_log_pow_le_rpow` statement only) |
| `nprimeMu_at`, `round_le`, `mu_diff` | SLP:448, 401, 380 | floor loss ≤ 2Σ_{p∈P} log p | NprimeMuR | glue (read) |
| `admissible_level_two` and its three branch lemmas | AGP:214, 92, 134, 171 | adm2 at every place | Bk(N_u) ⊆ cc | glue (read) |
| `baseChange_preserves_unitary_of`, `first_clause_cases`, `kernel_valuation_served` | SRB:162, 25; WJS:348 | Conclusion1 by sub-branch | — | glue (read) |
| Adm2InU binders: Conclusion5Sharp/TwistedColumnBoundAtT, UsedTuplesBoundByConstant/SgAtG, PeriodClassSumWeyl/TwistedPeriodAdmissible, MemberChainIntegral/TwistedPointIntegral | AGP:302-313 | integrality at T, g, and of periods (≥ −vDG) | **inputs**, from TS:34 binders aPt0…aAtG | core, producers not traced here |
| `ModelsOK`/`CmpLite`; `pdv` (OrbitPlaces data) | MOK:46-62; SOP:128-148 | local chains intertwine with the actual chain; orbit data at Sram places | the live tie of the GIdx and signal branches | core, producers not traced here |

## 4. Oddities

1. **The deLoss accounting is coarser than the brief assumed, and safer.**
   - The Lean never sums x^{798}·log p. It bounds N(j−1)N(j) by η, a single polynomially sized free parameter, and counts **all integers** ≤ X″ (`hcard`).
   - The closing inequality X″·η ≤ b is a size clause of the family (SizeEta), proved on the live constructor with margin b^{1/2}.
2. **The constant 848 is dominated by the c6·Σw/p term** (108·3 = 324 of 424).
   - It uses w ≤ 9b at every place, and Σ_{p≤X″} log p/p is bounded by Mertens up to b (3L), not up to X″ (≈ x^{ε/3}).
   - So the bound is ≈ x^{2ε/3}·m times looser than the true size. This is harmless.
3. **E has a large ΣA·log(g0 g1) main part at the level primes.**
   - adm11's first clause certifies it two-sidedly. It enters Ee ≤ m(ΣA·lg + cE·B0) and cancels Count5's m·lg [LEDGER L7].
   - At g primes sg is therefore strongly negative. adm2 there is a **denominator bound** (UsedTuplesBoundByConstant), not a gain.
   - Its producer was not read. Its precision matters at the ±C·B0 level, because the main part ΣA·log g ≈ |TT|·a·x^{szTh}·L is far larger than B0.
4. **`DegreeCountBound` carries that precision**: |Σ nuAbs − fockDeg − ΣA| ≤ errG ≈ f·b. Its body was not read. It is the one adm11 input whose error is not obviously "polynomial against b".
5. **Thresholds are existential**, ∃ x0 assembled by `max`, except a few explicit ones (x0 = 2 in `loss_sum_primes`, 11^{5Cpde/ε} in `szRow_eleven_le_splitBound`). They are uniform in the host. Dependence on ψ through the constant record was not checked.
6. **The NprimeMuR bound counts every prime ≤ X″**, split ones included, though sg = 0 at split primes not dividing DGam *(inferred from §2c)*. It is crude but sufficient.
7. **`Ties9` is a misleading name for "LatTied + Vram + FDef"**. The tie to the actual maps is `CmpV`/`CmpLite`, which sits upstream in `ModelsOK`, a hypothesis of `rowTwU_of_models`.

## 5. Coverage

Read in this pass:
- PROTOCOL; MAIN-ARGUMENT §0, §5, §6; NODE-GATIE (all); NODE-LOSS (all); NODE-LEDGER:100-235; NODE-ENGINE:355-400; NODE-CHAININD:215-235; NODE-COUNT:40-60; NODE-FAMILY:80-100; NODE-HOSTS:183-235; NODE-SLOPESN:30-50.
- Other NODE files greps only: SERVED, ORBIT, COLENGTH, SIGNAL, ROWSU.
- Data files: LQP:190-330; WDS:337-701, 836-1020; DE:1-200.
- DivisorProofs: NormDecompositionCondOfJetConsequence.lean:250-297; ClassOfRecordOfChoice.lean:140-200; TS (all); AdmissibleComplementTwoAlongFamily(.lean, Statement.lean); DivisionSecondComplementAtConstructedPoints (both); AdmissibleConstantsClosedUnderSizeBounds; InertPrimesLossLogSumAdmissible(+Statement); InertLossPrimeSum; OtherLossSum (all); LossSumPrimes (all); ExistsNonnegConstDiscriminantTermLeBudgetFamilyA; AdmissibleOffTypeFamilyBound; the six *Statement.lean files.
- Partial reads: TypePrimeSizesLeBudgetFamily (grep); OffDiagonalRamifiedBoundAlongFamily:8-57 (grep).
- Size and threshold files: EL:60-145; PC:30-60; GI/SzRowNumAt; GI/SzRowElevenLeSplitBound; GI/ExplicitChoiceSizeEta; GI/SzRowEtaBounds (all); GI/ScalePolynomialQuantitiesComparison:9-58 (+Statement); PRQ:95-130.
- Floor files: SLP:28-77, 270-302, 316-495, 544-566, 600-760; DDD:1-30; GTI:55-80.
- Branch files: AGP (all); WJS:1-420, 580-633; SOP:80-125, 140-225; SRB:1-210; AdmissibleIntegers.lean (all); GServT (all); IRZ:412-480; DataLatDefs.lean:1-40; MOK (all); UnitaryWeightModels.lean (all).

Greps run:
- `secondComplement_family_of_inputs|complement_two_of_items`;
- `degree_weight_family_of_constant|FamilySecondComplementInputs`;
- `familySecondComplementInputs_of_tuSize_of_dGamSize|DivisionSecondComplement…`;
- `SizesAt`, `sizes :=`, `szRow_sizesAt|SzRow`, `h0v|Delv`;
- `nprimeMuR_at|NprimeMuR`;
- `Conclusion1|ServF|Stmt`, `serv_re|reY|reW|serv_of`, `kernel_valuation_served`, `rowTwU_of_models`;
- `IsCs`, `GIdx`, `VV`;
- `sorry|axiom|admit` in the DP producer files read (none found).

Not opened:
- the bodies of `admissibleDegreeCount_along_family`, `typePrime_valuationSum_eq_logGap_family`, `ConjLoss.sum_primes_le`, `primeLogSum`, `log_add_rpow_mul_log_pow_le_rpow`, `explicitRanks_basic_bounds_large_scale`, `remaining_primes_of_admitted`, `four_orbit_conditions_of_proof`, `unit_bound_of_sum_over_primes`, `cmpV_of_cmpLite`;
- the producers of the binders aPt0, aPtTw, aPer0, aPerTw, aP10, aAtG, hServ/twU/ModelsOK and pdv upstream of TS:34;
- `AdmissibleFamilyNoKernel.lean` (zeroCh, cited from LOSS/SLOPESN);
- the wiring of the AllRows `aC2` row into TS:34 (inferred from the types).
