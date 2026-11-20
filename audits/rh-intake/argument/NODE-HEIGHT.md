# NODE-HEIGHT: the archimedean height of the period maps (clause (C) of DIV)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `INP` = `Formalism/LocalToGlobal/Divisibility/Inputs.lean`
- `DHB` = `Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean`
- `C28` = `Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`
- `PTK` = `Formalism/LocalToGlobal/PtKOfReal.lean`
- `SPL` = `Formalism/HarderNarasimhan/StatementPl.lean`
- `DIE6` = `Formalism/ThetaSupremumBounds/DivIneqExplicit6.lean`
- `FB` = `Development/AbelianVarietyTheory/Definitions/Divisors/FactorBounds.lean`
- `TPLT` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TopPlaceLogTheta.lean`
- `KHC` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/KernelHalfChainNumbersAnyLevelPrime.lean`
- `CKB` = `Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ChainKernelBoundAtEmbeddingAnyLevelPrime.lean`
- `PWN` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/PaddedWittNormSquare.lean`
- `NFL` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFockLSqLe.lean`
- `MLP` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogPeriodChowlaSelberg.lean`
- `MLC` = `Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanLogPeriodConjugatesEqChowlaSelberg.lean`
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`
- `ZON` = `Formalism/LocalToGlobal/Divisibility/ZscOfNum.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`

## 0. Verdict (short)

1. **The archimedean height bound is proved, not assumed, apart from one input.** Two pieces of
   real analysis are proved in-tree:
   - a Cauchy/Fock coefficient estimate (`BlockBound`, `NFL:262`) for Taylor jets of entire
     functions with Gaussian growth;
   - the averaged Chowla–Selberg formula over Galois conjugates of the CM period lattice
     (`mean_log_area`, `MLC:141`; `meanPeriod`, `MLP:84`), as an exact equality.

   On top of these, the bound htMap(B_u) ≤ h(u) = hu − meanLog κ is assembled by
   submultiplicativity along the chain `PtL ∘ K_m ∘ … ∘ K_1` (`height_chain_atR`, `C28:124`).
   `RowsU` is an output of this proof. It is not an input.
2. **The one non-proved input sits inside the height bound.** It is the lower bound **L6** on the
   theta-lift isometry scalars λ_j: log λ_j ≥ Σ_ρ logHook_{jρ} − C·f·nV²·Lp. This is the
   `IndefData.L6` field (`IS:325-326`). Its supplier is `lamLow_of_hypotheses_alt_alt`
   (`TPS/LamLowOfPublished.lean:18-19`), with seven `Published.*` premises: CuspRapidDecay,
   WeilSiegelFormulaUnitary, SiegelWeilUnitaryConvergent, DoublingMethodLocalZetaIntegrals,
   UnramifiedDoublingGL, BernsteinZelevinskyFiniteness, FormalDegreeCompactDual. Its term −Σ l6 is
   the hX term of hu. It is ≈ m·k·f·b·x^ε, as large as the hB term it cancels against.
3. **Precision.** The proved part is an inequality whose slack is polynomial in x: factors
   e·(2|ν|+2)^{2ab}, class numbers, index counts and log(8+…) terms, all ≤ poly(x)·La ≪ b. It has
   no slack in the coefficient of logΩ or of ph(ν). Because it is *proved*, the "relative x^{−4}"
   requirement of NODE-ACCOUNT puts no burden on (C) itself. That burden falls on (B) (covolume) and
   on L6 (hook lower bound). Both must hold to relative x^{−4} if the composed chain is to be true.
4. **logOmτ is not a free fudge.** On the live path, logOmτ(z, v) = Σ_ρ wt(v,ρ)·logOmAt(ρ, z).
   - ρ runs over the embeddings of a number field M that contains the theta coefficients.
   - logOmAt(ρ, ·) is the true log metric of the ρ-conjugate period lattice.
   - The per-embedding bound is proved for each ρ with its own true period.
   - The conjugate periods genuinely differ (they are different ideal classes). Only their mean
     equals logΩ, and that is the proved averaged Chowla–Selberg identity.
   - htMap is itself a mean over places, so only that mean is ever used.
5. **The m-independence of DIV's C·|TT|·a·La** comes from the parameter choice b′ = a/X′. Every
   deviation of a top place's weights from the clean value a_t is O(b′), and the windows give
   m·k·b′ ≤ a (`INP:155`, p33) and b′·Nn ≤ a (p32). The m copies of ph(a_t) − a_t·logΩ are exact.

**Judgement: yes, conditionally.** htMap ≤ h is proved from mathematics I can reconstruct (Cauchy
estimate in Fock norm, Gaussian growth of CM theta functions, averaged Chowla–Selberg), modulo the
L6/Rallis-type premise and the unopened proofs of the four `normalisedFamily_*`/`CosetRefinement`
theorems. It is proved to the precision the chain needs *as an upper bound*. Whether DIV is then
true depends on (B) and L6, not on (C).

## 1. Statement

### (a) The objects

**`htMap`** (`SPL:60-62`):

  htMap(φ) = (1/nPl K) Σ_{v ∈ InfinitePlace K} log ‖X′_v^{−1} · φ^v · X_v‖²_op.

- This is archimedean only. `opNormAt` (`SPL:55-58`) is the Euclidean operator norm after
  conjugating by the frames.
- For B_u the frames are the Nu-frame Xc and the dual frame of RR (XE).

**`RowsU`** (`PTK:141-160`). There exist a column chain `ch` (`ColChain`, `INP:301`) with
`fact : Pt φ F = PtL(chainMat Kj · φ) F`, and the following data:
- frames X0 with (X0⁻¹)*X0⁻¹ = HV_v. This pins X0 to the hermitian form of the definite side.
- `hn : HtNums R (InfinitePlace LL)`;
- a bound on the last map: ‖PtL‖²_v ≤ exp(hn.hPn) for every v;
- `cb : CBData ch.X ch.Kj` with log cb.sq(j,v) ≤ Σ_{l: lf l = j} hn.sz(l, v);
- invertibility of Xc, a > 0, and Nu a lattice.

**`HtNums`** (`INP:210-282`) is a record of reals with inequalities. The fields that matter:
- `i1`: ∀τ, mean_s logOmτ(τ, s) = R.logOm;
- `i2`: MainNotions ≤ C2·f·m²·Nn²(logg + logT) + Ce·f·Nn²·logg;
- `i3`: mean logth0 ≤ Cth·L;
- `i4`/`i5`: logh, logh′ ≤ C4·f·Nn²(L + logT + logg);
- `i6`–`i9`: sizes;
- `t1`–`t11`: the last-map record:
  - hPn ≤ −Σ_τ nτ·logT + Σ_τ(2 logc_τ + logxi_τ) + ev;
  - nτ = lam1 − D0, with lam1 = a_t − (Nn − k)/2 at tops;
  - logc ≤ (Nn−1)·D1·log 2a, with D1 ≤ 3D0 + S + η and D0 ≤ S + mη + [τ∈TT]·bT, bT ≤ 2b′.

**`sz`** = `liftedMapLogSize` (`DIE6:15-22`):

  sz(j, s) = Σ_τ [Σ_i ph(ν_{jτi}) − (Σ_i ν_{jτi})·logOmτ(τ, s)]
             + |Pl|·g0_j·logth0(s) + |Pl|·g0_j·log(8 + 32|Pl|·g0_j·v) + 2·MainNotions(j, s)
             + Σ_τ (1 + 2 g0_j·log(2Σ_i ν + 2)) + logh_j + logh′_j,

where ph(y) = y log y − y. The pieces:
- ν_{jτi} are the Harish-Chandra/weight entries of lift j at place τ.
- g0_j = N_{j−1}·N_j is the matrix size of the jet variables.

**`CBData`** (`INP:342-375`) consists of:
- class sets Cl, normed spaces W, weights γ (= 1/|stab|), maps Φ, T;
- the hypothesis `CBHyp`;
- sq(j, v) = cbSq(|AA_j|, |AA_{j+1}|, hcl_j, hcl_{j+1}, tmax_{jv}) = n·n′·h·h′·t (`StatementCB.lean:15`).

This is the norm of a class-weighted sum of block maps: (number of classes)² × (largest block
norm²).

**h(u)** (`INP:185-197`, RecNums): hu = hA + Σ_j (hB_j − hX_j), with three parts.

| term | formula | meaning | size |
|---|---|---|---|
| hA | −Σ_{t∈TT} a_t·log T + Ch(\|TT\|·b′·Nn + f(mη+S)Nn + f·Nn²)·La | last map PtL: Bessel functional at the top, scaled by T^{−deg} | ≈ \|TT\|·a·m·x^ε, plus error ≤ C·\|TT\|·a·La |
| hB_j | Σ_ρ [Σ_i ph(ν_{jρi}) − (Σ_i ν_{jρi})·logΩ] + Ch·f·Nn²(La + m³L) | jet-step operator norm: ∏ν!·Ω^{−Σν} | ≈ k·f·b·x^ε per j |
| hX_j | Σ_ρ logHook_{jρ} − Ch·f·nV²·Lp | log of the theta-scalar lower bound l6 (hook product, `ZON:64-67`) | ≈ k·f·b·x^ε per j |

Two numeric facts tie hu to the main term:
- `weight_sum_eq`: Σ_i ν = a_t[ρ∈TT] + k·w + δ;
- `weight_height_sum_le`: Σ_i ph(ν) − logH ≤ ph(a_t)[ρ∈TT] + eE.

Together they collapse hu to Σ_t [m(ph(a_t) − a_t·logΩ) − a_t·log T] + O(|TT|·a·La + m·B0·x^ε) (§2(d)).

### (b) The chain to the height bound

`height_chain_atR` (`C28:124-182`) gives, for every v:

  log‖B_u‖²_v ≤ hPn + Σ_j hK_j(v) − log κ_v − min_p Σ_j log λ_j(p, v).

Averaging over v and using L6 (Σ_j l6_j ≤ min_p Σ_j log λ_j):

  htMap(B_u) ≤ hPn + Σ_j mean_v hK_j − Σ_j l6_j − meanLog κ.

`HtNums.le_hu` (`DHB:115-126`) then gives hPn + Σ_j mean_s sz − mlam ≤ hu, with mlam ≥ Σ hX.
(The λ_j are the scalars by which θ_j scales the definite frame XT_j to the indefinite frame XW_j,
`RowLatticeBoundForBasis`, `IS:310-317`.)

## 2. Argument

### (b) The archimedean computation for one step K_j

**Definition of the step** (NODE-GLOBALCHAIN):

  K_jφ(c′) = Σ_c |stab c|⁻¹·ρρ′·jetMap(jetC cD θ_{c,c′})(φ(c)).

Here θ is a theta function whose archimedean component is a "vacuum" (Gaussian) built from the CM
period lattice Λ(δ).

**Norms.**
- The source and target norms are `famIpAt` (`DHB:245-246`): Σ_classes (stab-weighted)
  `ipAt` of `pairK`.
- `pairK` (`Formalism/LocalToGlobal/Divisibility/CoefMod.lean:171-179`) is the **Fischer/Fock form**
  `fockL`, normalised by gramTw/extNorm, on the polynomial model VV_λ of the highest-weight
  representation.
- No (2πy)^{wt} factor appears: these are definite (compact) groups. The Petersson×(2πx)^{−|wt|/2}
  normalisation of NODE-COVOL belongs to the indefinite side.
- The two sides are compared through λ_j (L6).

**The analytic core is `BlockBound`** (`PWN:36-49`), proved as `blockBound` (`NFL:262`). Its
hypotheses:
- G is entire on (ℂ^{a×b})^ι;
- |G(z)| ≤ S·exp(Σ_τ r_τ²|z_τ|²/2);
- |cD_τ·r_τ|² = 1/Ω_τ.

Its conclusion is that the jet operator jetOp(jetC cD G): VV_λ → VV_λ′ has

  ‖·‖²_op ≤ tmax = S²·∏_τ Ω_τ^{−|ν_τ|}·e·(2|ν_τ|+2)^{2ab}·exp(Σ_i ph(ν_{τi})).

The proof (`NFL:151` `taylor_jetC`, `:198` `scalar_block`, `:262`) is a Cauchy estimate against
the Gaussian weight, combined with the Fock adjoint. In words:
- |c_ν|² ≤ S²·(e/|ν|)^{|ν|}r^{−2|ν|} and the Fock norm of z^ν is ν!;
- so ‖D^ν G(0)·cD^ν‖² ≲ S²·ν!·Ω^{−|ν|} ≈ S²·exp(ph(ν))·Ω^{−|ν|}.

**Applying it to the CM theta function** (`CKB:17-95`):
- `block` (`JetCConstMul.lean:83`) applies BlockBound with Ω_τ = exp(logOmAt(ρ, τ)), the
  ρ-conjugate lattice, and S² = exp(logThAt(ρ)).
- The Gaussian growth comes from `FamilyTie`/`PeriodLattices`/`FamilyVectors`. These are proved
  theorems with no premises (`normalisedFamily_*`, statement files only read).
- The bound is converted to kernelBound_sq (`TPLT:17-25`) by `exists_jetBlockBound_le_exp_kernelBound`.

**Summing to the chain** (`KHC:219-332`):
- the class numbers h and index counts n are bounded by exp(C·errUnit);
- `kerSide_of_meansS` (`KHC:94`) packages the per-ρ bounds into a `KerSide`, i.e. HtNums data;
- `rowsBody_colFace` (`ColumnsMemberRowsOfLogLevelLe.lean:25-57`) adds the last map (`period_le`,
  `lastMapNorm`) and the frames.

So, per lift step at place τ, as the Lean normalises it:

  log‖K_j‖²_{v=ρ|K} ≤ Σ_τ [ph(ν_{jτ}) − |ν_{jτ}|·logOmAt(ρ,τ)] + logThAt(ρ) + poly(x)·La.

**The single-derivative product formula, in the Lean's normalisations.** This is my reconstruction.
The Lean combines the two sides only through slopes (factor 2 on both: `muDef` = 2·slope, and the
enlargement adds 2Σ lw·⌊sg⌋, `C28:120-122`). For x = D^aθ(0)/Ω^a at one top place, one lift:

  (1/nPl) Σ_{v|∞} log|x|²_v  ≤  ph(a) − a·logΩ + poly·La
    [ph(a) = a log a − a = log a! + O(log a); mean over conjugates of log Ω^ρ = logΩ, proved]

  Σ_{p inert, w|p} 2·v_w(x)·log p  ≥  Σ_{n ≤ a/w, χ_d(n) = −1} 2Λ(n)(a/n − w)₊ − loss
    [Legendre minus the height-2 Lubin–Tate cost: γ_p = p/(p²−1) = Σ_{e odd} p^{−e}, NODE-LOCALDIV]

with Σ_v log|x|_v = 0. Using logΩ = γ + log(π/v) − L′/L(1,χ_d):

  ph(a) − a·logΩ = [a log a − a − γa + a·L′/L(1,χ_d)] − a·log(π/v),

and

  Σ_n Λ(n)(1 − χ_d(n))(a/n − w)₊ = w·[y log y − (1+γ)y + y·L′/L(1,χ_d)] + E_{χ_d}(y),  y = a/w.

The −a·log(π/v) and −a·log w terms are matched through log T(u) (Count5, `key_identity5`).

**Where the split half of log a! goes.** Write log a! = Σ_n Λ(n)⌊a/n⌋. Then

  Σ_n Λ(n)(1−χ_d(n))⌊a/n⌋ = log a! − Σ_n Λ(n)χ_d(n)⌊a/n⌋,  with Σ_n Λ(n)χ_d(n)⌊a/n⌋ ≈ −a·L′/L(1,χ_d).

So the split half is not absorbed by the norm normalisation. It is **the twisted sum, which equals
the −L′/L(1,χ_d) part of logΩ (Chowla–Selberg)**. Its fluctuation E_{χ_d} is not proved small
here; it is the host-selected pointwise RH-strength hypothesis `ValuesAtX` (NODE-ACCOUNT §3(vi)).
- The archimedean side is the whole log a! (squared norm), corrected by the Chowla–Selberg period.
- The p-adic side is twice the inert count.
- They agree to first order identically.
- Note the hX/L6 step: per (j, ρ), Σ_i ph(ν_i) ≈ log ∏ν_i! is cancelled by the hook product of the
  theta scalar λ_j except for **one** ph(a_t) at tops. So the factorial growth of the k·w-sized
  entries never meets the p-adic side.

### (c) Precision: each inequality and its loss

| step | where | kind | loss |
|---|---|---|---|
| Cauchy/Fock jet estimate | `BlockBound`, `NFL:262` | inequality | e·(2\|ν\|+2)^{2ab} per τ ⇒ Σ_τ(1 + 2N_{j−1}N_j·log(2Σν+2)) ≈ f·Nn²·La; polynomial, ≪ b |
| Gaussian growth constant S | logThAt; mean over ρ ≤ Ct·f·2L·N0N1 (`KHC:276-316`) | inequality, on average | f·Nn²·L |
| class/stab sums | cbSq = n n′ h h′ t; `classNumbers_leS`, `card_matrixStep_indices_le_exp`, `ncard_ybSet_le` | inequality | log(hh′nn′) ≤ C·errUnit = C·f·m²Nn²·log(g0 g1 T) ≈ poly·m·x^ε |
| scalar \|muInvDet\| ≤ 1 | `CKB:66-73` | inequality | 0 |
| per-place weighting of conjugates | `factorBounds_of_weights`, `exists_weights` | convex combination of bounds valid at the same place | 0 |
| mean of logOmAt = logΩ | `mean_logMetric_generator_eq_meanPeriod`, `meanPeriod` (`MLP:58-85`), `mean_log_area` (`MLC:141-197`) | **exact equality** (η-product Chowla–Selberg + Σ_s log\|s(Δ)\| = 0 for the unit Δ) | 0 |
| submultiplicativity along the chain | `height_chain_atR`, `complex_height_cast_at` | inequality | can be large in truth (alignment), but only as an upper bound |
| theta scalars | L6: log λ_j ≥ Σ_ρ logHook − C·f·nV²·Lp | **premise** (Published) | must be sharp to ≈ x^3·b out of ≈ x^7·b, i.e. relative x^{−4} |
| last map | LastSide/`period_le` | inequality | logc, logxi ≲ Nn·b′·log 2a ≤ a·La per top |

- Every proved inequality loses only poly(x)·La or |TT|·a·La. The coefficients of ph(ν) and of
  logΩ are not inflated anywhere.
- There is no inequality in the logΩ coefficient: Σ_i ν_{jτi} appears *exactly* as the jet degree
  (`Reads.sumNu`, `FB:83`).

**The logOmτ question.** In `kerSide_of_meansS` (`KHC:94-212`) the witness is
logOmτ(z, v) := Σ_ρ wt(v,ρ)·logOmAt(B, cD, M, ρ, s.iT(pl z)), with Σ_ρ wt(v,ρ) = 1 and
mean_v wt(v,ρ) = 1/[M:ℚ] (`exists_weights`). So:
- the true per-conjugate bound holds at each ρ;
- the per-place value is a convex combination of true per-ρ values for ρ above v;
- `i1` reduces to mean_ρ logOmAt = logΩ (`hlo`, `KHC:320-322`), which is the proved averaged
  Chowla–Selberg formula.

No discrepancy can hide, because htMap only ever uses the mean over places. *I infer* that the
conjugate periods differ genuinely: `mean_log_area` sums over a class-group family of lattices
(`exists_family`, `MLC:48`).

### (d) Why DIV's error is independent of m

The term (50C0+10)·|TT|·a·La of `rhs` (`INP:200-203`) collects three contributions:
1. hA's Ch·|TT|·b′·Nn·La ≤ Ch·|TT|·a·La, since b′·Nn ≤ a (p32, `INP:153`).
2. The top part of δ: |δ_{jρ}| contains C0·k·b′ for ρ ∈ TT (`sδ`, `INP:173`). Multiplied by
   |logΩ| ≤ La and summed over j < m and ρ ∈ TT, this is C0·|TT|·m·k·b′·La ≤ C0·|TT|·a·La, since
   m·k·b′ ≤ a (p33, `INP:155`).
3. The last-map logc/logxi (D0 ≲ bT ≤ 2b′ at tops), also ≤ |TT|·a·La.

Everything else is either exact or an m-term:
- **exact**: m·ph(a_t) from `weight_height_sum_le` summed over j, and m·a_t·logΩ from `weight_sum_eq`;
- **m-terms**: (pq_j − k)·w·logΩ and eE, both ≤ m·f·b·La ≈ m·B0.

So m-independence is a parameter choice: b′ = a/X′ with X′ = e^{x^{ε/3}} ≫ m·k·Nn. Each top
carries one large weight a_t, and all its other perturbations are smaller than a/(mk).

## 3. Children

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `LambdaLowerBound₂` ← `lamLow_of_hypotheses_alt_alt` | `TPS/Realised.lean:126`; `TPS/LamLowOfPublished.lean:18` | theta-lift scalar λ_j ≥ hook product·e^{−C f nV² Lp}, from 7 Published premises (Siegel–Weil, doubling, formal degree) | **core**, premise; precision-critical (relative x^{−4}) |
| 2 | `BlockBound` / `blockBound` | `PWN:36`; `NFL:262` | Cauchy/Fock bound for Taylor jets of Gaussian-growth entire functions | standard (Cauchy estimates in Bargmann–Fock space); proved |
| 3 | `meanPeriod`, `mean_log_area` | `MLP:84`; `MLC:141` | mean over conjugates of log(area(Λ^ρ)/π) = γ + log(2π/√d) − L′/L(1,χ_d) | standard (Chowla–Selberg/Kronecker limit formula, averaged); proved |
| 4 | `FamilyTie`, `FamilyVectors`, `PeriodLattices`, `CosetRefinement`, `FamilyNorms` | `CosetRefinement.lean:80-106` (defs); `normalisedFamily_*` | the CM theta function has Gaussian growth with the conjugate period lattice; coefficients in M; coset refinement | core analytic inputs; proved theorems, bodies **not opened** |
| 5 | `height_chain_atR` | `C28:124` | submultiplicativity + λ/κ frame scalars | glue (linear algebra) |
| 6 | `kerSide_of_meansS`, `exists_htNums_of_kerSide_lastSide` | `KHC:94`; `ColumnsMemberRowsOfLogLevelLe.lean:36` | packaging into HtNums | glue |
| 7 | class-number / index bounds | `KHC:222-225` | ≤ exp(C·errUnit) | standard-looking, not opened |

## 4. Oddities

1. **ACCOUNT's (C) is mostly a theorem, and its large partner is L6.** The hB term (≈ x^7·b) is
   proved. The equally large hX term is supplied by L6, a lower bound on Rallis-type scalars from
   `Published.*` premises. The cancellation C3 (Σph(ν) vs logHook) therefore rests on (i) a proved
   jet bound and (ii) a premise. The chain needs L6 sharp to relative x^{−4}. ACCOUNT listed C3 as
   "Stirling, fine". That is true only of the *numeric* step `weight_height_sum_le`, not of L6.
2. On the live path `logh, logh′ := 0` (`KHC:155`). These are upper-bound slots, so this is harmless.
3. The bounds at two conjugates ρ, ρ′ over the same place v can differ, because they use different
   conjugate periods. Both are claimed, so the true norm is ≤ the minimum. The averaging uses a
   convex combination, so this is not an error, but it shows the per-ρ bounds are not sharp at
   every ρ.
4. The `IndefExample.lean` instances set `l6 := 0`. They are not on the live path.
5. The last two steps are bounded jointly (`CplBound_sq`, `TPLT:117-120`), not separately.
   This is glue.
6. Nothing here forces B_u ≠ 0. The height clause is guarded by B_u ≠ 0 (as NODE-ROWSU says).

## 5. Coverage

Read:
- `SPL:40-70`; `INP:1-400`; `DHB:95-130, 240-252`; `C28:100-182`;
- `PTK:130-175`; `TPS/PointEvaluationSide.lean` (all); `TPS/RowsUOfColPins.lean` (all);
  `TPS/RowsUOfColPinsStatement.lean`;
- `MemberRowsOfKernelDatumSizes(Statement).lean`; `ColumnsMemberRowsOfLogLevelLe.lean` (all);
- `KernelHalfChainNumbersAnyLevelPrime(Statement).lean` (all); `FB` (all); `TPLT:1-200`;
- `NormsMatrixStepsCoupledFactorBoundedAnyLevelPrim(Statement).lean:1-40`; `CKB` (all);
  `PWN:1-80`; `NFL:262-300` (and its signature list);
- `CosetRefinement.lean:25-106`; `MeanPeriodLogarithms.lean`; `MLP` (all); `MLC:141-240`;
- `KerSizes.lean`; `RecHeightSWith.lean`; `KerSizesOfStdKer.lean`;
- `DIE6:1-60`; `IS:180-330`; `IndefUse.lean:330-345`; `ZON:55-100`;
- `IndefiniteRealisationChoice.lean:55-75`; `PackageFromPrimitiveStatements.lean:115-135`;
- `TPS/IpbOfLamLow.lean`; `TPS/LamLowOfPublished.lean:1-40`;
- `ThDistC.lean:30-75`; `CoefMod.lean:165-185`; `StatementCB.lean:15, 148`.

Not opened:
- the bodies of `normalisedFamily_*`, `cosetIndicatorThetaRefinement_proof` and `JetCConstMul.block`;
- `taylor_jetC`/`scalar_block` in detail;
- `exists_jetBlockBound_le_exp_kernelBound`; `period_le`/`lastMapNorm`;
- `finiteness_inputs_real_data_three_alt` (the L6 producer), and the `Published` premises' statements;
- `chowla_selberg_eta`; `NumFacts.weight_height_sum_le`.
