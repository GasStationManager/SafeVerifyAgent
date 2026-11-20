# REVIEW-TWU (reviewer; did not write NODE-TWU)

Paths are relative to `.../scratchpad/art/lean/src`. IRZ, WJS, FGS, GG/, SP/ are abbreviated as in NODE-TWU.
Abbreviations for new files:
- `UQS` = `Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean`
- `CGL` = `Formalism/SharpRestriction/GrowthBounds/CornerGLContinuity.lean`
- `TCB` = `Formalism/SharpRestriction/GrowthBounds/TopChoiceBounds.lean`
- `C1G` = `Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean`
- `PCC` = `Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean`
- `WSE` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedSlopeExcessDecomposition.lean`

## Verdict: NEEDS-DETAIL

The bookkeeping in NODE-TWU is right, and the margin clause exists. The node's headline framing is not right,
and one of its rendering claims is false.

- The framing is "Hecke images gain γ_p·Σa". Read in the Lean, the theorem on the live path amounts to a
  **Hecke-free** divisibility of the chain on the whole integral lattice: chainK_m(M) ⊆ ϖ^{≈ASK}·Int_m (§2).
- The rendering claim is that "at μ = muAt(w) the chain is the family's own". It is false: the chain is an
  existentially chosen local model (§3).

Neither point is a defect. Both move the burden onto two children that are still unopened: the existence of the
model chain LC with its valuation-reflection clause, and the normalisation of Int_m.

## 1. NP, the direction of the argument, and τ against the gain

**Direction.**
- NP = span{yProd(VV′)(p^{Σ_{VV∖VV′}⌈Sv⌉}F)} ⊓ p^{⌈τ⌉}M ⊓ Vram (`IRZ:464-476`).
- vKge is closed under O-linear combinations. So divisibility on the generators gives divisibility on NP.
- More generators make NP bigger. That makes divisibility *harder* to prove and colength *easier* to bound.
- So the p^{Sv} generators cannot be a hidden free gain on the divisibility side. NODE-TWU is right on this.

**Mismatch 1.** NODE-TWU says the colength is "capped by the VV′ = VV generators alone". That is not what is stated:
- `LemmaVVolumeGeneral` (`FGS:832-847`) bounds the colength of the full NP.
- io = 2·Sig·max_{t0} Sv (`IRZ:348-352`) is exactly the price of using the p^{Sv} generators on the κ-exceptional part.
- This is harmless, because Sig ≤ x^{−ε} whenever VV ≠ ∅ (`IRZ:296-297`).

**Colength statement** (`SmallOrderPrimes.lean:220-230` = `LemmaVVolumeGeneral`):
- NP ≤ p^{⌈τ⌉}·Mram;
- length(Mram/NP) ≤ vUnit·d·(τ+io), with d = finrank M = duS (`PlaneCountTheoremWithConstants.lean:753`).

**`gluing_statement_holds`** (`TCB:1639-1648`) proves only clauses 1-2 of admG1, from `LemmaVVolumeGeneral` with
OrbitLatticeBounds/LPprime, LatticeSandwich and saturation. Clause 3, the divisibility, is the *hypothesis*
`ServiceLowerValuation` passed straight through (`exact ⟨h12.1, h12.2, hS1 …⟩`). On the live path this hypothesis
is discharged only for `zeroCh`, by `vKge_zero` (`AdmissibleFamilyNoKernel.lean:183-206`). NODE-TWU's account of
this point is consistent with the Lean.

**τ and io as formulas.**
- τ_p = ep + Σ_{t0∈VV} m·(⌈tv⌉ + Dp + 1) (`IRZ:338-342`).
- For p ≥ p0 (`IRZ:217-225`), tv = Σ_{y ∈ TT, ¬V} min(b_y, a_{y−d}/p^d) + κ1·|TT|·N1·(a/p² + La·a/(pk)) + lower-order terms,
  where d = dMinus(y).
- **τ is not small compared with the gain.** Its main term is of order a/p per non-V top, which is the same order as
  gU ≈ γ_p·Σa. Two global budgets confirm this:
  - `CutSizes` (`CGL:205-210`);
  - `WeightSumBound` (`CGL:212-213`), which gives Σ_w sz(τ_w) ≤ C·m·|TT|·a·log X′. Gain is of the same size, Σ_p (log p/p)·a·|TT|·m.
- io is small. It equals 2·Sig·max Sv ≤ 2x^{−ε}·O(m·|TT|·a/p).

**The clause that keeps gain − τ ≥ ASK.**
- `StarAt` (`C1G:129-131`), for **each** lift j: Σ_{s∈orbit}(askP − lo) ≤ gU + dl − Pr − ⌈tv⌉ − Dp − 1.
- It is proved in two cases:
  - p < p0, by `starAt_D` (`PCC:597`);
  - p ≥ p0, by `starAt_E` (`PCC:696`).
- It is assembled into `GainBoundAt` (`C1G:113-120`): Σ_j Σ_s(ask − lo) − m·fl ≤ Σ_j gain − τ.
- The m copies of (tv + Dp + 1) in τ are matched one-for-one by the |lifts| = m copies of StarAt.
- Mechanism: on IsV tops, gU subtracts no min(a/p^e, cap). That surplus has to cover tv, which comes from the
  ¬V tops. The covering is a combinatorial pairing inside `caseD_arith`/`kinkHH`, which I did not read.

**Rank mismatch, handled.** The global rank is du = duS·(1 − 1/(T−1))^f (`FamRec.lean:179`), smaller than the
local d = duS. The extra cost de/(1−de)·Ta is carried explicitly (`WSE:139`; `be` at `ClaimGaFree.lean:33-34`).

## 2. Is the divisibility just the p^{ArV·m} in yv? No. The burden moves, but not to heights

- ArV = Σ_s Σ_{i<r} λ_{s,i} (`UQS:124-125`, `DataG.lean:91`). This is the standard integral normalisation of T_r,
  the transport factor between H(L″) and H(L).
- LPprime (`UQS:205-220`) uses the same p^{Ar} (in `be`, `UQS:140-142`, and in `Re`/`Re′`). It says the normalised
  operator is near-surjective up to p^{tv+Dp}. So p^{ArV} is not a surplus.
- **No archimedean cost arises.** NuLat is an O-sublattice of M with M's metric, and the slope uses only colength
  (`WSE`). The archimedean norm of yv^m F never enters, so there is nothing to "pay" in heights.
- **Key sharpening.** NP ⊆ p^τ·Mram and colength ≤ d(τ+io). Therefore:
  - divisibility on NP is equivalent, up to d·io, to chainK_m(Mram) ⊆ ϖ^{Σgain − τ} ⊇ ϖ^{≈ASK};
  - `UAt` (`WJS:161-170`) with VV′ = ∅ already states chain(F) ≥ Σ_j Σ_{reps} g0⁺ + low for **every F ∈ M**, with no Hecke operator;
  - g0 (`IRZ:245-249`) is the ASK summand with shifted parameters (al = a − 2cG, cap = fill(partner) − kaJ + cG).
- So the main-term claim is a Legendre-type divisibility of the m-fold theta chain on all integral forms. The Hecke
  images only buy the γ_p surplus that pays τ.

## 3. Is it the same chain as the B_u pairing?

**Mismatch 2.** NODE-TWU §1 says "at μ = muAt(w) it is the family's own". In fact:
- `reY Y LC` (`GG/ModelsOK.lean:12-19`) *replaces* Lv and Ch by LC(muAt w).
- `reW`'s LC_muAt holds by `rfl` for that reason.
- RowTwU (`:41-44`) quantifies ∃ LC.

So the local chain, and Int_m with it, is an existential model. Its only link to the real periods is `CmpLite` (`:46-55`):
- it intertwines with (D.chTw u μ).K j;
- cmp 0 ∘ e0 = c.cmp;
- it has a **valuation-reflection** clause: vGeLat(Int_m)(cmp_m y) s → VGe((Tw.fm u μ).lat m) y s.

What this does and does not exclude:
- A tiny Int_m would make the local divisibility easy, but it would make reflection hard. So this is where the
  normalisation is decided.
- Zero is excluded: a zero LC forces the global chain to be zero.
- Remaining links not checked:
  - ColGeTw uses (D.chTw u μ).col (`WJS:28-31`), but CmpLite intertwines .K j. That col = K_{m−1}∘…∘K_0 is not shown here.
  - adm2 (`LocalQuadraticParts.lean:206-210`) is about perCol(muAt w)(jN φ)F for φ ∈ NuLat. Its bridge to ColGe and InNP (`WJS:60-63`) is unopened.

## Gaps

- The bodies of `starAt_D`/`starAt_E` (via `caseD_arith`) are unread. Those are where "the V-surplus covers tv" is proved.
- The existence of LC with reflection is unread: `modelsAt_bpt` ← `tuplesHaveLocalModels_of_standardColumnObjects`.
- `col` against ∘K_j is unread, and so is perCol ↔ ColGeTw (`perCol_eq_pairing_of_kills`, `RationalPairingEqColumnPairing.lean:58`).

## Expand next (ranked)

1. **`tuplesHaveLocalModels_of_standardColumnObjects`.** How are Int_m and cmp_m chosen? Is the reflection clause proved
   honestly? Check in particular that (Tw.fm u μ).lat m, a TwForms field from `Fm.ex`, is the lattice adm2 is integral against.
2. **`stmt_proved` at VV′ = ∅.** What makes chainK_m(M) ⊆ ϖ^{Σg0⁺}·Int_m true? Which clause of `admitted` carries it?
3. **The bridge adm2 ← Conclusion1.** Check perCol = pairing of chTw.col with F, and col = ∘K_j.
4. **`caseD_arith` / `kinkHH`.** Check the V-top surplus ≥ ⌈tv⌉ + Dp + 1 per lift, with constants.

## Escalation for an expert (ten-minute check)

**E-TWU-1.** Strip away the Hecke operators. The claim is that the composite of m theta-lift steps between definite
unitary groups, evaluated as Bessel periods at an inert p, is divisible by Σ_s Σ_{e odd} max(0, a_s/p^e − w_s) on
**every** integral form of weight a. This is a Legendre-type exponent.

- Locally, such factors can arise from branching or projection coefficients.
- But the factor depends entirely on how Int_m and the period lattice are normalised relative to the archimedean
  size of the periods. That size is the height h(u), which is fixed independently of a.

Check one case, m = 1 and small n: does the integral-normalised theta kernel really carry p^{Σ max(0, a/p^e − w)}, or
does that factor cancel against the normalisation of the target lattice?
