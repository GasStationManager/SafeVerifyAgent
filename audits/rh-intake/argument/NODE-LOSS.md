# NODE-LOSS: `Loss_at` / `LossFS`, and the lemma that supplies it on the live path

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
`GSB/` = `Formalism/SharpRestriction/GlobalSchurBounds/`, `GT/` = `Formalism/LocalToGlobal/GlobalTheory/`,
`GB/` = `Formalism/SharpRestriction/GrowthBounds/`, `SWB/` = `Formalism/SizeWindowBrackets/`,
`LS/` = `GB/LogarithmicSums/`.

## 0. Summary

On the live path the loss bound "Σ ASK − Ga ≤ C·|TT|·m·b" has **no divisibility content**. The per-prime
gain `gainP` is *defined* (`GB/IsResidueClassZero.lean:254-262,355-359`) as a rearranged copy of the inert-prime
ASK sum at p. It is built from γ_p = p/(p²−1) = Σ_{e odd} p^{−e} together with the elementary identity

  max(0, A/p^e − w) + min(A/p^e, w) = A/p^e, so Σ_{e odd} [max(0, A/p^e − w) + min(A/p^e, w)] = γ_p·A

(`ask_add_Mn`, `LS/PartnerCountOfCentral.lean:249-256`, and `gU_lower`, `:308-343`). The lemma "ASK_p ≤ gain_p + slack"
is therefore an accounting identity. Its slack terms (lo, fl, Pr, tv, Dp, dl) are then shown to be small by size
windows. Primes that are not served get trivial bounds. I found no integral object, no D^p ≡ 0, and no theta-lift
multiplicity in this node's proof. A divisibility statement of the expected shape does exist in the code (`admG1`, clause 3:
"every F ∈ NP has chainK^m(F) ∈ ϖ^{⌈(Σ_j gain_j)·v⌉}·Int"). It is **not used** for the loss bound, and on the live
LinkG path it is discharged with the **zero chain map** (`zeroCh`, `vKge_zero`), which makes it vacuous.
The real cost of Ga is pushed to the sibling clause `SlopesN_at`: μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo.

## 1. Statement

### `Loss_at` (`GSB/QuadraticLogDerivCongr.lean:203-210`)
```lean
def Loss_at (C eL : ℝ) : Prop :=
  IOsum L ≤ C * D.host.TT.card * D.R.m * L.sc.b * L.sc.x ^ (eL * L.sc.eps) ∧
  ∀ e m AD N TT a w, Reads L e m TT a w → HEq AD (arithOf D.host.toHostRaw) →
    (∀ j t ρ, t ∈ TT → InPhi ρ → a t / w j ρ ≤ N) →
    (∑ t ∈ TT, ∑ j : Fin m, ASK AD N (a t) t (w j)) - L.Ga ≤ C * |TT| * m * b * x^(eL ε)
```
`LossFS Fm eL` (`GSB/LossesSmallShares.lean:13-21`): ∃ C, x0, such that for every x ≥ x0 in the window there are an index i0 and weight
vectors av, bv (integers, a_t in the a-window, b' ≤ b_t ≤ bTop), carried by some index i1, and every index i that carries
(av, bv) satisfies `Loss_at (Fm.L x i) C eL`. On the live path eL = 0 (`lossF_of_7`, `:308`) and C = 3|K|+13
(`GT/LossRequirementsOfSmallShares.lean:105`).

### Unfolded
- **ASK** (arithmetic, `SWB/FirstPrimeNeSecondPrime.lean:84`, see NODE-COREGM): Σ over primes p ≤ N whose Frobenius is
  outside Φ ("inert"), 2 log p · Σ_{i, i·Frob∉Φ} max(a/p^i − w(partner), 0), plus a d-term. Via `Reads` and
  `askIsF` (`GSB/FrameCodeOfAdditive.lean:13-14,546`) it equals `LocalQuadraticParts.ASK L`. Via `ASK_at`
  (`GT/PowFourLtCeilThresholdPrime.lean:386`) that is the abstract
  `DeficitSplitLemmas.ASK Ps J TT ask dT = Σ_{j≤m} Σ_{t∈TT} (Σ_{p∈Ps} 2 log p·askAt_{j,t,p} + log d·askAt_d)`
  (`SWB/SecondKindBucket.lean:13-15`), with `askAt I a p w = Σ_{i∈I} max(a/p^i − w_i, 0)`, I = odd exponents (`:95-96`).
  Here Ps = `PsAt L` = primes p < bndP with `InertK D p`, i.e. p prime and `host.cls p ∈ {signal, inertClass}`
  (`GSB/ZetaZeroFreeRegion.lean:25-26`). *I infer* that this is "inert in the imaginary quadratic field K = ℚ(√−d)"
  (a variant in `GSB/GL3Theta.lean:115` is jacobi(−d, p) = −1). Weights: a_t ≈ x·b (one per target t ∈ TT), and
  w = fill(b, j, partner) − κ_j, where the lift index j runs over 1..m (`lifts = Icc 1 m`).
- **Ga** (`Formalism/LocalRingCardinality/DataParams₂.lean:220`): Ga = Σ_{w∈supp} sz(w, Σ_j gainD_j(w) − τ(w)), with
  sz(w, y) = 2·lwP(w)·e_w·y (`:211-212`), a sum of local quantities over places w of a field LL. `Ga_at`
  (`GT/PowFourLtCeilThresholdPrime.lean:210-245`) rewrites it as **GaW = 2 Σ_{p∈PsAt} log p·(Σ_j gainQ_j(p) − tauP(p))**.
  Here `ParametersFill` (`GB/IsResidueClassZero.lean:401-411`, a family field `Fm.fills`) pins
  `L.gain j w = gainP X K a b p j` and `L.tau w = tauP …`. So **gain is not a free real number. It is an explicit formula.**
- **gainP** (`GB/IsResidueClassZero.lean:355-359`) = Σ_{t0∈VV} max(gU − Pr, max(g0, 0)) + Σ_{t0∈reps∖VV} max(g0, 0),
  summed over Frobenius orbits t0. Here
  - gU(j,t0) = γ_p·Σ_{s∈orbit} al(s) − Σ_{s∉V} Σ_{e odd} min(al(s)/p^e, capU) − dl (`:254-258`), with
    γ_p = p/(p²−1) (`:89`), al = a − 2cG, capU = fillG + cG;
  - g0(j,t0) = Σ_s Σ_{e odd, ¬Excl} max(0, al(s)/p^e − capU) − dl (`:247-251`).
  
  Both are the ASK summand itself with slightly shifted parameters.
- **TT** = target set `D.host.TT` (|TT| ≈ x^{2+8ε}, NODE-COREGM); **m** = `D.R.m` = number of lifts j (≈ √x);
  **b** = `L.sc.b` (scale; a ≈ x·b).

## 2. Argument (live path)

`linkCore` ← `lossF_of_7 Fm (hL7 cTT cBad lG) cW` (`GSB/LossesSmallShares.lean:510-511`). Here hL7 =
`losses_of_small_share_weight` (`GT/LossRequirementsOfSmallShares.lean:86-163`) and lG : `LinkG Fm` is the output of
`closed_linkG_of_duty` (`Development/.../ThirdPlaceSeries/LinkG.lean:13-26`) → `linkG_concrete5` → `link_of_local_closed`
→ `linkG_fam_noKer` → `linkG_without_kernels` (`Formalism/LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean:224-239`).

1. **Prime classification.** `loss_setting_family` (`GT/LossRequirementsOfSmallShares.lean:43-82`) builds
   `PrimeClassLossHypotheses`. Each inert p is *served*, *first* (small Frobenius order), *second* (Σ-weight Sig > θ), or
   *high* (p > X''). Then `joint_discriminant_eventually` (`SWB/ChainSlopeWindows/DiscriminantSettingSatisfied.lean:234`)
   applies `loss_bound : SecondKindLoss` (`SWB/ChainSlopeWindows/AdmissibleSchurLemma.lean:762`; statement
   `SWB/SecondKindBucket.lean:261-297`).
2. **`SecondKindLoss`** is a split: ASK − GaW ≤ Σ_served 2 log p·servedLoss + Σ_{other classes} 2 log p·(trivial ASK)
   (`split_classes_count`, `SplitClasses` `:73-85`). Its only per-prime hypothesis is the **local clause**
   `SizeData₂ … p` (`SWB/SecondKindBucket.lean:45-48`):
   Σ_j Σ_{t∈TTp} (ask_{j,t,p} − lo(p)) − m·fl(p) ≤ Σ_j gain_j(p) − τ(p).
   It is a per-prime local statement, summed with weights 2 log p.
   Non-served primes contribute 4ma(log p/p)·|TT| each, which is controlled by `ChBadp_at`, `ChW_at` (lhsW ≤ x^{−9}) and FirstHyp.
   `size_core` then checks the total against (3C+13)|TT|·m·b.
3. **The local clause** comes from `lossHyp_at` (`GT/PowFourLtCeilThresholdPrime.lean:1989`) → `loss_bound_at`
   (`:766-816`), which reads it off the clause `LinkG_at.2.2` (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:127-133`).
   That clause is proved in `linkG_at_core` (`GB/PlaneCountTheoremWithConstants.lean:718-809`, second bullet) from
   `AuxBlock8.Conclusion1` (`GB/SmallOrderPrimes.lean:15-22`), which is `GainBoundAll`
   (`LS/Conclusion1OfGainBoundAll.lean:113-121`). That in turn comes from `StarAll` (`:129-136`),
   proved by `starAll_of`/`starAt_D`/`starAt_E` (`LS/PartnerCountOfCentral.lean:597-850`).
4. **Why ASK_p ≤ gain_p (the key question).** `StarAt`: Σ_{s∈orbit}(askP_s − lo) ≤ gU + dl − Pr − ⌈tv⌉ − Dp − 1.
   The core is `gU_lower` (`LS/PartnerCountOfCentral.lean:308-343`):
   Σ_s askP_s + Σ_{s∈V} Mn_s − N_v·3cG·log_p(2a) ≤ gU + dl. Its proof uses `ask_add_Mn` (`:249-256`):
   **askP_s + Mn_s = γ_p·a_s**, where Mn_s = Σ_{e odd} min(a_s/p^e, fill). This is the identity max(0, A−w) + min(A, w) = A,
   summed over odd e (`tsum_pos_add_min`). It also uses `odd_top` (`:270-296`, the same identity after the shift a → al, fill → capU).
   Since gU contains γ_p·Σ al − Σ min(…), gU is, up to O(cG·log_p a) per top, **equal to** Σ_s askP_s.
   The remaining slack (Pr, tv, Dp, dl, 3cG log) is absorbed by lo(p), and `numStar`/`caseD_arith`/`caseE_arith`
   show that it fits.
   **So the bound holds because the gain is defined to be the ASK.** No divisibility of any object is invoked.
5. The IO clause of Loss_at comes from `io_discriminant_bound` and `IO_at` (`GT/PowFourLtCeilThresholdPrime.lean:253`).

### The author's description vs the Lean
The divisibility the author describes ("each lift wins one unit of multiplicity, m ≈ √X lifts") matches *in shape*
`admG1` clause 3 (`GB/SmallOrderPrimes.lean:220-230`): ∀ F ∈ NP(u,w), `Y.vKge u w hg F (Σ_j gainP_j + lowFE)`, where
`vKge` (`GB/IsResidueClassZero.lean:420-422`) says (Ch.chainK m F) ∈ ϖ^{⌈g·v_w(p)⌉}·(Lv.Int m) (`vGeLat`, `:247` region).
In words: the m-fold iterated chain map applied to F is divisible by the uniformiser to the order of the total gain.
On the live path, however:
- `linkG_at_core` uses `hG1` only for the *length* clause lenMN ≤ duS·(τ + io), and never for the loss clause;
- `linkG_without_kernels` instantiates Y := `zeroCh (Fm.Gy x i)` (`AdmissibleFamilyNoKernel.lean:173-178,230-239`),
  whose chain `Ch` is identically 0. `vKge_zero` (`:185-193`) proves the divisibility from `0 ∈ submodule`.

## 3. (c) Local or global; which fields; pinned or free
- The bound is local: a per-inert-prime inequality, summed with weights 2 log p, plus trivial bounds for the other classes.
- It constrains `Dd.ASK`, `Dd.Ga` and `Dd.IO` (LossBounds in SizeData₂, `LossBoundsOfD` `SWB/PrimeClassLossHypothesesSatisfiable.lean:133-143`).
  On the live path these are pinned. IdentU pins Dd.ASK to the arithmetic prime sum. TieLocal pins Dd.Ga = L.Ga and
  Dd.IO = Σ lwP·e·io (`GSB/TieGlobal.lean:80-84`). L.gain, L.tau and L.io are pinned to the formulas gainP, tauP and ioP by
  `ParametersFill` (`Fm.fills`). So no free-real existential remains here: Ga is a definite number. That number is ≈ ASK by construction.
- Consequence: Loss_at is true but carries no information beyond "Ga ≈ ASK". The content sits wherever Ga is
  *upper-bounded*, which is `SlopesN_at` (`GSB/QuadraticLogDerivCongr.lean:180-182`):
  μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo. That is a lattice-index claim of size Ga ≈ ASK ≈ |TT|·m·a·log a.

## 4. Children

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `SlopesNF`/`SlopesN_at` ← `slopesNF_of`(`placesF_of`) | `GSB/QuadraticLogDerivCongr.lean:180,254`; `GSB/TopDensityNGeSixteen.lean:1544`; `GT/PlacesP.lean:638` | μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo | the place that actually pays for Ga; check whether its lattice index uses a real divisibility or the zero chain | **core** (not opened) |
| 2 | `gU_lower`, `ask_add_Mn`, `odd_top`, `starAt_D/E` | `LS/PartnerCountOfCentral.lean:249-343,597-840` | ASK at p ≤ gU + dl + O(cG log_p a) per top | the loss mechanism (identity max + min = A) | glue / elementary |
| 3 | `loss_bound` (`SecondKindLoss`), `split_classes_count`, `size_core` | `SWB/ChainSlopeWindows/AdmissibleSchurLemma.lean:762`; `SWB/SecondKindBucket.lean:261` | sum of the local clauses plus trivial bounds ≤ unit | summation and windows | glue |
| 4 | `ChBadp_at`, `ChW_at`/`chosenW_of` (Sig small for a chosen weight vector, by averaging) | `GSB/WeightVectorSmallSharesSeven.lean:17,30`; `GT/LossRequirementsOfSmallShares.lean:253` | the log-weighted count of non-served primes is tiny | controls non-served primes | core-ish (MeanKappaBound, from `AuxBlock8.Conclusion2`) |
| 5 | `MeanKappaBound` | `GB/IsResidueClassZero.lean:327-333` | the mean over the weight box of κ_v ≤ N_v·x^{−12} | feeds item 4 | definition to unfold |
| 6 | `admG1` / `vKge` / `zeroCh` | `GB/SmallOrderPrimes.lean:220`; `AdmissibleFamilyNoKernel.lean:173-193` | divisibility of chainK^m(F) by ϖ^{gain} | the "theta-lift multiplicity" object; vacuous on the live path | oddity |
| 7 | `askIsF`, `ASK_at`, `Ga_at`, `IO_at`, `ParametersFill` | `GSB/FrameCodeOfAdditive.lean:546`; `GT/PowFourLtCeilThresholdPrime.lean:210,253,386` | identification of the arithmetic ASK, Ga and IO with the abstract ones | glue | glue (askIsF body not read) |

## 5. Oddities
1. **Ga is ASK in disguise.** gainP is assembled from the same truncated sums max(0, a/p^e − w) as ASK, through
   γ_p·a − Σ min. The loss bound is therefore near-tautological. Every claim that Ga is "a sum of local multiplicities"
   has to be checked at the consumer (SlopesN_at), not here.
2. **Zero chain map.** The only divisibility-by-gain statement (`admG1` clause 3) is proved on the live path for
   `zeroCh`, i.e. for the zero map, via `vKge_zero`. If any downstream consumer (for example SlopesN or a lattice N_u
   built from Ch) relies on it, that consumer gets nothing.
3. `Loss_at` quantifies over all `Reads` and every HEq-equal ArithData. This is harmless here because `askIsF` rewrites them.
4. `PrimeClassLossHypothesesSatisfiable` (`SWB/PrimeClassLossHypothesesSatisfiable.lean:154`) is a sanity check with
   |J| = |TT| = 1. It is not on the path.
5. The served/non-served split uses `TTp p` (tops in served orbits). Tops outside it are charged to BAD, bounded by
   `badPrimeLogWeightedCount ≤ |TT|·x^{−2+ε}`, a hypothesis supplied by `ChosenBadp`. I did not trace it.

## 6. Coverage
Read: `GSB/QuadraticLogDerivCongr.lean:180-212`; `GSB/LossesSmallShares.lean:1-60,280-320,455-515`; `GSB/TieGlobal.lean:55-100`;
`GT/LossRequirementsOfSmallShares.lean:1-350`; `GT/SmallShareWeightExists.lean`; `SWB/ChainSlopeWindows/DiscriminantSettingSatisfied.lean:180-245`;
`SWB/WindowSettingSatisfiable.lean:225-300`; `SWB/PrimeClassLossHypothesesSatisfiable.lean:60-160`; `SWB/SecondKindBucket.lean:1-130,255-297`;
`SWB/ChainSlopeWindows/AdmissibleSchurLemma.lean:762-787`; `GT/PowFourLtCeilThresholdPrime.lean:186-246,760-816,1985-2005` + decl list;
`GlobalTheoremInputs.lean:100-150`; `Development/.../ThirdPlaceSeries/LinkG.lean`; `.../GlobalInterpolation/LinkGl.lean:1-35`;
`GroupLattices/LinkGConcreteNoKer.lean`; `GroupLattices/AdmissibleFamilyNoKernel.lean:140-290`;
`GB/PlaneCountTheoremWithConstants.lean:219-246,705-900`; `GB/SmallOrderPrimes.lean:1-60,205-275`;
`GB/IsResidueClassZero.lean:225-275,280-500`; `LS/Conclusion1OfGainBoundAll.lean:99-160`; `LS/LogarithmicSums.lean:1-105`;
`LS/StarFam.lean`; `LS/PartnerCountOfCentral.lean:136-150,246-345,820-850`; `GT/IsResidueClassZero.lean:60-200` (parallel defs);
`LocalRingCardinality/DataParams₂.lean:205-240`; `GSB/ZetaZeroFreeRegion.lean:20-40`.
Not opened: `starAt_D/E` bodies (only their tail), `numStar`, `size_core`, `askIsF` body, `SlopesNF`/`placesF_of`,
MeanKappaBound proof, `Inst` structure, `host.cls`.
