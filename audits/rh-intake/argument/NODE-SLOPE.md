# NODE-SLOPE: the degree/slope side (`SizeData₂` clauses, `LinkDIV_at`, `TieLocal`, the slope inequality)

Paths are relative to the source root `.../scratchpad/art/lean/src`. Abbreviations:
`MB` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`, `QSB` = `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`,
`LoC` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`,
`WMD` = `Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean`, `QLD` = `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`,
`DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`, `DA` = `Formalism/LocalRingCardinality/DataArith.lean`,
`GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`, `LSS` = `Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean`,
`TG` = `Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean`, `RB` = `Formalism/LocalToGlobal/Divisibility/RecBridge.lean`,
`FTR` = `Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean`.

## 0. Summary

- The 11 clauses of `SizeData₂` are inequalities between real numbers. Together with one exact algebraic identity (`key_identity`),
  they give ASK ≤ Main + ErrX5at by linear arithmetic. I reconstruct this in ten lines in §2(a).
- **The Fo terms cancel.** Fo enters DIV with a minus sign and the lower quotient-slope bound with a plus sign.
  So the chain only says this: the gain Ga, which is inserted into μ(N_u) by QuotientSlopeBounds, is at most (slope of
  the target) + h, by the slope inequality. That in turn is at most MAIN, by DIV.
- On the live producer `linkCore` (`LSS:38`), every field of `Data` is a concrete expression: `Mod.data`, `QLD:464-510`.
  The exceptions are η(u0) and e(u0), which come from an existential in `Frame_at`.
- Those concrete expressions are, however, fields of two **abstract records**: `D7` (`Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:76`)
  and the per-datum record `SizeData₂ D` (`DP2:76`). In the second record the local data `gain, F, E, tau, io` are **free
  function fields** (`DP2:93-97`). They are constrained only by family-level Link hypotheses.
- **The γ, log π and L'/L(1,χ_d) in MAIN are put in by definition**, through `logOm` (`DP2:224`). They are not produced by a
  computation in this node.
- The slope inequality is a genuinely proved Lean theorem, `joint_a_ramified_holds` (`JointDModelAppliesUnitLattice.lean:254`).
  It is a mean-slope inequality for families of maps into a dual lattice whose archimedean matrices form an almost tight frame.
- `ChainTied.core_of` (`TG:116-124`) **discards** TiePts/TieGlobal/TieLocal/TieArith (`-` patterns). The chain itself never uses the ties.
  They matter only as constraints that the producer of ChainTied has to meet.

## 1. Statement

### (a) `Data U0 W Top m f` (`MB:37-76`). Every field is a real number or a real-valued function.
Index sets: u0 ∈ U0 is the "unit" (an element of A0 ⊆ A). u ∈ W u0 are the "words". t ∈ Top are the targets (≅ TT).
j < m are the copies (lifts). ρ < f are the places of Φ.

| field | type | meaning on the live path (`Mod.data`, `QLD:464-510`; TieGlobal/TieLocal `TG:48-82`) |
|---|---|---|
| x, ε | ℝ | the scale x and ε |
| a, b, b' | ℝ | sc.a = x·b, b = exp(x^ε), b' = a/X' with X' = exp(x^{ε/3}) (`DP2:30-40`) |
| k | ℝ | rank parameter R.k |
| L, La | ℝ | L = x^ε; La = log(a·rdE) |
| B0, Nc | ℝ | size budgets: B0 = f·m·b·x^ε; Nc = budgetNc |
| gam, LpL | ℝ | γ (Euler's constant); L'/L(1, χ_d) for the quadratic character mod d (`DP2:63-70`, `logDerivative_at_one_eq`) |
| v, lg, logGam | ℝ | host.v; log(g0·g1) for two auxiliary primes g0, g1; log GamL |
| aT t | ℝ | integer weights a_t ∈ [a, a(1+…)] (the Riesz lengths) |
| w u0 j ρ | ℝ | weights wj(j,τ) = HC-parameter entries e_j (`DP2:72`) at the places of Φ |
| d u0 u | ℝ | rank of the hermitian lattice N_u = div.Nu u |
| T u0 u | ℝ | a prime T(u) = (mem u).A.T (the "auxiliary prime" of word u; see AdmT, `DP2:182`) |
| muN, muMaxN | ℝ | μ(N_u), μ_max(N_u) |
| h u0 u | ℝ | div.h u: an upper bound for the height of the map B_u (on the live path, = hExpl6) |
| muM, muMaxM | ℝ | μ, μ_max of M_u = (fm u).lat 0 |
| EeJ u0 u j | ℝ | Σ_w sz(w, E(u, j, w)), a local "exceptional" term; E is a free field of the record |
| muCC, muMinCC | ℝ | μ and μ_min of the dual lattice RR^∨ (target) |
| Fo, Ga, Ta | ℝ | Fo = Σ_j Σ_w sz(F_j(w)); Ga = Σ_w sz(Σ_j gain_j(w) − τ(w)); Ta = Σ_w sz(τ(w)) (`DP2:218-220`) |
| ASK | ℝ | Σ_t Σ_j ASK(a_t, t, w_{u0,j}), the inert prime-power count (pinned by Ident, `SChain.lean:25-30`) |
| IO | ℝ | Σ_w lwP·e_w·io(w) |
| HH | ℝ | x^{CH}·b (a constant) |
| del | ℝ | what₂.delp ≤ exp(−x^{ez/7}) |
| η, e | ℝ | ηv(u0), ev(u0): **existential witnesses from `Frame_at`** |
| delBar, etaBar, eBar | ℝ | exp(−x^{ez/7}); etaB, eB from FrameF |

Here sz(w, y) = 2·lw(w)·e_w·y, a local-degree weight (`DP2:204`).

### The 11 clauses of `SizeData₂ Dd C Xpp` (`SChain.lean:17-19`)
Derived quantities: s = Σ_u d_u(μN_u − h_u)/Σ d_u; uF = max_u(μmaxN_u − h_u) − s; logΩ = γ + log(π/v) − LpL;
Ee(u) = Σ_j EeJ; ph(y) = y log y − y (`MB:9-105`).
1. **HidaSetting** (`MB:111`): positivity (x, b, k, v, f, d_u, T_u, w > 0, a_t ≥ 0), μN ≤ μmaxN, δ̄ < 1, 0 ≤ ē ≤ 1/4. No geometric content.
2. **DIV** (`MB:118`): μCC + h(u) − Fo ≤ Σ_t [m(ph(a_t) − a_t logΩ) − a_t log T(u)] + EDiv, where EDiv = cDiv·nT·a·La + cDiv·m(B0+Nc)x^{eDiv ε}.
   This is the "degree" bound: the dual-target slope plus the height of the evaluation map is at most the archimedean degree (MAIN).
3. **EComp5** (`QSB:24`): |Ee(u) − m·ΣA·lg| ≤ cE·m·B0. The exceptional local term equals m·ΣA·log(g0 g1) up to error.
4. **HComp** (`MB:126`): h(u) + ΣA·log T(u) varies little with u.
5. **Count5** (`QSB:27`): Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − cCount(La + m²La/k) ≤ log T(u) ≤ cCount·m·L, and |log T(u) − log T(u')| ≤ cCount·log k.
   This is the size of the auxiliary prime T(u).
6. **Slopes** (`MB:139`): −cSlope·nT·a·La(1+m/k) ≤ μ(M_u) and μmax(M_u) ≤ cSlope·nT·a·La.
7. **QuotientSlopeBoundsWith** (`QSB:19`): μmax(N_u) ≤ μmax(M_u) + Ga + Fo − Ee + cSl1·m·B0 and
   **μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee(u) − Lo5(u)**, where Lo5 = cSl1·IO + cSl1·nT·m(a/k + b')·log T + cSl1·Xpp + 1.
   The slope of N_u is that of M_u raised by the local gains: N_u is an elementary modification of M_u at the places w, with
   multiplicities gain + F − E.
8. **LossBounds** (`QSB:34`): ASK − Ga ≤ LoP := cLoss·nT·m·b·x^{eLoss ε} and IO ≤ LoP.
9. **SlopeIneq** (`MB:151`): (for admissible δ, η, e, HH) s − log|W| − (1−δ)^{-1}(4uF·log(1+HH/uF) + (η+4√e)HH) ≤ μCC.
10. **HHBound** (`MB:158`): s − μminCC ≤ HH, 0 < HH ≤ x^{cHH}·b.
11. **FParams** (`MB:161`): 0 ≤ δ ≤ δ̄, 0 ≤ η ≤ η̄, 0 ≤ e ≤ ē.

### `LinkDIV_at L C Cabs CH` (`GTI:77-89`)
The datum's lattices satisfy all of the following:
- (i) B_u(N_u) ⊆ cc = RR^∨ (`OneMapIntoCC`, `DA:178`);
- (ii) s + μmax(RR) ≤ x^{CH}·b;
- (iii) ZeroAbove (gain and E vanish above X'');
- (iv) BesselId: B_u is a nonzero multiple of an explicit Bessel-type pairing besS u (U φ)(V F), up to isometries;
- (v) RR is of full rank;
- (vi) htMap(B_u) ≤ h(u), i.e. (1/#places)·Σ_v log‖B_u‖_v² ≤ h(u);
- (vii) **μ(RR^∨) + h(u) − Fo ≤ MAIN(u) + C·|TT|·a·La + C·m(B0+Nc)x^{Cabs ε}**;
- (viii) EComp;
- (ix) HComp.

Here MAIN(u) = Σ_t [m(ph(a_t) − a_t logΩ) − a_t log T(u)], with logΩ = γ + log(π/v) − L'/L(1,χ_d) (`DP2:224,232-234`).

### `TieLocal` (`TG:63-82`): see the table above. It equates d, T, μN, μmaxN, h, μM, μmaxM, EeJ, μCC, μminCC, Fo, Ga, Ta, IO and δ with the D7/SizeData₂ fields.

## 2. Argument

### (a) The ten-line derivation (`LoC:50-197`; identity `WMD:170-218`)
Fix u0 and write ΣA = Σ_t a_t and Λ5 = Σ_j mean_ρ log(w v/π) + m·lg − cCount(La + m²La/k).
1. [QSB lower] μN(u) ≥ μM(u) + Ga + Fo − Ee(u) − Lo5(u).
2. [Slopes lower] μM(u) ≥ −cSlope·nT·a·La(1+m/k). [EComp5] −Ee(u) ≥ −m(ΣA·lg + cE·B0).
3. [DIV] −h(u) ≥ μCC − Fo − SDiv + ΣA·log T(u) − EDiv, where SDiv = Σ_t m(ph(a_t) − a_t logΩ). **Adding to 1: the Fo terms cancel.**
4. [Count5 lower] ΣA·log T(u) ≥ ΣA·Λ5. Averaging over u with weights d_u = rk N_u (`s_lower5`, `LoC:50`) gives
   s ≥ Ga + μCC − K5 − wmean(Lo5), where K5 = cSlope(…) + m(ΣA·lg + cE B0) + SDiv − ΣA·Λ5 + EDiv.
5. [SlopeIneq] s − μCC ≤ log|W| + Φ, where Φ = (1−δ)^{-1}(4uF·log(1+HH/uF) + (η+4√e)HH).
6. From 4 and 5: Ga ≤ K5 + wmean(Lo5) + log|W| + Φ.
7. [key_identity5, `LoC:105`, pure algebra] SDiv − ΣA·Λ5 + m·ΣA·lg = Main + ΣA·cCount(La + m²La/k).
   The log(π/v) in logΩ cancels against the log(v/π) in Count; the m·lg terms cancel between EComp and Count.
   What survives is Main = Σ_j Σ_t a_t(log a_t − 1 − γ + LpL − mean_ρ log w_{jρ}).
8. [Φ bound] uF ≤ K3 + wmean(Lo5) (`u_function_le_mean`, `LoC:81`: uses QSB upper, Slopes upper, HComp, EComp, Count third
   clause). With HHBound (HH ≤ x^{cHH}b), FParams (δ ≤ δ̄, η ≤ η̄, e ≤ ē) and `phi_bound`:
   Φ ≤ (1−δ̄)^{-1}(4 log(1+x^{cHH})(K3 + wLo + b) + (η̄+4√ē)x^{cHH}b).
9. [Count5 middle + LossBounds 2nd] wmean(Lo5) ≤ cSl1·IO + K7 ≤ MLo5 (`LoC:162`).
10. [LossBounds 1st] ASK ≤ Ga + LoP ≤ Main + ErrX5at (`each_unit_bound_statement`, `LoC:175`).

Terms of ErrX5at (`QSB:45-54`) and their sources:
- ΣA·cCount(La + m²La/k): Count5.
- EDiv: DIV.
- m·cE·B0: EComp5.
- cSlope·nT·a·La(1+m/k): Slopes.
- log|W u0|: SlopeIneq.
- LoP: LossBounds.
- MLo5: QSB loss, with Count and IO.
- (1−δ̄)^{-1}(…): the SlopeIneq correction, through HHBound, FParams, HComp and the QSB upper bound.

### (b) What the objects are on the live path
**What the Lean says.**
- `D7` (`RhoDetPrimeEqMuTildeMulChiPow.lean:76-140`) is a structure. It has:
  - ranks R and a host (a CM field E/F with conjugation and auxiliary primes q, d, g0, g1);
  - a totally complex Galois field LL = what₂.LL;
  - Harish-Chandra parameters hc τ (one per place τ ∈ Ψ of the frame);
  - for each word u, a `Member` (ColumnChain, ColumnsAtT, **PeriodMap**) with an auxiliary prime T(u);
  - `div : DivData LL Words` (`DA:139-160`).
- DivData consists of:
  - a hermitian O_LL-lattice RR (an `HLat`: a K-space with a basis, a matrix X_v at each infinite place, and an O_LL-submodule; `DA:61-86`);
  - for each word u, a hermitian lattice N_u;
  - maps B_u : N_u ⊗ LL → (RR)^∨;
  - reals h(u), HH, etc.
- Slopes are Arakelov slopes normalised as μ = 2·slope − log 2 + log|disc LL|/[LL:Q] (`Formalism/HarderNarasimhan/StatementPl.lean:76-84`).
  The height of a map is htMap = mean over v of log‖B‖_v² (`:60-65`).
- `BesselId`/`BuRational` (`GTI:69-71`, `RhoDet…:353-365`) identify B_u with a Bessel-period pairing. The pairing is
  ⟨s_EE F, P_u(φ)⟩, i.e. an inner product of a vector of EE with the period map P_u applied to φ ∈ Mu u.

*I infer* (from these names, BesselId, PeriodMap, and the ROOT node's unitary-group/theta inputs) the following reading.
N_u is a lattice of automorphic forms with an integral structure, for a unitary group attached to E. RR^∨ is a lattice of Bessel/period
functionals. B_u is the evaluation-by-periods map, and its integrality (OneMapIntoCC) plus injectivity gives the slope
inequality. The auxiliary prime T(u) splits in K as ππ̄ (AdmT, `DP2:182-188`), which points to Hecke/CM points.
I did not find a Shimura variety or a CM abelian variety as a Lean object in this node. Everything is a hermitian lattice
over O_LL with arbitrary metric matrices X_v, which are fields of D7. Concrete ties to automorphic objects (RowSideTie,
`LocalToGlobal/Divisibility/RowSideTie.lean:194-257`; DivisionRows in `RB:380ff`) exist upstream. I did not unfold them.

**The slope inequality actually used** (`JointARam`, `FTR:197-221`; proved as `joint_a_ramified_holds`,
`Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean:254-257`, via `ramification_condition_holds`
and `flat_lattice_theorem_holds`, which I did not open). Hypotheses:
- (`LatGeom`, `FTR:59-77`) B_i(N_i) ⊆ cc, htMap(B_i) ≤ h_i, and (1−δ)|κ⊔κ₁| ≤ |κ|.
- (`LatNum`, `FTR:79-90`) s ≤ the rank-weighted mean of μ(N_i) − h_i; μmax(N_i) − h_i ≤ s + u; and s − μmin(cc) ≤ HH.
- (`InputSG`, `FTR:30-35`) the archimedean matrices of the B_i at one place v form an almost tight frame:
  - off-diagonal Hilbert–Schmidt ≤ (1+η0)d_i d_j/D*;
  - diagonal deviation ≤ e0·d_i;
  - target dimension ≤ (1+η1)D*.

Then

  s − log|I| − (1−δ)^{-1}·(4u·log(1 + HH/u) + ((5σ + 3√de) + 4√(2e0))·HH) ≤ μ(cc) = μ(RR^∨).

`frame_at_of`/`frameF_of` (`Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:536-640`) turn this into
`Frame_at` (`QLD:188-194`), which is the SlopeIneq clause with η = 5σ + 3√de, σ = x^{−CH}, and e = 2e0.
This bounds the weighted mean slope of the sources (minus heights) by the **mean slope of the target**, not by its μ_max.
That is why near-isometry (InputSG) and near-full rank (δ ≈ 0) are needed.

**DIV** is `WordFacts`' third clause (`RB:128-133`). It is supplied per word by `DivisionPackageFace.wordFacts` and
assembled in `linkDIV_at_words` (`RB:327-343`), with h pinned by `Fm.h_eq : div.h u = hExpl6 …`.
- hExpl6 (`Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean:25-27`) is an explicit sum of Σ ph(ν_i) − |ν|·logΩ
  ("kernel place" terms), minus hook-length / log-Γ terms (logHook = Σ log Γ(a_i+n−i) − Σ log(a_i−a_l+l−i)), minus the
  mean log of the archimedean κ.
- MAIN is matched to the numerical datum's `mainT` by the record field `NumRecTie.mainT` (`RB:250-251`, `rhs_le_record`, `RB:261`).
- I did not open DivisionPackageFace. It is the child where the actual inequality μ_dual + h − Fo ≤ MAIN is proved.

### (c) MAIN, and where y log y − (1+γ)y comes from
In the lattice language, MAIN(u) = Σ_t [m(ph(a_t) − a_t·logΩ) − a_t·log T(u)]. This is m copies of the archimedean degree
a log a − a − a·logΩ per target, minus the contribution a_t·log T(u) of the auxiliary prime.
- After Count (log T ≈ Σ_j mean log(w v/π) + m·lg) and EComp, the key identity rewrites it as
  Main = Σ_j Σ_t a_t(log a_t − 1 − γ + L'/L(1,χ_d) − mean_ρ log w_{jρ}).
- On the prime side, the same expression is the explicit-formula main term of Σ_{n} Λ(n)χ(n)(a/n − w)_+. With w = 1 and
  χ trivial, that is the Riesz main term a log a − (1+γ)a.
- **In the Lean the match is by definition, not by computation.**
  - ph(y) = y log y − y is Stirling's main term for the log-Γ / hook-length expressions in hExpl6 (*I infer*: the HC
    parameters have size ≈ a).
  - The constants γ, log(π/v) and −L'/L(1,χ_d) come from `SizeData₂.logOm := γ + log(π/v) − logDerivativeAtOne`
    (`DP2:224`), whose last term is pinned to L'/L(1,χ_d) (`DP2:150-151`).
  - *I infer* that logΩ is meant as a Chowla–Selberg/Colmez-type log-period of the CM field (the Faltings height of CM points
    involves exactly γ, log π and L'/L(1,χ)). The node contains no theorem identifying it with a period.
    Whether DIV holds with this logΩ is the content of DivisionPackageFace.

### (d) THE PINNING QUESTION
- **Consumer side.** `ChainTied.core_of` (`TG:116-124`) drops the four Tie clauses. `ChainCore` sees only the existential Dd with
  SizeData₂ + Ident + windows. So for the chain, Dd is existential: any reals satisfying the clauses would do. IdentU still
  pins ASK, aT, w, γ and LpL to arithmetic.
- **Producer side (`linkCore`, `LSS:38-296`).** Dd := `M.data …` (`QLD:464-510`). Every field is a closed expression in (Fm.D x i, Fm.L x i), except:
  - **η(u0), e(u0)**: witnesses of `Frame_at` (`QLD:188`), chosen by `choose` (`LSS:100-103`). Constrained by
    0 ≤ η ≤ etaB, 0 ≤ e ≤ eB ≤ 1/4 and (etaB + 4√eB)x^{CH} ≤ 6 (FrameF, `QLD:258-260`), and by the SlopeIneq for every HH.
  - **etaBar, eBar**: existential from FrameF, with the same constraints.
  - **HH** := x^{CH}·b. It is a constant, **not** div.HH (the DivData has its own HH field, `DA:150`).
- One level deeper, the "arithmetic objects" are fields of the family FamP: `Fm.D x i : D7` and `Fm.L x i : SizeData₂ D`.
  - In `SizeData₂ D`, **gain, F, E, tau, io, NuLat, wPart, lenMN, LaG, etaSz, Cc, Sc** are free data (`DP2:93-178`).
    They have support and conjugation side-conditions only.
  - So Ga, Fo, Ee, Ta and IO are pinned only to free functions. Their constraints come from:
    - LinkG_at (`GTI:131-144`): 0 ≤ gain ≤ 4|TT|a/p, and Σ class-sum − loss ≤ Σ gain − τ;
    - Loss_at (`QLD:203-210`): ASK − Ga ≤ C·|TT|·m·b·x^{eLε};
    - LinkMu/NprimeMuR (`GTI:73-75`): μ(N_u) − μ(N_u with NuLat) − Σ_w sz(Σ_j(gain + F − E)) is O(X''), i.e.
      gain + F − E is the local log-index of a sub-lattice;
    - SlopesN_at = QSB (`QLD:176-178`);
    - LinkDIV (vii).
  - The lattices themselves (Nu, RR, Bk, X_v, h) are D7 fields. They are tied to explicit objects only through further
    hypotheses (h = hExpl6 via `Fm.h_eq`; RowSideTie; BesselId).

## 3. Children (ranked)

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `DivisionPackageFace.wordFacts` (→ WordFacts (vii)) | `RB:128-133` (statement), package `RB:400ff`, used `RB:684-689` | μ(RR^∨) + h(u) − Fo ≤ MAIN(u) + errors, with h = hExpl6 | the degree bound; the source of MAIN with γ, L'/L(1) | core (definition to unfold) |
| 2 | `SlopesNF` ← `slopesNF_of` ← `placesF_of` | `TopDensityNGeSixteen.lean:1544`; `LSS:505` | μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo | puts the gain Ga into the slope of N_u | core |
| 3 | `joint_a_ramified_holds` (+ `ramification_condition_holds`, `flat_lattice_theorem_holds`) | `JointDModelAppliesUnitLattice.lean:254`; statement `FTR:197` | mean-slope inequality for an almost tight frame of maps | the slope inequality | core (proved; body of sub-lemmas not read; *I infer* a Bost/Gaudron-type argument) |
| 4 | `FrameRealF` / `frameRealF_of''` | `TopDensityNGeSixteen.lean:519-531, 695, 886` | the lattice/frame geometry (LatGeom, InputSG with η0, η1, e0 ≤ exp(−x^{ε/8})) holds for every datum | hypotheses of #3 | core (InputSG comes from LinkS: near-orthogonality of Bessel periods) |
| 5 | `LossFS`/`Loss_at`, `LinkG_at` | `QLD:203`; `GTI:131` | ASK ≤ Ga + loss; prime-power class sums ≤ gains | vanishing side (sibling node) | core |
| 6 | `CountF` (`countF_fam`), `SlopesMF` (`slopesMF_of_count_fam`) | `QLD:252-253`; `LSS:487,495` | log T(u) ≈ Σ mean log(wv/π) + m lg; |μ(M_u)| ≲ nT a La | sizes | standard-looking (not opened) |
| 7 | `key_identity`/`key_identity5` | `WMD:170`; `LoC:105` | the algebraic rewrite of SDiv − ΣA Λ + m ΣA lg as Main | glue | glue |
| 8 | `latF`, `data_HHBound` | `QLD:1338, 714` | μmin(RR^∨) = −μmax(RR); s + μmax(RR) ≤ x^{CH} b ⇒ HHBound | glue | glue |

## 4. Oddities

1. **The Fo terms cancel identically** between DIV and the QSB lower bound (step 3). F is a free field of the record (`DP2:94`).
   It enters only through this cancellation and the QSB upper bound. So it plays no part in the conclusion. That is harmless,
   but it means DIV's "−Fo" is not a real constraint; it is bookkeeping.
2. **MAIN's arithmetic constants are inserted by definition.** `logOm := γ + log(π/v) − L'/L(1,χ_d)` (`DP2:224`). The
   prime side's MAIN (`FirstPrimeNeSecondPrime.lean:89-91`, from the parent node) uses the same γ and L'/L. The agreement
   "degree = PNT main term" is therefore by construction. All of the content sits in DIV (child 1): that the actual height
   h(u) = hExpl6 and μ(RR^∨) satisfy that inequality with exactly this constant. A reader should check whether hExpl6 itself
   contains logΩ (its kerPlace term does: `Numbers.lean:258`). If so, DIV may again be partly a tautology.
   Specifically, check whether μ_dual − Fo − (hExpl6 − its ph/logΩ part) ≤ −a·log T + errors is the real content.
3. **Rank-free slope error.** The SlopeIneq correction 4u·log(1+HH/u) + c·HH has no dependence on the rank R = Σd_u or on
   the degree of LL. There is only log|W| for the number of words. Classical slope inequalities for a direct sum into a
   target of rank D lose a term of order log D or (1/2)log rank (Minkowski/Siegel), which is absent here. This is
   possible because of the tight-frame hypothesis, but the bound is strong and the proof (`flat_lattice_theorem_holds`) should be read.
4. **SlopeIneq bounds by the mean slope μ(RR^∨), not by μ_max.** It needs (1−δ)|κ⊔κ₁| ≤ |κ| with δ ≤ exp(−x^{ez/7}),
   i.e. the sources must essentially fill the target. Also, η·HH ≤ 6b is forced by FrameF. These hypotheses are very strong.
   Their supplier (FrameRealF, from LinkS: off-diagonal Bessel-period correlations ≤ (1+exp(−x^{ε/8}))…) is where they get real content.
5. **Tie clauses are dropped by the consumer** (`TG:121-122`). Correctness only needs the producer to build Dd. In `linkCore`
   it builds Dd concretely, but over free record fields (§2(d)).
6. **HH = x^{CH}·b is a constant** that is independent of the data. The HHBound clause s − μmin(RR^∨) ≤ HH is then proved from
   LinkDIV (ii), s + μmax(RR) ≤ x^{CH}b, and μmin(RR^∨) = −μmax(RR) (LatF). That is fine.
7. LossBounds and LinkG both give *lower* bounds on gain. The only upper bound on Ga is the slope chain itself. That is
   consistent with "vanishing ≤ degree", and it means the upper side (children 1–4) carries all the strength.
8. Xpp = X''(n) = x·n·exp(x^{ε/3}) enters Lo5 as cSl1·Xpp + 1. ErrWindows needs only Xpp ≤ a = x·exp(x^ε). No problem seen.

## 5. Coverage

Read:
- `MB:1-229`; `QSB:1-80`; `LoC:1-200`; `WMD:120-225`; `SChain.lean:1-60`;
- `Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:20-70`;
- `TG:1-127`; `GTI:1-170`; `LSS:1-300, 455-515`; `QLD:140-270, 367-520, 561-575, 575-740`; `DP2:1-260`;
- `DA:61-104, 130-190`; `RhoDetPrimeEqMuTildeMulChiPow.lean:70-140, 353-366`; `Formalism/HarderNarasimhan/StatementPl.lean:1-90`;
- `FTR:30-101, 197-237`; `JointDModelAppliesUnitLattice.lean:240-294`;
- `TopDensityNGeSixteen.lean:515-545, 590-640`; `RB:250-400, 640-718`; `KernelPlaceMeanBound.lean:1-30`;
- `Divisibility/Numbers.lean:230-330`; `LinkMin.lean:690-725`.

Not opened:
- DivisionPackageFace and `wordFacts`;
- `slopesNF_of`/`placesF_of` bodies;
- `flat_lattice_theorem_holds`, `ramification_condition_holds`, `phi_bound`;
- `frameRealF_of''`;
- `countF_fam`, `slopesMF_of_count_fam`;
- RowSideTie/DivisionRows semantics;
- `FamP` (in particular `Fm.h_eq`);
- `Rows.Data`, `Member`/`PeriodMap`.
