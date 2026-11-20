# NODE-ACCOUNT: end-to-end magnitude check of the slope chain

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`
- `DA` = `Formalism/LocalRingCardinality/DataArith.lean`
- `PRM` = `Formalism/LocalRingCardinality/Params.lean`
- `RV` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean`
- `SC` = `Formalism/SizeWindowBrackets/SChain.lean`
- `EW` = `Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean`
- `QSB` = `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`
- `MB` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`
- `QLD` = `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`
- `IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
- `NUM` = `Formalism/LocalToGlobal/Divisibility/Numbers.lean`
- `ZON` = `Formalism/LocalToGlobal/Divisibility/ZscOfNum.lean`
- `FPN` = `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean`
- `GRH` = `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean`
- `PFA` = `Formalism/ThickAverageLoss/PartnersToFactorsAt.lean`

Convention. "≈" means "up to x^{O(ε)} and constants". b = e^{x^ε} is larger than any fixed power of x,
so every poly(x) term (and every poly(x)·X′ term, X′ = e^{x^{ε/3}}) is negligible next to b once x ≥ x₀(ε).
Only the **coefficient of b** has to be tracked. This is why the tree carries b.

## 0. Verdict (short)

1. **The accounting closes, but only exactly, with no room in the exponent.** Every term of `ErrX5at`
   (`QSB:45-54`) fits the budget once the windows of `RankVal`/`RestSize`/`ErrWindows` are inserted. Two
   families of terms are tight, and both sit at x^{1/2+O(ε)} × (signal unit):
   - **"x/m" terms**: the DIV error C·|TT|·a·La, Count5's ΣA·La, Slopes' nT·a·La, and u·log(1+HH/u) through UBar5;
   - **"m" terms**: m·B0 (EComp5, QSB upper bound, DIV's m(B0+Nc)), which includes the covolume error m·B0·log log x.

   They balance at m ≈ √x (RankVal: m ≈ (x·x^{−ε/8})^{1/2}). This is the "x/m + m" of NODE-COREGM, read off the actual error terms.
2. **No term in the composed inequality exceeds the budget.** So the accounting alone forces no hypothesis to be unsatisfiable.
3. **The chain contains seven cancellations between quantities much larger than the budget.**
   - In the Lean, four of them are exact by construction (the same symbol on both sides: Fo, logΩ, log(π/v), m·lg).
   - The other three are hypotheses that must hold to a stated relative precision:
     - covolume and height (B)/(C), relative precision **x^{−4}**;
     - log T(u) (Count5), relative precision **1/m**;
     - Bessel-frame tightness, **η ≤ 6x^{−CH}** with x^{CH}·b ≥ the HN spread of the lattices.
4. **One satisfiability condition that the Lean neither proves nor needs.** Ga − ASK ≤ budget. Here
   Ga = Σ sz(Σ_j gain) − Ta, and both terms can be as large as m·|TT|·a·x^{ε/3} (`TaBound`, `MB:190`), about
   x^{1/2} × budget. The chain only uses Ga ≥ ASK − LoP (proved). If Ga exceeded ASK by more than the budget, then
   (P) + DIV + SlopeIneq would imply a one-sided bias Gm(x) ≤ −x^{1/2+δ} on all windows. That contradicts
   Gz(x) = Ω±(x^{1/2}). So the slope-side hypotheses would then be false for the real lattices.
   This is the place where an expert should check the combinatorics (V-tops vs τ, §3(v)).
5. **Items (v) and (vi) of the brief.**
   - **(v) Caps.** The caps lose nothing. gain = γ_p·a − Σ_{e odd} min(a/p^e, w) is an identity (`ask_add_Mn`).
     "m ≈ √x" does **not** enter through caps; it enters as the number of lifts.
   - **(vi) Split primes.** They are handled by the character expansion. The three nontrivial E0-characters (chC, psC, chC·psC,
     i.e. the (·/d), (·/q), (·/qd)-type twists) are bounded at the single point y = x by the explicit hypotheses `ValuesAtX`/`bdG`
     (|G_ψ(x)| ≤ x^{1/2+ε}). These are RH-strength inputs on the quadratic twists, supplied by host selection. They are not hidden.

## 1. Parameter table (sizes as functions of x, ε)

n = |A| = R.ord, b = e^{x^ε}.

| symbol | Lean definition | size | file:line |
|---|---|---|---|
| n = \|A\| | `RankVal` | x^{2+8ε} ≤ n ≤ 2x^{2+8ε} | `RV:28-30` |
| f = \|Φ\| (places ρ) | `R.f = 2n` | ≈ 2x^{2+8ε} | `PRM:30` |
| m (lifts) | `RankVal` | √(x·x^{−ε/8}) ≤ m ≤ 2√(…), i.e. ≈ x^{1/2−ε/16} | `RV:31` |
| k | `RankVal` | x^{9/2+10ε} ≤ k ≤ 2x^{9/2+10ε} | `RV:32` |
| r, t, N(j) | r = k+m−1; r+t = 8fr+4+TOv·nWv, TOv = ⌈x^{377}⌉, nWv ≈ 10 r f²k³L²/m; N(j) = k + j(t+1) | t ≈ x^{398.5+O(ε)}; N(m) ≈ x^{399} | `RV:18-33`, `PRM:32-40` |
| signatures | sigW j = (k+j−1, m−j); p_j − q_j = k+2j−m−1, Σ_j(p_j−q_j) = mk | p−q ≈ x^{4.5}, q ≤ m | `PRM:46`, `ZON:64` |
| L | x^ε | | `DP2:27` |
| b | e^{x^ε} | | `DP2:29` |
| a | x·b | | `DP2:31` |
| a_t | integers in [a, a + a/(k·x^{13})] | a(1 + x^{−17.5}) | `DP2:80` |
| X′ | e^{x^{ε/3}} | ≪ b | `DP2:33` |
| b′ | a/X′ | ≪ b | `DP2:35` |
| w″ | b′/(x·n) | thin weight | `DP2:37` |
| X″ | a/w″ = x·n·X′ | the Riesz length at thin partners | `DP2:39` |
| p0 | k²x^{26} ≈ x^{35} | | `DP2:43` |
| w_{jρ}, thick | ∈ [b, b+η+1] | | `DP2:151` |
| w_{jρ}, top | ∈ [b_t + b′/x, … + η], b_t ∈ [b′, b′(1+O(x^{−2.5}))] | | `DP2:153`, `IRZ` winB |
| w_{jρ}, thin | ∈ [w″, w″+η] | | `DP2:155` |
| w, non-thick ρ ∈ Φ | ≤ 2b′ | | `QLD:211-220` |
| T2/n = de2 | ≥ x^{−ε} | thick density δ | `DP2:140`, `SC:57` |
| \|TT\| = nT | ≥ x^{−ε/8}·n/2 | ≈ n | `SC:56` |
| o, QS | o ≤ x^{ε/100}, QS ≤ 4n·x^{ε/100} | | `DP2:131-132` |
| B0 | f·m·b·x^ε | ≈ x^{2.5+O(ε)}·b | `DA:200`, `NUM:74` |
| Nc | T2·k·b·x^{2ε}/n² | ≈ x^{2.5+O(ε)}·b·(T2/n) | `DA:204-210` |
| unitE / l3u | B0·log log x per layer | | `ZON:62,66` |
| La | log(a·rdE) ≤ 2x^ε | | `DP2:226`, `EW:33` |
| logΩ | γ + log(π/v) − L′/L(1,χ_d), with v = rdE/2 | \|logΩ\| ≲ log rdE ≈ x^{ε/5}log²x | `DP2:224`, `NUM:56,68` |
| T(u) | prime in [T*, (1+1/(fk))T*], b^{m/2} ≤ T, log T ≤ C·m·x^ε | log T ≈ m·x^ε | `DP2:182-188,252`, `QSB:27-32` |
| HH | x^{CH}·b (a constant) | | `QLD:503` |
| η, e | (η̄ + 4√ē)·x^{CH} ≤ 6 | η ≤ 6x^{−CH} | `QLD:258-260` |
| δ (delp), δ̄ | ≤ e^{−x^{ez/7}} | | `QLD:504-508` |
| log\|W\| | ≤ (k−3) log 2 | ≈ x^{4.5} ≪ b | `EW:37` |
| HC entries | top u₀ = a_t + (k−1)/2; b_j ≤ b²; e_j = w_j; cloud entries ≤ Sc = 4k·Del | | `DP2:83-90,106,148,160-166` |
| γ_p | p/(p²−1) = Σ_{e odd} p^{−e} | | `IRZ:89` |
| τ_p | ep + Σ_{t0∈VV} m(⌈tv⌉ + Dp + 1); Ta ≤ c·m·nT·a·log X′ + Bo | up to ≈ ASK | `IRZ:384-389`, `MB:190` |
| io_p | 2·Sig·sup Sv, with Sig ≤ x^{−ε} on served primes | | `IRZ:391-395,364` |
| inert primes | none below x^{ez/5} (all odd p ≤ splitBound split in ℚ(√−d)) | | `DP2:129` |

The **signal unit** (`GRH:119-122`):

  U := nT·m·b·(T2/n)/2 ≈ x^{2.5+O(ε)}·b.

The conclusion is G ≤ (Err + 2Ub/x·…)/U + 4x^{1/2+ε}. So the **budget** for every error is

  Err ≤ U·x^{1/2+O(ε)} ≈ x^{3+O(ε)}·b.

## 2. The chain, with sizes

Per u0, every quantity below is a sum over t ∈ TT (≈ x²) and j < m (≈ x^{1/2}). Each line gives the Lean form and then its size.

```
ASK  = Σ_t Σ_j Σ_{n=p^i, Frob∉Φ} 2 log p (a_t/n − w_{j,partner})₊ + d-term                       (FPN:84-87)
     ≈ m·nT·a·(log x + (1−de2)·x^{ε/3})              [thin partners: y = a/w″ ≈ X″, so log y ≈ x^{ε/3}]
     ≈ x^{3+O(ε)}·b·x^{1/2+ε/3}          = x^{1/2+ε/3} × budget

  ≤ Ga + LoP                         LoP = c·nT·m·b                ≈ x^{2.5}b       (x^{−1/2} budget)   [LossBounds]
Ga = Σ_w sz(Σ_j gain_j − τ)          gain ≈ ASK_p + Σ_{V}Mn,  Ta ≈ Σ_V Mn  (each up to ≈ ASK)

  Ga ≤ μ(N_u) − μ(M_u) − Fo + Ee + Lo5                                                         [QSB lower, definitional]
       μ(N_u), h, Fo ≈ x^{7+O(ε)}b;  Ee ≈ m·ΣA·lg ≈ x^{3.5}b·lg;  −μ(M_u) ≤ c·nT·a·La ≈ x^{3+ε}b (TIGHT)
       Lo5 = c·IO + c·nT m(a/k+b′)log T + c·X″ + 1                  ≪ budget

  s := wmean_u(μ(N_u) − h_u) ≤ μ(RR^∨) + log|W| + (1−δ)^{-1}[4u log(1+HH/u) + (η+4√e)·HH]           [SlopeIneq]
       log|W| ≈ x^{4.5} ≪ b;  (η+4√e)·HH ≤ 6b  (x^{−3} budget);
       u ≤ UBar5 ≈ nT·a·La + m·B0;  4u·log(1+x^{cHH}) ≈ budget·log x                                 (TIGHT)

  μ(RR^∨) + h(u) − Fo ≤ MAIN(u) + c·nT·a·La + c·m(B0+Nc)x^{cε}                                         [DIV]
       c·nT·a·La ≈ x^{3+ε}b (TIGHT, "x/m");  m·B0 ≈ x^{3+O(ε)}b (TIGHT, "m");  m·Nc ≈ x^{3−4ε}b

     where, inside DIV (NODE-DIV):
       μ(RR^∨) ≤ meanLog κ + Σ_j l3_j + 2·FoOfR + …                           (A) BoundsMu, proved
       l3_j = Σ_ρ (p_j−q_j)·w_{jρ}·logΩ + C·B0·log log x                       (B) covolume, hypothesis   ≈ k·f·b·|logΩ| ≈ x^{6.5+O(ε)}b per layer
       h ≤ hu = hA + Σ_j(hB_j − hX_j)                                          (C) height, hypothesis
          hA = −Σ_t a_t log T + …                                              ≈ nT·a·m·x^ε
          hB_j = Σ_ρ[Σ_i ph(ν_{jρi}) − (Σ_iν)·logΩ] + poly·La,  Σ_iν = a_t[ρ∈TT] + k·w + δ     ≈ k·f·b·x^ε per j
          hX_j = Σ_ρ logHook_{jρ} − poly·Lp                                     ≈ k·f·b·x^ε per j

  Count5:  log T(u) = Σ_j mean_ρ log(w v/π) + m·lg  ± c·La(1+m²/k)             (×ΣA: error ≈ nT·a·La, TIGHT)
  EComp5:  Ee(u) = m·ΣA·lg ± c·m·B0                                            (TIGHT)
  key_identity5:  Σ_t m(ph(a_t) − a_t logΩ) − ΣA·[Σ_j mean log(wv/π) + m lg] + m ΣA lg
                  = Σ_j Σ_t a_t(log a_t − 1 − γ + L′/L(1,χ_d) − mean_ρ log w_{jρ}) =: Main

MAIN ≈ m·nT·a·(log x + (1−de2)x^{ε/3})          (= ASK's main term; survivor ≈ budget·x^{1/2})
ASK  ≤ Main + ErrX5at,     ErrX5at ≈ x^{3+O(ε)}·b = budget
```

**The large cancellations and the precision each needs.** Precision is quoted relative to the size of the terms, for a
survivor of budget size x^{3+O(ε)}b.

| # | terms that cancel | size of each | how the Lean does it | precision required |
|---|---|---|---|---|
| C1 | Fo in DIV (−) vs Fo in QSB (+). FInert ≈ (k−1)Σ_z w/(p²−1) summed over inert p ≤ X″ | ≈ m·k·f·b ≈ x^{7+O(ε)}b | **syntactic**: the same `L.Fo`. At object level, N_u and RR^∨ are both rescaled by the same F-indices | exact (harmless relabelling, provided RR is glued with the same F as sg) |
| C2 | +Σ_j Σ_ρ (p_j−q_j)w logΩ (B) vs −Σ_j Σ_ρ (Σν)logΩ (C) | ≈ m·k·f·b·\|logΩ\| ≈ x^{7+O(ε)}b | the same symbol `logOm`, and Σ_j(p_j−q_j) = mk exactly; the residual Σ_j(2j−m−1)Σ_ρ w·La ≤ m²·f·b·2x^ε ≈ m·B0 | (B) and (C) each to absolute error ≈ m·B0, i.e. relative **x^{−4}**: per place and per unit weight, the slope coefficient must be (p−q)logΩ + O(q·x^ε) with p−q ≈ x^{4.5}, q ≤ m |
| C3 | Σ_i ph(ν_i) (hB) vs log-hook/Γ (hX) | ≈ m·k·f·b·x^ε | `weight_height_sum_le` (NumFacts field) | to eE, inside budget; Stirling corrections are poly(x) ≪ b, so fine |
| C4 | log(π/v) in logΩ vs log(v/π) in Count5; m·lg in EComp vs Count5 | ≈ m·nT·a·x^{ε/5}log²x | `key_identity5`, pure algebra | exact |
| C5 | ΣA·log T(u) in MAIN/hA vs Σ_j mean log(wv/π) + m lg | ≈ m·nT·a·x^ε ≈ x^{3.5+O(ε)}b | hypothesis Count5 | log T to ±La, i.e. relative **1/m** (a prime T in a window of relative width 1/(fk); plausible) |
| C6 | Σ_w sz(Σ_j gain) vs Ta | each up to ≈ m·nT·a·x^{ε/3} | Loss proves only Ga ≥ ASK − LoP | **for satisfiability** Ga − ASK ≲ budget, i.e. relative x^{−1/2} per prime; unproved, see §3(v) |
| C7 | s vs μ(RR^∨) | ≈ x^{7+O(ε)}b | SlopeIneq (proved theorem) under the frame hypotheses | the frame must be tight to η ≤ 6x^{−CH}, where x^{CH}b ≥ s − μ_min(RR^∨) (LinkDIV ii); this forces CH ≳ 7 if the HN spread is the size of the terms |

ASK vs MAIN is not on this list. Its survivor *is* the theorem.

## 3. Verdict on sizes, item by item (budget = U·x^{1/2+O(ε)} ≈ x^{3+O(ε)}b)

- **(i) SlopeIneq error.** It is **not** c·HH with c = O(1). The coefficient is η + 4√e ≤ 6x^{−CH}
  (`FrameF`, `QLD:258-260`), so (η+4√e)·HH ≤ 6b, which is x^{−3} of the budget: comfortable. The other part,
  4u·log(1+HH/u) with u ≤ UBar5 (`QSB:40-43`), is of size (nT·a·La + m·B0)·cHH·log x: tight, the same as the tight terms.
  The cost is moved into the hypothesis that the Bessel frame is tight to x^{−CH}.
  `ErrWindows` (`EW:44-46`) checks (η̄+4√ē)x^{cHH}b ≤ K·x^ε·nT·a, which then holds trivially.
- **(ii) Covolume error.** C·B0·log log x per layer, summed over m layers, is C·f·m²·b·x^ε·log log x ≈ 2C·n·m²·b·x^{O(ε)}.
  Ratio to the budget ≈ m/x^{1/2} = x^{O(ε)}: **tight**. It is one of the "m" terms.
  Relative to the per-layer main term k·f·b·|logΩ| it is m·x^ε/(k|logΩ|) ≈ **x^{−4}**.
- **(iii) Colength d(τ+io).**
  - τ is not an error: Ga is defined net of τ, and the colength cost is exactly the p^{⌈τ⌉} factor in NP (NODE-TWU).
  - io enters as c·IO in Lo5 and is ≤ LoP by hypothesis (`Loss_at` first clause, `QLD:204`), x^{−1/2} of the budget.
  - Comfortable *given* that hypothesis. The worst-case reading of ioP (Sig = x^{−ε}) would give ≈ m·nT·a·x^{−ε},
    which is larger than LoP. The hypothesis therefore needs the averaged Sig (MeanKappaBound ≤ x^{−12}), not the cut-off.
- **(iv) Excluded primes.**
  - p = 2 and q1 have Frob ∈ Φ and inertia ⊆ Φ (`FPN:54-55`), so they are split and contribute 0 to (1−χ).
    The identity needs no exclusion.
  - d is handled by `askD` with weight log d = Λ(d^i)(1−0).
  - All odd p ≤ x^{ez/5} split (`DP2:129`), so there are no small inert primes.
  - Non-served inert primes ("first", "second", hP = 0, "bad") cost ≈ 4m·a·|TT|·log p/p each. Summed, this must be ≤ LoP,
    i.e. Σ_{bad p} log p/p ≲ 1/x.
  - By Chebotarev in E (degree 4n ≈ x^{2+8ε}) the density of each class is 1/n ≪ 1/x. So this holds on average, but it
    needs the explicit host hypotheses `ChBadp_at`/`ChosenBadp` (|TT|·x^{−2+ε}) for small p. Inside the budget.
- **(v) Caps and "m ≈ √x".**
  - max(A − w, 0) + min(A, w) = A, summed over odd e, gives γ_p·A. So the Riesz-truncated count and the "gain" differ by
    Σ min(a/p^e, w) *identically*. No fraction of the count is lost.
  - √x does not come from caps. Thick partners have y = a/w ≈ x; thin partners have y ≈ X″; top partners have y ≈ X′.
  - **The real issue is the opposite.** At served primes, for tops s ∈ V, gU keeps the full γ_p·a_s (`IRZ:254-258`).
    So gain ≥ ASK + Σ_{s∈V} Mn_s, with Mn_s ≈ b′ (from e = 1, since a/p > b′ for p < X′).
  - Summed over served p < X′ with weight 2 log p, this is ≈ 2b′X′ = 2a per V-top per lift, i.e. ≈ m·nT_V·a ≈ x^{1/2} × budget.
  - τ is built to cancel it: tv = Σ_{y∉TypeV} min(b_y, a/p^{d}) + tiny (`IRZ:217-225`). The kappa-threshold terms are tiny
    because p ≥ p0 ≈ x^{35}, resp. p^{−L1} ≤ (k x^{26})^{−4}.
  - The cancellation must hold to relative x^{−1/2} at each prime. It depends on a pairing of V-tops with the non-TypeV tops
    at distance dMinus, and on their partners being top places (weight ≈ b′) rather than thin ones (weight w″).
  - I could not verify this pairing. The Lean does not need it, since it proves only Ga ≥ ASK − LoP.
  - If it fails, the real lattices cannot satisfy (P) + DIV + SlopeIneq (see §0.4).
- **(vi) Normalisation and the split half.**
  - ASK = Σ_{p^i, i·Frob∉Φ} 2 log p·(a/p^i − w_partner)₊ + log d·(…) (`FPN:75-87`). For unramified n this is
    Σ Λ(n)(1 − chC(Frob_n))(a/n − w)₊ with chC(g) = (−1)^{g.1.1} (`FPN:21`), the character of Φ.
  - MAIN = a(log a − 1 − γ + ell(chC) − mean_{ρ∈Φ} log w) (`FPN:89-91`). With y = a/w this is
    w·[y log y − (1+γ)y + y·L′/L(1,χ_d)]. That is exactly the explicit-formula main term of Σ Λ(n)(1−χ_d(n))(y/n − 1).
  - ch_balance (`ChBalance.lean:200`) then writes ASK − MAIN as the full character expansion over E0 × H (weights depend on
    g through `partner = cconj + g + topPl t`, `PFA:24-26`). The weight factor (1/|Φ|)·2 turns "inert" into (1−χ).
  - The split half is **−G_{chC}** and its H-twists. The thick-place sum also carries psC and chC·psC.
  - These are not cancelled by anything. They are bounded at y = x by `ValuesAtX` (‖GPsi ψ x‖ ≤ x^{1/2+ε} for psC, chC,
    chpsC, `GRH:67-69`) and by `EAtH.bdG` for their level twists (in SigA).
  - So there is no hidden assumption about split primes. There is an **explicit RH-strength pointwise hypothesis** on
    (·/d), (·/q), (·/qd) and their twists at y = x, from host selection (NODE-HOSTS, NODE-PAIRGOOD).
  - Thin partners (y ≈ X″) are handled by `ThinScales` (|G_ψ(y)| ≤ yθ, θ = e^{−c x^{ε/8}}). With CostWindows the total thin
    error is ≤ U·b/x: comfortable.

## 4. Conclusion

- **The accounting closes exactly.** The composed inequality says:
  > the m-fold gain (≈ m × one PNT count) is ≤ m × one-copy main term + O(one copy·La) + O(m·B0),

  which after division by U gives Gm(x) ≲ x/m + m ≈ x^{1/2}.
- **The tight inequality is DIV.** Its error C·|TT|·a·La is independent of m, while every term inside DIV scales like m·k.
  This is the "one copy's worth" saving.
- **DIV is assembled from two hypotheses, (B) covolume and (C) height,** each about x^{4} times larger than the budget.
  They must agree on the coefficient of logΩ to relative x^{−4}.
- No error term exceeds the budget. No hypothesis is shown unsatisfiable by size alone.
- **The places where a real object must achieve a stated precision:**
  1. (B)/(C) at relative x^{−4}. In effect: the arithmetic volume per unit weight of U(p,q), with q ≤ m ≪ p, equals
     (p−q)·logΩ + O(q·x^ε), with all other zeta/L-value corrections absorbed by F (C1).
  2. Frame tightness x^{−CH}.
  3. Ga − ASK ≲ budget (C6), unproved and logically unneeded, but required for (P) + DIV to be true.

## 5. Coverage

Read:
- `SC:1-110`; `EW:1-140`; `QSB:1-80`; `MB:76-200`;
- `DP2:1-274`; `DA:190-215`; `PRM:1-70`; `RV:15-60`;
- `IRZ:37-420`; `NUM:55-80,160-215,250-280`; `ZON:50-100`;
- `QLD:140-270,464-512`; `FPN:1-100`; `GRH:10-32,50-70,100-125`; `PFA` (grep for InPhi, cconj, topPl, PhiSet).

Used from sibling nodes (not re-read): the DIV internals (NODE-DIV), NP and τ as a p^{⌈τ⌉} factor (NODE-TWU), the CovolumeBoundOfX
precision (NODE-COVOL, NODE-HS).

Not opened: the body of `ch_balance`; `tIf`'s TypeV/dMinus combinatorics beyond the definition; `NumFacts.eE`;
`starAt_D/E`; `MeanKappaBound` proof; the producer of `LinkDIV (ii)` (the HN spread of RR).
