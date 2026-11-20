# NODE-COREGM: `UpperTheory.Comparison₂.core_gm` and `Deduction.ch_core`

Paths are relative to the source root `.../scratchpad/art/lean/src`. Abbreviations:
`PC/` = `Development/AutomorphicArithmetic/PrimitiveCosets/`,
`LT/` = `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`,
`SI` = `Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean`,
`SWB/` = `Formalism/SizeWindowBrackets/`,
`TGC/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`.

## 0. Summary

`ch_core` contains no deep mathematics. It is an averaging-and-bookkeeping lemma. The square-root quality is
put in by a hypothesis: the "gap" inequality `gapA ≤ x^{Cε}·errorBracket`, combined with the size windows
`m ≈ x^{1/2}`. After division by the main-term coefficient, that hypothesis says Gm(x) ≲ x^{1/2+O(ε)}.
`core_gm` gets the gap inequality from `Deduction.ch_top`. `ch_top` is again bookkeeping: gapA = `Dd.ASK − Dd.Main`,
and `ASK ≤ Main + ErrX5at` follows from a block of **real-number slope inequalities** (`SizeData₂`). These are
hypotheses of `CoreAtH`. On the live path they are clauses of `ChainTied`, and `TieLocal` ties them to
Arakelov/Harder–Narasimhan data: slopes μ, μ_max of lattices `Nu u`, heights h(u), dual slopes and local "gains".
The RH-strength content therefore sits in the family-level link statements that supply those inequalities:
`LinkDIV` (a degree/“Liouville” inequality), `LossFS`/`Loss_at` (the arithmetic prime sum ASK is matched by local
gains Ga), and the `SlopeIneq`/`QuotientSlopeBounds` inequalities. A second square-root input sits in `EAtH.bdG`:
a pointwise bound |gχ(x)| ≤ x^{1/2+ε} for the "non-kept" host characters, which `PairGood` supplies.

## 1. Statement

### `core_gm` (`PC/CoreGm.lean:12-15`)
```lean
theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)
```
In words: fix a level Λ (for example ⟨ψ⟩, see NODE-ROOT) and constants. For all large x, every frame φ (a finite
abelian group A with subgroup A0 and an extra factor E0 = (Z/2)², `Formalism/ThickAverageLoss/PartnersToFactorsAt.lean:13`),
every host H on φ and every TT ⊆ A satisfy: if (EAtH) and (CoreAtH) hold, then Gm_Λ(x) ≤ x^{1/2+(eD+eL+7)ε}.

### `ch_core` (`LT/ChCore.lean:343-351`)
```lean
theorem ch_core (C ε CE Ko c M : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hc : |c| ≤ 1) : ∃ x1, ∀ x ≥ x1,
  ∀ H [AddCommGroup H] [Fintype H] (m : ℕ) (D : ArithData H) (S) (ell) (N) (TT T2 : Finset H) (a) (w)
    (b b' k aE η X' θ : ℝ) (A0 : AddSubgroup H) (Kp),
  HostFactsS D S → 0 < b → 0 ≤ aE → 0 < k → (m:ℝ) ≤ x^(1/2+ε/2) → x*m ≤ k →
  SizesA A0 TT T2 a w N x b b' η X' θ → ThinScales D ell X' θ → CostWindows x (fPl H) b η θ →
  RestSize ε x |H| |TT| |T2| m b k aE → (∀ s ∈ T2, s ∈ A0) → CharsA ell A0 Kp TT c M Ko CE ε x →
  (∀ u ∈ A0, gapA D N ell TT a w u ≤ x^(C*ε) * errorBracketSizeWindows x ε |H| |TT| |T2| m b k aE) →
  GmA D ell Kp c x ≤ x^(1/2+(C+3)ε) + SigA D ell A0 Kp x
```

### Unfolded definitions
- **ArithData H** (`SWB/FirstPrimeNeSecondPrime.lean:38-42`): primes q1, d, and for every prime p an "inertia" subgroup
  I_p ≤ G := E0×H and a "Frobenius" Frob_p ∈ G. It is an abstract model of an abelian Galois group with its ramification
  and Frobenius data. **HostFactsS** (`SI:14-22`): d is prime; outside S ∪ {d} the primes are unramified; I_p and Frob_p
  lie in Φ = {g : g.1.1 = 0} for p ∈ S; I_d = {0, sgc0}.
- **GPsi D ell ψ y** (`FirstPrimeNeSecondPrime.lean:61-70`): for a character ψ of G,
  G_ψ(y) = Σ_{n≤y} Λ(n)·χ_ψ(n)·(y/n − 1) + y·ell(ψ). Here χ_ψ(n) = ∏_{p|n} (average of ψ over Frob_p^{v_p(n)}·I_p), i.e.
  the Artin-character value, and ell(ψ) plays the role of L'/L(1,χ). For ψ = 0 it is Gz(y). This is the Riesz-smoothed
  Chebyshev function with its main term removed, as in NODE-ROOT. CoreAtH's `HostAddCharCompatible`
  (`PC/CoreAtH.lean:18-20`) forces ell ψ = L'/L(1,χ) for the primitive Dirichlet χ that agrees with χ_ψ.
- **GmA** (`SI:34-35`) = Σ_{ψ∈Kp} wt(ψ)·Re G_ψ(x), with weight 1 on characters trivial on H and c otherwise.
  **SigA** (`SI:39-40`) = Σ_{ψ ∈ PsiA A0 \ Kp} |G_ψ(x)|, where PsiA A0 = characters trivial on {0}×A0.
  `gmA_eq` (cited in `CoreGm.lean:61`, not opened) rewrites GmA as Λ.Gm x.
- **ASK D N a t w** (`FirstPrimeNeSecondPrime.lean:75-87`) = Σ_{inert p ≤ N} 2 log p·Σ_{i≤N, i·Frob_p∉Φ} max(a/p^i − w(partner(t, i·Frob_p)), 0)
  plus a similar d-term. It is a weighted count of prime powers whose Frobenius lies outside Φ, measured with a
  "weight" w at the partner place. **MAIN ell a w** (`:89-91`) = a·(log a − 1 − γ + ell(chC) − mean_{ρ∈Φ} log w(ρ)).
- **gapA** (`SI:50-52`): gapA(u0) = Σ_{t∈TT} Σ_{j<m} [ASK(a_t, t, w_{u0,j}) − Re MAIN(a_t, w_{u0,j})]. It is the
  excess of the weighted inert-prime count over its expected main term, summed over |TT| "targets" t and
  m "copies" j.
- **errorBracketSizeWindows** (`SWB/ErrorFormsWeakWindowsFalse.lean:133-135`), with n = |H|:
  `nT·aE·(1 + m²/k) + m·(2n·m·b·x^ε + nT2·k·b·x^ε / (n²·x^{−ε}))`.
- **SizesA** (`SI:42-48`): |a_t/b − x| ≤ 1; w > 0 on Φ; on "thick" places b ≤ w ≤ b+η+1; on thin places w ≤ 2b';
  b'X' ≤ xb; a_t/w ≤ N. **ThinScales** (`SWB/GrowthBoundGivesRiemannHypothesis.lean:55-56`): |G_ψ(y)| ≤ yθ for y ≥ X'/3.
  **CostWindows** (`SWB/SChain.lean:50-51`): 2f(x+1)θ ≤ 1/x and 6f(x+1)(η+1) ≤ b/x.
- **RestSize** (`SWB/SChain.lean:53-58`): aE ≤ 2xb; nT ≥ x^{−ε/8}n/2; nT2/n ≥ x^{−ε}; **m ≥ x^{1/2−ε}**; k ≤ n²x^{1/2−ε}.
- **CharsA** (`SI:56-62`): 0 ∈ Kp ⊆ PsiA A0; |PsiA A0| ≤ M; equidistribution |Σ_{t∈TT} ψ(t) − c|TT|| ≤ M x^{−1+ε}|TT| for
  the nontrivial kept ψ; |ell ψ| ≤ Ko on Kp and ≤ CE log x off Kp.
- **EAtH Λ H TT x ε C** (`TGC/ExplicitFormulaErrorOfHostConditions.lean:144-151`): o(φ) = o(Λ); the level's characters
  occur as host characters in Xp; exceptional-character bookkeeping; TT has equidistributed shares
  |#{t : t−γ ∈ A0} − λ_γ|TT|| ≤ x^{−1+ε}|TT|; **bdG: for every "Bounded" host character θ (in Xp but not kept, or in Xm)
  with primitive χ, |gχ(x)| ≤ x^{1/2+ε}** (`TGC/Analytic.lean:136,154-156`); and |L'/L(1,χ)| ≤ C log x for those θ.
- **CoreAtH** (`PC/CoreAtH.lean:29-41`): there exist an index type U0 with a map tr : U0 → A onto A0, "word" types W u0,
  m, f, a real record `Dd : Data U0 W Top m f` (`Formalism/RankGapBounds/MeanBoundSecondForm.lean:37-76`, 40 real
  fields: x, ε, a, b, b', k, L, La, B0, Nc, aT, w, d, T, μN, μmaxN, h, μM, μmaxM, EeJ, μCC, μminCC, Fo, Ga, Ta, ASK, IO, HH, δ, η, e, …),
  constants C, ell, N, T2, a, w and so on, such that: HostAddCharCompatible; Dd.x = x, Dd.ε = ε; C.eDiv ≤ eD and C.eLoss ≤ eL;
  **IdentU** (`SI:67-72`: Dd.aT = a, Dd.w = w, Dd.gam = γ, Dd.LpL = Re ell(chC), **Dd.ASK u = Σ_t Σ_j ASK(…)**);
  **SizeData₂ Dd C Xpp**; **ErrWindows**; BNBoundsU; SizesA; ThinScales; CostWindows; RestSize; T2 ⊆ A0.
- **SizeData₂** (`SWB/SChain.lean:17-19`) = HidaSetting ∧ DIV ∧ EComp5 ∧ HComp ∧ Count5 ∧ Slopes ∧ QuotientSlopeBoundsWith ∧
  LossBounds ∧ SlopeIneq ∧ HHBound ∧ FParams. All of these are inequalities between the real fields of Dd
  (`MeanBoundSecondForm.lean:111-163`, `SWB/QuotientSlopeBoundsWith.lean:19-35`). Examples:
  - DIV: μCC(u0) + h(u0,u) − Fo(u0) ≤ Σ_t [m(ph(a_t) − a_t·logΩ) − a_t·log T(u0,u)] + cDiv(nT·a·La + m(B0+Nc)x^{eDiv ε}).
  - QuotientSlopeBounds: μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo and μmax(N_u) ≤ μmax(M_u) + Ga + Fo − Ee + c·m·B0.
  - LossBounds: **ASK(u0) − Ga(u0) ≤ cLoss·nT·m·b·x^{eLoss ε}**, and IO ≤ the same.
  - SlopeIneq: s − log|W| − (1−δ)^{-1}(4u·log(1+HH/u) + (η+4√e)HH) ≤ μCC, where s is the d-weighted mean of μN − h.
    This is the shape of a Harder–Narasimhan / Bost "slope inequality" for an evaluation map.
- **ErrWindows** (`ErrorFormsWeakWindowsFalse.lean:28-45`): size ranges, among them x·b ≤ a, m ≤ x^{1/2+ε/2}, x·m ≤ k ≤ x^{eK},
  log|W u0| ≤ (k−3) log 2, and (η̄ + 4√ē)·x^{cHH}·b ≤ K x^ε nT a.
- **"Host"** (`HostAx φ`/`HostRaw φ`): I did not open the structure. From its uses: H carries primes q, d, a conductor
  condN, a map from frame characters θ ∈ φ.Char to primitive Dirichlet characters (`IsPrimOf`), the sets Xp/Xm, and
  `arith H : ArithData φ.A`. The Bounded characters are the twists ξ·(·/q)^i·(·/d)^j, (i,j) ≠ (0,0), with ξ mod ψ.N
  (`Development/AutomorphicArithmetic/CharacterBoxes/BoundedTw.lean:5-9`). On the live path the host is
  (Fm.D x i).host of a D7 datum, and the rank R and the lattice data come from `TieLocal`
  (`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:63-82`): d(u0,u) = rank Nu(u), μN = slope of Nu(u),
  μmaxN = max slope, h = div.h u, μM, μmaxM = slopes of `(fm u).lat 0`, μCC = RR.muDual, Ga = L.Ga, and so on.
  `L.Ga = Σ_{w∈supp} sz(w, Σ_j gain_j(w) − τ(w))` is a weighted sum of local gains at places w
  (`Formalism/LocalRingCardinality/DataParams₂.lean:205-234`).

## 2. Argument

### `ch_core` (`LT/ChCore.lean:352-442`, with lemmas at `:16-338`)
1. **Character expansion of a coset sum** (`sum_Th`, `:56-73`). For each u0 ∈ A0 define
   Th(u0,t) = |Φ|^{-1} Σ_{s∈T2} Σ_ψ ψ(−e1(s+u0−t))·b·G_ψ(a_t/b). Summing over u0 ∈ A0 kills every ψ that is nontrivial on A0
   (orthogonality, `sum_A`, `:28-54`). The result is Σ_{u0} Th = |A0|·b·(δ/2)·Σ_{ψ∈PsiA A0} ψ(e1 t) G_ψ(a_t/b), where δ = |T2|/|H|.
2. **Balance identity** (`ch_balance`, `LT/ChBalance.lean:200-202`): ASK − MAIN = De. Here De is the character expansion
   Σ_{g∉Φ} Σ_ψ ψ̄(g)·w·G_ψ(a/w). It is an exact explicit-formula-type identity: weighted prime counting in a coset equals the
   average of character-twisted Chebyshev functions. Its proof rewrites a sum of max(a/n − w, 0) as w·G_ψ(a/w) plus the
   main-term corrections.
3. **Thick/thin replacement** (`th_le`, `:75-152`). Re Th ≤ Re De + 2f(3(x+1)(η+1) + (x+1)bθ). On thick places, w is replaced by b
   (Lipschitz `LipW`, a project lemma `lipschitz_weight_all`). Thin places are dropped (`ThinScales`). CostWindows makes the
   loss ≤ 2b/x.
4. **Core** (`core`, `:283-338`). Summing over t, j and u0, steps 1–3 and the gap hypothesis give
   |TT|·m·b·(δ/2)·Y ≤ Err + 2|TT|·m·b/x, where Y is any lower bound for the average over t of
   Σ_{ψ∈PsiA A0} ψ(e1 t) G_ψ(a_t/b).
5. **Lower bound for Y** (`one_char`, `:202-281`, and `:419-439`). For kept ψ, Σ_t ψ(e1 t) G_ψ(a_t/b) ≈ c|TT|·G_ψ(x). This
   uses the equidistribution clause of CharsA (error x^{−1+ε}), the derivative bound `DerivInt` (`derivative_integral_all`)
   and the trivial bound |G_ψ(x)| ≤ x(log x + …). Non-kept ψ contribute ≥ −|G_ψ(x)|. So Y ≥ GmA − SigA − 4x^{1/2+ε}.
6. **Size bound** (`proposition_size_bound : GrowthSizeBound`, `SWB/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507`;
   statement at `SWB/GrowthBoundGivesRiemannHypothesis.lean:119-122`). If SizeWindows holds and
   nT·m·b·(δ/2)·(G − 4x^{1/2+ε}) ≤ Err + 2nT·m·b/x, then G ≤ x^{1/2+(C+3)ε}.

**Where "1/2" is born.** It enters in step 6, as the quotient errorBracket / (nT·m·b·δ/2) under the windows of RestSize
and ErrWindows (aE ≤ 2xb, δ ≥ x^{−ε}, nT ≥ n x^{−ε/8}/2, x^{1/2−ε} ≤ m ≤ x^{1/2+ε/2}, xm ≤ k ≤ n²x^{1/2−ε}).
I checked the three terms by hand:
- nT·aE(1+m²/k) / (nT m b δ/2) ≲ 4x/(mδ) ≤ 4x^{1/2+2ε}. This term falls as m grows.
- m·2n·m·b·x^ε / (…) ≲ 4n·m·x^ε/(nT δ) ≲ 8m·x^{O(ε)} ≤ x^{1/2+O(ε)}. This term rises as m grows.
- m·nT2·k·b·x^{2ε}/n² / (…) = 2k x^{2ε}/(n·nT) ≲ x^{1/2+O(ε)}, using k ≤ n²x^{1/2−ε}.

So the exponent 1/2 is the optimum of x/m + m at m = √x. The "error per copy j" is of size x/m, and the m copies cost m.
This is a Stepanov/Bombieri-type parameter balance. *I infer*, more importantly, that the gap hypothesis says directly
that the m-fold average of (ASK − MAIN), which has trivial size ≍ x·b·(log), shows cancellation down to b·x^{1/2}. In
other words, `gapA ≤ x^{Cε}·errorBracket` is, up to x^{O(ε)} and through steps 1–5, *equivalent* to the conclusion
GmA − SigA ≲ x^{1/2+O(ε)}. `ch_core` only transfers it.

### `core_gm` (`PC/CoreGm.lean:16-74`)
It applies `ch_core` with C = max(eD+eL, 0) + 3, Ko = koOf Λ, c = (3o+1)^{-1}, M = 4o, and Kp = keptA Λ H. It supplies:
`hostFactsS φ H`; the fields of CoreAtH (SizesA, ThinScales, CostWindows, RestSize, T2 ⊆ A0); `charsA` from EAtH; and
**the gap hypothesis from `Deduction.ch_top`** (`CoreGm.lean:57-60`), weakened via x^{CErr·ε} ≤ x^{(eD+eL+3)ε}. Then
`gmA_eq` gives GmA = Λ.Gm x, and `sigA_le` (`PC/SigALe.lean:38`) bounds SigA by ≈ 4o·x^{1/2+ε}. That bound comes from
**EAtH.bdG**, the pointwise square-root bound for the non-kept characters. Exponents are then combined:
x^ε·x^{1/2+(eD+eL+6)ε}.

### `ch_top` (`LT/ChTop.lean:37-72`), the supplier of gapA
By IdentU, gapA(tr u) = Dd.ASK u − Dd.Main u (`ch_top_main_eq`, `:11-35`). `each_unit_bound_statement`
(`SWB/ChainSlopeWindows/LevelOfCongruence.lean:175-197`) shows that the 11 clauses of SizeData₂ imply ASK(u0) ≤ Main(u0) + ErrX5at(u0).
The chain of inequalities, all linear arithmetic in the real fields (`LevelOfCongruence.lean:50-160`), is:
- ASK ≤ Ga + LoP (LossBounds);
- Ga + μCC − K5 − Lo ≤ s (QuotientSlopeBounds plus DIV, `s_lower5`);
- s − log|W| − Φ(HH, u) ≤ μCC (SlopeIneq);
- the key identity SDiv − sumA·Λ5 + m·sumA·lg = Main + … (`key_identity5`, `:105-111`).

Then `errX5at_le` (`SWB/ChainSlopeWindows/PChain.lean:613`, not opened) bounds ErrX5at ≤ x^{CErr ε}·ErrText under ErrWindows
and LargeX. Finally BNBoundsU (B0 ≤ 2|H|m b x^ε, Nc ≤ …) gives ErrText ≤ errorBracketSizeWindows.

In mathematical terms this is a **slope-method (Arakelov / Bost-type) auxiliary construction**. A family of hermitian
lattices N_u (rank d, slope μ, max slope μ_max) maps into a dual object CC (slope μCC). The "gain" Ga at places w, which
LossBounds says dominates the inert-prime count ASK, works like a vanishing-order/multiplicity count. DIV is the upper
bound on degree (height of the evaluation map). SlopeIneq is the comparison of mean and minimal slope. Together they give
"vanishing ≤ degree + error", i.e. ASK ≤ Main + error. Whether real objects satisfy all of this is decided upstream.

### (c) Who supplies SizeData₂ on the live path
CoreAtH comes from `ChainTied` (`TieGlobal.lean:97-114`, clause `SizeData₂ Dd C Xpp` at `:109`), via `tiedCore_of_chainTied`
(`PC/LevelGmLeOnFamilyScales.lean:13`) and `windowInequality_of_artinInputs` (`PC/WindowInequalityOfArtinInputs.lean:17-25`).
ChainTied also contains TieLocal, which equates the Dd fields with the lattice data. ChainTied is produced by `LinkGLOBAL`
(`Formalism/SharpRestriction/GlobalTheoremInputs.lean:162-164`), which is the last conclusion of `topDesWin`
(`CB/DesWin.lean:22,30`). One concrete producer is `linkCore` (`Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean:38-42`),
whose inputs include `LossFS Fm eL` and `LinkDIV Fm Cabs CH`. Their content is:
- `Loss_at` (`Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:203-210`):
  Σ_t Σ_j ASK − L.Ga ≤ C·|TT|·m·b·x^{eL ε}, for every arithmetic reading of the datum.
- `LinkDIV_at` (`GlobalTheoremInputs.lean:77-89`): μ_dual + h(u) − Fo ≤ L.MAIN(u) + C(|TT|·a·La + m(B0+Nc)x^{Cabs ε}), plus
  Bessel identity, RR fullness, height-map bounds and the E-sum comparisons.
- `LinkGLOBAL7`/`linkGLOBAL7_pk` (`LossesSmallShares.lean:464-482`) take about 15 further family statements (Kudla family,
  Taylor log metric, twelfth-root discriminant, crystalline comparison, …). I did not open them.

## 3. Children

| # | Name | file:line | Statement (math) | Role | Weight |
|---|---|---|---|---|---|
| 1 | `Loss_at` / `LossFS` (→ `LossesSmallShares`, `lossF_of_7`) | `GlobalSchurBounds/QuadraticLogDerivCongr.lean:203`; `LossesSmallShares.lean:13,298,308` | The inert-prime count Σ ASK is at most the local gain total Ga + |TT| m b x^{O(ε)} | links the prime sum to the Arakelov side; the gain then has to be bounded | core |
| 2 | `LinkDIV` / `LinkDIV_at` | `GlobalTheoremInputs.lean:77-92` | degree inequality μ_dual + h − Fo ≤ MAIN + errors (with Bessel identity, etc.) | the upper bound "degree ≤ main term" | core |
| 3 | `SlopeIneq`, `QuotientSlopeBoundsWith`, `HHBound`, `Count5` as supplied on the live path (TieLocal and the `SlopesMF`/`SlopesNF`/`CountF` inputs of `linkCore`) | `MeanBoundSecondForm.lean:139-163`; `QuotientSlopeBoundsWith.lean:19-32`; `LossesSmallShares.lean:39` | HN/slope comparisons for the lattices N_u, M_u and the dual CC | the slope method | core (probably standard slope-theory inequalities, but they need checking) |
| 4 | `EAtH.bdG` ← `boundedTw` ← `PairGood.bounds` / `PairEx` | `TGC/Analytic.lean:154`; `CharacterBoxes/BoundedTw.lean:45-56`; `CharacterBoxes/PairGood.lean:18-30` | There are prime pairs (q,d) such that every twist ξ·(·/q)^i(·/d)^j, (i,j) ≠ 0, satisfies |gχ(y)| ≤ y^{1/2+ε/2} for all y ∈ [Y, Y^A] | bounds SigA, the non-kept characters | core (*I infer*: plausibly obtainable by large-sieve averaging over the huge (q,d) range, but the WinPair congruence constraints restrict it; needs checking) |
| 5 | `Deduction.ch_top` + `each_unit_bound_statement` + `errX5at_le` | `LT/ChTop.lean:37`; `LevelOfCongruence.lean:175`; `PChain.lean:613` | SizeData₂ + ErrWindows + BNBounds ⇒ gapA ≤ x^{CErr ε}·errorBracket | linear arithmetic over the slope data | glue (I read the first two; the third is a definition to unfold) |
| 6 | `ch_balance` | `LT/ChBalance.lean:200` | ASK − MAIN = character expansion De (explicit formula for a smoothed coset prime count) | exact identity | standard (orthogonality plus Riesz smoothing) |
| 7 | `proposition_size_bound` | `LipschitzWeightAndMinimum.lean:507` | GrowthSizeBound (the exponent arithmetic in §2) | where 1/2 appears numerically | glue (body not read) |
| 8 | `derivative_integral_all`, `lipschitz_weight_all` | `LipschitzWeightAndMinimum.lean:966`; use at `ChCore.lean:308` | Lipschitz bounds for G_ψ in y and in w | routine | standard |
| 9 | `gmA_eq`, `sigA_le`, `charsA`, `hostFactsS` | `PC/GmAEq.lean`, `PC/SigALe.lean:38`, `PC/charsA`, `PC/hostFactsS` | GmA = Λ.Gm, SigA ≤ 4o x^{1/2+ε} (from bdG), CharsA from EAtH | translation | glue (not opened except the start of sigA_le) |

## 4. Oddities

1. **The gap hypothesis of `ch_core` is the conclusion in disguise.** Given the windows (m ≈ x^{1/2}), gapA ≤ x^{Cε}·bracket
   is equivalent, up to x^{O(ε)}, to GmA − SigA ≤ x^{1/2+O(ε)}. `ch_core` and `ch_top` together contain no analytic input
   beyond orthogonality, smoothing and linear arithmetic. All the RH-strength content is passed upward into the real-number
   clauses of SizeData₂, chiefly LossBounds plus DIV plus SlopeIneq, and from there into `Loss_at`/`LinkDIV_at` at family level.
2. **`Data` is a record of 40 free real numbers.** The only clause that ties it to arithmetic inside CoreAtH is IdentU
   (Dd.ASK = the actual prime sum, plus aT, w, γ, L'/L). For CoreAtH alone, SizeData₂ is satisfiable if and only if suitable reals
   exist, and the chain shows it forces ASK ≤ Main + error. So inside CoreAtH, SizeData₂ is effectively the statement
   "ASK ≤ Main + error" with witnesses. Only on the live path does TieLocal pin the fields to lattice slopes.
   A reviewer should check that TieLocal ties *every* field that the chain uses. Ga, Fo, μCC, h, μN and μmaxN are tied
   (`TieGlobal.lean:66-82`). I did not check HH, η, e, ε̄, IO, B0 and Nc beyond the visible lines.
3. A second, independent square-root input is **EAtH.bdG**: |gχ(x)| ≤ x^{1/2+ε} for all non-kept host characters, supplied
   by `PairGood`. It is pointwise GRH-quality for quadratic twists of huge conductor (log q ≈ Y^{ε/5}). Its proof
   (`PairEx`) was not traced.
4. Size constraints: xm ≤ k ≤ n²x^{1/2−ε} with m ≥ x^{1/2−ε} forces |H| = n ≥ x^{1/2}·x^{O(ε)}. ErrWindows also asks for
   k ≤ x^{eK} and log|W u0| ≤ (k−3) log 2. These look consistent, but they need hosts with |A| ≥ √x. That matches the large
   abelian fields of degree ≈ x^{2+8ε} in NODE-ROOT.
5. `Loss_at` quantifies over *every* `Reads` of the datum and every `HEq`-equal ArithData. That is harmless if Reads pins
   everything down. Not checked.
6. The file `SWB/ErrorFormsWeakWindowsFalse.lean` holds `ErrorFormsWeakWindowsFalse` (`:60`). Its name suggests that a weaker
   window form was found to be false. Only the strong `ErrWindows` (with the (η̄ + 4√ē)x^{cHH}b ≤ K x^ε nT a clause) is used here.
   Worth a look.

## 5. Coverage

Read: `PC/CoreGm.lean:1-74`; `LT/ChCore.lean:1-446` (lemma bodies skimmed, statements and main proof read);
`SI:1-90`; `SWB/FirstPrimeNeSecondPrime.lean:30-100`; `SWB/ErrorFormsWeakWindowsFalse.lean:1-60,125-140`;
`SWB/GrowthBoundGivesRiemannHypothesis.lean:36-140`; `SWB/SChain.lean:1-110`; `LT/ChTop.lean:1-76`; `LT/ChBalance.lean:195-215`;
`Formalism/RankGapBounds/MeanBoundSecondForm.lean:30-229`; `SWB/QuotientSlopeBoundsWith.lean:1-80`;
`SWB/ChainSlopeWindows/LevelOfCongruence.lean:1-240`; `PC/CoreAtH.lean:1-48`; `PC/WindowInequalityOfArtinInputs.lean:1-36`;
`PC/SigALe.lean:1-40`; `TieGlobal.lean:60-116`; `CB/DesWin.lean:1-35`; `GlobalTheoremInputs.lean:60-100,150-168`;
`LossesSmallShares.lean:10-60,296-310,455-500`; `QuadraticLogDerivCongr.lean:190-212`; `DataParams₂.lean:205-240`;
`TGC/ExplicitFormulaErrorOfHostConditions.lean:125-152`; `TGC/Analytic.lean` (grep lines 127-160); `CB/BoundedTw.lean:1-56`;
`CB/PairGood.lean:18-30`.
Not opened: `proposition_size_bound` body, `errX5at_le`, `gmA_eq`, `charsA`, `hostFactsS`, `HostAx`/`HostRaw`/`Frame` structures,
`key_identity` (WeightedMeanData.lean:170), the bodies of `linkCore`/`linkGLOBAL7_pk`, `SlopesMF`/`SlopesNF`/`CountF`,
`PairEx`, `D7`/`SizeData₂ D` structure fields (gain, τ, E, F), and the `Reads` semantics.
