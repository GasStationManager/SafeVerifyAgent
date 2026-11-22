# NODE-ENDGAME: from a one-sided bound on G_m at host scales to GRH for an arbitrary ψ

Source root `.../scratchpad/art/lean/src` (read only; nothing compiled or run). Abbreviations:
`LT/` = `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`,
`DL/` = `Development/AutomorphicArithmetic/DedekindLFunctions/`,
`PC/` = `Development/AutomorphicArithmetic/PrimitiveCosets/`,
`CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`,
`TGC/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`,
`SWB/` = `Formalism/SizeWindowBrackets/`.

**Verdict of this node: no ESCALATE.** The top of the chain is a correct deduction, given its two inputs: the per-host
bound (core_gm) and the existence of host families (TopG/HostExW). Every lemma body in the Landau step has now been read,
except the routine differentiation under the integral in `iteratedDeriv_laplace`. The L(ψ)/L(ψχ_{−d}) cancellation worry
does not arise. No twisted L-function ever enters the function that Landau is applied to. The twists are removed earlier,
by a two-sided pointwise bound at the single point y = x (`bdG` ← `PairGood`). That bound is where the split primes are
paid for (§2.3).

---

## 1. Statement

### 1a. The live top (`CB/ZeroFreeAllOfTopG.lean:26-34`, `TGC/TopWin.lean:68-93`)
`zeroFreeAll_of_topG (la := 3/2)` calls `zeroFreeOn_of_tiedWin_cyc` with three inputs for each primitive ψ and
Λ = `Level.cyc ψ`:
- (I) `ChebyshevInequalityOnWindows Λ` (`TopWin.lean:26-28`), supplied by `level_gm_le_on_family_scales`
  (`PC/LevelGmLeOnFamilyScales.lean:28-30`) → `core_gm` (`PC/CoreGm.lean:12-15`);
- (II) `Λ.FormB` (`TGC/Window.lean:30-33`), supplied by `formB` (`PC/Imports.lean:8-19`);
- (III) `ChebyshevInequalityAtWindowScale (3/2) Λ` (`TopWin.lean:30-32`), supplied by `TopG` applied to `GChi ψ`
  (`ZeroFreeAllOfTopG.lean:30-33`).

### 1b. The function (`TGC/ExplicitFormulaErrorOfHostConditions.lean:36-38, 105-124`; `DL/CharFamily.lean:10-22, 36`)
Level.cyc ψ = Level.ofSub ⟨ψ⟩ (`:105-121`): KEPT = {ξ* : ξ ∈ ⟨ψ⟩}, the primitive characters inducing the ξ; psK = none;
o = |⟨ψ⟩|. wt = (3o+1)^{−1} on every ξ* ≠ 1 (`:36`), and
  G_m(y) = G_z(y) + (3o+1)^{−1} Σ_{ξ∈⟨ψ⟩, ξ*≠1} Re g_{ξ*}(y),
  g_χ(y) = Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L′/L(1,χ),   G_z(y) = Σ_{n≤y} Λ(n)(y/n − 1) − y log y + (1+γ)y.
The `level_family` identification (`PC/LevelFamily.lean:41-52`) turns this into a `CharFamily`: weight 1 on the mod-1
character (ζ) and (3o+1)^{−1} > 0 on the others. All weights are > 0, and that is the only property used later.

### 1c. The windowed one-sided Landau lemma, exactly as used live
`Deduction.zeroFree_of_rpow_window` (`LT/ZeroFreeOfRpowWindow.lean:11-14`), called from `formB` with δ = la − 1 = 1/2
and C = 1 (`PC/Imports.lean:14`):

> Let F be a finite family of Dirichlet characters χ_i (each with N_i = 1 or χ_i ≠ 1) with weights a_i > 0, and put
> G_F(y) = Σ a_i Re g_{χ_i}(y) (`CharFamily.lean:24-36`). Let 0 < θ < 1 and δ > 0. Suppose that **for every Y₀ there is
> Y ≥ Y₀ with G_F(y) ≤ C·y^θ for all y ∈ [Y, Y^{1+δ}]**. Then L(s, χ_i) ≠ 0 for every i and every Re s > θ
> (`ZeroFree`, `CharFamily.lean:38-39`).

- The hypothesis is one-sided. It is required on all y of a sequence of log-windows [Y, Y^{1+δ}] with Y → ∞, and on
  nothing else. It is not required at "special y = x·b": b = e^{x^ε} and a = xb are internal parameters of the host
  count. The bound that reaches Landau is on G_m(x) at the scale x itself (`core_gm` concludes `Λ.Gm x ≤ …`).
- The only information used off the windows is the trivial a priori bound |g_χ(y)| ≤ C·y² (`Gchi_growth`,
  `LT/GchiGrowth.lean:37-38`), which enters through `PoleData.growth` (`DL/LandauZeroFreeCriterion.lean:17`).
- The conclusion is for each L(s, χ_i) separately, including ζ.

The live call needs windows [Y, Y^{3/2}] ⊆ {x : Λ.Gm x ≤ x^θ} for arbitrarily large Y (`HasWindows`, `TGC/Window.lean:7-8`).

---

## 2. Argument (paper proof, top to bottom)

### 2.1 Quantifiers and ε (question 4)

Fix a primitive ψ, and put Λ = Level.cyc ψ, o = |⟨ψ⟩|.

1. **(III) is applied first, once per ψ** (`ZeroFreeAllOfTopG.lean:30`). TopG gives constants e_D, e_L and ε₁ > 0, all
   depending only on ψ. For each ε ∈ (0, ε₁) it also gives a family Fm whose scale set Win contains windows [Y, Y^{3/2}]
   for arbitrarily large Y, and on which `ChainTied Fm e_D e_L …` holds at every x ∈ Win with x ≥ x₀ (`TopWin.lean:30-32`).
   Inside Fm, each scale x ∈ Win carries a host. The (q,d) are chosen at a scale Y_qd ∈ [x^{1/J}, x] (`WinPair`; NODE-ROOT
   §(c)). The abelian CM field E ⊂ ℚ(ζ_{QS·q·d}), the frame (A, A₀), the tops TT and the lattice data are built for that
   x (NODE-HOSTS §1(a)).
2. **Then fix s with Re s > 1/2** (`level_of_tiedWin`, `TopWin.lean:68-81`). Put m = min(Re s − 1/2, 1/2) and
   θ = 1/2 + m/2 < Re s. `exists_small_eps` (`:59-66`) picks ε ∈ (0, ε₁) with (e_D+e_L+7)ε ≤ m/2.
3. (I) turns ChainTied into G_m(x) ≤ x^{1/2+(e_D+e_L+7)ε} ≤ x^θ for x ∈ Win, x ≥ max(x₁, 1). (II) is then applied with this
   θ and la = 3/2. It gives L(s, ξ*) ≠ 0 for every ξ ∈ ⟨ψ⟩, in particular for ψ (`Level.mem_cyc`, `TGC/ExplicitFormulaErrorOfHostConditions.lean:123-124`).

So for each ε one gets zero-freeness for Re s > 1/2 + (e_D+e_L+7)ε, and ε is sent to 0 *pointwise in s*: each s gets its
own ε, hence its own family and its own hosts. Nothing is uniform in ε. The exponent 1/2 + O(ε) becomes 1/2 because the
region is the union over ε. `imprimitive` (NODE-ROOT, Level 2) then passes to imprimitive characters.

**e_D, e_L and the "+7" (resolved).** `CoreAtH` contains C.eDiv ≤ e_D and C.eLoss ≤ e_L (`PC/CoreAtH.lean:35`).
- C.eDiv is the exponent of the x^{eDiv·ε} error in the degree (DIV) inequality; C.eLoss is that of the
  x^{eLoss·ε} error in LossBounds (ASK − Ga ≤ c·|TT|·m·b·x^{eLoss·ε}) (NODE-COREGM §1).
- `ErrWindows` contains `ConstsBound`, which demands 0 ≤ C.eDiv and 0 ≤ C.eLoss (`SWB/ErrorFormsWeakWindowsFalse.lean:24-27, 41-43`).
- `core_gm` derives `0 ≤ eD + eL` from these with `linarith` (`PC/CoreGm.lean:46`). So whenever the hypothesis of (I)
  holds, e_D + e_L + 7 ≥ 7. The universal quantifier over all real e_D, e_L in `ChebyshevInequalityOnWindows` is harmless:
  for e_D + e_L < 0 its hypothesis is unsatisfiable.

The 7 is 3 + 3 + 1:
- CErr = eDiv + eLoss + 3 (`ErrorFormsWeakWindowsFalse.lean:19`), weakened to (e_D+e_L+3) (`CoreGm.lean:51-54`);
- `ch_core` adds 3 (`GmA ≤ x^{1/2+(C+3)ε} + SigA`);
- one more x^ε absorbs the constant 1 + 4o in front, using SigA ≤ 4o·x^{1/2+ε} and x^ε ≥ 1 + 4o (`CoreGm.lean:25, 62-74`).

**The "effective PNT at long lengths"** is `ThinScales`: |G_θ(y)| ≤ y·θ_s for y ≥ X′/3, where X′ = e^{x^{ε/3}} and
θ_s = e^{−c x^{ε/8}}. It is produced by `ThinH` (`CB/PairGood.lean:36-40`): this holds for every character of Gal(E/ℚ)
once log(cond) ≤ 2x^{ε/5}log²x and `RealBox` excludes real zeros β > 1 − 1/400 for the real characters involving q, d
(`:32-34`). It is used only in the bridge, to discard every Frobenius class whose partner place is "top" or "thin": there
the Riesz length a/w is ≥ X′/2, astronomically long relative to the conductor (NODE-CHBALANCE §2(b)). It plays no part in
Landau.

### 2.2 The windowed Landau lemma (question 1)

The proof is `lemmaL` (`LT/lemmaL.lean:13-22`) → `landau_window` (`LT/landauWindow.lean:83-166`). I read every lemma body;
the one exception is that of `iteratedDeriv_laplace`, of which I read only the statement. Work in u = log y with
g(u) = G_F(e^u).

**Step 0: the transform** (`poleData`, `LT/poleData.lean:248-400`; `poleData_char`, `:137-239`; `poleData_abstract`, `:22-89`).
- For χ ≠ 1 (`mellin_Gchi_of_ne_one`, `LT/mellinGchiOfNeOne.lean:116-119`):
  ∫₁^∞ g_χ(y) y^{−s−1} dy = −(L′/L(s,χ) − s·L′/L(1,χ))/(s(s−1)), for Re s > 1.
- For ζ (`mellin_Gchi_modOne`, `LT/mellinGchiModOne.lean:115-118`):
  ∫₁^∞ G_z(y) y^{−s−1} dy = −(ζ′/ζ(s) + 1/(s−1) + 1 − (1+γ)s)/(s(s−1)).
- `poleData_abstract` is applied to g = L(·,χ), and for ζ to g = (s−1)ζ(s) with k = 1. The numerator then vanishes at
  s = 1, so the main terms y·L′/L(1,χ), resp. −y log y + (1+γ)y, cancel the pole at s = 1 exactly. The transform is
  meromorphic on Re s > 0. Its only singularities are simple poles at zeros ρ ≠ 0 of g, with principal part
  m_ρ·(−1/(ρ(ρ−1)))/(s−ρ), where m_ρ is the order of the zero (`:27-28`).
- Re g_χ = (g_χ + g_{χ̄})/2 (`Gchi_conj`). So Φ(s) = Σ_i (a_i/2)(Φ_{χ_i} + Φ_{χ_i^{-1}}) (`poleData.lean:261`).
- The pole set is Z = {ρ : Re ρ > 0, some L(ρ,χ_i) = 0 or L(ρ̄,χ_i) = 0} (`LandauZeroFreeCriterion.lean:11-13`).

**Non-cancellation** (`poleData.lean:336-400`). At ρ ∈ Z the residue is
  c(ρ) = S(ρ)·(−1/(ρ(ρ−1))),   S(ρ) = Σ_i (a_i/2)(m(ρ, χ_i) + m(ρ, χ_i^{-1})).
- Every term of S(ρ) is ≥ 0, and the term of the character that vanishes is ≥ a_{i₀}/2 > 0 (`:346-363`). Hence c(ρ) ≠ 0.
- If ρ = β is real, then β < 1 by non-vanishing on Re s ≥ 1 (`:371-376`), so β(β−1) < 0 and c(β) is real and **> 0**
  (`:377-383`). This is the analytic form of "a real zero pushes G up".

These two facts are the whole of the positivity used (`PoleData.pole`, `LandauZeroFreeCriterion.lean:22-23`). The weights
must be positive, and the principal parts at a common zero are the same complex number −1/(ρ(ρ−1)) times nonnegative
integers. So a zero of L(s,ψ) cannot be cancelled by ζ, by the other ξ, or by ψ̄. Positivity of Dirichlet coefficients
is never used.

**Step 1: the kernel** (`landau_coeff`, `LT/LandauCoeff.lean:10-28`). For Re z > 2, the Taylor coefficient
a_k(z) := (−1)^kΦ^{(k)}(z)/k! equals ∫₀^∞ g(u)·u^k e^{−zu}/k! du. On the real line, the kernel K_k(u) = u^k e^{−σu}/k! is
≥ 0.

**Step 2: one-sided bound ⇒ upper bound on coefficients** (`landau_window_ineq`, `LT/landauWindowIneq.lean:27-111`;
`landau_window_key`, `landauWindow.lean:40-73`).
- On the window W = [U, (1+δ)U], let R ≥ 0 with g ≤ R. Then |g| + g ≤ 2R (`:86-87`).
- Hence, uniformly in γ:
  |a_k(σ+iγ)| + Re a_k(σ) ≤ ∫(|g| + g)K_k ≤ 2(σ−θ)^{−k}∫_W R e^{−θu} du + 2C₀∫_{off W} u^k e^{−(σ−2)u}/k! du.
- The first term uses sup_u u^k e^{−(σ−θ)u}/k! ≤ (σ−θ)^{−k} (`landau_kernel_max`, `LT/LandauKernelMax.lean:9-19`).
- Re a_k(σ) appears on the left because only an *upper* bound on g is available: ∫|g|K is controlled only through
  ∫(2R − g)K, and ∫gK = Re a_k(σ). That is the price of one-sidedness.
- With R = C·y^θ, ∫_W R e^{−θu} = Cδ log Y ≤ Y^η = e^{ηU} for every η > 0 once Y is large (`windowHyp_of_rpow`,
  `LT/WindowHypOfRpow.lean:27-57`; change of variables in `LT/WindowHypUOfWindowHyp.lean:29-56`).

**Step 3: tails, and why σ must be large** (`landau_tails`, `LT/landauTails.lean:80-131`).
- Given δ, take l = 2 + 6/δ, M = l(1+δ), σ = M(2+l) (`:83-88`); for δ = 1/2 this is σ = 336.
- For each U ≥ 1 take k = ⌈(1+δ/2)σU⌉ ≥ U (`:96-101`).
- A Chernoff bound (`landau_tails_chernoff`, `:18-60`) gives ∫_{(0,∞)∖W} u^k e^{−(σ−2)u}/k! du ≤ C/σ^k.
- Why σ must be large: off the window only |g| ≤ C₀e^{2u} is known. So the tail integrand is the kernel shifted from
  e^{−σu} to e^{−(σ−2)u}, which inflates its total mass by (σ/(σ−2))^k ≈ e^{2k/σ}. The Gamma(k) kernel concentrates on
  the window, at relative width δ/2 around u ≈ k/σ ≈ (1+δ/2)U, with exponential decay of rate ≍ kδ². This beats e^{2k/σ}
  only when σ ≳ δ^{−2} (inferred from the constants; the Lean only verifies the inequality).
- Result: for every η > 0 there are arbitrarily large U and k ≥ U with
  |a_k(σ+iγ)| + Re a_k(σ) ≤ C′e^{ηU}/(σ−θ)^k for all γ (`landauWindow.lean:40-45`).

**Step 4: a zero with Re ρ₀ > θ forces larger coefficients.** All poles have Re ρ ≤ 2 < σ (`landau_pole_re_le`,
`LT/LandauPoleReLe.lean:29-53`). Poles in a closed disc inside Re > 0 are finite (`landau_finite`, `LT/LandauFinite.lean:9-26`).
`landau_dichotomy` (`LT/LandauDichotomy.lean:24-87`) gives two cases.
- **(ii) The nearest pole to σ is real.** If every pole at minimal distance d from σ satisfies σ − Re ρ ≥ d, then it lies on
  the axis at β = σ − d > θ. There it is the *unique* pole in a disc B(σ, r) with d < r ≤ σ−θ (`:47-87`).
  - `landau_pole_asym` (`LT/LandauPoleAsym.lean:19-79`) subtracts c/(s−β) and applies Cauchy to the remainder, which is
    analytic on B(σ, r). It gives |a_k(σ) − c/(σ−β)^{k+1}| ≤ M/r′^k with r′ ∈ (d, r).
  - Since c > 0 is real, Re a_k(σ) ≥ c/d^{k+1} − M/r′^k. Combined with |a_k(σ)| ≥ 0, the left side of Step 3 is
    ≳ c/d^{k+1}, while the right side is ≤ C′e^{ηU}/(σ−θ)^k with d < σ−θ.
  - `landau_growth_contra` (`LT/LandauGrowthContra.lean:9-40`, η = ½log(r′/d)) and `landau_window_contra`
    (`landauWindow.lean:20-38`) turn this into a contradiction for large k ≥ U. **Positivity of c is essential here.** A
    real pole with negative residue would make |a_k| + Re a_k ≈ 0 and give no contradiction.
- **(i) Otherwise.** There is D ≤ σ−θ such that B(σ, D) contains no pole, yet some pole ρ₁ (necessarily off the axis)
  has σ − Re ρ₁ < D.
  - `landau_nearest` (`LT/LandauNearest.lean:36-109`) moves the centre to z = σ + iγ with γ within ε of Im ρ₁. It avoids
    the finitely many γ at which two of the finitely many nearby poles are equidistant from z (`landau_nearest_equi`,
    `:10-34`; the set B, `:53-57`). So **one pole ρ is the unique nearest singularity to z**, at distance d < r ≤ D.
    Uniqueness matters because several poles on the circle |s − z| = d could make the d^{−k} terms cancel along a
    subsequence of k.
  - Then |a_k(z)| ≥ |c|/d^{k+1} − M/r′^k (`landau_pole_asym`), with |c| > 0 by non-cancellation.
  - The term Re a_k(σ), which may be negative, is bounded below by −M′/r′^k. This is Cauchy on the pole-free disc
    B(σ, D) (`landau_cauchy`, `LT/LandauCauchy.lean:92-116`), with r′ = (d+r)/2 < D.
  - So the left side of Step 3 is again ≳ |c|/d^{k+1}, with d < σ−θ, and the same contradiction follows
    (`landauWindow.lean:92-133`).

So complex zeros are handled directly, by a Cauchy–Hadamard (nearest-singularity) argument on Taylor coefficients along a
vertical line. No reduction to a real singularity is made. The real-singularity case is the one place where the sign of
the residue enters.

**Why sparse windows suffice.** All singularities in the argument are fixed: z, ρ, r and r′ depend only on σ and the zero
set, never on U. The contradiction needs only an unbounded set of k with the Step 3 bound. Each window [U, (1+δ)U]
supplies one such k ≈ (1+δ/2)σU, because the k-th kernel lives on that window up to an error C/σ^k, and C/σ^k is itself
o(d^{−k}). Hence any sequence of windows with U → ∞ works, however sparse. The windows must have a fixed *ratio* 1+δ in
log scale, and σ is taken large in terms of δ. A family of windows whose ratio shrank to 1 would not do.

**Re s ≥ 1** is covered by Mathlib's non-vanishing (`charFamily_LFunction_ne_zero_of_one_le_re`,
`LT/CharFamilyLFunctionNeZeroOfOneLeRe.lean:9-20`; `lemmaL.lean:18-19`). For ζ at s = 1 this rests on Mathlib's value ζ(1) ≠ 0.

I find this a correct theorem with a correct proof. It is a windowed Landau/Pólya-type argument on Taylor coefficients.
No `sorry`, `axiom`, `admit` or `native_decide` occurs in `LT/` outside the ChCore/ChBalance/ChTop files, nor in
`LandauZeroFreeCriterion.lean` or `CharFamily.lean` (grep, §5).

### 2.3 From ψ to G_m, and the bridge (questions 2 and 3)

**Why G_m gives L(s,ψ) itself.** G_m is a positive combination of g_ξ over ⟨ψ⟩ plus G_z. By §2.2 a zero of any one of
these L-functions is a pole of Φ that nothing can cancel. So the bound gives zero-freeness for ζ and for every ξ ∈ ⟨ψ⟩ at
once. No Dirichlet series with nonnegative coefficients is used.
- The averaged coefficients Λ(n)(1 + c·Σ_{j≠0} Re ψ^j(n)) are in fact ≥ 0 for c = (3o+1)^{−1}: for (n, N) = 1 the inner
  sum is o·1[ψ(n)=1] − 1 ≥ −1, and in general it is ≥ −(o−1), while c(o−1) < 1. But nothing uses this.
- ζ has weight 1 and is always present, so the same bound alone would give RH (NODE-LANDAU §4).

**Where 4:3 and 3o+1 come from.** They do not come from a nonnegativity requirement on coefficients. The bridge
averages the thick-class count over u₀ ∈ A₀ and sums over the tops t ∈ TT. Its output is Σ_{ξ} λ̂(ξ)·Re G_ξ(x), where λ is
the distribution of TT over A/A₀ (`Frame.lam`, `TGC/ExplicitFormulaErrorOfHostConditions.lean:135`; `Shares`,
`:139-140`; `EAtH.shares`, `:148`). With λ(h) = (3 + 1_{A₀}(h))/(3o+1):
- λ is a probability measure on the o cosets: Σλ = (3o+1)/(3o+1) = 1;
- λ̂(1) = 1, and λ̂(ψ^j) = (3o+1)^{−1}Σ_h 1_{A₀}(h)ψ^j(h) = (3o+1)^{−1} for j ≠ 0.

So c = (3o+1)^{−1} is the Fourier coefficient of a strictly positive share measure (NODE-CHBALANCE §2(a)). What the
argument needs is λ ≥ 0, since λ counts tops, and λ̂(ψ^j) > 0 for all j, since Landau needs positive weights. Any
λ = α + β·1_{A₀} with α ≥ 0 and β > 0 would do, and so would the point mass on A₀ (c = 1). Uniform shares (β = 0) would
kill ψ and leave only G_z (NODE-CHBALANCE remark under §2(a)). The specific ratio 4:3 is a choice; I found no constraint in
the files read that forces it. *Inference*: the large α keeps TT spread over every coset, but RestSize only asks
|TT| ≥ x^{−ε/8}n/2, which the point mass also meets for fixed o. Not located: a reason for exactly 3. Searches:
`rg 'Shares|φ\.lam|Frame\.lam'` over `Formalism/` and `Development/AutomorphicArithmetic/` hit only the definition,
`EAtH`, `PC/TopsSum.lean:76,98`, `ThickFrames/topsFrame.lean:15` and `CoprimeRanks/OfPInjective.lean:131`. The tree has
no comments.

**How ψ is embedded in the host.**
- E is the fixed field, inside ℚ(ζ_{QS·q·d}), of the kernel of the Artin map. That kernel is
  {a : a ≡ ±1 mod 2^{e+2}, ψ(a) = 1, (a/q) = (a/d) = 1} (`KerChi`, `CB/TwistForm.lean:9-12`; `IsChiField`, NODE-VWIN §1).
  So ψ factors through Gal(E/ℚ) = {±1}² × A.
- A₀ = ⟨a₀⟩ embeds in the 2-power quotient, and |A/A₀| = o (NODE-HOSTS §1(a)).
- Every frame character trivial on A₀ (`TrivialOnFirstFactor`, `TGC/Analytic.lean:88`) is ξ·(·/q)^i(·/d)^j with ξ ∈ ⟨ψ⟩
  (`TwistForm`, `TwistForm.lean:14-17`).
- So the A/A₀-coordinate of Frob_p is ψ(p), read off as a coset. The tops' 4:3 over-weighting of the coset A₀, i.e.
  ψ(Frob) = 1, is what injects ψ.

**Which primes are counted.** ASK counts n = p^i with Frob ∉ Φ = Gal(E/K), K = ℚ(√−d): p inert in K and i odd. It
counts them with cap w at the partner place (NODE-CHBALANCE §2(a)). As a function of n it is
Σ Λ(n)(1 − χ_{−d}(n))(a/n − w)₊. Only partner classes that are thick, i.e. Frob = ((1,0), h) with h ∈ A₀ − t, see the
scale x. All others have Riesz length ≥ X′/2 and are killed by ThinScales. The thick-class indicator is a combination of
the 4o characters (·/d)^α(·/q)^β ψ^j of E₀ × A/A₀. After averaging:
- the (α,β) = (0,0) part is exactly U·G_m(x), with U = |TT|·m·b·δ/2 > 0;
- the 3o twisted characters ξ·(·/q)^i(·/d)^j, (i,j) ≠ (0,0), make up SigA, which enters with a lower bound −|G| only
  (NODE-CHBALANCE §2(b), §2(d)).

**Why the split primes are not needed, and why L(ψχ_{−d}) does not spoil the conclusion.** The review's worry was that a
count over inert primes alone controls −L′/L(ψ) + L′/L(ψχ_{−d}). It does not apply, for the following reason.
- The χ_{−d}-, (·/q)- and (·/qd)-twisted pieces are never part of the function given to Landau. Each is bounded
  *two-sidedly at the single point y = x*, by `bdG`/`BoundedCharsPointwise`: |g_χ(x)| ≤ x^{1/2+ε} for every host
  character in `Bounded` (`TGC/Analytic.lean:136, 154-156`; `EAtH.bdG`, `ExplicitFormulaErrorOfHostConditions.lean:149`).
- `boundedTw` (`CB/BoundedTw.lean:45-56`) supplies `bdG` from `PairGood.bounds` (`CB/PairGood.lean:18-23`):
  ‖g_χ(y)‖ ≤ y^{1/2+ε/2} and ‖L′/L(1,χ)‖ ≤ 4 log y for every twist ξ(·/q)^i(·/d)^j with (i,j) ≠ 0 and all y ∈ [Y, X].
  `boundedTw_key` (`:5-43`) shows that the Bounded characters are exactly these twists.
- `sigA_le` then gives SigA ≤ 4o·x^{1/2+ε} (`PC/CoreGm.lean:62`). Via the identity
  Σ Λψ^j(1 − χ_{−d})(x/n−1) = [Σ Λψ^j(x/n−1)] − [Σ Λψ^jχ_{−d}(x/n−1)], this bound is precisely what lets a count over
  inert primes stand in for the full sum over all primes. **The split half of the primes is paid for by the selection of
  (q,d), not by a second field and not by several d.**
- The conclusion of core_gm is a bound on G_m(x), which involves only ζ and ⟨ψ⟩ and does not depend on the host. The host
  (q,d) changes from one x to the next, which is harmless: Landau sees only the host-independent function G_m on the
  windows.
- `PairEx` is a closed theorem: an averaging argument over the (q,d) family, valid for y ∈ [Y, Y^A] far below the
  conductor e^{Y^{ε/5}}. NODE-PAIRGOOD §0 found no circularity. Its body was not re-read here.

So the top-level logic does yield GRH for L(s,ψ) from the stated bound. No zeros of L(ψ) and L(ψχ_{−d}) can cancel,
because the latter never enter Φ.

---

## 3. Children

| name | file:line | statement (math) | role | weight |
|---|---|---|---|---|
| `core_gm` | `PC/CoreGm.lean:12-15` | EAtH + CoreAtH at x ⇒ G_m(x) ≤ x^{1/2+(e_D+e_L+7)ε}; forces e_D+e_L ≥ 0 (`:46`) | the RH-strength bound (input I) | core (NODE-COREGM) |
| `TopG` + `HostExW (3/2) (GChi ψ).req` | `CB/ZeroFreeAllOfTopG.lean:12-14, 26-33` | for small ε, ChainTied families with 3/2-windows exist | input III | core (NODE-HOSTS) |
| `PairGood.bounds` → `boundedTw` → `EAtH.bdG` | `CB/PairGood.lean:18-23`; `CB/BoundedTw.lean:45-56` | \|g_χ(y)\| ≤ y^{1/2+ε/2} for the 3o quadratic twists of ⟨ψ⟩, y ∈ [Y, X] | removes the χ_{−d}, (·/q) twists; pays for the split primes | core (NODE-PAIRGOOD) |
| `ThinH` / ThinScales | `CB/PairGood.lean:36-40` | effective PNT with saving e^{−cx^{ε/8}} at lengths ≥ X′/3, given RealBox | drops thin and top partner classes | standard (de la Vallée Poussin with Siegel-zero box) |
| `Frame.lam`, `Shares` | `TGC/ExplicitFormulaErrorOfHostConditions.lean:135-140` | TT has share (3+1_{A₀})/(3o+1) per coset | makes ψ enter with weight c = (3o+1)^{−1} | glue (choice; existence of TT is a host question) |
| `zeroFree_of_rpow_window` / `lemmaL` / `landau_window` | `LT/ZeroFreeOfRpowWindow.lean:11-14`; `LT/lemmaL.lean:13-22`; `LT/landauWindow.lean:83-166` | §1c | Landau step | standard (Landau-type, via Taylor coefficients); all bodies read, correct |
| `poleData` / `poleData_char` / `poleData_abstract` | `LT/poleData.lean:248-400, 137-239, 22-89` | transform meromorphic on Re>0; residue S(ρ)·(−1/(ρ(ρ−1))), S > 0; positive at real ρ | non-cancellation | standard (explicit formula for Riesz means) |
| `mellin_Gchi_of_ne_one`, `mellin_Gchi_modOne` | `LT/mellinGchiOfNeOne.lean:116-119`; `LT/mellinGchiModOne.lean:115-118` | Mellin transforms of g_χ, G_z | input to poleData | standard |
| `landau_tails`, `landau_window_ineq`, `landau_kernel_max`, `landau_coeff` | `LT/landauTails.lean:80`; `LT/landauWindowIneq.lean:27`; `LT/LandauKernelMax.lean:9`; `LT/LandauCoeff.lean:10` | Chernoff tail; one-sided inequality; kernel sup; Taylor coefficient as a Laplace moment | Steps 1–3 | standard |
| `landau_dichotomy`, `landau_nearest`, `landau_pole_asym`, `landau_cauchy`, `landau_growth_contra`, `landau_pole_re_le`, `landau_finite` | `LT/LandauDichotomy.lean:24`; `LT/LandauNearest.lean:36`; `LT/LandauPoleAsym.lean:19`; `LT/LandauCauchy.lean:92`; `LT/LandauGrowthContra.lean:9`; `LT/LandauPoleReLe.lean:29`; `LT/LandauFinite.lean:9` | nearest-singularity geometry and asymptotics | Step 4 | glue / standard |
| `level_of_tiedWin`, `exists_small_eps`, `level_family`, `formB` | `TGC/TopWin.lean:68-81, 59-66`; `PC/LevelFamily.lean:41-52`; `PC/Imports.lean:8-19` | §2.1 | glue | glue |

---

## 4. Oddities

1. **e_D + e_L + 7 > 0 is forced** (`ConstsBound`, `ErrorFormsWeakWindowsFalse.lean:24-27`; `CoreGm.lean:46`). The
   NODE-LANDAU §4 worry is closed.
2. **The windows can be arbitrarily sparse.** Only a fixed log-ratio 1+δ is needed, with σ ≈ 36/δ² (σ = 336 at δ = 1/2).
   That is correct. It means the burden is on (I) at *every* x of a window [Y, Y^{3/2}], since a window gives Landau
   nothing unless the bound holds at all of its points.
3. The hypothesis of the Landau lemma is a bound on G_m at the scale x, not at a = x·b. The parameter b = e^{x^ε} lives
   only inside the host count; the bridge moves from a_t/b to x at a cost of O(log x) (NODE-CHBALANCE §2(c)).
4. **The split primes are covered by `PairGood`** (pointwise GRH-quality bounds for the quadratic twists at y ∈ [Y, Y^A]),
   not by an identity. This is the second square-root input besides core_gm; its proof was examined in NODE-PAIRGOOD.
   The review's question is answered by it: the twists are bounded, not cancelled.
5. The 4:3 ratio is not forced by anything read; any positive share measure with positive Fourier mass at ψ would serve.
6. ζ (weight 1) is in every level, so input (I) alone would already give RH.
7. `LandauWinAt`/`LandauWin` (`TGC/Window.lean:24-28`) and `ChebyshevGrowthImpliesZeroFree`
   (`ExplicitFormulaErrorOfHostConditions.lean:40-41`) are alternative forms that the live path does not use.

---

## 5. Coverage

**Read in full:**
- `LT/`: ZeroFreeOfRpowWindow, lemmaL, WindowHypOfRpow, WindowHypUOfWindowHyp, landauWindow, poleData, LandauPoleReLe,
  LandauDichotomy, LandauGrowthContra, LandauCoeff, LandauKernelMax, kernelIntegral, LandauFinite, LandauNearest,
  LandauPoleAsym, LandauCauchy, landauTails, landauWindowIneq, CharFamilyLFunctionNeZeroOfOneLeRe;
- `DL/LandauZeroFreeCriterion.lean`, `DL/CharFamily.lean`;
- `CB/ZeroFreeAllOfTopG.lean`, `PC/CoreGm.lean`, `TGC/TopWin.lean:1-140`.

**Read in part:**
- `LT/mellinGchiOfNeOne.lean:110-146`, `LT/mellinGchiModOne.lean:112-125`, `LT/GchiGrowth.lean:30-70`;
  `LT/IteratedDerivLaplace.lean` (statement `:84-87` only);
- `PC/Imports.lean:1-19`, `PC/LevelFamily.lean:30-52`, `PC/LevelGmLeOnFamilyScales.lean:1-38`, `PC/CoreAtH.lean:1-48`;
- `SWB/ErrorFormsWeakWindowsFalse.lean:1-60`;
- `TGC/Window.lean:1-40`, `TGC/ExplicitFormulaErrorOfHostConditions.lean:1-165`, `TGC/Analytic.lean:80-92, 150-160`
  (and grep hits at 88, 92, 94, 106, 127, 136, 138, 154);
- `CB/BoundedTw.lean:1-56`, `CB/PairGood.lean:1-40`, `CB/TwistForm.lean:1-40`.

**Notes:** NODE-ROOT, NODE-LANDAU, NODE-COREGM, NODE-CHBALANCE (1-180), NODE-HOSTS (1-70), NODE-VWIN (1-45), NODE-FAMILY
(1-45), NODE-PAIRGOOD (1-30), MAIN-ARGUMENT §1–2 and §6, REVIEW-MAIN-ARGUMENT A1 §1–2 and A4.

**Greps:**
- `sorry|axiom|admit|native_decide|implemented_by|extern` over `DL/LandauTheorems/`, `LandauZeroFreeCriterion.lean`,
  `CharFamily.lean`: no hits outside ChCore/ChBalance/ChTop.
- `Shares|φ\.lam|Frame\.lam`, as in §2.3.

**Not opened:**
- the body of `iteratedDeriv_laplace`;
- `ChBalance`/`ChCore` (taken from NODE-COREGM/CHBALANCE);
- `sigA_le`, `gmA_eq`, `PAIRGOOD`'s `pairEx` body;
- the body of `ThinH`'s producer and `ChebyshevCharacterBound`;
- the TT construction (`ThickFrames/topsFrame.lean`).
