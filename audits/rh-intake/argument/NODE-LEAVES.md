# NODE-LEAVES: the three arithmetic leaves under the kernel law

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `TI/` = `Formalism/LocalToGlobal/TorsionIntegrality/`; `TTP/` = `TI/TorsionTranslationPowers/`; `NJN/` = `TTP/NonsingularJetNorms/`
- `GSP/` = `TI/GaussSumParity/`; `KTL/` = `GSP/KummerThetaLogarithms/`; `SLDU` = `KTL/SecondLogDerivativeUnique.lean`
- `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`; `ICL/` = `IKT/InertCoprimeLemmas/`; `K1LT` = `ICL/K1RepresentativesLTOfDictionary.lean`
- `SC` = `TI/EisensteinTranslationProducts/SemiChar.lean`

## 0. Verdict (short)

All three leaves are proved in the tree, and each proof is a classical argument I can name. I found nothing false.

- **L-A, per-letter law (`joint_integrality`).** This is the integrality of the Kronecker theta function at prime-to-p
  torsion. The proof is algebraic and needs **no CM, no s₂ and no supersingularity**:
  - the σ-addition formula, packaged as `IsTransSys`;
  - a telescoping product that writes G_t^N as a unit times ∏ (x(t) − x(z + jt))^{…};
  - integrality of prime-to-p torsion (a Nagell–Lutz-type lemma);
  - extraction of an N-th root with p ∤ N.

  s₂ cancels identically. Its only use is to make the Lean's normalisation e^{−πz t̄/A} the right linear term. I checked
  that normalisation numerically for the Lean's own definitions.
- **L-A, `NormRel`.** For α = m + nω_K prime to p it is the classical distribution relation: σ\*(αz)/σ\*(z)^{Nα} is
  elliptic up to sign, with divisor on E[α]. Its s₂ input is the exact identity **α(α − ᾱ)·s₂ = Σ_{P ∈ E[α]∖0} ℘(P)**,
  proved in `cdata` (SLDU:136-148). Density to all units of ℤ_{p²} is sound: the NormRel set is closed because the
  coefficients of ph([α]T) are polynomials in α. Extension to all integral α uses "every element is a sum of two units".
  - The numerical tests pass exactly (§2). With a wrong s₂ they fail at T^{2p} for every non-real α, and stay integral
    for real α. So the tests are sharp in both directions.
- **L-B.** `lamPos_of_posEmb` is a three-line rewrite (conj∘conj = id). The content is the field `pos` of `CmpHyp`,
  which comes from `pos_C`/`posOK` of the construction. The CM type is Ψ = Gal(E/K). The orbit generator is
  z = Frob_p·c = (1, h) (with Frob_p = (c₀, h)). The position (v, s) is the embedding r_v·z^s. Composed with c^s it is
  r_v·Frob^s, and it becomes σ^s∘ρ_v under the p-adic embedding.
  - "Served" means n′ = ord(h) is even, which is equivalent to c ∉ ⟨Frob_p⟩: the places of E⁺ over p split in E.
  - The NUMTEST3/4 identity Σ_k f_k σ^j(f_k) = δ_{j0}/λ is the **input** `LamONB` of `hypCoordLt_of`, not its output
    `IsHypPair`. NUMTEST3's A·A^σ + C·C^σ = 0 is the n′ = 2 instance of the output (`iso_fK`).
- **L-C.**
  - The "fourth-power trick" guess is **confirmed**, verbatim: `fourth_power` (`NJN/GeneralIntegrality.lean:160`) takes the
    coefficient at (ν,ν,ν,ν) of tensor4 f, which is f_ν⁴.
  - `pairs_standard_at_p` is coset averaging with prime-to-p index; read in full, correct.
  - **s₂ is p-integral at every p ≥ 5 with p ∤ d.** From the identity with α = √−d: −2d·s₂ = Σ_{P ∈ E[√−d]∖0} ℘(P), and
    the ℘(P) are integral by CM4 (`homothetic_lattice_integral_of`). So `OneLetterGaussInt`'s ‖s₂‖ ≤ 1 is **true**.
    Numerically, s₂ = 1 for y² = x³ − 35x − 98. The statement is **off the main path**: `oneLetterGaussInt` has no
    users, and neither VJoint nor NormRel needs it. Katz's supersingular subtlety concerns p-adic interpolation of E₂, not
    the integrality of the algebraic number E₂\*(Λ).

## 1. Statements and arguments

### L-A1. `joint_integrality : VJoint`

**Statement.** `TTP/StatementX.lean:31`; proved at `NJN/Joints.lean:128`, consumed by `factors` in
`UGM/OrthogonalGaussModels/OrthogonalShapeOneLetter.lean:22`.

Fix:
- l ≠ 2 prime, and a period lattice L whose short Weierstrass curve over ℂ_l is integral with unit Δ (`IntCurve`);
- g₂, g₃, s₂, ε in ℚ̂_l^{ur}, the images of L.g₂, L.g₃, s₂(L), with ‖ε‖ = 1;
- thetaS(g₂, g₃, ε) with integral coefficients (the Honda-to-Weierstrass isomorphism θ, CM3);
- ω₀ ∈ L with ω₀/2 ∉ L;
- s with N·s ∈ L, where N > 0 and l ∤ N.

Then

  exp(−phFF(T)) · V(T) = [taylor0(opU_s(th0_{ω₀/2}))](ε·ℓ(T)),  with V integral.

The pieces are:
- ℓ is the Honda logarithm Σ T^{p^{2j}}/p^j (`lgF`, `UTS/OddLogRelation.lean:13`).
- phFF = −σ-log-series(εℓ) + (s₂/2)(εℓ)² − log(ℓ/T) (`GSP/StatementE.lean:24`). That is,
  **exp(−phFF) = σ\*(εℓ(T))/T**.
- th0_t(z) = σ\*(z+t)e^{−πz t̄/A}/σ\*(t) (SC:27-34).
- opU_s(F)(z) = F(z+s)·e^{−πz s̄/A − π|s|²/2A}.

So V is the Kronecker quotient T·σ\*(z+t′)e^{−πz t̄′/A}/(σ\*(z)σ\*(t′)), up to a unit and a root of unity
(`OpUTh0Root`). Here t′ = s + ω₀/2 is torsion of order prime to l. The statement covers s = 0, i.e. th0 itself.
"≃" is not involved: this is an exact factorisation with V integral (`IntS`: every coefficient has norm ≤ 1).

**Argument** (`NJN/VIntegral.lean:46-71`, `NJN/Taylor0ConstMul.lean:180-271`, `TTP/AnalyticTransOfAdd.lean`):
1. Split exp(phFF)·thetaOne = exp(phFF − phL∘θ) · θ\*(exp(phL)·inU(opU_s th0)). The first factor is θ(T)/T-type and
   integral, by `phCompare` with θ integral and ‖ε‖ = 1. The second factor lives in the Weierstrass parameter of the
   model.
2. In the Weierstrass parameter put G_t := exp(phL)·inU(opU_t σ\*) = T·σ\*(z+t)e^{…}/σ\*(z).
   - `AnalyticSys`/`IsTransSys` (TTP/IsTransSys.lean:60) records G_0 = εT and the σ-addition formula
     X²·G(P+Q)G(P−Q) = G_Q(0)²·(x(Q)X² − X²x(z+P))·G(P)².
   - `TransPower` iterates this to G((k+1)t)·X^k = G(t)^{k+1}·∏_j (G_t(0)²(x(t) − x(z+(j+1)t)))^{k−j}.
3. With Nt = 0:
   - prime-to-l torsion is integral (`torsion_integral`, via `Formalism.ELL.torsionIntegral`, for any integral model);
   - x(t) − x(z + jt) is a unit series, because distinct prime-to-l torsion points stay distinct mod the maximal ideal
     (`FacShape`);
   - so G_t^N = unit·OneUnit, and the N-th root is integral since ‖N‖ = 1 (`rootInt`).
   - That ‖G_t(0)‖ = 1 comes from a parallelogram law for M(t) = log‖G_t(0)‖ on the finite group ⟨t⟩. Summing
     M(P+Q) + M(P−Q) − 2M(P) = 2M(Q) over P gives M(Q) = 0 (`ParSum`). I checked this little lemma by hand.
4. Finally `Th0Analytic_of` combines t = s + ω₀/2 with `OpUTh0Root`, and `GaussOne` gives integrality.

**Classical identification.** This is the integrality of the Kronecker theta function / Siegel-unit-type functions at
prime-to-p level. Compare de Shalit II.2–II.4 and Bannai–Kobayashi on Kronecker theta.

**Where CM and s₂ enter.**
- They do not enter step 2–3: s₂ cancels in σ\*(z+t)/(σ\*(z)σ\*(t)), and the leftover exponent −(s₂t + πt̄/A)z = −η(t)z
  is exactly the quasi-period term.
- Whether the Lean's `herm`/`area`/`s2` produce exactly that term is a sign and normalisation question. I checked it
  numerically (§2.1): K_t² = ℘ − ℘(t) at 2-torsion, and the multipliers are N-th roots of unity at N-torsion.
- CM4 is not used here. Torsion integrality is the general lemma.
- CM3 enters through hθ, which says that θ is integral.

### L-A2. `NormRel`, and extension to all integral α

**Statement.** `GSP/StatementC.lean:27`:

  NormRel l σ ph α :⇔ Simeq(ph(mulS α), α·σ(α)·ph),  where mulS α = exp_F(α·ℓ(T)) = [α]_F(T).

Simeq f g :⇔ cc(f−g) = 0 and exp(f − g) has integral coefficients (`UTS/CyclicPowerClassOfExpEquiv.lean:22`), in the
same variable T. So NormRel says:

  **exp(ph([α]T) − α σ(α) ph(T)) = ([α]T/T^{Nα})·σ\*(z)^{Nα}/σ\*(αz) is integral in the LT parameter.**

Here σ is any Frobenius lift on ℚ̂_l^{ur} (`UnrOK`). On ℤ_{p²} it is the nontrivial automorphism, so σ(ι ω_K) = ι(ω̄_K)
(`SplitPh`/`sqrtKur`).

**Argument for α = m + nω_K with l ∤ N(α)** (`NRDense_of`, SLDU:290-411):
- `cdata` (SLDU:136) lists E[α]∖0 (card N − 1, closed under negation) and the ℘-relation `IsEndoZ`. It also proves
  **α(α − ᾱ)·s₂ = Σ_P ℘(P)**.
  - This is the comparison of the z²-terms of the elliptic function σ\*(αz)/σ\*(z)^N. Classically this is how E₂\* at CM
    points is shown algebraic (Masser).
- CM4 makes x(P), y(P) integral and unramified.
- `curveNorm` (SLDU:218) gives the Weierstrass-parameter version.
- `transportNorm` moves it to LT coordinates through θ, using θ∘[α]_F = [α]_E∘θ (`theta_comm`).

Density (`normUnits`, `KTL/SecondLevelOfNormHolds.lean:387`):
- The set {α : NormRel α} is closed. This is `phNormClosed`, whose statement (`TI/SecondCoefficientNorms/PhNormClosed.lean:17`)
  holds because each coefficient of ph∘mulS α − ασ(α)ph is a polynomial in (α, σα), and the unit ball is closed. Body
  not read, but the statement is evidently true.
- σ is an isometry (`sigma_isometry`), so continuous.
- `denseOK` gives O_K-elements prime to l arbitrarily close to any unit of ℤ_{p²}.
- So **(i): continuity in α is proved (it is polynomiality), and the density step is sound.**

Extension to all integral α:
- `two_units` (SecondLevelOfNormHolds:220): α = (α+1) + (−1) if |α| < 1, else 2α + (−α).
- Then `endoAll` / `normAdjAll`, which use biadditivity of be = cob(ph) (cube).
- I read the top level only.

**(ii) CM2/CM3/CM4.**
- CM2 gives the good model over ℚ̂^{ur} (`IsGoodModel`).
- CM3 gives integral θ (hθ).
- CM4 gives integral, unramified prime-to-p torsion, in `NRDense_of` and in `homothetic_lattice_integral_of`.
- `joint_integrality` uses none of CM2/3/4 directly; it takes their outputs as hypotheses.

**(iii)** Nothing on the main path needs ‖s₂‖ ≤ 1. s₂ appears only through the identity above. It is in fact integral
anyway (L-C).

### L-B. `lamPos_of_posEmb` and `hypCoordLt_of`

**`lamPos_of_posEmb`** (`Development/AbelianVarietyTheory/Proofs/SatakeParameters/LamPosOfPosEmb.lean:39-54`).
- Hypothesis hpos: e(tEL(pos⟨v,s⟩)(s even ? x : σ_D x)) = ι_v(σ_v^s(ρ_v x)).
- Conclusion `LamPosG` (`IKT/FrameInt.lean:44`): λ(τ_{v,s}(x)) = twE_{v,s}(ρ_v(s odd ? x̄ : x)).
- The proof substitutes x̄ for x at odd s and uses σ_D = conj, conj∘conj = id (`posArg_eq_self`). It is pure glue.

**Where the content is.**
- hpos is the field `pos` of `CmpHyp`/`CmpHyp0` (`GroupLattices/ComparisonMaps/LatticeComparisonCompatible.lean:44`).
- It is supplied by `pos_C` (`GroupLattices/TiedFamilies/TieIwLevTieOf.lean:56-96`) from `posOK` (not opened) and the
  position map `posG(zPsi …)` (`GroupLattices/LevelGatherings/SecPsiMulPow.lean:64,148-158`).
- `posG⟨v,s⟩ = orbRep_v·z^s` and `zPsi h = (c₀, h)·cc = ((1,1), h)`.
- Then emb(posG⟨v,s⟩·cc^s) = emb(r_v·(c₀,h)^s) = r_v·Frob^s, with Frob_p = (c₀, h) (NUMTEST4 §A).

**"Served place" in these terms.**
- p is inert in K, Frob_p = (c₀, h) ∈ Gal(K/ℚ) × A.
- The CM type is Ψ = Gal(E/K), the subgroup of index 2 containing z = Frob·c.
- A place v is a ⟨z⟩-orbit on Ψ, of length n′ = ord(h). The place is served when n′ is even (`HidaSetting`, `hev`).
  This holds iff c ∉ ⟨Frob_p⟩, iff the primes of E⁺ above p split in E.
- Then E ⊗ ℚ_p ⊇ E_w × E_{w̄}: the hermitian space is hyperbolic. Even positions s give one Lagrangian (embeddings r_v·Frob^s);
  odd positions give the conjugate one.

**`hypCoordLt_of`** (K1LT:84-115).
- Inputs:
  - `LamTraceLt` (IKT/DefsRepLt.lean:114): every orthonormal local basis b satisfies `LamONB` (IKT/DefsRepFrame.lean:110),
    Σ_i λ(τ(b_i))·λ(τ′(b̄_i)) = δ_{ττ′};
  - `LamPosG`; `FrobTw`; n′ even; `MInv`; `FrameIntLt` (integrality of the frame entries).
- Output: `IsHypPair σ f f′` (UGM/IsHypPair.lean:23). The coefficients f, f′ are integral and σ²-fixed, and they are
  isotropic and dual: Σ_i σ(f_{ei})f_{e′i} = 0, Σ_i σ(f′)f′ = 0, Σ_i σ(f_{ei})f′_{e′i} = δ_{ee′}.

**Comparison with NUMTEST.**
- NUMTEST4's exact identity Σ_k f_k σ^j(f_k) = δ_{j0}/λ is LamONB (column orthonormality across the Frobenius-twisted
  embeddings), in its instance. It is the input, not the IsHypPair output.
- The output is derived from it by the algebra of `iso_fK`/`dual_fK`/`sigma2_fK` (RepFrame.lean, bodies not read).
- In the n′ = 2 instance, NUMTEST3's A·A^σ + C·C^σ = 0 is exactly the isotropy of the even-position direction (`iso_fK`).
  Its controls (broken isotropy ⇒ gain lost; isotropy mod p only ⇒ gain kept) test the output.
- So **both ends were tested numerically; the bridging algebra was not.**

### L-C. One-copy step and the remaining leaves

| leaf | statement | main path? | proof |
|---|---|---|---|
| `kappa_integral_of_calculation` (`UGM/OrthogonalGaussModels/KappaIntegralOfCalculation.lean:18`) | if tens4 Θ composed with a unitary 4n×4n frame γ over ℤ_{p²} is a product of letters e^{−ph}·V, then exp(Σph)·Θ is integral | yes (`kappa_integral`, `OneLetterGaussSharpTranslateHolds.lean:35`) | `generalIntOf` = `GeneralIntOf_of fourth_power unitaryInv …` (`NJN/GeneralIntegrality.lean:162-212`): (1) undo γ; Σph is γ-invariant mod ≃ (`unitaryInv`, i.e. NormRel + AdjAt, the hermitian invariance); (2) so tens4(exp(Σph)·Θ) is integral; (3) **`fourth_power`**: coefficient ν⁴ of tensor4 f is f_ν⁴, so ‖f_ν‖ ≤ 1. **Guess confirmed.** |
| `pairs_standard_at_p` (`ICL/IntStd.lean:302-376`), statement `StdStep` (IKT/DefsInt.lean:101) | a prime-to-p translate of eNat_{M,M′} is Σ c_k·U_{s_k}(thZero) with c_k algebraic, p-integral and s_k prime-to-p torsion of the standard lattice | yes | read in full: two coset averages `Iop` (std → (M, std) → (M, M′)), each of index prime to p (`idx_coprime`: s·La₂ ⊂ La₁ with p ∤ s); coefficients 1/√index (`good_iota`), phase `al`, the cocycle `cf` (a root of unity because Im H(x,y) ∈ ℚ, `im_rat`), and χ-factor a unit (`chiFacUnit`). Correct. |
| `nrDense` | NormRel for O_K-elements prime to l | yes | §L-A2 |
| `OneLetterGaussInt` (`UGM/StatementA.lean:77`) | there is a good model with ‖s₂‖ ≤ 1, etc. | **no** (`oneLetterGaussInt` has no users) | via `homothetic_lattice_integral_of` (`KTL/HomotheticLatticeIntegralOf.lean:24`): α = −1+2ω = √−d, α(α−ᾱ) = −2d, so s₂ = −(2d)⁻¹Σ℘(P), integral at l ∤ 2d by CM4. **True.** |
| `baseChange_preserves_unitary_of` | the name is used for at least eight unrelated theorems; the one GAUSSCLASS meant is `MV/DworkExponentialRestrictions.lean:137` (admitted + RestBeta + RestGc ⇒ class), used by `MV/CommonEigenvectorThird.lean:33` | yes | not opened; outside this node's three leaves |

**The s₂ question, settled.**
- s₂(Λ) = E₂\*-value is algebraic and, by the norm identity, **l-integral for all l ≥ 5, l ∤ d**, once Λ is normalised
  to have an integral, unit-discriminant model.
- Numerically (§2.1): s₂ = 0 for ℤ[i] and ℤ[ω]; **s₂ = 1** for y² = x³ − 35x − 98 (d = 7), matching
  ℘(P)/(ω(ω − ω̄)) = 1.
- Katz's supersingular issue is that the p-adic modular form E₂ and the real-analytic E₂\* disagree at non-ordinary CM
  points. It is not about integrality, and the Lean only ever uses E₂\*(Λ).

## 2. Numerics

Scripts are `numtest/leaves_float.py` and `numtest/leaves_normrel.py`; outputs are `out_leaves_float.txt` and
`out_leaves_normrel_M64.txt` (+ `_M130`).

### 2.1 Float check of the Lean's analytic normalisation (SC:8-34 implemented literally)

σ is computed from the q-product, ℘ from the q-series, and wEta by Legendre. The σ quasi-periodicity with the Lean's
wEta holds to 1e-12.

| curve | Lean s2 | K_t² = ℘ − ℘(t), three 2-torsion t | multipliers of K_t, N = 3, 5 | σ\*(αz)/σ\*(z)^N periodic (Lean s2 / s2 + 1) |
|---|---|---|---|---|
| ℤ[i], g₂=4 | 0 (1e-13) | rel. err ≤ 3e-15 | N-th roots of unity to 2e-15 | α=2+i: 4e-15 / **1e4**; α=1+i: ratio exactly −1 / fails; α=2: both periodic |
| ℤ[ω], g₃=−4 | 0 | ≤ 2e-15 | ≤ 2e-15 | α=1−ω, 2+ω: 2e-15 / **4e4**; α=2 both |
| d=7, y²=x³−35x−98 | **1.000000000000** | ≤ 3e-15 | ≤ 2e-15 | α=ω: ratio −1 / fails; α=2 both |

A ratio of −1 is the sign character (semiChar). The function is elliptic up to sign, which is irrelevant for
integrality: the Lean works with second log-derivatives.

### 2.2 Exact integrality in the Weierstrass formal parameter T = −x/y (to T^128)

Everything is computed exactly in ℚ(√−d). Since p is inert, v_p(a + b√−d) = min(v_p a, v_p b).

The quantities are:
- NR = exp(ph([α]T) − Nα·ph(T));
- PH = exp(−ph) = σ\*(z(T))/T;
- KR = T·K_t(z(T)) at 2-torsion.

| curve, p | PH (one σ\*) | KR (2-torsion translates) | NR, true s₂ | NR, wrong s₂ (non-real α) | NR, α = 2 any s₂ |
|---|---|---|---|---|---|
| ℤ[i], 7 | first v<0 at T^8, min −18 | integral | α=1+i, 2+i: integral | s₂=1: fails at T^14 | integral |
| ℤ[i], 11 | T^12, min −10 | integral | integral | T^22 | integral |
| ℤ[ω], 5 | T^6, min −25 | integral | α=1−ω, 2+ω: integral | s₂=1: T^10 | integral |
| ℤ[ω], 11 | T^12 | integral | integral | T^22 | integral |
| d=7, 5 | T^6, min −25 | integral (x(t) = 7, (−7+√−7)/2) | α=ω, 1+ω: integral | s₂=0 or 2: T^10 | integral |
| d=7, 13 | T^14 | integral | integral | T^26 | integral |

**§2.3, extended to T^260** (`out_leaves_normrel_M130.txt`). Every row is unchanged.
- At p = 5 this covers T^{126} = T^{p³+1}, past the third Honda level. At p = 7 and 11 it covers past p² + 1.
- Every true-s₂ NR and every KR series is integral up to T^260.
- The wrong-s₂ failures are at the same degrees as before.
- PH minima reach −36 (ℤ[i], p = 7), −52 (p = 5) and −19 (d = 7, p = 13). That is about −(degree)/(p²−1)·…, so it
  grows linearly, as expected for ph.

How to read the table:
- PH is non-integral from T^{p+1}. This is ph itself, consistent with NUMTEST's a/(p²−1).
- The specific combinations claimed by the Lean are integral.
- A wrong s₂ is caught at T^{2p} exactly when α² ≠ αᾱ. This is the predicted factor exp(−δs₂(α² − Nα)z²/2).

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `ThetaZeroAnalytic` chain: `AnalyticSys_of`, `translate_power`, `FacShape_of`, `root_integral_alt`, `TransPar`/`ParSum` | NJN/AnaSys.lean:387; TTP/StatementT.lean; TTP/FacShapeZero.lean | σ-addition formula in T; telescoping; unit differences of torsion x-coordinates; root extraction | standard (Kronecker theta / Siegel units); statements read, bodies of AnaSys/translate_power not read |
| 2 | `Formalism.ELL.torsionIntegral` | EllipticTorsion | prime-to-p torsion of an integral model is integral | standard (Nagell–Lutz-type) |
| 3 | `phCompare`, `transportNorm`, `theta_comm` | GSP/BiextensionRelation.lean:11; StatementC:60 | transfer Weierstrass ↔ LT through integral θ | glue/standard |
| 4 | `cdata`, `curveNorm` | SLDU:136, 218 | E[α] data, α(α−ᾱ)s₂ = Σ℘(P); distribution relation | **core**, classical; statements read, bodies partly |
| 5 | `phNormClosed`, `denseOK`, `two_units`, `endoAll` | PhNormFromDatum.lean:18; FinalOfNRDense.lean:11; SecondLevelOfNormHolds:220 | closedness, density, two units | standard |
| 6 | `posOK` / `pos_C` | TieIwLevTieOf.lean:56 | position (v, s) = r_v·Frob^s | **core** for L-B; posOK not opened |
| 7 | `iso_fK`, `dual_fK`, `sigma2_fK` | ICL/RepFrame.lean | LamONB + positions ⇒ IsHypPair | core, formal; not read |
| 8 | `fourth_power`, `unitaryInv`, `product_integral` | NJN/GeneralIntegrality.lean:160 | one-copy integrality | fourth_power read (correct); unitaryInv standard-formal |
| 9 | `pairs_standard_at_p` | ICL/IntStd.lean:302 | coset averaging | read, correct |
| 10 | `homothetic_lattice_integral_of` | KTL/HomotheticLatticeIntegralOf.lean:24 | ‖s₂‖ ≤ 1 | read top; off-path |

## 4. Oddities

1. **`joint_integrality` is stronger than its context suggests.** It holds for every lattice with good reduction (no CM).
   The "inert" hypothesis enters only through θ (CM3) and NormRel. That is fine, but it means the per-letter law carries
   no Gaussian content at all, consistent with GAUSSCLASS.
2. **Sign character.** σ\*(αz)/σ\*(z)^{Nα} is periodic only up to ±1 for some α (e.g. 1+i, ω). The Lean never claims
   ellipticity. It uses ℘-identities and the second log-derivative (`endoCurve_of_endoZ`), so there is no issue.
3. `lamPos_of_posEmb` carries no content of its own. The served-place structure is the `pos` field of `CmpHyp`,
   supplied by `pos_C` from `posOK`. I did not open `posOK`.
4. `OneLetterGaussInt` is unused, and the name `baseChange_preserves_unitary_of` is reused for unrelated theorems.
   Both are cosmetic.
5. The NormRel σ is an arbitrary Frobenius lift. That is harmless: on ℤ_{p²} all lifts agree, which is what `SplitPh`
   records.
6. Not followed: the bodies of `AnaSys`, `translate_power`, `curveNorm`, `iso_fK`, `unitaryInv`, `posOK`,
   `phNormClosed`.

## 5. Judgement and ranking

- **L-A: correct**, proved from recognisable mathematics (Kronecker theta integrality; distribution relation with E₂\*;
  density). Numerically confirmed, with negative controls.
- **L-B: correct** as a statement. The proof here is glue, and the content (positions = Frobenius twists of one
  embedding; served ⇔ n′ even) is classical CM-type bookkeeping. The bridging algebra LamONB ⇒ IsHypPair is unread
  but tested at both ends.
- **L-C: correct.** The fourth-power trick is confirmed. The s₂ question is settled (integral, off-path).

Children to open next, by value:
1. `posOK` (the actual supplier of the served-place structure);
2. `iso_fK`/`dual_fK`;
3. `AnaSys_of` (the σ-addition formula in T, which is the analytic-to-formal bridge);
4. `unitaryInv`.

None looks false.

## 6. Coverage

Read:
- `OrthogonalShapeOneLetter.lean` (all); `NJN/Joints.lean` (all); `NJN/VIntegral.lean` (all); `TTP/StatementV`,
  `StatementX`, `StatementA`, `StatementT`, `StatementN` (all); `TTP/IsTransSys.lean` (all); `AnalyticTransOfAdd.lean`
  (all); `NJN/Taylor0ConstMul.lean:1-60, 175-271`; `NJN/GeneralIntegrality.lean:100-214`;
- SC (all); `FrobeniusFibreCurves/CurveHyp.lean:60-100`; `GSP/StatementE.lean:1-60`; `GSP/StatementC.lean:1-100`;
  `GSP/HomotheticLatticeIntegralS2.lean:15-70`; SLDU:72-90, 136-150, 218-232, 280-411;
  `KTL/SecondLevelOfNormHolds.lean:60-108, 214-300, 387-406`; `PhNormClosed.lean:17-22`;
  `HomotheticLatticeIntegralOf.lean:24-70`; `RepDict.lean:415-440`;
- `LamPosOfPosEmb.lean` (all); `SitePlaceInducesPositionEmbeddings.lean`; `IKT/FrameInt.lean:20-70`;
  `ComparisonMaps/ValRat.lean:55-75`; `CmpLApply.lean:60-100`; `LatticeComparisonCompatible.lean` (all);
  `CmpHyp0P.lean` (all); `TieIwLevTieOf.lean:54-96`; `SecPsiMulPow.lean:1-160`; `ChartComparison/LocMore.lean:20-60`;
  K1LT:60-130; `UGM/IsHypPair.lean:23-35`; `IKT/DefsRepLt.lean:114-128`; `DefsRepFrame.lean:110`;
- `KappaIntegralOfCalculation.lean:1-45`; `UGM/StatementA.lean:70-85`; `ICL/IntStd.lean:169-220, 302-376`;
  `IKT/DefsInt.lean:95-125`.

Not opened: `posOK`, `RepFrame.lean` lemma bodies, `AnaSys.lean`, `TransW.lean`, `translate_power`, `curveNorm` body,
`unitaryInv`, `logNormClosed'`, `denseOK` body, `CM2/3/4` (see KERNELLAW).
