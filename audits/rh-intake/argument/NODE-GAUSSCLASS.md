# NODE-GAUSSCLASS: does the full theta kernel lie in the Gaussian class exp(−(π/p)hh)·(integral)?

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `MV/` = `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/`; `DER` = `MV/DworkExponentialRestrictions.lean`
- `UTS/` = `Formalism/ThetaLogCoordinates/UniformThetaSubstitution/`; `SE` = `UTS/StatementE.lean`
- `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`; `ICL/` = `IKT/InertCoprimeLemmas/`
- `UGM/` = `Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/`
- `K1LT` = `ICL/K1RepresentativesLTOfDictionary.lean`

## 0. Verdict (short)

**Class membership of the full kernel is proved by a chain of six statements, and I could reconstruct each link as
mathematics.** Four of the links are formal algebra about the height-2 Honda formal group and hermitian forms over
ℤ_{p²}. I read them and they are right. The arithmetic sits in three places:
1. a one-variable integrality law for prime-to-p torsion translates of σ\*;
2. the classical integrality of Θ_L / ∏σ\*;
3. the structure of the CM type at a served place (`LamPos`).

I read the statements of these three and the reductions that consume them. I did not read the bodies of their leaves.

The chain (the Lean says; the glosses are mine):

| # | statement | where | content |
|---|---|---|---|
| 1 | `IntInert` | IKT/StatementInt.lean:18 | for every admitted (L, L′), every p-integral combination F of prime-to-p translates of θ_{L,L′}, and every **orthonormal** local O_K-basis b: exp(Σ_i ph(X_i))·F(Σ X_i b_i) is integral in LT parameters. **No Gaussian content, and no served hypothesis.** The hypothesis is only that p is inert in K. |
| 2 | `FrameHyp` (`frameHypLt_of_lat`) | K1LT:178 | at a served place, the kernel in position variables equals Θ_orth∘hypLin(f, f′), where (f, f′) is a **unimodular hyperbolic pair over ℤ_{p²}** (σ²-fixed). Even positions go to x_e and odd positions to y_e. |
| 3 | `HypShape` (`hyperbolic_of_orthogonal`) | UGM/UniformGaussModelCondition.lean:42; ICL/ConstantCoeffFormalSum.lean:402 | Σ_i ph(X_i) ≃ Σ_e be(x_e, y_e) after the hyperbolic change, where be = cob(ph) is the polarisation. The self-terms cancel by isotropy. |
| 4 | `RestBeta` (`restBeta` → `betaIsG`) | DER:15; MV/BiadditiveSecondVariable.lean:137; UTS/IsLawOfLog.lean:98 | every biadditive hermitian be (mod ≃) is ≃ Gser(c, σc), with c ∈ W(F_{p²}) |
| 5 | `RestGc` (`restGc` → `gcCondition_of_twoSums`) | DER:22; MV/TwoSumsCondition.lean:174 | exp(−Σ_e Gser(x_e, y_e)) in ϖ-rescaled position coordinates equals exp(−(π/p)·hh_u)·V, with V integral |
| 6 | Dwork / `InClass` | FGS:220, 236 | exp(−(π/p)hh) = Σ (−π)^i hh^i/(i! p^i), and π^i/i! is integral, so the kernel ∈ InClass(hh) |

**Why the coupling is s ↔ s+1 and never s ↔ s** (answer to the brief's central question). There are three causes:
1. The 1/p part of Gser is exactly (c·x·y^p − σc·x^p·y)/p. It is a function of two points x, y of the formal group,
   because it is a polarisation.
2. In position coordinates, x_r = ϖΣ_{s even} σ^s(ω\*_r)Z_s and y_r = ϖΣ_{s odd} σ^s(ω_r)Z_s. Here (ω, ω\*) are dual
   bases of W(F_{p^{n′}}) over W(F_{p²}), with Σ_i σ^{2i}(ω_r ω\*_{r′}) = δ (FGS:172).
3. Mod p, y^p = Σ σ^{s+1}(ω)Z_s^p. Hence Σ_r x_r y_r^p = Σ_{t, t′} S_t·S_{t′}^p·Σ_r σ^t(ω\*_r)σ^{t′+1}(ω_r), and the
   inner sum is δ_{t, t′+1} by column orthogonality of the square dual matrices.

So the s ↔ s+1 adjacency is **trace duality for the unramified extension**. It is not a property of the theta function.
The theta function's contribution is that its Gaussian is a hyperbolic cross form, not a diagonal one. That happens only
because the hermitian space is split at a served place.

## 1. Statement

The composite statement (assembled from FGS:162, 220; DER:22; `theta_kernel_expansion`,
`MV/CommonEigenvectorThird.lean:32`) reads as follows. Fix:
- p ≥ 5 inert in K;
- a served place v of the host (n′_v even, `HidaSetting`);
- admitted lattices (L, L′) (even rank, self-dual hermitian O_E-lattices);
- a frame φ.

Let Θ be the local kernel, i.e. the Taylor series of the global theta in the frame-changed position variables, rescaled
by ϖ (ϖ^{p²−1} = p). Then there are u_s ∈ W[ϖ] and integral series g_i with

  coeff_n Θ = Σ_i p^{−i}·coeff_n(hh^i·g_i),  hh = Σ_s u_s Σ_{a,b} S_{s,a,b}^p·S_{s+1,a,b},  S_s = Σ_l (−1)^l Z_{s−2l}^{p^{2l}}.

Moreover u_s = uS(c, σc)(s): u_s = c for s odd and −σc for s even (UTS/CyclicPowerClassOfExpEquiv.lean:89). Here c is
the single constant of the curve given by RestBeta, and by `stepIII` (`c_add_sigma_c_eq_zero`, UTS/FinalS.lean) it
satisfies σc = −c, so u_s = c for every s. It is the same for every rank, entry, place and level.

## 2. Argument, link by link

### (a) The one-variable dictionary

**What the Lean states about one σ\*.** It does **not** state "σ\* = exp(quadratic form)·integral". The one-variable
objects are:
- ph = phFF(g₂, g₃, s₂, ε) (`TorsionIntegrality/GaussSumParity/StatementE.lean:24`):
  ph(T) = −log σ(εℓ(T)) + (s₂/2)(εℓ(T))² − log(ℓ(T)/T)-type term. So exp(−ph(T)) = σ\*(εℓ(T))/T, up to the unit
  normalisation. The "Gaussian" of a single σ\* is ph itself, tautologically.
- `CurveAt` (IKT/DefsRep.lean:17) requires:
  - integrality of g₂, g₃, θ, and ‖ε‖ = 1;
  - **NormRel**: ph([α]T) ≃ α·σ(α)·ph(T) for units α ∈ ℤ_{p²} (`GaussSumParity/StatementC.lean:27`);
  - be ≃ cob(F, ph), where cob(F, φ)(a, b) = φ(a +_F b) − φ(a) − φ(b). `coboundary_exact` (`ICL/ExistsWittSeriesInverseFormalGroupIso.lean:111`,
    statement `IKT/DefsBeCob.lean:25`) is an **exact identity**: beLT *is* cob(F, psiLT) after the change to LT
    coordinates. It is bookkeeping, not a classification.
- The per-letter law `factors` / `joint_integrality` (`UGM/OrthogonalGaussModels/OrthogonalShapeOneLetter.lean:21-34`):
  for every prime-to-p torsion s (N·s ∈ Λ, p ∤ N) and the 2-torsion shift ω₀/2, thetaOne(s) = exp(−ph)·V with V
  integral. *I infer:* this is the classical integrality of the Kronecker theta function σ\*(z+t)e^{…}/σ\*(z)·T at
  prime-to-p torsion t on a good supersingular model (torsion off the formal group). **Body not read.**

**Why a two-variable "be(x, y) = x^p·y/p" appears at all.** It is the polarisation be = cob(ph). By the cube theorem
(`first_level_on_curve`, used in `CalcC_proof`, `UGM/OrthogonalGaussModels/OfClosedInt.lean:108-170`) be is
biadditive modulo ≃. By NormRel it is hermitian: be([α]x, y) ≃ be(x, [σα]y) (`AdjAt`). NormRel is extended from units
to all integral α (`PhNormAt`) using "every element of ℤ_{p²} is a sum of two units" (`BrC.two_units`, `normAdjAll`).

**RestBeta is the classification.** It is proved by `betaIsG` (UTS/FinalS.lean:61) from:
- `LemmaOne` (UTS/IsLawOfLog.lean:73): if cob(F, f) is integral then f = α·g0 + β·ℓ + (integral), with
  g0 = Σ X^{p·p^{2j}}/p^{j+1}. These are the quasi-logarithms: H¹_dR of the height-2 Honda group is spanned by ℓ and g0.
  This is Katz/Honda Dieudonné theory.
- `LemmaTwo`, `StepI`–`StepIV`, all proved.

The result is that a biadditive hermitian be is ≃ Gser(c, σc) = c·Aser − σc·Aser′, with
Aser = Σ_{i≤j} X^{p^{2i}}Y^{p^{2j+1}}/p^{i+j+1} (UTS/OddLogRelation.lean:20-29), c ∈ W(F_{p²}) and σc = −c (because be
is symmetric).

**Comparison with the literature.**
- Bannai–Kobayashi-type bounds concern σ itself.
- The Lean's structural statement is that **the polarisation of log σ\* is, mod integral exponentials, the unique
  hermitian Dieudonné pairing**. I find this believable and standard in spirit: biextensions of a height-2 LT group by
  Ĝ_m, and H¹_dR rank 2.
- In one variable the self-term be(x, x)/2 ≈ c·x^{p+1}/p survives. It gives only the a/(p²−1)-type gain, consistent
  with NUMTEST/NUMTEST3 (σ alone, and anisotropic primes).

### (b) From one variable to the full kernel

**`IntInert` (the non-Gaussian integrality, all inert p).** The reduction is `integral_inert_of_weakApprox`. I re-read
the statements, IKT/DefsInt.lean:95-175 and IKT/DefsMM.lean:30-80. It runs in five steps:
1. **One copy (N = N′ = 1, ℂ^{Tau}).**
   - `IsomStd`/`IsomONB` (IKT/OneCopyTh1S.lean:27-75) give a 4-fold Lagrange isometry g₁ of prime-to-p index, with
     tens4(θ_one) = e·kernel4, ‖e‖ ≤ 1, and the frame γ unitary over ℤ_{p²}.
   - kernel4 is a product of letters in unitary coordinates. By per-letter `factors` plus unitary invariance of Σph,
     exp(Σph)·θ_one^{⊗4} is integral.
   - *I infer* (body of `kappa_integral_of_calculation` not read) that one copy follows by the **fourth-power trick**.
     Put G = exp(Σph)·θ_one. Then G^{⊗4} = e·(integral), and the coefficient of z₁^n z₂^n z₃^n z₄^n is G_n⁴. So
     4v(G_n) ≥ 0, and G is integral. No condition on θ_one(0) is needed.
2. **`FourProd` (1×1 → 2×2).** This is a local orthonormal change with det A a unit (DefsMM:62).
3. **`TensFact` (2×2 → even N×N′).** thZero is a tensor power by definition, and products of integral series are
   integral (DefsInt:122).
4. **`StdStep` (general admitted M, equal to std at p, → std).** The statement (DefsInt:101) is that every
   prime-to-p translate U_t(eNat_{M,M′}) is Σ_k c_k·U_{s_k}(thZero), with c_k algebraic and **p-integral** and s_k
   prime-to-p torsion of the *standard* lattice.
   - So the brief's worry is answered at the level of the statement. Translates by prime-to-p torsion keep the class,
     with the **same** hh, because the class is defined by Σ_i ph(X_i). That sum does not depend on the translate.
   - Each translate is integral by the per-letter law, and integral linear combinations stay integral.
   - The 1/[index] and 1/√index factors are units because the index is prime to p (`IsomStd` ¬p ∣ relIdx; HIGHERRANK).
   - Body (`pairs_standard_at_p`, ICL/IntStd.lean:302) not read.
5. **`WeakApprox` + `LocInv`.** A general L reaches std at p (Jacobowitz uniqueness plus weak approximation; HIGHERRANK
   §1.4).

**`FrameHyp`: where "served/split" is used.** `hypCoordLt_of` (K1LT:84-115) builds f, f′ explicitly (fK, fK′) from:
- the orthonormal basis b;
- the frames;
- `LamPosG` (IKT/FrameInt.lean:44): λ∘(CM-type coordinate at position (v, s)) = σ^s-twisted local embedding ρ_v of x
  for s even, and of **conj(x)** for s odd;
- `FrobTw` (FrameInt:47, proved `frobTw_of`, ICL/RepFrob.lean:218): σ(twK v s x) = twK v (s+1) x;
- `hev`: n′_v even.

From these it proves:
- **σ²(f) = f**: the coefficients lie in ℚ_{p²}. This uses n′ even.
- **isotropy** Σ_i σ(f_{ei})f_{e′i} = 0 and Σ_i σ(f′)f′ = 0, plus duality Σ σ(f)f′ = δ. These come from
  orthonormality of b (`LamTraceLt`) and the position structure.

*My reading of why this needs a served place.* For E/ℚ abelian and p inert in K, Frob_p = c·g with g ∈ Gal(E/K), and
n′ = ord(g).
- If ord g is even, c ∉ D_p. Then E ⊗ K_p ⊇ E_w × E_{w̄} with w ≠ w̄. The hermitian form tr(x·c(x)) pairs E_w with
  E_{w̄}, and the CM-type coordinates at even positions (place w) and odd positions (= c∘…, place w̄) are the two
  Lagrangians. That is exactly IsHypPair with x = even and y = odd.
- If ord g is odd, c ∈ D_p and all CM-type coordinates at p restrict to one K_p-embedding of a c-stable E_w. Then there
  is no splitting of the Tau-coordinates into a Lagrangian pair, and the self-Gaussians survive. This is NUMTEST3's
  1/(p²−1).
- Such primes are excluded by construction: the place system only contains served places (`setting.even`, used at
  K1LT:203). `IntInert` itself holds at all inert p. Whether the *count* (ASK) excludes non-served inert primes was not
  checked here (SUMMARY §9 says ASK carries (1 − χ_Φ)).

`LamPos` is a hypothesis of `first_kernel_small_of_frame` and is supplied by `lamPos_of_posEmb`
(`Development/AbelianVarietyTheory/Proofs/SatakeParameters/LamPosOfPosEmb.lean:39`), which I did not read.

**`HypShape`: why the self-terms cancel.** This is `HypShape_of` (`UGM/OrthogonalGaussModels/KappaIntegralOfCalculation.lean:42-120`)
→ `hyperbolicSum` (`TorsionIntegrality/SecondCoefficientNorms/PhNormFromDatum.lean:14`).

Write X_i = [f_{·i}]x +_F [f′_{·i}]y in the formal module. Then:
- Σ_i ph(X_i) ≃ Σ_e (Σ_i N f_{ei})ph(x_e) + (Σ_i N f′_{ei})ph(y_e) + Σ_{e,e′} be(x_e, (Σ_i σ(f_{ei})f′_{e′i})y_{e′})
  + (the x–x and y–y cross terms).
- Isotropy kills the first two groups and the x–x/y–y cross terms. Duality leaves Σ_e be(x_e, y_e).

This is NUMTEST3's A·A^σ + C·C^σ = 0, in general form. I checked the logic: biadditivity, hermitian transfer, NormRel
on all integral α, and closure of ≃ under integral substitution and finite sums (`SimeqRules`). It is correct.

**`RestGc` (read in full, MV/TwoSumsCondition.lean:174-260; MV/CommonEigenvectorThird.lean).** Substitute
t = ϖ·μ(coordZ₁(Z)), where μ = lamF⁻¹ and lamF(T) = ℓ(ϖT)/ϖ, so that ℓ(t) = ϖ·coordZ₁(Z).
- (i) `exists_atPi_G1…`: Gser(ϖs_x, ϖs_y) = ϖ^{p+1}·R(s) + (ϖ^{p+1}/p)(c·s_x·s_y^p − σc·s_y·s_x^p), with R
  integral. The non-leading monomials have v ≥ 1/(p−1) + p − 2 (`ValTable`, UTS/OddLogRelation.lean).
- (ii) exp(−ϖ^{p+1}R) is integral, because ϖ^{(p+1)k}/k! is integral (`PiFactorial`).
- (iii) `TwoSumsCondition`: Σ_e(c·s_x·s_y^p − σc·s_y·s_x^p) = hhS(u) + p·Y. This uses:
  - μ ≡ altF = Σ(−1)^l X^{p^{2l}} mod p (`sx_mu_alt`);
  - (aZ)^p ≡ σ(a)Z^p mod p (`frobenius_congruence_witt`), which gives s_x ≡ Σ_{t even} σ^t(ω\*_r)S_t;
  - the duality (`sx_dual`) computed above.

This is pure algebra, uniform in n′, r0, r1.

### (c) `HhDecomp` (SE:124; proved FLN/EDecomp.lean:498), hand expansion

Put Z_{t,a} = low_{t,a} + [t ∈ TT]·ξ_{t,a}·top_t (`zSub`, SE:88). Mod p:
- S_s^p ≡ Σ_l (−1)^l Z_{s−2l}^{p^{2l+1}};
- Z^{p^k} ≡ low^{p^k} + ξ^{p^k}top^{p^k} for k ≥ 1.

Expanding u_s·S_s^p·S_{s+1} gives:
- **top·top**: u_s(−1)^{l+l′}·ξ_{s−2l}^{p^{2l+1}}·ξ_{s+1−2l′}^{p^{2l′}}·top_{s−2l}^{p^{2l+1}}·top_{s+1−2l′}^{p^{2l′}}.
  This is exactly `aAof`/`dAof`, with pairFirst = s − 2l and pairSecond = s + 1 − 2l′.
- **top·low, l′ = 0**: u_{t+2l}(−1)^l·top_t^{p^{2l+1}}·Σ_a ξ_{t,a}^{p^{2l+1}}·low_{t+2l+1,a}. This is exactly
  `aBof`/`dBof`/`bBof`.
- **top·low^{p^{2l′}}, l′ ≥ 1**, and every term containing low^{p^{2l+1}}: low degree ≥ p, so they go into Z.
- **binomial and cross terms**: in p·(integral), so they go into pY.
- **truncation**: D < p^{2E} bounds l, l′ < E.

**n′ = 4** (positions mod 4, S_s = Z_s − Z_{s−2}^{p²} + Z_s^{p⁴} − …). For a top at t = 0, the β-couplings are:
- top₀^p·low₁, with u₀;
- top₀^{p³}·low₃, with −u₂;
- top₀^{p⁵}·low₁, with +u₀;
- and so on: e odd lands at position e mod 4.

This agrees with the statement and with HIGHERRANK. No mismatch.

### (d) Uniformity

- **RestGc.** u_s = c, independent of rank. V is integral over W[ϖ] with no constant. The proof is entrywise, and the
  sums over e are finite and integral.
- **IntInert.** Every statement is exact integrality, with no p^{−C}. The constants are: ‖e‖ ≤ 1 (one copy only,
  raised to tensor powers is still ≤ 1), p-integral c_k (StdStep), and unit-determinant frames.
- **`ScalGLt`** (read: `Development/.../SatakeParameters/ThetaSeriesScalarBoundedOfPosPair.lean:22-87`). It proves
  ‖p^{expG}·scalG‖ = **1 exactly**:
  - chiFac and the χ(detId) values are p-units (`chi_alg_unit_inert`);
  - ‖λμ̃(dt_j)‖ = p^{…} with ord = −len (`norm_lambdaCharacter_normOne_idele_eq_p_pow`,
    `lattice_det_mem_U1_and_ordA_eq_neg_len`);
  - so the p-power cancels expG term by term (Σ_v vm·(len_{j+1} − len_j) − (…) = 0, by `ring`).

  No growth with rank or orbit length.
- I found no hidden constant, denominator or rank-dependent normalisation.

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `joint_integrality` / `factors` | UGM/OrthogonalGaussModels/OrthogonalShapeOneLetter.lean:21 | for prime-to-p torsion s: thetaOne(s) = exp(−ph)·(integral) in LT coordinate | **core**, body unread (the one-variable arithmetic: Kronecker theta integrality, CM2/CM4) |
| 2 | `kappa_integral_of_calculation`, `IsomStd`/`IsomONB` | KappaIntegralOfCalculation.lean; IKT/OneCopyTh1S.lean:27-75 | one-copy integrality from the 4-fold Lagrange isometry | **core**; I infer the fourth-power trick; body unread |
| 3 | `pairs_standard_at_p` (StdStep), `tensor_matrix_units_fact`, `four_products_from_one` | ICL/IntStd.lean:302; ICL/IntTens.lean:640; ICL/MMFour.lean:206 | coset averaging; tensor; 1→2 | core-ish, statements read |
| 4 | `lamPos_of_posEmb` (LamPos) | SatakeParameters/LamPosOfPosEmb.lean:39 | odd positions = conjugated embeddings at a served place | **core** (this is where "split at p" enters); unread |
| 5 | `hypCoordLt_of` → `iso_fK`, `dual_fK`, `sigma2_fK` | K1LT:84 | constructs the hyperbolic pair | core, top level read |
| 6 | `hyperbolicSum`, `normAdjAll`, `first_level_on_curve` | PhNormFromDatum.lean:14; OfClosedInt.lean:108 | Σph ≃ Σbe under hyperbolic change; NormRel to all integral α; cube | core, formal; top level read, correct |
| 7 | `betaIsG` (LemmaOne, LemmaTwo, StepI–IV) | UTS/FinalS.lean:41-61 | be ≃ Gser(c, σc) | standard (Dieudonné/Honda quasi-logarithms); statements read |
| 8 | `restGc` | MV/TwoSumsCondition.lean:174 | Gaussian → exp(−(π/p)hh)·V | formal; read, correct |
| 9 | `decomposition_of_hh` | SE:124 | mod-p decomposition | formal; statement checked by hand (n′ = 4) |
| 10 | `scal_of_pos_pair` | ThetaSeriesScalarBoundedOfPosPair.lean:22 | ‖p^{expG}scalG‖ = 1 | read, correct |
| 11 | `nrDense` (NormRel) | RepDict.lean (KERNELLAW) | distribution relation, giving ph([α]T) ≃ Nα·ph | core, unread here |

## 4. Oddities

1. **u is effectively the constant c, and c could be 0.** RestBeta only says ∃c. If c = 0 the class is Gaussian-free,
   which is stronger, not weaker. NUMTEST3's anisotropic control shows the real c ≠ 0, but nothing depends on this.
2. **σc = −c** (`stepIII`, named `c_add_sigma_c_eq_zero`). It follows from the symmetry of be = cob(ph), and is
   consistent with that symmetry. It makes u_s constant in s.
3. **`OneLetterGaussInt`** (UGM/StatementA.lean:77-82) asserts ‖s₂‖ ≤ 1 at inert primes. KERNELLAW noted that the live
   `CurveAt` does not require this. The two are compatible. It looks like an off-path statement, but I did not trace
   whether it is on the path.
4. The class statement for one σ\* is **not** in the Lean, and is not needed. Only isotropic combinations are
   Gaussian-reduced. The brief's expectation "σ\*(z) = exp(Q(z)/p)·integral with Q = z·z^σ" holds only in the form
   "Σ_i ph(X_i) over an orthonormal basis ≃ Σ_e be(x_e, y_e) over a hyperbolic basis".
5. Steps I inferred but did not read: the fourth-power trick; that `LamPos` is the served-place structure; Kronecker
   theta integrality. Nothing false-looking seen.

## 5. Coverage

Read:
- DER:1-90;
- UTS/OddLogRelation.lean:1-70; UTS/CyclicPowerClassOfExpEquiv.lean:1-91; UTS/IsLawOfLog.lean:60-115;
  UTS/FinalS.lean:40-62;
- FGS:120-235; MV/SubstitutionOfVariables.lean:1-40, 190-210; MV/IntegralExpRename.lean:55-70;
  MV/TwoSumsCondition.lean:1-60, 160-260; MV/CommonEigenvectorThird.lean (all);
  MV/BiadditiveSecondVariable.lean:100-160;
- IKT/DefsRep.lean (all); ICL/RepAsm.lean:1-100; ICL/ConstantCoeffFormalSum.lean:380-452 plus the lemma list;
  IKT/FirstKernelGeneratorOfOrthogonal.lean:51-68;
- UGM/IsHypPair.lean; UGM/UniformGaussModelCondition.lean; UGM/OrthShapeOne.lean:1-60;
  UGM/OneLetterGaussSharpTranslateHolds.lean:1-60; OrthogonalGaussModels/KappaIntegralOfCalculation.lean:30-120;
  OfClosedInt.lean:100-170; OrthogonalShapeOneLetter.lean:1-90;
- GaussSumParity/StatementC.lean:1-60, StatementE.lean:1-50; IsUnitaryK.lean:115-135;
- K1LT:60-252; ICL/FirstKernelSmallOfFrameTwist.lean:1-90; FdOfCharts.lean:20-60; IKT/FrameInt.lean:20-70;
  IKT/DefsRepLt.lean:95-200; IKT/ScalG.lean:1-40; IKT/DefsInt.lean:95-175; IKT/DefsMM.lean:30-80;
  IKT/StatementInt.lean; IKT/OneCopyTh1S.lean:1-80; IKT/DefsBeCob.lean:25-40;
  ICL/ExistsWittSeriesInverseFormalGroupIso.lean:100-125;
- SE:80-135; ThetaSeriesScalarBoundedOfPosPair(Statement).lean (all); LamPosGOfLamPos.lean.

Not opened:
- the bodies of `joint_integrality`, `kappa_integral_of_calculation`, `pairs_standard_at_p`, `tensFact`, `fourProd`,
  `lamPos_of_posEmb`, `iso_fK`/`dual_fK`, `betaIsG`'s steps, `hyperbolicSum`, `decomposition_of_hh`, `nrDense`,
  `dict_core`;
- the link adm2 + RestGc → InClass (`baseChange_preserves_unitary_of`); I know only its statement shape, from FGS:220.
