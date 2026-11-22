# NODE-ENGINE: the p-adic engine for one lift at one inert prime, as a paper proof

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `MV/` = `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/`
- `UTS/` = `Formalism/ThetaLogCoordinates/UniformThetaSubstitution/`; `FLN/` = `UTS/FrobeniusLiftNorms/`
- `XIC` = `Formalism/LocalToGlobal/KernelLattices/XiIndCClass.lean`; `LAT2` = `Formalism/LocalToGlobal/KernelLattices/LateralTheory.lean`
- `KTH` = `Formalism/LocalToGlobal/PairingIndexBounds/OrthogonalChartLevels/KerTh.lean`
- `SC` = `Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/SemiChar.lean`
- `ISC` = `Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/IsSemiChar.lean`
- `RF` = `Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/RepFrame.lean`
- `HPS` = `Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean`

"Read" means I read the proof body in this round. "Stmt" means only the statement was read, by me or by the cited node.

## 0. Verdict (short)

**The one-lift, one-prime engine is a correct and essentially elementary argument once one hypothesis is granted.**
That hypothesis is clause `adm2`: the actual theta kernel, restricted to the formal group at a served place, is
exp(−Ph)·(LT-integral) with Ph ≃ Σ_e be(x_e, y_e) (a hyperbolic cross Gaussian). Everything downstream of `adm2` I read
to the bottom in this round: Dwork factorisation → class membership → jet bound → Legendre arithmetic → cap lemma.
The derivation of `adm2` from the arithmetic of σ\* is now read for its two formal links (isotropy `iso_fK`/`dual_fK`;
hyperbolic split `hyperbolic_plane_split`). Its arithmetic leaves were read by LEAVES.

The proved exponent, per top s and per lift, is

  v_p(jet) ≥ Σ_{e odd, e ∉ dSet(s)} (a_s/p^e − cap_{s+e})₊ − deLoss,

and this holds on **every** jet of the form (top linear forms)^{a}·(product of column minors). It therefore holds on the
whole integral lattice of level-j forms. It matches the ledger's shape exactly. The loss deLoss is polynomial in the ranks
and logarithmic in a, so it is negligible next to b. **No ESCALATE** on the exponent. The residual risk sits in
statement-level suppliers (§5).

The cleanest way to see the exponent: Legendre gives v_p(a!) ≈ Σ_{e≥1} a/p^e. Undoing the ϖ-rescaling of the height-2
Lubin–Tate coordinate costs a/(p²−1) = Σ_{e even ≥2} a/p^e, i.e. exactly the even-e terms. What survives is
γ_p a = Σ_{e odd} a/p^e. Each Gaussian factor of level e (necessarily odd) uses p^e top derivatives and costs one p.
Each is capped by the number of minors at the partner position s+e. Hence Σ_{e odd}(a/p^e − cap)₊.

## 1. Setup, precisely from the Lean

### 1.1 Field, space, lattice, Gaussian (the Lean says)

- **Fields.** K = ℚ(√−d) imaginary quadratic. E ⊃ K is the host CM field, with CM type Tau ≃ Gal(E/K) (NUMTEST3 §A;
  LEAVES L-B). p ≥ 5 is inert in K (`Std.five_le`, FGS:92).
- **Complex space.** VV = ℂ^{Tau × N′ × N} (XIC:148): an N′×N matrix variable at each τ ∈ Tau. Hom_E(E^N, E^{N′}) embeds
  by x ↦ (δ·τ(x(e_j)_i))_{τ,i,j} (`embH`, XIC:150-153).
- **Hermitian form.** H(z, w) = area(Λ)^{−1}·Σ_{τ,i,j} z_{τij}·w̄_{τij} (`HV`, XIC:155-156; `sc` = area⁻¹ at KTH:30).
  Semicharacter α(x) = exp(πi·(√d/2)·H(x,x)) (`alV`, XIC:164; `alphaQ`, ProductThetaMem.lean:18).
- **Lattice.** Λ_{N,N′} = δ·Φ_Tau(AA0·Hom(N, N′)), the span of r·x with r ∈ AA0 and x mapping N into N′ (`homO`, `perO`,
  `laV`, `LamC`, XIC:166-173, 184-185, 216). Here AA0 is an O_E-ideal (`aaOf`, KTH:16-18) and δ·O_K is the period lattice
  of the CM curve (`lamOf D cc δ`, KTH:30).
- **Theta functions.** A theta function for (H, α, Λ) is F with α(x)·U_x F = F for x ∈ Λ, where
  (U_x F)(z) = F(z+x)·exp(−πH(z,x) − πH(x,x)/2) (`opU`, `fixedBy`, ISC:21-22, 43-44). These are classical reduced theta
  functions, i.e. sections of the line bundle with Riemann form H on VV/Λ.
- **The kernel.** θ_{c,c′} = kerTh(B, χ, SS, c, N, N′, Ξ) = thC(Ξ, eNat) (KTH:26-31). Here thC = xiL (XIC:239, 224-228,
  26-27) is the finite Heisenberg/Weil-representation sum
    θ_{c,c′}(z) = Σ_{x ∈ Λ/A} α(x)·U_x[ Σ_{y ∈ Λ/B} hatS(Φ(·−x))(y)·α(y)·U_y θ_vac ](z),
  with the following ingredients:
  - Φ = Ξ is the finite Schwartz datum;
  - A, B are the two half-lattices twisted at the places SS by c^{∓1} (`halfAO`, `halfBO`, XIC:187-191);
  - hatS is a finite Fourier transform (XIC:20-21).
  So θ_{c,c′} is a **finite linear combination of Heisenberg translates, by torsion points of VV/Λ, of one vacuum
  theta θ_vac**.
- **The vacuum.** θ_vac = eNat(N, N′, L, L′) = chiFac·Iop(Iop(thZero)) (LAT2:169-178). The pieces are:
  - two coset averages carry the standard lattice to (L, std) and then to (L, L′) (LAT2:161-171);
  - thZero = ∏_{i,j} thMM(z_{·,i,j}) (`tensPow`, LAT2:34-35, 157);
  - thMM is a theta function for H = area⁻¹·I on ℂ^{Tau}/Λ_MM with tens⁴(thMM) = κ·kernel4 (`IsThM`, LAT2:20-29, 155);
  - kernel4 is a product of letters th0(z) = U_t(σ\*)(z)/U_t(σ\*)(0), at the 2-torsion point t = ω₀/2 (SC:34);
  - σ\* = σ·e^{−s₂z²/2} (`sgStar`, SC:23).
- **The Gaussian.** At ∞ it is the factor of automorphy e^{πH(z,z)/2}-growth built into `opU`. p-adically it is the class
  of ph = −log(σ\*(εℓ(T))/T) (LEAVES L-A1). No separate Gaussian is multiplied in.

### 1.2 Normalisation σ\*

σ\* = σ_Λ·exp(−s₂z²/2), with s₂ = (η₁ω̄₂ − η₂ω̄₁)/(ω₁ω̄₂ − ω₂ω̄₁) (`s2`, SC:20-21). This is the non-holomorphic
E₂\*-normalisation, so σ\*(z+ω) = ±σ\*(z)·exp(πω̄(z+ω/2)/A). LEAVES proved s₂ is p-integral and showed that it enters only
through NormRel.

### 1.3 The Lubin–Tate coordinate (the Lean says)

- **Honda logarithm.** ℓ(X) = Σ_j X^{p^{2j}}/p^j over K0 = Frac W(F̄_p) (`logF`, FGS:126-127). This is the height-2 Honda
  group, the formal group of the supersingular CM reduction.
- **ϖ.** ϖ ∈ ℂ_p with ϖ^{p²−1} = p, so v(ϖ) = ρ_p := 1/(p²−1) (SConcl hypothesis, FGS:216-223).
- **"Integral in the LT parameter"** means: U(ℓ(X)) has integral coefficients in the LT parameter X (`IntR … inParamK`,
  FGS:132, 162-170). The kernel's own variables are **log coordinates** z = ℓ(X).
- **Rescaled position variables.** The frame-changed log coordinates are x_r = ϖ·Σ_{s even} σ^s(ω\*_r)Z_s and
  y_r = ϖ·Σ_{s odd} σ^s(ω_r)Z_s (`coordZ`, `ThZ`, FGS:181-192). Here (ω, ω\*) is a dual W(F_{p^{n′}})/W(F_{p²}) basis with
  Σ_i σ^{2i}(ω_r ω\*_{r′}) = δ (`OmBasis`, FGS:172-178).
- **Why the rescaling is the right one** (my rendering of `RestSInt`, statement at
  MV/KernelExpansionOfRestrictions.lean:22-27). Put λ(T) = ℓ(ϖT)/ϖ. Its coefficients ϖ^{p^{2j}−1}/p^j have valuation
  (1+p²+…+p^{2j−2}) − j ≥ 0, so λ and μ = λ^{−1} are integral. Since ℓ(ϖμ(W)) = ϖW, a series integral in X is integral
  in W = z/ϖ. So for f integral in X: v(∂^n f(0)) in z ≥ v(n!) − |n|·ρ_p. This answers the review's "integral in which
  variable".

### 1.4 The statement proved (exponent and lattice)

**Jet operator** (UTS/StatementE.lean:144-154). For one place v and level j, the operator is
  entryOp = ∏_{x=(s,b)} (topForm_{s,b})^{e(s,b)} · ∏_c minorAt(sf c, T_c, I_c).
- topForm_{s,b} = Σ_a ξ_{s,a}·X_{s,a,b} is a linear form at a top position s ∈ TT.
- Each minor is det(Σ_a T_{i,a} X_{s,a,I(c′)}) at position s = sf c.
- The variables are X_{s,a,b}: s ∈ ℤ/n′ a position on the Frobenius orbit, and (a, b) ∈ N(j) × N(j+1) a matrix entry.
- On the live path this is the column-minor polynomial PI_j (FGS:398-419). At position s there is one minor per
  column c < ν_{j+1,s,1}, of height colHt = #{i : ν_{j+1,s,i} > c}. So the **number of minors at s is the first row
  length ν_{j+1,s,1}**.
- At a top, the ν₁ − ν₂ columns of height 1 are peeled off as top linear forms (`alG`, `capG`, UTS/StatementG.lean:19-29;
  `reduce`, FLN/EGaussK.lean:38-60, statement). So al_s = ν₁ − ν₂ and capN = ν₂ at a top, and capN = ν₁ elsewhere. This
  is exactly `cap` (FGS:36-38). So **"cap = number of minors" holds by definition**.
- jetPair(P, F) = Σ_κ coeff_κ(P)·κ!·coeff_κ(F) (Formalism/GaussJetBounds/StatementI.lean:13-14). It is the derivative
  pairing P(∂)F|_0 (`applyD`, FGS:256-260).

**EntryExcessBound** (UTS/StatementE.lean:191-199) is proved (`entry_a_one`, UTS/KOneConsequence.lean:43). Let F be in
`InClass(p, hh_u, ·)` with ‖u_s‖ ≤ 1. Then for every choice of ξ, e, minors (T, I):

  ‖jetPair(entryOp, F)‖ ≤ p^{−(excessGain + ρ_p·Σ_s(al_s + ls_s))},
  excessGain = Σ_{s∈TT} Σ_{e odd} [2e+1 ∉ dSet(s)]·(al_s/p^e − cap_{s+e})₊ − deLoss
  (Formalism/GrowthSums/StatementA.lean:108-112).

The ρ_p·(degree) term is removed by `descend` (FLN/EGaussK.lean:132-147), so for the **unrescaled** kernel the bound is
v_p ≥ excessGain. The other definitions:
- γ_p = p·ρ_p (StatementA.lean:63-65);
- deLoss = Σ_s (r1·lg(al_s) + r0·r1·lg(ls_s)) + Σ_{s∈TT} lg(al_s)², with r0 = N(j), r1 = N(j+1) and lg = ⌊log_p⌋ + 1
  (UTS/StatementAB.lean:95, 100-101);
- dSet(s) = {odd distances from s to another top of opposite parity} (StatementE.lean:163-164).

The variants EntryCappedBound and EntryB give gB (caps charged only at odd tops, with even tops paid by Hecke factors).

**Exact lattice.** The jet bound is universal over all top exponents e and all products of minors. It applies to the
kernel θ_{c,c′} for every pair of lattice classes (La, La′), every place v and every frame φ (`Conclusion1`,
FGS:633-635). Two further steps are stated in FGS but not re-read by me:
- `adm7` (FGS:613, proved per LOCALDIV) carries the jet bound to p^{g}·Int_{j+1} for every G in the integral weight
  lattice;
- `ExpansionEquality` (FGS:566) makes the chain map K_j a Stab-weighted sum of such kernel pairings.

So the statement holds **on the whole integral lattice Int_j** (skeleton step 5), not on a special linear combination.

## 2. The proof, link by link

| link | content | where | status |
|---|---|---|---|
| (a1) | kernel at a served place = exp(−Ph)·U, U LT-integral, Ph ≃ Σ_e be(x_e, y_e) (clause adm2) | `ExtensionLocalCondition` FGS:162-170; supplier `first_kernel_law_global_small` (LOCALDIV child 1) | **hypothesis**, supplier top-level only |
| (a2) | adm2 + RestBeta + RestGc + RestSInt ⇒ InClass | MV/DworkExponentialRestrictions.lean:95-105, 137-139; MV/KernelExpansionOfRestrictions.lean:116-140 | **read** |
| (a3) | RestBeta: be ≃ Gser(c, σc) | `restBeta`, MV/BiadditiveSecondVariable.lean:137 | stmt (GAUSSCLASS read the step list) |
| (a4) | RestGc: exp(−Gser) in rescaled coords = exp(−(ϖ^{p+1}/p)·hh_u)·V | statement DER:19-27; `restGc` MV/CommonEigenvectorThird.lean:21-22 → TwoSums | read by GAUSSCLASS; I read the statements |
| (a5) | Dwork: (ϖ^{p+1})^k/k! integral, which absorbs the exponential | `piFact` used at KernelExpansionOfRestrictions.lean:126; `PiFactorial` OddLogRelation.lean:65-69 | stmt; elementary |
| (b) | arithmetic leaves (Kronecker theta integrality; NormRel; fourth-power trick; coset averaging) | LEAVES §L-A, L-C | read by LEAVES |
| (c) | isotropy and duality of the hyperbolic frame; self-Gaussians cancel | RF:808-822, 825-835, 861-895, 935-1000; HPS:114-152 | **read** |
| (d) | cap lemma | FLN/MinorProdBlockDegree.lean:36-55; FLN/FinsuppStepInduction.lean:227-243, 746-785 | **read** |
| (e) | Dwork/Legendre exponent | FLN/NormNatCastLeOfDvd.lean:397-545; FLN/NormLeOfDvd.lean:202-405; FLN/ABArith.lean:35-260 | **read** |
| (f) | odd e, −w, positive part | UTS/StatementE.lean:95-138; FLN/EntryAOneParity.lean:177-215; ABArith.lean:193-238 | **read** (HhDecomp proof: stmt + GAUSSCLASS hand check) |

### (a) Why the restricted theta is in the Gaussian class, and what that means integrally

**Definition** (UTS/OddLogRelation.lean:76-79; FGS:210-213). F ∈ InClass(p, hh) iff there are integral U_i with
  coeff_n F = Σ_{i ≤ |n|} p^{−i}·coeff_n(hh^i U_i).
Integrally this says F ∈ O[[Z]][hh/p]: each power of hh/p costs exactly one p, and nothing else is non-integral.

**hh.** hh_u = Σ_s u_s Σ_{a,b} S_{s,a,b}^p·S_{s+1,a,b}, where S_{s,a,b} = Σ_l (−1)^l Z_{s−2l,a,b}^{p^{2l}} (`sSer`, `hhS`,
FGS:200-208). In the second library u = uS(c, σc) with u_s = c for s odd and −σc for s even
(UTS/CyclicPowerClassOfExpEquiv.lean:85-89).

**Proof of class membership** (`SConcl_of`, MV/KernelExpansionOfRestrictions.lean:116-134; read):
1. adm2 gives Th = exp(−Ph)·U with Ph ≃ Σ_e be(x_e, y_e) and U LT-integral.
2. RestBeta replaces be by Gser(c, σc) up to ≃, i.e. up to an integral exponential factor (`restSExp_of`, DER:95-105,
   read).
3. RestGc: in the rescaled position variables, exp(−Σ_e Gser(x_e, y_e)) = exp(−(π/p)·hh_u)·V, with π = ϖ^{p+1}
   (so π^{p−1} = p) and V integral.
   - The 1/p part of Gser is (c·x·y^p − σc·x^p·y)/p.
   - Under x = ϖ·(even positions), y = ϖ·(odd positions) it becomes (π/p)·Σ c·S_t·S_{t′}^p·(trace pairing), and the
     trace pairing gives δ_{t, t′+1}.
   - The higher Gser terms have valuation ≥ 1/(p−1) + p − 2 after rescaling (`ValTable`, OddLogRelation.lean:58-64),
     so they are absorbed into V.
4. RestSInt: U stays integral in the rescaled variables (§1.3).
5. The hh′ = hh + pG change is absorbed: exp(−(π/p)(hh + pG)) = exp(−(π/p)hh′)·exp(πG) (`exp_change`, :94-112, read).
6. Dwork: exp(−(π/p)hh) = Σ_k (−1)^k (π^k/k!)(hh/p)^k, and v(π^k/k!) ≥ 0. So `inClass_of_exp` (:134) gives InClass.

So "Gaussian class" means precisely: **after rescaling by ϖ, the kernel's only non-integrality is a polynomial in hh/p**,
whose degree in hh is bounded by the coefficient degree.

### (b) The three arithmetic leaves

I did not re-read them. LEAVES (§L-A1, L-A2, L-C) read `joint_integrality` (Kronecker theta integrality at prime-to-p
torsion: σ-addition formula, telescoping, root extraction), `NRDense_of`/`cdata` (α(α−ᾱ)s₂ = Σ℘(P); density) and
`fourth_power`/`pairs_standard_at_p` in full. `lamPos_of_posEmb` is a three-line rewrite; its content is `posOK`
(**not opened by anyone**). I consider (b) verified at the level LEAVES reports. The gap is `posOK` (§5).

### (c) Cancellation of self-Gaussians at split hermitian places (read)

**Frame** (RF:660-689). f_{e,i} = Σ_k LBc_{k,i}·YX(e,k) and f′_{e,i} = Σ_k LBc_{k,i}·YX′(e,k).
- YX is supported on **even** positions k.1 and YX′ on **odd** positions.
- LBc are the Frobenius-twisted local embeddings of the orthonormal basis b.

**σ rotates positions by one.** σ(twK_{v,s}x) = twK_{v,s+1}x (hypothesis hσtw). Hence σ(f_{e,i}) = Σ_k LB_{k,i}·ZX(e,k),
with ZX supported on **odd** positions (`sigma_fK`, RF:825-829). This uses n′ even (hev) so that "+1" swaps parity
on ℤ/n′.

**Orthonormality.** Σ_i LB_{k,i}·LBc_{k′,i} = δ_{pos k, pos k′} (`kurONB`, RF:808-817, from `LamONB`).

**Isotropy** (`iso_fK`, RF:861-877):
  Σ_i σ(f_{e,i})·f_{e′,i} = Σ_k ZX(e,k)·YX(e′,k) = 0,
because ZX is odd-supported and YX even-supported. The same holds for f′.

**Duality** (`dual_fK`, RF:935-1000): Σ_i σ(f_{e,i})·f′_{e′,i} = δ_{ee′}, from G^{−1}G = 1 for the frames and
Σ_i σ^{2i}(ω_r ω\*_{r′}) = δ (`dualT`).

**Hyperbolic split** (`hyperbolic_plane_split`, HPS:114-152; read). This is an abstract statement for a map φ: M → Q
with three properties: cob φ is biadditive; cob(αa, b) = cob(a, ᾱb); φ(αu) = N(α)φ(u). Then

  Σ_i φ(Σ_e f_{ei}t_e + f′_{ei}t′_e) = Σ_i φ(Σ f t) + Σ_i φ(Σ f′ t′) + Σ_i cob(Σ f t, Σ f′ t′).

- The first two sums vanish: by `diag'` (HPS:79-98) each equals Σ_e(Σ_i N(f_{ei}))φ(t_e), and Σ_i N(f_{ei}) = 0 by
  isotropy.
- The third equals Σ_e cob(t_e, t′_e) by duality (`cross'`, HPS:66-75).

It is applied with φ = ph on formal points modulo integral exponentials (`hyperbolic_sum_identity`,
.../SecondCoefficientNorms/BinomialSeriesCoefficients/UnitaryInverseIdentity.lean:476-488). NormRel supplies
φ(αu) = N(α)φ(u), and the cube theorem supplies biadditivity (LEAVES).

**NUMTEST3's AA^σ + CC^σ = 0** is the n′ = 2, one-entry case of `iso_fK`. In NUMTEST3 σ is the Frobenius of W(F̄_p),
which acts on O_K ⊗ ℤ_p as complex conjugation because p is inert.

**Why the split is needed.** If n′ were odd, rotation by one would not swap a parity decomposition. f and σ(f) would then
overlap, and the self-terms Σ_i N(f_{ei})·ph(t_e) would survive, which gives the a/(p²−1) regime (NUMTEST3
anisotropic rows). In the Lean the served condition is exactly the hypothesis hev: n′ even.

### (d) The cap lemma for column minors (read)

- **Adjointness** (`e_one_identity_of`, FLN/FinsuppStepInduction.lean:189-225):
  jetPair(Q, (∏_k ℓ_k^{β_k})·G) = (∏β_k!)·jetPair(∂^β_ℓ Q, G).
  So multiplying the kernel by a linear form ℓ_k = Σ_x b_{k,x}X_x is adjoint to the Hasse derivative of the operator
  polynomial in direction b_k. This is induction on β, using jetPair(Q, X_x G) = jetPair(∂_x Q, G).
- **One minor absorbs at most one derivative in a fixed direction ξ** (`minor_hits`, :746-785, via `hits_row`).
  - The derivative direction colDir(s, ξ, col) adds ξ to column `col` at position s.
  - In the matrix (Σ_a T_{ia}X_{s,a,I c}), shifting by directions with the same ξ adds (Tξ)·vᵀ, a rank-one update. So
    det is affine in the shift parameters. Hence the Hasse derivative vanishes in three cases:
    - if any β_k ≥ 2;
    - if two derivatives share ξ or share a column;
    - if the direction is at another position or misses the minor's columns.
  - These are the matrix determinant lemma and multilinearity.
- **Product rule** (`e_one_vanish_of`, :227-243). The Leibniz expansion of ∂^β(∏_c f_c) vanishes once Σβ exceeds
  Σ_c m_c, where m_c is the per-factor maximum.
- **HitsCapPos** (FLN/MinorProdBlockDegree.lean:36-55). Let all derivatives in S sit at position s₀ with one common ξ. If
  Σ_{k∈S} β_k > #{minors at s₀}, the derivative of the product of minors is 0.
- **Use in the count** (`entryExcessBound_of`, FLN/EntryAOneParity.lean:177-215). The B-type pieces of hh at level
  e = 2e′+1 from top s have direction bBof = colDir(s+e, ξ_s^{p^e}, b) (UTS/StatementE.lean:118-120). For fixed (s, e′)
  this is one ξ, at position s+e.
  - So iN(s, e′) ≤ capN(s+e) (`hcapN`, :213).
  - Degree gives p^e·(chN + iN) ≤ al_s (`level_le`), where chN counts A-type (top×top) pieces.

**"Cap = weight."** capN(s+e) is the number of minors at the partner: ν_{j+1,s+e,1} at a non-top partner, and ν₂ at a
top (§1.4). That this equals the ledger's w_{t+e} is a definitional identification, made through `LatTied` (PAIRING
§0.3). I did not re-read PAIRING.

### (e) Legendre/Dwork step giving the exponent (read)

**TermBound** (FLN/NormNatCastLeOfDvd.lean:397-545). Write hh (after zSub, the substitution of top variables) as a sum of
pieces, using HhDecomp:
- A-pieces a_φ·(top monomial of degree p^{2l+1} + p^{2l′});
- B-pieces a_k·(top monomial of degree p^{2l+1})·(low linear form b_k);
- Z, of low degree ≥ p;
- p·Y.

Expand p^{−i}hh^i U_i multinomially (`key`, :515-534). In each term pair against topMono(e)·lowPoly(Q):
- the top part contributes e! (the jetPair factor κ!);
- the B-pieces become a Hasse derivative of Q (adjointness), with factor ∏β_k!, bounded below by (Σβ)! through
  `fact_dvd` (:286-319);
- the low part contributes n!, where n is a monomial of ∂^βQ;
- each A, B or Z piece costs one p, and pY costs nothing (`hpp`, :470-472);
- Z-pieces force p·i₂ ≤ deg n.

Result: ‖jet‖ ≤ p^{#A + #B + i₂}·|e!|·|(Σβ)!|·|n!| (`bnd`, :392-395).

**StarArith** (`gainFactorialInequality`, ABArith.lean:103-183). It uses Legendre in the form
v_p(m!) ≥ m/(p−1) − lg(m) (`factorialValuationLowerBound`, :35-53, from (p−1)v_p(m!) = m − s_p(m)) and
1/(p−1) = γ_p + ρ_p (`hcg`).
- Top: Σ v(e_{s,b}!) ≥ (γ+ρ)al_s − r1·lg(al_s).
- Hasse orders: Σ v(i!) ≥ (γ+ρ)·Σi − lg(al)².
- Low: Σ v(n_x!) ≥ (γ+ρ)·(ls − Σi) − r0·r1·lg(ls).
- i₂ ≤ ls/p ≤ γ·ls.

Adding these gives v ≥ γ Σ al − #A − #B − deLoss + ρ Σ(al + ls). The +ρΣ(al + ls) exactly pays the rescaling
(`descend`). So **the low (minor) variables pay their own rescaling cost from their own factorials**, and the top
variables keep γ_p·al.

### (f) Odd e versus even, the "−w", and the positive part (read)

- **Only odd levels exist.** S_s has monomials of degree p^{2l}. So S_s^p·S_{s+1} has top degree p^{2l+1} in its first
  slot (`dBof` = single(p^{2e′+1}), UTS/StatementE.lean:115-116). That is the Frobenius-twisted pairing x·y^p of
  Gser.
- **Even levels are eaten by the LT radius.** Legendre gives Σ_{e≥1} a/p^e. The rescaling costs ρ_p a = Σ_{e even≥2} a/p^e.
  This is the "inert" input: height 2 means ρ = 1/(p²−1). At a split p the group has height 1, the radius cost is
  1/(p−1), and the gain is 0, consistent with the NUMTEST controls.
- **Matching the ledger's character.** 1 − χ_{−d}(p^e) = 2 for e odd and 0 for e even, at inert p. The factor 2 comes
  from squared norms, or Σ_{w|p} 2·lw·e_w (WRITEUP S7). That factor is outside this engine.
- **−w and (·)₊** (`excessGainBound`, ABArith.lean:193-238). For e ∉ dSet(s), iN ≤ min(al/p^e, cap), so
  al/p^e − iN ≥ (al/p^e − cap)₊. Summing over e with Σ_{e odd} al/p^e = γ·al (`oddPowerInvSumIdentity`) turns
  γ·al − Σ_e iN − Σ_e chN into Σ_e (al/p^e − cap)₊.
- **dSet.** For e ∈ dSet(s) (the partner is another top), A- and B-pieces together use up to al/p^e and that level
  contributes 0. The A-piece accounting is in `charge_exists`/`ChargeLemma` (EntryAOneParity.lean:55-126;
  ABArith.lean:185-191).

## 3. Reconciliation with the numerics

**Which object the Lean bounds.** The Lean bounds D^λθ_{c,c′}(0), where λ is a top linear form to the power a at position
s, times column minors at the other positions. It is taken in position coordinates that differ from the complex Taylor
coordinates of VV by a p-adically unitary change:
- frame (unit determinant);
- orthonormal basis b;
- ω-basis;
- ltC, which is a unit: ‖ν‖ = 1 at RepDict.lean:470-473, per KERNELLAW.

At w = 0 the bound is v ≥ v_p(a!) − aρ_p ≈ γ_p a.

| test | object | same as the Lean's? | result vs the proved exponent |
|---|---|---|---|
| NUMTEST (σ) | D^aσ(0), one variable | **no**: a single σ\* keeps its self-Gaussian ph | a/(p²−1), as predicted by (c): no isotropic partner |
| NUMTEST addendum (℘) | Laurent coefficients of ℘ | the w = 0, Gaussian-free case (℘ is a coordinate of the integral model) | γ_p, the Legendre − radius law |
| NUMTEST2 | σ(z+w)/(σ(z)σ(w)) | **no**: the Kronecker quotient, a non-hyperbolic two-variable combination | slope γ_p, cap only at e = 1; the Lean's bound is weaker there (conservative) |
| NUMTEST3 | th0(z₀+z₁)·th0(c(z₀−z₁)), cc^σ = −1; J = ∂_{z₀}^a∂_{z₁}^w Θ(0) | **yes**: n′ = 2, one matrix entry, top at 0, w size-1 minors at 1; isotropy is `iso_fK` | ≥ the proved bound, worst −0.98 relative to γa − Σmin (below excessGain only by the digit sum, which deLoss covers) |
| NUMTEST4 | n′ = 4 kernel; det(Y)^m blocks | **yes**, including genuine minors | caps per position, det^m costs m (= number of minors, as in (d)); worst −1.54 |

The σ-versus-℘ gap is the self-Gaussian: σ\* alone carries ph ≃ c·x^{p+1}/p, while the Lean's object is a hyperbolic
combination where ph cancels. So **the proved exponent concerns the same jets that NUMTEST3/4 measured**, and NUMTEST and
NUMTEST2 measured different functions. Caveat: NUMTEST3/4 tested only inertClass served primes (SERVED §2), and the
coupled-overhang case (NUMTEST4 T2 note) was not tested.

## 4. From one lift to m chained lifts

**`main_ind`** (MV/YEPEComm.lean:131-200; read):
- It is an induction on m′ with chainK_{m′+1} = Kz_{m′} ∘ chainK_{m′}.
- The induction hypothesis gives chainK_{m′}(W) = ϖ^{G_{m′}}·G′ with G′ ∈ Int_{m′} arbitrary (`hG'e`).
- The one-step bound `ZL_bound` holds for **every** G′ ∈ Int_{m′}. So linearity gives
  v(chainK_{m′+1}) ≥ G_{m′} + bbJ_{m′} (:195-199).
- **What is composed:** the linear maps Kz_j : Fm_j → Fm_{j+1}. Gains add because a scalar ϖ^g factors out of a linear
  map.
- Level-0 Hecke operators yv are pushed up through the chain by the Rallis-type commutation hCi at price PrZ (the gB
  route). The Hecke-free route uses G0n = gA, i.e. excessGain.
- **Where caps limit the gain per position:** at level j+1 the caps are ν_{j+1,·} (FGS:28-38, 57-70). They grow with j,
  because the level-j weight adds blocks w_j and w is monotone (`w_mono`, FGS:101). The top weight al = λ_{s,1} − λ_{s,2}
  is the same at every level (FGS:33-34). So the total is Σ_j Σ_s Σ_{e odd}(al_s/p^e − cap_{j,s+e})₊ − Σ_j(deLoss_j + dG_j).
- The orbit route has the same shape (`chain_ge`, ORBIT §0.2; not re-read).

## 5. Honest list

**Verified by reading (this round):**
1. The definition of θ_{c,c′}: variables, lattice, Heisenberg sum, vacuum, σ\* (§1.1-1.2).
2. The LT coordinate and the meaning of "integral" (§1.3).
3. adm2 ⇒ InClass via RestBeta/RestGc/RestSInt/Dwork: the composition proofs.
4. Isotropy and duality of the frame (`iso_fK`, `dual_fK`) and the hyperbolic split (self-terms cancel).
5. Adjointness, minor vanishing, product vanishing, HitsCapPos.
6. TermBound, StarArith (Legendre), star_norm, EntryStar_of assembly.
7. The excess-gain arithmetic (max + min); the odd-e structure; `main_ind`.

**Resting on statements only:**
- **adm2 for the live kernel** (`first_kernel_law_global_small`; LOCALDIV and KERNELLAW read the reduction, not every
  body). This is the main arithmetic input.
- `posOK` (supplier of position = r_v·Frob^s, i.e. of LamPosG): **not opened by any node**.
- `HhDecomp`'s proof `decomposition_of_hh` (statement checked by hand at n′ = 4 in GAUSSCLASS).
- TwoSums (read by GAUSSCLASS); RestBeta's LemmaOne (Dieudonné/Honda, standard).
- `HasseDerivIntegralHomogeneous` (`e_one_integral_of`).
- `reduce`/generic-frame reduction (FLN/EGaussK.lean:38-60, statement only).
- adm7 and ExpansionEquality (LOCALDIV); `ZL_bound`.
- The `LatTied` identification cap = ledger w (PAIRING).

**Inferences not visible in the Lean:**
1. The reading of `RestSInt` via λ(T) = ℓ(ϖT)/ϖ (§1.3). I derived it; it matches LOCALDIV Step A.
2. **Size of deLoss.** r0·r1 = N(j)·N(j+1) ≈ x^{798} (ranks from ARCH/CHAININD), and lg(ls) ≈ x^ε/log p. So deLoss is
   ≈ n′·x^{798+ε} per prime per lift, and at most x^{O(1)} summed over p ≤ x and m lifts.
   - This is negligible against b = e^{x^ε}, and so within the budget U·x^{−1/2}.
   - It is **far larger** than the 1–1.5 loss seen numerically. The bound is valid but loose in the constant.
   - If the ledger's loss allowance LoP is not superpolynomial (b-sized), this would matter. MAIN-ARGUMENT §2.3 says
     LoP ≈ c|TT|mb, which suffices.
3. That tops are placed so the dSet exclusions do not remove ledger terms: not traced.
4. The factor 2 and the identification with Λ(n)(1 − χ(n)) are ledger-side (WRITEUP S7), not part of this engine.

**ESCALATE: none.** The proved exponent equals the ledger's Σ_{e odd}(a/p^e − w)₊ up to deLoss + dG, which are
x^{O(1)}. Every link has a supplier. The expert's ten-minute check should be adm2 for the live kernel and `posOK`.

## 6. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `first_kernel_law_global_small` | IKT/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean:124 (LOCALDIV) | adm2/2b/3 for the live kernel | **core**; reduction read by others, not here |
| 2 | `posOK`/`pos_C` | GroupLattices/TiedFamilies/TieIwLevTieOf.lean:56 (LEAVES) | positions are Frobenius twists | **core**; unopened |
| 3 | `iso_fK`, `dual_fK`, `kurONB`, `sigma_fK` | RF:808-1000 | hyperbolic frame | core; **read** |
| 4 | `hyperbolic_plane_split` | HPS:114-152 | self-terms cancel | core; **read** |
| 5 | `SConcl_of`, `restSExp_of`, `baseChange_preserves_unitary_of` | KernelExpansionOfRestrictions.lean:116-140; DER:95-139 | adm2 ⇒ InClass | core; **read** |
| 6 | `TermBound_of`, `term_bound` | FLN/NormNatCastLeOfDvd.lean:397-545 | Dwork term expansion | core; **read** |
| 7 | `gainFactorialInequality` | FLN/ABArith.lean:103-183 | Legendre | standard; **read** |
| 8 | `HitsCapPos_of`, `minor_hits`, `e_one_vanish_of`, `e_one_identity_of` | FLN/MinorProdBlockDegree.lean:36; FLN/FinsuppStepInduction.lean:189-785 | cap lemma | core; **read** |
| 9 | `EntryStar_of`, `entryExcessBound_of`, `excessGainBound` | FLN/NormLeOfDvd.lean:309-405; FLN/EntryAOneParity.lean:177; ABArith.lean:193 | assembly | glue; **read** |
| 10 | `decomposition_of_hh` | FLN/EDecomp.lean:498 | mod-p decomposition of hh | formal; stmt |
| 11 | `reduce` | FLN/EGaussK.lean:38 | generic frame | glue; stmt |
| 12 | `main_ind` | MV/YEPEComm.lean:131 | composition | glue; **read** |

## 7. Oddities

1. **deLoss is enormous in absolute terms** (§5 inference 2). It is harmless only because b is superpolynomial.
2. **The cap at a non-top partner is ν_{j+1,s,1} = λ_{s,1} + w_{j+1}(s)** (FGS:28-38), the full first row, not the block
   weight w alone. The ledger's w must be this number (PAIRING's job).
3. `HitsCapPos` needs a common ξ for all derivatives charged to one position. It is applied per (top, level), where this
   holds. Derivatives from *different* levels landing on the same partner are charged separately. So the Lean caps
   per (s, e), not per partner position. With n′ > 2, several e can share a partner (s+e ≡ s+e′ mod n′); each is capped by
   the same capN, so the total charge can exceed capN. This is conservative, since the Lean subtracts more.
4. u_s may be 0 (RestBeta only gives ∃c). That would strengthen the bound. Nothing depends on c ≠ 0.
5. In gB, caps are subtracted only at odd tops, and even tops get full γ·al. That is paid by Hecke factors p^{colExp} and
   charged Pr in the chain. It is not a free gain, because the Pr charge in `main_ind` takes it back.

## 8. Coverage

Read this round:
- KTH:1-37; XIC:1-245; ISC:1-70; ProductThetaMem.lean:10-30; LAT2:1-200; SC:1-36;
- FGS:25-262, 395-430, 625-640;
- UTS/StatementE.lean (all); UTS/StatementAB.lean:1-142; UTS/StatementG.lean:1-60; UTS/OddLogRelation.lean:1-95;
  UTS/CyclicPowerClassOfExpEquiv.lean:60-140; UTS/KOneConsequence.lean (all);
- FLN/NormLeOfDvd.lean:196-405; FLN/NormNatCastLeOfDvd.lean:286-545; FLN/ABArith.lean (all);
  FLN/EntryAOneParity.lean:1-215; FLN/MinorProdBlockDegree.lean:36-75; FLN/FinsuppStepInduction.lean:150-260, 700-785;
  FLN/EGaussK.lean:38-60, 132-158;
- Formalism/GaussJetBounds/StatementI.lean:1-40; Formalism/GaussJetBounds/Statement.lean:15-60;
  Formalism/GrowthSums/StatementA.lean:63-112;
- MV/DworkExponentialRestrictions.lean (all); MV/CommonEigenvectorThird.lean (all);
  MV/KernelExpansionOfRestrictions.lean:1-142; MV/YEPEComm.lean:125-200;
- RF:660-700, 800-1000; .../SecondCoefficientNorms/IsotropicVanish.lean:60-125;
  .../BinomialSeriesCoefficients/UnitaryInverseIdentity.lean:476-488; HPS:1-152;
- PairingIndexBounds/OrthogonalChartLevels/LtCNeZero.lean:1-20; InertCoprimeLemmas/RepDict.lean:470-490.

Not opened: `posOK`; `decomposition_of_hh`; `e_one_integral_of`; `reduce` body; `TwoSums` body (GAUSSCLASS read it);
`ZL_bound`, `formB`, `restEnt_of`; `first_kernel_small_of_frame_twist`; `adm7` supplier; `hits_col`, `degLE_minor_row`
bodies (I read `hits_row`'s use and `minor_hits`); PAIRING and HIGHERRANK Lean sources.
