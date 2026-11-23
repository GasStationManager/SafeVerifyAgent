# NODE-INTINERT: `IntInert` = `kernels_integral_inert`, read to its leaves

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`; `ICL/` = `IKT/InertCoprimeLemmas/`
- `TLM` = `Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- `UGM/` = `Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/`
- `GG/` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`

**read** means I read the proof body this round. **stmt** means I read the statement only. **(mine)** marks my own
reasoning or computation; none of it is in the Lean.

## 0. Verdict

**No ESCALATE.**

1. **What is asserted.** Fix an admitted pair of self-dual hermitian O_E-lattices (L, L′) and any p ≥ 5 with
   (−d/p) = −1. Fix any p-local orthonormal O_K-basis b of the hermitian O_K-lattice Y = AA0·Hom(L, L′), with the form
   Tr_{E/K} tr(x y\*). Then θ(Σ_i b_i·u⁻¹log_W T_i)·∏_i u⁻¹T_i/σ\*(u⁻¹log_W T_i) has all coefficients in O_{ℂ_p}. This
   holds for every p-integral combination θ of prime-to-p torsion translates of the lattice theta θ_{L,L′}. The T_i are
   the formal parameters of any integral Weierstrass model with Δ = 1. The only use of p is (−d/p) = −1, plus p ≥ 5.
2. **The proof is complete in the tree and rests on no Published input.** Its one arithmetic `Fact` is CM2, good
   reduction of CM curves over ℚ̂_p^ur, which KERNELLAW records as proved. The reduction has six steps:
   - weak approximation for U(n), together with uniqueness of unimodular hermitian lattices at p;
   - prime-to-p coset averaging;
   - tensor products;
   - one copy, obtained from a fourfold Lagrange isometry of prime-to-p index whose normalising constant κ is a p-unit;
   - unitary invariance of Σph;
   - the one-letter Kronecker-quotient integrality.

   Each piece is classical. I name each one in §2.
3. **The "orthonormalisation" is a prime-to-p frame change at every inert p, and no prime is excluded.** Three facts
   make Y unimodular at every prime:
   - L and L′ are self-dual;
   - AA0 = 𝔟⁻¹ with different(E/K) = 𝔟𝔟̄ and 𝔟 + 𝔟̄ = 1 (a host field);
   - E/E⁺ is unramified at every finite prime (`IsCMUnram`, a host field).

   `LocBasis` itself says that b is a basis of Y up to integers prime to p, which is an isogeny of degree prime to p.
   No inert prime can be bad (mine, from host facts). E/K ramifies only at 2, q, d and the QS primes. Here 2, q and
   every odd QS prime split in K, and d ramifies in K. So no cost needs booking for IntInert.
4. **One-variable case (mine).** Here IntInert is not the ADM2 tautology. It is the integrality of the Kronecker
   quotient T·σ\*(z+t)e^{…}/(σ\*(z)σ\*(t)) at 2-torsion t. LEAVES checked this exactly to T^260. The first content beyond
   one letter is rank 2: unitary invariance of Σ ph. It holds exactly when Frobenius acts as complex conjugation on O_K,
   i.e. at inert p. My exact checks (§3) confirm the following:
   - unitary frames are integral at inert p;
   - non-unitary frames, and the bare two-variable Kronecker function exp(−be(x, y)), fail first at x·y^p with
     v = −1, at inert p only.

   This matches NUMTEST2 and ADM2's c·xy^p/p with c a unit. No contradiction.
5. **Corrections to earlier status entries.**
   - `HypShape_of` is a proved theorem (`UGM/OrthogonalGaussModels/KappaIntegralOfCalculation.lean:42-109`, read) and
     `b0` is proved (`.../GaussSumParity/BiextensionHypothesesOfLevelOne.lean:37`, a composition of named theorems).
     Neither is a bare statement.
   - `StdTie.adapted` is produced by `AdaptedBases.exists_sys`, read. It uses one global unitary matrix G for every
     embedding, so the conjugate-dual condition holds trivially: dualM G = G.
   - `der.frob` is a field of `HostDer`. It is the Frobenius = Artin-map statement for abelian E (CFT).

## 1. Statement

`IKT/StatementInt.lean:9-24` (read):

```lean
def IntFirst D T e p lam N N' L L' : Prop :=
  ∀ F, IsComb D T e lam L L' F → ∀ C wq r b,
    IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
    Orthonormal D b → IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)

def IntInert : Prop :=
  ∀ D cc δ (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ, IsChi D χ → ∀ p [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ lam N N' L L', admitted D N N' L L' → IntFirst D B.tor (B.eNat χ) p lam N N' L L'
```

Unfolded (TLM, read):

- **The CM curve and its lattice.** Λ = lamOf cc δ = δ·φ₀(cc) with δ¹² = Δ(lamOf cc 1) (TLM:53-60), so Δ(Λ) = 1. The
  ideal cc is coprime to 2d (TLM:56-57).
- **The lattices.** `admitted`: N and N′ are even, and L ⊂ E^N and L′ ⊂ E^{N′} are self-dual for stdH(x, y) = Σ x̄_i y_i
  (TLM:171-174; `IsSDLat`, `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:54-59`).
- **The hermitian O_K-lattice.** Y = YYl L L′ = AA0·Hom(L, L′) ⊂ M_{N′×N}(E) (TLM:27-36). Its form is
  hYY(x, y) = Tr_{E/K} Σ_{ij} x_{ij}·conj(y_{ij}) (TLM:38-39). Also AA0 = 𝔟⁻¹ (`Formalism/LocalRingCardinality/DataHost.lean:153-154`),
  and the host field 𝔟_spec says different(E/K) = 𝔟·conj(𝔟) with 𝔟 + conj 𝔟 = ⊤ (same file :64-67).
- **The theta datum.**
  - The space is VC = ℂ^{Tau×N′×N}, with hermitian form Hf(z, w) = Σ z w̄ / area(Λ) (TLM:66, 78-79).
  - The period lattice is La = ⟨w·embV(A) : w ∈ Λ, A ∈ Y⟩ (TLM:74-76), where embV applies the CM-type embeddings τ ∈ Tau
    entrywise.
  - The translate is U_x G(z) = G(z+x)·exp(−πHf(z, x) − πHf(x, x)/2) (TLM:84-85). The coset average Iop carries a
    1/√index factor (TLM:100-104).
  - θ_{L,L′} = B.eNat χ N N′ L L′ = χ-factor · Iop∘Iop(thZero), thZero = tensPow(thMM) (SAMETHETA §1, KERNELLAW §2).
  - thMM is the one-copy theta on ℂ^{Tau} for H = area⁻¹·I with the semicharacter alphaQ(√d/2). It is pinned by
    tens4(thMM) = κ·kernel4(gC), where kernel4 is a coset sum of products of th0-letters
    (`Formalism/LocalToGlobal/KernelLattices/LateralTheory.lean:20-29`; `.../QuadraticSemicharacters/ProductThetaMem.lean:66-69`).
- **The functions to which the claim applies (`IsComb`, TLM:280-295).** These are finite sums Σ r_k·pSer(U_{t_k} θ_{L₁,L₁′}) with:
  - |r_k| ≤ 1;
  - t_k torsion of order prime to p in La;
  - (L₁, L₁′) admitted and equal to (L, L′) up to integers prime to p (`EqAt`).

  pSer is the Taylor series at 0, mapped to ℂ_p by lam (TLM:211-213).
- **The variables.** `IsModel` requires an integral model C•wModel with Δ = 1 (TLM:187-190), and wq is its w-series
  (TLM:195-199). flog = log_W in the parameter T = −x/y (TLM:201-209). atLog substitutes
  z_{(τ,i,j)} = Σ_i u⁻¹·λ(τ(b_i)_{ij})·log_W(T_i) (TLM:225-232).
- **The normalising product.** ePh = ∏_i ePhi1(T_i)⁻¹, where ePhi1(T) = σ\*(u⁻¹log_W T)/(u⁻¹T) (TLM:245-257).
  Here σ\* = sgStar is the odd entire function with σ\*′(0) = 1 and the functional equation U1_ω σ\* = ±σ\* (TLM:234-243).
- **The basis.** `LocBasis` says three things (TLM:215-220):
  - the b_i are K-independent;
  - s·b_i ∈ Y for some s prime to p;
  - for every y ∈ Y there is s prime to p with s·y ∈ Σ O_K b_i.

  `Orthonormal` says hYY(b_i, b_j) = δ_{ij} exactly (TLM:222-223).
- **Integrality.** `IntegralMv` says every coefficient has ‖·‖ ≤ 1 in ℂ_p (TLM:259-260).

**In words.** At every prime p ≥ 5 inert in K = ℚ(√−d), the following holds in every p-local orthonormal O_K-frame of
the hermitian lattice AA0·Hom(L, L′). Each prime-to-p translate of the lattice theta, divided by the product of
one-variable σ\* in the frame coordinates, is integral in the Weierstrass formal parameters of a good model of the CM
curve with Δ = 1.

**No hypothesis needs to be met at the call site.** The statement is ∀b, and existence of b is proved separately:
`orthBasisExists_of` (`ICL/JetsOrth.lean:58-79`, read), used by `hostAt_inert` (`SP/JacobiOfClass.lean:71-72`, read). The
consumer `hostAt_inert` (:63-81, read) needs only p ≥ 5 and IsResidueClassZero ∨ IsSg. Through `jacobi_of_class` (:41-61,
read) these give (−d/p) = −1. It transfers to the LT parameter via CurveDict (`hd`, :74-81).

## 2. Argument (proof read down to named leaves)

`kernels_integral_inert = integral_inert_of_approx_basis weak_approximation_places local_orthonormal_basis`
(`IKT/KernelsIntegralInert.lean:9`, under `[Fact CM2]`). This unfolds to `integral_inert_of_weakApprox`
(`IKT/IntegralInertOfApproxBasis.lean:15-16`) and then to `intInert_of …` (`IKT/IntegralInertOfWeakApprox.lean:9-13`).
The skeleton is `ICL/IntAsm.lean:15-91` (read):

| step | statement (DefsInt.lean, read) | supplier | mathematics |
|---|---|---|---|
| 0 | `CombFact` (:33) | `combination_fact` | integral combinations of integral series are integral |
| 1 | `PairFact` (:40) | `pairing_fact` | LocBasis and TorsPrime are unchanged when L is altered by integers prime to p |
| 2 | `WeakApprox` (:48) | `weakApprox_of weak_approximation_places` (`ICL/IntWeak.lean:276-286`, read; `wa_main` :171-200, read) | L = γ·M with γ ∈ U_N(E) global and M = std up to integers prime to p. Uses `wa_unimod` (self-dual ⇒ unimodular, :144-152, read), `unimodular_genus_unique` (unimodular lattices are locally isometric to std; `Formalism/PeriodIntegrals/OrbitalBoundsConclusion/UnimodGenus.lean:5-6`), and `WAPlaces` (weak approximation for U(n) at the primes above p). Needs `IsCMUnram`: E/E⁺ unramified at every finite prime (`Formalism/PeriodIntegrals/UnimodGenus.lean:77-81`), a host field `D.sp.cm.cmUnram`. **Standard** (Jacobowitz; weak approximation for the rational group U(n)) |
| 3 | `PullTors`, `PullFact` (:59, :70) | `pullback_torsion`, `pullback_fact` | transport through the unitary γ, a linear change of the matrix variable |
| 4 | `StdStep` (:101) | `pairs_standard_at_p` (read in full by LEAVES) | a prime-to-p translate of θ_M is Σ c_k U_{s_k}(thZero), with c_k p-integral. Coset averaging of index prime to p |
| 5 | `BasisInv` (:114) | `basisInv_of_loc unit_substitution_local` (`IKT/IntegralInertOfWeakApproxTheta.lean:14-18`, read) | independence of the orthonormal basis. The change between two such bases is a unitary U ∈ U_r(ℤ_{p²}), and Σ ph is U-invariant mod ≃. Built from integral endomorphisms, NormRel and biadditivity (§3) |
| 6 | `TensFact` (:122) | `tensor_matrix_units_fact` | N×N′ from 2×2: thZero is a tensor power |
| 7 | `ThFourInt` (:133) via `thFourInt_of (oneCopyLoc_of_isom …) … four_products_from_one (globONB_of …)` | `IKT/IntegralInertOfWeakApprox.lean:12-13` | 2×2 from one copy (`FourProd`, `IKT/DefsMM.lean:58-68`, read) |
| 8 | `OneCopyLoc` (`IKT/DefsMM.lean:40-46`) from `IsomONB` (`IKT/OneCopyTh1S.lean:51-61`, read) | `isomONB_ofLB` → `isomONB_of` (`ICL/MMIsom.lean:72-79`, read) → `isomStd_frames` (:33-68, read) → `kappa_K1_hypothesis` (`ICL/KappaSelfDualFourthPowerLattice.lean:317-367`, read) | **The Lagrange device.** For each inert p, there is a fourfold isometry G = gC∘u from 4·(ℂ^{Tau}, hOne) to the standard form. Its image lattice has index in std prime to p (`¬ l ∣ relIdx`). tens4(thMM) = e·kernel4(G) with ‖e‖ = 1. Here e = κ·c, κ is a p-unit at inert p (`kappa_at_inert_prime` :302-311, read: `kap_norm_kappa`, `detInK`), and c^8-type ratio constants come from `kernelRatio`. So exp(Σph)·thMM^{⊗4} = e·(product of letters in a unitary frame over ℤ_{p²}), and the **fourth-power trick** gives thMM (LEAVES: `fourth_power`, `NJN/GeneralIntegrality.lean:160`) |
| 9 | the per-letter law | `joint_integrality` (LEAVES, read there) | T·σ\*(z+t)e^{−η\*(t)z}/(σ\*(z)σ\*(t)) is integral for torsion t of order prime to p. Proof: the σ-addition formula, telescoping, the unit differences x(t) − x(z+jt), and extraction of an N-th root with p ∤ N. **Standard**: the Kronecker theta function or Siegel-unit integrality (de Shalit II.2–4; Kubert–Lang, Ch. 2) |

**Mathematical content (mine, assembled from the above).** The abelian variety is A = (E_Λ ⊗_{O_K} Y) ⊗ …,
i.e. the Serre tensor construction of the CM curve E_Λ with the hermitian module Y. An orthonormal p-local O_K-basis b
of Y gives an isogeny A → E_Λ^r of degree prime to p that respects the polarisation. Pulling the theta back along it
gives a function on E_Λ^r. That function is a ℤ_{(p)}-combination of prime-to-p translates of the product theta. This
is weak approximation plus coset averaging, plus the Lagrange 4-copy trick that makes the one-copy theta a product
theta after a prime-to-p isogeny. The product theta divided by ∏σ\* is a product of Kronecker quotients, hence integral.

The one non-formal point is the basis change. Changing frames by U ∈ U_r(ℤ_{p²}) multiplies by
exp(Σph(X) − Σph(UX)). This is integral because ph([α]x) ≃ α·σ(α)·ph(x) and be(αx, y) ≃ be(x, σ(α)y). At inert p,
σ|O_K is complex conjugation, so ασ(α) = αᾱ and the cross terms cancel exactly for unitary U. This is the "only use of
(−d/p) = −1".

**Where the "isogeny/orthonormalisation" loss could have entered (task 3).**
- **Unimodularity of Y at p.** L and L′ are self-dual, AA0 = 𝔟⁻¹, and different(E/K) = 𝔟𝔟̄ with 𝔟 + 𝔟̄ = 1. Hence the
  hYY-dual of 𝔟⁻¹ is 𝔟̄·different⁻¹ = 𝔟⁻¹ (mine). So Y is unimodular at **every** prime, and `OneCopyOrth`
  (`IKT/DefsMMOnb.lean:9-14`; proved `one_theta_orthonormal`, `ICL/GlobalOrthonormalBasisFour.lean:1268`, body unread)
  can hold with unit diagonal values.
- **Global orthonormal basis.** OneCopyOrth gives an orthogonal basis with values u_i ∈ ℚ, p-units. Four copies then give
  an orthonormal one by Lagrange's four squares (`GlobONB`, `IKT/DefsMM.lean:70-76`; `globONB_of`). That is why the
  standard block is 2×2.
- **Degree of the frame change.** `LocBasis` fixes it to be prime to p; IsomStd fixes the Lagrange index to be prime to p
  (`IKT/OneCopyTh1S.lean:28-39`, read). IsLocONB's local frame A has integral entries and ‖det A‖ = 1
  (`IKT/DefsMM.lean:28-38`, read).
- **Small primes, primes dividing discriminants, and bad primes (mine, from host facts read in HOSTS and in source).**
  - E has conductor QS·q·d.
  - Every odd ℓ | QS, and every odd p ≤ splitBound, splits in K (HOSTS §1). So p = 3 and every QS prime are never inert.
  - q | d+1 gives (−d/q) = (1/q) = 1, so q splits in K (`WinPair`, HOSTS §(c1)).
  - d ≡ 7 mod 16 gives −d ≡ 1 mod 8, so 2 splits.
  - d ramifies in K.

  So every prime inert in K is ≥ 5, unramified in E, and prime to AA0 and the different. IntInert's hypotheses (p ≥ 5,
  inert) hold at every inert p ≤ X″ with no exclusion and no booked cost. The same facts make 𝔟_spec satisfiable: the
  ramified primes of E/K lie over split primes of K, so P ≠ P̄.
- **`MInv` / `isUnit_det_frameMatrix_ofCharts`** (`SP/IsUnitDetFrameMatrixOfCharts.lean:14-25`, read). This is only
  IsUnit in a field, i.e. det ≠ 0 (the proof is the det of a linear equivalence times the det of a unit matrix). The
  p-adic control of the frame and its inverse is the separate K1 field `FrameInt` (`IKT/FrameInt.lean:51-59`, read), which
  bounds the products with M and with M⁻¹ (`Gmi`). It is Hecke-route only (KLAW §3) and is not part of IntInert.

## 3. Hand and exact checks in the elliptic case (all mine)

**One variable.**
- θ = th0 = U_{ω₀/2}σ\*/U_{ω₀/2}σ\*(0). IntInert then reads: T·σ\*(z+t)e^{…}/(σ\*(z)σ\*(t)) is integral, with t = ω₀/2.
  This is the Kronecker quotient, not exp(ph)·σ\* (which is ADM2's tautology).
- The translate by ω₀/2 gives θ ∝ σ\*. The claim then reduces to |σ\*(t)e^{−π|t|²/2A}| = 1. That is the Klein-form value
  at 2-torsion, a unit away from 2 when Δ = 1 (Kubert–Lang). The Lean proves it by the parallelogram law `ParSum` (LEAVES).
- Exact data (`numtest/out_leaves_normrel_M130.txt:4-9`, read):
  - ℤ[i], p = 7, 11: PH = σ\*/T first becomes non-integral at T^{p+1};
  - KR = T·K_t is integral to T^260.

**Rank 2: the minimal non-tautological case.** Take θ = σ\*(w₁)σ\*(w₂) with w = Az (the product theta of the standard
rank-2 lattice) in the frame A. Since T(w_i) = [a]T₁ +_F [b]T₂ is integral, IntInert is equivalent to integrality of
E_A = exp(ph(T₁) + ph(T₂) − ph(T(w₁)) − ph(T(w₂))).

I computed E_A exactly in ℚ(√−d) to total degree D, in the Weierstrass parameters. The script is
`/tmp/claude-0/-home-user-SafeVerifyAgent/6f6a4549-468b-59ec-896e-73bdf5d26a96/scratchpad/intinert/rot_check.py`, with
outputs `out_rot_D26.txt` and `out_rot_w_D30.txt` in the same directory. The scratchpad is ephemeral, so the key lines
are below.

| curve, A | inert p | result | split p |
|---|---|---|---|
| ℤ[i], unitary (3/5, 4i/5; 4i/5, 3/5) | 3, 7, 11, 19, 23 | integral to degree 26 | 13, 17 integral |
| ℤ[i], real rotation (3/5, 4/5; −4/5, 3/5) | same | integral | integral |
| ℤ[ω], unitary (5/13, 12ω/13; −12ω̄/13, 5/13) | 5, 11 | integral to degree 30 (past p²+1 = 26 at p = 5) | 7 integral |
| ℤ[i], columns of norm 1 but not orthogonal (3/5, 4i/5; 4/5, 3i/5) | 7, 11, 19, 23 | **first v < 0 at T₁T₂^p, v = −1** | integral |
| ℤ[i], complex-orthogonal AAᵀ = 1, not unitary (5/4, 3i/4; −3i/4, 5/4) | 7, 11, 19, 23 | first v < 0 at T₂^{p+1} (self-term) | integral |
| ℤ[i], shear (1, 1; 0, 1) | 3, 7, 11, 19, 23 | first v < 0 at T₂^{p+1} | integral |
| two-variable Kronecker exp(−be(x, y)) = exp(ph(x) + ph(y) − ph(x +_F y)) | ℤ[i] 3, 7, 11, 19, 23; ℤ[ω] 5, 11 | **first v < 0 at T₁T₂^p, v = −1** | integral |

Reading:
- (a) The orthonormal-frame claim holds in the exact data. It is sharp: breaking unitarity in the cross term alone
  gives a failure at exactly x·y^p/p. This is ADM2's leading cross term c·xy^p/p with c a unit, and NUMTEST2's cap at
  e = 1.
- (b) The two-variable Kronecker function is **not** integral at inert p, and IntInert does not claim it is.
  IntInert's content beyond one letter is that the cross Gaussian cancels in unitary frames. That needs Frobenius =
  conjugation on O_K. At split p everything is integral. This is consistent with σ\* being the Mazur–Tate σ at ordinary
  CM primes (Katz: the p-adic E₂ equals E₂\* at ordinary CM points), so the split controls do not discriminate.
- (c) Two exceptions in the table have arithmetic explanations. For "not orthogonal" over ℤ[ω] at p = 5, the defect
  coefficient 120ω/169 is divisible by 5, so the failure moves to degree 30. For "C-orthogonal" over ℤ[i] at p = 3, the
  defect 9/8 is divisible by 9.
- (d) The checks cover rank 2, tiny degree, the curves of ℤ[i] and ℤ[ω], and σ\* letters in place of th0 (equal up to a
  2-torsion translate and a unit constant).

## 4. The other statement-level items (task 5)

| item | what it asserts | supplier | status |
|---|---|---|---|
| `HypShape_of` | given HostLog-type integrality exp(Σph)·Θ and a hyperbolic pair (f, f′), Θ∘inHyp = exp(−Φ)·U₀ with U₀ integral and Φ ≃ Σ_e cob(F, ph)(x_e, y_e) (statement `UGM/UniformGaussModelCondition.lean:42-56`, read) | **proved**: `UGM/OrthogonalGaussModels/KappaIntegralOfCalculation.lean:42-109` (read). The proof substitutes the hyperbolic coordinates into the integral series (`substExpInt`) and applies `hyperbolicSum` (isotropy and duality of f, f′, with NormRel on all integral α and biadditivity from `CalcC_proof`, `.../OfClosedInt.lean:108`) | proved; leaves `hyperbolicSum`, `CalcC_proof` read at top level by GAUSSCLASS |
| `b0` (B0) | moving from hyperbolic to position coordinates: thetaInZ(exp(−Φ)U₀) = thetaZ(g, U, −1, beMean), where beMean is the torus average of be₀ under the dual bases (om, oms) and ζ (statement `.../GaussSumParity/StatementB.lean:49-64`, read) | **proved**: `.../GaussSumParity/BiextensionHypothesesOfLevelOne.lean:37` = `biextension_of_exp_spec expSpec biextension_points_integral`, itself a composition of `meanSimeqL`, `tilInvariantL`, … (:14-36, read) | proved; bodies of the components unread |
| `StdTie.adapted` | conjugate-dual adapted bases: conj(P_{z+1})ᵀP_z = 1 (`GG/StdBases.lean:12-17`, read) | `linkR_stdTie_entry` (`TPS/LinkRStdTie.lean:20-24`, read) reads it off the linkage predicate `RecordCompatibleExtended.std` (`TPS/CoreAltAltBis.lean:56-60`, read). That predicate is witnessed by `exists_recPinE_alt` (`TPS/ExistsRecPinE.lean:21-31`, read) → `WPt.exists_kerTie` (`.../IwasawaDecomposition/ExistsKerTie.lean:16-40`, read), where Adapted = `AdaptedTh` comes from `EntOk`. The natural supplier is `kerEntC_true`/`kerEnt_true` → `AdaptedBases.exists_sys` (`.../IwasawaDecomposition/NormNatCastEqOne.lean:158-169`, read): **Pm := G, the same for every τ**, with G a global unitary matrix whose columns are a p-local basis of L (`exists_unitary_at` :28-60, read, ← `GenusSelfDual.inGenus_of_selfDual`, unread). Then dualM G = G (`dualM_eq_self`) | proved modulo `inGenus_of_selfDual` (genus + weak approximation). *Inferred, not traced by equality*: that the live point's `kT.ok` is this construction |
| `der.frob` | for p ∤ condN and P | p: an arithmetic Frobenius exists, equals art(p), has sign coordinates psAt(p) and (−d/p), and inertia is trivial (`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:103-111`, read) | field of `HostDer` inside `HostAx` (:172-176, read). On the live path HostAx is built by `fieldChi` (HOSTS §(c1)); I did not open that proof | standard (class field theory for an abelian field cut out by an explicit Artin map). HOSTS' question |
| `BeData.exists_of_curveData`, `Quant`, `LogStep`, `lat_S` leaves | — | — | not opened this round (see §6) |

## 5. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `weak_approximation_places`, `unimodular_genus_unique`, `wa_main` | `ICL/IntWAPlaces.lean:465`; `.../OrbitalBoundsConclusion/UnimodGenus.lean:5`; `ICL/IntWeak.lean:171` | L = γ·(std at p) | standard (Jacobowitz; weak approximation for U(n)); `wa_main` read, the others stmt |
| 2 | `pairs_standard_at_p` | `ICL/IntStd.lean:302` | StdStep, coset averaging of index prime to p | standard; read by LEAVES |
| 3 | `kappa_K1_hypothesis`, `kappa_at_inert_prime`, `kernelRatio`, `localStandard` | `ICL/KappaSelfDualFourthPowerLattice.lean:317, 302`; `.../QuadraticSemicharactersFactTer.lean:9`; `.../QuadraticSemicharacterIdentityReformulated.lean:6` | prime-to-p Lagrange isometry; κ·c a p-unit | **core**; the first two read at top level, the last two stmt |
| 4 | `fourth_power` / `kappa_integral_of_calculation` | `KappaIntegralOfCalculation.lean:18-40` (read) | one copy from four copies | standard trick; read |
| 5 | `unit_substitution_local` (BasisInv/LocInv) | `IKT/IntegralInertOfWeakApproxTheta.lean:14-18` | Σph invariant under U_r(ℤ_{p²}) mod ≃ | **core** (the only use of inertness); composition read, leaves stmt; checked exactly in §3 |
| 6 | `joint_integrality` | LEAVES §L-A1 | Kronecker quotient integrality at prime-to-p torsion | standard (de Shalit; Kubert–Lang); read by LEAVES |
| 7 | `one_theta_orthonormal`, `local_orthonormal_basis`, `conjugation_extension_inert`, `rational_coordinates`, `conjugation_fixed_closure` | `ICL/GlobalOrthonormalBasisFour.lean:1268`; `ICL/FrLocB.lean:503`; `ICL/MMConj.lean:87`; `ICL/BlockFourfoldHOneEqHOne.lean:112`; `ICL/ConjugationFixedClosure.lean:64` | existence of orthonormal frames | glue/standard; stmt |
| 8 | host fields `𝔟_spec`, `cmUnram` | `DataHost.lean:64-67`; `D.sp.cm.cmUnram` | unimodularity of AA0, and E/E⁺ unramified | host construction (HOSTS) |

## 6. Oddities

1. **IntInert is ∀b, so it is vacuous if no orthonormal b exists.** Existence is proved separately (`orthBasisExists_of`)
   and consumed in `hostAt_inert`. So the vacuity does not reach the live path.
2. **HypShape_of and b0 were listed as statement-only (KLAW, MAIN §4.3).** Both are proved theorems.
3. **The adapted bases are τ-independent**: one global unitary G at every embedding. The conjugate-dual condition is
   then automatic. That is legitimate, because G is a p-local basis of L for every embedding, but it carries no content
   of its own.
4. **`MInv` is det ≠ 0, not a p-adic unit.** The p-adic control of the frame lives in `FrameInt`. This is Hecke route
   only.
5. **IntInert is proved for all p ≥ 5 inert in K, with no level or served condition.** That matches the expectation that
   its only use of p is inertness. The supersingular content is entirely downstream, in RestBeta and be.
6. Nothing false-looking was found. My exact data agree with every claim checked.

## 7. Coverage

Read:
- PROTOCOL; MAIN-ARGUMENT §0 and §4; NODE-KLAW, ADM2, GAUSSCLASS, KERNELLAW, THETA, SAMETHETA (all); HIGHERRANK
  20-320; LEAVES (all); HOSTS 40-160 (parts); SERVED (grep); NUMTEST2 1-40; ENGINE and ENGINE2 (greps for IntInert, MInv
  and StdStep only, not in full).
- Source:
  - `IKT/StatementInt.lean` (all); `KernelsIntegralInert.lean`; `IntegralInertOfApproxBasis.lean`;
    `IntegralInertOfWeakApprox.lean`; `IntegralInertOfWeakApproxTheta.lean` (all); `DefsInt.lean` (all);
    `DefsMM.lean:1-84`; `DefsMMOnb.lean` (all); `OneCopyTh1S.lean` (all); `ICL/IntAsm.lean` (all);
    `ICL/JetsOrth.lean` (all); `ICL/IntWeak.lean:1-40, 144-200, 264-286`; `ICL/MMIsom.lean:15-96, 300-358`;
    `ICL/KappaSelfDualFourthPowerLattice.lean:260-376`; `IKT/StatementKap.lean:16-45`; `IKT/FrameInt.lean:36-62`.
  - TLM:1-299.
  - `SP/JacobiOfClass.lean` (all); `GG/ExistsConstantCoeffOne.lean` (all); `GG/StdBases.lean:1-40`;
    `SP/OrbitIdentityAllOfIntegralClassHostLog.lean:110-165`; `SP/IsUnitDetFrameMatrixOfCharts.lean` (all);
    `SP/KerEntTiedTrueEnt.lean`; `SP/KerEntTiedWithEnt.lean`; `SP/TrueColumnChoicesKernelDatumAdaptedBases.lean:158-241`;
    `SP/TrueColumnChoicesKernelDatumAdaptedBasesStatement.lean`.
  - `UGM/UniformGaussModelCondition.lean:30-58`; `UGM/OrthogonalGaussModels/KappaIntegralOfCalculation.lean` (all);
    `GaussSumParity/StatementB.lean:49-75`; `GaussSumParity/BiextensionHypothesesOfLevelOne.lean` (all).
  - `.../QuadraticSemicharacters/ProductThetaMem.lean:55-100`; `KernelLattices/LateralTheory.lean:15-40`;
    `KernelLattices/AdaptedEnt.lean:45-51, 85-97`; `.../FixedVectorEqOfStandardData.lean:114-115`;
    `.../IwasawaDecomposition/AdaptedThKerEntC.lean:167-181`; `.../IwasawaDecomposition/NormNatCastEqOne.lean:28-60, 158-169`;
    `.../IwasawaDecomposition/ExistsKerTie.lean:16-40`; `.../DecoratedLatticeProofs/ExistsKerTie.lean:83-92`.
  - `TPS/LinkRStdTie.lean`; `TPS/CoreAltAltBis.lean:40-60`; `TPS/ExistsRecPinE.lean`; `GG/HasPartAnd.lean:20-40`;
    `ConjEMemHostFIff.lean:87-176`; `DataHost.lean:120-175` + grep :64-67; `HostCls.lean:1-75`;
    `RhoDetPrimeEqMuTildeMulChiPow.lean:54-62`; `PeriodIntegrals/UnimodGenus.lean:77-81`; `CMTraceOnto.lean:9-17`.
- `numtest/leaves_normrel.py` (all), `out_leaves_normrel_M130.txt:1-52` (grep).

Greps run:
- `def (IsComb|admitted|IntegralMv|ePh|atLog|Orthonormal|LocBasis|IsWq|ePhi1)`; `theorem intInert_of(B)`;
  `orthBasisExists_of|global_orthonormal_basis_four|weak_approximation_places|local_orthonormal_basis`;
  `def (GlobONB|OrthBasisExists|OneCopyOrth|WAPlaces|LocBasisMM)`;
- `one_theta_orthonormal|primeClass_eq_inert_iff|AA0 :`; `𝔟`; `IsSDLat|stdH`; `IsCMUnram|unimodular_genus_unique`;
- `isomONB_of_facts|…|oneCopyLoc_of_isom`; `kappa_K1_hypothesis|kappa_at_inert_prime|KappaAt|kernelRatio|localStandard`;
  `relIdx|kernel4|…`;
- `HypShape_of|CalcC_proof|HypShape`; `b0|B0`;
- `linkR_stdTie_entry`; `RecordCompatibleExtended|ReciprocityLinkage|StdTie`; `exists_kerTie`; `kerEntTied_true_ent`;
  `AdaptedTh|EntOk`; `kerEnt_true|kerEntC_true`; `exists_sys`; `der :|frob :|HostDer|DerOfRaw`; `MInv`;
  `IsUnitDetFrameMatrixOfCharts`.

Not opened:
- bodies of `weak_approximation_places`, `unimodGenus_of`, `one_theta_orthonormal`, `local_orthonormal_basis`,
  `conjugation_extension_inert`, `rational_coordinates`, `conjugation_fixed_closure`, `kap_norm_kappa`, `detInK`,
  `kernelRatio`, `localStandard`, `tensor_matrix_units_fact`, `four_products_from_one`, `unitSubstLoc_of_model` leaves,
  `hyperbolicSum`, the B0 components, `inGenus_of_selfDual`;
- `fieldChi`'s proof of HostDer;
- `BeData.exists_of_curveData`, `Quant`, `LogStep`, the `lat_S` leaves (the brief listed them; not reached in budget);
- ENGINE and ENGINE2 were not reread in full.
