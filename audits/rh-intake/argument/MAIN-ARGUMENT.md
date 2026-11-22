# The main argument, reconstructed from the Lean source

> **Status.**
> 1. This document gives a continuous mathematical account of the argument in the alpo.ge Lean tree (SHA-256 `9631b4f0…49c7fc`). The tree claims RH and GRH for Dirichlet L-functions.
> 2. It is a reconstruction by reading. Sixty-four reader agents each read one piece over nine rounds, and their nodes are cited in brackets, e.g. [LOCALDIV]. Nothing was compiled or run in Lean.
> 3. "Proved" means that a proof term exists in the tree. It does not mean the term was checked, or that its leaves were read.
> 4. Where nodes conflict, the later node and the correction lists in SUMMARY §5–§12 win. *(inferred)* marks an inference by a node or by me. "Not established by the reading" marks a gap the nodes leave open.
> 5. This document describes the argument. It does not vouch for it. §9 states what has and has not been checked; §9.4 lists the holes in the chain.

> **Notation** [ACCOUNT §1; CHBALANCE §1; SERVED §1]. The Lean reuses letters; this document does not.
>
> | symbol | meaning here |
> |---|---|
> | x; ε; b; a | the scale; the small parameter (never a character; the cyclotomic character is ω); e^{x^ε}; x·b |
> | Y; Y_{qd}; Y_g; Y_j | Landau window base [Y, Y^{3/2}]; the (q, d)-selection scale, Y_{qd} ∈ [x^{1/J}, x], log q ≍ Y_{qd}^{ε/5} [HOSTS §1(a)]; the level-prime scale (k·e^{x^ε})^8 [ORDER]; row-tower spaces |
> | χ_{−d} | (−d/·), the character of K = ℚ(√−d), d ≡ 7 mod 16 prime. Nodes writing χ_d mean the same character |
> | q; q_v; (p_j, q_j) | the auxiliary prime q ≡ 3 mod 8; a residue-field size (§7); the signature of W_j |
> | n; Φ; f; r | n = \|A\| where Gal(E/ℚ) = {±1}² × A and [E:ℚ] = 4n; Φ = Gal(E/K), the "places" ρ; f = \|Φ\| = 2n; r = k + m − 1 (the rank; COUNT, GERMJET write n) |
> | 2^{e₂}; e; i | the cyclic 2-power quotient of A; an odd distance on a Frobenius orbit; a Tate twist (§8) |
> | TT; a_t; t | tops, TT ⊂ A, x^{−ε/8}n/2 ≤ \|TT\| ≤ n, so \|TT\| ≈ n; a_t ∈ [a, a(1+x^{−17.5})] the weight of top t; t is a top, or in ranks the odd block length (N(j) = k + j(t+1)), which is also the Speh length of §8 [CONGMOD] |
> | partner(t, g); w_{j,ρ} | the place cconj + g + topPl(t) ∈ Φ met from top t by Frobenius g; the cap at ρ, level j: thick w ∈ [b, b+η+1] (a/w ≈ x), top w ≤ 2b′, thin w ≈ w″ |
> | X′; b′; w″; X″ | e^{x^{ε/3}}; a/X′; b′/(xn); a/w″ = xnX′ |
> | δ; δ_p | \|T2\|/n ≥ x^{−ε}, T2 the thick places; ≤ e^{−x^{ε_z/7}}, with dim EE = (1−δ_p)·dim HH |
> | U; B₀ | \|TT\|·m·b·δ/2 ≈ x^{2.5}b (budget U·x^{1/2+O(ε)} ≈ x³b); f·m·b·x^ε, the per-lift error unit |
> | ph; logΩ | y log y − y; γ + log(π/v) − L′/L(1, χ_{−d}) with v = rd_E/2 |
> | κ; I, I₁ | the similitude constant of ι; frame-row index sets (§7, RANK's κ, κ₁) |
> | 𝓛; BL; P; HH; H_B | Laplace transform (§1); Bost loss (§5.4); Selmer presentation (§8); the L² space (§3.1); the Bost scale x^{C_H}b (§5.3). Φ is only Gal(E/K) |
>
> *Sign of Ω.* COVOL writes the proved Chowla–Selberg identity as "−meanLog = γ + log(2π/√d) − L′/L", HEIGHT as "mean_ρ log(area(Λ^ρ)/π) = …". So logΩ = −meanLog in COVOL's sign; √d versus rd_E is a separate proved identity [COVOL §2; HEIGHT child 3].

---

## 1. The statement and the strategy

**Target.** Fix a primitive Dirichlet character ψ and the cyclic group ⟨ψ⟩ of order o. Put

$$G_z(y)=\sum_{n\le y}\Lambda(n)\Big(\frac yn-1\Big)-y\log y+(1+\gamma)y,\qquad g_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)\Big(\frac yn-1\Big)+y\,\frac{L'}{L}(1,\chi),$$

$$G_m(y)=G_z(y)+\frac{1}{3o+1}\sum_{\xi\in\langle\psi\rangle,\ \xi\ne1}\operatorname{Re}g_{\xi^*}(y),$$

where ξ* is the primitive character inducing ξ [LANDAU §1a]. These are Riesz-smoothed Chebyshev functions with their main terms removed. Every weight is positive. The tree proves that L(s, ξ) ≠ 0 for Re s > 1/2 and every ξ ∈ ⟨ψ⟩. It does so by proving, for every ε ∈ (0, ε₁) and on a sequence of windows [Y, Y^{3/2}] reaching to infinity, the one-sided bound

$$G_m(x)\le x^{1/2+(e_D+e_L+7)\varepsilon}.$$

e_D, e_L are exponents of the chain hypothesis `Tied`, not identified further. The glue quantifies over *all* real e_D, e_L, so the chain must force e_D + e_L + 7 > 0, or the statement would contradict ζ's zeros on Re s = 1/2. LANDAU §4 flags this; no node checks it.

**Landau on windows.** A one-sided bound on windows is enough [LANDAU §1b, §2b; REVIEW-ROOT]. The Laplace transform 𝓛(s) of G_m(e^u) is meromorphic in Re s > 0, with poles at the zeros ρ of the L(s, ξ), principal parts ∝ −1/(ρ(ρ−1)) summed with positive weights, so residues at a common zero cannot cancel. Its Taylor coefficients a_k at σ + iγ are integrals of G_m against the positive kernel u^k e^{−σu}/k!. For σ large in terms of the window ratio, this kernel concentrates on a log-window [u₀, (1+δ′)u₀]; σ must be large because outside the window only |G_m(e^u)| ≪ e^{2u} is known, so the tails must be exponentially smaller. A one-sided bound G_m ≤ Ce^{θu} on the window, together with positivity of the kernel, bounds |a_k(σ+iγ)| + Re a_k(σ) by roughly (σ−θ)^{−k}; the Re a_k(σ) is the price of one-sidedness. A zero with Re ρ > θ produces a nearest singularity, which forces larger coefficients; γ is chosen so that this pole is the *unique* nearest one, so poles on the circle cannot cancel. A real zero β produces a positive real residue and pushes G_m upward. Positivity of the averaged Dirichlet coefficients is not used. The reader judged this a correct theorem with a correct proof; at least eight sub-lemma bodies were not read (§9.1).

**Reduction.** All the RH-strength content sits in one inequality between a weighted count of inert prime powers and its main term; the rest is character bookkeeping (§2). With one copy per lift j, the count is

$$\mathrm{ASK}=\sum_{\text{tops }t}\ \sum_{j<m}\ \sum_{n}\Lambda(n)\big(1-\chi_{-d}(n)\big)\Big(\frac{a_t}{n}-w_{j,\mathrm{partner}(t,\mathrm{Frob}_n)}\Big)_+ .$$

The inequality is ASK ≤ MAIN + Err [COREGM; WRITEUP (12)].

**The idea.** The argument is a Stepanov-type argument [WHYHALF §2]. Its auxiliary object is a vector of algebraic numbers: periods of high-order Taylor jets of CM theta functions.
- **p-adic side.** At a prime p inert in K = ℚ(√−d), the CM curve is supersingular. In the height-two Lubin–Tate coordinate, a jet of order a is divisible by about p^{Σ_{e odd}(a/p^e − w)₊}. Summed over inert p ≤ a (Legendre; the caps cut further, at n ≤ a/w) with weight 2 log p, the uncapped part is Σ_n Λ(n)(1 − χ_{−d}(n))⌊a/n⌋, the inert part of Chebyshev's log a! = Σ Λ(n)⌊a/n⌋.
- **Archimedean side.** The same jet has size a!·Ω^{−a}, where Ω is a Chowla–Selberg period. log Ω already contains the split part of log a! through −L′/L(1, χ_{−d}). §4.6 computes this for one lift.
- **Comparison.** One copy is Chebyshev quality; the gain comes from multiplicity. The jets are chained through m ≈ √x theta lifts U(X_0) → … → U(X_m), each again an order-a derivative against its own kernel, so the divisibility recurs m times [CHAININD]. The comparison is made for lattices of forms, through Bost's slope inequality.

The result has the shape

$$\text{relative error}\ \approx\ \frac1m+\frac mx ,$$

relative to the trivial size ≈ x of G_m. It is minimised at m ≈ √x, which gives G_m(x) ≲ x^{1/2+O(ε)} [WHYHALF §0; ACCOUNT §0]. §6 derives it.

**Sizes** [ACCOUNT §1; ARCH §6].

| quantity | size |
|---|---|
| b | e^{x^ε} |
| weight a | x·b |
| tops a_t | in [a, a(1+x^{−17.5})] |
| host degree [E:ℚ] | 4n, with n ≈ x^{2+8ε}; f = 2n; \|TT\| ≈ n |
| m | ≈ x^{1/2−ε/16} |
| k | ≈ x^{9/2+10ε} |
| t | ≈ x^{398.5+O(ε)} (SUMMARY rounds this to x^{398}) |
| top column rank N(m) | ≈ x^{399} |

b makes every polynomial loss (≲ x^{800}) negligible. t is fixed by the definition r + t = 8fr + 4 + ⌈x^{377}⌉·nWv, nWv ≈ 10rf²k³L²/m [ACCOUNT §1]. The recorded constraints are t ≥ r + 5 (L6), 3m < t (GLOBALCHAIN) and twists i < t below VWin's x^{401} [CONGMOD]. Why the definition has this shape, no node says.

---

## 2. The analytic frame

### 2.1 The host field and why each auxiliary object is there

Every hermitian space lives over a CM field E, called the host. It is built afresh for each scale x [HOSTS §1(a), §2(c1)]. It is abelian, with Gal(E/ℚ) = {±1}² × A, and it lies in ℚ(ζ_{QS·q·d}), with [E:ℚ] = 4n. Each auxiliary object has one job:

- **K = ℚ(√−d)** supplies the CM curve whose σ*-functions build every theta kernel, the supersingular reduction at inert p, the factor (1 − χ_{−d}) in the count, and the L′/L(1, χ_{−d}) inside Ω [ARCH §1].
- **√−q**, with q ≡ 3 mod 8 and (−d/q) = 1. This sign separates the two kinds of inert prime [SERVED §0; SIGNAL §0].
  - *Signal* primes are inert in K and split in ℚ(√−q), with Frob = ((+1,−1), h).
  - *InertClass* primes are inert in both, with Frob = c·h.

  At a signal prime, complex conjugation c is never a power of Frob. So every prime of E⁺ above p splits in E, and the hermitian space is split (hyperbolic) at p.[^n4]
- **The 2-power layer.** A surjects onto (ℤ/2^{e₂+2})^×/±1, cyclic of order 2^{e₂} ≈ x^{2+8ε}. An inertClass prime has a split hermitian form iff the A-part h of its Frobenius has even order. The anisotropic ones (density ≤ 2^{−e₂} ≤ x^{−2}) are excluded by elementary counting, not Chebotarev [SERVED §0].
- **ψ** enters through the A-coordinate: A/A_0, for a cyclic subgroup A_0, is dual to ⟨ψ⟩, and TT carries shares 4/(3o+1) on the trivial A_0-coset and 3/(3o+1) on each other coset [CHBALANCE §2(a)] (§2.2).
- **The level primes g₀, g₁ ∈ [Y_g, 2Y_g]** [ORDER]. They give the Bessel–Poincaré series a level, the source of the level saving in near-orthogonality [PAIRB], and carry depth-zero types that force residual irreducibility on the Selmer side [TWIST]; the two bad sets are made disjoint by pigeonhole [ORDER].
- **T_u**, one prime per word u, a norm from K in a short window, sets the level of the source forms [ARCH §1].

(q, d) are chosen by a density argument over quadratic families (mean square over q, Markov, zero density in a box, Siegel) [PAIRGOOD §0]. For all y ∈ [Y_{qd}, Y_{qd}^A], every twist ξ·(·/q)^i·(·/d)^j with (i, j) ≠ (0, 0) has |g_χ(y)| ≤ y^{1/2+ε/2}. Here log q ≈ Y_{qd}^{ε/5} ≤ x^{ε/5}: far above log y, and below log X′ = x^{ε/3}, as ThinScales (§2.2) needs. This concerns short sums in a varying family. It is not GRH, and there is no circularity: `QH.pairEx` has no hypotheses.

### 2.2 The exact bridge ASK ↔ G_m

The bridge (`ch_balance`, `ch_core`) is a finite-group computation that holds exactly [CHBALANCE §0–2].

**Step 1 (exact identity).** Orthogonality on Gal(E/ℚ) gives ASK − MAIN = De, where

$$\mathrm{MAIN}=a\Big(\log a-1-\gamma+\frac{L'}{L}(1,\chi_{-d})-\operatorname*{mean}_{\rho\in\Phi}\log w(\rho)\Big)$$

and De = |Φ|^{−1} Σ_g Σ_ψ ψ̄(g)·w·G_ψ(a/w) is an expansion over all characters of the Galois group (G_χ is the g_χ of §1). The identity uses

$$\sum_n\Lambda\chi(n)(a/n-w)_+=w\,G_\chi(a/w)-a\,\tfrac{L'}{L}(1,\chi).$$

The identity holds with an *arbitrary* constant in place of L′/L(1, χ) (CHBALANCE oddity 1); the true value is pinned by the host clause `HostAddCharCompatible` [SERVED §0].

**Step 2 (which partners matter).** The partner place of a prime is fixed by its Frobenius, and caps are thick, top or thin (notation box). At top and thin partners the Riesz length is ≥ X′/3, and the effective PNT `ThinScales`, |G_χ(y)| ≤ y·e^{−cx^{ε/8}}, makes them negligible: de la Vallée Poussin with an in-tree zero-free region, for conductors up to e^{x^{ε/5}}. Exceptional zeros of the real characters involving q or d are excluded by host-selected zero boxes (`RealBox`/`GoodFor`: none with β > 1 − 1/400) [SERVED Part 2, §3].

**Step 3 (only signal primes reach thick places).** The partner of a top t at odd distance e is (IsSignal ∧ e odd, t + e·h). So only signal primes reach thick places, and **the x-scale part of ASK, which carries ψ, sits entirely on signal primes** [SIGNAL §0.5].

**Step 4 (averaging).** Average over u₀ ∈ A₀ and sum over tops. The 4 : 3 shares then become

$$\lambda(h)=\frac{3+1_{A_0}(h)}{3o+1}=\frac1o\Big[1+\frac1{3o+1}\sum_{j\ne0}\psi^j(h)\Big].$$

With uniform shares only G_z, and hence only ζ, would survive.

**Result.** The bridge gives

$$U\cdot\big[G_m(x)-\mathrm{Sig}_A(x)-4x^{1/2+\varepsilon}\big]\ \le\ \sum(\mathrm{ASK}-\mathrm{MAIN})+\frac{2|TT|mb}{x},\qquad U=\tfrac12|TT|\cdot m\cdot b\cdot\delta ,$$

Sig_A collects the 3o quadratic twists of ⟨ψ⟩ by (·/q), (·/d) and (·/qd), bounded two-sidedly at the single point y = x by host selection (`bdG`/`ValuesAtX`). U ≈ x^{2.5}·b uses |TT| ≈ n; the budget is U·x^{1/2+O(ε)} ≈ x^{3+O(ε)}·b. Every replacement error in the bridge is ≲ x^ε·log x relative to U. **The x^{1/2} comes only from Err/U** [CHBALANCE §2(c)].

### 2.3 What is counted and what is paid for the rest

ASK counts every inert prime, not only the informative ones [CHBALANCE oddity 2]. The gain side must therefore either deliver divisibility at a prime or charge that prime its whole ASK summand. The classification works as follows; the routes are explained in §4.5 [SERVED §0, §1.1, §2].
- **Orbit route.** Signal primes p ≤ X″ *and* even-order inertClass primes in [X′(1+Crρ), X″] receive the Hecke-free gain g₀⁺, a copy of their ASK summand, through `NoOperatorOrbitBound`. Their mass is ≈ x log x·U, far above the budget. SERVED calls this clause the real open child.
- **Hecke/colength route.** Even-order inertClass candidates (p < X′, ord h ≥ x^{ε/4}, Sig ≤ x^{−ε}, outside the band), on their good orbit representatives.
- **Bad orbits of kernel-served primes.** SERVED is ambiguous: its summary gives them g₀⁺ via the orbit route, its §1(b) via `UAt` on the Hecke side, and its charge table charges them as a dropped bucket (≤ 4x^{−1+ε}U).
- **Dropped primes** are charged their full ASK with gain 0: classes of small order (all anisotropic ones among them), the band around X′, the second kind, the high primes p > X″, and d. Each bucket costs ≤ x^{−1+O(ε)}·U. The high bucket is bounded directly (≲ x^{−25}U), so the share of thin partner positions is not needed.

A loss term LoP ≈ c·|TT|·m·b, x^{−1/2} of the budget, absorbs the per-prime digit-sum slack [WRITEUP (11)].

---

## 3. The objects

### 3.1 Three towers

All spaces are hermitian over E. They are unimodular at the base, with ranks fixed by k, m (even), t (odd), r = k + m − 1 and N(j) = k + j(t+1) [ARCH §2].

- **Column tower**, X_0 ⊂ X_1 ⊂ … ⊂ X_m. Each X_j is totally definite of rank N(j). Its forms are *algebraic modular forms*: functions on the finite set of lattice classes in the genus of X_j, valued in a weight representation. Integrality is taken in the Weyl-module (Δ) lattice. The level-j weight at a top place is (a_t, small…, −b_t, −w_1^{×(t+1)}, …, −w_j^{×(t+1)}), so **the same large entry a_t sits at every level**, and each lift adds a block at the cap weight w_j [CHAININD §1.1]. The p-adic divisibility lives on this tower.
- **Row tower**, Y_m, …, Y_0, of rank r + jt. Y_m ≅ X_⊥ is the orthogonal complement of an anisotropic vector in X_m (the nodes write X′ for this space). The bottom is Y_0 = X_0 ⊕ ⟨z⟩ ⊕ r_S hyperbolic planes, r_S = m/2 − 1, of signature (k + m/2 − 1, m/2), with a non-compact quotient and genuine L² automorphic forms. HH is the discrete-series, level-(g₀g₁) part of L²(U(Y_0)), of dimension D_all; inside it EE has dimension (1 − δ_p)D_all and carries the target lattice RR.
- **Layers**, W_1, …, W_m, of rank r and signature (k+j−1, m−j), inner forms of U(Y_0) at every finite place. W_m is definite and W_{m/2} has the signature of Y_0. Each is paired with a definite V_j of rank r + t. The layer lattices M_j are integral cusp forms on the Shimura variety of U(W_j). They supply the covolume of RR only through a determinant hypothesis (§5.2; H1), and their signatures are an input (H4).

### 3.2 Maps

- **Column steps** K_j [ARCH §4(a)]. They are given by

  $$K_j\varphi(c')=\sum_{c}|\mathrm{Stab}\,c|^{-1}\rho_j(c)\rho_j'(c')\cdot\mathrm{divDe}\circ\mathrm{unf}_j(c,c')\circ\mathrm{sharp}(\varphi(c)),$$

  where unf_j(c, c′) is **the Taylor jet at 0 of a CM theta function θ_{c,c′} attached to a pair of lattice classes**, ρ_j, ρ′_j are unitary determinant characters, and sharp, divDe are diagonal normalisations. The chain is col = K_{m−1}∘…∘K_0.

  *What θ_{c,c′} is, as far as the nodes say.* A theta function in matrix variables (an N(j) × N(j+1) matrix at each archimedean place) [HEIGHT §1(a)]. Its finite Schwartz datum is the indicator of the local lattice conditions given by (c, c′); its archimedean component is a Gaussian "vacuum" built from the period lattice of the CM curve [GLOBALCHAIN §1]. σ* (the reduced sigma function of a Δ = 1 lattice with CM by K) enters because θ_{L,L′}(Σ b_i z_i)/∏σ*(z_i) is integral at inert p in an orthonormal local basis: locally θ is a combination of prime-to-p translates of products of σ* [KERNELLAW §3(iii)]. The nodes do not write out the lattice summed over.

  *Column minors and weights.* The jet is paired against a product of column minors, one per column of the Young diagram of the level-(j+1) weight at each position s [HIGHERRANK §1.2]. So s carries ν₁(s) minors (the first-row length); at a top the overhang ν₁ − ν₂ (≈ a_t) is peeled into linear "top forms", leaving ν₂. This is the cap of §4.3, pinned by `LatTied` to the count's cap w, so "cap = weight" holds by definition plus the minor lemma [PAIRING §0.3]. NUMTEST4: det(Y)^m costs m, not its degree 2m.
- **Row descent** io_j : Mult(j+1) → Mult(j). It is tied by Petersson adjointness to a genuine theta lift. The composite is ι : (top forms) → EE.
- **Layer lifts** θ_j : (forms on U(V_j)) → (forms on U(W_j)). Each is a λ_j-similitude on Hecke parts, where λ_j is the Rallis θθ* eigenvalue. The descent ι is a κ·∏λ_j-similitude. There is one λ, shared by construction (`LevelLink` is `rfl`) [SEESAW §3].
- **Poincaré series** P_u : C_u → HH, P_u(T)(x) = Σ_{δ ∈ R_u(F)\G(F)} Ph_T(δx), over the Bessel subgroup R_u = U(X_0) ⋉ N. C_u ≅ the source space at level T_u. P_u* is the Bessel period map [PAIRB §0].
- **Bessel pairing** B_u : N_u → RR^∨, (B_uφ)(F) = ⟨sEE F, P_uφ⟩ up to a nonzero scalar and unitary changes of basis (`BesselId`) [WRITEUP S11].

### 3.3 The seesaw

The top period of the m-fold column lift is the codimension-one Gross–Prasad period ∫_{[U(X_⊥)]}(K_{m−1}⋯K_0 φ)|_{U(X_⊥)}·F. The live identity joining it to the bottom is `MIid` [SEESAW §0]:

$$\zeta_{u,t}\cdot\mathrm{Pt}_u(\varphi,F)=a_u\cdot\big\langle \mathrm{sEE}(V\,\Theta_t F),\,P_u(U_u\varphi)\big\rangle_{HH},$$

with V and U_u isometries, a_u ≠ 0, and ζ a unit at twisted tuples. SEESAW found a supplier: an honest m-step seesaw done two levels at a time (Bessel → Fourier–Jacobi → Bessel, since the codimension of X_j ⊂ Y_j alternates in parity), with every intermediate column level realised automorphically. It is conditional on its own hypotheses [SEESAW §0.3], and JOIN did not reach it from the root's producer, so its use on the live path is not established [JOIN §1d; H2].[^tiebm]

The seesaw is stated as **transport of linear relations**: a relation among top periods implies the same relation among bottom Bessel periods. So a_u exists but is never computed, and need not be. B_u is *defined* as the period pulled back along ι, and RR as the image ι(Λ) of the integral top lattice. Hence B_u(N_u) ⊆ RR^∨ is literally integrality of the column period, with no λ_j or a_u entering [SEESAW §4]. a_u is used only in `BesselId`, i.e. in the frame (§7, §9.3).

```
 COLUMN (definite; p-adic side)          ROW (descent)                       LAYERS (covolume side)
 X_m  rank k+m(t+1)  ⊃  X_⊥ ≅ Y_m ──── top Gross–Prasad period ────┐        V_j (definite, r+t)
  ↑ K_{m−1}  (jet of CM theta)          ↓ io_{m−1}                  │          │ θ_j  (λ_j-similitude)
  ⋮                                      ⋮                           │          ↓
 X_1  rank k+t+1        ⊂    Y_1                                     │        W_j : rank r, sig (k+j−1, m−j),
  ↑ K_0                                  ↓ io_0                      │              lattice M_j of cusp forms
 X_0  rank k (definite) ⊂    Y_0 (sig (k+m/2−1, m/2)) ⊃ U(X_0)⋉N     │        j = 1..m;  W_m definite
  │                                       ↑                          │
  │  N_u = 𝔭^{−sg}·NuLat_u                │ P_u (Poincaré series)    │   covol(RR) = κ^D·∏_j det θ_j (hypothesis, §9.4 H1)
  └──────── B_u = Bessel period  ──────→ EE^∨ ⊇ RR^∨ ←── RR = ι(Λ) ←─┘   ⇒ μ(RR^∨) via lcv(M_j)
         MIid:  ζ·Pt_u(φ,F) = a_u·⟨sEE(VΘF), P_u(Uφ)⟩      (seesaw, m steps, two at a time)
```

**Sources.** For each word u (a binary string of length k; |W| ≈ 3Γ²x^{C_F}, with Γ = e^{Cm⁵fx^ε}) the source is a lattice N_u = I_u·NuLat_u. Here NuLat_u ⊆ M_u is a sublattice of the integral source forms, and I_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋} rescales by the expected divisibility, with sg = Σ_{j≤m}(gain_j + F_j − E_j) [WRITEUP §1].

---

## 4. The engine: p-adic divisibility at inert primes

### 4.1 σ* in the Lubin–Tate coordinate

Let p ≥ 5 be inert in K. The CM curve then has supersingular good reduction. Its formal group is the height-two Honda group with logarithm Σ_j X^{p^{2j}}/p^j over ℤ_{p²} [LOCALDIV §1]. Rescale by ϖ with ϖ^{p²−1} = p. A derivative of order a at the CM point 0, i.e. n!·(coefficient) [LOCALDIV §1], of a series integral in the ϖ-rescaled Lubin–Tate coordinate then has valuation at least v_p(a!) − a/(p²−1), which is γ_p·a up to a digit sum, where

$$\gamma_p=\frac{p}{p^2-1}=\sum_{e\ \mathrm{odd}}p^{-e}.$$

This is the author's item 2. A single σ* is not integral in this coordinate. Its obstruction is a Dwork-type Gaussian. In one variable the self-term c·x^{p+1}/p survives, and the gain drops to a/(p²−1) [GAUSSCLASS §2(a)].

### 4.2 The Gaussian class, and why self-terms cancel at split hermitian places

The central structural statement says that the full higher-rank kernel lies in the Gaussian class: coefficient by coefficient,

$$\Theta=\sum_i p^{-i}\,hh^i\,g_i,\qquad hh=\sum_s u_s\sum_{a,b}S_{s,a,b}^{\,p}\,S_{s+1,a,b},$$

with g_i integral and S_{s,a,b} = Σ_l (−1)^l Z_{s−2l,a,b}^{p^{2l}} the twisted log series in the position variables Z_{s,a,b} (s a position on the Frobenius orbit, (a, b) a matrix entry). u_s = c for odd s and −σc for even s, c a single constant of the curve, σ the Frobenius of W(F̄_p) (not complex conjugation) [GAUSSCLASS §1]. It is proved through six links. GAUSSCLASS reconstructed each as mathematics but read the three arithmetic leaves only as statements; LEAVES later read them (`joint_integrality`; the one-copy fourth-power trick; `lamPos_of_posEmb`, whose content is the field `pos` of `CmpHyp`) [LEAVES §0].

1. exp(Σ ph(X_i))·Θ is integral in an orthonormal local basis at every inert p (one copy, 2×2, tensor power, then prime-to-p coset averaging).
2. At a split place the position variables form a unimodular hyperbolic pair over ℤ_{p²}. This is the only use of "split at p". At a place of E⁺ split in E the hermitian form is a duality between V_w and V_{w̄}. Position (v, s) is the embedding r_v·z^s, z = Frob_p·c, so even and odd positions carry the two sides: they are the two isotropic halves, and the dual-basis condition Σ_i σ^{2i}(ω_r ω*_{r′}) = δ_{rr′} makes the pairing unimodular [LEAVES L-B; HIGHERRANK §1.1].
3. Self-terms cancel by isotropy, leaving the polarisation Σ_e be(x_e, y_e).
4. Every biadditive hermitian be is ≃ G_ser(c, σc). This is the Dieudonné/Honda classification: H¹_dR of the height-two group is spanned by ℓ and the quasi-logarithm.
5. Trace duality for the unramified extension forces the coupling s ↔ s+1 and never s ↔ s.
6. Dwork: π^i/i! is integral.

The simplest instance was computed exactly [NUMTEST3]. Take E = ℚ(√−d, √−q), with one matrix entry Θ(z₀, z₁) = th0(z₀+z₁)·th0(c(z₀−z₁)). Here th0 is a normalised torsion translate of σ*, and c·c^σ = −1 at a served p [NUMTEST3 §1]. In orthonormal coordinates (a unitary change of variables with entries A, C) Θ(z₀, 0) = th0(Az₀)·th0(Cz₀), with

$$A A^{\sigma}+C C^{\sigma}=0\ \text{ at }p,\qquad |A|^2+|C|^2=1\ \text{ at }\infty .$$

The even-position direction is isotropic p-adically, so the two Gaussians cancel at p while Gaussian growth at ∞ remains: one function saturates the archimedean bound and carries the full p-adic gain, because the form is definite at ∞ and hyperbolic at p.

### 4.3 Adjacency, caps and minors

**Positions.** Positions s ∈ ℤ/n′ run along the Frobenius orbit z = Frob·c, where n′ = ord(h) is the orbit length (even at a served prime). Mod p, a level-e factor of the Gaussian couples position t to position t + e, the place Frob^e·t [HIGHERRANK §0(a)].

**The cap lemma.** Under the jet pairing, multiplying by a linear form is adjoint to a directional derivative of the operator polynomial. So each Gaussian factor forces one derivative in a fixed direction onto the column minors at the partner position, and two derivatives in one direction kill a minor. Hence there are at most min(a/p^e, w_{t+e}) factors of level e, with w_{t+e} the number of minors at the partner, i.e. its weight (§3.2) [HIGHERRANK §0(b); PAIRING §0.3].

**Legendre and Dwork.** These give the per-lift, per-prime gain

$$\gamma_p\,a-\sum_{e\ \mathrm{odd}}\min\Big(\frac{a}{p^{e}},w_{t+e}\Big)=\sum_{e\ \mathrm{odd}}\Big(\frac{a}{p^{e}}-w_{t+e}\Big)_+ ,$$

using max(A − w, 0) + min(A, w) = A (`ask_add_Mn`). With weight 2 log p per prime (Σ_{w|p} 2·lw·e_w = 2 log p), **this is exactly the ASK summand** 2 log p·Σ_{i odd}(a/p^i − w)₊ = Σ_{n=p^i} Λ(n)(1 − χ_{−d}(n))(a/n − w)₊ [WRITEUP S7; ACCOUNT §0.5]. At a thick partner, w ≈ b and a/w ≈ x, so the capped count is a Riesz mean localised at n ≈ x.

**Numerical evidence** [NUMTEST, NUMTEST2, NUMTEST3, NUMTEST4, SIGNAL §E].
- For ℘ (no Gaussian factor) the slope is γ_p to three decimals up to order 6000; for σ only 1/(p²−1).
- On the actual kernel at served primes the slope is γ_p to 0.0003, and at w = 0 the bound v ≥ v_p(a!) − (a−1)/(p²−1) holds exactly. The measured valuation falls below Σ_{e odd}(a/p^e − w)₊ by at most 0.98 (n′ = 2), 1.54 (n′ = 4, 0/800 mismatches against brute force) or 1.13 (two tops, 57 jets); the Lean's bound subtracts a loss term of this size [WHYHALF §3].
- Caps are charged per position and are close to tight; a shared budget predicts a loss of 12, and ≈ 5 is observed.
- Controls collapse the gain at split primes, at anisotropic inert primes (only 1/(p²−1)), and with scrambled jets (slope 0.0185).

### 4.4 Iteration over the m lifts

The iteration is an honest induction (`main_ind`) [CHAININD §0]. The induction hypothesis after j steps is only that the image equals ϖ^{(gains so far)}·G′, with G′ an *arbitrary* element of the level-j integral lattice Int_j, the target of lift j−1 and the source of lift j. The next one-step bound holds for every element of Int_j. So the induction is a composition of maps, each divisible on the whole integral lattice. The derivative order is not split among lifts: every level carries a_t again. Hence

$$\sum_{j=1}^m\mathrm{gain}_j\ \approx\ \sum_{j=1}^{m}\sum_{t\in TT}\sum_{e\ \mathrm{odd}}\Big(\frac{a_t}{p^{e}}-w_{j,t+e}\Big)_+ ,$$

with w_{j,t+e} the level-j cap at the partner position (about m times a one-level sum), minus automorphism denominators v_p(#Stab). Those are charged once per lift via Minkowski, are ≈ x^{402}, and are negligible next to b. "Multiplicity" means exactly this: the same primes divide each of the m lifts to order a. A normalisation error in one step would be multiplied by m, and nothing in the induction would catch it [CHAININD §0.5].

*Why the intermediate lattices cost nothing.* The composite's height is bounded by Σ_j log‖K_j‖², each norm taken between the fixed Fock norms of levels j and j+1 (§5.1), and Bost is applied only to the composite N_u → RR^∨. Each intermediate metric occurs once as target and once as source, so no covolume of Int_j appears *(inferred from HEIGHT §1(b), WHYHALF §1.5)*.

### 4.5 Two routes

- **Hecke/colength route** (kernel-served even-order inertClass places, p < X′, on the good representatives VV) [LOCALDIV; PAIRING; COLENGTH].
  - A Rallis-type commutation lets a level-0 Hecke operator move up the chain. This unlocks the larger bound γ_p·a at even-position tops, at a price p^{−Pr} per step (Pr ≥ 0 a Hecke normalisation exponent).
  - The colength τ of the Hecke image (a p^{⌈τ⌉} factor) removes that surplus again.
  - The net gain at each served prime is the prime-count summand ± O(1), via an injective pairing of tops (`kinkHH`).
- **Orbit route** (signal places p ≤ X″, where the ψ-part lives, and even-order inertClass places in [X′(1+Crρ), X″]; §2.3) [SIGNAL; ORBIT; JETA; SERVED §0].
  - `NoOperatorOrbitBound` bounds the m-fold chain directly on global kernel entries, delivering g₀⁺ with no Hecke operators and no colength (VV = ∅, τ = 0).
  - The local theorem is an LP-duality valuation argument. Each Gaussian factor x^{l^α}y^{l^β} costs one p, which is paid by l^α r_x + l^β r_y ≥ 1. A generic-frame reduction is done by Cauchy–Binet.
  - The charge Σ_e min(cap_e, A/p^e) is at least the true LP maximum, so it is conservative (0/4000 random violations).
  - The iteration `chain_ge` has the same shape as `main_ind`.
  - The lattice tie charges no Δ/∇ index: Δ = ∇* is proved in-tree, and the ∇-span is saturated.
  - NUMTEST3/4 tested only inertClass served primes, not signal places [SERVED §2].

### 4.6 A one-lift model computation

This is HEIGHT's reconstruction of "one lift is one Chebyshev identity" [HEIGHT §2(b); WHYHALF §1.1]. Take the jet J = D^aθ(0)/Ω^a at one top place, one lift, with cap w at its partner.

$$\text{archimedean:}\quad \frac1{n_{\rm Pl}}\sum_{v\mid\infty}\log|J|_v^2\ \le\ \mathrm{ph}(a)-a\log\Omega+\mathrm{poly}(x)\cdot La,$$

$$\text{p-adic:}\quad \sum_{p\ \mathrm{inert},\,w\mid p}2\,v_w(J)\log p\ \ge\ \sum_{n\le a/w}\Lambda(n)\big(1-\chi_{-d}(n)\big)\Big(\frac an-w\Big)_+-\text{loss}.$$

The product formula Σ_v log|J|_v = 0 makes the p-adic total at most the archimedean one. Both sides are squared norms, hence the weight 2 log p: Λ(n)(1 − χ_{−d}(n)) = 2Λ(n) on odd powers of inert p.

*Leading order.* Without caps the p-adic side is Σ_{p inert, p ≤ a} 2γ_p·a·log p ≈ Σ_n Λ(n)(1 − χ_{−d}(n))⌊a/n⌋ = log a! − Σ_n Λ(n)χ_{−d}(n)⌊a/n⌋, and the twisted sum is ≈ −a·L′/L(1, χ_{−d}) (Mertens for χ_{−d}). On the archimedean side ph(a) = log a! + O(log a), and the averaged Chowla–Selberg value of logΩ gives

$$\mathrm{ph}(a)-a\log\Omega=\Big[a\log a-(1+\gamma)a+a\,\tfrac{L'}{L}(1,\chi_{-d})\Big]-a\log(\pi/v).$$

With caps and y = a/w, the p-adic count is exactly

$$\sum_n\Lambda(n)\big(1-\chi_{-d}(n)\big)\Big(\frac an-w\Big)_+=w\Big[y\log y-(1+\gamma)y+y\,\tfrac{L'}{L}(1,\chi_{-d})\Big]+E(y).$$

Here E(y) = w·(G_z(y) − g_{χ_{−d}}(y)) in the notation of §1 *(my computation from the definitions)*. The bracket is the archimedean bracket minus a·log w; −a·log(π/v) and −a·log w are matched through log T_u (Count5, §5.4). So **the main terms agree identically**, and all content is in the errors. The split part of log a! is the −L′/L inside logΩ; its fluctuation is the host-selected `ValuesAtX` (§6).

*Precision required.* At a thick partner (w ≈ b, y ≈ x) the main term is ≈ b·x·log x and the signal is b·G(x), with target G(x) ≲ x^{1/2+O(ε)}. So the comparison must be right to relative x^{−1/2+O(ε)} (MAIN ≈ x^{1/2} × budget [ACCOUNT §2]), which one lift cannot achieve (§6).

---

## 5. The archimedean side and the slope inequality

### 5.1 Heights

**The bound.** The archimedean height of B_u is bounded by submultiplicativity along the chain [HEIGHT §0]:

$$\mathrm{htMap}(B_u)\le\sum_j\log\|K_j\|^2+\log\|P_tL\|^2-\log\kappa-\sum_j\log\lambda_j .$$

**The jet-step norm.** A Cauchy estimate in Fock space for Taylor jets of entire functions with Gaussian growth gives

$$\log\|K_j\|^2\le\sum_\rho\big(\mathrm{ph}(\nu_{j\rho})-|\nu_{j\rho}|\log\Omega_\rho\big),\qquad \mathrm{ph}(y)=y\log y-y .$$

The conjugate periods Ω_ρ genuinely differ, since they come from different ideal classes. Only their mean enters, and the averaged Chowla–Selberg identity proved in-tree gives

$$\operatorname*{mean}_\rho\log\Omega_\rho=\log\Omega=\gamma+\log(\pi/v)-\frac{L'}{L}(1,\chi_{-d})$$

(sign as in the notation box). This is where the split part of log a! goes (§4.6) [WHYHALF §3.3]. The bound has no slack in the coefficients of ph or logΩ; NUMTEST3 found it saturated to within 5.3 in log.

**Why only m·ph(a_t) survives.** The height contains ph(ν) for *all* weight entries, including the k entries of size ≈ w and the t+1 blocks, not only a_t. These are removed by the theta scalars: −log λ_j sits in the height, L6 bounds log λ_j below by a hook product Σ_ρ logHook_{jρ}, and `weight_height_sum_le` gives Σ_i ph(ν_{jρi}) − logHook_{jρ} ≤ ph(a_t)·[ρ ∈ TT] + eE. So per (j, ρ) the hook product cancels the factorial growth of every entry except **one** ph(a_t) at tops, leaving m·ph(a_t) over the m levels. With `weight_sum_eq` (Σ_i ν_{jρi} = a_t[ρ ∈ TT] + k·w + δ_{jρ}) the height collapses to Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + O(|TT|·a·La + m·B₀x^ε) [HEIGHT §1(a), §2(b) end]. The cancelled terms are ≈ k·f·b·x^ε per level, so L6 must be sharp to relative x^{−4}.

**Rallis scalars.** λ_j is the Rallis inner-product eigenvalue. An exact product formula is proved and only its hook products are kept as main term; the L-value is taken deep in the convergent range, where |L^S| ≥ e^{−2rf} is elementary, so the loss is poly(x) ≪ b [L6 §0]. This rests on seven named literature theorems, each supplied in-tree. λ_j has no finite-place counterpart [JOIN oddity 5].

### 5.2 The target lattice and its covolume

RR is glued place by place: at y it is ι(μ(y)) applied to the projection of the integral lattice onto the type-μ(y) part (author's item 15) [CONGMOD §2a]. The covolume bound uses det ι = κ^D·∏_j det θ_j. **This is a hypothesis of `BoundsMu`, not a derived fact:** SEESAW infers it from the similitude clauses `l1c`/`l1d`, and no derivation, nor any theorem factoring ι through the θ_j, was found [ARCH §7.1; SEESAW §3] (hole H1, §9.4). Granted it,

$$\mu(RR^\vee)\le\operatorname{meanLog}\kappa+\sum_j\frac{\mathrm{lcv}(M_j)}{D}+2F_o+(\text{index and congruence terms}) .$$

**The layer covolume** is [COVOL; VOLUME; HS]

$$\frac{\mathrm{lcv}(M_j)}{D}\le(p_j-q_j)\sum_\rho w_{j\rho}\log\Omega+C\cdot B_0\log\log x,\qquad p_j-q_j=k+2j-1-m .$$

It is proved by descending induction over layers, from the definite top W_m through deep covers, using an effective arithmetic Hilbert–Samuel bound at one tensor power and `FlatDegree`: flat sections on U(p, q) have arithmetic degree (p − q)/2·logΩ + q(…), Chowla–Selberg again. **The flat directions are exact; the error is ∝ q ≤ m.** The main term comes from `FlatDegree`; the uniform volume theorem enters only through an error budget and has no main term of its own [VOLUME §0.1, §0.5].

**The index at the gain primes** of θ_jT_j in M_j is bounded by derivative content in the *layer* weights only, F = (k−1)Σw/(p²−1), which enters once on each side and cancels. The a-sized factorial is counted only in the column steps [JOIN §2d].

### 5.3 Bost's inequality, rank-free

The joint map ⊕_u B_u : ⊕N_u → RR^∨ satisfies [RANK; WRITEUP (5)]

$$s-\log|W|-(1-\delta_p)^{-1}\big[4u_F\log(1+H_B/u_F)+(\eta+4\sqrt{\bar e})H_B\big]\le\mu(RR^\vee),$$

where:
- s = Σ_u d_u(μ(N_u) − h(u))/Σ_u d_u is the mean source slope net of heights;
- u_F is the Harder–Narasimhan spread;
- H_B = x^{C_H}·b is the Bost scale;
- η, ē are frame-tightness parameters, with (η + 4√ē)·x^{C_H} ≤ 6.

The proof is a layer-cake over HN filtrations with Bost's slope inequality and a dimension-free frame lemma; no rank or degree error appears. The frame carries no metric content (its changes of basis are free invertible matrices) and yields only *robust near-surjectivity* of the joint period map, which is why non-vanishing (§7) is needed.

### 5.4 The chain

In one display [WRITEUP §2]:

```
ASK − LoP ≤ Ga                                                      (gain ≥ count − slack)
Ga ≤ μ(N_u) − μ(M_u) − Fo + Ee(u) + Lo5(u)                          (rescaling + colength)
   ≤ [μ(N_u) − h(u)] − μ(RR^∨) + MAIN(u) + E_DIV − μ(M_u) + Ee + Lo5   (DIV: μ(RR^∨) + h − Fo ≤ MAIN + E_DIV)
   ≤ [μ(N_u) − h(u)] − μ(RR^∨) + Σ_t m(ph(a_t) − a_t logΩ) − ΣA·Λ5 + m·ΣA·lg + errs   (source floor; Count5 on log T_u)
averaged over u:   Ga ≤ s − μ(RR^∨) + Main + errs                     (key_identity5)
                      ≤ log|W| + BL + Main + errs                     (Bost:  s − μ(RR^∨) ≤ log|W| + BL)
∴  ASK ≤ Main + ErrX5at.
```

Here ΣA = Σ_t a_t; Fo is the inert F-index ≈ Σ(k−1)w/(p²−1) over p ≤ X″; Ee (≈ m·ΣA·lg) and Lo5 are a per-lift term and small losses; E_DIV is DIV's error; lg, Λ5 are log-level constants matched by Count5; La ≤ 2x^ε; BL is the Bost loss of §5.3 [ACCOUNT §2].

Here

$$\mathrm{MAIN}(u)=\sum_t\big[m(\mathrm{ph}(a_t)-a_t\log\Omega)-a_t\log T_u\big],\qquad \mathrm{Main}=\sum_j\sum_t a_t\Big(\log a_t-1-\gamma+\frac{L'}{L}(1,\chi_{-d})-\operatorname*{mean}_\rho\log w_{j\rho}\Big).$$

Count5 needs log T_u to match Σ_j mean_ρ log(w_{jρ}v/π) + m·lg to within ±La.

**The cancellations** [ACCOUNT §0.3; WRITEUP S16].
- μ(RR^∨) enters both Bost and DIV with coefficient +1 and cancels. Only an *upper* bound on it is used (the covolume bound of §5.2, needed to relative x^{−4}); a two-sided estimate is never needed.
- F_o (`foTie`), the m·lg term of Ee (against Count5) and log(π/v) (`key_identity5`) cancel syntactically.
- The large logΩ terms cancel: +Σ_j(p_j − q_j)Σ_ρ w·logΩ from the covolume against −Σ_ρ(a_t + k·w + δ_{jρ})·logΩ in the height. They leave −m·a_t·logΩ, because

  $$\sum_{j=1}^m(p_j-q_j)=mk\quad\text{exactly},\qquad |p_j-q_j-k|\le m-1 .$$

  Each layer's logΩ term is ≈ k·f·b·|logΩ| ≈ x^{6.5}b against a per-layer allowance B₀ ≈ x^{2.5}b; summed over the layers, ≈ x^7 b against the budget x³b. Either way covolume and L6 must be right to relative x^{−4} [ACCOUNT §0.3, §3(ii)].
- Seventeen sign and direction checks pass [WRITEUP §3].

**Precision-critical hypotheses** [ACCOUNT §0.3–0.4].
1. Covolume (B), and height (C) through the L6 hook bound: relative **x^{−4}**.
2. Count5: log T_u to ±La, relative **1/m** (a prime in a window of relative width 1/(fk)).
3. Bessel-frame tightness: **η ≤ 6x^{−C_H}**, with x^{C_H}b at least the HN spread.
4. Two-sided, from host selection: `ValuesAtX`/`bdG` at the point x, and `ThinScales` (§6).
5. Satisfiability: **Ga − ASK ≲ budget**. The Lean uses only Ga ≥ ASK − LoP, but Ga and the colength term can each be ≈ x^{1/2} × budget. If Ga exceeded ASK by more than the budget, the chain would force G_m(x) ≤ −x^{1/2+δ} on all windows, contradicting G_z = Ω±(x^{1/2}): the slope-side hypotheses would be false for the real lattices. ACCOUNT could not verify this; the later node PAIRING §0.1 settles it on paper for the Hecke-route tops (τ cancels the surplus exactly). It is not in the Lean (H5).

---

## 6. Why 1/2

**The error terms.** The conclusion's error ErrX5at splits into two families at the budget [WHYHALF §1.2].

- **One-off (boundary) terms**, each ≈ |TT|·a·x^ε, one whole copy of the per-lift signal: the precision of the prime T_u (Count5); DIV's top-place terms, m-independent because b′ = a/X′; the floor on the slope of the level-0 source lattice; the HN spread u·log(1 + H_B/u) in Bost.
- **Per-lift (interior) terms**, each ≈ B₀ = f·m·b·x^ε, **which contains the factor m**: the layer covolume error ∝ q_j ≤ m; the logΩ residual from |p_j − q_j − k| ≤ m; the congruence allowance η_j; the local error E_j. Summed over m lifts, m·B₀ ∝ m².

**The balance.** Dividing by U = |TT|·m·b·δ/2 [WHYHALF §1.3; `SizeWindows`, `GrowthSizeBound`]:

$$G_m(x)\ \lesssim\ x^{O(\varepsilon)}\Big[\frac{2a_E}{m\,b\,\delta}+\frac{4nm}{|TT|\,\delta}+\frac{2k}{n|TT|}\Big]\ \lesssim\ x^{O(\varepsilon)}\Big[\frac xm+m+\frac{k}{n^2}\Big].$$

The second step uses a_E ≤ 2xb (`SC:53-58`; the nodes do not describe a_E further), f = 2n, δ ≥ x^{−ε} and |TT| ≈ n [WHYHALF §1.3]. The windows x^{1/2−ε} ≤ m ≤ x^{1/2+ε/2} and k ≤ n²x^{1/2−ε} hold each bracket at √x. With m = 1 the bracket gives the trivial bound x^{1+O(ε)}, Chebyshev quality *(inferred; the tree never instantiates m = 1)*.

**Stepanov.** Schematically, ℓN ≤ D with D = ℓq + O(q) + O(ℓ²), so N ≤ q + O(q/ℓ) + O(ℓ) and ℓ ≈ √q. The correspondence [WHYHALF §2]:

| Stepanov | here |
|---|---|
| points | served (signal) inert primes, weighted at scale x |
| vanishing order ℓ | m |
| auxiliary polynomial | the joint Bessel period map on N_u |
| degree | the product formula: Bost, height, covolume |
| one-off degree ≈ q | the four boundary terms |
| ℓ² derivative overhead | m·B₀ |

One difference: in Stepanov the cap ℓ ≲ √q is also what makes the linear system solvable. Here non-vanishing costs only a polynomial relation k ≳ m⁵·f·log b, which the parameters absorb. **The cap on m is the growth of the per-lift error, not non-vanishing** [WHYHALF §2]. Non-vanishing does fix the host: with f = 2n, k ≳ m⁵·f and k/n² ≲ m force n ≳ m⁴ ≈ x², which explains n ≈ x^{2+8ε} *(the review's observation, REVIEW-MAIN-ARGUMENT A3)*. The tree also assumes m⁴ ≤ f directly (`SLN:36`).

**Sharpness: the conceptual question.** G_z = Ω±(x^{1/2}); the review adds that G_m(x) ≥ c√x then occurs in every window, where the chain must be tight to x^{o(1)} [REVIEW-MAIN-ARGUMENT A4]. So some per-lift loss must truly be ≍ m, not merely ≤ m: a per-lift cost independent of m would prove ψ(x) = x + O(x^δ) for every δ, which is false [WHYHALF §0.5 *(inferred)*]. The growth is not a removable inefficiency; it is where G_z = Ω±(x^{1/2}) shows up. The reading locates it in the layer signatures (k+j−1, m−j), with q_j up to m, which are an input (§9.4 H4). Which inequality is tight, and why an m-fold Bessel period needs targets with q up to m, is not established [WHYHALF §6.7]. The satisfiability condition of §5.4 (item 5) is the same phenomenon from the other side.

**Chebyshev.** Chebyshev's method fails beyond constants: no multiplicity, an auxiliary integer not supported on the counted primes, divisibility bounded but not computed. Here m supplies multiplicity, and the main terms are exact [WHYHALF §3]: Legendre/LT divisibility to O(1) per prime, exact caps, the split half via Chowla–Selberg, flat covolumes, the Fock coefficients, the bridge identity.

**One- and two-sided ingredients.** One-sided, in the direction consumed: divisibility (the truth exceeds it in rank one, NUMTEST2), heights and covolumes, L6 (sharp to x^{−4}), Bost, and the conclusion (as Landau needs). Two-sided, from host selection: |g_χ(x)| ≤ x^{1/2+ε} at the point x for the (·/q), (·/d), (·/qd)-twists of ⟨ψ⟩, and ThinScales. The quadratic twists' fluctuation is not cancelled by the method; it is placed in the choice of (q, d) [WHYHALF §3; ACCOUNT §0.5(vi)].

---

## 7. Non-vanishing

**Why it is needed.** If the periods B_u vanished, or the joint map fell far short of surjective, Bost's inequality would say nothing about the primes. The frame hypothesis excludes this: if every B_u = 0, its rank bound contradicts (1 − δ)·|I ⊔ I₁| ≤ |I|, with I the target rows and I₁ the padding rows (HH outside EE), δ tiny [RANK §0]. The frame inputs also force D_all > 0 and some B_u ≠ 0, so the degenerate "stand-in" row records in the tree cannot be the live one [JOIN §1c]. The frame in turn rests on "Theorem S", which has two halves.

**Near-orthogonality** [PAIRB; COUNTS; THMB; THEOREMS]. The Gram kernel K(u, u′) = (c_uc_{u′})^{−1/2}P_u*P_{u′} has off-diagonal squared Hilbert–Schmidt norm ‖K(u,u′)‖²_HS ≤ (1 + b^{−6})·d_ud_{u′}/D*, the value for random subspaces, and ‖K(u,u) − 1‖²_HS ≲ d_u/Γ. This `TheoremSSelected` is proved only *conditionally* (`theoremS_selected_of_loops`) [RANK §0; PAIRB §1]. It is the author's "relative trace formula" (item 16), done by a **double unfolding of Poincaré series** with no spectral decomposition, so the continuous spectrum never appears. The savings are:
- identity-orbit terms: an exact volume identity and Schur orthogonality, ∫HS² ≤ 1/formal degree;
- non-generic terms: sublattice counting, q_v^{−(k−2r_S−5)} (q_v a residue-field size, r_S = m/2 − 1);
- second-type terms: a character-sum cancellation on a hermitian quadric [COUNTS correcting PAIRB];
- corank-s terms, s ≥ 2: mainly the level factor (2/g)^{(s−1)kf}, with g ≥ Y_g a level prime;
- the Gauss-sum matrix: Gelfand–Graev multiplicity one.

The tight comparison 2^{−k/2}e^{Cm⁵f log b} ≤ b^{−14} is what fixes k ≈ x^{9/2+10ε}.

**The exponentially precise dimension count** [COUNT; SLEAVES; FORMULAGAP; GERMJET]. D_all = dim HH is a limit-multiplicity count for a very regular discrete series of U(k + r_S, r_S + 1)^f in L² of a non-compact quotient:

$$D_{\rm all}\le(1+\eta_1)D^*,\qquad D^*=\text{formal degree}\times\text{covolume},$$

with relative error e^{−rf log r/16} (COUNT's n is the rank r), uniformly in rank. The smallness of δ_p (`LinkIRR`) is also supplied only conditionally, from a row count [RANK §0]. It is not a trace formula over conjugacy classes: R(φ_e) is an exact orthogonal projection onto cusp forms (Schur orthogonality for integrable discrete series), and its kernel Σ|F_i(x)|² = Σ_γ φ_e(x^{−1}γx) is bounded pointwise region by region (unipotent near terms, a Siegel mean-value thin part, a sup-norm bound in the deep cusp).

The key analytic input is a **compression formula** for lowest-K-type matrix coefficients of non-holomorphic discrete series, c_λ(z) = ∏_iΔ_i(z)^{−s_i} (Δ_i the leading principal minors). It is proved via Schmid's first-order system and jet uniqueness (`germ_jet_zero`, read and found correct, needing only a Harish-Chandra gap larger than twice the rank). It reproduces (cosh t)^{−m} on U(1,1) and the classical holomorphic U(2,1) value, and passes independent checks on the middle series of U(2,1). The readers did not find it in the literature; it is not Knapp–Wallach. The Harish-Chandra gap it needs, ≈ x^{110}, is met with ≈ x^{1300}, counting only opposite-sign pairs.

---

## 8. The Galois-theoretic inputs

**Where congruence modules enter.** At *twisted* places (every prime below X″, the whole gain range) RR is a projection onto a Hecke-eigen type part Z_j ⊂ forms on U(V_j), and the dual index of the projected lattice T_j is bounded by Hida's congruence module len[Pr_Z L : L ∩ Z] [CONGMOD §0]. This error sits inside DIV's per-lift allowance (the m-family).

Z is the space of theta lifts whose A-parameter contains a Speh block μ⊠S_t, t the block length of §3. Their Galois representations are ρ ⊕ χ₁ ⊕ χ₁ω^{−1} ⊕ … ⊕ χ₁ω^{−(t−1)}, with ω the cyclotomic character [LINKN §0; author's item 8: π ↦ π ⊞ μ_j[t]].

**Congruence ≤ Selmer.** This is the Ribet–Wiles direction, made quantitative by a Fitting-ideal determinant lemma. The key input `NoChiOff` says no form outside Z contains χ₁. It is proved by a Galois-side rank/weight count [GALREP], which is not the deep input: the converse-theta content sits in `ConclusionZ` and the datum field `D7.Z_tie`, both unread. Purity is used inside `ConclusionG6` although `Row0b` has no purity clause; its source is untraced [GALREP §4; SUMMARY §12]. The bound has three blocks:
- the ρ-block: Bloch–Kato Selmer of ρ⊗χ₁^{−1};
- the c = 1 block: v_l(h_E);
- the c ≥ 2 blocks: Ш¹(E, ℚ_l/ℤ_l(−i)), i = c − 1.

**Killing the ρ-block** [KILLAT; ORDER]. The ρ-block is killed by twisting through a finite multivariable tame tower O[(ℤ/l^M)^{2R}] with Chebotarev-chosen auxiliary primes. The Selmer module has a square presentation P, and the length at ψ equals v(ψ(det P)). Killing the residual Selmer group gives det P a unit coefficient in low degree. Neither weak Leopoldt nor an infinite Iwasawa module is used.

This is a **two-pass construction**: pass 1 is untwisted, a seed (Q, k, ψ) is chosen from its export, and pass 2 rebuilds with twisted types under `SameExport`, which keeps ρ_s, χ_s, the theta and Bloch–Kato data identical. The archimedean constants are fixed before the twist datum, which closes the defect TWIST had raised [ORDER].

**Residual irreducibility** at every l comes from the prescribed depth-zero types at g₀, g₁ [TWIST].

**The Ш bound** [VWIN; ONECHARU; RT3; MODU3; PATCH; FINEND]. The bound needed is

$$\sum_l\log l\sum_{0<i<t}\mathrm{len}\,Ш^1(E,\mathbb Q_l/\mathbb Z_l(-i))\le\sqrt b,$$

VWin states it for all twists i < x^{401}. Crude bounds do not suffice: the tree's `LemmaK` gives exp((2kn)^C log disc), far above e^{x^ε}; Brauer–Siegel controls only h_E; and the plus parts would need lower bounds for Borel regulators, which are not known [ONECHARU §0, §2a.4]. The proof is therefore R = T-type on the deformation side.
- Ш embeds in first-order deformations of Ψ ⊕ 1 ⊕ Ψ^{−1}.
- A graded commutative-algebra inequality bounds len Ш by 2Σ v_l(tr ρ(σ) − t) over automorphic or endoscopic points. Uniformity in l comes from one integer NN.
- The modularity input is residually reducible ordinary automorphy for U(3): Skinner–Wiles extended to n = 3, with a Chenevier determinant ring and Taylor–Wiles patching at nice primes. The seed exists unconditionally (an Eisenstein congruence for n = 2, an adjoint lift for n = 3).
- At reducible nice points the patching rests on a new local model, a quotient of O[[X, M]]/(Y·M) with two big components, one reducible and one irreducible and determinantal. It requires g² + e′ ≤ D₀ (g the rank of the off-diagonal Selmer group, e′ the reducible-locus directions used, D₀ a local dimension), derived from a Greenberg–Wiles bound by an unread argument [PATCH §0].
- Finiteness is proved for the torus-invariant subalgebra (`FinEnd`). Adjoint vanishing uses `regDet` instead of an enormous-image hypothesis.

A consequence would be a polynomial bound on plus parts of K_{2k}(O_E). This is the "weakening of Vandiver" of the author's item 17.

**Galois representations** (`Row0b`) [GALREP] come from descent to unitary groups, an Eichler–Shimura-type construction in odd rank (Lefschetz proved in-tree), a stable-range theta lift to odd rank (replacing the eigenvariety parity trick), and Arthur–Clozel base change. The statement is weaker than Chenevier–Harris/Caraiani: WD matching away from l only for abelian N = 0 parameters, and no purity clause (though purity is used downstream). It is not circular: an import closure of 66,168 files has no self-reference.

---

## 9. What has and has not been checked

### 9.1 Step by step

"Read to" levels: **C** = down to classical statements; **N** = to a named new idea; **S** = statement or top level only.

| step | read to | numerical check | main unread items |
|---|---|---|---|
| Windowed Landau | C (correct theorem) | — | ≥ 8 bodies (`landau_tails`, `_nearest`, `_pole_asym`, `_cauchy`, `_growth_contra`, `poleData_char` past l.175, `Gchi_growth`, `windowHyp_of_rpow`); whether `ChainTied` forces e_D + e_L + 7 > 0 [LANDAU §4–5] |
| Bridge ASK ↔ G_m | C (exact identity) | — | `TwistForm` definition; existence of TT with exact shares |
| Hosts, (q, d), ThinScales | C | — | bodies of `stage1`/`stage2` (density), `levelData`, `classSel` |
| Gaussian class of the kernel | C, six links; leaves in LEAVES | NUMTEST3/4, LEAVES (NormRel to T^{260}) | `baseChange_preserves_unitary_of` (admitted + RestBeta + RestGc ⇒ class); `CmpHyp.pos`. (`restGc` read in full; `HhDecomp` proved; one-copy step confirmed) |
| Cap lemma, minors | C | NUMTEST4 (det^m costs m) | the coupled-overhang case (untested) |
| Iteration over m lifts | C (honest induction) | none for a composite of two lifts | — |
| Orbit route (signal p ≤ X″; even-order inertClass in [X′, X″]) | N (LP duality) | JETA 0/4000; two-tops −1.13 | `orbitIdentity…` body, `latS`/`latT` leaves; the supplier of `OrbitsWithoutOperator` [SERVED child 1] |
| Hecke/colength route | C | COLENGTH hand computation; COUNTS Smith forms 0/24 | `admB2` per-edge rank bound partly |
| Seesaw `MIid` | N (m-step transport of relations; supplier conditional on its own hypotheses) | — | `pins_finiteIntegrals`; whether the root's MIstar2 producer reaches it [JOIN §1d] |
| Heights (Fock, Chowla–Selberg) | C (proved) | Fock bound within 5.3 (NUMTEST3) | `normalisedFamily_*` |
| L6 (Rallis) | C, 7 premises | — | several sub-suppliers |
| Layer covolume | N (effective HS, flat sections) | — | `ThmB`, point heights; the det ι factorisation (H1); the signatures (H4) |
| Layer index at gain primes | N (depth ≤ F + err) | — | `MuDef` supplier: Tw = {resChar ≤ X″} ∪ {d, g₀, g₁} [JOIN child 1] |
| Bost/HN frame | C (correct theorem) | — | `slope_inequality_mean`, `FrameLA1` bodies |
| Near-orthogonality | N (double unfolding; Theorem S and `LinkIRR` proved conditionally [RANK §0]) | COUNTS model check | local defect masses (partly), `IdZero` |
| Dimension count | N (compression formula) | FORMULAGAP hand checks | near/far/deep/flag lemma bodies |
| Congruence ≤ Selmer, KillAt | N | — | Wach-module lemmas; `exists_levelB2_carried_of_levelB1`, `nonempty_seed_of_kept` |
| U(3) R = T, patching | N (determinantal model) | RT3 toy cases | `HasAut`, derivation of g² + e′ ≤ D₀, `core_o_of_literal_automorphy_n` |
| Row0b | N | — | Ferrero–Washington, Hida control, Eichler–Shimura construction (statement level); `ConclusionZ`, `D7.Z_tie`; the source of purity in `ConclusionG6` |
| Sizes | C | — | — |

### 9.2 Where the argument exceeds the published literature

Each item names the new idea the Lean uses.

1. **Rank-uniform limit multiplicity with exponential precision** [COUNT; FORMULAGAP]: an exact cusp-form projection by Schur orthogonality, plus a closed compression formula for lowest-K-type coefficients.
2. **Near-orthogonality of Bessel periods to relative b^{−6}** [PAIRB; COUNTS; THMB]: double unfolding, with savings from counting, level, and a Gauss-sum cancellation on a hermitian quadric.
3. **p-adic divisibility of high-order jets of higher-rank CM theta kernels** [GAUSSCLASS; HIGHERRANK; JETA]: the polarisation of log σ* as the unique hermitian Dieudonné pairing; isotropy at split places; the cap lemma for column minors. The method is recognisable; the statement was not known to the readers.
4. **Selmer bounds uniform in l for weights up to x^{401}** [ONECHARU; MODU3; PATCH]: Skinner–Wiles for U(3) with patching at reducible nice points via a determinantal local model.
5. **Selmer killing at finite level** [KILLAT; ORDER]: a square presentation over a finite tame tower, plus the two-pass construction.
6. **Residual irreducibility at all l** [TWIST]: depth-zero types at pigeonholed level primes.
7. **Galois representations** [GALREP]: the stable-range theta lift replacing the parity trick; the statement is weaker than the literature's.
8. **Uniform arithmetic volume and covolume bounds on varying Shimura varieties** [VOLUME; HS]: an effective finite-level Hilbert–Samuel bound and a structural intersection formula (`ThmB`); weak but sufficient.

### 9.3 What remains conceptually unclear

- **Why the per-lift error must grow with m** [WHYHALF §6.7; SEESAW §3]. See the sharpness paragraph of §6 and hole H4. WHYHALF calls this the conceptual heart of "why 1/2".
- **How the towers are joined** [ARCH §7.1, §7.7; SEESAW §3]. See hole H1. In addition, nobody showed that the layer index matches the lift index one for one.
- **The seesaw constant** [SEESAW oddity 3]. a_u is existential and depends on the word. Whether the frame needs it uniform, i.e. why near-orthogonality of the P_u transfers to B_u, was not checked.
- **The twisted-place set** [JOIN §2c]. See hole H3.
- **Dimensions and level structure** [ARCH §7.3, §7.5]. The ratio of the two d_u's (dim Mram versus dim Mu0) is not stated; Mram as "new at T" is inferred.
- **Design choices** [WHYHALF §6.1, §6.3, §4]. Why the weight is exponential rather than a large power of x; why orbit length n′ > 2 is needed; why the shares are 4 : 3 (any positive perturbation would do for Landau); why t has the shape of §1.
- **Behrend** [WHYHALF §6.6]. `BehrendSets` plausibly chooses the thick set T2; not traced to the live path.

### 9.4 Holes in the chain

Hypotheses with no supplier found, or suppliers not traced from the live path (after REVIEW-MAIN-ARGUMENT A2).

- **H1. The determinant identity.** The final chain needs μ(RR^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + …, i.e. det ι = κ^D·∏_j det θ_j. It is a hypothesis of `BoundsMu` (SO:31-41), inferred by SEESAW from `l1c`/`l1d`; no derivation was found, no theorem factors ι through the θ_j, and the supplier of `l1c` is untraced [ARCH §7.1; SEESAW §3]. *Status after NODE-DETSIG: supplied on the live route.* `IndefSide.boundsMu` gets it from the proved linear-algebra lemma `SpecDet` (read): ι is a (κ·∏_jλ_{j,p})-similitude on each Hecke part p, θ_j a λ_{j,p}-similitude on the matching part, and matching parts have equal dimension. The reason is not a factorisation of ι through the θ_j: both sides carry the same partial L-value L^S((1+t)/2, B⊗μ_j^{−1}) on each part (Rallis inner product, same rank gap t). At the base place ι is the identity by choice of coordinates, and at v ≠ v₀ the EE metric is defined so the ι side holds; the height side uses the same metric. Content rests on three inputs not read to the bottom: the two Rallis-type theorems `AForm`/`BForm` (statements only), `MultEq` and `GalD`. *After NODE-MULTEQ and NODE-SWRANGE:* `MultEq` compares two inner forms of the same odd rank, isomorphic at all finite places; "good" σ excludes every non-simple parameter (types with no vector fixed by the unipotent radical of any P_{(a,r−a)}), so multiplicity is 1 on both; proof by a simple trace formula (statement-level reading). `GalD` is supplied: Galois equivariance of the rational theta lift plus Rallis at the conjugate datum. The Rallis formula is used only inside Weil's range rank B − witt B > rank A: row step 0→1 and the layer lifts are absolutely convergent (Weil 1965); row steps j ≥ 1 use Siegel–Weil in the range n < m ≤ 2n (attributed by the reader to Ichino 2007; attribution not checked against the paper). No regularised statement is assumed. The in-tree proofs of these inputs were not read.
- **H2. The seesaw supplier.** `mainX_of_lawsX` is an honest m-step seesaw, conditional on its own hypotheses, but JOIN did not reach it from the root's producer of `MIid`, and other producers exist [SEESAW §0.3, §7; JOIN §1d]. *Status after NODE-LIVEPATH: closed.* A 20-step trace from the root reaches `miStar2_at_realisation_alt`, whose `JointCondition` comes from `joint_of_famAllQ_alt` with `MainX` = `SeeSaw.mainX_of_lawsX`; the consumer side (`RowsAt4.miStar` → `wire4F_alt` → `base_lifts_package_of_primitive_links.miStar`) is confirmed. The same trace shows the determinant identity's live consumer is `divClausesR_of` (same `IndefSide.boundsMu`, so H1's mathematics stands) and that the live `MultEq` producer is `PsCo.Pc.multEq_of_sides`, not the route NODE-MULTEQ read (that route is dead); being re-read.
- **H3. The twisted-place set.** Untwisted places must contribute index 0. That needs Tw = {resChar ≤ X″} ∪ {d, g₀, g₁}, equivalent to integral theta-unimodularity at every good p > X″. Neither its proof nor the suppliers `IndefSide.on`/`Untwisted` were located [JOIN §2c; SEESAW §4]. *Status after NODE-TWSET: restated.* No unimodularity theorem above X″ exists or is needed. The iff "twisted ⇔ resChar ≤ X″ or bad" quoted by earlier nodes is dead code. Live: `MuDef` sets Tw := W1, the places where the untwisted layer index, the dual index or F is nonzero, so the index off Tw is 0 by definition; congruence primes of any size join Tw, are twisted, and are paid for by a global budget Σ_v log N(v)·r(v) ≤ rank·f·m·b·de2 (`WeightAlgebra.Concl`, top level read; its inputs `Heights`/`sumGC4` unread). The cost enters the x^{O(ε)}·m·(B0+Nc) error. Consequence: every twisted-place input (Selmer killing, residual irreducibility) must hold at arbitrarily large residue characteristic, not only ≤ X″ as NODE-KILLAT recorded; being read.
- **H4. The layer signatures.** (k+j−1, m−j) is an input (`FactKaBlocks`) with no derivation, and it is the source of the per-lift growth, hence of "1/2". Its only stated reason is Σ_j(p_j − q_j) = mk [SEESAW §3]. *Status after NODE-DETSIG:* the signature is a definition (`sigW`), chosen rather than derived from the row tower, but forced: the proved lemma `arithAt` (read) needs exactly k+j−1 positive and m−j negative entries of the twisted Harish-Chandra parameter, and the gap conditions b_j < e_j < b_{j+1} force that split. Reader's interpretation: (U(V_j), U(W_j)) is a compact dual pair and twisting by μ_j moves the zero line one step per layer (Kashiwara–Vergne weight matching). Σ_j(p_j − q_j) = mk enters as the coefficient of logΩ in the covolume main term, by definition.
- **H5. Satisfiability, not logic.** The hypotheses can be jointly true only if Ga − ASK ≲ budget. The Lean neither proves nor needs it [ACCOUNT §0.4]; PAIRING argues it on paper for the Hecke-route tops (§5.4, item 5).

Conditional suppliers bear on all of these: the seesaw (H2), Theorem S and `LinkIRR` (§7), and L6 (seven `Published` premises).

---

## 10. Correspondence with the author's timeline

1. *Stepanov determinant.* Not located as an object; the analogy is structural (§6) [WHYHALF §2].
2. *D℘ ≡ 0; Dᵃ(Ω·θ)(0) divisible by p^{a/p+a/p³+…−O(log a)}.* Located: γ_p·a, the LT divisibility [LOCALDIV; NUMTEST].
3. *qN = M^k + R; μ automorphic from θ on the sixfold cover of GL₅; Poincaré bundle.* Not located (`GL5/` holds a rank-2 mass formula of unclear relation [THETA]).
4. *W(1_S) ≥ 0 via a determinant; multiplicity one; bootstrap.* Not located.
5. *Switch to Σ Λ(n)(X/n − 1)₊ − X log X + (1+γ)X.* Located: exactly G_z [LANDAU §1a].
6. *W·1_{(0,1]} + (∼X^η)·1_{(0,1/X]} ≥ 0.* Not located.
7. *Determinants of W(·) containing GGP periods; interlacing, or up to m non-interlacing weights.* GGP/Bessel periods located (§3.3); the "m non-interlacing" link is inferred [WHYHALF §6.7].
8. *Iterated theta lifts between totally definite unitary groups, π ↦ π ⊞ μ_j[t], multiplicity m, m like √X.* Located [ARCH; LINKN; CHAININD].
9. *Norms of lifts, level, cancellation of order-m terms via Chowla–Selberg, Weyl, Siegel mass.* Located (inferred match): the logΩ cancellation with Σ(p_j − q_j) = mk [WHYHALF §1.5].
10. *Sufficient lower bound on divisibility of the m-fold lift.* Located [CHAININD; ORBIT].
11. *Iwasawa tower via pigeonhole on 𝔽_{qⁿ}/𝔽_q.* Not located (SUMMARY §7); *inferred* candidates: the host's 2-power layer, or KILLAT's tame tower.
12. *Seesaw: period of the iterated lift is a Bessel period independent of Hecke characters; Rallis.* Located: `MIid`, Rallis scalars λ_j [SEESAW; L6].
13. *Bost slope inequality.* Located [RANK].
14. *Cost of each lift; 2/3 a priori; kill via twisting; "division".* Per-lift cost located [WHYHALF §1]; the 2/3 version not located (WHYHALF infers it from a per-lift cost ∝ m²). "Twisting" matches KillAt; "division" plausibly DIV *(inferred)*.
15. *Glue an integral structure across Hecke characters.* Located: RR glued across types [CONGMOD §2a].
16. *Relative trace formula; Cauchy–Schwarz; projected Poincaré series; approximate orthogonality.* Located: Theorem S [PAIRB; RANK]; the GL₅ part not located.
17. *Classes in H¹(O_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) not killed by twisting; weakening of Vandiver.* Located: the Ш bound via U(3) [VWIN; ONECHARU].
18. *Covolumes, theta-series index, congruences between lifts and forms.* Located [COVOL; JOIN; CONGMOD].
19. *Precise choice of the Iwasawa tower using Behrend.* `BehrendSets` located, not traced to the live path [WHYHALF §6.6; KILLAT].
20. *GRH.* Located: the level ⟨ψ⟩ with 4 : 3 shares, plus windowed Landau [CHBALANCE; LANDAU].

---

[^n4]: Audit history. NUMTEST4 described the served class as "inert in both", which was wrong; SIGNAL corrects it. Per SUMMARY §11 the NUMTEST3 instance was a signal place.

[^tiebm]: Audit history. The orphaned `TieBm` formulation, in which the middle levels are set to 0, has no consumer, so ARCH's worry about it lapses [SEESAW §0.1].
