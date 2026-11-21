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

**Landau on windows.** A one-sided bound on windows is enough [LANDAU §1b, §2b; REVIEW-ROOT]. Let 𝓛(s) be the Laplace transform of G_m(e^u). It is meromorphic in Re s > 0. Its poles sit at the zeros ρ of the L(s, ξ), with principal part proportional to −1/(ρ(ρ−1)) and summed with positive weights, so residues at a common zero cannot cancel. The Taylor coefficients a_k of 𝓛 at σ + iγ are integrals of G_m against the positive kernel u^k e^{−σu}/k!. For σ large in terms of the window ratio, this kernel concentrates on a log-window [u₀, (1+δ′)u₀]; σ must be large because outside the window only |G_m(e^u)| ≪ e^{2u} is known, so the tails must be exponentially smaller. A one-sided bound G_m ≤ Ce^{θu} on the window, together with positivity of the kernel, bounds |a_k(σ+iγ)| + Re a_k(σ) by roughly (σ−θ)^{−k}; the Re a_k(σ) is the price of one-sidedness. A zero with Re ρ > θ produces a nearest singularity, which forces larger coefficients; γ is chosen so that this pole is the *unique* nearest one, so poles on the circle cannot cancel. A real zero β produces a positive real residue and pushes G_m upward. Positivity of the averaged Dirichlet coefficients is not used. The reader judged this a correct theorem with a correct proof; at least eight sub-lemma bodies were not read (§9.1).

**Reduction.** All the RH-strength content therefore sits in one inequality between a weighted count of inert prime powers and its expected main term. The rest is character bookkeeping (§2). With the notation box, and one copy per lift j, the weighted count is

$$\mathrm{ASK}=\sum_{\text{tops }t}\ \sum_{j<m}\ \sum_{n}\Lambda(n)\big(1-\chi_{-d}(n)\big)\Big(\frac{a_t}{n}-w_{j,\mathrm{partner}(t,\mathrm{Frob}_n)}\Big)_+ .$$

The inequality is ASK ≤ MAIN + Err [COREGM; WRITEUP (12)].

**The idea.** The argument is a Stepanov-type argument [WHYHALF §2]. Its auxiliary object is a vector of algebraic numbers: periods of high-order Taylor jets of CM theta functions.
- **p-adic side.** At a prime p inert in K = ℚ(√−d), the CM curve is supersingular. In the height-two Lubin–Tate coordinate, a jet of order a is divisible by about p^{Σ_{e odd}(a/p^e − w)₊}. Summed over inert p ≤ a (Legendre; the caps cut further, at n ≤ a/w) with weight 2 log p, the uncapped part is Σ_n Λ(n)(1 − χ_{−d}(n))⌊a/n⌋, the inert part of Chebyshev's log a! = Σ Λ(n)⌊a/n⌋.
- **Archimedean side.** The same jet has size a!·Ω^{−a}, where Ω is a Chowla–Selberg period. log Ω already contains the split part of log a! through −L′/L(1, χ_{−d}). §4.6 computes this for one lift.
- **Comparison.** One copy of this comparison is Chebyshev quality. The gain comes from multiplicity. The jets are chained through m ≈ √x theta lifts U(X_0) → U(X_1) → … → U(X_m). Each lift is again an order-a derivative against its own kernel, so the divisibility recurs m times [CHAININD].
- **Product formula.** The comparison is made for lattices of forms rather than for single numbers, through Bost's slope inequality.

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

The exponential b exists so that every polynomial loss, ≲ x^{800}, is negligible next to it. t is fixed by the definition r + t = 8fr + 4 + ⌈x^{377}⌉·nWv, nWv ≈ 10rf²k³L²/m [ACCOUNT §1]. The recorded constraints are t ≥ r + 5 (L6), 3m < t (GLOBALCHAIN) and twists i < t below VWin's x^{401} [CONGMOD]. Why the definition has this shape, no node says.

---

## 2. The analytic frame

### 2.1 The host field and why each auxiliary object is there

Every hermitian space lives over a CM field E, called the host. It is built afresh for each scale x [HOSTS §1(a), §2(c1)]. It is abelian, with Gal(E/ℚ) = {±1}² × A, and it lies in ℚ(ζ_{QS·q·d}), with [E:ℚ] = 4n. Each auxiliary object has one job:

- **K = ℚ(√−d)**, with d ≡ 7 mod 16 prime. It supplies the CM elliptic curve whose σ*-functions build every theta kernel, the supersingular reduction at inert p, and the factor (1 − χ_{−d}) in the count. It also supplies the L′/L(1, χ_{−d}) inside Ω [ARCH §1].
- **√−q**, with q ≡ 3 mod 8 and (−d/q) = 1. This sign separates the two kinds of inert prime [SERVED §0; SIGNAL §0].
  - *Signal* primes are inert in K and split in ℚ(√−q), with Frob = ((+1,−1), h).
  - *InertClass* primes are inert in both, with Frob = c·h.

  At a signal prime, complex conjugation c is never a power of Frob. So every prime of E⁺ above p splits in E, and the hermitian space is split (hyperbolic) at p.[^n4]
- **The 2-power layer.** A surjects onto (ℤ/2^{e₂+2})^×/±1, cyclic of order 2^{e₂} ≈ x^{2+8ε}. An inertClass prime has a split hermitian form iff the A-part h of its Frobenius has even order. The anisotropic ones have Chebotarev density ≤ 2^{−e₂} ≤ x^{−2} [SERVED §0]. They are excluded by elementary counting, not by Chebotarev.
- **ψ** enters through the A-coordinate. The quotient A/A_0 by a cyclic subgroup A_0 is dual to ⟨ψ⟩. The top set TT ⊂ A carries unequal shares: 4/(3o+1) on the trivial A_0-coset and 3/(3o+1) on each other coset [CHBALANCE §2(a)]. This is how ψ reaches G_m (§2.2).
- **The level primes g₀, g₁ ∈ [Y_g, 2Y_g]**, with Y_g = (k·e^{x^ε})^8 [ORDER]. They play two roles.
  - They give the Bessel–Poincaré series a level and character. That is the source of the level saving (2/g)^{(s−1)kf} in near-orthogonality [PAIRB].
  - They carry prescribed depth-zero types, which force residual irreducibility of the Galois representations on the Selmer side [TWIST]. The two bad sets BB(r, g_k) are made disjoint by pigeonhole [ORDER].
- **T_u**, one prime per word u. It is a norm from K in a short window, and it sets the level of the source forms [ARCH §1].

(q, d) are chosen by a density argument over quadratic families: a mean square over q, Markov, a zero-density estimate in a box, and Siegel [PAIRGOOD §0]. For all y ∈ [Y_{qd}, Y_{qd}^A], every twist ξ·(·/q)^i·(·/d)^j with (i, j) ≠ (0, 0) satisfies |g_χ(y)| ≤ y^{1/2+ε/2}. Here log q ≈ Y_{qd}^{ε/5} ≤ x^{ε/5}, far above log y, and below log X′ = x^{ε/3}, which ThinScales (§2.2) needs. This is a statement about short sums in a varying family. It is not GRH, and there is no circularity: `QH.pairEx` has no hypotheses.

### 2.2 The exact bridge ASK ↔ G_m

The bridge (`ch_balance`, `ch_core`) is a finite-group computation that holds exactly [CHBALANCE §0–2].

**Step 1 (exact identity).** Orthogonality on Gal(E/ℚ) gives ASK − MAIN = De, where

$$\mathrm{MAIN}=a\Big(\log a-1-\gamma+\frac{L'}{L}(1,\chi_{-d})-\operatorname*{mean}_{\rho\in\Phi}\log w(\rho)\Big)$$

and De = |Φ|^{−1} Σ_g Σ_ψ ψ̄(g)·w·G_ψ(a/w) is an expansion over all characters of the Galois group (G_χ is the g_χ of §1). The identity uses

$$\sum_n\Lambda\chi(n)(a/n-w)_+=w\,G_\chi(a/w)-a\,\tfrac{L'}{L}(1,\chi).$$

The identity holds with an *arbitrary* constant in place of L′/L(1, χ) (CHBALANCE oddity 1); the true value is pinned by the host clause `HostAddCharCompatible` [SERVED §0].

**Step 2 (which partners matter).** The partner place of a prime is fixed by its Frobenius, and caps are thick, top or thin (notation box). At top and thin partners the Riesz length is at least X′/3. There the effective PNT `ThinScales`, |G_χ(y)| ≤ y·e^{−cx^{ε/8}}, makes them negligible. It is de la Vallée Poussin with a zero-free region proved in the tree, for conductors up to e^{x^{ε/5}}. Exceptional zeros of the real characters involving q or d are excluded by host-selected zero boxes (`RealBox`/`GoodFor`: none with β > 1 − 1/400) [SERVED Part 2, §3].

**Step 3 (only signal primes reach thick places).** The partner of a top t at odd distance e is (IsSignal ∧ e odd, t + e·h). So only signal primes reach thick places, and **the x-scale part of ASK, which carries ψ, sits entirely on signal primes** [SIGNAL §0.5].

**Step 4 (averaging).** Average over u₀ ∈ A₀ and sum over tops. The 4 : 3 shares then become

$$\lambda(h)=\frac{3+1_{A_0}(h)}{3o+1}=\frac1o\Big[1+\frac1{3o+1}\sum_{j\ne0}\psi^j(h)\Big].$$

With uniform shares only G_z, and hence only ζ, would survive.

**Result.** The bridge gives

$$U\cdot\big[G_m(x)-\mathrm{Sig}_A(x)-4x^{1/2+\varepsilon}\big]\ \le\ \sum(\mathrm{ASK}-\mathrm{MAIN})+\frac{2|TT|mb}{x},\qquad U=\tfrac12|TT|\cdot m\cdot b\cdot\delta ,$$

with δ the thick density. Sig_A collects the 3o quadratic twists of ⟨ψ⟩ by (·/q), (·/d) and (·/qd). It is bounded two-sidedly at the single point y = x by host selection (`bdG`/`ValuesAtX`). The signal unit is U ≈ x^{2.5}·b, using |TT| ≈ n. The budget for errors is U·x^{1/2+O(ε)} ≈ x^{3+O(ε)}·b. Every replacement error in the bridge is ≲ x^ε·log x relative to U. **The x^{1/2} comes only from Err/U** [CHBALANCE §2(c)].

### 2.3 What is counted and what is paid for the rest

ASK counts every inert prime, not only the informative ones [CHBALANCE oddity 2]. The gain side must therefore either deliver divisibility at a prime or charge that prime its whole ASK summand. The classification works as follows; the routes are explained in §4.5 [SERVED §0, §1.1, §2].
- **Orbit route.** Signal primes p ≤ X″ *and* even-order inertClass primes in [X′(1+Crρ), X″] receive the Hecke-free gain g₀⁺, a copy of their ASK summand, through `NoOperatorOrbitBound`. Their mass is ≈ x log x·U, far above the budget. SERVED calls this clause the real open child.
- **Hecke/colength route.** Even-order inertClass candidates (p < X′, ord h ≥ x^{ε/4}, Sig ≤ x^{−ε}, outside the band), on their good orbit representatives.
- **Bad orbits of kernel-served primes.** SERVED is ambiguous. Its summary lists them among the g₀⁺ recipients of the orbit route; its §1(b) has their g₀⁺ delivered by `UAt` on the Hecke side; its charge table charges them as a dropped bucket (≤ 4x^{−1+ε}U). The reading did not decide which.
- **Dropped primes** are charged their full ASK with gain 0: classes of small order (all anisotropic ones among them), the band around X′, the second kind, the high primes p > X″, and d. Each bucket costs ≤ x^{−1+O(ε)}·U. The high bucket is bounded directly (≲ x^{−25}U), so the share of thin partner positions is not needed.

A loss term LoP ≈ c·|TT|·m·b, x^{−1/2} of the budget, absorbs the per-prime digit-sum slack [WRITEUP (11)].

---

## 3. The objects

### 3.1 Three towers

All spaces are hermitian over E. They are unimodular at the base, with ranks fixed by k, m (even), t (odd), r = k + m − 1 and N(j) = k + j(t+1) [ARCH §2].

- **Column tower**, X_0 ⊂ X_1 ⊂ … ⊂ X_m. Each X_j is totally definite of rank N(j). Its forms are *algebraic modular forms*: functions on the finite set of lattice classes in the genus of X_j, valued in a weight representation. Integrality is taken in the Weyl-module (Δ) lattice. The level-j weight at a top place is (a_t, small…, −b_t, −w_1^{×(t+1)}, …, −w_j^{×(t+1)}), so **the same large entry a_t sits at every level**, and each lift adds a block at the cap weight w_j [CHAININD §1.1]. The p-adic divisibility lives on this tower.
- **Row tower**, Y_m, …, Y_0, of rank r + jt. Y_m ≅ X_⊥ is the orthogonal complement of an anisotropic vector in X_m (the nodes write X′ for this space, not to be confused with the scale X′). The bottom is Y_0 = X_0 ⊕ ⟨z⟩ ⊕ r_S hyperbolic planes, with r_S = m/2 − 1, signature (k + m/2 − 1, m/2), and a non-compact quotient. Its forms are genuine L² automorphic forms. The relevant space HH is the discrete-series, level-(g₀g₁) part of L²(U(Y_0)), of dimension D_all. Inside it sits EE, of dimension (1 − δ_p)D_all, δ_p ≤ e^{−x^{ε_z/7}}. The target lattice RR lives in EE.
- **Layers**, W_1, …, W_m. Each has rank r and signature (k+j−1, m−j). They are inner forms of U(Y_0) at every finite place. W_m is definite, and W_{m/2} has the signature of Y_0. Each is paired with a definite space V_j of rank r + t. The layer lattices M_j are integral cusp forms on the Shimura variety of U(W_j). They supply the covolume of RR, but only through a determinant hypothesis (§5.2; §9.4 H1). The signatures are stated (`FactKaBlocks`), not derived (§9.4 H4).

### 3.2 Maps

- **Column steps** K_j [ARCH §4(a)]. They are given by

  $$K_j\varphi(c')=\sum_{c}|\mathrm{Stab}\,c|^{-1}\rho_j(c)\rho_j'(c')\cdot\mathrm{divDe}\circ\mathrm{unf}_j(c,c')\circ\mathrm{sharp}(\varphi(c)),$$

  where unf_j(c, c′) is **the Taylor jet at 0 of a CM theta function θ_{c,c′} attached to a pair of lattice classes**. Here ρ_j, ρ′_j are unitary determinant characters, and sharp, divDe are diagonal normalising exponents [ARCH §4(a)]. The chain is col = K_{m−1}∘…∘K_0.

  *What θ_{c,c′} is, as far as the nodes say.* A theta function in matrix variables (an N(j) × N(j+1) matrix at each archimedean place) [HEIGHT §1(a)]. Its finite Schwartz datum is the indicator of the local lattice conditions given by (c, c′); its archimedean component is a Gaussian "vacuum" built from the period lattice of the CM curve [GLOBALCHAIN §1]. σ* (the reduced sigma function of a Δ = 1 lattice with CM by K) enters through the classical fact that θ_{L,L′}(Σ b_i z_i)/∏σ*(z_i) is integral at inert p in an orthonormal local basis: locally the theta function is a combination of prime-to-p translates of products of σ* [KERNELLAW §3(iii)]. The lattice summed over is not written out in the nodes (presumably Hom(c, c′) tensored with the CM lattice *(inferred)*).

  *Column minors and weights.* The jet is paired against a product of column minors, one per column of the Young diagram of the level-(j+1) weight at each position s [HIGHERRANK §1.2]. So position s carries ν₁(s) minors, the first-row length; at a top the overhang ν₁ − ν₂ (≈ a_t) is peeled into linear "top forms", leaving ν₂. This number is the cap of §4.3, and `LatTied` pins it to the count's cap w: "cap = weight" holds by definition plus the minor lemma [PAIRING §0.3]. NUMTEST4: det(Y)^m costs m, the number of minors, not its degree 2m.
- **Row descent** io_j : Mult(j+1) → Mult(j). It is tied by Petersson adjointness to a genuine theta lift. The composite is ι : (top forms) → EE.
- **Layer lifts** θ_j : (forms on U(V_j)) → (forms on U(W_j)). Each is a λ_j-similitude on Hecke parts, where λ_j is the Rallis θθ* eigenvalue. The descent ι is a κ·∏λ_j-similitude. There is one λ, shared by construction (`LevelLink` is `rfl`) [SEESAW §3].
- **Poincaré series** P_u : C_u → HH, P_u(T)(x) = Σ_{δ ∈ R_u(F)\G(F)} Ph_T(δx), over the Bessel subgroup R_u = U(X_0) ⋉ N. C_u ≅ the source space at level T_u. P_u* is the Bessel period map [PAIRB §0].
- **Bessel pairing** B_u : N_u → RR^∨, (B_uφ)(F) = ⟨sEE F, P_uφ⟩ up to a nonzero scalar and unitary changes of basis (`BesselId`) [WRITEUP S11].

### 3.3 The seesaw

The top period of the m-fold column lift is the codimension-one Gross–Prasad period ∫_{[U(X_⊥)]}(K_{m−1}⋯K_0 φ)|_{U(X_⊥)}·F. The live identity joining it to the bottom is `MIid` [SEESAW §0]:

$$\zeta_{u,t}\cdot\mathrm{Pt}_u(\varphi,F)=a_u\cdot\big\langle \mathrm{sEE}(V\,\Theta_t F),\,P_u(U_u\varphi)\big\rangle_{HH},$$

with V and U_u isometries, a_u ≠ 0, and ζ a unit at twisted tuples. SEESAW found a supplier for it: an honest m-step seesaw done two levels at a time (Bessel → Fourier–Jacobi → Bessel, because the codimension of X_j ⊂ Y_j alternates in parity), in which every intermediate column level is realised automorphically. JOIN traced the root's producer of this identity through several layers but did not reach that supplier. That the live path uses it is therefore not established [JOIN §1d], and the supplier is itself conditional on its chain's hypotheses [SEESAW §0.3].[^tiebm]

The seesaw is stated as **transport of linear relations**: a relation among top periods implies the same relation among bottom Bessel periods. So a_u exists, but its value is never computed. It does not need to be. B_u is *defined* as the period pulled back along ι, and RR is *defined* as the image lattice ι(Λ) of the integral top lattice. Hence the integrality B_u(N_u) ⊆ RR^∨ is literally integrality of the column period, with no λ_j or a_u entering [SEESAW §4]. a_u is used only in `BesselId`, i.e. in the frame (§7, §9.3).

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

with g_i integral and S_{s,a,b} = Σ_l (−1)^l Z_{s−2l,a,b}^{p^{2l}} the twisted log series in the position variables Z_{s,a,b} (s a position on the Frobenius orbit, (a, b) a matrix entry). The u_s are c for odd s and −σc for even s, for a single constant c of the curve, with σ the Frobenius of W(F̄_p), not complex conjugation [GAUSSCLASS §1; HIGHERRANK §1.1]. It is proved through six links. GAUSSCLASS reconstructed each link as mathematics, but read the three arithmetic leaves only at statement level. LEAVES later read them: `joint_integrality` (Kronecker theta integrality at torsion), the one-copy step (the fourth-power trick, confirmed), and `lamPos_of_posEmb` (a rewrite whose content is the field `pos` of `CmpHyp`) [GAUSSCLASS §0; LEAVES §0].

1. exp(Σ ph(X_i))·Θ is integral in an orthonormal local basis at every inert p. The steps are one copy, then 2×2, then a tensor power, then a general lattice by prime-to-p coset averaging.
2. At a split place the position variables form a unimodular hyperbolic pair over ℤ_{p²}. This is the only use of "split at p". The reason: at a place of E⁺ split in E, the hermitian form is a duality between V_w and V_{w̄}. The position (v, s) is the embedding r_v·z^s with z = Frob_p·c, so even positions carry one of the two and odd positions the other. The even and odd positions are therefore the two isotropic halves, and the dual-basis condition Σ_i σ^{2i}(ω_r ω*_{r′}) = δ_{rr′} makes the pairing unimodular [LEAVES L-B; HIGHERRANK §1.1].
3. Self-terms cancel by isotropy, leaving the polarisation Σ_e be(x_e, y_e).
4. Every biadditive hermitian be is ≃ G_ser(c, σc). This is the Dieudonné/Honda classification: H¹_dR of the height-two group is spanned by ℓ and the quasi-logarithm.
5. Trace duality for the unramified extension forces the coupling s ↔ s+1 and never s ↔ s.
6. Dwork: π^i/i! is integral.

The simplest instance was computed exactly [NUMTEST3]. Take E = ℚ(√−d, √−q), with one matrix entry Θ(z₀, z₁) = th0(z₀+z₁)·th0(c(z₀−z₁)). Here th0(z) = σ*(z+t₀)e^{−πz t̄₀/A₀}/σ*(t₀) is a normalised torsion translate of σ*, and c satisfies c·c^σ = −1 at a served p [NUMTEST3 §1]. In orthonormal coordinates (a unitary change of variables with entries A, C, and σ the Frobenius) Θ(z₀, 0) = th0(Az₀)·th0(Cz₀), with

$$A A^{\sigma}+C C^{\sigma}=0\ \text{ at }p,\qquad |A|^2+|C|^2=1\ \text{ at }\infty .$$

The even-position direction is isotropic for the p-adic hermitian form, so the two Gaussians cancel p-adically, while the function keeps Gaussian growth at ∞. This is how one function can saturate the archimedean bound and carry the full p-adic gain: the form is definite at ∞ and hyperbolic at p.

### 4.3 Adjacency, caps and minors

**Positions.** Positions s ∈ ℤ/n′ run along the Frobenius orbit z = Frob·c, where n′ = ord(h) is the orbit length (even at a served prime). Mod p, a level-e factor of the Gaussian couples position t to position t + e, the place Frob^e·t [HIGHERRANK §0(a)].

**The cap lemma.** Under the jet pairing, multiplying by a linear form is adjoint to a directional derivative of the operator polynomial. Each Gaussian factor therefore forces one derivative in a fixed direction onto the product of column minors at the partner position. Two derivatives in one direction kill a minor. So the number of Gaussian factors of level e is at most min(a/p^e, w_{t+e}), where the cap w_{t+e} is the number of minors at the partner position, which equals that position's weight (§3.2) [HIGHERRANK §0(b); PAIRING §0.3].

**Legendre and Dwork.** These give the per-lift, per-prime gain

$$\gamma_p\,a-\sum_{e\ \mathrm{odd}}\min\Big(\frac{a}{p^{e}},w_{t+e}\Big)=\sum_{e\ \mathrm{odd}}\Big(\frac{a}{p^{e}}-w_{t+e}\Big)_+ ,$$

using max(A − w, 0) + min(A, w) = A (`ask_add_Mn`). With weight 2 log p per prime (Σ_{w|p} 2·lw·e_w = 2 log p), **this is exactly the ASK summand** 2 log p·Σ_{i odd}(a/p^i − w)₊ = Σ_{n=p^i} Λ(n)(1 − χ_{−d}(n))(a/n − w)₊ [WRITEUP S7; ACCOUNT §0.5]. At a thick partner, w ≈ b and a/w ≈ x, so the capped count is a Riesz mean localised at n ≈ x.

**Numerical evidence** [NUMTEST, NUMTEST2, NUMTEST3, NUMTEST4, SIGNAL §E].
- For ℘, which has no Gaussian factor, the slope is γ_p to three decimals up to order 6000. For σ the slope is only 1/(p²−1).
- On the actual kernel at served primes: the slope is γ_p to 0.0003. At w = 0 the bound v ≥ v_p(a!) − (a−1)/(p²−1) holds exactly. The measured valuation falls below the formula Σ_{e odd}(a/p^e − w)₊ by at most 0.98 (n′ = 2), 1.54 (n′ = 4, 0/800 mismatches against brute force) or 1.13 (two tops, 57 jets). The Lean's bound subtracts a loss term of this size, and it held in every test [WHYHALF §3.1].
- Caps are charged per position and are close to tight. A shared budget is excluded: it predicts a loss of 12, and ≈ 5 is observed. det(Y)^m costs m.
- Controls collapse the gain at split primes, at anisotropic inert primes (only 1/(p²−1)), and with scrambled jets (slope 0.0185).

### 4.4 Iteration over the m lifts

The iteration is an honest induction (`main_ind`) [CHAININD §0]. The induction hypothesis after j steps is only that the image equals ϖ^{(gains so far)}·G′, with G′ an *arbitrary* element of the level-j integral lattice Int_j, the target of lift j−1 and the source of lift j. The next one-step bound holds for every element of Int_j. So the induction is a composition of maps, each divisible on the whole integral lattice. The derivative order is not split among lifts: every level carries a_t again. Hence

$$\sum_{j=1}^m\mathrm{gain}_j\ \approx\ \sum_{j=1}^{m}\sum_{t\in TT}\sum_{e\ \mathrm{odd}}\Big(\frac{a_t}{p^{e}}-w_{j,t+e}\Big)_+ ,$$

with w_{j,t+e} the level-j cap at the partner position (about m times a one-level sum), minus automorphism denominators v_p(#Stab). Those are charged once per lift via Minkowski, are ≈ x^{402}, and are negligible next to b.

*Why the intermediate lattices cost nothing.* p-adically only divisibility of each step on all of Int_j is used. Archimedeanly the composite's height is bounded by Σ_j log‖K_j‖², each norm taken between the fixed Fock norms of levels j and j+1 (§5.1), and Bost is applied only to the composite N_u → RR^∨. Each intermediate norm occurs once as target and once as source, so the metric and covolume of Int_j appear in no term *(inferred from HEIGHT §1(b), WHYHALF §1.5)*. "Multiplicity" means exactly this: the same primes divide each of the m lifts to order a. A normalisation error in one step would be multiplied by m, and nothing in the induction would catch it [CHAININD §0.5].

### 4.5 Two routes

- **Hecke/colength route** (kernel-served inertClass places of even order, p < X′; VV denotes the good orbit representatives where it is used) [LOCALDIV; PAIRING; COLENGTH].
  - A Rallis-type commutation lets a level-0 Hecke operator move up the chain. This unlocks the larger bound γ_p·a at even-position tops, at a price p^{−Pr} per step (Pr ≥ 0 is the Hecke normalisation exponent).
  - The colength τ of the Hecke image, a p^{⌈τ⌉} factor in the target, then removes that surplus again.
  - The net gain at each served prime is the prime-count summand ± O(1); the pairing of tops used (`kinkHH`) is injective. Any excess the Hecke operators buy is spent on their colength.
- **Orbit route** (signal places p ≤ X″, where the ψ-part lives, and even-order inertClass places in [X′(1+Crρ), X″]; see §2.3 for bad orbits) [SIGNAL; ORBIT; JETA; SERVED §0].
  - `NoOperatorOrbitBound` bounds the m-fold chain directly on global kernel entries and delivers the Hecke-free gain g₀⁺. It uses no Hecke operators and no colength: VV = ∅ and τ = 0.
  - The local theorem is an LP-duality valuation argument. Each Gaussian factor x^{l^α}y^{l^β} costs one p, which is paid by l^α r_x + l^β r_y ≥ 1. A generic-frame reduction is done by Cauchy–Binet.
  - The charge Σ_e min(cap_e, A/p^e) is at least the true LP maximum, so it is conservative (0/4000 random violations).
  - The iteration `chain_ge` has the same shape as `main_ind`.
  - The lattice tie charges no Δ/∇ index: Δ = ∇* is proved in-tree, and the ∇-span is saturated.
  - NUMTEST3/4 tested only inertClass served primes. The signal places rely on the same local mechanism, applied to a class the tests did not cover [SERVED §2].

### 4.6 A one-lift model computation

This is the leading-order identity behind "one lift is one Chebyshev identity". It is HEIGHT's reconstruction in the Lean's normalisations [HEIGHT §2(b); WHYHALF §1.1; ACCOUNT §2]. Take the single jet J = D^aθ(0)/Ω^a at one top place, one lift, and let w be the cap at its partner.

$$\text{archimedean:}\quad \frac1{n_{\rm Pl}}\sum_{v\mid\infty}\log|J|_v^2\ \le\ \mathrm{ph}(a)-a\log\Omega+\mathrm{poly}(x)\cdot La,$$

$$\text{p-adic:}\quad \sum_{p\ \mathrm{inert},\,w\mid p}2\,v_w(J)\log p\ \ge\ \sum_{n\le a/w}\Lambda(n)\big(1-\chi_{-d}(n)\big)\Big(\frac an-w\Big)_+-\text{loss}.$$

The product formula Σ_v log|J|_v = 0 makes the p-adic total at most the archimedean one. Both sides are squared norms. This is why the inert count carries the weight 2 log p, i.e. Λ(n)(1 − χ_{−d}(n)) = 2Λ(n) on odd powers of inert primes.

*Leading order.* Without caps, the p-adic side is Σ_{p inert} 2 log p·Σ_{i odd} a/p^i = Σ_{p inert} 2γ_p·a·log p, cut at p ≤ a. That is the inert part Σ_n Λ(n)(1 − χ_{−d}(n))⌊a/n⌋ = log a! − Σ_n Λ(n)χ_{−d}(n)⌊a/n⌋ of log a!. The twisted sum is ≈ −a·L′/L(1, χ_{−d}) (Mertens for χ_{−d}). On the archimedean side, ph(a) = log a! + O(log a), and the averaged Chowla–Selberg value of logΩ gives

$$\mathrm{ph}(a)-a\log\Omega=\Big[a\log a-(1+\gamma)a+a\,\tfrac{L'}{L}(1,\chi_{-d})\Big]-a\log(\pi/v).$$

With caps and y = a/w, the p-adic count is exactly

$$\sum_n\Lambda(n)\big(1-\chi_{-d}(n)\big)\Big(\frac an-w\Big)_+=w\Big[y\log y-(1+\gamma)y+y\,\tfrac{L'}{L}(1,\chi_{-d})\Big]+E(y).$$

Here E(y) = w·(G_z(y) − g_{χ_{−d}}(y)) is the explicit-formula remainder, in the notation of §1 *(my computation from the definitions)*. The bracket equals the archimedean bracket minus a·log w. The leftover −a·log(π/v) and −a·log w are matched through log T_u (Count5, `key_identity5`, §5.4). So **the main terms agree identically**, and all content is in the errors. The split part of log a! is not absorbed by any normalisation: it is the −L′/L inside logΩ. Its fluctuation is the host-selected hypothesis `ValuesAtX` (§6).

*Precision required.* At a thick partner, w ≈ b and y ≈ x. The main term is then ≈ b·x·log x, while the quantity to be detected is the signal b·G(x), and the target bound is G(x) ≲ x^{1/2+O(ε)} [ARCH §6]. So one copy of the comparison must be right to relative x^{−1/2+O(ε)}. Equivalently, MAIN ≈ x^{1/2} × budget [ACCOUNT §2]. One lift cannot reach this: its boundary costs are each one whole copy, giving only G_m(x) ≲ x^{1+O(ε)} (§6).

---

## 5. The archimedean side and the slope inequality

### 5.1 Heights

**The bound.** The archimedean height of B_u is bounded by submultiplicativity along the chain [HEIGHT §0]:

$$\mathrm{htMap}(B_u)\le\sum_j\log\|K_j\|^2+\log\|P_tL\|^2-\log\kappa-\sum_j\log\lambda_j .$$

**The jet-step norm.** A Cauchy estimate in Fock space for Taylor jets of entire functions with Gaussian growth gives

$$\log\|K_j\|^2\le\sum_\rho\big(\mathrm{ph}(\nu_{j\rho})-|\nu_{j\rho}|\log\Omega_\rho\big),\qquad \mathrm{ph}(y)=y\log y-y .$$

The conjugate periods Ω_ρ genuinely differ, since they come from different ideal classes. Only their mean enters, and the averaged Chowla–Selberg identity proved in-tree gives

$$\operatorname*{mean}_\rho\log\Omega_\rho=\log\Omega=\gamma+\log(\pi/v)-\frac{L'}{L}(1,\chi_{-d})$$

(sign convention as in the notation box).

**Where the split half of log a! goes.** The split part Σ Λ(n)χ_{−d}(n)⌊a/n⌋ ≈ −a·L′/L(1, χ_{−d}) is exactly the −L′/L inside a·logΩ [WHYHALF §3.3]. The bound has no slack in the coefficients of ph or logΩ. NUMTEST3 found it saturated to within 5.3 in log.

**Why only m·ph(a_t) survives.** The height contains Σ_ρ Σ_i ph(ν_{jρi}) over *all* weight entries. These include the k entries of size ≈ w and the t+1 blocks at every level, not only a_t. They do not reach the main term, because the theta scalar λ_j enters the height as −log λ_j, and L6 bounds log λ_j below by a hook product Σ_ρ logHook_{jρ}. The numeric fact `weight_height_sum_le` says Σ_i ph(ν_{jρi}) − logHook_{jρ} ≤ ph(a_t)·[ρ ∈ TT] + eE. So per (j, ρ) the hook product cancels the factorial growth of every entry except **one** ph(a_t) at tops, and over the m levels this leaves m·ph(a_t). Together with `weight_sum_eq` (Σ_i ν_{jρi} = a_t[ρ ∈ TT] + k·w + δ_{jρ}) this collapses the height to Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + O(|TT|·a·La + m·B₀x^ε). This is why −Σ log λ_j sits in the height. The factorial growth of the k·w-sized entries never meets the p-adic side [HEIGHT §1(a), §2(b) end]. The cancelled terms are ≈ k·f·b·x^ε per level, so L6 must be sharp to relative x^{−4} (§5.4).

**Rallis scalars.** λ_j is the Rallis inner-product eigenvalue. An exact product formula is proved, and only its hook products are kept as main term. The L-value is evaluated deep in the convergent range, where |L^S| ≥ e^{−2rf} is elementary. The loss is poly(x) ≪ b [L6 §0]. This rests on seven named literature theorems, each supplied in-tree. λ_j has no finite-place counterpart [JOIN oddity 5].

### 5.2 The target lattice and its covolume

RR is glued place by place. At y it is ι(μ(y)) applied to the projection of the integral lattice onto the type-μ(y) part (author's item 15) [CONGMOD §2a]. The covolume bound uses the factorisation det ι = κ^D·∏_j det θ_j. **This is a hypothesis of `BoundsMu` (SO:31-41), not a derived fact.** SEESAW infers it from the similitude clauses `l1c` (ι is a κ·∏λ_j-similitude, θ_j a λ_j-similitude) and `l1d`, by taking determinants part by part. Neither ARCH nor SEESAW found that derivation, nor any theorem that factors ι through the θ_j as maps [ARCH §7.1; SEESAW §3]. It is hole H1 of §9.4. Granted it,

$$\mu(RR^\vee)\le\operatorname{meanLog}\kappa+\sum_j\frac{\mathrm{lcv}(M_j)}{D}+2F_o+(\text{index and congruence terms}) .$$

**The layer covolume** is [COVOL; VOLUME; HS]

$$\frac{\mathrm{lcv}(M_j)}{D}\le(p_j-q_j)\sum_\rho w_{j\rho}\log\Omega+C\cdot B_0\log\log x,\qquad p_j-q_j=k+2j-1-m .$$

It is proved by descending induction over layers, from the definite top W_m through deep covers. The steps use an effective arithmetic Hilbert–Samuel bound at one tensor power, and `FlatDegree`: flat sections on U(p, q) have arithmetic degree (p − q)/2·logΩ + q(…), which is Chowla–Selberg again. **The flat directions are exact. The error is ∝ q ≤ m.** So the main term (p_j − q_j)Σw·logΩ comes from `FlatDegree`. The separate uniform volume theorem (`VolumeTheoremX`) enters only through an error budget inside this induction. It has no main term of its own, and is weak but sufficient [VOLUME §0.1, §0.5]. The signatures (k+j−1, m−j) themselves are an input (`FactKaBlocks`), not derived (§9.4 H4).

**The index at the gain primes.** The index of θ_jT_j in M_j at the gain primes is bounded by derivative content in the *layer* weights only, F = (k−1)Σw/(p²−1). F enters once on each side and cancels. The a-sized factorial is counted only in the column steps [JOIN §2d].

### 5.3 Bost's inequality, rank-free

The joint map ⊕_u B_u : ⊕N_u → RR^∨ satisfies [RANK; WRITEUP (5)]

$$s-\log|W|-(1-\delta_p)^{-1}\big[4u_F\log(1+H_B/u_F)+(\eta+4\sqrt{\bar e})H_B\big]\le\mu(RR^\vee),$$

where:
- s = Σ_u d_u(μ(N_u) − h(u))/Σ_u d_u is the mean source slope net of heights;
- u_F is the Harder–Narasimhan spread;
- H_B = x^{C_H}·b is the Bost scale;
- η, ē are frame-tightness parameters, with (η + 4√ē)·x^{C_H} ≤ 6.

The proof is a layer-cake over HN filtrations, using Bost's slope inequality and a dimension-free frame lemma. No rank or degree error appears. The frame hypothesis carries no metric content: its changes of basis are free invertible matrices. It yields only *robust near-surjectivity* of the joint period map. That is why non-vanishing (§7) is needed at all.

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

Glossary [ACCOUNT §2]: ΣA = Σ_t a_t; Fo is the F-index of the inert primes ≤ X″, ≈ (k−1)Σw/(p²−1) per prime (it cancels); Ee and Lo5 are a per-lift term (≈ m·ΣA·lg) and small losses; E_DIV is DIV's error; lg and Λ5 are log-level constants matched by Count5; La ≤ 2x^ε; BL is the Bost loss (1−δ_p)^{−1}[…] of §5.3.

Here

$$\mathrm{MAIN}(u)=\sum_t\big[m(\mathrm{ph}(a_t)-a_t\log\Omega)-a_t\log T_u\big],\qquad \mathrm{Main}=\sum_j\sum_t a_t\Big(\log a_t-1-\gamma+\frac{L'}{L}(1,\chi_{-d})-\operatorname*{mean}_\rho\log w_{j\rho}\Big).$$

Count5 needs log T_u to match Σ_j mean_ρ log(w_{jρ}v/π) + m·lg to within ±La.

**The cancellations** [ACCOUNT §0.3; WRITEUP S16].
- μ(RR^∨) enters both Bost and DIV with coefficient +1 and cancels. Only an *upper* bound on μ(RR^∨) is used (through DIV, i.e. the covolume bound of §5.2), and it must be right to relative x^{−4}. What is never needed is a two-sided estimate.
- F_o cancels (via `foTie`), the m·lg term of Ee cancels against Count5, and log(π/v) cancels in `key_identity5`. These are syntactic.
- The large logΩ terms cancel: +Σ_j(p_j − q_j)Σ_ρ w·logΩ from the covolume against −Σ_ρ(a_t + k·w + δ_{jρ})·logΩ in the height. They leave −m·a_t·logΩ, because

  $$\sum_{j=1}^m(p_j-q_j)=mk\quad\text{exactly},\qquad |p_j-q_j-k|\le m-1 .$$

  Each layer's logΩ term is ≈ k·f·b·|logΩ| ≈ x^{6.5}·b, against a per-layer allowance B₀ ≈ x^{2.5}b. Summed over the m layers this is ≈ x^7·b against the budget x^3·b. Either way, covolume and L6 must each be right to relative x^{−4} [ACCOUNT §0.3, §3(ii); HEIGHT §0.3].
- Seventeen sign and direction checks pass [WRITEUP §3].

**Precision-critical hypotheses** [ACCOUNT §0.3–0.4, §2 table].
1. Covolume (B) and height (C), the latter through the L6 hook lower bound: relative **x^{−4}**.
2. Count5: log T_u to ±La, i.e. relative **1/m** (a prime in a window of relative width 1/(fk)).
3. Bessel-frame tightness: **η ≤ 6x^{−C_H}**, with x^{C_H}·b at least the HN spread.
4. Two-sided, from host selection: `ValuesAtX`/`bdG` at the single point x, and `ThinScales` (§6).
5. A satisfiability condition **Ga − ASK ≲ budget** (relative x^{−1/2} per prime). The Lean neither proves nor needs it, since it uses only Ga ≥ ASK − LoP. But Ga and the colength term can each be ≈ x^{1/2} × budget. If Ga exceeded ASK by more than the budget, the chain would force G_m(x) ≤ −x^{1/2+δ} on all windows, contradicting G_z = Ω±(x^{1/2}). The slope-side hypotheses would then be false for the real lattices. It depends on a pairing of V-tops (Hecke-route tops) that ACCOUNT could not verify. The later node PAIRING §0.1 resolves it on paper in the favourable direction: `kinkHH` is an injective pairing, τ cancels the V-top surplus exactly, and Ga − ASK ≲ |TT|·m·b/n, far below LoP. That upper direction is not in the Lean (§9.4 H5).

---

## 6. Why 1/2

**The error terms.** The conclusion's error ErrX5at splits into two families at the budget [WHYHALF §1.2].

- **One-off (boundary) terms**, each about |TT|·a·x^ε, i.e. one whole copy of the per-lift signal:
  - the precision of the prime T_u that scales the last map (Count5);
  - DIV's top-place boundary terms, which are m-independent because b′ = a/X′;
  - the floor on the slope of the level-0 source lattice;
  - the HN spread u·log(1 + H_B/u) in Bost.
- **Per-lift (interior) terms**, each about B₀ = f·m·b·x^ε, **which contains the factor m**:
  - the layer covolume error ∝ q_j ≤ m;
  - the logΩ residual from |p_j − q_j − k| ≤ m;
  - the congruence allowance η_j;
  - the per-lift local error E_j.

  Summed over m lifts these give m·B₀ ∝ m².

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

One difference: in Stepanov the cap ℓ ≲ √q is also what makes the linear system solvable. Here non-vanishing costs only a polynomial relation k ≳ m⁵·f·log b, which the parameters absorb. **The cap on m is the growth of the per-lift error, not non-vanishing** [WHYHALF §2]. Non-vanishing does constrain the host: with f = 2n, k ≳ m⁵·f and k/n² ≲ m force n ≳ m⁴ ≈ x². So the host degree n ≈ x^{2+8ε} is fixed by non-vanishing *(the review's observation, REVIEW-MAIN-ARGUMENT A3)*. The tree also carries m⁴ ≤ f directly as a hypothesis (`SLN:36`). WHYHALF notes that enlarging n would relax the Theorem S constraint, so that constraint does not cap m.

**Sharpness: the conceptual question.** G_z(x)/√x is a nonzero mean-zero almost-periodic function of log x, so G_z = Ω±(x^{1/2}). Hence G_m(x) ≥ c√x occurs in every window, and there the chain must be tight to x^{o(1)}. Equivalently, some per-lift loss must truly be of size ≍ m, not merely ≤ m. A per-lift cost independent of m would prove ψ(x) = x + O(x^δ) for every δ, which is false [WHYHALF §0.5, *(inferred)*]. So the growth of the per-lift error is not a removable inefficiency. It is where G_z = Ω±(x^{1/2}) shows up in the argument. The reading locates the growth in the layer signatures (k+j−1, m−j), whose q_j runs up to m. Those signatures are an input, not derived (§9.4 H4). Which inequality is tight, and why an m-fold Bessel period needs targets with q up to m, is not established by the reading [WHYHALF §6.7]. ACCOUNT's satisfiability condition (§5.4, item 5) is the same phenomenon seen from the other side.

**Chebyshev.** Chebyshev's method fails beyond constants for three reasons: no multiplicity, the auxiliary integer is not supported on the counted primes, and divisibility is bounded but not computed. Here m supplies the multiplicity, and the main terms are computed exactly [WHYHALF §3]:
- Legendre/LT divisibility holds to O(1) per prime. Its total, O(x) per top per lift, is relatively 1/b against a = x·b.
- Caps localise the count exactly.
- The split half is computed via averaged Chowla–Selberg.
- Flat covolumes are exact.
- The Fock bound has no slack in its main coefficients.
- The slope inequality is near-tight for a rank reason.

**Exact, one-sided and two-sided ingredients.**
- **Exact:** the items just listed, plus the bridge identity.
- **One-sided, in the direction consumed:** divisibility (a lower bound; the truth exceeds it in rank one, NUMTEST2), heights and covolumes (upper bounds), L6 (a lower bound, which must nonetheless be sharp to relative x^{−4}), Bost (an inequality), and the conclusion itself (an upper bound, on windows), which Landau needs.
- **Two-sided and supplied by host selection:** |g_χ(x)| ≤ x^{1/2+ε} at the single point x for the (·/q), (·/d), (·/qd)-twists of ⟨ψ⟩, and the effective PNT ThinScales at lengths ≥ X′/3. The fluctuation of these quadratic twists is not cancelled by the method. It is placed in the host's choice of (q, d) [WHYHALF §3; ACCOUNT §0.5(vi)].

---

## 7. Non-vanishing

**Why it is needed.** The slope inequality compares sizes of lattices. If the periods B_u vanished, or if the joint map fell far short of surjective, Bost's inequality would say nothing about the primes. The frame hypothesis excludes this: if every B_u = 0, the frame's rank bound contradicts (1 − δ_p)·|I ⊔ I₁| ≤ |I|, where I, I₁ index frame rows [RANK §0]. The same data record must also satisfy the frame inputs. These force D_all > 0 and some B_u ≠ 0, so the degenerate "stand-in" row records found in the tree cannot be the live one [JOIN §1c]. The frame in turn rests on "Theorem S", which has two halves.

**Near-orthogonality** [PAIRB; COUNTS; THMB; THEOREMS]. The Gram kernel K(u, u′) = (c_uc_{u′})^{−1/2}P_u*P_{u′} has off-diagonal squared Hilbert–Schmidt norm ‖K(u,u′)‖²_HS ≤ (1 + b^{−6})·d_ud_{u′}/D*, the value for random subspaces. Its diagonal satisfies ‖K(u,u) − 1‖²_HS ≲ d_u/Γ. In the Lean this is `TheoremSSelected`, proved *conditionally* by `theoremS_selected_of_loops` from further hypotheses [RANK §0; PAIRB §1]. This is the author's "relative trace formula" (item 16). It is proved by a **double unfolding of Poincaré series**, with no spectral decomposition, so the continuous spectrum never appears. The savings are:
- identity-orbit terms: an exact volume identity and Schur orthogonality, ∫HS² ≤ 1/formal degree;
- non-generic terms: sublattice counting, q_v^{−(k−2r_S−5)} (q_v a residue-field size, r_S = m/2 − 1);
- second-type terms: a character-sum cancellation on a hermitian quadric [COUNTS correcting PAIRB];
- corank-s terms, s ≥ 2: mainly the level factor (2/g)^{(s−1)kf}, with g ≥ Y_g a level prime;
- the Gauss-sum matrix: Gelfand–Graev multiplicity one.

The tight comparison 2^{−k/2}e^{Cm⁵f log b} ≤ b^{−14} is what fixes k ≈ x^{9/2+10ε}.

**The exponentially precise dimension count** [COUNT; SLEAVES; FORMULAGAP; GERMJET]. D_all = dim HH is a limit-multiplicity count for a very regular discrete series of U(k + r_S, r_S + 1)^f in L² of a non-compact quotient:

$$D_{\rm all}\le(1+\eta_1)D^*,\qquad D^*=\text{formal degree}\times\text{covolume},$$

with relative error e^{−rf log r/16} (r = k + m − 1 the rank; COUNT writes n), uniformly in rank. The smallness of δ_p (`LinkIRR`) is likewise supplied only *conditionally*, from a row count [RANK §0]. The proof is not a trace formula over conjugacy classes. R(φ_e) is shown to be an exact orthogonal projection onto cusp forms, by Schur orthogonality for integrable discrete series. Its kernel Σ|F_i(x)|² = Σ_γ φ_e(x^{−1}γx) is then bounded pointwise, region by region: unipotent near terms, a Siegel mean-value thin part, and a sup-norm bound in the deep cusp.

The key analytic input is a **compression formula** for lowest-K-type matrix coefficients of non-holomorphic discrete series, c_λ(z) = ∏_iΔ_i(z)^{−s_i} (Δ_i the leading principal minors). It is proved via Schmid's first-order system and jet uniqueness (`germ_jet_zero`, read and found correct, needing only a Harish-Chandra gap larger than twice the rank). It reproduces (cosh t)^{−m} on U(1,1) and the classical value on holomorphic U(2,1). On the middle series of U(2,1) it passes independent checks. The readers did not find it in the literature, and it is not Knapp–Wallach. The Harish-Chandra gap it needs, ≈ x^{110}, is met with ≈ x^{1300}, counting only opposite-sign pairs.

---

## 8. The Galois-theoretic inputs

**Where congruence modules enter.** At *twisted* places the target lattice RR is a projection onto a Hecke-eigen type part Z_j ⊂ forms on U(V_j). Twisted places include every prime below X″, which is the whole gain range. There the dual index of the projected lattice T_j is bounded by Hida's congruence module len[Pr_Z L : L ∩ Z] [CONGMOD §0]. This error sits inside DIV's per-lift allowance, which is at the budget (the m-family).

Z is the space of theta lifts whose A-parameter contains a Speh block μ⊠S_t. Here t is the block length R.t of §3. Their Galois representations are ρ ⊕ χ₁ ⊕ χ₁ω^{−1} ⊕ … ⊕ χ₁ω^{−(t−1)}, with ω the cyclotomic character [LINKN §0; author's item 8: π ↦ π ⊞ μ_j[t]].

**Congruence ≤ Selmer.** This is the Ribet–Wiles direction, made quantitative by a Fitting-ideal determinant lemma. The key input `NoChiOff` says no form outside Z contains χ₁. It is proved by a Galois-side rank/weight count [GALREP]. That count is not the deep input. The converse-theta content (theta image = forms with a Speh block) sits in `ConclusionZ` and in the datum field `D7.Z_tie`, both unread. Purity is used inside `ConclusionG6` although `Row0b` has no purity clause; its source is untraced [GALREP §4; SUMMARY §12]. The resulting bound has three blocks:
- the ρ-block: Bloch–Kato Selmer of ρ⊗χ₁^{−1};
- the c = 1 block: v_l(h_E);
- the c ≥ 2 blocks: Ш¹(E, ℚ_l/ℤ_l(−i)), i = c − 1.

**Killing the ρ-block** [KILLAT; ORDER]. The ρ-block is killed by twisting through a finite multivariable tame tower O[(ℤ/l^M)^{2R}] with Chebotarev-chosen auxiliary primes. The Selmer module has a square presentation P, and the length at ψ equals v(ψ(det P)). Killing the residual Selmer group gives det P a unit coefficient in low degree. Neither weak Leopoldt nor an infinite Iwasawa module is used.

This runs as a **two-pass construction**. Pass 1 is untwisted. A seed (Q, k, ψ) is chosen from its export. Pass 2 rebuilds with twisted types under `SameExport`, which keeps ρ_s, χ_s, the theta data and the Bloch–Kato data identical. The archimedean constants are fixed before the twist datum. ORDER closed a possible defect that TWIST had raised on the order of these choices.

**Residual irreducibility** at every l comes from the prescribed depth-zero types at g₀, g₁ [TWIST].

**The Ш bound** [VWIN; ONECHARU; RT3; MODU3; PATCH; FINEND]. The bound needed is

$$\sum_l\log l\sum_{0<i<t}\mathrm{len}\,Ш^1(E,\mathbb Q_l/\mathbb Z_l(-i))\le\sqrt b,$$

and VWin states it for all twists i < x^{401}. Crude bounds do not suffice. The best crude bound in the tree (`LemmaK`) is exp((2kn)^C log disc), far above e^{x^ε}. Brauer–Siegel controls only h_E. E is abelian, so the minus parts are governed by Bernoulli-type L-values, but the plus parts would need lower bounds for Borel regulators, which are not known [ONECHARU §0, §2a.4]. The proof is therefore R = T-type on the deformation side.
- Ш embeds in first-order deformations of Ψ ⊕ 1 ⊕ Ψ^{−1}.
- A graded commutative-algebra inequality bounds len Ш by 2Σ v_l(tr ρ(σ) − t) over automorphic or endoscopic points. Uniformity in l comes from one integer NN.
- The modularity input is residually reducible ordinary automorphy for U(3). It is Skinner–Wiles extended to n = 3, using a Chenevier determinant ring and Taylor–Wiles patching at nice primes. The seed exists unconditionally (an Eisenstein congruence for n = 2, an adjoint lift for n = 3).
- At reducible nice points the patching rests on a new local model. It is a quotient of O[[X, M]]/(Y·M), with two big components, one reducible and one irreducible and determinantal. It requires a derived condition g² + e′ ≤ D₀ (g the rank of the off-diagonal Selmer group over K((t)), e′ the number of tangent directions of the reducible locus used, D₀ = n·d + n·q in PATCH's local notation). It is derived from a Greenberg–Wiles bound; that derivation is unread [PATCH §0].
- Finiteness is proved for the torus-invariant subalgebra (`FinEnd`). Adjoint vanishing uses `regDet` instead of an enormous-image hypothesis.

A consequence would be a polynomial bound on plus parts of K_{2k}(O_E). This is the "weakening of Vandiver" of the author's item 17.

**Galois representations** (`Row0b`) [GALREP]. They come from descent to unitary groups, an Eichler–Shimura-type construction in odd rank (Lefschetz proved in-tree), and a stable-range theta lift to odd rank. The theta lift replaces the eigenvariety parity trick. Arthur–Clozel base change completes the construction. The statement is weaker than Chenevier–Harris/Caraiani: WD matching away from l holds only for abelian N = 0 parameters, and there is no purity clause (though purity is used downstream, see above). It is not circular: an import closure of 66,168 files was checked with no self-reference.

---

## 9. What has and has not been checked

### 9.1 Step by step

"Read to" levels: **C** = down to classical statements; **N** = to a named new idea; **S** = statement or top level only.

| step | read to | numerical check | main unread items |
|---|---|---|---|
| Windowed Landau | C (correct theorem) | — | at least eight bodies: `landau_tails`, `landau_nearest`, `landau_pole_asym`, `landau_cauchy`, `landau_growth_contra`, `poleData_char` past l.175, `Gchi_growth`, `windowHyp_of_rpow`; whether `ChainTied` forces e_D + e_L + 7 > 0 [LANDAU §4–5] |
| Bridge ASK ↔ G_m | C (exact identity) | — | `TwistForm` definition; existence of TT with exact shares. (The identity is constant-free; the true L′/L is pinned by `HostAddCharCompatible`) |
| Hosts, (q, d), ThinScales | C | — | bodies of `stage1`/`stage2` (density), `levelData`, `classSel` |
| Gaussian class of the kernel | C, six links (arithmetic leaves read later, in LEAVES) | NUMTEST3/4, LEAVES (NormRel to T^{260}) | the link `baseChange_preserves_unitary_of` (admitted + RestBeta + RestGc ⇒ class); the content of `CmpHyp.pos`. (`restGc` was read in full and `HhDecomp` found proved [GAUSSCLASS]; the one-copy step was confirmed in LEAVES) |
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

1. **Rank-uniform limit multiplicity with exponential precision** [COUNT; FORMULAGAP]. New idea: an exact cusp-form projection by Schur orthogonality, plus a closed compression formula for lowest-K-type coefficients of non-holomorphic discrete series.
2. **Near-orthogonality of Bessel periods to relative b^{−6}** [PAIRB; COUNTS; THMB]. New idea: double unfolding with savings from counting, from level, and from a Gauss-sum cancellation on a hermitian quadric.
3. **p-adic divisibility of high-order jets of higher-rank CM theta kernels** [GAUSSCLASS; HIGHERRANK; JETA]. New idea: the polarisation of log σ* is the unique hermitian Dieudonné pairing; isotropy at split places kills self-terms; the cap lemma for column minors. The method is recognisable. As a statement it was not known to the readers.
4. **Selmer bounds uniform in l for weights up to x^{401}** [ONECHARU; MODU3; PATCH]. New idea: Skinner–Wiles for U(3) with patching at reducible nice points through a determinantal local model.
5. **Selmer killing at finite level** [KILLAT; ORDER]. New idea: a square presentation over a finite tame tower, plus the two-pass construction.
6. **Residual irreducibility at all l** [TWIST]. New idea: depth-zero types at pigeonholed level primes.
7. **Galois representations** [GALREP]. New idea: the stable-range theta lift replacing the parity trick. The resulting statement is weaker than the literature's.
8. **Uniform arithmetic volume and covolume bounds on varying Shimura varieties** [VOLUME; HS]. New idea: an effective finite-level Hilbert–Samuel bound and a structural intersection formula (`ThmB`). The bound is weak but sufficient.

### 9.3 What remains conceptually unclear

- **Why the per-lift error must grow with m** [WHYHALF §6.7; SEESAW §3]. See the sharpness paragraph of §6 and hole H4. WHYHALF calls this the conceptual heart of "why 1/2".
- **How the towers are joined** [ARCH §7.1, §7.7; SEESAW §3]. See hole H1. In addition, nobody showed that the layer index matches the lift index one for one.
- **The seesaw constant** [SEESAW oddity 3]. a_u is existential and depends on the word. Whether the frame argument needs it uniform was not checked. Near-orthogonality is a metric statement about P_u, and why it is insensitive to the unknown a_u is not explained by the nodes.
- **The twisted-place set** [JOIN §2c]. See hole H3.
- **Dimensions and level structure** [ARCH §7.3, §7.5]. The ratio of the two d_u's (dim Mram versus dim Mu0) is not stated. The reading of Mram as "new at T" is inferred.
- **Design choices** [WHYHALF §6.1, §6.3, §4]. Why the weight must be exponential rather than a large power of x. Why orbit length n′ > 2 is needed. Why the shares are 4 : 3; any positive perturbation would do for Landau.
- **Behrend** [WHYHALF §6.6]. `BehrendSets` is present in the tree and plausibly chooses the thick set T2. It was not traced to the live path.

### 9.4 Holes in the chain

These are the places where the chain as reconstructed has a gap: a step that is a hypothesis with no supplier found, or a supplier not traced from the live path. They follow REVIEW-MAIN-ARGUMENT A2.

- **H1. The determinant identity** (between the height/covolume steps and the final chain). The final chain needs μ(RR^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + …, i.e. det ι = κ^D·∏_j det θ_j. This is a hypothesis of `BoundsMu` (SO:31-41), inferred by SEESAW from the similitude clauses `l1c`/`l1d`. No derivation was found, and no theorem factors ι through the θ_j. The supplier of `l1c` is untraced [ARCH §7.1; SEESAW §3, child 6–7]. *Status: being read.*
- **H2. The seesaw supplier.** `mainX_of_lawsX` is an honest m-step seesaw, conditional on its own hypotheses. But JOIN traced the root's producer of `MIid` through several layers without reaching it, and several other producers exist [SEESAW §0.3, §7; JOIN §1d].
- **H3. The twisted-place set.** Untwisted places must contribute index 0. That needs Tw = {resChar ≤ X″} ∪ {d, g₀, g₁}, which is equivalent to integral theta-unimodularity of θ_j at every good p > X″. Its proof, and the suppliers `IndefSide.on`/`Untwisted`, were not located [JOIN §2c; SEESAW §4, child 1].
- **H4. The layer signatures.** (k+j−1, m−j) is an input (`FactKaBlocks`, ROWS:250-251), with no derivation. It is the source of the per-lift growth, and hence of "1/2". Its only stated reason is the count Σ_j(p_j − q_j) = mk [SEESAW §3; ARCH §7.1]. *Status: being read.*
- **H5. Satisfiability, not logic.** For the hypotheses to be jointly true, Ga − ASK ≲ budget must hold. The Lean neither proves nor needs it [ACCOUNT §0.4]. PAIRING gives a paper argument that it holds for the Hecke-route tops (§5.4, item 5). No node addresses the orbit-route primes.

The status of the conditional suppliers bears on all of these: the seesaw supplier (H2), Theorem S and `LinkIRR` (§7), and L6 (seven `Published` premises, §5.1).

---

## 10. Correspondence with the author's timeline

1. *Stepanov determinant.* Not located as an object. The analogy is structural (§6) [WHYHALF §2].
2. *D℘ ≡ 0; Dᵃ(Ω·θ)(0) divisible by p^{a/p+a/p³+…−O(log a)}.* Located: γ_p·a = Σ_{e odd} a/p^e, the LT divisibility [LOCALDIV; NUMTEST].
3. *qN = M^k + R; μ automorphic from θ on the sixfold cover of GL₅; Poincaré bundle.* Not located. (A directory named `GL5/` holds a rank-2 mass formula [THETA]. Its relation to this item was not established.)
4. *W(1_S) ≥ 0 via a determinant; multiplicity one; bootstrap.* Not located.
5. *Switch to Σ Λ(n)(X/n − 1)₊ − X log X + (1+γ)X.* Located: this is exactly G_z [LANDAU §1a].
6. *W·1_{(0,1]} + (∼X^η)·1_{(0,1/X]} ≥ 0.* Not located.
7. *Determinants of W(·) containing GGP periods; interlacing, or up to m non-interlacing weights.* GGP/Bessel periods located (§3.3). The "m non-interlacing" link is an inference [WHYHALF §6.7].
8. *Iterated theta lifts between totally definite unitary groups, π ↦ π ⊞ μ_j[t], multiplicity m, m like √X.* Located: column tower, Speh blocks, m ≈ √x [ARCH; LINKN; CHAININD].
9. *Norms of lifts, level, cancellation of order-m terms via Chowla–Selberg, Weyl, Siegel mass.* Located (inferred match): the logΩ cancellation with Σ(p_j − q_j) = mk [WHYHALF §1.5; DIV].
10. *Sufficient lower bound on divisibility of the m-fold lift.* Located [CHAININD; ORBIT].
11. *Iwasawa tower via pigeonhole on 𝔽_{qⁿ}/𝔽_q.* Not located (SUMMARY §7). *(inferred candidates: the 2-power layer of the host, or KILLAT's tame tower.)*
12. *Seesaw: period of the iterated lift is a Bessel period independent of Hecke characters; Rallis.* Located: `MIid` with twist unit ζ; Rallis scalars λ_j [SEESAW; L6].
13. *Bost slope inequality.* Located [RANK].
14. *Cost of each lift; 2/3 a priori; kill via twisting; "division".* Per-lift cost located [WHYHALF §1]. The 2/3 version was not located; WHYHALF infers it from a per-lift cost ∝ m². "Twisting" matches KillAt; "division" plausibly matches DIV *(inferred)*.
15. *Glue an integral structure across Hecke characters.* Located: RR glued across types [CONGMOD §2a].
16. *Relative trace formula; Cauchy–Schwarz; projected Poincaré series; approximate orthogonality.* Located: Theorem S [PAIRB; RANK]. The GL₅ part was not located.
17. *Classes in H¹(O_E[1/ℓ], ℚ_ℓ/ℤ_ℓ(−e)) not killed by twisting; weakening of Vandiver.* Located: the Ш bound via U(3) [VWIN; ONECHARU].
18. *Covolumes, theta-series index, congruences between lifts and forms.* Located [COVOL; JOIN; CONGMOD].
19. *Precise choice of the Iwasawa tower using Behrend.* `BehrendSets` located, not traced to the live path [WHYHALF §6.6; KILLAT].
20. *GRH.* Located: the level ⟨ψ⟩ with 4 : 3 shares, plus windowed Landau [CHBALANCE; LANDAU].

---

[^n4]: Audit history. NUMTEST4 described the served class as "inert in both", which was wrong; SIGNAL corrects it. Per SUMMARY §11 the NUMTEST3 instance was a signal place.

[^tiebm]: Audit history. The orphaned `TieBm` formulation, in which the middle levels are set to 0, has no consumer, so ARCH's worry about it lapses [SEESAW §0.1].
