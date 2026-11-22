# The main argument, reconstructed from the Lean source

> **Status.**
> 1. This document gives a continuous mathematical account of the argument in the alpo.ge Lean tree (SHA-256 `9631b4f0…49c7fc`). The tree claims RH and GRH for Dirichlet L-functions.
> 2. It is a reconstruction by reading. Reader agents each read one piece over fifteen rounds (100 nodes), cited in brackets, e.g. [ENGINE], and two cold reviews read the document (§9.7). Nothing was compiled or run in Lean. After round 15 every step of §0 has a mechanism read on the live path, and no defect has been found; what rests on statements only is listed in §9.4.
> 3. "Proved" means that a proof term exists in the tree. It does not mean the term was checked, or that its leaves were read.
> 4. Where nodes conflict, the newer node wins; the corrections that change the picture are listed at the end, and SUMMARY §5–§17 records them all. *(inferred)* marks an inference by a node or by the auditors. "Not established by the reading" marks a gap the nodes leave open.
> 5. This document describes the argument. It does not vouch for it. §9 states what has been read, what rests on statements only, and what is still not understood.

> **Notation** [ACCOUNT §1; CHBALANCE §1; SERVED §1]. The Lean reuses letters; this document does not.
>
> | symbol | meaning here |
> |---|---|
> | x; ε; b; a | the scale; the small parameter (never a character; the cyclotomic character is ω); e^{x^ε}; x·b |
> | Y; Y_{qd}; Y_j | Landau window base [Y, Y^{3/2}]; the (q, d)-selection scale X^{1/J}, one per window, with the window inside [X^{1/J}, X] (§2.3); row-tower spaces |
> | χ_{−d} | (−d/·), the character of K = ℚ(√−d), d ≡ 7 mod 16 prime. Nodes writing χ_d mean the same character |
> | q; q_v; (p_j, q_j) | the auxiliary prime q ≡ 3 mod 8; a residue-field size (§7); the signature of W_j |
> | n; Φ; f; r | n = \|A\| where Gal(E/ℚ) = {±1}² × A and [E:ℚ] = 4n; Φ = Gal(E/K), the "places" ρ; f = \|Φ\| = 2n; r = k + m − 1 (the rank; COUNT, GERMJET write n) |
> | 2^{e₂}; e; i | the cyclic 2-power quotient of A; an odd distance on a Frobenius orbit; a Tate twist (§8) |
> | TT; a_t; t | tops, TT ⊂ A, x^{−ε/8}n/2 ≤ \|TT\| ≤ n; the weight of top t; t is a top, or in ranks the odd block length (N(j) = k + j(t+1)), also the Speh length of §8 |
> | T (= T_u); π_T | the type prime of word u, a rational prime split in E; π_T ∈ O_E with π_T·π̄_T = T (§5.5) |
> | η; η_F, e_F | the one polynomial parameter (thick caps w ∈ [b, b+η+1]; η = 2m⌈x^{ch}⌉, §4.7); the frame tightness of §5.3 |
> | partner(t, g); w_{j,ρ} | the place cconj + g + topPl(t) ∈ Φ met from top t by Frobenius g; the cap at ρ, level j: thick w ∈ [b, b+η+1] (a/w ≈ x), top w ≤ 2b′, thin w ≈ w″ |
> | X′; b′; w″; X″ | e^{x^{ε/3}}; a/X′; b′/(xn); a/w″ = xnX′ |
> | δ; δ_p | \|T2\|/n ≥ x^{−ε}, T2 the thick places; ≤ e^{−x^{ε_z/7}}, with dim EE = (1−δ_p)·dim HH |
> | U; B₀ | \|TT\|·m·b·δ/2 ≈ x^{2.5}b, the signal unit (budget U·x^{1/2+O(ε)}); f·m·b·x^ε, the per-lift error unit |
> | ph; logΩ | y log y − y; γ + log(π/v) − L′/L(1, χ_{−d}) with v = rd_E/2 |
> | κ; I, I₁ | the similitude constant of ι; frame-row index sets (§7, RANK's κ, κ₁) |
> | BL; P; HH; H_B | Bost loss (§5.3); Selmer presentation (§8); the L² space (§3.1); the Bost scale x^{C_H}b (§5.3). Φ is only Gal(E/K); the Laplace transform of §2.1 is ℒ, the Schwartz datum of §4.1 is 𝒮, and §2.1's window letters carry a subscript L |
> | Ga; sg(u, w); LoP | the gain, a defined formula (§5.4); the per-place exponent Σ_j(gain_j + F_j − E_j); the loss allowance C·\|TT\|·m·b |
> | cc; E1, E2, E3 | the target lattice of the DIV map, whose slope is bounded through μ(RR^∨) by a base-to-column passage (§5.4); the three index errors of the covolume bound (§5.2) |
>
> *Sign of Ω.* COVOL writes the proved Chowla–Selberg identity as "−meanLog = γ + log(2π/√d) − L′/L", HEIGHT as "mean_ρ log(area(Λ^ρ)/π) = …". So logΩ = −meanLog in COVOL's sign; √d versus rd_E is a separate proved identity [COVOL §2; HEIGHT child 3].

---

## 0. The argument in one page

Fix a primitive Dirichlet character ψ, of order o, and ε ∈ (0, ε₁). Each step gives the Lean's statement and its node; each uses only earlier steps.

1. **The function.** G_m(y) = G_z(y) + (3o+1)^{−1} Σ_{ξ∈⟨ψ⟩, ξ*≠1} Re g_{ξ*}(y) (§1): Riesz-smoothed Chebyshev functions of ζ and of ⟨ψ⟩ with their main terms removed, all weights positive. The coefficient (3o+1)^{−1} is the Fourier coefficient at ψ^j of the share measure λ(h) = (3 + 1_{A₀}(h))/(3o+1) with which the tops are spread over A/A₀ [ENDGAME §1b, §2.3].
2. **A host for each window and scale.** An abelian CM field E ⊃ K = ℚ(√−d), Gal(E/ℚ) = {±1}² × A, in which ψ(p) is the A/A₀-coordinate of Frob_p. One pair q ≡ 3 mod 8, d ≡ 7 mod 16 (log q ≍ Y^{ε/5}) serves a whole Landau window: the 3o twists ξ(·/q)^i(·/d)^j, (i, j) ≠ 0, satisfy |g(y)| ≤ y^{1/2+ε/2} and |L′/L(1)| ≤ 4 log y on [Y, X] (`PairGood`), by orthogonality over moduli q > Z², Siegel and zero density: neither GRH nor the large sieve [HOSTSEL].
3. **The engine: one lift, one signal prime.** At a signal prime (inert in K, split in ℚ(√−q)) the positions form an even orbit, the kernel is exp(−cross Gaussian) × integral, and the self-Gaussians cancel. LP duality gives, per top, v_p ≥ Σ_{e odd}(a_t/p^e − cap)₊ − γ_p·Wc − (logs), cap = number of minors at the partner; at a thick partner the e = 1 term is the Riesz weight b·(a_t/(bp) − 1)₊. The kernel law is the Hecke route's theorem specialised: its one arithmetic input (`IntInert`) uses only (−d/p) = −1, and a Frobenius identity makes the frame hyperbolic [ENGINE2; ADM2; KLAW; §4.2–4.4].
4. **m lifts.** The one-lift bound holds on the whole global lattice of each level, so gains add along `chain_ge`; the exponent is the ledger's sg symbol for symbol (`liftI_of`) [ENGINE2 §4; GATIE §0.3].
5. **The gain is tied to a lattice.** Ga is a *defined* piecewise-linear formula, and the source lattice is *defined* as N_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋}·NuLat_u, sg = Σ_j(gain + F − E). Step 4 gives Bk_u(N_u) ⊆ cc on every branch: this inclusion *is* the p-adic divisibility of the actual chain maps. An exact slope formula gives μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo5 [GATIE; LEDGER L2].
6. **DIV.** μ(cc) + h(u) − Fo ≤ Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + c·|TT|·a·La + c·m(B₀+Nc)x^{2ε}: the height (Fock norms, Chowla–Selberg, Rallis hooks) meets the covolume bound, whose index errors E1, E2, E3 are per-lift; E2 is the only congruence input, Nc its allowance. The term −a_t·log T_u is where the scale x enters: T_u is the *type prime*, a rational prime split in E, one per word and shared by all m lifts; the source forms live at level T, and the last (Bessel) map reads the heavy last-row component in level-T coordinates, scaling its archimedean norm by T^{−a_t} at no T-adic cost, because divisibility by π̄_T^{nBr} (nBr ≈ a_t) *is* the integral structure at a level-T point (§5.5) [LEDGER L1; DIVKEY; STEPE; TU; TDIV].
7. **Bost.** s − log|W| − BL ≤ μ(cc), s the mean source slope net of heights: Bost on each Harder–Narasimhan piece, combined by a layer cake. It consumes *robust near-surjectivity* of ⊕B_u at one complex place, the sources overfilling the target by ≥ x^{C_H}; that comes from Theorem S and an explicit dimension count, both proved on the live path by named theorems (§5.3, §7) [RANK; NONVAN].
8. **Floors and the type prime.** μ(M_u) ≥ −c·|TT|·a·La(1+m/k), whose T-term is the mean weight (a/k)·log T; Ee ≤ m(ΣA·lg + cE·B₀) (adm11), including the loss m·EatT at T; and Count5, log T_u ≥ Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − c(La + m²La/k), an explicit dimension ratio: T is pinned by matching the level-T source dimension to the target [LEDGER L3–L5; TU; TFLOOR].
9. **Key identity.** Σ_t m(ph(a_t) − a_t logΩ) − ΣA·Lam5 + m·ΣA·lg = Main + ΣA·c(La + m²La/k) exactly, where Main = Σ_j Σ_t a_t(log a_t − 1 − γ + L′/L(1, χ_{−d}) − mean_ρ log w_{jρ}). The split half of log a! is the −L′/L(1, χ_{−d}) inside logΩ [LEDGER L7].
10. **Upper bound on the gain.** Steps 5–9 add, with Fo and h cancelling, to Ga ≤ Main + log|W| + (errors) (`Ga_bound5`) [LEDGER L9].
11. **Loss bound, and the main inequality.** ASK − Ga ≤ LoP = C·|TT|·m·b, ASK = Σ_t Σ_j Σ_n Λ(n)(1 − χ_{−d}(n))(a_t/n − w_{j,partner})₊: two explicit formulas with the same caps, no lattice [GATIE §0.2]. With step 10: ASK ≤ Main + ErrX5at, ErrX5at ≤ x^{5ε}·[|TT|·a(1+m²/k) + m(B₀+Nc)] [LEDGER L10–L12].
12. **Bridge.** ASK − MAIN = De exactly (orthogonality on Gal(E/ℚ)). Top and thin partners are discarded by an effective PNT (`ThinScales`). Only signal primes reach thick places, where the summand is the Riesz weight of step 3. Averaging gives U·[G_m(x) − SigA − 4x^{1/2+ε}] ≤ Σ(ASK − Main) + 2|TT|mb/x, U = |TT|·m·b·δ/2, with SigA ≤ 4o·x^{1/2+ε} by step 2 at y = x [LEDGER L13–L15; ENDGAME §2.3].
13. **Core bound.** Dividing by U: G_m(x) ≤ x^{1/2+9ε}, at every x ≥ x₀ of every window [Y, Y^{3/2}] of the family attached to ε; 9 = (2 + 0 + 3) + 3 + 1 (§6.2) [LEDGER §0.2].
14. **Landau on windows, and GRH.** A one-sided bound G ≤ C·y^θ on all y of windows [Y, Y^{1+δ_L}], Y → ∞, for a positive combination of g_χ, forces L(s, χ) ≠ 0 on Re s > θ for each χ in it; with ε → 0 separately for each s, L(s, ξ) ≠ 0 for Re s > 1/2 and every ξ ∈ ⟨ψ⟩, ζ included [ENDGAME §1c, §2.1].

**Where 1/2 arises.** Divided by U, the error *budget* of step 11 has three families [LEDGER §2a; SHARP]: one-off boundary terms (≈ |TT|·a·x^ε) give x/m; per-lift allowances (≈ B₀ = f·m·b·x^ε at each of m levels) give m; the E2 congruence allowance m·Nc, not a non-vanishing term, gives k/n² [NONVAN]. At m ≈ x^{1/2} each is x^{1/2+O(ε)}; at m = 1 the result is trivial. Most per-lift allowances far exceed actual use; the identified loss that genuinely grows like m per lift is at the type prime, where every lift is non-integral by about its weight mass (§6.4). Step 2 removes the split primes without producing cancellation. Steps 3–9 must hold to relative x^{−1/2+O(ε)}; step 11 to relative x^{−1}, formula against formula (§6.3).

---

## 1. The statement and the strategy

**Target.** Fix a primitive Dirichlet character ψ and the cyclic group ⟨ψ⟩ of order o. Put

$$G_z(y)=\sum_{n\le y}\Lambda(n)\Big(\frac yn-1\Big)-y\log y+(1+\gamma)y,\qquad g_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)\Big(\frac yn-1\Big)+y\,\frac{L'}{L}(1,\chi),$$

$$G_m(y)=G_z(y)+\frac{1}{3o+1}\sum_{\xi\in\langle\psi\rangle,\ \xi\ne1}\operatorname{Re}g_{\xi^*}(y),$$

where ξ* is the primitive character inducing ξ [ENDGAME §1b]. The tree proves L(s, ξ) ≠ 0 for Re s > 1/2 and every ξ ∈ ⟨ψ⟩ from the one-sided bound G_m(x) ≤ x^{1/2+9ε} at every point of a sequence of windows [Y, Y^{3/2}] (§0, step 13). All the RH-strength content sits in one inequality between the count ASK of inert prime powers (§0, step 11) and its main term; the rest is character bookkeeping (§2).

**The idea** [WHYHALF §2]. It is a Stepanov-type argument whose auxiliary object is a vector of periods of high-order Taylor jets of CM theta functions. *p-adically*, at p inert in K a jet of order a is divisible by about p^{Σ_{e odd}(a/p^e − w)₊}; summed with weight 2 log p, the uncapped part is the inert part of Chebyshev's log a! = Σ Λ(n)⌊a/n⌋. *Archimedeanly*, the same jet has size a!·Ω^{−a}, and log Ω contains the split part through −L′/L(1, χ_{−d}). One copy is Chebyshev quality. The gain comes from multiplicity: the jets are chained through m ≈ √x theta lifts, so the divisibility recurs m times [CHAININD]. The comparison is made for lattices through Bost's slope inequality, with relative error ≈ 1/m + m/x (§6).

**Sizes** [LEDGER §2a; ACCOUNT §1; ARCH §6]. The live record assumes 0 < ε < 1/52.

| quantity | size |
|---|---|
| b | e^{x^ε} |
| weight a | x·b |
| tops a_t | in [a, a + a/(k·x^{13})], i.e. a(1 + O(x^{−17.5})) |
| host degree [E:ℚ] | 4n, n ∈ [1, 2]·x^{2+8ε}; f = 2n; \|TT\| ≥ x^{−ε/8}n/2 |
| m | ∈ [1, 2]·x^{1/2−ε/16} |
| k | ∈ [1, 2]·x^{9/2+10ε} |
| signal unit U = \|TT\|·m·b·δ/2 | ∈ [x^{5/2+6.8ε}/4, 2x^{5/2+8ε}]·b |
| t | ≈ x^{398.5+O(ε)} |
| top column rank N(m) | ≈ x^{399} |

t is fixed by r + t = 8fr + 4 + ⌈x^{377}⌉·nWv [ACCOUNT §1]; no node says why it has this shape.

---

## 2. The analytic frame

### 2.1 The windowed Landau lemma

**Statement** (`zeroFree_of_rpow_window`, called with δ_L = 1/2, C = 1) [ENDGAME §1c]. Let χ_i be finitely many Dirichlet characters with weights a_i > 0, G_F = Σ a_i Re g_{χ_i}, 0 < θ < 1, δ_L > 0. Suppose that for every Y₀ there is Y ≥ Y₀ with G_F(y) ≤ C·y^θ for *all* y ∈ [Y, Y^{1+δ_L}]. Then L(s, χ_i) ≠ 0 for every i and every Re s > θ. Off the windows only the trivial |g_χ(y)| ≤ C·y² is used. The conclusion holds for each L-function separately, ζ included.

**Mechanism** [ENDGAME §2.2]. In u = log y, the Laplace transform ℒ of g(u) = G_F(e^u) is −Σ a_i(L′/L(s, χ_i) − s·L′/L(1, χ_i))/(s(s−1)): the main terms cancel the pole at 1, and ℒ has simple poles at zeros. The residue at ρ is S(ρ)·(−1/(ρ(ρ−1))) with S(ρ) > 0, so positive weights cannot cancel a zero, and a real zero pushes G *up*; positivity of Dirichlet coefficients is never used. The coefficients a_{k_L}(z) = ∫ g(u)u^{k_L} e^{−zu}/k_L! du are bounded from the one-sided bound on a window J_L = [V_L, (1+δ_L)V_L], since |g| + g ≤ 2R there; the extra Re a_{k_L}(σ) is the price of one-sidedness. With k_L ≈ (1+δ_L/2)σV_L the Gamma kernel concentrates on J_L, and σ = 336 (for δ_L = 1/2) makes the tails ≤ C/σ^{k_L}. A zero with Re ρ₀ > θ gives a pole at distance d < σ − θ. Either it is real and its positive residue makes Re a_{k_L}(σ) ≳ d^{−k_L−1}, or an ordinate γ_L is chosen so that one pole is the *unique* nearest singularity to σ + iγ_L. Either way a_{k_L} grows like d^{−k_L}, against (σ−θ)^{−k_L}.

**Why sparse windows suffice.** The radii depend only on σ and the zero set, never on V_L, and each window supplies one k_L. So any windows with V_L → ∞ and fixed log-ratio work, provided the bound holds at *every* y of each window. ENDGAME read every body except the routine `iteratedDeriv_laplace` and judged it a correct theorem with a correct proof.

### 2.2 How ψ enters: the host and the shares

Every hermitian space lives over a CM field E, the host, built for each scale x from a pair (q, d) fixed per window [HOSTS §1(a), §2(c1); HOSTSEL]. E is the fixed field, inside ℚ(ζ_{QS·q·d}), of the kernel {a ≡ ±1 mod 2^{e₂+2}, ψ(a) = 1, (a/q) = (a/d) = 1} of the Artin map [ENDGAME §2.3]. So ψ factors through Gal(E/ℚ) = {±1}² × A, [E:ℚ] = 4n. A₀ = ⟨a₀⟩ embeds in the 2-power quotient, |A/A₀| = o, and every frame character trivial on A₀ is ξ·(·/q)^i(·/d)^j with ξ ∈ ⟨ψ⟩. **ψ(p) is read off as the A/A₀-coset of Frob_p.** Each auxiliary object has one job:

- **K = ℚ(√−d)**, d ≡ 7 mod 16 prime: the CM curve behind every theta kernel, supersingular reduction at inert p, the factor (1 − χ_{−d}), and L′/L(1, χ_{−d}) inside Ω [ARCH §1].
- **√−q**, q ≡ 3 mod 8, (−d/q) = 1, separates *signal* primes (inert in K, split in ℚ(√−q)) from *inertClass* primes (inert in both) [LEDGER §0.4]. At a signal prime the hermitian space is split.[^n4]
- **The 2-power layer**, of order 2^{e₂} ≈ x^{2+8ε}: an inertClass prime has a split hermitian form iff h has even order; the anisotropic ones (density ≤ x^{−2}) are dropped [SERVED §0].
- **The level primes g₀, g₁** give the Poincaré series a level and carry depth-zero types forcing residual irreducibility at every l [PAIRB; TWIST; ORDER]. **T_u**, the type prime, one per word u and shared by all m lifts, sets the level of the source forms and carries the scale x into the archimedean main term (§5.5).

**The shares.** The tops are distributed over A/A₀ by λ(h) = (3 + 1_{A₀}(h))/(3o+1), with λ̂(ψ^j) = (3o+1)^{−1} for j ≠ 0: the weight in G_m [ENDGAME §2.3; CHBALANCE §2(a)]. Any α + β·1_{A₀} with α ≥ 0, β > 0 would do; uniform shares would leave only ζ. No reason for the 3 was found. ζ has weight 1, so the core bound alone would give RH.

### 2.3 What is counted, and the bridge

**Which primes.** ASK counts n = p^i, p inert in K, i odd, with the cap w at the partner place: Σ Λ(n)(1 − χ_{−d}(n))(a/n − w)₊ [ENDGAME §2.3; LEDGER §2c]. Only signal primes have thick partners (w ≈ b, a/w ≈ x); inertClass partners are top or thin, with Riesz length ≥ X′/2. The thick-class indicator is a combination of the 4o characters (·/d)^α(·/q)^β ψ^j. After averaging, the (α, β) = (0, 0) part is exactly U·G_m(x); the 3o twisted characters make SigA.

The bridge (`ch_balance`, `ch_core`) is an exact finite-group computation [CHBALANCE §0–2].

**Step 1 (exact identity).** Orthogonality on Gal(E/ℚ) gives ASK − MAIN = De, where

$$\mathrm{MAIN}=a\Big(\log a-1-\gamma+\frac{L'}{L}(1,\chi_{-d})-\operatorname*{mean}_{\rho\in\Phi}\log w(\rho)\Big)$$

and De = |Φ|^{−1} Σ_g Σ_ψ ψ̄(g)·w·G_ψ(a/w) is an expansion over all characters of the Galois group (G_χ is the g_χ of §1). The identity uses

$$\sum_n\Lambda\chi(n)(a/n-w)_+=w\,G_\chi(a/w)-a\,\tfrac{L'}{L}(1,\chi).$$

The identity holds with an *arbitrary* constant in place of L′/L(1, χ) (CHBALANCE oddity 1); the true value is pinned by the host clause `HostAddCharCompatible` [SERVED §0].

**Step 2 (thin and top partners drop).** There the Riesz length is ≥ X′/3, and `ThinScales`, |G_χ(y)| ≤ y·e^{−cx^{ε/8}} for y ≥ X′/3, makes them negligible: de la Vallée Poussin with an in-tree zero-free region, real zeros β > 1 − 1/400 being excluded by host-selected boxes [ENDGAME §2.1; SERVED Part 2].

**Step 3 (thick partners and averaging).** **The x-scale part of ASK, which carries ψ, sits entirely on signal primes** [SIGNAL §0.5; LEDGER §2c]. Averaging over u₀ ∈ A₀ and the tops turns λ into the weights of G_m.

**Result.** The bridge gives

$$U\cdot\big[G_m(x)-\mathrm{Sig}_A(x)-4x^{1/2+\varepsilon}\big]\ \le\ \sum(\mathrm{ASK}-\mathrm{MAIN})+\frac{2|TT|mb}{x},\qquad U=\tfrac12|TT|\cdot m\cdot b\cdot\delta .$$

Every replacement error is ≈ x^{1/4+ε}·U, far below x^{1/2}·U, and `ch_core` absorbs them into a crude 4x^{1/2+ε}; the x^{1/2} comes only from Err/U and Sig_A [CHBALANCE §0, §2(c)].

**The twists are bounded, not cancelled.** Sig_A collects the 3o twists [ENDGAME §2.3]. They never enter the function given to Landau; each is bounded *two-sidedly at the single point y = x* (`bdG` ← `PairGood.bounds`), and Sig_A ≤ 4o·x^{1/2+ε}. Through

$$\sum\Lambda\psi^j(1-\chi_{-d})(x/n-1)=\sum\Lambda\psi^j(x/n-1)-\sum\Lambda\psi^j\chi_{-d}(x/n-1),$$

this bound lets a count over inert primes stand in for the sum over all primes. **The split half of the primes is paid for by the choice of (q, d)**, so L(s, ψχ_{−d}) never enters ℒ and cannot cancel a zero of L(s, ψ). G_m involves only ζ and ⟨ψ⟩, so the change of host is invisible to Landau.

**Host selection** [HOSTSEL] (`PairEx`, closed, read). `winPairs` fixes (q, d) at Y = X^{1/J} *before* quantifying over x; the bound is proved on [X^{1/J}, X], holds for every ξ mod N, and is consumed at y = x plus one Lipschitz step. Every modulus exceeds Z² = Y^{800K}; reciprocity and a Gallagher-type PNT in progressions bound the off-diagonal except at one s = n\* (Landau–Page), the diagonal is C·y log y, and Markov on dyadic blocks gives a bad proportion ≲ Y^{−τ}. Siegel enters only there, making Y₀ ineffective. Moduli with a twist zero in Re s > 1 − 1/400 inside a box are removed by zero density; this box is what the tail bound beyond Z needs, and it gives |L′/L(1, χ_{−d})| ≤ 4 log x. Averaging excludes ≤ ½ of the q, then ≤ ½ of the d.

### 2.4 The order of quantifiers

[ENDGAME §2.1; LEDGER §0.2]
ψ; then e_D, e_L, ε₁ from `TopG` (live: 2, 0); then s with Re s > 1/2, θ = 1/2 + min(Re s − 1/2, 1/2)/2 < Re s; then ε ∈ (0, ε₁) with 9ε ≤ θ − 1/2; then a family `FamP ε` with windows [Y, Y^{3/2}] for arbitrarily large Y; then, for each window, one (q, d) at Y_{qd} = X^{1/J}; then, for each scale x of the window, E, the frame, TT and the lattice data; then the core bound at every x ≥ x₀ of every window; then Landau with δ_L = 1/2. Nothing is uniform in ε: each s gets its own ε, family and hosts.

---

## 3. The objects

### 3.1 Three towers

All spaces are hermitian over E. They are unimodular at the base, with ranks fixed by k, m (even), t (odd), r = k + m − 1 and N(j) = k + j(t+1) [ARCH §2].

- **Column tower**, X_0 ⊂ X_1 ⊂ … ⊂ X_m, totally definite of rank N(j), carrying *algebraic modular forms*. The level-j weight at a top is (a_t, small…, −b_t, −w_1^{×(t+1)}, …, −w_j^{×(t+1)}), so **the same large entry a_t sits at every level** and each lift adds a block at the cap weight w_j [CHAININD §1.1]. The p-adic divisibility lives here.
- **Row tower**, Y_m, …, Y_0, of rank r + jt. Y_m ≅ X_⊥ is the complement of an anisotropic vector in X_m. Y_0 = X_0 ⊕ ⟨z⟩ ⊕ r_S hyperbolic planes, r_S = m/2 − 1, has signature (k + m/2 − 1, m/2) and genuine L² automorphic forms. HH is the discrete-series, level-(g₀g₁) part of L²(U(Y_0)), of dimension D_all; inside it EE, of dimension (1 − δ_p)D_all, carries the target lattice RR.
- **Layers**, W_1, …, W_m, of rank r and signature (k+j−1, m−j), inner forms of U(Y_0) at every finite place, each paired with a definite V_j of rank r + t. The layer lattices M_j of integral cusp forms supply the covolume of RR through a determinant identity (§5.2).

### 3.2 Maps

- **Column steps** K_j [ARCH §4(a)]. They are given by

  $$K_j\varphi(c')=\sum_{c}|\mathrm{Stab}\,c|^{-1}\rho_j(c)\rho_j'(c')\cdot\mathrm{divDe}\circ\mathrm{unf}_j(c,c')\circ\mathrm{sharp}(\varphi(c)),$$

  where unf_j(c, c′) is **the Taylor jet at 0 of a CM theta function θ_{c,c′} attached to a pair of lattice classes**, ρ_j, ρ′_j are unitary determinant characters, and sharp, divDe are diagonal normalisations. The chain is col = K_{m−1}∘…∘K_0.

  θ_{c,c′} is written out in §4.1; the jet is paired against column minors, whose number is the cap [HIGHERRANK §1.2].
- **Row descent** io_j : Mult(j+1) → Mult(j). It is tied by Petersson adjointness to a genuine theta lift. The composite is ι : (top forms) → EE.
- **Layer lifts** θ_j : (forms on U(V_j)) → (forms on U(W_j)). Each is a λ_j-similitude on Hecke parts, where λ_j is the Rallis θθ* eigenvalue. The descent ι is a κ·∏λ_j-similitude. There is one λ, shared by construction (`LevelLink` is `rfl`) [SEESAW §3].
- **Poincaré series** P_u : C_u → HH over the Bessel subgroup R_u = U(X_0) ⋉ N, C_u the source space at level T_u; P_u* is the Bessel period map [PAIRB §0]. The **Bessel pairing** is B_u : N_u → RR^∨, (B_uφ)(F) = ⟨sEE F, P_uφ⟩ up to a nonzero scalar and unitary changes of basis [WRITEUP S11].

### 3.3 The seesaw

The top period of the m-fold column lift is the codimension-one Gross–Prasad period ∫_{[U(X_⊥)]}(K_{m−1}⋯K_0 φ)|_{U(X_⊥)}·F. The live identity joining it to the bottom is `MIid` [SEESAW §0]:

$$\zeta_{u,t}\cdot\mathrm{Pt}_u(\varphi,F)=a_u\cdot\big\langle \mathrm{sEE}(V\,\Theta_t F),\,P_u(U_u\varphi)\big\rangle_{HH},$$

with V and U_u isometries, a_u ≠ 0, and ζ a unit at twisted tuples. Its live supplier is an honest m-step seesaw done two levels at a time, conditional on its own hypotheses [SEESAW §0.3; LIVEPATH].[^tiebm] It is stated as **transport of linear relations**, so a_u is never computed. B_u is *defined* as the period pulled back along ι, and RR as ι(Λ), so B_u(N_u) ⊆ RR^∨ is literally integrality of the column period [SEESAW §4]. a_u is used only in the frame (§7).

```
 COLUMN (definite; p-adic side)          ROW (descent)                       LAYERS (covolume side)
 X_m  rank k+m(t+1)  ⊃  X_⊥ ≅ Y_m ──── top Gross–Prasad period ────┐        V_j (definite, r+t)
  ↑ K_{m−1}  (jet of CM theta)          ↓ io_{m−1}                  │          │ θ_j  (λ_j-similitude)
  ⋮                                      ⋮                           │          ↓
 X_1  rank k+t+1        ⊂    Y_1                                     │        W_j : rank r, sig (k+j−1, m−j),
  ↑ K_0                                  ↓ io_0                      │              lattice M_j of cusp forms
 X_0  rank k (definite) ⊂    Y_0 (sig (k+m/2−1, m/2)) ⊃ U(X_0)⋉N     │        j = 1..m;  W_m definite
  │                                       ↑                          │
  │  N_u = 𝔭^{−⌊e·sg⌋}·NuLat_u            │ P_u (Poincaré series)    │   covol(RR) = κ^D·∏_j det θ_j (SpecDet, §5.2)
  └──────── B_u = Bessel period  ──────→ EE^∨ ⊇ RR^∨ ←── RR = ι(Λ) ←─┘   ⇒ μ(RR^∨) via lcv(M_j)
         MIid:  ζ·Pt_u(φ,F) = a_u·⟨sEE(VΘF), P_u(Uφ)⟩      (seesaw, m steps, two at a time)
```

**Sources.** For each word u (a binary string of length k; |W| ≥ C0·Γ²x^{C_H}, Γ = e^{Cm⁵fx^ε}) the source is N_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋}·NuLat_u, NuLat_u ⊆ M_u, by definition (`NprimeDef`; §5.4) [GATIE §0.3].

---

## 4. The engine: p-adic divisibility at inert primes

Two routes prove the one-lift bound, for two classes of inert prime p ≥ 5 [ADM2; LEDGER §0.4; ENGINE2]. The primes that carry the count are the **signal** primes: only they reach thick places, where the ASK summand is the Riesz weight at p ≈ x (§2.3). They are served by the **orbit route** (§4.3). The **Hecke route** of ENGINE (§4.4) serves inertClass primes of even order. Their partners are top or thin, and the bridge discards them by ThinScales. Both routes rest on one local core (§4.2).

### 4.1 The function and the coordinate

**The kernel** [ENGINE §1.1–1.2]. Let Tau ≃ Gal(E/K) be the CM type. The space is VV = ℂ^{Tau×N′×N} with hermitian form H(z, w) = area(Λ)^{−1}·Σ z_{τij}w̄_{τij} and lattice Λ = δ·Φ_Tau(AA0·Hom(N, N′)), δ·O_K the period lattice of the CM curve. θ_{c,c′} is a reduced theta function for (H, α, Λ), a **finite Heisenberg sum of torsion translates of one vacuum theta**:

$$\theta_{c,c'}(z)=\sum_{x\in\Lambda/A}\alpha(x)\,U_x\Big[\sum_{y\in\Lambda/B}\widehat{\mathcal S}(\cdot-x)(y)\,\alpha(y)\,U_y\,\theta_{\rm vac}\Big](z),$$

with 𝒮 the finite Schwartz datum of (c, c′) and A, B half-lattices twisted at SS. θ_vac is built from th0(z) = U_t(σ*)(z)/U_t(σ*)(0), t = ω₀/2, σ* = σ·e^{−s₂z²/2}. The Gaussian is not multiplied in separately: at ∞ it is the automorphy factor in U_x, p-adically the class of ph = −log(σ*(εℓ(T))/T).

**Why the Lubin–Tate coordinate is legitimate** *(KLAW's computation)*. The kernel's CM type is Psi = ker χ_{−d} ⊂ Gal(E/ℚ), the type lifted from K. At every place above a prime inert in K, χ_{−d}(Frob) = −1, so half the embeddings at that place lie in the type and the slope is 1/2 everywhere, signal and inertClass primes alike. The abelian variety is isogenous to a power of the supersingular CM curve; no ordinary factor occurs.

**The coordinate** [ENGINE §1.3]. At inert p the CM curve is supersingular, with height-two Honda logarithm ℓ(X) = Σ_j X^{p^{2j}}/p^j. The kernel's variables are z = ℓ(X), and "integral" means integral in X. With ϖ^{p²−1} = p, a series integral in X is integral in z/ϖ, so

$$v\big(\partial^n f(0)\big)\ \ge\ v(n!)-\frac{|n|}{p^2-1}\qquad(f\ \text{integral in }X).$$

Since v_p(a!) ≈ Σ_{e≥1} a/p^e and a/(p²−1) = Σ_{e even ≥ 2} a/p^e, what survives is γ_p·a with γ_p = p/(p²−1) = Σ_{e odd} p^{−e}. This is the author's item 2.

### 4.2 The common core

[ENGINE §2; ENGINE2 §0, §2.1; ADM2 §0–§1]
1. **Kernel law.** At a served place the kernel is exp(−Ph)·U, with U integral (bounded coefficients, no growth) in the height-two LT parameter X, and Ph ≃ Σ_e be(x_e, y_e) a cross Gaussian between the two halves of the orbit, with no diagonal terms (≃: up to a factor whose exponential is integral). It does *not* claim σ* integral. The content is the class be ≃ G_ser(c, σc), with 1/p part c(xy^p − x^p y)/p (Dieudonné/Honda), c a unit (NUMTEST's measured a/(p²−1) is attained) [ADM2]. After rescaling positions by ϖ, Dwork gives θ ∈ O[[Z]][hh/p] for an explicit cross form hh: **each power of hh/p costs one p.**
2. **Even orbit; self-Gaussians cancel.** The orbit has even length on both routes: ord h is even at a served inertClass prime, and nP = 2·ord(2h) at every signal prime. Rotation by one swaps the two isotropic halves of the split hermitian space, and `hyperbolic_plane_split` leaves only the cross pairing: the only use of "split at p". The orbit route's condition B3 (every monomial of be has positive even- and odd-position degree) holds *by construction* of be, so it certifies nothing about the kernel; the cancellation is used in the kernel *equation* Θ = U·exp(−Σbe), through isotropy [KLAW oddity 1]. With odd length the gain would fall to a/(p²−1).
3. **Caps = number of minors.** The jet operator is (top linear forms)^{a_s} times column minors, one per column of the level-(j+1) Young diagram at each position. The cap is the first-row length (ν₂ at a top), **by definition**; its identification with the ledger's w is `LatTied` and `row_le` [PAIRING; ENGINE2].
4. **Legendre, Dwork, odd e.** The pieces of hh have degree p^{2l+1}, so only odd levels occur. With 1/(p−1) = γ_p + 1/(p²−1), the top variables keep γ_p·a, and **the minor variables pay their own rescaling out of their own factorials**. Each odd-level factor uses p^e top derivatives and costs one p, giving Σ_{e odd}(a/p^e − cap)₊. At split p the gain is 0 [WRITEUP S7].

### 4.3 The orbit route at a signal prime

[ENGINE2; SIGNAL; ORBIT; JETA]

**Setup.** Frob_p = ((+1, −1), h), and c = ((−1, −1), 1) is not a power of Frob, so every place of F = E^{⟨c⟩} above p splits in E. Positions run along the orbit of z ↦ z·Frob·c. Even positions lie over w (tops or thin), odd ones over w̄ (thick or thin), so every odd-distance partner of a top is thick or thin: dTop = ∞, no top–top exclusions, no Hecke operator, no colength.

**Kernel law** [KLAW]. `ThetaExpansionAllPlaces`: the adapted entry of the *global* theta kernel is U·exp(−Σ_{orbits} be), U integral, be satisfying B1–B4. Its supplier `normalisedFamily_standardBases_integrality` (read) is the Hecke-route theorem specialised. Its one arithmetic input, `HostLog` (exp(Σph(X_i))·Θ_orth(ℓ(X)) integral in the LT parameter), comes via `hostAt_inert` from `IntInert` (statement), whose only use of p is (−d/p) = −1; a hyperbolic frame and the class computation `HypShape_of`/`b0` (statements) then give the shape. The signal-specific part is proved and read: σ∘ρ_z = ρ_{z+1}∘conj (`exists_kur_frob_tauEmb_posPl`), so with conjugate-dual adapted bases at adjacent positions (`StdTie.adapted`, a hypothesis) the hermitian pairing is Σσ(g_z)g_{z′} = δ_{z+1,z′}, and each parity block is isotropic (`fOf_isotropic`). B3 then holds by construction (be is built from even-position x and odd-position y; be₀ = cob(ph); the torus average kills bidegree (1,1)); a hand check of the local picture agrees. Stated for every column choice and class pair, the law holds on the whole global lattice through the equality `KerEnt.lat_S`.

**Statement** (`split_bound_eleven_one`, `OrbitValuationBound`). Per lift and orbit the exponent is g0 + FOrb − errF:
- g0 = Σ_{tops}Σ_{e odd}(al_s/p^e − capU)₊ − dl, al = a_t − 2cG, capU = (family weight at the partner) − kaJ + cG;
- FOrb, the Gaussian-free LP value of the non-top rows;
- errF = γ_p·tops·(b + η + 1 + 3Sc) + c6·Σw/p + (digit sums).

**The e = 1 term is the Riesz weight** *(ENGINE2's arithmetic)*. At a thick partner the family weight lies in [b, b+η+1], and a_t = a(1 + O(x^{−17.5})), a = x·b. So

$$\Big(\frac{al}{p}-\mathrm{capU}\Big)_+=b\Big(\frac{a_t}{bp}-1\Big)_+-O(|\theta|),\qquad |\theta|\le\eta+1+\mathrm{kaJ}+c_G+2c_G/p=\mathrm{poly}(x).$$

This is the Riesz kernel (y/n − 1)₊ at n = p, y = a_t/b ≈ x, scale b; e ≥ 3 gives n = p^e. At a thin partner the term is ≈ a_t/p^e, with Riesz length ≥ X′. g0 can exceed the ASK summand by kaJ per level, harmlessly, since only ASK − Ga ≤ LoP is needed.

**Proof: LP duality** (`thmAJetA`, Lemma RA; ENGINE2 read `rowRadiusAssembly` to CLR:299, the final assembly lines unread). Give frame coordinate i the radius 1/(p²−1) + r_i. If every bad bipower W_i^{p^α}W_j^{p^β} satisfies p^α r_i + p^β r_j ≥ 1, then v(κ!·coeff_κ) ≥ Σ_i κ_i(γ_p − r_i) − |coords|·(log_p a + 1). The input `lemmaS` says be is at most one power of p worse than the Dwork weight 1/(p−1), and only on even–odd bipowers X_s^{p^α}X_{s′}^{p^β} with s + α ≡ s′ + β: **each Gaussian factor costs one p.** It is proved and read to `binomial_coefficient_extraction` [KLAW §2.5]: B4 makes the additivity defects of be Dwork-integral; torus quantisation lifts their weight to 1/(p−1) (`Quant`, `LogStep`, statements); by Lucas, non-p-power exponents keep weight 1/(p−1), while on bipowers C(p^α, p^{α−1}) has valuation exactly 1, losing one p; torus invariance forces the congruence. This matches NUMTEST5's forward and backward bipowers (per-minor cost 0.80 against 1 − γ₅ = 0.79). A residually generic frame and Cauchy–Binet carry the bound to products of actual minors. For one top with budget A and caps c_j at odd forward distance j, the primal is max Σ_j n_j subject to 0 ≤ n_j ≤ c_j, Σ_j p^j n_j ≤ A; the dual is min_{ε≥0} A·ε + Σ_j c_j(1 − p^jε)₊. The Lean takes ε = p^{−T} at the first odd level T where the budget binds and charges Σ_j min(c_j, A/p^j); since A·γ_p = Σ_{j odd} A/p^j, the gain is Σ_{j odd}(A/p^j − c_j)₊. The true optimum is larger but not in Riesz form; the weaker charge reproduces ASK prime power by prime power.

**The backward charge.** Rows behind the top cost Σ_{j<0}c_{s₀+j}p^{−|j|} ≤ γ_p·Wc, Wc the largest cap behind the top. At a signal top those positions are thick or thin, so this is ≈ γ_p·b per top, prime and lift; over signal p ≤ X″ and m lifts, ≈ |TT|·m·b·log X″, x^{ε/3} above LoP, booked in E (errF), not in Ga. ENGINE2 called it plausibly an artefact; NUMTEST5 (§4.8) finds that it pays for something real.

**One lift.** `liftI_of`: the proved exponent at a signal place is g0S + F − ES, ES = vDG + EatI, equal to the ledger's sg symbol for symbol [ENGINE2 §5; KLAW §3].

### 4.4 The Hecke route at inertClass primes

[ENGINE; ADM2; LOCALDIV; PAIRING; COLENGTH]
The served class GIdx is: inertClass (Frob = ((−1, −1), h)), ord h even, p ≥ 5, not a level prime, p ∤ T.

**Theorem** (`EntryExcessBound`, proved). For every choice of top exponents and minors,

$$v_p(\mathrm{jet})\ \ge\ \sum_{s\in TT}\ \sum_{e\ \mathrm{odd},\ e\notin d\mathrm{Set}(s)}\Big(\frac{a_s}{p^e}-\mathrm{cap}_{s+e}\Big)_+-\mathrm{deLoss},$$

with deLoss the rank logarithms and digit sums and dSet(s) the odd distances from s to another top of opposite parity. Being universal over exponents and minors, the bound holds on the whole integral lattice Int_j. *Cap lemma:* multiplying by a linear form is adjoint to a Hasse derivative, and a minor absorbs at most one derivative per direction. *Hecke operators,* pushed up the chain by a Rallis-type commutation, unlock γ_p·a at even-position tops at a price p^{−Pr} per step; the colength τ removes the surplus. *`adm2`* is proved, conditional on ≈ 15 hypotheses of the site record `Joint.At.K1`; its one-letter law `VIntegral` was read to the leaves (σ-addition formula, Kronecker–Robert theta quotients, root extraction). No supersingularity is used there; that sits entirely in be.

### 4.5 Composition over the m lifts

The iteration is an honest induction on both routes (`chain_ge`, `main_ind`, both read) [ENGINE2 §4; ENGINE §4; CHAININD §0]. After j steps the image is ϖ^{(gains so far)}·z with z an *arbitrary* element of the level-j lattice, and the one-step bound holds for every such z, so gains add. The top weight a_s is the same at every level, while the caps grow with j. Hence

$$\sum_{j=1}^m\mathrm{gain}_j\ \ge\ \sum_{j=1}^{m}\sum_{s\in TT}\sum_{e\ \mathrm{odd}}\Big(\frac{a_s}{p^{e}}-\mathrm{cap}_{j,s+e}\Big)_+-\sum_j(\mathrm{deLoss}_j+dG_j),$$

with dG_j the automorphism denominators v_p(#Stab) (≈ x^{402} in total, ≪ b). "Multiplicity" means exactly this: the same primes divide each of the m lifts to order a. A normalisation error in one step would be multiplied by m, and nothing in the induction would catch it [CHAININD §0.5]. What composes are the linear maps K_i between the actual global lattices; the orbit route's lattice tie `KerEnt.lat_S` is an equality [ORBIT]. The intermediate lattices cost nothing: each intermediate Fock metric occurs once as target and once as source, and Bost is applied only to the composite *(inferred from HEIGHT §1(b))*.

### 4.6 Which primes each route serves

ASK counts every inert prime, so the gain side must deliver divisibility at a prime or charge it its whole ASK summand [CHBALANCE oddity 2; LEDGER §0.4, §2c; SERVED §0; GATIE §2b U11]:

| class | splitting | partners; ASK summand per (t, j) | route |
|---|---|---|---|
| **signal** | inert in K, split in ℚ(√−q) | thick: 2 log p·b·(a_t/(bp) − 1)₊, **the Riesz weight, carrying ψ**; else ≈ 2 log p·a_t/p | **orbit route**, p ≤ X″ |
| **inertClass** | inert in both; split form iff ord h even | top or thin: ≈ 2 log p·Σ_{i odd} a_t/p^i; no ψ; removed by ThinScales | Hecke route, p < X′; orbit route in [X′(1+Crρ), X″] |
| **split** | split in K | not in ASK; only via L′/L(1, χ_{−d}) and De's twists | none |

**Dropped primes** (small-order classes, the band around X′, the second kind, p > X″, p = d) are charged their whole ASK with gain 0, each bucket ≤ x^{−1+O(ε)}·U; SERVED books the bad orbits in three inconsistent ways, each within budget [SERVED §1–2].

### 4.7 The fixed loss, and why b is exponential

[ADM11 §2a, oddity 1; ENGINE §5]
deLoss is ≈ f·x^{804}·log a per prime per lift with the Lean's bounds, far above the loss of 1–2 seen numerically (§4.8). The Lean bounds N(j−1)N(j) ≤ N(m)² ≤ η, counts *all integers* ≤ X″, and closes with X″·η ≤ b (`SizeEta`; live: x^{ch+1228}·e^{x^{ε/3}} ≤ e^{x^ε/2}).

**Why b is exponential.** b must dominate poly(x)·X″, and X″ = x·n·X′ contains X′ = e^{x^{ε/3}}, the Riesz length past which ThinScales discards top and thin partners *(inferred)*. The threshold x₀ is existential, depends on ε and the constant record, and is uniform over hosts, as the Landau windows need.

### 4.8 Numerics, and which object they tested

[ENGINE §3; NUMTEST–NUMTEST5; SIGNAL §E; JETA]

| test | object | the Lean's object? | result |
|---|---|---|---|
| NUMTEST σ, ℘; NUMTEST2 | D^aσ(0); ℘; σ(z+w)/(σ(z)σ(w)) | no | slopes 1/(p²−1), γ_p, γ_p, as the core predicts |
| NUMTEST3; NUMTEST4 | length-2 kernel, one entry; length 4 with det(Y)^m blocks | **yes** | worst −0.98; −1.54, det^m costs m |
| SIGNAL two tops; `jeta_lp.py` | length 4, caps ≤ 8; the top LP | yes; LP arithmetic only | worst −1.13; 0/4000 |
| **NUMTEST5** | the capped law at a signal place, cap ≈ a/p | **yes**, across the kink | worst −1.00 (length 2), −1.83 (length 4) |

NUMTEST3/4's kernels are GIdx-shaped, and locally the signal-orbit object [ADM2; SIGNAL §5]. Before NUMTEST5 all caps were ≪ a/p, so the kink was never probed.

**NUMTEST5** tested P1 = Σ_{e odd}(a/p^e − ν_e)₊ (the Lean's `topTerm`) on real theta-kernel jets at the smallest signal place, Θ = th0(z₀+z₁)·th0(c(z₀−z₁)), N(c) = −1: rank-one jets and 2×2 blocks over ℤ[ω], ℤ[i] at p = 5, 7, 11, caps ≤ 220, and a length-4 orbit; exact Leibniz sums mod p^K [NUMTEST5].
- *Loss O(1):* worst v − P1 is −1.00 over ≈ 250,000 jets, −1.83 at length 4.
- *The kink* is exactly at ν = a/p and follows the number of minors, not the weight; beyond it v is at σ-level. So **the whole signal-place gain is the (a/p − ν)₊ piece**, as the Riesz weight requires.
- *The backward charge pays for something real*: crediting γν without it fails at 32,682 of 42,010 points; the Lean's accounting holds and is nearly tight.
- *Controls* (split primes, anisotropic direction, wrong Gaussian, non-CM curves, scrambled jets) each give thousands of violations.
- *Limits:* rank ≤ 2, one top, no frames, lattices or chains; sizes tiny against a ≈ x·b; e ≥ 5 never active; not the Lean host's curve.

---

## 5. The archimedean side and the slope inequality

### 5.1 Heights

**The bound.** The archimedean height of B_u is bounded by submultiplicativity along the chain [HEIGHT §0]:

$$\mathrm{htMap}(B_u)\le\sum_j\log\|K_j\|^2+\log\|P_tL\|^2-\log\kappa-\sum_j\log\lambda_j .$$

**The jet-step norm.** A Cauchy estimate in Fock space for Taylor jets of entire functions with Gaussian growth gives

$$\log\|K_j\|^2\le\sum_\rho\big(\mathrm{ph}(\nu_{j\rho})-|\nu_{j\rho}|\log\Omega_\rho\big),\qquad \mathrm{ph}(y)=y\log y-y .$$

The conjugate periods Ω_ρ genuinely differ, since they come from different ideal classes. Only their mean enters:

$$\operatorname*{mean}_\rho\log\Omega_\rho=\log\Omega=\gamma+\log(\pi/v)-\frac{L'}{L}(1,\chi_{-d})$$

(sign as in the notation box). This is where the split part of log a! goes [WHYHALF §3.3]. The bound has no slack in the coefficients of ph or logΩ.

**Chowla–Selberg, in classical form** [STEPE §4; NORMS; REVIEW2 A4]. It is *proved in-tree* from Kronecker's first limit formula and the class number formula: for unit-discriminant lattices (|g₂³ − 27g₃²| = 1), mean over conjugates of log(area/π) = γ + log(2π/√d) − L′/L(1, χ_{−d}) (`mean_log_area`; the elliptic formula for K, not Colmez's). `two_log_brN` converts √d to rd_E. NORMS's script reproduces the identity to 8 decimals for d = 4, 3, and REVIEW2 confirmed the constant independently; for the archimedean size of a jet see §5.5.

**DIV per lift and place** [DIVKEY §2.1; STEPE]. DIV is real-number algebra (`divisor_inequality`, read). For each lift j and place ρ it adds the layer covolume +(p_j − q_j)·w·logΩ (D2), the Fock jet term +Σ_i ph(ν_i) − |ν|·logΩ, and the hook term −logHook from L6's lower bound on λ_j. It substitutes |ν| = a_t[ρ∈TT] + k·w + δ and Σ_i ph(ν) − logHook ≤ ph(a_t)[ρ∈TT] + eE. The k·w·logΩ parts cancel against the covolume, and one ph(a_t) − a_t·logΩ per top per lift remains: the height collapses to Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + O(|TT|·a·La + m·B₀x^ε).

**On the live record δ and eE are *defined* as the remainders**; the content is their size bound `stepE_num`, proved and read, an elementary Young-diagram inequality: the k-row Fock weight and the (k−1)-row hook weight interlace, the hook product is ≥ the product of row factorials, and the a_t row is not in the hook, so ph(a_t) survives exactly. A Stirling model gives eE ≈ w·log a at a top and ≈ w·log w off it. Summed over m lifts and f places, eE ≈ m·W·x^ε ≈ (δ/2)·B₀, with W = Σ_ρ w_{jρ} ≈ δ·n·b the weight mass of one lift: **B₀ in total, not per lift**, so eE/U ≲ 4x^{9ε/8} and eE does not carry the √x barrier [REVIEW2 B4; SHARP §2.3, correcting STEPE's total]. The top part of the δ bound is slack. The cancelled terms are ≈ k·f·b·x^ε per level, so L6 must be sharp to relative x^{−4}; it rests on an exact Rallis product formula and seven `Published` theorems supplied in-tree [L6 §0].

**Only the Fock jet bound carries the coefficient of a** [NORMS]. a_t appears only in `BlockBound`, proved in the column Fischer metric `pairK`, which N_u shares; so m·(ph(a_t) − a_t·logΩ) comes from one proved theorem in one metric. The hook and covolume inputs read the same record fields, built from one layer inner product, and `fockModel` identifies the Weil and Fischer norms. A c^{weight} mismatch would falsify L6 or D2 by ≈ k·f·b·|log c|, not shift Main. No lemma identifies the three norms.

### 5.2 The target lattice and its covolume

RR is one global lattice in K^D, glued place by place: at y it is ι(μ(y)) applied to the projection of the integral lattice onto the type-μ(y) part, with {μ ≠ μ₀} finite (author's item 15) [CONGMOD §2a; MIRABOLIC]. The covolume bound (`BoundsMu`, D1 of §5.4) is

$$\mu(RR^\vee)\le\operatorname{meanLog}\kappa+\sum_j\frac{\mathrm{lcv}(M_j)}{D}+2\sum_j\sum_{y\in Tw}lw\cdot F+LG+\sum_j(E1_j+E2_j)+E3 .$$

It uses det ι = κ^D·∏_j det θ_j, from the proved lemma `SpecDet`: ι and θ_j are similitudes with the same Rallis L-value on matching Hecke parts of equal dimension, not a factorisation of ι [DETSIG; LIVEPATH]. The twisted set Tw is *defined* as the places where an index or F is nonzero; it is finite, with no bound on the residue characteristic [TWSET; LARGETW]. The terms [WHERECONG; INDEXBUDGET; MIRABOLIC; E1LOOSE]:

| term | supplied by | congruence/Galois input |
|---|---|---|
| lcv(M_j)/D | Hilbert–Samuel and flat sections (below) | none |
| 2ΣF | layer derivative content; cancels against Fo (`foTie`) | none |
| LG | valuation of a Gram determinant | none |
| **E1**: index of the theta image at Tw | a test lattice of products of short forms, its index bounded by a discriminant and the product formula (≈ m·B₀, tight), inside the theta image by a finite-mirabolic chain (`ThURel`, `IdxAt`); integral surjectivity of theta is never proved | none from the congruence chain; the J0 term uses `CuspUAlt`, base change, Bhatt–Scholze, Chebotarev |
| **E2**: dual index of the type-part projection at Tw | Hida congruence module ≤ Selmer + Ш + v_l(h_E), with no local term at l (`CongBound_at`, `TopCore`) | **all of it**: `KillAt`, `LinkN`, `VWin`, `OneCharU`, `AutEnd3Alt`, `Row0b`, residual irreducibility (§8) |
| **E3** = Σ lw·2/ℓ² | the cost of twisting, ≤ 2/ℓ² per place in the mirabolic chain | none (elementary) |

E1's Galois-typed premise is discarded by the proof, so there is no circularity [E1LOOSE]. All three sit in DIV's per-lift error ce·m·x^ε(B₀+Nc).

**The layer covolume** is [COVOL; VOLUME; HS]

$$\frac{\mathrm{lcv}(M_j)}{D}\le(p_j-q_j)\sum_\rho w_{j\rho}\log\Omega+C\cdot B_0\log\log x,\qquad p_j-q_j=k+2j-1-m .$$

It is proved by descending induction over layers with an effective arithmetic Hilbert–Samuel bound and `FlatDegree`: flat sections on U(p, q) have arithmetic degree (p − q)/2·logΩ + q(…), Chowla–Selberg again. **The flat directions are exact; the error is ∝ q ≤ m** [VOLUME §0.1, §0.5]. The index at the gain primes involves only the *layer* weights, F = (k−1)Σw/(p²−1), which cancels; the a-sized factorial is counted only in the column steps [JOIN §2d].

### 5.3 Bost's inequality, rank-free

The joint map ⊕_u B_u : ⊕N_u → RR^∨ satisfies [RANK; NONVAN §1; TFLOOR §2.3]

$$s-\log|W|-(1-\delta_p)^{-1}\big[4u_F\log(1+H_B/u_F)+(\eta_F+4\sqrt{e_F})H_B\big]\le\mu(RR^\vee),$$

where s = Σ_u d_u(μ(N_u) − h(u))/Σ_u d_u is the mean source slope net of heights, u_F the Harder–Narasimhan spread, H_B = x^{C_H}·b any bound on s − μ_min(cc), and η_F, e_F frame-tightness parameters with (η_F + 4√e_F)·x^{C_H} ≤ 6. In the ledger the target is written μ(cc).

**What it consumes.** At one complex place of the totally complex field LL, the frame gives *robust near-surjectivity*: for Ñ_u ⊆ N_u ⊗ LL of total codimension ≤ ε·Σd_u, the joint image Σ_u B_u(Ñ_u) has rank ≥ |κ|·(1 − (1−δ_p)^{−1}(η_F + 4ε + 4√e_F)). No injectivity is used; the sources overfill the target by ≥ x^{C_H} (|W| ≥ C0·Γ²·x^{C_H}). W is the set of binary words of length k, and log|W| ≤ (k−3)·log 2 ≪ U.

**The mean-slope argument without semistability.** For each τ take the HN piece of N_u of slopes ≥ s − τ + h(u). Bost for a nonzero map, μ_min(E′) ≤ μ_max(F) + h, puts its image in the HN piece of RR^∨ of slopes ≥ s − τ. Markov bounds the total codimension of these pieces by u_F/(u_F + τ), robust rank bounds the codimension of the image, and a layer cake integrates over τ. In BL the (η_F + 4√e_F)·H_B part is ≤ 6b, x^{−5/2} of U; the u_F part is the HN spread times log x, bounded by the ledger's error families.

**Why one heavy functional cannot cheat** [TFLOOR §2.3]. The type-prime gain of §5.5 comes from a functional reading only the heavy component. If B_u read *only* that, it would kill the light, high-slope pieces and violate robust rank; Theorem S's diagonal clause ‖K(u,u) − 1‖² ≤ e₀·d_u excludes this. The −a·log T sits in h(u), common to all of N_u, so it does not widen u_F. "The frame is a rank statement" suffices, provided rank means *robust* rank.

**What is not described.** The frame carries no metric content [RANK]. Nothing read controls the Hadamard defect of the composite or h(u) − log‖B_u‖_true, which the conclusion forces to be tiny (§9.7, point 1).

### 5.4 The ledger

Fifteen Lean statements combined by proved linear arithmetic; no term has the wrong sign or is missing [LEDGER §0–2]. For fixed x, family member and u₀ ∈ A₀, with ΣA = Σ_t a_t, nT = |TT|, ph(y) = y log y − y, logΩ = γ + log(π/v) − L′/L(1, χ_{−d}), s = wmean_u(μ(N_u) − h(u)):

```
SLOPE SIDE (per word u)
(L0) s − log|W| − BL ≤ μ(cc)                                          Bost (proved; frame inputs)
(L1) μ(cc) + h(u) − Fo ≤ Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u]
                         + c·nT·a·La + c·m(B0+Nc)x^{2ε}                DIV  (sub-ledger D1–D5 below)
(L2) μ(M_u) + Ga + Fo − Ee(u) − Lo5(u) ≤ μ(N_u)                         slope of N_u (exact formula, §5.4 tie)
(L3) −c·nT·a·La(1+m/k) ≤ μ(M_u)                                         source floor
(L4) Ee(u) ≤ m(ΣA·lg + cE·B0)                                           EComp5 (adm11)
(L5) Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − c(La + m²La/k) ≤ log T_u          Count5
(L6) add L1–L5 (the two Fo cancel), average over u                      s_lower5
(L7) Σ_t m(ph(a_t) − a_t logΩ) − ΣA·Lam5 + m·ΣA·lg = Main + ΣA·c(La + m²La/k)   key_identity5 [exact]
(L9) Ga ≤ Main + log|W| + (one-off and per-lift errors) + BL                 Ga_bound5
GAIN SIDE AND CLOSING
(L10) ASK − Ga ≤ LoP = C·nT·m·b,  IO ≤ LoP                              LossBounds (formula vs formula)
(L11) ASK ≤ Main + ErrX5at                                               each_unit_bound_statement
(L12) ErrX5at ≤ x^{(eD+eL+3)ε}·[nT·a(1+m²/k) + m(B0+Nc)]                  errX5at_le
BRIDGE
(L13) ASK − Main = Σ_t Σ_j [ASK − Re MAIN]        (Main = Σ Re MAIN by definition)    ch_top
(L14) ASK − MAIN = De [exact];  nT·m·b·(δ/2)·(G_m − SigA − 4x^{1/2+ε}) ≤ Err + 2nT·m·b/x   ch_balance, core
(L15) G_m − SigA ≤ x^{1/2+(eD+eL+6)ε};  SigA ≤ 4o·x^{1/2+ε};  ⇒ G_m(x) ≤ x^{1/2+9ε}     GrowthSizeBound, core_gm
```

L8 bounds the HN spread inside L9. The DIV line L1 is the sum of five lines (`divClausesR_of`): D1, the covolume bound of §5.2; D2, Σ_j lcv(M_j)/D ≤ Σ_jΣ_ρ(p_j − q_j)·w_{jρ}·logΩ + El3; D3, a base-to-column passage from μ(RR^∨) to μ(cc); D4, the height bound mean_v log‖B_u‖²_v ≤ h(u) − meanLog κ of §5.1; D5, their sum, with El3 + LG + Σ(E1+E2) + E3 ≤ ce·m·x^ε(B₀+Nc).

**The tie of Ga to lattices** [GATIE; ADM11]. Ga = Σ_w 2·lw·e_w·(Σ_j gainD_j(w) − τ(w)) is *defined*, its fields pinned by `ParametersFill` to explicit formulas, so L10 compares two piecewise-linear formulas with the same caps and needs no lattice. The content enters through sg(u, w) = Σ_j(gainD_j + F_j − E_{u,j}):
- N_u = ∏_w 𝔭_w^{−⌊e_w·sg⌋}·NuLat_u has exact slope μ(NuH_u) + Σ_w 2·lwP·⌊e_w·sg⌋; the floor loses ≤ 2·lwP per place with sg ≠ 0, ≤ C·X″ ≪ b in total, once per place;
- N_u is the source of DIV only if Bk_u(N_u) ⊆ cc (`OneMapIntoCC`), which holds because the period of the **actual** chain image of every φ ∈ NuLat_u has valuation ≥ ⌊e_w·sg⌋ (clause `adm2`). So the inclusion *is* the p-adic divisibility of the actual chain maps;
- the same fields enter Ga, Fo, Ee, N_u and the proved divisibility; GATIE found no slack.

**The inclusion on every branch** (`admissible_level_two`, read):

| place (p = resChar w) | exponent sg | supplier |
|---|---|---|
| p = T_u | −m·EatT ≤ 0 | `Conclusion5Sharp`, `TwistedColumnBoundAtT` |
| p ∈ {g₀, g₁} | strongly negative (the ΣA·log g main part) | `UsedTuplesBoundByConstant`, a denominator bound (unread) |
| GIdx, served orbits | Hecke-route gain | `kernel_valuation_served`, moved to the actual columns by `CmpV` |
| signal, or inertClass with h ≠ 0, p ≤ X″, VV = ∅ | orbit-route gain g0S | `OrbitsWithoutOperator` (§4.3) |
| inertClass, h = 0, p ≤ X″ | F − EatC | `MediumInertPrimeLengthBound` |
| p = d | F − EatD | `LossAtDiscriminant` |
| split, p > X″ | ≤ 0 (integral up to v_p(DGam)) | `IntegralKernelValuation` |

**The zero-chain alarm is closed on the live path**: the auxiliary local chain enters only through `CmpLite`, which must intertwine with the actual K_j. `exists_data_completion` confirms the content lies in this tie: from ASK ≤ Main + error alone one can build a record satisfying every ledger clause [LEDGER §0.6].

**The main terms never meet as numbers** [LEDGER §2b]. m·ph(a_t) − m·a_t·logΩ becomes Main by the exact algebra of L7, and Main is MAIN by definition. **DIVKEY and TU verified L7 by hand**: log(π/v) cancels Count5's log(v/π), the m·lg terms cancel, and only γ and the L′/L constant survive; the signs agree (`Char_at`). A sign error in Chowla–Selberg would show as a Main/MAIN mismatch; §5.1's checks exclude it. The p-adic sum Σ_p γ_p·a·log p appears nowhere: one lift is one Chebyshev identity, with all content in the errors (§5.5) [HEIGHT §2(b); WHYHALF §1.1].

**The cancellations** [ACCOUNT §0.3; LEDGER §2].
- μ(cc) enters Bost and DIV with coefficient +1 and cancels; only an *upper* bound on μ(RR^∨) is used.
- Fo (`foTie`), h(u), the m·lg terms and log(π/v) cancel syntactically.
- The large logΩ terms: Σ_jΣ_ρ(p_j − q_j)·w·logΩ from D2 against −Σ_jΣ_ρ(a_t[ρ∈TT] + k·w + δ)·logΩ from the height leave −m·Σ_t a_t·logΩ plus a residual Σ_j(2j − 1 − m)·Σ_ρ w_{jρ}·logΩ, booked crudely at ≤ 2m²·f·b·La. The record has only |p_j − q_j − k| ≤ m, never Σ_j(p_j − q_j) = mk [DIVKEY §2.5]. In truth the residual is negligible: Σ_j(2j − 1 − m) = 0, and w_{jρ} varies in j by ≤ η + 1 at thick places and ≤ 2b′ elsewhere, so it is poly(x)·m²·f·La ≪ b [SHARP; REVIEW2 A4]. The cancelling terms are ≈ x^{4.5+O(ε)}·U. In the Lean they cancel *syntactically*, through the one `logOm` symbol; that L6 and D2 are each true to relative x^{−4} is a separate claim, resting on `covolume_measure_eq_one`, the `FlatDegreeSt` chain and L6's seven `Published` inputs (§9.4).

**Precision-critical inputs** [ACCOUNT §0.3–0.4; LEDGER §2b]: covolume and height to relative **x^{−4}**; Count5 to relative **1/m**, and log T* − Lam5 ≲ x^{O(ε)} in truth (§5.5); Bessel-frame tightness **η_F ≤ 6x^{−C_H}**; the real divisibility to E ≤ C·B₀ per lift, relative **x^{−1/2+O(ε)}** (§6.3); and, two-sided, `PairGood` at x and `ThinScales`.

### 5.5 The type prime T

[TU; TDIV; TFLOOR; SHARP] The term −Σ_t a_t·log T_u of DIV supplies the −a·mean log w part of Main: it is where the scale x = a/w enters the archimedean side.

**What T is.** A rational prime (`T_prime`) with f places above it, each with residue field F_T, and π_T ∈ O_E with π_T·π̄_T = T. There is one T per word u (`ColumnsAtT.T`); T's of different words differ by norms from E, with |log T(u) − log T(u′)| ≤ C·log k. It is ADM11's "type prime".

**Its size, and how it is pinned.** Count5 is a sum over the m lifts, so log T ≈ m·log w ≈ m·x^ε and T ≈ (cap)^m, consistent with b^{m/2} ≤ T. T lies in a window T* ≤ T ≤ (1 + 1/(fk))·T* (`T_win`), T* = (D*/d*_u)^{1/(fk)}·Γ^{−2/(fk)}, where D* = (target mass) × (level index) × ∏_ρ(formal degree) and d*_u = (source mass) × (level index) × ∏_ρ(Weyl dimension). The defining identity is D*Γ^{−2}/2 ≤ d*_u·(T^k − 1)^f ≤ e·D*Γ^{−2}; since T^k − 1 is the index of the mirabolic in GL_k(F_T), **T is chosen so that the level-T source dimension matches the target** (the Theorem-S window). Count5's supplier is this explicit dimension-ratio computation (`countF_fam` → … → `division_level_prime_family`, error 11L), not a limit-multiplicity count.

**The level-T lattice.** "Translated by π_T" is a lattice operation, not an isogeny: `DecoSet.til` sends a row lattice N to N ⊕ O·e_last with level datum h(π_T e_last, ·) mod P, and the live column point is K.lat ⊕ O·z0, z0 = π_T e_last, h(z0, z0) = T (`TilTied`). Integrality of a form at a point is *defined* by coordinates in a basis of the point's dual lattice (`ValTied.lat`), and there the dual coordinate is h(z0, y) = π̄_T·y_last. So **"divisible by π̄_T^{nBr} in standard coordinates" is the integral structure at a level-T point**, not a claim about the forms. The last map `brC` multiplies the Bessel functional by ∏_τ τ(π̄_T)^{−nBr}, nBr = |λ| − |σ| the last-row degree (≈ a_t at a top); `LowerMapTieS` identifies it with the unscaled branching map in z0-coordinates (checked by hand, not by a Lean lemma). `periodFun_le` gives the archimedean factor T^{−nBr} once, so hA = −Σ_t a_t·log T, once per top, not per lift. The live integrality chain (`aPt0` → … → `Pt_integral`) was read; it rests on `colsTiedSym_std`, unread.

**The rank-one model: the product formula holds** *(TDIV's computation)*. Take a hermitian line, point lattice L = π·O, and f = c·y^n. Then f is integral at L iff p := c·π̄^{−n} ∈ O, the last map is f ↦ p, and the Fock norm ‖f‖² = n!·|c|² gives |p|² = T^{−n}‖f‖²/n!. For integral f ≠ 0, ‖f‖² ≥ n!·T^n: the source slope drops by (n/2)·log T, exactly the gain, and Bost reads 0 ≤ 0. Nothing is gained in rank one.

**Rank N: gain against cost.** In rank N the source pays only the *mean* weight per dimension, ≈ (|λ|/N)·log T, while the gain is the degree of the extracted heavy component, nBr ≈ a. In the ledger the costs are the L3 floor's −Σ_t(a_t/k)·log T (the Weyl-symmetric mean exponent |λ|/k; its "(1+m/k)" is this term after log T ≤ C·m·La), Lo5's c·|TT|·m·(a/k + b′)·log T (the colength of NuLat_u in Mram above T, same lattice), and m·EatT·log T (§6.4). TFLOOR's model, Sym^a with one scaled coordinate, gives covolume shift (a/N)·log T, matching the floor exactly. The net, ≈ a(1 − O(m/k))·log T per top, is legitimate because the period functional reads only the heavy component, and robust rank (§5.3) stops it from killing the light pieces.

**What bounds T above.** The ledger improves strictly as T grows (gain a·Δ against costs m·EatT·Δ + c|TT|m(a/k + b′)·Δ); only `T_win` stops a larger T. Doubling T violates d*_u(T^k − 1)^f ≤ e·D*Γ^{−2}: the source would outnumber the target and the joint map could not frame, a rank obstruction *(inferred; the frame's use of the upper pin was not re-read)*. The lower pin serves the main term, the upper pin the frame.

**Rigidity** *(TFLOOR's computation, not the Lean's)*. Truth forces log T* − Lam5 ≲ x^{O(ε)}, while the Lean bounds log T above only by cCount·m·L [SHARP]. Inserting the Harish-Chandra formal degree (dsig = dimV(rowLam), Haar measure transferred from the compact form) into the Lean's exact closed form for fk·logXu (`LemmaFiveOneIdentity`), with the shapes of `DataB`, `RowsA`, gives logXu = Lam5₀ − θ, 0 ≤ θ ≲ 3L + O(log k) + O(m²L/k): the (v/π), lg, facProd(r) and k·Σ log w terms cancel exactly, the remainder being the u-column Vandermonde. So log T − Lam5 = O(L), inside the x/m budget. This rests on the formal degree under the unread normalisation `cdScale` being the Harish-Chandra value (consistent with `BaseVolumeEqualsMass`). The stated formal-degree bounds give no matching upper bound (loose by ≈ (m/2)·x^{ε/3} in log T); an excess of e^{Θ(km)} would make the proved chain assert something false.

**One prime for all lifts.** The record forces it: one `ColumnsAtT.T` per word; level-T data at every level i ≤ m from one `AtTTied u` (`LvTied`); `Eval` sets E = EatT at T for every lift, so sg = −m·EatT. Mathematically, the prime fixing the source dimension at level 0 must be the one the last map divides by at level m, and the jet chain carries that level datum through the intermediate levels; a prime used only at one intermediate level would add cost and no gain *(TFLOOR's reading)*. With one prime per lift and log T_j ≈ x^ε, the T-loss would not grow with m (§6.4).

**One lift, displayed.** Per top, at m = 1, in log‖·‖² units:

$$\underbrace{\mathrm{ph}(a)-a\log\Omega}_{\text{Fock jet bound}}\ \underbrace{-\,a\log T}_{\text{last map}}\ \le\ \mathrm{ph}(a)-a\log\Omega-a\operatorname*{mean}_\rho\log\frac{wv}{\pi}-a\,\mathrm{lg}\ =\ a\Big(\log a-\operatorname*{mean}_\rho\log w-1-\gamma+\frac{L'}{L}(1,\chi_{-d})\Big)-a\,\mathrm{lg},$$

with Count5 used in the middle, v and π cancelling, and the a·lg cancelling against adm11's ΣA·lg at g₀, g₁. The p-adic side gives Σ_{p inert} 2 log p·Σ_{e odd}(a/p^e − w)₊ up to errors, and by the explicit formula Σ_n Λ(n)(1 − χ_{−d}(n))(a/n − w)₊ = a(log(a/w) − 1 − γ + L′/L(1, χ_{−d})) + O(w) + (zeros) [TU §2.3]. So one lift is the explicit formula for the inert count at Riesz length a/w ≈ x: the caps w enter both sides identically, as the Riesz cap on the p-adic side and through Count5 on the archimedean side; the floors ⌊e·sg⌋ cost ≤ 2·lwP per place once (§5.4). NORMS checks the first brace numerically: 2·log|D^aσ(0)| − [ph(a) − a·logΩ + (a/6)log|Δ|] = 7.4 and 5.4 at a ≈ 6000 (d = 4, 3), i.e. O(log a). At m = 1 the one-off errors, ≈ |TT|·a·x^ε, swamp the zeros' contribution, and nothing follows (§6.1).

---

## 6. Why 1/2

### 6.1 The error budget by family, and the balance

The budget ErrX5at splits into families [LEDGER §2a; SHARP §2.2]. These are *allowances*; §6.4 compares them with actual use. Relative to U, at m ≈ x^{1/2−ε/16}:

| family | entries | budget/U |
|---|---|---|
| main terms | ASK, Main ≈ m·nT·a·x^{ε/3} | ≈ x^{1+4ε/3} |
| cancelling | Fo, μ(N_u), h, Σ lcv, Σ hB ≈ m·k·f·b·x^{O(ε)} | ≈ x^{4.5+O(ε)}; cancel exactly or to relative x^{−4} |
| **x/m** (one-off, ≈ \|TT\|·a·x^ε) | Count5; DIV boundary terms (hA, the δ top part); the source floor; the \|TT\|·a·La part of the HN spread | ≲ x^{1/2+2.06ε} each |
| **m** (B₀ = f·m·b·x^ε per lift) | every B₀-proportional entry: DIV interior (covolume error l3u, E1, eE, the pq residual, eP, Lpass), EComp5 m·cE·B₀, and cSl1·m·B₀ inside Bost's spread | ≲ x^{1/2+4.06ε} |
| **k/n²** | m·Nc, Nc = \|T2\|·k·b·x^{2ε}/n²: the E2 congruence allowance | ≲ x^{1/2−1.875ε} |
| negligible | LoP = C·nT·m·b; log\|W\|; (η_F+4√e_F)·H_B; MLo5 | ≤ x^ε |

**k/n² is not a non-vanishing term** [NONVAN §0.3, correcting earlier versions of this document]. Nc enters only as an allowance in `LinkN_at`, the congruence-length bound on the E2 exponents, and reaches DIV through `DIVinN`; it appears in neither `Frame_at` nor the Bost line. Non-vanishing enters only indirectly: Theorem S forces k ≳ m⁵·f·log b, and the record clause k ≤ n²·x^{1/2−ε} keeps m·Nc within budget; together they give n ≳ m⁴.

**The balance.** The Lean replaces this table by L12–L13. Divided by U the bracket is

$$\frac{2a_E(1+m^2/k)}{m\,b\,\delta}+\frac{4nm\,x^{\varepsilon}}{|TT|\,\delta}+\frac{2k\,x^{2\varepsilon}}{n\,|TT|}\ \le\ 8x^{1/2+2\varepsilon}+8x^{1/2+2.625\varepsilon}+4x^{1/2+1.125\varepsilon}\ \lesssim\ x^{O(\varepsilon)}\Big[\frac xm+m+\frac{k}{n^2}\Big],$$

using a_E ≤ 2xb, f = 2n, δ ≥ x^{−ε}, |TT| ≥ x^{−ε/8}n/2 and the window x^{1/2−ε} ≤ m ≤ x^{1/2+ε/2} [LEDGER §2a; WHYHALF §1.3]. So the total error is ≤ 20x^{1/2+2.625ε}·U. With m = 1 the bracket gives G(x) ≲ x^{1+O(ε)}, **no better than the trivial bound**: Mertens already gives G = O(x) unconditionally. The one-off errors then swamp the main-term identity, as in Stepanov at one vanishing order *(DIVKEY's inference; the tree requires m ≥ x^{1/2−ε} and m ≥ 2)*.

### 6.2 The exponent 9

On the live path `topDesWin` is called with e_D = 2, e_L = 0 [LEDGER §0.2, §1]. The final exponent is 1/2 + 9ε, with 9 = 5 + 3 + 1:
- **5** = e_D + e_L + 3, from the envelope ErrX5at ≤ x^{(eDiv+eLoss+3)ε}·ErrText;
- **3** from `GrowthSizeBound` (read): 13/8 from the bracket, 1 from dividing by δ ≥ x^{−ε}, 3/8 from the constant 26 ≤ x^{3ε/8} [DIVKEY §2.7];
- **1** to absorb 1 + 4o in front of SigA ≤ 4o·x^{1/2+ε}.

The record's parameter inequalities hold for x ≥ x₀(ε) by hand; the existential frame bounds were not checked [LEDGER oddity 2].

### 6.3 Two precisions, and where each loss is booked

[GATIE §0.5, §2c; LEDGER §2b]
- **Archimedean side: relative x^{−1/2+O(ε)}**, what DIV, Count5 and Bost deliver, on lattices.
- **Gain formula against count formula: relative x^{−1}.** LoP ≈ x^{−1−ε/3}·ASK is demanded only of two formulas that agree by construction; its O(b) per (top, lift) pays the top offset.
- **The real divisibility: relative x^{−1/2+O(ε)}.** Its losses are booked in E. adm11, proved on the live path down to eight bounds, says per word and lift: Σ_w sz(E) = ΣA·log(g₀g₁) ± C·B₀ (the m·ΣA·lg that cancels Count5), the rest ≤ C·B₀; split primes and p > X″ carry only v_p(DGam) [ADM11 §2a]:

| loss of the real divisibility | Lean bound per lift | real size per lift |
|---|---|---|
| kindA orbit term; errF (backward charge); c6·Σw/p | 18·B₀; 36·B₀; 324·B₀ | ≈ k·f·b′; ≈ \|TT\|·b·x^{ε/3}; ≈ 12·W·x^{ε/3} |
| deLoss (§4.7); EatX at IsCs primes | 23·B₀; 21·B₀ | ≪ b |
| **signal and inertClass p ≤ X″, total** | **≤ 424·B₀** (doubled for 2 log p) | U·x^{O(ε)}/m |
| type prime T_u (EatT, every lift) | 12·CTu·B₀ | ≳ (δ/2)·B₀: genuinely used (§6.4) |
| d; g₀, g₁ | 4·B₀; Cg·B₀ via `DegreeCountBound` (unread) | g-part ≈ 2W·x^ε |
| rounding ⌊e·sg⌋, once per place | ≤ C·X″ (in LoU) | ≪ b |

`DegreeCountBound` carries the ±C·B₀ precision against ΣA·log g, far larger than B₀. Away from T the 848·m·B₀ budget is about m times actual use [SHARP §2.3].

### 6.4 Stepanov, and what carries the barrier

**Stepanov.** Schematically, ℓN ≤ ℓq + O(q) + O(ℓ²), so ℓ ≈ √q. Here the points are the signal primes at scale x, the vanishing order ℓ is m, the auxiliary polynomial is the joint Bessel period map on N_u, the degree is the product formula (Bost, height, covolume), the one-off degree is the boundary terms, and the ℓ² overhead is the loss at the type prime: each of the m lifts is non-integral at T by about its weight mass, and log T must hold m copies of the Riesz-length normalisation [WHYHALF §2; SHARP oddity 1]. Unlike Stepanov, non-vanishing costs only a polynomial relation k ≳ m⁵·f·log b: **the cap on m is the growth of a per-lift loss, not non-vanishing**. Non-vanishing does fix the host: n ≳ m⁴ ≈ x² (§6.1).

**The forced-rigidity principle** [REVIEW2 A3; SHARP §1]. The actual consumptions r_i = A_i − B_i of the links A_i ≤ B_i + e_i telescope to ASK − Main ≈ U·(G_m − SigA). In every window G_m − SigA ≥ c√x on a set of positive logarithmic density, so there some link must *actually* lose ≥ c′·U·x^{1/2}; negative slacks (Hadamard defect, h(u) − log‖B_u‖_true, unused divisibility, Count5 slack) cannot carry it. Conversely, if every link is true, the total actual slack is ≤ U·x^{1/2+9ε}, and unconditionally ≲ relative x^{−3.5} of the cancelling terms. If the construction is valid for larger m, the carrier must lose ≳ min(m, √x)·|TT|·b per lift, or the method would prove G = o(√x).

**Allowances far above actual use** [SHARP §2.3]: eE totals ≈ (δ/2)·B₀ (§5.1); the signature residual cancels in truth (§5.4), though booked in absolute value; the adm11 losses at p ≤ X″ use about 1/m of their budget (§6.3); Bost's m-part holds only the u-dependence of the T-loss, U·x^{O(ε)}. E1 and E2 are not shown to be m-sized in truth (E1's J0 piece and E2's Selmer and v_l(h_E) parts are unquantified).

**The term that genuinely grows with m: the loss at T** [SHARP §0.1, §2.3]. At p = T every lift has E_{u,j} = EatT, so sg = −m·EatT. EatT ≥ 2·Σ_τ Wtau, with Wtau ≈ b at thick places *(inferred from the weight formulas)*, so EatT ≳ 2δnb; and log T ≍ m·x^ε (§5.5). Hence Ee_T ≈ m·EatT·log T and, by SHARP's arithmetic,

$$2m\,x^{\varepsilon}\ \le\ \mathrm{Ee}_T/U\ \lesssim\ 192\,c_{\rm Count}\,m\,x^{2.1\varepsilon},$$

so ≥ 2x^{1/2+15ε/16} across the window: a defined nonnegative quantity pinned from below, growing like m² in total. Two caveats:
- *SeenDef.* EatT is nonzero only at "seen" places (all τ-conjugates of π_T of positive valuation), which SHARP reads as the places over one prime of K above T. If that reading failed, EatT would vanish and the question would reopen [SHARP oddity 4].
- *What is actually lost* [TFLOOR oddity 2]. EatT is a maximum over levels and rows charged m times, a conservative booking (level j costs only ≈ j(t+1)w/N(j) per dimension). Safe for validity; but "the method does not prove too much" needs the *real* T-adic loss of the jet steps to be ≈ EatT per lift, which rests on the unread hypotheses `Conclusion5Sharp`, `TwistedColumnBoundAtT`. Not established by the reading.

A second candidate, sign unsettled, is the covolume's q-part (`flatDegVal`'s exact q·(log d − lrd E) and the non-flat Hilbert–Samuel part ∝ q_j·W, both inside l3u).

**The admissible range of m.** The Lean fixes m ≈ x^{1/2−ε/16}, with m ≤ x^{1/2+ε/2}. Re-dimensioned under the Theorem-S constraints (m⁴ ≤ f, x^{3ε/2}·m⁵·f ≤ k ≤ x⁵) and k ≤ n²·x^{1/2−ε}, the largest admissible m is ≈ x^{11/20} *(SHARP's arithmetic)*. There the bracket gives only G ≲ x^{0.55+O(ε)}, and Ee_T ≳ x^{0.55}·U: nothing false follows. Without Ee_T, the actual consumption at m = x^{11/20} would be ≈ x^{0.45+O(ε)}·U, contradicting the Ω-result. One prime for all lifts (§5.5) is what makes Ee_T grow with m.

**The core inequality as a statement about zeros** *(SHARP §2.4)*. Fix u₀. ASK − MAIN = De is exactly Σ_χ r̂_{u₀}(χ)·(Riesz error of L(s, χ) at y ≈ x, or at the lengths ≈ X′, X″), over characters of Gal(E/ℚ), with r_{u₀}(h) = #{t ∈ TT : t + h − u₀ ∈ T2} a nonnegative class weight; these are Dirichlet L-functions of conductor dividing d·q·2^{s+2}. The core is a one-sided bound, at the single point y ≈ x, on this weighted sum over zeros: ≤ U·x^{1/2+O(ε)}. GRH implies it (Σ_ξ|r̂(ξ)|/r̂(1) ≤ √2·x^{9ε/16} by Parseval). No known result contradicts it, since the conductors are exp(x^{Θ(ε)}) ≫ x; an adversarial choice of T2 correlated with the primes reaches only x^{1/2}·polylog·x^{ε/16}.

**The core is itself of GRH strength** [REVIEW2 A3(b)]. Steps 3–11 do not use host selection (`PairGood`), only the zero boxes and |L′/L(1)| ≤ 4 log x. So the core is an inert-count bound G_z − g_{χ_{−d}} − (ψ-twists) ≤ x^{1/2+O(ε)} for every admissible d: GRH strength for the inert primes of ℚ(√−d). Were it uniform in d, it would imply GRH for L(s, χ_{−d}) to the right of its real zeros. That is not false, but the core is no weaker than what it is used to prove. Whether d must grow with Y for anything but `PairGood` is open.

**Why not Chebyshev.** Chebyshev lacks multiplicity and computes no main term; here m supplies multiplicity, and the main terms are exact (Legendre/LT divisibility to O(1), exact caps, Chowla–Selberg, flat covolumes, Fock coefficients, the bridge identity) [WHYHALF §3]. Everything is one-sided except the host-selected inputs, where the twists' fluctuation is placed in the choice of (q, d).

---

## 7. Non-vanishing

**Why it is needed.** If the periods B_u vanished, or the joint map fell far short of surjective, Bost would say nothing about the primes. The frame hypothesis excludes this through robust near-surjectivity (§5.3) [RANK §0; NONVAN]; it also forces D_all > 0 and some B_u ≠ 0, so the degenerate "stand-in" records cannot be the live one [JOIN §1c]. Its inputs are a near-tight frame (Theorem S plus the dimension count), a ramified share de ≤ 2f/b, overcompleteness of the word family, and δ_p < 1.

**From orthogonality to rank** *(NONVAN's reconstruction)*. Let Q = Σ_u γ_u·P_uP_u* on HH. Then tr Q ≈ Σd_u by the diagonal clause, and tr Q² = Σ_{u,u′}‖K(u,u′)‖²_HS ≤ (1 + η₀ + η₁ + x^{−C_H} + O(√e₀))·(tr Q)²/D_all by the off-diagonal clause, overcompleteness and the count. Since tr Q² ≥ (tr Q)²/D_all with equality iff Q is scalar, Q is a near-tight frame, dimension-free; projecting onto the Bessel rows EE ≅ RR^∨ ⊗ ℂ does not increase codimension. A constant 1 + c in Theorem S, or a relative error c in D_all/D*, would give η_F ≈ c, so the precision needed is x^{−C_H}, polynomial.

**Near-orthogonality (Theorem S)** [PAIRB; COUNTS; THMB; THEOREMS; NONVAN]. The Gram kernel K(u, u′) = (c_uc_{u′})^{−1/2}P_u*P_{u′} has off-diagonal squared Hilbert–Schmidt norm ‖K(u,u′)‖²_HS ≤ (1 + b^{−6})·d_ud_{u′}/D*, the value for random subspaces, and ‖K(u,u) − 1‖²_HS ≤ e₀·d_u. On the live path both clauses are **proved by named theorems** (`at_choice_alt` → `offDiag` → `offDiagonalK0_of_rows`, `theoremS_of_conj` → `theoremS_closedP` → `theoremS_rec` → `pbApplied` → `t_PairBound`), all closed hypotheses discharged from the Siegel–Weil input; `theoremS_selected_of_loops` is dead, so its "conditional" status was stale. The leaves are unread. It is the author's "relative trace formula" (item 16): a **double unfolding of Poincaré series**, with savings from an exact volume identity with Schur orthogonality, sublattice counting, a character-sum cancellation on a hermitian quadric [COUNTS] and Gelfand–Graev multiplicity one. The comparison 2^{−k/2}e^{Cm⁵f log b} ≤ b^{−14} fixes k ≈ x^{9/2+10ε}.

**The dimension count** [COUNT; SLEAVES; FORMULAGAP; GERMJET; NONVAN]. D_all = dim HH is a limit-multiplicity count for a very regular discrete series of U(k + r_S, r_S + 1)^f in L² of a non-compact quotient:

$$D_{\rm all}\le(1+\eta_1)D^*,\qquad D^*=\text{formal degree}\times\text{covolume},$$

with relative error e^{−nf log n/16}, uniformly in rank. It is live (`count_constants_of_siegelWeil` → `countingTheorem_of_volumeStep`), proved conditionally on the in-tree Siegel–Weil input; its application to *this* HH rests on `rowsTiePT'_of`, unread. `LinkIRR` (δ_p ≤ e^{−x^{ez/7}}, the share of HH outside the Bessel-functional space) is likewise proved by named theorems from Green's classification and Siegel–Weil (`closed_linkIRR_of_join_count`), bodies unread. *Non-compactness*: π∞ is integrable, so R(φ_e) is an exact orthogonal projection onto cusp forms; no spectral decomposition or truncation is used, and the kernel is bounded pointwise region by region. *Where exponential precision comes from*: the very regular weight kills only the far terms (DecGap); the unipotent, thin and deep contributions are small by **rank**, e^{−nf log n/4}, through Siegel–Weil volumes. (This count is not Count5, the explicit ratio that pins T, §5.5.) DecGap rests on a **compression formula** for lowest-K-type matrix coefficients of non-holomorphic discrete series, c_λ(z) = ∏_iΔ_i(z)^{−s_i}, proved via Schmid's first-order system and jet uniqueness (read); it reproduces the known U(1,1) and holomorphic U(2,1) cases and was not found in the literature.

**Over-delivery.** Theorem S gives 1 + b^{−6}, the count e^{−nf log n/16} and LinkIRR e^{−x^{ez/7}}, where the Bost step needs only x^{−C_H}, x^{−C_H} and δ_p < 1. Even polynomial precision, uniform in rank n ≈ x^{4.5} and degree f ≈ x², is beyond published limit-multiplicity results, which fix the group *(auditor knowledge)* [NONVAN §2.5].

---

## 8. The Galois-theoretic inputs

**Where congruence modules enter.** Only through E2 (§5.2) [WHERECONG]: at Tw, RR is a projection onto a type part Z_j, and the dual index is bounded by Hida's congruence module [CONGMOD §0]. Since Tw has no bound on l, every input below must hold at arbitrarily large l. Z consists of theta lifts whose A-parameter contains a Speh block μ⊠S_t, with Galois representations ρ ⊕ χ₁ ⊕ χ₁ω^{−1} ⊕ … ⊕ χ₁ω^{−(t−1)} [LINKN §0].

**Congruence ≤ Selmer.** The Ribet–Wiles direction, made quantitative by a Fitting-ideal determinant lemma; `NoChiOff` is a Galois-side rank/weight count [GALREP], and the converse-theta content sits in `ConclusionZ`, `D7.Z_tie` (unread). Purity comes from an in-tree Jacquet–Shalika bound [ROWCRYS]. The bound (`CongBound_at`) has three blocks, Bloch–Kato Selmer of ρ⊗χ₁^{−1}, v_l(h_E), and Ш¹(E, ℚ_l/ℤ_l(−i)), and **no local term at l** [BEYONDFL].

**No local term at l, beyond Fontaine–Laffaille** [BEYONDFL; TOPCORE; SENLAT; G2A]. Hodge–Tate weights are ≈ b, outside the Fontaine–Laffaille range for l < b. The local defect is proved 0 by `TopCore`, a new integral comparison: for crystalline ρ over unramified K with weights satisfying base-l digit conditions, an extension cut out by crystalline lattices of the prescribed weights lies in H¹_f. The proof counts Herr cocycles on reduced Wach modules, using `SenLat` (proved in-tree); primes failing the digit conditions are charged ≤ b in total.

**Killing the ρ-block** [KILLAT; ORDER; LARGETW]. Twisting through a finite tame tower with Chebotarev-chosen auxiliary primes gives the Selmer module a square presentation P with det P of unit coefficient; no weak Leopoldt, no infinite Iwasawa module, at a summable cost 1/l² per place.

**The Ш bound** [VWIN; ONECHARU; RT3; MODU3; PATCH; FINEND]. The bound needed is

$$\sum_l\log l\sum_{0<i<t}\mathrm{len}\,Ш^1(E,\mathbb Q_l/\mathbb Z_l(-i))\le\sqrt b,$$

VWin states it for all twists i < x^{401}; against E2's allowance ≈ x^{2.5}·b it is nearly idle. Crude bounds do not suffice [ONECHARU §2a]: the truth is heuristically polynomial in x, but the best crude bound in the tree (`LemmaK`) is exp((2kn)^C·log disc) = exp(x^{C′}). Minkowski/Brauer–Siegel controls only h_E; for the plus parts of K_{2k}(O_E), k ≥ 1, a crude route would need lower bounds for Borel regulators, which are not available, while the minus parts have an L-value route. The proof is R = T-type: Ш embeds in first-order deformations of Ψ ⊕ 1 ⊕ Ψ^{−1}, and a commutative-algebra inequality bounds its length over automorphic points. The modularity input is residually reducible ordinary automorphy for U(3) (Skinner–Wiles for n = 3, a Chenevier determinant ring, patching at nice primes, with a new determinantal local model requiring g² + e′ ≤ D₀, derived by an unread argument [PATCH §0]). A consequence would be the author's "weakening of Vandiver".

**Galois representations** (`Row0b`) [GALREP] come from descent to unitary groups, an Eichler–Shimura-type construction in odd rank, a stable-range theta lift and base change, with WD matching only for abelian, N = 0 (or tame) parameters [ROWCRYS]. The key unread step is `CongUW4`/`wtLacEx_holds`. An import closure of 66,168 files has no self-reference.

---

## 9. What has and has not been checked

### 9.1 Step by step

"Read to" levels: **C** = down to classical statements; **N** = to a named new idea; **S** = statement or top level only.

| step | read to | main unread items (full list §9.4) |
|---|---|---|
| Windowed Landau, quantifiers | C (correct; every body but `iteratedDeriv_laplace`) | — |
| Bridge, ThinScales | C (exact identity) | TT with exact shares |
| Host selection (`PairEx`) | C (classical orthogonality, read) | `twist_one`, `page_across`, zero density, progression PNT |
| Ledger L0–L15 | C (every step and every body read) | — |
| Engine core; orbit route at signal primes | C to statement leaves: kernel law and `lemmaS` read [KLAW]; LP assembly read to CLR:299 | `IntInert`, `HypShape_of`/`b0`, `Quant`, `LogStep`; `StdTie.adapted` |
| Hecke route at inertClass primes | C below `adm2`; `adm2` proved, conditional | ≈ 15 site hypotheses (AdmGLt, MInv, FrameLatMapLt) |
| Composition; tie of Ga to N_u; adm11; floor | C (every branch read) | `DegreeCountBound`, `UsedTuplesBoundByConstant`; ModelsOK producers |
| Seesaw `MIid` | N (live) | the supplier's own hypotheses |
| Heights; DIV algebra; L6 | C (`stepE_num`, Chowla–Selberg read); C to 7 `Published` premises | `covolume_measure_eq_one`, `FlatDegreeSt`; a norm-identifying lemma |
| det ι (SpecDet, MultEq) | C to Rallis-type inputs | `AForm`/`BForm`; Siegel–Weil leaves |
| Layer covolume; E1 | N; N (discriminant budget, mirabolic chain) | `ThmB`; `ThURel`, `ExportTie` |
| Type prime T: Count5, level-T lattice, floor | N [TU; TDIV; TFLOOR] | `cdScale`; `Conclusion5Sharp`, `TwistedColumnBoundAtT`; `colsTiedSym_std`; L3/Lo5 producers |
| Bost/HN frame | C | `slope_inequality_mean`, `FrameLA1` |
| Near-orthogonality; dimension count | N (live, proved by named theorems [NONVAN]); N | leaves; `rowsTiePT'_of` |
| E2, KillAt, `TopCore` | N (cocycle count read in full; `SenLat` proved) | `PerS.image`; Wach-module lemmas |
| U(3) R = T; Row0b | N; N (l-adic limits) | g² + e′ ≤ D₀; `CongUW4` |

### 9.2 Where the argument exceeds the published literature

1. Rank-uniform limit multiplicity with exponential precision; the compression formula [COUNT; FORMULAGAP].
2. Near-orthogonality of Bessel periods to relative b^{−6} by double unfolding [PAIRB; COUNTS; THMB].
3. p-adic divisibility of high-order jets of higher-rank CM theta kernels: hyperbolic cancellation, LP duality on bipower radii, the cap lemma [ENGINE; ENGINE2; JETA].
4. Selmer bounds uniform in l for weights up to x^{401}: Skinner–Wiles for U(3) with a determinantal local model [ONECHARU; MODU3; PATCH].
5. Selmer killing at finite level over a tame tower [KILLAT; LARGETW].
6. Residual irreducibility at all l from depth-zero types [TWIST].
7. Galois representations via a stable-range theta lift; crystallinity by l-adic limits [GALREP; ROWCRYS].
8. Uniform covolume bounds on varying Shimura varieties [VOLUME; HS].
9. `TopCore`, an integral comparison far outside Fontaine–Laffaille [BEYONDFL; TOPCORE; SENLAT].
10. An index budget for products of short forms [INDEXBUDGET; E1LOOSE].

### 9.3 Status of the former holes

The first review's five holes in the reconstruction [REVIEW-MAIN-ARGUMENT A2]: **H1** (det ι) supplied by `SpecDet`, read, with `AForm`/`BForm` and Siegel–Weil below it at statement level [DETSIG; LIVEPATH]; **H2** (seesaw supplier) closed by a 20-step trace, conditional on its own laws; **H3** (twisted places) restated: Tw has no cutoff in l, its cost a discriminant budget inside E1 [TWSET; INDEXBUDGET]; **H4** (layer signatures) forced by `arithAt`, and DIV uses only |p_j − q_j − k| ≤ m; the question behind it, where the m-growth comes from, is answered in §6.4; **H5** withdrawn [LEDGER §0.5].

### 9.4 What rests on statements only

Each item was read at statement level only, or not opened. After round 15 the statement-only items **on the spine** are these [SUMMARY §17–18]:
- **The type prime** [TU; TDIV; TFLOOR], unread and load-bearing: `cdScale`/`cdScaleTie` (that the formal degree is the Harish-Chandra value, on which log T* − Lam5 = O(L) rests); `Conclusion5Sharp` and `TwistedColumnBoundAtT` (the real T-adic loss of the jet steps); `colsTiedSym_std`, `lowerMap_tie`, `beOnTie_true`, `ipV_co_ofS` (the level-T record); the producers of the L3 floor and of Lo5 (`slopesMF_of_count_fam`, `placesF_of`).
- **Theorem S and the count** [NONVAN]: their leaves; the in-tree Siegel–Weil input; `rowsTiePT'_of` (count ↔ this HH); the `BesselId` supplier; `irr_row_closed`; `FrameLA1`; `ramRankF_min`.
- **Kernel law and `lemmaS`** [KLAW], now read to: `IntInert`, `HypShape_of`/`b0`, `BeData.exists_of_curveData`, `Quant`, `LogStep`, the `lat_S` leaves; passed down as hypotheses, the host field `der.frob` and `StdTie.adapted` (supplier `linkR_stdTie_entry` located, unread). The suppliers of AdmGLt, MInv and FrameLatMapLt concern `adm2` on the Hecke route only.
- **Two adm11 inputs** [ADM11]: `DegreeCountBound` and `UsedTuplesBoundByConstant`, which carry the ±C·B₀ precision against ΣA·log g.
- **Covolume** [NORMS; COVOL]: `covolume_measure_eq_one` and the `FlatDegreeSt` chain.
- **L6's seven `Published` inputs** [L6].
- **Classical analytic inputs under host selection** [HOSTSEL]: `twist_one`, `page_across`, `zero_density_box`, the progression-PNT chain.

Off the spine, or upstream of read clauses:
- **Analytic end** [ENDGAME; HOSTSEL]: `topsFrame` (TT with exact shares); `levelData`, `topsChoiceH`, `fieldChi`; `gmA_eq`, `ThinH`'s producer; the existential frame constants.
- **Engine and tie** [ENGINE; ENGINE2; ADM11]: `kform_of_ker`; `decomposition_of_hh`, `adm7`, `ExpansionEquality` (Hecke route); the producers of ModelsOK/twU, pdv and the Adm2InU binders.
- **Slope side**: `AForm`/`BForm`, the Siegel–Weil leaves, `SpecX.main` [LIVEMULT]; `ThmB` and point heights [VOLUME]; the body of `part_five_family_of_mass_volume` (Count5).
- **E1** [INDEXBUDGET; E1LOOSE]: the suppliers of `ThURel` and `ExportTie`; J0/`ExponentStatement`; `localIdx`, `heights_arith`.
- **E2 and Galois** [WHERECONG; TOPCORE; SENLAT; G2A; ROWCRYS; PATCH]: `PerS.image`; the mod-l Sen step; `UseLoc.main`; Wach-module lemmas; `CongUW4`/`wtLacEx_holds`; C_cris bodies; `HasAut` and g² + e′ ≤ D₀; `ConclusionZ`, `D7.Z_tie`; `IsBCV`'s unramified clause for l ∈ {q, d, small}.

Now read, so removed: `PairEx`; the ledger bodies and `stepE_num`; the adm11 producer, the floor and every adm2 branch; `thmAJetA` to CLR:299; Chowla–Selberg; `lemmaS` and the signal kernel law [KLAW]; the live Theorem S and count chains [NONVAN]; Count5's supplier chain and the level-T integrality chain [TU; TDIV].

### 9.5 Open conceptual questions

1. **Which inequality carries the barrier.** The identified carrier is the loss at the type prime, Ee_T/U ≥ 2m·x^ε (§6.4) [SHARP]. Open: whether the *real* T-adic loss of the jet steps is ≈ EatT per lift, as the unread `Conclusion5Sharp`/`TwistedColumnBoundAtT` assert, rather than the Weyl-mean cost per level [TFLOOR oddity 2]; the `SeenDef` reading; and the sign of the covolume q-part. WHYHALF calls this the conceptual heart of "why 1/2".
2. **Rigidity of T.** log T* − Lam5 = O(L) holds in TFLOOR's computation only if the formal degree under `cdScale` is the Harish-Chandra value; the Lean proves no matching upper bound (§5.5).
3. **Metric sharpness of Bost.** The frame gives robust rank only. Nothing read controls the Hadamard defect of the composite, h(u) − log‖B_u‖_true, or the word-dependent seesaw constant a_u, whose uniformity was not checked [SEESAW oddity 3]; the forced-rigidity principle requires all to be tiny (§6.4).
4. **The three DIV norms.** No lemma identifies the definite frame of the Rallis-hook input with the `pairK` Fock frame of the jet bound; the tie is the shared logΩ symbol and type-shared frames. A mismatch would falsify L6 or D2 rather than shift Main [STEPE §3.4; NORMS].
5. **Scale of the numerical evidence.** The checks of §9.6 run far below a ≈ x·b, at rank ≤ 2, with one top; no two-lift composite has been computed.
6. **Layer index against lift index.** Nobody showed that the layer index matches the lift index one for one [ARCH §7.7]. Mram is now identified: the level-0 vectors on which no torus character at T is trivial, with dim Mram/dim Mu0 = (1 − 1/(T − 1))^f [TU; NONVAN].
7. **Design choices.** Why exactly 3 in the shares; why orbit length n′ > 2 rather than just even; why t has the shape of §1; whether `BehrendSets` chooses T2 [ENDGAME §2.3; WHYHALF §6.3, §6.6].

Now answered: what T is, what bounds it, why one prime serves all lifts (§5.5); whether eE carries the barrier (no); whether k/n² is non-vanishing (no, §6.1); whether Theorem S is conditional (no, §7); the signal kernel law (§4.3); why b is exponential (§4.7); which route carries the count (§4); the backward charge (real, §4.8); where the Galois side enters (E2, §5.2); m = 1 (trivial); the zero-chain alarm (closed); how (q, d) is chosen (§2.3).

### 9.6 The numerical checks

Three checks bear on the spine; none runs Lean code. **NUMTEST3/4** test the Hecke-route kernel at orbit lengths 2 and 4 with genuine minors, caps ≪ a/p (§4.8). **NUMTEST5** tests the capped law at a signal place across the kink (§4.8). **NORMS** tests the Chowla–Selberg constant and the archimedean size of D^aσ(0) (§5.5), not the higher-rank Fock bound or the hook and covolume normalisations. None tests rank > 2, several tops, chains or real sizes.

### 9.7 Second review: candidate failure points and what was found

A second cold review, with an adversarial pass [REVIEW2], judged the exposition "understandable with gaps": the analytic shell and the ledger algebra close on paper (it re-derived 9 = 5 + 3 + 1, the U range, the balance and the Riesz weight, and checked the Chowla–Selberg constant numerically for d = 3, 4). It ranked five candidate failure points. Round 15 read each.

1. **Metric sharpness of the Bost step.** *Found:* the mean-slope inequality runs through HN pieces, robust rank and a layer cake, and Theorem S's diagonal clause excludes a single heavy functional (§5.3) [TFLOOR B; NONVAN]. *Open:* what controls the Hadamard defect, h(u) − log‖B_u‖_true and a_u (§9.5, item 3).
2. **The √x barrier is not located.** *Found:* eE totals ≈ B₀, as the review said; the barrier is carried by the loss at the type prime, Ee_T/U ≥ 2m·x^ε (§6.4) [SHARP]. *Open:* this rests on the `SeenDef` reading and on unread hypotheses for the real T-adic loss [TFLOOR].
3. **T_u and Count5.** *Found:* T is a level prime carrying all m lifts; its gain is the degree of the heavy component read in level-T coordinates, paid by the mean weight in the source slope; the product formula holds in the rank-one model; rank bounds T above; log T* matches Lam5 to O(L) (§5.5) [TU; TDIV; TFLOOR]. *Open:* `cdScale`; `colsTiedSym_std`.
4. **Leading-coefficient cancellation through one logΩ symbol.** *Unchanged:* the cancellation is syntactic, the truth of L6 and D2 to relative x^{−4} rests on statement-only inputs, and no lemma identifies the three norms (§5.4). The review's check, all three normalisations in U(1,1) or U(2,1), has not been done.
5. **The kernel law at rank ≈ x^{399}.** *Found:* the signal kernel law and `lemmaS` are read to statement leaves; it is the Hecke-route theorem specialised, and the slope is 1/2 at every place (§4.3) [KLAW]. *Open:* no two-lift composite at rank > 2 has been computed.

The review also observed that the core is itself of GRH strength for χ_{−d} (§6.4).

**The reviewer's opinion.** The reviewer stated that, on present evidence, it considers the argument as described *very unlikely to be correct*, the likeliest failure being in steps 6–8 rather than in the analytic shell. Its reasons: terms of size x^{4.5}·U cancel along a chain of one-sided inequalities, so every link must be tight to relative x^{−1/2}, and no mechanism for that tightness is described; and the most novel inputs were statement-only. It named what would change its mind: (i) a toy computation (m = 2, small rank) showing the composite jet/Bessel map near-isometric and the three metrics agreeing in their logΩ coefficients; (ii) an identified step whose actual loss is ≳ √x·|TT|·b per lift; (iii) a checkable account of the T mechanism, including what bounds T above; (iv) Theorem S and the kernel law read to classical leaves. Round 15 supplied readings, not proofs, bearing on (ii), (iii) and part of (iv); (i) is untouched. This document reports the opinion and does not adjudicate it.

---

## 10. Correspondence with the author's timeline

**Located.** (2) Dᵃ(Ω·θ)(0) divisible by p^{a/p+a/p³+…−O(log a)}: γ_p·a, §4. (5) the switch to G_z. (8) iterated theta lifts π ↦ π ⊞ μ_j[t], m ≈ √X: §3. (9) cancellation of order-m terms via Chowla–Selberg: the logΩ cancellation of §5.4 *(inferred match)*. (10) divisibility of the m-fold lift: §4.5. (12) seesaw and Rallis: `MIid`, λ_j. (13) Bost. (14) the cost of each lift: §6; "twisting" matches KillAt and §5.2; "division" plausibly DIV *(inferred)*. (15) an integral structure glued across Hecke characters: RR. (16) a relative trace formula with projected Poincaré series: Theorem S, without GL₅. (17) a weakening of Vandiver: the Ш bound. (18) covolumes, theta-series index, congruences: §5.2. (20) GRH: ⟨ψ⟩ with 4 : 3 shares and windowed Landau.

**Partly located.** (1) Stepanov: structural only (§6.4). (7) GGP periods; "m non-interlacing weights" is inferred. (19) `BehrendSets`, not traced to the live path.

**Not located.** (3) the sixfold cover of GL₅ and the Poincaré bundle. (4) W(1_S) ≥ 0 and the bootstrap. (6) W·1_{(0,1]} + X^η·1_{(0,1/X]} ≥ 0. (11) the Iwasawa tower via pigeonhole (candidates: the 2-power layer, KILLAT's tower). (14) the "2/3 a priori" version.

Sources: [WHYHALF; LOCALDIV; ARCH; LINKN; CHAININD; SEESAW; L6; RANK; CONGMOD; PAIRB; VWIN; ONECHARU; THETA].

---

[^n4]: NUMTEST4's phrase "inert in both" describes inertClass primes, not signal primes [SIGNAL; LEDGER §0.4]. NUMTEST3/4's kernels are GIdx-shaped and locally the signal-orbit object (§4.8).

[^tiebm]: The orphaned `TieBm` formulation, in which the middle levels are set to 0, has no consumer, so ARCH's worry about it lapses [SEESAW §0.1].

**Corrections that change the picture** (newer first; SUMMARY §5–§18 has the full list).
1. The √x barrier is carried by the loss at the type prime T, not by eE: eE totals ≈ B₀, not m·B₀ (STEPE's sum was wrong), and the signature residual cancels in truth [SHARP; REVIEW2, correcting earlier versions of §5.1, §6.4, §9.5].
2. The k/n² term is the E2 congruence allowance, not a non-vanishing term; Theorem S and the count are live and proved by named theorems, not "conditional" [NONVAN, correcting §0, §6.1, §7, RANK, LEDGER].
3. T is a level prime carrying all m lifts, its size a sum over lifts (log T ≈ m·x^ε); the scaling of the last map is not paid at the places above T but by the mean weight in the source slope [TU; TDIV; TFLOOR; the orchestrator's "T of the size of the cap" was a misreading].
4. The signal kernel law is the Hecke-route theorem specialised; B3 holds by construction; `lemmaS` is read [KLAW].
5. The orbit route at signal primes carries the count; the backward charge is needed [ADM2; ENGINE2; NUMTEST5]. b must beat poly(x)·e^{x^{ε/3}} [ADM11]. Σ_j(p_j − q_j) = mk is never used, and m = 1 is trivial [DIVKEY]. One (q, d) per window, by orthogonality [HOSTSEL].
6. Earlier: the live exponent is 9 [ENDGAME; LEDGER]; the x^{−1} precision is formula against formula [GATIE]; Tw has no cutoff at X″ [TWSET]; congruences enter only through E2 [WHERECONG]; MULTEQ read a dead route [LIVEPATH]; crystallinity via `G2a`; purity from Jacquet–Shalika [ROWCRYS].
