# The main argument, reconstructed from the Lean source

> **Status.**
> 1. This document gives a continuous mathematical account of the argument in the alpo.ge Lean tree (SHA-256 `9631b4f0…49c7fc`). The tree claims RH and GRH for Dirichlet L-functions.
> 2. It is a reconstruction by reading. Reader agents each read one piece over fourteen rounds (94 nodes), cited in brackets, e.g. [ENGINE]. Nothing was compiled or run in Lean. After round 14 every step of §0 has a mechanism read on the live path, and no defect has been found; what rests on statements only is listed in §9.4.
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
> | partner(t, g); w_{j,ρ} | the place cconj + g + topPl(t) ∈ Φ met from top t by Frobenius g; the cap at ρ, level j: thick w ∈ [b, b+η+1] (a/w ≈ x), top w ≤ 2b′, thin w ≈ w″ |
> | X′; b′; w″; X″ | e^{x^{ε/3}}; a/X′; b′/(xn); a/w″ = xnX′ |
> | δ; δ_p | \|T2\|/n ≥ x^{−ε}, T2 the thick places; ≤ e^{−x^{ε_z/7}}, with dim EE = (1−δ_p)·dim HH |
> | U; B₀ | \|TT\|·m·b·δ/2 ≈ x^{2.5}b, the signal unit (budget U·x^{1/2+O(ε)}); f·m·b·x^ε, the per-lift error unit |
> | ph; logΩ | y log y − y; γ + log(π/v) − L′/L(1, χ_{−d}) with v = rd_E/2 |
> | κ; I, I₁ | the similitude constant of ι; frame-row index sets (§7, RANK's κ, κ₁) |
> | BL; P; HH; H_B | Bost loss (§5.3); Selmer presentation (§8); the L² space (§3.1); the Bost scale x^{C_H}b (§5.3). Φ is only Gal(E/K) |
> | Ga; sg(u, w); LoP | the gain, a defined formula (§5.4); the per-place exponent Σ_j(gain_j + F_j − E_j); the loss allowance C·\|TT\|·m·b |
> | cc; E1, E2, E3 | the target lattice of the DIV map, whose slope is bounded through μ(RR^∨) by a base-to-column passage (§5.4); the three index errors of the covolume bound (§5.2) |
>
> *Sign of Ω.* COVOL writes the proved Chowla–Selberg identity as "−meanLog = γ + log(2π/√d) − L′/L", HEIGHT as "mean_ρ log(area(Λ^ρ)/π) = …". So logΩ = −meanLog in COVOL's sign; √d versus rd_E is a separate proved identity [COVOL §2; HEIGHT child 3].

---

## 0. The argument in one page

Fix a primitive Dirichlet character ψ, of order o, and ε ∈ (0, ε₁). Each step gives the Lean's statement and its node; each uses only earlier steps.

1. **The function.** G_m(y) = G_z(y) + (3o+1)^{−1} Σ_{ξ∈⟨ψ⟩, ξ*≠1} Re g_{ξ*}(y) (§1): Riesz-smoothed Chebyshev functions of ζ and of ⟨ψ⟩ with their main terms removed, all weights positive. The coefficient (3o+1)^{−1} is the Fourier coefficient at ψ^j of the share measure λ(h) = (3 + 1_{A₀}(h))/(3o+1) with which the tops are spread over A/A₀ [ENDGAME §1b, §2.3].
2. **A host for each window and scale.** An abelian CM field E ⊃ K = ℚ(√−d), Gal(E/ℚ) = {±1}² × A, in which ψ(p) is the A/A₀-coordinate of Frob_p. One pair of primes serves a whole Landau window: q ≡ 3 mod 8, log q ≍ Y^{ε/5}, and d ≡ 7 mod 16, log d ≍ Y^{ε/5}log²Y, at Y = X^{1/J}. The 3o twists ξ(·/q)^i(·/d)^j, (i, j) ≠ 0, satisfy |g(y)| ≤ y^{1/2+ε/2} and |L′/L(1)| ≤ 4 log y for all y ∈ [Y, X] (`PairGood`). The proof is elementary orthogonality over moduli q > Z², with Siegel and zero density removing exceptions: neither GRH nor the large sieve [HOSTSEL].
3. **The engine: one lift, one signal prime.** At a signal prime (inert in K, split in ℚ(√−q)) the positions form an even orbit, the kernel is exp(−cross Gaussian) × integral, and the self-Gaussians cancel. LP duality gives, per top, v_p ≥ Σ_{e odd}(a_t/p^e − cap)₊ − γ_p·Wc − (logs), cap = number of minors at the partner. At a thick partner the e = 1 term is the Riesz weight b·(a_t/(bp) − 1)₊; the backward charge γ_p·Wc is booked in E. A second (Hecke) route on the same core serves the inertClass primes, which the bridge discards [ENGINE2; ADM2; §4.2–4.4].
4. **m lifts.** The one-lift bound holds on the whole global lattice of each level, so gains add along `chain_ge`. The actual column map lands in ϖ^{e·Σ_j(g0S+F−ES)}·(level-m lattice), and this exponent is the ledger's sg symbol for symbol (`liftI_of`, `WJS.Conclusion1`) [ENGINE2 §2.6, §4; GATIE §0.3].
5. **The gain is tied to a lattice.** Ga = Σ_w 2·lw·e_w(Σ_j gain_j(w) − τ(w)) is a *defined* piecewise-linear formula. The source lattice is *defined* as N_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋}·NuLat_u, sg = Σ_j(gain + F − E). Step 4 gives Bk_u(N_u) ⊆ cc on every branch (§5.4): this inclusion *is* the p-adic divisibility of the actual chain maps. An exact slope formula with one floor per place gives μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo5 [GATIE; LEDGER L2].
6. **DIV.** μ(cc) + h(u) − Fo ≤ Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + c·|TT|·a·La + c·m(B₀+Nc)x^{2ε}. Here the height (Fock norms, Chowla–Selberg, Rallis hook products) meets the covolume bound of §5.2, whose index errors E1, E2, E3 are per-lift; E2 is the only entry of the congruence machinery. Per lift and place, three terms combine, and the content is the Young-diagram bound `stepE_num` [LEDGER L1, D1–D5; DIVKEY; STEPE; §5.1].
7. **Bost.** s − log|W| − BL ≤ μ(cc), with s the mean slope of the N_u net of heights and BL a rank-free Harder–Narasimhan/frame loss [LEDGER L0; RANK]. Non-vanishing of the joint period map (§7) is what makes it informative.
8. **Slope floors and the level prime.** μ(M_u) ≥ −c·|TT|·a·La(1+m/k); Ee ≤ m(ΣA·lg + cE·B₀), the real divisibility's losses (clause adm11); log T_u ≥ Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − c(La + m²La/k) [LEDGER L3–L5; GATIE §2c].
9. **Key identity.** Σ_t m(ph(a_t) − a_t logΩ) − ΣA·Lam5 + m·ΣA·lg = Main + ΣA·c(La + m²La/k) exactly, where Main = Σ_j Σ_t a_t(log a_t − 1 − γ + L′/L(1, χ_{−d}) − mean_ρ log w_{jρ}). The split half of log a! is the −L′/L(1, χ_{−d}) inside logΩ [LEDGER L7].
10. **Upper bound on the gain.** Steps 5–9 add, with Fo and h cancelling, to Ga ≤ Main + log|W| + (errors) (`Ga_bound5`) [LEDGER L9].
11. **Loss bound, and the main inequality.** ASK − Ga ≤ LoP = C·|TT|·m·b, ASK = Σ_t Σ_j Σ_n Λ(n)(1 − χ_{−d}(n))(a_t/n − w_{j,partner})₊: two explicit formulas with the same caps, no lattice [GATIE §0.2]. With step 10: ASK ≤ Main + ErrX5at, ErrX5at ≤ x^{5ε}·[|TT|·a(1+m²/k) + m(B₀+Nc)] [LEDGER L10–L12].
12. **Bridge.** ASK − MAIN = De exactly (orthogonality on Gal(E/ℚ)). Top and thin partners are discarded by an effective PNT (`ThinScales`). Only signal primes reach thick places, where the summand is the Riesz weight of step 3. Averaging gives U·[G_m(x) − SigA − 4x^{1/2+ε}] ≤ Σ(ASK − Main) + 2|TT|mb/x, U = |TT|·m·b·δ/2, with SigA ≤ 4o·x^{1/2+ε} by step 2 at y = x [LEDGER L13–L15; ENDGAME §2.3].
13. **Core bound.** Dividing by U: G_m(x) ≤ x^{1/2+9ε}, at every x ≥ x₀ of every window [Y, Y^{3/2}] of the family attached to ε; 9 = (2 + 0 + 3) + 3 + 1 (§6.2) [LEDGER §0.2].
14. **Landau on windows, and GRH.** A one-sided bound G ≤ C·y^θ on all y of windows [Y, Y^{1+δ}], Y → ∞, for a positive combination of g_χ, forces L(s, χ) ≠ 0 on Re s > θ for each χ in it; with ε → 0 separately for each s, L(s, ξ) ≠ 0 for Re s > 1/2 and every ξ ∈ ⟨ψ⟩, ζ included [ENDGAME §1c, §2.1].

**Where 1/2 arises.** Divided by U, the error of step 11 has three families [LEDGER §2a; WHYHALF §1.3]. One-off boundary terms, ≈ |TT|·a·x^ε once per chain, give x/m. Per-lift terms, ≈ B₀ = f·m·b·x^ε at each of m levels, give m. The non-vanishing term gives k/n². At m ≈ x^{1/2} each is x^{1/2+O(ε)}, so 1/2 is the balance of x/m against m; at m = 1 the result is trivial. The other square-root input is step 2, which removes the split primes without producing cancellation. Steps 3–9 must hold to relative x^{−1/2+O(ε)}; step 11 to relative x^{−1}, but formula against formula (§6.3).

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

b must beat poly(x)·e^{x^{ε/3}} (§4.7). t is fixed by r + t = 8fr + 4 + ⌈x^{377}⌉·nWv [ACCOUNT §1], subject to t ≥ r + 5, 3m < t and twists i < t below x^{401}; no node says why it has this shape.

---

## 2. The analytic frame

### 2.1 The windowed Landau lemma

**Statement** (`zeroFree_of_rpow_window`, called with δ = 1/2, C = 1) [ENDGAME §1c]. Let χ_i be finitely many Dirichlet characters with weights a_i > 0, G_F = Σ a_i Re g_{χ_i}, 0 < θ < 1, δ > 0. Suppose that for every Y₀ there is Y ≥ Y₀ with G_F(y) ≤ C·y^θ for *all* y ∈ [Y, Y^{1+δ}]. Then L(s, χ_i) ≠ 0 for every i and every Re s > θ. Off the windows only the trivial |g_χ(y)| ≤ C·y² is used. The conclusion holds for each L-function separately, ζ included.

**Mechanism** [ENDGAME §2.2]. In u = log y, the Laplace transform Φ of g(u) = G_F(e^u) is −Σ a_i(L′/L(s, χ_i) − s·L′/L(1, χ_i))/(s(s−1)): the main terms cancel the pole at 1, and Φ has simple poles at zeros. The residue at ρ is S(ρ)·(−1/(ρ(ρ−1))) with S(ρ) > 0, so positive weights cannot cancel a zero, and a real zero pushes G *up*; positivity of Dirichlet coefficients is never used. The coefficients a_k(z) = ∫ g(u)u^k e^{−zu}/k! du are bounded from the one-sided bound on a window W = [U, (1+δ)U], since |g| + g ≤ 2R there; the extra Re a_k(σ) is the price of one-sidedness. With k ≈ (1+δ/2)σU the Gamma kernel concentrates on W, and σ = 336 (for δ = 1/2) makes the tails ≤ C/σ^k. A zero with Re ρ₀ > θ gives a pole at distance d < σ − θ. Either it is real and its positive residue makes Re a_k(σ) ≳ d^{−k−1}, or γ is chosen so that one pole is the *unique* nearest singularity to σ + iγ. Either way a_k grows like d^{−k}, against (σ−θ)^{−k}.

**Why sparse windows suffice.** The radii depend only on σ and the zero set, never on U, and each window supplies one k. So any windows with U → ∞ and fixed log-ratio work, provided the bound holds at *every* y of each window. ENDGAME read every body except the routine `iteratedDeriv_laplace` and judged it a correct theorem with a correct proof.

### 2.2 How ψ enters: the host and the shares

Every hermitian space lives over a CM field E, the host, built for each scale x from a pair (q, d) fixed per window [HOSTS §1(a), §2(c1); HOSTSEL]. E is the fixed field, inside ℚ(ζ_{QS·q·d}), of the kernel {a ≡ ±1 mod 2^{e₂+2}, ψ(a) = 1, (a/q) = (a/d) = 1} of the Artin map [ENDGAME §2.3]. So ψ factors through Gal(E/ℚ) = {±1}² × A, [E:ℚ] = 4n. A₀ = ⟨a₀⟩ embeds in the 2-power quotient, |A/A₀| = o, and every frame character trivial on A₀ is ξ·(·/q)^i(·/d)^j with ξ ∈ ⟨ψ⟩. **ψ(p) is read off as the A/A₀-coset of Frob_p.** Each auxiliary object has one job:

- **K = ℚ(√−d)**, d ≡ 7 mod 16 prime: the CM curve behind every theta kernel, supersingular reduction at inert p, the factor (1 − χ_{−d}), and L′/L(1, χ_{−d}) inside Ω [ARCH §1].
- **√−q**, q ≡ 3 mod 8, (−d/q) = 1, separates *signal* primes (inert in K, split in ℚ(√−q)) from *inertClass* primes (inert in both) [LEDGER §0.4]. At a signal prime the hermitian space is split.[^n4]
- **The 2-power layer**, of order 2^{e₂} ≈ x^{2+8ε}: an inertClass prime has a split hermitian form iff h has even order; the anisotropic ones (density ≤ x^{−2}) are dropped [SERVED §0].
- **The level primes g₀, g₁** give the Poincaré series a level and carry depth-zero types forcing residual irreducibility at every l [PAIRB; TWIST; ORDER]. **T_u**, one prime per word u, sets the level of the source forms.

**The shares.** The tops are distributed over A/A₀ by λ(h) = (3 + 1_{A₀}(h))/(3o+1), with λ̂(ψ^j) = (3o+1)^{−1} for j ≠ 0: the weight in G_m [ENDGAME §2.3; CHBALANCE §2(a)]. Any α + β·1_{A₀} with α ≥ 0, β > 0 would do; uniform shares would leave only ζ. No reason for the 3 was found. ζ has weight 1, so the core bound alone would give RH.

### 2.3 What is counted, and the bridge

**Which primes.** ASK counts n = p^i, p inert in K, i odd, with the cap w at the partner place: Σ Λ(n)(1 − χ_{−d}(n))(a/n − w)₊ [ENDGAME §2.3; LEDGER §2c]. Only signal primes have thick partners (w ≈ b, a/w ≈ x); inertClass partners are top or thin, with Riesz length ≥ X′/2. The thick-class indicator is a combination of the 4o characters (·/d)^α(·/q)^β ψ^j. After averaging, the (α, β) = (0, 0) part is exactly U·G_m(x); the 3o twisted characters make SigA.

The bridge (`ch_balance`, `ch_core`) is a finite-group computation that holds exactly [CHBALANCE §0–2].

**Step 1 (exact identity).** Orthogonality on Gal(E/ℚ) gives ASK − MAIN = De, where

$$\mathrm{MAIN}=a\Big(\log a-1-\gamma+\frac{L'}{L}(1,\chi_{-d})-\operatorname*{mean}_{\rho\in\Phi}\log w(\rho)\Big)$$

and De = |Φ|^{−1} Σ_g Σ_ψ ψ̄(g)·w·G_ψ(a/w) is an expansion over all characters of the Galois group (G_χ is the g_χ of §1). The identity uses

$$\sum_n\Lambda\chi(n)(a/n-w)_+=w\,G_\chi(a/w)-a\,\tfrac{L'}{L}(1,\chi).$$

The identity holds with an *arbitrary* constant in place of L′/L(1, χ) (CHBALANCE oddity 1); the true value is pinned by the host clause `HostAddCharCompatible` [SERVED §0].

**Step 2 (thin and top partners drop).** There the Riesz length is ≥ X′/3, and `ThinScales`, |G_χ(y)| ≤ y·e^{−cx^{ε/8}} for y ≥ X′/3, makes them negligible: de la Vallée Poussin with an in-tree zero-free region, real zeros β > 1 − 1/400 being excluded by host-selected boxes [ENDGAME §2.1; SERVED Part 2].

**Step 3 (thick partners and averaging).** **The x-scale part of ASK, which carries ψ, sits entirely on signal primes** [SIGNAL §0.5; LEDGER §2c]. Averaging over u₀ ∈ A₀ and the tops turns λ into the weights of G_m.

**Result.** The bridge gives

$$U\cdot\big[G_m(x)-\mathrm{Sig}_A(x)-4x^{1/2+\varepsilon}\big]\ \le\ \sum(\mathrm{ASK}-\mathrm{MAIN})+\frac{2|TT|mb}{x},\qquad U=\tfrac12|TT|\cdot m\cdot b\cdot\delta .$$

Every replacement error is ≲ x^ε·log x relative to U; the x^{1/2} comes only from Err/U and Sig_A [CHBALANCE §2(c)].

**The twists are bounded, not cancelled.** Sig_A collects the 3o twists ξ·(·/q)^i(·/d)^j, (i, j) ≠ (0, 0) [ENDGAME §2.3]. They never enter the function given to Landau. Each is bounded *two-sidedly at the single point y = x* (`bdG` ← `boundedTw` ← `PairGood.bounds`), and Sig_A ≤ 4o·x^{1/2+ε} (`sigA_le`, the only consumer of `.bdG`). Through

$$\sum\Lambda\psi^j(1-\chi_{-d})(x/n-1)=\sum\Lambda\psi^j(x/n-1)-\sum\Lambda\psi^j\chi_{-d}(x/n-1),$$

this bound lets a count over inert primes stand in for the sum over all primes. **The split half of the primes is paid for by the choice of (q, d)**, so L(s, ψχ_{−d}) never enters Φ and cannot cancel a zero of L(s, ψ). G_m involves only ζ and ⟨ψ⟩, so the change of host is invisible to Landau.

**Host selection** [HOSTSEL]. `PairEx`, a closed theorem, has now been read.
- *Sizes.* Besides the congruences and sizes of §0 step 2, q | d+1 and every odd p ≤ Y^{ε/5} divides d+1. The bounds hold for every ξ mod N, not only ⟨ψ⟩.
- *One pair per window.* `winPairs` fixes (q, d) at Y = X^{1/J} *before* quantifying over x. The bound is proved on [X^{1/J}, X] and consumed at y = x for each x of a window inside it, plus one Lipschitz step to |y − x| ≤ 1.
- *Orthogonality, not the large sieve.* Every modulus exceeds Z² = Y^{800K}, Z the truncation. Reciprocity turns Σ_q(nn′/q) into Σ_q(q/s), and a Gallagher-type PNT in progressions bounds it by Y^{−B}·#P except at one s = n\* (unique by Landau–Page; its few pairs are bounded trivially). The diagonal is C·y log y; Markov on dyadic blocks gives a bad proportion ≲ Y^{−τ} on the whole range.
- *Siegel and zero density.* Siegel enters only there, making Y₀ ineffective. Any q or d with a twist zero in Re s > 1 − 1/400 inside a box is removed by zero density (≤ U^{3/8} against ≥ U^{9/10}); this is also what gives |L′/L(1, χ_{−d})| ≤ 4 log x.
- *Simultaneity.* The structural host data are built for *every* (q, d) with `PairGood` (inferred; `levelData`, `topsChoiceH`, `fieldChi` unread); averaging excludes ≤ ½ of the q, then ≤ ½ of the d.

### 2.4 The order of quantifiers

[ENDGAME §2.1; LEDGER §0.2]
ψ; then e_D, e_L, ε₁ from `TopG` (live: 2, 0); then s with Re s > 1/2, θ = 1/2 + min(Re s − 1/2, 1/2)/2 < Re s; then ε ∈ (0, ε₁) with 9ε ≤ θ − 1/2; then a family `FamP ε` with windows [Y, Y^{3/2}] for arbitrarily large Y; then, for each window, one (q, d) at Y_{qd} = X^{1/J}; then, for each scale x of the window, E, the frame, TT and the lattice data; then the core bound at every x ≥ x₀ of every window; then Landau with δ = 1/2. Nothing is uniform in ε: each s gets its own ε, family and hosts.

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

  θ_{c,c′} is written out in §4.1; the jet is paired against column minors whose number is the cap of §4.2 [HIGHERRANK §1.2].
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

**Sources.** For each word u (a binary string of length k; |W| ≈ 3Γ²x^{C_F}, Γ = e^{Cm⁵fx^ε}) the source is N_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋}·NuLat_u, with NuLat_u ⊆ M_u of colength ≤ duS·(τ + io). This is a definition (`NprimeDef`); §5.4 explains why it is legitimate [GATIE §0.3].

---

## 4. The engine: p-adic divisibility at inert primes

Two routes prove the one-lift bound, for two classes of inert prime p ≥ 5 [ADM2; LEDGER §0.4; ENGINE2]. The primes that carry the count are the **signal** primes: only they reach thick places, where the ASK summand is the Riesz weight at p ≈ x (§2.3). They are served by the **orbit route** (§4.3). The **Hecke route** of ENGINE (§4.4) serves inertClass primes of even order. Their partners are top or thin, and the bridge discards them by ThinScales. Both routes rest on one local core (§4.2).

### 4.1 The function and the coordinate

**The kernel** [ENGINE §1.1–1.2]. Let Tau ≃ Gal(E/K) be the CM type. The space is VV = ℂ^{Tau×N′×N}, an N′×N matrix variable at each τ, with hermitian form H(z, w) = area(Λ)^{−1}·Σ z_{τij}w̄_{τij} and lattice Λ = δ·Φ_Tau(AA0·Hom(N, N′)), where δ·O_K is the period lattice of the CM curve and AA0 an O_E-ideal. θ_{c,c′} is a reduced theta function for (H, α, Λ), i.e. a section of the line bundle with Riemann form H, namely a **finite Heisenberg sum of torsion translates of one vacuum theta**:

$$\theta_{c,c'}(z)=\sum_{x\in\Lambda/A}\alpha(x)\,U_x\Big[\sum_{y\in\Lambda/B}\widehat{\Phi}(\cdot-x)(y)\,\alpha(y)\,U_y\,\theta_{\rm vac}\Big](z),$$

with Φ the finite Schwartz datum of (c, c′) and A, B half-lattices twisted at SS. θ_vac is built from th0(z) = U_t(σ*)(z)/U_t(σ*)(0), t = ω₀/2, σ* = σ·e^{−s₂z²/2}. The Gaussian is not multiplied in separately: at ∞ it is the automorphy factor in U_x, p-adically the class of ph = −log(σ*(εℓ(T))/T).

**The coordinate** [ENGINE §1.3]. At inert p the CM curve is supersingular, with height-two Honda logarithm ℓ(X) = Σ_j X^{p^{2j}}/p^j. The kernel's variables are z = ℓ(X), and "integral" means integral in X. With ϖ^{p²−1} = p, a series integral in X is integral in z/ϖ, so

$$v\big(\partial^n f(0)\big)\ \ge\ v(n!)-\frac{|n|}{p^2-1}\qquad(f\ \text{integral in }X).$$

Since v_p(a!) ≈ Σ_{e≥1} a/p^e and a/(p²−1) = Σ_{e even ≥ 2} a/p^e, what survives is γ_p·a with γ_p = p/(p²−1) = Σ_{e odd} p^{−e}. This is the author's item 2.

### 4.2 The common core

[ENGINE §2; ENGINE2 §0, §2.1; ADM2 §0–§1]
1. **Kernel law.** At a served place the kernel is exp(−Ph)·U, with U integral (bounded coefficients, no growth) in the height-two LT parameter X, and Ph ≃ Σ_e be(x_e, y_e) a cross Gaussian between the two halves of the orbit, with no diagonal terms (≃: up to a factor whose exponential is integral). It does *not* claim σ* integral; in one variable that is the tautology ph = −log σ*. The content is the class be ≃ G_ser(c, σc), with 1/p part c(xy^p − x^p y)/p (Dieudonné/Honda). A reader's check: the self-Gaussian ph ≃ c·x^{p+1}/p predicts v ≥ −⌊a/(p+1)⌋ for the coefficient of W^a, W = z/ϖ, which is NUMTEST's measured a/(p²−1) converted; it is attained, so c is a unit [ADM2]. After rescaling even and odd positions by ϖ, exp(−Σ G_ser) = exp(−(π/p)hh)·V with π = ϖ^{p+1}, V integral, hh = Σ S^p_s S_{s+1}, S_s = Σ_l(−1)^l Z^{p^{2l}}_{s−2l}. Dwork gives θ ∈ O[[Z]][hh/p]: **each power of hh/p costs one p.**
2. **Even orbit; self-Gaussians cancel.** The orbit has even length on both routes: ord h is even at a served inertClass prime, and nP = 2·ord(2h) at every signal prime. Rotation by one swaps the two isotropic halves of the split hermitian space, and `hyperbolic_plane_split` leaves only the cross pairing: the only use of "split at p". The orbit route records this as condition B3 (every monomial of be has positive even- and odd-position degree). With odd length the gain would fall to a/(p²−1).
3. **Caps = number of minors.** The jet operator is (top linear forms)^{a_s} times column minors, one per column of the level-(j+1) Young diagram at each position. The cap is ν₂ at a top and the first-row length elsewhere, **by definition**. Its identification with the ledger's w is `LatTied` (Hecke route) and `row_le`, ν₀(partner) = w_j − kaJ + u₀ (orbit route) [PAIRING; ENGINE2].
4. **Legendre, Dwork, odd e.** The pieces of hh have degree p^{2l+1}, so only odd levels occur. With v_p(m!) ≥ m/(p−1) − lg m and 1/(p−1) = γ_p + 1/(p²−1), the top variables keep γ_p·a, and **the minor variables pay their own rescaling out of their own factorials**. Each odd-level factor uses p^e top derivatives and costs one p, which gives Σ_{e odd}(a/p^e − cap)₊. At split p the gain is 0. The factor 2 in Λ(n)(1 − χ_{−d}(n)) is on the ledger side [WRITEUP S7].

### 4.3 The orbit route at a signal prime

[ENGINE2; SIGNAL; ORBIT; JETA]

**Setup.** Frob_p = ((+1, −1), h), and c = ((−1, −1), 1) is not a power of Frob, so every place of F = E^{⟨c⟩} above p splits in E. Positions run along the orbit of z ↦ z·Frob·c. Even positions lie over w (tops or thin), odd ones over w̄ (thick or thin), so every odd-distance partner of a top is thick or thin: dTop = ∞, no top–top exclusions, no Hecke operator, no colength.

**Kernel law.** `ThetaExpansionAllPlaces`: the adapted entry of the *global* theta kernel is U·exp(−Σ_{orbits} be), U integral, be satisfying B1–B4. Its supplier `normalisedFamily_standardBases_integrality` covers signal places explicitly; it was read at the top level, two of its three inputs as statements. Stated for every column choice and class pair, it holds on the whole global lattice through `KForm` and the equality `KerEnt.lat_S`.

**Statement** (`split_bound_eleven_one`, `OrbitValuationBound`). Per lift and orbit the exponent is g0 + FOrb − errF:
- g0 = Σ_{tops}Σ_{e odd}(al_s/p^e − capU)₊ − dl, al = a_t − 2cG, capU = (family weight at the partner) − kaJ + cG;
- FOrb, the Gaussian-free LP value of the non-top rows;
- errF = γ_p·tops·(b + η + 1 + 3Sc) + c6·Σw/p + (digit sums).

**The e = 1 term is the Riesz weight** *(ENGINE2's arithmetic)*. At a thick partner the family weight lies in [b, b+η+1], and a_t = a(1 + O(x^{−17.5})), a = x·b. So

$$\Big(\frac{al}{p}-\mathrm{capU}\Big)_+=b\Big(\frac{a_t}{bp}-1\Big)_+-O(|\theta|),\qquad |\theta|\le\eta+1+\mathrm{kaJ}+c_G+2c_G/p=\mathrm{poly}(x).$$

This is the Riesz kernel (y/n − 1)₊ at n = p, y = a_t/b ≈ x, scale b; e ≥ 3 gives n = p^e. At a thin partner the term is ≈ a_t/p^e, with Riesz length ≥ X′. g0 can exceed the ASK summand by kaJ per level, harmlessly, since only ASK − Ga ≤ LoP is needed.

**Proof: LP duality** (`thmAJetA`, Lemma RA, read in full). Give frame coordinate i the radius 1/(p²−1) + r_i. If every bad bipower W_i^{p^α}W_j^{p^β} satisfies p^α r_i + p^β r_j ≥ 1, then v(κ!·coeff_κ) ≥ Σ_i κ_i(γ_p − r_i) − |coords|·(log_p a + 1). The input `lemmaS` (statement only) says be is at most one power of p worse than the Dwork weight 1/(p−1), and only on even–odd bipowers: **each Gaussian factor costs one p.** A residually generic frame and Cauchy–Binet carry the bound to products of actual minors. For one top with budget A and caps c_j at odd forward distance j, the primal is max Σ_j n_j subject to 0 ≤ n_j ≤ c_j, Σ_j p^j n_j ≤ A; the dual is min_{ε≥0} A·ε + Σ_j c_j(1 − p^jε)₊. The Lean takes ε = p^{−T} at the first odd level T where the budget binds and charges Σ_j min(c_j, A/p^j); since A·γ_p = Σ_{j odd} A/p^j, the gain is Σ_{j odd}(A/p^j − c_j)₊. The true optimum is larger but not in Riesz form; the weaker charge reproduces ASK prime power by prime power.

**The backward charge.** Rows behind the top cost Σ_{j<0}c_{s₀+j}p^{−|j|} ≤ γ_p·Wc, Wc the largest cap behind the top. At a signal top those positions are thick or thin, so this is ≈ γ_p·b per top, prime and lift; over signal p ≤ X″ and m lifts, ≈ |TT|·m·b·log X″, x^{ε/3} above LoP, booked in E (errF), not in Ga. ENGINE2 called it plausibly an artefact; NUMTEST5 (§4.8) finds that it pays for something real.

**One lift.** `liftI_of`: the proved exponent at a signal place is g0S + F − ES, ES = vDG + EatI, equal to the ledger's sg symbol for symbol. **Expert check first:** the kernel law in its signal branch, and `lemmaS`. Everything downstream is LP arithmetic and linear algebra, read to the bottom [ENGINE2 §5].

### 4.4 The Hecke route at inertClass primes

[ENGINE; ADM2; LOCALDIV; PAIRING; COLENGTH]
The served class GIdx is: inertClass (Frob = ((−1, −1), h)), ord h even, p ≥ 5, not a level prime, p ∤ T.

**Theorem** (`EntryExcessBound`, proved). For every choice of top exponents and minors,

$$v_p(\mathrm{jet})\ \ge\ \sum_{s\in TT}\ \sum_{e\ \mathrm{odd},\ e\notin d\mathrm{Set}(s)}\Big(\frac{a_s}{p^e}-\mathrm{cap}_{s+e}\Big)_+-\mathrm{deLoss},$$

with deLoss = Σ_s(r₁·lg a_s + r₀r₁·lg ls_s) + Σ_{s∈TT}(lg a_s)², r₀ = N(j), r₁ = N(j+1), lg = ⌊log_p⌋ + 1. dSet(s) is the set of odd distances from s to another top of opposite parity. Being universal over exponents and minors, the bound holds on the whole integral lattice Int_j.
- *Cap lemma.* Multiplying by a linear form is adjoint to a Hasse derivative, and a minor absorbs at most one derivative per direction, so level-e factors from top s number at most cap_{s+e}.
- *Hecke operators.* Pushed up the chain by a Rallis-type commutation, they unlock γ_p·a at even-position tops at a price p^{−Pr} per step; the colength τ removes the surplus, and a pairing of tops (`kinkHH`) leaves ± O(1).
- *`adm2` is proved in the tree*, conditional on ≈ 15 hypotheses of the site record `Joint.At.K1` (suppliers of AdmGLt, MInv, FrameLatMapLt unopened). Its one-letter law `VIntegral` was read to the leaves: the σ-addition formula, prime-to-p torsion integrality (Kronecker–Robert theta quotients), root extraction. No supersingularity is used; that sits entirely in be.
- *`posOK`'s supplier was read*: a position is the CM-type element orbRep_v·(1, h)^s, and σ∘iw_v = iw_v∘Frob.

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
deLoss (rank logarithms and Legendre digit sums) is ≈ f·x^{804}·log a per prime per lift with the Lean's bounds t ≤ x^{401}, k ≤ x⁵ (ENGINE estimated x^{798}), far above the loss of 1–2 seen numerically (§4.8). The Lean never sums it over primes. It bounds N(j−1)N(j) ≤ N(m)² ≤ η, one polynomial parameter (η = 2m⌈x^{ch}⌉ on the live path), counts *all integers* ≤ X″, and closes with X″·η ≤ b (`SizeEta`: x·t·η ≤ w″, so X″·η = (a/w″)·η ≤ a/x = b). On the live constructor that is `scale_poly_comparison`, x^{ch+1228}·e^{x^{ε/3}} ≤ e^{x^ε/2}, with room b^{1/2}.

**Why b is exponential (corrected).** The earlier remark said b must dominate every power of x. The requirement is stronger: b must dominate poly(x)·X″, and X″ = x·n·X′ contains X′ = e^{x^{ε/3}}, itself superpolynomial because it is the Riesz length past which ThinScales discards top and thin partners *(inferred)*. So the comparison is poly(x)·e^{x^{ε/3}} ≤ e^{x^ε}. The threshold x₀ is existential, depends on ε, the constant record and the exponents, and is uniform over hosts, as the Landau windows need.

### 4.8 Numerics, and which object they tested

[ENGINE §3; NUMTEST–NUMTEST5; SIGNAL §E; JETA]

| test | object | the Lean's object? | result |
|---|---|---|---|
| NUMTEST σ, ℘; NUMTEST2 | D^aσ(0); ℘; σ(z+w)/(σ(z)σ(w)) | no | slopes 1/(p²−1), γ_p, γ_p, as the core predicts |
| NUMTEST3; NUMTEST4 | length-2 kernel, one entry; length 4 with det(Y)^m blocks | **yes** | worst −0.98; −1.54, det^m costs m |
| SIGNAL two tops; `jeta_lp.py` | length 4, caps ≤ 8; the top LP | yes; LP arithmetic only | worst −1.13; 0/4000 |
| **NUMTEST5** | the capped law at a signal place, cap ≈ a/p | **yes**, across the kink | worst −1.00 (length 2), −1.83 (length 4) |

The dispute over NUMTEST3/4's prime class resolves: their kernels are GIdx-shaped, and locally the signal-orbit object [ADM2; SIGNAL §5; NUMTEST5 §A]. Before NUMTEST5 all caps were ≪ a/p, so the kink was never probed.

**NUMTEST5** tested P1 = Σ_{e odd}(a/p^e − ν_e)₊ (the Lean's `topTerm`, dTop = ∞) on real theta-kernel jets with cap ≈ a/p [NUMTEST5].
- *What.* The smallest signal place, Θ = th0(z₀+z₁)·th0(c(z₀−z₁)) with N(c) = −1: rank-one jets ∂^a_{z₀}∂^ν_{z₁} and a 2×2 block (ξ·X)^a·det(Y)^ν, over ℤ[ω] at p = 5 (a ≤ 5p³), ℤ[i] at p = 7 (a ≤ 3p³) and both at p = 11 (a ≤ 6p²), caps ≤ 220; and a length-4 orbit (p = 5, a ≤ 320). Exact finite Leibniz sums mod p^K, no truncation.
- *Loss O(1).* Worst v − P1 is −1.00 over ≈ 250,000 jets, −0.83 for blocks, −1.83 at length 4, at ν ≈ 0 and Legendre-bad a.
- *The kink* is exactly at ν = a/p, and in the block it follows the number of minors, not the weight 2ν. The slack is ≈ +γ_p·ν below it (safe direction) and ≈ a/(p(p−1)) on it; beyond it v is at σ-level, like the anisotropic control. So **the whole signal-place gain is the (a/p − ν)₊ piece**, switching off at the kink as the Riesz weight requires.
- *The backward charge pays for something real*: the partner row's own γ-gain, which a backward neighbour at distance 1 destroys. Crediting γν with no backward charge fails at 32,682 of 42,010 points (length 2, by up to 33), and the forward-only bound at 298/390 (length 4). The Lean's accounting (γ per unit minus γ·Wc) holds there and is nearly tight; it is crude (≈ 30×) only at backward distance 3. So booking γ_p·Wc in E is necessary.
- *Controls.* Split primes, the anisotropic direction, the wrong Gaussian, non-CM curves and scrambled jets each give thousands of violations; s₂ = p changes nothing. Validation: 0/248 against a direct double sum, 0/630 against `kernel4_lib`.
- *Limits.* Rank ≤ 2, no frames or HidaSetting, one top, no lattice-wide statement or chains; sizes tiny against a ≈ x·b; e ≥ 5 never active; not the Lean host's curve; the Lean is not executed.

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

**Chowla–Selberg, in classical form** [STEPE §4; NORMS]. It is *proved in-tree* from Kronecker's first limit formula and the class number formula: for unit-discriminant lattices, mean over conjugates of log(area/π) = γ + log(2π/√d) − L′/L(1, χ_{−d}) (`mean_log_area`; the elliptic formula for K, not Colmez's). `two_log_brN` converts √d to rd_E, and d ≡ 3 mod 4 makes (·/d) = χ_{−d}. A reader re-derived sign and constant by hand. NORMS's script (`normcheck_cs.py`) reproduces the identity to 8 decimals for d = 4, 3, and finds 2·log|D^aσ(0)| − [ph(a) − a·logΩ + (a/6)log|Δ|] = 7.4 and 5.4 at a ≈ 6000, i.e. O(log a); with 2Ω the miss is ≈ a·log 2.

**DIV per lift and place** [DIVKEY §2.1; STEPE]. DIV is real-number algebra (`divisor_inequality`, read). For each lift j and place ρ it adds the layer covolume +(p_j − q_j)·w·logΩ (D2), the Fock jet term +Σ_i ph(ν_i) − |ν|·logΩ, and the hook term −logHook from L6's lower bound on λ_j. It substitutes |ν| = a_t[ρ∈TT] + k·w + δ and Σ_i ph(ν) − logHook ≤ ph(a_t)[ρ∈TT] + eE. The k·w·logΩ parts cancel against the covolume, and one ph(a_t) − a_t·logΩ per top per lift remains: the height collapses to Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + O(|TT|·a·La + m·B₀x^ε).

**On the live record both substitutions hold by definition**: δ and eE are *defined* as the remainders. The content is their size bound `stepE_num`, proved and read to the bottom, an elementary Young-diagram inequality. The k-row Fock weight ν and the (k−1)-row hook weight a⁺ interlace (Gelfand–Tsetlin); the hook product is ≥ the product of row factorials; ph(n) ≤ log n!. The a_t row is not in the hook, so ph(a_t) survives exactly, and one w-sized row of ν is unmatched. A Stirling model (one top, a ≫ w ≫ k²) gives eE = w·log a − (k²/2)log(w/k) + O(k²) at a top and ≈ w·log w off it, against the Lean's 2w·La and w·La (an lgamma check agrees). So eE ≈ m·f·b·La in total: **a genuine per-lift loss in the "m" family**, which no averaging over j removes. The top part of the δ bound is slack. The cancelled terms are ≈ k·f·b·x^ε per level, so L6 must be sharp to relative x^{−4}; it rests on an exact Rallis product formula and seven `Published` theorems supplied in-tree [L6 §0].

**Only the Fock jet bound carries the coefficient of a** [NORMS]. a_t appears only in `BlockBound`, proved in the column Fischer metric `pairK` (extremal vector of norm 1), which N_u shares; the hook omits the a_t row and the covolume involves only caps. So m·(ph(a_t) − a_t·logΩ) comes from one proved theorem in one metric. The hook and covolume inputs read the same record fields, built from one layer inner product; the (2πx)^{−|wt|/2} factor is one definition, cancelling in `ExactRatio`; `fockModel` (proved) identifies the Weil norm with the Fischer norm. A c^{weight} mismatch would falsify L6 or D2 by ≈ k·f·b·|log c|, not shift Main. No lemma identifies the three norms; the tie is the shared logΩ symbol and type-shared frames.

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

The joint map ⊕_u B_u : ⊕N_u → RR^∨ satisfies [RANK; WRITEUP (5)]

$$s-\log|W|-(1-\delta_p)^{-1}\big[4u_F\log(1+H_B/u_F)+(\eta+4\sqrt{\bar e})H_B\big]\le\mu(RR^\vee),$$

where s = Σ_u d_u(μ(N_u) − h(u))/Σ_u d_u is the mean source slope net of heights, u_F the Harder–Narasimhan spread, H_B = x^{C_H}·b, and η, ē frame-tightness parameters with (η + 4√ē)·x^{C_H} ≤ 6. The proof is a layer-cake over HN filtrations with a dimension-free frame lemma, with no rank error. The frame yields only *robust near-surjectivity* of the joint map, hence §7. In the ledger the target is written μ(cc).

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

**The tie of Ga to lattices** [GATIE; ADM11]. Ga is *defined*: Ga = Σ_w 2·lw·e_w·(Σ_j gainD_j(w) − τ(w)), with its fields pinned by `ParametersFill` to explicit formulas. So L10 compares two piecewise-linear formulas with the same caps and no floors, and needs no lattice. The content enters through one symbol, sg(u, w) = Σ_j(gainD_j + F_j − E_{u,j}):
- the source lattice is *defined* as N_u = ∏_w 𝔭_w^{−⌊e_w·sg⌋}·NuLat_u (L2), and its slope is exact: μ(N_u) − μ(NuH_u) = Σ_w 2·lwP·⌊e_w·sg⌋ (`nprimeMuR_at`). **The floor inequality** sz(sg) − 2lwP ≤ 2lwP·⌊e·sg⌋ ≤ sz(sg) loses ≤ 2·lwP per place with sg ≠ 0 (over primes ≤ X″, T, g₀, g₁, d, and the primes of DGam), ≤ C·X″ ≪ b in total, once per place, paid by LoU. The direction is right for Bost: N_u is at most the ideal lattice. The divisibility is proved unrounded and needed only floored;
- N_u can be the source of DIV only if Bk_u(N_u) ⊆ cc (`OneMapIntoCC`), which holds because the period of the **actual** chain image of every φ ∈ NuLat_u has valuation ≥ ⌊e_w·sg⌋ (the ledger clause `adm2`, not the kernel law of §4.4). So the inclusion *is* the p-adic divisibility of the actual chain maps;
- the same fields enter Ga, Fo, Ee, N_u and the proved divisibility, so raising Ga would require divisibility at a larger exponent. GATIE found no slack.

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

**The zero-chain alarm is closed on the live path.** `Ties9` is parameter matching only, and `Conclusion1` concerns the actual column maps. The auxiliary local chain enters only through `CmpLite`, which must intertwine with the actual K_j, so NODE-LOSS's `zeroCh` cannot make adm2 vacuous. The producers of ModelsOK/twU are unread.

`exists_data_completion` confirms the content lies in this tie: from ASK ≤ Main + error alone one can build a record satisfying every ledger clause, with Ga := ASK − LoP [LEDGER §0.6].

**The main terms never meet as numbers** [LEDGER §2b]. The archimedean m·ph(a_t) − m·a_t·logΩ becomes Main by the exact algebra of L7, and Main is identified with the explicit-formula MAIN by definition. **DIVKEY verified L7 by hand**: it is exact; the log(π/v) of logΩ cancels Count5's log(v/π), the m·lg terms cancel, and only γ and the L′/L constant survive, so the normalisation of Ω plays no role. The signs agree: Main gets +L′/L from −a·logΩ, MAIN gets +ell(chC), and `Char_at` ties them. Since logΩ is one shared symbol, a sign error in Chowla–Selberg would show as a Main/MAIN mismatch, not in the identity; §5.1's checks exclude it. The m²La/k term (from `Conclusion5`, producer untraced) is negligible. The p-adic sum Σ_p γ_p·a·log p appears nowhere. In paper terms, the uncapped inert count log a! − Σ Λχ_{−d}⌊a/n⌋ has twisted part ≈ −a·L′/L(1, χ_{−d}), the split half that Chowla–Selberg puts into logΩ. So one lift is one Chebyshev identity, with all content in the errors [HEIGHT §2(b); WHYHALF §1.1].

**The cancellations** [ACCOUNT §0.3; LEDGER §2].
- μ(cc) enters Bost and DIV with coefficient +1 and cancels; only an *upper* bound on μ(RR^∨) is used.
- Fo (`foTie`), h(u), the m·lg terms and log(π/v) cancel syntactically.
- The large logΩ terms: Σ_jΣ_ρ(p_j − q_j)·w·logΩ from D2 against −Σ_jΣ_ρ(a_t[ρ∈TT] + k·w + δ)·logΩ from the height leave −m·Σ_t a_t·logΩ plus a residual Σ_j(2j − 1 − m)·Σ_ρ w_{jρ}·logΩ, booked crudely at ≤ 2m²·f·b·La in the per-lift error. **Σ_j(p_j − q_j) = mk is never used** [DIVKEY §2.5]: the record has only |p_j − q_j − k| ≤ m, used once in a triangle inequality. The residual would vanish if w did not depend on j. These terms are ≈ x^{4.5+O(ε)}·U, so covolume and L6 must be right to relative x^{−4}; in the Lean this holds by definition (the same `logOm` symbol).

**Precision-critical inputs** [ACCOUNT §0.3–0.4; LEDGER §2b]: covolume and height to relative **x^{−4}**; Count5 to relative **1/m**; Bessel-frame tightness **η ≤ 6x^{−C_H}**; the real divisibility to E ≤ C·B₀ per lift, relative **x^{−1/2+O(ε)}** (§6.3); and, two-sided, `PairGood` at x and `ThinScales`.

---

## 6. Why 1/2

### 6.1 The error families and the balance

The error ErrX5at splits into families [WHYHALF §1.2; LEDGER §2a]. The **one-off** terms, each ≈ |TT|·a·x^ε, are Count5's precision, DIV's top-place terms, the source floor and the HN spread. The **per-lift** terms, each ≈ B₀ = f·m·b·x^ε **(which contains m)**, are DIV's interior error (eE, covolume error ∝ q_j ≤ m, the logΩ residual, E1, E2, E3) and EComp5, so m·B₀ ∝ m². The **non-vanishing** term is m·Nc, Nc = |T2|·k·b·x^{2ε}/n². Relative to U [LEDGER §2a]:

| term | size | /U | family |
|---|---|---|---|
| ASK, Main | ≈ m·nT·a·x^{ε/3} | ≈ x^{1+4ε/3} | — |
| Fo, μ(N_u), h, Σ lcv, Σ hB | ≈ m·k·f·b·x^{O(ε)} | ≈ x^{4.5+O(ε)}; cancel exactly or to relative x^{−4} | — |
| Count5, DIV boundary, source floor | ≲ nT·a·x^ε each | ≲ x^{1/2+2.07ε} | x/m |
| DIV interior, EComp5 | ≈ n·m²·b·x^{O(ε)} | ≲ x^{1/2+4.07ε} | m |
| DIV's m·Nc·x^{2ε} | m·k·b·x^{4ε}·δ/n | ≲ x^{1/2−1.9ε} | k/n² |
| LoP | C·nT·m·b | ≲ x^ε, i.e. x^{−1/2} of the budget | — |

**The balance.** The Lean replaces this table by L12–L13. Divided by U the bracket is

$$\frac{2a_E(1+m^2/k)}{m\,b\,\delta}+\frac{4nm\,x^{\varepsilon}}{|TT|\,\delta}+\frac{2k\,x^{2\varepsilon}}{n\,|TT|}\ \le\ 8x^{1/2+2\varepsilon}+8x^{1/2+2.625\varepsilon}+4x^{1/2+1.125\varepsilon}\ \lesssim\ x^{O(\varepsilon)}\Big[\frac xm+m+\frac{k}{n^2}\Big],$$

using a_E ≤ 2xb, f = 2n, δ ≥ x^{−ε}, |TT| ≥ x^{−ε/8}n/2 and the window x^{1/2−ε} ≤ m ≤ x^{1/2+ε/2} [LEDGER §2a; WHYHALF §1.3]. So the total error is ≤ 20x^{1/2+2.625ε}·U. With m = 1 the bracket gives G(x) ≲ x^{1+O(ε)}, **no better than the trivial bound**: Mertens already gives G = O(x) unconditionally. The one-off errors then swamp the main-term identity, as in Stepanov at ℓ = 1 *(DIVKEY's inference; the tree requires m ≥ x^{1/2−ε} and m ≥ 2)*.

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
- **The real divisibility: relative x^{−1/2+O(ε)}.** Its losses are booked in E. adm11, proved on the live path down to eight bounds, says per word u and lift j: Σ_w sz(E) = ΣA·log(g₀g₁) ± C·B₀ (the m·ΣA·lg that cancels Count5), and the part away from g₀, g₁ is ≤ C·B₀ [ADM11 §2a]. Split primes and p > X″ carry only v_p(DGam), with Σ_p log p·v_p(DGam) ≤ log DGam ≈ x^{404}. Where each loss is booked:

| loss of the real divisibility | Lean bound per lift (`sum_eatI` etc.) | real size |
|---|---|---|
| kindA orbit term | 18·B₀ | ≈ k·f·b′ |
| errF, the backward charge γ_p·Wc (§4.3) | 36·B₀ | ≈ \|TT\|·b·x^{ε/3} |
| c6·Σw/p | 324·B₀, the largest (w ≤ 9b, Mertens up to b) | ≈ 12·f·b·x^{ε/3} |
| deLoss: rank logs and digit sums (§4.7) | 2·B₀ + 21·B₀, via η and X″·η ≤ b | ≈ f·x^{804}·X″·log a ≪ b |
| EatX at IsCs primes | ≤ 21·B₀ | — |
| **signal and inertClass p ≤ X″, total** | **≤ 424·B₀** (doubled for the weight 2 log p) | — |
| inertClass with h = 0 (EatC) | 18(1/ε + 1)·B₀ | — |
| T_u; d; g₀, g₁ | 12·CTu·B₀; 4·B₀; Cg·B₀ through `DegreeCountBound` (unread) | — |
| rounding ⌊e·sg⌋, once per place | ≤ C·X″ (§5.4, booked in LoU, not E) | ≪ b |

`DegreeCountBound` carries the ±C·B₀ precision against the main part ΣA·log g, which is far larger than B₀. It is the one adm11 input whose error is not obviously polynomial against b. The bounds are looser than the real sizes by ≈ m·x^{2ε/3}. Rounding happens once per place, not once per top and lift.

### 6.4 Stepanov, and what is sharp

**Stepanov.** Schematically, ℓN ≤ ℓq + O(q) + O(ℓ²), so ℓ ≈ √q. Here the points are the signal primes at scale x, the vanishing order ℓ is m, the auxiliary polynomial is the joint Bessel period map on N_u, the degree is the product formula (Bost, height, covolume), the one-off degree is the boundary terms, and the ℓ² overhead is m·B₀ [WHYHALF §2]. Unlike Stepanov, non-vanishing costs only a polynomial relation k ≳ m⁵·f·log b: **the cap on m is the growth of the per-lift error, not non-vanishing** [WHYHALF §2]. Non-vanishing does fix the host: k ≳ m⁵·f and k/n² ≲ m force n ≳ m⁴ ≈ x², which explains n ≈ x^{2+8ε} *(REVIEW-MAIN-ARGUMENT A3)*.

**Sharpness.** G_z = Ω±(x^{1/2}), and G_m(x) ≥ c√x occurs in every window, where the chain must be tight to x^{o(1)} [REVIEW-MAIN-ARGUMENT A4]. So some per-lift loss must truly be ≍ m: a per-lift cost independent of m would prove ψ(x) = x + O(x^δ) for every δ [WHYHALF §0.5 *(inferred)*]. The reading finds candidates. The first is eE, the Fock–hook branching defect ≈ w·log w per (lift, place), a genuine positive loss that no averaging removes [STEPE]. Then come the covolume error ∝ q_j ≤ m, E1 (whose tightness sits in its 12·f·m·b allocation and the J0 term [E1LOOSE]), E2 and EComp5. The layer signatures (k+j−1, m−j) are **not** evidence by themselves. DIV uses only |p_j − q_j − k| ≤ m, never Σ_j(p_j − q_j) = mk. The resulting logΩ residual is m·B₀-sized only if w varies in j by ≈ b, so its place in the "m" family is a booking choice [DIVKEY oddity 2]. Which inequality is tight is not established [WHYHALF §6.7] (§9.5).

**Why not Chebyshev.** Chebyshev lacks multiplicity and computes no main term; here m supplies multiplicity, and the main terms are exact (Legendre/LT divisibility to O(1), exact caps, Chowla–Selberg, flat covolumes, Fock coefficients, the bridge identity) [WHYHALF §3]. Everything is one-sided except the host-selected inputs, where the twists' fluctuation is placed in the choice of (q, d).

---

## 7. Non-vanishing

**Why it is needed.** If the periods B_u vanished, or the joint map fell far short of surjective, Bost would say nothing about the primes. The frame hypothesis excludes this through a rank bound [RANK §0]; it also forces D_all > 0 and some B_u ≠ 0, so the degenerate "stand-in" records cannot be the live one [JOIN §1c]. The frame rests on "Theorem S", which has two halves.

**Near-orthogonality** [PAIRB; COUNTS; THMB; THEOREMS]. The Gram kernel K(u, u′) = (c_uc_{u′})^{−1/2}P_u*P_{u′} has off-diagonal squared Hilbert–Schmidt norm ‖K(u,u′)‖²_HS ≤ (1 + b^{−6})·d_ud_{u′}/D*, the value for random subspaces, and ‖K(u,u) − 1‖²_HS ≲ d_u/Γ. This `TheoremSSelected` is proved only *conditionally* (`theoremS_selected_of_loops`) [RANK §0; PAIRB §1]. It is the author's "relative trace formula" (item 16), done by a **double unfolding of Poincaré series** with no spectral decomposition. The savings come from an exact volume identity with Schur orthogonality, sublattice counting, a character-sum cancellation on a hermitian quadric [COUNTS], the level factor, and Gelfand–Graev multiplicity one. The tight comparison 2^{−k/2}e^{Cm⁵f log b} ≤ b^{−14} is what fixes k ≈ x^{9/2+10ε}.

**The exponentially precise dimension count** [COUNT; SLEAVES; FORMULAGAP; GERMJET]. D_all = dim HH is a limit-multiplicity count for a very regular discrete series of U(k + r_S, r_S + 1)^f in L² of a non-compact quotient:

$$D_{\rm all}\le(1+\eta_1)D^*,\qquad D^*=\text{formal degree}\times\text{covolume},$$

with relative error e^{−rf log r/16}, uniformly in rank; the smallness of δ_p is supplied only conditionally [RANK §0]. R(φ_e) is an exact orthogonal projection onto cusp forms, whose kernel is bounded pointwise region by region. The key input is a **compression formula** for lowest-K-type matrix coefficients of non-holomorphic discrete series, c_λ(z) = ∏_iΔ_i(z)^{−s_i} (leading principal minors), proved via Schmid's first-order system and jet uniqueness (read); it reproduces the known U(1,1) and holomorphic U(2,1) cases and was not found in the literature. The Harish-Chandra gap it needs, ≈ x^{110}, is met with ≈ x^{1300}.

---

## 8. The Galois-theoretic inputs

**Where congruence modules enter.** Only through E2 (§5.2) [WHERECONG]: at Tw, RR is a projection onto a type part Z_j, and the dual index is bounded by Hida's congruence module [CONGMOD §0]. Since Tw has no bound on l, every input below must hold at arbitrarily large l. Z consists of theta lifts whose A-parameter contains a Speh block μ⊠S_t, with Galois representations ρ ⊕ χ₁ ⊕ χ₁ω^{−1} ⊕ … ⊕ χ₁ω^{−(t−1)} [LINKN §0].

**Congruence ≤ Selmer.** The Ribet–Wiles direction, made quantitative by a Fitting-ideal determinant lemma. The key input `NoChiOff` is a Galois-side rank/weight count [GALREP]; the converse-theta content sits in `ConclusionZ` and `D7.Z_tie`, both unread. Purity comes from an in-tree Jacquet–Shalika bound, with no Ramanujan input [ROWCRYS]. The bound (`CongBound_at`) has three blocks and **no local term at l** [BEYONDFL]:
- the ρ-block: Bloch–Kato Selmer of ρ⊗χ₁^{−1};
- the c = 1 block: v_l(h_E);
- the c ≥ 2 blocks: Ш¹(E, ℚ_l/ℤ_l(−i)), i = c − 1.

**No local term at l, beyond Fontaine–Laffaille** [BEYONDFL; TOPCORE; SENLAT; G2A]. Hodge–Tate weights are ≈ b, outside the Fontaine–Laffaille range for l < b [LARGETW]. The local defect (Ribet cut cocycles modulo H¹_f) is proved 0 by `TopCore`, a new integral comparison: for crystalline ρ over unramified K with weights satisfying base-l digit ("position") conditions, an extension cut out by crystalline lattices of the prescribed weights lies in H¹_f. The proof counts Herr cocycles on reduced Wach modules, using `SenLat` (proved in-tree). Primes failing the position conditions are charged ≤ b in total. Readers' hand tests are consistent. Crystallinity comes from `Row0b` by local–global compatibility.

**Killing the ρ-block** [KILLAT; ORDER; LARGETW]. Twisting through a finite tame tower O[(ℤ/l^M)^{2R}] with Chebotarev-chosen auxiliary primes gives the Selmer module a square presentation P; killing the residual Selmer group gives det P a unit coefficient. No weak Leopoldt, no infinite Iwasawa module. There are two passes and no single seed: a pack is chosen at each twist index, at a summable cost 1/l².

**The Ш bound** [VWIN; ONECHARU; RT3; MODU3; PATCH; FINEND]. The bound needed is

$$\sum_l\log l\sum_{0<i<t}\mathrm{len}\,Ш^1(E,\mathbb Q_l/\mathbb Z_l(-i))\le\sqrt b,$$

VWin states it for all twists i < x^{401}; against E2's allowance ≈ x^{2.5}·b it is nearly idle. Crude bounds do not suffice [ONECHARU]. The proof is R = T-type: Ш embeds in first-order deformations of Ψ ⊕ 1 ⊕ Ψ^{−1}, and a graded commutative-algebra inequality bounds its length over automorphic points. The modularity input is residually reducible ordinary automorphy for U(3) (Skinner–Wiles for n = 3, a Chenevier determinant ring, Taylor–Wiles patching at nice primes). At reducible nice points the patching uses a new determinantal local model, requiring g² + e′ ≤ D₀, derived by an unread argument [PATCH §0]. A consequence would be a polynomial bound on plus parts of K_{2k}(O_E), the author's "weakening of Vandiver".

**Galois representations** (`Row0b`) [GALREP] come from descent to unitary groups, an Eichler–Shimura-type construction in odd rank, a stable-range theta lift to odd rank (replacing the parity trick) and base change. The l-adic clauses hold for every CM field, every l and every regular algebraic polarized cuspidal π, with no weight bound, but WD matching only for abelian, N = 0 (or tame) parameters [ROWCRYS]. The proof is by l-adic limits of geometric seeds; its key unread step is `CongUW4`/`wtLacEx_holds`. It is not circular: an import closure of 66,168 files has no self-reference.

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
| Engine core; orbit route at signal primes | N (LP duality read in full) | kernel-law inputs; `lemmaS` |
| Hecke route at inertClass primes | C below `adm2`; `adm2` proved, conditional | ≈ 15 site hypotheses (AdmGLt, MInv, FrameLatMapLt) |
| Composition; tie of Ga to N_u; adm11; floor | C (every branch read) | `DegreeCountBound`, `UsedTuplesBoundByConstant`; ModelsOK producers |
| Seesaw `MIid` | N (live) | the supplier's own hypotheses |
| Heights; DIV algebra; L6 | C (`stepE_num`, Chowla–Selberg read); C to 7 `Published` premises | `covolume_measure_eq_one`, `FlatDegreeSt`; a norm-identifying lemma |
| det ι (SpecDet, MultEq) | C to Rallis-type inputs | `AForm`/`BForm`; Siegel–Weil leaves |
| Layer covolume; E1 | N; N (discriminant budget, mirabolic chain) | `ThmB`; `ThURel`, `ExportTie` |
| Bost/HN frame | C | `slope_inequality_mean`, `FrameLA1` |
| Near-orthogonality; dimension count | N (conditional [RANK]); N | local defect masses; region lemmas |
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

Five holes in the reconstruction (not defects of the proof) named by the first review [REVIEW-MAIN-ARGUMENT A2]:

- **H1. det ι = κ^D·∏_j det θ_j.** *Supplied* by `SpecDet` (read), from partwise similitudes with the same Rallis L-value and equal part dimensions [DETSIG; LIVEPATH; LIVEMULT]. Below it, at statement level: `AForm`/`BForm`, Siegel–Weil in Weil's range [SWRANGE], the SameGrp transports.
- **H2. The seesaw supplier.** *Closed* by a 20-step trace from the root, conditional on its own laws [LIVEPATH].
- **H3. The twisted-place set.** *Restated:* Tw has no cutoff in l, and its cost is a discriminant budget inside E1 [TWSET; INDEXBUDGET].
- **H4. The layer signatures.** *A definition forced by `arithAt`* [DETSIG]; DIV uses only |p_j − q_j − k| ≤ m [DIVKEY].
- **H5** (Ga − ASK ≲ budget) is withdrawn: the Lean uses only Ga ≥ ASK − LoP, and the content sits in the tie of §5.4 [LEDGER §0.5; GATIE].

### 9.4 What rests on statements only

Each item was read at statement level only, or not opened. After round 14 the statement-only items **on the spine** are these [SUMMARY §17]:
- **Kernel-law suppliers** [ENGINE2; ADM2]: the inputs of `normalisedFamily_standardBases_integrality` (`hyp_of_stdBases`, `orbitIdentity_all…`, `standard_series_b_conditions_large_prime`); `lemmaS`, the "one p per bipower" law; the suppliers of AdmGLt, MInv and FrameLatMapLt for `adm2`.
- **Two adm11 inputs** [ADM11]: `DegreeCountBound` and `UsedTuplesBoundByConstant`, which carry the ±C·B₀ precision against ΣA·log g.
- **Covolume** [NORMS; COVOL]: `covolume_measure_eq_one` and the `FlatDegreeSt` chain.
- **L6's seven `Published` inputs** [L6].
- **Classical analytic inputs under host selection** [HOSTSEL]: `twist_one`, `page_across`, `zero_density_box`, the progression-PNT chain.

Off the spine, or upstream of read clauses:
- **Analytic end** [ENDGAME; HOSTSEL]: the TT construction with exact shares (`topsFrame`); `levelData`, `topsChoiceH`, `fieldChi`; `gmA_eq`, `ThinH`'s producer; the existential frame bounds (FrameF, LinkS, LinkIRR).
- **Engine and tie** [ENGINE; ENGINE2; ADM11]: `kform_of_ker` and the `lat_S` leaves; `decomposition_of_hh`, `adm7`, `ExpansionEquality` on the Hecke route; the producers of ModelsOK/twU, pdv and the Adm2InU binders upstream of `TopShape`.
- **Slope side**: Theorem S and `LinkIRR`, proved only conditionally (`theoremS_selected_of_loops`) [RANK]; `AForm`/`BForm`, the Siegel–Weil leaves, `nonFieldT`, `ellipticT`, `localPC_holds`, `SpecX.main` [LIVEMULT]; `ThmB` and point heights [VOLUME]; the producer of `Conclusion5` (Count5's `lowB`).

Now read, so removed: `PairEx`; the four ledger bodies and `stepE_num`; the adm11 producer, the floor and every adm2 branch; `posOK`; `thmAJetA` and the top LP; Chowla–Selberg.
- **E1** [INDEXBUDGET; MIRABOLIC; E1LOOSE]: the suppliers of `ThURel` and `ExportTie` (if ExportTie failed, LeafTW1 would compare unrelated lattices); J0/`ExponentStatement`; `localIdx`, `heights_arith`.
- **E2 and Galois** [WHERECONG; TOPCORE; SENLAT; G2A; ROWCRYS; PATCH]: `PerS.image` (Berger); the mod-l Sen step; `UseLoc.main` and the position-data lemma; Wach-module lemmas; `CongUW4`/`wtLacEx_holds`; the closure theorem and C_cris bodies; `HasAut` and the derivation of g² + e′ ≤ D₀; `ConclusionZ`, `D7.Z_tie`; `IsBCV`'s unramified clause at non-split w | l for l ∈ {q, d, small} (the live TopCore call excludes these l).

### 9.5 Open conceptual questions

1. **Which inequality is tight.** G_z = Ω±(x^{1/2}) forces some per-lift loss to be ≍ m, not merely ≤ m, in every window. The candidates are now eE (genuinely ≈ m·f·b·La), the covolume q-error, E1, E2 and EComp5. The signature residual is a booking choice, not a candidate (§6.4). The reading does not say which is tight, nor why an m-fold Bessel period needs targets with q up to m [WHYHALF §6.7; STEPE; DIVKEY]. WHYHALF calls this the conceptual heart of "why 1/2".
2. **The three DIV norms.** No lemma identifies the definite frame of the Rallis-hook input with the `pairK` Fock frame of the jet bound; the tie is the shared logΩ symbol and type-shared frames. A mismatch would falsify L6 or D2 rather than shift Main [STEPE §3.4; NORMS].
3. **Scale of the numerical evidence.** The checks of §9.6 run far below a ≈ x·b, at rank ≤ 2, with one top.
4. **The seesaw constant.** a_u is existential and depends on the word. Whether the frame needs it uniform, i.e. why near-orthogonality of the P_u transfers to B_u, was not checked [SEESAW oddity 3].
5. **Layer index against lift index.** Nobody showed that the layer index matches the lift index one for one [ARCH §7.7]. The ratio dim Mram/dim Mu0 is not stated, and Mram as "new at T" is inferred [ARCH §7.3, §7.5].
6. **Design choices.** Why exactly 3 in the shares; why orbit length n′ > 2 rather than just even; why t has the shape of §1; whether `BehrendSets` chooses T2 [ENDGAME §2.3; WHYHALF §6.3, §6.6].

Now answered: why b is exponential (§4.7, corrected by ADM11); which route carries the count (the orbit route, §4); whether the backward charge is an artefact (no, §4.8); where the Galois side enters (E2 only, §5.2); whether Σ_j(p_j − q_j) = mk is used (no, §5.4); m = 1 (trivial, §6.1); the zero-chain alarm (closed, §5.4); how (q, d) is chosen (§2.3).

### 9.6 The numerical checks

Three independent checks bear on the spine [SUMMARY §17]. None runs Lean code.

| check | what it tests | what it does not |
|---|---|---|
| **NUMTEST3/4** | p-adic valuations of real jets of the Hecke-route (GIdx-shaped) kernel, orbit lengths 2 and 4, with genuine minors det(Y)^m: caps per position, det^m costing m, the law to O(1) (worst −0.98, −1.54) | the regime cap ≈ a/p; frames; several tops |
| **NUMTEST5** | the capped law Σ_{e odd}(a/p^e − cap)₊ at a signal place across the kink cap ≈ a/p, on rank-one and 2×2-block jets, with the backward charge and five controls (§4.8) | rank > 2, several tops, the lattice-wide statement, chains, real sizes, e ≥ 5, the Lean host's curve |
| **NORMS** | input (a) only: the in-tree Chowla–Selberg constant to 8 decimals (d = 3, 4), and the archimedean size of D^aσ(0) against ph(a) − a·logΩ to O(log a) at a ≈ 6000 | inputs (b) and (c); the higher-rank Fock bound |

The other tests of §4.8 test other objects, arithmetic only, or caps far below the kink.

---

## 10. Correspondence with the author's timeline

**Located.** (2) Dᵃ(Ω·θ)(0) divisible by p^{a/p+a/p³+…−O(log a)}: γ_p·a, §4. (5) the switch to G_z. (8) iterated theta lifts π ↦ π ⊞ μ_j[t], m ≈ √X: §3. (9) cancellation of order-m terms via Chowla–Selberg: the logΩ cancellation of §5.4 *(inferred match)*. (10) divisibility of the m-fold lift: §4.5. (12) seesaw and Rallis: `MIid`, λ_j. (13) Bost. (14) the cost of each lift: §6; "twisting" matches KillAt and §5.2; "division" plausibly DIV *(inferred)*. (15) an integral structure glued across Hecke characters: RR. (16) a relative trace formula with projected Poincaré series: Theorem S, without GL₅. (17) a weakening of Vandiver: the Ш bound. (18) covolumes, theta-series index, congruences: §5.2. (20) GRH: ⟨ψ⟩ with 4 : 3 shares and windowed Landau.

**Partly located.** (1) Stepanov: structural only (§6.4). (7) GGP periods; "m non-interlacing weights" is inferred. (19) `BehrendSets`, not traced to the live path.

**Not located.** (3) the sixfold cover of GL₅ and the Poincaré bundle. (4) W(1_S) ≥ 0 and the bootstrap. (6) W·1_{(0,1]} + X^η·1_{(0,1/X]} ≥ 0. (11) the Iwasawa tower via pigeonhole (candidates: the 2-power layer, KILLAT's tower). (14) the "2/3 a priori" version.

Sources: [WHYHALF; LOCALDIV; ARCH; LINKN; CHAININD; SEESAW; L6; RANK; CONGMOD; PAIRB; VWIN; ONECHARU; THETA].

---

[^n4]: NUMTEST4's phrase "inert in both" describes inertClass primes, not signal primes [SIGNAL; LEDGER §0.4]. NUMTEST3/4's kernels are GIdx-shaped and locally the signal-orbit object (§4.8).

[^tiebm]: The orphaned `TieBm` formulation, in which the middle levels are set to 0, has no consumer, so ARCH's worry about it lapses [SEESAW §0.1].

**Corrections that change the picture** (newer node first; SUMMARY §5–§17 has the full list).
1. The engine that carries the count is the orbit route at signal primes; the Hecke route of ENGINE serves inertClass primes only [ADM2; ENGINE2, correcting the previous §4].
2. The backward charge γ_p·Wc is needed whenever a backward-distance-1 neighbour carries a cap ≈ b [NUMTEST5, correcting ENGINE2 oddity 1 and JETA oddity 2].
3. deLoss closes through η and X″·η ≤ b, and b must beat poly(x)·e^{x^{ε/3}} [ADM11, correcting the former "why b is exponential" remark].
4. δ and eE are definitions on the live record; the content is `stepE_num`. eE is a genuine per-lift loss, and the top part of the δ bound is slack [STEPE, correcting DIVKEY and HEIGHT on the m-independent δ term].
5. Σ_j(p_j − q_j) = mk is never used, and the signature residual is a booking choice, not a source of 1/2 [DIVKEY, confirming LEDGER and correcting §6.4's earlier candidate list]. m = 1 gives no better than the trivial bound [DIVKEY].
6. The twist bound is proved on [Y, X] for one (q, d) per window and consumed at y = x; the averaging is orthogonality, not the large sieve [HOSTSEL].
7. Earlier: the live exponent is 9 [ENDGAME; LEDGER]; the x^{−1} precision is formula against formula, and errF carries log X″ [GATIE]; H5 is not in the Lean [LEDGER]; Tw has no cutoff at X″ [TWSET]; congruences enter only through E2 [MIRABOLIC; WHERECONG]; MULTEQ read a dead route [LIVEPATH]; crystallinity comes via `G2a` [G2A]; purity from Jacquet–Shalika [ROWCRYS].
