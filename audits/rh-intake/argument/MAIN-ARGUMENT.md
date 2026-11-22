# The main argument, reconstructed from the Lean source

> **Status.**
> 1. This document gives a continuous mathematical account of the argument in the alpo.ge Lean tree (SHA-256 `9631b4f0…49c7fc`). The tree claims RH and GRH for Dirichlet L-functions.
> 2. It is a reconstruction by reading. Reader agents each read one piece over thirteen rounds (86 nodes), cited in brackets, e.g. [ENGINE]. Nothing was compiled or run in Lean.
> 3. "Proved" means that a proof term exists in the tree. It does not mean the term was checked, or that its leaves were read.
> 4. Where nodes conflict, the newer node wins; the corrections that change the picture are listed at the end, and SUMMARY §5–§16 records them all. *(inferred)* marks an inference by a node or by the auditors. "Not established by the reading" marks a gap the nodes leave open.
> 5. This document describes the argument. It does not vouch for it. §9 states what has been read, what rests on statements only, and what is still not understood.

> **Notation** [ACCOUNT §1; CHBALANCE §1; SERVED §1]. The Lean reuses letters; this document does not.
>
> | symbol | meaning here |
> |---|---|
> | x; ε; b; a | the scale; the small parameter (never a character; the cyclotomic character is ω); e^{x^ε}; x·b |
> | Y; Y_{qd}; Y_j | Landau window base [Y, Y^{3/2}]; the (q, d)-selection scale in [x^{1/J}, x], log q ≍ Y_{qd}^{ε/5}; row-tower spaces |
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
2. **A host for each scale x.** An abelian CM field E ⊃ K = ℚ(√−d), Gal(E/ℚ) = {±1}² × A, in which ψ(p) is the A/A₀-coordinate of Frob_p. The pair (q, d) is chosen so that the 3o quadratic twists ξ(·/q)^i(·/d)^j, (i, j) ≠ (0, 0), satisfy |g(y)| ≤ y^{1/2+ε/2} on a range of y up to x (`PairGood`, an averaging theorem over a family of quadratic fields, not GRH) [ENDGAME §2.3; PAIRGOOD].
3. **The engine: one lift, one inert prime p.** In height-two Lubin–Tate log coordinates, every jet (top linear forms)^{a_s}·(column minors) of the CM theta kernel θ_{c,c′} has v_p ≥ Σ_{e odd}(a_s/p^e − cap_{s+e})₊ − deLoss, where cap is the number of minors at the partner position s + e. This is proved granted the clause `adm2` (the kernel is exp(−hyperbolic Gaussian) × integral) [ENGINE §1.4; §4.2].
4. **m lifts.** The one-step bound holds on the whole integral lattice of each level, so gains add along the m-fold column map: the actual column map lands in ϖ^{e·totS}·(level-m lattice) (`main_ind`, `chain_ge`, `WJS.Conclusion1`) [ENGINE §4; GATIE §0.3].
5. **The gain is tied to a lattice.** Ga = Σ_w 2·lw·e_w(Σ_j gain_j(w) − τ(w)) is a *defined* piecewise-linear formula. The source lattice is *defined* as N_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋}·NuLat_u, sg = Σ_j(gain + F − E). Step 4 gives Bk_u(N_u) ⊆ cc, i.e. the period map is integral on N_u; this inclusion *is* the p-adic divisibility of the actual chain maps. An exact slope formula gives μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo5 [GATIE; LEDGER L2].
6. **DIV.** μ(cc) + h(u) − Fo ≤ Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + c·|TT|·a·La + c·m(B₀+Nc)x^{2ε}. Here the height (Fock norms, Chowla–Selberg, Rallis hook products) meets the covolume bound μ(RR^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + 2ΣF + LG + Σ_j(E1_j + E2_j) + E3. E1 is the index of the theta image at twisted places (a discriminant budget); E2 the dual index of the type-part projection (congruence module ≤ Selmer + Ш + class number, the only entry of the congruence machinery); E3 = Σ lw·2/ℓ² the cost of twisting. All three are per-lift errors [LEDGER L1, D1–D5; WHERECONG; INDEXBUDGET; MIRABOLIC].
7. **Bost.** s − log|W| − BL ≤ μ(cc), with s the mean slope of the N_u net of heights and BL a rank-free Harder–Narasimhan/frame loss [LEDGER L0; RANK]. Non-vanishing of the joint period map (§7) is what makes it informative.
8. **Slope floors and the level prime.** μ(M_u) ≥ −c·|TT|·a·La(1+m/k); Ee ≤ m(ΣA·lg + cE·B₀), the real divisibility's losses (clause adm11); log T_u ≥ Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − c(La + m²La/k) [LEDGER L3–L5; GATIE §2c].
9. **Key identity.** Σ_t m(ph(a_t) − a_t logΩ) − ΣA·Lam5 + m·ΣA·lg = Main + ΣA·c(La + m²La/k) exactly, where Main = Σ_j Σ_t a_t(log a_t − 1 − γ + L′/L(1, χ_{−d}) − mean_ρ log w_{jρ}). The split half of log a! is the −L′/L(1, χ_{−d}) inside logΩ [LEDGER L7].
10. **Upper bound on the gain.** Steps 5–9 add, with Fo and h cancelling, to Ga ≤ Main + log|W| + (errors) (`Ga_bound5`) [LEDGER L9].
11. **Loss bound, and the main inequality.** ASK − Ga ≤ LoP = C·|TT|·m·b, where ASK = Σ_t Σ_j Σ_n Λ(n)(1 − χ_{−d}(n))(a_t/n − w_{j,partner})₊. This compares two explicit formulas with the same caps; no lattice enters [GATIE §0.2]. With step 10: ASK ≤ Main + ErrX5at, ErrX5at ≤ x^{5ε}·[|TT|·a(1+m²/k) + m(B₀+Nc)] [LEDGER L10–L12].
12. **Bridge.** ASK − MAIN = De exactly (orthogonality on Gal(E/ℚ)). Top and thin partners are discarded by an effective PNT (`ThinScales`). Only *signal* primes (inert in ℚ(√−d), split in ℚ(√−q)) reach thick places, where the summand is a Riesz weight b·(a_t/(bp) − 1)₊ at p ≈ x. Averaging gives U·[G_m(x) − SigA − 4x^{1/2+ε}] ≤ Σ(ASK − Main) + 2|TT|mb/x, U = |TT|·m·b·δ/2, with SigA ≤ 4o·x^{1/2+ε} by step 2 at y = x [LEDGER L13–L15; ENDGAME §2.3].
13. **Core bound.** Dividing by U: G_m(x) ≤ x^{1/2+9ε}, at every x ≥ x₀ of every window [Y, Y^{3/2}] of the family attached to ε; 9 = (2 + 0 + 3) + 3 + 1 (§6.2) [LEDGER §0.2].
14. **Landau on windows, and GRH.** A one-sided bound G ≤ C·y^θ on all y of windows [Y, Y^{1+δ}], Y → ∞, for a positive combination of g_χ, forces L(s, χ) ≠ 0 on Re s > θ for every χ in it. With θ < Re s and ε → 0 separately for each s, L(s, ξ) ≠ 0 for Re s > 1/2 and every ξ ∈ ⟨ψ⟩, ψ and ζ included [ENDGAME §1c, §2.1].

In one line: Landau ⇐ (13) ⇐ bridge (12) ⇐ ASK ≤ Main + Err (11) ⇐ [ASK − Ga ≤ LoP, formula against formula] + [Ga ≤ Main + Err (10) ⇐ Bost (7) + DIV (6) on N_u, legitimate because Bk(N_u) ⊆ cc (4–5) + slope floors (8) + key identity (9)].

**Where 1/2 arises.** Divided by U, the error of step 11 has three families [LEDGER §2a; WHYHALF §1.3]. One-off boundary terms, ≈ |TT|·a·x^ε once per chain, give x/m. Per-lift terms, ≈ B₀ = f·m·b·x^ε at each of m levels, give m. The non-vanishing term gives k/n². At m ≈ x^{1/2} each is x^{1/2+O(ε)}, so 1/2 is the balance of x/m against m. The other square-root input is step 2, a bound on quadratic twists at one point, which removes the split primes without producing cancellation. Steps 3–9 must hold to relative x^{−1/2+O(ε)}; step 11 to relative x^{−1}, but formula against formula (§6.3).

---

## 1. The statement and the strategy

**Target.** Fix a primitive Dirichlet character ψ and the cyclic group ⟨ψ⟩ of order o. Put

$$G_z(y)=\sum_{n\le y}\Lambda(n)\Big(\frac yn-1\Big)-y\log y+(1+\gamma)y,\qquad g_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)\Big(\frac yn-1\Big)+y\,\frac{L'}{L}(1,\chi),$$

$$G_m(y)=G_z(y)+\frac{1}{3o+1}\sum_{\xi\in\langle\psi\rangle,\ \xi\ne1}\operatorname{Re}g_{\xi^*}(y),$$

where ξ* is the primitive character inducing ξ [ENDGAME §1b]. The tree proves L(s, ξ) ≠ 0 for Re s > 1/2 and every ξ ∈ ⟨ψ⟩ from the one-sided bound G_m(x) ≤ x^{1/2+9ε} at every point of a sequence of windows [Y, Y^{3/2}] (§0, step 13). All the RH-strength content sits in one inequality between the count ASK of inert prime powers (§0, step 11) and its main term; the rest is character bookkeeping (§2).

**The idea** [WHYHALF §2]. It is a Stepanov-type argument whose auxiliary object is a vector of periods of high-order Taylor jets of CM theta functions. *p-adically*, at p inert in K the CM curve is supersingular, and a jet of order a is divisible by about p^{Σ_{e odd}(a/p^e − w)₊}; summed with weight 2 log p, the uncapped part is Σ_n Λ(n)(1 − χ_{−d}(n))⌊a/n⌋, the inert part of Chebyshev's log a! = Σ Λ(n)⌊a/n⌋. *Archimedeanly*, the same jet has size a!·Ω^{−a}, and log Ω contains the split part of log a! through −L′/L(1, χ_{−d}). One copy is Chebyshev quality. The gain comes from multiplicity: the jets are chained through m ≈ √x theta lifts, each again an order-a derivative, so the divisibility recurs m times [CHAININD]. The comparison is made for lattices of forms, through Bost's slope inequality, and its relative error ≈ 1/m + m/x is minimised at m ≈ √x (§6).

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

b makes every polynomial loss (≲ x^{800}) negligible; §4.4 says why this matters. t is fixed by the definition r + t = 8fr + 4 + ⌈x^{377}⌉·nWv, nWv ≈ 10rf²k³L²/m [ACCOUNT §1]. The recorded constraints are t ≥ r + 5 (L6), 3m < t (GLOBALCHAIN) and twists i < t below VWin's x^{401} [CONGMOD]. Why the definition has this shape, no node says.

---

## 2. The analytic frame

### 2.1 The windowed Landau lemma

**Statement** (`zeroFree_of_rpow_window`, called with δ = 1/2, C = 1) [ENDGAME §1c]. Let χ_i be finitely many Dirichlet characters with weights a_i > 0, G_F = Σ a_i Re g_{χ_i}, 0 < θ < 1, δ > 0. Suppose that for every Y₀ there is Y ≥ Y₀ with G_F(y) ≤ C·y^θ for *all* y ∈ [Y, Y^{1+δ}]. Then L(s, χ_i) ≠ 0 for every i and every Re s > θ. Off the windows only the trivial |g_χ(y)| ≤ C·y² is used. The conclusion holds for each L-function separately, ζ included.

**Mechanism** [ENDGAME §2.2]. Work in u = log y, g(u) = G_F(e^u), and let Φ be its Laplace transform.
- *Transform.* For χ ≠ 1, ∫₁^∞ g_χ(y)y^{−s−1}dy = −(L′/L(s,χ) − s·L′/L(1,χ))/(s(s−1)), similarly for ζ; the main terms cancel the pole at s = 1 exactly. Φ is meromorphic on Re s > 0 with simple poles at zeros ρ.
- *Non-cancellation by positive weights.* The residue at ρ is S(ρ)·(−1/(ρ(ρ−1))), with S(ρ) = Σ_i (a_i/2)(m(ρ, χ_i) + m(ρ, χ̄_i)) > 0 if any L(ρ, χ_i) = 0. At a real zero β < 1 the residue is real and **positive**: a real zero pushes G up. Positivity of Dirichlet coefficients is never used.
- *Laplace kernel and one-sidedness.* For Re z > 2, a_k(z) = (−1)^kΦ^{(k)}(z)/k! = ∫ g(u)·u^k e^{−zu}/k! du. If g ≤ R on W = [U, (1+δ)U], then |g| + g ≤ 2R there, so |a_k(σ+iγ)| + Re a_k(σ) ≤ 2(σ−θ)^{−k}∫_W R e^{−θu} + (tails), uniformly in γ. The Re a_k(σ) is the price of one-sidedness.
- *Chernoff, and why σ is large.* With k = ⌈(1+δ/2)σU⌉ the Gamma kernel concentrates on W with decay of rate ≍ kδ². Off W only |g| ≤ C₀e^{2u} is known, which inflates the tail by ≈ e^{2k/σ}, so σ ≳ δ^{−2} is needed *(inferred from the constants)*; the Lean takes σ = 336 for δ = 1/2, with tails ≤ C/σ^k.
- *Nearest singularity.* A zero with Re ρ₀ > θ gives a pole at distance d < σ − θ. If the nearest pole is real, its positive residue gives Re a_k(σ) ≳ c/d^{k+1}. Otherwise γ is chosen so that one pole is the *unique* nearest singularity to σ + iγ (poles on one circle could cancel along a subsequence of k), and Cauchy on a pole-free disc bounds the possibly negative Re a_k(σ). Either way the left side grows like d^{−k}, against (σ−θ)^{−k}e^{ηU}.

**Why sparse windows suffice.** The singularities and radii depend only on σ and the zero set, never on U. The contradiction needs only an unbounded set of k, and each window supplies one, k ≈ (1+δ/2)σU, since the k-th kernel lives on it up to C/σ^k = o(d^{−k}). So any sequence of windows with U → ∞ works, provided the log-ratio 1+δ is fixed; in exchange the bound must hold at *every* y of each window. Re s ≥ 1 is Mathlib's non-vanishing. ENDGAME read every body except the routine `iteratedDeriv_laplace` and judged it a correct theorem with a correct proof.

### 2.2 How ψ enters: the host and the shares

Every hermitian space lives over a CM field E, the host, built afresh for each scale x [HOSTS §1(a), §2(c1)]. E is the fixed field, inside ℚ(ζ_{QS·q·d}), of the kernel {a ≡ ±1 mod 2^{e₂+2}, ψ(a) = 1, (a/q) = (a/d) = 1} of the Artin map [ENDGAME §2.3]. So ψ factors through Gal(E/ℚ) = {±1}² × A, [E:ℚ] = 4n. A₀ = ⟨a₀⟩ embeds in the 2-power quotient, |A/A₀| = o, and every frame character trivial on A₀ is ξ·(·/q)^i(·/d)^j with ξ ∈ ⟨ψ⟩. **ψ(p) is read off as the A/A₀-coset of Frob_p.** Each auxiliary object has one job:

- **K = ℚ(√−d)**, d ≡ 7 mod 16 prime: the CM curve behind every theta kernel, supersingular reduction at inert p, the factor (1 − χ_{−d}), and L′/L(1, χ_{−d}) inside Ω [ARCH §1].
- **√−q**, q ≡ 3 mod 8, (−d/q) = 1, separates *signal* primes (inert in K, split in ℚ(√−q)) from *inertClass* primes (inert in both) [LEDGER §0.4]. At a signal prime the hermitian space is split.[^n4]
- **The 2-power layer**, of order 2^{e₂} ≈ x^{2+8ε}: an inertClass prime has a split hermitian form iff h has even order; the anisotropic ones (density ≤ x^{−2}) are dropped [SERVED §0].
- **The level primes g₀, g₁** give the Poincaré series a level and carry depth-zero types forcing residual irreducibility [PAIRB; TWIST; ORDER]. **T_u**, one prime per word u, sets the level of the source forms.

**The shares.** The tops are distributed over A/A₀ by λ(h) = (3 + 1_{A₀}(h))/(3o+1), a probability measure with λ̂(ψ^j) = (3o+1)^{−1} for j ≠ 0: that is the weight in G_m [ENDGAME §2.3; CHBALANCE §2(a)]. The argument needs only λ ≥ 0 and λ̂(ψ^j) > 0. Any α + β·1_{A₀} with α ≥ 0, β > 0 would do; uniform shares would leave only ζ. No reason for the specific 3 was found. ζ has weight 1, so the core bound alone would already give RH.

### 2.3 What is counted, and the bridge

**Which primes.** ASK counts n = p^i with Frob ∉ Φ = Gal(E/K), i.e. p inert in K and i odd, with the cap w at the partner place: as a function of n it is Σ Λ(n)(1 − χ_{−d}(n))(a/n − w)₊ [ENDGAME §2.3; LEDGER §2c]. Split primes are not counted. Of the inert primes, only signal primes have thick partners (w ≈ b, so a/w ≈ x); inertClass partners are top or thin, with Riesz length ≥ X′/2. The thick-class indicator is a combination of the 4o characters (·/d)^α(·/q)^β ψ^j. After averaging, the (α, β) = (0, 0) part is exactly U·G_m(x); the 3o twisted characters make SigA.

The bridge (`ch_balance`, `ch_core`) is a finite-group computation that holds exactly [CHBALANCE §0–2].

**Step 1 (exact identity).** Orthogonality on Gal(E/ℚ) gives ASK − MAIN = De, where

$$\mathrm{MAIN}=a\Big(\log a-1-\gamma+\frac{L'}{L}(1,\chi_{-d})-\operatorname*{mean}_{\rho\in\Phi}\log w(\rho)\Big)$$

and De = |Φ|^{−1} Σ_g Σ_ψ ψ̄(g)·w·G_ψ(a/w) is an expansion over all characters of the Galois group (G_χ is the g_χ of §1). The identity uses

$$\sum_n\Lambda\chi(n)(a/n-w)_+=w\,G_\chi(a/w)-a\,\tfrac{L'}{L}(1,\chi).$$

The identity holds with an *arbitrary* constant in place of L′/L(1, χ) (CHBALANCE oddity 1); the true value is pinned by the host clause `HostAddCharCompatible` [SERVED §0].

**Step 2 (thin and top partners drop).** There the Riesz length is ≥ X′/3, and `ThinScales`, |G_χ(y)| ≤ y·e^{−cx^{ε/8}} for y ≥ X′/3, makes them negligible: de la Vallée Poussin with an in-tree zero-free region, for conductors with log(cond) ≤ 2x^{ε/5}log²x, with real zeros β > 1 − 1/400 excluded by host-selected boxes (`RealBox`) [ENDGAME §2.1; SERVED Part 2]. It is not used in Landau.

**Step 3 (thick partners and averaging).** Only signal primes reach thick partners, so **the x-scale part of ASK, which carries ψ, sits entirely on signal primes** [SIGNAL §0.5; LEDGER §2c]. Averaging over u₀ ∈ A₀ and the tops turns the share measure λ into the weights of G_m.

**Result.** The bridge gives

$$U\cdot\big[G_m(x)-\mathrm{Sig}_A(x)-4x^{1/2+\varepsilon}\big]\ \le\ \sum(\mathrm{ASK}-\mathrm{MAIN})+\frac{2|TT|mb}{x},\qquad U=\tfrac12|TT|\cdot m\cdot b\cdot\delta .$$

Every replacement error in the bridge is ≲ x^ε·log x relative to U, and the budget is U·x^{1/2+O(ε)}. The x^{1/2} comes only from Err/U and from Sig_A [CHBALANCE §2(c)].

**The twists are bounded, not cancelled.** Sig_A collects the 3o twists ξ·(·/q)^i(·/d)^j, (i, j) ≠ (0, 0) [ENDGAME §2.3]. They never enter the function given to Landau. Each is bounded *two-sidedly at the single point y = x*: `bdG` ← `boundedTw` ← `PairGood.bounds`, which gives |g_χ(y)| ≤ y^{1/2+ε/2} and |L′/L(1, χ)| ≤ 4 log y for every such twist and all y ∈ [Y, X]; then Sig_A ≤ 4o·x^{1/2+ε}. Through

$$\sum\Lambda\psi^j(1-\chi_{-d})(x/n-1)=\sum\Lambda\psi^j(x/n-1)-\sum\Lambda\psi^j\chi_{-d}(x/n-1),$$

this bound is exactly what lets a count over inert primes stand in for the sum over all primes. **The split half of the primes is paid for by the choice of (q, d)**, not by a second field and not by several d. So L(s, ψχ_{−d}) never enters Φ, and no zero of it can cancel one of L(s, ψ). G_m involves only ζ and ⟨ψ⟩, so the change of host from one x to the next is invisible to Landau.

`PairEx`, which supplies (q, d), is a closed theorem with no hypotheses (mean square over q, Markov, zero density in a box, Siegel), about short sums y ∈ [Y, Y^A] far below the conductor in a varying family; it is not GRH [PAIRGOOD §0]. ENDGAME did not re-read its body.

### 2.4 The order of quantifiers

[ENDGAME §2.1; LEDGER §0.2]
ψ; then e_D, e_L, ε₁ from `TopG` (live: 2, 0); then s with Re s > 1/2, θ = 1/2 + min(Re s − 1/2, 1/2)/2 < Re s; then ε ∈ (0, ε₁) with 9ε ≤ θ − 1/2; then a family `FamP ε` with windows [Y, Y^{3/2}] for arbitrarily large Y; then, for each scale x, (q, d) at a scale Y_{qd} ∈ [x^{1/J}, x], E, the frame, TT and the lattice data; then the core bound at every x ≥ x₀ of every window; then Landau with δ = 1/2. Nothing is uniform in ε: each s gets its own ε, family and hosts. The glue's quantifier over all real e_D, e_L is harmless, because `ConstsBound` forces e_D, e_L ≥ 0.

---

## 3. The objects

### 3.1 Three towers

All spaces are hermitian over E. They are unimodular at the base, with ranks fixed by k, m (even), t (odd), r = k + m − 1 and N(j) = k + j(t+1) [ARCH §2].

- **Column tower**, X_0 ⊂ X_1 ⊂ … ⊂ X_m, totally definite of rank N(j). Its forms are *algebraic modular forms* (functions on lattice classes in the genus, valued in a weight representation, integral in the Weyl-module lattice). The level-j weight at a top is (a_t, small…, −b_t, −w_1^{×(t+1)}, …, −w_j^{×(t+1)}), so **the same large entry a_t sits at every level** and each lift adds a block at the cap weight w_j [CHAININD §1.1]. The p-adic divisibility lives here.
- **Row tower**, Y_m, …, Y_0, of rank r + jt. Y_m ≅ X_⊥ is the complement of an anisotropic vector in X_m. Y_0 = X_0 ⊕ ⟨z⟩ ⊕ r_S hyperbolic planes, r_S = m/2 − 1, has signature (k + m/2 − 1, m/2) and genuine L² automorphic forms. HH is the discrete-series, level-(g₀g₁) part of L²(U(Y_0)), of dimension D_all; inside it EE, of dimension (1 − δ_p)D_all, carries the target lattice RR.
- **Layers**, W_1, …, W_m, of rank r and signature (k+j−1, m−j), inner forms of U(Y_0) at every finite place. W_m is definite and W_{m/2} has the signature of Y_0. Each is paired with a definite V_j of rank r + t. The layer lattices M_j are integral cusp forms on the Shimura variety of U(W_j). They supply the covolume of RR through a determinant identity (§5.2), and their signatures are a definition forced by a lemma (§9.3).

### 3.2 Maps

- **Column steps** K_j [ARCH §4(a)]. They are given by

  $$K_j\varphi(c')=\sum_{c}|\mathrm{Stab}\,c|^{-1}\rho_j(c)\rho_j'(c')\cdot\mathrm{divDe}\circ\mathrm{unf}_j(c,c')\circ\mathrm{sharp}(\varphi(c)),$$

  where unf_j(c, c′) is **the Taylor jet at 0 of a CM theta function θ_{c,c′} attached to a pair of lattice classes**, ρ_j, ρ′_j are unitary determinant characters, and sharp, divDe are diagonal normalisations. The chain is col = K_{m−1}∘…∘K_0.

  θ_{c,c′} is a reduced theta function in matrix variables, written out in §4.1. The jet is paired against a product of column minors, one per column of the Young diagram of the level-(j+1) weight at each position; the number of minors is the cap of §4.2 [HIGHERRANK §1.2; ENGINE §1.4].
- **Row descent** io_j : Mult(j+1) → Mult(j). It is tied by Petersson adjointness to a genuine theta lift. The composite is ι : (top forms) → EE.
- **Layer lifts** θ_j : (forms on U(V_j)) → (forms on U(W_j)). Each is a λ_j-similitude on Hecke parts, where λ_j is the Rallis θθ* eigenvalue. The descent ι is a κ·∏λ_j-similitude. There is one λ, shared by construction (`LevelLink` is `rfl`) [SEESAW §3].
- **Poincaré series** P_u : C_u → HH over the Bessel subgroup R_u = U(X_0) ⋉ N, C_u the source space at level T_u; P_u* is the Bessel period map [PAIRB §0]. The **Bessel pairing** is B_u : N_u → RR^∨, (B_uφ)(F) = ⟨sEE F, P_uφ⟩ up to a nonzero scalar and unitary changes of basis [WRITEUP S11].

### 3.3 The seesaw

The top period of the m-fold column lift is the codimension-one Gross–Prasad period ∫_{[U(X_⊥)]}(K_{m−1}⋯K_0 φ)|_{U(X_⊥)}·F. The live identity joining it to the bottom is `MIid` [SEESAW §0]:

$$\zeta_{u,t}\cdot\mathrm{Pt}_u(\varphi,F)=a_u\cdot\big\langle \mathrm{sEE}(V\,\Theta_t F),\,P_u(U_u\varphi)\big\rangle_{HH},$$

with V and U_u isometries, a_u ≠ 0, and ζ a unit at twisted tuples. Its live supplier is an honest m-step seesaw done two levels at a time (Bessel → Fourier–Jacobi → Bessel), conditional on its own hypotheses [SEESAW §0.3; LIVEPATH].[^tiebm] It is stated as **transport of linear relations**, so a_u is never computed. B_u is *defined* as the period pulled back along ι, and RR as ι(Λ); hence B_u(N_u) ⊆ RR^∨ is literally integrality of the column period, with no λ_j or a_u entering [SEESAW §4]. a_u is used only in the frame (§7, §9.5).

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

This section is ENGINE's paper proof for one lift at one inert prime p ≥ 5, with what it rests on marked.

### 4.1 The function and the coordinate

**The kernel** [ENGINE §1.1–1.2]. Let Tau ≃ Gal(E/K) be the CM type. The space is VV = ℂ^{Tau×N′×N}, an N′×N matrix variable at each τ, with hermitian form H(z, w) = area(Λ)^{−1}·Σ z_{τij}w̄_{τij} and lattice Λ = δ·Φ_Tau(AA0·Hom(N, N′)), where δ·O_K is the period lattice of the CM curve and AA0 an O_E-ideal. θ_{c,c′} is a reduced theta function for (H, α, Λ), i.e. a section of the line bundle with Riemann form H, namely a **finite Heisenberg sum of torsion translates of one vacuum theta**:

$$\theta_{c,c'}(z)=\sum_{x\in\Lambda/A}\alpha(x)\,U_x\Big[\sum_{y\in\Lambda/B}\widehat{\Phi}(\cdot-x)(y)\,\alpha(y)\,U_y\,\theta_{\rm vac}\Big](z),$$

with Φ the finite Schwartz datum of (c, c′) and A, B half-lattices twisted at the places SS. θ_vac is built from a tensor power of thMM, where tens⁴(thMM) is a product of th0(z) = U_t(σ*)(z)/U_t(σ*)(0), t = ω₀/2, and σ* = σ·e^{−s₂z²/2} is the E₂*-normalised sigma function. The Gaussian is not multiplied in separately: at ∞ it is the automorphy factor in U_x, and p-adically it is the class of ph = −log(σ*(εℓ(T))/T).

**The coordinate** [ENGINE §1.3]. At inert p the CM curve has supersingular reduction, with height-two Honda logarithm ℓ(X) = Σ_j X^{p^{2j}}/p^j over W(F̄_p). The kernel's variables are log coordinates z = ℓ(X), and "integral" means integral in X. Let ϖ^{p²−1} = p. Then λ(T) = ℓ(ϖT)/ϖ has coefficients of valuation (1 + p² + … + p^{2j−2}) − j ≥ 0, so a series integral in X is integral in z/ϖ, and

$$v\big(\partial^n f(0)\big)\ \ge\ v(n!)-\frac{|n|}{p^2-1}\qquad(f\ \text{integral in }X).$$

Since v_p(a!) ≈ Σ_{e≥1} a/p^e and a/(p²−1) = Σ_{e even ≥ 2} a/p^e, what survives is γ_p·a with γ_p = p/(p²−1) = Σ_{e odd} p^{−e}. This is the author's item 2.

### 4.2 The statement

**The jets** [ENGINE §1.4]. Positions s ∈ ℤ/n′ run along the Frobenius orbit, n′ = ord(h). The jet operator at level j is (top linear forms)^{a_s} at the tops times a product of column minors det(Σ_a T_{ia}X_{s,a,I(c)}), paired with θ by P(∂)θ|₀. At position s there is one minor per column of the level-(j+1) weight, so the number of minors is the first-row length ν_{j+1,s,1}. At a top, the ν₁ − ν₂ columns of height one are peeled off as top linear forms. So the cap is ν₂ at a top and ν₁ = λ_{s,1} + w_{j+1}(s) elsewhere; **"cap = number of minors" holds by definition**. That this number is the ledger's w is the identification `LatTied` [PAIRING §0.3].

**Theorem** (`EntryExcessBound`, proved). For every choice of top exponents and minors,

$$v_p(\mathrm{jet})\ \ge\ \sum_{s\in TT}\ \sum_{e\ \mathrm{odd},\ e\notin d\mathrm{Set}(s)}\Big(\frac{a_s}{p^e}-\mathrm{cap}_{s+e}\Big)_+-\mathrm{deLoss},$$

deLoss = Σ_s(r₁·lg a_s + r₀r₁·lg ls_s) + Σ_{s∈TT}(lg a_s)², r₀ = N(j), r₁ = N(j+1), lg = ⌊log_p⌋ + 1; dSet(s) is the set of odd distances from s to another top of opposite parity. Being universal over exponents and minors, it holds on the **whole integral lattice Int_j** (via `adm7`, `ExpansionEquality`, stated). Its shape is exactly the ledger's Σ_{e odd}(a/p^e − w)₊.

### 4.3 The five links

1. **Gaussian class** [ENGINE §2(a)]. *Hypothesis* `adm2`: at a served place the kernel is exp(−Ph)·U, with U integral in X and Ph ≃ Σ_e be(x_e, y_e) a hyperbolic cross Gaussian. Then be ≃ G_ser(c, σc) (`RestBeta`, Dieudonné/Honda). In the rescaled variables x = ϖ·(even positions), y = ϖ·(odd positions), exp(−Σ G_ser) = exp(−(π/p)hh)·V with π = ϖ^{p+1}, V integral and hh = Σ_s u_s Σ_{a,b} S^p_{s,a,b}S_{s+1,a,b}, S_{s,a,b} = Σ_l(−1)^l Z^{p^{2l}}_{s−2l,a,b} (`RestGc`). Dwork gives v(π^k/k!) ≥ 0. So θ ∈ O[[Z]][hh/p]: **after rescaling, the only non-integrality is a polynomial in hh/p, each power costing one p.** The arithmetic leaves were read by LEAVES. Their input `posOK`, that positions are Frobenius twists r_v·Frob^s, was opened by no one.
2. **Self-Gaussians cancel** [ENGINE §2(c)]. Frobenius rotates positions by one. With n′ even this swaps the even and odd positions, the two isotropic halves of the split hermitian space: isotropy (`iso_fK`) and duality (`dual_fK`). `hyperbolic_plane_split` then gives Σ_i ph(Σ f t + Σ f′t′) = Σ_e cob(t_e, t′_e), so only the cross-pairing remains. This is the only use of "split at p". With n′ odd the self-terms survive and the gain falls to a/(p²−1). NUMTEST3's AA^σ + CC^σ = 0 is the case n′ = 2: one function saturates the archimedean bound and carries the full p-adic gain, because the form is definite at ∞ and hyperbolic at p.
3. **Cap lemma** [ENGINE §2(d)]. Multiplying by a linear form is adjoint to a Hasse derivative of the operator polynomial. Shifting a minor's columns in one direction is a rank-one update, so a minor absorbs at most one derivative per direction. Hence level-e factors from top s number at most cap_{s+e}. The Lean caps per (s, e), not per partner, which is conservative.
4. **Legendre and Dwork** [ENGINE §2(e)]. Each piece of hh costs one p, and the pairing contributes factorials. With v_p(m!) ≥ m/(p−1) − lg m and 1/(p−1) = γ_p + 1/(p²−1), the top variables keep γ_p·a, and **the minor variables pay their own rescaling out of their own factorials**.
5. **Odd e and the positive part** [ENGINE §2(f)]. S_s has degrees p^{2l}, so the pieces of hh have top degree p^{2l+1}: only odd levels occur. Legendre supplies all e ≥ 1, the height-two radius eats exactly the even e, and each odd-level factor uses p^e top derivatives and costs one p. With max(A − w, 0) + min(A, w) = A this gives Σ_{e odd}(a/p^e − cap)₊. At split p the height is one and the gain is 0. The factor 2 in Λ(n)(1 − χ_{−d}(n)) is on the ledger side (Σ_{w|p} 2·lw·e_w = 2 log p) [WRITEUP S7].

### 4.4 The fixed loss, and why b is exponential

deLoss is polynomial in the ranks and logarithmic in a: r₀r₁ ≈ x^{798}, so deLoss ≈ n′·x^{798+ε} per prime per lift, x^{O(1)} in total [ENGINE §5]. This is far above the loss of 1–1.5 seen numerically (§4.7); the bound is valid but loose in its constant. *(Inference by the auditors, not stated in the Lean:)* this size is why b must be superpolynomial. The losses summed over π(X″) primes and m lifts are ≈ X″·x^{O(1)} (with the other polynomial losses booked in E, §6.3), and they are negligible only because b = e^{x^ε} dominates every power of x.

### 4.5 Composition over the m lifts

The iteration is an honest induction (`main_ind`, read) [ENGINE §4; CHAININD §0]. After j steps the image is ϖ^{(gains so far)}·G′ with G′ an *arbitrary* element of Int_j, and the one-step bound `ZL_bound` holds for every element of Int_j, so gains add. The top weight a_s is the same at every level, while the caps grow with j. Hence

$$\sum_{j=1}^m\mathrm{gain}_j\ \ge\ \sum_{j=1}^{m}\sum_{s\in TT}\sum_{e\ \mathrm{odd}}\Big(\frac{a_s}{p^{e}}-\mathrm{cap}_{j,s+e}\Big)_+-\sum_j(\mathrm{deLoss}_j+dG_j),$$

with dG_j the automorphism denominators v_p(#Stab) (≈ x^{402} in total, ≪ b). "Multiplicity" means exactly this: the same primes divide each of the m lifts to order a. A normalisation error in one step would be multiplied by m, and nothing in the induction would catch it [CHAININD §0.5]. Level-0 Hecke operators can be pushed up the chain by a Rallis-type commutation (the Hecke route, §4.6). The orbit route's `chain_ge` has the same shape, and its lattice tie `KerEnt.lat_S` is an equality [ORBIT]. The intermediate lattices cost nothing: each intermediate Fock metric occurs once as target and once as source, and Bost is applied only to the composite *(inferred from HEIGHT §1(b))*.

### 4.6 Which primes each route serves

ASK counts every inert prime, so the gain side must either deliver divisibility at a prime or charge that prime its whole ASK summand [CHBALANCE oddity 2]. The splitting types are now settled [LEDGER §0.4, §2c; SERVED §0; GATIE §2b U11]:

| class | splitting | partners; ASK summand per (t, j) | route |
|---|---|---|---|
| **signal** | inert in ℚ(√−d), split in ℚ(√−q); hermitian space split | thick iff t + i·h − u₀ ∈ T2: 2 log p·b·(a_t/(bp) − 1)₊, **the Riesz weight at p ≈ x, carrying ψ**; otherwise ≈ 2 log p·a_t/p | **orbit route**, p ≤ X″ |
| **inertClass** | inert in both; hermitian space split iff ord h even | top or thin, never thick: ≈ 2 log p·Σ_{i odd} a_t/p^i, uncapped; no ψ, and removed from the bridge by ThinScales | Hecke/colength route for even order, p < X′; orbit route for even order in [X′(1+Crρ), X″] |
| **split** | split in ℚ(√−d) | not in ASK; only through L′/L(1, χ_{−d}) in MAIN and the twisted terms of De, bounded at y = x | no local gain |

- **Orbit route** [SIGNAL; ORBIT; JETA]. `NoOperatorOrbitBound` bounds the m-fold chain on global kernel entries, with no Hecke operators and no colength (τ = 0). Its local theorem `split_bound_eleven_one` repeats §4.2–4.3 as an LP-duality valuation bound (0/4000 random violations). At signal places the gain is g₀ = Σ_{e odd}(a_t/p^e − capU)₊ − dl with capU the thick weight, so **the Riesz term is reproduced symbol for symbol**, up to shifts totalling X″·poly(x) ≪ b [GATIE §2c].
- **Hecke/colength route** [LOCALDIV; PAIRING; COLENGTH]. The commutation of §4.5 unlocks γ_p·a at even-position tops at a price p^{−Pr} per step; the colength τ removes the surplus, and a pairing of tops (`kinkHH`) leaves the summand ± O(1).
- **Dropped primes** (small-order classes, the band around X′, the second kind, p > X″, p = d) are charged their whole ASK with gain 0, each bucket ≤ x^{−1+O(ε)}·U. SERVED books the bad orbits of served primes in three inconsistent ways, each within the budget [SERVED §1–2].

### 4.7 Numerics, and which object they tested

[ENGINE §3; NUMTEST–NUMTEST4; SIGNAL §E; JETA]

| test | object | the Lean's object? | result |
|---|---|---|---|
| NUMTEST, σ | D^aσ(0), one variable | no: one σ* keeps its self-Gaussian | slope 1/(p²−1), as link 2 predicts |
| NUMTEST addendum, ℘ | Laurent coefficients of ℘ | the Gaussian-free w = 0 case | slope γ_p to three decimals up to order 6000 |
| NUMTEST2 | σ(z+w)/(σ(z)σ(w)) | no: a non-hyperbolic two-variable quotient | slope γ_p, cap only at e = 1; the Lean's bound is weaker there |
| NUMTEST3 | th0(z₀+z₁)·th0(c(z₀−z₁)), cc^σ = −1, n′ = 2, one entry | **yes** | above the proved bound; worst −0.98 against γa − Σmin, a digit sum |
| NUMTEST4 | n′ = 4 kernel with det(Y)^m blocks | **yes**, genuine minors | caps per position; det^m costs m; worst −1.54; 0/800 brute-force mismatches |
| SIGNAL two tops | n′ = 4, two tops, 57 jets | yes, at a signal place | worst −1.13 |
| controls | split, anisotropic, scrambled | — | gain collapses |

The nodes disagree about the prime class of NUMTEST3/4: SERVED §2, repeated by ENGINE, says inertClass only; SIGNAL says NUMTEST3's instance was a signal place. The two-tops check is at a signal place in either reading. The coupled-overhang case was not tested.

---

## 5. The archimedean side and the slope inequality

### 5.1 Heights

**The bound.** The archimedean height of B_u is bounded by submultiplicativity along the chain [HEIGHT §0]:

$$\mathrm{htMap}(B_u)\le\sum_j\log\|K_j\|^2+\log\|P_tL\|^2-\log\kappa-\sum_j\log\lambda_j .$$

**The jet-step norm.** A Cauchy estimate in Fock space for Taylor jets of entire functions with Gaussian growth gives

$$\log\|K_j\|^2\le\sum_\rho\big(\mathrm{ph}(\nu_{j\rho})-|\nu_{j\rho}|\log\Omega_\rho\big),\qquad \mathrm{ph}(y)=y\log y-y .$$

The conjugate periods Ω_ρ genuinely differ, since they come from different ideal classes. Only their mean enters, and the averaged Chowla–Selberg identity proved in-tree gives

$$\operatorname*{mean}_\rho\log\Omega_\rho=\log\Omega=\gamma+\log(\pi/v)-\frac{L'}{L}(1,\chi_{-d})$$

(sign as in the notation box). This is where the split part of log a! goes (§5.4) [WHYHALF §3.3]. The bound has no slack in the coefficients of ph or logΩ; NUMTEST3 found it saturated to within 5.3 in log.

**Why only m·ph(a_t) survives.** The height contains ph(ν) for *all* weight entries, not only a_t. The theta scalars remove the rest: −log λ_j sits in the height, L6 bounds log λ_j below by a hook product, and `weight_height_sum_le` gives Σ_i ph(ν_{jρi}) − logHook_{jρ} ≤ ph(a_t)·[ρ ∈ TT] + eE. So one ph(a_t) per top and level survives. With `weight_sum_eq` (Σ_i ν_{jρi} = a_t[ρ ∈ TT] + k·w + δ_{jρ}) the height collapses to Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T_u] + O(|TT|·a·La + m·B₀x^ε) [HEIGHT §1(a), §2(b)]. The cancelled terms are ≈ k·f·b·x^ε per level, so L6 must be sharp to relative x^{−4}. λ_j is the Rallis inner-product eigenvalue, from an exact product formula with the L-value taken deep in the convergent range, where |L^S| ≥ e^{−2rf} is elementary; it rests on seven `Published` theorems, each supplied in-tree [L6 §0].

### 5.2 The target lattice and its covolume

RR is one global lattice in K^D, glued place by place: at y it is ι(μ(y)) applied to the projection of the integral lattice onto the type-μ(y) part, with {μ ≠ μ₀} finite (author's item 15) [CONGMOD §2a; MIRABOLIC]. The covolume bound (`BoundsMu`, D1 of §5.4) is

$$\mu(RR^\vee)\le\operatorname{meanLog}\kappa+\sum_j\frac{\mathrm{lcv}(M_j)}{D}+2\sum_j\sum_{y\in Tw}lw\cdot F+LG+\sum_j(E1_j+E2_j)+E3 .$$

It uses det ι = κ^D·∏_j det θ_j. On the live route this comes from the proved linear-algebra lemma `SpecDet`: ι is a (κ·∏_jλ_{j,p})-similitude and θ_j a λ_{j,p}-similitude on matching Hecke parts p, and matching parts have equal dimension. The reason is not a factorisation of ι through the θ_j: both sides carry the same Rallis L-value on each part [DETSIG; LIVEPATH; §9.3]. The twisted set Tw is *defined* as the places where the untwisted index, the dual index or F is nonzero; it is finite, with no bound on the residue characteristic, and the index off Tw is 0 by definition [TWSET; LARGETW]. The terms, with their suppliers [WHERECONG; INDEXBUDGET; MIRABOLIC; E1LOOSE]:

| term | supplied by | congruence/Galois input |
|---|---|---|
| lcv(M_j)/D | Hilbert–Samuel and flat sections (below) | none |
| 2ΣF | layer derivative content; cancels against Fo (`foTie`) | none |
| LG | valuation of a Gram determinant | none |
| **E1**: index of the theta image at Tw | a test lattice of products of short forms, whose index is bounded at every place by a discriminant and the product formula (total ≈ m·B₀, tight); it lies in the theta image by a finite-mirabolic chain and Hecke Euler-factor determinants (`ThURel`, `IdxAt`). Integral surjectivity of theta is never proved: congruences are paid for by the budget | none from the congruence chain; the J0 term uses `CuspUAlt`, base change, Bhatt–Scholze, Chebotarev |
| **E2**: dual index of the type-part projection at Tw | Hida congruence module ≤ Selmer + Ш + v_l(h_E), with no local term at l (`CongBound_at`, `TopCore`) | **all of it**: `KillAt`, `LinkN`, `VWin`, `OneCharU`, `AutEnd3Alt`, `Row0b`, residual irreducibility (§8) |
| **E3** = Σ lw·2/ℓ² | the cost of twisting, ≤ 2/ℓ² per place in the mirabolic chain | none (elementary) |

E2 also sits in the base-to-column constant and in DIV's error, and nowhere else [WHERECONG]. The fields carrying E1 are typed with a Galois-side premise that the proof discards, so there is no circularity [E1LOOSE]. All three sit in DIV's error ce·m·x^ε(B₀+Nc), the per-lift "m" family.

**The layer covolume** is [COVOL; VOLUME; HS]

$$\frac{\mathrm{lcv}(M_j)}{D}\le(p_j-q_j)\sum_\rho w_{j\rho}\log\Omega+C\cdot B_0\log\log x,\qquad p_j-q_j=k+2j-1-m .$$

It is proved by descending induction over layers with an effective arithmetic Hilbert–Samuel bound and `FlatDegree`: flat sections on U(p, q) have arithmetic degree (p − q)/2·logΩ + q(…), Chowla–Selberg again. **The flat directions are exact; the error is ∝ q ≤ m** [VOLUME §0.1, §0.5]. The index at the gain primes is bounded by derivative content in the *layer* weights only, F = (k−1)Σw/(p²−1), which enters once on each side and cancels; the a-sized factorial is counted only in the column steps [JOIN §2d].

### 5.3 Bost's inequality, rank-free

The joint map ⊕_u B_u : ⊕N_u → RR^∨ satisfies [RANK; WRITEUP (5)]

$$s-\log|W|-(1-\delta_p)^{-1}\big[4u_F\log(1+H_B/u_F)+(\eta+4\sqrt{\bar e})H_B\big]\le\mu(RR^\vee),$$

where s = Σ_u d_u(μ(N_u) − h(u))/Σ_u d_u is the mean source slope net of heights, u_F the Harder–Narasimhan spread, H_B = x^{C_H}·b, and η, ē frame-tightness parameters with (η + 4√ē)·x^{C_H} ≤ 6. The proof is a layer-cake over HN filtrations with Bost's slope inequality and a dimension-free frame lemma; no rank or degree error appears. The frame carries no metric content and yields only *robust near-surjectivity* of the joint period map, which is why non-vanishing (§7) is needed. In the ledger (§5.4) the target is written μ(cc).

### 5.4 The ledger

The final inequality is fifteen displayed lines, each a Lean statement, combined by proved linear arithmetic (`linarith`/`linear_combination`); no term has the wrong sign or is missing [LEDGER §0–2]. Condensed to what composes, for a fixed x, family member and unit u₀ ∈ A₀, with ΣA = Σ_t a_t, nT = |TT|, ph(y) = y log y − y, logΩ = γ + log(π/v) − L′/L(1, χ_{−d}), s = wmean_u(μ(N_u) − h(u)):

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

**The tie of Ga to lattices** [GATIE]. Ga is *defined*: Ga = Σ_w 2·lw·e_w·(Σ_j gainD_j(w) − τ(w)), with the fields gain, τ, io pinned by `ParametersFill` to explicit formulas at signal and inertClass places and forced to 0 elsewhere. So L10 compares two piecewise-linear formulas with the same caps and no floors; it needs no lattice, and its live producer (`losses_of_small_share_weight`) is arithmetic. The content enters on the other side, through one symbol, sg(u, w) = Σ_j(gainD_j + F_j − E_{u,j}):
- the source lattice is *defined* as N_u = ∏_w 𝔭_w^{−⌊e_w·sg⌋}·NuLat_u (`NprimeDef`), and its slope is computed exactly (`mu_eq`), which is L2;
- N_u can be the source of the DIV map only if Bk_u(N_u) ⊆ cc (`OneMapIntoCC`), which holds because the period of the **actual** chain image of every φ ∈ NuLat_u has valuation ≥ ⌊e_w·sg⌋ (`adm2` ← `admissible_level_two` ← `WJS.Conclusion1`, the column-map bound of §4.5 at the exponent totS ≥ sg + vDG). So the inclusion Bk(N_u) ⊆ cc *is* the p-adic divisibility of the actual chain maps;
- the same fields enter Ga, Fo, Ee, the exponent of N_u and the proved divisibility. Raising Ga would raise sg and require the divisibility at the larger exponent. GATIE found no slack.

`exists_data_completion` confirms that this tie is where the content lies: from ASK ≤ Main + error alone one can build a record satisfying every clause of the ledger, by taking Ga := ASK − LoP [LEDGER §0.6].

**The main terms never meet as numbers** [LEDGER §2b]. The archimedean m·ph(a_t) − m·a_t·logΩ becomes Main by the exact algebra of L7: the log(π/v) inside logΩ cancels the log(v/π) of Count5, and the m·lg of EComp5 cancels that of Count5. Main is identified with the explicit-formula MAIN by definition, and the two L′/L(1, ·) constants are tied by `Char_at`. The p-adic sum Σ_p γ_p·a·log p appears nowhere. In paper terms, the uncapped inert count log a! − Σ Λχ_{−d}⌊a/n⌋ has twisted part ≈ −a·L′/L(1, χ_{−d}), the split half that Chowla–Selberg puts into logΩ. So one lift is one Chebyshev identity, with all content in the errors [HEIGHT §2(b); WHYHALF §1.1].

**The cancellations** [ACCOUNT §0.3; LEDGER §2].
- μ(cc) enters Bost and DIV with coefficient +1 and cancels; only an *upper* bound on μ(RR^∨) is used.
- Fo (`foTie`), h(u), the m·lg terms and log(π/v) cancel syntactically.
- The large logΩ terms: Σ_jΣ_ρ(p_j − q_j)·w·logΩ from D2 against −Σ_jΣ_ρ(a_t[ρ∈TT] + k·w + δ)·logΩ from the height leave −m·Σ_t a_t·logΩ plus a residual ≤ 2m²·f·b·La (from |p_j − q_j − k| ≤ m, w ≤ 2b), inside the per-lift error. So the exact sum Σ_j(p_j − q_j) = mk is not used *(LEDGER's reading; `divIneqRecord` not re-read)*. These terms are ≈ x^{4.5+O(ε)}·U, so covolume and L6 must be right to relative x^{−4}; in the Lean this holds by definition (the same `logOm` symbol).

**Precision-critical inputs** [ACCOUNT §0.3–0.4; LEDGER §2b].
1. Covolume main term and height (through the L6 hook bound): relative **x^{−4}**.
2. Count5: log T_u to ±La, relative **1/m** (a prime in a window of relative width 1/(fk)).
3. Bessel-frame tightness: **η ≤ 6x^{−C_H}**, with x^{C_H}b at least the HN spread.
4. The real divisibility: to E ≤ C·B₀ per lift (adm11), relative **x^{−1/2+O(ε)}** (§6.3).
5. Two-sided, from host selection: `PairGood`/`bdG` at the point x, and `ThinScales`.

---

## 6. Why 1/2

### 6.1 The error families and the balance

The error ErrX5at splits into families [WHYHALF §1.2; LEDGER §2a]. The **one-off** terms, each ≈ |TT|·a·x^ε, one whole copy of the per-lift signal, are Count5's precision, DIV's top-place terms (m-independent because b′ = a/X′), the source floor and the HN spread. The **per-lift** terms, each ≈ B₀ = f·m·b·x^ε **(which contains m)**, are DIV's interior error (covolume error ∝ q_j ≤ m, the logΩ residual, E1, E2, E3) and EComp5, so m·B₀ ∝ m². The **non-vanishing** term is m·Nc, Nc = |T2|·k·b·x^{2ε}/n². Relative to U [LEDGER §2a]:

| term | size | /U | family |
|---|---|---|---|
| ASK, Main | ≈ m·nT·a·x^{ε/3} | ≈ x^{1+4ε/3} | — |
| Fo, μ(N_u), h, Σ lcv, Σ hB | ≈ m·k·f·b·x^{O(ε)} | ≈ x^{4.5+O(ε)}; cancel exactly or to relative x^{−4} | — |
| Count5, DIV boundary, source floor | ≲ nT·a·x^ε each | ≲ x^{1/2+2.07ε} | x/m |
| DIV interior, EComp5 | ≈ n·m²·b·x^{O(ε)} | ≲ x^{1/2+4.07ε} | m |
| DIV's m·Nc·x^{2ε} | m·k·b·x^{4ε}·δ/n | ≲ x^{1/2−1.9ε} | k/n² |
| Bost HN term | (1+cHH)x^ε × the three families | x^{1/2+O(ε)} | — |
| frame term (η̄+4√ē)x^{cHH}b | ≤ 6b | ≤ 24x^{−5/2} | — |
| LoP | C·nT·m·b | ≲ x^ε, i.e. x^{−1/2} of the budget | — |

**The balance.** The Lean replaces this table by L12–L13. Divided by U the bracket is

$$\frac{2a_E(1+m^2/k)}{m\,b\,\delta}+\frac{4nm\,x^{\varepsilon}}{|TT|\,\delta}+\frac{2k\,x^{2\varepsilon}}{n\,|TT|}\ \le\ 8x^{1/2+2\varepsilon}+8x^{1/2+2.625\varepsilon}+4x^{1/2+1.125\varepsilon}\ \lesssim\ x^{O(\varepsilon)}\Big[\frac xm+m+\frac{k}{n^2}\Big],$$

using a_E ≤ 2xb, f = 2n, δ ≥ x^{−ε}, |TT| ≥ x^{−ε/8}n/2 and the window x^{1/2−ε} ≤ m ≤ x^{1/2+ε/2} [LEDGER §2a; WHYHALF §1.3]. So the total error is ≤ 20x^{1/2+2.625ε}·U. With m = 1 the bracket would give the trivial x^{1+O(ε)}, Chebyshev quality *(inferred; the tree never instantiates m = 1)*.

### 6.2 The exponent 9

On the live path `topDesWin` is called with e_D = 2, e_L = 0 [LEDGER §0.2, §1]. The final exponent is 1/2 + 9ε, with 9 = 5 + 3 + 1:
- **5** = e_D + e_L + 3, from the envelope ErrX5at ≤ x^{(eDiv+eLoss+3)ε}·ErrText;
- **3** from `GrowthSizeBound`, which absorbs 20x^{2.625ε} + o(1) into x^{3ε}; this needs x^{3ε/8} ≥ 26, which is exactly a hypothesis of the record (the window m ≤ x^{1/2+ε/2} is wider than the record's m, and the slack is part of these 3ε);
- **1** to absorb the constant 1 + 4o in front of SigA ≤ 4o·x^{1/2+ε}, using x^ε ≥ 1 + 4o.

The record's parameter inequalities were checked by hand and hold for x ≥ x₀(ε); the existential frame bounds were not [LEDGER oddity 2].

### 6.3 Two precisions, and where each loss is booked

[GATIE §0.5, §2c; LEDGER §2b]
- **Archimedean side: relative x^{−1/2+O(ε)}.** Main/U ≈ x^{1+4ε/3} against ErrX5at/U ≲ x^{1/2+O(ε)}. This is what DIV, Count5 and Bost deliver, on lattices.
- **Gain formula against count formula: relative x^{−1}.** LoP = C·|TT|·m·b is ≈ x^{−1−ε/3} of ASK, but it is demanded only of two formulas that agree by construction (same caps, no floors). Its O(b) per (top, lift) pays the top offset: Σ_{p<X′} 2 log p·b′/x ≈ 2b.
- **The real divisibility: relative x^{−1/2+O(ε)}.** Its losses relative to the gain formula are booked in E, and adm11 bounds them by C·B₀ per lift, the "m" family:

| loss of the real divisibility | size | booked in |
|---|---|---|
| integer rounding ⌊e·sg⌋, once per place on the total exponent | ≤ C·X″ ≪ b | LoU |
| Legendre digit sums, rank-logarithms (deLoss, §4.4) | ≈ X″·x^{≈800} per lift ≪ b | E |
| v_p(DGam) | Σ_p log p·v_p(DGam) = poly(x) | E |
| γ_p·Wc loss (errF) at signal primes | ≈ |TT|·m·b·log X″ ≈ x^{ε/3}·LoP in total | E |
| c6·Σw/p; kindA orbit term | ≈ f·b·log X″ per lift; ≈ k·f·b′ ≪ b *(inferred)* | E |

So errF uses only ≈ x^{ε/3}/(m·x^ε) of the allowance m·C·B₀. Rounding happens once per place, not once per top and lift.

### 6.4 Stepanov, and what is sharp

**Stepanov.** Schematically, ℓN ≤ D with D = ℓq + O(q) + O(ℓ²), so N ≤ q + O(q/ℓ) + O(ℓ) and ℓ ≈ √q. The correspondence [WHYHALF §2]:

| Stepanov | here |
|---|---|
| points | served (signal) inert primes, weighted at scale x |
| vanishing order ℓ | m |
| auxiliary polynomial | the joint Bessel period map on N_u |
| degree | the product formula: Bost, height, covolume |
| one-off degree ≈ q | the four boundary terms |
| ℓ² derivative overhead | m·B₀ |

Unlike Stepanov, non-vanishing costs only a polynomial relation k ≳ m⁵·f·log b: **the cap on m is the growth of the per-lift error, not non-vanishing** [WHYHALF §2]. Non-vanishing does fix the host: k ≳ m⁵·f and k/n² ≲ m force n ≳ m⁴ ≈ x², which explains n ≈ x^{2+8ε} *(REVIEW-MAIN-ARGUMENT A3)*.

**Sharpness.** G_z = Ω±(x^{1/2}), and G_m(x) ≥ c√x occurs in every window, where the chain must be tight to x^{o(1)} [REVIEW-MAIN-ARGUMENT A4]. So some per-lift loss must truly be ≍ m: a per-lift cost independent of m would prove ψ(x) = x + O(x^δ) for every δ [WHYHALF §0.5 *(inferred)*]. The reading finds candidates: the layer signatures (k+j−1, m−j), with q_j up to m (a definition forced by `arithAt`, §9.3), and E1, whose tightness sits in its 12·f·m·b allocation and the J0 term [E1LOOSE]. Which inequality is tight, and why an m-fold Bessel period needs targets with q up to m, is not established [WHYHALF §6.7] (§9.5).

**Why not Chebyshev.** Chebyshev's method lacks multiplicity and computes no main term. Here m supplies multiplicity, and the main terms are exact: Legendre/LT divisibility to O(1) per prime, exact caps, the split half via Chowla–Selberg, flat covolumes, the Fock coefficients, the bridge identity [WHYHALF §3]. Everything is one-sided in the direction consumed, except the host-selected inputs (`PairGood` at the point x, ThinScales), which are two-sided: the quadratic twists' fluctuation is not cancelled by the method but placed in the choice of (q, d).

---

## 7. Non-vanishing

**Why it is needed.** If the periods B_u vanished, or the joint map fell far short of surjective, Bost's inequality would say nothing about the primes. The frame hypothesis excludes this: if every B_u = 0, its rank bound contradicts (1 − δ)·|I ⊔ I₁| ≤ |I|, with I the target rows and I₁ the padding rows (HH outside EE), δ tiny [RANK §0]. The frame inputs also force D_all > 0 and some B_u ≠ 0, so the degenerate "stand-in" row records in the tree cannot be the live one [JOIN §1c]. The frame in turn rests on "Theorem S", which has two halves.

**Near-orthogonality** [PAIRB; COUNTS; THMB; THEOREMS]. The Gram kernel K(u, u′) = (c_uc_{u′})^{−1/2}P_u*P_{u′} has off-diagonal squared Hilbert–Schmidt norm ‖K(u,u′)‖²_HS ≤ (1 + b^{−6})·d_ud_{u′}/D*, the value for random subspaces, and ‖K(u,u) − 1‖²_HS ≲ d_u/Γ. This `TheoremSSelected` is proved only *conditionally* (`theoremS_selected_of_loops`) [RANK §0; PAIRB §1]. It is the author's "relative trace formula" (item 16), done by a **double unfolding of Poincaré series** with no spectral decomposition, so the continuous spectrum never appears. The savings come from an exact volume identity and Schur orthogonality (identity orbits), sublattice counting (non-generic terms), a character-sum cancellation on a hermitian quadric (second-type terms [COUNTS]), the level factor (2/g)^{(s−1)kf} (corank s ≥ 2), and Gelfand–Graev multiplicity one. The tight comparison 2^{−k/2}e^{Cm⁵f log b} ≤ b^{−14} is what fixes k ≈ x^{9/2+10ε}.

**The exponentially precise dimension count** [COUNT; SLEAVES; FORMULAGAP; GERMJET]. D_all = dim HH is a limit-multiplicity count for a very regular discrete series of U(k + r_S, r_S + 1)^f in L² of a non-compact quotient:

$$D_{\rm all}\le(1+\eta_1)D^*,\qquad D^*=\text{formal degree}\times\text{covolume},$$

with relative error e^{−rf log r/16}, uniformly in rank. The smallness of δ_p (`LinkIRR`) is also supplied only conditionally, from a row count [RANK §0]. It is not a trace formula over conjugacy classes: R(φ_e) is an exact orthogonal projection onto cusp forms, and its kernel Σ|F_i(x)|² = Σ_γ φ_e(x^{−1}γx) is bounded pointwise region by region. The key input is a **compression formula** for lowest-K-type matrix coefficients of non-holomorphic discrete series, c_λ(z) = ∏_iΔ_i(z)^{−s_i} (Δ_i the leading principal minors). It is proved via Schmid's first-order system and jet uniqueness (`germ_jet_zero`, read), reproduces the known U(1,1) and holomorphic U(2,1) cases, and was not found in the literature. The Harish-Chandra gap it needs, ≈ x^{110}, is met with ≈ x^{1300}.

---

## 8. The Galois-theoretic inputs

**Where congruence modules enter.** Only through E2 (§5.2) [WHERECONG]. At the twisted places Tw, RR is a projection onto a Hecke-eigen type part Z_j ⊂ forms on U(V_j), and the dual index of the projected lattice is bounded by Hida's congruence module [CONGMOD §0], inside DIV's per-lift allowance. Since Tw has no bound on the residue characteristic, every input below must hold at arbitrarily large l.

Z is the space of theta lifts whose A-parameter contains a Speh block μ⊠S_t, t the block length of §3. Their Galois representations are ρ ⊕ χ₁ ⊕ χ₁ω^{−1} ⊕ … ⊕ χ₁ω^{−(t−1)}, with ω the cyclotomic character [LINKN §0; author's item 8: π ↦ π ⊞ μ_j[t]].

**Congruence ≤ Selmer.** This is the Ribet–Wiles direction, made quantitative by a Fitting-ideal determinant lemma. The key input `NoChiOff` (no form outside Z contains χ₁) is a Galois-side rank/weight count [GALREP]; the converse-theta content sits in `ConclusionZ` and `D7.Z_tie`, both unread. Purity inside `ConclusionG6` comes from an in-tree Jacquet–Shalika bound plus half-integral exponents, with no Ramanujan input [ROWCRYS]. The bound (`CongBound_at`) has three blocks and **no local term at l** [BEYONDFL]:
- the ρ-block: Bloch–Kato Selmer of ρ⊗χ₁^{−1};
- the c = 1 block: v_l(h_E);
- the c ≥ 2 blocks: Ш¹(E, ℚ_l/ℤ_l(−i)), i = c − 1.

**No local term at l, beyond Fontaine–Laffaille** [BEYONDFL; TOPCORE; SENLAT; G2A]. Hodge–Tate weights are ≈ b, so for l < b they lie outside the Fontaine–Laffaille range [LARGETW]. The local defect (Ribet cut cocycles at w | l modulo H¹_f) is proved to be 0 by `TopCore`, a new integral comparison for widely spaced weights. For crystalline ρ over unramified K with weights satisfying base-l digit ("position") conditions, an extension cut out by crystalline lattices of the prescribed weights lies in H¹_f. The proof counts Herr cocycles on reduced Wach modules, using `SenLat` (proved in-tree) and the fact that for heights h ≥ l any two lattices lie within X^σ of each other. Primes failing the position conditions form a set Exc charged ≤ b in total. Readers' hand tests (Gee–Liu–Savitt weights over ℚ_{l²}; GL₃ at l = 101) are consistent. The crystallinity it needs comes from `Row0b` by local–global compatibility and Fontaine's criterion.

**Killing the ρ-block** [KILLAT; ORDER; LARGETW]. Twisting through a finite multivariable tame tower O[(ℤ/l^M)^{2R}] with Chebotarev-chosen auxiliary primes; the Selmer module has a square presentation P, the length at ψ is v(ψ(det P)), and killing the residual Selmer group gives det P a unit coefficient. Neither weak Leopoldt nor an infinite Iwasawa module is used. The construction has two passes (untwisted, then twisted under `SameExport`, with the same twisted set), and no single seed: a pack (Q, k′, ψ′) is chosen at each twist index, with pairwise disjoint Q, at a summable cost 1/l².

**Residual irreducibility** at every l comes from the prescribed depth-zero types at g₀, g₁ [TWIST].

**The Ш bound** [VWIN; ONECHARU; RT3; MODU3; PATCH; FINEND]. The bound needed is

$$\sum_l\log l\sum_{0<i<t}\mathrm{len}\,Ш^1(E,\mathbb Q_l/\mathbb Z_l(-i))\le\sqrt b,$$

VWin states it for all twists i < x^{401}; against E2's allowance ≈ x^{2.5}·b it is nearly idle. Crude bounds do not suffice (`LemmaK` gives exp((2kn)^C log disc); Brauer–Siegel controls only h_E; plus parts would need unknown lower bounds for Borel regulators) [ONECHARU]. The proof is R = T-type: Ш embeds in first-order deformations of Ψ ⊕ 1 ⊕ Ψ^{−1}, and a graded commutative-algebra inequality bounds its length by 2Σ v_l(tr ρ(σ) − t) over automorphic points. The modularity input is residually reducible ordinary automorphy for U(3): Skinner–Wiles for n = 3 with a Chenevier determinant ring and Taylor–Wiles patching at nice primes, with an unconditional seed. At reducible nice points the patching uses a new determinantal local model, requiring g² + e′ ≤ D₀, derived by an unread argument [PATCH §0]. A consequence would be a polynomial bound on plus parts of K_{2k}(O_E), the "weakening of Vandiver" of the author's item 17.

**Galois representations** (`Row0b`) [GALREP] come from descent to unitary groups, an Eichler–Shimura-type construction in odd rank (Lefschetz proved in-tree), a stable-range theta lift to odd rank (replacing the eigenvariety parity trick), and Arthur–Clozel base change. Its l-adic clauses hold for every CM field, every l and every regular algebraic polarized cuspidal π, with no weight bound: crystalline with the right HT weights where π_w is spherical, and WD matching only for abelian, N = 0 (or tame) parameters, narrower than the literature [ROWCRYS]. The proof is by l-adic limits of geometric seeds with an in-tree closure theorem; its key unread step is `CongUW4`/`wtLacEx_holds`. It is not circular: an import closure of 66,168 files has no self-reference.

---

## 9. What has and has not been checked

### 9.1 Step by step

"Read to" levels: **C** = down to classical statements; **N** = to a named new idea; **S** = statement or top level only.

| step | read to | main unread items (full list §9.4) |
|---|---|---|
| Windowed Landau, quantifiers | C (correct; every body but `iteratedDeriv_laplace`) | — |
| Bridge, hosts, ThinScales | C (exact identity) | `PairEx` body; TT with exact shares |
| Ledger L0–L15 | C (every combination step proved) | four bodies |
| Engine, one lift one prime | C below `adm2` | `adm2` for the live kernel; `posOK` |
| Composition; tie of Ga to N_u | C | adm11 producer; `Ties9` |
| Orbit route; Hecke route | N (LP duality); C | `split_bound_eleven_one`; `admB2` partly |
| Seesaw `MIid` | N (live) | the supplier's own hypotheses |
| Heights; L6 | C; C to 7 `Published` premises | `normalisedFamily_*` |
| det ι (SpecDet, MultEq) | C to Rallis-type inputs | `AForm`/`BForm`; Siegel–Weil leaves |
| Layer covolume; E1 | N; N (discriminant budget, mirabolic chain) | `ThmB`; `ThURel`, `ExportTie` |
| Bost/HN frame | C | `slope_inequality_mean`, `FrameLA1` |
| Near-orthogonality; dimension count | N (conditional [RANK]); N | local defect masses; region lemmas |
| E2, KillAt, `TopCore` | N (cocycle count read in full; `SenLat` proved) | `PerS.image`; Wach-module lemmas |
| U(3) R = T; Row0b | N; N (l-adic limits) | g² + e′ ≤ D₀; `CongUW4` |

### 9.2 Where the argument exceeds the published literature

1. **Rank-uniform limit multiplicity with exponential precision** [COUNT; FORMULAGAP]: exact cusp-form projection; the compression formula.
2. **Near-orthogonality of Bessel periods to relative b^{−6}** [PAIRB; COUNTS; THMB]: double unfolding; a Gauss-sum cancellation on a hermitian quadric.
3. **p-adic divisibility of high-order jets of higher-rank CM theta kernels** [GAUSSCLASS; ENGINE; JETA]: hyperbolic cancellation of self-Gaussians; the cap lemma. The method is recognisable; the statement was not known to the readers.
4. **Selmer bounds uniform in l for weights up to x^{401}** [ONECHARU; MODU3; PATCH]: Skinner–Wiles for U(3) with a determinantal local model.
5. **Selmer killing at finite level** [KILLAT; LARGETW]: a square presentation over a finite tame tower; twist packs per index.
6. **Residual irreducibility at all l** [TWIST]: depth-zero types at pigeonholed level primes.
7. **Galois representations** [GALREP; ROWCRYS]: a stable-range theta lift replacing the parity trick; crystallinity by l-adic limits.
8. **Uniform covolume bounds on varying Shimura varieties** [VOLUME; HS]: effective finite-level Hilbert–Samuel; `ThmB`.
9. **An integral comparison for widely spaced Hodge–Tate weights** [BEYONDFL; TOPCORE; SENLAT]: `TopCore`, far outside Fontaine–Laffaille.
10. **An index budget for products of short forms** [INDEXBUDGET; E1LOOSE]: jets along a generic intersection, the product formula, Hadamard.

### 9.3 Status of the former holes

The review of the first version named five holes in the reconstruction (not established defects of the proof) [REVIEW-MAIN-ARGUMENT A2]. Their status now:

- **H1. det ι = κ^D·∏_j det θ_j.** *Supplied on the live route* by `SpecDet` (read), from partwise similitudes with the same Rallis L-value on both sides and equal part dimensions (`MultEq`, live producer read) [DETSIG; LIVEPATH; LIVEMULT].
  Below it, at statement level: `AForm`/`BForm`; Siegel–Weil, used only in Weil's range (`Published` Props filled by unread in-tree theorems) [SWRANGE]; the SameGrp transports [E1LOOSE].
- **H2. The seesaw supplier.** *Closed:* a 20-step trace from the root reaches `SeeSaw.mainX_of_lawsX` [LIVEPATH].
  It is conditional on its own laws. A doubling-method pole clause is a literal `True`, and nothing live needs it [LIVEPATH; LIVEMULT].
- **H3. The twisted-place set.** *Restated:* Tw is the support of the untwisted index, with no cutoff in l, and its cost is a discriminant budget inside E1 [TWSET; INDEXBUDGET].
  So the twisted-place inputs must hold at every l; they are read to a mechanism [LARGETW; BEYONDFL; TOPCORE; SENLAT].
- **H4. The layer signatures (k+j−1, m−j).** *A definition forced by the proved lemma `arithAt`* (gap conditions on the twisted Harish-Chandra parameter) [DETSIG].
  DIV uses only |p_j − q_j − k| ≤ m [LEDGER §2]. Why q up to m is needed is §9.5, item 1.

The fifth, H5 (Ga − ASK ≲ budget), is withdrawn. It is not a hypothesis of the Lean, which uses only Ga ≥ ASK − LoP; since Ga is a defined formula with the same caps as ASK, its excess over ASK is arithmetic about two formulas, and the content sits in the tie of §5.4 [LEDGER §0.5; GATIE].

### 9.4 What rests on statements only

The spine items, in the order of §0. Each was read at statement level only, or not opened.
- **Analytic end** [ENDGAME; LEDGER]: the hypotheses of `core_gm` (EAtH ∧ CoreAtH, i.e. `PairGood` and the ledger record) at *every* x of each window, which Landau needs; the body of `PairEx` (not re-read since PAIRGOOD); the TT construction with exact shares (`topsFrame`); `sigA_le`, `gmA_eq`, `ThinH`'s producer.
- **Ledger** [LEDGER]: the bodies of `proposition_size_bound` (GrowthSizeBound), `core_ineq` (the exponent envelope), `divIneqRecord` (the logΩ cancellation is the reader's inference), `windowInequality_of_artinInputs`, `joint_a_ramified_holds`; the existential frame bounds (FrameF, LinkS, LinkIRR).
- **Engine** [ENGINE]: `adm2` for the live kernel (`first_kernel_law_global_small`), the main arithmetic input; `posOK` (positions are Frobenius twists), opened by no node; `decomposition_of_hh`; the generic-frame `reduce`; `adm7`, `ExpansionEquality`, `ZL_bound`; cap = ledger w through `LatTied`; whether the dSet exclusions remove ledger terms.
- **Tie** [GATIE]: the adm11 producer `secondComplement_family_of_inputs`, which certifies all divisibility losses E ≤ C·B₀ at once; `nprimeMuR_at` (floors); the body of `admissible_off_twist_places`; `Ties9` on the Hecke (GIdx) branch of `Conclusion1`, which must tie the LatInst chain to the actual column map; `hServ` upstream of the top.
- **Orbit route** [SIGNAL; ORBIT]: `split_bound_eleven_one`, `orbitIdentity_all…`, `thmAJetA`, `kform_of_ker`, the `latS`/`latT` leaves.
- **Slope side**: Theorem S and `LinkIRR`, proved only conditionally (`theoremS_selected_of_loops`) [RANK]; L6's seven `Published` premises; `AForm`/`BForm`, the Siegel–Weil leaves, `nonFieldT`, `ellipticT`, `localPC_holds`, `SpecX.main` [LIVEMULT]; `ThmB` and point heights [VOLUME].
- **E1** [INDEXBUDGET; MIRABOLIC; E1LOOSE]: the suppliers of `ThURel` and `ExportTie` (if ExportTie failed, LeafTW1 would compare unrelated lattices); J0/`ExponentStatement`; `localIdx`, `heights_arith`.
- **E2 and Galois** [WHERECONG; TOPCORE; SENLAT; G2A; ROWCRYS; PATCH]: `PerS.image` (Berger); the mod-l Sen step; `UseLoc.main` and the position-data lemma; Wach-module lemmas; `CongUW4`/`wtLacEx_holds`; the closure theorem and C_cris bodies; `HasAut` and the derivation of g² + e′ ≤ D₀; `ConclusionZ`, `D7.Z_tie`; `IsBCV`'s unramified clause at non-split w | l for l ∈ {q, d, small} (the live TopCore call excludes these l).

### 9.5 Open conceptual questions

1. **Which inequality is tight.** G_z = Ω±(x^{1/2}) forces some per-lift loss to be ≍ m, not merely ≤ m, in every window. Candidates are the layer signatures and E1's allocation (§6.4), but the reading does not say which one is tight, nor why an m-fold Bessel period needs targets with q up to m [WHYHALF §6.7; E1LOOSE]. WHYHALF calls this the conceptual heart of "why 1/2".
2. **The seesaw constant.** a_u is existential and depends on the word. Whether the frame needs it uniform, i.e. why near-orthogonality of the P_u transfers to B_u, was not checked [SEESAW oddity 3].
3. **Layer index against lift index.** Nobody showed that the layer index matches the lift index one for one [ARCH §7.7].
4. **Dimensions and level structure.** The ratio dim Mram/dim Mu0 is not stated, and Mram as "new at T" is inferred [ARCH §7.3, §7.5].
5. **Design choices.** Why exactly 3 in the shares; why orbit length n′ > 2 rather than just even; why t has the shape of §1 [ENDGAME §2.3; WHYHALF §6.3].
6. **Behrend.** `BehrendSets` plausibly chooses the thick set T2; not traced to the live path [WHYHALF §6.6].

Now answered: why b is exponential (§4.4, an inference); the splitting type of signal primes (§4.6); where the Galois side enters (E2 only, §5.2); why only inert primes are counted (§2.3); how the towers are joined (H1).

---

## 10. Correspondence with the author's timeline

**Located.**
- (2) Dᵃ(Ω·θ)(0) divisible by p^{a/p+a/p³+…−O(log a)}: γ_p·a, §4.
- (5) the switch to G_z: exactly G_z.
- (8) iterated theta lifts π ↦ π ⊞ μ_j[t], multiplicity m ≈ √X: §3.
- (9) cancellation of order-m terms via Chowla–Selberg: the logΩ cancellation of §5.4 *(inferred match)*.
- (10) a lower bound on the divisibility of the m-fold lift: §4.5.
- (12) the seesaw and Rallis: `MIid`, λ_j.
- (13) Bost.
- (14) the cost of each lift: §6; "twisting" matches KillAt and §5.2's twisting; "division" plausibly DIV *(inferred)*.
- (15) gluing an integral structure across Hecke characters: RR.
- (16) a relative trace formula with projected Poincaré series: Theorem S, without the GL₅ part.
- (17) classes not killed by twisting, a weakening of Vandiver: the Ш bound.
- (18) covolumes, theta-series index, congruences: §5.2.
- (20) GRH: the level ⟨ψ⟩ with 4 : 3 shares, a choice, and windowed Landau.

**Partly located.**
- (1) Stepanov: structural only (§6.4).
- (7) GGP periods are located; "m non-interlacing weights" is inferred.
- (19) `BehrendSets` is located but not traced to the live path.

**Not located.**
- (3) the sixfold cover of GL₅ and the Poincaré bundle.
- (4) W(1_S) ≥ 0 and the bootstrap.
- (6) W·1_{(0,1]} + X^η·1_{(0,1/X]} ≥ 0.
- (11) the Iwasawa tower via pigeonhole; candidates are the 2-power layer or KILLAT's tame tower *(inferred)*.
- (14) the "2/3 a priori" version.

Sources: [WHYHALF; LOCALDIV; ARCH; LINKN; CHAININD; SEESAW; L6; RANK; CONGMOD; PAIRB; VWIN; ONECHARU; THETA].

---

[^n4]: NUMTEST4's phrase "inert in both" describes inertClass primes, not signal primes [SIGNAL; LEDGER §0.4]. Which class NUMTEST3's instance belongs to is disputed (§4.7).

[^tiebm]: The orphaned `TieBm` formulation, in which the middle levels are set to 0, has no consumer, so ARCH's worry about it lapses [SEESAW §0.1].

**Corrections that change the picture** (newer node first; SUMMARY §5–§16 has the full list).
1. e_D + e_L + 7 > 0 is forced, and the live exponent is 9 [ENDGAME; LEDGER, closing LANDAU §4].
2. The live LossBounds producer is `linkGLOBAL7_items`; `linkGLOBAL7_pk` is a twin off the live path [GATIE, correcting LEDGER].
3. The x^{−1} precision is formula against formula [GATIE, correcting LEDGER oddity 4]. LoP pays the top offset; digit sums are booked in E [GATIE, correcting WRITEUP (11)]. errF carries log X″, not log log X″ [GATIE, correcting SUMMARY §11].
4. H5 is not in the Lean [LEDGER, against ACCOUNT §0.4]. DIV uses only |p_j − q_j − k| ≤ m, not Σ_j(p_j − q_j) = mk [LEDGER, inferred].
5. Tw has no cutoff at X″ [TWSET, correcting CONGMOD, JOIN, KILLAT]; there is no single twist seed [LARGETW, correcting ORDER].
6. The congruence machinery enters only through E2, not E1 [MIRABOLIC; WHERECONG, correcting CONGMOD].
7. MULTEQ read a dead route [LIVEPATH]. Crystallinity at l comes from `Row0b` via `G2a` [G2A, correcting GALREP]; purity from Jacquet–Shalika [ROWCRYS].
