# Review of MAIN-ARGUMENT.md

Reviewer brief: read the exposition cold as a number theorist (Part A), then check its eight weightiest claims
against the nodes it cites (Part B). I did not edit MAIN-ARGUMENT.md. I did not open the Lean source: every
claim checked here was settled by the node files. "Doc" means MAIN-ARGUMENT.md.

---

# PART A — cold read

## A1. Section by section

### §1 The statement and the strategy

**Restatement.** G_z and g_χ are the Riesz-smoothed (kernel y^s/(s(s−1))) explicit-formula remainders for ζ and
for L(s,χ). Each equals −Σ_ρ y^ρ/(ρ(ρ−1)) + O(log). I checked the main terms: the residue at s = 1 of
−ζ′/ζ·y^s/(s(s−1)) is y log y − (1+γ)y. G_m is a positive combination of these over ⟨ψ⟩. A one-sided bound
G_m ≤ x^{1/2+Cε} on windows [Y, Y^{3/2}] for a sequence Y → ∞ gives GRH for ⟨ψ⟩. The proof is a Landau argument
on Taylor coefficients of the Laplace transform at σ+iγ. The bound itself is to come from a product-formula
comparison: the p-adic divisibility of jets of CM theta functions at inert primes against their archimedean size,
repeated m ≈ √x times through a chain of theta lifts. The relative error is 1/m + m/x.

**Could not follow / gaps.**
- e_D, e_L in the exponent (e_D+e_L+7)ε are undefined. Whether e_D+e_L+7 > 0 is forced is never said. LANDAU §4
  flags this as something to check.
- ASK is displayed before tops t, TT, a_t, w_{j,·}, partner(t, Frob_n) and m are defined. Most of them are never
  defined in a sentence. In particular |TT| never gets a size, and §2 and §6 need |TT| ≈ n.
- Landau paragraph:
  - "σ large in terms of the window ratio" is unexplained. The reason is that outside the window G_m is bounded only
    trivially (≪ e^{2u}), and σ must be large enough that the gamma kernel's tails beyond the window are
    exponentially smaller.
  - Why Re a_k(σ) appears beside |a_k(σ+iγ)| is unexplained. It is the cost of the one-sided bound.
  - "A zero … produces a nearest singularity" needs γ chosen so that the nearest pole is unique. Without that,
    poles on the circle of convergence could make the coefficients cancel.
- Ω, "the jet", "Chowla–Selberg period" and "theta lift" are used with no object attached.
- Characters: χ_{−d} (in ASK and MAIN) and χ_d (in Ω) are both used. With d ≡ 3 mod 4, (d/·) is not a quadratic
  field character, so these must be the same character. Fix the notation.
- "Summed over inert p … the uncapped part is the inert half of log a!". The uncapped sum Σ_{inert} γ_p a log p
  diverges. It is cut at p ≤ a (Legendre), or at n ≤ a/w by the caps. The sentence should say which.
- "relative error ≈ 1/m + m/x" is asserted with no derivation in §1. Relative to what? It is relative to the trivial
  size x of G.
- The size table omits |TT|, f = 2n, δ, X′, X″ and b′, all of which later arithmetic needs. It gives no reason for
  t ≈ x^{398.5}.

### §2 The analytic frame

**Restatement.** The host E is an abelian CM field of degree 4n ≈ x^{2+8ε}. Its Galois group is (sign for
√−q, sign for √−d) × A. A carries a cyclic 2-power quotient of order 2^e and a subgroup A_0 with A/A_0 dual to
⟨ψ⟩. ASK − MAIN is expanded over characters of Gal(E/ℚ) by orthogonality and the Riesz identity. Only "thick"
partner places (w ≈ b, Riesz length ≈ x) carry fluctuation at scale x; the rest are killed by an effective PNT. Only
signal primes reach thick places. Averaging over A_0 with 4:3 shares on TT turns the thick indicator into
Gz + (3o+1)^{-1}Σψ^j plus quadratic twists Sig_A. Sig_A is bounded by host selection of (q,d). The upshot is
U·(G_m(x) − Sig_A − 4x^{1/2+ε}) ≤ Σ(ASK − MAIN) + small, with U = |TT|mbδ/2. So the whole task is
ASK − MAIN ≤ U·x^{1/2+O(ε)}.

**Could not follow / gaps.**
- **"Y" has three meanings.** It is the window base (§1), the (q,d)-selection scale with log q ≈ Y^{ε/5} (§2.1),
  and the level-prime scale Y = (k e^{x^ε})^8 (§2.1). This is not cosmetic. ThinScales needs log q ≪ log X′ = x^{ε/3}.
  That holds if log q ≈ x^{ε/5}, and fails completely if Y is the level-prime Y.
- X″ is never defined. (SERVED: X″ = x·n·X′.) b′, T2 and Φ (= Gal(E/K)) are undefined. Φ is also the Laplace
  transform of §1 and, later, the Bost loss term of §5.4.
- U ≈ x^{2.5}b silently uses |TT| ≈ n.
- Step 2: the three kinds of cap are listed, but not where thin caps occur or what fraction of positions they take.
  Without that I could not check that "high primes" (X′ < p < X″) are cheap.
- ThinScales for characters of conductor ≈ e^{x^{ε/5}}: de la Vallée Poussin requires no exceptional zero. The
  doc says "zero-free region proved in the tree" but does not say that the real characters are protected by
  host-selected zero boxes (RealBox / GoodFor).
- §2.2 writes G_χ for the function §1 called g_χ. The bridge identity holds for an arbitrary constant in place of
  L′/L(1,χ) (CHBALANCE oddity 1). The doc does not say where the true L′/L(1,χ) is pinned.
- "ASK counts every inert prime" (§2.3) is followed by a classification that uses Hecke and orbit "routes" before
  either is explained.
- "LoP … of relative size x^{−1/2}": relative to U it is x^{O(ε)}. It is x^{−1/2} only relative to the budget
  U·x^{1/2}.
- Audit history ("NUMTEST4's description … was wrong") interrupts the mathematics.

### §3 The objects

**Restatement.** Three towers of hermitian spaces over E:
- definite column spaces X_0 ⊂ … ⊂ X_m, carrying algebraic modular forms;
- a row tower Y_m ≅ X′ ⊂ X_m down to an indefinite Y_0 with non-compact quotient, which carries the L² space HH;
- layers W_j of signature (k+j−1, m−j), paired with definite V_j, which carry cusp-form lattices M_j.

Column steps K_j are kernels built from Taylor jets of CM theta functions. The top period of the m-fold lift is a
codimension-one Gross–Prasad period on U(X′). A seesaw (MIid) transports linear relations among it to Bessel
periods of Poincaré series on U(Y_0). B_u is defined by pulling back along ι and RR := ι(Λ), so integrality of B_u
is integrality of the column period.

**Could not follow / gaps.**
- **θ_{c,c′} is the central object and is not defined.** The doc does not say in which variables it lives, which
  lattice (Hom(c, c′)⊗O?) it sums over, or how σ* enters. Without that, "jet of order a" and "column minors" in §4
  are opaque.
- ρ_j, ρ′_j, divDe, unf_j, sharp, Ph_T, C_u and P_tL are Lean names, not mathematics.
- Only Y_0's signature is given. Y_j for 0 < j < m are not described.
- The layers are said to "supply the covolume of RR", but no map from Λ (or ι) to the M_j is stated. §5.2's
  det ι = κ^D∏det θ_j is the only link, and §9.3 says no theorem factors ι through the θ_j. This is a structural
  hole (see A2).
- κ is the descent similitude constant here, and in §7 it is an index set of frame rows.
- "a_u exists but its value is never computed. It does not need to be." Plausible for integrality, but the reader
  needs one sentence on why the frame (which mixes u's) is insensitive to per-u scalars. The doc defers this to
  §9.3.
- F_j, E_j in sg; |W| ≈ 3Γ²x^{C_F}; C_F; f: undefined.
- The diagram helps but introduces 𝔭^{−sg} and NuLat without definition.

### §4 The engine

**Restatement.**
- At inert p, the CM formal group is the height-two Honda group. Rescaling by ϖ with ϖ^{p²−1} = p makes order-a
  derivatives divisible by about p^{γ_p a}, γ_p = Σ_{e odd} p^{−e}. This is Legendre minus the Lubin–Tate cost.
- A single σ* has a Dwork Gaussian obstruction. For the full kernel at a place where the hermitian form is split,
  the self-terms cancel by isotropy. What is left is a cross Gaussian exp(−(π/p)hh) coupling positions s and s+1 on
  the Frobenius orbit.
- Each Gaussian factor of level e forces one derivative onto the minors at the partner position. Two such
  derivatives kill a minor, so the factors are capped by the weight w there.
- Legendre/Dwork then gives a per-lift gain Σ_e(a/p^e − w)₊, which is exactly the ASK summand.
- The gains add over m lifts because each step is divisible on the whole integral lattice and every level carries
  the same a.

**Could not follow / gaps.**
- "A derivative of order a of an integral series has valuation ≥ v_p(a!) − a/(p²−1)". Integral in which variable,
  evaluated where? The statement needs the normalisation: D^a f(0) = a!·c_a, with c_a integral in the ϖ-rescaled
  coordinate.
- S_s ("twisted log series") is given no formula. u_s, "orthonormal local basis", σ (Frobenius of ℤ_{p²} vs
  complex conjugation c) are not distinguished.
- At a place of E⁺ split in E, the hermitian form is a duality between V_w and V_{w̄}. Why it becomes a
  "unimodular hyperbolic pair over ℤ_{p²}" in the position variables is the key point and is not explained.
- NUMTEST3: A, C, th0, c are undefined. "AA^σ + CC^σ = 0" needs σ specified.
- n′ (orbit length) is undefined. "Column minors" are never related to the weight vector, so "cap = number of
  minors = weight" is a bare assertion.
- §4.4's display is m·Σ_t Σ_e (a_t/p^e − w_j)₊ with j free. It should be Σ_j Σ_t Σ_e(…)₊.
- "Honest induction": this is composition of maps each divisible on the whole lattice. The doc should say so, and
  add that the intermediate lattices' metrics cancel in the Bost height (submultiplicativity with fixed
  intermediate norms). Otherwise "its slope never enters" reads as a claim needing proof.
- §4.5: Pr, τ, kinkHH, VV, g₀⁺ and "LP-duality" are undefined. The Hecke/colength route is described as buying a
  surplus and then spending it, which is opaque. The orbit route is said to serve "signal places" only. SERVED says
  it also serves even-order inertClass primes in [X′, X″] (see B4).
- "The Lean bound is never short by more than 0.98": short of what, in which direction?

### §5 Archimedean side and the slope inequality

**Restatement.**
- The height of B_u is bounded by the product of the column-step norms (a Fock-space Cauchy bound,
  ph(ν) − |ν|logΩ per place) and the Rallis scalars.
- The mean of the conjugate periods is the averaged Chowla–Selberg constant, which carries −L′/L(1,χ).
- RR's covolume is bounded through layer covolumes, by Hilbert–Samuel plus flat sections, with main term
  (p_j − q_j)Σ w logΩ.
- Bost's inequality for the joint map ⊕B_u bounds the mean source slope by μ(RR^∨) + log|W| + HN terms.
- Chaining: gain ≤ source slope − μ(M_u) ≤ … ≤ s − μ(RR^∨) + Main ≤ log|W| + Φ + Main.
- The large logΩ terms cancel because Σ_j(p_j − q_j) = mk.

**Could not follow / gaps.**
- **The ph-terms of the non-top weight entries.** The height has Σ_ρ ph(ν_{jρ}), which includes the k entries of
  size ≈ w and the t+1 blocks. Main keeps only m·ph(a_t). The doc never says where the rest goes. (HEIGHT: it is
  cancelled by the hook products in λ_j. That is why −Σ log λ_j sits in the height.) This is the most important
  single omission for following the arithmetic.
- "mean_ρ log Ω_ρ = log Ω = γ + log(π/v) − L′/L". v is undefined. COVOL writes the in-tree identity as
  "−meanLog = γ + log(2π/√d) − L′/L", so a sign convention needs stating.
- Notation clashes: HH is the Hilbert space in §3 and x^{C_H}b in §5.3. Φ appears again. Lo5, Ee, Fo, E_DIV, Λ5, lg,
  La, Count5, u_F, B₀ (defined only in §6) and F_o are undefined.
- "μ(RR^∨) … cancels, so its size is never used". Misleading: the upper bound on μ(RR^∨) (DIV, covolume) is used, at
  relative precision x^{−4}. What is never needed is a two-sided estimate.
- §5.2: "the uniform volume theorem behind the lower slope bound has no main term" sits next to a covolume bound
  with an explicit main term. A reader cannot tell which theorem supplies which.
- "Each side ≈ x^{6.5}·b per layer against a budget of x^3·b … relative x^{−4}" mixes per-layer and total.
  x^3/x^{6.5} = x^{−3.5}. The x^{−4} is after summing the m layers (x^7 b).

### §6 Why 1/2

**Restatement.** The errors are one-off terms of size one copy of the signal (|TT|·a·x^ε) and per-lift terms
B₀ = f·m·b·x^ε, which grow with m because the layers have q_j up to m. Dividing by U gives x/m + m + k/n². The
exponent 1/2 is the balance point.

**Gaps.** a_E is undefined. The display needs f ≈ 2n and |TT| ≈ n, neither stated. The Stepanov table is helpful.
The statement "a per-lift cost independent of m would prove ψ(x) = x + O(x^δ)" is the most important conceptual
remark in the doc and deserves promotion (see A4, Q1).

### §7 Non-vanishing

**Restatement.** Bost needs the joint period map to be nearly surjective. This follows from a frame property, which
rests on Theorem S. Theorem S has two halves:
- near-orthogonality of the Bessel Poincaré series, off-diagonal ≈ the random value d_u d_{u′}/D*, by double
  unfolding;
- an exponentially precise dimension count D_all ≈ formal degree × volume, by an exact cusp-form projection and
  pointwise kernel bounds.

**Gaps.**
- κ, κ₁, "the record D" and "stand-in row records" are audit/Lean vocabulary.
- "n" in e^{−nf log n/16} and "gap > 2n" is the rank, not the host n.
- "q" in q^{−(k−2r−5)} is a residue-field size, not the host prime q. s and r in (2/g)^{(s−1)kf} are undefined.
- "Off-diagonal HS norm ≤ (1+b^{−6})d_u d_{u′}/D*" should be the HS norm squared.
- Why near-orthogonality at the bottom transfers to B_u (with unknown a_u) is left implicit.

### §8 Galois-theoretic inputs

**Restatement.**
- At twisted places the target lattice is a projection onto a Hecke-eigen type part. Its index is bounded by a
  congruence module.
- The congruence module is bounded by Selmer groups through a Ribet–Wiles/Fitting-ideal argument.
- The ρ-block is killed by choosing a twist in a finite tame tower.
- The cyclotomic blocks need Σ_l Σ_{e<t} log|Ш¹(ℚ_l/ℤ_l(−e))| ≤ √b, proved by an R = T argument for
  residually reducible U(3).

**Gaps.**
- Why crude bounds fail is asserted without reason. E is abelian, so the minus part is governed by Bernoulli-type
  L-values. A reader will ask why that, plus the known equivariant results for abelian fields, is not enough.
  ONECHARU's answer is that the plus part needs lower bounds for Borel regulators, which are not known. That belongs
  in one sentence here.
- ε is the cyclotomic character in "χ₁ε^{−1}", and also the small parameter. e is reused: 2-power exponent, odd
  distance, twist. t is the Speh length here; is it the same t as the column-block size?
- NN, g² + e ≤ D₀ and HasAut are undefined.

## A2. Logical skeleton

1. **[standard, windowed variant]** If G_m(x) ≤ x^{1/2+Cε} for all x in [Y, Y^{3/2}] for arbitrarily large Y, for
   every small ε, then L(s,ξ) ≠ 0 for Re s > 1/2, ξ ∈ ⟨ψ⟩.
2. **[standard: mean-square/zero-density/Siegel]** For each scale there are (q,d) such that:
   - every quadratic twist ξ(·/q)^i(·/d)^j, (i,j) ≠ 0, has |g| ≤ y^{1/2+ε/2} on the window;
   - all characters of Gal(E/ℚ) satisfy ThinScales at lengths ≥ X′/3.
3. **[new, with mechanism: finite Fourier analysis]** The bridge: U·[G_m(x) − Sig_A − 4x^{1/2+ε}] ≤ Σ(ASK − MAIN)
   + small, with U = |TT|mbδ/2 > 0.
4. **[elementary]** So it suffices that ASK ≤ MAIN + Err with Err ≤ U·x^{1/2+O(ε)}.
5. **[new, with mechanism: Gaussian class + cap lemma + Legendre/Dwork]** At every split-hermitian inert p, the
   one-step column map is divisible on the whole integral lattice by Σ_t Σ_{e odd}(a_t/p^e − w)₊ (up to O(1)).
6. **[new, with mechanism (two routes); bookkeeping]** Summing over served primes, and charging dropped primes their
   full ASK at cost ≤ x^{−1+O(ε)}U, gives ASK − LoP ≤ Ga.
7. **[elementary]** The divisibilities compose over the m steps, so the m-fold column period has divisibility Ga.
8. **[asserted, with stated mechanism; supplier not traced on the live path]** Seesaw MIid: the top Gross–Prasad
   period equals a unit times a_u times a bottom Bessel period. Hence B_u(N_u) ⊆ RR^∨ with RR = ι(Λ).
9. **[new, with mechanism: Fock/Cauchy + averaged Chowla–Selberg + Rallis]** Height of B_u ≤ Σ_j[Σ ph − |ν|logΩ]
   − Σ log λ_j + … . The hook products of λ_j cancel all ph except m·ph(a_t). That cancellation is not stated in
   the doc.
10. **[asserted without a mechanism in this document]** Covolume of RR: det ι = κ^D∏_j det θ_j. The doc gives no
    relation between ι, Λ and the layer lattices M_j, and §9.3 says none was found.
11. **[new, with mechanism: descending induction, effective arithmetic Hilbert–Samuel, flat sections]** lcv(M_j)/D ≤
    (p_j − q_j)Σ w logΩ + C·B₀ log log x, with signatures (k+j−1, m−j). The signatures themselves are asserted.
12. **[new, with mechanism: Ribet–Wiles + KillAt + U(3) R = T]** Congruence-module and index terms at twisted places
    are ≤ per-lift budget. This needs the twisted-place set to be {resChar ≤ X″} ∪ {d,g₀,g₁}, which is not located.
13. **[new, with mechanism: double unfolding; exact cusp projection]** Theorem S, which gives the frame, which gives
    robust near-surjectivity. Then Bost/HN: s − μ(RR^∨) ≤ log|W| + Φ.
14. **[arithmetic, mechanism given]** Chaining 6–13: ASK ≤ Main + (one-off |TT|a x^ε) + m·(B₀ per lift). Dividing by
    U gives x/m + m + k/n² ≲ x^{1/2+O(ε)} at m ≈ √x, k ≈ x^{9/2+10ε}, n ≈ x^{2+8ε}.
15. With 3 and 4, G_m(x) ≤ x^{1/2+O(ε)} on windows. By 1, GRH for ⟨ψ⟩.

**Holes, exactly where.**
- **H1 (between 9/11 and 14).** Step 14 needs μ(RR^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + …, i.e. step 10. The doc states
  det ι = κ^D∏det θ_j as a fact in §5.2, but supplies no map relating ι to the θ_j. The nodes call it a hypothesis of
  `BoundsMu`, "inferred" from similitude clauses. Step 14 needs exactly this.
- **H2 (step 8).** The live producer of MIid was not traced to the seesaw supplier (JOIN §1d). The doc says so.
- **H3 (step 12).** The identification of the twisted-place set ("integral theta-unimodularity at every good
  p > X″") is needed so that untwisted places contribute index 0. It is not located (§9.3).
- **H4 (step 11).** The layer signatures (k+j−1, m−j) are an input (`FactKaBlocks`) with no derivation. They are the
  source of the per-lift growth, i.e. of "1/2".
- **H5 (consistency, not logic).** Ga ≤ Main + Err must hold arithmetically for the hypotheses to be jointly true.
  ACCOUNT §0.4 says this "Ga − ASK ≤ budget" condition is neither proved nor needed by the Lean. The doc does not
  mention it.
- The doc's own chain also omits why only m·ph(a_t) survives (step 9). This is a gap in the exposition, not in
  the logic.

## A3. Paper checks

| check | result |
|---|---|
| Riesz main terms; residue −1/(ρ(ρ−1)); MAIN = a(log a − 1 − γ + L′/L(1,χ_{−d}) − log w) from the identity Σ Λχ(a/n − w)₊ = w g_χ(a/w) − aL′/L | closes |
| λ(h) = (3 + 1_{A_0})/(3o+1) = o^{−1}[1 + (3o+1)^{−1}Σ_{j≠0}ψ^j(h)]; total mass 1/o; resulting G_m weights 1 and (3o+1)^{−1} | closes |
| Balance x/m + m + k/n², assuming a_E ≈ a = xb, f = 2n, \|TT\| ≈ n | x/m = x^{1/2+ε/16}; m = x^{1/2−ε/16}; k/n² = x^{1/2−6ε}; window k ≤ n²x^{1/2−ε} = x^{4.5+15ε} holds. Closes, but only with \|TT\| ≈ n, which the doc never states |
| Non-vanishing constraint k ≳ m⁵ f log b | m⁵·f·x^ε ≈ x^{4.5+8.7ε} ≤ x^{4.5+10ε}. Closes. Consequence the doc does not state: k/n² ≤ m forces n ≳ m⁴ = x². **The host degree is fixed by non-vanishing**, which explains n ≈ x^{2+8ε}. |
| U ≈ x^{2.5}b, budget x^{3}b; per-layer logΩ terms ≈ k·f·b ≈ x^{6.5}b, total ≈ x^7 b | relative precision x^{−4} after summing layers. Closes (doc's "per layer" wording off by x^{0.5}) |
| N(m) = k + m(t+1) ≈ x^{0.5}·x^{398.5} = x^{399}; Y_m rank r + mt = N(m) − 1 (so X′ ⊂ X_m has codim 1); codim of X_j in Y_j is m−1−j, so its parity alternates; W_j has p+q = r; Y_0 = (k + m/2 − 1, m/2) = W_{m/2} | closes |
| Σ_{j=1}^m(p_j − q_j) = Σ(k + 2j − 1 − m) = mk exactly; \|p_j − q_j − k\| ≤ m − 1 | closes. Side remark: p_j − q_j ≡ k+1 (mod 2) since m is even, so the residual is never 0. |
| Leading order, Mertens vs Chowla–Selberg | log(a!Ω^{−a}) = a log a − a − aγ − a log(π/v) + aL′/L (the log(π/v) is matched by Count5). Inert half of log a! ≈ (a/2)(log a − γ + L′/L) and split half ≈ (a/2)(log a − γ − L′/L), so log a! + aL′/L ≈ 2·(inert half), matching the ASK weight Λ(n)(1−χ(n)) = 2Λ(n) on inert odd powers. Main terms agree identically; the content is all in errors. Signal per thick place is b·G(x) ≈ b x^{1/2} against a main term ≈ xb·log, so the needed relative precision is x^{−1/2}. Closes, given χ_d ≡ χ_{−d}. |
| Legendre: v_p(a!) − a/(p²−1) ≈ a/(p−1) − a/(p²−1) = ap/(p²−1) = γ_p a; γ_p a − Σ min(a/p^e, w) = Σ(a/p^e − w)₊ | closes |
| Anisotropic inertClass primes: h of odd order ⇒ trivial image in C_{2^e}; count in ≤ 2 classes mod 2^{e+2} ≈ x²; charge ≈ \|TT\|m·a·x^{O(ε)}/x² ≈ x^{−1+O(ε)}U | closes |
| ThinScales: log q ≈ x^{ε/5}, log y ≥ x^{ε/3}; classical region gives saving exp(−c x^{2ε/15}) ⊇ exp(−c x^{ε/8}) | closes **only** if the (q,d)-scale Y is ≲ x. With the level-prime Y = (ke^{x^ε})^8 it fails completely. The notation must be fixed. |
| (q,d) selection: Σ_ρ 1/\|ρ(ρ−1)\| ≈ log q ≈ Y^{ε/5} ≤ y^{ε/2}; Heath-Brown-type quadratic zero density makes exceptional q a vanishing proportion | plausible; consistent with stated sizes |
| Chain display line 2 → 3 (adding DIV) | closes (Fo cancels); Bost and DIV directions consistent; final direction (upper bound on G_m) is what Landau needs |
| Landau lemma as stated | true-looking, provided the nearest pole is made unique by choice of γ and σ is large enough for the tails |
| Ш bound √b vs truth | truth is poly(x), √b = e^{x^ε/2}, so the bound is weak; the need for R = T is unexplained in the doc |
| "dropped high primes" X′ < p < X″ at thin caps | cannot check: the fraction of thin partner positions is not given |
| t ≈ x^{398.5} | no constraint in the doc determines it (nodes: t ≥ r + 5 for L6; ranks ≤ x^{400} for VWin's 401) |

## A4. Five questions for the author of the proof

1. **Sharpness.** G_z(x)/√x is a nonzero mean-zero almost-periodic function of log x. So G_m(x) ≥ c√x occurs in
   every window, and the chain must be tight to x^{o(1)} there. Equivalently, some per-lift loss must really be ≍ m,
   not merely ≤ m. Which inequality is tight? Why do the layers need signature (k+j−1, m−j), with q up to m? Why not
   q_j bounded, which would beat RH and so cannot be?
2. **Joining the towers.** The descent ι: (top forms) → EE and the layer lifts θ_j are different maps. Precisely
   what identity relates covol(ι(Λ)) to the layer covolumes lcv(M_j)? How does the arithmetic Hilbert–Samuel bound
   reach relative precision x^{−4}, uniformly on Shimura varieties of U(p,q) with p ≈ x^{4.5} that change with x?
3. **The seesaw.** "Transport of linear relations" from Gross–Prasad periods of an m-fold lift to Bessel periods,
   two levels at a time, is a strong statement. Is it an Ichino–Ikeda-free identity of distributions? Is a_u ≠ 0
   proved, or only existent? Why is near-orthogonality, a metric statement about P_u, insensitive to the unknown
   per-word a_u?
4. **Theorem S at exponential precision.** For a discrete series of U(k+r_S, r_S+1)^f on a non-compact quotient,
   with rank ≈ x^{4.5}, why is the non-identity contribution e^{−nf log n/16} relative, uniformly including the deep
   cusp? Why is the off-diagonal Gram mass equal to the random value d_u d_{u′}/D* to within 1 + b^{−6}? Where would a
   spectral (Eisenstein) contribution have gone?
5. **Divisibility on the whole lattice.** The one-step bound must hold for every integral algebraic modular form in
   rank up to x^{399}, not just theta images, to O(1) per prime per lift. Otherwise the m-fold multiplication
   destroys it. Has any composite of two lifts been computed? Separately: for abelian E, exactly which part of the
   Ш bound is out of reach of the known equivariant results? Is it only the plus part, and only for lack of
   regulator lower bounds?

---

# PART B — fidelity check

| # | claim (doc §) | node(s) | verdict |
|---|---|---|---|
| B1 | Windowed Landau (§1, §9.1) | LANDAU §1b, §2b, §4, §5 | **Faithful** on statement and mechanism (kernel positivity, non-cancelling residues, real zeros push up; averaged-coefficient positivity not used). Minor: (i) the doc says "every ε > 0"; the node has ε ∈ (0, ε₁). (ii) "Four technical sub-lemma bodies were not read": the node lists at least eight unread bodies (`landau_tails`, `landau_nearest`, `landau_pole_asym`, `landau_cauchy`, `landau_growth_contra`, `poleData_char` past l.175, `Gchi_growth`, `windowHyp_of_rpow`). (iii) The node's oddity (the hypothesis quantifies over all eD, eL, so ChainTied must force eD+eL+7 > 0) is dropped. |
| B2 | ASK − MAIN = De and how ψ enters (§2.2) | CHBALANCE §0–2; SIGNAL §0.5 | **Faithful**: exact orthogonality identity, 4:3 shares, U = \|TT\|mbδ/2, errors ≲ x^ε log x relative to U, signal primes alone reach thick places (SIGNAL, the later node, correctly used). Understatements: the identity holds for an arbitrary ell (CHBALANCE oddity 1), and the true L′/L(1,χ) is pinned by `HostAddCharCompatible` (SERVED §0); the doc's "uses Σ … = wG_χ(a/w) − aL′/L" hides this. ThinScales also needs host-selected real-zero boxes (CHBALANCE oddity 6, SERVED). The existence of TT with exact shares is correctly listed as unread. |
| B3 | Gaussian class; cancellation at split places (§4.2, §9.1) | GAUSSCLASS §0–2; LEAVES; SUMMARY §10–11 | **Mostly faithful** (six links, u_s = c constant, split-at-p used only in link 2, one-variable a/(p²−1)). Overstatement: "proved through six links, each reconstructed". GAUSSCLASS read the statements, not the bodies, of the three arithmetic leaves. LEAVES later read `joint_integrality` and `lamPos_of_posEmb` (the latter is a rewrite whose content is the field `pos` of `CmpHyp`). **§9.1 "main unread" is stale**: it lists `restGc`/`HhDecomp`, but GAUSSCLASS read `restGc` in full and found `HhDecomp` proved. The actually unread items are the link `baseChange_preserves_unitary_of` (admitted + RestBeta + RestGc ⇒ class), the one-copy step (fourth-power trick inferred; confirmed numerically in LEAVES), and `CmpHyp.pos`. |
| B4 | Gain formula and iteration over m lifts (§4.3–4.5, §2.3) | HIGHERRANK §0; WRITEUP S7; ACCOUNT §0.5; CHAININD §0; SERVED §0; ORBIT/JETA (SUMMARY §11–12) | **Faithful** on the cap lemma, `ask_add_Mn`, the factor 2 (Σ 2·lw·e_w = 2 log p), the same a at every level, and the "normalisation error × m" caveat. Inherited slip: m·Σ(… − w_j)₊ with j free (CHAININD §0.2 has the same). **Misattribution:** the doc assigns the orbit route to signal primes only and lists "bad orbits" among dropped primes. SERVED §0 says g₀⁺ via `NoOperatorOrbitBound` is credited at signal p ≤ X″, at **even-order inertClass primes in [X′(1+Crρ), X″]**, and at bad orbits of Cand primes. (SERVED's own table also charges "bad orbits at kernel-served primes" as a dropped bucket, so the node is ambiguous; the doc should say which.) **Omission:** ACCOUNT §0.4's satisfiability condition Ga − ASK ≤ budget is unproved. |
| B5 | Seesaw joining column chain to Bessel pairing (§3.3, §5.2) | SEESAW §0, §3–4; JOIN §1d; ARCH §7.1 | §3.3 is **faithful**: TieBm orphaned, MIid live, supplier `mainX_of_lawsX` found, JOIN did not reach it, a_u uncomputed, RR = ι(Λ), integrality is column integrality. Small omission: SEESAW says the supplier is "conditional on that chain's hypotheses". **Overstatement in §5.2:** "Its determinant factors as det ι = κ^D·∏_j det θ_j" is stated as a fact. ARCH §7.1 and SEESAW §3 say it is a hypothesis of `BoundsMu` (SO:31-41), "inferred" from `l1c` + `l1d`, with no derivation found and no theorem factoring ι through the θ_j. §9.3 partly concedes this, but §5.2 should carry the caveat. |
| B6 | Slope chain and its final inequality (§5.3–5.4) | WRITEUP §1–3; ACCOUNT §0; RANK §0; HEIGHT | **Faithful** to WRITEUP's display, the 17 checks, and the syntactic cancellations (Fo, m·lg, log(π/v), logΩ symbol). Understatements: (i) ACCOUNT lists three precision-critical hypotheses: covolume/height at x^{−4}, Count5 at relative 1/m, and frame tightness η ≤ 6x^{−C_H}. The doc mentions only x^{−4} and "±La". (ii) "μ(RR^∨)'s size is never used" goes beyond WRITEUP: the upper bound is used. (iii) RANK: the log\|W\| term is not needed (a sharp version is proved); harmless. (iv) The hook-product cancellation of non-top ph terms (HEIGHT, end of "Where the split half goes") is missing, and the reader needs it. |
| B7 | Dimension count and near-orthogonality (§7) | COUNT §0; PAIRB §0–1; RANK §0; COUNTS, THMB (SUMMARY) | **Faithful**: double unfolding, no spectral decomposition, savings list with COUNTS' correction on second-type terms, PAIRB's level correction over SLEAVES, exact cusp projection, compression formula, gap x^{110} vs x^{1300}, k fixed by 2^{−k/2}e^{Cm⁵f log b} ≤ b^{−14}. Minor: (i) the off-diagonal bound is on ‖K₀‖²_HS, not the norm. (ii) RANK says Theorem S is proved "conditionally" (`theoremS_selected_of_loops`) and δ's smallness (`LinkIRR`) "supplied conditionally from a row count". The doc states the δ_p bound and D_all ≤ (1+η₁)D* without that qualifier. (iii) In "e^{−nf log n/16}", n is the rank r (COUNT), not the host n. |
| B8 | Ш/congruence bound: role and proof scheme (§8) | CONGMOD; LINKN; ONECHARU; VWIN; RT3 → MODU3, FINEND; TWIST → ORDER; GALREP; KILLAT | **Faithful, and the later node is picked at each conflict**: MODU3 (patching) over RT3 (no patching); FINEND (torus-invariant subalgebra) over RT3; ORDER over TWIST's possible defect. The VWin statement (Σ_l Σ_{k<x^{401}} log #Ш ≤ √b) matches VWIN. Omissions: (i) ONECHARU's reason crude bounds fail (LemmaK gives exp((2kn)^C log disc); the plus part would need regulator lower bounds). (ii) GALREP: `NoChiOff`'s real content is in `ConclusionZ`/`D7.Z_tie` (unread), and purity is used in `ConclusionG6` with its source untraced. The doc says only "no purity clause". (iii) RT3's hypotheses l ∤ h_K·disc K, l − 1 ∤ 2e are not mentioned; MODU3 says no l > 3 hypothesis. |

Other checks made in passing:
- The sizes table matches ACCOUNT, PAIRB and CHAININD (m ≈ x^{1/2−ε/16}; k; n; N(m) ≈ x^{399}; Stab ≈ x^{402}).
- The NUMTEST numbers match SUMMARY §8–10.
- The NUMTEST4/SIGNAL conflict is resolved in SIGNAL's favour, correctly.
- L6 ("seven literature theorems, each supplied in-tree") matches L6 §0.

---

# Conclusions

## (i) Verdict on the exposition

**UNDERSTANDABLE WITH GAPS.**

A number theorist comes away knowing the intended mechanism:
- a Chebyshev-type product-formula comparison, Lubin–Tate divisibility against the Chowla–Selberg archimedean size,
  identical at leading order;
- amortised over m composable theta lifts;
- one-off errors give x/m and per-lift errors grow like m;
- a finite-Fourier bridge to G_m, and windowed Landau.

The bridge, the Landau step, the local divisibility and the error balance can be reconstructed and checked on paper.
They cannot be reconstructed for:
- the central object θ_{c,c′};
- how the descent ι is tied to the layer covolumes (a genuine hole in the stated chain);
- why only m·ph(a_t) survives in the height;
- why the layer signatures, and hence "1/2", are what they are.

## (ii) Prioritised edits

1. **§1 (new box) and passim: notation.** Define TT and |TT| ≈ n, a_t, partner, caps w_j, f = 2n, δ, T2, X′, X″ = xnX′
   and b′ before ASK. Resolve the collisions:
   - Y: three meanings, one of them load-bearing for ThinScales;
   - n: host degree vs rank in §7;
   - HH: Hilbert space vs x^{C_H}b;
   - Φ: three meanings;
   - κ: two meanings;
   - e: three meanings;
   - q: host prime vs residue size;
   - ε: small parameter vs cyclotomic character;
   - χ_d vs χ_{−d}.
2. **§1/§4: a one-lift model computation.** Display the product-formula inequality for one jet with squared norms
   (HEIGHT's display). Show the leading-order identity: archimedean a log a − a − a logΩ equals 2 × the inert half,
   by Mertens and Chowla–Selberg. State that the signal b·G(x) requires relative precision x^{−1/2}. This is the
   missing bridge between the §1 slogans and §5.
3. **§3.2: define θ_{c,c′}.** Give its variables, lattice and σ*-construction, and how column minors relate to
   weight entries. Without this, §4.2–4.3 cannot be followed.
4. **§5.1: say where the non-top ph(ν) terms go.** They are cancelled by the hook products of λ_j (HEIGHT), which is
   why −Σ log λ_j is in the height and only m·ph(a_t) reaches Main.
5. **§5.2: downgrade det ι = κ^D∏det θ_j.** Call it a `BoundsMu` hypothesis, inferred from the similitude clauses,
   derivation not found. Mark it as a hole in the chain, with a cross-reference to §9.3.
6. **§2.3/§4.5: correct the orbit-route coverage.** It covers signal p ≤ X″ and even-order inertClass p in
   [X′, X″]. Reconcile "bad orbits" with SERVED.
7. **§5.4/§6: add the precision-critical hypotheses** (x^{−4}; Count5 at 1/m; frame η) and ACCOUNT's unproved
   satisfiability condition Ga − ASK ≤ budget. Replace "μ(RR^∨)'s size is never used" with "only an upper bound is
   used".
8. **§4.4: fix the display.** Use Σ_j, not m·, with w_j. Say the induction is composition of maps divisible on the
   whole lattice, and that intermediate metrics cancel in the Bost height.
9. **§6/§9.3: promote the sharpness remark.** G_z = Ω±(x^{1/2}) forces some per-lift loss to be genuinely ≍ m. Name
   that as the conceptual question, tied to the layer signatures. Say what fixes t ≈ x^{398.5} (L6's t ≥ r+5, the
   x^{400} rank bound), or that it is unknown. Note the observation n ≳ m⁴, forced by non-vanishing.
10. **§1 Landau, §8, §9.1: smaller additions and corrections.**
    - §1 Landau: add two sentences, on σ large because of the trivial-bound tails and on choosing γ so the nearest
      pole is unique.
    - §8: add ONECHARU's regulator reason and GALREP's purity / `ConclusionZ` caveats.
    - §9.1: update the stale unread lists (B1, B3).
    - Move audit-history parentheticals (NUMTEST4/SIGNAL, ARCH's worry) to footnotes.

## (iii) Mismatches found in Part B

1. §1/§9.1 Landau: "four sub-lemma bodies unread" understates (≥ 8). The ε-quantifier is loosened. The eD+eL+7 > 0
   oddity is dropped. [LANDAU §4–5]
2. §2.2: the bridge identity is ell-free. The L′/L pinning (`HostAddCharCompatible`) and the real-zero boxes for
   ThinScales are not mentioned. [CHBALANCE oddities 1, 6; SERVED §0]
3. §4.2: "each reconstructed" overstates. The arithmetic leaves were read at statement level in GAUSSCLASS, with
   later LEAVES coverage. [GAUSSCLASS §0]
4. §9.1 Gaussian-class row: the unread list is stale. `restGc` was read and `HhDecomp` was found proved. The real
   residue is `baseChange_preserves_unitary_of`, the one-copy step and `CmpHyp.pos`. [GAUSSCLASS §2, LEAVES]
5. §2.3/§4.5: the orbit route is attributed to signal primes only. SERVED credits it also at even-order inertClass
   primes in [X′, X″]. "Bad orbits" are listed as dropped, while SERVED §0 lists them among g₀⁺ recipients (the node
   is internally ambiguous). [SERVED §0, table l.118–125]
6. §4.4: m·Σ(…−w_j)₊ with j free (inherited from CHAININD §0.2).
7. §5.2: det ι = κ^D∏det θ_j is stated as fact. It is a hypothesis of `BoundsMu`, inferred, with no derivation
   found. [ARCH §7.1; SEESAW §3]
8. §3.3: the seesaw supplier's own conditionality ("conditional on that chain's hypotheses") is dropped. [SEESAW §0.3]
9. §5.4: the precision-critical hypotheses (Count5 at 1/m, frame η) and the unproved satisfiability condition
   Ga − ASK ≤ budget are omitted. "μ(RR^∨)'s size never used" overstates. [ACCOUNT §0.3–0.4]
10. §7: "HS norm" should be HS norm squared. The conditional status of Theorem S's supplier and of `LinkIRR` is not
    carried. "n" in e^{−nf log n/16} is the rank. [PAIRB §1; RANK §0; COUNT §0]
11. §8: ONECHARU's reason crude bounds fail, and GALREP's untraced purity source and unread `ConclusionZ`/`Z_tie`,
    are omitted. [ONECHARU §0; GALREP; SUMMARY §12]
12. §5.1: the averaged Chowla–Selberg sign convention differs from COVOL's "−meanLog = …". It is consistent only if
    logΩ := −meanLog. State the convention. [COVOL §0; HEIGHT l.280]

No conflicts were found where the doc picked an earlier node over a later correction.
