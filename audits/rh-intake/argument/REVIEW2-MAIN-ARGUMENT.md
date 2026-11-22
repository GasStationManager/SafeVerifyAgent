# Second review of MAIN-ARGUMENT.md

Reviewer brief: read MAIN-ARGUMENT.md ("the doc") cold as a number theorist (Part A). Then spot-check six claims against
the nodes they cite (Part B). Then compare with the first review (Part C). For Part A I opened no other file in the
directory. For Part B I opened only NODE files (HOSTSEL, ENGINE2, GATIE, STEPE, RANK, LEDGER, CHBALANCE, HEIGHT, DIVKEY,
ADM11), and I read REVIEW-MAIN-ARGUMENT.md only after Part B. I did not open the Lean source, and I did not edit the doc.
The verdicts below are about the exposition and about the argument as the doc describes it.

---

## A1. How the proof is supposed to work (in my words)

The target is a one-sided bound G_m(x) ≤ x^{1/2+9ε}. Here G_m is a positive combination of the Riesz-smoothed
explicit-formula remainders of ζ and of the characters in ⟨ψ⟩. The bound has to hold at every point of a sparse
sequence of windows [Y, Y^{3/2}]. A Landau-type argument on Taylor coefficients of the Laplace transform then turns this
one-sided bound into zero-freeness for Re s > 1/2.

The bound comes from a Chebyshev-type product-formula argument, amplified Stepanov-style.
- **The object.** Take a CM field K = ℚ(√−d) and an abelian CM host E ⊃ K. The auxiliary object is a family of Bessel
  periods of an m-fold chain of theta lifts. Each lift takes an order-a Taylor jet of a CM theta function.
- **The p-adic side.** At a prime p inert in K the CM curve is supersingular, and its height-two Lubin–Tate logarithm
  makes an order-a jet divisible by about p^{γ_p a}, with γ_p = Σ_{e odd} p^{−e}. On a split hermitian space the
  self-Gaussians cancel. "Caps" (the number of minors at a partner position) reduce the gain to
  Σ_{e odd}(a/p^e − w)₊. With a = xb and w ≈ b this is b times the Riesz weight (x/p^e − 1)₊. Summed over inert p, the
  gain is b times the inert-prime Chebyshev count at scale x.
- **The archimedean side.** The same jet has size ≈ a!·Ω^{−a}. By Chowla–Selberg, log Ω contains −L′/L(1, χ_{−d}), and
  this is exactly the main term of the inert count.
- **The comparison.** The two sides are compared on lattices through Bost's slope inequality. A frame (Theorem S)
  provides non-vanishing, and the layer covolumes supply the target's slope.
- **Amplification.** One lift is only Chebyshev quality, because the one-off costs are as large as one copy of the main
  term. Composing m lifts multiplies the main terms by m. The one-off errors stay fixed, and the per-lift errors are
  claimed to grow ∝ m. So G ≲ x/m + m, which is optimised at m ≈ √x.
- **From the inert count to G_m.** An upper bound on the inert count is an upper bound on G_z − g_{χ_{−d}} (plus
  ψ-twists). The split half is removed because the host (q, d) is selected by an unconditional mean-square argument over
  huge conductors, so that every quadratic twist has |g| ≤ y^{1/2+ε/2} on the window. The ψ-content is planted by 4 : 3
  weights on the tops over A/A₀. Finite Fourier analysis on Gal(E/ℚ) then gives exactly U·G_m(x) plus bounded twists.

---

## A2. The fourteen steps of §0

Columns: (ii) is the statement precise enough to attack? (iii) is there a mechanism, and do I believe it? (iv) does
the step compose with the earlier ones? I checked signs and sizes against §1's table.

| # | restatement | (ii) precise? | (iii) mechanism | (iv) composes? |
|---|---|---|---|---|
| 1 | G_m = G_z + (3o+1)^{−1}Σ_{ξ≠1} Re g_{ξ*}. The coefficient is λ̂(ψ^j) for λ = (3 + 1_{A₀})/(3o+1) on A/A₀ | yes | definition. I checked it: Σ_h λ = 1, λ̂(1) = 1, λ̂(ψ^j) = 1/(3o+1) | yes; all weights > 0, as Landau needs |
| 2 | For each window there is one (q, d), log q ≍ Y^{ε/5}, such that every quadratic twist has \|g\| ≤ y^{1/2+ε/2} and \|L′/L(1)\| ≤ 4 log y on [Y, X] | yes | **believable**. Mean square over a family of moduli > Z² is diagonal-dominated; reciprocity plus Siegel–Walfisz-type PNT handles the off-diagonal; zero density in a box handles the tail beyond Z. This is the classical "almost all characters" phenomenon | yes. Consumed two-sidedly at y = x only |
| 3 | At a signal prime, per top and lift: v_p ≥ Σ_{e odd}(a_t/p^e − cap)₊ − γ_p·Wc − logs | partly. "Kernel", "positions" and "the lattice" are only sketched (§4.1) | **believable locally**: Honda height 2, Dwork, isotropic cancellation, LP duality, and NUMTEST5 across the kink at rank ≤ 2. **Doubtful globally**: the kernel law and `lemmaS` at rank ~x^{399}, with many tops and frames, are statement-only | yes. Lower bound on valuations, the right direction. I checked the e = 1 term (A4) |
| 4 | m lifts: gains add along the chain | yes | **believable**: composing maps that are each divisible on the whole lattice is elementary. The weight sits in "on the whole global lattice of each level" (step 3) | yes |
| 5 | N_u := ∏𝔭^{−⌊e·sg⌋}·NuLat_u; Bk_u(N_u) ⊆ cc is the divisibility; μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee − Lo5 | yes | **believable**: a definition, an exact slope formula, floors ≤ C·X″ ≪ b | yes. A lower bound on the source, as Bost needs |
| 6 | DIV: μ(cc) + h(u) − Fo ≤ Σ_t[m(ph − a logΩ) − a log T_u] + errors | the pieces yes; the whole is a sum of many black boxes | Fock–Cauchy jet bound, Rallis hook, layer covolume and Chowla–Selberg: each believable as an inequality. **Doubtful in precision**: terms of size ≈ x^{4.5}·U (the k·w·logΩ pieces) must cancel to relative x^{−4} between two independent theorems (L6, D2) whose normalisations are tied only by a shared symbol | yes. An upper bound |
| 7 | Bost: s − log\|W\| − BL ≤ μ(cc) | yes | **believable as a theorem** (layer-cake over HN, a rank-only frame lemma). The frame input (Theorem S) is conditional. **What controls sharpness is not described** (A3, point 1) | yes. A lower bound on the target |
| 8 | Floors: μ(M_u) ≥ −c\|TT\|aLa(1+m/k); Ee ≤ m(ΣA·lg + cE·B₀); log T_u ≥ Σ_j mean log(w v/π) + m·lg − … | yes | L3: no mechanism given. L4: adm11, believable, with two unread inputs carrying ±B₀ against ΣA·lg. **L5: no mechanism in the doc.** One auxiliary prime T_u supplies, through −a_t log T_u, the entire −a·mean log w of Main. That is where the scale x = a/w enters the archimedean side (A3, point 3) | directions right. Only the lower bound on log T_u is used, where −a log T_u appears |
| 9 | Key identity L7 | yes | exact algebra, which I re-did: m·ph(a_t) − m·a_t logΩ − a_t log T_u, with Count5 substituted, gives Main. log(π/v) cancels and m·lg cancels | yes |
| 10 | Ga ≤ Main + log\|W\| + errors | yes | sum of 5–9 | yes. I re-derived it from L0–L5: h(u) and Fo cancel, and the signs are right |
| 11 | ASK − Ga ≤ LoP; ASK ≤ Main + ErrX5at | yes | **believable**: two piecewise-linear formulas with the same caps. LoP/U ≈ x^{O(ε)} | yes |
| 12 | Bridge: U[G_m − SigA − 4x^{1/2+ε}] ≤ Σ(ASK − Main) + 2\|TT\|mb/x | yes | exact orthogonality; ThinScales (dlVP) at lengths ≥ X′/3; host-selected twists | yes. A lower bound on ASK − Main by the signal; SigA used from above |
| 13 | G_m(x) ≤ x^{1/2+9ε} | yes | arithmetic; I checked it (A4) | yes |
| 14 | Windowed Landau gives GRH for ⟨ψ⟩ | yes | **believable**. The Gamma kernel u^k e^{−σu} has relative width k^{−1/2}, so any fixed log-ratio window carries one coefficient; a unique nearest pole gives \|a_k\| ~ d^{−k}; the one-sided bound costs only Re a_k(σ) | yes; ε is taken separately for each s |

**Net.** The analytic shell (steps 1, 2, 12, 13, 14) and the ledger algebra (steps 5, 9, 10, 11) close on paper. All the
content sits in steps 3–8. There, three things are claimed with no mechanism a reader can check:
- the precision of the archimedean leading coefficients;
- the T_u/Count5 conversion;
- the metric sharpness of the Bost step.

---

## A3. Adversarial pass: where an error would most plausibly hide

**The forced-rigidity principle.** This principle underlies points 1–3. Write the chain as ASK − LoP ≤ Ga ≤ … ≤ Main +
Σ(error bounds), and let S ≥ 0 be the total *actual* slack of all the inequalities in it. The bridge gives
ASK − Main ≈ U·(G_m − SigA). This is ≥ −U·x^{1/2+O(ε)} under the claimed result. Even unconditionally (PNT for ζ and
⟨ψ⟩, plus PairGood) it is ≥ −U·x·e^{−c√log x}. So, if every step is true, then
S ≤ U·x^{1/2+9ε}, and unconditionally S ≤ U·x·e^{−c√log x}. The chain contains terms of size x^{4.5}·U. **So every
inequality in steps 3–8 must actually be tight to relative x^{−1/2} of ASK under GRH, and to relative ≲ x^{−3.5} of the
big terms even unconditionally.** This includes:
- Hadamard in Bost;
- submultiplicativity of the jet norms;
- the Fock–Cauchy bound;
- the excess divisibility of the periods over the claimed lower bound.

Any instance where one of these is visibly loose refutes some lemma of the chain. This is testable in toy models
without reaching the GRH scale.

**Top five, ranked.**

1. **Step 7 together with step 6: metric sharpness of the slope step (question (a)).**
   - *Why suspicious.* Bost's inequality is sharp only when three things hold: the joint map is a near-similitude on
     the relevant directions (no Hadamard defect); the image saturates with index ≈ 1; and the true archimedean norm
     equals the height bound used. Here:
     - h(u) is the submultiplicative bound Σ_j log‖K_j‖² + log‖PtL‖² − log κ − Σ log λ_j. The true norm of the
       composite equals this bound only if the extremal directions of all m jet operators align on the Bessel image;
     - the true ‖B_u‖ also carries the uncomputed, word-dependent seesaw constant a_u (§3.3, §9.5.4);
     - the frame is only a rank statement. RANK says the frame "carries no metric content".
   - So nothing described controls the Hadamard defect or the defect h_bound − h_true, yet the forced-rigidity
     principle says both are ≤ relative x^{−1/2}. An exponentially precise Theorem S (b^{−6}) and limit multiplicity
     (e^{−rf log r/16}) are claimed, but they are used for rank, so they cannot be what delivers the metric precision.
     A slope inequality *can* in principle be sharp to x^{−1/2} (a near-isometry onto a nearly semistable target with
     exactly accounted index). The question is which hypothesis supplies the near-isometry of the *chain*, not of P_u.
   - *Check.* In a toy model (m = 2, rank ≤ 4, one top, small a), compute:
     - the singular values of the composite column map followed by the Bessel functional;
     - log‖composite‖ against Σ_j log‖K_j‖;
     - |a_u| across words and places.

     If the composite is far from extremal, some lemma of steps 6–7 is false. Separately, find the lemma that makes
     the joint map near-isometric with the metrics used in s.

2. **Step 6/§6.4: the √x barrier is not located, and the doc's leading candidate is ruled out by its own sizes
   (questions (a) and (e)).**
   - *Why suspicious.* A correct proof must contain a step whose actual loss is at least the prime fluctuation. If
     every actual per-lift loss were m-independent and ≪ √x·|TT|·b, then running the construction with larger m (all
     constraints seem polynomially adjustable: n ≳ m⁴, k ≳ m⁵f, b exponential) would prove G = o(√x). That is false.
     Now check the doc's candidates:
     - eE ≈ w·log w per (lift, place) gives Σ eE ≈ m·f·b·La ≈ B₀, not m·B₀. Divided by U it is x^{O(ε)}, not √x. So
       eE is **not** in the "m" family. This is an arithmetic slip inherited from STEPE.
     - The p-adic losses have real sizes ≈ f·b·x^{ε/3} or |TT|·b·x^{ε/3} per lift (§6.3 table), also m-independent.
     - The logΩ residual is negligible, since Σ_j(2j − 1 − m) = 0 and w_j varies by ≤ η + 1 = poly(x) at thick places.
   - So the whole burden falls on three items: the covolume q_j-error, E1 (index of the theta image) and E2
     (congruence modules). Each must be *genuinely* ≳ min(m, √x)·|TT|·b per lift. If a direct computation showed the
     Hilbert–Samuel q-term to be an exact, movable main term, the argument would prove too much.
   - *Check.* Decide whether the record is satisfiable at m = x^{0.9} (adjusting n, k). Then compute the real size of
     the flat-section q-error on U(p, q) (VOLUME/HS) and of E1 in a model case.

3. **Steps 8–9: the T_u/Count5 conversion of scale a into scale x.**
   - *Why suspicious.* Main = a(log a − 1 − γ + L′/L − mean log w). The −a·mean log w part, of size ≈ m·|TT|·a·x^ε,
     comparable to everything else, reaches the archimedean side only through −a_t log T_u. Here T_u is a single
     auxiliary prime of size log T_u ≈ m·x^ε. The doc says only that it "sets the level of the source forms".
   - In the record (from my Part B reading), hA is the top Bessel functional "scaled by T^{−deg}", T is a prime in
     [T*, (1 + 1/(fk))T*], and log T* = (1/(fk))·log(D*/d*_u). The T-adic cost is only m·EatT ≤ 12·CTu·B₀.
   - Two consequences. First, a scalar rescaling is height-neutral by the product formula. So the archimedean saving
     a_t·log T must be matched by genuine extra divisibility of the period values at some primes, and the T-adic
     integrality at cost only O(B₀) is a strong claim. Second, the benefit (≈ |TT|·a·log T) outgrows the cost
     (≈ m·f·b·log T) by a factor ≈ x/m. So unless something bounds T *above*, a larger T would prove ASK ≤ Main − (huge).
     The only candidates for that bound are the dimension relation and the frame.
   - *Check.* Read the producer of `Conclusion5`/`lowB` and `TwistedColumnBoundAtT`. Find every occurrence of T_u, and
     confirm that an upper bound on log T_u (or the frame's dependence on d_u) is used where it must be.

4. **Step 6 (D1/D2/L6): leading-coefficient cancellation at relative x^{−4}.**
   - *Why suspicious.* The Fock metric (pairK), the Rallis hook (λ_j) and the layer covolume each carry ≈ k·f·b·logΩ
     per level. They cancel only because the same `logOm` symbol appears in each. A shared symbol does not make both
     inequalities true. A c^{weight} normalisation mismatch (2π vs π, √d vs rd_E, Weil vs Fischer) by |log c| ~ 1 would
     falsify L6 or D2 by ≈ k·f·b ≫ U√x, and the doc says no lemma identifies the three norms (§9.5.2). The inputs at
     stake are statement-only: `covolume_measure_eq_one`, `FlatDegreeSt` and the seven `Published` theorems.
   - *Check.* Compute all three normalisations in one model, for example U(1,1) or U(2,1) at small weight with an
     explicit CM point. Verify that the logΩ coefficients agree exactly, including the 2π/rd_E constants. I verified the
     Chowla–Selberg constant itself (A4), so that part is not the issue.

5. **Steps 3–4: the kernel law at global rank (question (e)).**
   - *Why suspicious.* The local mechanism is convincing: supersingular height two, self-Gaussian cancellation on even
     orbits, one p per Gaussian factor. But it is tested only at rank ≤ 2 with one top and tiny sizes. The claim needs
     the cancellation on the *whole* global lattice at rank ≈ x^{399}, with frames, at every signal p ≤ X″, with
     per-lift loss ≪ U√x/m. If the cross-Gaussian structure fails anywhere (an anisotropic block, a bidegree-(1,1)
     term, an odd sub-orbit), the top variables lose ≈ a/p per prime. That is a loss of order a·log x per (top, lift),
     far beyond the budget. Integral surjectivity of theta is never proved (E1), and with HT weights ≈ b = e^{x^ε}
     everything is far outside Fontaine–Laffaille.
   - *Check.* Read `lemmaS` and `normalisedFamily_standardBases_integrality`. Compute v_p of a composite of two lifts
     (m = 2) at rank 4 with two tops.

**Points (b)–(d) of the brief, which I rank lower.**
- **(b) Would the argument prove something false?** Most of the tests asked about are vacuous, but one observation
  is substantive.
  - *Lower bounds.* None. Valuation lower bounds and size upper bounds only ever yield "not too many primes". One-sided
    Landau suits this, and there is no symmetric lower-bound proof to embarrass it.
  - *Split primes.* The gain there is 0 (ordinary reduction, and NUMTEST5's split control fails), so the count cannot
    be pointed at split primes. If it could, it would bound G_z + g_χ instead, which is no contradiction.
  - *Davenport–Heilbronn.* The arithmetic is used in step 3 (valuations at prime ideals of E), in step 6 (Kronecker
    limit formula ↔ L′/L(1, χ_{−d}), which uses the Euler product) and in step 12 (Artin reciprocity). A DH function
    has none of these, so the test is vacuous.
  - *Uniformity in d.* This is the substantive point. Steps 3–11 never use PairGood, only the zero boxes and
    |L′/L(1)| ≤ 4 log x. So the core claims an inert-count bound G_z − g_{χ_{−d}} − (ψ-twists) ≤ x^{1/2+O(ε)} for
    *every* admissible d. If the core is also uniform in d (fixed d across windows), it would imply GRH for
    L(s, χ_{−d}) to the right of its real zeros. That is not false, but the core is itself GRH-strength for χ_{−d}.
    Whether d must grow with Y for anything but PairGood is worth asking.
- **(c) Landau with windows.** I believe it (A2, step 14). The only care needed is the unique nearest pole and σ large
  for the tails, and the doc now says both.
- **(d) Removing split primes.** Sound in principle. For y ≪ log q the family has mean square ≈ y log y. The tail
  beyond Z needs a zero-free box and Z ≥ X^{2·400}, and the stated sizes give this. Two-sided use at one point is
  legitimate.

---

## A4. Paper checks

| check | result |
|---|---|
| U = \|TT\|mbδ/2 range | lower: (x^{−ε/8}·x^{2+8ε}/2)·x^{1/2−ε/16}·x^{−ε}/2 = x^{5/2+6.8125ε}/4; upper: 2x^{5/2+7.94ε}·b. **Matches** the table |
| balance x/m + m + k/n² | term 1: 4x(1+m²/k)/(mδ) ≤ 4x^{1/2+1.06ε}(1+o(1)) ≤ 8x^{1/2+2ε}. Term 2: 2f·m·x^ε/(\|TT\|δ) ≤ 16x^{1/2+2.06ε} ≤ 8x^{1/2+2.625ε} for large x. Term 3: 2k x^{2ε}/(n\|TT\|) ≤ 8x^{1/2−3.875ε}, within the stated 4x^{1/2+1.125ε}. Total ≤ 20x^{1/2+2.625ε}U. **Closes** |
| 9 = 5 + 3 + 1 | x^{5ε} (envelope) × 20x^{1/2+(13/8+1)ε} × (26 ≤ x^{3ε/8}) gives G_m − SigA ≤ x^{1/2+8ε}. Then (1+4o)x^{1/2+ε} + x^{1/2+8ε} ≤ x^{1/2+9ε}. **Closes** |
| Riesz weight from e = 1 | a_t/p − W = b(a_t/(bp) − 1) − (W − b) with W ∈ [b, b+η+1]. Plus the al/capU shifts, \|θ\| ≤ η+1+kaJ+c_G+2c_G/p. Summed over p ≤ x, \|TT\| tops and m lifts: poly(x)·\|TT\|m ≪ U√x since b ≫ poly(x). Also a_t/b = x(1 + O(x^{−17.5})). χ_{−d}(p^i) = (−1)^i for inert p, so only odd e count, consistent with the LT side. **Closes** |
| Chowla–Selberg constant | I computed γ + log(2π/√d) − L′/L(1, χ_{−d}) numerically and compared it with log(area/π) of the CM lattice normalised to \|g₂³ − 27g₃²\| = 1. d = 4: 1.476330 vs 1.476336. d = 3: 1.497499 vs 1.497505 (series error ~6·10^{−6}). **Confirmed** in that normalisation. It agrees with −L′/L(0, χ) + ½log d via the functional equation, i.e. with Colmez's h_Fal. The doc should say "|Δ| = 1 with Δ = g₂³ − 27g₃²" |
| Main ≈ m\|TT\|a·x^{ε/3} | log a − mean_ρ log w ≈ (1−δ)x^{ε/3} + δ·log x, since top and thin places have Riesz length ≈ X′. **Closes**; the signal is δ-diluted. Required precision is relative ≈ δx^{−1/2−ε/3} |
| eE family | Σ_{j,ρ} eE ≈ m·f·b·La ≈ B₀. Divided by U it is x^{O(ε)}. **Not** the m family (m·B₀ ∝ m²). Contradicts §5.1, §6.4, §9.5.1 and Correction 4 |
| logΩ residual | Σ_{j=1}^m (2j−1−m) = 0. At thick places w_j − w̄ = O(η), and top/thin caps are ≪ b. So the residual is poly(x)·m²·f·La ≪ b: **negligible**, not just a booking choice |
| n ≳ m⁴ | from k ≳ m⁵f, f = 2n and k/n² ≲ m: n ≳ 2m⁴ = x^{2−ε/4} ≤ x^{2+8ε}. **Closes** |
| LoP/ASK | C·x^{−1−ε/3}. **Closes** |

---

## A5. Ten questions for the author, most important first

1. **Metric sharpness of the Bost step.**
   - Is ⊕_u B_u : ⊕N_u → RR^∨ used as a near-surjection? What are Σ_u d_u and D?
   - The frame is a rank statement. Which hypothesis makes the joint map, with the metrics used in s, near-isometric
     to relative x^{−1/2}?
   - The chain forces log‖B_u‖_true = h(u) − O(U x^{1/2}). What makes the m-fold jet composite extremal on the Bessel
     image, and |a_u| uniform in u at each archimedean place?
2. **Which step's actual loss is ≳ min(m, √x)·|TT|·b per lift?** eE and the p-adic losses are m-independent. Is the
   construction valid at m = x^{0.9}? If so, which loss grows with m, and why can it not be improved?
3. **T_u.**
   - Why does the top Bessel functional at level T_u have archimedean norm ≈ T^{−a_t}, while its T-adic denominators
     cost only m·EatT?
   - Why log T* = (1/(fk))log(D*/d*_u)?
   - What bounds T above?
4. **One normalisation.** Is there one lemma that identifies the Fock (pairK), Rallis-hook and layer-covolume metrics,
   with constants, so that the k·f·b·logΩ terms cancel exactly?
5. **Theorem S.**
   - What are the open hypotheses of `theoremS_selected_of_loops`?
   - How does the double unfolding avoid continuous-spectrum contributions?
   - Why is relative precision b^{−6} needed when the frame tolerance is polynomial?
6. **The kernel law at rank ≈ x^{399}.**
   - Give a written proof of `lemmaS` and the IsSg branch.
   - Has the valuation of a two-lift composite ever been computed?
7. **Uniformity in d.** Does any step of 3–11 use the host selection beyond the zero boxes and |L′/L(1)| ≤ 4 log x? If
   not, does the method also give one-sided GRH-strength bounds for G_z − g_{χ_{−d}} at fixed d?
8. **E1/E2 sizes.** Is E1's index (≈ m·B₀) genuinely that large, or is it a bound? What does TopCore assert for HT
   weights ≈ e^{x^ε} at primes l ≪ b, and is there a known special case?
9. **The Ш bound.** Since √b = e^{x^ε/2} dwarfs any poly(x) bound, why do crude K-theoretic bounds fail? Is it only
   the lack of regulator lower bounds for plus parts? Why is a U(3) R = T theorem needed?
10. **Design.** Why does t have the shape of §1? Why the 3 in the shares? Why must D_all be exponentially precise?

---

## B. Fidelity spot-check (six claims)

| # | doc claim | node(s) checked | verdict |
|---|---|---|---|
| B1 | §0 step 2 / §2.3: one (q, d) per window; bounds on all of [Y, X]; orthogonality, "neither GRH nor the large sieve"; Siegel only via n* and zero boxes | HOSTSEL §0–1 | **Supported.** The node also records `boxes` and the tail identity g = −S − y·tail(Z). The doc could add that the tail bound is what needs the zero-free box |
| B2 | §0 step 3 / §4.3: the e = 1 term is the Riesz weight; LP duality "read in full" | ENGINE2 §0, §1.2, children table | Riesz derivation **supported**, and it is marked as ENGINE2's own inference, correctly. **Overstated:** ENGINE2 read `rowRadiusAssembly` only to CLR:299, "the final assembly lines 300+ not read". `lemmaS`, `PureCross` and `ExpWtLe` are statement-only, as the doc says |
| B3 | §0 step 5 / §5.4: Bk_u(N_u) ⊆ cc is the actual divisibility; "GATIE found no slack" | GATIE §0, §2d, children | **Supported**: same fields on both sides, adm2 via `val2AllAtRF`. GATIE lists the adm11 producer as "core, body not read". The doc's §9.4 says ADM11 later read it; newer wins, which is consistent |
| B4 | §5.1 / §6.4 / Correction 4: eE is "a genuine per-lift loss in the 'm' family" and the first candidate for tightness | STEPE §0 item 2, l.122, l.247 | **Faithful to the node, but the node is wrong.** STEPE sums eE to ≈ m·f·b·La and calls it "≈ m·B₀-sized". Since B₀ = f·m·b·x^ε, that sum is ≈ B₀. STEPE's own l.247 says "≈ f·b·La per level", which is m-independent. The doc propagates the slip into its central conceptual question (§9.5.1) |
| B5 | §0 step 7 / §5.3 / §7: Bost rank-free; the frame gives near-surjectivity; Theorem S conditional | RANK §0 | **Supported, and understated in one respect.** RANK says the frame hypothesis "carries no metric content" (Y_u, Y′ are free invertible matrices) and is used only for rank. The doc calls η, ē "frame-tightness parameters" and does not say that no metric near-isometry enters. That fact matters for A3 point 1 |
| B6 | §0 step 8–9 / §2.2: T_u "one prime per word u, sets the level of the source forms"; Count5 at relative 1/m | LEDGER L5 and oddity 2; DIVKEY §2.4; HEIGHT §2(a); ADM11 input 5 | **Understated.** The nodes say: hA = −Σ_t a_t log T is the top Bessel functional "scaled by T^{−deg}"; T is a prime in [T*, (1+1/(fk))T*] with log T* = (1/(fk))log(D*/d*_u); b^{m/2} ≤ T, log T ≤ cCount·m·L; EatT ≤ 12fb. The −a·log w and −a·log(π/v) terms are matched "through log T(u)", and lowB's producer is unread. None of this is in the doc, although it is where the scale x enters the archimedean side |

Also checked in passing: CHBALANCE bounds the replacement errors by ≈ x^{1/4+ε}·U. The doc says "≲ x^ε·log x relative to
U". Both are harmless, but they disagree.

---

## C. Against the first review

**Holes H1–H5.**
- **H1** (det ι). *Resolved in the exposition*: now `SpecDet`, proved from partwise similitudes with equal dimensions.
  Statement-level below that (AForm/BForm, Siegel–Weil), which is stated.
- **H2** (seesaw supplier). *Resolved, conditionally*: a 20-step trace exists. The supplier's own hypotheses remain.
- **H3** (twisted places). *Resolved by restatement*: Tw has no cutoff, its cost sits in E1, and E2 must hold at
  every l.
- **H4** (signatures). *Partly resolved*: they are forced by `arithAt`, and DIV uses only |p_j − q_j − k| ≤ m. The
  conceptual question H4 pointed at (where the m-growth comes from) **remains**, and the new candidate list answers it
  wrongly (B4).
- **H5.** *Withdrawn correctly.*

**The ten edits.**

| edit | status |
|---|---|
| 1 notation | largely done: notation box; Y, n/r, HH/H_B, q/q_v, ε/ω and χ_d/χ_{−d} fixed; \|TT\| sized. **Remaining or new collisions:** Φ is still the Laplace transform (§2.1) and the Schwartz datum (§4.1); §2.1 uses U, W, δ, k and γ for the window, Taylor index and imaginary part, clashing with the signal unit, words, thick fraction, rank and Euler's constant; η is the frame tightness, the polynomial parameter and the cap width; t has three meanings by declaration |
| 2 one-lift model computation | **not done.** There are slogans (§1, §5.4 "one Chebyshev identity"), but no displayed single-jet product-formula inequality with the leading-order identity |
| 3 define θ_{c,c′} | mostly done (§4.1). U_x, Φ̂, A, B and SS are still opaque |
| 4 where non-top ph goes | **done** (§5.1, `stepE_num`) |
| 5 downgrade det ι | superseded by SpecDet |
| 6 orbit-route coverage | **done** (§4.6 table, SERVED's three bookings) |
| 7 precision-critical hypotheses | **done** (§5.4 list; "only an upper bound on μ(RR^∨)") |
| 8 §4.4 display | **done** (Σ_j; composition; intermediate metrics, marked inferred) |
| 9 promote sharpness | **done**, but the content is now partly wrong (B4, and the next list) |
| 10 smaller items | Landau sentences done; purity source done; ONECHARU's regulator reason **still missing** ("crude bounds do not suffice" with no reason); stale unread lists refreshed; audit history partly moved to the end |

**New problems introduced by the rewrite.**
1. **eE misclassified** as m-family, and EComp5 listed as a candidate although the §6.3 table gives its real size as
   m-independent ("looser than the real sizes by ≈ m·x^{2ε/3}"). The doc is internally inconsistent here.
2. **The sharpness argument is stated too strongly** (§6.4).
   - "G_m(x) ≥ c√x occurs in every window, where the chain must be tight to x^{o(1)}" ignores SigA: the relevant
     signal is G_m − SigA, the inert-count fluctuation.
   - The tightness is x^{9ε}, not x^{o(1)}.
   - "Some per-lift loss must truly be ≍ m" holds only if the construction is valid for m ≫ √x. What is forced is a
     per-lift loss ≳ min(m, √x)·|TT|·b.
3. **"In the Lean this holds by definition (the same `logOm` symbol)"** (§5.4) reads as if the x^{−4} precision were
   free. The shared symbol makes the cancellation syntactic. The truth of L6 and D2 at that precision is the claim.
4. **T_u is now a silent load-bearing object.** The rewrite foregrounds Count5's precision, but never says that
   −a_t log T_u carries the scale-x part of Main (B6).
5. "LP duality read in full" overstates (B2).
6. **New notation collisions in the rewritten §2.1** (edit 1 above).

---

## Verdict on the exposition

**UNDERSTANDABLE WITH GAPS.**

A number theorist can now follow:
- the analytic shell;
- the bridge;
- the local p-adic mechanism;
- the ledger algebra;
- the error balance.

These can be re-derived on paper, and I re-derived them. Three things cannot be reconstructed from the doc:
- how the scale x enters the archimedean side (T_u, Count5);
- what makes the Bost step metrically sharp, given a rank-only frame;
- which inequality carries the √x barrier. The doc's leading answer is arithmetically wrong.

---

## Reviewer's opinion on the argument as described

**What I believe.** The windowed Landau lemma, the host selection by orthogonality over huge conductors, the finite
Fourier bridge with 4 : 3 shares and the exact identity L7 are correct, or correct in principle, and cleverly
arranged. They reduce GRH for ⟨ψ⟩ to an inert-prime Chebyshev inequality at relative precision x^{−1/2}. The local
p-adic mechanism (supersingular LT divisibility with self-Gaussian cancellation on split hermitian spaces, capped by
minors) is real at small rank, and NUMTEST5 supports it.

**What I doubt.**
- The argument is a chain of one-sided inequalities in which terms of size x^{4.5}·U cancel. The conclusion forces
  every link to be tight to relative x^{−1/2}, and even unconditionally to roughly x^{−3.5} of the large terms. This
  includes the Hadamard defect of Bost, the submultiplicativity of m composed jet operators, the uncomputed seesaw
  constant and the three metric normalisations. For none of these does the doc describe a mechanism that delivers
  such tightness. The near-orthogonality theorem, the obvious candidate, is used only for rank.
- The step that must genuinely lose √x is unidentified, and the leading candidate is excluded by size.
- The most novel inputs are statement-only or conditional: the kernel law at rank x^{399}, Theorem S at precision
  e^{−6x^ε}, TopCore for weights e^{x^ε}, and U(3) R = T.

For a claimed proof of GRH this pattern is what I would expect if a black box is false. On present evidence I consider
the argument very unlikely to be correct, and the likeliest failure is in steps 6–8 rather than in the analytic shell.

**What would change my mind.**
- (i) A toy computation (m = 2, small rank) showing that the composite jet/Bessel map is extremal and near-isometric
  to high relative precision, and that the three metrics agree in their logΩ coefficients.
- (ii) An identified step whose actual loss is provably ≳ √x·|TT|·b per lift, with a reason tied to prime
  fluctuations.
- (iii) A written, checkable proof of the T_u mechanism, including what bounds T above.
- (iv) Theorem S and the kernel law read to classical leaves.

---

## Prioritised edits (≤ 10)

1. **§5.1, §6.4, §9.5.1, Correction 4.** eE totals ≈ B₀ (m-independent per lift) and contributes x^{O(ε)}, not √x.
   Drop it, and EComp5, from the tightness candidates. State that the remaining candidates are the covolume q-error,
   E1 and E2.
2. **§6.4 sharpness, restated correctly.** Use G_m − SigA, tightness x^{9ε}, and a forced per-lift loss
   ≳ min(m, √x)·|TT|·b if the construction is valid for larger m. Add the forced-rigidity principle: total actual
   slack ≤ U·x^{1/2+9ε}, and unconditionally ≲ relative x^{−3.5} of the cancelling terms.
3. **§2.2, §5.4: explain T_u.**
   - Its size: log T ≈ m·x^ε, b^{m/2} ≤ T.
   - Its definition from log(D*/d*_u)/(fk).
   - That −a_t log T_u supplies −a·mean log w, the scale x.
   - hA as "Bessel functional scaled by T^{−deg}", the T-adic cost m·EatT, and what bounds T above.
   - That lowB's producer is unread.
4. **§5.3/§7: metric content of the frame.** Say that the frame is a rank statement, and that the ranks and direction
   are near-surjective (give Σd_u vs D). State plainly that the doc does not identify what controls the Hadamard
   defect and h_bound − h_true, both of which the conclusion forces to be tiny.
5. **§5.4.** Replace "holds by definition (the same `logOm` symbol)" with "cancels syntactically; the truth of L6/D2
   to relative x^{−4} is a separate claim resting on [list of unread inputs]".
6. **Add the one-lift worked display** (first review, edit 2): a single jet, the product formula, the leading-order
   identity, and where floors versus Riesz weights and caps enter.
7. **Notation.** Rename the Laplace transform (§2.1) and the Schwartz datum (§4.1) away from Φ. Rename §2.1's U, W,
   δ, k and γ, and disambiguate η.
8. **§4.3, §9.1.** Change "LP duality read in full" to "read to CLR:299; final assembly unread".
9. **§8.** Give ONECHARU's reason crude bounds fail, and say why poly(x)-size K-theoretic or ETNC bounds, which would
   be far below √b, are not available.
10. **Small consistency fixes.**
    - §2.3: reconcile the replacement-error size with CHBALANCE (≈ x^{1/4+ε}·U).
    - §6.4: call the logΩ residual negligible, not just a booking choice.
    - §5.1: state the Chowla–Selberg normalisation (|g₂³ − 27g₃²| = 1).
    - Add the observation that steps 3–11 never use PairGood, so the core is GRH-strength for χ_{−d} itself.
