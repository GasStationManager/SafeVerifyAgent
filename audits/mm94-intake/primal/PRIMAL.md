# A primal (explicit) construction behind the 9/4 proof

Status: a derivation by one Claude model (Fable 5.1) on 2026-10-08, after the read-through
in `../../2026-10-08-openai-math-MatrixMultiplication-9-4.md`. Every tensor degeneration it
uses is one the paper states and the Lean artifact proves; what is new is the way they are
combined, and that combination has been checked only by the LP arithmetic below and by my
own reading. It has NOT been reviewed by another model family or formalised. Treat it as a
proposal with evidence, not a result.

## 1. Claim

For every integer a ≥ 2 there is an explicit finite recipe of degenerations, built from the
paper's Proposition 3.1 (Fourier separation), Lemma 4.1 (determinant filtration) and Lemma 4.2
(three sectors), which proves

    S(a,a) ⊗ T_A  ≳  T_{A·D*(a)²}        (asymptotic degeneration, for an explicit A),

where S(a,b) = ⊗_{π∈S₃} C(a,b)^π is the six-fold leg-symmetrised polynomial multiplication
tensor (rank ≤ (a+b−1)⁶) and D*(a) = ((3a−1)/2)·∏_{m<a}(1+1/(3m)) is the paper's own growth
bound. With Bini's interpolation and Schönhage's bootstrap this gives an explicit (galactic)
family of algorithms with

    ω ≤ 3·log(2a−1) / log D*(a),

which is 2.7375 at a = 2, 2.4927 at a = 10, 2.3864 at a = 100, 2.37111 at a = 190 (below the
2.371177 the paper cites as the current record), and tends to 9/4 as a → ∞.

Concretely at a = 2: six copies of 2×2 polynomial multiplication on permuted legs, tensored
with a 9×9 matrix multiplication, asymptotically degenerate to a 100×100 matrix
multiplication, S(2,2) ⊗ T₉ ≳ T₁₀₀. Rank of the left is 3⁶·R(T₉); so ω ≤ log(729·9^ω)/log 100,
i.e. ω ≤ 3 log 3 / log(10/3) = 2.7375.

## 2. Why the dual proof contains the primal construction

Write L(a,b) = log λ(S(a,b)) for a character λ with mean dot-product exponent t. The three
inequalities the paper feeds into Lemma 5.1 are, for every word type q = (q₊, q₋):

    (E_{a,b,q})   L(a,b) + 6t·log 2  ≥  6t·H(q) + q₊·L(a,b+1) + q₋·L(a,b−1)
    (F_{a,h})     L(a,3h+a−1)        ≥  6t·log 3 + L(a,h)
    (B)           L(1,b) = L(b,1) = 6t·log b,     L(a,b) = L(b,a)

(E) is Lemma 4.1's degeneration followed by Corollary 3.2 at the FIXED type q, on all six
legs; the paper then takes the envelope over q, which is what makes the profile
P = exp(L/6t) concave. (F) is Lemma 4.2 with the uniform type. Lemma 5.1 is real arithmetic
on P with subtraction, which is why the paper's chain has no tensor meaning.

But the family (E) ∪ (F) ∪ (B) is LINEAR in (L, t) and homogeneous, and the conclusion
L(a,a) ≥ 8t·log a is linear too. So Lemma 5.1 is a linear-programming implication, and by
LP duality it has a certificate: nonnegative multipliers w on finitely many (E), (F) whose
sum is the conclusion, as an identity of linear forms. Each multiplied constraint is a
degeneration; a nonnegative combination in log-space is a TENSOR PRODUCT of the
corresponding degenerations; a variable that cancels between the two sides is a common
TENSOR FACTOR, i.e. a catalyst. Nothing in the certificate is a subtraction.

Three facts make the certificate usable as a construction:

1. Degenerations are compatible with ⊗ and ⊕, so the product of the multiplied
   degenerations is a single degeneration  Cat ⊗ X ⇝ Cat ⊗ Y.
2. Catalysts are free for asymptotic rank: Cat ⊗ X ⇝ Cat ⊗ Y gives Cat ⊗ X^{⊗n} ⇝ Cat ⊗ Y^{⊗n}
   by applying it n times, hence R̲(Y^{⊗n}) ≤ R(Cat)·R(X)^n with R(Cat) independent of n.
   The direct-sum multiplicities ⟨M⁶⟩ (M ≈ e^{N·H(q)}) that Proposition 3.1 leaves on both
   sides are catalysts of this kind; the ⟨5⁶⟩ per use is an O(1/N) loss in the exponent.
3. The matrix-multiplication factors T_A that remain are handled by Schönhage's bootstrap:
   from S(a,a)^{⊗k} ⊗ T_A ≳ T_B with R(S) ≤ (2a−1)⁶ one gets, using any current algorithm
   for T_A, a better one for T_B, and the iteration's fixed point is
   ω* = 6k·log(2a−1)/log(B/A), with no loss.

So the question "find a primal construction" is answered by solving the LP and reading off
the dual. The dual proof informs the primal construction in a precise sense: by
complementary slackness, the certificate uses exactly the constraints that are tight on the
paper's extremal profile, so the separation types are read off that profile:

    q*(a,a) = (3a+1)/(6a−2),      q*(a,b) = (a+2b+1) / (2(a+2b−1))  for a < b ≤ 4a−2,

a separation slightly biased towards the longer polynomial, and one tripling per row at
h = a−1 (C(a,4a−4) into three copies of C(a,a−1)).

## 3. The LP and what it returned

`lp_cert.py` (grid of types q) and `lp_exact.py` (the q* above only) build the LP with
variables L(a,b), 2 ≤ a ≤ a₀, a ≤ b ≤ 4a−1, constraints (E_{a,b,q}) for a ≤ b ≤ 4a−2,
(F_{a,h}) for h ≤ a, monotonicity L(a,b) ≤ L(a,b+1) (never used), boundary values substituted,
t = 1 (homogeneity), objective min L(a₀,a₀). Results (HiGHS):

| a₀ | variables | constraints | LP minimum | 6·log D*(a₀) | certificate size | ω ≤ |
|---|---|---|---|---|---|---|
| 2 | 6 | 12 | 7.223837 | 7.223837 | 3 | 2.73747 |
| 3 | 15 | 31 | 10.968763 | 10.968763 | 9 | 2.64113 |
| 5 | 42 | 90 | 15.438877 | 15.438877 | 30 | 2.56172 |
| 10 | 162 | 357 | 21.262200 | 21.262200 | 135 | 2.49268 |
| 30 | 1,392 | 3,112 | 30.232217 | 30.232217 | 1,305 | 2.42773 |
| 100 | 15,147 | 34,017 | 39.926598 | 39.926598 | 14,850 | 2.38637 |
| 190 | 54,432 | 122,352 | 45.074087 | 45.074088 | 53,568 | 2.37111 |

The LP minimum equals the paper's 6·log D* to solver precision at every size (so the
linearised family loses nothing against the envelope), the dual's identity
Σ w_i·row_i = e_{(a₀,a₀)} holds to 1e-15, and with the type grid instead of q* the optimum
is lower, as a relaxation must be. The certificates are in `certs/` (JSON: constraint,
type, weight). Only (E) and (F) carry weight; monotonicity never does.

Exact rational certificates (`exact_cert.py`, sympy over the LP support):

    a₀ = 2:  20·(E_{2,2, q=7/10}) + 14·(E_{2,3, q=9/14}) + 9·(F_{2,1})     [÷15]
    a₀ = 3:  80·E_{2,2,7/10} + 224·E_{2,3,9/14} + 144·F_{2,1} + 280·E_{3,3,5/8} + 280·E_{3,4,3/5}
             + 252·E_{3,5,7/12} + 196·E_{3,6,4/7} + 112·E_{3,7,9/16} + 63·F_{3,2}        [÷168]

## 4. The a₀ = 2 construction, written out

Per unit of the tensor power N (all exponents multiply by N; N a multiple of 420 makes
every Nq and the three multinomials integral):

  (i)   20 × Lemma 4.1 at (2,2), type 7/10:
        ⟨(5M₁)^{120}⟩ ⊗ (S(2,2) ⊗ T₂^{⊗2})^{⊗20N}  ⇝  ⟨M₁^{120}⟩ ⊗ T_{M₁}^{⊗40} ⊗ S(2,3)^{⊗14N} ⊗ S(2,1)^{⊗6N},
        M₁ = C(N, 0.7N)
  (ii)  14 × Lemma 4.1 at (2,3), type 9/14:
        ⟨(5M₂)^{84}⟩ ⊗ (S(2,3) ⊗ T₂^{⊗2})^{⊗14N}   ⇝  ⟨M₂^{84}⟩ ⊗ T_{M₂}^{⊗28} ⊗ S(2,4)^{⊗9N} ⊗ S(2,2)^{⊗5N},
        M₂ = C(N, 9N/14)
  (iii) 9 × Lemma 4.2 at (2, h=1):
        ⟨(5M₃)^{54}⟩ ⊗ S(2,4)^{⊗9N}                 ⇝  ⟨M₃^{54}⟩ ⊗ T_{M₃}^{⊗18} ⊗ S(2,1)^{⊗9N},
        M₃ = N!/((N/3)!)³

Tensoring (i)–(iii) and using S(2,1) = T₂^{⊗2}:

    ⟨5^{258}⟩ ⊗ Cat ⊗ S(2,2)^{⊗15N} ⊗ T_{2^{68N}}   ⇝   Cat ⊗ T_{B_N},
    Cat = ⟨M₁^{120} M₂^{84} M₃^{54}⟩ ⊗ S(2,3)^{⊗14N} ⊗ S(2,4)^{⊗9N} ⊗ S(2,2)^{⊗5N},
    B_N = 2^{30N} · M₁^{40} · M₂^{28} · M₃^{18}.

Sizes: log B_N = N·(30 log 2 + 40 H(7/10) + 28 H(9/14) + 18 log 3) − O(log N) = 83.253 N − O(log N),
against 68 N·log 2 = 47.134 N on the left; the difference 36.119 N = 30 N·log(10/3) is
15 N times log D*(2)². Catalytic cancellation and the bootstrap give, as n → ∞ then N → ∞,

    ω ≤ 90 log 3 / (83.253 − 68 log 2) = 2.7375.

Every object here is explicit: the degenerations are the paper's (with the Lean's
`separationPolynomial`, `adaptedTensor` and sector weights as the maps), the word selections
are restrictions, Bini's interpolation turns the composed degeneration (degree polynomial
in n for fixed N) into a rank decomposition. No choice is made anywhere.

## 5. Sanity checks

- Known spectral points. Any character must satisfy λ(S(a,a)) ≥ D*(a)^{2(p_X+p_Y+p_Z)}. The
  flattening ranks give a⁴(2a−1)² and the quantum functionals (support functionals, C(a,a)
  being tight) give at least 2^{2(H(i)+H(j)+H(i+j))} at the uniform distribution. Both
  exceed D*(a)⁴ for every a tested (`spectral_check.py`, a ≤ 30); at a = 2 the quantum
  functional gives 128 against 123.5, a 3.7% margin, which is the near-tightness one
  expects (the paper's extremal profile at a = 2 is 10/3 ≈ 3.33 against the quantum
  functional's 128^{1/4} ≈ 3.36).
- The LP reproduces D* exactly; the exact rational certificate at a₀ = 2 agrees with a hand
  computation.
- The bound ω(a₀) → 9/4 only logarithmically (gap ≈ 9/4·log 2/log a₀): 2.3075 at a₀ = 10⁵.

## 6. What is NOT established, and what would establish it

1. The primal reading of (E) and (F). I read the paper's Lemma 4.1 proof, Corollary 3.2's
   proof and Proposition 3.1 as the degeneration chain in §4; readers D and E confirmed
   each piece is executed explicitly in Lean. The six-leg bookkeeping (T₂^{⊗2} on the left,
   T_M^{⊗2} on the right, ⟨(5M)⁶⟩ and ⟨M⁶⟩) is mine. An error here would most likely show as
   a violation by a known spectral point; none appears, but that is evidence, not proof.
2. Catalysts being free and the bootstrap being lossless are standard arguments (Strassen;
   Schönhage's asymptotic sum inequality) that I reproduced from memory in §2; a referee
   should check them against Bürgisser–Clausen–Shokrollahi §15.
3. Nothing here improves on the paper: the finite-a₀ bounds are exactly its own intermediate
   bounds, made primal. The construction is galactic in the same sense as every laser-method
   algorithm (N and n → ∞), and no explicit coefficient set has been written down.
4. The decisive check is a formalisation of the a₀ = 2 chain on top of the artifact: the
   statement "for all N ≡ 0 mod 420, ⟨5^{258}⟩ ⊗ Cat ⊗ S(2,2)^{⊗15N} ⊗ T_{2^{68N}}
   degenerates to Cat ⊗ T_{B_N}" is a finite composition of lemmas the Lean already has
   (`PolynomialRestrictionDegeneration`, the explicit separation polynomial, the adapted
   tensor, the sector weights); a second theorem turning it into an explicit border-rank
   bound on T_{B_N^n} is the Schönhage/Bini step. Independent review by a different model
   family of §2's three facts and of §4's bookkeeping is the cheap first step.

## 7. Corrections and additions (2026-10-09, after an independent review)

An independent review (ReadingGroup, `brainstorms/mm94-primal-review-and-general-certificates.md`)
found three errors in the exposition and supplied the missing general argument. Nothing in §4's
construction or in the Lean development changes.

1. §1's sentence "hence R̃(S(a,a)) ≥ a^8" is false (R̃ ≤ R ≤ (2a−1)^6). The correct chain is, per
   character, 8t·log a ≤ log λ(S(a,a)) ≤ 6 log(2a−1), hence t ≤ 3/4.
2. §5's "3.7% margin at a = 2 against the quantum functional" evaluated the support functional at
   the uniform distribution, a lower bound. Its maximum at uniform θ is attained by a distribution
   with uniform marginals ((1/3,1/6,1/6,1/3) at a = 2; one exists for every a ≤ 30 by LP
   feasibility), equals the flattening value a⁴(2a−1)², and gives a 16.6% margin at a = 2 growing to
   5× at a = 30. `spectral_check.py` now reports both numbers.
3. §6.3's "no explicit coefficient set" stands, but §6's item 3 (certificates exist only numerically
   for a₀ > 3) is superseded: the dual weights are the expected visit counts of an absorbing Markov
   chain on the tight rows (E at q* for a ≤ b ≤ 4a−5, F at h = a−1), the profile
   P*(a,b) = ((a+2b−1)/2)·∏_{m<a}(1+1/(3m)) is feasible for the full system, and so the LP optimum is
   exactly 6 log D*(a₀) at every a₀ with an exact rational certificate. `chain_certificate.py`
   computes it row by row (O(a₀²)): a₀ = 2 and 3 reproduce §3's certificates; a₀ = 190 gives 53,865
   rows in one second with a 186-digit common denominator. The bound ω(a₀) crosses 2.371339 at
   a₀ = 188 and 2.371177 at a₀ = 190.
4. The LP improvement direction in any search: adding a valid constraint can only RAISE the minimum
   v = min L(a₀,a₀), and the bound is 18 log(2a₀−1)/v, so a larger optimum is better; a nonzero dual
   multiplier is not an improvement criterion.
