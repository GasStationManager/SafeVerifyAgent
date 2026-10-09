# Review brief: does the LP dual of the 9/4 growth lemma give an explicit construction?

This is a request for an adversarial review by a reader who did NOT produce the claim. It is
self-contained: you need the paper "An Upper Bound of 9/4 for the Matrix Multiplication
Exponent" (OpenAI, 2 Oct 2026, 12 pages; `github.com/openai/math`, preprint
`Matrix-Multiplication-Nine-Fourths-October-2-2026`) and standard facts about tensor rank
(Bürgisser–Clausen–Shokrollahi, *Algebraic Complexity Theory*, chapter 15). The claim under
review is in `PRIMAL.md` (same directory); this brief states it again with every step
numbered so that you can say exactly which step you reject. Please answer the numbered
questions in §5 and nothing else is required. Do not trust anything here because it is
written confidently; the author is a language model and has been wrong before.

## 1. Notation (the paper's)

- Tensors are trilinear forms over ℂ with legs X, Y, Z. A ≥ B means B is a restriction of A
  (independent linear substitutions on each leg). A ⇝ B is degeneration (B is the lowest-
  weight part of A after integer weights on coordinates). A ≳ B (asymptotic) means
  A^{⊗n} ≥ 2^{o(n)}·B^{⊗n} as full direct sums, for large n. R(A) is rank, R̲(A) border
  rank, R̃(A) = lim R(A^{⊗n})^{1/n} asymptotic rank. ⟨m⟩ is the direct sum of m scalar
  multiplications; A ⊕ B is a full direct sum (disjoint variables on all three legs).
- T_n = Σ x_ij y_jk z_ki is n×n matrix multiplication; R̃(T_n) = n^ω. T_m ⊗ T_n ≅ T_mn.
- B_X(m) = x·Σ_i y_i z_i is the dot product with the singleton on the X leg; B_Y, B_Z
  cyclically. B_X(m) ⊗ B_Y(m) ⊗ B_Z(m) ≅ T_m (paper, (2.4)). B_X(m) ⊗ B_X(n) ≅ B_X(mn).
- C(a,b) = Σ_{i<a, j<b} x_i y_j z_{i+j} is polynomial multiplication; R(C(a,b)) = a+b−1.
  C(1,b) ≅ B_X(b). C(a,b)^π is C(a,b) with legs permuted by π ∈ S₃.
- S(a,b) := ⊗_{π∈S₃} C(a,b)^π, the six-fold symmetrisation; R(S(a,b)) ≤ (a+b−1)⁶;
  S(a,b) ≅ S(b,a); S(1,b) ≅ T_b ⊗ T_b.
- A character λ is an additive, multiplicative, restriction-monotone map to ℝ≥0 with
  λ(1) = 1 (Strassen's spectral points). For each λ there are p_X, p_Y, p_Z ∈ [0,1] with
  λ(B_X(m)) = m^{p_X} etc., and t := (p_X+p_Y+p_Z)/3, so λ(T_m) = m^{3t} and
  λ(T_m ⊗ T_m) = m^{6t}.
- D*(a) := ((3a−1)/2)·∏_{m=1}^{a−1} (1 + 1/(3m)); the paper's Lemma 5.1 proves the
  profile P(a,a) ≥ a^{4/3} through the chain whose exact value is D*(a) (so P(a,a) ≥ D*(a)).

## 2. The three primal inputs (each a theorem of the paper, each formally verified)

(P1) Separation, paper Prop. 3.1. If A = Σ_{h=1}^M A_h with the A_h sharing the X leg and
having pairwise disjoint Y- and Z-sectors (no cross terms), then
      ⟨5M⟩ ⊗ A  ⇝  ⊕_{h=1}^M (A_h ⊗ B_X(M)).
(P2) Fixed-type words, from the proof of paper Cor. 3.2. For such an A, N ≥ 1 and a type
q = (q₁..q_s) with Nq_i integers, restricting A^{⊗N} on the Y and Z legs to the words of
type q (a restriction, since it zeroes coordinates) gives a shared-X sum of
M_q = N!/∏(Nq_i)! blocks, each block isomorphic to ⊗_i A_i^{⊗Nq_i} (reordering factors).
(P3a) Determinant filtration, paper Lemma 4.1: C(a,b) ⊗ B_X(2) ⇝ [C(a,b+1) +_X C(a,b−1)],
a shared-X sum of two blocks with disjoint Y, Z sectors (a ≥ 1, b ≥ 2).
(P3b) Three sectors, paper Lemma 4.2: C(a,3h+a−1) ⇝ [C(a,h) +_X C(a,h)^σ +_X C(a,h)],
σ exchanging legs Y and Z, three blocks sharing X (a, h ≥ 1).

## 3. The derived primal inequalities (the author's reading; please check)

Applying (P3a), then (P2) at type q = (q₊, q₋), then (P1), on each of the six leg
permutations π with the SAME q, and tensoring the six results:

(E_{a,b,q})  ⟨(5M)⁶⟩ ⊗ (S(a,b) ⊗ T₂ ⊗ T₂)^{⊗N}  ⇝  ⟨M⁶⟩ ⊗ (T_M ⊗ T_M) ⊗ S(a,b+1)^{⊗Nq₊} ⊗ S(a,b−1)^{⊗Nq₋},
             M = C(N, Nq₊).

Here T₂ ⊗ T₂ = ⊗_π B_X(2)^π and T_M ⊗ T_M = ⊗_π B_X(M)^π; ⟨(5M)⁶⟩ is the product of the six
⟨5M⟩'s. Similarly from (P3b), (P2) at the uniform type, (P1):

(F_{a,h})    ⟨(5M)⁶⟩ ⊗ S(a,3h+a−1)^{⊗N}  ⇝  ⟨M⁶⟩ ⊗ (T_M ⊗ T_M) ⊗ S(a,h)^{⊗N},   M = N!/((N/3)!)³,

using that ⊗_π (C^σ)^π ≅ S (σπ runs over S₃). Taking a character and N-th roots gives
exactly the paper's inequalities 2^{p_X}λ_π(C(a,b)) ≥ e^{p_X H(q)}λ_π(C(a,b+1))^{q₊}λ_π(C(a,b−1))^{q₋}
multiplied over π, and λ_π(C(a,B)) ≥ 3^{p_X}λ_π(C)^{2/3}λ_π(C^σ)^{1/3} multiplied over π.

## 4. The argument

Step 1 (LP). With L(a,b) := log λ(S(a,b)), every constraint in §3 is linear in (L, t):
  (E) L(a,b) + 6t log 2 ≥ 6t H(q) + q₊ L(a,b+1) + q₋ L(a,b−1);  (F) L(a,3h+a−1) ≥ 6t log 3 + L(a,h);
  (B) L(1,b) = 6t log b;  symmetry L(a,b) = L(b,a).
The paper's Lemma 5.1 derives L(a,a) ≥ 8t log a from the envelope over q of (E) plus (F),
(B). An LP (`lp_exact.py`) with constraints (E) only at the types
  q*(a,a) = (3a+1)/(6a−2),  q*(a,b) = (a+2b+1)/(2(a+2b−1)) for a < b ≤ 4a−2,
(F) for h ≤ a, and (B), minimising L(a₀,a₀), returns exactly 6·log D*(a₀) at every a₀
tested (2 … 190), and its dual multipliers w ≥ 0 satisfy Σ w_i·(constraint_i) ≡ L(a₀,a₀) − 6 log D*(a₀)
as an identity of linear forms (verified to 1e-15; exactly in rationals for a₀ = 2, 3).

Step 2 (reading the certificate as tensors). Multiply the degenerations (E), (F) with
multiplicities w_i·N (integers after clearing denominators). Degenerations are compatible
with ⊗ and ⊕, so this is one degeneration  Cat ⊗ X ⇝ Cat ⊗ Y  where every S(a,b) whose
coefficient cancels in the identity, and every ⟨M⁶⟩, is a common factor (Cat), and what
remains is X = ⟨5^c⟩ ⊗ S(a₀,a₀)^{⊗kN} ⊗ T_A, Y = T_B with log(B/A) = (k/3)·6·log D*(a₀)·N·(1 − O(log N/N)).

Step 3 (catalysts are free). From Cat ⊗ X ⇝ Cat ⊗ Y, applying it n times gives
Cat ⊗ X^{⊗n} ⇝ Cat ⊗ Y^{⊗n}, so R̲(Y^{⊗n}) ≤ R(Cat)·R(X)^n with R(Cat) independent of n,
hence R̃(Y) ≤ R̃(X) (apply to X^{⊗m}, take roots).

Step 4 (bootstrap). R̃(T_B) ≤ R̃(S(a₀,a₀))^{kN} · R̃(T_A) ≤ (2a₀−1)^{6kN} · A^ω, and
R̃(T_B) = B^ω, so (B/A)^ω ≤ (2a₀−1)^{6kN}, i.e. ω ≤ 3·log(2a₀−1)/log D*(a₀) as N → ∞.
Explicit version: any explicit algorithm for T_{A^m} with exponent ω₀ yields, through
Bini's interpolation on the composed degeneration, an explicit algorithm for T_{B^m} with
exponent ω₁ = (6kN log(2a₀−1) + ω₀ log A)/log B < ω₀ whenever ω₀ > 3 log(2a₀−1)/log D*;
iterating converges to that fixed point.

Worked instance, a₀ = 2 (weights 20, 14, 9 on E_{2,2,7/10}, E_{2,3,9/14}, F_{2,1}):
  ⟨5^{258}⟩ ⊗ Cat ⊗ S(2,2)^{⊗15N} ⊗ T_{2^{68N}}  ⇝  Cat ⊗ T_{B_N},
  Cat = ⟨M₁^{120} M₂^{84} M₃^{54}⟩ ⊗ S(2,3)^{⊗14N} ⊗ S(2,4)^{⊗9N} ⊗ S(2,2)^{⊗5N},
  B_N = 2^{30N} M₁^{40} M₂^{28} M₃^{18}, M₁ = C(N, 0.7N), M₂ = C(N, 9N/14), M₃ = N!/((N/3)!)³,
giving S(2,2) ⊗ T₉ ≳ T₁₀₀ and ω ≤ 3 log 3 / log(10/3) = 2.7375.

## 5. Questions for the reviewer

Q1. Is (E_{a,b,q}) in §3 a correct primal reading of the paper's Lemma 4.1 + Cor. 3.2 at a
    fixed type, on all six legs? In particular: is the cost exactly T₂ ⊗ T₂ (one B_X(2)
    per permuted factor), is the gain exactly T_M ⊗ T_M, and are the direct-sum
    multiplicities ⟨(5M)⁶⟩ on the left and ⟨M⁶⟩ on the right right? Is it legitimate to
    use the same q on all six factors?
Q2. Same for (F_{a,h}) and the identification ⊗_π (C^σ)^π ≅ S.
Q3. Step 1: is it correct that the family (E) ∪ (F) ∪ (B), linearised with t as a variable,
    implies the growth lemma's conclusion, so that an LP certificate must exist? (The LP
    finding it is evidence; the question is whether anything non-linear was smuggled in.)
Q4. Step 2: is "a nonnegative combination of log-inequalities with cancelling variables"
    exactly "a tensor product of degenerations with common tensor factors", with no hidden
    subtraction? Pay attention to the ⟨M⁶⟩ multiplicities, which the character argument
    cancels by division.
Q5. Step 3: is the catalyst argument right as stated (one copy of Cat for all n), including
    the claim that R(Cat) is independent of n and that Y^{⊗n} ≤ Cat ⊗ Y^{⊗n}?
Q6. Step 4: is the bootstrap lossless at its fixed point, and is the explicit version (Bini
    interpolation on a degeneration of degree polynomial in n for fixed N) correct? What is
    the degree of the composed degeneration, and does the Stirling error in log M_q only
    cost O(log N / N) in the exponent?
Q7. Sanity: the claim implies, for every character, λ(S(a,a)) ≥ D*(a)^{2(p_X+p_Y+p_Z)}.
    Known characters (flattening ranks; quantum/support functionals) satisfy this with
    margins 1.17 (flattening) and 1.04 (quantum functional, uniform θ) at a = 2. Can you
    find any spectral point, or any direct tensor argument, that violates
    S(2,2) ⊗ T₉ ≳ T₁₀₀? A violation would refute the whole reading.
Q8. Is anything here new relative to the literature on explicit degenerations (Schönhage's
    asymptotic sum inequality, the laser method, Strassen's spectral theorem), or is it a
    known consequence that the author is re-deriving?

Please give a verdict per question (correct / wrong because … / cannot tell), and list the
single weakest step.
