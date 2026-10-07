# Statement check: FourRowPermanent

- Challenge: `ComparatorChallenges/FourRowPermanent.lean` (48 lines), theorem `OAI.FourRow.robust_permanent`
- Config: `ComparatorChallenges/FourRowPermanent.json`. Solution module `OAI.Combinatorics.Permanent.Main`; permitted axioms propext, Quot.sound, Classical.choice; no extra definition names.
- Scope note: `docs/238.md` (last paragraph of "Scope"; comparator-link row "Strict four-row permanent inequality near the uniform law").
- Repo commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a

## 0. Which paper

`docs/238.md` links ten preprints. Its paragraph for this challenge reads: "The formalization proves the
paper's strict four-row permanent inequality. There are constants 4/3<p<2 and ε>0 such that every
probability law on S_4 within total-variation distance ε of uniform, and with exactly uniform coordinate
marginals, satisfies the permanent bound by the product of the four L^p row norms for every nonnegative
matrix. The exponent and neighborhood are uniform over those laws. The Thorp mixing consequence is
outside this selected statement."

That is the tenth linked paper, **"A strict four-row permanent inequality and permutation moments"**
(`preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/main.pdf`,
19 pages), not either of the two named in the task ("Optimal-order mixing of the Thorp shuffle" covers
the overall Thorp result, and "From partial permutation information to Fourier bounds" covers
`PartialPermutation.lean`). I fetched that paper (HTTP OK, a valid PDF) and extracted its text with pypdf.
Status: **PAIRED**.

## 1. Reference statement (written from the paper before reading the Lean)

Notation (paper, p.1): for f : {1,2,3,4} → [0,∞), ‖f‖_p = ((1/4) Σ_{j=1..4} f(j)^p)^{1/p}.
u is the uniform measure on S_4. E_u Π_i f_i(π(i)) = perm(f_i(j)) / 4!.

**Theorem 1.1 (A robust four-row inequality), paper p.2.** There are absolute constants
p0 ∈ (4/3, 2) and ε > 0 with the following property. Let ν be a probability measure on S_4 such that
  (R1) ‖ν − u‖_TV < ε, and
  (R2) ν{π : π(i) = j} = 1/4 for all 1 ≤ i, j ≤ 4.
Then every four nonnegative functions f_1..f_4 on {1,2,3,4} satisfy
  (R3) E_ν Π_{i=1..4} f_i(π(i)) ≤ Π_{i=1..4} ‖f_i‖_{p0}.
"Here total variation is one half the sum of the absolute differences of the probability masses."

Quantifier structure: ∃ p0 ∈ (4/3,2), ∃ ε > 0, ∀ ν (probability law, R1, R2), ∀ f_1..f_4 ≥ 0, (R3).
So p0 and ε are uniform over all admissible laws and all functions.

Other numbered results in the paper (they are the denominator for (a)):
- Theorem 1.2 (p.2): fixed even r, η > 0 with D_λ Tr B_N(λ)^r ≤ D_λ^{1−η} for every dyadic N and
  λ ⊢ N, so that a fixed number q of sweeps mixes the Thorp shuffle in total variation.
- Support lower bound (3), p.3: ‖μ_t − U‖_TV ≥ 1 − 2^{tN/2}/N!.
- Lemma 2.1 (tensorization), Lemma 3.1 (annihilation and finite-size gap), Lemmas 4.1–4.3
  (color-string trace, cost of restriction, hook deficits), Lemma 5.1 (sparse stopping),
  Lemmas 6.1–6.2 (tree budget, hook comparison).

The scope note's own stated scope for this challenge: Theorem 1.1 only. "The Thorp mixing consequence
is outside this selected statement." The note's overall Thorp-mixing claim belongs to other
challenges (`ThorpRemaining`, `CoordinateTrace` and the rest), not to this file.

## 2. The Lean definitions, unfolded

- `Site := Fin 4`, `Perm := Equiv.Perm Site` (that is, S_4 with 24 elements), `Law := Perm → ℝ`,
  `Functions := Site → Site → ℝ` (row i ↦ function f i : Site → ℝ).
- `IsProbability ν := (∀ π, 0 ≤ ν π) ∧ Σ_π ν π = 1`.
- `UniformMarginals ν := ∀ i j, Σ_π (if π i = j then ν π else 0) = 1/4`, which is exactly ν{π : π i = j} = 1/4.
- `totalVariation ν := (Σ_π |ν π − 1/24|) / 2`. Since |S_4| = 24, 1/24 is the uniform mass, so this is
  one half of the ℓ¹ distance to u, matching the paper's convention.
- `lpNorm p f := ((Σ_j (f j)^p) / 4)^(1/p)`, with real `rpow`. For f ≥ 0 and p > 0 this is exactly
  ‖f‖_p with uniform counting normalization. Since 0^p = 0 for p ≠ 0, a zero entry raises no rpow issue.
- `permanentExpectation ν f := Σ_π ν π * Π_i f i (π i)`, which is E_ν Π_i f_i(π(i)). Under ν = u
  it equals perm/24. The permanent is therefore modelled exactly as the paper's left side
  (an expectation, not the raw permanent).

Theorem:
```
∃ p₀ : ℝ, 4/3 < p₀ ∧ p₀ < 2 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Law,
  IsProbability ν → totalVariation ν < ε → UniformMarginals ν →
  ∀ f : Functions, (∀ i j, 0 ≤ f i j) → permanentExpectation ν f ≤ ∏ i, lpNorm p₀ (f i)
```

## 3. Clause table

| # | Paper clause (Thm 1.1) | Lean clause | Class |
|---|---|---|---|
| 1 | ∃ absolute p0 with 4/3 < p0 < 2 | `∃ p₀ : ℝ, 4/3 < p₀ ∧ p₀ < 2` (outermost) | EXACT |
| 2 | ∃ absolute ε > 0 | `∃ ε, 0 < ε`, after p₀ and before ν | EXACT (the same order, so uniform over laws) |
| 3 | ν a probability measure on S_4 | `ν : Perm (Fin 4) → ℝ` with `IsProbability` | EXACT (finite space; a mass function is equivalent) |
| 4 | ‖ν − u‖_TV < ε, TV = ½ Σ\|differences\| | `totalVariation ν < ε` = ½ Σ\|ν π − 1/24\| | EXACT (strict, and the same ½ normalisation) |
| 5 | ν{π(i)=j} = 1/4 for all i, j | `UniformMarginals ν` | EXACT |
| 6 | every four nonnegative functions on {1..4} | `∀ f : Fin 4 → Fin 4 → ℝ, ∀ i j, 0 ≤ f i j` | EXACT (row i = f_i, column j = argument) |
| 7 | LHS E_ν Π_i f_i(π(i)) | `permanentExpectation ν f` | EXACT |
| 8 | RHS Π_i ‖f_i‖_{p0}, ‖f‖_p = ((1/4)Σ f^p)^{1/p} | `∏ i, lpNorm p₀ (f i)` | EXACT |
| 9 | ≤ (non-strict) | `≤` | EXACT |

Row/column convention: the paper evaluates f_i at π(i), so row i is read at column π(i). The Lean code
evaluates `f i (π i)`, which is the same orientation. Under the marginal hypothesis a transposed
convention would also be harmless, but none is present.

## 4. Denominators

(a) Paper main claims formalised by this challenge: 1 of the paper's 2 headline theorems
(Theorem 1.1, in full; Theorem 1.2 and the mixing corollary are not formalised here).
Lemma 2.1, Lemmas 3.1–6.2 and the lower bound (3) are not formalised here. In total: Theorem 1.1 out of
2 theorems plus 9 lemmas/displayed claims. This matches the scope note, which selects Theorem 1.1 and
explicitly excludes the Thorp mixing consequence. The note's statement of the selected claim
("constants 4/3<p<2 and ε>0 ... uniform over those laws") is accurate.

(b) Lean clauses that match the paper: 9 of 9 EXACT. None is STRONGER, WEAKER, DIFFERENT or NOT LOCATED.

## 5. Traps checked

- Vacuity: not vacuous. The uniform law u (mass 1/24) satisfies `IsProbability`, `UniformMarginals`
  and TV = 0 < ε for every ε > 0, so the hypothesis set is always inhabited.
- Trivial constant choice: not trivial. Even at ν = u, the inequality fails for p below the
  Bristiel–Caputo threshold p_c = 4 log 4 / log 24 ≈ 1.744 (the identity-matrix example, paper p.2).
  The prover must therefore produce a real p₀ in [p_c, 2), and with ν ≠ u a strictly positive
  neighbourhood. Choosing p₀ = 2 is excluded by `p₀ < 2`. Choosing ε tiny does not remove the ν = u
  case, so the uniform-law permanent bound with p < 2 is unavoidable content.
- Real rpow: `(f j)^p` with p : ℝ is `Real.rpow`; the base is nonnegative because of the
  hypothesis `0 ≤ f i j`. `(·)^(1/p)` is applied to a nonnegative sum. No negative-base junk values occur.
- Coercions: Fin 4 is used only as an index set, with no arithmetic on it. All quantities are in ℝ.
  `1/4`, `1/24` and `4/3` are real literals (ℝ division, not ℕ).
- Uniform mass: `1/24` = 1/|S_4|, so it is correct. A wrong constant here would have shifted the
  TV centre, and it does not.
- Sense: `≤` matches the paper, and `<` in TV matches the paper's strict inequality.
- Missing hypotheses: none. Nonnegativity of ν is required (`IsProbability`), the marginals are exact,
  and the nonnegativity of f is required.
- Redundancy: `IsProbability`'s total mass is implied by the marginals (Σ_j of marginal i = 1), which is
  harmless.
- Forbidden constructs: the challenge file contains no `opaque`, `axiom`, `implemented_by`,
  `native_decide` or `unsafe` (I read it top to bottom; it imports only Mathlib). The solution module
  files `OAI/Combinatorics/Permanent/*.lean` also contain none of these, nor `sorry` (grep).
- Note, outside the statement: the solution instantiates p₀ = 2 − 10⁻⁵ and ε = 10⁻⁵ (`Main.lean`
  lines 9–11). This lies inside the required range and is consistent with the paper's remark that p₀ is
  "chosen closer to two and is not optimized". It is a proof-side fact and does not affect the statement.

## 6. Verdict

**PAIRED, EXACT.** The Lean theorem states Theorem 1.1 of "A strict four-row permanent inequality and
permutation moments" clause for clause. The details are:
- the same quantifier order (∃p₀ ∃ε ∀ν ∀f), so p₀ and ε are uniform over laws;
- the same open interval (4/3, 2);
- the strict TV hypothesis with the ½-ℓ¹ normalisation;
- exact uniform coordinate marginals;
- nonnegative row functions;
- the permanent modelled as the ν-expectation of Π_i f_i(π(i));
- uniformly normalised L^{p₀} row norms.

There are no deviations. The paper's Theorem 1.2 (the moment bound and Thorp mixing) and its lemmas
are outside this challenge, as the scope note says.
