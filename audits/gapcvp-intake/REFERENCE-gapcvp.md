# Reference statement: NP-hardness of GapCVP^(2)_{n^{1/400}} and its coding / ℓ_p corollaries

Written BEFORE `ComparatorChallenges/H_GapCVP.lean` (and before any span of
`GapCVP.lean`) was opened, from Chapter 7 of "Ten advances in mathematics and
theoretical computer science" (OpenAI, 2026-08-01; extracted text
`paper-ch7-cvp.txt`: §1.1 lines 37–106, Lemma 7 lines 533–580, §6 lines
1564–1608, Corollaries 15–16 lines 1610–1672) and the textbook definitions of
NP and Karp reductions (Arora–Barak, *Computational Complexity: A Modern
Approach*, Defs. 2.1, 2.7; promise problems after Even–Selman–Yacobi and
Goldreich, "On promise problems", 2006). One clause per item so `STATEMENT.md`
can pair each with its Lean counterpart.

Disclosure: the brief that launched this rung NAMES Lean identifiers of the
challenge file (`lengthPrefixedWord`, `encodeAtomic`, `BitTM`, `VerifierTM`,
`IsNP`, `wellFormed`, `hasIntegerTarget`, `distanceSquared`, `gapFactor400`,
`disjoint`, `bitEncoding = id`, the four `*Promise` definitions) and that the
challenge uses Mathlib's `TM2ComputableInPolyTime`. So this reference is not
blind to the challenge's vocabulary; it is blind to the challenge's TEXT. The
W-list below is therefore phrased against those named slots, and every clause
is stated from the paper or the textbook, not from a guess at the Lean.
Paper line numbers were re-checked and corrected after drafting (citations
only; no clause changed).

## Problems (P)

- P1. **Lattice.** For a NONSINGULAR B ∈ ℤ^{n×n}, L(B) = Bℤ^n = {Bz : z ∈ ℤ^n}
  (columns generate; paper l.41–43). n ≥ 1 is the dimension = rank.
  (Row vs column convention is immaterial for a hardness statement only if the
  formal problem is closed under transpose of the encoding; check which.)
- P2. **Distance.** dist₂(t, L(B)) = min_{z∈ℤ^n} ‖t − Bz‖₂ (attained since L(B)
  is discrete; paper l.44–47). Equivalent comparison form, used below:
  dist₂ ≤ r ⇔ ∃ z ∈ ℤ^n, ‖t − Bz‖₂² ≤ r²; dist₂ > γr ⇔ ∀ z, ‖t − Bz‖₂² > γ²r²
  (the min is attained, so the ∃/∀ forms are exact, not approximations).
- P3. **GapCVP^(2)_γ instance.** (B, t, r): B ∈ ℤ^{n×n} nonsingular, t ∈ ℚ^n,
  r ∈ ℚ_{>0}, "all encoded in binary" (l.48–51).
- P4. **YES / NO.** YES: dist₂(t, L(B)) ≤ r. NO: dist₂(t, L(B)) > γ(n)·r, γ
  evaluated at the DIMENSION n (l.52–56). YES ∩ NO = ∅ because γ ≥ 1 and r > 0.
  The gap region r < dist ≤ γr is outside both.
- P5. **γ.** γ(n) = n^{1/400} (real 400th root; γ(1) = 1). Theorem 1 states
  the NO side as dist₂ > n^{1/400} r (l.73–76).
- P6. **Theorem 1 output shape.** The reduction produces t ∈ ℤ^n (not only ℚ^n),
  r ∈ ℚ_{>0} (§6: the main branch has integer r = ⌈√((ℓ+1)|P|)⌉ and integer
  binary t = u; the fixed NO instance is B = (2), t = (1), r = 1/2, l.1566–1572,
  1590–1593). So the reduction's image lies in the integer-target subproblem.
- P7. **Nearest codeword (Cor. 15).** Instance: a generator matrix G ∈ F₂^{k×n}
  (rows span C ≤ F₂^n), a received word u ∈ F₂^n, an integer radius R > 0.
  Objective d_H(u, C) = min_{c∈C} wt(u − c), wt = Hamming weight. YES: d_H ≤ R;
  NO: d_H > γ(n)·R, n = BLOCK LENGTH, γ(n) = n^{1/200} (l.84–101, 1616–1617,
  1631–1632). The paper's inconsistent-branch output is the code {00}, u = 11,
  R = 1 (l.1631–1634), so the generator matrix may be the zero matrix / have
  zero rows (C = {0}); a formal instance type must admit that (or the
  reduction must choose another NO instance).
- P8. **Syndrome decoding (Cor. 15).** Instance: parity-check H ∈ F₂^{m×n},
  syndrome b ∈ F₂^m, integer R > 0. Objective W(H,b) = min{wt(x) : Hx = b}
  (= +∞ / no solution when inconsistent). YES: W ≤ R; NO: W > n^{1/200}·R, n =
  block length (l.92–99). An inconsistent system has no x, so it is a NO
  instance under "∀ x, Hx = b → wt x > γR" and not a YES instance.
- P9. **ℓ_p CVP (Cor. 16).** Fixed rational p ≥ 1, independent of the input
  (l.1638–1640). Instance: nonsingular square integer B, target t, radius r
  with "polynomial-size exact rational encodings" (l.1647–1648). dist_p(t, L) =
  min_{z} ‖t − Bz‖_p. YES: dist_p ≤ r; NO: dist_p > n^{1/(200p)}·r, n = rank
  (l.1643–1646). The paper's radius r_p is RATIONAL and its target integral.
  Comparison form avoiding p-th roots: ‖t − Bz‖_p^p ≤ r^p vs > n^{1/200} r^p.
- P10. **Not claimed with a formal counterpart anywhere in the chapter.**
  ℓ_∞ (the corollary is "every FIXED FINITE rational p ≥ 1"); real p; SVP;
  randomized reductions. The overview's "related consequences for binary
  decoding and other lattice norms" (paper.txt l.26–28) is exactly Cors. 15–16.

## Complexity notions (C)

- C1. **Strings and encodings.** Inputs are finite strings over a finite
  alphabet (wlog {0,1}). An instance encoding must be INJECTIVE (two instances
  with the same string would make YES/NO ill-defined) and its length must be
  polynomially related to the binary size of the instance; the paper's
  "encoded in binary" fixes this up to polynomial equivalence.
- C2. **P-time computable function.** f : {0,1}* → {0,1}* computed by a
  deterministic TM that halts within poly(|x|) steps on every input x, with
  |f(x)| ≤ poly(|x|) (a consequence of the time bound). The polynomial is a
  fixed polynomial in the INPUT LENGTH.
- C3. **NP.** L ∈ NP iff there are a polynomial q and a polynomial-time TM V
  (deterministic, on input (x, w)) such that x ∈ L ⇔ ∃ w ∈ {0,1}^{≤ q(|x|)},
  V(x, w) = 1 (Arora–Barak Def. 2.1 uses |w| = q(|x|); ≤ is equivalent). Both
  bounds are load-bearing: drop the certificate bound and every r.e. language
  with a decidable P-time-checkable witness relation qualifies (NP grows to
  include undecidable-in-P things — hardness for a LARGER class is a STRONGER
  hardness claim); drop V's time bound likewise.
- C4. **Promise problem.** Π = (Π_YES, Π_NO), Π_YES ∩ Π_NO = ∅, both sets of
  strings. Nothing is required of strings in neither (malformed encodings,
  gap instances).
- C5. **Karp reduction of a language L to Π.** A P-time f with
  x ∈ L ⇒ f(x) ∈ Π_YES and x ∉ L ⇒ f(x) ∈ Π_NO.
- C6. **NP-hard promise problem.** For EVERY L ∈ NP, a Karp reduction L ≤ Π
  exists (C5). Equivalently (and that is the paper's route) a Karp reduction
  from 3SAT plus Cook–Levin; the formal statement should be the ∀ L form, or
  the 3SAT form together with a formal Cook–Levin — the ∀ L form is the
  stronger and self-contained one.
- C7. **Deterministic.** The paper claims a DETERMINISTIC reduction (l.73–79, 81);
  a formal TM-based statement is deterministic by construction if its machine
  model is.

## Headline claims (H)

- H1 (Thm 1). GapCVP^(2)_{n^{1/400}} is NP-hard under deterministic P-time
  Karp reductions, with the image in the integer-target subproblem (P6).
- H2 (Cor. 15). Binary nearest codeword and binary syndrome decoding, factor
  n^{1/200}, n = block length, NP-hard under the same reductions.
- H3 (Cor. 16). For each fixed rational p ≥ 1, full-rank ℓ_p CVP with factor
  n^{1/(200p)}, n = rank, NP-hard under the same reductions.

## What would make a formal version weaker, stronger, different, or vacuous (V)

- V1. **`IsNP` unsatisfiable → every hardness statement vacuous.** If no
  language provably satisfies the formal NP predicate (e.g. the machine
  structure required of a verifier cannot be inhabited because the alphabet
  equivalences / encodings demanded of it are impossible, or the time bound is
  unsatisfiable), then "∀ L, IsNP L → ∃ reduction" is trivially true. This is
  THE risk in a complexity statement. The check: (a) is the verifier
  structure inhabitable in principle (e.g. by a machine that ignores its input
  and accepts, or by the identity map), reading the Mathlib structure fields;
  (b) does the artifact itself CONSTRUCT such a structure, and (c) does any
  theorem of the artifact prove `IsNP L` for a concrete L (e.g. 3SAT), or does
  the proof only ever CONSUME an `IsNP` hypothesis.
- V2. **`IsNP` too weak** (verifier time bound missing or on the wrong
  length; certificate length unbounded). Then the formal NP is LARGER than NP
  and NP-hardness for it is a STRONGER claim than the paper's — not a way for
  the headline to be weaker than claimed. It is also self-limiting: a Karp
  reduction to a promise problem whose YES set is decidable decides L
  (x ∈ L ⇔ f(x) ∈ YES, since f(x) ∈ YES ∪ NO always), so if the formal NP
  contained an undecidable language the formal theorem would be FALSE, not
  vacuous. [Wording of V2 clarified after the challenge file was read; the
  check itself is unchanged.]
- V3. **Reduction time too weak.** The reduction's polynomial must bound
  steps as a function of the INPUT length (C2), for every input; a bound in
  the output length, a bound only on well-formed inputs, a bound `p.eval n`
  with `p` chosen after the input, or a non-polynomial bound would weaken C5.
  Note `Polynomial ℕ` evaluation at a natural is monotone in the argument
  automatically (all coefficients ≥ 0), so no monotonicity hypothesis is
  needed for the statement to mean "polynomial time".
- V4. **Encoding.** `encodeInstance` should be injective on instances (or at
  least YES/NO should be defined as "∃ instance with that encoding and the
  property", in which case non-injectivity could put one string in both
  languages — that is the disjointness question, V5). Malformed strings in
  neither language is fine (C4). The gap factor's n must be read off the
  instance, not the string.
- V5. **`disjoint` field.** If the promise-problem structure carries a
  `disjoint : Disjoint YES NO` Prop field, the challenge file may fill it with
  `sorry` (allowed in a comparator challenge for a Prop that is not itself
  compared?). Check what the comparator compares: if the four `*Promise`
  DEFINITIONS are compared by value/type and the theorem TYPES mention only
  `.yes`/`.no` projections, a `sorry`'d disjointness proof is proof-irrelevant
  to the statements, but the solution file must then supply a real proof, and
  the comparator must accept the solution's definition as matching the
  challenge's (definitional equality of structures differing only in a Prop
  field holds by proof irrelevance). Disjointness is in any case a FACT about
  the YES/NO sets (P4), checkable by reading.
- V6. **Gap factor on the wrong n.** γ must be at n = lattice dimension (P4),
  block length (P7, P8), rank (P9) — not the encoding length (which would
  make the factor polynomially SMALLER in effect... n_enc ≥ n, so
  γ(n_enc) ≥ γ(n): NO-set smaller, hardness STRONGER; still a deviation).
- V7. **`wellFormed` emptying YES/NO.** If well-formedness is unsatisfiable
  (e.g. det ≠ 0 over a 0×0 matrix only, r > 0 impossible in the chosen type)
  the promise problem is empty and "hardness" is false-or-vacuous; a
  reduction into an empty YES set from a nonempty NP language cannot exist, so
  this would show up as an unprovable statement, not a vacuous one — but
  combined with V1 it could hide. Check the predicate is inhabited (e.g. by
  the paper's fixed instance B = (1), t = (0), r = 1).
- V8. **`hasIntegerTarget` in both YES and NO.** Restricting BOTH sides to
  integer targets defines GapCVP restricted to ℤ^n targets — a SUBPROBLEM
  Π' with Π'_YES ⊆ Π_YES, Π'_NO ⊆ Π_NO. Any Karp reduction L ≤ Π' is
  verbatim a Karp reduction L ≤ Π (same f), so NP-hardness of Π' IMPLIES
  NP-hardness of Π: the restricted statement is STRONGER (and is exactly what
  Theorem 1 proves, P6). Not a weakening, provided the integer-target
  predicate is decided on the instance (not the string) and the rest of the
  instance (t's type) is ℚ^n as in P3.
- V9. **Squared distance.** Comparing ‖t − Bz‖² to r² (and to γ²r²) is exact
  for r ≥ 0, γ ≥ 0 (P2); a formal version comparing squared distance with r
  (not r²), or with γ·r² instead of γ²·r², would be a different problem.
  ‖·‖₂ must be the Euclidean sum of squares over ℚ (or ℝ), not ℤ-truncated.
- V10. **Classical `decide` Bool languages.** A language `x ↦ @decide P
  (Classical.propDecidable P)` is a `Bool` that equals `true` iff P (by
  `decide_eq_true_iff`, for ANY Decidable instance, since `Decidable P` is a
  subsingleton). So `L x = true ↔ P x` holds and no information is lost; the
  noncomputability only matters to `#eval`, never to the meaning of the
  statement.
- V11. **Machine-model alphabet coupling.** Mathlib's `TM2ComputableInPolyTime`
  is relative to `FinEncoding`s of the input and output types; if the
  challenge passes `bitEncoding = id`-style encodings, the machine's
  input/output alphabet must be in bijection with the encoding's alphabet
  (`Bool`), and the reduction is bit-string to bit-string. Fine, but the
  verifier for NP takes a PAIR (x, w); check how the pair is encoded (a
  separator, or a length-prefix) and that the encoding of pairs is injective
  and linear-length.
