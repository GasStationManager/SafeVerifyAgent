# Statement check: LaughlinGap

Challenge: `ComparatorChallenges/LaughlinGap.lean` (theorem `OAI.LaughlinGap.thm_main`, solution
module `OAI.Analysis.LaughlinGap.Main`, permitted axioms propext / Quot.sound / Classical.choice).
Scope note: `docs/269.md`. Papers fetched (both, commit adc7f12):
- S = "Uniform Stability of the Spherical Laughlin Gap" (Oct 5 2026), 4268 text lines.
- F = "A Fock-space inequality and the Laughlin spectral gap" (Sep 24 2026), 1412 text lines.

Which paper: the note says the challenge is "the uniform unperturbed gap estimate used in the
paper's stability argument", i.e. S's Theorem 2.2, eq. (2.10), which S explicitly imports from F
("its proof is in the companion manuscript [16, Theorem 1.1 and Corollary 1.2]"). The reference
statement is therefore F Corollary 1.2 = S eq. (2.10). S's own main theorem (disorder stability)
is NOT the challenge.

## 1. Reference statement (written before reading the Lean body)

Model (F §1.1, S §1.1, §2.1). For integer Q >= 1, U_Q = spin-Q/2 rep of SU(2) = homogeneous
degree-Q polynomials in a spinor (u,v) (S writes (z0,z1)); orthonormal basis
e_j = C(Q,j)^{1/2} u^{Q-j} v^j, 0 <= j <= Q. For 2 <= N <= Q+1,
  H_{N,Q} = sum_{1<=i<j<=N} P^{(1)}_{ij} restricted to wedge^N U_Q,
P^{(1)}_{ij} = orthogonal projector onto pair spin Q-1 (relative angular momentum one) in tensor
slots i,j; coefficient one per unordered pair, no N- or Q-dependent rescaling.
Explicit basis of the spin-(Q-1) pair space (S eq. 2.5): for 1 <= b <= 2Q-1,
  v_{b-1} = Z_{Q,b}^{-1/2} sum_{i<j, i+j=b} (j-i) C(Q,i)^{1/2} C(Q,j)^{1/2} e_i ^ e_j,
  Z_{Q,b} = b(2Q-b)/(2(2Q-1)) C(2Q,b).
Laughlin vector Psi_{L,N} = prod_{i<j} (u_i v_j - u_j v_i)^3; P_{L,N} = projector onto its line.

F Corollary 1.2 (= S Theorem 2.2, eq. 2.10). There is an integer N_0 >= 2 such that for every
N >= N_0 and Q = 3(N-1),
  H_{N,Q} >= (1/25)(I - P_{L,N})   on wedge^N U_Q   (operator inequality).
Constants: 1/25 explicit; N_0 existential (F: "thresholds ... are existential").

Other main claims of the two papers (for denominator (a)):
- F Thm 1.1: for every 0 < gamma < gamma_* = 4616733319001/10^14, exists Q_gamma with
  H_Q^2 >= gamma H_Q on the whole Fock space F_Q for Q >= Q_gamma, independent of particle number.
- F §7: planar untruncated inequality at the endpoint gamma_* on every homogeneous sector.
- F (line ~1038): Delta_N >= N/[25(N-1)] (charge/neutral-gap type consequence).
- S Thm 1.1 (main): exist lambda_* > 0, Delta_* > 0, N_* such that for N >= N_*, every real bounded
  measurable phi on S_{3(N-1)} with ||phi||_inf <= 1, every |lambda| <= lambda_*, the two lowest
  eigenvalues of H_{N,q} + lambda sum_i T_q(phi)_(i) differ by >= Delta_*; perturbed ground state unique.
- S Thm 6.6 (zero-mode local observable bound), S Thm 7.1 (particle-loss operators), S App. A
  (retained four-body blocks).

Scope note's own statement (docs/269.md): the selected statement is "the unperturbed Fock-space
inequality" at flux q = 3(N-1), large N: V1 energy >= 1/25 times squared distance from the
Laughlin line. "Stability under projected one-body potentials and uniqueness of the perturbed
ground state are outside it." Other results (1/100 bound, H_Q^2 >= gamma H_Q, planar) are
attributed to separate challenges Laughlin.lean, LaughlinFock.lean, LaughlinPlanar.lean.

## 2. Lean statement and its definitions

- `Configuration N Q := Fin N -> Fin (Q+1)`, `State N Q := Configuration N Q -> ℂ`: a vector in
  the tensor power U_Q^{⊗N} in coordinates of the orbital basis e_0..e_Q.
- `Antisymmetric ψ`: ψ(a ∘ swap i j) = -ψ(a) for all i ≠ j — i.e. ψ ∈ wedge^N U_Q (as
  antisymmetric tensors).
- `pairCoefficient Q p x y` = [x+y = p+1] (x-y) sqrt(Q↓x · Q↓y · p! / (Q · (2Q-2)↓p · x! · y!)) / sqrt 2
  (↓ = descending factorial). Since Q↓x/x! = C(Q,x) and (2Q-2)↓p/p! = C(2Q-2,p), this is
  (x-y) sqrt(C(Q,x)C(Q,y) / (2 Q C(2Q-2,b-1))) with b = p+1. Algebra:
  Z_{Q,b} / (Q C(2Q-2,b-1)) = [(2Q)!/(2Q-2)!] / [2Q(2Q-1)] = 1, so the coefficient is exactly the
  antisymmetric-tensor form of S's v_{b-1} (e_i^e_j ↦ (e_i⊗e_j - e_j⊗e_i)/sqrt 2), up to an
  irrelevant global sign. These have unit tensor norm, are orthogonal for different p, and p
  ranges over `Finset.range (2*Q-1)` = {0..2Q-2}, i.e. all 2Q-1 = dim(spin Q-1) basis vectors.
- `pairAmplitude ψ i j p a` = sum_{x,y} c_p(x,y) ψ(a[i:=x][j:=y]) = partial inner product of slots
  i,j with w_p (real coefficients, so no conjugation issue).
- `energy ψ` = sum_{i<j} sum_p sum_{a : a i = 0 ∧ a j = 0} |pairAmplitude|^2. The a i = a j = 0
  filter just picks one representative per assignment of the other N-2 slots (slots i,j are
  overwritten). Hence energy ψ = sum_{i<j} <ψ, P^{(1)}_{ij} ψ> = <ψ, H_{N,Q} ψ> in tensor norm,
  coefficient one per unordered pair.
- `bracket i j` = X(i,false)X(j,true) - X(j,false)X(i,true) (false = u, true = v);
  `laughlinPolynomial N` = prod_{i<j} bracket^3.
- `laughlinVector N Q a` = coeff of prod_i u_i^{Q-a_i} v_i^{a_i} divided by prod_i sqrt C(Q,a_i):
  exactly the e-basis coordinates of the polynomial Psi_{L,N} (since e_j = C(Q,j)^{1/2} u^{Q-j} v^j).
  Unnormalized, which is harmless below.
- `distanceToLaughlinSq ψ` = sInf over c ∈ ℂ of sum_a |ψ a - c L a|^2. The set is nonempty and
  bounded below by 0, so this is the true minimum = ||ψ||^2 - |<L,ψ>|^2/||L||^2 = <ψ,(I-P_L)ψ>
  whenever L ≠ 0 (it is: a product of nonzero polynomials, and the coefficient extraction
  is injective at Q = 3(N-1), each variable having degree exactly 3(N-1)).
- `MainTarget`: ∃ N₀, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
  (1/25) * distanceToLaughlinSq ψ ≤ energy ψ.

Numerical sanity check (a literal Python mirror of the Lean definitions, run in the scratchpad):
N=2,Q=3: spectrum of the energy form on the antisymmetric subspace {0, 1, 1, 1, ...}; N=3,Q=6:
{0, 0.785714 (x3), ...}; in both, the kernel is one-dimensional and contains laughlinVector
(L^T H L / |L|^2 ≈ 1e-17). This confirms the coefficient formula, the basis conventions and the
Laughlin encoding agree with each other (a coefficient or orientation error would put L outside
the kernel or change the kernel dimension).

## 3. Clause table

| # | Reference clause (F Cor 1.2 / S eq 2.10) | Lean clause | Class |
|---|---|---|---|
| 1 | ∃ integer N_0 ≥ 2 | `∃ N₀ : ℕ, 2 ≤ N₀` | EXACT |
| 2 | ∀ N ≥ N_0 | `∀ N, N₀ ≤ N` | EXACT |
| 3 | Q = 3(N-1) | `State N (3*(N-1))` (ℕ subtraction harmless, N ≥ 2) | EXACT |
| 4 | Hilbert space wedge^N U_Q | antisymmetric functions Fin N → Fin(Q+1) → ℂ, tensor ℓ² norm | EXACT (norm convention differs from the wedge normalization by a constant factor N!, which cancels: both sides are quadratic forms in the same norm) |
| 5 | U_Q basis e_j = C(Q,j)^{1/2} u^{Q-j} v^j | coordinates; division by sqrt C(Q,a_i) in `laughlinVector` | EXACT |
| 6 | P^{(1)}_{ij} = projector on pair spin Q-1 | sum_p |w_p><w_p| with w_p = `pairCoefficient` = S eq. 2.5 basis | EXACT (checked algebraically and numerically) |
| 7 | H = sum_{i<j} P^{(1)}_{ij}, coefficient one | `energy` = sum over i<j, coefficient one | EXACT |
| 8 | Psi_L = prod_{i<j}(u_i v_j - u_j v_i)^3 | `laughlinPolynomial` / `laughlinVector` | EXACT |
| 9 | I - P_L (projector onto complement of Laughlin line) | `distanceToLaughlinSq` = min_c ||ψ - cL||² | EXACT (quadratic form of I - P_L) |
| 10 | operator inequality H ≥ (1/25)(I - P_L) | ∀ antisymmetric ψ, (1/25)·dist² ≤ energy | EXACT (self-adjoint operator inequality ⇔ quadratic-form inequality for all ψ) |
| 11 | constant 1/25 | `(1/25 : ℝ)` | EXACT |

Not a surrogate: the paper's statement is itself a finite-dimensional operator inequality for
each N; the Lean statement is that inequality written in explicit tensor coordinates, with no
truncation of the interaction and no restriction of the state space.

## 4. Denominators

(a) Paper main claims formalised by THIS challenge: 1 of the papers' main claims — F Corollary 1.2
(= S Thm 2.2 eq. 2.10). Not here: S Thm 1.1 (disorder stability, the stability paper's headline
result), S uniqueness of perturbed ground state, S Thm 6.6 / 7.1 / App. A; F Thm 1.1
(H_Q² ≥ γ H_Q for all γ < γ_*) and the planar §7 result are routed to other challenges
(LaughlinFock.lean, LaughlinPlanar.lean) per the note. This matches the note's own scope statement,
which explicitly excludes stability and perturbed uniqueness. In particular, measured against the
stability paper's title claim (S Thm 1.1), this challenge covers only the unperturbed input.
(b) Lean clauses matching the paper: 11 / 11 EXACT.

## 5. Traps checked

- No `opaque`, `axiom`, `implemented_by`, `native_decide`, `unsafe`, or `decide` in the file;
  `definition_names` is empty; all definitions are plain noncomputable defs.
- Vacuity: `Antisymmetric` is inhabited (0 and nonzero alternating tensors since N ≤ Q+1 for
  Q = 3(N-1), N ≥ 2). laughlinVector ≠ 0, so dist² is the genuine I-P_L form, not ||ψ||²
  (which would make the statement H ≥ I/25 and false, since L has energy 0).
- sInf over `Set.range` on ℂ: nonempty, bounded below by 0 — no junk-value 0 from an empty or
  unbounded set. If it were junk 0 the statement would be trivial; it is not.
- Direction: `(1/25) * dist ≤ energy` — the correct (lower bound on H) sense; non-strict as in paper.
- ℕ subtraction: `3*(N-1)`, `2*Q-1`, `2*Q-2`, `Q - a` all safe since N ≥ N₀ ≥ 2 ⇒ Q ≥ 3 and a ≤ Q.
  `Finset.range (2*Q-1)` gives p ∈ {0..2Q-2}, the full spin-(Q-1) multiplet; Q·(2Q-2)↓p ≠ 0 there.
- Real.sqrt of a nonnegative ratio; no negative-argument junk.
- The `a i = 0 ∧ a j = 0` filter neither double counts nor drops terms (slots overwritten).
- Pair coefficient normalization: per-pair projector coefficient one (not 2, not 1/(N-1)),
  confirmed by N=2 spectrum {0,1}.
- Existential N₀ with `2 ≤ N₀` matches the paper's "integer N_0 ≥ 2"; the guard does not trivialize.
- Complex scalars, tensor (not wedge) normalization: irrelevant to a homogeneous quadratic inequality.

## 6. Verdict

PAIRED (against F Corollary 1.2, which S states verbatim as eq. 2.10 of Theorem 2.2).
EXACT: the Lean theorem is a faithful coordinate transcription of
"H_{N,3(N-1)} ≥ (1/25)(I - P_{L,N}) on wedge^N U_{3(N-1)} for all N ≥ some N_0 ≥ 2",
with the Hamiltonian (full V1 pair projectors, coefficient one), the Laughlin line, the flux
Q = 3(N-1) and the existential threshold all modelled as in the paper. Deviations: none at
statement level. Coverage caveat: it is the unperturbed input of the stability paper, not that
paper's main theorem (disorder stability), as the scope note itself says.
