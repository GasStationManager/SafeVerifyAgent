# Statement check: DimensionTenPair

- Challenge: `ComparatorChallenges/DimensionTenPair.lean` (125 lines), theorem `OAI.DimensionTen.main_pair`
- Config: `ComparatorChallenges/DimensionTenPair.json` (solution module `OAI.Analysis.Quantum.DimensionTen.Main`,
  axioms propext / Quot.sound / Classical.choice, no extra definition names)
- Scope note: `docs/272.md`
- Paper: "Entanglement with zero distillable secret key in local dimension ten" (Sept 27 2026), 53 pp., read from PDF.

## 1. Reference statement (written from the paper first)

**Theorem 1.2 (p. 2).** There are explicitly specified PPT maps Phi1, Phi2 : M10(C) -> M10(C) for which
Z = J(Phi2 o Phi1) is nonzero and its range contains no nonzero product vector in C^10 (x) C^10. In particular
Phi2 o Phi1 is not entanglement breaking.

Definitions the paper uses (Sec. 1 p. 2, Sec. 2 pp. 5-7):
- CP: F complex-linear, id_k (x) F preserves positive matrices for every k >= 1.
- PPT: F and T_b o F are both CP (output-transpose convention; no trace condition). Lemma 2.1 shows input/output
  transpose conventions are equivalent.
- Choi (2.1): J(F) = sum_{i,j} E_ij (x) F(E_ij) = (id_a (x) F)(Omega Omega*), unnormalized, input factor first.
- Separable: finite sum of positive product matrices (cone, not normalized).
- Entanglement breaking (Lemma 2.2(2)): CP and for every k >= 1 and W >= 0 in M_k (x) M_a, (id_k (x) F)(W) is separable.
- The explicit maps (6.5): Phi1(A) = E S(A^T) E*, Phi2(B) = R^dagger(E* B E), with
  S(A) = V*(L (x) L)(U A U*)V, R(A) = K S(A)^T K* (6.4); U : C^10 -> C^4(x)C^4 symmetric isometry and
  V : C^6 -> C^4(x)C^4 antisymmetric isometry (6.1), lexicographic pair bases; K the signed complementary-pair
  permutation (6.3): (Ke01..Ke23) = (e23, -e13, e12, e03, -e02, e01); E the coordinate inclusion C^6 -> first six
  coordinates of C^10; L(E_ij) = M_i^T M_j (7.2) for the four integer 6x4 matrices M0..M3 of (7.1).

Other main claims of the paper: Thm 1.1 (entangled state rho = Z/tr Z on C^10(x)C^10, no product vector in range,
K_D(rho) = 0, with the uniform 1/5 trace-norm gap (1.1)); Thm 1.3 (trace-preserving PPT channel on M21(C) whose
square is not entanglement breaking).

**Scope note (docs/272.md), recorded separately:** formalizes (i) the dimension-ten PPT pair with
non-entanglement-breaking composition and nonzero product-free Choi matrix (this challenge) and (ii) the
dimension-21 channel (separate challenge DimensionTenChannel). States explicitly that the zero distillable secret
key statement is out of scope.

## 2. Clause table (Lean read after the reference)

| # | Paper clause | Lean clause (definitions unfolded) | Class |
|---|---|---|---|
| 1 | Phi1, Phi2 "explicitly specified" by (6.5) | `∃ Φ₁ Φ₂, Φ₁ = phiOne ∧ Φ₂ = phiTwo ∧ …` - pinned by equality, no freedom | EXACT |
| 2 | Integer blocks M0..M3 of (7.1) | `blocksZ` (Int), cast to ℂ in `blocks` | EXACT (entry-by-entry; see 4.1) |
| 3 | L(E_ij) = M_i^T M_j | `pencilMap A = Σ_ij A i j • (blocks i)ᵀ * blocks j` (linear extension) | EXACT |
| 4 | U, V isometries (6.1), lex pair order | `symmetricIsometry`, `exteriorIsometry` with `symmetricPairs` (00,01,02,03,11,12,13,22,23,33), `exteriorPairs` (01,02,03,12,13,23), 1/√2 off-diagonal, sign + on (p,q), - on (q,p) | EXACT |
| 5 | L (x) L | `tensorMap pencilMap pencilMap`: Σ_{i,j} kron(F(block_ij X), G(E_ij)), which is F (x) G for linear F, G with first factor first | EXACT |
| 6 | S(A) = V*(L(x)L)(UAU*)V | `exteriorMap A = Vᴴ * tensorMap … (U*A*Uᴴ) * V` | EXACT |
| 7 | K (6.3) | `hodgeComplement`: rows give K e01=e23, K e02=-e13, K e03=e12, K e12=e03, K e13=-e02, K e23=e01; symmetric | EXACT |
| 8 | R(A) = K S(A)^T K* | `complementaryMap A = K * (exteriorMap A)ᵀ * Kᴴ` | EXACT |
| 9 | E: C^6 into first six coordinates | `firstSix i j = if i.val = j.val then 1 else 0` (10x6) | EXACT |
| 10 | Phi1(A) = E S(A^T) E* | `phiOne A = firstSix * exteriorMap Aᵀ * firstSixᴴ` | EXACT |
| 11 | Phi2(B) = R^dagger(E* B E), HS adjoint tr(Y*F(X)) = tr(F^dagger(Y)* X) | `phiTwo B = hsAdjoint complementaryMap (Eᴴ B E)`, `hsAdjoint F Y i j = Σ_uv conj(F(E_ij) u v) * Y u v`; for linear F this is exactly the HS adjoint (checked: F^dagger(Y)_ij = <E_ij, F^dagger Y> = conj tr(Y* F(E_ij))) | EXACT |
| 12 | Phi1, Phi2 PPT (F and T o F CP, linear) | `PPT F = IsComplexLinear F ∧ CompletelyPositive F ∧ CompletelyPositive (fun X => (F X)ᵀ)`; `CompletelyPositive F = ∀ k, 0<k → ∀ X PSD, (amplify F k X).PosSemidef`; `amplify` = id_k (x) F (block (u1,v1) of X fed to F, k factor first) | EXACT |
| 13 | Z = J(Phi2 o Phi1), input-first unnormalized Choi | `choi F u v = F (single u.1 v.1 1) u.2 v.2`, i.e. Σ E_ij (x) F(E_ij); equals `amplify F a (ΩΩ*)` | EXACT |
| 14 | Z nonzero | `Z ≠ 0` | EXACT |
| 15 | range contains no nonzero product vector | `∀ u v w, Z *ᵥ w = productVector u v → u = 0 ∨ v = 0`, `productVector u v (i,j) = u i * v j` (same (Fin a × Fin b) order as `kronecker`); u(x)v = 0 iff u = 0 ∨ v = 0 | EXACT |
| 16 | Phi2 o Phi1 not entanglement breaking | `¬ EntanglementBreaking (Φ₂ ∘ Φ₁)`, EB = CP ∧ ∀ k>0, ∀ X PSD, `separable (amplify F k X)`; `separable X = ∃ r A B, all A i, B i PSD ∧ X = Σ kron (A i) (B i)` | EXACT |

## 3. Denominators

(a) Paper main claims formalized by this challenge: Theorem 1.2 in full (1 of 3 main theorems). Of Theorem 1.1,
only the range clause is reachable (ran rho = ran Z, by trivial rescaling) - the state rho, its entanglement as a
stated conclusion, and K_D(rho) = 0 / bound (1.1) are not formalized; the docs note says so explicitly.
Theorem 1.3 belongs to the sibling challenge DimensionTenChannel (not audited here). The docs' stated scope
matches what is in this file.

(b) Lean clauses matching the paper: 16/16 EXACT. Nothing STRONGER, WEAKER, DIFFERENT or NOT LOCATED.

## 4. Traps checked

4.1 Integer blocks. Compared `blocksZ` entry-by-entry against (7.1) as extracted from the PDF: identical for all
96 entries. Independent consistency checks (numerical rebuild of the Lean definitions in numpy, script
`DimensionTenPair/check.py`): M_i^T M_j = M_j^T M_i for all i, j (paper's (7.4)) and M_0^T M_0 = 36 I_4 (Lemma 7.1),
so no sign was lost in extraction. Rebuilding Z exactly as the Lean definitions read gives: Hermitian, PSD up to
1e-6 roundoff, rank 80 (= 100 - 20, consistent with the twenty kernel vectors x^ (x) x^ of (6.10)), partial
transpose PSD, and Z[(0,0),(0,0)] = 10,077,696 = 6·36^4, the exact value stated in the proof of Thm 1.2 (p. 32).
So the Lean `phiOne`/`phiTwo`/`choi` reproduce the paper's Z, not a variant.

4.2 `0 < k` guards (CompletelyPositive, EntanglementBreaking). k = 0 would quantify over empty matrices and be
vacuous anyway; the paper also quantifies k >= 1. Harmless, standard.

4.3 `separable` with r = 0. The empty sum makes 0 separable, which is standard for the separable cone (paper:
"finite sum of positive product matrices"). It only enlarges the separable set, so it makes `EntanglementBreaking`
easier and `¬ EntanglementBreaking` harder - no trivialization. No PSD/nonzero requirement is missing (A i, B i
are required PSD; zero factors are allowed, harmless). Not normalized, matching the paper's cone formulation
(Lemma 2.2 works at the cone level, no trace preservation).

4.4 `¬ EntanglementBreaking` cannot be discharged via the CP conjunct: PPT Φ₁, PPT Φ₂ are proved in the same
statement, so the composite is CP and the negation must come from a non-separable output (genuine claim). It is
in fact derivable from clauses 14-15 by the paper's Lemma 2.3 plus choi = amplify F 10 (ΩΩ*).

4.5 `choi` is the standard (input-first, unnormalized) Choi matrix, as in (2.1). `Matrix.single i j 1` = E_ij.

4.6 `CompletelyPositive` does not itself require linearity, but `PPT` adds `IsComplexLinear`; `EntanglementBreaking`
uses CP without linearity - harmless since the composite of the pinned maps is linear.

4.7 PosSemidef over ℂ uses Mathlib's `Matrix.PosSemidef` (Hermitian + nonnegative quadratic form) with
`open scoped ComplexOrder`; standard.

4.8 Range clause uses `Z *ᵥ w` (column range) and the same pair ordering as `Matrix.kronecker`; no conjugation or
transposition slip. Product vector u (x) v is zero iff u = 0 or v = 0, so the conclusion `u = 0 ∨ v = 0` is exactly
"no nonzero product vector".

4.9 The Φ existential is pinned by `Φ₁ = phiOne ∧ Φ₂ = phiTwo`; no freedom to pick other maps. `compositeChoi` is
defined but unused (harmless).

4.10 Grep of the challenge file: no `axiom`, `opaque`, `implemented_by`, `native_decide`, `unsafe`, `decide`.
`noncomputable section` only. `Real.sqrt 2` cast into ℂ - correct normalization.

4.11 The basis ordering / choice of "first six" coordinates for E only needs E*E = I6, which holds.

## 5. Verdict

PAIRED. EXACT: `main_pair` is a faithful statement of the paper's Theorem 1.2 with the paper's own explicit
maps (6.5) built from the integer pencil (7.1); all definitions (PPT, CP, separable, entanglement breaking, Choi,
HS adjoint, tensor of maps, U, V, K, E) are the standard / paper notions. No deviations. Scope limits (Theorem 1.1's
secret-key content not formalized; Theorem 1.3 in a separate challenge) are stated correctly by docs/272.md.
