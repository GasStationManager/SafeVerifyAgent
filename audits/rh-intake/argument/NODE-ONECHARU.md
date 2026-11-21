# NODE-ONECHARU: what the Sha bound is for, and how `OneCharU` + `CongruenceNumberUnitaryThree` bound the plus part

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations: `AV/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/`,
`DTC/` = `AV/ModularityArgument/ThresholdArguments/DenseThresholdCases/`, `U3/` = `AV/UnitaryThreeGroups/`,
`TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`,
`IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`.
"The Lean says" means I read it. *(inferred)* means my reading. Nothing was compiled.

## 0. Answers in brief
- **(a) Use.** Ш bounds the length of **Hecke congruence modules** at the local indices i of a host datum. The argument is the Ribet/Mazur
  direction: congruence ⇒ cocycle, so congruence length ≤ length of Selmer-type groups. Those lengths go into the divisibility
  exponents η_j (`LinkN`/`DIVinN`). The bound actually consumed is Σ_l log l·Σ_e len Ш ≤ b = exp(x^ε). VWin supplies √b, and the
  budget is then absorbed into B0 = f·m·b·x^ε. Crude bounds do **not** suffice. The truth is polynomial in x, the best crude bound in
  the tree (LemmaK) is exp((2kn)^C log disc), and with k ≤ x^401, n ≈ x^{2+8ε} that is far larger than exp(x^ε).
- **(b) Mechanism.** It is type **(ii)**, an R = T-type argument run on the deformation-ring side: (Ш ↪ first-order deformations of
  Ψ⊕1⊕Ψ⁻¹) + (the deformation ring is finite over O, its generic fibre is a regular curve at the irreducible points, and every point
  is automorphic or endoscopic) + a proved commutative-algebra inequality, giving len Ш_ψ′ ≤ 2Σ_points v_l(tr ρ(σ) − t). It is not an
  Euler system, and it is not a crude class-group bound.
- **(c) Uniformity.** No separate "Ш = 0 for large l" is proved. Uniformity in l comes from **one integer NN, independent of l**:
  Σ_l log l·v_l(NN) ≤ log|NN|. The dependence on k and the conductor is the explicit N^18·e^7 (`CorG`). The host conductor is kept at
  log cond ≈ Y^{ε/5}log²Y, so that poly(cond·t) ≤ exp(x^{ε/2}).
- **(d) Judgement.** The skeleton is recognisable and internally coherent. The deep content sits in three places: residually reducible
  ordinary automorphy for U(3) uniformly in l (`GdEndAlt` ← `LinkedEndEAlt` ← `ModUAlt`/`HidaUAlt`); regularity of the generic fibre
  at every automorphic point (adjoint-Selmer vanishing, uniformly in l); and finiteness of the trace algebra over O. None of these
  is a standard citation in this generality. If they hold, the consequence would be a new theorem: a polynomial bound on the plus
  parts of K_{2k}(O_E), uniform in l.

## 1. Statement

### OneCharU (`AV/ModularityArgument/LinkedUnramifiedChains/WeightInfinitesimalCharacters/AdmissibleUnitaryThreePoint.lean:116-126`)
```lean
def OneCharU : Prop := ∀ Ω K [IsCMField K] l c N e (ψ : DirichletCharacter c.O N), GD Ω K l e ψ →
  ∀ ι σ t, t = Ψ(σ) + 1 + Ψ(σ)⁻¹  (Ψ = Chr.Psi l e (dirG ψ), σ ∈ G_K pushed to G_ℚ) →
  (∀ ρ : G_K → GL3(Q̄_l), Adm3U ι e N ρ ∨ Adm2 ι e (N·|disc K|) ρ → tr ρ(σ) ≠ t) →
  Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset _, (∀ ρ∈X, Adm3U ∨ Adm2) ∧ (pairwise non-iso) ∧ Vn Ω c e ψ ≤ 2·Σ_{ρ∈X} v_l(tr ρ(σ) − t)
```
`GD` (`AV/HeightAndVanishing/Counts.lean:9-22`): l odd, e ≥ 1, N even, l ∤ ord ψ, (l-part of ψ)² = 1, the parity `PsiEven e ψ`
(the plus-part parity), K imaginary quadratic, l ∤ |disc K|·h_K, (disc K, N) = 1, a non-containment condition `eta`, and
**l − 1 ∤ 2e**. **There is no condition l > e.** Vlen/Vn is the ψ-component of Ш¹(G_{ℚ,S}, ℚ_l/ℤ_l(−e)⊗ψ) (ShaU, `U3/VlenLe.lean:46`).
Adm3U = irreducible, conjugate-self-dual automorphic after a twist, HT weights (e,0,−e), level N, with an unramifiedness clause `Unl`.
Adm2 = the endoscopic shape W ⊕ 1.

### CongruenceNumberUnitaryThree (same file, `:93-108`)
For each imaginary quadratic K there are c, A such that for all e ≥ 1, N ≥ 1 and primes p ≥ 7 with p ∤ N·disc K, a place w | p,
and any finite Galois-stable set Orb of roots of unity z_o, there is an integer NN ≠ 0 with
log|NN| ≤ c·#Orb·(N(e+1))^A·log p, such that for all odd l ≠ p, Frobenius σ at w, and families X_o of pairwise non-isomorphic
Adm3U/Adm2 representations: tr ρ(σ⁻¹) ≠ eis3(p, e, z_o), and ‖NN‖_l ≤ ∏_o ∏_{ρ∈X_o} ‖tr ρ(σ⁻¹) − eis3‖_l.
*(inferred)* NN is the norm of ∏ over all U(3) automorphic forms of level N and weight e of (a_w(π) − Eisenstein eigenvalue). It is
finite by finite-dimensionality, and it is nonzero by purity. `CorG` (`Counts.lean:24-32`) is the summed form:
Σ_l log l·Σ_ψ Vn ≤ 4c5·φ(index)·|disc K|^5·N^18·e^7·(log p + log p′), using two auxiliary primes so that l = p is covered.

### What the Sha bound feeds (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:31-63`; `CharacterBoxes/DivinNOfHypV.lean:10-130`)
- `vvTerm D l = log l·Σ_{1≤e<t} len Ш_l(e)`.
- `LinkN_at`: η_j ≤ dZ0·(C(f·m·b·L² + log²x·Nc) + Σ_l vvTerm).
- `DIVinN_at`: η_j ≤ D0·C·x^ε·(B0 + Nc), with B0 = f·m·b·x^ε (`Formalism/LocalToGlobal/Divisibility/Numbers.lean:74`).
- `divinN_of_hypV` uses HypV (= VVle E t √b) only through Σ vvTerm ≤ √b ≤ b ≤ B0 (`:100-128`).
- b = exp(x^ε) (`Formalism/LocalRingCardinality/DataParams₂.lean:27-29`).
- There is also an unused-here `LinkV_at` with the quasi-polynomial `Vbound = C·exp(C·log²(n t condE))` (`GlobalTheoremInputs.lean:16-20`).

## 2. Argument

### (a) Where Ш enters the slope chain
1. `GlobalCongruenceCountOfRootDifferenceUnit.main` (`IE/…:44`) is the local congruence count. For a local index i with residue prime
   l = l_i and an eigen-system π, the congruence module vcc_i(π) (length of O/cc(π), the Hecke congruence ideal of π against the rest
   of the cut) is bounded by:
   - sPi (the local Selmer/Bloch–Kato term for ρ_π);
   - Σ_{0<e<t} len Ш¹(ℚ_l/ℤ_l(−e)) over the host E;
   - v_l(h_E);
   - t·Σ_q len O/(ζ_q − 1) (tame places).

   The proof (`:56-118`) is a Ribet / generalised-matrix-algebra argument. An orthogonal idempotent decomposition splits the cocycles
   into a ρ-block and character blocks χ^c, c = 0..t−1. The ρ-block is bounded by local-at-l Selmer (`length_cocycles_le_coboundaries_add_selmer`).
   The c = 0 block is unramified homomorphisms, bounded by the class number (`UnramHom.length_le_classNumber`). Each c ≥ 1 block is
   unramified outside l and lies in the cut at l, so it is bounded by Ш (`length_cyclotomic_block_cocycles_le_sha`). This is the
   standard direction (congruence ⇒ Selmer classes).
2. `StepsNoCut.GlobalStatement` (`TPS/StepsNoCut.lean:18-32`) and `LocalCongruenceBound` (`Formalism/SharpRestriction/LevelLetterCocycles/LocalCongruenceBound.lean:12-20`)
   carry the same Ш sum into the divisibility exponents of the slope chain (LinkN → DIVinN).
3. *(inferred, matches the author's note)* Twisting kills most cohomology classes. The classes in H¹(o_E[1/l], ℚ_l/ℤ_l(−e)) that
   survive are exactly Ш, and they enter the divisibility exponents additively. A Vandiver-type statement (Ш = 0) would remove the term.
   A bound Σ log l·len Ш ≤ b, at the scale of the already-present main term B0, is enough.
4. **Size needed vs. available.**
   - Needed: ≤ exp(x^ε) (supplied as exp(x^ε/2)).
   - True *(heuristic)*: log|⊕_k K_{2k}(O_E)| ≲ n·t²·log(t·cond), which is polynomial in x.
   - Crude (proved in the tree, `LemmaK`): exp((2kn)^C·log disc). With k < x^401 and n ≈ x^{2+8ε} this is exp(x^{C'}), which is too weak.

   Minkowski/Brauer–Siegel controls only h_E (the c = 0 block, used directly above). For k ≥ 1 one would need a lower bound on Borel
   regulators (no Zimmert analogue is known to me), so **no crude route exists**. That is why U(3) appears. The minus part has the
   archimedean Bernoulli/L-value route (`ThmBc`, `minusBound`). The plus part does not.

### (b) Proof skeleton of OneCharU (`DTC/FOneCharU.lean:19-96`)
**Level 0.** Reduce to unramified coefficients (`exists_unram`, `:78-95`).

**Level 1** (`oneChar_unramU`, `:31-74`):
1. Build `Dat D`: residual r₀ = Ψ⊕1⊕Ψ⁻¹ as a GG3-valued (unitary C-group, η = quadratic character of K) representation of G_ℚ.
2. Build the local conditions U, the deformation ring S = `D.Ring U g₁`, and a ℤ-graded `Model M`. The grading is the weight under
   conjugation by the diagonal torus: entries (1,2), (2,3) have weight ±1 and (1,3) has weight ±2.
3. Lower bound, `U3.vlen_le` (`U3/VlenLe.lean:52-67`): Vlen ≤ M.len. `sha_inj` sends Ш[b] injectively to O/a-valued cocycles in
   `shaCoc`. `model_lower` (`U3/ModelLower.lean:373-380`) turns each such cocycle into a deformation to O ⊕ (O/a)ε, i.e. a derivation
   of the model. Ш classes are locally trivial at l, so they stay inside the ordinary/local condition. This step is formal.
4. Upper bound, `U3.model_upper` (`U3/ModelUpper.lean:103-111`). Hypotheses:
   - the weight-zero (trace) subalgebra is finite over O;
   - `PtHyp`;
   - LemmaM;
   - trDiff(σ) ≠ 0 at every two-signed point.

   Conclusion: nrm(M.len) ≤ 2·Σ_{f∈T} v_l(tr ρ_f(σ) − t), over a set T of torus-orbit representatives of the ℚ̄_l-points that are
   nonzero in both the positive and the negative weights (the "irreducible-type" points). The element a = Σ E_ii − tr r₀(σ) has
   weight 0 and vanishes at the base point (`:137-148`).
5. Automorphy of points (`hadm`, `:48-54`). Each point in T is either type I, giving Adm3U via `AdmI_s` and `AutBAlt`, or type II,
   giving Adm2 via `LemWAlt` and modularity of the 2-dimensional piece. Injectivity up to isomorphism comes from `twoPt_shape`.

**Level 2.**
- **LemmaM** (`Formalism/SharpRestriction/ValuationFrobeniusEpsilon/GradedPowerSeriesLemmas.lean:143-187, 221-232`) is a pure
  commutative-algebra statement about a quotient ST of a graded power-series ring over a DVR, with weights in [−2,2], a prime 𝔓, and
  flatness. Its hypotheses:
  - M1: after inverting l, the localisation at the base point is regular, and the graded cotangent pieces have prescribed ranks
    (*inferred*: Selmer ranks of the characters);
  - M2: the weight-0 part is finite over O;
  - M4: at every "Both" point the local ring is **regular of Krull dimension 1**, i.e. the generic fibre is a smooth curve there,
    which is a multiplicity-one input;
  - M5: a₀ has weight 0, vanishes at the base point and is nonzero at Both points.

  Conclusion: the cotangent index V′ ≤ 2Σ_τ v(τ(a₀)). It is claimed proved as `Alg.M.main_holds`, in the directory
  `AV/CommutativeAlgebra/GradedModulesLength/` (not opened).
- **FinA, AutBAlt, LemWAlt** come from `automorphyUnramified_of_locPrints_kisin_gdEnd` (`DTC/AutomorphyU3OfEndoscopy.lean:27-60`)
  ← `GdEndAlt` (`DTC/AutEnd3AltAlt.lean:35-40`): finiteness `FinEnd` and `AutEnd3Alt`. `AutEnd3Alt` says every ordinary point over a
  finite extension of O that is irreducible on open subgroups is automorphic.
- `GdEndAlt` is proved by `gdEnd_of_frame_linkedEnd_downCsdK_descent` (`DTC/GdEndOf.lean:22-80`). It uses `LinkedEndEAlt`
  (`DTC/PlDefs.lean:12-20`: finiteness and automorphy of points over an auxiliary CM field L) and descends to K.
- `LinkedEndEAlt` ← `linked_endomorphism_dense` (`DTC/LinkedEndE.lean:18-60`), which uses `ModUAlt`, `UnitaryThreeAutomorphyDense`,
  seeds and `twoRuns_alt`.
- `ModUAlt` (`DTC/PointTheoremBaseObject.lean:44-48`) says: for the universal ordinary determinant (pseudo-deformation) ring B of a
  Hida setting over a CM field there is an ideal J with B/J "modular" (ring properties, density of classical points, purity,
  classicality). It is proved from `HidaUAlt` (`DTC/HidaU.lean:12-16`; `DTC/THidaU.lean:38-50`), where J is the kernel to a unitary
  Hida Hecke algebra (`exists_hecke_ideal`).
- *(inferred)* This is the Skinner–Wiles residually-reducible scheme: B/J = T^ord, plus a connectedness/"linked ends" argument
  showing that the relevant points lie in V(J).

**Classification.**
- It is (ii), R = T on the R side. It needs no Gorenstein property of T and no isomorphism R ≅ T. It needs instead:
  1. finiteness of the trace algebra over O;
  2. every ℚ̄_l-point automorphic (Adm3U) or endoscopic (Adm2);
  3. regularity of the generic fibre at those points (M4, *inferred* from adjoint-Selmer vanishing, supplied through
     `ptHyp_of_autB_of_lemW_of_isBase` with `KatoTwoW` and `RigidityFirst/SecondCase`).
- It is not (iii). Ribet's direction is used elsewhere (the congruence-count side in (a)), not here.
- It is not (iv). The crude route fails for k ≥ 1 (§2a.4).

### (c) Uniformity in l and k
- Fix K and two auxiliary primes p, p′ (`CorG`; CountI picks r₁, r₂ below q₁ and d, `Counts.lean:56-61`).
- For every l in "case I", OneCharU with σ = Frob_w gives Vn(ψ) ≤ 2Σ_ρ v_l(tr − eis). CongruenceNumberUnitaryThree gives
  Σ_ρ v_l(·) ≤ v_l(NN) **for the same NN for all l** (l ≠ p, 2).
- Summing: Σ_l log l·Σ_ψ Vn ≤ 2·log|NN|·(#orbits) ≤ (N·t)^C. So "vanishing for l ∤ NN" is automatic and no regular-prime statement is
  needed.
- The excluded l are handled as separate cases with per-l bounds (l·N·e)^C (`CountShape`, `Counts.lean:63-73`): l | 2·disc·h_K, l | ord ψ,
  and l − 1 | 2e, i.e. cases II, III, V, Z. Each such case covers only finitely many l per (e, ψ), so the sum stays polynomial.
- The reading proposed in the task is confirmed: the minus part is L-value controlled, and the plus part is controlled by the
  congruence number.
- One correction. NN is not an L-value numerator. It is the norm of the product of (a_w − Eisenstein eigenvalue) over **all** level-N,
  weight-e U(3) forms. It is crude (a full-spectrum product) but uniform, and it gives a polynomial bound because the number of forms
  and the size of the Hecke eigenvalues are polynomial in (N, e).

## 3. Children

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `GdEndAlt` ← `LinkedEndEAlt` ← `ModUAlt`/`HidaUAlt`, `UnitaryThreeAutomorphyDense`, `twoRuns_alt` | `DTC/AutEnd3AltAlt.lean:35`; `DTC/GdEndOf.lean:22`; `DTC/PlDefs.lean:12`; `DTC/LinkedEndE.lean:18`; `DTC/PointTheoremBaseObject.lean:44`; `DTC/THidaU.lean:38` | every ordinary point of the residually-(Ψ⊕1⊕Ψ⁻¹) U(3) deformation ring is automorphic, and the ring is finite over O; uniform in all odd l, with no l > e condition | gives AutB/LemW/FinA | **core**, non-standard (residually reducible U(3) R = T à la Skinner–Wiles; nearest literature: Thorne 2015, Allen–Newton–Thorne, which do not cover three-character residual representations in general) |
| 2 | `PtHyp` via `ptHyp_of_autB_of_lemW_of_isBase` (KatoTwoW, RigidityFirstCase/SecondCase) | `DTC/FOneCharU.lean:56` (not opened) | M1/M3/M4: regularity of the generic fibre at the base point and at every automorphic point, with cotangent ranks | the multiplicity-one input | **core** (*inferred*: adjoint Bloch–Kato vanishing, as in Allen / Newton–Thorne, needed uniformly in l) |
| 3 | `LemmaM` / `Alg.M.main_holds` | `…/GradedPowerSeriesLemmas.lean:221`; dir `AV/CommutativeAlgebra/GradedModulesLength/` | V′ ≤ 2Σ_τ v(τ(a₀)) for graded curves over a DVR | turns smoothness plus points into a length bound | core, claimed proved; new to me; the factor 2 needs checking |
| 4 | `vlen_le` ← `sha_inj`, `model_lower` | `U3/VlenLe.lean:52`; `U3/ShaInj.lean:29`; `U3/ModelLower.lean:373` | Ш ↪ first-order deformations, so Vlen ≤ M.len | Selmer ⊂ tangent space | standard (Ribet/Bellaïche–Chenevier GMA formalism) |
| 5 | `model_upper` | `U3/ModelUpper.lean:103` | nrm(M.len) ≤ 2Σ_{f∈T} v_l(trDiff σ f) | assembles LemmaM | glue/core |
| 6 | `CongruenceNumberUnitaryThree` / `numberU3U_of_prints` | `AdmissibleUnitaryThreePoint.lean:93` | a single integer NN dominates all Eisenstein–cusp trace congruences at Frob_w, with log|NN| ≤ c·#Orb·(N(e+1))^A·log p | uniformity in l | core but plausibly elementary given a finite-dimensional space of forms, purity and a bounded number of Hecke eigenvalues (body not opened) |
| 7 | `GlobalCongruenceCountOfRootDifferenceUnit.main` (+ `length_cyclotomic_block_cocycles_le_sha`, `UnramHom.length_le_classNumber`) | `IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44` | congruence module ≤ sPi + Σ_e len Ш + v_l(h_E) + tame terms | **consumer** of Ш | standard direction (Ribet / Mazur–Wiles) |
| 8 | `divinN_of_hypV`, `vvRecord` | `CharacterBoxes/DivinNOfHypV.lean:17,117` | VVle ⇒ Σ vvTerm ≤ √b ⇒ DIVinN | consumer | glue |

## 4. Oddities
1. **Ш is used twice, in opposite directions.**
   - Downstream (item 7): congruence ≤ Ш. This is the safe direction.
   - Upstream (OneCharU): Ш ≤ congruence. This needs items 1–3.

   The groups differ (host E with twists e < t, versus Ш⁺ components over ℚ), so the argument is not circular. A reviewer should still
   keep the two directions apart.
2. **No condition l > e in GD.** Weights e up to x^401 are used with arbitrarily small l (only l − 1 ∤ 2e is excluded). This rules out
   Fontaine–Laffaille and forces the ordinary/Hida route. Hida theory is weight-independent, which makes this plausible, but items 1–2
   must then hold for l far below the weight. That is a strong uniformity claim.
3. **M4 is a multiplicity-one hypothesis in disguise.** It requires every irreducible point to be a regular point of a one-dimensional
   generic fibre. If some automorphic point had nonzero adjoint Selmer group, the inequality could fail. This is exactly where
   upper-bound Selmer arguments usually need Gorenstein / R = T input.
4. **The factor 2** comes from the ±1 weights. *(inferred)* B and C are dual under polarization. I did not verify it in LemmaM's proof.
5. **Existential X.** OneCharU says "∃ X". CongruenceNumberUnitaryThree is "∀ X", so the composition is sound. On its own, OneCharU's
   bound is only as good as the X it produces.
6. **Hypothesis "no admissible ρ with tr ρ(σ) = t".** This is supplied by the first conjunct of CongruenceNumberUnitaryThree, which
   comes from purity. If it failed, OneCharU would be vacuous for that σ. That is why two auxiliary primes are used.
7. **The slack is huge.** exp(x^ε/2) against a proved (cond·t)^C ≈ exp(O(x^{ε/5}log²x)). The host conductor is chosen tiny on purpose
   (WinPair). Nothing is tight.
8. **Implied new theorem.** If correct, the chain proves Σ_l log l·len(Ш⁺) ≤ poly(conductor, k) for abelian fields, i.e. a polynomial
   bound on log of the plus part of K_{2k}(O_E). That is a weak Vandiver-type statement which, as far as I know, is not in the
   literature (Soulé's bounds via Voronoi complexes are much larger). This is not evidence against it, but it means the result needs
   expert scrutiny rather than a citation check.

## 5. Coverage
Read:
- PROTOCOL (Explainer), SUMMARY (head), NODE-VWIN (all), NODE-HOSTS (grep plus the `supplyOfAdmOf` lines), NODE-ROOT:100-170,
  NODE-THETA:30-60, 120-190.
- `CharacterBoxes/DivinNOfHypV.lean` (all); `Formalism/SharpRestriction/GlobalTheoremInputs.lean:1-70`;
  `Formalism/LocalRingCardinality/DataParams₂.lean:9-77` (defs).
- `TPS/LinkNFam.lean:1-89`; `…/LocalCongruenceBound.lean` (all); `…/CongruenceSingleEndomorphism.lean:93-135`; `TPS/StepsNoCut.lean:1-32`;
  `TPS/StepsNoCutOfArtin.lean`; `TPS/StepsNoCutOfArtinStatement.lean`; `TPS/ImportsMoreMoreStatement.lean`; `TPS/ImportsMoreMore.lean`.
- `IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44-120`.
- `AdmissibleUnitaryThreePoint.lean` (all); `DTC/FOneCharU.lean` (all); `U3/VlenLe.lean` (all); `U3/ModelUpper.lean:1-230`;
  `U3/ShaInj.lean:29-37`; `U3/ModelLower.lean:373-383`.
- `…/GradedPowerSeriesLemmas.lean:125-245`; `AV/HeightAndVanishing/Counts.lean` (all).
- `DTC/AutomorphyUnramifiedCoefficients.lean`; `AV/AutomorphicCases/AutomorphyUnramifiedCoefficients.lean:1-30`; `DTC/AutomorphyU3OfEndoscopy.lean:1-60`;
  `DTC/AutEnd3AltAlt.lean:10-43`; `DTC/GdEndOf.lean:1-80`; `DTC/PlDefs.lean`; `DTC/LinkedEndE.lean:17-60`; `DTC/SymUse.lean:27-37`;
  `AV/WeilGroupCharacters/ArithmeticPointClassicality.lean:120-160`; `DTC/PointTheoremBaseObject.lean:30-48`; `DTC/CoefIsCoef.lean`;
  `DTC/HidaU.lean`; `DTC/THidaU.lean:30-50`.
- `AV/GaloisLibrary/KummerTheory/MinusLenLeOfCl.lean` (theorem headers).

Not opened:
- the body of `Alg.M.main_holds` (the GradedModulesLength directory), `ptHyp_of_autB_of_lemW_of_isBase`, `twoRuns_alt`, and
  `numberU3U_of_prints` (the NN construction);
- `exists_hecke_ideal`, `dense_of_is_j_unitary_hecke_data`, `Dat`/`D.Ring`/`Model` definitions, `KatoTwoW`, and the Rigidity cases;
- `CountII/III/V/Z` bodies and the minus-part `ThmBcFree`.
