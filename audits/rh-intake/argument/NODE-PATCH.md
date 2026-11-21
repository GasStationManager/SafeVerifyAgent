# NODE-PATCH: Taylor–Wiles patching at nice primes (`Pa.pFromAut` → `P1core`/`P3core`), read as a specialist

## Conventions

Paths are relative to `.../scratchpad/art/lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/`.
Abbreviations: `PM/` = `PatchingModules/`, `CDS/` = `CurveDVRSpecialization/`, `FSV/` = `FrobeniusSmoothVectors/`,
`WGC/` = `WeilGroupCharacters/`.

"The Lean says" means I read it. *(inferred)* means it is my reading. Nothing was compiled. A grep for
`sorry|axiom|admit|native_decide` over `PM/`, `CDS/`, `FSV/` and `AlgebraTools/` returns nothing.

## 0. Answers in brief

### The parent's bet is half right
- **Right:** patching is done at endoscopic (TypeE) nice points, where ρ_𝔭 over K((t)) is reducible, of shape W ⊕ W′.
- **Wrong:** "no Ext/Selmer-dimension condition".
  - There is a quantitative condition: g² + e ≤ D0, where
    - g = the rank over K((t)) of the off-diagonal Selmer group;
    - D0 = n·d + n·q;
    - e = the number of tangent directions of the reducible locus that are used.
  - It is not assumed. It is derived from the same Greenberg–Wiles bound used in the irreducible case (`claim1`, inside
    `pres`).
- **The new idea** is an explicit determinantal local model at the reducible point.
  - Bh ⊕ N (a generalised-matrix-algebra-type ring) is a quotient of OO[[X₁..X_{D0}, M₁..M_g]] by the g relations Y·M = 0.
  - Here Y is a g×g matrix of linear forms in the X whose residues are linearly independent.
  - Such a ring has exactly two components of dimension 1 + D0:
    - {M = 0}, the reducible one;
    - {Y·M = 0, det Y = 0}, which is irreducible.
  - The second one contains every non-semisimple prime and every irreducible-type prime.
  - This is proved in Lean as pure commutative algebra (`presOut1`, `under_le_of_det_mem`).

### (c) No condition l > n, and as far as I can reconstruct none is needed
- Detection of dual Selmer classes is a Carayol/Bellaïche–Chenevier-type statement: "trace data determine the thickened
  representation over K((t))". It is not an H¹(finite image, ad) = 0 adequacy statement.
- Taylor–Wiles primes only need Frobenius elements whose characteristic polynomial is separable over K((t)). That is the
  point-condition N3; it is not a residual condition.
- Passing from G′ = G_{L(μ_{l^∞})} back to G uses only that ε mod l is nontrivial.

## 1. Statements

### 1.1 Nice points (`WGC/UniversalOrdinaryDeterminantRing.lean:187-280`)

**`Point r`.** It consists of:
- a finite field K;
- ρ : G_L → GL_n(K[[t]]), continuous and polarised, whose determinant reduces to D̄;
- characters ψ_{v,i} lifting ψ̄;
- unramified at the places in `Ip`;
- a flag at each v | l over K((t)).

**Conditions on a point:**
- **N1** (`:229`): the ψ_{v,i} are pairwise distinct, and ψ_{v,i} ≠ ψ_{v,j}·ε for i < j.
- **TypeI** (`:256`): ρ is absolutely irreducible on G′, where G′ = ker ε ∩ G_L (`:73`).
- **TypeE** (`:258-265`): over K((t)), ρ ≅ r₁ ⊕ r₂ with:
  - dimensions a, b ≥ 1;
  - each block polarised;
  - each block absolutely irreducible on G′;
  - Hom_{G′}(r₁, r₂) = 0.
- **N3** (`:267`): every open coset of G′ contains σ with charpoly ρ(σ) separable over K((t)).
- **N4** (`:271`): Hom(ρ, ρ(1))^{D0} = 0 on a fixed decomposition group D0 (at v0).
- **NiceI** = N1 ∧ TypeI ∧ N3 ∧ N4. **NiceE** = N1 ∧ TypeE ∧ N3 ∧ N4 (`:275-277`).

So the answer to (a) is:
- reducibility over K((t)) **is allowed** (TypeE);
- the "big image" condition is the absolute irreducibility of each block on G′, together with N3;
- there is no adequacy or l > n hypothesis.

**Patching-side version `NP`** (`PM/PairedDualFirstOrderDualMatrixSpace.lean:251-274`). ρ is block-diagonal with block
sizes (a, n−a) (`blk`), and the K[[t]]-span of ρ(G′) contains t^s·(all block-diagonal matrices) (`span`).

**`Norm`** (`PM/TaylorWilesObstructionBound.lean:16`) converts a Point into an NP:
- by a finite extension of K[[t]];
- with a = n for TypeI;
- keeping N3 and N4.

**Where N1/N3/TypeE come from.** At the S-level, a `Nice` prime (`CDS/PropagationTheoremGL2.lean:16`) has dimension 1,
characteristic l, is OffTri and has no coincidences. `niceOf` (`CDS/NiceOf.lean:7`) derives N1, N3 and TypeI/TypeE from
that. N3 is obtained from strong irreducibility on open subgroups plus a "free ratios" element, with n ≤ 3
(`CDS/NiceSpecializationTwistSatisfiesThirdCondition.lean:50-60`).

### 1.2 `P1core`, `P3core` (`WGC/UniversalOrdinaryDeterminantRing.lean:290-307`)
- **P1core.** Let x be NiceI and modular (J ≤ ker f). Then every generisation q ⊆ ker f has J ≤ q, i.e. every component
  through x is modular.
- **P3core.** Suppose:
  - x₀, …, x_h are NiceE;
  - for each i there is a thick prime e_i (not stable, and E0 ⊗ κ(e_i) not semisimple) with e_i ⊆ ker f_i ∩ ker f_{i+1};
  - some stable (absolutely irreducible) modular prime q₁ ⊆ ker f₀ exists.

  Then every stable or thick prime q ⊆ ker f_h is modular.

### 1.3 `Raw` (`PM/PatchedSupportCompletions.lean:207-213`) and `ChainConcl` (`:181-185`)
**Inputs:**
- `TWAut u J Empty D T` (`PM/ThetaCoefficientMapEq.lean:230`). This consists of:
  - the Hida module M, free and finite over Λ = O[[D]] with D = n·d, and with Supp_B M = V(J) (`TWBase`, `:163-175`);
  - for each N, a ring R_N with a module M_N ≅ (Λ[[x_{j,i}]]/((1+x)^{l^{a_j}} − 1))^{rk}, i.e. free over Λ[Δ_N] with
    Δ_N ≅ (ℤ/l^{a})^{q·n} (`TWRing`, `:185-205`);
  - maps φ, ψ between M_N/𝔞 and (Sp ⊗ M) whose composites are multiplication by f = fEl = ∏(u_i − u_{i′})(u_i − Nq·u_{i′})
    (`TWMaps`, `:213-226`). This is "isomorphic after inverting the Taylor–Wiles eigenvalue discriminant", as in
    Skinner–Wiles;
  - local–global compatibility at the Taylor–Wiles primes, up to f^{ex} (`rel1`, `rel2`).
- Points `Pt T u (D + n q)` (`:165-174`). Each is an NP x with:
  - a Selmer basis `Kap`;
  - eigenvalues al of the Taylor–Wiles Frobenii, distinct in K[[t]];
  - **B1**: #Sel1 ≤ #Bd1 · |K|^{m·D0 + C};
  - **B2**: an obstruction bound.

**Output, `ChainConcl`.** For thick links e_i under consecutive points and a stable modular q₁ under x₀, every stable or
thick q under x_h contains J.

### 1.4 `Choice` (`:223-230`, proof `PM/AutomorphicDetection/Choice.lean:155-181`)
**Hypotheses:**
- l ≠ 2;
- `PhiCond` (finitely many open index-l subgroups);
- ε mod l nontrivial on G_L;
- N3 at every point.

**Output:**
- finitely many σ_a ∈ G′, whose charpoly is separable and split after extending coefficients;
- which detect every dual class (`Detects`).

**Proof:**
1. S, the set of σ ∈ G′ that are separable for all points, is dense in G′ (`omDense`, from N3).
2. `detection`: if a dense S is given, then `Detects` holds.
3. `detFin`: some finite subset still detects.
4. The eigenvalues are split.

**`Detection`** (`PM/AutomorphicDetection/Detection.lean:6`) reduces to `detAsm` (`PM/DeterminantPadicFree/DetAsm.lean`).
- Statement: a twisted dual cocycle z for the thickened representation ρ₁ = (1 + Σ ε_j κ_j)ρ over DD(K[[t]], g), whose
  η-trace tr(z(σ)ρ₁(σ))_η vanishes on all of G′, is t^s times a coboundary.
- The algebra behind it is `detAlg` (`PM/DeterminantPadicFree/DetAlg.lean:71`).

## 2. Argument (as mathematics)

### 1. Reduction (`raw_main`, `PM/SeparableMatrixStability/RawMain.lean:12`; `coreBC`, `PM/AutomorphicDetection/CoreBC.lean:24`)
- Pass to a pro-l quotient.
- Extend O to O′ with residue field of size #K.
- Replace B, Λ by (O′ ⊗ B)[[s]] (`Til`, `PM/PatchingBaseChange/AlgebraMapEq.lean:10`), so that s ↦ t at the points.
- This gives `Core` (`PM/AutomorphicDetection/LiftPt.lean:76`), with Λ = O[[s, w₁..w_D]].

### 2. Ultraproduct patching (`s4`, `s5`; `S5` statement `PM/PatchedSupportCompletions.lean:50-70`)
- This is the standard ultrafilter patching of the M_N into M∞, which is free over S∞ = Λ[[q·n]].
- Output, for each point x_i with f ∉ q_i: a completion B_i of R∞ at q_i, and an ideal S_i (the support of M∞) such that:
  - every minimal prime of S_i has dimension ≥ (1+D) + q·n = 1 + D0 (`dim`);
  - on the fibre where the patching variables vanish, S_i is exactly Supp of the unpatched module (`fib`);
  - support components are global (`move`).

### 3. Galois side at one point (`galOut`, `PM/AutomorphicDetection/GalOut.lean:39`)
**Ingredients:**
- `s6` (`PM/AutomorphicDetection/S6.lean:65`) builds a GMA-type representation `URep` over Bh: a commutative ring
  AA = Bh ⊕ N with N·N ⊆ m_Bh, and off-diagonal entries in N.
- `cohLim` turns B1/B2/Detects into the limit statements K1/K2/K3:
  - **K1**: the tangent of the W1-deformation has rank ≤ D0;
  - **K2**: even classes lift;
  - **K3**: off-diagonal Selmer is spanned by the κ_j.
- `pres` (`PM/SelmerScaling/AlCSmul.lean:12`) turns these into `Pres D0` (`SelmerSpannedByKappaLaurent.lean:37`):
  - X₁..X_{D0} generate m_Bh modulo m_OO + m² + ired(N);
  - m₁..m_g generate N;
  - Σ_j (Σ_a c_{ija} X_a) m_j ≡ 0;
  - the g² vectors c_{ij·} are independent mod m_OO.

**The two cases:**
- **TypeI** (`presOut0`, `PM/SelmerScaling/PresOut0.lean:9`). Here N = 0, so Bh is a quotient of OO[[D0]]. Every prime
  Z with dim Bh/Z ≥ 1 + D0 is therefore 0, so Z ⊆ Q for all Q. This is "R = T at the nice prime" (Skinner–Wiles).
- **TypeE** (`presOut1`, `PM/SelmerScaling/CotangentIndependentOfResidues.lean:74`).
  1. AA is a quotient of OO[[X, M]] by the relations ζ·M, with ζ = Y − (higher-order terms).
  2. det ζ annihilates N.
  3. Every irreducible-type Z (ired ⊄ Z) of dimension ≥ 1 + D0 is the generic point of {YM = 0, det Y = 0}
     (`under_le_of_det_mem`, `AlgebraTools/CaDetCore.lean:9`).
  4. That locus contains every Q with det ∈ Q. That covers thick Q (because `URep.thick` gives ann N ≤ Q) and stable Q.

### 4. Chain (`chainAbs`, `PM/AnnihilatorBaseChange/ChainAbs.lean:7`)
1. At x₀, the modular stable q₁ lies in the support. Take a minimal support prime Z₀ ⊆ q₁; it is stable, because
   stability generises.
2. By step 3, Z₀ contains the thick link e₀.
3. Through `move`, the same global component passes through x₁, and is again stable and big.
4. Induct along the chain.
5. At x_h, every stable or thick q lies on it, so q ∈ Supp M∞ ∩ fibre = V(J).

### 5. Numerology
- The patched dimension is 1 + n·d + n·q.
- The tangent bound is D0 = n·d + n·q (`W1_bound_arithmetic_rank_two`, `PM/EpsilonEtaMatrices/W1BoundArithmeticRankTwo.lean:40`).
- These coincide exactly, as they should for definite U(n) (ℓ₀ = 0).
- **Why g does not change D0.** For W1, the local count at v is m·(n(d′_v + 1) + ν(1 + d_v)). The ν-terms (strictly
  upper-triangular coordinates) cancel against the archimedean skew part, which has the same count ν (`sum_exp`,
  `cancel_pow`, `:30-38`). So only the n diagonal entries survive, giving n·d whatever g is. *(inferred)* This is the
  correct Panchishkin-type count.

### 6. Local propagation (d) (`CDS/PropagationTheoremGL3.lean:80-120`; `FSV/ChainedOfComap.lean:72`; `CDS/FlipTwoThree.lean:15-55`)
**`sharp3`.**
- At an endoscopic residual point x, the unpatched local ring has the same determinantal shape:
  O′[[a + g]]/(f, M·X_off) with a = b + D.
- Sharp I = (det M) is **chained** in codimension 1 (`detsec`). This is a Hartshorne-type connectedness result for this
  explicit presentation, not an abstract S₂ argument.
- I contains every non-endoscopic prime.
- Its components are TI or Thick (`dich`). Triangular primes are excluded by the dimension bound
  `krull_dim_lt_of_not_le_triangular`, which uses `Big`/C₀.

**Nice primes on the links.** `l53` provides an ideal I₃ coming from the n = 2 run: every TE prime is I₃-modular. Hence
TE/thick loci are Λ-finite, and `exists_nice_prime_above_of_large_dim` puts a nice TE prime on any intersection of
dimension ≥ 3d + 1.

**`locProp`/`flipTwoThree`** then carry goodness across thick components through chains of nice TE points. Those chains
are exactly the input of P23′ ← P3core (`CDS/SecondThirdPrimeConditionTransferAlt.lean:98`).

## 3. Children

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `presOut1` + `under_le_of_det_mem` | `PM/SelmerScaling/CotangentIndependentOfResidues.lean:74`; `AlgebraTools/CaDetCore.lean:9` | determinantal local model ⇒ unique big irreducible-type component through a TypeE point | **core, new**, proved (pure commutative algebra) |
| 2 | `pres` / `claim1` / `linAlg` | `PM/SelmerScaling/AlCSmul.lean:12` | K1/K2/K3 ⇒ presentation with g² + e ≤ D0 | **core, new** (the Ext condition, derived); `claim1` not opened |
| 3 | `s6` (`idem`, `gr_E`, `urep_of`) | `PM/AutomorphicDetection/S6.lean:65` | GMA-type representation over the completion at a TypeE point, with thick ⇒ ann N ≤ Q | core; standard in spirit (Bellaïche–Chenevier); bodies not opened |
| 4 | `b1Ar` → `W1_bound_arithmetic_rank_two` | `PM/AutomorphicDetection/BoundW1Arithmetic.lean:7` | Greenberg–Wiles bound for Sel1 of the thickened ρ₁ | core; assumes `CohP` (published Galois cohomology); `oneLevel`, `locV`, `dualN` not opened |
| 5 | `b2Ar` | `PM/AutomorphicDetection/TaylorWilesObstructionBound.lean:62` | obstruction bound via duality | core; body of `obstructionBound_of_duality` not opened |
| 6 | `detection` / `detAsm` / `detAlg` | `PM/DeterminantPadicFree/DetAsm.lean`; `DetAlg.lean:71` | trace-vanishing on G′ ⇒ coboundary, for the κ-thickened ρ₁ | core; partly read |
| 7 | `choice` | `PM/AutomorphicDetection/Choice.lean:155` | Taylor–Wiles σ's from N3 | glue over 6 plus `omDense`, `detFin` |
| 8 | `HasAut` (`TWAut` existence) | `PM/TaylorWilesObstructionBound.lean:147`; `DTC/PaLevel.lean:54` | Hida modules at Taylor–Wiles level, free over Λ[Δ], isomorphic after inverting f, local–global at Q | **core automorphic input, not opened** |
| 9 | `s5`, `s4` | `PM/AutomorphicDetection/AnnBc.lean:69`; `Imports.lean:5` | ultraproduct patching; limit group | standard (Scholze-style ultrapatching), not opened |
| 10 | `sharp3`, `detsec`, `krull_dim_lt_of_not_le_triangular`, `l53`, `preconnected_rank_three` | `FSV/ChainedOfComap.lean:72`; `CDS/PropagationTheoremGL3.lean:213` | local determinantal presentation and connectedness; triangular locus small; TE ⇒ n = 2 modular | core; statements read, bodies not opened |
| 11 | `niceOf`, `n4Of` | `CDS/NiceOf.lean:7`; `CDS/EveryPointSatisfiesFrameConditionAlt.lean:142` | nice prime ⇒ N1/N3/Type; v0 ⇒ N4 for every point | core-ish; read the top level only |

## 4. Oddities

1. **`Raw` takes `TWAut … Empty`, while `Core` takes `… Unit`.** The extra variable is the adjoined s of `Til`
   ((O′⊗B)[[s]]). This is harmless: the dimension rises by 1 on both sides.
2. **`Glob.frame` sets `D0 := ⊥`** (`PM/PairedDualFirstOrderDualMatrixSpace.lean:73`). Literally, N4 at ⊥ is false. The
   N4 that is used is always taken at the original `V0.frame.D0` (`Norm`, `b1Ar`), so there is no vacuity. Still,
   `ModIn.n4` (∀ points, N4) is worth checking for non-emptiness of D0. It comes from `absolute_irreducible_rank_four R.v0`,
   which I did not open.
3. **Points live on K[[t]], not K((t)).** All Selmer statements hold "up to t^s". So K3 (no growth of the off-diagonal
   Selmer group at Taylor–Wiles level) relies on charpoly separability over K((t)). This is correct only up to torsion,
   which is how it is stated.
4. **Thorne's condition is replaced, not removed.** Thorne's requirement that the reducible locus be small is replaced by
   the two-component determinantal model. The {M = 0} component may have full dimension 1 + D0; that is harmless, because
   only irreducible-type and thick primes are claimed modular.
5. **The literal statements are fine.** No vacuous quantifier was seen in P1core, P3core or ChainConcl: chains with h = 0
   give P2core (`:309`), and the seed q₁ is a real hypothesis.

## 5. Coverage

### Read
- PROTOCOL (Explainer section); NODE-MODU3 (all); SUMMARY §11.
- `PM/PatchedSupportCompletions.lean` (all); `PM/ThetaCoefficientMapEq.lean` (all);
  `PM/PairedDualFirstOrderDualMatrixSpace.lean` (all); `PM/TaylorWilesObstructionBound.lean` (all).
- `PM/ChebotarevFamilies/PFromAutOf.lean` (all); `PM/AutomorphicDetection/{PfromAut,Raw,Choice,CoreBC,GalOut,S6,CohLim,Detection,BoundW1Arithmetic,TaylorWilesObstructionBound}.lean`;
  `LiftPt.lean:43-177`.
- `PM/SeparableMatrixStability/RawMain.lean`; `PM/SelmerScaling/{SelmerSpannedByKappaLaurent:1-200, PresOut0:1-40, CotangentIndependentOfResidues, AlCSmul:1-92}`;
  `PM/AnnihilatorBaseChange/ChainAbs.lean`.
- `PM/EpsilonEtaMatrices/{B1abs, W1BoundArithmeticRankTwo}`; `PM/DeterminantPadicFree/DetAsm.lean:1-120, 200-268`; `DetAlg.lean:1-120`.
- `PM/PatchingBaseChange/{AlgebraMapEq:8-20, AutBc:10-22, Oprime:104-116}`; `AlgebraTools/CaDetCore.lean:1-30`.
- `WGC/UniversalOrdinaryDeterminantRing.lean:60-80, 185-312`.
- `CDS/{PropagationTheoremGL3 (all), PropagationTheoremGL2:10-50, SecondThirdPrimeConditionTransferAlt:36-111, NiceOf, NiceSpecializationTwistSatisfiesThirdCondition:1-60, FlipTwoThree:15-75}`.
- `FSV/{ChainedOfComap:1-140, Integral:90-105, LeAdicClosure:255-280}`; `EveryPointSatisfiesFrameConditionAlt:142-145`.

### Not opened
- `claim1`, `linAlg`, `dualEx`, `tpDual`, `alSel`;
- `oneLevel`, `locV`, `dualN`, `h0v0`, `obstructionBound_of_duality`;
- `s5`, `s4`, `idem`, `gr_E`, `urep_of`, `discImp`, `kapEx`, `detFin`, `omDense`, `oddPart`/`evenPart`;
- `HasAut`/`HasAutOfAlt` and its proof (the automorphic Taylor–Wiles-level input);
- `detsec`, `epres`, `thick`, `l53`, `locProp`, `globProp`, `preconnected_rank_three`, `exists_nice_prime_above_of_large_dim`;
- `niceTypeE`, `niceIrr`, `absolute_irreducible_rank_four`, `CohP` formalisations.
