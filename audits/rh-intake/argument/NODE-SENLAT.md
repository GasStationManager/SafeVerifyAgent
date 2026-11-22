# NODE-SENLAT: `SenLat` (adm21), the closeness lemma, `Gauge.main`, the Herr-complex inputs, and a GL₃ test

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my own reading. **(mine)** marks my own computations. Nothing was compiled or run.

Abbreviations:
- `TL2` = `Formalism/SharpRestriction/LevelLetterCocycles/TableLineDegreeTwo.lean`
- `IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- `AEZ` = `IE/AevalEqZeroOfDiag.lean` (proof of `SenLat`)
- `DIL` = `Formalism/SharpRestriction/LevelLetterCocycles/DeltaInvariantLattices.lean`
- `DQE` = `Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/DiagonalQuotientEigen.lean`
- `CL` = `IE/CompletionLines.lean`
- `PG` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean`
- `GM` = `IE/CoeSmulMem.lean` (`Gauge.main`)
- `NBW` = `IE/NabBijectiveWindow.lean`
- `CV` = `IE/CloseVectorNeZero.lean`
- `CT` = `IE/PhiGammaLatticeFamiliesShiftInclusion.lean`
- `BKT` = `IE/BlochKatoTopOfLocalTateDualityEulerChar.lean`

## 0. Verdicts

**No ESCALATE.**

| Q | Answer | Status |
|---|---|---|
| 1 `SenLat` | It is an exact, characteristic-0 statement about the Wach module N(T) of **every** crystalline O-lattice T, with no weight bound. It gives the O-ranks of the χ(γ)^{−x}-eigenspaces of γ on (q^{−y}N^Δ_i)/(q^k N^Δ_i). Its content is Berger's "N ⊗ B_dR⁺ = Fil⁰(D_dR ⊗ B_dR)". It is **proved in-tree**, not admitted: `stmtSen` (AEZ:576) → `senLat_of_coeff` → `senLat_of_tie` → `clauses_of_lines`/`diag_quot`. The analytic input is P4 = `lattice_at_level`, which rests on `lat_eq_fil` and `PerS.image`. The rank-1 test (mine) agrees with the Lean, sign of x included, and the direction of the label shift in σ matches. | proved and read down to `lat_eq_fil`; `PerS.image` statement only |
| 2 closeness | Proved and read (CT:12-34, `CV.le_sg`, `CV.key` statement). The bound X^{σ_i}N₁ ⊆ N₂ with σ_i = ⌊Σ h_{i+j+1}/l^{j+1}⌋ is correct, and **sharp** in rank 1 (mine). | proved and read |
| 3 Herr facts | `HerrLat` (adm16), `HerrSub`/`HerrExt` (adm17), and Tate duality + Euler characteristic for finite Z/l^r-modules (adm18) are all standard: Fontaine's equivalence, Herr's theorem for Γ = Δ × Γ₁ via Δ-invariants, and Tate. adm16 and adm17 are proved in-tree. adm18 is a Published hypothesis of `blochKatoTop_of_localTateDuality_eulerChar_alt`. | statements read; discharges read to statement level |
| 4 `Gauge.main` | Proved and read (GM:57-149). Reconstruction in §4. | proved and read; `nab_bijective_window` statement and induction read; `one_sub_frob_bij` statement only |
| 5 GL₃ | The dsum = dim H¹_f identity holds (by construction, checked). The "weight-swapped reducible lift" mechanism, which is the only one I can compute, is excluded exactly by T2/T3, with explicit numbers in §5. I found no case allowed by T1–T3 with a known extra class. Irreducible 3-dimensional lifts cannot be tested here. | mine |

**Correction to NODE-TOPCORE §2e.** The eigenvalue of ∇ on X^aN/X^{a+1}N is (Sen weight) **− a**, not + a. The gauge window is therefore a ∈ [0, σ+1], not [1, σ+2]. This matches the Lean's hypothesis sen(N, a) = 0 for a ≤ σ+1 (GM:65) and the polar window [−w, −1] (§4). It changes no conclusion.

## 1. `SenLat` (Task 1)

### 1a. Statement (TL2:365-396, read)

- E := Epol = π₀ + p (TL2:365). By `QFrame` (CL:48-55), J(X) = π₀₁ + p is associated to q₀. *(inferred)* So E is the Δ-invariant "q = φ(π)/π", and (O[[π]])^Δ = O[[E]] through J.
- ENΔ(T, i, y) (TL2:370-374) = {m ∈ D(T) : E^y m ∈ N(T), m in letter i, m Δ-invariant} = (E^{−y}N_i)^Δ.
- EkNΔ(T, i, k) = E^k·ENΔ(T, i, 0) (TL2:376-378).
- SenEig(T, i, y, k, x) (TL2:380-383) = {m ∈ ENΔ_y : (γ − u^{−x})m ∈ EkNΔ_k}, where u = uU = χ(γ) (DIL:257) and γ = W.gam, a topological generator of Γ₁ (χ(γ) = 1 + l, `gamK_eq_gam`, TL2:442-446).

`SenLat W` (TL2:385-396) says: for every lattice T with T ⊗ Q crystalline, every label i, every τ over i, and all y, k ≥ 0:
1. Q_{y,k} := ENΔ_y / (EkNΔ_k ∩ ENΔ_y) is free and finite over O.
2. γ is killed on Q_{y,k} by some Π_{x∈F}(γ − u^{−x}).
3. For every x ∈ ℤ, rank_O(SenEig_x mod EkNΔ_k) = Σ_{j=1−k}^{y} mult_τ(x − j), where mult_τ(a) is the multiplicity of the Hodge jump a at τ, with the Lean convention jump(ε) = −1.

**Precision and lattice.**
- The statement is exact, in ℤ and over O. It is not mod l.
- It is about the Wach module of each crystalline lattice. When h ≥ l nothing changes: no hypothesis bounds the weights.
- Clauses 1 and 3 together amount to the rational statement plus O-freeness. The O-rank of a saturated sub-lattice is the LL-dimension of the rational eigenspace.
- So the "integral" form adds only freeness of Q_{y,k}. *(inferred)* That freeness follows from N^Δ being O[[E]]-free (`wach_free`, `exists_invariant_basis`, AEZ:568-570).
- **The mod-l statement is not in `SenLat`.** It is derived downstream (`senMultiset_base_lattice_eq_jumps_mod`, statement only per TOPCORE). *(inferred)* The derivation is sound for every weight:
  - Clauses 2–3 give the characteristic polynomial of γ on the free module N^Δ/EN^Δ as Π(X − u^{−x})^{mult(x)}.
  - The Wach condition gives (γ−1)N^Δ ⊆ π₀N^Δ, and π₀ ≡ −p mod E.
  - So ∇ = (γ−1)/π₀ acts on N^Δ/EN^Δ as (γ−1)/(−p). Its characteristic roots are cc(l, −x) = ((1+l)^{−x} − 1)/(−l) ≡ x mod l (`cc`, DQE:13).
  - Since E ≡ π₀ mod p, reducing mod λ gives N̄/XN̄. Its generalised ∇-eigenvalue multiplicities are #{jumps ≡ x mod l}.

### 1b. Discharge on the live route (read)

- `blochKatoTop_of_localTateDuality_eulerChar_alt` (BKT:25-42) obtains `a21` from `GlobalTheory.SenMult.stmtSen D HW F Cm ⟨a2, a4, a5, a9, a11⟩` (BKT:39).
- The inputs a1–a15 come from `wachLattice_laterClauses_hold` = `NL.wach_used_clauses` (`IE/WachLatticeLaterClausesHold.lean:28-38`). In particular P4 = `T.wach_lattice_expansion_at_low_level_points` = `NL.LatLevel.lattice_at_level`.
- `stmtSen` (AEZ:576-579) → `senLat_of_coeff` (AEZ:538-572) → `senLat_of_tie` (AEZ:497-534) → `clauses_of_lines` (AEZ:447-495), `diag_quot` (AEZ:257-344), `ENΔ_eq`/`EkNΔ_eq` (AEZ:347-388), `count_pairs` (AEZ:390-409), `lines_of_coeff` (AEZ:411-445). All proved and read.

**The argument, as mathematics.**
1. Choose an adapted basis d_k of D_dR,τ with Fil^a = span{d_k : u_k ≥ a} (`adapted_basis`).
2. P4 says the expansion map `levN` at the point π = ζ_l − 1 (a power series in t, on which γ acts by t ↦ χ(γ)t) sends N onto ⊕_k t^{−u_k} d_k LL[[t]]. This is `SpanIsLines`, CL:28-31, via `lines_of_coeff` from the P4 clauses (DIL:159-175).
3. In these coordinates, γ acts on the coordinate k by χ^{−u_k}·(t ↦ χt) (`hγ` in `diag_quot`).
4. Therefore E^{−y}N/E^kN, which `ENΔ_eq` identifies with qN(−y)/qN(k), is diagonalisable over LL. Its eigenvalues are χ^{j − u_k} for j ∈ [−y, k−1].
5. Counting the pairs (`count_pairs`) gives Σ_{j∈[1−k, y]} mult(x − j).

**Where the real content sits.**
- P4 is proved by `lattice_at_level` (`IE/WachLatticeExpansionAtLowLevelPoints.lean:66-163`, read). That proof rests on `LatFil.lat_eq_fil` (`IE/WachLatticeEqFiltrationSumAtLevel.lean:423-480`, read).
- `lat_eq_fil` says that the span of expansions = {f with every f_k ∈ D_cris and in Fil^{−k}}. This is Berger's "N ⊗_{ι} K_n[[t]] = Fil⁰(D ⊗ K_n((t)))". Its proof rests on `T.wach_image_deRham_plus_component_level` = `NL.PerS.image`. That gives Ψ : N → V ⊗ B_dR⁺ with image generating Fil⁰(V ⊗ B_dR) modulo `compKer` (`IE/WachImageDeRhamPlusComponentLevelStatement.lean:7`; `IE/WachImageDeRhamPlusComponentLevel.lean:409`). I read its statement only.
- *(inferred)* So `SenLat` is Berger's theorem, derived in-tree from the Wach-module construction. Per NODE-BEYONDFL, that construction is ultimately Bhatt–Scholze. It is **not** an independent new admitted theorem.

### 1c. Rank-1 test **(mine)**

**Setup.** K unramified of degree n, letters i ∈ ℤ/n, φ_i : N_{i−1} → N_i (PG:74-75 convention). Let N = ⊕ O[[π]]e_i with φ(e_{i−1}) = q^{a_i}·(unit)·e_i and γ(e_i) = c_i e_i, c_i ≡ 1 mod π.

**Eigenvalue at the point.**
- φγ = γφ gives c_i = φ(c_{i−1})·(q/γ(q))^{a_i}.
- At π = ζ_l − 1, where q has a simple zero: φ(c_{i−1}) ↦ c_{i−1}(ζ^l − 1) = c_{i−1}(0) = 1.
- With 1+π = ζe^s, q/γ(q) → (ζ^{χ} − 1)/(χ(ζ − 1)). For γ ∈ Γ₁ (χ ≡ 1 mod l) this equals χ^{−1}.
- So γ acts on N_i/qN_i by χ^{−a_i}: **the Sen weight x of N_i equals the φ-height a_i of φ_i**.
- Hence ∇ ≡ cc(l, −a_i) ≡ a_i mod l. This matches `SenLat` with y = 0, k = 1 (mult(x) at x = a_i) and the Lean's sen(N_i, ·) ≡ jumps − w_i.

**Labels.**
- The Lean attributes both the height of φ_i (ABC/`CondAB`, PG:74-75; TOPCORE §1c) and the Sen weights of N_i to label i. My computation shows these are the same embedding, so the Lean is internally consistent.
- Berger's description Fil^j = {x : φ(x) ∈ q^jN} attributes height(φ_i) to the source component of D_cris. The ζ_l-point expansion is ι₁ = ι₀∘φ^{−1}, which attributes it to the same component. These agree.
- Whether "label i" in `Over emb i τ` is the right embedding is fixed by `ptK`/`IsPt` and the proved `lat_eq_fil`. It is not a free convention left open.

**Direction of the shift in σ.**
- With φ_i : i−1 → i, the closeness recursion is s_{i−1} ≤ ⌊(s_i + h_i)/l⌋ (CT:19-31, read).
- Hence s_i ≤ Σ_j h_{i+j+1}/l^{j+1}. This is `sg` (PG:77-78, read: `h (i + (j+1))`).
- **The Lean's direction matches** (the weight at letter i+j+1 enters with weight l^{−(j+1)}).

## 2. Closeness lemma (Task 2)

**Statement** (`IE/PhiGammaLatticeFamiliesShiftInclusionStatement.lean:8`). Let N₁, N₂ be lattice families. Suppose both satisfy CondAB with exponents (w, h − w), that is ⟨φN_{i−1}⟩ ⊆ X^{−w_i}N_i and X^{h_i−w_i}N_i ⊆ ⟨φN_{i−1}⟩. Then X^{σ_i}N₁,i ⊆ N₂,i. No γ condition is used.

**Proof** (CT:12-34, read).
1. Let a_i be the least a with X^a N₁,i ⊆ N₂,i (`exists_pow`).
2. For x ∈ N₁,{i−1}: X^{w_i}φx ∈ N₁,i, so X^{a_i+w_i}φx ∈ N₂,i ⊆ X^{−(h_i−w_i)}⟨φN₂,{i−1}⟩.
3. `CV.key` (CV:144, statement): if X^mφx ∈ ⟨φN⟩ then X^{⌊m/l⌋}x ∈ N. This uses φ(X) = X^l·unit (`R.φ_v`) and étaleness.
4. Hence a_{i−1} ≤ ⌊(a_i + h_i)/l⌋.
5. `le_sg` (CV:311-330, read) iterates this around ℤ/n to a_i ≤ σ_i.

**Rank-1 sharpness (mine).**
- Take N₂ = X^{s}N₁. CondAB requires l s_{i−1} − s_i + c_i ∈ [−w_i, h_i − w_i], where X^{c_i} is the φ-matrix.
- With c_i = −w_i, this allows l s_{i−1} − s_i up to h_i. The maximal solution is s_i = Σ h_{i+j+1}/l^{j+1}.
- For n = 1 this is h/(l−1). So σ is attained up to the floor.

**Normalisation.** X ~ π^{l−1} ~ q mod l, and φ multiplies X-valuation by l. In π-adic terms the ambiguity is π^{≈h(l−1)/(l−1)}, which is the familiar "height h, divided by l−1". **Correct.**

## 3. Herr-complex and duality inputs (Task 3)

| Fact | file:line | Statement | Discharge (read) | Matches literature? |
|---|---|---|---|---|
| `HerrLat` (adm16) | TL2:316-338 (adm16 TL2:434-436) | For every lattice T: (a) the class map from Δ-invariant Herr 1-cocycles (`CocΔ` = `herrZ1Δ`, TL2:313-314) to H¹(G_K, T) is surjective, with kernel {((φ−1)m, (γ−1)m) : m Δ-invariant}; (b) naturality; (c) T^{G_K} ≅ D(T)^{φ=1, γ=1, Δ} (`fixDD`, TL2:309-311); (d) D is fully faithful on lattices; (e) D is exact on short exact sequences of lattices; (f) ψ on the coefficient ring EE with ψ(φa·x) = a ψx, Γ-equivariant, the (1+π)^j-basis property, and decomposition; (g) ψ on D(T), left inverse of φ | BKT:34-35: `herr_lattice_of_fon` from `herr_part_a_every_record` (`IE/HerrPartAEveryRecord.lean:8-11` → `herr_a_and_natural`, `IE/HerrAAndNatural.lean:16-24`, from `fontaine_decompletion`; inner proofs not opened), `invariants_statement_holds`, `fontaine_fullFaithful_exact_psi` | Yes. Herr (1998) for Γ_K ≅ Δ × Γ₁ with l ≠ 2: H^i(Γ, ·) = H^i(Γ₁, ·)^Δ because \|Δ\| is prime to l. Fontaine's equivalence. Integral, for lattices, H¹ only. |
| `HerrSub` (adm17a) | TL2:345-350 | Every (φ, Γ)-stable E-submodule D′ ⊆ D(T) containing p^aD(T) is D(T′) for a finite-index sublattice T′ | BKT:36-38: `exists_lattice_of_pow_mem` | Yes (Fontaine's equivalence on the torsion quotient) |
| `HerrExt` (adm17b) | TL2:352-363 | For 0 → T → T_p → 1 → 0 and a Δ-invariant lift e of the unit: the Herr class of ((φ−1)e, (γ−1)e) equals the Galois class of g ↦ ρ(g)x − x | BKT:38: `extension_rule` | Yes (standard compatibility; the sign is consistent: both are "δ(lift)") |
| adm18 | TL2:453; `Formalism/GaloisCohomology/LocalTateDualityK.lean:47-61` | For finite discrete Z/l^r[G_K]-modules M: H²(μ) ≅ Z/l^r; the cup products H⁰×H², H¹×H¹ (both sides), H²×H⁰ into H²(μ) are perfect; #H¹ = #H⁰·#H²·#M^{[K:Q_l]} | **hypothesis passed down**: arguments `hdual`, `heul` of BKT:25 (Published) | Yes (Tate local duality and the Euler characteristic formula, exactly as stated) |
| adm19 `BlochKatoJumpDimension` | TL2:233-246 | dim H¹_f(V) = dim H⁰(V) + Σ_τ #{jumps < 0}; saturation of the lattice H¹_f; `UnrTriv` | BKT:42: `blochKato_dimension_saturation_unramified` (`IE/BlochKatoDimensionSaturationUnramified.lean:166`, statement only) | Yes (Bloch–Kato 3.8 with jump(ε) = −1; saturation holds by definition of the integral H¹_f as a preimage) |

**Mod-λ^a use.** No Herr fact is admitted at torsion level.
- The residual (φ,Γ)-module of a torsion A is reached through `realD`/`Pres`: D(T)^Δ ↠ F(A) with kernel D(ker q) (TOPCORE §1b).
- The only residual Herr fact the count needs is "Herr coboundary ⇒ Galois coboundary" (`indep_pairs`, ADM:39-58, read by TOPCORE). *(inferred)* It follows from `HerrLat`(a) on lattices together with `Pres.j_ker`.
- Tate duality and the Euler characteristic enter only through Vanish/FreeH (TOPCORE §2f).

## 4. `Gauge.main` (Task 4)

**Statement** (GM:57-74, read). Setting:
- k of characteristic l; D an étale (φ_i, γ_i)-module over k((X)) with letters ℤ/n.
- Lattices N_i satisfying CondAB(w, w′) and CondC ((γ−1)N ⊆ XN).
- Integers s_i ≥ 0 with s_i + 1 ≤ l(s_{i−1}+1) − w_i.
- sen(N_i, a) = 0 for a = 0, …, s_i+1.

Let (b, g) be a Herr cocycle, (γ−1)b_i = φ_i g_{i−1} − g_i, with g_i ∈ XN_i. Then:
- **(G1)** There is m ∈ N with g − (γ−1)m ∈ X^{s+3}N.
- **(G2)** If g ∈ X^{s+3}N and b ∈ N, then (b, g) = ((φ−1)m, (γ−1)m) for some m ∈ N.

**Proof** (GM:75-149, read).
- **Window lemma.** On X^aN/X^{a+1}N, ∇ = X^{−1}(γ−1) has eigenvalues (Sen weight) − a. This uses γ(X) = X(1 − κX) with κ(0) = 1, and `gam_zpow` (NBW:63). `nab_bijective_window` (NBW:219-235, statement and induction read): if sen(N, a + j) = 0 for j < m, then ∇ is injective and surjective modulo X^{a+m} on X^aN.
- **(G1).** Apply the window lemma with a = 0, m = s + 2 to y = X^{−1}g ∈ N. Choose x with y − ∇x ∈ X^{s+2}N. Then g − (γ−1)x = X(y − ∇x) ∈ X^{s+3}N.
- **(G2).**
  1. (γ−1)b = φg_{i−1} − g_i. By `phi_sh` (GM:16-33) and the recursion, φ(X^{s_{i−1}+3}N) ⊆ X^{l(s_{i−1}+3) − w_i}N ⊆ X^{s_i+3}N.
  2. So ∇b ∈ X^{s+2}N, and window injectivity gives b ∈ X^{s+2}N.
  3. On the family X^{s+2}N, φ maps letter i−1 into X·(letter i), because l(s_{i−1}+2) − w_i ≥ s_i + 3. So 1 − φ is bijective there (`one_sub_frob_bij`, statement only; geometric series).
  4. Choose m ∈ X^{s+2}N with (φ−1)m = b. Then g′ = g − (γ−1)m lies in X^{s+2}N and satisfies φg′_{i−1} = g′_i. Injectivity of 1 − φ gives g′ = 0.

*(inferred)* This is exactly the Fontaine–Laffaille/Wach-style "Herr cocycles with small g are coboundaries", with the range s = σ coming from closeness.

## 5. GL₃ consistency test (Task 5), all **(mine)**

**Setting.**
- K = Q_l (n = 1), t = 1, block {w}, typ G, σ = ⌊h/(l−1)⌋.
- ρ is 2-dimensional crystalline with Lean jumps U = {u₁, u₂}, residually irreducible.
- The extension E has ρ̄χ̄₁^{−1} as sub and 1 as quotient, with jumps d_i = u_i − w.

**(a) dsum = BK, by construction.**
- dsum = #{u ∈ U : u < w}.
- BK (TL2:233-238) for ρχ₁^{−1}: dim H¹_f = dim H⁰ + #{d_i < 0} = #{u_i < w}, because H⁰ = 0.
- **They agree.** Example: l = 101, w = η = 10, u₁ = 3 (low; |3 − 10| = 7 > σ + 2), u₂ = 160 (cloud), h = 161, σ = 1.
  - T1: 10 + 4 + 6 = 20 < 101.
  - T3 window [−4, 15]; 160 ≡ 59, so allowed.
  - dsum = 1 = dim H¹_f. dim H¹(ρ̄′) = 2 by the Euler characteristic.

**(b) Weight-swapped reducible lifts (the computable source of extra classes).**
- A reducible crystalline lift V′ = (W * ; 0 χ) of E with weights U ∪ {w} must have W lifting the irreducible ρ̄′, so χ is a character with χ̄ = χ̄₁.
- If χ carries the jump u_i instead of w, then χχ₁^{−1} is crystalline of jump d_i with trivial reduction, which forces (l − 1) | d_i.
- The extension class then lies in H¹_f(W ⊗ χ^{−1}), whose jumps {w − u_i, u_j − u_i} can both be negative. That would give up to 2 > dsum classes.
- **Exclusion.**
  - Write d_i = m(l−1) with 1 ≤ m ≤ h/(l−1), so m ≤ σ. Then u_i ≡ w − m ∈ [w − σ, w − 1] mod l.
  - For a cloud weight, this lies inside the T3 window [−2σ−2, η+2σ+3]: **excluded by T3**.
  - For a low weight, |d_i| < l − 1 forces d_i = 0, i.e. u_i = w: **excluded by T2**.
- Explicit: l = 101, w = η = 1, u₁ = 160, u₂ = 201 (d₂ = 200 = 2·100), h = 202, σ = 2.
  - T3 window [−6, 8]; 201 ≡ −1, so **excluded**.
  - The neighbouring allowed choice u₂ = 250 (≡ 48) has d₂ = 249, which is not ≡ 0 mod 100, so no swapped lift exists.
- So T3 is exactly calibrated against this mechanism, by the same digit identity as BEYONDFL §2b.

**(c) What I could not test.**
- Irreducible 3-dimensional crystalline lifts, which need Herzig/BM-type information for GL₃(Q_l) with weights ≫ l. None is available to me.
- Whether two different crystalline lifts W, W′ of ρ̄′ with the same weights reduce H¹_f to the same line in H¹(ρ̄′). The Lean claims yes. This is uniform through N^max ⊇ every model, and §§2, 4 hold for all ranks.
- I found **no configuration allowed by T1–T3 with a known extra class**. No ESCALATE.

## 6. Children

| # | Name | file:line | Statement | Role | Weight / status |
|---|---|---|---|---|---|
| 1 | `SenMult.stmtSen` → `senLat_of_coeff` → `senLat_of_tie` | AEZ:576, 538, 497 | `SenLat` from P4 + Wach freeness + D_cris = D_dR | discharge of adm21 | core; proved, read |
| 2 | `clauses_of_lines`, `diag_quot`, `ENΔ_eq`, `count_pairs` | AEZ:447, 257, 347, 390 | diagonalisation of γ on E^{−y}N/E^kN | algebra of SenLat | glue/core; proved, read |
| 3 | `lattice_at_level` (P4) | `IE/WachLatticeExpansionAtLowLevelPoints.lean:66` | expansions at ζ_l lie in D_cris ∩ Fil and span | Berger comparison | core; proved, read |
| 4 | `lat_eq_fil` | `IE/WachLatticeEqFiltrationSumAtLevel.lean:423` | span of expansions = Fil-condition | Berger comparison | core; proved, read |
| 5 | `PerS.image` | `IE/WachImageDeRhamPlusComponentLevel.lean:409` | Ψ : N → Fil⁰(V ⊗ B_dR) generating | N ⊗ B_dR⁺ = T ⊗ B_dR⁺ | standard (Berger); statement only |
| 6 | `CloseTw.main` | CT:12 | X^σN₁ ⊆ N₂ | closeness | core; proved, read |
| 7 | `Gauge.main`, `nab_bijective_window` | GM:57; NBW:219 | §4 | gauge | core; proved, read |
| 8 | `one_sub_frob_bij`, `CV.key` | — ; CV:144 | 1−φ bijective on contracting family; φ-pullback valuation | glue | statement only |
| 9 | adm16/17 discharges | BKT:34-38 | Herr, Fontaine | standard | statement only |
| 10 | `LocalTateDualityK`, `LocalEulerCharK` | `Formalism/GaloisCohomology/LocalTateDualityK.lean:47, 57` | Tate | Published hypothesis | standard |

## 7. Oddities

1. NODE-TOPCORE §2e gives the wrong sign for ∇ on graded pieces (see §0). The Lean itself is consistent.
2. `SenLat`'s "integral" form is rational ranks plus freeness. Calling it a new integral theorem (TOPCORE oddity 1) overstates it. The real mod-l content sits in the downstream `senMultiset_base_lattice_eq_jumps_mod` (statement only). I checked that step informally (§1a) and found it sound for all weights.
3. `CompletionLines` (CL:57-66) carries a hypothesis u ≥ 0. `SenLat`/P4 carry none. The live route uses P4, not `CompletionLines`.
4. `BlochKatoLocal` is discarded (BKT:28), as BEYONDFL noted.

## 8. Coverage

Read:
- PROTOCOL, NODE-TOPCORE, NODE-BEYONDFL (all).
- TL2:228-250, 300-505.
- BKT (all); AEZ:1-40, 240-579; DQE:1-60; CL:1-120; DIL:140-200, 330-360, 625-640.
- `InvariantsGenerators.lean:85-95`; `UsedLocalConclusion.lean:1-30`.
- `WachLatticeLaterClausesHold(Statement).lean` (all).
- `WachLatticeExpansionAtLowLevelPoints(Statement).lean` (all).
- `WachLatticeEqFiltrationSumAtLevel.lean:409-482` and its imports.
- `WachImageDeRhamPlusComponentLevelStatement.lean` (all).
- GM:14-151; NBW:219-235 and its theorem list.
- `PhiGammaLatticeFamiliesShiftInclusion(Statement).lean` (all); CV:144-160, 311-330.
- PG:74-79; `LocalTateDualityK.lean` (all); `HerrPartAEveryRecord.lean`, `HerrAAndNatural.lean` (all); `ClassMapInjectiveBijectiveNorms.lean:1-20`.
- `BlochKatoDimensionSaturationUnramified.lean` (theorem list).

Greps run:
- `theorem (GlobalTheory\.SenMult\.)?stmtSen\b`
- `def P4W|def P4 |def SenOperatorTheorem|def DeltaInvariantNormBound|def ptK|def FilC|def ιDi`
- `wachLattice_laterClauses_hold`; `wach_used_clauses`; `wach_lattice_expansion_at_low_level_points`
- `^(def|structure|abbrev) (qN|qΔ|QFrame|qQuot|NΔl|uU|Epol|letπ|letE)\b`
- `Gauge\.main|namespace .*Gauge$`; `shift_inclusion`
- `def LocalTateDualityK|def LocalEulerCharK`; `herr_part_a_every_record`; `def ClassMapInjectiveBijectiveNorms`

Not opened:
- the bodies of `PerS.image`, `herr_a`, `fontaine_decompletion`, `exists_lattice_of_pow_mem`, `extension_rule`, `one_sub_frob_bij`, `CV.key`, `blochKato_dimension_saturation_unramified`;
- `senMultiset_base_lattice_eq_jumps_mod` and the rest of MTP;
- `ptK`/`IsPt`.
