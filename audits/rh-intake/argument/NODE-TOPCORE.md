# NODE-TOPCORE: the beyond-Fontaine–Laffaille comparison `TopCore`, read down to the mod-l Herr/Sen count

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my own reading. My own computations are marked **(mine)**. Nothing was compiled or run.

Abbreviations:
- `TL2` = `Formalism/SharpRestriction/LevelLetterCocycles/TableLineDegreeTwo.lean`
- `PG` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean`
- `TMA` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean`
- `RB` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ResBound.lean`
- `JS` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/JSmul.lean`
- `OPA` = `Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/OnePlusPowerAssembly.lean`
- `IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- `CC` = `IE/CardCocyclesIndependentModCoboundariesLe.lean`, the proof of `card_cocycles_independent_mod_coboundaries_le` (namespace `GlobalTheory.Models.PolarBound`)
- `ADM` = `IE/AdmissibleCocyclesCardLeSumDims.lean` (`AdmBound.main`)
- `MC` = `IE/TwistedPhiGammaModelSenWeightCount.lean` (`ModelCount.count`)
- `SR` = `IE/SenWeightSubquotientModelMemResidues.lean`
- `TOP` = `IE/TwistedLatticeCohomologyTheoremTOP.lean`
- `MTP` = `IE/ExistsModThOfPres.lean`
- `EPT` = `IE/ExistsPresTensor.lean`
- `APE` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/AdmissibleParameterEventually.lean`

## 0. Verdicts

**No ESCALATE.** The cocycle count is a real argument, and I could follow every step of it. It generalises the Fontaine–Laffaille / Wach-module proof of "torsion-crystalline = H¹_f" in a clean way. Large weights are handled by two ingredients:
- Sen weights are only used **mod l**.
- The X^σ closeness of any two φ-lattices of the same height absorbs non-uniqueness, with σ = Σ_j h_{i+j+1}/l^{j+1}.

The genericity hypotheses T2/T3 are exactly what makes the counted window see only the "negative" Hodge–Tate weights.

My tests against the weight part of Serre's conjecture for K = Q_{l²} agree with the Lean in every case its hypotheses allow (§3). In one mixed case the **T2** hypothesis is what removes a genuine extra residual class (§3b). So T2 is sharp, not decorative. I did not complete a GL₃ test (§3d).

The mathematical weight rests on admitted Wach-module facts. The main one is `SenLat` (adm21). These are listed in §4.

| Q | Answer | Status |
|---|---|---|
| 1 | §1 | definitions read |
| 2 | §2: Herr complex of étale (φ,Γ₁)-modules over k((X)), X ≈ π^{l−1}; gauge + polar-part count | `CC` proved and read; `MC`, `SR`, `ADM` proved and read; `Gauge.main`, `phiGamma_lattice_families_shift_inclusion`, `gammaMinusOneDivVariable_polar_kernel_le_senWeights`, `polarPart_finrank_add_senWeights_le_rank`, `senMultiplicity_lattice_count_relation` statement only |
| 3 | Consistent (§3). T2 is needed (§3b) | my computation, conditional on BM-type existence of lifts |
| 4 | Dévissage `adm_eq_H1fX` (§2f); logic sound | statement and call read; `subset_of_bound` statement only |
| 5 | Crystallinity at w ∣ l with HT = automorphic weights is the clause `G2a`. It sits inside `CoreNormFacts.g2` (`DeRhamFamilyAwayAlt`), which is a **hypothesis passed down** to `NLinkE.main_alt_alt` (§5) | read; discharge not located |

## 1. Statements

### 1a. `TopCore emb lam I` (TL2:193-212)

**Setting.**
- G = G_K, K/Q_l finite. The period data `PD` require `CaseA`: K unramified, l ≠ 2 (TL2:398-401).
- LL is a finite extension of Q_l, O ⊂ LL, λ = `lam` irreducible.
- n = number of Frobenius-orbit labels i ∈ Z/n of embeddings K₀ → LL (`Over`, TL2:47).
- I = inertia.

**Hypothesis** `TopHyp` (TL2:180-191):
- t ≥ 1.
- `PositionHyps` (TL2:25-31).
- ρ is a continuous crystalline LL-representation. At every τ over label i, its Hodge–Tate multiplicities are those of the multiset U_i, with Lean weight convention weight(ε) = −1.
- χ_c = χ₁·ε^{−(c−1)} (c = 1..t) are crystalline characters of labelled weight w_i + c − 1.

**`PositionHyps`.** For each i there are data h_i, w_i, η_i, typ_i, with σ_i := sg = ⌊Σ_{j≥0} h_{i+j+1}/l^{j+1}⌋ (PG:77). Conditions:
- U_i ⊂ [1, h_i − 1].
- The block [w_i, w_i+t−1] ⊂ [1, η_i] when typ = G (resp. ⊂ [h_i − η_i, h_i − 1] when typ = Bd).
- **T1**: η_i + 4σ_i + 6 < l.
- **T2**: every "low" u ∈ U_i ∩ window has |u − y| > σ_i + 2 for every block weight y.
- **T3** (`ResidueAvoidance`): every other ("cloud") weight has residue mod l outside [−2σ−2, η+2σ+3]. This is BEYONDFL §2b; I did not reopen HWR.

**Conclusion.** For every finite O-module X, and every lattice T₀ ⊂ ρ with twisted copy T₀′ = T₀ ⊗ χ₁^{−1}:
1. For every continuous 1-cocycle z : G → T₀ ⊗ X for the action χ₁^{−1}ρ: **z is admissible ⇔ z ∈ InHfX**.
   - **Admissible** (`IsAdmCoc`, TL2:172-178; `AdmQ`, TL2:93-98) means: for all a ≥ a₀ with λ^a X = 0, the extension E_a = (T₀⊗X) ⊕ O/λ^a, with action (x, p) ↦ (ρx + p χ₁ z, χ₁ p) (`actExt`/`kerExt`, TL2:132-138), is G-isomorphic to L₁/L₂.
   - Here L₂ ⊂ L₁ are O-lattices in a finite direct sum ⊕_j V_j of "full" representations (`IsFull`, TL2:59-63). Each V_j is continuous and crystalline, has labelled HT multiset U_i + {w_i, …, w_i+t−1} at every τ over i (`jTil`, TL2:33), and has charpoly(g) ≡ charpoly ρ(g)·Π_c(X − χ_c(g)) coefficientwise mod λ.
   - **InHfX** (TL2:140-151) means: z = Σ_j c_j ⊗ x_j + coboundary, with c_j integral cocycles of T₀′ that are crystalline (in H¹_f). That is, z lies in the image of H¹_f(T₀′) ⊗ X → H¹(T₀′ ⊗ X).
2. For c ∈ [2, t], every lattice L_c of χ_c: admissible ⇔ coboundary.
3. For L₁ ⊂ χ₁: admissible ⇔ unramified.

So the statement is **integral**: for X = O/λ^a, "subquotients of crystalline lattices with the same labelled weights and the same residual characteristic polynomial" give exactly the propagated Bloch–Kato condition. It is not only a residual dimension statement.

### 1b. `realD` (EPT:556; `TopSit.RealD`, JS:62-68)

For every residue field k of O, all of the following exist:
- An étale ring (R, ι) with `IsCyclotomic` (OPA:28-35):
  - ι identifies k((X)) with k((π))^Δ, where Δ = μ_{l−1} ⊂ Z_l^×;
  - ι(X) = unit·π^{l−1};
  - φ(π) = π^l;
  - γ acts by π ↦ (1+π)^{1+l} − 1.
  - Hence γ(X) = X(1 − κX) with κ(0) = 1 (`RingPG`, PG:9-27).
- A functor F (`DFun`, TMA:46-91). It sends finite k[G_K]-modules A to étale (φ_i : D_{i−1} → D_i, γ_i)-modules over k((X)), indexed by i ∈ Z/n (`ModPG`, PG:54-72). It is exact and faithful on the admitted class, and has the Herr fixed-point property `fix`.
- An index map τ, and γ with χ(γ) = 1 + l.
- A `Pres` (JS:28-57): for every O-lattice T and every G-surjection q : T → A, a surjection j from the Δ-invariants of the integral étale module DD(T) onto F(A). It is compatible with φ, γ and scalars; its kernel is the image of the sublattice ker q (`j_ker`); and it is functorial and unital.

*(Inferred)* This is "the Δ-descended mod-λ reduction of the integral (φ,Γ)-module of a lattice is the mod-l (φ,Γ)-module of its reduction". The proof (EPT:556-569, read) assembles `exists_cyclotomic`, `gamma_action_reduction`, `exists_letter_bijection'`, `fixed_of_fixed_by_delta_gamma_lifts` and `exists_pres_tensor`. I read these at statement level only.

### 1c. `card_cocycles_independent_mod_coboundaries_le` (statement at `IE/CardCocyclesIndependentModCoboundariesLeStatement.lean:8`; proof CC:117-194)

**Inputs.**
- `LemmaPsi` (OPA:62-76): existence of the left inverse ψ of φ with the shift properties. Proved in-tree as `PsiShiftProof.lemmaPsi`; I did not open it.
- k of characteristic l.
- D ∈ ModPG R n (k((X))^m).
- Lattices N_i ⊂ D_i.
- Weight data `TopData` Dt with T1, T2, T3.
- **ABC** (TMA:104-105):
  - each N_i is a k[[X]]-lattice;
  - ⟨φ(N_{i−1})⟩ ⊆ X^{−w_i}N_i and X^{wst_i}N_i ⊆ ⟨φ(N_{i−1})⟩, with wst = h − w;
  - (γ−1)N_i ⊆ XN_i.
- **Sen conditions.** sen(N_i, x) is the multiplicity of the generalised eigenvalue x ∈ k of ∇ = X^{−1}(γ − 1) on N_i/XN_i (PG:37, 45-52). The conditions are:
  - sen(N_i, a) = 0 for a = 0, …, σ_i + 1;
  - typ G: Σ_{j<w_i} sen(N_i, −w_i + j) = d_i;
  - typ Bd: d_i + Σ_{a ≤ wst_i} sen(N_i, a) = m, together with EPoly.

**Conclusion.** If s Herr 1-cocycles (b, g) ∈ D^n × D^n satisfy `InZZ` (TMA:173-177) and are linearly independent modulo Herr coboundaries ((φ−1)y, (γ−1)y) (`herrB`, TMA:179-184), then **s ≤ dsum = Σ_i d_i**. `InZZ` means:
- (γ−1)b_i = φ(g_{i−1}) − g_i;
- g_i ∈ XN_i;
- b_i ∈ X^{−w_i}N_i for typ G (the Bd variant is analogous).

Here d_i = #{u ∈ U_i : u < w_i}. The Lean says `Dt.d i = card (U i).filter (· < w i)` (MC:205, `rfl`).

**Its rank-level meaning** (`AdmBound.main`, ADM:73-81, read). Let T̄ = ρ̄χ̄₁^{−1}. Residual classes z ∈ H¹(G_K, T̄) whose extension 0 → T̄ → E → 1 → 0 has a "model" span a space of dimension ≤ dsum. A model is a lattice in F(E) obtained by push/pull from a base lattice (`IsModel`, TMA:99-102); base lattices are reductions of Wach lattices (`ModTh`, TMA:117-158).

## 2. The argument, as mathematics

### 2a. Module category and the residual constraint

Let L be a crystalline O-lattice with labelled HT weights in [0, h_i] (after the twist, [−w_i, h_i − w_i]). Let 𝔑 be its Wach module over O_K⊗O[[π]] (Bhatt–Scholze input, BEYONDFL child 8). Put N = (𝔑/λ)^Δ, a lattice over k[[X]] with X = π^{l−1}·unit. The `ModTh` clauses (TMA:117-158), proved in MTP:28-70 from Wach facts, say three things about N.

**(i) Height.** ⟨φ N_{i−1}⟩ ⊆ X^{−w_i} N_i and X^{h_i−w_i} N_i ⊆ ⟨φ N_{i−1}⟩.
- *(inferred)* This holds because q = φ(π)/π ≡ π^{l−1} ≡ X mod l. A Wach module of height h therefore reduces to a φ-lattice whose φ-cokernel is killed by X^{h}, for any h. **No bound h < l is needed here.** (`phiGamma_reduction_base_lattice_bounds`, statement only.)

**(ii) Wach condition.** (γ−1)N ⊆ XN.
- *(inferred)* Γ acts trivially on 𝔑/π𝔑. Δ-invariants of π𝔑/π^{l−1}𝔑 vanish, so on Δ-invariants (γ−1) lands in π^{l−1} = X.

**(iii) Residual Sen weights.** sen(N_i, x) = #{u ∈ U_i ∪ block : u − w_i ≡ x mod l} (`base_sen`, `std_sen`; `senMultiset_base_lattice_eq_jumps_mod`, statement only). This is the **only** residual trace of the Hodge–Tate weights, and it is mod l.
- It comes from the admitted `SenLat` (TL2:385-396, read). On (E^{−y}𝔑/E^{k}𝔑)^Δ, with E = π₀ + p, the generalised u^{−x}-eigenspaces of γ are free of rank Σ_{j∈[1−k,y]} mult_τ(x − j), where u = χ(γ) = 1 + l.
- *(inferred)* Take y = 0, k = 1. In 𝔑/E𝔑 one has π₀ = −p, so ∇ = (γ−1)/X acts as −(γ−1)/p. Its eigenvalues are −((1+l)^{−x} − 1)/l ≡ x mod l. Reducing mod λ gives N/XN, which gives (iii).
- This is sound for any weights. What is lost for h ≥ l is that N is **not unique**: two lattices with the bounds (i) differ by up to X^{σ}.

### 2b. Closeness of lattices: where σ ≈ h/(l−1) enters

Let N, N′ be two families satisfying (i) with the same (w, h). Then X^{σ_i}N_i ⊆ N′_i (`phiGamma_lattice_families_shift_inclusion`, statement read at `IE/PhiGammaLatticeFamiliesShiftInclusionStatement.lean:8`).

*(inferred proof)* Suppose N_i ⊆ X^{−s_i}N′_i. Then

φ*N_{i−1} ⊆ N_i ⊆ X^{−s_i−h_i} φ*N′_{i−1},

and φ multiplies X-adic valuation by l, so s_{i−1} ≤ (s_i + h_i)/l. Iterating gives s_i ≤ Σ_j h_{i+j+1}/l^{j+1} = σ_i. This is the recursion `hI` used in CC:41: σ_i + 1 ≤ l(σ_{i−1} + 1) − h_i.

### 2c. The largest model and its Sen weights (MC:85-209, read)

Fix A = T̄. Its models form a lattice-ordered family (base sums, `base_sum`). Let N^max be the largest model (`exists_largest_model'`, statement only). It contains N^std, the reduction of the Wach module of T₀ ⊗ χ₁^{−1}, and N^max ⊆ X^{−σ}N^std by §2b (MC:91-94).

**Telescoping.** The Lean uses (`senMultiplicity_lattice_count_relation`, statement only)

sen(N^max, y) + q(y+1) = sen(N^std, y) + q(y),

where q(y) is the multiplicity of the eigenvalue y on N^max/N^std. That module lies in X^{−σ}N^std/N^std. Its graded pieces have eigenvalues (Sen weights of N^std) + j, for j ∈ [1, σ]. So q(y) ≠ 0 forces y − j ≡ u − w for some u ∈ U and some j ∈ [1, σ] (MC:110-118).

**No block weights in any model of A** (SR:25-47, read):
- Every Sen weight x of any model is within ±σ of a Sen weight of N^std (`senWeights_close_of_height_gamma_conditions`), so x ≡ u − w + c with |c| ≤ σ.
- It is also ≡ (some element of U ∪ block) − w (`model_senWeight_mem_weight_residues`).
- If it were a block weight, some u ∈ U would be within σ of the block mod l. T2 (lows) and T3 (cloud) forbid this (`admissibleLetterData_window_arithmetic`).

**Conclusions for N^max** (MC:140-208):
- (α) sen(N^max, a) = 0 for a ∈ [0, σ+1]: no u ≡ w + a. Lows are excluded by T2, cloud weights by T3.
- (β) For typ G, Σ_{j<w} sen(N^max, −w + j) = #{u ∈ U : u mod l ∈ [0, w−1]} = #{u ∈ U : u < w} = d_i.
  - Lows lie in [1, η] with η < l, so their residues are the integers themselves.
  - Cloud residues avoid [0, w−1] ⊂ [−2σ−2, η+2σ+3] by T3.
  - The boundary terms q(0) and q(−w) vanish by the same windows (MC:136-139, 157-161).
  - **This is why the bound equals dsum = rank H¹_f.** The Sen weights in the polar window [−w, −1] mod l are exactly the u < w, which are the negative weights of ρχ₁^{−1} that compute dim H¹_f (`BlochKatoJumpDimension`, TL2:233-246: dim H¹_f = dim H⁰ + #{weights < 0}).

The quotient side behaves the same way. If the quotient lattice of the trivial character inside a model of E were X^a·unit with a ∈ [1, σ], its Sen weight would be ≡ −a, so some u ≡ w − a. That is again excluded by T2/T3 *(inferred; this is inside `exists_phiGammaModel_extension_cocycle_pair`, statement only)*.

### 2d. From a residual extension to a Herr cocycle (ADM:73-81)

Suppose z is model-admissible, with E and N_E. Lift the unit to ε ∈ N_E. Then

(b, g) = ((φ−1)ε, (γ−1)ε) ∈ A,

and b ∈ X^{−w}N_A, g ∈ XN_A by ABC for N_E. So (b, g) satisfies InZZ for N_A ⊆ N^max, and InZZ is monotone in N (`inZZ_mono`, ADM:17-24).
- Galois-independent classes give Herr-independent pairs: a Herr coboundary implies a Galois coboundary (`indep_pairs`, ADM:39-58; `mem_coboundaries_of_herrPair_coboundary`, statement only; Herr's theorem).

### 2e. The count (CC:117-194, read)

1. **Gauge** (`gauge_one`, CC:40-105; `Gauge.main`, statement only). Modify (b, g) by a Herr coboundary so that g ∈ X^{σ+3}N and b is congruent mod N to c ∈ X^{−w}N with ∇c ∈ N.
   - *(inferred)* To solve (γ−1)y ≡ g one needs γ − 1 = X∇ to be invertible on the graded pieces X^{a}N/X^{a+1}N for a ∈ [1, σ+2]. There ∇ has eigenvalues (Sen weight) + a, and (α) makes them nonzero. Pushing the error through φ uses the recursion for σ.
2. **Polar part.** The classes define vectors c^{(a)} = (c_i^{(a)})_i. The span of the c_i in X^{−w}N_i/N_i is killed by ∇. Its dimension is at most the multiplicity of the eigenvalue 0 of ∇ on X^{−w}N/N, namely Σ_{j<w} sen(N, −w + j) = d_i (`gammaMinusOneDivVariable_polar_kernel_le_senWeights`, statement read). For typ Bd the dual count uses ψ/`LemmaPsi` (`polarPart_finrank_add_senWeights_le_rank`, statement only).
3. **Injectivity** (CC:168-194). If Σ t_a c^{(a)}_i ∈ N_i for every i, the second half of `Gauge.main` makes Σ t_a z′_a a Herr coboundary. So the linear map t ↦ (polar parts) is injective, and s ≤ Σ d_i (`card_le_sum`, CC:14-34).

**Shape.** This is the mod-l Wach-module proof of "torsion-crystalline classes = H¹_f", with the FL hypothesis h < l − 1 replaced by:
- residues mod l (T3) and separation (T2) of the weights, at margin σ ≈ h/(l−1);
- an FL-sized low window (T1).

The "extra" classes that exist for large weights all live in polar parts at Sen weights ≡ 0. T2/T3 empty that eigenspace.

### 2f. From the residual count to the integral statement (Q4)

`stmtAt_of_real` (TOP:44-65, read) assembles:
- **Vanish**: residual H⁰(T̄) = H²(T̄) = 0, from Real via `vanish_of_real` (statement only).
- **FreeH**: H¹(T₀′) is free of rank rn, and H¹(T₀′ ⊗ X) = H¹(T₀′) ⊗ X (`TensIso`), via Euler characteristic.
- **FSummand** (RB:109-111): H¹_f is a direct summand of rank dsum. Saturation is part of adm19, `BlochKatoJumpDimension`, clause 2 (TL2:241-246): λκ ∈ H¹_f ⇒ κ ∈ H¹_f.
- **FinAdm**: H¹_f ⊗ X ⊆ admissible.
- **Lem0** (RB:87-94): the admissible classes form a submodule; they are stable under pushforward X → X′; and they are detected after an injective X → X′.
- **ResBound** = §2e.

`cls_eq_H1fX` → `adm_eq_H1fX` (`IE/ToAmbCoefH1EqCoefAmbToAmb.lean:234-266`, read; core `subset_of_bound`, statement only).

*(Inferred proof)*
- **For X = k:** H¹_f ⊗ k ↪ H¹(T̄) has dimension dsum, because H¹_f is a saturated summand. The admissible classes contain it and have dimension ≤ dsum, so they are equal.
- **For X = O/λ^a:** let c be admissible. Its image in H¹(T̄) is admissible (pushforward), so it equals h̄ with h ∈ H¹_f. Then c − h is admissible and maps to 0. By TensIso, c − h = ι(c′) for ι : O/λ^{a−1} ↪ O/λ^a. By injective detection, c′ is admissible. Induct on a.
- General finite X go through TensIso.

**The trap is avoided.** "Admissible" is a condition at every level a: the extension must be a subquotient of crystalline lattices of the prescribed weights for O/λ^a, not just mod λ. An integral non-crystalline class whose reduction is admissible is therefore not called admissible. Saturation is an explicit clause. The logic is sound.

## 3. Tests against known answers (Q3), all **(mine)**

Convention: a crystalline character of K = Q_{l²} with standard labelled weights (k₀, k₁) reduces on inertia to ω_{τ₀}^{k₀} ω_{τ₁}^{k₁}, with ω_{τ₁} = ω_{τ₀}^{l}. The Lean weight u corresponds to standard weight −u. Write d_i = u_i − w_i.

Residual ρ̄ = (χ̄ *; 0 1), with χ̄ = ω₂^{N} and N ≡ −Σ d_i l^i mod l² − 1. The Breuil–Mézard type of labelled HT {−d_i, 0} is W = ⊗_i (Sym^{d_i−1} ⊗ det^{−d_i})^{(τ_i)}.

The Gee–Liu–Savitt weights of ρ̄ are σ_J = ⊗ Sym^{r_i} ⊗ det^{s}, for J ⊆ {0, 1}, defined by Σ_{i∈J}(r_i+1)l^i − Σ_{i∉J}(r_i+1)l^i ≡ N and s ≡ −Σ_{i∉J}(r_i+1)l^i. The weight σ_J occurs iff the class lies in L_J. Generically dim L_J = |J|, L_{{0,1}} is all of H¹, and L_{0} ≠ L_{1}.

Admissible classes = ∪{L_J : σ_J ∈ JH(W)}, assuming "Serre weight in JH(W) ⇒ crystalline lift of that weight". JH(W) is computed with Steinberg/Glover: Sym^{a+lb} has the factors L(a)⊗L(b)^{(1)} and L(l−2−a)⊗det^{a+1}⊗L(b−1)^{(1)}, followed by Clebsch–Gordan.

**(a) Both labels cloud.** l = 101, w_i = η_i = t = 1, u_i = 960 (h = 961, σ = 9; 960 ≡ 51 lies outside [−20, 22]). Then dsum = 0. I get N = 4182, σ_{0,1} = Sym⁴⁰⊗Sym⁴⁰⁽¹⁾, σ_{0} = Sym⁴¹⊗Sym⁵⁹⁽¹⁾⊗det^{4140}, σ_{1} = Sym⁵⁹⊗Sym⁴¹⁽¹⁾⊗det^{10140}. Each occurs in JH(W) only twisted by det^{(l²−1)/2}, never itself. So **no crystalline lift exists; this matches dsum = 0.**
- In general, the collision for σ_{0,1} from the L(a)⊗L(b) pieces needs a₀ + b₁ ≥ l − 2 (a carry), i.e. u₀ mod l ∈ [w₀ − 1 − b₁, w₀ − 1].
- Since σ₀ ≥ h₁/l ≥ b₁, T3 excludes this. The relevant digit belongs to the **other** label, and that is exactly why σ_i is built from h_{i+1}.

**(b) Mixed case: label 0 low below the block, label 1 cloud.** Write e₀ = w₀ − u₀ > 0, d₁ − 1 = a + lb. Then dsum = 1 and the H¹_f line is L_{0}.
- I find σ_{1} ∈ JH(W) **iff b ≥ e₀**. The source is the factor L(l−2−a)⊗det^{a+1}⊗L(b−1), with Clebsch–Gordan index j = e₀ − 1. The determinant and the character both check, the difference being l² − 1 ≡ 0.
- If b ≥ e₀, the line L_{1} ≠ L_{0} would be admissible, and the admissible span would be 2 > dsum.
- The Lean excludes this through **T2**: e₀ > σ₀ + 2 ≥ ⌊h₁/l⌋ + 2 > b.
- Note also that T1 + T2 force σ₀ < (l − 10)/5 whenever a low exists.
- **Consistent, and T2 is sharp.** Without T2, Lean's claim would fail here, with l = 101, e₀ = 20, d₁ ≳ 20·101.

**(c) The characters χ_c for c ≥ 2** (gap c − 1 < l, ambient cloud generic). These are FL-like and consistent.

**(d) Dimension 3** (sub of dim 1, quotient irreducible of dim 2). By Tate duality this is the Lean's orientation for r = 2 with negated weights. I did not finish it: no Breuil–Mézard result for GL₃ in this weight range is available to compare against. The Lean's proof is uniform in r, so it stands or falls with §2a(iii) and §2b, which do not depend on r.

**Caveats.**
- "Serre weight in JH(W) ⇒ lift" for K = Q_{l²} with weights ≫ l is the BM-type direction. I used it as known/expected and did not verify a reference.
- For n ≥ 3 I did not independently test the orientation of the label shift in sg (h_{i+1} rather than h_{i−1}). The in-tree recursion is internally consistent with "φ_i : D_{i−1} → D_i has the height of label i" (§2b). It would be wrong only if the Wach/Pres dictionary attached labels the other way round, and that would make `phiGamma_reduction_base_lattice_bounds` false.

## 4. Children

| # | Name | file:line | Statement | Role | Weight / status |
|---|---|---|---|---|---|
| 1 | `twistedLatticeCohomology_theoremTOP`, `stmtAt_of_real` | TOP:67, 44 | Stmt := admitted ⇒ TopCore for all l | skeleton | glue; read |
| 2 | `card_cocycles_…_le` = `PolarBound.main` | CC:117 | §1c | the count | **core; proved, read** |
| 3 | `Gauge.main` | (via CC:52) | gauge g into X^{σ+3}N; injectivity | contraction | core; statement only |
| 4 | `gammaMinusOneDivVariable_polar_kernel_le_senWeights`, `polarPart_finrank_add_senWeights_le_rank` | `IE/GammaMinusOneDivVariablePolarKernelLeSenWeightsStatement.lean:7` | dim(∇-kernel in X^{−w}N/N) ≤ #Sen weights in window | polar count | standard linear algebra; statement only |
| 5 | `ModelCount.count` | MC:85 | Sen weights of the largest model | §2c | core; proved, read |
| 6 | `sen_model_subquot_mem_U` | SR:25 | model Sen weights ⊂ U − w residues | excludes block | core; proved, read |
| 7 | `phiGamma_lattice_families_shift_inclusion` | `IE/PhiGammaLatticeFamiliesShiftInclusionStatement.lean:8` | X^σ N₁ ⊆ N₂ | §2b | core; statement only (standard) |
| 8 | `AdmBound.main` | ADM:73 | model-admissible classes ≤ dsum | residual bound | core; read |
| 9 | `realD`, `real_of_presented`, `exists_modTh_of_pres` | EPT:556; MTP:72, 28 | Δ-descended mod-λ reduction functor; ModTh from Wach data | Real | core; assembly read, inputs statement only |
| 10 | `senMultiset_base_lattice_eq_jumps_mod`, `phiGamma_reduction_base_lattice_bounds`, `wachDeltaInvariants_reduction_isLattice`, `reduction_sum` | MTP:56-66 | §2a (i)–(iii) | the bridge from HT weights to residual data | **core; statement only** |
| 11 | admitted Wach facts: `SenLat` (adm21), `HerrLat` (adm16), `HerrSub`/`HerrExt` (adm17), `BlochKatoJumpDimension` (adm19), Tate duality / Euler characteristic (adm18), adm1–15 | TL2:316-396, 434-478 | integral Sen eigenspace ranks on E^{−y}𝔑/E^{k}𝔑; Herr complex computes integral cohomology; BK dimension + saturation | inputs | standard-type / new (`SenLat` integral form); discharged by `blochKatoTop_of_localTateDuality_eulerChar` per BEYONDFL, not reopened |
| 12 | `adm_eq_H1fX` → `subset_of_bound` | `IE/ToAmbCoefH1EqCoefAmbToAmb.lean:234` | dévissage, §2f | integral step | core; read; inner lemma statement only |

## 5. Hypotheses at l in the live application (Q5)

- **Which l.** The live caller is `NLinkE.main_alt_alt` (APE:30-57, read). It applies for l > lStar, l ≠ g_k, l ∉ Exc.
  - `position_data_exist` gives 5 ≤ l, t + 1 < l, l ∉ {q, d, small}.
  - From that, the host is unramified at l (`host_ramificationIdx_eq_one`, APE:42).
  - CaseA (K_w unramified) is therefore met.
  - The clauses for l ∣ d, l = q and l = g_k are not in this branch (midG, StarH; NODE-LARGETW).
- **Crystallinity.** It enters as `admG2` (`Formalism/SharpRestriction/LevelLetterCocycles/DecompositionData.lean:184-189`, read): at every w ∣ l and every family member x, r(x) ⊗ χ₁^{−1} is crystalline, plus `GainBoundAt`.
  - It is supplied by `admG2_of_isRankR_of_lStar_lt` (`…/ThirdPlaceSeries/ImportsExtraMoreStatement.lean:11`, statement) from `FontaineBcris`, which concerns only the period ring (`…/GaloisCohomology₂/OneSubPhiOntoOfFilZero.lean:18-20`, read), and from `NormChoiceFacts`.
  - Through `GTwoTheta.main_alt_alt` (statement read) it rests on `DeRhamFamilyAwayAlt D` (`…/ThirdPlaceSeries/DeRhamFamilyAway.lean`, read): ∀ i, r, GoodR(r) ⇒ `G2a` (`Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/TrivialLocalCondition.lean:81-84`, read).
  - **G2a** says: for every w ∣ l with l ≠ g₀, g₁ and every x, r(x) is crystalline at w, and its HT jumps at each τ equal `locAutHodgeTateWeightsLevelZero`. **So crystallinity at l with the right HT weights is a clause.**
  - It is a field `g2` of `CoreNormFacts` (`…/ThirdPlaceSeries/NormChoiceFacts.lean`, read), which is a hypothesis of `NLinkE.main_alt_alt`: **a hypothesis passed down**. I did not locate its discharge.
  - `GoodR` (`Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:1224-1233`, read) is only continuity, semisimplicity and Frobenius charpolys at `SplitOut` places. It contains **no condition at l**. So G2a is a separate local–global compatibility at l for every family member, for every l ≠ g₀, g₁. G2a itself carries no l ∤ level or "π_x unramified at w" guard; see oddity 2.
- The weight shape (the position data) comes from `position_data_exist` (BEYONDFL row 6).

## 6. Oddities

1. **New theorem.** The integral `SenLat` (adm21) is an admitted input of real strength: freeness, plus ranks of u^{−x}-eigenspaces of γ on (E^{−y}𝔑/E^{k}𝔑)^Δ for every y, k. Rationally it is the B_dR⁺-lattice / Sen comparison. The count uses only the reduction mod λ of the case y = 0, k = 1, which I find sound (§2a(iii)). The discharge was not reopened.
2. **G2a's crystallinity clause is quantified over all l ≠ g₀, g₁ and all GoodR families**, with no unramified-at-l guard visible in its definition. If some family member is ramified above some l (for instance l = q or d), G2a is false there, and the hypothesis bundle `CoreNormFacts` would be unsatisfiable. Whether `D.nd` structurally rules this out was not checked. NODE-GALREP should confirm.
3. **The genericity is about the other label's digits** (σ_i from h_{i+1}), and this is right for n = 2 (§3a). For n ≥ 3 the orientation was not tested.
4. **T2 is essential, not cosmetic** (§3b). T1 + T2 also mean a low weight below the block can exist only if σ_i < (l − 10)/5.
5. `ModelCount.count` needs N ⊇ N^std. This is supplied by `exists_largest_model'` (statement only).

## 7. Coverage

Read:
- PROTOCOL; NODE-BEYONDFL, NODE-LARGETW, NODE-KILLAT (all).
- TL2:1-215, 300-505; PG:1-90; TMA:1-200; OPA:1-94; RB:1-134; JS:1-69.
- CC:1-196 (all); its Statement file; ADM (all); MC (all); `TwistedPhiGammaModelSenWeightCountStatement.lean`; SR (all) and its Statement.
- The statement lines of `GammaMinusOneDivVariablePolarKernelLeSenWeightsStatement.lean` and `PhiGammaLatticeFamiliesShiftInclusionStatement.lean`.
- TOP (all); MTP (all); EPT:540-572; `ToAmbCoefH1EqCoefAmbToAmb.lean:234-266`.
- `AdmissibleOfLargeResidueChar.lean:1-54`; APE:28-58; `DecompositionData.lean:150-200`; `EmbeddingTypeJumps.lean:80-100`; `LargeLevelLemmas.lean:88-100`.
- `ImportsExtraMoreStatement.lean` (all); `BigImageSecondCondition.lean:14-22`; `AdmG2OfDecomposition.lean:26` (statement); `DeRhamFamilyAway.lean`; `TrivialLocalCondition.lean:81-90`; `DataN.lean:1224-1234`.
- `NormChoiceFacts.lean` (structures); `OneSubPhiOntoOfFilZero.lean:18-30`; the DeRhamFamilyAwayAlt statement lines in `PointInputAwayFromTypePrimesStatement.lean`, `MainAltAltTerStatement.lean`, `UnrCrysAtRangePrime.lean`.

Greps run:
- `card_cocycles_independent_mod_coboundaries_le`; `theorem realD|real_of_presented|wachLattice_usedProperties_of_admitted`;
- `def (ModPG|RingPG|Vc|Lats|ABC|InZZ|herrB|sen|sh|pull|EPoly|TopData|LType)`; `def (LemmaPsi|IsCyclotomic|kerPsi)`;
- `PolarBound`; `def RealD|structure TopSit|def Real`;
- `cls_eq_H1fX|resBound_dsum|fSummand|BlochKatoJumpDimension|admissibleLocalSituation_admissible_classes`; `adm_eq_H1fX`;
- `def (admG2|admG3|SemisimpleDecomposition)`; `TruncatedSeriesCountingIdentities.admG2`; `admG2_of_isRankR_of_lStar_lt`; `AdmGTwoLarge`; `GTwoTheta`;
- `def DeRhamFamilyAwayAlt`; `def (UpperTheory.GalS.)?G2a`; `CrysIffWD`; `def GoodR|def FontaineBcris`; `def IsHeckeGalois`; `structure CoreNormFacts|NormChoiceFacts`; `DeRhamFamilyAwayAlt` (file list).

Not opened:
- the bodies of `Gauge.main`, `exists_largest_model'`, `exists_phiGammaModel_extension_cocycle_pair`, `senMultiplicity_lattice_count_relation`, `senWeights_close_of_height_gamma_conditions`, `model_senWeight_mem_weight_residues`, `polarPart_finrank_add_senWeights_le_rank`, `lemmaPsi`;
- the MTP inputs (`senMultiset_base_lattice_eq_jumps_mod` and the rest), `exists_pres_tensor`, `vanish_of_real`, `subset_of_bound`, `exactLocalConditions_topCore`, `CharVanish.stmt_of_real`;
- the discharge of `admitted` and of `CoreNormFacts.g2`; HWR (`ResidueAvoidance`).
