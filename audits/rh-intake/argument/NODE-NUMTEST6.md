# NODE-NUMTEST6: does composing the m jet steps lose anything? (the Hadamard prediction of CARRIER §5)

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own algebra or inference. [NODE] means taken from that node and not re-read. Nothing from the tree was compiled or executed.

Scripts (numpy + standard library, `python3 -I`, auditors' own code) are in `numtest/`:

| script | output | wall time (4 cores) |
|---|---|---|
| `composite6_lib.py` | engine: theta moments, Lean step bound, exact step operators | — |
| `composite6_validate.py` | `out_composite6_validate.txt` (brute-force checks V1–V5) | 1 s |
| `composite6_square.py 1536` | `out_composite6_square.txt` (E1, E1b, controls a, a′, b) | 1258 s at Amax = 1536 (run concurrently with the next two) |
| `composite6_growing.py` | `out_composite6_growing.txt` (E2, rank-growing tower) | 482 s |
| `composite6_wrows.py 768` | `out_composite6_wrows.txt` (E3, a persistent w-row) | 958 s |
| `composite6_young.py` | `out_composite6_young.txt` (E5, eE over m lifts; control c) | 1 s |
| `composite6_controls.py` | `out_composite6_controls.txt` (singular-value cluster; rank-one control; extremal-coefficient functional) | 2 s |

## 0. Verdict

**The multi-step defect is within the proof's per-lift allowance in the model.** No ESCALATE.

1. **Structure (read).** The m lifts never reuse a variable, and the top degree is not accumulated. Each step K_j has its own matrix variable Z_j ∈ M_{N_j×N_{j−1}} (`DVar ι a b`, ThDistC:18) and its own theta kernel. It multiplies by det(X)^{n_j}, substitutes X = Z_jᵀY and pairs the Z_j-monomials with the jet of θ_j (`jetMap`, ThDistC:20-32). The top-column degree is the same a_t + w′ at every level, because ν^{(j+1)} = pad ν^{(j)} + n_{j+1} (`IsStepWeight`, PWN:15-17, with NUM:224-225). So the composite is E[(P·dets)(ξ₁ᵀ⋯ξ_mᵀW)] over *independent* jets. A product z^a·z^{a′} in one variable, whose (a+a′)!/(a!a′!) the brief feared, does not occur. *(mine, from the definitions)*
2. **Measured Hadamard defect (true, model).** H_m = Σ_j log‖K_j‖²_op − log‖K_m⋯K_1·1‖² stays small:
   - **Same kernel at every step:** H₈ ≤ 7 for every kernel and every top weight A from 48 to 1536. It does not grow with A.
   - **Different kernels at successive steps:** H₈ ≤ 11, growing like ≈ log A.
   - **Rank-growing tower 1→2→3→4:** H ≤ 3.1.
   - **One persistent cap row, w ≤ 32:** H₆ ≤ 18.
   - **Per step:** at most ≈ 1.4 in the square cases and ≈ 3 with w = 32.

   For comparison, A·log 2 = 33 to 1065. An engine control with a rank-one kernel and a misaligned frame recovers the predicted loss A·log(1/|u₀₀|²) per step to 4 digits, so the engine does detect a-proportional composition losses.
3. **The total defect is BlockBound's polynomial slack, not composition.** D_m = Σ_j log tmax_j − log‖composite‖² grows linearly in m, with a per-step increment equal to the one-step slack log tmax − log‖K‖²_op to within 1. That slack is 29 → 49 for A = 48 → 1536 on 2×2 steps (≈ 6 log A + const) 33 → 61 on 2→3 steps and 70 → 92 on 3→4 steps. Its source is the factor e·S²·(2|ν|+2)^{2ab} of tmax (PWN:32-34), i.e. O(rank²·log a) per step per τ. It **does not depend on w**: at fixed A it moves by at most 5 between w = 0 and w = 32. It is not proportional to a.
4. **The one-step calibration reproduces NODE-STEPE.** The true one-step log-norm minus [logHook(w) + ph(A)] is w·log A + (11 to 22), against STEPE's Stirling model w·log a.
5. **The Young-diagram remainder does not accumulate.** With the Lean's weight formulas, eE_j at a top is constant in j for t = 0 and no block rows, and decreases with j for t = 1. It grows with j only through the block rows, which the hypothesis `blk` caps at m(t+1)η per lift. Σ_j eE_j ≤ 0.96·m·w·La in every case.
6. **Controls (§4).**
   - **These show power:**
     - a rank-one (anisotropic) kernel with a rotated frame loses exactly A·0.576 per step;
     - a wrong coordinate constant cD = √2 shifts D by exactly A·log 2 per step, making the "bound" false;
     - a reused top variable would cost log((ma)!) − m·ph(a) ≈ m·a·log m.
   - **This one has little power:** a non-extremal start vector, and the true kernel with a rotated frame, cost only 0.1–3 per step. The true step operator has a top singular cluster of 7–118 nearly equal values, roughly one per lattice direction. It absorbs any direction of the heavy line. This is the mechanism behind item 2.

What this does **not** settle: the model has one CM embedding, no Heisenberg/character sums θ_{c,c′}, no class sums, rank ≤ 4 and k ≤ 2. See §5.

## 1. Statement tested

CARRIER §5 / MAIN §9.8 predict the following from near-sharpness of the final inequality: log‖PtL∘K_m∘⋯∘K_1‖² on the proof's vectors must equal Σ_j(step bound_j) + log‖PtL‖² up to the allowed slack. That slack is ≤ U·x^{1/2+O(ε)} in total, i.e. per lift and per top ≲ b·√x = a/√x. In particular there may be **no loss of size ≈ a per lift** (for example a·log 2 from binomials). A loss of size poly(x)·log a, or w·La per lift, is allowed: the ledger books f·Nn²·La and C₀·w·La per lift and place (`hB`, NUM:261-263; `stepE_num` [STEPE]), and Nn², poly(x) ≪ b by `n2`, `n3` (NL:51-52).

Tested: D_m and its parts as functions of A (top weight), w (cap rows), m (number of steps), rank, and kernel.

## 2. Model and identifications

| model object | Lean object | file:line | status |
|---|---|---|---|
| polynomials on N×N matrices of column weight natW λ, invariant under column unipotents | `VV` = `dualWeyl` of natW | CM:67-68; DataCoeff:49-50; StatementA:24-29 | read |
| extremal vector ∏_s Δ_s^{ν_s−ν_{s+1}} (leading minors) | `extremal` = `hw` | DataCoeff:55-56; StatementA:55-65 | read |
| norm = Fischer form ⟨z^m, z^m⟩ = m!, divided by the Fischer norm of the extremal vector | `normSq` = pairK with G = 1; `fockS`; `extNorm` | PWN:22-23; CM:19-22, 160-176; NFL:71-77 (`normSq_eq`) | read |
| ‖ext_ν‖²_Fischer = hook product H(ν) | used to read logHook (NUM:245) as log‖ext_{a⁺}‖² | V1 (brute force, 44 shapes) | *(mine)*, checked |
| step: P ↦ (P·det^n)(ZᵀY) paired with the jet J(m) = cD^{\|m\|}∂^mG(0) | `jetMap` = jetLin ∘ subD ∘ (· × ∏frDet^n); `jetC`; `jetOp` | ThDistC:20-40, 56-61 | read |
| fresh variable per step, weight bookkeeping ν^{(j+1)} = pad ν^{(j)} + n_{j+1} | `DVar ι a b`; `IsStepWeight`; `nu` | ThDistC:18; PWN:15-17; NUM:216-225 | read; the "+n" form is *(mine)* |
| step bound tmax = S²·∏Ω^{−\|ν\|}·e·(2\|ν\|+2)^{2ab}·exp Σph(ν_i), hypotheses a ≤ b, (a < b or lastEntry ν = 0), \|G\| ≤ S·e^{r²\|z\|²/2}, \|cD·r\|² = 1/Ω | `tmax`, `BlockBound` | PWN:32-47 | read |
| G_j(Z) = ∏_{entries} θ(Z_{βα}), θ(z) = Σ_{ℓ∈L} α(ℓ)e^{zℓ̄−\|ℓ\|²/2}, L a CM lattice of area π (principal for H = zw̄/π), α a semi-character; optionally the Heisenberg translate by a half period | the kernel θ_{c,c′} on VV = ℂ^{Tau×N′×N}, Λ = δ·Φ(AA0·Hom(N, N′)), H = area⁻¹Σzw̄, vacuum th0 = U_t(σ*)/… [ENGINE §1.1; MAIN §4.1] | — | **inference**: the vacuum of a product lattice with the product form factorises over matrix entries; the finite Heisenberg sum of torsion translates is **not** modelled |
| r = 1, cD = 1, area π ⇒ Ω = 1 = area/π | logΩ = mean log(area/π) [STEPE §4] | PWN:46 | *(mine)*; Ω is additive and dropped, as instructed |
| one τ, one class, no ρρ′ factors | product over τ in tmax; class sums `cbSq` = n·n′·h·h′·t [HEIGHT] | — | not modelled (poly factors) |
| the source of the chain at level 0 is VV_{λ₀}. For k = 1 it is one-dimensional (the constant 1), so the composite applied to 1 *is* its operator norm; for the square chains the start vector is the extremal | N_u ⊂ VV_{λ₀} [NORMS table] | — | *(mine)* |
| PtL = a functional on the last level. Reported: the best functional (‖·‖) and the one reading only the extremal coefficient | `PtL`, `period_le` [HEIGHT] | — | not modelled beyond these two choices |

**Reduction to a moment functional** *(mine; V2, V3 check it against brute-force expansion)*. With the product kernel, J(m) = ∏_{entries} d_{m_{βα}} with d_p = θ^{(p)}(0). Hence K_j P(Y) = E[(P·det^n)(ξ_jᵀY)], where E is the linear functional E[ξ^p] = d_p, independent across entries. The composite is a product of independent E's.

**Exact coordinates.** For weight (A, 0, …) the space is Sym^A(ℂ^N) in the first column. In the orthonormal basis y^s/√(s!), rescaled by √(A!), the step has entries Σ ∏_α √multinom(r_α; s_α) ∏ d̃_{s_{αβ}} / √multinom(A; S), with d̃_p = d_p/√(p!) of size O(1) and each term ≤ |∏d̃|. Products of these are evaluated exactly in floating point, with no cancellation of large terms. log‖K‖² = log A! + log‖K̃‖².

**The w-row.** On 2×2 the weight (A+w, w) is det^w ⊗ Sym^A. Under X = ξᵀY, det(X)^w Q(X) ↦ det(ξ)^w·det(Y)^w·Q(ξᵀy₀), so the w-row persists through the substitution exactly as the top row does. The model step is P ↦ E[det(ξ)^w P(ξᵀy₀)], bounded with tmax(2, 2, (A+w, w)). This square-with-det case lies outside BlockBound's hypothesis (a < b or lastEntry = 0). It is a **surrogate** for the rank-growing step, where the cap rows persist in columns 1…k−1 *(mine)*.

**Kernels.** ℤ[i] (zero characteristic; d_p ≠ 0 only for 4 | p), ℤ[i] translated by ω₁/2, ℤ[ω], 𝒪_{−7} (units ±1, the generic case), 𝒪_{−7} translated. S₁ = sup|θ|e^{−|z|²/2} = 1.67, 1.67, 1.40, 1.63, 1.63. One-variable sharpness: 2log|d̃_p| ∈ [−4.4, +2.9] for p ≤ 400 (V5), i.e. |d_p|² = p!·e^{O(1)}. This agrees with NODE-NORMS (R(a) ∈ [−4.5, 2.2] up to a ≈ 6000).

## 3. Method and results

### E1: square tower (`out_composite6_square.txt`)
Level 0 is 1×1, holding the vector 1. K₁: 1→2 with ν = (A) (det^A). Then K₂…K₈: 2→2 with ν = (A, 0). The same kernel is used at every step.

| kernel | A | D₈ | D₈/8 | **H₈** | B₈ − X₈ | per-step slack log tmax − log‖K‖²_op |
|---|---|---|---|---|---|---|
| ℤ[i] | 48 | 216.4 | 27.1 | **0.73** | 218.5 | 29.1 |
| ℤ[i] | 192 | 277.9 | 34.7 | **1.78** | 280.6 | 37.3 |
| ℤ[i] | 768 | 341.4 | 42.7 | **1.77** | | 45.9 |
| ℤ[i] | 1536 | 370.0 | 46.3 | **3.03** | | 49.4 |
| ℤ[ω] | 1536 | 383.0 | 47.9 | **2.69** | | 51.3 |
| 𝒪_{−7} | 48 | 227.2 | 28.4 | **6.84** | 229.6 | 29.6 |
| 𝒪_{−7} | 1536 | 381.9 | 47.7 | **4.44** | | 50.9 |
| ℤ[i] + ω₁/2 | 1536 | 380.4 | 47.6 | **3.03** | | 50.8 |

(B₈ − X₈: the bound minus the log of the extremal coefficient, i.e. a PtL that reads only y₀^A. The full rows are in the output.) The 𝒪_{−7} kernel and its half-period translate give identical numbers, because their moments agree in modulus (checked to 3·10⁻¹⁴).

- **Per-step increments** of D are constant in m and equal the one-step slack to within 1, for every A.
- **The Hadamard part does not scale with A**: H₈ ≤ 7 while A runs over a factor of 32.
- **The realised gain of step j along the chain** equals log‖K_j‖²_op to within 0.1–0.9 for j ≥ 3. The heavy line is carried to the next step's top singular direction.
- Fit of the per-step D increment *(mine)*: ≈ 29 + 5.9·log(A/48). It is entirely the slack of the one-step bound, of which 8·log(2A+2) comes from tmax's (2|ν|+2)^{2ab} and 8·log S₁ ≈ 4.1 from S², minus the true lattice-coherence gain.

**E1b** uses a different kernel at each successive step (ℤ[i], ℤ[i]+½, ℤ[ω], 𝒪_{−7}, 𝒪_{−7}+½, …):

| A | 48 | 96 | 192 | 384 | 768 | 1536 |
|---|---|---|---|---|---|---|
| H₈ | 5.0 | 5.6 | 5.6 | 9.6 | 9.8 | 10.9 |
| D₈/8 | 28.3 | 32.1 | 35.9 | 40.4 | 44.4 | 48.4 |

So H grows by ≈ +1 per doubling of A, i.e. like log A.

### E2: rank-growing tower 1→2→3(→4) (`out_composite6_growing.txt`)
Here t = 0 (rank +1 per step), the weight (A, 0, …) persists, and each new row has length 0.

| kernel | A | levels | D | **H** | per-step log‖K_j‖²_op − log A! | per-step slack |
|---|---|---|---|---|---|---|
| ℤ[i] | 36 | 1→2→3→4 | 146.8 | **1.40** | 6.4, 13.6, 22.2 | 11.2, 42.5, 91.7 |
| ℤ[i]+½ | 36 | 1→2→3→4 | 152.4 | **3.11** | | |
| 𝒪_{−7} | 36 | 1→2→3→4 | 149.7 | **1.58** | | |
| ℤ[i] | 240 | 1→2→3 | 76.9 | **0.73** | 8.4, 17.2 | 15.7, 60.4 |
| 𝒪_{−7} | 240 | 1→2→3 | 79.0 | **1.13** | 7.3, 16.3 | 16.8, 61.1 |

- The true gain per step *rises* with the rank: more lattice directions add coherently in norm². The bound's polynomial factor rises faster, because 2ab = 4, 12, 24.
- The composite stays multiplicative to within ≤ 3.1.

### E3: one persistent cap row (`out_composite6_wrows.txt`)
Here ν = (A+w, w) at every step; 6 steps from the extremal vector.

"cal" is T₁ − logHook(a⁺ = (w)) − ph(A), the one-step DIV remainder at a top with the true norm in place of the bound. dD is the mean per-step increment of D. H₆ is the Hadamard part after 6 steps.

| kernel | A | w | step slack | cal | w·log A | dD | H₆ |
|---|---|---|---|---|---|---|---|
| ℤ[i] | 48 | 0 / 4 / 16 / 32 | 29.1 / 28.7 / 29.6 / 31.7 | 11.2 / 27.2 / 77.2 / 145.3 | 0 / 15.5 / 61.9 / 123.9 | 29.2 / 28.8 / 29.7 / 31.9 | 2.3 / 1.5 / 1.9 / 2.7 |
| ℤ[i] | 384 | 0 / 4 / 16 / 32 | 41.0 / 39.0 / 39.6 / 35.3 | 14.0 / 39.1 / 110.4 / 206.9 | 0 / 23.8 / 95.2 / 190.4 | 41.6 / 39.3 / 39.9 / 37.0 | 6.5 / 4.0 / 3.6 / 14.4 |
| ℤ[i] | 768 | 4 / 16 | 43.9 / 43.2 | 42.0 / 122.5 | 26.6 / 106.3 | 44.4 / 43.6 | 5.4 / 4.4 |
| 𝒪_{−7} | 384 | 4 / 16 / 32 | 40.5 / 39.5 / 35.9 | 36.8 / 108.9 / 204.6 | 23.8 / 95.2 / 190.4 | 42.2 / 40.1 / 38.0 | 11.6 / 6.5 / 18.3 |
| 𝒪_{−7} | 768 | 4 / 16 | 45.0 / 44.0 | 40.7 / 120.9 | 26.6 / 106.3 | 46.4 / 45.4 | 9.8 / 10.4 |

- **The w-row costs nothing per step.** dD(w) − dD(0) ∈ [−5.4, +2.7] over the whole grid, and (dD(w) − dD(0))/(w·log A) ∈ [−0.26, +0.02]. The w-row factor exp(ph(w)) in tmax is attained by the truth at every step.
- **Calibration.** cal − w·log A = 11 to 22 at every (A, w), rising slowly with w (Stirling's ½·log terms). This matches STEPE's Stirling result (≈ w·log a at a top) with the *true* norm in place of BlockBound.
- Some small w are absent, because the unit group forces those jets to vanish: w = 1, 2 for ℤ[i] with zero characteristic, and w = 1 for the other kernels.

### E4/E5: the Young-diagram remainder over the lifts (`out_composite6_young.txt`)
The shapes are built from the Lean's formulas, with clean interlacing parameters:
- u₀ = a + (k−1)/2, u_i = (k−1)/2 − i, v_i = (k−2)/2 − i;
- w_j = w₁ + (j−1)(t+1+ex), where ex = 1 creates block rows;
- b large, so the small a⁺ rows are 0 (the conservative choice).

This gives ν^{(j)} = (a + w′, w′^{k−1}, blk) and a⁺ = (w′ + (j−1)t)^{k−1}, as STEPE describes.

| k | t | ex | a | w₁ | m | eE_1 … eE_m | Σ/(m·w̄·La) |
|---|---|---|---|---|---|---|---|
| 2 | 0 | 0 | 2000 | 40 | 8 | 292.1 (all j) | 0.879 |
| 2 | 0 | 1 | 2000 | 40 | 8 | 292.1 → 360.1 | 0.895 |
| 2 | 1 | 0 | 200 | 40 | 8 | 202.0 → 175.8 (decreasing) | 0.714 |
| 3, 4 | 0 | 0 | — | 40 | 6 (off-top) | constant 91.1, 85.4 | — |

- With t = 0 and no block rows, eE_j is exactly constant in j.
- For t = 1 it decreases by ≈ t·(k−1)·log w per lift, because the a⁺ rows gain the shift (j−1)t.
- With block rows it increases by ≈ (block mass)·log, bounded by the m(t+1)η·La term of `stepE_num`.
- max_j eE_j/(w_j·La) ≤ 0.96 everywhere. **The accumulated defect is ≤ m·C·w·La with C < 1, independent of m.**
- Over several lifts there is no "big diagram": the hook of lift j is computed from lift j's a⁺ alone (NUM:241-245). A product of step hooks never has to match the hook of a stacked diagram.

## 4. Controls

Sources: `out_composite6_square.txt` (a, a′, b), `out_composite6_controls.txt` (1, 2, 4), `out_composite6_young.txt` (c).

| control | what it changes | result | power |
|---|---|---|---|
| (2) anisotropic kernel | θ only in entry (0,0), d_p = δ_{p0} elsewhere: each step is rank one, plus a fixed rotation U with \|u₀₀\|² = 0.562 between steps | H₈ = 193.5, 774.2, 3096.6 at A = 48, 192, 768. That equals 7·A·log(1/\|u₀₀\|²) to 4 digits | **yes**: an a-proportional composition loss is measured exactly when present |
| (b) wrong coordinate constant | cD = √2, i.e. jets × 2^{p/2}, with the bound still at Ω = 1 | D shifts by −A·log 2 per step (ratio 1.0000 at A = 48…384). D becomes negative, so the "bound" is false | **yes**: a c·a normalisation error is seen at once |
| (c) reused top variable | lift j multiplies the same variable by z^a | log((ma)!) − m·ph(a) = 72.5 (a = 50, m = 2) … 33 277 (a = 2000, m = 8), ≈ m·a·log m. The one-lift allowance 2w·La at w = a/50 is 8–608 | **yes** (arithmetic): this is the binomial the brief feared. It is absent in the Lean because the variables are fresh (§2) |
| (a) non-extremal start | start the square chain at y₀^{A/2}y₁^{A/2} | realised per-step gain within 0.07–0.6 of the heavy chain | **little**, see (1) |
| (a′) true kernel, rotated frame | Sym^A(U) inserted between true steps | extra 2.6–3.2 per step, A-independent (A = 48…768); NaN at A = 1536 (floating-point overflow in the Sym^A(U) builder; not used) | little, see (1) |
| (1) singular values of the true step | — | top cluster within e³ of σ_max: 7, 19, 65 values (ℤ[i], A = 48, 192, 768) and 10, 30, 118 (𝒪_{−7}); median 75–225 below the top in log; about 3/4 of the singular values are exact zeros, from the unit-group selection rules. ‖K e_ext‖²/σ²_max = e^{−1.6…−2.1} | — |
| (4) extremal-coefficient functional | PtL reads only the y₀^A(⊗det^w) coefficient | log share after steps 1…8 fluctuates in [−13, −1.2], with no drift (mean per-step change −1.0 to +0.8) | — |

**Reading (1) *(mine)*.** The lattice sum makes the true step operator nearly maximal on a whole cluster of directions, roughly one per lattice direction of norm ≈ √A. The heavy output of step j lies in that cluster, and step j+1's cluster contains it again. That is why the composite is multiplicative, and why a rotated frame or a non-extremal start costs only O(1). The rank-one control (2) shows that the same engine reports A-sized losses when the cluster is absent. Item (4) shows that a functional reading only the heavy coefficient pays O(log A) once, not per lift.

## 5. Limits

- **Archimedean only.** No p-adic side, no lattices, no index or covolume. Ω is set to 1; the cD control shows what a wrong Ω does.
- **The kernel.** I used a product over matrix entries of a single principal theta, including its half-period translate (the Lean's th0 is such a translate), and both units cases (±1 and ℤ[i]/ℤ[ω]). The Lean's θ_{c,c′} is a finite Heisenberg sum of torsion translates with Schwartz datum and characters (ENGINE §1.1). Those sums could add or cancel phases across translates. They change the per-step constant, but could only create an a-sized loss if the translates cancelled on the heavy line coherently at every step. I did not test that.
- **Size.** Rank ≤ 4; only k = 1 runs on the true rank-growing tower. The w-row is tested on the 2×2 square surrogate (outside BlockBound's hypothesis), not on 2→3→4 with k = 2. A ≤ 1536 and m ≤ 8, against the live a ≈ x·e^{x^ε}, k ≈ x^{4.5} and m ≈ √x. The claim "per-step H is O(1) and A-independent" is extrapolated from A = 48 to 1536 and m ≤ 8.
- **One τ, one class.** The class sums (`cbSq` = n·n′·h·h′·t) and the conjugate periods Ω_ρ are absent. Both are polynomial factors in the Lean's bound.
- **PtL** is either the best functional or the extremal-coefficient functional; the true Bessel functional at the top was not built. The extremal coefficient carries a share e^{−13}…e^{−1.2} of the norm², with no drift in m (control 4). That is a one-off O(log A) cost, not a per-lift one.
- **The identification of the kernel's factorisation is inference** (§2). Everything else in §2 was read.
- What would change the verdict: an a-proportional H in a model with the Heisenberg sum included, or with rank-growing k ≥ 2 steps.

## 6. Conclusion

**The multi-step defect is within the proof's per-lift allowance in the model.**
- The composite of fresh-variable jet maps is multiplicative on the heavy line, for A up to 1536:
  - H ≤ 7 over 8 steps with the same kernel, with no A-dependence;
  - H ≤ 11 with different kernels at successive steps, growing like log A;
  - H ≤ 18 over 6 steps with a w = 32 row.

  A·log 2 would be 33–1065.
- The total defect per step is the polynomial slack of BlockBound, ≈ 2ab·log(2A) + O(1). That is O(rank²·log a) per lift and τ, which is booked (f·Nn²·La in `hB`) and is ≪ b.
- A cap row of length w adds nothing to the per-step defect (w ≤ 32).
- The Young-diagram remainder is ≤ 0.96·w·La per lift, stationary in j.

The structural reason is read from the definitions: each lift uses a new variable and preserves the top degree, so no binomial between lifts can arise. This supports CARRIER §5's prediction, that the Hadamard defect is negligible on the heavy line, in the regime the model reaches. It does not test the Heisenberg/character structure of θ_{c,c′} or ranks ≈ x^{4.5}.
