# `theta40` worker report — the `Θ^40` / `stabilityConstant` numeral cluster

Scope: `Euler/EulerProof.lean` + `Euler/PacketCommonScaleChoice.lean`,
`Euler/ParentRenewalScaleCosts.lean`, `Euler/ParentRenewalParameters.lean`,
`Euler/PacketActualFrameEstimates.lean` (NSE @ f9e8bc5, read-only clone).
Repo has NO Mathlib and NO `lake build` => every claim below is SOURCE-LEVEL (**UNBUILT**).
Every `file:line` was re-read from the original file and is quoted verbatim.

## 0. Mechanism actually used (grounded, not from the brief)

The brief's mechanism is right in outline, but I could sharpen it against a stray Mathlib
source copy on this machine (`/tmp/stray_packages_r12325x1w3/mathlib/Mathlib/...`),
so the following is machine-read Mathlib source, not recollection:

* `Tactic/Linarith/Parsing.lean` `linearFormOfExpr`: coefficients are `ℤ`; `HMul` multiplies
  linear forms (so atom products become MONOMIALS: `K*e*Θ^40` is one monomial `K·e·Θ^40`),
  and **`HPow` with a numeral exponent is expanded by `comp.pow n`** — i.e. a *numeral base*
  raised to a literal exponent is fully evaluated into the coefficient.
* `Tactic/Linarith/Preprocessing.lean` `cancelDenoms`: fires only if the comparison LHS
  `containsConst` one of `HDiv.hDiv / Div.div / Inv.inv / OfScientific.ofScientific`,
  then scales by `CancelDenoms.derive` (numeral denominators only).
* `nlinarithExtras` (same file): adds `sq_nonneg`/`mul_self_nonneg` facts and **all pairwise
  products** `mul_nonneg_of_nonpos_of_nonpos a b` of the preprocessed comparisons
  (including the negated goal), appended *after* the originals.
* `Tactic/Linarith/Verification.lean` `proveFalseByLinarith`: the oracle
  (`.simplexAlgorithmSparse`) returns **ℕ** coefficients; only hypotheses with a NONZERO
  coefficient enter the emitted term (`used := enum_inputs.filterMap certificate[n]?`);
  the term is `Σ cᵢ·tᵢ` with `tᵢ` the *unexpanded* source LHS, and the identity
  `Σ cᵢ·tᵢ = 0` is discharged by `discharger := ring1` (`Frontend.lean`).
  => **the widest kernel numeral ≈ max over USED i of (cᵢ × the product of source literals in tᵢ)**,
  produced inside the kernel-checked `ring1` normalisation, not by `norm_num` on a `Nat` goal.
  A product hypothesis that gets coefficient 0 costs the kernel nothing beyond its own
  `mul_nonneg…` type (which still contains only the *un-multiplied* literals).

Consequence for this cluster: literals like `1000000`, `30000000`, `160000000` almost always
multiply an ATOM or monomial (`K`, `e`, `Θ^n`, `exp 6`, `δ`, `M`), so they enter as monomial
COEFFICIENTS. A *closed numeral product* is formed only where two literals sit in the same
monomial: `1000000 * stabilityConstant` after `unfold` (=`1000000*(320000000*exp 6)`),
`40 * (200000*e)`, `800*(200000*e)`, `2 * (160000000·…)`, `10*(320000000·…)`.

## 1. Findings table

Bit widths are of the widest CLOSED numeral in the emitted certificate.
"deg-1" = the linear certificate that provably exists (I reconstruct it below);
"deg-2 worst" = the same certificate if the simplex oracle instead uses an `nlinarith`
pairwise product of the two widest terms (upper bound, cannot be excluded without a build).

| # | decl (line) | site line(s) | verbatim | closer | literal role | denominators in ctx | deg-1 | deg-2 worst | verdict |
|---|---|---|---|---|---|---|---|---|---|
| C1 | `controlled_velocity_relative_error` (16887) | 16892, 16925 | `(hlam : 0 ≤ lam) (hsmall : 8000000 * e * Θ ^ 21 ≤ 1)` / `\|V t - Z t\| + \|U t + Z₁ t\| ≤ 160000000 * e * Θ ^ 29 * (1 + lam) * F t := by` | statements; closed at 16944 `nlinarith only [hsmall]` and 16957 `nlinarith only [h]` | `8000000`·monomial `e·Θ^21`; at 16944 the closed product `40*200000=8e6`; at 16957 `800*200000=1.6e8` vs `160000000` | `1/4` (hσsmall) → `cancelDenoms` ×4 on that comparison only | **8e6 (23 b)** / **1.6e8 (28 b)** | 6.4e13 (46 b) / 2.56e16 (55 b) | OK |
| C2 | `frame_error_polynomial_bounds` (17913) | 17916, 17925, 17926, 17935, 17994, 17995 | `(hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)`; `4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧`; `8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40` | 17935 `dsimp [M]; nlinarith only [hsmall]`; 17998 `· nlinarith only [hJbound, hPD, hPE, hM]`; 17999 `· nlinarith only [hSbound, hJbound, hJdiv, hEbound, hM]` | every literal multiplies the monomial `K·e·Θ^40` (=`M`) or `ε^2·Θ^n`, `P₀·…`; NO closed numeral product | `1/2`, `1/4`, `P₀/4`, `dJ/P₀` (ATOM denominator → `cancelDenoms` cannot touch it; handled by `div_le_iff₀`/`hJdiv` at 17990-17992) | **3e7 (25 b)** (multipliers 4/16/16 + slack `30000000-205800=29794200` on `hM`) | 9e14 (50 b) | OK |
| C3 | `frame_renewal_order40` (18003) | 18007, 18024, 18025, 18070, 18071 | `(htΘ : y⁻¹ / σ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)`; `y ^ 4 + σ ^ 2 * y ^ 2 + 8 * σ * y ^ 3 + 30000000 * K * e * Θ ^ 40 ∧` | 18069-18071 is a `change` (defeq, no arithmetic); big-literal work is inherited from C2 via 18068 `have hpoly := frame_error_polynomial_bounds …` | as C2 | `y⁻¹`, `1/4`, `1/2` — `y⁻¹` is a variable inverse, so `cancelDenoms` finds no numeral denominator | **3e7 (25 b)** | 9e14 (50 b) | OK |
| C4 | `stabilityConstant` / `_ge` (18479, 18481) | 18479, 18481 | `noncomputable def stabilityConstant : ℝ := 320000000 * exp 6` / `theorem stabilityConstant_ge : 320000000 ≤ stabilityConstant := by` | 18482-18484: `have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)` / `unfold stabilityConstant` / `nlinarith only [hh]` | `320000000` multiplies the ATOM `exp 6`; the only `norm_num` obligation is `(0:ℝ) ≤ 6` from `one_le_exp_iff` | none | **3.2e8 (29 b)** (cert: `1·(320000000 - 320000000·E) + 320000000·(1 - E)`-shaped, multiplier `3.2e8` on `hh`) | 1.024e17 (57 b) | OK |
| C5 | `controlled_stage_references` (18488) | 18492, 18519, 18531, 18542 (+18544-18549, 18556-18561) | `(hlam : 0 ≤ lam) (hsmall : 1000000 * stabilityConstant * e * Θ ^ 40 ≤ 1)`; `let δ := 160000000 * e * Θ ^ 29`; `have hrelSmall : 4 * exp 6 * δ ≤ 1 := by` | 18535 `nlinarith only [hsmall, hm, hKmul]`; **18548 `unfold stabilityConstant at hm hn hsmall` + 18549 `nlinarith only [hm, hn, hsmall]`**; 18558/18561 `nlinarith only [hc.2.1]` / `[hc.2.2]` | at 18549 the `unfold` creates the CLOSED PRODUCT `1000000*(320000000*exp 6)` = `3.2e14 · exp 6`; at 18558/18561 `2*160000000=3.2e8` and `10*(320000000)=3.2e9` | none in the used comparisons (the `1/4`,`1/2` facts are not in the `only` lists) | **3.2e14 (49 b)** at 18549 — cluster max | **1.024e29 (97 b)** at 18549 (`hsmall²`) | NOTE (deg-1 fine, deg-2 would be multi-limb) |
| C6 | `target_compression_order40` (18873) | 18877, 18887 | `(hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1) (hscale : 1 ≤ β * t ^ 2)` / `have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]` | `dsimp [M]; nlinarith only [hsmall]` | `1000000` multiplies monomial `K·e·Θ^40`; goal and hyp are the SAME linear form up to associativity | none | **1e6 (20 b)** | 1e12 (40 b) | OK |
| C7 | `source_coefficient_error_eventually_small` (19957) | 19961, 19963 | `∀ᶠ n in atTop, 1000000 * K * sourceCoefficientError J C c x n * sourceTheta J C x n ^ 40 ≤ 1 := by` / `(1000000 * K)` | 19967 `nlinarith only [hn]` (after `filter_upwards`) | `1000000` × monomial `K·err·Θ^40`; `hn` is the same form re-associated by `.const_mul (1000000*K)` | none | **1e6 (20 b)** | 1e12 (40 b) | OK |
| C8 | `PacketCommonScaleChoice.lean` | 41-48 | `let δ : ℝ := min η (min (1/2) (1/(1000000*K)))` … `have hδK : 1000000*K*δ ≤ 1 := by` / `have hh : δ ≤ 1/(1000000*K) := (min_le_right _ _).trans (min_le_right _ _)` / `have hm := (le_div_iff₀ (show 0 < 1000000*K by positivity)).mp hh` / `nlinarith only [hm]` | 48 `nlinarith only [hm]` | `1000000` × monomial `K·δ`. **`cancelDenoms` never sees a numeral denominator here**: the divisor is `1000000*K` with `K` a VARIABLE, and the division is removed *before* linarith by `le_div_iff₀` (hm : `δ*(1000000*K) ≤ 1`), so the LHS reaching `Parsing.lean` contains no `HDiv`/`Inv` at all and the `cancelDenoms` guard is false | `1/2`, `1/(1000000*K)` (non-numeral) | **1e6 (20 b)** | 1e12 (40 b) | OK |
| C9 | `ParentRenewalScaleCosts.lean` | 20, 174, 176, 179 (+187, 190) | `def errorConstant (CF : ℝ) : ℝ := 30000000*neighborStabilityConstant*CF^2`; `have hK : 0 ≤ 30000000*neighborStabilityConstant := by positivity [neighborStabilityConstant_ge]`; `have hnorm : 30000000*neighborStabilityConstant*G.error*G.Θ^40 ≤` … `nlinarith only [hm]` | 179 `nlinarith only [hm]`; 187 `nlinarith only [hp,hyp,hnorm,hi]`; 190 `nlinarith only [hsp,hnorm]` | `30000000` × monomial `N·err·Θ^40` where `N = neighborStabilityConstant` stays an ATOM (**never `unfold`ed in this file** — verified by grep: the only `unfold neighborStabilityConstant` sites are `PacketNeighborControlled.lean:220,229,232` and `ParentPacketGeometryGuards.lean:200`) | `1/scaleSequence …`, `3000/scaleSequence …` — variable denominators, `simp only [div_eq_mul_inv]` at 186/189 turns them into `⁻¹` atoms; no numeral denominator | **3e7 (25 b)** | 9e14 (50 b) | OK |
| C10 | `ParentRenewalParameters.lean` | 21 | `def tiltError : ℝ := 1500*G.σ+30000000*neighborStabilityConstant*G.error*G.Θ^40` | pure `def`, no tactic | literals multiply atoms/fields | — | 3e7 (25 b) if unfolded into a `nlinarith` (as at C9:190) | 9e14 (50 b) | OK |
| C11 | `PacketActualFrameEstimates.lean` | 36, 49, 51 | `(htΘ : y⁻¹/σ ≤ Θ) (hsmall : 1000000*K*e*Θ^40 ≤ 1)`; `y^4+σ^2*y^2+8*σ*y^3+30000000*K*e*Θ^40 ∧`; `1500*σ+30000000*K*e*Θ^40 := by` | statements; local closer 55 `have hρ : 800*e*Θ^5 ≤ 1/2 := by nlinarith only [hsmall, hp]`; the `3e7` bound is transported verbatim from C3 (67 `have hbound := frame_renewal_order40 …`) | `1000000`/`30000000` × monomial `K·e·Θ^40`; `800` × `e·Θ^5` | `1/2` at 55 → `cancelDenoms` ×2 → multipliers (1e6, 1e6, 1) | **1e6 (20 b)** | 1e12 (40 b) | OK |

## 2. The three items the brief asked about explicitly

### (a) `stabilityConstant_ge` (18481) — does the kernel evaluate `exp 6`? NO.

```
18479: noncomputable def stabilityConstant : ℝ := 320000000 * exp 6
18480:
18481: theorem stabilityConstant_ge : 320000000 ≤ stabilityConstant := by
18482:   have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
18483:   unfold stabilityConstant
18484:   nlinarith only [hh]
```
`exp 6` is an opaque `Real.exp` application: `linearFormOfAtom` makes it ATOM `E`.
The goal becomes `320000000 - 320000000·E ≤ 0`-form, `hh` becomes `1 - E ≤ 0`; the ℕ
certificate is `(negated goal)·1 + hh·320000000 (+ (-1<0)·k)`. Kernel work = `ring1` on
`(320000000·E - 320000000) + 320000000·(1 - E) = 0` → widest numeral `320000000` (**29 bits**).
The only `norm_num` call is on `one_le_exp_iff`'s side goal `(0:ℝ) ≤ 6`. There is **no
numerical evaluation of `exp` anywhere** in the cluster (`Real.exp` has no `norm_num`
extension; nothing computes `e^6`). Same shape at `PacketNeighborControlled.lean:156-159`
(`linarith only [h]`, `1000000000` = 30 bits). Verdict **OK**.

### (b) `hMb : 1000000 * M ≤ 1` (17935 and 18887) — certificate by hand

```
17933:   let M := K * e * Θ ^ 40
...
17935:   have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]
```
(identical at `18884: let M := K * e * Θ ^ 40` / `18887: have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]`,
with `hsmall` at 18877 `1000000 * K * e * Θ ^ 40 ≤ 1`.)

After `dsimp [M]` the goal is `1000000 * (K * e * Θ ^ 40) ≤ 1`; `hsmall` is
`1000000 * K * e * Θ ^ 40 ≤ 1`. Both parse to the SAME single monomial `m = K·e·Θ^40`
with coefficient `1000000` (parsing is associativity-blind: `Sum.mul`).
Preprocessed comparisons: `t₀ = 1 - 1000000·m < 0` (negated goal), `t₁ = 1000000·m - 1 ≤ 0`
(`hsmall`), plus the auto-added `-1 < 0`.
Exact ℕ certificate: **`1·t₀ + 1·t₁ = 0`**, with the strict `t₀` making the sum `< 0`,
i.e. `0 < 0`. Emitted term = `mkLTZeroProof [(t₀,1),(t₁,1)]` (no `mulExpr`, since `n = 1`
is skipped) + `ring1` proving `(1 - 1000000*(K*e*Θ^40)) + (1000000*K*e*Θ^40 - 1) = 0`.
**Exact closed numerals: `1000000` (twice) and `1`. Widest = 1000000 = 2^19.93 → 20 bits.**
`nlinarith`'s extra products (`t₀·t₁`, `t₁²`, `t₀²`) would carry `1000000² = 10^12`
(40 bits) but they get coefficient 0 in this trivially-degenerate system, so they should
not reach the kernel (UNBUILT: not machine-confirmed). Verdict **OK**.

### (c) `PacketCommonScaleChoice.lean:41-47` — does `cancelDenoms` see a numeral denominator?

```
41:   let δ : ℝ := min η (min (1/2) (1/(1000000*K)))
42:   have hδ : 0 < δ := by dsimp [δ]; positivity
43:   have hδη : δ ≤ η := min_le_left _ _
44:   have hδhalf : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
45:   have hδK : 1000000*K*δ ≤ 1 := by
46:     have hh : δ ≤ 1/(1000000*K) := (min_le_right _ _).trans (min_le_right _ _)
47:     have hm := (le_div_iff₀ (show 0 < 1000000*K by positivity)).mp hh
48:     nlinarith only [hm]
```
**No.** Two independent reasons: (i) `K` is a variable, so `1/(1000000*K)` is not a numeral
denominator and `CancelDenoms.derive` has nothing to clear; (ii) the author removes the
division *before* linarith with `le_div_iff₀` (line 47), so the comparison actually handed to
`nlinarith only [hm]` has no `HDiv`/`Inv` head at all and the `cancelDenoms` preprocessor
guard (`lhs.containsConst …`) is simply false. The certificate is again `1·(negated goal) +
1·hm` over the single monomial `K·δ` with coefficient `1000000`: **20 bits**. Verdict **OK**.

### (d) Is `Θ` (or `Θ^40` / `Θ^21`) ever given a NUMERAL base?

**No.** Repo-wide grep for a numeral base with a ≥2-digit exponent
(`grep -rnoE '[0-9]+ *\^ *[0-9]{2,}' --include=*.lean`) returns exactly three hits in the
whole artifact: `NavierStokes/PulseAmplitude.lean:110: 2 ^ 10`,
`Euler/ConstantCorrectionData.lean:146: 9^729`, `Euler/PacketSourceScaleActual.lean:33: 0^60`.
All `Θ^40`/`Θ^29`/`Θ^21` occurrences have a variable/field base
(`Θ`, `G.Θ`, `P.horizon`, `sourceTheta J C x n`, `D.Θ`), and every call site of the four
`…order40` theorems passes structure fields, never literals
(`PacketActualFrameEstimates.lean:67`, `PacketGeometryAssembly.lean:146`,
`PacketPhysicalCompression.lean:84`, `PacketWithinStage.lean:101`, `PacketPhysicalStage.lean:145`).
`K` is likewise always a variable or the `exp`-valued constant. So the kernel is never asked
for a large power of a literal in this cluster. Verdict **OK**.

## 3. Cross-cluster NOTEs (verified citations, outside my assigned list)

1. **The `Θ^40` family's true deg-1 maximum is 10^15, not 3.2e14, and it is in the
   *neighbor* twin of C5**, one file over:
   `Euler/PacketNeighborControlled.lean:154: def neighborStabilityConstant : ℝ := 1000000000*exp 6`
   `…:215: have hs : 4*exp 6*δ ≤ 1 := by` … `…:220: unfold neighborStabilityConstant at hm hn hsmall`
   `…:221: nlinarith only [hm, hn, hsmall]`
   with `hsmall` (`…:165`) `1000000*neighborStabilityConstant*e*Θ^40 ≤ 1` and `δ = 400000000*e*Θ^29`
   (`…:213`). After the `unfold`, `hsmall` carries the closed product `1000000*1000000000 = 10^15`
   (**50 bits**). Deg-1 certificate by hand, with `E = exp 6`, `X = E·e·Θ^29`, `Y = E·e·Θ^40`:
   `t_goal = 1 - 1.6e9·X < 0`, `t_hm = 1e9·X - 1e9·Y ≤ 0`, `t_hsmall = 1e15·Y - 1 ≤ 0`;
   solving `a·t_goal + b·t_hm + c·t_hsmall + d·(-1) = 0` gives `b = 1.6a`, `c = 1.6a/10^6`,
   i.e. the ℕ solution `(a,b,c,d) = (625000, 1000000, 1, 624999)`, so the `ring1` identity
   carries `625000·1.6e9 = 10^15` and `10^6·10^9 = 10^15` (50 bits). Same for
   `Euler/ParentPacketGeometryGuards.lean:198: have hN1 : 1 ≤ 1000000*neighborStabilityConstant := by`
   / `…:201: nlinarith only [he]` → `10^15` after `unfold` at 200 (50 bits).
   Still one machine word. **NOTE**, not a refutation.
2. **`nlinarith` degree-2 is the only thing between this cluster and multi-limb GMP.**
   At `EulerProof.lean:18549` the squared `hsmall` product is `(3.2e14)² = 1.024e29`
   (**97 bits**); at `PacketNeighborControlled.lean:221` it is `(10^15)² = 10^30`
   (**100 bits**); at `EulerProof.lean:18561` (`nlinarith only [hc.2.2]`, closed numerals
   `10*320000000 = 3.2e9` vs `20*exp 6*δ`) the square is `1.024e19` = **64 bits**, i.e.
   sitting exactly on the one-word boundary `2^64 = 1.845e19`. Whether the simplex oracle
   returns the (existing) degree-1 certificate or a product-carrying one CANNOT be decided
   from source. **UNCLEAR / conditional KERNEL-RISK, UNBUILT.**
3. **Near-miss bignum, worth the thread's attention:**
   `Euler/ConstantCorrectionData.lean:146: def pressureBound : ℝ := 9^729`.
   `9^729` is a **2311-bit** number. It is *not* evaluated today: `…:148-149`
   (`theorem pressureBound_one_le : 1 ≤ pressureBound := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)`)
   proves the bound structurally, and the only place it is unfolded is
   `…:165: simpa only [mul_one,pressureBound] using fixed_pressure_constants P hq`
   (a `simp only` with an explicit lemma list; `Nat.reducePow` cannot fire on `(9:ℝ)^(729:ℕ)`).
   But `Linarith/Parsing.lean` DOES expand `numeral ^ numeral` (`comp.pow n`), so a single
   future `unfold pressureBound` inside any `linarith`/`nlinarith`/`norm_num` goal would put a
   2311-bit literal into the kernel. **NOTE** (fragile, but no current kernel bignum).

## 4. Verdict summary for this worker

* deg-1 (the certificate that provably exists in each case): cluster maximum
  **3.2 × 10^14 = 49 bits** at `Euler/EulerProof.lean:18549` (via `unfold stabilityConstant`
  at 18548 turning `1000000 * stabilityConstant` into the closed product `1000000*320000000`).
  Family maximum incl. the neighbor twin: **10^15 = 50 bits**
  (`Euler/PacketNeighborControlled.lean:221`). **64 bits is NOT crossed.**
* deg-2 (`nlinarith` pairwise products, un-excludable without a build): up to
  **97 bits** (18549) / **100 bits** (PacketNeighborControlled:221) → would be multi-limb GMP.
* The brief's "largest closed `Nat` ≈ 5.0×10^17 (59-61 bits)" claim is **consistent with this
  cluster at degree 1** (my max is ~640× smaller) and I do **not** refute it. It is only
  safe, however, under the unproven side condition that no `nlinarith` product term ever
  receives a nonzero oracle coefficient at `EulerProof.lean:18549`,
  `PacketNeighborControlled.lean:221`, `EulerProof.lean:18561`.
* Counts: **OK 9** (C1, C2, C3, C4, C6, C7, C8, C9, C10/C11 grouped as OK), **NOTE 3**
  (C5 deg-2 exposure; §3.1 the 10^15 twin; §3.3 `9^729`), **UNCLEAR 1** (§3.2 oracle choice),
  **ESCALATE 0**, **KERNEL-RISK 0 unconditional** (1 conditional), **REFUTED 0**.
* Everything above is **UNBUILT**: no Mathlib, no `lake build` in the clone; Mathlib mechanism
  claims were read from a stray Mathlib source tree, tactic *outcomes* were not machine-checked.
