# Worker report — threat vector (2): kernel numeral computation (`decide` / big numerals / `Nat.choose`)

Auditor: read-only worker `decide-bignum`. Target: `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`.
No `lake build` (no Mathlib on box). **Source-level reading only.** Nothing under `NSE/` was modified.

## Scope

- Repo-wide scan of all **2659 `.lean` files** (`.lake` excluded) for the token `decide`.
- **210 `decide` occurrences in 85 files** — I re-derived this set myself; it agrees *exactly* (as a multiset of `(file, source-line-text)`) with `audits/nse-deep/DECIDE_SITES.md`.
  **CAVEAT ON THE INPUT ARTIFACT:** the *line numbers* in the version of `DECIDE_SITES.md` I was given were wrong
  (drift of up to ~200 lines, e.g. it says `Euler/EulerProof.lean:17744` for `have hh := hp 0 (by decide)`, whose
  real location is `Euler/EulerProof.lean:17942`). Parent confirmed mid-task that the lists were generated on
  comment-stripped text. **Every line number in this report was re-derived from the original files by me and
  re-read before being cited.**
- Those 210 sites sit inside **129 distinct enclosing declarations**; the 85 files contain **5438 top-level declarations** in total (repo-wide ≈ 50973).
- **Read line-by-line: all 210 `decide` sites** (each with ≥ 8 lines of context) **plus the full signature of every
  lemma whose hypothesis a bare `by decide` is discharging** (76 of the 210 sites are bare `by decide` with no type
  ascription, so the proposition is only visible in the applied lemma's binder — I resolved every one of them).
- Additionally read line-by-line: `Euler/PacketKnownDecomposition.lean` (whole file, 3 non-trivial `decide`s),
  `Euler/PacketKnownPieces.lean:14-25`, `Euler/ConstantCorrectionData.lean:146-169`,
  `Euler/EulerProof.lean:11094-11100` + `12150-12158`, and the 4 `Classical.propDecidable` files (grep-level for `if`/`decide`, not full read).
- Skimmed (grep-driven, not full read): `audits/nse-deep/BIGNUM_SITES.md`'s 121 numerals; the deep read of those is
  delegated (see §Delegated sub-reports).

## Per-declaration findings

### A. Classification of all 210 `decide` sites (task D: **210 of 210 classified**)

Every site is a *tactic-mode* `by decide` (or `show … by decide`) discharging a side condition. There is **no
`native_decide`, no `Decidable.decide` used as a term, no custom `Decidable` instance** anywhere in the repo.

| # sites | proposition decided | what the kernel must actually evaluate for `of_decide_eq_true rfl` | verdict |
|---:|---|---|---|
| 55 | `(k : ℕ) ≠ 0` for k ∈ {2,3,10} (argument of `zero_pow`) | `Nat.decEq k 0` → one `Nat.beq` on a 1–2 digit literal | **OK** |
| 96 | `a ≤ b` / `a < b` / `0 < 1` on ℕ literals; max literal seen = 1000 | `Nat.decLe/decLt` → one `Nat.ble` on ≤ 4-digit literals | **OK** |
| 5 | `k < n` to build `⟨k, _⟩ : Fin n` (n ≤ 3) | `Nat.decLt` → one `Nat.blt` on 1-digit literals | **OK** |
| 19 | `(k : Fin 6).val < 4` (index-range side condition) | reduce `Fin.instOfNat` (`k % 6`, `Nat.mod` on 1-digit args) then `Nat.blt` | **OK** |
| 21 | `i ≠ j` / `i = j` on `Fin 2` / `Fin 3` | `instDecidableEqFin` → `Nat.decEq` after `Fin.val` reduction; 1-digit | **OK** |
| 8 | `s ≠ .mean` / `l ≠ .heat` on 3–4 constructor enums (`KnownPiece`, `Slot`) | derived structural `DecidableEq`: 1 recursor reduction per argument, no recursion depth | **OK** |
| 3 | `(univ : Finset E) = {…}` for E = `KnownPiece` (3 elts), `KnownTerm` (15 elts); `Fintype.card KnownTerm = 15` | reduce derived `Fintype.elems`, build the `insert`-literal with dedup (O(n²) ≈ 10²  structural `DecidableEq` calls), then decide `Finset` equality; the only non-trivial `decide` in the repo | **OK (proposition hand-verified true, see §Kernel-risk)** |
| 1 | `Even 6` | `Nat.even_iff`/`decEq (6 % 2) 0` → one `Nat.mod` on a 1-digit literal | **OK** |
| 2 | `3 ∈ Finset.range 4`, `0 ∈ Finset.range 4` | `List.decidableMem` walk over a 4-element list of 1-digit numerals | **OK** |
| **210** | | | |

Largest numeral occurring in **any** `decide` goal in the repo: **1000** (`Euler/ParentHistoryFrequencyGuard.lean:81`,
`pow_le_pow_right₀ hx1 (by decide : 1 ≤ 1000)`; next largest 80 at `:101`, then 40). Every other `decide` numeral is ≤ 40.
So the whole `decide` surface of the artifact is `Nat.ble`/`Nat.beq`/`Nat.mod` on **1–4 digit literals**: entirely
inside GMP's small-integer path, no multi-limb arithmetic, no `Nat.pow`, no `Nat.gcd`, no `Nat.div` on large values.

### B. The declarations that actually matter (read in full)

| declaration | file:line (decl) | statement in my words | proof mechanism | verdict |
|---|---|---|---|---|
| `sum_knownPiece` | `Euler/PacketKnownDecomposition.lean:14` | a sum over the 3-constructor enum `KnownPiece` equals `f .high + f .mean + f .corrector` | `have hu : (univ : Finset KnownPiece) = {.high,.mean,.corrector} := by decide` (line 16) then `rw [hu]; simp [add_assoc]`. `KnownPiece` is `deriving DecidableEq` (`Euler/PacketKnownPieces.lean:18`) and its `Fintype` instance is **hand-written** with `elems := {.high,.mean,.corrector}` (`PacketKnownPieces.lean:20-22`), so the decided proposition is syntactically `{a,b,c} = {a,b,c}` up to `insert`/dedup reduction | **OK** |
| `card_knownTerm` | `Euler/PacketKnownDecomposition.lean:31` | `Fintype.card KnownTerm = 15` | `by decide`. Kernel must reduce the **`deriving Fintype`-generated** `elems` for `KnownTerm`, take its `card`, and `Nat.beq … 15`. I hand-counted the constructors: `previousLinear`, `previousPressure`, `slow (l r : KnownPiece)` = 3·3 = 9, `fastMeanHigh`, `fastMeanCorrector`, `fastCorrectorHigh`, `fastCorrectorCorrector` ⇒ 2+9+4 = **15**. The proposition is TRUE independently of the kernel's evaluation | **OK** |
| `sum_knownTerm` | `Euler/PacketKnownDecomposition.lean:33` | the known-force sum over `KnownTerm` splits into the 2 previous-order terms + the 3×3 slow products + the 4 fast products | `have hu : (univ : Finset KnownTerm) = {…15 explicit elements…} := by decide` (`:36-41`) then `rw [hu]; simp [sum_knownPiece, add_assoc]`. **This is the single most load-bearing `decide` in the repo**: if the enumeration dropped a constructor the force decomposition would silently lose a term. I checked the 15-element literal element by element against the inductive declaration (`:21-29`): complete, no duplicates, no repeats ⇒ **the proposition is true by hand**, so a kernel `Finset`-decision bug could not make this lemma false | **OK** |
| `knownTermIndices_card` | `Euler/PacketKnownDecomposition.lean:84` | `(knownTermIndices p).card = 15*(p+2)^2` | `Finset.card_product` twice + `card_univ` + `card_knownTerm` + `ring`. Depends on `card_knownTerm`; the `15` is *not* recomputed. Downstream consumer `knownTermIndices_card_room` only needs `card+1 ≤ 100*(p+2)^2`, i.e. there is a **6.6× slack**, so even a miscount would not break the consumer | **OK** |
| `step` / `step_profile` / `step_axis_zero` | `NavierStokes/SlowRecursion.lean:776`, `:784`, `:873` | build the next coefficient tuple from 4 components + transport their profile / axis-vanishing | 11 `by decide` sites all discharging `(i : Fin 6).val < 4` for `i = 0,1,2,3` (`stepComponent`'s binder, `SlowRecursion.lean:732`). Kernel work: reduce `Fin.instOfNat` (`k % 6`) then `Nat.blt k 4`. `Coefficient R U = Fin 5 → AxisFunction R U` (`:722`), consistent with the 5-entry `![a,u,k,p,betaOperator …]` at `:782` — no index/arity mismatch | **OK** |
| `norm_sq_le_eight_mixedEnergy_on_cube` | `NavierStokes/PeriodicSobolev.lean:242` | `‖f x‖² ≤ 8 · mixedEnergy f` on the unit cube | 10 `by decide` sites discharging `j ≠ i` / `k ≠ i` / `k ≠ j` on `Fin 3` (binders at `:162`, `:177-178`). Pure `Nat.decEq` on 1-digit `Fin.val`s | **OK** |
| `exponential_error_small` | `Euler/EulerProof.lean:12150` | `256 ≤ z → exp(-z) ≤ 1/(8z³)` | `have h := factorial_decay 4 z hz0.le` (`:12153`) instantiates `t^n·exp(-t) ≤ n!` (`:11094`) at `n = 4`, then **`norm_num only [Nat.factorial, Nat.cast_ofNat] at h`** (`:12154`) forces the **only real closed factorial evaluation in the repo**: `(Nat.factorial 4 : ℝ) ⇝ 24`. Kernel work = 4 unfoldings of the recursive `Nat.factorial` equation + 3 one-digit `Nat.mul`s. Then `nlinarith` with `192 ≤ z`. Slack is enormous (24 vs the 1/8 target) | **OK** |
| `pressureBound`, `pressureBound_one_le`, `identity_pressure` | `Euler/ConstantCorrectionData.lean:146`, `:148`, `:160` | a pressure constant defined as `(9:ℝ)^729`, and `1 ≤ 9^729` | `pressureBound_one_le := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 9)` — the exponent **stays symbolic**; `identity_pressure` proves `… ≤ pressureBound` by `simpa only [mul_one, pressureBound] using fixed_pressure_constants …` whose conclusion is literally `… ≤ (9*L)^729` (`Euler/GevreyUniformConstants.lean:82-83`) with `L := 1`, so the match is *syntactic* after `mul_one`. **The kernel never evaluates `9^729`** (which would be a 696-digit numeral) — ℝ is opaque, and no tactic asks for its decimal value | **OK** |
| `card_liftedRectangles_le` | `NavierStokes/TorusCoverDegree.lean:302` | `Nat.card (range (sheetRectangle g r)) ≤ 14 ^ maximumGap` | `Nat.pow_le_pow_right (by decide) hgap`, i.e. `by decide : 1 ≤ 14`. **The exponent `maximumGap` is a variable**, so `14^maximumGap` is never evaluated | **OK** |
| `accumulatedGaussianBlock_band_pow` | `NavierStokes/ErrorHarmonics.lean:501` | a harmonic-band bound with band `2 ^ steps` | `Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_of_lt hs)` (`:507`). Exponent symbolic ⇒ no kernel `Nat.pow` | **OK** |
| `summable_integer_weight_inv_two` | `NavierStokes/SmoothFourierData.lean:312` | `Summable (fun n : ℤ => ((1+|n|)^2)⁻¹)` | `Real.summable_one_div_nat_pow.mpr (by decide)` (`:315`), the `decide` proving `1 < 2` on ℕ | **OK** |
| `native_slot_length_lower` | `NavierStokes/GaussianTailFlat.lean:656` | a uniform lower bound `κ(1+S n) ≤ slotLength` | `(Finset.range 4).exists_min_image … (by exact ⟨0, by decide⟩)` (`:662-664`); the `decide` proves `0 ∈ Finset.range 4` via a 4-element `List` membership walk | **OK** |
| `sum_inv_choose_le_three` and the 4 other `Nat.choose` lemmas | `Euler/EulerProof.lean:108,126,150,162,172` | see task C below | **no kernel binomial computation** — details in the delegated sub-report | **OK** |

## Delegated sub-reports

I spawned two read-only children on disjoint slices; their reports live beside this one:

- **Task C (`Nat.choose`/factorial):** `audits/nse-deep/workers/decide-bignum-partC.md` — verdict: all five
  declarations `OK`, **no kernel binomial computation**; `le_choose_of_interior:108` non-vacuous (`n ≥ 2`),
  `sum_inv_choose_le_three:126` true with slack (real max 8/3 ≤ 3) and **live** downstream
  (`EulerProof.lean:239` → `majorant_convolution:226` → `sequence_product_majorant:410` →
  `Euler/GevreyProductLp.lean:83`); `shifted_factorial_kernel_le`'s "kernel" is an *integral* kernel, not the Lean
  kernel. Independently corroborated by me for `factorial_decay 4` (see table).
- **Task B (big numerals, `AxisModelBounds`, `ConstantCorrectionData`, repo-wide closed-Nat search):**
  `audits/nse-deep/workers/decide-bignum-partB.md` (322 lines). Verdict **no KERNEL-RISK, no SUSPICIOUS**. Key results,
  which I cross-checked against my own scans:
  - **Zero ℕ-valued literals with more than 4 digits anywhere in real code.** All 308 sites with ≥ 5-digit numerals are
    ℝ-literals (51 of the 121 `BIGNUM_SITES` rows verified against source; 41 of the rows are comments).
    Largest ℕ literal in the repo: **1000** (`Euler/ParentHistoryFrequencyGuard.lean:81`) — matching my `decide` scan.
    Largest closed `Nat.pow`: `3^6 ≤ 729` (`Euler/GevreyUniformConstants.lean:73`).
  - **Largest closed Nat the kernel must ever evaluate: ≈ 5.0·10^17 (61 bits)**, inside an `nlinarith` certificate at
    `NavierStokes/PulseCone.lean:1017-1018` (`200097999 · 2499900001 = 500224987900197999`, denominator 2·10^18).
    **Still one machine word — never multi-limb, so never on GMP's multi-limb code paths.**
  - `9^729` (`Euler/ConstantCorrectionData.lean:146`) confirmed **never normalised**; upstream is `(9*L)^729` with `L`
    a variable (`Euler/GevreyUniformConstants.lean:70`).
  - Tightest strict inequality in the repo: `NavierStokes/AxisModelBounds.lean:56`,
    `(53/200 : ℝ) < (305719/1152000 : ℝ)`, proved by `norm_num`; exact gap **439/1152000 ≈ 3.81·10⁻⁴**, which the
    kernel checks as `53·1152000 = 61 056 000 < 61 143 800 = 305719·200` (relative gap of the cross products
    ≈ 0.144 %). 8-digit multiplication — safe.
  - `305719/1152000 = cubicLower(41/20)` **exactly**, so `AxisModelBounds.lean:25` is a margin-zero (tight-by-construction)
    bound; but the child reports **nothing consumes `profile_bounds`/`model_bounds`** (only the aggregator import
    `PaperAdditionalResults.lean:4`), and the live bound is `1/4 < bessel` (`NavierStokes/AxisSeries.lean:295`) with
    margin `17719/1152000`. So the tight constant is reporting, not load-bearing.
  - No `native_decide`; no `decide` on ≥ 4-digit literals; no closed `Nat.gcd`/`div`/`mod`; all side conditions
    re-derived true in exact `Fraction` arithmetic.
  - The child independently reports the same line-number staleness in `BIGNUM_SITES.md` (109 of 121 rows off, +207 for
    `EulerProof.lean`) that I found in `DECIDE_SITES.md`.

## Escalations

Ranked by how much an expert answer would change the verdict.

1. **`Euler/PacketKnownDecomposition.lean:33` (`sum_knownTerm`, decide at `:36-41`) — the only load-bearing
   `decide` in the artifact.** Question for an expert: *is the 15-element `Finset KnownTerm` literal exactly the
   image of `Fintype.elems` from `deriving Fintype`, and does `sum_knownTerm_raw` (`:100`) plus every consumer of
   `sum_knownTerm` really cover all 15 constructors — in particular are `.slow l r` products for `l = r = .mean`
   treated by the same estimate as the off-diagonal ones?* What would settle it: `#eval Fintype.card KnownTerm`,
   `#print axioms sum_knownTerm`, and a `Finset.univ.val.toList` dump in a built environment; failing that, a
   by-hand recount (I did the recount: 2 + 3·3 + 4 = 15, list complete and duplicate-free ⇒ statement true).
2. **`NavierStokes/AxisModelBounds.lean:56`** — `(53/200 : ℝ) < (305719/1152000 : ℝ)`, margin 0.144 %.
   Question: *is `305719/1152000` derived from a truncated series with a rigorous remainder bound, or reverse
   engineered to just clear `53/200`?* The tactic question is **settled**: `norm_num`, one 8-digit `Nat` product, and
   `305719/1152000 = cubicLower(41/20)` exactly — so the constant is the *value* of the cubic lower model at the
   window endpoint, not a fudge. Remaining question: *is `AxisProfile.cubicLower` itself a rigorous lower bound for
   `AxisSeries.bessel 1` with a proved remainder term?* What would settle it: re-derive the Bessel truncation error
   independently. Note the *live* consumer bound is the much slacker `1/4 < bessel` (`NavierStokes/AxisSeries.lean:295`).
3. **`Classical.propDecidable` as a default-priority `local instance`** at
   `NavierStokes/ActualParticularPhysicalData.lean:24`, `ActualSignedPhysicalData.lean:22`,
   `InitialPhysicalData.lean:28`, `PositiveTimeSignedData.lean:24`. Question: *do any two occurrences of the same
   `if`-condition in these files elaborate with different `Decidable` instances, and does any downstream lemma
   silently rely on `Subsingleton (Decidable p)` to identify them?* And: *does any theorem about
   `potentialFamily`/`pressureFamily` (`InitialPhysicalData.lean:364,373`) get its content only from the `else 0`
   junk branch (i.e. is it true merely because `0 < x.1.1` fails)?* What would settle it: `set_option pp.all true`
   on those definitions in a built environment, plus a check that every consumer supplies `0 < x.1.1`.
4. **`NavierStokes/SlowRecursion.lean:964` — `rw [WellFounded.fix_eq]` then `rfl`.** Not my vector, but this is the
   one place in my reading where the kernel must unfold a well-founded recursion (`Acc.rec`). Question for the
   recursor worker: *does the `rfl` at `:965` close a goal that requires the kernel to reduce `Acc.rec` on an opaque
   accessibility proof?* What would settle it: `#print axioms` + `set_option maxHeartbeats` behaviour on a build.
5. **`Euler/ConstantCorrectionData.lean:146` — `def pressureBound : ℝ := 9^729`.** Question: *is `729 = 9^3` an
   intentional and sufficient exponent, or a placeholder?* This is not a kernel risk (never evaluated) but a
   9-to-the-729 pressure constant is a red flag for whether the quantitative scheme closes at all; hand to the
   constants/semantics worker.

## Residue — what I could NOT check

- **Nothing was compiled.** No Mathlib build exists on this box (disk full), so I could not run `lake build`,
  `#eval`, `#print axioms`, `decide?`, or check which `Decidable` instance elaboration actually picks. Every claim
  about *which instance is used* is inferred from the source and from the fact that the artifact reportedly
  compiles; a `decide` that resolved to `Classical.propDecidable` would not compile, which is my evidence that
  none did.
- **Mathlib lemma signatures were not verified against the pinned revision by me** (my child checked a sample
  against Mathlib v4.29.0 sources; repo pins rev `85e3a25e`). If a Mathlib lemma name in this repo has a different
  signature than I assumed (e.g. `pow_le_pow_right₀` taking `1 ≤ a` vs `0 ≤ a`), a `by decide` could be discharging
  a different proposition than the one I recorded. The propositions are all tiny Nat facts either way.
- **I did not read the ≈50 000 declarations of the repo.** My reading was `decide`/numeral-driven: 210 sites + the
  ~30 enclosing declarations that carry non-trivial content + 4 whole files. Vacuity/junk-value auditing of
  declarations *without* `decide` or big numerals is out of my scope.
- **`norm_num`/`nlinarith` certificate sizes are not measurable from source.** I can say the *goals* involve ≤ 10-digit
  ℝ literals; I cannot bound the Positivstellensatz certificates `nlinarith` emits (some `nlinarith only [...]` calls
  in `Euler/EulerProof.lean:17935-17990` combine 4+ hypotheses with `Θ^40`-degree terms). If a kernel arithmetic bug
  were to matter anywhere, it would be inside one of those certificates, and only a build could measure them.
- **The two `insert`-literal `decide`s' exact reduction cost** (`PacketKnownDecomposition.lean:16,36-41`) is my
  estimate (O(n²) ≈ 10² comparisons), not a measurement.

## Appendix — all 210 `decide` sites, with verified line numbers

Grouped by file; `decl` is the enclosing declaration (name @ its own line). Category keys are the rows of the
table in §A. Verdict is **OK** for every site (see §Kernel-risk for why); the three `F` rows are the only
non-trivial kernel reductions and the one `sum_knownTerm` row is the only load-bearing one.


**`Euler/BaseEulerGuards.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 124 | A `k≠0` | `lowBoundsOn` @ 100 | `simp only [mul_zero,zero_mul,zero_pow (by decide : 3 ≠ 0),add_zero]` |

**`Euler/CompactSolenoidalDensity.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 39 | A `k≠0` | `weakHarmonicOn_univ_eq_zero` @ 21 | `((tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp hrad)` |

**`Euler/CurlTransportAlgebra.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 81 | C `k<n` (Fin mk) | `vectorCurl_convection` @ 29 | `simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>` |

**`Euler/EulerProof.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 5781 | G `Even 6` | `besselWeight_six_le_pure_six` @ 5768 | `exact (by decide : Even 6).pow_abs (ξ i)` |
| 10394 | A `k≠0` | `terminal_poincare` @ 10365 | `simp only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_eq_mul]` |
| 15729 | A `k≠0` | `triangular_ray_formula` @ 15680 | `simp only [sub_self, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, sub_zero] at…` |
| 15930 | A `k≠0` | `triangular_ray_difference_bound` @ 15872 | `simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at herr` |
| 16073 | C `k<n` (Fin mk) | `scaled_ray_entry_identity` @ 16066 | `simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>` |
| 16272 | C `k<n` (Fin mk) | `scaled_velocity_entry_identity` @ 16265 | `simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>` |
| 16425 | C `k<n` (Fin mk) | `scaled_unprojected_entry_identity` @ 16413 | `simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>` |
| 16615 | B ℕ-order | `velocity_rhs_error` @ 16579 | `have h45 : Θ ^ 4 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by decide)` |
| 16665 | B ℕ-order | `velocity_rhs_error` @ 16579 | `have h2 : Θ ^ 2 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` |
| 16666 | B ℕ-order | `velocity_rhs_error` @ 16579 | `have h4 : Θ ^ 4 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` |
| 16667 | B ℕ-order | `velocity_rhs_error` @ 16579 | `have h6 : Θ ^ 6 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` |
| 16668 | B ℕ-order | `velocity_rhs_error` @ 16579 | `have h7 : Θ ^ 7 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` |
| 16669 | B ℕ-order | `velocity_rhs_error` @ 16579 | `have h8 : Θ ^ 8 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` |
| 16670 | B ℕ-order | `velocity_rhs_error` @ 16579 | `have h11 : Θ ^ 11 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` |
| 16928 | B ℕ-order | `controlled_velocity_relative_error` @ 16887 | `have hh := pow_le_pow_right₀ hΘ (show 5 ≤ 21 by decide)` |
| 17335 | B ℕ-order | `frame_cross_numerator_error` @ 17321 | `have h24 : Θ ^ 2 ≤ Θ ^ 4 := pow_le_pow_right₀ hΘ (by decide)` |
| 17942 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have hh := hp 0 (by decide)` |
| 17950 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have hρb : ρ ≤ 1 / 2 := by have hh := hp 5 (by decide); dsimp [ρ]; nlinarith only [hh, hMb]` |
| 17951 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have hηb : η ≤ 1 / 2 := by have hh := hKp 29 (by decide); dsimp [η]; nlinarith only [hh, hMb]` |
| 17952 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have hAb : 210 * e * Θ ^ 2 ≤ 1 := by have hh := hp 2 (by decide); nlinarith only [hh, hMb]` |
| 17953 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have hEb : dE ≤ 1 := by have hh := hεp 4 (by decide); dsimp [dE]; nlinarith only [hh, hMb]` |
| 17955 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h4 := hp 4 (by decide)` |
| 17956 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h5 := hp 5 (by decide)` |
| 17957 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h31 := hKp 31 (by decide)` |
| 17970 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h9 := hp 9 (by decide)` |
| 17971 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h6 := hεp 6 (by decide)` |
| 17976 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h8 := hεp 8 (by decide)` |
| 17980 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h9 := hp 9 (by decide)` |
| 17981 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h33 := hKp 33 (by decide)` |
| 17982 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h6 := hp 6 (by decide)` |
| 17983 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have h4 := hεp 4 (by decide)` |
| 17987 | B ℕ-order | `frame_error_polynomial_bounds` @ 17913 | `have hh := hεp 4 (by decide)` |
| 18344 | B ℕ-order | `scalar_coefficient_bounds` @ 18324 | `· have hh : \|t\| ^ 3 ≤ \|t\| ^ 4 := pow_le_pow_right₀ (le_of_not_ge ht) (by decide)` |
| 18529 | B ℕ-order | `controlled_stage_references` @ 18488 | `have hpow21 : Θ ^ 21 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)` |
| 18530 | B ℕ-order | `controlled_stage_references` @ 18488 | `have hpow29 : Θ ^ 29 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)` |
| 18890 | B ℕ-order | `target_compression_order40` @ 18873 | `have hh := hp 5 (by decide)` |
| 18894 | B ℕ-order | `target_compression_order40` @ 18873 | `have hh := hp 6 (by decide)` |
| 18919 | B ℕ-order | `target_compression_order40` @ 18873 | `have hm := hp 2 (by decide)` |
| 19804 | B ℕ-order | `source_neighbor_error_summable` @ 19785 | `pow_le_pow_right₀ hp (by decide)` |
| 20168 | B ℕ-order | `source_good_interval_cost_summable` @ 20150 | `(by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_right₀ hp (by decide : 5 ≤ 7))` |

**`Euler/InviscidCorrectionUniqueness.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 81 | A `k≠0` | `inviscid_correction_unique` @ 25 | `simpa only [E,StabilityBudget.growth,sub_self,abs_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul…` |

**`Euler/LpOperatorFieldPath.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 154 | A `k≠0` | `supported_quadratic_upper` @ 142 | `· simp only [hu hs,map_zero,inner_zero_left,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,l…` |

**`Euler/MetricRootLimit.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 25 | A `k≠0` | `regularized_root_tendsto` @ 22 | `simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using` |

**`Euler/OrdinaryLogarithmicGradient.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 47 | H `range` mem | `logarithmic_gradient_bound` @ 29 | `single_le_sum (fun _ _ => norm_nonneg _) (by decide : 3 ∈ range (3+1))` |

**`Euler/OrdinaryRegularizedCauchy.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 46 | A `k≠0` | `regularized_l2_comparison` @ 22 | `hinit,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]` |

**`Euler/OrdinarySobolevL4.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 119 | A `k≠0` | `square_norm_le_two` @ 113 | `simpa only [h20,h60,mul_zero,zero_pow (by decide : 3 ≠ 0),add_zero,` |
| 120 | A `k≠0` | `square_norm_le_two` @ 113 | `zero_pow (by decide : 2 ≠ 0)] using square_norm_scaled h2 h6 1 zero_lt_one` |

**`Euler/PacketActualFrameEstimates.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 54 | B ℕ-order | `physical_frame_renewal_order40` @ 26 | `have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)` |

**`Euler/PacketBaseGuardScales.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 58 | A `k≠0` | `baseGuardCost_tendsto_zero` @ 50 | `norm_num only [zero_pow (by decide : 2 ≠ 0),zero_div,mul_zero,add_zero,` |
| 59 | A `k≠0` | `baseGuardCost_tendsto_zero` @ 50 | `zero_pow (by decide : 3 ≠ 0),zero_mul] at h` |

**`Euler/PacketControlledPropagator.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 52 | B ℕ-order | `controlled_velocity_propagator_within` @ 16 | `have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he` |

**`Euler/PacketForwardFactorization.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 135 | A `k≠0` | `uncutVelocity_ne_zero` @ 126 | `rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hl` |

**`Euler/PacketGeometryGuards.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 55 | B ℕ-order | `error_le_half` @ 52 | `(by decide : 0 ≤ 40)` |
| 77 | B ℕ-order | `ray_error_small` @ 74 | `(by decide : 5 ≤ 40)` |
| 84 | B ℕ-order | `relative_error_small` @ 82 | `have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 29 ≤ 40))` |
| 94 | B ℕ-order | `scalar_error_small` @ 90 | `have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 29 ≤ 40))` |
| 102 | B ℕ-order | `propagator_small` @ 101 | `have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 21 ≤ 40)) …` |

**`Euler/PacketInductionStage.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 72 | A `k≠0` | `sigma_pos` @ 68 | `rw [hz,zero_pow (by decide : 2 ≠ 0),zero_mul] at ht` |

**`Euler/PacketInitialScaleSummability.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 81 | B ℕ-order | `high_summable` @ 59 | `div_le_div_of_nonneg_left hx (by positivity) (pow_le_pow_right₀ hp (by decide))` |

**`Euler/PacketKnownDecomposition.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 16 | F Fintype/Finset | `sum_knownPiece` @ 14 | `have hu : (univ : Finset KnownPiece) = {.high, .mean, .corrector} := by decide` |
| 31 | F Fintype/Finset | `card_knownTerm` @ 31 | `theorem card_knownTerm : Fintype.card KnownTerm = 15 := by decide` |
| 41 | F Fintype/Finset | `sum_knownTerm` @ 33 | `.fastMeanHigh, .fastMeanCorrector, .fastCorrectorHigh, .fastCorrectorCorrector} := by decide` |

**`Euler/PacketKnownTermProfiles.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 38 | I enum DecEq | `mean_profile_fits` @ 25 | `exact KnownPiece.fast_corrector_profile_mean .high S i j p (by decide) hl.1 hr.1 hn` |
| 41 | I enum DecEq | `mean_profile_fits` @ 25 | `exact KnownPiece.fast_corrector_profile_mean .corrector S i j p (by decide) hl.1` |
| 58 | I enum DecEq | `high_profile_fits` @ 44 | `exact KnownPiece.fast_mean_profile_high .high S i j p (by decide)` |
| 62 | I enum DecEq | `high_profile_fits` @ 44 | `exact KnownPiece.fast_mean_profile_high .corrector S i j p (by decide)` |
| 66 | I enum DecEq | `high_profile_fits` @ 44 | `exact KnownPiece.fast_corrector_profile_high .high S i j p (by decide) hl.1 hr.1 hn` |
| 69 | I enum DecEq | `high_profile_fits` @ 44 | `exact KnownPiece.fast_corrector_profile_high .corrector S i j p (by decide) hl.1` |

**`Euler/PacketNeighborControlled.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 119 | B ℕ-order | `controlled_neighbor_relative_error_within` @ 77 | `have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he` |
| 140 | B ℕ-order | `controlled_neighbor_relative_error_within` @ 77 | `have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 8 ≤ 29))` |
| 203 | B ℕ-order | `controlled_neighbor_stage_references_within` @ 161 | `have hm := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 21 ≤ 40)) he` |
| 216 | B ℕ-order | `controlled_neighbor_stage_references_within` @ 161 | `have hm := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))` |

**`Euler/PacketParameterEnvelope.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 60 | B ℕ-order | `source_size_le` @ 23 | `have hp := monomial_le_polynomialFactor J (by omega) X hX n 0 1000 (by decide) le_rfl` |
| 83 | B ℕ-order | `source_size_le` @ 23 | `monomial_le_polynomialFactor J (by omega) X hX n 20 20 le_rfl (by decide)` |

**`Euler/PacketPhysicalNeighbor.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 87 | B ℕ-order | `physical_neighbor_stage_references` @ 19 | `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 40)) he` |

**`Euler/PacketPhysicalPropagator.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 71 | B ℕ-order | `physical_tangent_propagator` @ 19 | `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he` |

**`Euler/PacketPhysicalSign.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 43 | B ℕ-order | `controlled_pressure_ratio_lower` @ 17 | `have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)` |
| 47 | B ℕ-order | `controlled_pressure_ratio_lower` @ 17 | `have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))` |
| 75 | B ℕ-order | `controlled_pressure_ratio_lower` @ 17 | `have hp6 := scaled_power_le hΘ hK he (by decide : 6 ≤ 40)` |
| 76 | B ℕ-order | `controlled_pressure_ratio_lower` @ 17 | `have hp7 := scaled_power_le hΘ hK he (by decide : 7 ≤ 40)` |
| 77 | B ℕ-order | `controlled_pressure_ratio_lower` @ 17 | `have hp33 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 33 ≤ 40))` |
| 123 | B ℕ-order | `physical_pressure_positive_order40` @ 98 | `have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)` |

**`Euler/PacketPhysicalStage.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 82 | B ℕ-order | `physical_stage_references` @ 20 | `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 40)) he` |

**`Euler/PacketPressureScaleCosts.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 81 | B ℕ-order | `badCost_bound` @ 60 | `have hp4 : p^4 ≤ p^7 := pow_le_pow_right₀ hp (by decide)` |
| 82 | B ℕ-order | `badCost_bound` @ 60 | `have hj5 : p^4 ≤ j^5 := (pow_le_pow_left₀ hp0 hpj 4).trans (pow_le_pow_right₀ hj (by decide))` |
| 168 | B ℕ-order | `parameters_le_source_exponential` @ 141 | `(pow_le_pow_right₀ hp (by decide : 4 ≤ 7))` |

**`Euler/PacketPrimaryDynamics.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 65 | A `k≠0` | `labelVelocity_exists_ne_zero` @ 56 | `rw [hn t,norm_zero,zero_pow (by decide : 2 ≠ 0)] at h` |

**`Euler/PacketReferenceRatio.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 37 | A `k≠0` | `equation30_slope_ratio_dominates` @ 12 | `simpa only [hF0, hF₁0, hZ₁0, D, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,` |

**`Euler/PacketSizeComparison.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 72 | B ℕ-order | `physical_size_comparison_order40` @ 45 | `exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))` |
| 75 | B ℕ-order | `physical_size_comparison_order40` @ 45 | `have hρ : ρ ≤ 1/2 := by have hh := hp 5 (by decide); dsimp [ρ]; nlinarith only [hh, hA]` |
| 78 | B ℕ-order | `physical_size_comparison_order40` @ 45 | `have he1 : e ≤ 1 := by have hh := hp 0 (by decide); norm_num at hh; linarith only [hh, hA]` |
| 82 | B ℕ-order | `physical_size_comparison_order40` @ 45 | `(mul_le_mul_of_nonneg_right hε2e (pow_nonneg hΘ0 4)).trans (hp 4 (by decide))` |
| 104 | B ℕ-order | `physical_size_comparison_order40` @ 45 | `have hp7 := hp 7 (by decide)` |

**`Euler/PacketSourceParameterScales.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 86 | B ℕ-order | `previousFrequency_power_le` @ 74 | `(mul_le_mul_of_nonneg_left (predecessor_power_le J hJ X hX n 4 (by decide)) hc)` |
| 92 | B ℕ-order | `previousShear_le_exponential` @ 88 | `(exp_le_exp.mpr (predecessor_power_le J hJ X hX n 7 (by decide)))` |
| 96 | B ℕ-order | `shear_le_exponential` @ 94 | `exp_le_exp.mpr (current_power_le J hJ X hX n 5 (by decide))` |
| 121 | B ℕ-order | `base_inverse_time_le` @ 107 | `_ ≤ 2*X^1000 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by decide)) (by norm_num)` |
| 126 | B ℕ-order | `inverse_time_le_factor` @ 123 | `have hp := monomial_le_polynomialFactor J hJ X hX n 0 1000 (by decide) le_rfl` |

**`Euler/PacketSourceScaleBounds.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 70 | B ℕ-order | `sourceNeighborError_bound` @ 62 | `(pow_le_pow_right₀ hp (by decide : 4 ≤ 7))` |
| 164 | B ℕ-order | `sourceGoodCost_bound` @ 156 | `(pow_le_pow_right₀ hp (by decide : 5 ≤ 7))` |

**`Euler/ParentHistoryFrequencyGuard.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 81 | B ℕ-order | `base_inverse_le_initial_frequency` @ 76 | `simpa only [pow_one] using pow_le_pow_right₀ hx1 (by decide : 1 ≤ 1000))` |
| 101 | B ℕ-order | `base_inverse_le_previous_frequency_pow80` @ 95 | `simpa only [pow_one] using pow_le_pow_right₀ hk (by decide : 1 ≤ 80))` |

**`Euler/ParentPacketBadRatioPolynomial.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 144 | B ℕ-order | `prefactor_bound` @ 139 | `have hθ : Θ ≤ Θ^5 := by simpa only [pow_one] using pow_le_pow_right₀ hΘ (by decide : 1 ≤ 5)` |

**`Euler/SourceCylinderPressureMean.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 82 | A `k≠0` | `normal_ne_zero_of_lower` @ 78 | `rw [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h` |

**`Euler/SourcePotentialTime.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 38 | A `k≠0` | `potentialCoefficient_hasDerivWithinAt` @ 30 | `rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h` |

**`Euler/SourcePotentialTimeCoefficient.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 127 | A `k≠0` | `potentialTimeCoefficient_apply` @ 121 | `rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h` |

**`Euler/SourcePotentialTimePath.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 75 | A `k≠0` | `potentialTimePath_apply` @ 70 | `rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h` |
| 136 | A `k≠0` | `potentialTimePath_hasDerivWithinAt` @ 128 | `rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h` |

**`Euler/TerminalTimePrimitive.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 330 | A `k≠0` | `realPrimitive_poincare` @ 318 | `simp only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_eq_mul]` |

**`Euler/TransversePacketCorrectorParity.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 33 | A `k≠0` | `rawPotential_smooth` @ 28 | `rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hl` |

**`NavierStokes/ActualCandidateConstruction.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 728 | D `Fin` DecEq | `graph_cylinderPoint` @ 699 | `simp only [show (0 : Fin 3) ≠ 2 by decide, ite_false, add_zero]` |

**`NavierStokes/ActualCorrectionModels.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 838 | A `k≠0` | `virtualStress_smoothAt` @ 827 | `simpa only [modelCoordinates, stablePoint, hzero, zero_pow (by decide : 2 ≠ 0), zero_div] using` |

**`NavierStokes/ActualInitialExcluded.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 187 | A `k≠0` | `closedSlowSet_axial_ne` @ 183 | `rw [hT, hz, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hsep` |

**`NavierStokes/ActualPrimaryCoherence.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 1886 | A `k≠0` | `cartesianVelocity_axis_zero` @ 1880 | `zero_pow (by decide : 2 ≠ 0),zero_add,Real.sqrt_zero] using physicalAxisRadius_pos L` |

**`NavierStokes/ActualPrimaryCovariance.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 330 | A `k≠0` | `viewTangent_pair_covariance` @ 319 | `intervalIntegral.integral_zero, zero_div, Finset.sum_const_zero, hm, zero_pow (by decide : (2…` |

**`NavierStokes/ActualSignedMeanBinding.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 295 | A `k≠0` | `primary_diagonal_average` @ 282 | `PartitionedCovariance.amplitude, hm, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]` |

**`NavierStokes/ActualSignedPhysicalData.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 375 | C `k<n` (Fin mk) | `positiveIndex` @ 374 | `(L, ⟨1, by decide⟩)` |

**`NavierStokes/BaseRankPatch.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 52 | I enum DecEq | `nominal_mean_fields` @ 44 | `W.heat.physical.coefficients (s := .mean) (by decide) p.2 hp` |

**`NavierStokes/EntranceAlignedBase.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 275 | A `k≠0` | `baseAgreement` @ 265 | `simpa only [xProfile, mul_zero, Real.sqrt_zero, zero_pow (by decide : 2 ≠ 0), zero_div] using` |
| 1008 | B ℕ-order | `modulated_weighted_on_actual_scales` @ 984 | `have hz := modulated_positive_stress_zero H v (by decide : 0 < 1) hp.le` |

**`NavierStokes/ErrorHarmonics.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 507 | B ℕ-order | `accumulatedGaussianBlock_band_pow` @ 501 | `exact (hj s hs).trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_of_lt hs))` |

**`NavierStokes/FirstOrderBaseEdge.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 69 | B ℕ-order | `first_angular_balance` @ 60 | `(exterior_mono (angularHistory_exterior s (by decide : 0 < 1)) hR)` |
| 71 | B ℕ-order | `first_angular_balance` @ 60 | `(fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).2.1)` |
| 72 | B ℕ-order | `first_angular_balance` @ 60 | `(fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).2.2.1)` |
| 79 | B ℕ-order | `first_angular_balance` @ 60 | `exact thetaDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ r, heta⟩` |
| 98 | B ℕ-order | `first_axial_exterior` @ 85 | `· exact fun _ he => (conservative_moments_zero s (by decide : 0 < 1) he).1` |
| 99 | B ℕ-order | `first_axial_exterior` @ 85 | `· exact fun _ he => (conservative_moments_zero s (by decide : 0 < 1) he).2.2.2` |
| 102 | B ℕ-order | `first_axial_exterior` @ 85 | `pressureField_exterior s (by decide : 0 < 1) z hz s.B le_rfl, zero_add]` |
| 112 | B ℕ-order | `first_axial_exterior` @ 85 | `(pressureField_exterior s (by decide : 0 < 1))` |
| 117 | B ℕ-order | `first_axial_exterior` @ 85 | `rw [zDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ R, heta⟩]` |
| 126 | B ℕ-order | `first_axial_exterior` @ 85 | `exact zDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ r, heta⟩` |
| 768 | B ℕ-order | `first_axial_balance` @ 754 | `pressureField_exterior s (by decide : 0 < 1) z hz R hR, zero_add]` |
| 774 | B ℕ-order | `first_axial_balance` @ 754 | `(fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).1)` |
| 775 | B ℕ-order | `first_axial_balance` @ 754 | `(fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).2.2.2) hflux heta` |
| 782 | B ℕ-order | `first_axial_balance` @ 754 | `exact zDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ r, heta⟩` |

**`NavierStokes/GaussianEnvelope.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 70 | A `k≠0` | `integral_quadratic_bounds` @ 39 | `simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), sub_zero] using And.intro hl hu` |

**`NavierStokes/GaussianTailFlat.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 664 | H `range` mem | `native_slot_length_lower` @ 656 | `(by exact ⟨0, by decide⟩)` |

**`NavierStokes/GenericAngularRecovery.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 158 | D `Fin` DecEq | `angular_admissibility` @ 149 | `(axial_scale_horizontal_derivative Q hd 0 (by decide))` |
| 159 | D `Fin` DecEq | `angular_admissibility` @ 149 | `(axial_scale_horizontal_derivative Q hd 1 (by decide))` |

**`NavierStokes/GlobalStressSupport.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 191 | A `k≠0` | `fluxHistory_axis` @ 188 | `simp only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul]` |

**`NavierStokes/GrowingMode.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 178 | A `k≠0` | `positive_invariant_cone` @ 128 | `simpa only [hpzero, zero_pow (by decide : 2 ≠ 0), mul_zero] using hsq` |

**`NavierStokes/LeadingStressWeights.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 689 | A `k≠0` | `modulated_terminal_speed_slope` @ 680 | `simp only [ActivationContinuation.shearSize, zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0),` |

**`NavierStokes/LoopVariance.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 248 | A `k≠0` | `logSlope_hasDerivAt_zero` @ 246 | `mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, one_pow, div_one] using` |

**`NavierStokes/MeanRankUpdate.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 1420 | I enum DecEq | `reserved_five_rows` @ 1399 | `exact ReservedPatches.radial_heated_fields F XR hXR c (by decide) η` |

**`NavierStokes/MovingFrameODE.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 72 | D `Fin` DecEq | `frame_inner01` @ 71 | `exact B.inner_eq_zero (by decide)` |
| 74 | D `Fin` DecEq | `frame_inner10` @ 73 | `exact B.inner_eq_zero (by decide)` |

**`NavierStokes/NaturalCore.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 120 | A `k≠0` | `core_axis_mem` @ 117 | `zero_pow (by decide : 2 ≠ 0), zero_add, zero_div] using profile_axis_mem h Λ ht` |

**`NavierStokes/NominalProfile.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 155 | A `k≠0` | `matchingRadius_tendsto` @ 152 | `exact (tendsto_const_mul_atTop_of_pos Xi_pos).mpr ((tendsto_pow_atTop (by decide : 10 ≠ 0)).c…` |

**`NavierStokes/OffplaneCorrectionExtensions.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 795 | A `k≠0` | `physicalScalar_smooth` @ 786 | `zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_zero]` |

**`NavierStokes/OutgoingCone.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 381 | A `k≠0` | `relaxed_of_zero_shear` @ 367 | `· simpa only [normalV, normalP, normalJ, hB, zero_mul, zero_div, zero_pow (by decide : (2 : ℕ…` |

**`NavierStokes/OutgoingEntranceCone.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 1660 | A `k≠0` | `first_ramp_cone_margins` @ 1651 | `simp only [zero_mul, mul_zero, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, zero_a…` |
| 1679 | A `k≠0` | `second_ramp_cone_margins` @ 1664 | `simp only [zero_mul, mul_zero, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, zero_a…` |

**`NavierStokes/PeriodicSobolev.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 252 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h1 := averaged_line_energy_bound hf 0 1 (by decide) x (hx 1)` |
| 253 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h10 := averaged_line_energy_bound hd0 0 1 (by decide) x (hx 1)` |
| 254 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h2 := twice_averaged_line_energy_bound hf 0 1 2 (by decide) (by decide) x (hx 2)` |
| 254 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h2 := twice_averaged_line_energy_bound hf 0 1 2 (by decide) (by decide) x (hx 2)` |
| 255 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h20 := twice_averaged_line_energy_bound hd0 0 1 2 (by decide) (by decide) x (hx 2)` |
| 255 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h20 := twice_averaged_line_energy_bound hd0 0 1 2 (by decide) (by decide) x (hx 2)` |
| 256 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h21 := twice_averaged_line_energy_bound hd1 0 1 2 (by decide) (by decide) x (hx 2)` |
| 256 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h21 := twice_averaged_line_energy_bound hd1 0 1 2 (by decide) (by decide) x (hx 2)` |
| 257 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h210 := twice_averaged_line_energy_bound hd10 0 1 2 (by decide) (by decide) x (hx 2)` |
| 257 | D `Fin` DecEq | `norm_sq_le_eight_mixedEnergy_on_cube` @ 242 | `have h210 := twice_averaged_line_energy_bound hd10 0 1 2 (by decide) (by decide) x (hx 2)` |

**`NavierStokes/PeriodicUniqueness.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 610 | A `k≠0` | `energy_initial_zero` @ 606 | `simp only [Pi.sub_apply, hinitial x, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]` |

**`NavierStokes/PositiveAxisExistence.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 622 | C `Fin.val<4` | `xProfile_vector_eq` @ 595 | `· exact xProfile_square hparity 0 (by decide) heta hr` |
| 623 | C `Fin.val<4` | `xProfile_vector_eq` @ 595 | `· exact xProfile_square hparity 1 (by decide) heta hr` |
| 624 | C `Fin.val<4` | `xProfile_vector_eq` @ 595 | `· exact xProfile_square hparity 2 (by decide) heta hr` |
| 625 | C `Fin.val<4` | `xProfile_vector_eq` @ 595 | `· exact xProfile_square hparity 3 (by decide) heta hr` |
| 765 | C `Fin.val<4` | `positiveSolution_extends_order` @ 721 | `(hnew 0 (by decide)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))` |
| 769 | C `Fin.val<4` | `positiveSolution_extends_order` @ 721 | `(hnew 1 (by decide)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))` |
| 774 | C `Fin.val<4` | `positiveSolution_extends_order` @ 721 | `hphi hu ((hnew 2 (by decide)).differentiableAt (by simp))` |
| 775 | C `Fin.val<4` | `positiveSolution_extends_order` @ 721 | `((hnew 3 (by decide)).differentiableAt (by simp)) hbet).mp hsUpdated` |

**`NavierStokes/PrimaryResidualClass.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 721 | B ℕ-order | `initial_residual_band` @ 714 | `have ha : ∀ n i, HarmonicFields.BandLimited (A n i) 1 := fun n i => (hA n i).mono (by decide)` |

**`NavierStokes/PrimaryTargetBounds.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 45 | D `Fin` DecEq | `basisMatrix_det` @ 42 | `simp only [basisMatrix, Matrix.det_fin_two, ite_true, show (1 : Fin 2) ≠ 0 by decide,` |

**`NavierStokes/R3/CompactComparisonBounds.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 68 | A `k≠0` | `continuousOn_integral_norm_cube` @ 58 | `simp only [hzero, norm_zero, zero_pow (by decide : (3 : ℕ) ≠ 0)]` |
| 145 | A `k≠0` | `uniformFiniteEnergy_of_compact_slab` @ 133 | `simp only [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]` |

**`NavierStokes/R3/CompactForceBound.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 39 | A `k≠0` | `exists_uniform_l2sq_bound` @ 25 | `simp only [hzero t x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]` |
| 50 | A `k≠0` | `exists_uniform_l2sq_bound` @ 25 | `simp only [hzero t x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]` |

**`NavierStokes/R3/FourierSobolevWeights.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 107 | B ℕ-order | `fourierHNormSq_three_integrand_le_four` @ 103 | `exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg ‖ξ‖)) (by decide)` |

**`NavierStokes/ReferenceBounds.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 170 | A `k≠0` | `p1_lower_from_source` @ 141 | `simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at hsourceInt` |

**`NavierStokes/ShapeTransition.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 830 | A `k≠0` | `prefix_bound_tendsto` @ 825 | `· simp only [separation, hP, mul_zero, zero_pow (by decide : 10 ≠ 0), div_zero]` |

**`NavierStokes/SlowRecursion.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 778 | C `Fin.val<4` | `step` @ 776 | `let a := stepComponent c hS hSR C n F 0 (by decide)` |
| 779 | C `Fin.val<4` | `step` @ 776 | `let u := stepComponent c hS hSR C n F 1 (by decide)` |
| 780 | C `Fin.val<4` | `step` @ 776 | `let k := stepComponent c hS hSR C n F 2 (by decide)` |
| 781 | C `Fin.val<4` | `step` @ 776 | `let p := stepComponent c hS hSR C n F 3 (by decide)` |
| 789 | C `Fin.val<4` | `step_profile` @ 784 | `fin_cases i <;> exact stepComponent_profile c hS hSR C n F _ (by decide)` |
| 877 | C `Fin.val<4` | `step_axis_zero` @ 873 | `· exact stepComponent_axis_zero c hS hSR C n F 0 (by decide) hz` |
| 878 | C `Fin.val<4` | `step_axis_zero` @ 873 | `· exact stepComponent_axis_zero c hS hSR C n F 1 (by decide) hz` |
| 879 | C `Fin.val<4` | `step_axis_zero` @ 873 | `· exact stepComponent_axis_zero c hS hSR C n F 2 (by decide) hz` |
| 880 | C `Fin.val<4` | `step_axis_zero` @ 873 | `· exact stepComponent_axis_zero c hS hSR C n F 3 (by decide) hz` |
| 882 | C `Fin.val<4` | `step_axis_zero` @ 873 | `(fun _ hz => stepComponent_axis_zero c hS hSR C n F 1 (by decide) hz)` |
| 883 | C `Fin.val<4` | `step_axis_zero` @ 873 | `(fun _ hz => stepComponent_axis_zero c hS hSR C n F 2 (by decide) hz) hz` |

**`NavierStokes/SlowStressSupport.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 1031 | B ℕ-order | `axial_stress_support` @ 1015 | `have hprev_le : n - 1 ≤ n := (Nat.sub_lt hn (by decide : 0 < 1)).le` |

**`NavierStokes/SmoothFourierData.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 315 | B ℕ-order | `summable_integer_weight_inv_two` @ 312 | `Real.summable_one_div_nat_pow.mpr (by decide)` |

**`NavierStokes/SupportedActualContext.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 95 | A `k≠0` | `virtualStress_smoothAt` @ 80 | `zero_pow (by decide : 2 ≠ 0), zero_div] using NominalConeAssembly.activeLeft_pos W₀` |

**`NavierStokes/TerminalCompensation.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 163 | D `Fin` DecEq | `correction_square` @ 161 | `have h01 := bumps_disjoint P 0 1 (by decide) x` |
| 164 | D `Fin` DecEq | `correction_square` @ 161 | `have h02 := bumps_disjoint P 0 2 (by decide) x` |
| 165 | D `Fin` DecEq | `correction_square` @ 161 | `have h12 := bumps_disjoint P 1 2 (by decide) x` |

**`NavierStokes/TerminalHistoryBridge.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 1054 | A `k≠0` | `radiusClock_tendsto` @ 1052 | `(regularClock_tendsto hq hXR).comp ((tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).atTop_div_con…` |
| 1519 | A `k≠0` | `terminal_forward_cone` @ 1482 | `simp only [HeatSwitchCone.normalV,hB,zero_div,zero_pow (by decide : (2:ℕ)≠0),add_zero,mul_one]` |

**`NavierStokes/TorusCoverDegree.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 307 | B ℕ-order | `card_liftedRectangles_le` @ 302 | `exact Nat.pow_le_pow_right (by decide) hgap` |

**`NavierStokes/TrueConeLoop.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 81 | A `k≠0` | `correction_formula` @ 77 | `zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]` |
| 88 | A `k≠0` | `correction_zero` @ 87 | `simp only [correction, correctionRoot_zero δ v hδ hv, zero_pow (by decide : (2 : ℕ) ≠ 0)]` |
| 230 | A `k≠0` | `seedSpeed_nominal_of_inactive` @ 227 | `zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]` |

**`NavierStokes/VolterraAnalyticBounds.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 504 | B ℕ-order | `summable_half_exponential` @ 495 | `let index : ℕ → Fin 2 × ℕ := fun k => (⟨k % 2, Nat.mod_lt _ (by decide)⟩, k / 2)` |

**`NavierStokes/WeightedQuotients.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 722 | A `k≠0` | `zeroExtension_sqrt_sq` @ 715 | `· simp only [FlatZeroExtension.zeroExtension_of_nonpos _ (le_of_not_gt hδ), zero_pow (by deci…` |

**`NavierStokes/WholeDomainHeatGeometry.lean`**

| line | category | enclosing decl @ line | source |
|---:|---|---|---|
| 54 | D `Fin` DecEq | `rescale_radialEnergy` @ 48 | `show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,` |
| 54 | D `Fin` DecEq | `rescale_radialEnergy` @ 48 | `show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,` |