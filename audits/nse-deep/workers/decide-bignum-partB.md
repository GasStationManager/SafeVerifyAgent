# Part B — `decide` / bignum / kernel-Nat-arithmetic audit of `openai/NavierStokesAndEuler` @ `f9e8bc5`

Read-only source audit. No `lake build` (no Mathlib on this box, disk full). Every claim below is
source-quoted with `file:line` from the clone at `/home/gsm/.openclaw/workspace/repos/NSE`
(2659 `.lean` files). Docstrings/comments are *not* used as evidence; all margins were
re-derived independently in Python `fractions.Fraction`.

**Headline.** The repo contains **no ℕ-valued literal with ≥5 digits anywhere** (all 308 sites of
≥5-digit numerals are ℝ literals or comments/heartbeat tables). The single 696-digit numeral in the
repo, `9^729`, is an **ℝ** numeral and is **never normalised** by any tactic. The largest closed
Nat numeral the kernel can be forced to compute is ≈`2·10^18` (61 bits, still inside the
machine-word fast path, below `2^63 = 9.22·10^18`), at `NavierStokes/PulseCone.lean:1017-1018`.
No site reaches true GMP multi-limb territory. Independently, every closed numeric side condition
I could reconstruct is **true in exact rational arithmetic**, so even a hypothetical kernel Nat bug
would have nothing false to certify at these sites.

---

## 1. `NavierStokes/AxisModelBounds.lean` (60 lines, read in full)

### 1.1 The constant is the *exact* endpoint value of the cubic

`AxisProfile.cubicLower` is defined at `NavierStokes/AxisProfile.lean:84`:

```lean
def cubicLower (t : ℝ) : ℝ := 1 - t / 2 + t ^ 2 / 12 - t ^ 3 / 144
```

Exact evaluation (Python `Fraction`):

`cubicLower (41/20) = 1 - 41/40 + (41/20)^2/12 - (41/20)^3/144 = 305719/1152000` **exactly**.

So the constant in `AxisModelBounds.lean` is not a rounded bound: it *is* `f(2.05)`.
Also `cubicLower' (t) = -1/2 + t/6 - t^2/48` and `t^2 - 8t + 24` has discriminant `64-96 < 0`,
so `cubicLower` is strictly decreasing on all of ℝ; the minimum on `(-∞, 41/20]` is attained at
`t = 41/20`. Therefore `cubicLower_ge_endpoint` is **true and tight (margin exactly 0)**.

### 1.2 Line-by-line numeric steps

| # | file:line | step / source | tactic | kernel Nat work | margin (exact) | verdict |
|---|---|---|---|---|---|---|
| 1.a | `NavierStokes/AxisModelBounds.lean:29-35` | `hidentity : AxisProfile.cubicLower t = cubicLower (41/20) + (1/2 - (41/20)/6 + (41/20)^2/48) * (41/20 - t) + (1/12 - (41/20)/48) * (41/20 - t)^2 + (41/20 - t)^3/144` proved by `unfold AxisProfile.cubicLower; ring` | `ring` | `ring_nf` rational-coefficient normalisation; denominators ≤ `1152000`, pair products ≤ `1152000·19200 ≈ 2.2·10^10` (35 bits) | identity — verified true for 100 rational sample points; Taylor coefficients are exactly `4721/19200` and `13/320` | OK |
| 1.b | `NavierStokes/AxisModelBounds.lean:36` | `norm_num [AxisProfile.cubicLower] at hidentity` | `norm_num` | normalises the three rational literals `305719/1152000`, `4721/19200`, `13/320` (coprimality → `Nat.gcd` on ≤7-digit args) | n/a (rewrite) | OK |
| 1.c | `NavierStokes/AxisModelBounds.lean:26-28,37-38` | `hd : 0 ≤ 41/20 - t`, `h2 : 0 ≤ (41/20-t)^2`, `h3 : 0 ≤ (41/20-t)^3`, then `unfold AxisProfile.cubicLower; nlinarith` | `nlinarith` | Positivstellensatz certificate with coefficients `4721/19200 > 0`, `13/320 > 0`, `1/144 > 0`; kernel re-checks products of these rationals (≤ ~10^12, 40 bits) | **0** — equality at `t = 41/20` | OK |
| 1.d | `NavierStokes/AxisModelBounds.lean:40-42` | `bessel_one_lower` = `(cubicLower_ge_endpoint t ht).trans (AxisSeries.cubic_lower_le_bessel t ht0 ht)` | term-mode `.trans` | none | inherits 1.c: **0** | OK |
| 1.e | `NavierStokes/AxisModelBounds.lean:45-52` | `profile_bounds`: `ht : (χ/2)*Y ≤ 41/20 := by nlinarith` from `χ ≤ 1`, `Y ≤ 41/10` | `nlinarith` | tiny (`41/10`, `41/20`, `1/2`) | **0** — equality at `χ=1, Y=41/10` | OK |
| 1.f | `NavierStokes/AxisModelBounds.lean:55-58` | `(53/200 : ℝ) < (305719/1152000 : ℝ) ∧ …` proved by `exact ⟨by norm_num, profile_bounds 1 z …⟩` | `norm_num` | **cross-multiplication of ℕ literals: `53 * 1152000 = 61 056 000` vs `305719 * 200 = 61 143 800`** (8 digits, 27 bits) | `305719/1152000 - 53/200 = 439/1152000 = 3.8107638…·10^-4` | OK |
| 1.g | `NavierStokes/AxisModelBounds.lean:18-21` | `model_eq_series` — `simpa only [...] using AxisSeries.profile_eq_tsum 1 z` | `simpa only` | none | n/a | OK |

### 1.3 Load-bearing or slack?

**`305719/1152000` is a *reporting* constant, not load-bearing.** Grep over all 2659 files shows the
only consumer of `AxisModelBounds.profile_bounds` is `AxisModelBounds.lean:58` itself, and
`AxisModelBounds` is imported by exactly one file, which is a pure import aggregator
(`NavierStokes/PaperAdditionalResults.lean:4`). The bound that is actually used downstream is the
much slacker `1/4`:

- `NavierStokes/AxisProfile.lean:92-93` — `theorem cubicLower_gt_quarter (t : ℝ) (ht : t ≤ 41 / 20) : 1 / 4 < cubicLower t`
- `NavierStokes/AxisSeries.lean:295-298` — `bessel_one_gt_quarter := lt_of_lt_of_le (AxisProfile.cubicLower_gt_quarter t ht) (cubic_lower_le_bessel t ht0 ht)`, consumed at `AxisSeries.lean:304` and `AxisSeries.lean:375`.

Margin of the load-bearing `1/4` version: `305719/1152000 - 1/4 = 17719/1152000 = 1.538·10^-2` —
**~40× slacker** than the `53/200` claim, and ~4·10^4× the size of any plausible arithmetic slip
in an 8-digit multiplication. Consequence: the tight-looking numeral sits on a *dead-end display
theorem*; the live path is slack.

Related numerics in the same cluster (for completeness):

| file:line | statement | tactic | exact value / margin | verdict |
|---|---|---|---|---|
| `NavierStokes/AxisProfile.lean:110-121` | `quarticUpper t < -(18/100)` for `99/50 ≤ t ≤ 2` | `pow_le_pow_left₀` + `norm_num at hsquare hcube hfour` + `nlinarith` | `quarticUpper` is decreasing there; max at `t=99/50` is `-75535511/400000000`; margin `= 8.8387775·10^-3`. Closed numerals: `99^3 = 970299`, `(1/100)^2 = 1/10000`, `2^4 = 16`; certificate denominators ≤ `4·10^8` | OK |
| `NavierStokes/AxisSeries.lean:283-287` | `hpoly` via `norm_num [Finset.sum_range_succ, term, AxisProfile.cubicLower, Nat.factorial_succ]; ring` | `norm_num`+`ring` | only `0!..4! = 1,1,2,6,24` and `(n+1)!` up to `120`; denominators ≤ `144` | OK |
| `NavierStokes/AxisProfile.lean:125-130` | `first_four_terms_eq_cubic` — `norm_num [profileCoeff, cubicLower, Nat.factorial_succ]; ring` | `norm_num`+`ring` | same tiny factorials | OK |

---

## 2. `Euler/ConstantCorrectionData.lean` — the `9^729`

Only one numeral in the whole repo carries a ≥3-digit exponent
(`grep -E '\^\s*[0-9]{3,}'` over all 2659 files):

```lean
-- Euler/ConstantCorrectionData.lean:146
def pressureBound : ℝ := 9^729
```

**The base is an ℝ numeral, not a Nat/Int literal.** `(9 : ℝ) ^ (729 : ℕ)` is `Monoid.npow` on the
noncomputable `Real`; there is no kernel reduction path to a numeral at all, and no tactic in the
repo asks for one. Its only proof:

```lean
-- Euler/ConstantCorrectionData.lean:148-149
theorem pressureBound_one_le : 1 ≤ pressureBound :=
  one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)
```

`one_le_pow₀` consumes the exponent symbolically; the only kernel arithmetic is `1 ≤ 9`.
Its consumer:

```lean
-- Euler/ConstantCorrectionData.lean:160-167
theorem identity_pressure (q : ℕ) (hq : 6 ≤ q) :
    (… .restrict … 5 (by omega)).pressureConstant 1 ≤ pressureBound ∧
    (… .restrict … 6 hq).pressureConstant 1 ≤ pressureBound := by
  simpa only [mul_one,pressureBound] using fixed_pressure_constants P hq … (by norm_num) …
```

The upstream source is `(9*L)^729` with `L : ℝ` a *variable*:

```lean
-- Euler/GevreyUniformConstants.lean:70-74
    (hcoeff : ∀ r ≤ q, boundLevel period K r ≤ L) : K.pressureConstant c ≤ (9*L)^729 := by
  have h := pressureConstant_polynomial K c L hc hL hcL hcoeff
  have he : 3^q ≤ 729 := by
    exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hq).trans (by norm_num)
  exact h.trans (pow_le_pow_right₀ (by linarith : 1 ≤ 9*L) he)
```

`GevreyUniformConstants.lean:72-73` is the *only* closed Nat power in the repo:
`by norm_num : 3^6 ≤ 729`, i.e. the kernel computes `Nat.pow 3 6 = 729` and `Nat.ble 729 729`.
Three digits. All other `^` occurrences with literal exponents have variable bases
(e.g. `Θ^40`, `(4*R*550^2)^110` at `Euler/PacketTailBase.lean:57,65,67` where `R,N : ℝ`).

| file:line | numeral | base kind | evaluated by kernel? | verdict |
|---|---|---|---|---|
| `Euler/ConstantCorrectionData.lean:146` | `9^729` (696 digits if expanded) | **ℝ literal base**, ℕ exponent | **no** — `Real` has no kernel numeral reduction, and no tactic normalises it (`pressureBound_one_le` uses `one_le_pow₀`) | OK |
| `Euler/GevreyUniformConstants.lean:70,82,83` | `(9*L)^729` | ℝ **variable** `L` | no | OK |
| `Euler/GevreyUniformConstants.lean:72-73` | `3^q ≤ 3^6 ≤ 729` | **ℕ literal** | **yes**: `Nat.pow 3 6`, `Nat.ble 729 729` | OK (3-digit) |
| `Euler/PacketTailBase.lean:57,65,67` | `(4*R*550^2)^110` | ℝ variables + `550^2` | `550^2 = 302500` only (6-digit) | OK |
| `NavierStokes/PulseAmplitude.lean:107-114` | `(1024 : ℝ) = 2 ^ 10 := by norm_num` | ℝ base, ℕ exponent | `norm_num` evaluates `2^10 = 1024` (4-digit) | OK |

Note the *hypothetical*: had anybody written `norm_num [pressureBound]` or `decide` against
`9^729`, the kernel would have had to build a 2313-bit integer — a genuine multi-limb GMP
exercise. **Nobody does.** `grep -rn 'pressureBound'` shows only `≤`/`0 ≤`/`1 ≤`-style symbolic
uses (`Euler/SmallCorrectionBudget.lean:26,34`, `Euler/StaticEulerWeightedBounds.lean:42,44,53,59`,
`Euler/SmallCorrectionScales.lean:16,19,20`) — plus an *unrelated* real-valued
`NavierStokes/OutgoingEntranceCone.lean:872 pressureBound := 10 * FuturePressureBounds.envelopeConstant`.

---

## 3. Repo-wide search for forced closed Nat computation

Grep results over all 2659 `.lean` files:

| pattern | hits | assessment |
|---|---|---|
| `10 ^ [0-9]+` | **0** | — |
| `2 ^ [0-9]{2,}` | 1 | `NavierStokes/PulseAmplitude.lean:110` — `(1024 : ℝ) = 2 ^ 10 := by norm_num` (4-digit) |
| `Nat.gcd` | **0** explicit | only implicit, inside `norm_num`'s `Rat` coprimality certificates |
| `Nat.div` / `Nat.mod` | **0** explicit | — |
| `%` | 7, of which 5 real code | `NavierStokes/SlotColoring.lean:144` (`z % 5`), `:161,:170` (`L.1 % 9`), `NavierStokes/VolterraAnalyticBounds.lean:504,507` (`k % 2`) — all on **variables**, moduli 2/5/9 |
| `Nat.pow` | 10 | all `Nat.pow_le_pow_{left,right}` **lemma** applications with variable exponents/bases; only `Euler/GevreyUniformConstants.lean:73` closes on `3^6` |
| `factorial` | 1186 lines | all symbolic (`Nat.factorial_succ`, `Nat.factorial_le_pow`, `(n.factorial : ℝ)`); no closed factorial of a ≥2-digit literal (`grep 'factorial\s+\(?[0-9]{2,}'` → **0**). Largest closed factorial evaluated: `4! = 24`, `5! = 120` in the `Finset.range 4` sums at `NavierStokes/AxisSeries.lean:286` and `NavierStokes/AxisProfile.lean:129` |
| `decide` | 205 lines; only 6 share a line with a ≥3-digit numeral | all are ℕ order facts on tiny/round literals: `Euler/ParentHistoryFrequencyGuard.lean:81` `(by decide : 1 ≤ 1000)`; `Euler/PacketSourceParameterScales.lean:121,126` (`1 ≤ 1000`, exponent `1000`); `Euler/PacketGeometryGuards.lean:84,94` `(by decide : 29 ≤ 40)`; `NavierStokes/PeriodicSobolev.lean:257`, `Euler/EulerProof.lean:17952`, `NavierStokes/TorusCoverDegree.lean:307`, `NavierStokes/ErrorHarmonics.lean:507` `(by decide : 1 ≤ 2)`. **No `decide` on a ≥4-digit literal (in)equality.** |
| `native_decide` | **0** | good: no compiler-trust escape hatch anywhere |
| `(rfl : … = …)` | 1 | `NavierStokes/PhaseEstimates.lean:903` — `(rfl : shearVector F0 G0 q0 = _)`, no numerals |
| `by rfl` | 23 | all defeq/`le_refl`, no numeral arithmetic except `NavierStokes/CorrectedPressureBounds.lean:624` `show (28 : ℕ) = 27 + 1 by rfl` (2-digit) and `NavierStokes/LoopVariance.lean:270` `show (2 : ℕ) = 1 + 1 by rfl`. Note `NavierStokes/ActualParticularMeanGain.lean:153` `(show ChartScales.kappa ≤ 1/100000 by rfl)` — `ChartScales.kappa` is literally `1/100000` (`NavierStokes/ChartScales.lean:24`), so this is `le_refl` on ℝ: **zero-margin but zero arithmetic** |
| `norm_num` whose two sides are closed ≥5-digit numerals | 8 | `NavierStokes/PulseCone.lean:1016`; `Euler/PacketGeometryGuards.lean:54,76,83,93`; `Euler/PacketPhysicalFamily.lean:118`; `Euler/PacketGeometryAssembly.lean:70` (all `0 ≤ 10^9` / `1 ≤ 10^9`, trivial); plus `NavierStokes/AxisModelBounds.lean:56` |

### 3.1 The largest closed Nat computation in the repo

**`NavierStokes/PulseCone.lean:1015-1018`** — approximately `2·10^18` (61 bits):

```lean
-- NavierStokes/PulseCone.lean:1012-1018
theorem derivativeCoefficient_le (d : TailData)
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000) (eta : ℝ) :
    derivativeCoefficient d eta ≤ 2001 / 1000 := by
  have hb : (49999 / 100000 : ℝ) ≤ decay d.core := by dsimp [decay]; linarith
  have hb₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 49999 / 100000) hb 2
  have hbase : (1 / 2 : ℝ) ≤ (2001 / 1000) * decay d.core ^ 2 * (99999 / 100000) := by
    nlinarith
```

(`decay c = 1/2 - c.lam` at `NavierStokes/PulseLag.lean:165`.) The `nlinarith` at line 1018 has
exactly one route: scale `hb₂` by `(2001/1000)·(99999/100000) = 200097999/10^8`, which forces the
kernel through
`49999^2 = 2 499 900 001`, then `200097999 * 2499900001 = 500 224 987 900 197 999` (18 digits,
59 bits), then a common denominator `2·10^18` (61 bits) against `1/2`, plus `Nat.gcd` normalisation
on those operands. Exact residual (Python):

`(2001/1000)·(49999/100000)^2·(99999/100000) - 1/2 = 224987900197999/10^18 = 2.24987900198·10^-4 > 0`.

`2·10^18 < 2^63 = 9.223·10^18`, so even this stays inside Lean's tagged-scalar fast path — **the
repo never reaches multi-limb GMP arithmetic**. Runners-up: `≈4·10^8`–`1.25·10^9` in the
`AxisProfile.lean:110-121` quartic certificate; `≈2.2·10^10` in the `AxisModelBounds.lean:36-38`
cubic certificate; `≈8.8·10^11` (`883420 * 10^6`) in `Euler/EulerProof.lean:17954,17979`
(`dJ ≤ 17490 * M`, `dS ≤ 883420 * M`, `nlinarith`).

---

## 4. Are there any ℕ-valued big literals at all? — **No**

Method: (a) re-scanned all 2659 files for `(?<![\w.])\d{5,}(?!\w)` → **308 occurrences**, only
**46 distinct values**; (b) cross-checked
`audits/nse-deep/BIGNUM_SITES.md` (121 sites, ≥7 digits) against the source.

**Data-quality note on the starting list (`UNCLEAR` for the list, not the repo).** All 121 quoted
strings exist verbatim in the clone, but **109 of 121 line numbers are stale**: they are shifted by
a small per-file constant (+1…+12 for the `Packet*`/`Parent*`/`Axis*` files) and by **+207** for
`Euler/EulerProof.lean` (e.g. the list's `EulerProof.lean:18272 def stabilityConstant : ℝ := 320000000 * exp 6`
is really at `Euler/EulerProof.lean:18479`). Corrected line numbers are used below.

Verified sample — 51 sites (>25 required), ≥1 per file, all re-read from source:

| corrected file:line | list said | source (verbatim) | type of the big literal | verdict |
|---|---|---|---|---|
| `Euler/EulerProof.lean:16892` | 16708 | `(hlam : 0 ≤ lam) (hsmall : 8000000 * e * Θ ^ 21 ≤ 1)` | ℝ (`e Θ : ℝ`) | OK |
| `Euler/EulerProof.lean:16925` | 16741 | `|V t - Z t| + |U t + Z₁ t| ≤ 160000000 * e * Θ ^ 29 * (1 + lam) * F t := by` | ℝ | OK |
| `Euler/EulerProof.lean:18479` | 18272 | `noncomputable def stabilityConstant : ℝ := 320000000 * exp 6` | ℝ (explicit `: ℝ`) | OK |
| `Euler/EulerProof.lean:18481` | 18274 | `theorem stabilityConstant_ge : 320000000 ≤ stabilityConstant := by` (proof: `linarith only [1 ≤ exp 6]`) | ℝ | OK |
| `Euler/PacketActualFrameEstimates.lean:36` | 32 | `(htΘ : y⁻¹/σ ≤ Θ) (hsmall : 1000000*K*e*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketActualFrameEstimates.lean:49` | 45 | `y^4+σ^2*y^2+8*σ*y^3+30000000*K*e*Θ^40 ∧` | ℝ | OK |
| `Euler/PacketBeforeTargetSize.lean:23` | 19 | `(hsmall : 1000000*K*e*Θ^40 ≤ 1) (hτ : 1 ≤ τ) (hτΘ : τ ≤ Θ)` | ℝ | OK |
| `Euler/PacketBeforeTargetSize.lean:64` | 58 | `(hsmall : 1000000*K*e*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketCommonScaleChoice.lean:41` | 39 | `let δ : ℝ := min η (min (1/2) (1/(1000000*K)))` | ℝ (explicit `: ℝ`) | OK |
| `Euler/PacketCommonScaleChoice.lean:45` | 43 | `have hδK : 1000000*K*δ ≤ 1 := by` | ℝ | OK |
| `Euler/PacketControlledPropagator.lean:21` | 20 | `(hsmall : 8000000*e*Θ^21 ≤ 1)` | ℝ | OK |
| `Euler/PacketForwardGeometryData.lean:40` | 38 | `small : 1000000*neighborStabilityConstant*` | ℝ (structure field) | OK |
| `Euler/PacketGeometryAssembly.lean:35` | 31 | `… ≤ 400000000*D.error*D.Θ^29*(1+D.lam)*F τ` | ℝ | OK |
| `Euler/PacketGeometryAssembly.lean:47` | 43 | `|D.nextCoupling/D.a-1| ≤ D.y^4+D.σ^2*D.y^2+8*D.σ*D.y^3+30000000*neighborStabilityConstant*D.error*D.Θ^40 ∧` | ℝ | OK |
| `Euler/PacketGeometryData.lean:57` | 54 | `small : 1000000*neighborStabilityConstant*(16*(ε*Θ*(4*G)^2+d))*Θ^40 ≤ 1` | ℝ | OK |
| `Euler/PacketGeometryGuards.lean:54` | 54 | `((by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge) D.error_nonneg` | ℝ (**ascribed** `(1:ℝ)`) | OK |
| `Euler/PacketGeometryGuards.lean:57` | 57 | `change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs` | ℝ | OK |
| `Euler/PacketHorizonSize.lean:92` | 88 | `(hsmall : 1000000*K*e*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketInductionScales.lean:94` | 92 | `delta_geometry : 1000000*geometryConstant*δ ≤ 1` | ℝ | OK |
| `Euler/PacketInductionScales.lean:129` | 127 | `(min (1/(1000000*geometryConstant)) (1/(8*(1+errorConstant frameConstant)))))` | ℝ | OK |
| `Euler/PacketNeighborControlled.lean:82` | 77 | `(hlam : 0 ≤ lam) (hsmall : 8000000*e*Θ^21 ≤ 1)` | ℝ | OK |
| `Euler/PacketNeighborControlled.lean:115` | 110 | `|V t-Z t|+|U t+Z₁ t| ≤ 400000000*e*Θ^29*(1+lam)*F t := by` | ℝ | OK |
| `Euler/PacketNeighborControlled.lean:139` | 134 | `have hcoef : 20*e*Θ^8+800*(200000*e)*Θ^29*(1+lam+e) ≤ 400000000*e*Θ^29*(1+lam) := by` | ℝ | OK (see §5) |
| `Euler/PacketNeighborControlled.lean:154` | 149 | `def neighborStabilityConstant : ℝ := 1000000000*exp 6` | ℝ | OK |
| `Euler/PacketPhysicalCompression.lean:76` | 76 | `(hsmall : 1000000*K*e*Θ^40 ≤ 1) (hscale : 1 ≤ β*τ^2)` | ℝ | OK |
| `Euler/PacketPhysicalFamily.lean:26` | 22 | `(hsmall : 1000000*neighborStabilityConstant*(16*(ε*Θ*(4*G)^2+d))*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketPhysicalFamily.lean:66` | 62 | `|scaledVelocity … 0+Z₁ τ| ≤ 400000000*e*Θ^29*(1+lam)*F τ) ∧` | ℝ | OK |
| `Euler/PacketPhysicalFamily.lean:118` | — | `have hK : 1 ≤ neighborStabilityConstant := (by norm_num : (1:ℝ) ≤ 1000000000).trans …` | ℝ | OK |
| `Euler/PacketPhysicalNeighbor.lean:25` | 20 | `(hsmall : 1000000*neighborStabilityConstant*(16*(ε*Θ*(4*G)^2+d))*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketPhysicalNeighbor.lean:64` | 59 | `(∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤ 400000000*e*Θ^29*(1+lam)*F t) ∧` | ℝ | OK |
| `Euler/PacketPhysicalPropagator.lean:25` | 21 | `(hsmall : 8000000*(16*(ε*Θ*(4*G)^2+d))*Θ^21 ≤ 1)` | ℝ | OK |
| `Euler/PacketPhysicalPropagator.lean:66` | 62 | `change 8000000*e*Θ^21 ≤ 1 at hsmall` | ℝ | OK |
| `Euler/PacketPhysicalSign.lean:20` | 16 | `… (hsmall : 1000000*K*e*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketPhysicalSign.lean:106` | 102 | `… (hsmall : 1000000*K*e*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketPhysicalStage.lean:26` | 21 | `(hsmall : 1000000*stabilityConstant*(16*(ε*Θ*(4*G)^2+d))*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketPhysicalStage.lean:59` | 54 | `(∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤ 160000000*e*Θ^29*(1+lam)*F t) ∧` | ℝ | OK |
| `Euler/PacketSizeComparison.lean:52` | 50 | `(hsmall : 1000000*K*e*Θ^40 ≤ 1)` | ℝ | OK |
| `Euler/PacketSizeComparison.lean:69` | 67 | `have hA : 1000000*A ≤ 1 := by simpa only [A, mul_assoc] using hsmall` | ℝ | OK |
| `Euler/PacketSourceFrequency.lean:13` | 12 | `def theta : ℝ := 1/1000000` | ℝ (explicit `: ℝ`) | OK |
| `Euler/PacketSourceGeometryData.lean:106` | 101 | `small : 1000000*neighborStabilityConstant*` | ℝ | OK |
| `Euler/PacketSourceScaleGuards.lean:130` | 129 | `geometry_small : 1000000*K*geometryError J D C c X a n*sourceTheta J C (scaleSequence J X) n^40 ≤ 1` | ℝ | OK |
| `Euler/PacketSourceScaleGuards.lean:136` | 135 | `(hδK : 1000000*K*δ ≤ 1) (hb : ActualBounds J D C c X δ)` | ℝ | OK |
| `Euler/PacketWithinStage.lean:25` | 19 | `(hlam : 0 ≤ lam) (hsmall : 1000000 * stabilityConstant * e * Θ ^ 40 ≤ 1)` | ℝ | OK |
| `Euler/PacketWithinStage.lean:54` | 48 | `160000000 * e * Θ ^ 29 * (1 + lam) * F t) ∧` | ℝ | OK |
| `Euler/ParentForwardGeometryGuards.lean:93` | 91 | `have hN1 : 1 ≤ 1000000*neighborStabilityConstant := by` | ℝ | OK |
| `Euler/ParentForwardGeometryGuards.lean:95` | 93 | `have hN : 0 ≤ 1000000*neighborStabilityConstant := zero_le_one.trans hN1` | ℝ | OK |
| `Euler/ParentPacketGeometryGuards.lean:198` | 193 | `have hN1 : 1 ≤ 1000000*neighborStabilityConstant := by` | ℝ | OK |
| `Euler/ParentPacketGeometryGuards.lean:202` | 197 | `have hN : 0 ≤ 1000000*neighborStabilityConstant := zero_le_one.trans hN1` | ℝ | OK |
| `Euler/ParentRenewalParameters.lean:19` | 16 | `30000000*neighborStabilityConstant*G.error*G.Θ^40` | ℝ | OK |
| `Euler/ParentRenewalParameters.lean:21` | 18 | `def tiltError : ℝ := 1500*G.σ+30000000*neighborStabilityConstant*G.error*G.Θ^40` | ℝ | OK |
| `Euler/ParentRenewalPrefix.lean:119` | 114 | `(hδK : 1000000*K*δ ≤ 1) (hb : ActualBounds J D C c X δ)` | ℝ | OK |
| `Euler/ParentRenewalScaleCosts.lean:20` | 18 | `def errorConstant (CF : ℝ) : ℝ := 30000000*neighborStabilityConstant*CF^2` | ℝ | OK |
| `Euler/ParentRenewalScaleCosts.lean:174` | 171 | `have hK : 0 ≤ 30000000*neighborStabilityConstant := by positivity [neighborStabilityConstant_ge]` | ℝ | OK |
| `NavierStokes/AxisModelBounds.lean:25` | 19 | `(305719 / 1152000 : ℝ) ≤ AxisProfile.cubicLower t := by` | ℝ (**ascribed**) | OK |
| `NavierStokes/AxisModelBounds.lean:41` | 35 | `(305719 / 1152000 : ℝ) ≤ AxisSeries.bessel 1 t :=` | ℝ (ascribed) | OK |
| `NavierStokes/ExponentLedger.lean:276` | 264 | `theorem smaller_kappa_admissible {κ : ℝ} (hκ : κ < 1 / 1000000) :` | ℝ | OK |

**Result: 51/51 sampled sites are ℝ literals. 0 ℕ literals.** The only 8 distinct ≥7-digit values
in the repo are `1000000` (65×), `30000000` (17×), `400000000` (10×), `8000000` (8×), `1000000000`
(8×), `160000000` (6×), `1152000` (5×), `320000000` (2×) — every one of them multiplying a real
variable (`e`, `Θ`, `K`, `D.error`, `σ`, `exp 6`) or ascribed `: ℝ`.

Cross-check on ℕ context: of the 308 ≥5-digit sites, the 9 lines that mention `ℕ` at all
(`NavierStokes/ExponentLedger.lean:304`, `NavierStokes/ActualIterationLedger.lean:119,183,188,193,198`,
`NavierStokes/ActualPhysicalStageBounds.lean:353,365,373`) all have the shape
`(n : ℕ) {κ : ℝ} (hκ : κ ≤ 1 / 100000)` — the ℕ is a *separate* variable; the literal is ℝ.
41 further ≥5-digit sites are comments/heartbeat tables (e.g.
`Euler/BaseFirstPacketChoiceNoOptions.lean:33-34`, `Euler/ParentGeometryJoinedChoiceInvestigation.lean:29-32`)
and carry no proof weight at all.

Largest ℕ literal anywhere in real code: **`1000` (4 digits)** at
`Euler/ParentHistoryFrequencyGuard.lean:81` / `Euler/PacketSourceParameterScales.lean:121,126`, and
**`729`** at `Euler/GevreyUniformConstants.lean:72-73`.

---

## 5. Verdict — danger ranking

Threat model reminder: a kernel Nat-arithmetic bug is only harmful if the tactic asks the kernel to
certify something **false**. I re-derived every closed numeric side condition below in exact
`Fraction` arithmetic; all are **true**, and none needs >61-bit integers.

| rank | site | tightest thing the kernel must certify | exact margin | if kernel Nat arithmetic were wrong… | verdict |
|---|---|---|---|---|---|
| 1 | `NavierStokes/PulseCone.lean:1017-1018` (`nlinarith` for `(1/2 : ℝ) ≤ (2001/1000)*decay^2*(99999/100000)`) | `200097999 * 2499900001 = 500224987900197999`, common denominator `2·10^18` (**largest closed Nat in the repo, 61 bits**) | `224987900197999/10^18 ≈ 2.2499·10^-4` (relative `4.5·10^-4`) | A **false statement could become provable** only if the error exceeded 2.2·10^-4 in relative terms `≈ 4.5·10^-4`, i.e. corrupted the *4th most significant* digit of an 18-digit product. Independently recomputed: the product and the inequality are **correct**. Downstream this feeds `derivativeCoefficient_le … ≤ 2001/1000`, a real load-bearing coefficient bound, so it is *not* mere slack — but the value is verified. | OK |
| 2 | `NavierStokes/AxisModelBounds.lean:56` (`norm_num` for `(53/200 : ℝ) < (305719/1152000 : ℝ)`) | `53 * 1152000 = 61056000` vs `305719 * 200 = 61143800` (8 digits, 27 bits) | `439/1152000 ≈ 3.8108·10^-4` (relative `1.4·10^-3`) | A wrong 8-digit `Nat.mul`/`Nat.ble` **would** make a false decimal claim (`0.265 < f₀`) provable. Both products recomputed independently: correct. Impact contained: this theorem (`model_bounds`) has **no consumers** — grep shows nothing imports it except the aggregator `NavierStokes/PaperAdditionalResults.lean:4`. | OK |
| 3 | `NavierStokes/AxisModelBounds.lean:25-38` + `:41` + `:47` (`ring`/`norm_num`/`nlinarith`, constant `305719/1152000`) | rational certificate with denominators up to `1152000`; pair products `≤ 2.2·10^10` (35 bits) | **exactly 0** — `cubicLower (41/20) = 305719/1152000` *identically*, and `cubicLower` is strictly decreasing (`t^2-8t+24` has negative discriminant), so equality is attained at the endpoint | Zero-margin, hence maximally sensitive *in principle*; but the statement is an exact rational identity that I reproduced bit-for-bit, and the constant is **slack/reporting, not load-bearing** — the live downstream bound is `1/4 < bessel 1 t` (`NavierStokes/AxisSeries.lean:295-298`, used at `:304,:375`) with margin `17719/1152000 ≈ 1.54·10^-2`, ~40× slacker. | OK |
| 4 | `NavierStokes/ExponentLedger.lean:227-231` (`linarith` for `69999/100000 ≤ waveExponent σ - κ`, `waveExponent σ = 1/2 + σ`, `σ ≥ 1/5`, `κ ≤ 1/100000`) | 5–6-digit rational addition (`1/2+1/5-1/100000 = 69999/100000`) | **exactly 0** (equality at `σ=1/5, κ=1/100000`) | Zero-margin and this *is* on a live ledger path, but the numbers are 5-digit; `linarith`'s certificate is exact rational addition, verified. Same story for `NavierStokes/PulseCone.lean:1015` (`49999/100000 ≤ decay`, margin 0) and `:1021` (`(99999/100000)*lam + … ≤ equilibriumNumerator`, margin 0 given `h ≤ lam/100000`), and `NavierStokes/ActualParticularMeanGain.lean:153` (`ChartScales.kappa ≤ 1/100000 by rfl` = `le_refl`, no arithmetic). | OK |
| 5 | `Euler/OrdinaryGradientEnergy.lean:60-66` (`norm_num [gradientEnergyConstant, sum_range_succ]` for `54*(∑ n ∈ range 4, (6:ℝ)^n) = 13986`) | `1+6+36+216 = 259`, `54*259 = 13986` (5 digits, 14 bits) | This is an **equality**, so margin 0 by construction: a wrong `Nat.mul` would prove a false equation. Recomputed: `54*259 = 13986` ✓. Consumers use the symbolic `gradientEnergyConstant`, so a slip would shift a constant, not break a structure. | OK |
| 6 | `Euler/GevreyUniformConstants.lean:72-73` (`by norm_num : 3^6 ≤ 729`) — **the only closed `Nat.pow` in the repo** | `Nat.pow 3 6 = 729`, `Nat.ble 729 729` | 0 (equality) | Zero-margin ℕ fact; 3 digits; `3^6 = 729` ✓. If wrong, `(9*L)^729` in `pressureConstant_le_six` would be an unjustified exponent bump — but 3-digit `Nat.pow` is the most exercised code path in the kernel. | OK |
| 7 | `Euler/ConstantCorrectionData.lean:146-149` (`pressureBound : ℝ := 9^729`) | **nothing** — the 696-digit numeral is never built | n/a | The one place where a GMP bignum bug *could* bite (2313-bit `Nat.pow`) is **never triggered**: `one_le_pow₀` consumes the exponent symbolically and no `norm_num`/`decide`/`rfl` ever unfolds `pressureBound`. Worth re-checking if the file ever changes. | OK |
| 8 | `NavierStokes/AxisProfile.lean:110-121` (`quarticUpper t < -(18/100)`) | `99^3 = 970299`, certificate denominators ≤ `4·10^8` (30 bits) | `8.8388·10^-3` at the worst point `t = 99/50` (exact value `-75535511/400000000`) | Comfortable margin (>20× any 9-digit rounding scenario); only a slack cone constant would move. | OK |
| 9 | `Euler/PacketNeighborControlled.lean:139-145` (`hcoef`, `nlinarith only [...]`) | `800 * 200000 = 160000000` vs the stated `400000000` (9 digits, 28 bits) | factor **2.5** of headroom (`1.6·10^8` used out of `4·10^8`) | Pure slack: even a grossly wrong 9-digit multiply is absorbed by the 2.5× factor. Same for `Euler/PacketGeometryGuards.lean:82-99` (`nlinarith only` with `10^6·10^9` vs `1/2` / `1`) and `Euler/EulerProof.lean:17954,17979` (`17490 * M`, `883420 * M`). | OK |
| 10 | `NavierStokes/SlotColoring.lean:144,161,170`, `NavierStokes/VolterraAnalyticBounds.lean:504,507` (`%` on ℕ/ℤ) | moduli **2, 5, 9** on *variables* | n/a | No closed `Nat.mod`/`Nat.div` computation anywhere; `Nat.mod_lt _ (by norm_num)` / `(by decide)` on `0 < 2`, `0 < 9`. | OK |

### Bottom line

- **No `KERNEL-RISK` or `SUSPICIOUS` site found.** No `native_decide`. No `decide` on ≥4-digit
  literals. No closed `Nat.gcd`/`Nat.div`/`Nat.mod`/`Nat.factorial` of a large literal. No ℕ literal
  above 4 digits in real code.
- Peak closed Nat magnitude ≈ `2·10^18` (61 bits) — inside the small-scalar fast path, three orders
  of magnitude short of where multi-limb GMP behaviour would even begin, and ~700 orders short of
  the repo's one big *symbolic* numeral `9^729`.
- The two zero-margin numeric families (`305719/1152000 = cubicLower(41/20)`;
  `1/2+1/5-1/100000 = 69999/100000` and the `49999/100000` / `99999/100000` ledger constants) are
  exact rational identities that I reproduced independently, so the kernel had nothing false to
  accept. The tightest *strict* inequality is
  `(53/200 : ℝ) < (305719/1152000 : ℝ)` with margin `439/1152000 ≈ 3.81·10^-4`
  (`NavierStokes/AxisModelBounds.lean:56`), and it sits on a theorem with no consumers.
- One `UNCLEAR` outside the repo: `audits/nse-deep/BIGNUM_SITES.md` line numbers are stale
  (109/121 shifted; `+207` for `Euler/EulerProof.lean`). Corrected numbers are in §4.
- Residual uncertainty: `nlinarith`/`ring_nf` certificate *internals* cannot be observed without a
  build. The magnitudes in §3.1 and §5 are the *forced* ones (they follow from the hypotheses'
  literals and the unique scaling that closes the goal), not observed kernel traces. A future
  `lake build` with `set_option trace.profiler true` / `#print axioms` pass would upgrade these
  from derived to observed.
