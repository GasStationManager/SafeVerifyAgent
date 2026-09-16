# `bigpow-refute` — worker report (thread `cert-numerals`, NSE @ f9e8bc5)

Scope: hunt for anything that forces the Lean 4 kernel to evaluate a numeral WIDER than 64 bits,
OUTSIDE the linarith/nlinarith-certificate route. READ-ONLY on `/home/gsm/.openclaw/workspace/repos/NSE`.

STATUS OF EVERY CLAIM BELOW: **UNBUILT / SOURCE-LEVEL**. There is no Mathlib and no `lake build` in the
NSE clone, so nothing here was machine-checked by Lean. Tactic semantics were read from local Mathlib
source copies (`/home/gsm/src/SafeVerify/.lake/packages/mathlib`, toolchain `v4.27.0`;
`/tmp/junk_packages_w4/mathlib`, `v4.29.0`) and from Lean core `v4.34.0`
(`~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/...`). NSE pins
`leanprover/lean4:v4.34.0-rc2` + mathlib4 `v4.34.0-rc2` (`lean-toolchain`, `lakefile.toml:7-11`), i.e. the
tactic sources I read are 1-2 minor versions older than the pin. The code paths quoted are unchanged
between the two Mathlib copies I have.

## Mechanism used (as required by the brief)

* `linarith` parses hypotheses/negated goal into linear forms over atoms with rational coefficients
  (`Mathlib/Tactic/Linarith/Parsing.lean`), `cancelDenoms`-preprocesses each comparison (x lcm of its
  numeral denominators), runs a simplex oracle for nonneg rational multipliers, then emits a scaled sum
  of the used hypotheses and closes the final closed comparison with `norm_num`
  (`Linarith/Verification.lean`). Widest kernel numeral ~ (lcm of denominators) x (max numerator).
* `nlinarith` first adds pairwise products/squares of hypotheses, which squares denominators and
  numerators, so a product term that survives in the certificate roughly DOUBLES the bit width.
* `norm_num` proves closed rational (in)equalities by reducing to `Nat`/`Int` literal arithmetic; the
  kernel evaluates those with GMP. <= 2^64 = 1.8446744e19 is one machine word; above that is multi-limb
  GMP (a much less exercised kernel path).
* NEW, and decisive for this task — two facts I verified in source, both of which the audit headline does
  not use:
  1. **`ring` exponentiates numeral coefficients.** `Mathlib/Tactic/Ring/Basic.lean:922-939`
     (v4.27 copy; identical at `Ring/Common.lean:915-938` in the v4.29 copy) — `evalPowProd`, branch
     `| .const za ha, .const zb hb => ... NormNum.evalPow.core ...`. So the ring normal form of
     `(c * x)^n` for a numeral `c` contains the LITERAL `c^n`, produced by
     `Mathlib/Tactic/NormNum/Pow.lean:66-108` `evalNatPow`, a balanced binary-exponentiation proof whose
     leaves are `IsNatPowT.bit0/bit1` i.e. `Nat.mul c c` / `Nat.mul c (Nat.mul c a)` defeq checks against
     raw literals. Those multiplications are exactly what the kernel must redo.
  2. **Exponents > 256 are refused.** `evalNatPow` is guarded by
     `guard <| ← Lean.checkExponent b.natLit!` (`NormNum/Pow.lean:82`), and
     `Lean/Util/SafeExponentiation.lean:15-33` (Lean core v4.34.0) sets
     `register_builtin_option exponentiation.threshold : Nat := { defValue := 256 }` and *logs a warning*
     above it. So no `norm_num`/`ring` numeral power with exponent > 256 is ever evaluated by default.
     Note also `lakefile.toml:23` — `leanOptions = { autoImplicit = false, warningAsError = true }` for the
     `Euler` lib: if any Euler-side tactic ever tried, the warning would be a build ERROR.
  3. `simp only [...]` carries NO simprocs: Lean core `Lean/Elab/Tactic/Simp.lean:568`,
     `let simprocs ← if simpOnly then pure {} else Simp.getSimprocs`. So a `simp only` list can never do
     ground arithmetic that isn't in the listed lemmas.

## Findings table

| # | Site (verified file:line) | What | Bit width | Normalisable? | Verdict |
|---|---|---|---|---|---|
| 1 | `Euler/PacketTailBase.lean:90` (`ring`, goal from :86-89) | `ring` must normalise `(4*R*550^2)^110`; coefficient `(4*550^2)^110 = 1210000^110 ~ 1.28e669` and `163*1210000^110` | **2223 / 2231 bits** (~35 limbs); largest single kernel multiply `c*c` with `c = 1210000^55` (1112 bits) | YES — exponent 110 <= 256 threshold, `evalPowProd` const-const branch | **REFUTED** (audit headline) / KERNEL-RISK |
| 2 | `Euler/ConstantCorrectionData.lean:146` `def pressureBound : ℝ := 9^729` | 2311-bit latent literal | 2311 bits if ever normalised | **NO** — 3 independent blocks (below) | OK (claim survives, mechanism restated) |
| 3 | `Euler/GevreyUniformConstants.lean:70,82,83` `(9*L)^729` | same numeral with symbolic `L` | 2311 bits if `ring`ed | NO — proofs use only `apply/rw/exact/linarith`; and 729 > 256 | OK |
| 4 | `Euler/PacketFiveCostPolynomial.lean:79` `(4*X*Polynomial.C ((550:ℝ)^2))^110` in `Polynomial ℝ` | `4^110 = 2^220` latent | 220 bits if `ring`ed | NO — only `simp only [Polynomial.eval_*]` at :113-114, no `ring`/`ring_nf` anywhere on `fivePolynomial` | NOTE |
| 5 | `Euler/PacketFiveCostPolynomial.lean:50-51` + `Euler/PacketShiftArithmetic.lean:8` | `Polynomial.C ((highShift n).factorial : ℝ)^2` with `n := 1,2` via `velocityPolynomial` (:53-54); `highShift 2 = 120`, `120!` | 661 bits (`120!`), 1322 bits squared | NO — `gradePolynomial_eval` (:83-88) is generic in `n` and rewrites with `Polynomial.eval_C` only; `highShift` is a plain non-reducible `def`; no `decide`/`Nat.factorial` unfolding here | NOTE (2nd largest latent numeral) |
| 6 | `Euler/PacketCoarseMajorant.lean:11,48,49` | `(4*R*(550*N)^2)^110`, `^(110*(p+1))` | — | NO — exponents symbolic; closers are `pow_le_pow_right₀`, `rw [pow_mul]; rfl`, `positivity`, `nlinarith` on `1 ≤ 4*R*(550*N)^2` (max ~`302500^2 = 9.15e10`, 37 bits) | OK |
| 7 | `Euler/PacketFiveCostGuards.lean:80-81` | `unfold tailPolynomialConstant; gcongr` on the `^110` term | — | NO — `gcongr` does congruence + `positivity` discharge, never ring-normalises | OK |
| 8 | `decide` surface: max literal is 1000 — `Euler/ParentHistoryFrequencyGuard.lean:81`, and ALSO `:101` (80), `Euler/PacketParameterEnvelope.lean:60`, `Euler/PacketSourceParameterScales.lean:121,126` | `Nat.decLe`/`Nat.ble` on 10-bit literals | 10 bits | evaluated, trivially | OK (audit right about the max VALUE, incomplete about the site list) |
| 9 | widest directly-stated CLOSED numeral (in)equality: `(1:ℝ) ≤ 1000000000` / `(0:ℝ) ≤ 1000000000` — `Euler/PacketGeometryAssembly.lean:70`, `Euler/PacketGeometryGuards.lean:54,76,83,93`, `Euler/PacketPhysicalFamily.lean:118` | `norm_num` on 10^9 | 30 bits | evaluated | OK |
| 10 | `Nat.factorial` with a CLOSED argument: only `Euler/EulerProof.lean:12153-12154` (`factorial_decay 4 z`, `norm_num only [Nat.factorial, Nat.cast_ofNat] at h`) and `Nat.factorial 0` (`Euler/GevreyInverseMap.lean:119`) | `4! = 24` | 5 bits | evaluated | OK |
| 11 | `Nat.choose`, `Nat.gcd`, `Nat.div`, `%`, `Nat.pow`, `native_decide`, `decide := true` simp config, `Finset.range <literal >= 100>`, `Fintype`-based `decide` | census: **no** `native_decide` (0 hits), **no** `decide := true` (0), **no** `Finset.range` with a literal >= 100 (0), **no** `Nat.gcd` (0); `%` only at `NavierStokes/SlotColoring.lean:144,161,170` and `NavierStokes/VolterraAnalyticBounds.lean:504` (mod 2/5/9); every `Nat.choose`/`Nat.pow`/`Nat.factorial` argument elsewhere is symbolic; the one custom `Decidable` instance (`Euler/PacketKnownPieces.lean:32`, `k.active p i`) is only used in `if`s with symbolic `p i` | — | — | OK |

## 1. `pressureBound := 9^729` — the audit's claim TESTED (it survives, its stated mechanism does not)

Complete reference list for `EulerConstantCorrection.pressureBound` (repo-wide grep; the homonym
`NavierStokes/OutgoingEntranceCone.lean:872` `noncomputable def pressureBound : ℝ := 10 * FuturePressureBounds.envelopeConstant`
and all `ShapedWaitBounds`/`OutgoingEntranceCone` `nlinarith`/`linarith`/`positivity` uses of it are the
OTHER, unrelated constant and are excluded):

```
Euler/ConstantCorrectionData.lean:146   def pressureBound : ℝ := 9^729
Euler/ConstantCorrectionData.lean:148   theorem pressureBound_one_le : 1 ≤ pressureBound :=
Euler/ConstantCorrectionData.lean:149     one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)
Euler/ConstantCorrectionData.lean:162/164  ... .pressureConstant 1 ≤ pressureBound ∧ ... ≤ pressureBound := by
Euler/ConstantCorrectionData.lean:165     simpa only [mul_one,pressureBound] using fixed_pressure_constants P hq
Euler/ConstantCorrectionData.lean:166       (jet P (ContinuousLinearMap.id ℝ Space) q) 1 1 zero_lt_one le_rfl (by norm_num)
Euler/SmallCorrectionScales.lean:16    def growth : ℝ := energyConstant P 0 0 1 1 pressureBound 1 1 0 0 1
Euler/SmallCorrectionScales.lean:19-20 energyConstant_pos ... (zero_le_one.trans pressureBound_one_le)
Euler/SmallCorrectionBudget.lean:26      M := pressureBound
Euler/SmallCorrectionBudget.lean:34      M_one_le := pressureBound_one_le
Euler/SmallCorrectionBudget.lean:91-94   change energyConstant P ... (1/1) 1 pressureBound 1 1 0 0 1 = growth P
Euler/SmallCorrectionBudget.lean:95      norm_num [growthBudgetBase,growthBudgetSlope,growth]
Euler/StaticEulerWeightedBounds.lean:42  def staticTimeCost (R : ℝ) : ℝ := (1+2*pressureBound*(448*1+1))*staticSourceCost P R
Euler/StaticEulerWeightedBounds.lean:44  def staticPressureCost (R : ℝ) : ℝ := 2*pressureBound*staticSourceCost P R
Euler/StaticEulerWeightedBounds.lean:53-55  have hP := zero_le_one.trans pressureBound_one_le / unfold staticTimeCost / positivity
Euler/StaticEulerWeightedBounds.lean:57-61  (same shape for staticPressureCost)
```

Tactic-by-tactic verdict:

* `:149` `one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)` — the `norm_num` goal is literally `(1:ℝ) ≤ 9`
  (2 bits). Elaboration unifies `1 ≤ pressureBound` with `1 ≤ ?a ^ ?n` by delta-unfolding the def,
  assigning `?a := 9`, `?n := 729`; the kernel then re-checks by delta + syntactic equality. The `729`
  stays an `OfNat` binary numeral and `Monoid.npow` is never unfolded. **The audit's phrase "with a
  symbolic exponent" is WRONG** — 729 is a closed literal — but the conclusion is right.
* `:165` `simpa only [mul_one,pressureBound] using fixed_pressure_constants ...` — this is the ONLY place
  where `9^729` becomes syntactically visible (the term's type is `... ≤ (9*1)^729`, see
  `Euler/GevreyUniformConstants.lean:82-83` with `L := 1`, and `mul_one` turns `9*1` into `9`). It cannot
  be evaluated: (a) `simp only` carries no simprocs (Lean core `Simp.lean:568`); (b) the reduction of
  `(9:ℝ)^729` to a literal needs the `norm_num` `Pow` extension, which `simp only` never runs — core
  simprocs `Nat.reducePow`/`Int.reducePow` do not apply to a `Real` base; (c) even a direct `norm_num`
  would REFUSE: `729 > 256 = exponentiation.threshold`, and under `warningAsError = true`
  (`lakefile.toml:23`) the resulting warning would fail the Euler build.
* `:166` `(by norm_num)` is the `hcL : (1:ℝ)⁻¹ ≤ 1` argument (see the signature at
  `Euler/GevreyUniformConstants.lean:78-83`); no `9^729` in that goal.
* `SmallCorrectionBudget.lean:95` `norm_num [growthBudgetBase,growthBudgetSlope,growth]` is the most
  dangerous-looking site: `norm_num` DOES run here with `pressureBound` in the goal (:94). It is still
  safe: `pressureBound` is not in the simp set, is a plain `def` (not `abbrev`/`@[reducible]`/`@[simp]`),
  so neither simp unfolding nor the norm_num discrimination-tree lookup reaches `HPow.hPow 9 729`; both
  sides keep it as one opaque atom.
* `StaticEulerWeightedBounds.lean:54-55/60-61` `unfold <cost>; positivity` — `unfold` names only
  `staticTimeCost`/`staticPressureCost`; `pressureBound` stays an atom and is discharged from the
  hypothesis `hP` at :53/:59. The only numeral `positivity`/`norm_num` evaluates there is `448*1+1 = 449`.

**Verdict: the audit's `9^729`-is-never-normalised claim SURVIVES** (OK), with two corrections: the
exponent is a closed literal, not symbolic; and the real, checkable protections are the ℝ base +
non-reducible `def` + the core `exponentiation.threshold = 256` guard.

## 2. Other big closed powers (repo-wide census)

Regex census over all 2659 `.lean` files (643991 lines) for `<digits> ^ <digits>`: exactly **one** hit with
a closed numeral base and closed exponent >= 20, namely `Euler/ConstantCorrectionData.lean:146` (`9^729`).
(The only other regex hit, `Euler/PacketSourceScaleActual.lean:33`
`sourceTheta J C (scaleSequence J X) 0^60`, is a false positive: the base is the application
`sourceTheta ... 0`, not the numeral `0`.) The largest closed power actually STATED in a `by norm_num`
goal is `NavierStokes/PulseAmplitude.lean:110` `(1024 : ℝ) = 2 ^ 10 := by norm_num` (11 bits).

Census of every `^ n` with `n >= 20` (472 hits; exponent multiset `{29:120, 1000:80, 40:72, 28:53, 80:36,
21:23, 30:23, 20:13, 60:10, 27:10, 1010:7, 110:5, 498:4, 729:4, 222:4, 102:3, 2000:2, 500:2, 220:1}`),
filtered to those whose base is a parenthesised expression containing a numeral >= 2 — i.e. the only ones
where a ring-family tactic could produce `c^n`:

```
Euler/GevreyUniformConstants.lean:70,82,83   (9*L)^729                       -> never ring-normalised; 729 > 256
Euler/PacketCoarseMajorant.lean:11,48        (4*R*(550*(N : ℝ))^2)^110       -> exponents symbolic; no ring
Euler/PacketFiveCostPolynomial.lean:79       (4*X*Polynomial.C ((550:ℝ)^2))^110 -> simp only, no ring
Euler/PacketTailBase.lean:57,65              (4*R*550^2)^110                 -> ring at :90  <-- THE HIT
Euler/EulerProof.lean:20222 / PacketSourceScaleActual.lean:197  (T*x^2)^60   -> coefficient 1
```

All `X^1000`, `X^1010`, `X^2000`, `X^498`, `Θ^40`, `k^(10*(q+2))` etc. have a bare atom base (coefficient
1), so their ring coefficient is `1^n = 1`. `Euler/ParentHistoryFrequencyGuard.lean:85`
`_ = X^2000 := by rw [← pow_add]` and `Euler/PacketTailBase.lean:89`
`rw [show 222 = 2+220 from rfl, pow_add]` only ask the kernel for `1000+1000` / `2+220` (11 bits).

## 3. The refutation in detail — `Euler/PacketTailBase.lean:86-90`

Verbatim (re-derived from the original file):

```lean
56  def tailPolynomialConstant (R H C : ℝ) : ℝ :=
57    (1+163*C)*H^2*(4*R*550^2)^110
...
64  theorem gradeBase_polynomial (R : ℝ) (N : ℕ) :
65      gradeBase R N = (4*R*550^2)^110*(N : ℝ)^220 := by
...
70  theorem tailBase_polynomial_bound (R H C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 1 ≤ N) :
71      tailBase R H C N ≤ tailPolynomialConstant R H C*(N : ℝ)^222 := by
...
86      _ = tailPolynomialConstant R H C*(N : ℝ)^222 := by
87        rw [gradeBase_polynomial]
88        unfold tailPolynomialConstant
89        rw [show 222 = 2+220 from rfl, pow_add]
90        ring
```

At line 90 the goal is (both sides contain the unfolded power)

```
((1+163*C)*(N:ℝ)^2)*H^2*((4*R*550^2)^110*(N:ℝ)^220)
  = ((1+163*C)*H^2*(4*R*550^2)^110)*((N:ℝ)^2*(N:ℝ)^220)
```

`ring` normalises `4*R*550^2` to the monomial `1210000 * R` (`4*302500`), then `evalPow` -> `evalPowProd`
hits the `.const za, .const zb` branch (`Ring/Basic.lean:930-939`) and calls
`NormNum.evalPow.core` -> `evalNatPow 1210000 110`, guarded by `checkExponent 110` (110 <= 256 -> PASS).
The emitted certificate therefore contains the raw literals

* `1210000^110 = 1.2777...e669`, **2223 bits** (35 x 64-bit limbs), and
* `163 * 1210000^110`, **2231 bits** (from distributing the 2-term factor `1+163*C`),

and the kernel must re-check the binary-exponentiation chain `IsNatPowT.bit0/bit1`, whose widest single
step is `Nat.mul c c` with `c = 1210000^55` (1112 bits x 1112 bits -> 2223 bits). This is squarely
multi-limb GMP, ~2160 bits above one machine word.

**REFUTED**: the audit's published headline — "The largest closed `Nat` the kernel is ever asked to
evaluate in the whole artifact is ~5.0x10^17 (59-61 bits, one machine word) — an `nlinarith` certificate
at NavierStokes/PulseCone.lean:1017" — is FALSE as stated. `Euler/PacketTailBase.lean:90` forces a
2223-bit closed `Nat` through the kernel, ~10^650 times larger. (For the record the PulseCone site is
quoted correctly by the audit: `:1017` reads
`have hbase : (1 / 2 : ℝ) ≤ (2001 / 1000) * decay d.core ^ 2 * (99999 / 100000) := by`, closed by
`nlinarith` on :1018, whose denominator lcm is `10^10 * 1000 * 100000 = 10^18` — consistent with ~5e17,
~60 bits. It is simply not the maximum of the artifact.)

Residual doubt (stated plainly): UNBUILT. If the reader disputes that `ring` exponentiates the
coefficient, the fallback path is `evalPowProdAtom` (`Ring/Basic.lean:945`), which would keep
`(4*R*550^2)^110` symbolic and leave the artifact's max at the certificate scale. The quoted
`evalPowProd` source, present identically in both local Mathlib copies, says it does exponentiate;
the only way to settle it is one `lake build` of `Euler/PacketTailBase.lean` (or a 3-line
`example (R H C : ℝ) : ... := by ring` probe with `set_option trace.profiler true`).

## 4. Widest CLOSED numeral (in)equality stated directly in the source

Max literal appearing anywhere in the artifact (excluding a git hash inside a URL comment at
`Euler/SolutionDefinitions.lean:26`) is `1000000000 = 10^9`:
`Euler/PacketNeighborControlled.lean:154` `def neighborStabilityConstant : ℝ := 1000000000*exp 6`, and the
directly proved closed goals `(by norm_num : (1:ℝ) ≤ 1000000000)` /
`(by norm_num : (0:ℝ) ≤ 1000000000)` at `Euler/PacketGeometryAssembly.lean:70`,
`Euler/PacketGeometryGuards.lean:54,76,83,93`, `Euler/PacketPhysicalFamily.lean:118`. **30 bits.** No
closed-numeral goal in the artifact exceeds 10 digits, so the source-literal route never approaches 64
bits; every wide kernel numeral in this artifact is tactic-manufactured.

## 5. Answer

* Single widest numeral I can prove (source-level) the kernel must evaluate:
  **`1210000^110` (= `(4*550^2)^110` ~ 1.28e669, 2223 bits; with the `163*` copy, 2231 bits)**, at
  **`Euler/PacketTailBase.lean:90`** (`ring`, goal set up at :86-89), mechanism =
  `ring` `evalPowProd` const-const branch -> `NormNum.evalNatPow` binary exponentiation ->
  kernel `Nat.mul` GMP chain.
* Is 64 bits (1.8446744e19) crossed? **YES, decisively — by a factor of ~10^650 at that one site.**
  Elsewhere: the `decide` surface tops out at 10 bits, closed source (in)equalities at 30 bits, closed
  factorials at 5 bits, and the two other 2000+-bit literals in the artifact (`9^729` = 2311 bits,
  `120!^2` = 1322 bits) are latent and never normalised.

## Verdict counts

REFUTED 1 (audit headline max-numeral claim, via `Euler/PacketTailBase.lean:90`; the same row is a
KERNEL-RISK) - OK 7 - NOTE 3 - UNCLEAR 0 - ESCALATE 0.
Everything above is UNBUILT (no Mathlib, no `lake build` in the clone).
