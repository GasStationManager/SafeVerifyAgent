# Worker report — thread `kernel-choose-pow`

Artifact: `openai/NavierStokesAndEuler` @ `f9e8bc5`, clone `/home/gsm/.openclaw/workspace/repos/NSE`
(2,659 `.lean` files, 641,332 lines, 52,516 declarations). **No Mathlib on this box, no `lake build`
was run: every statement below is SOURCE-LEVEL and therefore UNBUILT unless marked otherwise.**
Method note: all citations were re-derived from the ORIGINAL file text (`TEXT[file].split('\n')[line-1]`),
not from the comment-stripped copy used for the census, and are quoted verbatim.

## Headline

**The published one-sentence claim is right about `9^729` and wrong about `Nat.choose`.** `9^729`
(`Euler/ConstantCorrectionData.lean:146`) is confirmed inert — but it is 2311 bits, not "~2313", and
its consumer is `one_le_pow₀` (subscript zero), not `one_le_pow0`. On the combinatorial side the
claim `"the only closed values are 0!, C(0,0), and 4! = 24"` is **REFUTED in two directions**:
(i) `C(0,0)` **does not exist anywhere in the artifact** — of 368 `Nat.choose` applications, **zero**
have a closed numeral in either argument, and the token `Nat.choose` applied to a literal occurs
0 times; (ii) the report **missed** a closed factorial value, `fixedCost 6`
(`Euler/SobolevSourceExponent.lean:14` instantiated at `Euler/PacketUniversalFrequency.lean:24`)
`= 2^6·Σ_{j=0}^{6}(j!)^2 = 34,138,752` (26 bits), which is 20 bits larger than `4! = 24` — harmless,
because it is an `ℝ`-valued `Finset.sum` that no tactic ever normalises.

**Verdict tally: OK 6, NOTE 1, REFUTED 4, ESCALATE 3, KERNEL-RISK 0, UNCLEAR 0.**
(OK: A1 `0!`/`change`, A2 `0!`/`simp`, A3 `4!`, B1 `9^729`, B2 `2^10`, C jet files.
NOTE: A4 `fixedCost 6` missing from the report. REFUTED: A5 `C(0,0)` does not exist;
B3 `0^60` is a parse artifact; and two claims of this brief — "534 declarations" and the
"`!` in `simp!`/`≠`" pollution story — see next paragraph. ESCALATE: E1-E3.)

**Additionally, the audit's own instrument is broken on this surface and the brief mis-reads it.**
The `choose_fact` column regex is `\bNat\.(?:choose|factorial)\b|\bchoose\b`
(`audits/scan_kernel_risk.py`). It is blind to dot notation `n.factorial`, which is how the artifact
writes **878 of its 892** factorial terms. Measured on the same scope, the 534 the brief calls
"declarations" is 534 *mentions* in **321** declarations (246 in-cone, not 400), and decomposes as
368 `X.choose` + 100 `choose` *tactic* invocations + 56 `Classical.choose` + 4 argument-less
`.choose` + **6** `Nat.factorial`. So the census saw 6 of the artifact's 892 factorial sites (0.7%)
and 30% of what it did count is not combinatorics at all. The brief's specific warning is also
wrong: the pollution is **not** `!` in `simp!`/`≠` (the regex contains no `!`), it is the `choose`
tactic and `Classical.choose`.

Net kernel exposure for these two surfaces: **the largest closed integer the kernel is asked to
reduce is ~2^21 (`1146880`), from `ring` on `1120*(2*Cθ)^10`; on the factorial surface it is `24`.**

## Scope

| what | count | how |
|---|---|---|
| declarations in artifact | 52,516 | `INVENTORY.csv`, re-derived |
| declarations containing a genuine factorial term | **423** (334 in-cone) | own scan, comment-stripped, enclosing-decl map |
| declarations containing a genuine `Nat.choose` | **173** (132 in-cone) | own scan |
| union of the two (my population) | **567** (444 in-cone), 241 files | own scan |
| factorial TERM occurrences enumerated with their argument atom | **892** = 878 `.factorial`/`Nat.factorial` + 14 postfix `!` | balanced-paren argument extractor, every one classified closed / symbolic |
| `Nat.choose` application sites enumerated with both argument atoms | **368** | same |
| `^`-with-literal-exponent occurrences with exponent ≥ 8, base atom extracted | **711** | same |
| closed-base **and** closed-exponent `^` occurrences | **105** (all values computed) | same |
| closed-base, symbolic-exponent `^` occurrences | **203** | same |
| declarations read LINE BY LINE | **99** (84 in-cone) in 26 source windows, 860 lines | shown in full and quoted |
| declarations only grepped / machine-classified | the remaining 468 of my 567 | argument-atom classification only |

## (A) Every closed-numeral factorial / binomial site

Method: for every `.factorial` I took the preceding atom (balanced-paren backwards scan); for every
`Nat.factorial` the following argument; for every `X.choose Y` both. An argument counts as CLOSED
only if it contains a digit and matches `[\s\d()+*\-/^]+` after stripping type ascriptions. This
correctly rejects the trap that fooled the earlier scan: `(k + 1).factorial` and `(n + 1)!` contain
the literal `1` but are symbolic.

| # | site | value | is the kernel forced to reduce it? | verdict |
|---|---|---|---|---|
| A1 | `Euler/GevreyInverseMap.lean:119` — `change ‖iteratedFDeriv ℝ 1 Y x‖ ≤ C * L^0 * (Nat.factorial 0 : ℝ)^2` | `0! = 1` (1 bit) | **No.** `change` needs only `0+1 ≡ 1` on `Nat` literals; the factorial itself is then discharged by the NAMED lemma `Nat.factorial_zero` at `:121` (`simpa only [norm_iteratedFDeriv_zero, pow_zero, Nat.factorial_zero,`) | OK |
| A2 | `NavierStokes/BorelExtension.lean:58` and `:67` — `simp [monomial]` with `j := 0`, where `:26` is `def monomial (j : ℕ) (v : E) (s : ℝ) : E := (s ^ j / (j.factorial : ℝ)) • v` | `0! = 1` (1 bit) | **No.** `Nat.factorial_zero` is `@[simp]`; simp rewrites by name. Value never built. *(Not in the published list.)* | OK |
| A3 | `Euler/EulerProof.lean:12153` — `have h := factorial_decay 4 z hz0.le`, then `:12154` — `norm_num only [Nat.factorial, Nat.cast_ofNat] at h` | `4! = 24` (5 bits) | **YES.** This is the ONLY tactic in the artifact that unfolds `Nat.factorial` at a closed argument. `factorial_decay` (`:11094-11095`, `t ^ n * Real.exp (-t) ≤ n.factorial`) is instantiated at `n := 4`; the equation lemmas plus `Nat.reduceMul` give `24`, cast to `ℝ`. Downstream `192 ≤ z` at `:12156` is `8·24`, consistent. | OK (report CONFIRMED, citation exact) |
| A4 | `Euler/SobolevSourceExponent.lean:14` — `def fixedCost (q : ℕ) : ℝ := (2 : ℝ)^q*∑ j ∈ range (q+1), (j.factorial : ℝ)^2`, instantiated at `Euler/PacketUniversalFrequency.lean:24` — `derivative_bound : fixedCost 6 ≤ k` (and `:29`) | `2^6·Σ_{j≤6}(j!)^2 = 64·533418 = 34,138,752` (26 bits); largest single factorial `6! = 720` | **No.** `fixedCost` is unfolded only at symbolic `q` (`Euler/SobolevSourceExponent.lean:54`, then `ring`); at `q := 6` it appears only as an `ℝ` hypothesis and as an `eventually_ge_atTop` threshold. It is an `ℝ`-valued `Finset.sum`: `ℝ` has no kernel numeral form, so there is no GMP path even in principle. | NOTE — **report incomplete**: this is the artifact's largest closed factorial value and it is not in the published list |
| A5 | any `Nat.choose`/`Nat.ascFactorial`/`Nat.descFactorial` at a closed argument | — | **none exist** | REFUTED (see below) |

**`C(0,0)` is refuted.** All 368 `Nat.choose` applications carry symbolic receivers and symbolic
second arguments (`(n + 1).choose (k + 1)`, `(j + l + 1).choose l`, `(i + k).choose k`, …). A
whole-file regex for `choose` adjacent to a literal in either slot returns nothing; the single
numeral-looking hit, `A.selection.2.2.choose` (`Euler/PacketSourceGeometryData.lean:188`), is
`Exists.choose` on a structure projection. The binomial *consumers* are all named lemmas that never
compute: `Nat.sum_range_choose` at symbolic order in ≥ 30 files (e.g.
`NavierStokes/JetBounds.lean:111` — `exact_mod_cast Nat.sum_range_choose n`), and
`Nat.choose_zero_right`, `Nat.choose_self`, `Nat.choose_pos`, `Nat.choose_symm`,
`Nat.choose_le_two_pow` used as simp lemmas (e.g. `NavierStokes/AxisOperators.lean:48` —
`simp only [Nat.choose_zero_right, Nat.cast_one, one_mul,`). The generic shape is
`Euler/EulerProof.lean:391` — `|∑ k ∈ range (n + 1), (n.choose k : ℝ) * f k * g (n - k)|`.

**Corrected maximum.** Closed factorial value *present*: 34,138,752 = 26 bits (A4).
Closed factorial value the kernel is actually *forced to compute*: `24` = **5 bits** (A3).
Closed binomial values: **none, at any width**.

**Tactic-adjacency cross-check.** Of all lines that contain a factorial or a `Nat.choose` term,
81 also name a tactic. The distribution is `positivity` 57, `ring` 17, `nlinarith` 4, `linarith` 3,
`norm_num` 2, `field_simp` 1, `rfl` 1 — and **zero `decide`, zero `native_decide`, zero `omega` on
a factorial/choose goal**. The single bare `rfl` is `Euler/VolumeSobolevComposition.lean:93` —
`have hβ : (β : ℝ) = (n.factorial : ℝ)*D^n := rfl` — which is a projection of the structure literal
at `:60` (`let β : ℝ≥0 := ⟨(n.factorial : ℝ)*D^n,by positivity⟩`) at symbolic `n`: iota/proj
reduction only, no arithmetic. The one `field_simp` is `Euler/EulerProof.lean:11101` at symbolic `n`.

## (B) Powers with closed base AND closed exponent

**Rule used** (stated because it decides most of this section): a `^` is a kernel-GMP hazard only if
the *whole* expression can reduce to a numeral in a type the kernel represents as a literal —
`Nat`, `Int`, and (via `norm_num` certificates) `Rat`. `HPow.hPow (9:ℝ) (729:ℕ)` is
`Monoid.npow` over a `noncomputable` field: there is no numeral form for `Real`, `Monoid.npow` on
`Real.instMonoid` has no numeral-reducing kernel path, and core's numeral simprocs
(`Nat.reducePow`, `Int.reducePow`) do not fire on a general `OfNat` semiring. So an `ℝ`-typed
closed power is inert *unless* a `norm_num`/`ring`/`nlinarith` invocation actually sees it and emits
a rational certificate. Consequently the test I applied to every candidate is: **is the base atom
closed, and does any tactic in the enclosing declaration have the closed power in scope?**

Census result: of **711** occurrences of `^ <literal ≥ 8>`, exactly **3** have a closed base, and one
of those is a parse artifact.

| # | site | pair | value | forced? | verdict |
|---|---|---|---|---|---|
| B1 | `Euler/ConstantCorrectionData.lean:146` — `def pressureBound : ℝ := 9^729` | `9^729` in `ℝ` | **2311 bits**, 696 decimal digits | **No.** Consumer at `:148-149`: `theorem pressureBound_one_le : 1 ≤ pressureBound :=` / `  one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)` — the exponent `729` stays a symbolic `Nat` literal argument of `one_le_pow₀`; `norm_num` is applied only to `(1:ℝ) ≤ 9`. The declaration is a term-mode `def` with 0 tactics. | OK — report CONFIRMED, with two corrections (bits, and `one_le_pow₀` not `one_le_pow0`) |
| B2 | `NavierStokes/PulseAmplitude.lean:110` — `    (1024 : ℝ) = 2 ^ 10 := by norm_num` | `2^10` in `ℝ` | 1024, 11 bits | **YES** — `norm_num` emits a rational certificate. Trivial width. | OK |
| B3 | `Euler/PacketSourceScaleActual.lean:33` — `    sourceTheta J C (scaleSequence J X) 0^60` | **not** a closed pair | — | Application binds tighter than `^`: this is `(sourceTheta J C (scaleSequence J X) 0)^60`, symbolic base. Compare `:36` — `geometryError J D C c X a n * sourceTheta J C (scaleSequence J X) n^60`. | REFUTED (my own regex false positive; a naive `bigpow` census would report this as `0^60`) |

Every other closed base/closed exponent pair in the artifact has exponent < 8. Full value multiset
over the 105 such occurrences: `9^729`×1, `550^2`×3, `2^10`×1, `4^5`×2, `4^3`×2, `2^5`×1, `2^2`×5,
`1^2`×38, `1^3`×2, `2^0`×1, `0^2`×48. Largest besides B1: **`550^2 = 302500` (19 bits)**, in
`Euler/PacketTailBase.lean:57` — `  (1+163*C)*H^2*(4*R*550^2)^110` and
`Euler/PacketCoarseMajorant.lean:11` — `def gradeBase (R : ℝ) (N : ℕ) : ℝ := (4*R*(550*(N : ℝ))^2)^110`.

**The `^110` family deserved the check and passes.** `ring` normalises an `ℝ` product to a Horner
form with rational coefficients, so a `ring` call that ever saw `(4*R*550^2)^110` would be asked to
produce the coefficient `1210000^110` — about 2148 bits, comparable to `9^729`. It never does:
`gradeBase_polynomial` (`Euler/PacketTailBase.lean:65`) proves the identity by
`unfold` + `rw [show 4*R*(550*(N : ℝ))^2 = (4*R*550^2)*(N : ℝ)^2 by ring, mul_pow, ← pow_mul]`,
so `ring` sees only exponent 2; `majorant_grade_bound` (`Euler/PacketCoarseMajorant.lean:48-49`)
moves the `^110` with `pow_le_pow_right₀` / `pow_mul` and closes with `rfl` on a delta-unfold of
`gradeBase`; `tailPolynomialConstant_nonneg` and `gradeBase_nonneg` use `positivity`, which recurses
structurally (`pow_pos`, `mul_pos`) and never collapses numerals. Verdict OK.

**The audit's earlier list is not made of closed pairs at all.** `Θ^40`, `Θ^29`, `Θ^21`, `k^80`
have *symbolic* bases (`Θ` is the top base atom in the exponent census, 213 occurrences; `k` 34), so
no reduction is possible in any type. `6^m` is the mirror case, closed base and symbolic exponent:
the only `6^<ident>` in the artifact is `NavierStokes/SlotGeometry.lean:107` (`6 ^ D` in `ℚ`,
paired with `:95` — `def denominator (m D : ℕ) : ℝ := ((m : ℝ) + 1) * (6 : ℝ) ^ D`). There are 203
closed-base/symbolic-exponent occurrences repo-wide, max base 64; a symbolic exponent blocks
`Monoid.npow` reduction outright, so none is a hazard. Verdict: OK for all five.

**Where the kernel actually does closed-power arithmetic on this surface** (all tiny):
* `Euler/PacketParameterEnvelope.lean:90-91` — `simp only [mul_pow,← pow_mul]` then `ring` on
  `560*(2*Cθ*A^2*B^2)^10*(2*exp z) = (1120*(2*Cθ)^10)*(A^20*B^20)*exp z`. `ring` must confirm
  `560·2^10·2 = 1120·2^10 = 1146880` — **21 bits, the widest closed integer on this whole surface.**
  The constant is `Euler/PacketParameterEnvelope.lean:16` — `def constant (Cθ CB Cξ : ℝ) : ℝ := 8+1120*(2*Cθ)^10+CB+Cξ`.
* `Euler/GevreyUniformConstants.lean:72-73` — `have he : 3^q ≤ 729 := by` /
  `    exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hq).trans (by norm_num)`: a genuine **`Nat`**
  closed power, `3^6 = 729`, 10 bits. This is the provenance of the `729`: the exponent is `3^6`
  where 6 is the Sobolev order, and `:70` reads
  `    (hcoeff : ∀ r ≤ q, boundLevel period K r ≤ L) : K.pressureConstant c ≤ (9*L)^729 := by`.
* `(by decide)` at `Euler/PacketParameterEnvelope.lean:83` discharges `hq : q ≤ 1000`
  (`Euler/PacketSourceParameterScales.lean:51`) at `q := 20`: `Nat.ble 20 1000`, 10 bits.
* `550^2` under `nlinarith` (`Euler/PacketCoarseMajorant.lean:20`, `:36`) and `ring`: 19 bits.

**`9^729` is never exposed to a normalising tactic.** All consumers of `pressureBound` are symbolic:
`Euler/SmallCorrectionScales.lean:16` and `:19` pass it as an `ℝ` argument and use
`pressureBound_one_le`; `Euler/StaticEulerWeightedBounds.lean:42,44,53,59` likewise;
`Euler/SmallCorrectionBudget.lean:26,34,94`. The one norm_num that comes close,
`Euler/SmallCorrectionBudget.lean:95` — `  norm_num [growthBudgetBase,growthBudgetSlope,growth]` —
has `pressureBound` **folded** on both sides of the `change` at `:91-94` (`     (1/1) 1 pressureBound 1 1 0 0 1 = growth P`);
`pressureBound` is a plain `def` with no `@[simp]`/`@[reducible]`, so `norm_num` cannot unfold it.
The single place it *is* unfolded is `Euler/ConstantCorrectionData.lean:165` —
`  simpa only [mul_one,pressureBound] using fixed_pressure_constants P hq` — where `mul_one` turns
the supplier's `(9*L)^729` at `L := 1` into `9^729` and matches it **syntactically** against
`pressureBound`'s body. No numeral is built. See Escalation E1 for the residual `simp only`
simproc question.

## (C) Jet / Taylor files: is any factorial at a closed order?

**No — zero closed orders in all ten factorial-dense files.** Argument atoms, machine-extracted:

| file | factorial+choose sites | argument atoms | closed |
|---|---|---|---|
| `NavierStokes/AxisWeightEstimates.lean` | 54 | `m`, `n`, `(n + m)`, `(k + l)`, `(i + k)`, `kl.1` | **0** |
| `NavierStokes/JetBounds.lean` | 8 | `n.choose i` only | **0** |
| `NavierStokes/EdgeWeightJets.lean` | 3 | `i.choose k` | **0** |
| `NavierStokes/FiveProfileMoments.lean` | 5 | `N`, `k`, `n.choose i` | **0** |
| `NavierStokes/CutStageEstimates.lean` | 9 | `m`, `m.choose i` | **0** |
| `NavierStokes/SlowBorelBase.lean` | 13 | `m`, `(m - i)`, `n`, `m.choose i` | **0** |
| `NavierStokes/BaseResidual.lean` | 3 | `m` | **0** |
| `NavierStokes/AxisOperators.lean` | 9 | `m.choose kl.1` | **0** |
| `NavierStokes/BaseChartJets.lean` | 1 | `N` | **0** |
| `NavierStokes/PhysicalResidualJetBounds.lean` | 9 | `m`, `k`, `k.choose i` | **0** |

The analytic normalising factors are uniformly `(m.factorial : ℝ)`, `((k+1).factorial : ℝ)^2`,
`(n.factorial : ℝ)^2` at a universally quantified order, and the binomials always come from a
Leibniz/Faà-di-Bruno sum over `range (n+1)`. Two files use Mathlib's postfix notation instead —
`NavierStokes/TangentODE.lean:83` (`      (v.lip * |t.1 - v.left|) ^ (n + 1) / (n + 1)! * d := by`)
and `Euler/EulerProof.lean:18207` — 14 occurrences total, all at `n`, `N` or `(n + 1)`.
The factorial *bounding* lemmas are also order-symbolic: `Euler/PacketCoarseMajorant.lean:24` —
`    (hd : d ≤ 110*(p+1)) : (d.factorial : ℝ) ≤ (550*(N : ℝ))^d := by` (proved via
`Nat.factorial_le_pow` + `Nat.pow_le_pow_left`, then `omega` for `d ≤ 550*N`). Verdict OK.

## (D) Corrected one-sentence statement for the published report

> The one large power, `9^729` (`Euler/ConstantCorrectionData.lean:146`, 2311 bits), is never
> normalised — it is consumed by `one_le_pow₀` with the exponent left as a symbolic `Nat` literal
> (`:148-149`), it is a `Monoid.npow` over `ℝ` for which the kernel has no numeral path, and the one
> site that unfolds it (`:165`) matches it syntactically under `simp only [mul_one, pressureBound]`;
> `Nat.choose` is never computed at all (368 applications, **zero** with a closed argument in either
> slot — there is no `C(0,0)` in the artifact), and the complete list of closed factorial values is
> `0!` (three sites, each discharged by the named lemma `Nat.factorial_zero`), `4! = 24`
> (`Euler/EulerProof.lean:12153-54`, the only factorial the kernel actually reduces, 5 bits), and
> `fixedCost 6 = 2^6·Σ_{j≤6}(j!)^2 = 34,138,752` (`Euler/SobolevSourceExponent.lean:14` at
> `Euler/PacketUniversalFrequency.lean:24`, 26 bits, an `ℝ`-valued `Finset.sum` that no tactic ever
> normalises) — so the widest closed integer the kernel is asked to reduce anywhere on the
> power-and-binomial surface is `1146880` (21 bits, from `ring` on `1120*(2*Cθ)^10`,
> `Euler/PacketParameterEnvelope.lean:16,90-91`).

## Kernel-risk assessment for this scope

**(1) Recursive inductive types and recursor/iota reduction.** `Nat.choose` is the artifact's most
`Nat.rec`-heavy potential consumer — it is both wide (Pascal branching) and deep — and it is
**never applied to a literal**, so the kernel never runs its recursor on a closed argument. Same for
`Nat.factorial` except at `0` and `4`: `Nat.factorial 4` unfolds through 4 iota steps
(`Nat.factorial.eq_2` chain) and `Nat.factorial 0` through one, both via simp equation lemmas rather
than raw `Nat.rec` whnf. On my surface the recursor exposure is therefore ~5 iota reductions in the
whole artifact. The `Finset.sum` in `fixedCost 6` would be a `Multiset.foldr`/`List.rec` walk over
`Finset.range 7` if anything forced it; nothing does (A4). Residual iota work is the delta/proj
unfolds at `Euler/VolumeSobolevComposition.lean:93` and `Euler/PacketCoarseMajorant.lean:49`, both
at symbolic order. **Verdict: OK.**

**(2) `Nat` arithmetic delegated to GMP.** This is the vector the thread exists for, and the answer
is that the artifact's two "big" surfaces are both *decorative*. `9^729` (2311 bits) and
`(4*R*550^2)^110` (a 2148-bit coefficient if `ring` ever expanded it) are `ℝ` terms that no tactic
normalises; the largest closed *integers* the kernel must actually evaluate on this surface are
`1146880` (21 bits, `ring`), `302500` (19 bits, `ring`/`nlinarith`), `1024` (11 bits, `norm_num`),
`729` (10 bits, `Nat`, `norm_num`), `1000` (10 bits, `Nat.ble` under `decide`) and `24` (5 bits,
`norm_num only [Nat.factorial]`). All are single-limb GMP operations, the most exercised code path in
the kernel. A GMP-level kernel bug would have to be wrong on ≤ 21-bit multiplication and comparison
to be reachable from here. **Verdict: OK.** (The artifact's real bignum surface is the 7+-digit
decimal literals in `BIGNUM_SITES.md` — e.g. `Euler/EulerProof.lean:18479`
`noncomputable def stabilityConstant : ℝ := 320000000 * exp 6` — which is a different thread's scope,
and is `ℝ` besides.)

**(3) Custom metaprogramming.** Nothing new. The two surfaces are driven entirely by stock Mathlib
tactics (`norm_num`, `simp only`, `ring`, `nlinarith`, `positivity`, `gcongr`, `omega`, `decide`) and
stock lemma names (`one_le_pow₀`, `pow_le_pow_right₀`, `pow_le_pow_left₀`, `mul_pow`, `pow_mul`,
`Nat.factorial_zero`, `Nat.factorial_le`, `Nat.factorial_le_pow`, `Nat.pow_le_pow_right`,
`Nat.sum_range_choose`, `Nat.choose_zero_right`). Zero `macro`/`elab`/`syntax`/`notation`/`set_option`
occurrences in any file I read. **Verdict: OK.**

## Escalations

**E1 — Does `simp only [mul_one, pressureBound]` fire a numeral simproc on `(9:ℝ)^729`?**
*Question for an expert:* in the toolchain pinned by `lean-toolchain`, does `simp only [<lemmas>]`
run the default `simproc` set, and if so is there any simproc that evaluates `HPow.hPow (9:ℝ) (729:ℕ)`
(as opposed to `Nat.reducePow`/`Int.reducePow`, which need a `Nat`/`Int` literal)?
*Site:* `Euler/ConstantCorrectionData.lean:165` — `  simpa only [mul_one,pressureBound] using fixed_pressure_constants P hq`.
*Why it matters:* this is the only place in the artifact where `9^729` is unfolded from behind its
`def`. If a simproc evaluated it, the kernel would be handed a 2311-bit literal — still only a GMP
multiplication chain, but it would move the artifact's measured exposure by two orders of magnitude.
*Evidence that settles it:* `lake env lean --run` on a one-line file
`example : (9:ℝ)^729 = 9^729 := by simp only []` plus `set_option trace.Meta.Tactic.simp true`, or
`#print axioms` size / `.olean` term size of `pressureBound_one_le` and `identity_pressure`. My
source-level reading (no `@[simp]`/`@[reducible]` on `pressureBound`; `norm_num`'s `Pow` extension
is what handles `ℝ` literal powers, and it is not invoked at `:165`) says NO, but it is UNBUILT.

**E2 — Is `norm_num only [Nat.factorial, Nat.cast_ofNat]` at `Euler/EulerProof.lean:12154` closing on
`24`, and does it stay 5 bits?**
*Question:* does that call produce `h : z^4 * exp (-z) ≤ 24`, i.e. does the `Nat.factorial` equation
chain plus `Nat.reduceMul` fully evaluate, and is the certificate a `Nat` numeral chain
(`4*3*2*1*1`) rather than an `Int`/`Rat` one?
*Why it matters:* it is the artifact's ONLY kernel-forced factorial evaluation, so it is the whole
factorial exposure. The downstream `192 ≤ z` at `:12156` and `nlinarith` at `:12158` are only sound
if the value is 24.
*Evidence:* build the file and `#check`/`set_option pp.numericTypes true` on `h` after `:12154`;
or `example (z:ℝ) (h : z^4*Real.exp (-z) ≤ (Nat.factorial 4:ℝ)) : True := by norm_num only [Nat.factorial, Nat.cast_ofNat] at h; trivial`
with a trace. UNBUILT here.

**E3 — Could `nlinarith only [...]` at `Euler/PacketParameterEnvelope.lean:98` cross-multiply
`(2*Cθ)^10` into a wider coefficient than `ring` does?**
*Question:* what is the largest rational coefficient in the Positivstellensatz certificate that
`nlinarith only [hFE,hKF,hTiF,hTiTotalF,hBF,hξF,hDF,hhF,hCpF]` emits, given `hCpF` carries
`1120*(2*Cθ)^10`? Products of two hypotheses could square `1146880` → 42 bits; three → 63 bits.
*Why it matters:* it is the only place on my surface where a nonlinear tactic multiplies a
closed power by another closed power. 42-63 bits is still one GMP limb, so I rate this LOW, but I
could not bound it at source level.
*Evidence:* `set_option trace.linarith true` / `Polyrith`-style certificate dump on that goal.

## Residue — what I could NOT check

1. **Nothing was machine-checked.** No Mathlib, no `lake build`. Every "the kernel is not forced"
   judgement is a reading of the tactic script plus the standard behaviour of `simp only`,
   `norm_num`, `ring`, `positivity` and `Monoid.npow` over `ℝ`. All UNBUILT.
2. **Instantiation channel is only partly covered.** Closed factorial values can be *born* at a call
   site (`factorial_decay 4`, A3) and are then invisible to any term-level grep of the source — this
   is exactly how the published report's own `4!` arose. I swept applications of the 306 genuine
   factorial/choose-bearing declaration names plus 29 Mathlib `Nat.choose`/`Nat.factorial` lemma
   names for a literal argument on the same line, which found A3, A4 and the `monomial 0` of A2, and
   I swept every literal ≥ 2 inside my 323 genuine declarations (max relevant literal: 6). I did
   **not** cover: literals separated from the head by a newline in files outside my 323; local
   *hypothesis* instantiation, e.g. `hAjet 0 (Y x)` at `Euler/GevreyInverseMap.lean:122`, where the
   binder `∀ j y, … (j.factorial : ℝ)^2` is hit at `j := 0` (this one is harmless; a systematic
   sweep of `∀`-bound factorial binders instantiated at literals needs elaborated types, not grep);
   and implicit-argument instantiation.
3. **Structure-field defaults.** If a structure field's type mentions a factorial and an instance
   supplies it at a literal order, my declaration-name sweep would miss it. `fixedCost 6` (A4) was
   found this way only because it sits in a `structure … : Prop` field I happened to read.
4. **`ring`/`nlinarith` certificate widths are unbounded at source level** (E3). I bounded what
   `ring` must produce for the identities I read; I did not bound `nlinarith`'s products.
5. **`ℚ`-typed powers.** `NavierStokes/SlotGeometry.lean:107` puts `6 ^ D` in `ℚ`, which *is*
   kernel-computable. I confirmed `D` is symbolic at that site and in `denominator`/`center`, but I
   did not enumerate every downstream instantiation of `center m D i` to prove `D` is never a
   literal. Even at, say, `D := 40`, `6^40` is 104 bits — an order of magnitude below the 2311 bits
   the report already accepts as inert, so I did not spend the cycles.
6. **Comment-vs-code split.** My scan classifies 872 bare `factorial` tokens, of which the ones I
   sampled in prose (`/-- … factorial estimate … -/`) are comments; I stripped block and line
   comments before every count in the tables above, but the enclosing-declaration map comes from
   `INVENTORY.csv` line ranges, so a factorial mentioned in a doc-comment *inside* a declaration's
   line span could inflate the "declarations containing a genuine factorial term" count (423). The
   892 term-occurrence count and every closed/symbolic verdict are comment-free.
7. **`decide` sites**: I checked only that no `decide` goal mentions a factorial or `Nat.choose`
   (zero do) and read the two `decide`s adjacent to my pow surface
   (`Euler/PacketParameterEnvelope.lean:60,83`, both `Nat.ble` on ≤ 10-bit literals). The other 208
   `decide` sites are `DECIDE_SITES.md` / the `decide-bignum` thread's scope.
