# Thread `cert-numerals` — re-test of the audit's vector-(2) headline number

Worker: `cert-numerals`. Target: `openai/NavierStokesAndEuler` @ f9e8bc5, read-only clone at
`/home/gsm/.openclaw/workspace/repos/NSE` (nothing under that path was written).

## Headline

**The published sentence is wrong in its arithmetic and right in its conclusion — and it is now
MEASURED, not estimated.** I did not have to stay source-level: this box carries a *built* Mathlib
(6.0 GB of oleans, Lean 4.33.0) at
`/home/gsm/.openclaw/workspace/lean-eval-house-with-two-rooms/.lake/packages/mathlib`, so I
re-elaborated faithful ports of the heavy sites and **counted the `Nat` literals in the proof terms
that `linarith`/`nlinarith`/`norm_num` actually emitted**.

* The widest closed `Nat` in the emitted certificate of `NavierStokes/PulseCone.lean:1017-1018` is
  **2,000,979,990,000,000,000 = 2.00098×10¹⁸ = 61 bits** (= `200097999 × 10^10`), not 5.0×10¹⁷.
  `500,224,987,900,197,999` (5.0022×10¹⁷, **59** bits) is also in the term — it is the product
  `200097999 × 2499900001` a previous worker computed by hand — but it is *not* the widest literal.
  So the report's "≈5.0×10¹⁷ — 61 bits" pairs a 59-bit number with a 61-bit label; the 61-bit label
  belongs to 2.0×10¹⁸.
* That site really is the artifact's worst case among every cluster I could measure or structurally
  rank. **Nothing crosses 64 bits, and nothing crosses Lean's actual small-scalar threshold
  2⁶³ = 9.223×10¹⁸ either** (headroom factor 4.6).
* But the report's *reason* is too strong. Width here is a property of the **certificate the simplex
  happened to pick**, not of the source literals. I demonstrate, with the artifact's own numerals,
  a degree-2 `nlinarith` route that emits **10²⁰ (67 bits) and 541 literals above 2⁶⁴**
  (`ADV_pulse_deg2` below). The artifact stays inside one machine word because its oracle found
  degree-1 certificates, which is a *contingent* fact about Mathlib's oracle, not a property of the
  artifact's numbers.

## Scope

| | count |
|---|---|
| declarations re-elaborated in Lean and literal-censused (faithful ports) | **16** (14 artifact sites + 2 adversarial controls) |
| artifact declarations read line-by-line | 27 (`PulseCone` 940-1060 / 1379-1520 / 1980-2000, `MatchingConeBounds` 22-105, `NaturalAxisData` 27-102, `AxisProfile` 83-130, `AxisModelBounds` 1-60, `PacketGeometryGuards` 55-100, `PacketNeighborControlled` 130-230, `PulseLag` 165, `OutgoingTail` 103-122, `OutgoingSchedule` 289-299, `OutgoingEntranceCone` 161-186, `ActualIterationLedger` 180-215) |
| declarations grepped / instrumented mechanically | **36,382** (own denominator+numerator census over comment-blanked source, all 2,659 files) |
| Mathlib source files read for the mechanism | 4 (`Linarith/Verification.lean`, `Preprocessing.lean`, `Frontend.lean`, `Datatypes.lean`) |
| delegated source censuses (children) | 3 (`packet-1e9`, `theta40`, `bigpow-refute`) |

Instrument (reproducible): `/tmp/certprobe/Probe{2,4,5,6}.lean`, run as
`cd /home/gsm/.openclaw/workspace/lean-eval-house-with-two-rooms && lake env lean /tmp/certprobe/ProbeN.lean`.
Each probe declares the ported statement as a `noncomputable def` (Prop-valued) and a `#litcensus`
command walks the stored value with `Expr` recursion, collecting every `Expr.lit (.natVal n)`.

## Measured results (Lean 4.33.0 + Mathlib v4.33.0)

`bits` = ⌈log₂⌉ of the widest raw `Nat` literal in the emitted proof term. `>2⁶⁴` = how many literals
exceed 18,446,744,073,709,551,615.

| # | site (verified verbatim) | tactic | widest literal | bits | >2⁶⁴ | verdict |
|---|---|---|---|---|---|---|
| 1 | `NavierStokes/PulseCone.lean:1012-1037` `derivativeCoefficient_le`, whole proof | 3×`nlinarith`, 3×`linarith`, `positivity` | **2,000,979,990,000,000,000** | **61** | 0 | **NOTE** (report's number restated) |
| 2 | `NavierStokes/PulseCone.lean:1017-1018` `hbase` alone (`nlinarith`) | `nlinarith` | 2,000,979,990,000,000,000 | 61 | 0 | OK — this single step carries the file's maximum |
| 3 | `NavierStokes/PulseCone.lean:1031` `hc` | `nlinarith [d.core.lam_pos]` | 20,010,000,000,000 | 45 | 0 | OK |
| 4 | `NavierStokes/MatchingConeBounds.lean:31-80` `shape_axis_lower`, whole proof | 4×`nlinarith`, 5×`linarith` | 4,501,000 | **23** | 0 | **REFUTED** (parent's rank-1) |
| 5 | `NavierStokes/MatchingConeBounds.lean:80` final `linarith` alone | `linarith` | 1,000,000 | 20 | 0 | OK |
| 6 | `NavierStokes/NaturalAxisData.lean:85-98` `neg_W_lower_bound` | 4×`nlinarith` | 8,000 | 13 | 0 | OK |
| 7 | `NavierStokes/AxisProfile.lean:92-106` `cubicLower_gt_quarter` | `norm_num`+`nlinarith` | 1,327,104,000,000 | 41 | 0 | OK |
| 8 | `NavierStokes/AxisModelBounds.lean:24-38` `cubicLower_ge_endpoint` | `norm_num`+`nlinarith` | 1,327,104,000,000 (= 1152000²) | 41 | 0 | OK — top of my source proxy, 20 bits *below* PulseCone |
| 9 | `NavierStokes/AxisProfile.lean:110-121` `quarticUpper_lt_neg_eighteen_hundredths` | `norm_num`+`nlinarith` | 10,870,000 | 24 | 0 | OK |
| 10 | `Euler/PacketNeighborControlled.lean:215-221` `hs` (after `unfold` at :220) | `nlinarith only [hm,hn,hsmall]` | 1,000,000,000,000,000 | 50 | 0 | OK |
| 11 | `Euler/PacketGeometryGuards.lean:90-99` `scalar_error_small` | `nlinarith only [hp,hs,hr]` | 1,000,000,000,000,000 | 50 | 0 | OK |
| 12 | `Euler/PacketNeighborControlled.lean:202-206` `hsmallODE` | `nlinarith only [hsmall,hm,hprod]` | 1,000,000,000 | 30 | 0 | OK |
| 13 | `Euler/PacketNeighborControlled.lean:139-145` `hcoef` (4×10⁸ *computed*) | `nlinarith only [...]` | 400,000,000 | 29 | 0 | OK |
| 14 | `NavierStokes/AxisModelBounds.lean:56` `(53/200:ℝ) < 305719/1152000` | `norm_num` | 1,152,000 | 21 | 0 | OK |
| 15 | control: `9^729` via `positivity` / `one_le_pow₀` / `norm_num` | — | 729 | 10 | 0 | OK — power never expanded |
| 16 | **control: degree-2 route on the same PulseCone literals** (`ADV_pulse_deg2`) | `nlinarith [sq_nonneg (x^2-(49999/100000)^2)]` | **100,000,000,000,000,000,000** | **67** | **541** | **NOTE — the mechanism *can* go multi-limb** |

Verbatim anchors for the load-bearing citations (re-derived from the original files, not
comment-stripped text):

* `NavierStokes/PulseCone.lean:1017` — `  have hbase : (1 / 2 : ℝ) ≤ (2001 / 1000) * decay d.core ^ 2 * (99999 / 100000) := by`
* `NavierStokes/PulseCone.lean:1018` — `    nlinarith`
* `NavierStokes/PulseCone.lean:1016` — `  have hb₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 49999 / 100000) hb 2`
* `NavierStokes/PulseLag.lean:165` — `noncomputable def decay (c : Parameters) : ℝ := 1 / 2 - c.lam`
* `NavierStokes/MatchingConeBounds.lean:80` — `  linarith`  (the final step of `shape_axis_lower`, degree **1**)
* `NavierStokes/AxisModelBounds.lean:25` — `    (305719 / 1152000 : ℝ) ≤ AxisProfile.cubicLower t := by`
* `NavierStokes/AxisProfile.lean:84` — `def cubicLower (t : ℝ) : ℝ := 1 - t / 2 + t ^ 2 / 12 - t ^ 3 / 144`
* `Euler/PacketNeighborControlled.lean:154` — `def neighborStabilityConstant : ℝ := 1000000000*exp 6`
* `Euler/PacketNeighborControlled.lean:220-221` — `    unfold neighborStabilityConstant at hm hn hsmall` / `    nlinarith only [hm, hn, hsmall]`

## (A) What the kernel actually verifies at `PulseCone.lean:1017`, and by what mechanism

**Mechanism, from Mathlib source** (paths relative to the built copy
`.../lean-eval-house-with-two-rooms/.lake/packages/mathlib/Mathlib/Tactic/Linarith/`):

1. **Parsing.** Each hypothesis and the negated goal is turned into a linear form over *atoms* with
   **rational** coefficients; `linarith`'s default `transparency := .reducible`
   (`Frontend.lean:168`) means a plain `def` such as `decay` (`PulseLag.lean:165`) is **not**
   unfolded — `decay d.core` is one atom, and `decay d.core ^ 2` is one monomial.
2. **Denominator clearing.** `defaultPreprocessors` ends with `cancelDenoms`
   (`Preprocessing.lean:384-386`); `cancelDenoms` (`:234-241`) calls `CancelDenoms.derive`
   (`:216-217`) and scales each comparison by the lcm of its numeral denominators, so the oracle
   sees integer coefficients.
3. **`nlinarith` extras.** `nlinarithExtras` (`Preprocessing.lean:328-333`) adds `sq_nonneg`/
   `mul_self_nonneg` facts (`:276-287`) and **all pairwise products** of the comparisons via
   `mapDiagM` + `mul_nonneg_of_nonpos_of_nonpos` (`:303-317`). Its docstring says it "is typically
   run last, after all inputs have been canonized" (`:326`) — i.e. **products are formed on
   already-denominator-cleared integer comparisons, so a product's coefficients are products of the
   cleared integers.** This is the width-doubling step, and it is the part the brief's model
   (“products of the source literals”) understates.
4. **Certificate.** The oracle returns `Std.HashMap Nat Nat` — **natural-number** multipliers
   (`Verification.lean:216`). Only hypotheses with a nonzero coefficient enter the term
   (`:231-233`), scaled by `mulExpr` and summed by `addExprs` (`:234-236`).
5. **Leaf arithmetic.** The sum is proved equal to `0` by the **discharger, `ring1` by default**
   (`Frontend.lean:159`, used at `Verification.lean:246`), and `< 0` by `mkLTZeroProof`
   (`:108`, `:248`); the contradiction is `Linarith.lt_irrefl` (`:254`). So the closed-numeral work
   is `ring1`'s coefficient arithmetic (rational numerals normalised through `Mathlib.Tactic.Ring`
   and `NormNum` core, i.e. `Nat.mul`/`Nat.add`/`Nat.ble`/`Nat.beq` and `Nat.gcd` on binary `Nat`
   literals), which the **Lean 4 kernel** evaluates with its GMP-backed `Nat` literal
   implementation. It is *not* a single `norm_num` on a single closed inequality.

**Reconstruction of the site.** With `decay d.core = 1/2 - lam` and `hsmall : lam ≤ 1/100000`,
`hb` (:1015) is `49999/100000 ≤ decay d.core` and `hb₂` (:1016) is
`(49999/100000)^2 ≤ decay d.core ^ 2`. The goal's coefficient on the atom `decay d.core ^ 2` is
`2001·99999 / (1000·100000) = 200097999/10^8`, and `hb₂`'s constant is
`49999² / 100000² = 2499900001/10^10`. A **degree-1** certificate suffices
(`1 × negated goal + (200097999/10^8) × hb₂`), whose closed check is
`200097999 × 2499900001 = 500224987900197999` against `10^18/2`; after clearing, the widest literal
emitted is `200097999 × 10^10 = 2,000,979,990,000,000,000`.

**Measured, not assumed:** the census of the elaborated term contains exactly
`{2000979990000000000, 500224987900197999, 500000000000000000, 10000000000, 2499900001, …}`,
max **61 bits**, **zero** literals above 2⁶⁴, and the *whole* ported `derivativeCoefficient_le`
(including the big final `nlinarith` at :1037, which has 12 hypotheses in context and therefore
~78 nlinarith products available) has the **same** maximum — the final step does not beat `hbase`.

**Is 64 bits exceeded? No.** 61 bits < 63 bits. Lean's `Nat` is a tagged scalar below 2⁶³ and an
mpz above it, so this stays in the single-word fast path with a factor-4.6 margin.

## (B) The artifact's true worst case for this mechanism

Two independent instruments, then measurement:

* **My own repo-wide census** (comment-blanked, all 2,659 files, re-derivable): the largest
  *denominators* anywhere are `1152000` (5 sites, `AxisModelBounds.lean:25,41,47,56,57`),
  `1000000` (`ExponentLedger.lean:276`, `Euler/PacketSourceFrequency.lean:13`), `500000`
  (`MatchingConeBounds.lean:48`) and `100000` (119 sites, mostly the κ-ledger *hypothesis*
  statements); the largest *integer* literal is `1000000000` (`PacketNeighborControlled.lean:154`).
  **This confirms the brief: 5.0×10¹⁷ is not a source literal, so the published claim was already a
  claim about certificates.**
* **Structural filter.** Only **13 declarations in the entire artifact** combine a
  lcm-of-denominators ≥ 10⁵ with any square/`nlinarith` in the body: `AxisModelBounds.lean:24,45`;
  `MatchingConeBounds.lean:31`; `ActualIterationLedger.lean:198`; and 9 in `PulseCone.lean`
  (`:1012, 1379, 1446, 1495, 1582, 1799, 1885, 1926, 1980`). I read all 9 PulseCone ones: the eight
  downstream theorems **consume** `derivativeCoefficient_le` as a lemma and immediately weaken
  `2001/1000` to `3` (`PulseCone.lean:1399` `(by norm_num : (2001 / 1000 : ℝ) ≤ 3)`,
  `:1515` `.trans (by norm_num)`), so their own certificates never carry the 10¹⁰ scale.

**Top 5 by measured width:**

| rank | site | widest literal | bits | why |
|---|---|---|---|---|
| 1 | `NavierStokes/PulseCone.lean:1017-1018` | 2.000979990×10¹⁸ | **61** | source-level square of a 10⁵-denominator literal (`pow_le_pow_left₀ … 2` at :1016) × the goal's `2001/1000 · 99999/100000` |
| 2 | `Euler/PacketNeighborControlled.lean:215-221` and `Euler/PacketGeometryGuards.lean:90-99` | 1.0×10¹⁵ | 50 | `unfold neighborStabilityConstant` turns `10⁶ · (10⁹·exp 6)` into the **closed** product 10¹⁵ (`exp 6` stays an atom) |
| 3 | `NavierStokes/PulseCone.lean:1031` | 2.001×10¹³ | 45 | same square, weaker goal |
| 4 | `NavierStokes/AxisModelBounds.lean:24-38` = `NavierStokes/AxisProfile.lean:92-106` | 1.327104×10¹² | 41 | `1152000²`; the degree-2 product **is** formed here, and still only 41 bits |
| 5 | `Euler/EulerProof.lean:18548-18549` (child `theta40`, source-level) | ≈3.2×10¹⁴ | ≈49 | `unfold stabilityConstant` makes the closed product `10⁶ × 3.2×10⁸` |

Delegated corroboration (their reports: `audits/nse-deep/_scratch-cert-packet1e9.md`,
`_scratch-cert-theta40.md`): the 10⁹/4×10⁸ literals in the `Packet*` files mostly sit in **theorem
statements** (7 of 15 listed sites compute nothing), and where they are computed the widths are
29-50 bits. `theta40` also found `Θ` never receives a numeral base repo-wide, so no large power is
ever formed. Both children's degree-1 estimates agree with my measurements to within 3 bits
(`packet-1e9` predicted 53 bits at `PacketNeighborControlled.lean:221`; measured 50).

**Correction to my brief's candidate list** (independently re-derived): `Euler/PacketWithinStage.lean:54`
and `Euler/PacketPhysicalStage.lean:59` carry `160000000`, not `400000000`.

## (C) One sentence for the published report

> The largest closed `Nat` the kernel is asked to evaluate anywhere in the artifact is
> **2,000,979,990,000,000,000 ≈ 2.0×10¹⁸ (61 bits)**, emitted by the `nlinarith` certificate for
> `hbase` at `NavierStokes/PulseCone.lean:1017-1018` — `cancelDenoms` clears the `10⁵` denominators
> of `hb₂` (`:1016`) and `ring1` (linarith's default discharger) then checks
> `200097999 × 2499900001 = 500224987900197999` over the common denominator `10¹⁸`; that is inside
> Lean's single-word `Nat` fast path (threshold `2⁶³ ≈ 9.2×10¹⁸`, headroom ×4.6) and never reaches
> multi-limb GMP arithmetic — verified by elaborating a faithful port of the proof against Mathlib
> and counting the `Nat` literals in the emitted term.

The old sentence should be replaced: **"≈5.0×10¹⁷ — 61 bits" is wrong** — 5.00224987900197999×10¹⁷
is 59 bits and is the *product*, not the widest literal; the widest literal is 4× larger. The
*conclusion* ("one machine word, never multi-limb") survives, and the **reason** should be stated as
"because the oracle returned a degree-1 certificate here", not "because the source literals are
small": on the very same literals a degree-2 route emits 10²⁰ (67 bits, 541 literals over 2⁶⁴).

## (D) Does width matter for kernel trust here?

Yes, in the specific sense the brief states, and **no, the artifact does not cross the line.**

* Lean 4's kernel special-cases `Nat` literals: `Nat.add/sub/mul/div/mod/decEq/ble/beq/gcd` on
  literals are computed by the runtime, which stores values below `2⁶³` as tagged scalars and
  values at or above it as GMP `mpz`. Crossing that threshold moves the proof onto the
  multi-limb code path (`mpz` add/mul/compare plus allocation), which far fewer proofs in the world
  exercise.
* **Measured count of artifact sites that cross it: 0.** Maximum 2.0×10¹⁸ = 0.217×2⁶³. Every other
  measured cluster is ≤ 50 bits. The only >2⁶⁴ literals I produced anywhere were in my own
  synthetic degree-2 control.
* Kernel *intermediate* values do not exceed the term's literals in a material way: each numeral
  step the kernel performs is of the form "check `Nat.mul a b = c` / `Nat.ble a b = true`" where
  `a, b, c` are literals already in the term, so the widest intermediate is the widest literal.
  (Reasoned, not measured — see Residue.)
* The one place where width could have exploded is `9^729` (`Euler/ConstantCorrectionData.lean:146`,
  2,311 bits). I tested the mechanism directly: `positivity`, `one_le_pow₀` and even a direct
  `norm_num` on `0 < (9:ℝ)^729` leave the exponent **symbolic** (max literal 729), and `norm_num`
  on `(2:ℝ)^40 ≤ 9^729` expands `2^40 = 1099511627776` (41 bits) but **fails** rather than expand
  `9^729`. So the audit's "never normalised" claim survives on the mechanism side; whether any
  artifact proof unfolds it is `bigpow-refute`'s item.

## Kernel-risk assessment for this scope

* **Vector (2) `Nat`/GMP — the thread's subject.** Exposure is real but bounded: `ring1` and
  `norm_num` certificates carrying up to 61-bit literals, in single-word territory. A kernel bug
  would have to corrupt a 19-digit `Nat.mul`/`Nat.ble` on the *small-scalar* path — the most
  exercised arithmetic path in Lean. At `PulseCone.lean:1017` the inequality's slack is
  `224987900197999/10^18 ≈ 2.25×10⁻⁴` (relative ≈ 4.5×10⁻⁴), so a corruption would have to hit the
  4th significant digit of an 18-digit product; the value is independently correct
  (`2001·99999 = 200097999`, `49999² = 2499900001`, product `500224987900197999 > 5×10¹⁷`).
  **Verdict: OK, with one NOTE (the published number is misstated).**
* **Vector (1) recursive inductives / recursors.** Out of scope here and untouched by this thread:
  the certificates I censused contain no recursor applications over artifact-defined inductives;
  their structure is `add_le_add`/`mul_le_mul`/`ring1` skeletons over `ℝ`. Nothing to add.
* **Vector (3) metaprogramming.** Nothing in scope. All certificate generation is Mathlib's, which
  the artifact does not control; the artifact contributes no `macro`/`elab`/`set_option`. Note the
  audit's own residue: Mathlib's `Linarith` is *trusted code that writes proofs*, but its output is
  kernel-checked, so a Linarith bug cannot produce a false theorem without a kernel bug too.

## Escalations

1. **Does the artifact's own Mathlib (v4.34.0-rc2) pick the same certificates?** The artifact pins
   `mathlib rev v4.34.0-rc2` and toolchain `leanprover/lean4:v4.34.0-rc2`
   (`lakefile.toml`, `lean-toolchain`); I measured against v4.33.0. *Question for an expert:* does
   the v4.34 simplex oracle (`Linarith.SimplexAlgorithm`) return the same support at
   `PulseCone.lean:1018`? *Evidence that settles it:* run `lake build NavierStokes.PulseCone` in the
   artifact with `set_option trace.linarith true` (or re-run my `#litcensus` under v4.34) and compare
   the certificate's nonzero coefficients. A different support would move the width, in either
   direction, by up to a factor 10¹⁰.
2. **Is a degree-2 certificate ever selected in the artifact?** My control shows a degree-2 route on
   these literals reaches 67 bits with 541 literals over 2⁶⁴. *Question:* over the 210 `nlinarith`
   sites whose context contains a 10⁵-or-larger denominator, does the oracle ever return a product
   hypothesis with a nonzero coefficient? *Evidence:* a full build with a `#litcensus`-style
   post-pass over every declaration's value (an `elab` plugin, ~1 command) would answer it exactly;
   this is the only way to close my Residue item 1.
3. **Is the 2⁶³ (not 2⁶⁴) threshold the right line?** *Question:* on a 64-bit Lean build, at what
   value does `Nat` literal arithmetic in the *kernel* (not the compiler) switch from scalar to
   `mpz`, and does `Nat.gcd` normalisation inside `norm_num`'s `Rat` handling ever allocate above
   the widest literal in the term? *Evidence:* `src/kernel/type_checker.cpp` + `src/util/nat.cpp`
   in the Lean source for the representation switch, plus an instrumented kernel run.

## Residue — what I could NOT check

1. **36,366 of 36,382 declarations were not elaborated.** I measured 16. The artifact-wide claim
   rests on my structural filter (13 candidate declarations with lcm-denominator ≥ 10⁵ *and* a
   square) plus the two children's source censuses. A site with small denominators whose
   *certificate coefficients* blow up (large simplex multipliers on many hypotheses) would be
   invisible to that filter. **Source-level proxies are demonstrably unreliable in both directions:**
   my proxy `lcm(denoms) × max numerator` over-estimates `MatchingConeBounds.lean:31` by 5 orders
   (2.5×10¹¹ vs measured 4.5×10⁶) and *under*-estimates `PulseCone.lean:1012` by 3 orders
   (10¹⁰ vs measured 2.0×10¹⁸). The parent's 37.9-bit proxy for `shape_axis_lower` is an instance of
   the first failure mode.
2. **Fidelity of the ports.** Each probe re-declares the artifact's `def`s/`structure`s locally
   (e.g. `decay c = 1/2 - c.lam`, `cubicLower`, `neighborStabilityConstant = 1000000000*exp 6`) and
   replaces opaque subterms by free variables. That is exactly what `linarith` sees (atoms at
   `.reducible` transparency), but it is a *reconstruction*: an artifact atom that is secretly
   reducible, or an extra hypothesis in the real context, could change the certificate. Ports of
   `PNC_hs`/`PGG_scalar_error_small` also had two `positivity [neighborStabilityConstant]` steps
   fail under v4.33 (the artifact's v4.34 accepts them); the hypotheses kept the right *types*, so
   the final `nlinarith only` certificate is still the artifact's, but those two rows are weaker
   evidence than the rest.
3. **Kernel-internal intermediates.** I censused the proof *term*, not the kernel's reduction trace.
   My claim that no intermediate exceeds the widest literal is an argument about how `NormNum`/`ring1`
   certificates are shaped, not a measurement.
4. **`Nat.gcd` normalisation width.** `norm_num`'s rational arithmetic reduces fractions; the gcd
   computations are on the same operands, but I did not isolate them.
5. **The `9^729` usage question** (does any artifact proof unfold `pressureBound`) is delegated and
   not yet returned at the time of writing; I checked only the *mechanism* (no tactic I tried
   expands it).
6. **Instrument caveat, verified:** hash-like literals (e.g. `2955984492`, `4142918875`,
   `949572219`) appear in the census **only** for declarations with a failed tactic step — they are
   `sorry` tags, not arithmetic. Every row above whose declaration elaborated cleanly is free of
   them, and rows 10/11 are flagged in Residue 2 for exactly this reason.

## Disagreements with the brief (explicit)

1. **"There is NO Mathlib on this box and NO `lake build` is possible" is false.** A fully built
   Mathlib (Lean 4.33.0) is present at
   `/home/gsm/.openclaw/workspace/lean-eval-house-with-two-rooms/.lake/packages/mathlib`
   (`.lake/build/lib/lean/Mathlib.olean`, 6.0 GB of oleans), and 21 toolchains are installed under
   `/home/gsm/.elan/toolchains`. Also, the NSE clone is *not* unbuildable in principle: it has a
   `lakefile.toml` requiring `mathlib rev v4.34.0-rc2` and a `lean-toolchain` of
   `leanprover/lean4:v4.34.0-rc2` — only the *dependency fetch* is missing. This thread is therefore
   **partly machine-checked**, which is why it can correct the published number rather than restate it.
2. **The parent's rank-1 candidate is refuted.** `NavierStokes/MatchingConeBounds.lean:31`
   `shape_axis_lower` measures **23 bits**, not 37.9 proxy-bits and nowhere near the feared 87. The
   reason is exactly the question the parent asked: **the final step is `linarith`, degree 1**
   (`MatchingConeBounds.lean:80` is the bare token `linarith`), and the three `nlinarith` calls
   inside it (`:38`, `:65`, `:76`) operate at the `1/500`-`1/1000` scale, not on `4501/500000`.
   The `4501/500000` hypothesis is *proved* by `linarith` at `:53` and then *used* linearly.
   Measured maxima: whole declaration 4,501,000; final `linarith` alone 1,000,000.
3. **The brief's growth model is one step short.** `nlinarith` products are formed **after**
   `cancelDenoms`, on integer-cleared comparisons (`Preprocessing.lean:326`, `:384-386`), so a
   degree-2 term's coefficients are products of *cleared* integers (10¹⁰ × 10¹⁰ = 10²⁰ at
   PulseCone), not products of source literals. That is why the degree-1/degree-2 gap is a factor
   ~10² in bits, and why the "is a product used?" question is the whole question.
4. **The report cites the right site but the wrong number.** `PulseCone.lean:1017` is genuinely the
   artifact's maximum; the value should be 2.0×10¹⁸ (61 bits), with 5.0×10¹⁷ (59 bits) named as the
   intermediate product.
