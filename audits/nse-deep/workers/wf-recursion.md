# Worker report: `wf-recursion` — threat vector (1), non-structural recursion outside `EulerProof.lean`

Target: `/home/gsm/.openclaw/workspace/repos/NSE` @ f9e8bc5 (read-only; nothing under that path was modified).
Method: source reading only (no `lake build`; no Mathlib on box). Every line number below was
re-read in the ORIGINAL (non-comment-stripped) file before being cited.

## Scope

| file | lines | decls (thm/def/inductive/structure/abbrev) | read line-by-line | skimmed only |
|---|---|---|---|---|
| `Euler/H6Pressure.lean` | 369 | 25 (18 thm, 7 def) | 25 | 0 |
| `NavierStokes/VolterraAnalyticBounds.lean` | 603 | 56 (37 thm, 16 def, 3 abbrev) | 56 | 0 |
| `Euler/LpSmoothJetField.lean` | 109 | 9 (7 thm, 2 def) | 9 | 0 |
| `NavierStokes/SlowRecursion.lean` | 1306 | 139 | 68 (L510–1306) | 71 (L1–509) |
| `NavierStokes/GlobalSlowProfiles.lean` | 1974 | 194 | 40 (L715–1135) | 154 |
| `NavierStokes/ActivationContinuation.lean` | 2032 | 131 | 14 (L440–740) | 117 |
| `NavierStokes/WeightedODEJets.lean` | 755 | 36 | 29 (L1–420) | 7 |
| **total** | **7148** | **590** | **241** | **349** |

Out-of-scope files read as *required context* for the above: `Euler/EulerProof.lean:3063–3110, 4544–4600`
(`SpatialJet`/`CoefficientJet` inductives, `word_unique`), `Euler/H6PressureConstants.lean:1–50`
(the only place a `termination_by` def in my scope is unfolded), `Euler/SmoothL2CoefficientPath.lean:1–49`
(sole consumer of `Nat.rec`-built `jetField`), `NavierStokes/StressActivation.lean:537–560, 790–830`
(`HistoryRow` inductive + `profileDensity`), `NavierStokes/NilpotentVolterra.lean:380–470`
(the place the `AnalyticField` hypothesis of `VolterraAnalyticBounds` is discharged).

Repo-wide census re-confirmed for my vector: **14** `termination_by` sites total (3 in `H6Pressure`,
2 in `VolterraAnalyticBounds`, 9 in `EulerProof.lean`), **0** `decreasing_by`, **2** hand-rolled
`WellFounded.fix` (`SlowRecursion.lean:946`, `GlobalSlowProfiles.lean:902`), **3** hand-written
recursor applications with explicit motive (`LpSmoothJetField.lean:17`, `ActivationContinuation.lean:517,520`,
`WeightedODEJets.lean:177,187`), **0** `macro/elab/syntax/notation/set_option/axiom/unsafe/partial`
at declaration position anywhere in the repo (the one `partial` grep hit,
`VolterraAnalyticBounds.lean:585`, is the English words "partial sums" inside a docstring).

### Key framing used throughout

A well-founded-recursion **measure cannot be unsound**: if the measure were wrong, the definition would
fail to elaborate, and no theorem would exist. The absence of `decreasing_by` therefore is *not* a risk —
it only means every measure was discharged by the default automation, i.e. each measure is a one-step
`n < n+1` / `List.length` decrease. The real vector-(1) question is whether the **kernel** must *reduce*
`WellFounded.fix` / `Acc.rec` / a recursor to accept a proof. `WellFounded.fix_eq` is a *theorem proved
once in core Lean*; instantiating it costs the kernel nothing and needs no `Acc.rec` reduction, provided the
subsequent `rfl` does not force `whnf` of `fix` itself. I checked exactly this for every site.

## Per-declaration findings

### `Euler/H6Pressure.lean` (3 `termination_by` sites)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `SpatialJet.restrict` | H6Pressure.lean:21–28 | truncate a derivative jet of order `s` to order `q ≤ s` | WF recursion, `termination_by s`; match on `(q, J, hq)`; arm 3 recurses on `lower i : SpatialJet … s' …` with `s = s'+1`, so measure drops `s'+1 → s'`; impossible arm `(_+1, .zero _, h)` is killed by `False.elim (by omega)` from `hq : _+1 ≤ 0` — so the def is total, not vacuous | OK |
| `SpatialJet.wordJet` | H6Pressure.lean:44–53 | from an order-`(q+n)` jet of `f` and a word `w : Fin n → Fin 4`, produce an order-`q` jet of `J.word w` | WF recursion, `termination_by n`, `n+1 → n`; arm 2 pattern `.succ _ lower _` forces the index `q+n+1 = s'+1`; the type-level fix-up is `simpa only [word_succ] using …`, i.e. an `Eq.mpr` cast, not a recursor reduction | OK |
| `CoefficientJet.restrict` | H6Pressure.lean:86–93 | same truncation for coefficient jets | identical shape to `SpatialJet.restrict`, `termination_by s` | OK |
| `sobolevSize` | H6Pressure.lean:59–62 | `‖·‖_{H^q}` as a *total* function: `Classical.choice` of a jet if one exists, else `0` | **explicit junk value**, admitted in the docstring | OK-with-reason, see Kernel-risk §(1)/junk |
| `sobolevSize_eq` | H6Pressure.lean:64–69 | given ANY jet `J` of `f` at order `q`, `sobolevSize … q f = J.sobolevNorm` | `dite_eq_left ⟨J⟩` to enter the `then` branch, then `SpatialJet.norm_unique` | OK |
| `SpatialJet.norm_unique` | H6Pressure.lean:30–41 | two jets over equal fields have equal Sobolev norms | pushes to `sobolevNorm_eq_sum_words` and then `word_unique` termwise | OK |
| `SpatialJet.derivativeJet` | H6Pressure.lean:100–107 | order-`q` jet of `J.word w` whenever `n+q ≤ s` | builds `K := restrict J (q+n) _`, gets `hw : K.word w = J.word w` from `word_unique`, returns `hw ▸ wordJet K w` — note it uses `restrict` **only as an inhabitant**; no equation for `restrict` is ever needed | OK |
| `blockNorm`, `coefficientBlock` | H6Pressure.lean:72–79 | fixed-base-order derivative blocks as finite `Finset.range (q+1)` sums | plain definitions | OK |
| `blockNorm_zero_eq_size` | H6Pressure.lean:187–199 | `blockNorm J q 0 = sobolevSize q f` | again `sobolevSize_eq (restrict J q h)` + `word_unique J (restrict J q h)`; the *value* of `restrict` is never unfolded | OK |
| `blockNorm_succ` | H6Pressure.lean:163–173 | one external order = sum over the 4 children | `cases J` + `simp_rw [hi, levelNorm]` + `Finset.sum_comm` | OK |
| `blockNorm_eq_word_sizes` | H6Pressure.lean:202–225 | block = sum of word sizes | `induction n generalizing s f`; the `zero` arm uses `blockNorm_zero_eq_size`, `succ` uses `wordSnocEquiv` reindexing; `cases J with | zero => omega` closes the impossible index case | OK |
| `triangle_sum_le_product` | H6Pressure.lean:228–264 | `∑_{r≤q} ∑_{l≤r} A l B (r−l) ≤ (∑A)(∑B)` for nonneg `A,B` | genuine `Finset.sum_le_sum_of_injOn` with an explicit injection `(r,l) ↦ (l, r−l)` and `InjOn`/image proofs | OK |
| `base_convolution_bound` | H6Pressure.lean:267–288 | Leibniz sum ≤ `2^q (∑A)(∑B)` | `Nat.choose_le_two_pow` + monotonicity; `2^q` is symbolic, no numeral evaluation | OK |
| `multiply_base_block_bound`, `multiply_blockNorm_bound` | H6Pressure.lean:299–366 | Leibniz product estimate in external order | induction on `n`, truncation-congruence lemmas `coefficientBlock_truncate`/`blockNorm_truncate`; final step is `leibnizConvolution_succ` + `funext` | OK |
| remaining 8 thms (`sobolevSize_nonneg`, `_add_le`, `_sub_le`, `blockNorm_nonneg`, `coefficientBlock_nonneg`, `blockNorm_truncate`, `coefficientBlock_truncate`, `blockNorm_add_le`) | H6Pressure.lean:111–161, 290–296 | monotonicity/nonnegativity plumbing | each supplies a real jet witness (`J.add K`, `J.sub K`) before invoking `sobolevSize_eq` | OK |

Non-vacuity anchor for this whole file: `SpatialJet` (`EulerProof.lean:3064–3070`) is an *indexed* inductive
whose `succ` constructor **carries** `hasDeriv : ∀ i, HasDerivAt (fun t => translation … t) f) (derivatives i) 0`.
So a jet is not a formal symbol — inhabiting it requires actual strong derivatives. `word_unique`
(`EulerProof.lean:4549–4561`) is proved from `HasDerivAt.unique`, so the "choice" in `sobolevSize` is harmless.

### `NavierStokes/VolterraAnalyticBounds.lean` (2 `termination_by` sites, both on *theorems*)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `word` | :52–54 | Volterra word operator, `List Bool → Field → Field` | **structural** (no `termination_by`), compiled via `List.rec`/`brecOn` | OK |
| `losses`, `GoodWord`, `halfLength` | :137–148, :373 | number of derivative letters; "no two adjacent derivative letters"; `(k+1)/2` | structural matches; `GoodWord (true::true::_) = False` | OK |
| `goodWord_losses` | :150–164 | `2 * losses w ≤ w.length + 1` for good words | WF recursion on a **Prop**, `termination_by w.length`, drops by 1 or 2 per arm; `omega` per arm; `true::true::w` arm is `False.elim hw` | OK (Prop-valued `fix`: the kernel only type-checks it, never reduces it) |
| `word_eq_zero_of_not_good` | :172–184 | every non-good word is identically `0`, for arbitrary input field | WF recursion on a Prop, `termination_by w.length`; the payload arm is `adjacent_derivative_letters_zero` at `true::true::w`. Passing `hw` unchanged into the `false::w` and `true::false::w` arms relies on `GoodWord` matcher iota — legitimate | OK |
| `adjacent_derivative_letters_zero` | :131–134 | two consecutive derivative letters annihilate | `derivativeLetter_of_lowZero ∘ derivativeLetter_lowZero`, both traced to `DerivativeShape A₁` (last two rows / first four columns only) — a real structural hypothesis on the matrix, `:57–58` | OK |
| `RadialBound.matrixAction / .radialInverse / .parameterDeriv` | :208–226, :230–267, :305–316 | one row-sum factor `M`; one factorial denominator `r^{k+1}/(k+1)!`; one Cauchy loss `B/δ` | real Bochner/interval integrals, `intervalIntegral.norm_integral_le_abs_of_norm_le`, `Nat.factorial_succ`; the Cauchy step goes through `norm_deriv_le` (:270–297) which is proved from `cauchyPowerSeries` + `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const` | OK |
| `word_radialBound` | :331–370 | `‖word w F‖ ≤ B M^{|w|} δ^{-losses w} r^{|w|}/|w|!` on the shrunk disk | `induction w generalizing ρ`, strip budget `hgap : ρ + losses w * δ ≤ σ` split only over derivative letters | OK |
| `norm_word_le` | :386–436 | uniform bound by `B * wordMajorant (M T) (max 1 (σ−ρ)⁻¹) |w|`, **including** forbidden words | `by_cases GoodWord w`; good branch sets `δ = (σ−ρ)/max 1 halfLength` and uses `losses_le_half`; bad branch rewrites by `word_eq_zero_of_not_good` — this is exactly where the combinatorial gain is cashed | OK |
| `factorial_half_bound`, `half_power_div_factorial_le`, `wordMajorant_le_exponential`, `summable_half_exponential`, `summable_wordMajorant`, `summable_wordLayers` | :440–531 | `(max 1 ⌈k/2⌉)^{⌈k/2⌉} (k/2)! ≤ k!`; majorant ≤ exponential series; summability incl. the `2^k` word count | `Nat.factorial_mul_ascFactorial`, `Nat.pow_succ_le_ascFactorial`, `Real.summable_pow_div_factorial`, reindexing `k ↦ (k % 2, k / 2)` with an injectivity proof by `omega` | OK |
| `wordLayer`, `norm_wordLayer_le`, `summable_norm_wordLayer`, `summable_wordLayer`, `tendstoUniformlyOn_wordLayer` | :534–601 | layer = finite sum over `Fin k → Bool`; absolute + uniform convergence on `Icc 0 T ×ˢ closedBall c ρ` | `norm_sum_le`, `Summable.of_nonneg_of_le`, `tendstoUniformlyOn_tsum_nat` | OK |
| `ha : ∀ v, AnalyticField (word A₀ A₁ v F) T c σ` (hypothesis of :331, :386, :542, :565, :579, :593) | — | analyticity of **every** finite word is an input, not a conclusion | discharged for the intended data by `NilpotentVolterra.raw_word_analytic` (`NilpotentVolterra.lean:410–427`) via `pathWord_holomorphic` + `rawField_pathWord`; so it is not an unbacked assumption | OK (verified downstream) |

### `Euler/LpSmoothJetField.lean` (`Nat.rec` into `Type u`)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `jetFieldAux` | :14–24 | `Nat.rec (motive := fun n => ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V], SmoothL2Field V → SmoothL2Field (Space [×n]→L[ℝ] V))` | This is **not** a large elimination in the dangerous sense: `Nat` is `Type`-valued, so eliminating into any `Sort` is the ordinary rule; the motive is a Π-type landing in `Type u`. The explicit `Nat.rec` is *necessary* because the recursion changes the target type at each step (`V ↦ Space →L[ℝ] V`), so ordinary structural recursion with a fixed `V` cannot express it. The step composes with `continuousMultilinearCurryRightEquiv'` and calls `ih (Space →L[ℝ] V) A.derivative` | OK |
| `jetField_zero` | :29–32 | `jetField 0 A = mapField (curryFin0).symm A` | `:= rfl` — **the kernel must iota-reduce `Nat.rec … 0`** (one step; literal `0` → `Nat.zero`) | KERNEL-RISK (theoretical, 1 iota step) |
| `jetField_succ` | :34–39 | `jetField (n+1) A = mapField (curryRight n).symm (jetField n A.derivative)` | `:= rfl` — kernel must normalise `n + 1` to `Nat.succ n` and take **one** iota step of `Nat.rec`, with `n` symbolic | KERNEL-RISK (theoretical, 1 iota step) |
| `jetField_field_aux` / `jetField_field` | :41–60 | `(jetField n A).field x = iteratedFDeriv ℝ n A.field x` | `induction n` with the ∀-`V` generalisation; `iteratedFDeriv_zero_eq_comp` / `iteratedFDeriv_succ_eq_comp_right`. **This is the honesty anchor**: the `Nat.rec` construction is proved equal to Mathlib's iterated derivative | OK |
| `jetField_toLp`, `continuous_jetField_jet(_aux)` | :62–106 | `L²` class of the jet is `A.jetLp n`; parameter-continuity of all jets | `Lp.ext` + a.e. filter argument; induction with the same ∀-`V` motive | OK |
| consumer `coefficientPath` | `SmoothL2CoefficientPath.lean:32–43` | packages the family into `SmoothCoefficientPath` with `jet_eq n t x` | uses only the propositional `jetField_field`; no reduction of `Nat.rec` at any concrete `n` | OK |

### `NavierStokes/SlowRecursion.lean` (hand-rolled `WellFounded.fix`, L946)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `lowerHistory` | :918–923 | `ℕ → Coefficient (radius … (n−1))`: restrict `previous j hj` for `j < n`, else **`0`** | explicit junk-`0` default | OK-with-reason (see below) |
| `lowerHistory_apply` | :925–929 | for `j < n` the history is the real previous coefficient | `dite_eq_left hj` + `restrict_apply` | OK |
| `recursionStep` | :931–938 | course-of-values step: `0 ↦ base`, `n+1 ↦ step … (n+1) (lowerHistory …)` | structural match on `n` (matcher, i.e. `Nat.casesOn`) | OK |
| `hierarchy` | :942–946 | `Nat.lt_wfRel.wf.fix (recursionStep …) n` | hand-written `WellFounded.fix` over the standard core relation `Nat.lt_wfRel` (not a repo-defined relation) | OK |
| `hierarchy_zero` | :948–954 | `hierarchy … 0 = base` | `unfold hierarchy; rw [WellFounded.fix_eq]; rfl`. After the rewrite both sides contain `fix` only in *identical* positions, so `rfl` is a delta+iota check on the `Nat` matcher with `fix` treated as an opaque atom — **no `Acc.rec` reduction** | OK |
| `hierarchy_succ` | :956–965 | `hierarchy … (n+1) = step … (lowerHistory … (fun j _ => hierarchy … j))` | same idiom; kernel work is: `n+1 → Nat.succ n`, one matcher iota | OK |
| `sequence`, `sequence_profile`, `sequence_zero` | :969–983 | restrict every order to the common core radius; `profile` unchanged (`rfl`) | `restrict` is value-preserving (`restrict_apply`, :128) | OK |
| `previousOmega_congr` | :993–1018 | `previousOmegaDivX h u beta n` depends only on `j < n` | `cases n`; `Finset.antidiagonal k` indices are `≤ k = n−1`; `shiftedAxialFactor` uses only `beta k` | OK — **this is the lemma that proves the junk-`0` branch is never read** |
| `sequence_succ_profile` | :1020–1027 | profile of order `n+1` = profile of `step` applied to the junk-padded history | `rw [sequence_profile, hierarchy_succ]` | OK |
| `sequence_expanded` | :1047–1086 | the `ExpandedEquations` hold at each order with the source rebuilt from the *actual sequence* | `step_expanded` for the padded history `H`, then `previousOmega_congr`, `actualLowerSource_congr`, `baseAtOrderZero` congruence transport `H → A` using only `j < n+1`; finishes `simpa only [… ← sequence_succ_profile]` | OK |
| `sequence_positive_order` | :1090–1106 | `PositiveOrderEquations` at every positive order | `expanded_iff_positiveOrder … (sequence_beta …)` | OK |
| `sequence_beta`, `sequence_axis_zero`, `sequence_average`, `sequence_omega_quotient`, `average_from_equation`, `profile_axis_jet` | :1034–1204 | 5th component is the divergence formula; axis trace vanishes; stored average is the literal integral average | `betaOperator_value`; `step_axis_zero`; FTC via `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` and `mul_left_cancel₀` | OK |
| `LocalHierarchy` / `buildLocalHierarchy` / `exists_local_slow_hierarchy` | :1256–1287 | the hierarchy is an **output** structure (fields: `starts`, `zero_axis`, `beta`, `equations`, `average`) and it is inhabited | each field is one of the theorems above | OK |
| `step`, `stepComponent`, `stepRaw`, `sourceData*`, `betaOperator`, `step_expanded` | :724–856 | one inductive step from the convergent Volterra solution + the divergence formula | `PositiveAxisExistence.positiveSolution_spec/_jointly_smooth/_parity`, `symmetrize`, then `profileSystem_iff_expanded` | UNCLEAR (correctness rests on `PositiveAxisExistence`, outside my scope; nothing here looked circular) |
| index-safety audit of the junk-`0` branch | :549–616, :918–923 | — | I checked every consumer of the history inside `step`: `radialSource` reads `beta k` and `Finset.antidiagonal k` (indices `≤ k = n`), `previousRadialSource (n+1) = radialSource n`, `angularSource`/`axialSource`/`pressureProduct` read `range (n−1)` shifted, i.e. `i+1 ≤ n−1` and `n−(i+1) ≤ n−1`, `priorDiffusion … n` reads `F (n−1)`, `sourceFunctions` reads index `0`. **All accesses are at `j ≤ n`, and `lowerHistory` at order `n+1` is real for all `j ≤ n`.** So the junk `0` is provably unread, and the docstring claim at :916–917 is accurate | OK |

### `NavierStokes/GlobalSlowProfiles.lean` (hand-rolled `WellFounded.fix`, L902)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `Admissible` | :758–768 | per-order data + exterior support + seed agreement inside `|R| ≤ a` and outside `b ≤ R`, plus `zero_data : n = 0 → data = s.base` | structure | OK |
| `previousAxial` / `previousPhi` | :770–776 | junk default is **`s.seedAxial n` / `s.seedPhi n`** (not `0`) for `j ≥ n` | deliberate: index `n` is the *seed to be repaired*, and `StepProperties` overwrites it with `Function.update … n out.data.…` | OK-with-reason |
| `previousBeta` | :778–780 | junk default `0` for `j ≥ n` | only consumed by `previousOmegaDivX … n` | OK |
| `StepProperties` | :786–797 | `beta = betaFromU …`, `pressure = pressureFromSource (pressureSource C (update previousPhi n out.phi) …)`, and 5 vanishing moments | all history reads are `range (n+1)` convolutions with index `n` supplied by `Function.update` | OK |
| `exists_step` | :799–873 | existence of an admissible order-`n` output with those properties | `exists_repaired_order` + `betaFromU` + `pressureFromSource`; exterior preservation via `reconstructed_beta_exterior` / `reconstructed_pressure_exterior` | UNCLEAR (rests on `exists_repaired_order`, :600–692, which I only skimmed) |
| `step` / `step_spec` | :875–882 | `Classical.choose` of `exists_step` and its spec | choice, non-constructive but sound | OK |
| `recursionStep` | :884–897 | `0 ↦` base `Admissible` (all positive-order fields killed by `(Nat.lt_irrefl 0 hn).elim`), `n+1 ↦ step` | structural match on `n` | OK |
| `sequence` | :901–902 | `Nat.lt_wfRel.wf.fix (recursionStep s) n` | as in `SlowRecursion` | OK |
| `sequence_succ` | :907–911 | `sequence (n+1) = step s _ (fun j _ => sequence s j)` | `unfold; rw [WellFounded.fix_eq]; rfl` — same safe idiom: `fix` appears identically on both sides, only the `Nat` matcher must iota-reduce; proof arguments are `Prop`, so kernel proof-irrelevance covers any mismatch | OK |
| `previousOmegaDivX_congr_prefix`, `omegaDivX_congr_prefix`, `pressureSource_congr_prefix`, `cauchy_congr_prefix`, `moments_congr_prefix` | :946–1006 | each source functional depends only on indices `< n` (resp. `≤ n`) | `Finset.antidiagonal`/`Finset.range (n+1)` index bounds (`AxisSourceRegularity.antidiagonal_indices_le`), `Nat.sub_le` | OK — **the junk-branch discharge** |
| `previousSource_sequence`, `updated_sequence_axial`, `updated_sequence_phi` | :1014–1041 | padded/updated history agrees with the real sequence on the used range | `dite_eq_left hj`, `Function.update_self`, `Function.update_of_ne` | OK |
| `profiles_moments`, `profiles_beta_eq`, `profiles_pressure_eq` | :1045–1075 | the five row-moment identities and the beta/pressure formulas hold for the *actual* sequence | `sequence_step_spec` + the congruence lemmas | OK |
| `profiles_zero`, `profiles_*_exterior`, `profiles_inner_*`, `profiles_outer_*` | :913–944 | order-0 = base; compact support; seed agreement | direct field projections of `sequence s n` | OK |
| `schemeFromHierarchy` | :1092–1130 | builds a `Scheme` whose seeds are `cutoffLift` of a `SlowRecursion.LocalHierarchy` | this is the join point between the two WF recursions | OK |

### `NavierStokes/ActivationContinuation.lean` (`HistoryRow.rec` with explicit motive)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `valueIndex` | :516–517 | `HistoryRow.rec (motive := fun _ => Fin 10) 0 2 4 6 8 r` | `HistoryRow` (`StressActivation.lean:539–540`) is a **non-recursive 5-constructor enum**, so `.rec` is plain case analysis; writing `.rec` instead of `match` is stylistic, not suspicious | OK |
| `derivativeIndex` | :519–520 | same with `1 3 5 7 9` | ditto | OK |
| `densityJet` | :505–509 | the 10-entry vector `![U, ∂U, 2Xf, 2X∂f, U(2Xf), ∂U(2Xf)+U(2X∂f), U²−Xf², 2U∂U−2Xf∂f, f², 2f∂f]` | plain `Matrix.vecCons` literal | OK |
| `densityJet_value` | :522–524 | `densityJet p.1 (fieldJet P p) (valueIndex r) = profileDensity P r p` | `cases r <;> rfl`. I checked all five entries by hand against `radialDensity` (`StressActivation.lean:543–548`): mass `U`↔`u`; angular `2Xf`↔`2xf`; transport `U(2Xf)`↔`u(2xf)`; energy `U²−Xf²`↔`u²−xf²`; pressure `f²`↔`f²`. **Correct, and the even indices are exactly the value slots** | OK (kernel does small `Fin`/`Nat` literal work — see §(2)) |
| `densityJet_derivative` | :526–537 | odd slots are the η-derivatives of the value slots | mass by `rfl`; the other four by the `Profiles` fields `parameterPartial_H`, `parameterPartial_transportDensity`, `parameterPartial_energyDensity`, `ReferenceBounds.parameterPartial_square` — i.e. real derivative identities, not `rfl` | OK; I verified the product/chain rules by hand (slot 5 = `∂U·2Xf + U·2X∂f`, slot 7 = `2U∂U − 2Xf∂f`, slot 9 = `2f∂f`) — all correct, and `X = p.1` is a radial coordinate so it is correctly *not* differentiated |
| `profileHistory_parameter_formula`, `profileHistory_difference`, `profileHistory_parameter_difference` | :539–584 | history = initial + primitive; differences are integrals of density differences | `parameterPartial_primitive`, `intervalIntegral.integral_sub` with real integrability side-conditions | OK |
| `field_to_stockJet_transfer` | :625–675 | uniform first-jet closeness ⇒ closeness of all 12 stock entries | `uniform_density_transfer` + `short_integral_bound`; the 12 `fin_cases` arms are matched one-by-one to `(fieldJet 0, fieldJet 1, 5 rows × (value, ∂))` | OK |
| `stockJet_uniform_bound` | :698–740+ | bounded first jet ⇒ bounded stock vector | `uniform_density_bound` (compactness) + `integral_bounded_length` | OK |
| `hold_axis_source_lower` etc. | :262–281 | 4-digit rational inequalities such as `|U| ≤ 4001/1000` | `linarith`/`norm_num` over ℝ | OK (see §(2)) |
| the other 117 decls of this file | — | ODE/continuation machinery | **not read** | see Residue |

### `NavierStokes/WeightedODEJets.lean` (`List.rec` with explicit motive)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `directional`, `jet` | :25–31 | `jet f l = l.foldl directional f` | `List.foldl`, structural | OK |
| `jet_nil`, `jet_cons` | :33–36 | `:= rfl` | one `List.rec`/`foldl` iota step, symbolic tail | OK (see §(1)) |
| `jet_ofFn_reverse` | :111–125 | `jet f (List.ofFn v).reverse p = iteratedFDeriv ℝ n f p v` | induction on `n`, `iteratedFDeriv_succ_apply_right`, `iteratedFDerivWithin_clm_apply_const_apply`. **Honesty anchor: the word calculus is Mathlib's iterated Fréchet derivative** | OK |
| `productJet` | :175–181 | `List.rec (motive := fun _ : List P => (P → Coefficient a b E) → (P → Curve a b E) → P → Curve a b E) …` — full ordered Leibniz expansion | explicit `List.rec` is again *necessary*: the step recurses at **changed** arguments (`directional B v`, `directional z v`), so the motive must be the function type. `List` is a recursive inductive, so this is a genuine vector-(1) site | OK |
| `crossJet` | :185–192 | the proper Leibniz terms (at least one derivative on the coefficient) | same shape, base case `0` | OK |
| `productJet_split` | :194–204 | `productJet = A p ⬝ jet u l + crossJet` | `induction l generalizing A u`; the `cons` arm opens with `change …`, i.e. a **defeq check that forces one `List.rec` iota step** with symbolic tail `l`; then `abel` | KERNEL-RISK (theoretical, 1 iota step) |
| `norm_productJet_le` | :263–295 | `‖productJet A u l p t‖ ≤ 2^{|l|} M B` | induction with `change` (one iota step per level), `norm_add_le`, `pow_succ`. The `2^{|l|}` is symbolic — **no numeral is evaluated** | OK |
| `norm_crossJet_le` | :299–326 | same bound but needing solution jets only of **strictly lower** order (the triangularity) | induction; note hypothesis `hu : ∀ k, k.length < l.length → …` (strict) — this is the non-circularity condition | OK |
| `jet_product` | :231–259 | `jet (A ⬝ u) l = productJet A u l` on `U` | `directional_product` (real `HasFDerivAt.clm_apply` product rule) then induction; last step `rfl` = one iota step | OK |
| `jetSource`, `jet_solution_eq_solution` | :329–388 | every parameter jet of the constructed solution **is** the constructed solution of the triangular variational equation | uses the integral equation `solution_integralEquation`, `jet_clm`, `jet_add`, `productJet_split`, then inverts `equationOperator` via `equationOperator_isInvertible`. Docstring claim "no existence or smoothness of solution jets is assumed" matches the proof: smoothness comes from `contDiffOn_solution_family` | OK |
| `jet_solution_hasDerivWithinAt` | :392–401 | the time derivative of each jet satisfies the variational ODE on `Icc a b` | `rw [jet_solution_eq_solution]` + `solution_hasDerivWithinAt` | OK |
| `norm_solution_le_envelope` … `norm_iteratedFDeriv_odeFamily_le_polynomial` | :415–751 | energy-estimate envelope, then polynomial-in-order bounds | **skimmed only** (7 decls) | see Residue |
| `multilinear_norm_le_of_unit`, `norm_jet_le_iteratedFDeriv` | :129–165 | unit-direction bounds control the full multilinear operator norm (incl. order 0) | `opNorm_le_bound` with the normalisation `w i = ‖v i‖⁻¹ • v i`, correct `v i = 0` case split | OK |

## Kernel-risk assessment

### (1) Recursive inductive types / recursor reduction / `Acc.rec` / WF unfolding — PRESENT, but never on a large or closed term

* **`WellFounded.fix` sites (`SlowRecursion.lean:946`, `GlobalSlowProfiles.lean:902`).** The two unfolding
  proofs (`SlowRecursion.lean:948–965`, `GlobalSlowProfiles.lean:907–911`) are all of the form
  `unfold f; rw [WellFounded.fix_eq]; rfl`. After the rewrite, `WellFounded.fix …` occurs in the *same
  positions* on both sides of the goal, and the only remaining work is delta-unfolding `recursionStep`
  and one iota step of the `Nat` matcher (`0` / `n+1 → Nat.succ n`). **The kernel therefore never needs
  to reduce `Acc.rec` or `WellFounded.fixF` on a canonical `Acc.intro`**, which is the known danger zone.
  `WellFounded.fix_eq` itself is a core theorem instantiated, not recomputed. Cost: O(1) per lemma.
* **`termination_by` sites.** In `H6Pressure.lean` these are three *data* definitions
  (`restrict` ×2, `wordJet`). They are consumed in exactly two ways: (a) as **inhabitants** only
  (`sobolevSize_eq`, `derivativeJet`, `blockNorm_zero_eq_size`, and all downstream users via
  `word_unique`), which needs no unfolding at all; (b) via generated equation lemmas inside an
  ordinary `induction`, at `H6PressureConstants.lean:24,32,34` (`simp [CoefficientJet.restrict, …]`).
  Case (b) is still *propositional*: the equation lemmas were proved once at definition time from
  `WellFounded.fix_eq`; `simp` rewriting with them costs the kernel a proof-term check, not a fixpoint
  reduction. In `VolterraAnalyticBounds.lean` the two `termination_by` sites are **Prop-valued theorems**
  (`:150–164`, `:172–184`) — the kernel type-checks a `fix` term inhabiting a `Prop` and can never be
  asked to reduce it, because nothing projects out of a proof.
* **Hand-written recursor applications.** `Nat.rec` (`LpSmoothJetField.lean:17`) and `List.rec`
  (`WeightedODEJets.lean:177,187`) *do* force real iota reduction, because `jetField_zero`/`jetField_succ`
  (`:32`,`:39`) are `:= rfl` and `productJet_split`/`jet_product` use `change`/`rfl`. But in every case
  the major premise is either the literal `0` or a term of the form `n + 1` / `v :: l` with a **symbolic**
  tail, so exactly **one** iota step is performed per lemma. There is no place in my scope where a
  recursor is applied to a closed term of nontrivial size, so there is no "unroll 10^k times" exposure.
  `HistoryRow.rec` (`ActivationContinuation.lean:517,520`) is on a **non-recursive** 5-constructor enum:
  `cases r <;> rfl` (`:524`) performs 5 single iota steps.
* **Indexed families / structure eta.** `SpatialJet`/`CoefficientJet` (`EulerProof.lean:3064–3079`) are
  `ℕ`- and value-indexed inductive families with a Π-typed recursive field (`lower : ∀ i, … n (derivatives i)`).
  They are *not* nested and *not* Prop-valued, so no large-elimination or nested-inductive-compilation
  subtlety applies. Impossible-index arms are handled either by index unification (`wordJet`) or by an
  explicit `False.elim (by omega)` (`restrict`), and the two proofs I saw that could have leaned on
  vacuity instead close the bad case honestly (`H6Pressure.lean:25`, `:212`, `SlowRecursion.lean:1011`).
  Structure eta is used routinely (`buildLocalHierarchy`, `Admissible` literals) but only for
  non-recursive structures.
* **Junk-value / course-of-values pattern (the mathematically important half of this vector).** Both WF
  recursions feed the step function a *total* history `ℕ → …` padded with a default outside the legal
  range: `0` in `SlowRecursion.lean:918–923` and `GlobalSlowProfiles.lean:778–780`; the **seed at order `n`**
  in `GlobalSlowProfiles.lean:770–776`. In both files the padding is discharged by explicit
  prefix-congruence lemmas that I read: `SlowRecursion.previousOmega_congr:993`,
  `GlobalSlowProfiles.omegaDivX_congr_prefix:946`, `previousOmegaDivX_congr_prefix:966`,
  `pressureSource_congr_prefix:976`, `cauchy_congr_prefix:986`, `moments_congr_prefix:995`,
  and used at `sequence_expanded:1085` / `profiles_moments:1054` / `profiles_pressure_eq:1073`.
  I separately audited every index actually read by the step (`SlowRecursion.lean:549–616`) and found all
  of them at `j ≤ n`. **Conclusion: the junk default is provably never read; the docstring claim at
  `SlowRecursion.lean:916–917` is accurate.** This was the most plausible place for a silent
  "assume the future coefficient is zero" cheat and it is not there.

### (2) Nat/GMP numeral arithmetic — present only in miniature

No `decide` on a nontrivial proposition, no `Nat.pow/div/mod/gcd` on large literals, no `native_decide`
anywhere in scope. Concretely, the complete list of kernel numeral work in my files:

* `VolterraAnalyticBounds.lean:504` — `Nat.mod_lt _ (by decide)` decides `0 < 2`.
* `SlowRecursion.lean:778,779,780,781,789,877,878,879,880,882,883` — `(by decide : (i : Fin 6).val < 4)`
  for `i ∈ {0,1,2,3}`, i.e. `Nat.decLt` on one-digit literals.
* `ActivationContinuation.lean:517,520` + `:524` — `Fin 10` literals `0…9` (`OfNat` → `Fin.ofNat` →
  one `Nat.mod` on one-digit numbers) and, for the `rfl` in `densityJet_value`, up to 9 unfoldings of
  `Matrix.vecCons`/`Fin.cons`.
* `ActivationContinuation.lean:268,273,276,280` — `norm_num`/`linarith` certificates over ℝ containing
  4-digit rationals (`4001/1000`, `4501/500`), plus the constants `110`/`111` at `:610–620`, `:685–694`.
* `H6Pressure.lean:281` (`norm_num` proving `(1:ℝ) ≤ 2`), 27 `norm_num` calls in `GlobalSlowProfiles.lean`,
  5 in `WeightedODEJets.lean` — all on 1–3 digit rationals.
* `2 ^ q`, `2 ^ w.length`, `2 ^ k` appear throughout but always with a **symbolic** exponent
  (`H6Pressure.lean:270`, `VolterraAnalyticBounds.lean:525`, `WeightedODEJets.lean:269`) — the kernel
  never evaluates them.

So the largest integer the kernel must compute with anywhere in my scope has 4 digits. This vector is
effectively absent here; nothing depends on GMP correctness beyond schoolbook arithmetic.

### (3) Custom metaprogramming — absent, confirmed independently for my scope

Zero occurrences of `macro`, `elab`, `syntax`, `notation`, `macro_rules`, `set_option`, `native_decide`,
`axiom`, `sorry`, `unsafe`, `partial` at declaration position in any of my 7 files, and (re-checked)
in the whole repo. The single `partial` grep hit is the phrase "partial sums" in the docstring at
`VolterraAnalyticBounds.lean:585`. The three explicit `.rec` applications are the closest thing to
"hand-rolled elaboration" in my scope, and in each case I identified a *legitimate technical reason*
why the ordinary equation compiler could not be used (the motive must generalise over the changing
type `V`, resp. over the changing function arguments `A`, `u`).

## Escalations

Ranked by how much of the blowup claim rests on them; none of the three is a kernel-exploit finding.

1. **`NavierStokes/GlobalSlowProfiles.lean:600–692` `exists_repaired_order` (and `:799–873` `exists_step`).**
   Question for an expert: does `exists_repaired_order` really produce, for *arbitrary* admissible lower
   data, a repaired order that simultaneously (a) keeps the seed on `|R| ≤ a` and on `b ≤ R`, (b) kills all
   five moments, and (c) preserves compact support — without an implicit smallness or genericity assumption
   hidden in `SmallParameters`/`amplitude_ne`? Everything downstream of `sequence` is `Classical.choose` of
   this one existence statement, so a defect here is invisible to `sequence_succ`. What would settle it:
   read `:600–692` line-by-line and check that the 5-dimensional moment system is solved by a genuine
   finite-rank surjectivity argument (`FiveRowRank.background` at `:749` suggests a rank-5 ansatz) and that
   the correction's support is inside `Ioo a b`.
2. **`Euler/H6Pressure.lean:59–62` `sobolevSize` junk value.** Question: is there any downstream chain
   where a *lower* bound on `sobolevSize` (or a blowup rate) is derived without exhibiting a jet? I checked
   all 60 call sites repo-wide: every equation/bound passes through `sobolevSize_eq` and hence supplies a
   real jet, and the only "naked" uses (`sobolevSize_nonneg` at `H6Pressure.lean:111`,
   `BasePressureCommutator.lean:56`) are in the safe direction. What would settle it definitively: confirm
   that the top-level Euler blowup statement is phrased in terms of a norm whose finiteness/positivity is
   witnessed by `toJet`, not by `sobolevSize` of a field that might have no jet.
3. **`NavierStokes/VolterraAnalyticBounds.lean:331,386,542,565,579,593` — the `ha : ∀ v, AnalyticField (word … v F) T c σ` hypothesis.**
   Question: `raw_word_analytic` (`NilpotentVolterra.lean:410–427`) discharges it for `rawField/rawCoefficient`
   built from `DifferentiableOn` path data on an open `U ⊇ closedBall center ρ`. Is the `σ` used in the
   *bound* lemmas the same radius as the one where holomorphy was established, or is there a silent
   radius mismatch (the bound lemmas consume `σ` and give the conclusion on `ρ < σ`)? What would settle it:
   trace the single call site of `norm_word_le`/`tendstoUniformlyOn_wordLayer` in
   `NavierStokes/PositiveAxisDifferential.lean` and check the radius bookkeeping.
4. (Minor, for completeness.) **`Euler/H6Pressure.lean:21–28,86–93` measure `termination_by s` on an implicit
   binder.** Nothing unsound can follow from a measure, but a reader should confirm that the `s` referred to
   is the jet's order index and not shadowed. Settled by: reading the elaborated `_unary` definition once a
   build exists (`#print` the equations).

## Residue — what I could not check and why

* **No build.** Disk is full and Mathlib is not compiled, so I could not (i) confirm the files actually
  elaborate at f9e8bc5, (ii) `#print axioms` any declaration, (iii) inspect the *generated* WF equation
  lemmas or the elaborated `_unary` forms, or (iv) measure real kernel time. Every statement above about
  what the kernel must reduce is a reading of the tactic script, not an observation of the kernel.
  In particular I could not rule out that a `simp`/`simpa only` call in one of these proofs silently
  invokes a `Nat.rec`/`Acc.rec` reduction through a Mathlib simp lemma.
* **349 of 590 declarations skimmed, not read.** Specifically: `SlowRecursion.lean:1–509` (the
  `AxisFunction`/`Regular` algebra and `complexProfile` plumbing, 71 decls), `GlobalSlowProfiles.lean`
  outside `715–1135` (154 decls, notably `exists_repaired_order:600`, `cutoffLift:350`, and the whole
  `xProfile` transfer section `1134–1974`), `ActivationContinuation.lean` outside `440–740` (117 decls),
  `WeightedODEJets.lean:420–755` (7 decls: the energy envelope and the polynomial-order bounds).
  My verdicts for those regions are "not examined", not "OK".
* **Dependencies deliberately not audited**, since they are other workers' scope or out of scope:
  `PositiveAxisExistence.positiveSolution*` (the Volterra existence engine behind `SlowRecursion.step`),
  `PositiveAxisSystem.ExpandedEquations` / `PositiveOrderEquations` / `profileSystem_iff_expanded`
  (the definition of the equations being solved — a misdefinition there would make everything above
  correct-but-irrelevant), `PositiveOrderMoments.*`, `EulerProof.lean` proper.
* **I did not verify that the two WF hierarchies are actually consumed by the top-level theorem.**
  `SlowRecursion` is imported by 3 files, `GlobalSlowProfiles` by 1 (`AssembledSlowBase.lean`);
  `LpSmoothJetField` reaches the rest of the development only through
  `Euler/SmoothL2CoefficientPath.lean`. Whether those chains reach the headline statement is another
  worker's question.
