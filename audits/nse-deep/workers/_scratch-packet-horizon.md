# Question D — the finite positive lifespan `Tstar` of the Euler blowup claim
Read-only audit of /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5).
No Mathlib build available: NOTHING was compiled. All claims are source-level reads (statements + actual
proof terms/tactics). Nothing under the repo was modified.

## Scope

READ IN FULL (every declaration, statement and proof):
- `Euler/PacketBaseGuardScales.lean` (79 lines, 8 decls: 3 defs + 5 theorems)
- `Euler/PacketInductionScales.lean` (221 lines, 12 decls: 5 defs/structures + 7 theorems)
- `Euler/OrdinaryEulerLifespan.lean` (86 lines, 1 def + 1 structure + 8 decls)
- `Euler/PacketFiniteLifespan.lean` (60 lines, 9 decls)
- `Euler/EulerFiniteLifespan.lean` (50 lines, 5 decls)
- `Euler/Solution.lean` (75 lines, 3 decls)

READ IN PART (targeted, for the chain hops and the X/J guards):
- `Euler/PacketInductionScaleBounds.lean:1-40` (`x_one`,`x_pos`,`j_one`)
- `Euler/PacketInfiniteConstruction.lean:1-77` (`constructionScales`, `packets`)
- `Euler/EulerSingularity.lean:100-153` (second headline form)
- `Euler/PacketStageLocalExistence.lean:25-60` (`Stage.exists_local_evolution`)
- `Euler/PacketCommonScaleChoice.lean:1-70` (`exists_common_guards`: source of `8 ≤ X₀`, `3 ≤ J`)
- `Euler/EulerProof.lean:20240-20276` (`base_horizon_tendsto_zero`, `base_core_volume_cost_tendsto_zero`)
- `Euler/PacketSourceScaleSequence.lean:25-50`, `Euler/PacketSourceScaleChoice.lean:226-233`
  (`timeWidth`, `previousShear`, `scaleSequence`)
- `ComparatorChallenges/Euler.lean:85-186` (challenge statements; both carry `sorry`)

## Per-declaration findings

### Euler/PacketBaseGuardScales.lean

1. `baseHorizon` (:14) — `def baseHorizon (J : ℕ) (X : ℝ) : ℝ := 6*(J:ℝ)^2*X^(-498:ℝ)`.
   `X^(-498:ℝ)` is `Real.rpow` (REAL exponent, `Monoid.npow` is not used): the kernel never computes a
   498-fold product. For `X > 0` this is `exp (-498 * log X) > 0`. For `X ≤ 0` Lean's rpow junk
   convention gives `0` (X=0) or `exp(log|X|·y)·cos(...)`-free junk-defined value — hence positivity
   REQUIRES a hypothesis; see (4). Verdict [OK].
2. `baseRadius` (:16) — `X^(-1000:ℝ)`, same rpow remark. [OK]
3. `baseGuardCost` (:18-20) — the local-existence/coercivity cost
   `K*(S²/2)+Be*S+Cboundary*(CM*X^1000+2)*r³*S` with `S = baseHorizon`, `r = baseRadius`. Note
   `X^1000` here is a NAT exponent on a REAL base (`Monoid.npow`), still no kernel numeral arithmetic. [OK]
4. `baseHorizon_pos` (:22-26) — `(hJ : 1 ≤ J) (hX : 0 < X) → 0 < baseHorizon J X`. Proof: derive
   `hj : (0:ℝ) < J` by `exact_mod_cast (show 0 < J by omega)`, `unfold baseHorizon`, `positivity`.
   `positivity` needs `0 < X` for the rpow factor and `hj` for `(J:ℝ)^2`; both are in the local context,
   so the two hypotheses are genuinely load-bearing (statement is not vacuous, and NOT provable without
   `hX`, since `X = 0` would give `baseHorizon = 0`). [OK]
5. `baseRadius_pos` (:28) — `rpow_pos_of_pos hX _`. [OK]
6. `baseHorizon_eq_timeWidth` (:30-40) — `0 < X → baseHorizon J X = 2*timeWidth J X 0`.
   I re-derived by hand: `timeWidth J X 0 = 3*scaleSequence J X 1*scaleSequence J X 0 / sqrt (previousShear J X 0)`
   (`Euler/PacketSourceScaleSequence.lean:42-43`) `= 3*((J+0:ℕ):ℝ)^2*X*X / sqrt (X^1000)`
   (`scaleSequence_succ`, `scaleSequence_zero`, `previousShear 0 = X^1000` at
   `Euler/PacketSourceScaleSequence.lean:30-31`) `= 3*J²*X²/X^500 = 3*J²*X^(-498)`. Twice that is exactly
   `baseHorizon`. Proof mechanism is honest: `sqrt (X^1000) = X^500` from `pow_mul` + `Real.sqrt_sq`
   (:32-34), then `rpow_neg`, `rpow_ofNat`, `field_simp [hX.ne']`, `ring`. The `-498` matches the
   manuscript exponent `2 - 1000/2`. [OK]
7. `baseHorizon_tendsto_zero` (:42-45) — `Tendsto (baseHorizon J) atTop (𝓝 0)`. Proof imports
   `base_horizon_tendsto_zero (J:ℝ)` (`Euler/EulerProof.lean:20257-20261`, statement
   `Tendsto (fun x => 6*J^2*x^(2-1000/2:ℝ)) atTop (𝓝 0)`, itself proved from
   `tendsto_rpow_neg_atTop (0 < 498)`), and rewrites `(2-1000/2:ℝ) = -498` by `norm_num`.
   Real analysis, no numeral recomputation. [OK]
8. `baseRadius_tendsto_zero` (:47-48) — `tendsto_rpow_neg_atTop (0 < 1000)`. [OK]
9. `baseGuardCost_tendsto_zero` (:50-63) — sum/product of the three limits, glued with
   `convert! h using 1; funext X; unfold ...; ring`. Uses `base_core_volume_cost_tendsto_zero`
   (`EulerProof.lean:20265`, exponent bookkeeping `1000 + (-1000)*3 + (-498) = -2498`). I checked that
   identity by hand: correct. [OK]
10. `eventually_base_guards` (:65-77) — for `1 ≤ J`, `0 < T₀`: eventually in `X → ∞`,
    `1 < X ∧ 0 < baseHorizon J X ∧ baseHorizon J X ≤ T₀ ∧ 0 < baseRadius X ∧ baseRadius X ≤ 1/4 ∧
     baseGuardCost … ≤ 1/2`. Proof: `filter_upwards` on `eventually_gt_atTop 1` and three
    `Tendsto.eventually_le_const` instances, then `hXp : 0 < X` from `1 < X` and the two positivity
    lemmas. This is a genuine `X → ∞` limit argument; it CARRIES the positivity `0 < baseHorizon`
    alongside the smallness. [OK] — and note the conjunct order, used below.

### Euler/PacketInductionScales.lean (the `Scales` record and its inhabitant)

11. `geometryConstant` (:22), `geometryConstant_one` (:24-27) — `1 ≤ neighborStabilityConstant*frameConstant^2`
    from imported one-bounds. [OK]
12. `activationMargin` (:29-30), `activationMargin_pos` (:32-34), `activationMargin_small` (:36-43) —
    `1/(32*(activationConstant … +1))`, `positivity [hessian_nonneg]`, `field_simp; linarith`. [OK]
13. `correctionCostSpec` (:45-60) — a `CostSpec` of literal small rationals, side goals by `norm_num`
    (`d_le_two`, `a_nonneg`, `a_lt_B`, `a_le_N`, `b_pos`, `C_pos`). Tiny numerals. [OK]
14. `correctionCost_eq` (:62-68) — `simp only [...] ; congr 1; ring`. [OK]
15. `extraCost` (:70-73), `initialIncrement` (:75-77), `pressureIncrement` (:79-81) — plain defs. [OK]
16. `structure Scales (c B : ℝ)` (:83-112) — the ONE global scale record: `J D : ℕ`, `X δ : ℝ`, with
    `stage_large : 3 ≤ J` (:88), `base_power : 2000 ≤ D` (:89), `x_large : 8 ≤ X` (:90),
    `delta_pos : 0 < δ` (:91) … `time_small : baseHorizon J X ≤ 1` (:110),
    `localized : baseGuardCost … ≤ 1/2` (:111-112).
    CRITICAL OBSERVATION: the record does NOT carry `0 < baseHorizon J X` as a field. It does not need
    to: `x_large : 8 ≤ X` (:90) and `stage_large : 3 ≤ J` (:88) give `x_pos : 0 < S.X`
    (`Euler/PacketInductionScaleBounds.lean:19-20`, via `x_one : 1 ≤ S.X`) and `j_one : 1 ≤ S.J`
    (:21, `omega` from `3 ≤ J`), hence `baseHorizon_pos S.J S.j_one S.x_pos` is available anywhere a
    `Scales` is in scope. So the record CANNOT be instantiated with a degenerate `X ≤ 0`. [OK]
17. `exists_base_power` (:114-121) — `∃ D, 2000 ≤ D ∧ (firstFrequencyPower:ℝ) < D*(theta/100)` via
    `exists_nat_gt` and `max 2000 d`. `theta = 1/1000000` (`Euler/PacketSourceFrequency.lean:13`);
    `0 < theta/100` by `norm_num [theta]` — an ℝ numeral certificate of size ~1e8, trivial for the
    kernel (binary Nat, not a `Nat.pow` unfolding). [OK]
18. `exists_scales (c B : ℝ) (hc : 0 ≤ c) : Nonempty (Scales c B)` (:123-193) — THE inhabitant.
    Mechanism: `exists_base_power` for `D`; `EulerPacketCommonScaleChoice.exists_common_guards`
    (`Euler/PacketCommonScaleChoice.lean:18-32`) for `J` with `3 ≤ J` and a choice function producing
    `X₀ δ` with `8 ≤ X₀`; a min-of-four `η` with `positivity`; then `hevent` (:150-171), an `atTop`
    eventual conjunction obtained by `filter_upwards` on `eventually_ge_atTop X₀`,
    `eventually_ge_atTop (48000:ℝ)`, `eventually_firstScaleGuards`, two `eventually_all_frequency`,
    `hp.eventually …`, and — the hop that matters here —
    `eventually_base_guards J (by omega) (initialCoefficientCost+1) (initialCoefficientCost+1)
     gradientConstant boundaryLocalizationC2 1 zero_lt_one` (:164-165), i.e. `eventually_base_guards`
    INSTANTIATED AT `T₀ := 1` with the proof `zero_lt_one : (0:ℝ) < 1`.
    Then `refine ⟨hfloor,hlarge,hfirst,hfrequency,?_,hb.2.2.1,hb.2.2.2.2.2⟩` (:167): `hb.2.2.1` is the
    third conjunct of `eventually_base_guards`, i.e. exactly `baseHorizon J X ≤ T₀ = 1`, and
    `hb.2.2.2.2.2` is `baseGuardCost … ≤ 1/2`. Finally `X` is extracted by `hevent.exists` (:172) and
    `time_small := htime` (:193).
    ANSWER TO SUB-QUESTION 2: `baseHorizon J X ≤ 1` is genuinely PROVED by real `rpow` asymptotics
    (`X^(-498:ℝ) → 0` as `X → ∞`, via `tendsto_rpow_neg_atTop`), NOT by any numeral computation the
    kernel must perform. No explicit numeric `X` is ever exhibited: `X` comes from
    `Filter.Eventually.exists`, so the whole scale choice is non-constructive but honest. [OK]
19. `Scales.initial_series` (:199), `Scales.pressure_series` (:205), `Scales.stage` (:211-218) —
    `convert`/`ring` glue and one imported `stage_guards_at`. Not on the `Tstar` path. [OK]

### Euler/OrdinaryEulerLifespan.lean (where `Tstar` is actually born)

20. `HasEulerEvolution A T` (:13-14) — `∃ hT : 0 < T, ∃ U : Evolution T hT.le, U.velocity ⟨0,…⟩ = A`.
    NOTE: positivity of `T` is packed INSIDE the predicate. That is what later supplies `0 < Tstar`. [OK]
21. `HasEulerEvolution.restrict` (:16-20), `.lt_of_failure` (:22-25) — restriction and the
    "no solution at `B` ⇒ every solvable `T` is `< B`". [OK]
22. `structure FiniteLifespan A` (:29-33) — `duration`, `duration_pos : 0 < duration`,
    `shorter : ∀ S, 0 < S → S < duration → HasEulerEvolution A S`,
    `maximal : ∀ S, duration < S → ¬ HasEulerEvolution A S`. [OK]
23. `exists_finite_lifespan` (:35-54) — given `0 < B`, a local solution, and failure at `B`, builds
    `L` with `L.duration ≤ B`. Mechanism: `times := {T | HasEulerEvolution A T}`, nonempty from
    `hlocal`, bounded above by `B` via `lt_of_failure`; `duration := sSup times`;
    `duration_pos := hT.choose.trans_le (le_csSup hbdd hT)` (:42-44) — i.e. the positivity of the
    lifespan is the positivity of the LOCAL existence time, transported to the sup;
    `L.duration ≤ B` by `csSup_le hne hbound`. `sSup` on a nonempty bounded-above set of reals is not
    a junk value. [OK]
24. `FiniteLifespan.evolution` / `evolution_initial` / `evolution_agrees` / `endpoint_of_bounded_gradient`
    (:60-83) — `Exists.choose`-based selection plus an imported endpoint theorem. [OK]

### Euler/PacketFiniteLifespan.lean, Euler/EulerFiniteLifespan.lean, Euler/Solution.lean

25. `initialDatum` (:18) — `Stage.initialDataLimit packets le_rfl le_rfl`. [OK]
26. `initialDatum_Hm` (:20-25), `initialDatum_local` (:27-29) — the local existence for the limit datum,
    from `Stage.exists_local_evolution`. Its statement
    (`Euler/PacketStageLocalExistence.lean:39-41`) is
    `∃ L, ∃ hL : 0 < L, L ≤ baseHorizon S.J S.X/12 ∧ ∃ E : Evolution L hL.le, …`, and its proof
    starts `hT : 0 < T := div_pos (baseHorizon_pos S.J S.j_one S.x_pos) (by norm_num)`
    (`:42-43`). So `0 < baseHorizon` is USED to produce the positive local time. [OK]
27. `initialDatum_no_base` (:31-36) — no Euler evolution on the FULL `baseHorizon`. [OK]
28. `initialDatum_solenoidal` (:38-40), `initialDatum_divergence` (:42-44). [OK]
29. `initialDatum_finite_lifespan` (:46-52) — `∃ L, L.duration ≤ baseHorizon …`, by
    `exists_finite_lifespan initialDatum (baseHorizon …)
     (baseHorizon_pos constructionScales.J constructionScales.j_one constructionScales.x_pos)
     initialDatum_local initialDatum_no_base`. **This is the site where `0 < baseHorizon` enters the
    spine as an explicit argument (`:51`).** [OK]
30. `lifespan` (:54) — `initialDatum_finite_lifespan.choose`; `lifespan_le_base` (:56-58) —
    `.choose_spec`. [OK]
31. `lifespan_le_one` (`Euler/EulerFiniteLifespan.lean:24-25`) —
    `lifespan_le_base.trans constructionScales.time_small`. One-line, exact. [OK]
32. `exists_compact_smooth_finite_lifespan` (`EulerFiniteLifespan.lean:39-50`) and
    `Euler.exists_compact_smooth_euler_singularity` (`Euler/Solution.lean:43-69`) — both instantiate
    `Tstar := lifespan.duration`, `0 < Tstar := lifespan.duration_pos`,
    `Tstar ≤ 1 := lifespan_le_one` (`Solution.lean:59`). [OK]
33. `EulerPacketInduction.exists_compact_smooth_euler_singularity`
    (`Euler/EulerSingularity.lean:133-151`) and `initialDatum_singularity` (:115-127) — same two
    ingredients `lifespan.duration_pos, lifespan_le_one` (:126, :148). [OK]

## The `Tstar` chain (explicit hop list)

1. `Euler/Solution.lean:44,46` — headline `∃ … (Tstar : ℝ) …, 0 < Tstar ∧ Tstar ≤ 1 ∧ …`.
2. `Euler/Solution.lean:57` — `Tstar := lifespan.duration`.
3. `Euler/Solution.lean:59` — `0 < Tstar := lifespan.duration_pos`; `Tstar ≤ 1 := lifespan_le_one`.
4. `Euler/PacketFiniteLifespan.lean:54` — `lifespan := initialDatum_finite_lifespan.choose`
   (`FiniteLifespan initialDatum`).
5. `Euler/PacketFiniteLifespan.lean:46-52` — `initialDatum_finite_lifespan :
   ∃ L, L.duration ≤ baseHorizon constructionScales.J constructionScales.X`, built by
   `exists_finite_lifespan` with `hB := baseHorizon_pos … j_one … x_pos` (`:51`).
6. `Euler/OrdinaryEulerLifespan.lean:35-54` — `exists_finite_lifespan`: `duration := sSup {T | HasEulerEvolution A T}`;
   `duration_pos` from `hlocal`'s own `0 < T` (`:42-44`); `duration ≤ B` by `csSup_le` (`:49`).
   Positivity source: `Euler/PacketFiniteLifespan.lean:27-29` `initialDatum_local`, i.e.
   `Euler/PacketStageLocalExistence.lean:39-43` (`0 < L ≤ baseHorizon/12`, itself from `baseHorizon_pos`).
7. `Euler/EulerFiniteLifespan.lean:24-25` — `lifespan_le_one := lifespan_le_base.trans constructionScales.time_small`.
8. `Euler/PacketFiniteLifespan.lean:56-58` — `lifespan_le_base : lifespan.duration ≤ baseHorizon …`.
9. `Euler/PacketInductionScales.lean:110` — `Scales.time_small : baseHorizon J X ≤ 1` (a record FIELD).
10. `Euler/PacketInfiniteConstruction.lean:68-70` — `constructionScales := Classical.choice (exists_scales …)`
    (choice on a type proved `Nonempty`, not on a possibly-empty type).
11. `Euler/PacketInductionScales.lean:164-165,167,172,193` — `time_small` discharged from
    `eventually_base_guards … (T₀ := 1) zero_lt_one`, conjunct `hb.2.2.1`, `hevent.exists`.
12. `Euler/PacketBaseGuardScales.lean:65-77` — `eventually_base_guards`: `filter_upwards` on
    `(baseHorizon_tendsto_zero J).eventually_le_const hT₀` (`:72`).
13. `Euler/PacketBaseGuardScales.lean:42-45` → `Euler/EulerProof.lean:20257-20261` →
    `tendsto_rpow_neg_atTop (0 < 498)`. Pure real `rpow` asymptotics.
14. `Euler/PacketBaseGuardScales.lean:14` — `baseHorizon J X = 6*(J:ℝ)^2*X^(-498:ℝ)`, with `J ≥ 3`
    (`PacketInductionScales.lean:88`) and `X ≥ 8` (`:90`) fixed by the record.

Net numeric envelope actually proved: `baseHorizon/12 ≤ Tstar ≤ baseHorizon ≤ 1` with
`baseHorizon = 6 J² X^(-498) > 0`, `J ≥ 3`, `X ≥ 8` — hops 6 (lower) and 8+9 (upper).

## Verdict on sub-question 4 (junk / degeneracy)

`Tstar` is provably FINITE and POSITIVE; a degenerate `Tstar = 0` is NOT accepted anywhere:
- `0 < Tstar` is a structure FIELD (`FiniteLifespan.duration_pos`, `OrdinaryEulerLifespan.lean:31`),
  discharged (`:42-44`) from a genuine local solution whose time is `> 0`.
- The rpow junk hazards are all fenced: `X^(-498:ℝ)` is only ever positivity-analysed under
  `0 < X`, which in the spine comes from the record field `x_large : 8 ≤ X`
  (`PacketInductionScales.lean:90` → `PacketInductionScaleBounds.lean:19-20`). There is no `0^0`, no
  `rpow` of a nonpositive base, and no division by a possibly-zero quantity on this path
  (`baseHorizon/12` divides by the literal `12`; `12/baseHorizon` appears elsewhere but always with a
  `baseHorizon_pos` in hand, e.g. `Euler/PacketInductionStage.lean:91-92`).
- An "unconstrained `X` making the horizon 0" is impossible twice over: (a) `X` is not a parameter of
  the headline, it is fixed inside `constructionScales` with `8 ≤ X`; (b) even if it were 0, the chain
  would FAIL to build, because `exists_finite_lifespan` demands `0 < B`
  (`PacketFiniteLifespan.lean:51` supplies it) and `Stage.exists_local_evolution` needs
  `0 < baseHorizon/12` (`PacketStageLocalExistence.lean:43`). So `0 < baseHorizon` IS load-bearing in
  the spine, not merely decorative.
- `Classical.choice` (`PacketInfiniteConstruction.lean:69`) is applied to `Scales …`, proved
  `Nonempty` by `exists_scales` — not a choice out of a possibly-empty-in-spirit type.
- Honest limitation, not a defect: `Tstar` has NO effective positive lower bound in the statement.
  `X` is produced by `Filter.Eventually.exists`, so `baseHorizon` is not a computable numeral and
  `Tstar ∈ (0,1]` is all that is claimed. The blowup content is carried by the limsup/vorticity
  clauses, not by the size of `Tstar`.
- `Tstar ≤ 1` is NOT what makes the theorem non-vacuous, and it is not achieved by cheating: it is
  `Tstar ≤ baseHorizon ≤ 1` where the second step is the record field `time_small`.

## Kernel-risk (files read in full)

Scanned all 6 full-read files plus the 4 chain files (`PacketInfiniteConstruction`,
`PacketStageLocalExistence`, `PacketCommonScaleChoice`, `EulerSingularity`) for
`decide|native_decide|.rec|Nat.rec|Acc.rec|termination_by|decreasing_by|WellFounded|sorry|axiom|macro|elab|syntax|set_option|unsafe|partial`:

- `native_decide`: 0. `axiom`: 0. `sorry`: 0. `macro/elab/syntax/set_option/unsafe/partial`: 0.
  `termination_by`/`decreasing_by`: 0. `WellFounded`/`Acc.rec`: 0. Explicit `.rec`/`Nat.rec`: 0.
  So NO custom metaprogramming finding in my scope.
- `decide`: exactly 2 occurrences, both tiny and inside `zero_pow` side goals —
  `Euler/PacketBaseGuardScales.lean:58` (`(by decide : 2 ≠ 0)`) and `:59` (`(by decide : 3 ≠ 0)`).
  `Nat.decEq` on one-digit literals. Negligible. [OK]
- Big literals — ALL of them are REAL-side, none is a `Nat.pow`/`decide` the kernel must grind:
  - `X^(-498:ℝ)` (`PacketBaseGuardScales.lean:14`), `X^(-1000:ℝ)` (`:16`), `(2-1000/2:ℝ) = -498`
    (`:44`), `(0:ℝ) < 1000` (`:48`), `-2498` bookkeeping (`EulerProof.lean:20272`): `Real.rpow` with a
    real exponent — the kernel does no exponentiation, only linear-arith numeral certificates.
  - `X^1000` (`PacketBaseGuardScales.lean:20,32,33`) and `X^(2000:ℕ)` (`EulerProof.lean:20252`):
    `Monoid.npow` on a REAL base. The only kernel numeral work is the `rfl` side of
    `rw [← pow_mul]`, i.e. checking `500*2 = 1000` and `1000*2 = 2000` in binary `Nat`. Trivial.
  - `2000 ≤ D` (`PacketInductionScales.lean:89,114,119,121`), `48000 ≤ X` (`:151,159`),
    `1000000*geometryConstant` (`:94,129,136,141`), `1000000*K` (`PacketCommonScaleChoice.lean:41,45-47`),
    `1010*frequencyPower` (`BasePacketFrequencyCost.lean:39`), `theta = 1/1000000`
    (`PacketSourceFrequency.lean:13`, used by `norm_num [theta]` at `PacketInductionScales.lean:117`):
    literals in `≤`/`<`/`*` over ℝ or ℕ, discharged by `norm_num`/`omega`/`linarith`/`nlinarith`
    certificates whose numerals are ≤ ~1e8. No exponentiation, no `Nat.gcd`, no `Nat.pow` unfolding.
- Recursion the kernel does see on this path (structural `Nat.rec`, not well-founded):
  `scaleSequence` (`PacketSourceScaleChoice.lean:226-228`), `previousShear`/`previousFrequency`/
  `olderShear` (`PacketSourceScaleSequence.lean:30-40`), `stages` (`PacketInfiniteConstruction.lean:39-41`,
  a DEPENDENT motive `fun n => Stage S n`), `Stage.successor` (`:21-25`, `cases n`). All are structural
  on `ℕ`; `stages_zero`/`stages_succ` are `rfl` (`:43,:46`), which is what one expects from a
  structural definition. Mild indexed-family reduction load, no `Acc.rec`. [OK]
- `nlinarith` at `PacketInductionScales.lean:144,149` and `PacketCommonScaleChoice.lean:48`: produces
  polynomial certificates with the `1e6` constants. Elaborator-side work; kernel sees small
  ring-normalisation numerals. [OK]

Conclusion: the `Tstar` subsystem is essentially kernel-risk-free. I found NOTHING here that stresses
GMP numeral arithmetic, well-founded recursion, or structure eta.

## Escalations (ranked, with the exact expert question)

1. **[SUSPICIOUS — statement fidelity, NOT provability] `Euler/Solution.lean:43-56` reproduces
   `ComparatorChallenges/Euler.lean:170-183` VERBATIM (I diffed the two statement bodies modulo
   whitespace: identical), but the challenge file's own proofs are `sorry`
   (`ComparatorChallenges/Euler.lean:88` and `:184`), and `Euler/Solution.lean` does NOT import
   `ComparatorChallenges` (imports at `:1-7`). Therefore every identifier in the solution's statement
   (`InitialVelocityConditionDecay`, `EulerSobolevExistenceAndSmoothnessR3On`, `velocityC1Norm`,
   `vorticityNorm`, `toL2`, `vorticity`, `Ico`) resolves to the repo's OWN copies, and the token-level
   match proves nothing about meaning. Also note the deliberate
   `attribute [local instance] CompletePartialOrder.toSupSet` at `Euler/Solution.lean:41` with the
   comment "Match the reference's elaboration of ENNReal suprema" — an instance change that alters how
   `⨆` in the STATEMENT elaborates.
   EXPERT QUESTION: *Are the repo's `EulerSobolevExistenceAndSmoothnessR3On`, `velocityC1Norm`,
   `vorticityNorm`, `toL2` and `InitialVelocityConditionDecay` definitionally the same as the
   challenge file's, and does `attribute [local instance] CompletePartialOrder.toSupSet` at
   Solution.lean:41 make the two `⨆ t ∈ Icc 0 T, …` / `limsup … = ⊤` clauses elaborate to the same
   term as in ComparatorChallenges/Euler.lean:179,181?* (Out of my scope; likely another worker's.)
2. **[UNCLEAR — the positivity of `Tstar` is only as strong as local existence]** `0 < Tstar` reduces
   entirely to `Stage.exists_local_evolution` (`Euler/PacketStageLocalExistence.lean:39-41`) providing
   SOME `L > 0` with an `Evolution L`. Everything else on the positivity side is bookkeeping.
   EXPERT QUESTION: *Is `Stage.exists_local_evolution`'s `Evolution` the intended honest solution class
   (not a class satisfiable by, e.g., a field that is only required to solve Euler at interior times
   of an empty interior), and does its Cauchy-limit construction really produce an evolution whose
   initial value is `initialDatum` rather than a limit object matched only in `L²`?*
3. **[UNCLEAR — no effective lower bound on `Tstar`]** Because `X` comes from `Eventually.exists`
   (`PacketInductionScales.lean:172`), the theorem cannot exhibit any numeric `T₀ > 0` with
   `T₀ ≤ Tstar`. This is legal for the stated claim but means "finite positive lifespan" is
   existential only.
   EXPERT QUESTION: *Does the manuscript claim a quantitative lifespan bound (e.g.
   `Tstar ≈ 6 J² X^(-498)` for explicit `J, X`) that the formalisation silently weakens to a
   non-constructive existential?*
4. **[OK, but worth one check] `eventually_base_guards` conjunct indexing.** `time_small` is
   `hb.2.2.1` and `localized` is `hb.2.2.2.2.2` (`PacketInductionScales.lean:167`). Against the
   6-conjunct statement (`PacketBaseGuardScales.lean:67-70`) these are `baseHorizon ≤ T₀` and
   `baseGuardCost ≤ 1/2` respectively — I verified the projections by hand and they are correct, and
   the elaborator would have rejected a mismatch anyway. No action.

## Residue (what I did NOT verify)

- NOTHING was compiled: no `lake build`, no `#print axioms` output. All `sorry`/axiom claims are
  grep-level over the files I read; I did not check the transitive import closure of
  `Euler/Solution.lean` (hundreds of files) for `sorry`/`axiom`, only my 10 chain files.
- `Euler/EulerProof.lean` was read only at `20240-20276`. It is ~20k+ lines; I did not audit
  `tendsto_rpow_neg_atTop` usage elsewhere, nor `base_exponential_decay`.
- I did not audit `ActualBounds`, `FirstScaleGuards`, `SmallSeries`, `UniversalFrequency`,
  `renewal_series_small`, `literal_uniform_choice`, `Stage`, `Evolution`, `SmoothL2Field`, or
  `Stage.initialDataLimit*` — i.e. everything that makes the OTHER `Scales` fields and the blowup
  itself true. My claim is only about `Tstar ∈ (0,1]`.
- I did not verify `initialDatum_nonzero`, `initialDatum_compact`, the limsup/vorticity `= ⊤` clauses,
  or `initialDatum_no_global_solution`.
- `positivity`'s internal use of `hX : 0 < X` in `baseHorizon_pos` (`PacketBaseGuardScales.lean:26`) is
  inferred from Mathlib's documented behaviour (context search for atoms), not observed in a build.
