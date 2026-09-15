# Worker report: `source_physical_label_bound` and the `10*(q+2)` label exponent

Repo audited read-only: `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5` (source reading only; no
`lake build` available on this box). Cone column from `audits/nse-deep/CONE.csv` (mark 4).

## Scope

Primary (read line-by-line, 100%):

| file | decls (theorem/def/structure) | read |
|---|---|---|
| `Euler/ChildParticleSourceBound.lean` (78 lines) | 3 theorems | all 3, line by line |
| `Euler/SobolevSourceExponent.lean` (109 lines) | 1 def + 6 theorems = 7 | all 7, line by line |
| `Euler/PhysicalChildSourceBound.lean` (81 lines) | 2 theorems | both, line by line |
| `Euler/ParentPacketLabelData.lean` | 1 structure + 7 (def/theorem) = 8 | `LabelData`, `child`, `block_nonneg` line by line; the 5 budget/match defs skimmed |
| `Euler/ParentUniformForwardChild.lean` | 1 theorem | all, line by line |

Secondary (read the parts the exponent depends on):

| file | decls | read |
|---|---|---|
| `Euler/ChildParticleFieldBounds.lean` | 50 | `Data` + lines 44-72, 137-256 line by line (amplitude/radius/child-field jet bounds); composition internals skimmed |
| `Euler/ParameterSobolevCoefficient.lean` | 8 | the 2 defs + 2 nonneg lemmas line by line; block lemmas skimmed |
| `Euler/PacketForwardUniformChild.lean` | 1 | statement + proof line by line |
| `Euler/PacketUniversalFrequency.lean` | 6 | all line by line |
| `Euler/ParentNeighborThreshold.lean` | 12 | `requiredExponent`, `degree_le_requiredExponent`, `strainDifferenceCost_monomial`, `forward_neighbor_error_of_source_scales` line by line; rest skimmed |
| `Euler/NormalPacketFrequencyGuards.lean` | 6 | `exponential_le_envelope`, `secondary_frequency_guards` line by line |
| `Euler/PacketSourceParameterScales.lean` | 16 | `predecessor_power_le`, `previousFrequency_power_le` + all 5 `decide` sites; rest skimmed |
| `Euler/PacketParentLabelBounds.lean` | (partial) | `direction`, `embeddingCost`, `tensor_le_wordSum` only |
| `Euler/MeanClassicalWordBounds.lean` | (partial) | `classicalBaseSize`, `classicalBlockSize`, `classicalBlockSize_eq` only |

Total decls fully read line-by-line: 33. Skimmed: ~55.

## Answer in one line

**The exponent `10*(q+2)` is CHOSEN, not derived.** Every *constant* in the chain (45, 69, 12, 3, 9, 36,
`fixedCost q`) is derived exactly, and the derived *exponent* is `6*q+8` (= **44** at `q = 6`). The step
from `6*q+8` to `10*(q+2) = 10*q+20` (= **80** at `q = 6`) is a single monotonicity step closed by
`by omega` at `Euler/SobolevSourceExponent.lean:73`, with slack `4*q+12` = **36 powers of k** at `q = 6`.
The choice is *safe in direction* (it weakens an upper bound, and needs only `1 ≤ k`), and I found **no
exponent mismatch anywhere**: all consumers quote `^80`, and the one place where 80 must be "small
enough" (`c ≤ 320`, `Euler/NormalPacketFrequencyGuards.lean:24`) is discharged with 4x headroom.

## A. The statement and the exponent ledger

`source_physical_label_bound` — `Euler/ChildParticleSourceBound.lean:65-76` (verbatim statement):

```lean
theorem source_physical_label_bound (q : ℕ) (k : ℝ) (hk : 69 ≤ k)
    (hbig : 2+45*embeddingCost ≤ k) (hcost : fixedCost q ≤ k)
    (hK : G.K ≤ k) (hM : G.amp ≤ k) (hR : G.rad ≤ k^2) (n : ℕ) :
    classicalBlockSize direction q G.childDisplacement.toLp ... n+
      classicalBlockSize direction q G.childVelocity.toLp ... n+
      classicalBlockSize direction q G.childAcceleration.toLp ... n ≤
        (k^(10*(q+2)))^(n+1)*(n.factorial : ℝ)^2
```

The proof is a single term application of `source_triple_classical_bound`
(`Euler/SobolevSourceExponent.lean:98`) with `M := G.amplitude`, `R := G.radius`; the two interesting
arguments are `G.amplitude_le_power` and `G.radius_le_power`, proved in the same file. Full ledger:

| step | file:line | inequality proved | where the powers come from |
|---|---|---|---|
| 1 | `ChildParticleFieldBounds.lean:47-49` | `amplitude = K+amp+9*(c*K^2)*amp+9*(4*c*K^3)*amp^2` | `firstAmplitude = c*K^2`, `secondAmplitude = 4*c*K^3`; the coefficient `9` is *exactly* the sum of the three `3`'s in `childAcceleration_bound` (`:224-234`, closed by `ring`, no slack) |
| 2 | `ChildParticleSourceBound.lean:16-41` | `amplitude ≤ k^6` | worst monomial `36*c*K^3*amp^2` has joint degree **5** in `(K,amp)`; `K,amp ≤ k` gives `k^5`; the **+1** absorbs the constant `2+45*embeddingCost` (note `45 = 9+36`, derived exactly, `hbig` is the *tight* constant). Slack: `K ≤ k ≤ k^5` and `K^2*amp ≤ k^3 ≤ k^5` waste 4 resp. 2 powers *inside* the `k^5`, not on the exponent. |
| 3 | `ChildParticleFieldBounds.lean:45-46` | `radius = (1+rad)*((1+amp)*(16*K)+2)+rad` | definition |
| 4 | `ChildParticleSourceBound.lean:43-63` | `radius ≤ k^5` | `(1+rad) ≤ 2k^2`, `(1+amp)*16K+2 ≤ 34k^2` → product `≤ 68k^4`, plus `rad ≤ k^2 ≤ k^4` → `69k^4`; degree **4**, the **+1** absorbs `69 = 68+1` (again the *tight* constant, matching `hk : 69 ≤ k`) |
| 5 | `ParameterSobolevCoefficient.lean:38` | `sobolevCoefficientRadius (Fin 3) R = 4*(max 1 3*R) = 12*R` | `Fintype.card (Fin 3) = 3` |
| 6 | `SobolevSourceExponent.lean:18-27` | `12*R ≤ k^6` for `R ≤ k^5` | 5 from step 4, **+1** absorbs `12` (`hk : 12 ≤ k`) |
| 7 | `ParameterSobolevCoefficient.lean:43` | `sobolevCoefficientAmplitude = 2^q*C*∑_{j≤q} (12R)^j*(j!)^2` | definition |
| 8 | `SobolevSourceExponent.lean:29-59` | `sobolevCoefficientAmplitude ≤ k^(6*q+7)` | `(12R)^j ≤ (k^6)^q = k^(6q)` (**6q**), `C = amplitude ≤ k^6` (**+6**), and **+1** absorbs `fixedCost q = 2^q*∑(j!)^2` (`hcost`) |
| 9 | `SobolevSourceExponent.lean:61-74` | `3*amplitudeCoef ≤ k^(6*q+8) ≤ k^(10*(q+2))` and `12R ≤ k^6 ≤ k^(10*(q+2))` | **+1** absorbs the factor `3` (the three fields). **Then the only non-derived step:** `pow_le_pow_right₀ hk1 (by omega)`, i.e. `6*q+8 ≤ 10*q+20` (line 73) and `6 ≤ 10*q+20` (line 74) |
| 10 | `SobolevSourceExponent.lean:76-96` | sum of three block sizes `≤ J^(n+1)*(n!)^2` with `J := k^(10*(q+2))` | `classicalBlockSize_of_jet_bound` per field, then `(3*amp)*R^n ≤ J*J^n = J^(n+1)` |

So the arithmetic **adds up to `6*q+8`, not to `10*(q+2)`**. At `q = 6`: derived 44, quoted 80.
The gap is `4*q+12 = 36` powers of `k`, and `k ≥ 69` (in fact `k ≥ fixedCost 6 = 34138752` from
`UniversalFrequency.derivative_bound`), so the quoted bound is astronomically weaker than what is proved.

Direction check (why the slack is harmless here): the exponent sits on the **right** of a `≤`, and
`pow_le_pow_right₀` needs only `1 ≤ k` (available from `hk : 12 ≤ k` / `69 ≤ k`). So a too-large chosen
exponent can only weaken the conclusion; it cannot make a false statement true. The risk is entirely
at the consumers (part C), and there `k^80` must still be *small enough*.

Docstring vs statement: `Euler/PhysicalChildSourceBound.lean:6` says "the resulting exponent is
**exactly** 10(s+2)", and `Euler/ChildParticleSourceBound.lean:4-6` says the losses "fit the
manuscript's C*=10(s+2)". "Fit" is accurate; "exactly" is not — nothing in the file proves the exponent
is attained or minimal, and 44 is provable. Tag: SUSPICIOUS-DOCSTRING (author-side, not proof-side).

## B. Cross-file exponent consistency (grep census)

Greps run repo-wide: `10\s*\*\s*\(q`, `\^80`, `\^ 80`, `k\^\(10`, `labels.K`, `\.K=k`, and
`\^(4[0-9]|5[0-9]|6[0-9]|7[0-9]|8[0-9]|9[0-9]|1[0-9][0-9])`.

* `k^(10*(q+2))` occurs at exactly 6 sites, all the same statement being relayed:
  `SobolevSourceExponent.lean:63,64,73,105`, `ChildParticleSourceBound.lean:71`,
  `PhysicalChildSourceBound.lean:70`, `PacketForwardUniformChild.lean:99`,
  `PacketInitializedUniformChild.lean:101`, `PacketInitializedChildBounds.lean:86`,
  `PacketForwardInitializedChildShear.lean:84`. No variant exponent.
* The instantiation `q := 6` is passed literally at `ParentUniformForwardChild.lean:72` (and the
  parallel `ParentUniformJoinedChild`, `ParentPacketForwardChildChoice`, `ParentPacketChildChoice`),
  and the label constant supplied 6 lines later is the literal `k^80`
  (`ParentUniformForwardChild.lean:78`, `ParentUniformJoinedChild.lean:85`,
  `ParentPacketForwardChildChoice.lean:83`, `ParentPacketChildChoice.lean:85`). The two are reconciled
  **by definitional unification** `10*(6+2) ≡ 80`, not by a rewrite, so a mismatch would be a type
  error, not a silent gap. Good design from an audit standpoint.
* Every downstream quotation of the label constant is `^80`, with no competing number:
  `PacketInductionStage.lean:34` (`labels.K=(previousFrequency ...)^80`),
  `BaseLiteralFirstPacket.lean:61` (`(X^D)^80`), `label_constant : labels.K=k^80` in the 6 choice
  structures (`BaseFirstPacketChoice.lean:42`, `BaseFirstPacketChoiceNoOptions.lean:78`,
  `ParentGeometryForwardChoice.lean:86`, `ParentGeometryForwardChoiceNoOptions.lean:111`,
  `ParentGeometryJoinedChoice.lean:35`, `ParentGeometryJoinedChoiceInvestigation.lean:71`), and the
  hypothesis form `L.K ≤ ...^80` at `ParentNeighborThreshold.lean:58,74,122`,
  `ParentNormalPacketParameters.lean:87`, `ParentForwardNormalParameters.lean:26`,
  `NormalPacketFrequencyGuards.lean:69`, `PacketInductionScaleBounds.lean:88`,
  `ParentHistoryFrequencyGuard.lean:98,138`.
* Two places hard-code the same 80 as a *derived* numeric budget, and both are consistent:
  `ParentNeighborThreshold.lean:23` `def requiredExponent : ℕ := 80*degree+1` (used at
  `ParentNeighborThreshold.lean:63` as `have he : 80*degree+1 ≤ c := hc`, i.e. relying on
  `requiredExponent` being *definitionally* `80*degree+1`), and
  `NormalPacketFrequencyGuards.lean:75-77`, which feeds the literal `80` into
  `previousFrequency_power_le ... 80` and `exponential_le_envelope ... 80 hX (by norm_num)`, whose
  side condition is `hc : c ≤ 320` (`NormalPacketFrequencyGuards.lean:24`).

**Verdict on B: no mismatch found.** The one real coupling is that the chosen 80 is replicated by hand
in `requiredExponent := 80*degree+1` and in the `80 ≤ 320` envelope check; both are consistent with the
proved exponent today, but they are *literal duplicates*, not references, so a future change of
`10*(q+2)` or of `q := 6` would silently desynchronize `requiredExponent` (it would still compile — it
is only a `def` — while the neighbor-error estimate would then be proved for the wrong exponent).
Tag: UNCLEAR/maintenance-risk, not a defect.

## C. Uniformity and quantifier order

* In `source_physical_label_bound` the `Data` value `G` (one child at one time) is fixed and `n` is a
  trailing explicit argument, so the bound is `∀ n` for that child. There is no `t` at this level.
* `exists_source_child_fields` (`PhysicalChildSourceBound.lean:53-79`) lifts it to
  `∀ t n, ... ≤ (k^(10*(q+2)))^(n+1)*(n!)^2` (line 67-70), proving it at line 79 by
  `(E t).source_physical_label_bound q k hk hbig hcost hKk le_rfl le_rfl n` — i.e. **the same `k` for
  all `t` and all `n`**, with `t` ranging over all of `Icc 0 T`. Note `le_rfl le_rfl` for `hM`/`hR`:
  the child data is built with `amp := k`, `rad := k^2` (line 72), so those two hypotheses hold by
  reflexivity. Genuinely uniform.
* `hR : G.rad ≤ k^2` is supplied uniformly by `coarsen_graph_bounds`
  (`PhysicalChildSourceBound.lean:18-43`), which needs `ell⁻¹ ≤ k^(3/4)` — a *hypothesis* `hinv`
  carried all the way up to `forward_uniform_child` (`ParentUniformForwardChild.lean:33`). So
  uniformity in `t` is real, but uniformity across *stages* rests on `hinv`/`hKk`, discharged by the
  scale sequence, not here.
* Consumers, and their quantifier shape (all match `∀ t n`, in that order):
  1. `EulerParentPacketFrames.LabelData.child` (`ParentPacketLabelData.lean:81-86`) —
     `hb : ∀ t n, ...(direction 6)... ≤ K^(n+1)*(n!)^2`. Order and `q = 6` match exactly. It then
     splits the *sum* bound into three per-field `HasLabelBound K` by discarding the other two
     summands via `block_nonneg` + `linarith` (`:101-112`). Sound, and the sum form is strictly
     stronger than three separate bounds, as the docstring claims.
  2. `forward_uniform_child_label_bounds` (`PacketForwardUniformChild.lean:57`, conclusion at `:95-99`).
  3. `forward_uniform_child` (`ParentUniformForwardChild.lean:36`, uses it at `:74-78` to build `LC`
     with `LC.K = k^80`), plus the three parallel copies `ParentUniformJoinedChild.lean:68`,
     `ParentPacketForwardChildChoice.lean:66`, `ParentPacketChildChoice.lean:68`.
  4. `PacketInitializedUniformChild.lean:98-101`, `PacketInitializedChildBounds.lean:86`,
     `PacketForwardInitializedChildShear.lean:84` (initialized/shear variants).
  5. Downstream of `LC.K = k^80`: `secondary_frequency` (`PacketInductionScaleBounds.lean:87-93`) →
     `secondary_frequency_guards` (`NormalPacketFrequencyGuards.lean:66-82`), which is the **only
     place where the size of the chosen exponent is actually tested**: it must satisfy `80 ≤ 320`
     (`exponential_le_envelope`, `NormalPacketFrequencyGuards.lean:24`) to conclude
     `K ≤ frequency J X n`, i.e. `k_n^80 ≤ k_{n+1}`. And
     `strainDifferenceCost_monomial` (`ParentNeighborThreshold.lean:57-68`), which converts
     `L.K ≤ k^80` into `L.K ≤ k^c` for `c ≥ requiredExponent = 80*degree+1`.
* Non-vacuity spot check: `direction i = EuclideanSpace.single i 1`
  (`PacketParentLabelBounds.lean:22`) — genuine unit coordinate vectors, and
  `tensor_le_wordSum` (`:29-32`) shows `‖iteratedFDeriv ℝ n f x‖ ≤ wordSum direction f n x`, so the
  quantity being bounded really dominates full iterated-derivative norms. It is not a degenerate
  seminorm that would make the label bound empty. Also `exists_firstPacketChoice`
  (`BaseFirstPacketChoice.lean:54-84`) actually *constructs* a `FirstPacketChoice` from
  `forward_uniform_child`, so `label_constant : labels.K = k^80` is realized, not merely assumed.

## Per-declaration findings

| # | name | file:line | statement (my words) | proof mechanism | cone | verdict |
|---|---|---|---|---|---|---|
| 1 | `Data.amplitude_le_power` | `Euler/ChildParticleSourceBound.lean:16` | if `K,amp ≤ k`, `k ≥ 1`, `k ≥ 2+45c` then `amplitude ≤ k^6` | rewrite `amplitude` to `K+amp+9cK²amp+36cK³amp²` (`ring`), bound each monomial by `k^5`, sum `≤ (2+45c)k^5 ≤ k·k^5`; `nlinarith`+`mul_le_mul_of_nonneg_*` | True | OK (constants tight, exponent +1 for the constant) |
| 2 | `Data.radius_le_power` | `:43` | if `k ≥ 69`, `K,amp ≤ k`, `rad ≤ k^2` then `radius ≤ k^5` | unfold `radius`/`compositionRadius`; `(1+rad) ≤ 2k²`, inner `≤ 34k²`, product `≤ 68k^4`, `+rad ≤ k^4`, total `69k^4 ≤ k·k^4`; `nlinarith` | True | OK |
| 3 | `Data.source_physical_label_bound` | `:65` | sum of the three child H^q block norms `≤ (k^(10(q+2)))^(n+1)(n!)²`, per child, all `n` | one term: `source_triple_classical_bound` fed with 1,2 and the three `child*_bound` jet bounds | True | OK statement; exponent CHOSEN (see A) |
| 4 | `fixedCost` | `Euler/SobolevSourceExponent.lean:14` | `2^q*∑_{j≤q}(j!)²` | def | True | OK (never evaluated; see kernel section) |
| 5 | `coefficient_radius_le` | `:18` | `12 ≤ k`, `R ≤ k^5` ⟹ `sobolevCoefficientRadius (Fin 3) R ≤ k^6` | `norm_num [sobolevCoefficientRadius]` reduces it to `12*R`; then `12k^5 ≤ k·k^5` | True | OK |
| 6 | `coefficient_amplitude_le` | `:29` | `C ≤ k^6`, `R ≤ k^5`, `fixedCost q ≤ k` ⟹ amplitude coefficient `≤ k^(6q+7)` | per-`j` bound `(12R)^j ≤ k^(6q)` via `pow_le_pow_left₀`/`pow_le_pow_right₀`, `Finset.sum_le_sum`, then `fixedCost q*k^(6q+6) ≤ k^(6q+7)` | True | OK — this is the decl that fixes the derived exponent at `6q+7` |
| 7 | `source_cost_bounds` | `:61` | same hypotheses ⟹ `3*amplitudeCoef ≤ k^(10(q+2))` **and** `radiusCoef ≤ k^(10(q+2))` | `k^(6q+8) ≤ k^(10(q+2))` by `pow_le_pow_right₀ hk1 (by omega)` (line 73) and `k^6 ≤ k^(10(q+2))` (line 74) | True | **KEY: this is where the chosen exponent enters.** OK as an inequality; SUSPICIOUS as a claim of "exactly 10(s+2)" |
| 8 | `triple_classical_bound` | `:76` | three fields with a common jet bound `(M,R)` and `3*amplitudeCoef ≤ J`, `radiusCoef ≤ J` ⟹ sum of block sizes `≤ J^(n+1)(n!)²` | `classicalBlockSize_of_jet_bound` three times; `‖direction i‖ ≤ 1` by `simp [direction]`; then `mul_le_mul` chain and `pow_succ` | True | OK |
| 9 | `source_triple_classical_bound` | `:98` | packaging of 7+8 with `J := k^(10(q+2))` | two-line term proof | True | OK |
| 10 | `coarsen_graph_bounds` | `Euler/PhysicalChildSourceBound.lean:18` | rpow-scaled jet bounds with amplitude `k^(-1/2+1/4)` / `k^(1/4)` and radius `ell⁻¹k^(5/4)` coarsen to `(k, k^2)` given `ell⁻¹ ≤ k^(3/4)` | `Real.rpow_le_rpow_of_exponent_le` (needs `1 ≤ k`) and `rpow_add` to get `k^(3/4)·k^(5/4) = k^2`; then `HasJetBound.mono` | True | OK — the `k^2` in `hR` is exactly `3/4+5/4` |
| 11 | `exists_source_child_fields` | `:53` | existence of child field data over all `t` with the `∀ t n` label bound at exponent `10(q+2)` | builds `E := data ... k (k^2) ...` and applies #3 pointwise with `le_rfl` for `amp`/`rad` | True | OK |
| 12 | `Data.childAcceleration_bound` | `Euler/ChildParticleFieldBounds.lean:224` | `childAcceleration.HasJetBound amplitude radius` | additive combination of 6 jet bounds; `he : K+3fa+3fa+9sa·amp²+amp+3fa = amplitude` closed by `ring` — **exact**, no slack | True | OK (this is why `amplitude`'s coefficient 9 is derived) |
| 13 | `Data.childDisplacement_bound` / `childVelocity_bound` | `:207` / `:215` | same with the smaller sums | `HasJetBound.mono` + `nlinarith` using nonnegativity of the unused monomials | True | OK (slack factor 3 here, absorbed) |
| 14 | `LabelData.child` | `Euler/ParentPacketLabelData.lean:81` | given `∀ t n` sum bound at constant `K`, builds the child's `LabelData` with `.K = K` | record construction; per-field bounds by dropping two nonneg summands (`block_nonneg`, `linarith`) | True | OK |
| 15 | `LabelData.forward_uniform_child` | `Euler/ParentUniformForwardChild.lean:36` | existence of the next parent with `∃ LC, LC.K = k^80` | destructs `forward_uniform_child_label_bounds ... 6 ...` and feeds `hlabel` to `LabelData.child` with `K := k^80`; final `rfl` | True | OK — the `80` is unified with `10*(6+2)` definitionally |
| 16 | `forward_uniform_child_label_bounds` | `Euler/PacketForwardUniformChild.lean:57` | the big packet-stage existence with the `∀ t n` label bound at `10(q+2)` | `forward_uniform_flow_and_shear` + `coarsen_graph_bounds` + `exists_source_child_fields` | True | OK (flow/shear part out of my scope) |
| 17 | `requiredExponent` / `degree_le_requiredExponent` | `Euler/ParentNeighborThreshold.lean:23,25` | `80*degree+1`, and `degree ≤ requiredExponent` | def; `unfold` + `omega`-style arithmetic | True | UNCLEAR (literal 80 duplicated by hand — see B) |
| 18 | `strainDifferenceCost_monomial` | `:57` | `L.K ≤ k^80` + `requiredExponent ≤ c` ⟹ `strainDifferenceCost ≤ k^c` | `polynomial_le_monomial` with the literal `80` as the K-exponent; `he : 80*degree+1 ≤ c := hc` relies on `requiredExponent` unfolding | True | OK |
| 19 | `exponential_le_envelope` | `Euler/NormalPacketFrequencyGuards.lean:23` | `c ≤ 320` ⟹ `exp(c·predecessorExponent) ≤ envelope` | `exp_le_exp` monotonicity, then multiply by a `≥ 1` polynomial factor | True | OK — **the only real size test of the chosen 80** (`80 ≤ 320`, 4x headroom) |
| 20 | `secondary_frequency_guards` | `:66` | `K ≤ previousFrequency^80` ⟹ `K ≤ frequency J X n` (and a support-scale bound) | `previousFrequency_power_le ... 80` (needs `0 ≤ 80`) then `exponential_le_envelope ... 80 (by norm_num : 80 ≤ 320)` and `smallPower_le_power` | True | OK |
| 21 | `UniversalFrequency` | `Euler/PacketUniversalFrequency.lean:15` | the 9 numeric conditions on `k`, incl. `child_bound : 69 ≤ k`, `embedding_bound : 2+45c ≤ k`, `derivative_bound : fixedCost 6 ≤ k` | structure; `universal_frequency_eventually` (`:26`) shows all 9 hold for large `k` by `filter_upwards`/`eventually_ge_atTop` | True | OK — hypotheses of #3 are exactly these three fields; nothing is assumed that is not shown eventually satisfiable |

Verdict counts over the 21 rows: **OK 18, UNCLEAR 2 (#17 duplicate-literal coupling; and the
"exactly 10(s+2)" docstring class), SUSPICIOUS 1 (#7 as a *claim*, not as a theorem), KERNEL-RISK 0.**

## Kernel-risk assessment

Vector (1) recursive inductives / recursors / `Acc.rec` / large elimination:
* No `inductive`, no `termination_by`, no `WellFounded.fix`, no `.rec` written by hand, and no
  `induction` tactic anywhere in the three primary files. One `induction` exists in the secondary file
  `ParameterSobolevCoefficient.lean:26` (`block_eq_sum_levels`, structural `induction n`) — a normal
  `Nat.rec` on a *variable* `n`, so the kernel never unfolds it a fixed number of times.
* `Finset.range (q+1)` sums appear with `q` a *variable* (`SobolevSourceExponent.lean:14,44,52`); no
  proof instantiates `q` to a literal and forces the sum. The only literal instantiation is `q := 6`
  in *types* (`ParentUniformForwardChild.lean:72`, `LabelData.child`'s `direction 6`), which does not
  require evaluating `∑ j ∈ range 7, (j!)^2`.
* Structure eta: `Data` (`ChildParticleFieldBounds.lean:17`) and `LabelData`
  (`ParentPacketLabelData.lean:17`) are plain (non-recursive) structures; `PhysicalChildSourceBound.lean`
  closes six components by `rfl` (`:77`) against the `data ...` constructor — projection-of-constructor
  reduction, iota only, no recursor. `ParentUniformForwardChild.lean:79` ends in `rfl` for
  `LC.K = k^80` — again projection reduction plus the numeral unification below. Cheap and standard.

Vector (2) Nat/GMP numeral arithmetic the kernel must redo:
* The largest computation the kernel is *forced* to do in my scope is the definitional unification
  `10*(6+2) ≡ 80` on `ℕ` at `ParentUniformForwardChild.lean:78` (and the 3 sibling files). That is
  `Nat.add`/`Nat.mul` on 1-2 digit literals through the GMP fast path. Negligible.
* `by omega` sites: `SobolevSourceExponent.lean` lines 51, 55, 72, 73, 74 and
  `ChildParticleSourceBound.lean` lines 19, 20, 57. All goals are linear `ℕ` (in)equalities in the
  *variable* `q` or with literals `≤ 8`: e.g. `6*q+8 ≤ 10*(q+2)`, `6*q+6 = 6+6*q`, `1 ≤ 5`, `2 ≤ 4`.
  `omega` emits a certificate the kernel checks with small-literal `Int`/`Nat` arithmetic. No bignum.
* `norm_num`/`nlinarith`/`linarith`/`positivity`: 6+3+3 `norm_num`, 3 `nlinarith`, 6 `linarith` in
  `ChildParticleSourceBound.lean`; the numerals involved are `2,3,9,12,16,34,36,45,68,69` — all
  ≤ 2 digits. The heaviest `nlinarith` (`:39`, `:59`) produce products of the supplied hypotheses;
  their certificates are polynomial identities over ℚ with small coefficients. No `Nat.pow`,
  `Nat.div`, `Nat.mod`, `Nat.gcd` on literals anywhere in scope.
* `decide`: **zero** in the three primary files. Five occur in the dependency
  `PacketSourceParameterScales.lean:86,92,96,121,126`, all deciding `Nat` comparisons with literals
  (`3 ≤ 4`, `3 ≤ 7`, `≤ 5`, `≤ 1000`) via `Nat.decLe`/`Nat.ble`, which the kernel evaluates through
  GMP in constant time. `1000` is the largest literal; no exponentiation of it is forced.
* `fixedCost 6` (`PacketUniversalFrequency.lean:24,29`) would evaluate to
  `64*533418 = 34138752` if anyone computed it — **nobody does**. It only ever appears as an opaque
  real under `≤` and inside `eventually_ge_atTop`. So the factorial/`Finset.sum` is never forced.
  This is a genuine positive finding: the file avoids the obvious bignum trap.
* `(n.factorial : ℝ)^2` is always at a variable `n`; never at a literal.

Vector (3) custom metaprogramming: none in scope. No `macro`, `elab`, `syntax`, `set_option`,
`native_decide`, `axiom`, `unsafe`, `partial`, `sorry` in any of the 12 files I read. One
`attribute [local irreducible] Parent.child initialParent` at `BaseFirstPacketChoice.lean:25` —
an ordinary attribute that only makes elaboration *harder*, never easier, and has no kernel effect.

**Bottom line: this sub-tree is kernel-benign.** The heaviest kernel obligation is a 2-digit `Nat`
multiplication and a handful of `omega`/`linarith` certificates over small rationals. If the OpenAI
artifact is exploiting a kernel bug, it is not doing it here.

## Escalations

1. **(medium) The label exponent is a chosen round number, so every consumer must be re-checked if it
   ever changes; two consumers hard-code `80` as a *literal*, not as a reference.**
   `Euler/SobolevSourceExponent.lean:73` (chosen step `6q+8 → 10q+20`) vs
   `Euler/ParentNeighborThreshold.lean:23` (`requiredExponent := 80*degree+1`) and
   `Euler/NormalPacketFrequencyGuards.lean:75-77` (`... 80 ... (by norm_num : 80 ≤ 320)`).
   Question for an expert: is `80` (and hence `requiredExponent = 80*degree+1`) the number the
   manuscript's neighbor-error and frequency-envelope estimates were designed around, or would the
   sharper provable exponent `6q+8 = 44` change any *other* constant (e.g. `320`, `degree`, the
   `k^(3/4)` inversion budget)? Settled by: recomputing `secondary_frequency_guards` and
   `strainDifferenceCost_monomial` with `44` and confirming both still close (they should, `44 ≤ 320`),
   and by checking the manuscript's C* convention. Nothing here is *wrong*; the risk is purely that a
   future edit desynchronizes two hand-copied 80s.
2. **(medium) `exponential_le_envelope`'s `c ≤ 320` is the only place the size of the label exponent is
   tested — is `320` itself derived?** `Euler/NormalPacketFrequencyGuards.lean:24`. The pair
   (label exponent 80, envelope budget 320, shear exponent 1000 at
   `PacketSourceParameterScales.lean:89`) forms a numeric contract across files. Question: is
   `320` chosen with the *sum* of all `^80`-class demands in mind (labels 80, plus whatever else is
   charged to the same envelope), or does it only cover 80? Settled by enumerating all callers of
   `exponential_le_envelope`/`envelope` and adding up the exponents charged per stage. **Out of my
   scope** — hand to whoever owns `PacketSourceScaleSequence`/`NormalPacketFrequencyGuards`.
3. **(low) Docstring overclaim.** `Euler/PhysicalChildSourceBound.lean:6` "the resulting exponent is
   exactly 10(s+2)". The proved exponent is an upper bound with 36 powers of slack at `s = 6`.
   Question: does the manuscript claim `C* = 10(s+2)` is *sharp* anywhere a reader would rely on it?
   Settled by reading the manuscript passage; the Lean is unaffected.
4. **(low) `q` is generic in the estimate but only ever `6`, and `q = 6` is hard-coded in two other
   places.** `ParentPacketLabelData.lean:83-85` (`direction 6`) and
   `PacketUniversalFrequency.lean:24` (`fixedCost 6 ≤ k`). Question: is there any route that
   instantiates `exists_source_child_fields` at `q ≠ 6` and then feeds `LabelData.child`? I found none
   (the four call sites all come from theorems that receive `q` and are only ever called with `6`), and
   a mismatch would be a type error. Settled by `lake build` once a machine has Mathlib.

## Residue

* **No `lake build`.** I could not confirm that `10*(6+2)` and `80` actually unify in the elaborator,
  that the `omega`/`nlinarith` calls close, or that the four parallel `Parent*Child*` copies really
  type-check. Everything above is source reading. (Mitigation: the artifact reportedly passed
  Comparator, so elaboration is not in doubt; my claims are about *what* is proved, not *whether*.)
* I did **not** audit `forward_uniform_flow_and_shear` (`PacketForwardUniformChild.lean:103`), the
  correction-budget machinery `Q`, or the error bounds `k^(-(1/4))` — other workers' scope. So I cannot
  say whether the *other* outputs of `forward_uniform_child_label_bounds` are as clean as the label bound.
* I did not verify `classicalBlockSize_of_jet_bound`, `HasJetBound.mono`, `productField_bound`,
  `composeField_bound`, `hasLabelBound_of_jet_bound` or `sobolevEmbeddingConstant` (Gevrey/embedding
  library, `SmoothL2Gevrey*`, `CylinderSobolevEmbedding`). If `HasJetBound`'s definition were weaker
  than advertised the whole ledger in part A would be about the wrong quantity; I only checked that
  `direction` is the true unit coordinate frame and that `tensor_le_wordSum` dominates
  `iteratedFDeriv`, which is decent but not complete evidence.
* `degree = polynomial.natDegree` (`ParentPacketNeighborPolynomial.lean:33`) — I did not compute it, so
  I cannot say what `requiredExponent = 80*degree+1` is numerically.
* The base case's `labels.K = (X^D)^80` (`BaseLiteralFirstPacket.lean:61`) and the `previousShear`
  exponent `1000` come from files I only grepped.
