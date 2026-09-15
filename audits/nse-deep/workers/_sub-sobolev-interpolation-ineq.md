# Worker report: Sobolev interpolation inequality (compactness engine of the Euler limit)

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` = openai/NavierStokesAndEuler @ f9e8bc5.
Read-only, source-level only (no `lake build`, no Mathlib built).

## Scope

READ IN FULL (line by line):

| file | lines | decls (def/theorem/instance/abbrev) |
|---|---|---|
| `Euler/SobolevInterpolation.lean` | 39 | 1 theorem (`word_square_le_parent`) |
| `Euler/SobolevPathInterpolation.lean` | 111 | 2 defs/instances + 6 theorems |
| `Euler/SobolevTranslationDifferentiation.lean` | 45 | 1 theorem |
| `Euler/CylinderSobolevSpace.lean` | 145 | 6 defs/abbrevs + 2 instances + 7 theorems |
| `Euler/CylinderSobolevOperators.lean` | ~140 read | 7 defs + 11 theorems |
| `Euler/CylinderSobolevDerivatives.lean` | 105 | 4 defs + 7 theorems |
| `Euler/ClosedTranslationGraph.lean` | 87 | 1 def + 4 theorems |
| `Euler/SobolevRestriction.lean` | 75 (first 40 read, rest skimmed) | 2 defs + 3 theorems |
| `Euler/SobolevCauchyInterpolation.lean` | 96 | 1 def + 5 theorems (the actual consumer) |

SKIMMED / TARGETED READ (grep + surrounding blocks only):
`Euler/EulerProof.lean` (7k+ lines; read L1080-1130, L1215-1265, L2250-2270, L2640-2670, L2740-2830,
L3064-3076, L3340-3450, L4540-4570, L6515-6545), `Euler/CylinderSmoothOrbit.lean` (L1-90),
`Euler/CorrectionFamilyCompactness.lean` (L1-80), `Euler/CylinderPathProductBounds.lean` (L35-70),
`Euler/CylinderOrbitSobolev.lean` (L75-95).

## Answers to the three headline questions (short form)

1. **PROVED, not assumed.** `word_square_le_parent` has a complete 20-line proof. No `sorry`, no axiom,
   no unproved hypothesis smuggled in as an argument.
2. **Mechanism = antisymmetry of the translation generator (integration by parts in abstract form)
   + Cauchy-Schwarz + sup-norm domination.** Not Fourier, not a concrete integral computation.
3. **The derivative coordinates ARE proved derivatives.** Membership in the space is *defined* as
   "every child coordinate is the strong L² derivative of its parent coordinate along the corresponding
   coordinate direction" (`sobolevSubspace`, `CylinderSobolevSpace.lean:44-46`), and this is *extracted*
   by `word_hasDerivAt` (`CylinderSobolevSpace.lean:70-75`). They are NOT unconstrained bundled data.
   Moreover the whole array is *uniquely determined by the value* (`value_injective`,
   `CylinderSobolevSpace.lean:128-137`). This is the strongest possible answer in the good direction.

## Per-declaration findings

| name | file:line | statement (my words) | real proof mechanism | verdict |
|---|---|---|---|---|
| `SobolevWord q` | `Euler/CylinderSobolevSpace.lean:15` | `Σ n : Fin (q+1), Fin n → Fin 4`: a coordinate word of length ≤ q over 4 directions (angle + 3 space). Finite type. | abbrev | OK |
| `SobolevEdge q` | `CylinderSobolevSpace.lean:18` | word of length n<q together with one extra direction | abbrev | OK |
| `closedDerivativeGraph a` | `CylinderSobolevSpace.lean:34-36` | the graph `{(f,g) | d/dt translation(t·a) f |_{t=0} = g}` as a CLOSED submodule of `L²×L²` | packages `translationDerivativeGraph` + `translationDerivativeGraph_closed` (`ClosedTranslationGraph.lean:53-66`, `68-87`) | OK |
| `translationDerivativeGraph` | `ClosedTranslationGraph.lean:53-66` | carrier is literally `HasDerivAt (fun t => translation period (translationPath period a t) p.1) p.2 0` | submodule axioms from linearity of `translation` and of `HasDerivAt` | OK |
| `translationDerivativeGraph_closed` | `ClosedTranslationGraph.lean:68-87` | that graph is closed (the generator is a closed operator) | sequential closedness: `hasDerivAt_of_tendstoUniformly` applied to the translated orbits, using that translation is an isometry so `f_n → f` gives *uniform in t* convergence of orbits (`translation_orbits_tendstoUniformly`, L38-49) and `translation_hasDerivAt_all` (L20-36) to propagate the derivative to all t. Real functional analysis. | OK |
| `sobolevSubspace period q` | `CylinderSobolevSpace.lean:44-46` | `⨅ e : SobolevEdge q, (closedDerivativeGraph (standardDirection e.2.2)).comap (edgeEvaluation e)`: arrays of L² fields indexed by words, subject to a genuine derivative condition on EVERY edge (parent, child) | definition | **OK — this is the crux; the "derivative" coordinates are constrained** |
| `SobolevSpace period q` | `CylinderSobolevSpace.lean:49` | `= sobolevSubspace period q` as a type (subtype of `SobolevWord q → LiftL2 period`) | abbrev | OK |
| norm instance `sobolevNormedAddCommGroup` | `CylinderSobolevSpace.lean:52-53` | norm inherited from the submodule of the finite Pi type ⇒ `‖u‖ = sup_{|w| ≤ q} ‖∂^w u‖_{L²}` (Mathlib `Pi.seminormedAddCommGroup` on a Fintype index is the SUP norm) | `inferInstanceAs` | OK (sup, not sum; see below) |
| `value` | `CylinderSobolevSpace.lean:63` | `u.val (emptyWord q)` = the underlying L² field | def | OK |
| `word period u hn w` | `CylinderSobolevSpace.lean:66-67` | `u.val ⟨⟨n, _⟩, w⟩` — a literal array lookup at the word `w` | def | OK (no junk branch, no default 0) |
| `word_hasDerivAt` | `CylinderSobolevSpace.lean:70-75` | for `n < q`: `t ↦ translation (t·e_i) (word u w)` has strong derivative `word u (Fin.cons i w)` at 0 | one line: `ClosedSubmodule.mem_iInf.mp u.property` at the edge `⟨⟨n,hn⟩,w,i⟩`. i.e. the derivative property IS the membership property | **OK — proved derivative relation** |
| `ofJet`, `word_has_jet`, `toJet`, `jet_word_eq`, `toJet_word` | `CylinderSobolevSpace.lean:78-125` | compatible arrays ↔ genuine strong-derivative jets (`SpatialJet`), coordinatewise | induction + `HasDerivAt.unique`; `toJet` uses `Classical.choice` (noncomputable, harmless) | OK |
| `value_injective` | `CylinderSobolevSpace.lean:128-137` | the map `u ↦ value u` is injective on `SobolevSpace period q` | via `SpatialJet.word_unique` (`EulerProof.lean:4549-4561`, itself induction + `HasDerivAt.unique`) | OK — strong non-degeneracy |
| `word_norm_le` | `CylinderSobolevOperators.lean:28-29` | `‖u.val w‖ ≤ ‖u‖` | `norm_le_pi_norm` — i.e. the norm really is the sup over words | OK |
| `norm_le_sumNorm` / `sumNorm_le_card_norm` / `sumNorm_eq_jet` | `CylinderSobolevOperators.lean:38-65` | sup norm and the source's SUM norm `∑_w ‖∂^w u‖` are equivalent up to `Fintype.card (SobolevWord q)`, and the sum equals the jet's `sobolevNorm` | Pi-norm lemmas + `Fintype.sum_sigma` | OK (see kernel note on `Fintype.card`) |
| `translation` | `EulerProof.lean:1223-1225` | `Lp.compMeasurePreservingₗᵢ` for `x ↦ x+a` on `LiftL2 period = Lp Vector3 2 (liftMeasure period)`, `liftMeasure = volume(ℝ³) ⊗ Haar(AddCircle period)` (`EulerProof.lean:1083-1100`) | genuine measure-preserving isometry | OK — non-degenerate concrete Hilbert space |
| `standardDirection i` | `EulerProof.lean:6526-6540` | 4 unit covering directions: `0 ↦ (0,1)` (angle), `i.succ ↦ (e_i,0)` (space) | `coordinateEquiv` of `EuclideanSpace.single` | OK |
| `translation_pairing` | `EulerProof.lean:2647-2651` | `⟪T_a f, g⟫ = ⟪f, T_{-a} g⟫` | `inner_map_map` of the isometry + `translation_add` | OK |
| `translation_derivative_pairing` | `EulerProof.lean:2784-2812` | if orbits of `f` and `g` have strong derivatives `f'`, `g'` at 0 then `⟪f',g⟫_ℝ = -⟪f,g'⟫_ℝ` | differentiate `t ↦ ⟪T_{ta} f, g⟫` two ways: as `⟪f',g⟫` and, using `translation_pairing` + `translationPath_neg`, as `-⟪f,g'⟫`; conclude by `HasDerivAt.unique`. **This IS the integration by parts**, done at the level of the unitary group instead of on the cylinder integral. | OK — proved, this is the real content |
| **`word_square_le_parent`** | **`Euler/SobolevInterpolation.lean:17-37`** | see verbatim below | see below | **OK — genuine Landau/Kolmogorov estimate** |
| `sobolevTranslation_hasDerivAt` | `SobolevTranslationDifferentiation.lean:15-43` | translation on `H^{q+1}`, truncated to `H^q`, is strongly differentiable at 0 with derivative `derivativeOperator q i u` | `hasDerivAt_pi` coordinatewise from `word_hasDerivAt`, closedness of the subspace to keep the limit inside (`isClosed.mem_of_tendsto`), then identify the derivative via `valueOperator` + `value_injective` | OK — costs exactly one Sobolev order |
| `truncateOperator`, `derivativeOperator` | `CylinderSobolevDerivatives.lean:23-45` | `H^{q+1} → H^q` word-reindexing maps (`truncateIndex`, `derivativeIndex` = `Fin.snoc w i`) | codRestrict with the edge condition re-derived from `word_hasDerivAt` and `Fin.cons_snoc_eq_snoc_cons` | OK |
| `derivativeOperator_hasDerivAt` | `CylinderSobolevDerivatives.lean:82-96` | `value (derivativeOperator i u)` is the strong derivative of the L² orbit of `value u` | `word_hasDerivAt` at the empty word | OK — ties the operator to a real derivative |
| `restrictOperator` (+`_apply`,`_bound`) | `SobolevRestriction.lean:19-40` | `H^p → H^q` for `q ≤ p`, contractive, preserves `value` | same codRestrict pattern | OK |
| `wordPathOperator` | `SobolevPathInterpolation.lean:54-56` | word coordinate as a CLM on time paths `C(Icc 0 T, H^s) → C(Icc 0 T, L²)` | `compLeftContinuous` of `wordOperator` | OK |
| `wordPathOperator_apply` | `SobolevPathInterpolation.lean:59-61` | `= word (u t) h w`, by `rfl` | definitional projection | OK |
| `wordPath_square_bound` | `SobolevPathInterpolation.lean:64-80` | the same inequality for the uniform (sup-in-time) norms | pointwise `word_square_le_parent` + `ContinuousMap.norm_le` + `Real.le_sqrt_of_sq_le` | OK |
| `cauchySeq_of_square_bound` | `SobolevPathInterpolation.lean:14-30` | `‖g m - g n‖² ≤ A‖f m - f n‖` + `CauchySeq f` ⇒ `CauchySeq g` | ε–δ with threshold `ε²/(A+1)`, closed by `nlinarith` | OK |
| `clm_difference_square_bound` | `SobolevPathInterpolation.lean:33-43` | for CLMs `A,B` with `‖Au‖² ≤ ‖Bu‖‖u‖`: `‖Au-Av‖² ≤ 2M‖Bu-Bv‖` when `‖u‖,‖v‖ ≤ M` | apply at `u-v`, `map_sub`, triangle ineq | OK |
| `wordPath_difference_square_bound`, `wordPath_cauchy_step` | `SobolevPathInterpolation.lean:90-109` | difference form; then Cauchy transfers from parent word to child word | composition of the two above | OK |
| `wordPath_cauchy_of_value` | `SobolevCauchyInterpolation.lean:21-37` | uniform `H^s` bound + Cauchy in L² (uniformly in time) ⇒ every word path with `|w| < s` is Cauchy | induction on `|w|`, one `wordPath_cauchy_step` per derivative | OK |
| `pathCoordinates_norm`, `path_cauchy_of_coordinates` | `SobolevCauchyInterpolation.lean:39-72` | the coordinate map is an isometry onto the Pi of coordinate paths; Cauchy coordinatewise ⇒ Cauchy | `cauchy_pi_iff'` + `Isometry.isUniformInducing` | OK |
| `cauchy_restrict_of_value`, `exists_limit_restrict_of_value` | `SobolevCauchyInterpolation.lean:74-96` | **the compactness engine**: uniformly `H^s`-bounded + L²-Cauchy ⇒ Cauchy, hence convergent, in `C(Icc 0 T, H^q)` for every `q < s` | the interpolation ladder + completeness (`cauchySeq_tendsto_of_complete`) | OK |

### Verbatim `word_square_le_parent` (`Euler/SobolevInterpolation.lean:16-37`)

```lean
/-- One genuine derivative is controlled by its parent word and one available higher derivative. -/
theorem word_square_le_parent {s n : ℕ} (h : n+2 ≤ s) (u : SobolevSpace period s)
    (w : Fin n → Fin 4) (i : Fin 4) :
    ‖word period u (by omega : n+1 ≤ s) (Fin.cons i w)‖^2 ≤
      ‖word period u (by omega : n ≤ s) w‖*‖u‖ := by
  have hp := translation_derivative_pairing period (standardDirection i)
    (word period u (by omega : n ≤ s) w)
    (word period u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word period u (by omega : n+1 ≤ s) (Fin.cons i w))
    (word period u h (Fin.cons i (Fin.cons i w)))
    (word_hasDerivAt period u (by omega : n < s) w i)
    (word_hasDerivAt period u (by omega : n+1 < s) (Fin.cons i w) i)
  rw [real_inner_self_eq_norm_sq] at hp
  calc
    _ = -inner ℝ (word period u (by omega : n ≤ s) w)
        (word period u h (Fin.cons i (Fin.cons i w))) := hp
    _ ≤ |inner ℝ (word period u (by omega : n ≤ s) w)
        (word period u h (Fin.cons i (Fin.cons i w)))| := neg_le_abs _
    _ ≤ ‖word period u (by omega : n ≤ s) w‖*
        ‖word period u h (Fin.cons i (Fin.cons i w))‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (word_norm_le period u ⟨⟨n+2,Nat.lt_succ_of_le h⟩,Fin.cons i (Fin.cons i w)⟩) (norm_nonneg _)
```

Dependencies of this proof, all inside the audited set:
`translation_derivative_pairing` (`EulerProof.lean:2784`), `word_hasDerivAt` (`CylinderSobolevSpace.lean:70`),
`word_norm_le` (`CylinderSobolevOperators.lean:28`), and Mathlib's `real_inner_self_eq_norm_sq`,
`neg_le_abs`, `abs_real_inner_le_norm`, `mul_le_mul_of_nonneg_left`.
Nothing else. No lemma local to `SobolevInterpolation.lean` other than this theorem (the file has exactly
one declaration).

### Question 2 in detail: mechanism, and the role of the second derivative

Write `g := ∂^w u` (`word u w`), `g_i := ∂_i ∂^w u` (`word u (Fin.cons i w)`),
`g_ii := ∂_i ∂_i ∂^w u` (`word u (Fin.cons i (Fin.cons i w))`).

1. `translation_derivative_pairing` is instantiated at `f := g`, `f' := g_i`, `g := g_i`, `g' := g_ii`.
   The two `HasDerivAt` witnesses are `word_hasDerivAt … w i` (needs `n < s`) and
   `word_hasDerivAt … (Fin.cons i w) i` (needs `n+1 < s`). Result: `⟪g_i, g_i⟫ = -⟪g, g_ii⟫`.
   This is exactly one integration by parts in the direction `e_i` — obtained abstractly from
   unitarity of translation, not from a concrete cylinder integral.
2. `real_inner_self_eq_norm_sq` turns the LHS into `‖g_i‖²`.
3. Cauchy–Schwarz (`abs_real_inner_le_norm`): `‖g_i‖² ≤ ‖g‖ · ‖g_ii‖`.
4. `word_norm_le` at the word of length `n+2`: `‖g_ii‖ ≤ ‖u‖`.

So YES, the proof genuinely uses the second derivative in direction `i` (the array coordinate at word
`Fin.cons i (Fin.cons i w)`, length `n+2`), and `n+2 ≤ s` is genuinely what makes it available in two
independent ways: (a) the word of length `n+2` must be a legal index (`Fin (s+1)`), and (b)
`word_hasDerivAt` for the child needs `n+1 < s`, i.e. `n+2 ≤ s`. With only `n+1 ≤ s` the child exists
but has no derivative coordinate and the proof cannot start. The hypothesis is tight, not decorative.

### Question 3 in detail: vacuity / junk check

* **Both sides are honest real numbers.** `‖·‖` on `LiftL2 period = Lp Vector3 2 (liftMeasure period)`
  is the genuine L² norm on `ℝ³ × 𝕋_period` with `liftMeasure = volume ⊗ Haar` (`EulerProof.lean:1092-1100`),
  a non-degenerate measure. `‖u‖` on `SobolevSpace period s` is the sup norm over the finitely many
  words: `‖u‖ = max_{|w| ≤ s} ‖∂^w u‖_{L²}` (Mathlib Pi sup norm, confirmed by the proofs at
  `CylinderSobolevOperators.lean:28` `norm_le_pi_norm` and `:41` `pi_norm_le_iff_of_nonneg`).
* **No side is defined to be 0.** `word` (`CylinderSobolevSpace.lean:66`) is a plain array lookup with
  *no* out-of-range/junk branch. (Contrast `SpatialJet.word`, `EulerProof.lean:3393-3399`, which DOES have
  a junk branch `| _n+1, .zero _ => 0`; that function is used only inside `word_unique` / `jet_word_eq`,
  always guarded by `n ≤ s`, so the junk branch is unreachable there. Flagged below anyway.)
* **The inequality is not a triviality.** `word_norm_le` alone gives `‖g_i‖ ≤ ‖u‖`, i.e. `‖g_i‖² ≤ ‖u‖²`.
  The theorem gives the strictly stronger `‖g_i‖² ≤ ‖g‖·‖u‖`, which is what makes the Cauchy ladder in
  `SobolevCauchyInterpolation.lean` work (small parent ⇒ small child). Real content.
* **Concrete check.** Take a nonzero smooth compactly supported field `u₀` on the cylinder whose full
  L² translation orbit is `C^∞` (`SmoothOrbit`, `CylinderSmoothOrbit.lean:26-27`); then
  `spatialJet` (`CylinderSmoothOrbit.lean:64-72`) builds the strong-derivative tree from
  `orbitDerivative` (= `fderiv` of the orbit), and `ofJet` (`CylinderSobolevSpace.lean:78-83`) turns it
  into an element `u` of `SobolevSpace period s` with `value u = u₀` (`value_ofJet`, `:87-88`) and
  `word u w = ∂^w u₀` in L². Both sides of the inequality are then the numbers one expects:
  LHS `= ‖∂_i∂^w u₀‖²_{L²}`, RHS `= ‖∂^w u₀‖_{L²} · max_{|v| ≤ s} ‖∂^v u₀‖_{L²}`.
* **THE MOST IMPORTANT QUESTION — answered in the good direction.** The derivative coordinates are NOT
  unconstrained bundled data. Membership in `sobolevSubspace` (`CylinderSobolevSpace.lean:44-46`) is
  the intersection over *all* edges `(w, w·i)` of the pullback of the closed graph of the strong
  translation derivative, so for each parent/child pair the child IS the strong L² derivative of the
  parent along `standardDirection i`. `word_hasDerivAt` (`:70-75`) is the projection of that fact and its
  proof is literally `ClosedSubmodule.mem_iInf.mp u.property`. Additionally `value_injective` (`:128`)
  proves the whole array is determined by the single L² field, so there is no freedom to fake
  derivatives. `derivativeOperator_hasDerivAt` (`CylinderSobolevDerivatives.lean:82-96`) confirms the
  same at the level of the operator and the underlying value.
* **Residual vacuity risk (NOT resolved by me, see Escalations):** nothing in the audited files exhibits
  a *nonzero* inhabitant of `SobolevSpace period q` for `q ≥ 1`. All constructions are conditional on a
  `SmoothOrbit` / jet hypothesis supplied elsewhere; my greps found no theorem whose conclusion is
  `SmoothOrbit period <concrete nonzero field>` (all 142 files mentioning `SmoothOrbit` use it as a
  hypothesis or propagate it: `CylinderSmoothOrbit.lean:44`, `CylinderClassicalWordBounds.lean:60`,
  `CylinderOrbitSobolev.lean:84`). The space is not degenerate *by definition*, but I did not verify a
  nonzero inhabitant is ever produced.

## Kernel-risk assessment

Automated scan over the 8 fully-read files
(`SobolevInterpolation`, `SobolevPathInterpolation`, `SobolevTranslationDifferentiation`,
`CylinderSobolevSpace`, `CylinderSobolevOperators`, `CylinderSobolevDerivatives`,
`ClosedTranslationGraph`, `SobolevRestriction`) plus `SobolevCauchyInterpolation`:

| pattern | count | notes |
|---|---|---|
| `decide` | **0** | — |
| `native_decide` | **0** | — |
| numerals with ≥ 4 digits | **0** | — |
| `Nat.pow` / `Nat.div` / `Nat.mod` / `Nat.gcd` | **0** | only `Nat.lt_succ_of_le`, `Nat.succ_le_of_lt`, `Nat.le_of_lt_succ`, `Nat.zero_lt_succ`, `Nat.succ_lt_succ` (proof-level, no computation) |
| `termination_by` | **0** in these files | but see `SpatialJet.word`, `EulerProof.lean:3399` (`termination_by s`) reached via `value_injective` |
| `WellFounded` | **0** | — |
| `.rec` / `.recOn` / `.brecOn` / `Acc.rec` | **0** | inductions are `induction … with` and `Fin.cases`, elaborated normally |
| `axiom` / `unsafe` / `partial` / `macro` / `elab` / `syntax` / `set_option` | **0** | — |
| `sorry` / `admit` | **0** | — |
| `rfl` closing a goal | 21 occurrences | ALL are projections of a subtype/Pi definition (`wordPathOperator_apply` `SobolevPathInterpolation.lean:61`, `wordPath_sub` `:87`, `liftOperator_apply` `CylinderSobolevOperators.lean:88`, `value_liftOperator` `:109`, `truncateOperator_apply` `CylinderSobolevDerivatives.lean:51`, `derivativeOperator_apply` `:57`, `value_truncateOperator` `:78`, `derivativeOperator_translation` `:101`, `restrictOperator_apply` `SobolevRestriction.lean:29`, `restrict_eq_truncate` `CorrectionFamilyCompactness.lean:28`, plus `Finset.sum_congr rfl` uses). No `rfl` on recursive data, no `rfl` forcing numeral arithmetic. |
| `fin_cases` | 1 (`CylinderSobolevDerivatives.lean:88`) | on `j : Fin 1`. Trivial. |
| `Fintype.card (SobolevWord q)` | `CylinderSobolevOperators.lean:47,49` | symbolic in `q`; appears only as a real cast inside inequalities |

**`Fin 4` and `Fin n → Fin 4` enumeration.** In the audited chain the kernel never enumerates them:
sums over `SobolevWord q` (`sumNorm`, `CylinderSobolevOperators.lean:35`) and over `Fin 4` are always
handled by *symbolic* lemmas (`Finset.single_le_sum`, `Pi.sum_norm_apply_le_norm`, `Fintype.sum_sigma`,
`Fin.sum_univ_eq_sum_range`, `Finset.sum_congr`), never by `decide`/`Finset.decide` and never at a
concrete `q` in these files. Word arguments are handled by `Subsingleton.elim` (for `Fin 0 → Fin 4`,
`CylinderSobolevSpace.lean:114`, `SobolevCauchyInterpolation.lean:28`), `Fin.cons_self_tail`,
`Fin.init`/`Fin.snoc` lemmas — all symbolic.

**LATENT (not triggered here, worth a downstream check):** `Fintype.card (SobolevWord q)` is
`∑_{n=0}^{q} 4^n = (4^{q+1}-1)/3`. Two sites instantiate it at a CONCRETE order:
`Euler/CylinderPathProductBounds.lean:49` (`Fintype.card (SobolevWord 6)` = 5461) and, indirectly,
files using `SobolevSpace period 7` (card 21845, e.g. `Euler/SobolevBaseCommutator.lean:25`). At those
sites the card is only ever used symbolically (`positivity`, `ring`, `mul_le_mul_of_nonneg_left`;
`productBlockConstant` at `CylinderPathProductBounds.lean:48` is never numerically evaluated — checked
all 10 use sites). If any tactic (`decide`, `norm_num` on a `Fintype.card` goal, `simp` with card
lemmas) ever forced one of these, the kernel would have to enumerate up to 21845 functions
`Fin n → Fin 4`. Currently NOT forced anywhere I could see.

**One inherited item:** `SpatialJet.word` (`EulerProof.lean:3393-3399`) is a well-founded recursion
(`termination_by s`) with a junk `0` branch, and its equation lemmas are used by `rw [word]`
(`:3403`, `:3411`). It enters my subtree through `value_injective` → `SpatialJet.word_unique`
(`EulerProof.lean:4549`), hence through `sobolevTranslation_hasDerivAt` and several `restrict_eq_...`
lemmas — but NOT through `word_square_le_parent` itself. Verdict for my scope: KERNEL-RISK (low),
because unfolding is done via equation lemmas rather than kernel reduction of `WellFounded.fix`.

Overall verdict counts across the declarations I inspected: **OK 33, UNCLEAR 0, KERNEL-RISK 1
(`SpatialJet.word`, inherited, low), SUSPICIOUS 0.**

## Escalations

1. **NOT an escalation about this file — a correction of expectations.** The interpolation inequality is
   real, proved, and about the right object. The Sobolev element does NOT bundle unconstrained
   derivative data: the derivative relation is the *defining condition* of the space and is extracted by
   `word_hasDerivAt` (`CylinderSobolevSpace.lean:70-75`), reinforced by `value_injective` (`:128`).
2. **The "compactness engine" is not compactness — it is a conditional upgrade.**
   `cauchy_restrict_of_value` (`SobolevCauchyInterpolation.lean:78-86`) requires the sequence to already
   be **Cauchy in L² uniformly in time** (`h0`) plus a **uniform `H^s` bound**; it then gives Cauchy in
   `H^q`, `q < s`. No subsequence is extracted anywhere, so no Rellich-type compactness is claimed or
   needed. The L²-Cauchy input is supplied by `correction_family_cauchy`
   (`Euler/CorrectionFamilyCompactness.lean:70`, from `Euler/ViscosityCauchy.lean`), i.e. by a
   quantitative viscosity-difference estimate. **Whoever audits the Euler limit must audit
   `ViscosityCauchy` — that is where the actual analytic risk sits, not here.** I did not audit it.
3. **Non-vacuity of the whole construction is not established inside my scope.** No lemma in the audited
   files (nor found by grep across `Euler/`) produces a nonzero inhabitant of `SobolevSpace period q`
   for `q ≥ 1`, i.e. no `SmoothOrbit period <concrete nonzero field>` witness. Everything is conditional
   on that datum being supplied by the packet/base-construction files. Someone should verify the base
   Euler datum really lands in these spaces with nonzero value; otherwise the chain is formally correct
   but could be about the empty (only-zero) situation.
4. **Latent kernel hazard to watch (not currently triggered):** `Fintype.card (SobolevWord 6)` = 5461
   at `CylinderPathProductBounds.lean:49`, and `SobolevSpace period 7` (card 21845) in
   `SobolevBaseCommutator.lean`. A future `decide`/`norm_num`/`simp` that forces such a card would make
   the kernel enumerate thousands of functions `Fin n → Fin 4`.

## Residue

* I could not run `lake build` (no Mathlib on disk), so every "proved" verdict is a *source-level
  reading* verdict: I verified the proof scripts are complete, cite existing lemmas with matching
  signatures, and contain no `sorry`/`axiom`. I did NOT verify they elaborate.
* Mathlib lemma names/orientations I relied on but did not check against a built Mathlib:
  `real_inner_self_eq_norm_sq`, `abs_real_inner_le_norm`, `neg_le_abs`, `norm_le_pi_norm`,
  `pi_norm_le_iff_of_nonneg`, `Pi.sum_norm_apply_le_norm`, `cauchy_pi_iff'`,
  `hasDerivAt_of_tendstoUniformly`, `Lp.compMeasurePreservingₗᵢ`, and the fact that the Pi norm on a
  Fintype index is the SUP norm (this last one is load-bearing for my reading of `‖u‖`; if it were the
  sum norm the inequality would still be true and still non-trivial, only the constant story changes).
* `Euler/EulerProof.lean` was only sampled around the declarations I needed. `ViscosityCauchy.lean`,
  `SobolevPathLimits.lean`, `OrdinaryCauchyInterpolation.lean` and the divergence-free/trace machinery
  in `CorrectionFamilyCompactness.lean` were NOT audited.
* I did not check whether `SpatialJet.word`'s well-founded compilation causes any real kernel cost, and
  I did not attempt to measure elaboration times anywhere.
