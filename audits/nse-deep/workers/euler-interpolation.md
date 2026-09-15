# Worker report: Euler `Icc`-endpoint derivative upgrade & the Sobolev interpolation that replaces Rellich

Repo audited (READ-ONLY): `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`
(clone of `openai/NavierStokesAndEuler`). No Mathlib build on this box (disk full);
this is source-level reading (grep + line-by-line). **Nothing under `NSE/` was modified.**

Predecessor read first, as instructed: `audits/nse-deep/workers/euler-cauchy-endpoint.md`.
This report answers its **Escalation 6** (the `Ioo`-vs-`Icc` endpoint of `time_law`) and
**Escalation 7** (the interpolation lemma that replaces Rellich compactness), and
incidentally settles its **Escalation 3** (the `Fact (0 < (1:ℝ))` instance).

**Headline: no gap. Both key steps are genuinely PROVED, not assumed and not vacuous.**
The endpoint derivative is obtained by *integrating* (FTC), which is the mathematically
correct route and needs no one-sided-derivative subtlety at all. The interpolation is the
classical Landau/Kolmogorov estimate and it delivers something *stronger* than
Rellich compactness — but only because it is fed a *stronger* hypothesis (the sequence is
L²-**Cauchy**, not merely bounded). See `## The compactness question` for why that is
honest rather than circular, and Escalation 1 for the one thing this shifts.

---

## Scope

Assigned files, read IN FULL, line by line, both of them:

| file | lines | `theorem` | `def` | `instance` | `structure`/`inductive` | total decls | read line-by-line | skimmed |
|---|---|---|---|---|---|---|---|---|
| `Euler/SmoothFieldSobolevTime.lean` | 113 | 7 | 2 | 1 | 0 | **10** | 10/10 | 0 |
| `Euler/SobolevCauchyInterpolation.lean` | 96 | 5 | 1 | 2 | 0 | **8** | 8/8 | 0 |

Both counts were cross-checked against `audits/nse-deep/CONE.csv` (10 and 8 rows
respectively — exact match, so no declaration was missed).

Because both assigned theorems are **one-line delegations of their hard content**
(`:86-93` delegates to `EulerSeparatingTimeDerivative.hasDerivWithinAt`; `:78-85`
delegates to `EulerSobolevPathInterpolation.wordPath_cauchy_step`), answering the
assigned questions required reading the callee chain. Read IN FULL outside the nominal scope:

* `Euler/SeparatingTimeDerivative.lean` (68 lines, 3 theorems) — **where the endpoint upgrade actually happens**;
* `Euler/SobolevPathInterpolation.lean` (111 lines, 10 decls) — **where the interpolation actually happens**;
* `Euler/SobolevRestriction.lean` (75 lines, 11 decls);
* `Euler/OrdinaryCauchyInterpolation.lean` (100 lines, 8 decls) — the sole consumer of `SobolevCauchyInterpolation.lean:78`;
* `Euler/SobolevPointEvaluation.lean` (77 lines, 7 decls) — the separating family's bottom;
* `Euler/CorrectionFamilyCompactness.lean` (68 lines, 3 decls) — the second consumer of `:88`;
* `Euler/CylinderSobolevSpace.lean:1-145` (the `SobolevSpace` definition, `value_injective`, `word_hasDerivAt`);
* `Euler/CylinderSobolevOperators.lean:1-60` (`valueOperator`, `wordOperator`, `word_norm_le`).

Spot-read (targeted ranges, not whole files): `Euler/OrdinarySmoothLimit.lean:1-70`,
`Euler/OrdinaryWordTime.lean:55-99`, `Euler/SmoothEulerEvolution.lean:55-125`,
`Euler/OrdinaryEulerHigherEnergy.lean:30-70`, `Euler/VolterraConvolution.lean:20-24`.

Two sub-chains were delegated to read-only children:
`_sub-endpoint-ftc-integral.md` (the FTC/Bochner integral machinery under the endpoint
upgrade) and `_sub-sobolev-interpolation-ineq.md` (`word_square_le_parent`, the
interpolation inequality itself, and whether the Sobolev "derivative coordinates" are
*proved* derivatives). Their results are folded in at `## Delegated sub-chains`.

### Verdict counts (18 in-scope declarations)

**16 OK, 2 OK-with-remark, 0 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS.**
Out-of-scope chain rows: 24 OK, 1 **name-overclaims** (`CorrectionFamilyCompactness`, harmless — see row).
Delegated children: **13 OK / 1 UNCLEAR (off-path)** and **33 OK / 1 low inherited KERNEL-RISK**; **0 adverse findings on the audited path.**

---

## Part A — `SmoothFieldSobolevTime.lean`: what exactly is upgraded, and by which lemma

### A.1 The two statements, and the difference between them

The file's `variable` block (`:77-83`) fixes the input:

```lean
variable (T : ℝ) (hT : 0 ≤ T)
  (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
  (hd : ∀ t (ht : t ∈ Ioo 0 T) x,                       -- ← OPEN interval only
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).field x)
      ((B ⟨t,ht.1.le,ht.2.le⟩).field x) t)
```

So the hypothesis `hd` is: *pointwise in space*, on the **open** interval `Ioo 0 T`,
`t ↦ A(t)(x)` has derivative `B(t)(x)`. This is exactly the shape of `Evolution.time_law`
(`OrdinaryEulerDifference.lean:28`), with `B` = the Euler right-hand side.

The conclusion of **`sobolevPath_hasDerivWithinAt` (`:96-104`)** — the assigned line — is:

```lean
theorem sobolevPath_hasDerivWithinAt (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath A hA q))
      (sobolevPath B hB q t) (Icc (0 : ℝ) T) t
```

**Two upgrades happen at once, and it is important not to conflate them:**

1. **Pointwise → strong.** `hd` is a derivative of *real-vector-valued* functions
   `t ↦ A(t)(x)` for each fixed `x`. The conclusion is a derivative *in the Sobolev-space
   norm* `SobolevSpace 1 q` — a genuinely stronger statement (norm convergence of
   difference quotients, not pointwise).
2. **`Ioo` → `Icc`, i.e. the ENDPOINT upgrade.** `t : Icc (0:ℝ) T` is **universally
   quantified over the closed interval**, so the theorem asserts a within-`Icc`
   (one-sided) derivative at `t = 0` and at `t = T`, where `hd` says nothing.

Note also there is **no `3 ≤ q` hypothesis** at `:96`, whereas the helper `:86` has one.
`:96` obtains the unrestricted-`q` version by proving it at order `q+3` and pushing down
through the *bounded linear* `restrictOperator 1 (q ≤ q+3)` (`:100`), then rewriting with
`restrict_sobolev` (`:44`). Composing a CLM with a within-derivative is the **safe
direction** (`ContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt`) — no derivative is
pulled *back* through anything. `3 ≤ q` is needed at `:86` only because `observation`
(`:52`) needs the H³ Sobolev embedding, and the cylinder domain `LiftDomain 1` has
dimension 4 (words are `Fin n → Fin 4`, `CylinderSobolevSpace.lean:15`), so
`H^s ↪ C⁰` needs `s > 4/2 = 2`; `s = 3` is the sharp integer choice. **This is a
consistency signal, not a fudge.**

### A.2 The endpoint upgrade is done by `EulerSeparatingTimeDerivative.hasDerivWithinAt`, via the INTEGRAL

`:90-93` is the whole proof of `:86`:

```lean
apply EulerSeparatingTimeDerivative.hasDerivWithinAt T hT (sobolevPath A hA q)
  (sobolevPath B hB q) (observation q hq) (observation_injective q hq)
intro x r hr
simpa only [extendPath,sobolevPath,ContinuousMap.coe_mk,observation_apply] using hd r hr x.1
```

so the upgrading lemma is **not** a Mathlib lemma; it is the repo's own
`Euler/SeparatingTimeDerivative.lean:49`. That lemma's mechanism, read in full:

**Step 1 (`eq_initial_add_integral`, `SeparatingTimeDerivative.lean:24-46`).**
It first proves the *integral identity* `f t = f 0 + ∫₀ᵗ g`, for every `t : Icc 0 T`
**including the endpoints**. Mechanism: apply the separating family (`hsep`, `:26`), so
it suffices to prove it after each bounded functional `L i`; then the scalar identity is
exactly Mathlib's **FTC-2**

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
  hc.continuousOn (f' := fun r => L i (extendPath T hT g r))
  (fun r hr => …) (hg.intervalIntegrable 0 t)                     -- :36-42
```

`integral_eq_sub_of_hasDerivAt_of_le` is precisely the version of FTC-2 that requires
**(a)** continuity of the antiderivative on the *closed* interval `[0,t]`,
**(b)** `HasDerivAt` only on the *open* interval `Ioo 0 t`, **(c)** interval-integrability
of the derivative. All three are genuinely supplied:
(a) `hc := (L i).continuous.comp (extendPath_continuous T hT f)` (`:29-30`) — global
continuity of the clamped extension, a proved lemma
(`VolterraConvolution.lean:24`, and `extendPath T hT f t = f (projIcc 0 T hT t)`,
`VolterraConvolution.lean:20`, i.e. a genuinely *clamped* extension);
(b) `hd i r hrT` with `hrT : r ∈ Ioo 0 T` derived from `r ∈ Ioo 0 t` by
`hr.2.trans_le t.property.2` (`:39`) — so **only the open-interval hypothesis is used**;
(c) `hg.intervalIntegrable 0 t` (`:42`) from continuity. Integrability is **proved**, so
the Mathlib junk value `∫ (non-integrable) = 0` is *not* in play.

**Step 2 (`hasDerivWithinAt`, `:49-60`).** The primitive
`r ↦ f 0 + realIntegral T hT g r` is differentiated by `realIntegral_hasDerivAt`
(`:53`) — FTC-1 for the *continuous* clamped integrand `extendPath T hT g`, which gives a
genuine **two-sided** `HasDerivAt` at *every real* `t`, hence in particular at `0` and at
`T`; `.hasDerivWithinAt` (`:56`) weakens it to the within-`Icc` statement. Then
`HasDerivWithinAt.congr_of_mem` (`:57`) transports the derivative from the primitive to
`extendPath T hT f`, and the congruence is supplied **exactly on `Icc 0 T`**
(`intro r hr; … eq_initial_add_integral … ⟨r,hr⟩`, `:58-60`) with `t ∈ Icc` from
`t.property`. That is precisely the hypothesis shape `congr_of_mem` needs, and it is
sound: a within-`s` derivative only depends on the function's values on `s`.

**So the answer to the assigned question is: the endpoint value is not obtained by any
one-sided-derivative gymnastics, and no junk value is used. It is obtained by proving the
Duhamel/integral identity on the closed interval (which needs only interior
differentiability + continuity) and then differentiating the integral, which is
differentiable everywhere.** This is the textbook-correct construction and it is the
strongest available: `realIntegral_hasDerivAt` even gives two-sided differentiability of
the primitive at the endpoint. **Verdict: OK, and cleanly so.**

### A.3 Is the endpoint claim non-vacuous?

* For `T = 0`: `Icc 0 0 = {0}`, and `HasDerivWithinAt` on a singleton is trivially true
  (the relevant filter `𝓝[{0}\{0}] 0 = ⊥`). So at `T = 0` the theorem is vacuous — but
  harmlessly, and every consumer has `0 < T` (e.g. `SmoothEulerEvolution.lean:59`'s
  callers, `OrdinaryEulerHigherEnergy.lean:64-70`).
* For `T > 0` at `t = 0` (and `t = T`): `𝓝[Icc 0 T \ {0}] 0 ≠ ⊥`, so a **real
  one-sided derivative in the Sobolev norm is being asserted**, and per A.2 it is
  really proved. Not vacuous.
* No junk-value escape hatch: the derivative *value* is `sobolevPath B hB q t`, i.e. the
  prescribed field `B` at the endpoint, not `0`. `fderiv` does not appear in this file at
  all (0 occurrences); the `fderiv` of the Euler law lives one level up
  (`SmoothEulerEvolution.lean:62`) applied to `SmoothL2Field.field`, which carries
  `ContDiff ℝ ∞`, so it is not the `fderiv`-of-a-non-differentiable-function junk value.

### A.4 The separating family is genuinely separating (this is what makes "pointwise → strong" legitimate)

The suspicious-looking part of the design is that a *pointwise* hypothesis yields a
*strong* conclusion. It is legitimate here because the strong information enters through
`hB` (continuity of **all L² jets** of `B`, hence continuity of `sobolevPath B hB q`
in the Sobolev norm, `continuous_sobolev` `:24-38`), and the pointwise family is only used
to *identify* the strong primitive. Concretely:

* `observation q hq x := (pointEvaluation 1 x).comp (restrictOperator 1 hq)` (`:52-53`)
  is a composition of two **bounded linear** maps. `pointEvaluation`
  (`SobolevPointEvaluation.lean:64-69`) is a real CLM: it evaluates the *continuous
  representative* of an H³ field and its operator norm bound is the genuine Sobolev
  embedding bound `sobolevEmbeddingConstant period 3` (`representative_bound`, `:37-45`,
  which upgrades an a.e. bound to a pointwise bound using continuity plus
  `Measure.dense_of_ae` — correct, and needs the lift measure to have full support).
* `observation_apply` (`:55-66`) proves `observation q hq x (ordinarySobolev q A.toLp _) = A.field x.1`.
  So the observation really returns **the value of the field at the space point `x.1`** —
  the family is pinned to the intended meaning, not free-floating.
* `observation_injective` (`:68-75`) is proved from `value_injective 1`
  (`CylinderSobolevSpace.lean:128`) plus `representative_ae`: if all point evaluations
  agree, the a.e.-representatives agree a.e., hence the L² values are equal, hence the
  Sobolev elements are equal. **`value_injective` is itself a real theorem** — the whole
  derivative array is determined by its order-0 coordinate, by *uniqueness of strong
  derivatives* (`SpatialJet.word_unique`, via `HasDerivAt.unique` in `word_hasDerivAt`,
  `CylinderSobolevSpace.lean:70-75`). Nothing here is definitional trickery.
* **Structural check that matters most**: `SobolevSpace period q` is *not* an
  unconstrained bundle of "derivative" coordinates. It is
  `sobolevSubspace period q` (`CylinderSobolevSpace.lean:44-49`), a **closed submodule**
  of the finite product `SobolevWord q → LiftL2 period` cut out by an `⨅` over edges of
  the *closed graph of the strong translation derivative*. `word_hasDerivAt` (`:70-75`)
  extracts from membership exactly the statement "coordinate at `cons i w` **is** the
  strong derivative of the coordinate at `w` in direction `i`". So the coordinates are
  genuine derivatives by construction, and the norm is the inherited pi (sup-over-words)
  norm (`:52-57`) — a legitimate `H^q`-equivalent norm.

### A.5 Where the endpoint upgrade is consumed — it *is* load-bearing

`grep` for callers of `SmoothFieldSobolevTime.lean:96` (disambiguated from the
same-named cylinder version `CylinderTimeRegularity.lean:70`, which takes a leading
`period` argument):

* `Euler/SmoothEulerEvolution.lean:68` (in `sobolev_evolution`, `:59-71`) — turns the
  Euler pointwise law into a strong Sobolev-valued within-`Icc` derivative;
* `Euler/OrdinaryWordTime.lean:82` (in `ordinaryWord_hasDerivWithinAt`, `:78-84`)
  → `wordEnergy_hasDerivWithinAt` (`:87-97`)
  → `Evolution.integerEnergy_hasDerivWithinAt` (`OrdinaryEulerHigherEnergy.lean:48-54`)
  → `Evolution.integer_energy_bound` (`:64-70`), whose Grönwall hypothesis is
  `hd (r : ℝ) (hr : r ∈ Ico 0 T)` — **`Ico`, i.e. it needs the derivative AT `r = 0`.**

That last line is the exact point the predecessor flagged (its Escalation 6):
the H³ Grönwall bound `M` — which is what supplies the uniform bound feeding the
compactness step in `exists_smooth_endpoint` — genuinely requires the left-endpoint
derivative, and the bridge that supplies it is `SmoothFieldSobolevTime.lean:96`.
**Escalation 6 of the predecessor is hereby resolved in the artifact's favour: the
bridge exists, it is at `:96`, and it is proved by the FTC route of A.2, not assumed.**

---

## Part B — `SobolevCauchyInterpolation.lean`: what the interpolation delivers, and who consumes it

### B.1 The statement at `:78`

```lean
theorem cauchy_restrict_of_value {s q : ℕ} (hq : q < s) (T M : ℝ) (hM : 0 ≤ M)
    (u : ℕ → C(Icc (0 : ℝ) T,SobolevSpace period s)) (hu : ∀ k, ‖u k‖ ≤ M)
    (h0 : CauchySeq (fun k => (valueOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k))) :
    CauchySeq (fun k => (restrictOperator period hq.le).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u k))
```

In words: a sequence of time-paths valued in the order-`s` Sobolev space, **uniformly
bounded in the sup-in-time order-`s` norm** and **Cauchy in the sup-in-time L² norm**, is
Cauchy in the sup-in-time order-`q` norm for every `q < s`.

**This is NOT compactness.** Compactness would be: *bounded* ⟹ *some subsequence
converges*. What is proved is: *bounded + already-Cauchy-in-L²* ⟹ *the whole sequence is
Cauchy in `H^q`*. That is a different (and, given its hypothesis, stronger) statement.
The predecessor's chain description ("interpolation substitutes for Rellich") is accurate,
and the substitution is legitimate **only because the producer supplies L²-Cauchyness**.
See `## The compactness question` for the audit of exactly that.

### B.2 The mechanism — genuine Landau/Kolmogorov interpolation, and the exponent bookkeeping is right

`:82-85` reduces to coordinates and then to `wordPath_cauchy_of_value` (`:21-37`), an
**induction on word length `n`** (`:27`):

* base `n = 0`: `w = Fin.elim0` by `Subsingleton.elim` (`:30`), and the goal is closed by
  `exact h0` (`:32`). This works because the length-0 word coordinate **is** the
  `valueOperator` coordinate (`emptyWord`, `CylinderSobolevOperators.lean:20-21` vs
  `SobolevPathInterpolation.lean:54-56`), definitionally up to proof irrelevance of the
  `Fin` bound. Not a fudge: it is the same projection.
* step `n → n+1` (`:33-37`): `wordPath_cauchy_step period (by omega : n+2 ≤ s) (Fin.tail w) (w 0) …`,
  reassembled by `Fin.cons_self_tail`.

`wordPath_cauchy_step` (`SobolevPathInterpolation.lean:103-109`) is
`cauchySeq_of_square_bound` (`:14-30`: from `‖g m − g n‖² ≤ A‖f m − f n‖` and `f` Cauchy,
conclude `g` Cauchy — an honest ε/`ε²/(A+1)` argument) applied to
`wordPath_difference_square_bound` (`:90-100`), which is `clm_difference_square_bound`
(`:33-43`) applied to **`wordPath_square_bound` (`:64-80`)**:

```lean
‖wordPathOperator (n+1 ≤ s) (Fin.cons i w) T u‖^2 ≤ ‖wordPathOperator (n ≤ s) w T u‖ * ‖u‖
```

i.e. `‖∂ᵢ D^w u‖²_{sup t} ≤ ‖D^w u‖_{sup t} · ‖u‖_{H^s, sup t}`, proved pointwise in time
from `word_square_le_parent period h (u t) w i` (`:75`) and then sup'd
(`ContinuousMap.norm_le` + `norm_coe_le_norm`, `:72-77`). **This is the classical
Landau/Kolmogorov estimate `‖∂f‖² ≤ ‖f‖·‖∂∂f‖`** with the second derivative absorbed into
the order-`s` norm — and that is exactly why the hypothesis is `n+2 ≤ s` and not
`n+1 ≤ s`: the word `∂ᵢ∂ᵢ D^w` has length `n+2` and must still be inside the order-`s`
array. The `omega` at `:35` derives `n+2 ≤ s` from `hn : n+1 < s`. **The bookkeeping is
correct and tight**; there is no place where an exponent could be off by one without the
`omega` failing.

The loss is a square root per derivative order (`‖g‖² ≤ 2M‖f‖`), which is irrelevant for
a purely qualitative Cauchy conclusion. The `clm_difference_square_bound` step
(`:36-43`) applies the inequality to the **difference** `u − v` (`hb := h (u-v)`,
`map_sub` at `:40`) and bounds `‖u−v‖ ≤ 2M` from the two uniform bounds — so the
inequality really is applied to differences, as the predecessor's Escalation 7 asked.

`pathCoordinates_norm` (`:46-60`) proves the coordinate map is a **norm isometry** —
`sup_t sup_w = sup_w sup_t`, both inequalities proved — and
`path_cauchy_of_coordinates` (`:63-75`) uses `AddMonoidHomClass.isometry_of_norm` +
`Isometry.isUniformInducing.cauchy_map_iff` + `cauchy_pi_iff'`. Standard, correct, and
the isometry (rather than a mere bound) is what makes the coordinate reduction lossless.

### B.3 The consumers, and whether the shape matches

`grep` gives exactly **two** consumers of this file:

1. **`Euler/OrdinaryCauchyInterpolation.lean:83`** inside `sobolevPath_cauchy_of_l2`
   (`:60-89`) — the Euler route. It instantiates `s := q+1`, so it uses the uniform
   order-`(q+1)` bound to get Cauchyness at order `q`. The hypotheses are supplied as:
   `hu` from `sobolevPath_norm_le_tensor` (`:53-58`) + the assumed `hb (q+1)` (`:66`), and
   `h0` (L² Cauchy) is *transported* from the assumed `CauchySeq (fieldPath (A k))` via
   `ordinarySobolev_value` (`:75-82`) — a genuine identification of the `valueOperator`
   coordinate with the L² field, not an assumption. Then
   `exists_sobolevPath_limit` (`:91-98`) = `cauchySeq_tendsto_of_complete`.
   **Consumer of that:** `nonempty_smoothLimitData` (`OrdinarySmoothLimit.lean:34-60`),
   which needs precisely
   `sobolev_convergence : ∀ q, Tendsto (fun k => sobolevPath (A k) (hA k) q) atTop (𝓝 (tower.realization q))`
   (`:31-32`). **Shape matches exactly** — full-sequence convergence at every fixed order,
   which is what `exists_sobolevPath_limit` delivers via `choose` (`:40`).
   Crucially, `nonempty_smoothLimitData` also *proves* the coherence field
   `value_eq` (`:41-59`) by `tendsto_nhds_unique`, i.e. it proves that the limits at
   different orders all have the **same underlying L² field** `u`. Without that, the
   per-order limits could be unrelated objects; it is proved, so they are not.
2. **`Euler/CorrectionFamilyCompactness.lean:41`** inside `exists_limit_with_constraints`
   (`:31-49`) — the viscosity/NS side, outside this worker's Euler scope. Same shape:
   the `hCauchy` hypothesis is explicit in the statement (`:35`) and is *discharged* one
   level up by `correction_family_cauchy` (`:64`) from Cauchy viscosities. See the
   name-overclaim remark in the table.

**Answer to the assigned question: the interpolation delivers exactly what the consumer
consumes (norm convergence of the whole sequence at each fixed Sobolev order, uniformly
in time). It is not a weaker statement dressed up as compactness — it is a
*differently-hypothesised* statement, and the extra hypothesis (L² Cauchyness) is
genuinely established by the producer.**

---

## The compactness question, stated loudly

The Euler limit construction **never uses a compactness theorem**. There is no
Rellich-Kondrachov, no Banach-Alaoglu, no Arzelà-Ascoli, and no subsequence extraction
anywhere on this route. The full logical shape is:

```
Cauchy INITIAL data (L²)                             [exists_smooth_endpoint: σₙ•A, σₙ → 1]
  --Grönwall L² stability (cauchyPath_of_initial)-->  Cauchy velocity PATHS in sup-t L²
  --uniform H^q bounds at EVERY order (all_order_bounds_of_h3)
  --INTERPOLATION (SobolevCauchyInterpolation:78)-->  Cauchy in sup-t H^q, every q
  --completeness (cauchySeq_tendsto_of_complete)-->   a single limit path, all orders coherent
  --Duhamel + Helmholtz (OrdinaryEulerLimit:27,55)--> the limit satisfies time_law
```

This is a legitimate architecture and, if anything, *cleaner* than the compactness route,
because it produces convergence of the whole sequence rather than a subsequence.
**But it relocates the entire analytic burden onto the producers of L²-Cauchyness**, i.e.
onto the Grönwall L² stability estimate `velocityPath_norm_sub_le`
(`OrdinaryEulerL2Stability.lean:136`) and onto `Evolution.all_order_bounds_of_h3`
(`OrdinaryEulerCauchy.lean:70`). The predecessor audited both and found them OK; I did not
re-derive them. **This is Escalation 1 below: the interpolation file is clean, so if the
limit construction is wrong, the error is now in the Grönwall estimates, not here.**

One further point worth stating: because the route is Cauchy-based, nothing is lost by the
absence of compactness *in this development*, but the development is thereby **unable** to
handle a merely-bounded (non-Cauchy) approximating family. I checked that no consumer
needs that: both consumers supply Cauchyness explicitly.

---

## Per-declaration findings

`cone` = `in_cone` column of the regenerated `audits/nse-deep/CONE.csv` (mark-3
over-approximation: `False` is meaningful, `True` is weak evidence).

### `Euler/SmoothFieldSobolevTime.lean` (10/10 read line-by-line)

| # | declaration | file:line | what the statement says (my words) | how the proof establishes it (real mechanism) | cone | verdict |
|---|---|---|---|---|---|---|
| 1 | `_anon` instance `Fact (0 < (1:ℝ))` | `:20` | the number `1` is a positive real | `⟨by norm_num⟩`. **This is a PERIOD, not an Lp exponent** — `SobolevSpace period q`, `LiftL2 period`, `LiftDomain period` all take a *cylinder period* with `[Fact (0 < period)]` (`CylinderSobolevSpace.lean:31`). The ordinary (non-periodic) field is lifted to the **unit** cylinder, hence `period = 1`. So this instance cannot select a different `Lp` exponent. **Resolves the predecessor's Escalation 3.** | False | OK |
| 2 | `continuous_sobolev` | `:24` | if all L² jets of `A t` are continuous in `t`, then `t ↦ ordinarySobolev q (A t)` is continuous **in the Sobolev norm** | `ordinarySobolev_continuous` reduces to continuity of each `iteratedFDeriv` of the translation orbit at 0; `he` (`:29-36`) identifies that with `multilinearBundling ∘ jetLp n` via the proved `iteratedFDeriv_translation_eq` + `translation_zero`; then `.continuous.comp (hA n)` (`:38`). Real: the strong continuity comes from the *hypothesis* `hA`, through a bounded bundling map | True | OK |
| 3 | `sobolevPath` (def) | `:40` | packages #2 as a `ContinuousMap` `K → SobolevSpace 1 q` | bundling only; content is #2 | True | OK |
| 4 | `restrict_sobolev` | `:44` | `restrictOperator 1 (q ≤ p)` applied to the order-`p` Sobolev element of a field gives the order-`q` one | `value_injective 1` (a real theorem: the array is determined by its order-0 coordinate, by uniqueness of strong derivatives, `CylinderSobolevSpace.lean:128`) + `value_restrictOperator` + `ordinarySobolev_value` twice. Sound: proves equality of two *constrained* arrays by equality of their L² values | True | OK |
| 5 | `observation` (def) | `:52` | the CLM "restrict to H³, then evaluate at the cylinder point `x`" | composition of two CLMs; `pointEvaluation` is bounded by the genuine Sobolev embedding constant (`SobolevPointEvaluation.lean:64-69`, bound at `:37-45`) | True | OK |
| 6 | `observation_apply` | `:55` | `observation q hq x` applied to the Sobolev element of a smooth field returns **`A.field x.1`** | `restrict_sobolev` then `pointEvaluation_eq` with the continuous candidate `fun z => A.field z.1`; the a.e.-agreement is chained from `ordinarySobolev_value`, `ordinaryLift_ae` and `A.toLp_ae` through a measure-preserving projection (`:62-66`). Pins the observation to the intended meaning | True | OK |
| 7 | `observation_injective` | `:68` | the family of all point-observations separates points of `SobolevSpace 1 q` | `value_injective 1` + `Lp.ext` + `filter_upwards` on `representative_ae` for both elements: equal pointwise evaluations ⟹ representatives agree ⟹ L² values equal ⟹ elements equal. Genuine; also *retro-proves* that `pointEvaluation` is not degenerate | True | OK |
| 8 | `sobolevPath_hasDerivWithinAt_of_three_le` | `:86` | **for `3 ≤ q`**: the Sobolev-valued path has a within-`Icc` derivative `sobolevPath B t` at **every** `t ∈ Icc 0 T`, given the pointwise law only on `Ioo 0 T` | one `apply` of `EulerSeparatingTimeDerivative.hasDerivWithinAt` (`SeparatingTimeDerivative.lean:49`) with the separating family #5/#7; the remaining goal is `hd` transported by `observation_apply` (`:92-93`). **The endpoint content is entirely in the callee** — see Part A.2: FTC-2 on `[0,t]` (interior derivative + closed-interval continuity) gives the integral identity, then FTC-1 differentiates the integral at *every* real point, then `congr_of_mem` on `Icc`. No one-sided subtlety, no junk value | True | **OK** |
| 9 | **`sobolevPath_hasDerivWithinAt`** | **`:96`** | **same, for EVERY `q` with no `3 ≤ q`** — the assigned line | proves it at order `q+3` (#8, `by omega`), then composes with the **bounded linear** `restrictOperator 1 (q ≤ q+3)` using `hasFDerivAt.comp_hasDerivWithinAt` (`:100-101`) — the *safe* direction — and rewrites both the function and the derivative value with `restrict_sobolev` (#4) inside `convert! … <;> simp only […]`; a final `rfl` (`:104`) closes the leftover congruence. `convert!` is sound here: it replaces the goal by congruence subgoals that must all be discharged, and they are | True | **OK** (see remark) |
| 10 | `sobolevPath_hasDerivAt` | `:107` | on the **open** interval the within-`Icc` derivative is a genuine two-sided derivative | `.hasDerivAt (Icc_mem_nhds ht.1 ht.2)` — legitimate: `Icc` is a neighbourhood of interior points | **False** (genuinely unused; the `Icc` version #9 is what consumers want) | OK |

**Remark on #9.** `convert!` + a bare `rfl` is exactly the kind of step where a
mismatch could be papered over, so I looked at it specifically. It cannot hide a gap:
`convert` does not weaken the goal, it *replaces* it by congruence subgoals, every one of
which Lean must close (here by `simp only [… restrict_sobolev]` and one `rfl`). The `rfl`
is on non-recursive structure/`Subtype` projections (`Function.comp_def` unfolding), not
on recursive data. I record it as OK-with-remark only because I could not run the
elaborator to see the intermediate goal states (see `## Residue`).

### `Euler/SobolevCauchyInterpolation.lean` (8/8 read line-by-line)

| # | declaration | file:line | what the statement says (my words) | how the proof establishes it (real mechanism) | cone | verdict |
|---|---|---|---|---|---|---|
| 11 | `cauchySobolevGroup` instance | `:15` | the normed-group structure on `SobolevSpace period q` | `inferInstance`, i.e. a restatement of `sobolevNormedAddCommGroup` (`CylinderSobolevSpace.lean:52`). Diamond-hygiene noise; **does not introduce a new norm** | False | OK |
| 12 | `cauchySobolevSpace` instance | `:18` | ditto for the ℝ-module structure | `inferInstance` (`sobolevNormedSpace`, `:56`) | False | OK |
| 13 | `wordPath_cauchy_of_value` | `:21` | uniform order-`s` bound + L²-Cauchy ⟹ **every** derivative-word path of length `n < s` is Cauchy in sup-in-time L² | induction on `n` (`:27`): base is `exact h0` (the length-0 word coordinate *is* the `valueOperator` coordinate — same projection, defeq up to proof irrelevance); step is `wordPath_cauchy_step` with `n+2 ≤ s` by `omega` (`:35`), reassembled by `Fin.cons_self_tail`. The engine is the Landau/Kolmogorov inequality — see B.2 | True | OK |
| 14 | `pathCoordinates` (def) | `:40` | the path-space element as its finitely many word-coordinate paths | `ContinuousLinearMap.pi` of `wordPathOperator`s; the index bound `Nat.le_of_lt_succ w.1.isLt` is the honest `w.1.val ≤ q` | True | OK |
| 15 | `pathCoordinates_norm` | `:46` | that map is **norm-preserving** (not merely bounded) | `le_antisymm`; `≤` from `word_norm_le` + `norm_coe_le_norm`, `≥` from `pi_norm_le_iff_of_nonneg` + `norm_le_pi_norm`. i.e. `sup_t sup_w = sup_w sup_t`. Exactness is what makes the coordinate reduction lossless | True | OK |
| 16 | `path_cauchy_of_coordinates` | `:63` | coordinatewise Cauchy ⟹ Cauchy in the Sobolev path space | `AddMonoidHomClass.isometry_of_norm` (from #15) + `cauchy_pi_iff'` + `Isometry.isUniformInducing.cauchy_map_iff`. Standard and correct; uses the isometry, so no constant is lost | True | OK |
| 17 | **`cauchy_restrict_of_value`** | **`:78`** | **the interpolation step**: uniformly order-`s`-bounded + L²-Cauchy ⟹ Cauchy at every order `q < s`, uniformly in time | `path_cauchy_of_coordinates` (#16) then, for each word `w : SobolevWord q`, `wordPath_cauchy_of_value … w.1.val ((Nat.le_of_lt_succ w.1.isLt).trans_lt hq) w.2` (#13). The `exact` at `:84` also silently certifies that the order-`q` coordinate of `restrictOperator (u k)` **is** the order-`s` coordinate of `u k` (`restrictIndex` is the identity on the word, `SobolevRestriction.lean:13,29`) — no index shift | True | **OK** |
| 18 | `exists_limit_restrict_of_value` | `:88` | the same, plus completeness: a limit path in order `q` exists | `cauchySeq_tendsto_of_complete (#17)`; completeness of `SobolevSpace` is real (`sobolev_complete`, `CylinderSobolevSpace.lean:60` — closed subspace of a finite product of complete L² spaces) | True | OK |

### Out-of-scope declarations I read line-by-line and judged (relevant to the two questions)

| declaration | file:line | mechanism | verdict |
|---|---|---|---|
| `eq_initial_add_integral` | `SeparatingTimeDerivative.lean:24` | the **endpoint-safe** integral identity `f t = f 0 + ∫₀ᵗ g` for `t ∈ Icc`, via the separating family and Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` (interior derivative + closed-interval continuity + interval integrability, all three genuinely supplied) | **OK** |
| `EulerSeparatingTimeDerivative.hasDerivWithinAt` | `SeparatingTimeDerivative.lean:49` | **the actual `Ioo → Icc` upgrade**: differentiate the primitive (FTC-1, two-sided, at every real point) and transport by `HasDerivWithinAt.congr_of_mem` with the congruence proved exactly on `Icc` | **OK** |
| `EulerSeparatingTimeDerivative.hasDerivAt` | `:63` | interior two-sided version, `Icc_mem_nhds` | OK |
| `extendPath` / `extendPath_continuous` | `VolterraConvolution.lean:20,24` | `extendPath T hT f t = f (projIcc 0 T hT t)` — a genuinely **clamped** (constant outside `[0,T]`) extension, continuity proved | OK |
| `cauchySeq_of_square_bound` | `SobolevPathInterpolation.lean:14` | `‖g m − g n‖² ≤ A‖f m − f n‖` + `f` Cauchy ⟹ `g` Cauchy; honest `ε²/(A+1)` bookkeeping, `nlinarith` on `‖·‖ ≥ 0` | OK |
| `clm_difference_square_bound` | `:33` | applies the interpolation inequality to `u − v` (`map_sub`) and uses `‖u−v‖ ≤ 2M`. Confirms the estimate really is applied to **differences** | OK |
| `wordPath_square_bound` | `:64` | the Landau/Kolmogorov inequality lifted to sup-in-time norms; `n+2 ≤ s` is exactly what makes `∂ᵢ∂ᵢD^w` available inside the order-`s` array | OK (its bottom `word_square_le_parent` was delegated) |
| `wordPath_cauchy_step` | `:103` | one interpolation step, = `cauchySeq_of_square_bound` ∘ `wordPath_difference_square_bound` | OK |
| `SobolevSpace` / `sobolevSubspace` | `CylinderSobolevSpace.lean:44,49` | **closed submodule** of `SobolevWord q → LiftL2 period` cut out by closed derivative graphs; norm = inherited pi (sup-over-words) norm. So "derivative coordinates" are **constrained to be genuine strong derivatives** | OK — this is the single most important non-degeneracy fact |
| `word_hasDerivAt` | `:70` | extracts, from submodule membership, that the `cons i w` coordinate is the strong derivative of the `w` coordinate | OK |
| `value_injective` | `:128` | the whole array is determined by its order-0 coordinate, via uniqueness of strong derivatives (`SpatialJet.word_unique` / `HasDerivAt.unique`) | OK |
| `restrictOperator` and its 8 `rfl` lemmas | `SobolevRestriction.lean:19-73` | codRestrict of a coordinate reindexing; every `rfl` closes an array-coordinate lookup after `value_injective`, i.e. delta + projection + `Fin`-bound proof irrelevance | OK |
| `sobolevPath_cauchy_of_l2` | `OrdinaryCauchyInterpolation.lean:60` | the Euler-side consumer of `:78`; instantiates `s := q+1`, transports the L²-Cauchy hypothesis through `ordinarySobolev_value`, and rewrites the conclusion back with `restrict_sobolev` | OK |
| `exists_sobolevPath_limit` | `:91` | `cauchySeq_tendsto_of_complete` of the above | OK |
| `nonempty_smoothLimitData` | `OrdinarySmoothLimit.lean:34` | the ultimate consumer; needs **full-sequence** convergence at every order (`sobolev_convergence`, `:31`) — shape matches — and *proves* the cross-order coherence field `value_eq` by `tendsto_nhds_unique` (`:41-59`) | OK |
| `pointEvaluation` / `representative_bound` | `SobolevPointEvaluation.lean:64,37` | genuine CLM from the H³ Sobolev embedding; a.e. bound upgraded to pointwise by continuity + `Measure.dense_of_ae` | OK |
| `ordinaryWord_hasDerivWithinAt`, `wordEnergy_hasDerivWithinAt` | `OrdinaryWordTime.lean:78,87` | consume `:96` through a CLM composition and `HasDerivWithinAt.norm_sq`/`fun_sum`; give the **energy** derivative within `Icc` at every `t` | OK |
| `Evolution.integerEnergy_hasDerivWithinAt`, `integer_energy_bound` | `OrdinaryEulerHigherEnergy.lean:48,64` | the Grönwall that needs the derivative on `Ico 0 T` (**including `t = 0`**) — the consumer that makes the endpoint upgrade load-bearing | OK |
| `exists_limit_with_constraints` | `CorrectionFamilyCompactness.lean:31` | second consumer of `:88` (viscosity side). **Name/docstring overclaim**: the file is named `…Compactness` and the docstring says "Strong lower-Sobolev compactness", but the theorem takes `hCauchy` as an explicit hypothesis, so it is **not** a compactness theorem. Harmless — the hypothesis is visible in the statement and is discharged one level up by `correction_family_cauchy` (`:64`) | OK, **name overclaims** |

---

## Kernel-risk assessment

Method: regex census over the two scope files and the six dependency files I read in
full. Counts are line hits with line numbers.

### Vector (3) — custom metaprogramming: **ZERO**

Across `SmoothFieldSobolevTime.lean`, `SobolevCauchyInterpolation.lean`,
`SeparatingTimeDerivative.lean`, `SobolevPathInterpolation.lean`,
`SobolevRestriction.lean`, `OrdinaryCauchyInterpolation.lean`,
`CylinderSobolevSpace.lean`, `CylinderSobolevOperators.lean`:
**0** hits for `macro`, `elab`, `syntax`, `set_option`, `native_decide`, `axiom`,
`unsafe`, `partial`, `deriving`, `attribute`, `sorry`, `admit`.

The only `instance` declarations are `Fact (0 < (1:ℝ))`
(`SmoothFieldSobolevTime.lean:20`, `OrdinaryCauchyInterpolation.lean:17`) and four
`inferInstance` restatements (`SobolevCauchyInterpolation.lean:15,18`,
`SobolevPathInterpolation.lean:48,51`). **The `Fact` is a cylinder PERIOD, not an `Lp`
exponent** (`variable (period : ℝ) [Fact (0 < period)]`,
`CylinderSobolevSpace.lean:31`, `SobolevCauchyInterpolation.lean:12`), so it cannot
silently swap an `L¹` for an `L²`; the ordinary field is lifted to the **unit** cylinder,
hence `period = 1`. The `inferInstance` restatements are provably the same instances
they restate (they are `inferInstance`, so if a different instance existed they would
still pick the canonical one). **Diamond noise, not kernel risk.**

### Vector (2) — Nat/GMP numeral arithmetic: **essentially absent**

* **`decide` / `Decidable.decide` / `by decide`: 0 occurrences in all eight files.** The
  kernel is never asked to evaluate a `Decidable` instance.
* **No numeral with ≥ 4 digits anywhere** (largest literals: `4` in `Fin 4`, `3` in
  `3 ≤ q`, `2` in `n+2`, and `1` as the period). **0** hits for `Nat.pow`, `Nat.div`,
  `Nat.mod`, `Nat.gcd`.
* Arithmetic tactics, all with tiny symbolic certificates:
  `omega` — `SmoothFieldSobolevTime.lean:99,100` (goals `3 ≤ q+3`, `q ≤ q+3`),
  `SobolevCauchyInterpolation.lean:35,36` (`n+2 ≤ s`, `n < s` from `n+1 < s`),
  `SobolevPathInterpolation.lean` 13 hits (all `n ≤ s` / `n+1 ≤ s` from `n+2 ≤ s`),
  `SobolevRestriction.lean:52,57`, `OrdinaryCauchyInterpolation.lean:37,83,84,88`,
  `CylinderSobolevSpace.lean:93,97,98,99,105,118,119,120`. Every one is a linear-integer
  goal in *symbolic* variables; `omega` emits a small certificate the kernel checks by
  linear arithmetic on `Int` literals ≤ 3. No GMP work.
  `norm_num` — only `SmoothFieldSobolevTime.lean:20` and
  `OrdinaryCauchyInterpolation.lean:17`, both the goal `0 < (1:ℝ)`.
  `nlinarith` (`SobolevPathInterpolation.lean:27,30`) and `positivity` (`:108`) work on
  `ℝ` with the symbolic `A`, `M`, `ε`; real literals are `OfNat` applications the kernel
  does not evaluate.
* **`Fintype` enumeration risk, checked explicitly.**
  `SobolevWord q = Σ n : Fin (q+1), Fin n.val → Fin 4`
  (`CylinderSobolevSpace.lean:15`) is a `Fintype` of cardinality `Σ_{n≤q} 4ⁿ`. In my
  scope `q` is **always symbolic**, and every manipulation goes through *lemmas*
  (`pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `cauchy_pi_iff'`,
  `Finset.single_le_sum`, `Pi.sum_norm_apply_le_norm`) rather than enumeration. The
  cardinality is never computed: `sumNorm_le_card_norm`
  (`CylinderSobolevOperators.lean:46`) keeps `Fintype.card (SobolevWord q)` **symbolic**.
  The one place a literal order appears is `observation`/`pointEvaluation` at order 3
  (`SmoothFieldSobolevTime.lean:52-53`, and `q = 3` at
  `OrdinaryStrongTime.lean:51`), where `SobolevWord 3` has `1+4+16+64 = 85` elements — but
  nothing forces the kernel to enumerate them, because no goal about that type is closed
  by `decide` or by `rfl`-on-a-`Finset.sum`. **Even if it did, 85 is trivial.**

### Vector (1) — recursive inductive types / recursors

* **The two scope files declare no `inductive`, no `structure`, and no recursive `def`.**
  **0** hits for `termination_by`, `WellFounded`, `WellFounded.fix`, `Acc.rec`, `.rec`,
  `.recOn`, `.brecOn` in either scope file, and **0** in
  `SeparatingTimeDerivative.lean`, `SobolevPathInterpolation.lean`,
  `SobolevRestriction.lean`, `CylinderSobolevOperators.lean`.
* Two structural inductions do occur, both on `ℕ` and both with **symbolic** bound:
  `SobolevCauchyInterpolation.lean:27` (`induction n`) and
  `CylinderSobolevSpace.lean:94,111` (`induction r` / `induction n`). These elaborate to
  `Nat.rec` applications the kernel **type-checks but never reduces**, because the
  index is a variable. Kernel cost = proof-term checking, not recursor reduction.
* The one genuinely recursive *data* type in the neighbourhood is
  `SpatialJet period standardDirection q f` (used at
  `CylinderSobolevSpace.lean:78,91-105`, `.zero`/`.succ`) — an **indexed, `Type`-valued
  inductive family**, which is the shape flagged in the threat model. It is *not* in my
  scope files, and in the files I read it is only used through lemmas
  (`SpatialJet.word_zero`, `SpatialJet.word_unique`,
  `SpatialJet.sobolevNorm_eq_sum_words`) plus `Classical.choice` of a `Nonempty`
  (`:99,105`). The only `rfl` touching it is `CylinderSobolevSpace.lean:116`, which
  closes `J.word Fin.elim0 = word u hn Fin.elim0` **after** `rw [SpatialJet.word_zero]`,
  i.e. at symbolic `q`; that is a delta/projection step, not a recursor unfolding on
  concrete data. **I therefore report no kernel-risk instance in scope, while noting
  that the `SpatialJet` family itself is a legitimate target for the deep-kernel worker
  (it is `EulerProof.lean:3064`-shaped and outside my remit).**
* `rfl` census (the kernel-reduction hot spots): `SmoothFieldSobolevTime.lean:104` (1),
  `SobolevPathInterpolation.lean:61,87` (2), `SobolevRestriction.lean` (8),
  `CylinderSobolevSpace.lean:116` (1), `OrdinaryCauchyInterpolation.lean:22` (1);
  `SobolevCauchyInterpolation.lean` and `SeparatingTimeDerivative.lean` have **0**.
  Every one of them closes an **array-coordinate lookup** or a `ContinuousMap`/`Subtype`
  projection: `(restrict u).val w ≡ u.val (restrictIndex h w)`,
  `wordPathOperator … u t ≡ word (u t) h w`, `value ≡ u.val (emptyWord)`. Kernel work =
  delta + structure projection + **proof irrelevance of `Fin`/`Nat.lt` bounds** (a
  definitional feature Lean uses everywhere). **No `rfl` in scope reduces a recursor on a
  concrete `List`/`Finset`/`Nat` literal.**
* Structure eta *is* used pervasively (`Subtype` for `SobolevSpace` and `Icc 0 T`,
  anonymous constructors `⟨0,le_rfl,hT⟩`, `Sigma` for `SobolevWord`). Lean 4 has
  definitional eta for structures, so this is formally vector (1); but these are
  non-recursive single-constructor structures, the standard Mathlib idiom. Flagged for
  completeness only.

**Bottom line: the kernel accepts both scope files by type-checking proof terms built
from Mathlib lemmas and the repo's own lemmas. It is never asked to decide a proposition,
evaluate a numeral, or reduce a recursor on concrete data. If this artifact is exploiting
a kernel bug, it is not doing it in these two files.**

---

## Cone status of every theorem I audited

From the regenerated `audits/nse-deep/CONE.csv` (`in_cone=False` is meaningful,
`in_cone=True` is weak evidence):

| decl | file:line | in_cone | in_import_closure |
|---|---|---|---|
| `continuous_sobolev` | `SmoothFieldSobolevTime.lean:24` | True | True |
| `sobolevPath` | `:40` | True | True |
| `restrict_sobolev` | `:44` | True | True |
| `observation` | `:52` | True | True |
| `observation_apply` | `:55` | True | True |
| `observation_injective` | `:68` | True | True |
| `sobolevPath_hasDerivWithinAt_of_three_le` | `:86` | True | True |
| **`sobolevPath_hasDerivWithinAt`** | **`:96`** | **True** | True |
| `sobolevPath_hasDerivAt` | `:107` | **False** | True |
| `_anon` (`Fact`) | `:20` | False | True |
| `wordPath_cauchy_of_value` | `SobolevCauchyInterpolation.lean:21` | True | True |
| `pathCoordinates` | `:40` | True | True |
| `pathCoordinates_norm` | `:46` | True | True |
| `path_cauchy_of_coordinates` | `:63` | True | True |
| **`cauchy_restrict_of_value`** | **`:78`** | **True** | True |
| `exists_limit_restrict_of_value` | `:88` | True | True |
| `cauchySobolevGroup` / `cauchySobolevSpace` | `:15`, `:18` | False | True |
| `eq_initial_add_integral` | `SeparatingTimeDerivative.lean:24` | True | True |
| `EulerSeparatingTimeDerivative.hasDerivWithinAt` | `:49` | True | True |
| `EulerSeparatingTimeDerivative.hasDerivAt` | `:63` | True | True |
| `cauchySeq_of_square_bound` | `SobolevPathInterpolation.lean:14` | True | True |
| `clm_difference_square_bound` | `:33` | True | True |
| `wordPathOperator` | `:54` | True | True |
| `wordPathOperator_apply` | `:59` | **False** | True |
| `wordPath_square_bound` | `:64` | True | True |
| `wordPath_sub` | `:83` | **False** | True |
| `wordPath_difference_square_bound` | `:90` | True | True |
| `wordPath_cauchy_step` | `:103` | True | True |
| all 8 decls of `OrdinaryCauchyInterpolation.lean` | `:19-91` | True (the `Fact` instance `:17` False) | True |

**Reading:** both assigned load-bearing theorems (`:96`, `:78`) are `in_cone=True`, and
every lemma on the two critical paths is `in_cone=True`. The four `False` rows are
(a) the `Fact`/`inferInstance` instances (an artefact of how the cone tracks instances),
(b) `sobolevPath_hasDerivAt` (`:107`) — genuinely unused: consumers want the `Icc`
version, and `Ioo`-only would not suffice for the energy Grönwall,
(c) `wordPathOperator_apply` (`:59`) and `wordPath_sub` (`:83`) — genuinely unused
convenience lemmas (their content is available by `rfl`/`map_sub`).
**No `in_cone=False` row hides load-bearing content here.** I did *not* observe the
dot-notation false-negative pathology the predecessor found (its D.1), because these two
files export plain (non-projection) names.

---

## Delegated sub-chains

Two read-only children were given the two bottoms my verdict is conditional on.

* `audits/nse-deep/workers/_sub-endpoint-ftc-integral.md` — `extendPath`,
  `extendPath_continuous`, `realIntegral`, `realIntegral_hasDerivAt`, `integral`,
  `integral_apply` (`Euler/VolterraConvolution.lean`, `Euler/ContinuousTimeIntegral.lean`)
  plus an independent re-read of `SeparatingTimeDerivative.lean`. Question: is the
  endpoint derivative of the *primitive* genuinely proved (which Mathlib FTC lemma), and
  is Bochner integrability proved rather than assumed away (the `∫ = 0` junk value)?
* `audits/nse-deep/workers/_sub-sobolev-interpolation-ineq.md` —
  `word_square_le_parent` (`Euler/SobolevInterpolation.lean:17`) and the non-degeneracy of
  `SobolevSpace`/`word`/`value`. Question: is the Landau/Kolmogorov inequality proved by
  a real integration-by-parts/Cauchy-Schwarz (or Fourier) argument, does it really use
  `∂ᵢ∂ᵢ`, and are the derivative coordinates *proved* derivatives?

### Result of the endpoint/FTC sub-chain (`_sub-endpoint-ftc-integral.md`): **13 OK, 1 UNCLEAR (off-path), 0 adverse — Escalation 3 RESOLVED in the artifact's favour**

The child confirms my Part A.2 reading and pins the Mathlib lemma I could not name:

* **`realIntegral_hasDerivAt` (`Euler/ContinuousTimeIntegral.lean:57`) is a genuine
  TWO-SIDED `HasDerivAt` at EVERY real `t`**, proved by Mathlib **FTC-1
  `intervalIntegral.integral_hasDerivAt_right`**
  (`Mathlib/.../FundThmCalculus.lean:725`). All three of that lemma's hypotheses are
  really supplied: interval integrability (`Continuous.intervalIntegrable`),
  `StronglyMeasurableAtFilter` (`Continuous.aestronglyMeasurable.stronglyMeasurableAtFilter`),
  and `ContinuousAt` — all three from the **proved** `extendPath_continuous`
  (`VolterraConvolution.lean:24`), with `extendPath = f (projIcc 0 T hT t)` (`:20`), i.e.
  genuinely clamped.
* **No junk-value or vacuity escape.** FTC-1 sits under `variable [CompleteSpace E]`
  (`FundThmCalculus.lean:472`, with no intervening `end`), so it cannot be applied without
  completeness; completeness is supplied at `ContinuousTimeIntegral.lean:50` and
  `SeparatingTimeDerivative.lean:15-16` (for both `E` and `F`). **Every integral in the
  chain carries an explicit integrability witness**, so the Mathlib
  `∫ (non-integrable) = 0` junk value is never in play.
* The child independently confirms the two points I considered most delicate:
  (i) FTC-2 at `SeparatingTimeDerivative.lean:36-42` is applied on `[0,t]`, **not**
  `[0,T]`, so reaching `t = T` needs no derivative *at* `T` — the endpoint content comes
  from `f, g : C(Icc 0 T, E)` (continuity on the closed interval) rather than from any
  derivative assumption; and the claim is non-vacuous for `T > 0` (right-derivative at 0,
  left-derivative at `T`), degenerate only at `T = 0`;
  (ii) `HasDerivWithinAt.congr_of_mem` (`:57`) is applied with the correct argument shape
  (`Mathlib/.../Deriv/Basic.lean:566`), the agreement being supplied exactly on `Icc`.
* **Its one UNCLEAR is off my path:** `VolterraConvolution.lean:15-16` declares its
  variables **without** `[CompleteSpace X]`, so `convolution` (`:108`) and
  `convolution_bound` (`:124`) would be junk-`0`-vacuous for an incomplete `X`. Neither is
  on the endpoint route (the endpoint route uses `realIntegral`/`integral` with
  completeness supplied), but it is a live pattern worth handing to whoever audits the
  Volterra/heat machinery. Recorded as Escalation 7.
* Kernel risk across all 349 lines it read: **0** `decide`, `native_decide`, ≥4-digit
  numerals, `Nat.pow/div/mod/gcd`, `termination_by`, `WellFounded`, `.rec`,
  metaprogramming, `sorry`; only 2 structure-projection `rfl` and 1 `nlinarith`.
* Caveat it records: it read the Mathlib signatures at a **v4.33.0** checkout while the
  repo pin is **v4.34.0-rc2**, and no build was possible.

### Result of the interpolation-inequality sub-chain (`_sub-sobolev-interpolation-ineq.md`): **33 OK, 0 UNCLEAR, 1 low inherited KERNEL-RISK, 0 SUSPICIOUS — Escalation 2 RESOLVED in the artifact's favour**

* **The derivative coordinates are PROVED derivatives, confirming my A.4 finding
  independently.** `sobolevSubspace` (`CylinderSobolevSpace.lean:44-46`) is the `⨅` over
  edges of the pullback of the **closed graph of the strong translation derivative**
  (`ClosedTranslationGraph.lean:53-87`); the child coordinate is the strong L² derivative
  of the parent **by definition of membership**, and `word_hasDerivAt` (`:70-75`) is
  literally `mem_iInf.mp u.property`. `value_injective` (`:128`) then fixes the whole
  array from its L² value. **Not a bundled-junk "derivative".**
* **`word_square_le_parent` (`Euler/SobolevInterpolation.lean:17-37`, the only
  declaration in that file) is a genuine integration-by-parts + Cauchy-Schwarz proof.**
  Mechanism: `translation_derivative_pairing` (`EulerProof.lean:2784` — `⟪f',g⟫ = −⟪f,g'⟫`
  from unitarity of translation plus uniqueness of the strong derivative, i.e. abstract
  integration by parts) instantiated at `(g, gᵢ, gᵢ, gᵢᵢ)`, then Cauchy-Schwarz, then
  `word_norm_le` (`CylinderSobolevOperators.lean:28`, the sup-over-words norm) to absorb
  `∂ᵢ∂ᵢ` into `‖u‖`. **The second derivative is genuinely used, and `n+2 ≤ s` is tight** —
  it is needed both for the length-`n+2` index to exist and for `word_hasDerivAt`'s
  `n+1 < s`. The child also checked non-triviality: `word_norm_le` alone would only give
  `‖gᵢ‖² ≤ ‖u‖²`, so the interpolation inequality is strictly stronger than the trivial
  bound. **This exactly matches the Landau/Kolmogorov reading in my B.2.**
* Kernel, across the 9 files it read: **0** `decide`, `native_decide`, ≥4-digit numerals,
  `Nat.pow/div`, `termination_by`, `.rec`, `unsafe`, `sorry`, `axiom`; `rfl` only on
  subtype projections; **no `Fin n → Fin 4` enumeration**. Its one low inherited risk is a
  *latent* one I echo below: `Fintype.card (SobolevWord 6) = 5461` and order 7 = `21845`
  appear at `CylinderPathProductBounds.lean:49`, i.e. a ≥4-digit cardinality **does** exist
  in the wider repo, symbolic today but a genuine bignum/enumeration target if some file
  ever forces it by `decide`/`rfl`/`norm_num`.
* Its escalation (a) is the same conclusion I reached independently — this is **not**
  compactness, and the L²-Cauchy input must be audited at its producer. Its escalation
  (b) is new and worth passing up: **it found no nonzero inhabitant of
  `SobolevSpace period q` for `q ≥ 1`** anywhere it looked (`SmoothOrbit` is always a
  hypothesis, never discharged for a concrete nonzero field). That is a *global*
  non-triviality question, recorded as Escalation 6 below.

---

## Escalations

Ranked. None is a demonstrated defect; each is a place where my OK is conditional on
something outside my scope.

1. **The burden has moved to the Grönwall estimates, not to interpolation.**
   Because the limit construction is **Cauchy-based and uses no compactness theorem at
   all** (see `## The compactness question`), the analytic load now sits entirely on
   (a) `Evolution.cauchyPath_of_initial` (`OrdinaryEulerCauchy.lean:50`) → the L²
   stability estimate `velocityPath_norm_sub_le` (`OrdinaryEulerL2Stability.lean:136`),
   and (b) `Evolution.all_order_bounds_of_h3` (`OrdinaryEulerCauchy.lean:70`) →
   `higher_energy_of_h3` (`OrdinaryEulerHigherEnergy.lean:101`). If either Grönwall
   constant is wrong (e.g. depends on `k`, or on the interval length in the wrong way),
   the whole limit collapses — and the interpolation file would still be a correct
   theorem. *Question for an expert:* are the constants in those two estimates uniform in
   `k` and finite for the actual `T`, and is the L²-stability exponent driven by a
   quantity (`‖∇u‖_∞`) that the H³ bound genuinely controls?
   *What would settle it:* the energy-identity chain below `l2_stability` and
   `integer_energy_uniform`, which the predecessor also left unread.
2. **[RESOLVED by the delegated read — kept for the record]
   `word_square_le_parent` (`Euler/SobolevInterpolation.lean:17`) is the single
   inequality on which the whole compactness substitute rests.** The risk was that it be
   stated with the wrong pair of words, so that it is true and provable for a degenerate
   reason. *Settled:* it is proved from `translation_derivative_pairing`
   (`EulerProof.lean:2784`, abstract integration by parts from unitarity + uniqueness of
   the strong derivative) instantiated at `(g, gᵢ, gᵢ, gᵢᵢ)`, then Cauchy-Schwarz, then
   `word_norm_le`; the second derivative genuinely enters and `n+2 ≤ s` is tight. The
   trivial bound `word_norm_le` alone would give only `‖gᵢ‖² ≤ ‖u‖²`, so the inequality is
   strictly stronger than the trivial one.
3. **[RESOLVED by the delegated read — kept for the record]
   `realIntegral_hasDerivAt` (`Euler/ContinuousTimeIntegral.lean:57`) supplies the
   endpoint derivative.** *Settled:* it is a genuine two-sided `HasDerivAt` at **every**
   real `t`, by Mathlib FTC-1 `intervalIntegral.integral_hasDerivAt_right`
   (`FundThmCalculus.lean:725`), whose integrability / `StronglyMeasurableAtFilter` /
   `ContinuousAt` hypotheses all come from the proved `extendPath_continuous`. FTC-1 sits
   under `variable [CompleteSpace E]` (`FundThmCalculus.lean:472`), and completeness is
   supplied (`ContinuousTimeIntegral.lean:50`, `SeparatingTimeDerivative.lean:15-16`), so
   the Bochner integral is real and the `∫ (non-integrable) = 0` junk value is never used.
4. **Name/docstring overclaim: `Euler/CorrectionFamilyCompactness.lean`.** The file
   docstring (`:5`) says "Strong lower-Sobolev compactness" and the theorem is
   `exists_limit_with_constraints` (`:31`), but the statement takes `hCauchy` (`:35`) as a
   hypothesis, so **no compactness is proved**. Harmless here (the hypothesis is visible
   and is discharged at `:64`), but a reader auditing by name would be misled. Same
   remark applies to the predecessor's phrase "interpolation substitutes for Rellich":
   accurate only because the input is Cauchy, not merely bounded.
   *What would settle it:* nothing to prove — a naming remark for the final report.
5. **`Measure.dense_of_ae` in `representative_bound`
   (`SobolevPointEvaluation.lean:44`)** needs the lift measure to have full support
   (`IsOpenPosMeasure`). If `liftMeasure period` had a null open set, the pointwise
   Sobolev bound — and hence the boundedness of `pointEvaluation`, and hence the whole
   separating family — would be unsound. *What would settle it:* the definition of
   `liftMeasure` and its `IsOpenPosMeasure` instance.
6. **NON-TRIVIALITY, raised by the interpolation child and passed up: is there any
   NONZERO inhabitant of `SobolevSpace period q` for `q ≥ 1`?** The child found none —
   `SmoothOrbit`/`translation_contDiff` is always a *hypothesis*, never discharged for a
   concrete nonzero field, in everything it read. On the Euler route the inhabitant comes
   from `SmoothL2Field.toLp` + `ordinarySobolev` (`MeanOrbitSobolev.lean:71`), so a
   nonzero inhabitant exists iff a nonzero `SmoothL2Field` exists — which the predecessor's
   chain also assumes rather than constructs at this level (its `initial_nonzero` route
   goes through `zeroEvolution`). *Question for an expert:* is a concrete nonzero
   `SmoothL2Field Space` (equivalently a nonzero `SobolevSpace 1 q`) ever exhibited
   anywhere in the artifact? If not, every quantified statement over these spaces is
   satisfiable but the *singularity* claim would need its own witness. *What would settle
   it:* grep for a `def` producing a `SmoothL2Field` from an explicit bump/Gaussian, and
   check the top-level `EulerSingularity.lean` existence clause supplies one.
7. **`VolterraConvolution.lean:15-16` omits `[CompleteSpace X]`** (endpoint child's one
   UNCLEAR), so `convolution` (`:108`) and `convolution_bound` (`:124`) are
   junk-`0`-vacuous for an incomplete `X`. **Off the endpoint path** (which supplies
   completeness), but the same pattern elsewhere would be a real vacuity. *What would
   settle it:* check every caller of `convolution` instantiates a complete `X`.
8. **Latent bignum/enumeration target (not triggered today).**
   `Fintype.card (SobolevWord q)` is `Σ_{n≤q} 4ⁿ`: `5461` at `q = 6` and `21845` at
   `q = 7`, appearing at `CylinderPathProductBounds.lean:49`. Symbolic in everything I and
   the children read, but if any file closes a goal about such a cardinality by `decide`,
   `rfl`, or a `norm_num` certificate, the kernel would do real GMP/enumeration work.
   *What would settle it:* a repo-wide `decide`/`rfl`-on-`Fintype.card` sweep — that is the
   `decide-bignum` worker's territory.
9. **Unverified elaboration of `convert!` at `SmoothFieldSobolevTime.lean:102-104`.**
   Sound in principle (see the remark under row #9 of the table), but I could not see the
   goal states without a build. *What would settle it:* one `#print axioms` /
   `set_option pp.all true` run once a Mathlib build exists.

---

## Residue — what I could NOT check, and why

* **No build.** No compiled Mathlib on this box (disk full), so no `lake build`,
  no `#print axioms`, no `pp.all`. Everything above is source reading. In particular I
  cannot exclude that a name I resolved by `grep` elaborates to a *different*
  declaration (namespace shadowing, `export`, `open` aliasing). Both scope files open
  8-10 namespaces (`SmoothFieldSobolevTime.lean:14-18`,
  `SobolevCauchyInterpolation.lean:9-10`), so this risk is real but unquantified. It bit
  me once in a benign way: `sobolevPath_hasDerivWithinAt` exists **twice**
  (`SmoothFieldSobolevTime.lean:96` and `CylinderTimeRegularity.lean:70`); I
  disambiguated consumers by whether a leading `period` argument is passed, which is
  sound but is an argument-arity heuristic, not elaboration.
* **The interpolation inequality itself** (`SobolevInterpolation.lean:17`) and the
  **integral/FTC machinery** (`ContinuousTimeIntegral.lean`) — delegated and **returned
  clean** (Escalations 2 and 3, both resolved). I did not re-derive them myself, so my
  confidence there is one level of hearsay removed, though both children quoted
  `file:line` and named the Mathlib lemmas. Both children also note they could not build,
  and the endpoint child read Mathlib signatures at a **v4.33.0** checkout while the repo
  pins **v4.34.0-rc2** — so the FTC-1 signature it verified could in principle differ.
* **`SmoothL2Field` internals.** I took `field`, `smooth`, `toLp`, `jetLp`,
  `translation_contDiff`, `iteratedFDeriv_translation_eq`, `toLp_ae` on faith as fields
  and proved lemmas of a real structure. Also `ordinarySobolev`/`ordinarySobolev_value`/
  `ordinarySobolev_continuous`/`ordinarySobolev_norm_le` (`MeanOrbitSobolev.lean:71,74`)
  and `ordinaryLift`/`ordinaryLift_ae`/`ordinaryProjection_measurePreserving`. If the lift
  to the unit cylinder were not isometric or not angle-independent, `observation_apply`'s
  identification with `A.field x.1` would still hold (it is proved) but the *norms* used
  by the interpolation would not be the ordinary Sobolev norms. Flagged for whoever
  audits `EulerMeanOrdinaryLift` / `EulerLpTranslation`.
* **`SpatialJet` (indexed `Type`-valued inductive) and its `word_unique` /
  `sobolevNorm_eq_sum_words`** — used by `value_injective` and `sumNorm_eq_jet`. I read
  the *uses*, not the inductive's own eliminator behaviour. This is the one genuine
  vector-(1) object in the neighbourhood and belongs to the deep-kernel worker.
* **`sobolevEmbeddingConstant`, `value_ae_bound`,
  `exists_continuous_representative`** (`CylinderSobolevEmbedding`) — the actual Sobolev
  embedding theorem on the cylinder. I checked only that they are *used* with the correct
  order (`3` for a 4-dimensional domain) and never need to be evaluated.
* **The `liftMeasure` support question** (Escalation 5).
* **The other consumer branch** (`CorrectionFamilyCompactness` → viscosity/NS
  correction family, `Euler/ViscosityCauchy.lean`, `correction_family_cauchy`) — read only
  at the interface; it is not on the Euler limit route this worker was assigned.
