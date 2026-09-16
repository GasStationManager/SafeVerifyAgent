# Worker report — `NavierStokes/HarmonicResidual.lean`

Audit target: `openai/NavierStokesAndEuler` @ `f9e8bc5`, file `NavierStokes/HarmonicResidual.lean`
(1620 lines, 173 declarations, 124 theorems of which 112 in-cone per `INVENTORY.csv`).

**Every claim below is SOURCE-LEVEL.** There is no Mathlib and no `lake build` on this box, so
nothing here is machine-checked; anything whose truth depends on elaboration/tactic behaviour is
tagged **UNBUILT**. All `file:line` citations were re-derived from the original (non-stripped)
file and the quoted text is verbatim.

## Headline

**OK, with four NOTEs (one substantive), one UNCLEAR and two ESCALATIONs — and no kernel risk worth naming.**

This file is, for kernel-trust purposes, close to the best case in the artifact: **zero
`inductive`, zero `.rec`/`Acc.rec`/`WellFounded`, zero `termination_by`, zero `deriving`, zero
`decide`, zero `Nat.pow/div/mod/gcd`, zero numerals with ≥ 5 digits, zero `sorry`/`axiom`/
`opaque`/`unsafe`/`partial`, zero metaprogramming.** The largest closed numeral anywhere in the
file is `3` (as `Fin 3`); the peak kernel numeral work, expressed as a value, is the evaluation of
`(2 : ℕ)` and the three `Fin 3` index literals `0,1,2` — i.e. **< 10**, and **zero GMP bignum
work**. The one arithmetic tactic call in the whole file is `omega` on a symbolic-exponent
identity (line 1567); its statement is mathematically true and its exponent never becomes a closed
numeral.

Mathematically the file is honest and, where I could check it against textbook cylindrical
Navier–Stokes, **correct**: the scalar Laplacian (177), vector Laplacian with both frame
connection terms (185), the cylindrical convective derivative (192) and the cylindrical gradient
(199) all reproduce the standard formulas exactly, including signs (checked component by
component, below). Every limit/integral interchange in the file is guarded by a real
`Continuous` hypothesis that is discharged from a proved lemma — **I found no asserted
interchange and no quantifier-order slip.**

The NOTE is a **never-supplied leaf hypothesis of the shape the brief asked me to hunt**, though
in a benign direction: `HarmonicResidual.ExtractionRegular` (1461) is **never constructed anywhere
in the repository**. The only concrete suppliers build a *same-named, strictly weaker* duplicate
structure `LocalResidualGrouping.ExtractionRegular`, and `LocalResidualGrouping.lean` re-proves
this file's whole `ExtractionRegular`-gated tail from it. So this file's tail
(`stateGoodWaveResidual_grouped`, `stateMeanCoefficientValue_eq_average`,
`stateFullResidual_reconstructed`) is a **superseded duplicate layer whose hypothesis has no
supplier** — safe (weaker hypothesis downstream ⇒ stronger theorem), but it means three in-cone
theorems of this file are vacuously in the cone.

### Verdict counts

Counted over the 60 verdict-tagged items below (operator definitions, proof-pattern groups,
declaration groups, the numeral audit, and the three kernel vectors) — not over the 173
declarations, since I grouped mechanically identical declarations.

| verdict | count | where |
|---|---|---|
| OK | 54 | B.1 (6), B.2 (13), B.3 (5), B.4 (5), B.8 (21), C (1), kernel vectors (3) |
| NOTE | 4 | B.3 `angularAverage`/`period` defeq coupling; B.5 unsupplied `ExtractionRegular`; B.6 shadowed `nonlinearResidual`; B.8 `residualBlock.pressure = 0` |
| UNCLEAR | 1 | B.7 `Frame` is not certified to be a cylindrical frame |
| ESCALATE | 2 | E1, E2 |
| KERNEL-RISK | 0 | — |
| REFUTED | 0 | — |

## (A) What the file does, and who uses it

`HarmonicResidual` is the **finite-harmonic bookkeeping layer** of the Navier–Stokes correction
cycle. A field on the lifted domain `D × ℝ` (slow variable × angle) is represented by a
finitely-supported family of angular Fourier coefficients (`Coefficients D` from
`HarmonicFields`, re-exported at line 23). The file does three things:

1. **Coefficient-level cylindrical differential operators.** `scalarLaplacian` (177),
   `vectorLaplacian` (185), `transport` (192), `gradient` (199), `linearResidual` (206),
   `nonlinearResidual` (212) act on coefficient families; a matching family of `field_*` bridge
   theorems (235–342) proves each one evaluates to the *field-level* operator of
   `HarmonicCalculus`/`LinearWaveResidual` (`cylindricalLaplacian`,
   `cylindricalVectorLaplacian`, `LinearWaveResidual.transport/gradient/linearResidual`), under
   explicit smoothness hypotheses. A matching family of `band_*` theorems (346–438) tracks how
   the largest occupied harmonic `|j|` grows (`N + N` for the quadratic term, 435), and a family
   of `smooth_*` theorems (875–943) tracks smoothness.
2. **Reality and mean/oscillation splitting.** `realCoefficients` (453), `nonconstant = erase 0`
   (525), `extract` (502), `realAngularMean` (1198) and the exactness lemma
   `realAngularMean_field` (1217).
3. **The grouped residual identity.** `goodResidual` (1016) is the *actual* nonlinear residual of
   a base + mean + a finite sum of label wave packets, minus the excluded Gaussian and alias
   errors; `goodResidual_grouped` (1091) proves it splits as *mean zero-mode + virtual stress +
   a per-label sum*, given pairwise-disjoint closed supports. `goodResidual_angularMean` (1235)
   computes its angular mean exactly, and `goodWaveResidual_grouped` (1275) is the nonconstant
   part. Then `contextFrame`/`stateFullResidual` (1296–1336) instantiate all of this on
   `CorrectionState`, and `residualBlock` (1438) packages the per-label residual as a new
   `HarmonicBlock` — the forcing handed to the next cycle stage.

**Consumers** (grep `HarmonicResidual` over `NavierStokes/*.lean`, 1695 hits in 58 files). The
heaviest are `HarmonicWaveInteraction.lean` (284 hits), `CorrectionStep.lean` (265),
`HarmonicMeanInteraction.lean` (169), `PhysicalResidualNaturality.lean` (86),
`PrimaryResidualClass.lean` (70), `AxisymmetricResidualGrouping.lean` (69),
`StateReindex.lean` (69), `HarmonicSourceSupport.lean` (55), `ActualInitialization.lean` (49),
`ParticularWaveAssembly.lean` (49). Named **in-cone** consumers I verified individually:
`AxisymmetricResidualGrouping.stateGoodWaveResidual_grouped` (line 212, `in_cone`),
`AxisymmetricResidualGrouping.stateFullResidual_reconstructed` (260, `in_cone`),
`AxisymmetricResidualGrouping.extractionRegular_erase` (137, `in_cone`),
`AxisymmetricResidualGrouping.represented_goodResidual_angular_continuous` (162, `in_cone`),
`ActualCycleResidualBounds.extraction_regular` (263, `in_cone`) and
`.actual_extraction_regular` (701, `in_cone`), and `LabelSumBounds.lean:850-851`
(`HarmonicResidual.band_sub`, in-cone file). `ActualInitialization.initialResidualBlock_band`
(290) is the concrete numeral consumer audited in (C).

## Scope

**Sampling scheme, stated honestly.** The file is small enough and its proofs short enough
(median 5 lines) that I did not sample: **I displayed and read all 1620 lines, i.e. all 173
declarations, statements and proof bodies.** What I did *not* do is re-derive the upstream
definitions of every symbol; for the mathematically load-bearing ones I went one level up into
`HarmonicFields.lean`, `HarmonicCalculus.lean`, `LinearWaveResidual.lean` and
`CorrectionState.lean` and read the definitions verbatim (cited below). Beyond that, dependencies
are taken on faith and listed in **Residue**.

| category | count | how |
|---|---|---|
| declarations in file (`INVENTORY.csv`) | 173 | 40 `def`, 124 `theorem`, 6 `structure`, 3 `abbrev` |
| statements read line-by-line | **173 / 173** | full display of lines 1–1620 |
| proof bodies read line-by-line | **173 / 173** | ditto |
| upstream definitions read verbatim | 14 | `field`, `period`, `angularMean`, `angularMean_field`, `field_angular_continuous`, `BandLimited(.mono)`, `along`, `cylindricalLaplacian`, `angularGenerator`, `cylindricalVectorLaplacian`, `LinearWaveResidual.transport/gradient/linearResidual`, `ExcludedErrors.total`, `CorrectionState.angularAverage` |
| repo-wide greps run | 9 | consumers, `ExtractionRegular`/`BlockRepresentation` suppliers, `radialDiv`, numeral consumers |
| declarations only grepped, never read | **0** | — |

### Proof-pattern census (the basis for "no hiding place")

Leading-token census over the whole file (`^\s*token`), cross-checked by targeted grep:

| pattern | instances | risk of hiding a math error |
|---|---|---|
| term-mode direct application / anonymous constructor | ~60 | none beyond the cited lemma's own statement |
| `intro`/`exact`/`have`/`rw` chains | `have` 76, `rw` 56, `exact` 42 | low; every `rw` target is a named lemma |
| `ext` / `funext` congruence | `ext` 33, `funext` 7 | none |
| `fin_cases i <;> simp [...]` component dispatch | **13** (175, 297, 377, 412, 582, 651, 661, 725, 748, 788, 882, 930, 1409) | this is where a wrong `Fin 3` component would hide — **all 13 read**; see (B) |
| `change` / `unfold` definitional re-shaping | `change` 16, `unfold` 8 | defeq only; a mismatch is a compile error |
| `Finset.induction_on` | **3** (732, 745, 782) | all read; both base cases discharge the operator at `0` |
| `by_cases hj : j = 0` harmonic split | **5** (64, 532, 555, 713, 959) | all read |
| `ring` / `abel` / `linear_combination` | `ring` 10, `abel` 3 (583, 631, 707), `linear_combination` 1 (863) | decision procedures over a commutative ring; cannot import a hypothesis |
| `simp` closing the goal outright | 2 (474, 516) | both are `Complex`/`Finsupp` normalisation, not inequalities |
| `calc` | **1** (970) | first/last line checked against the statement — see (B) |
| `field_simp` | **1** (1203) | `[period_ne_zero]`, the side condition is a proved theorem |
| `omega` | **1** (1567) | true `Nat` identity, symbolic exponent |
| `convert! ... using 1` | 2 (801, 1122) | both immediately followed by `ext`/`simp only [Finset.sum_apply]`, i.e. the created goal is displayed and closed |
| **`nlinarith`** | **0** | — |
| **`positivity` / `linarith` / `norm_num` / `decide`** | **0** | — |
| **`simp` closing an inequality** | **0** | the only inequality-shaped predicate in the file is `BandLimited`, always closed by `.mono`/`Nat.le_max_*`/`Nat.le_add_right` |
| **change of variables under an integral** | **0** | the only integrals are `∫ θ in 0..period`, never substituted |

So the brief's "audit EVERY instance of the patterns that can hide a mathematical error" reduces,
for this file, to: the 13 `fin_cases` dispatches, the 1 `calc`, the 3 inductions, the 4 integral
lemmas, and — much more importantly — **the definitions themselves**. That is where I spent the
effort.

## (B) Findings

### B.1 The cylindrical operators are correct (this is the main positive result)

I checked each coefficient-level operator against the standard cylindrical formulas, component by
component. `rotate` (168) and `HarmonicCalculus.angularGenerator` (`HarmonicCalculus.lean:319-320`)
are both literally `![-a 1, a 0, 0]`, i.e. the frame rotation `J`, with `J² a = ![-a 0, -a 1, 0]`
(`HarmonicCalculus.lean:322-323`).

| site | verbatim | textbook | verdict |
|---|---|---|---|
| `scalarLaplacian`, 177–183 | `differentiate g.radial … (differentiate g.radial … c) + constantCoefficient (fun x => ((g.radius x)⁻¹ …)) * differentiate g.radial … c + constantCoefficient (fun x => (((g.radius x) ^ 2)⁻¹ …)) * angularDifferentiate kp (angularDifferentiate kp c) + differentiate g.axial … (differentiate g.axial … c)` | `∂²_r + r⁻¹∂_r + r⁻²∂²_θ + ∂²_z` | **OK** |
| `vectorLaplacian`, 185–190 | `scalarLaplacian … (a i) + constantCoefficient (…r⁻²…) * (constantCoefficient (fun _ => (2 : ℂ)) * rotate (fun j => angularDifferentiate kp (a j)) i + rotate (rotate a) i)` | comp 0: `Δa_r − 2r⁻²∂_θ a_θ − r⁻²a_r`; comp 1: `Δa_θ + 2r⁻²∂_θ a_r − r⁻²a_θ`; comp 2: `Δa_z` | **OK** — expanding `J` and `J²` gives exactly these, signs included |
| `transport`, 192–197 | `a 0 * differentiate g.radial … (b i) + (a 1 * constantCoefficient (fun x => ((g.radius x : ℂ)⁻¹))) * (angularDifferentiate kp (b i) + rotate b i) + a 2 * differentiate g.axial … (b i)` | `a_r∂_r b + (a_θ/r)(∂_θ b + Jb) + a_z∂_z b`, i.e. comp 0 gets `−b_θ`, comp 1 gets `+b_r` | **OK** |
| `gradient`, 199–203 | `![differentiate g.radial k Φ p, constantCoefficient (fun x => ((g.radius x)⁻¹ …)) * angularDifferentiate kp p, differentiate g.axial k Φ p]` | `(∂_r p, r⁻¹∂_θ p, ∂_z p)` | **OK** |
| `linearResidual`, 206–210 | `differentiate g.time … (a i) + transport … B a i + transport … a B i + gradient … p i - constantCoefficient (fun _ => (g.viscosity : ℂ)) * vectorLaplacian … a i` | `∂_t a + (B·∇)a + (a·∇)B + ∇p − νΔa` | **OK** |
| `nonlinearResidual`, 212–214 | `linearResidual g k Φ kp B a p i + transport g k Φ kp a a i` | perturbation residual around base `B`; **the base's own residual `∂_tB+(B·∇)B−νΔB` is deliberately absent** | **OK** — it is restored as `s.errors.base` at 1328, see B.3 |

The field-level counterparts I read verbatim and they agree:
`HarmonicCalculus.lean:183-186` (`cylindricalLaplacian`), `:330-334`
(`cylindricalVectorLaplacian`, `2 * angularGenerator (…) i + angularGenerator (angularGenerator (a x)) i`
scaled by `((R x) ^ 2)⁻¹`), `LinearWaveResidual.lean:46-50` (`transport`, `u x 1 / (R x : ℂ)`),
`:52-54` (`gradient`), `:57-61` (`linearResidual`).

**Verdict: OK.** UNBUILT (no elaboration check), but the formulas are right.

### B.2 The bilinearity / summation layer (`namespace Actual`, 577–865)

| decl | line | pattern | verdict |
|---|---|---|---|
| `angularGenerator_add` | 579 | `fin_cases <;> simp; abel` | OK |
| `transport_add_left` | 585 | `simp only [transport, Pi.add_apply]; ring` — **no differentiability hypothesis, correctly**: `transport` is *pointwise* linear in its first argument | OK |
| `transport_add_right` | 593 | needs `ha`/`hb : ∀ i, DifferentiableAt ℝ … x` because `along_add` is used | OK |
| `twiceAlong_add` | 604 | `along_congr` on the open set, then `along_add`; the "second derivative of a sum" step is done properly via `EqOn … U` | OK |
| `cylindricalLaplacian_add` / `cylindricalVectorLaplacian_add` | 618 / 633 | `abel` / `fin_cases <;> simp … <;> ring`; hypotheses `hf hg : ContDiffOn ℝ ∞ … U`, `hx : x ∈ U` | OK |
| `linearResidual_add` | 663 | assembles the four pieces then `ring` | OK |
| `nonlinearResidual_add_sub` | 690 | `R(B,a+b,p+q) − R(B,a,p) = LR(B,b,q) + T(a,b) + T(b,a) + T(b,b)`; verified by hand: the quadratic term `T(a+b,a+b) − T(a,a)` is exactly `T(a,b)+T(b,a)+T(b,b)` | OK |
| `transport_zero_of_disjoint` | 710 | `by_cases hu : u x = 0`; if `u x ≠ 0` then `x ∈ tsupport u`, so `x ∉ tsupport v`, so `v =ᶠ[𝓝 x] 0` (718), hence `v x = 0` **and** all `along V (v · i) x = 0` (720–723). Correct and complete — this is the lemma that kills the cross terms. **It needs GLOBAL `Disjoint (tsupport u) (tsupport v)`** (711) | OK (see B.5) |
| `transport_sum_left/right/self` | 727 / 739 / 757 | `Finset.induction_on`; `transport_sum_self` (761) is the diagonal collapse using `Finset.sum_eq_single` + `transport_zero_of_disjoint` | OK |
| `linearResidual_sum` | 773 | induction; the `empty` case (783–791) discharges every operator at the zero field via `hzero : along V (fun _ => 0) = 0` | OK |
| `nonlinearResidual_sum` | 807 | linear part by `linearResidual_sum`, quadratic part by `transport_sum_self` under `hdisj` | OK |
| `linearResidual_base_add` | 823 | `LR(B+M,a,p) = LR(B,a,p) + T(M,a) + T(a,M)` | OK |
| `nonlinearResidual_mean_add` | 836 | `R(B, M+a, p+q) = R(B,M,p) + R(B+M, a, q)`. **I expanded both sides by hand**: LHS `= ∂_t(M+a) + T(B,M+a) + T(M+a,B) + ∇(p+q) − εΔ(M+a) + T(M,M)+T(M,a)+T(a,M)+T(a,a)`; RHS sums to the same. Closes with `linear_combination hei` (863) | OK |

### B.3 The grouping identities

* `goodResidual_grouped` (1091) — **the mathematical heart.** Statement 1100–1103:
  `goodResidual … x i = (meanCoefficients g B M p i 0 x.1).re + virtual x.1 i + ∑ l ∈ labels, (field ((data l).residualCoefficients g B M i) … x).re`.
  Binder order (1091–1099): `labels, data, {U}, hU, {g}, hg : g.Regular U, B M p virtual,
  hB hM hp` (smoothness on `U`), `hd : ∀ l ∈ labels, (data l).Regular U`,
  `hdisj` (pairwise disjoint closed supports), **then** `{x} (hx : x ∈ liftDomain U) (i : Fin 3)`.
  Every regularity datum is fixed **before** the point `x`. There is no constant in the statement,
  so no uniformity claim to slip. Proof = `nonlinearResidual_mean_add` + `nonlinearResidual_sum` +
  `meanCoefficients_field` + `residualCoefficients_field`, closed by `ring` (1143). **OK.**
* `goodResidual_angularMean` (1235) — statement 1244–1245. Same binder order plus
  `hkp : ∀ l ∈ labels, (data l).angularFrequency ≠ 0` (1243) **before** `x`. **OK.**
* `goodWaveResidual_grouped` (1275) — the nonconstant part; `rw` of the two above, then
  `simp only [meanResidualValue, LabelData.waveResidualCoefficients, field_nonconstant, …]; ring`.
  **OK.**
* `BlockRepresentation.goodResidual_eq` (1424) — the docstring claims *"The fixed base error
  cancels literally"*. I checked the cancellation arithmetic: `stateFullResidual` (1322) is
  `(…).re + contextVirtual c n x.1 i + s.errors.base n x i` (1327–1328); `stateGoodResidual`
  (1330) subtracts `s.errors.total`; and `CorrectionState.ExcludedErrors.total` is
  `e.base + e.gaussian + e.aliasError` (`CorrectionState.lean:47-48`). So
  `stateFullResidual − total = (…).re + virtual − gaussian − alias`, which is exactly
  `goodResidual` (1019–1024) after `hrep.gaussian`/`hrep.aliasError`. The closing `ring` (1436) is
  legitimate. **OK.**
* `stateFullResidual_reconstructed` (1596) — `rw [← stateGoodWaveResidual_grouped …,
  stateMeanCoefficientValue_eq_average …]; simp only [...]; ring` (1605–1608). Algebraically
  `(G − A) + A + total = G + total`. **OK** (but see B.5 for its hypothesis).
* `residualBlock_mean_zero` (1584) — `change` (1589–1591) rewrites
  `CorrectionState.angularAverage` into `realAngularMean`. This works **only because**
  `angularAverage` is `(∫ θ in 0..2*Real.pi, …) / (2*Real.pi)` (`CorrectionState.lean:73-74`) and
  `period := 2 * Real.pi` (`HarmonicFields.lean:126`) are literally the same term. Two
  independently defined means silently identified by defeq. It is *safe* (a mismatch would be a
  compile error, not a false theorem), but it is a coupling nobody documents. **NOTE.**

### B.4 The four integral facts — the interchange audit

The brief asked specifically for asserted interchanges. There are none. Verbatim:

* `realAngularMean` (1198–1199): `(∫ θ in (0 : ℝ)..period, f θ) / period`.
* `realAngularMean_const` (1201): `simp only [realAngularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]` then `field_simp [period_ne_zero]` (1203). `period_ne_zero` is a **proved** theorem (`HarmonicFields.lean:130`, from `period_pos`, `:128`). **OK.**
* `realAngularMean_add` (1205): hypotheses `(hf : Continuous f) (hg : Continuous g)`; proof
  `rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), add_div]` (1208). Integrability is **derived from continuity, not assumed**. **OK.**
* `realAngularMean_sum` (1210): hypothesis `(hf : ∀ l ∈ s, Continuous (f l))`; proof
  `rw [intervalIntegral.integral_finsetSum (fun l hl => (hf l hl).intervalIntegrable _ _), Finset.sum_div]` (1214). Finite sum only — **no infinite interchange anywhere in the file.** **OK.**
* `realAngularMean_field` (1217): the `Complex.re`/integral commutation is done by
  `Complex.reCLM.intervalIntegral_comp_comm` **with an explicit integrability argument**
  `((field_angular_continuous c k Φ kp x).intervalIntegrable (0 : ℝ) period)` (1220–1221), and
  `field_angular_continuous` is proved unconditionally at `HarmonicFields.lean:121-124`. The
  exactness input `angularMean_field` (`HarmonicFields.lean:192-201`) requires `kp ≠ 0`, and that
  hypothesis is threaded here as `{kp : ℤ} (hkp : kp ≠ 0)` (1218). **OK.**
* Call sites: `goodResidual_angularMean` supplies `continuous_const` and
  `continuous_finsetSum labels (fun l _ => hF l)` (1259–1262), with
  `hF (l : ι) : Continuous (F l) := Complex.continuous_re.comp (field_angular_continuous _ _ _ _ _)` (1254–1255). **OK.**

### B.5 NOTE — `HarmonicResidual.ExtractionRegular` has no supplier in the repository

This is the (B)/leaf-hypothesis finding.

`ExtractionRegular` is declared twice in the artifact, with the **same name**, the **same nine
field names**, and one materially different field:

* `NavierStokes/HarmonicResidual.lean:1472-1473` (this file):
  `disjoint : ∀ l ∈ labels n, ∀ j ∈ labels n, l ≠ j →` /
  `    Disjoint (tsupport ((blockFamily l).oscillation n)) (tsupport ((blockFamily j).oscillation n))`
* `NavierStokes/LocalResidualGrouping.lean:220-222`:
  `disjoint : ∀ l ∈ labels n, ∀ j ∈ labels n, l ≠ j →` /
  `    Disjoint (liftDomain U ∩ tsupport ((blockFamily l).oscillation n))` /
  `      (liftDomain U ∩ tsupport ((blockFamily j).oscillation n))`

This file's version demands **global** support separation; the `LocalResidualGrouping` version
demands separation only **inside `liftDomain U`** and is therefore strictly weaker.

I enumerated every occurrence of `ExtractionRegular` in `NavierStokes/*.lean` and classified each
as hypothesis-position or conclusion-position. Result:

* **Conclusion position, concrete state:** `ActualInitialization.initial_extraction_regular`
  (`ActualInitialization.lean:848-849`), `ActualCycleResidualBounds.extraction_regular`
  (`:263,269`), `ActualCycleResidualBounds.actual_extraction_regular` (`:701,702`) — **all three
  produce `LocalResidualGrouping.ExtractionRegular`.**
* **Conclusion position, transport only:** `LocalResidualGrouping.ExtractionRegular.erase`
  (`:238-239`) and `AxisymmetricResidualGrouping.extractionRegular_erase` (`:137,142`) — each
  consumes one of the same flavour it produces.
* **Nowhere** does any declaration construct a `HarmonicResidual.ExtractionRegular` from
  anything other than a `HarmonicResidual.ExtractionRegular`.

And `LocalResidualGrouping.lean` re-proves **the whole grouping layer of this file**, from the
disjointness lemma upwards, using the weaker local structure: `zero_germ_of_disjoint_on` (`:25`),
`transport_zero_of_disjoint_on` (`:33`) — the local twin of this file's
`Actual.transport_zero_of_disjoint` (710) — then `transport_sum_self` (`:50`),
`nonlinearResidual_sum` (`:70`), `goodResidual_grouped` (`:90`), `goodResidual_angularMean`
(`:145`), `goodWaveResidual_grouped` (`:181`), and finally the state-level tail:
`stateGoodWaveResidual_grouped_of_blockRepresentation` (`:267`),
`stateMeanCoefficientValue_eq_average` (`:280`), `stateGoodWaveResidual_grouped` (`:296`),
`stateGoodResidual_angularAverage` (`:314`), `stateFullResidual_reconstructed` (`:338`).
That is a full, independent local-support re-derivation — which is exactly why this file's
global-support version is unused.

**Consequence.** This file's `stateGoodWaveResidual_grouped` (1488, in-cone),
`stateMeanCoefficientValue_eq_average` (1508, in-cone), `residualBlock_smooth` (1542, not in
cone) and `stateFullResidual_reconstructed` (1596, in-cone) are theorems whose leading hypothesis
**no declaration in the artifact can supply**. Their consumers
(`CorrectionStep.fullGoodWaveResidual_grouped:1405`, `.fullResidual_reconstructed:9256`,
`PhysicalResidualJetBounds.state_fullResidual_reconstructed:123`,
`HarmonicWaveInteraction.grouped_wave_change:1116`,
`HarmonicMeanInteraction.grouped_wave_change:613`) are all `in_cone == False` in `INVENTORY.csv`;
`AxisymmetricResidualGrouping.stateGoodWaveResidual_grouped:212` and
`.stateFullResidual_reconstructed:260` are `in_cone == True` but their only consumers
(`CorrectionStep.lean:9254,9264`) are `in_cone == False`, while the *local* twins
(`CorrectionStep.lean:9272,9282`, `fullGoodWaveResidual_grouped_local:9266`) are also out of cone.

**Direction of the gap is safe**: a weaker hypothesis gives a *stronger* theorem, so
`LocalResidualGrouping` is not smuggling anything in from this file. But the honest reading is
that **this file's `ExtractionRegular`-gated tail is dead legacy code that the cone script marks
live**, and the `in_cone == True` flag on three of its theorems is an artefact of syntactic
reachability (which `audits/nse-deep/COVERAGE.md` itself calls "an over-approximation").
**NOTE**, plus ESCALATION E1.

### B.6 NOTE — two distinct `nonlinearResidual` definitions, 474 lines apart

`nonlinearResidual` is defined twice in this file:

* line 212, on `VectorCoefficients` (coefficient level), inside `namespace NavierStokes.HarmonicResidual`;
* line 686, on `D → ComplexVector` (field level), inside `namespace Actual` (opened at 577, closed at 865), so its full name is `NavierStokes.HarmonicResidual.Actual.nonlinearResidual`.

They are genuinely different functions of different types, and the file distinguishes them
correctly at every use I checked: `meanCoefficients` (1004) uses the coefficient-level one,
`goodResidual` (1019) and `stateFullResidual` (1324) use the explicitly qualified
`Actual.nonlinearResidual`. But the shadowing is a real trap for a reader — and for an auditor
who greps. Similarly `linearResidual` (206) vs `LinearWaveResidual.linearResidual`.
**NOTE**, no error found.

### B.7 UNCLEAR — nothing in this file ties `Frame` to a genuine cylindrical frame

`Frame` (158–163) is `radius : D → ℝ`, `radial axial time : D → D`, `viscosity : ℝ`, and
`Frame.Regular` (868–873) asks only for `ContDiffOn` of each plus `radius x ≠ 0` (870). There is
**no orthonormality condition, no relation between `radius` and the angular direction, and no
condition that `radial`/`axial`/`angularDirection` span anything.** The angular direction is the
hard-coded `angularDirection (_p : D × ℝ) : D × ℝ := (0, 1)` (33), i.e. the raw `∂_θ`, and the
metric factor appears only as the explicit `(g.radius x)⁻¹`/`(g.radius x)^{-2}` weights in the
operators. That is *self-consistent* (raw angle ⇒ `1/r` weights), and `HarmonicCalculus.lean:328-329`
is candid about the gap: *"Its identification with Cartesian vector Laplacian belongs to the
cylindrical coordinate calculus."*

So `stateFullResidual` (1322) is the residual of a **formal operator built from an arbitrary
`Frame`**, and nothing in this file certifies that `stateFullResidual c s n x i = 0` means the
reconstructed velocity solves incompressible Navier–Stokes. Two things are simply absent from
this file: the frame↔Cartesian identification, and the **continuity/divergence-free equation**
(the file's residual is momentum-only; pressure enters only through `gradient`).
**UNCLEAR** — presumably supplied elsewhere; ESCALATION E2. I am explicitly *not* claiming a
defect, only that this file does not contain the link and I did not find it within my scope.

### B.8 Remaining per-declaration verdicts (grouped; all read line-by-line)

| group | lines | notes | verdict |
|---|---|---|---|
| `liftDomain`/`liftDirection`/`angularDirection` and `SmoothCoefficients` algebra | 26–78 | `SmoothCoefficients.mul` (52) routes through `HarmonicFields.convolution_apply` and `ContDiffOn.sum` — a *finite* Finsupp support sum, no interchange | OK |
| `field_add/zero/neg/sub/constant`, `field_smoothOn` | 81–115 | ring-hom transport of `evaluate`; `field_smoothOn` (103) is a finite `ContDiffOn.sum` over `c.support` | OK |
| `along_liftDirection` (117), `along_angularDirection` (129) | 117–135 | the two derivative-lift lemmas; both carry `hf : DifferentiableAt ℝ f (x, θ)`. `along_angularDirection` uses `HasDerivAt (fun t => (x, t)) (0, 1) θ` (132) — matches `angularDirection = (0,1)` (33) exactly | OK |
| `field_differentiate` (137), `field_angularDifferentiate` (148) | 137–155 | differentiability obtained from `field_smoothOn` at an interior point via `(liftDomain_open hU).mem_nhds` | OK |
| `field_secondDerivative` … `field_nonlinearResidual` | 216–341 | the bridge family; the two `change` blocks at 265–266 and 316–319 restate the goal in `vectorField (rotate …)` form so that `vectorField_rotate` can fire, then close by `rfl`. First/last shapes match the statements | OK, UNBUILT |
| `field_gradient` (289) | 289–299 | `fin_cases i <;> simp [...]` — the one bridge proved purely by component dispatch; components match `gradient` (201–203) and `LinearWaveResidual.gradient` (`LinearWaveResidual.lean:54`) one for one | OK |
| `band_*` family | 346–438 | `band_nonlinearResidual` (431) gives `N + N`; `band_linearResidual` (417) requires `hB : ∀ i, BandLimited (B i) 0`, i.e. **the base must be axisymmetric** — supplied at 1152 via `band_constantCoefficient` | OK |
| `realCoefficients` family | 453–499 | `realCoefficients c = constantCoefficient (fun _ => (2 : ℂ)⁻¹) * (c + conjugateReverse c)` (454); `field_realCoefficients` (478) proves it equals `((field c …).re : ℂ)` via `Complex.add_conj` — i.e. `(z + conj z)/2 = Re z`. Correct | OK |
| `extract` (502), `extract_field` (508), `coefficients_unique` (520) | 502–523 | extraction against the conjugate carrier; `extract_field` needs `hkp : kp ≠ 0` (509) and it is threaded everywhere it is used (1196, 1582) | OK |
| `nonconstant` family | 525–575 | `nonconstant c = c.erase 0` (525); `field_nonconstant` (539) `= field c … − c 0 p.1`; `angularMean_nonconstant` (545) needs `kp ≠ 0` | OK |
| `Frame.Regular.invRadius/invSquare` (887/891), `smooth_*` family | 875–943 | term-mode mirrors of the operator definitions; `smooth_rotate` (879) `fin_cases` branches `(ha 1).neg / ha 0 / smoothCoefficients_zero` match `rotate = ![-a 1, a 0, 0]` | OK |
| `band_zero_eq_constant` (955), `field_band_zero` (968) | 955–973 | the **one `calc`** in the file, lines 970–973: `_ = field (constantCoefficient (c 0)) k Φ kp p := congrArg … (band_zero_eq_constant hc)` then `_ = _ := field_constant _ _ _ _ _`. First line's LHS is the statement's LHS `field c k Φ kp p`, last line's RHS is `c 0 p.1`. **First and last match the statement.** | OK |
| `LabelData` (976), `.Regular` (997) | 976–1000 | `LabelData.Regular` asks smoothness of `phase`, `velocity`, `pressure` only — **not** of `gaussian`/`aliasError`; those are separate `ExtractionRegular` fields (1470–1471) and are threaded as separate hypotheses in `waveResidualCoefficients_smooth` (1184–1185). Consistent | OK |
| `meanCoefficients_band/_field` (1026/1032), `residualCoefficients_field` (1063) | 1026–1089 | `meanCoefficients_field` closes by `field_band_zero (meanCoefficients_band …)` (1061): the mean part is band-0, so its field is its own zero coefficient. Correct | OK |
| `residualCoefficients_band` (1145), `waveResidualCoefficients_band` (1156), `_values` (1163), `_conjugate` (1171/1175), `_smooth` (1179) | 1145–1191 | `max (N + N) E`; `.mono` used with `Nat.le_max_left`/`Nat.le_max_right` (1153–1154) — direction correct against `BandLimited.mono` (`HarmonicFields.lean:335-337`) | OK |
| `contextFrame` … `stateGoodWaveResidual` | 1296–1336 | `contextFrame.time = fastCoefficient n • vT − epsilon n • eT` (1301); `viscosity = epsilon n` (1302) — so the same `epsilon n` is both the viscosity and part of the time direction. Consistent within the file | OK |
| `ofBlock` (1342) + `ofBlock_wave/pressure/tsupport_wave/regular` | 1342–1388 | `ofBlock_tsupport_wave` (1365) proves `tsupport (…).wave = tsupport (b.oscillation n)` — needed so the disjointness hypothesis on blocks transfers to `LabelData`; used by `ExtractionRegular.dataDisjoint` (1476) | OK |
| `BlockRepresentation` (1392) + `.perturbation/.pressureField` | 1392–1421 | pure representation hypotheses; docstring 1390 is candid: *"Only representations of the stored fields are inputs; no residual identity is assumed."* | OK |
| `residualBlock` (1438) | 1438–1446 | `pressure := fun _ => 0` (1443) — the residual block carries **no** pressure. Deliberate (the next solve produces its own) but worth naming | NOTE |
| `residualBlock_band` (1522), `_conjugate` (1532), `_zero_mode` (1537), `_values` (1550), `_stage_band` (1561), `_extract` (1570), `_mean_zero` (1584) | 1522–1593 | `_zero_mode` is `Finsupp.erase_same` (1540) — the zero harmonic is erased by construction; `_extract` needs `hkp` (1572) | OK |
| `contextFrame_regular` (1612) | 1612–1618 | `refine ⟨hR, hRn, ?_, contDiffOn_const, contDiffOn_const⟩` — `axial` and `time` of `contextFrame` are constant in `x` (1300–1301), so `contDiffOn_const` is right | OK |

## (C) Every explicit numeral / rational constant in a theorem statement

I extracted the statement region (declaration head up to `:=` / `by`) of all 124 theorems and
scanned for numerals. **The only numerals occurring in any theorem statement in this file are
`0`, `1`, `2` and `3`. There is not a single rational literal, and not a single numeral with more
than one digit.** So the "producer's `2001/1000` vs consumer's `2/1`" failure mode has no
foothold here. Full list with roles:

| constant | representative site (verbatim) | role | consumer check |
|---|---|---|---|
| `3` | ubiquitous, e.g. `1099`: `{x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :` | space dimension | `Fin 3` everywhere in `HarmonicCalculus`/`LinearWaveResidual`/`CorrectionState`; `ComplexVector = Fin 3 → ℂ`. **OK** |
| `0` as harmonic index | `1026`: `∀ i, BandLimited (meanCoefficients g B M p i) 0`; `1101`: `(meanCoefficients g B M p i 0 x.1).re`; `1539`: `(residualBlock … ).velocity n i 0 = 0` | the zero (mean) harmonic | `LocalResidualGrouping.lean:101` and `:159` and `:170` and `:253` all use `meanCoefficients g B M p i 0` — **same index 0. OK** |
| `0` as band bound | `968`: `theorem field_band_zero {c : Coefficients D} (hc : BandLimited c 0)`; `419`: `(hB : ∀ i, BandLimited (B i) 0)` | axisymmetric base | supplied at 1029–1030 and 1152 by `band_constantCoefficient`. **OK** |
| `0`/`1`/`2` as `Fin 3` components | `168`: `noncomputable def rotate (a : VectorCoefficients D) : VectorCoefficients D := ![-a 1, a 0, 0]` | frame rotation `J` | identical to `HarmonicCalculus.angularGenerator`, `HarmonicCalculus.lean:319-320`: `![-a 1, a 0, 0]`. **OK** |
| `(2 : ℂ)⁻¹` | `458`: `realCoefficients c j x = (2 : ℂ)⁻¹ * (c j x + conj (c (-j) x))` (def at `454`) | real projection `(z+z̄)/2` | consumers `LabelSumBounds.lean:404`, `ActualCycleCoherence.lean:129`, `ActualReferenceRebase.lean:154,157,160,163`, `HarmonicWaveInteraction.lean:285,765,835`, `PhysicalResidualNaturality.lean:145,421`, `ActualCyclePeriodicity.lean:94`, `WaveStageContinuation.lean:289`, `ActualInitialization.lean:371`, `LabelSupportPreservation.lean:361,402,423` — **all consume the lemma, so all use the same `2`. OK** |
| `(2 : ℂ)` in `vectorLaplacian` | `189`: `constantCoefficient (fun _ : D => (2 : ℂ)) * rotate (fun j => angularDifferentiate kp (a j)) i` (def) | the `2` of the `2r⁻²∂_θ J a` connection term | matched field-level: `HarmonicCalculus.lean:333`: `(2 * angularGenerator (fun j => along Vθ (fun y => a y j) x) i +`. **OK — same 2 on both sides of the bridge (`field_vectorLaplacian`, 249).** |
| exponent `2` in `r²` | `181`, `188` (defs) and `892` (statement): `SmoothCoefficients U (constantCoefficient (fun x => (((g.radius x) ^ 2)⁻¹ : ℝ) : D → ℂ))` | `r⁻²` weight | matched at `HarmonicCalculus.lean:186` and `:332`: `((R x) ^ 2)⁻¹`. **OK** |
| `N + N` | `435`: `∀ i, BandLimited (nonlinearResidual g k Φ kp B a c i) (N + N)` | quadratic band doubling | consumed by `residualCoefficients_band` (1149) as `max (N + N) E`. **OK** |
| `max (N + N) E` | `1149`, `1160`, `1168`, `1526`: `(residualBlock c s b gaussian aliasError).BandLimited (max (N + N) E)`, `1556` | band of the residual block | **The one concrete numeral chain in the artifact, and I checked it end to end:** `ActualInitialization.lean:290`: `theorem initialResidualBlock_band (l : Index B N0) : (initialResidualBlock l).BandLimited 2`, proved by `residualBlock_band` (`:296-297`) with `hb = primaryBlock_band l : (primaryBlock l).BandLimited 1` (`:124`) and `hG`/`hA` at band `1` (`:291-294`). So `N = 1, E = 1` and `max (1+1) 1 = 2` — **the claimed `2` is exactly right. OK** |
| `2 ^ stage`, `2 ^ (stage + 1)` | `1563-1566`: `(stage : ℕ) (hb : b.BandLimited (2 ^ stage))` … `(residualBlock c s b gaussian aliasError).BandLimited (2 ^ (stage + 1))` | dyadic band schedule | specialises `max (N + N) E` with `N = 2 ^ stage`, `E = 2 ^ (stage + 1)`: `max (2^s + 2^s) (2^(s+1)) = 2^(s+1)`. Proved by `have he : 2 ^ stage + 2 ^ stage = 2 ^ (stage + 1) := by omega` (1567) then `simpa only [he, max_self]` (1568). **Arithmetically correct. OK** |
| `radialDiv 2` / `radialDiv 1` | `1319` (def `contextVirtual`): `![0, -(c.operators.radialDiv 2 c.virtualTheta n x), -(c.operators.radialDiv 1 c.virtualAxial n x)]` | cylindrical weight exponent per component | **Cross-checked against the independent definitions of the same residuals:** `CorrectionInitialization.lean:1833`: `u.thetaResidual c = c.operators.radialDiv 2 (u.covariance 0 1) + …` and `:1834`: `… - c.operators.radialDiv 2 c.virtualTheta`; `:1840-1841`: `u.axialResidual c = c.operators.radialDiv 1 (u.covariance 0 2) + … - c.operators.radialDiv 1 c.virtualAxial`. **θ-component uses 2, axial uses 1, in both places. Also matched by `PhysicalResidualTZ.lean:278-279`. OK — no off-by-one.** |

**Verdict for (C): OK.** No numeral disagreement found between any producer and any consumer.

## Kernel-risk assessment

### Vector (1) — recursive inductive types, recursors, iota reduction

**No risk introduced by this file.** `grep -n '\binductive\b'` → **0 hits**. `grep -n '\.rec\b'` →
**0 hits**. `Acc.rec` → 0. `WellFounded` → 0. `termination_by` → 0. `deriving` → 0. `motive` → 0.
`Nat.rec` → 0.

The file declares **6 `structure`s**, all single-constructor and **non-recursive**:
`Frame` (158, `Type`-valued), `Frame.Regular` (868, `Prop`), `LabelData` (976, `Type`),
`LabelData.Regular` (997, `Prop`), `BlockRepresentation` (1392, `Prop`),
`ExtractionRegular` (1461, `Prop`). All six are used only through field projections and anonymous
constructors (`⟨…⟩` at 1169, 1388, 1557 and `refine ⟨…⟩` at 1527, 1617); no
`.rec`, no custom `motive`, no large elimination. Structure-eta and projection-iota on a
non-recursive one-constructor structure is the most-exercised and least-suspect corner of the
kernel.

The only iota reduction of any interest is on `Fin 3` through the `![a, b, c]`
(`Matrix.of ∘ vecCons`) literals at 168, 201, 1305, 1308, 1311, 1319, combined with the 13
`fin_cases i` dispatches. `fin_cases` on `Fin 3` produces three closed goals and each is closed by
`simp` using `Matrix.cons_val_*` lemmas; the kernel work is three constructor-index reductions per
site, at most 39 in the file. **No risk.**

`Finset.induction_on` (732, 745, 782) reduces to `Finset.induction`, i.e. `Multiset`/`List`
recursion in Mathlib, not in this file. Its use here is structurally standard (base case + insert
case) and the recursion is over an abstract `Finset ι`, so no closed unfolding is ever demanded of
the kernel.

**Verdict: OK.**

### Vector (2) — `Nat` arithmetic delegated to GMP

**No bignum exposure at all.**

* `grep -nE '(?<![\w.])\d{5,}'` → **0 hits**: there is no numeral of 5 or more digits anywhere in
  the file (including comments).
* Largest closed numeral in scope, anywhere in the file: **`3`** (as `Fin 3`); the largest
  arithmetic literal is **`2`** (as `(2 : ℂ)` at 189, `(2 : ℂ)⁻¹` at 454, the exponent `2` at 181,
  188, 892, 894, and the base `2` at 1563–1567).
* `Nat.pow` / `Nat.div` / `Nat.mod` / `Nat.gcd` → **0 hits**. `Nat.choose` / factorial → 0.
* `decide` → **0 hits**; `native_decide` → 0; `norm_num` → 0.
* The **only** arithmetic tactic call in 1620 lines is line 1567, verbatim:
  `  have he : 2 ^ stage + 2 ^ stage = 2 ^ (stage + 1) := by omega`
  The exponent is the **bound variable** `stage : ℕ` (1563), so this is never a closed
  computation: whatever proof term `omega` emits, it is a fixed-size term that the kernel checks
  by rewriting `2 ^ (stage + 1)` to `2 * 2 ^ stage`, not by evaluating a power. Its statement is
  mathematically true for every `stage`. **UNBUILT** (I cannot confirm `omega` in fact closes
  this goal — it is `Nat` linear arithmetic over the atom `2 ^ stage` plus one `pow_succ`
  normalisation, which recent `omega` does handle; and the artifact compiled).
* **Peak kernel numeral work, as a value: the evaluation of `(2 : ℕ)` and of the `Fin 3` index
  literals `0, 1, 2`. Every closed numeral the kernel must reduce in this file is `< 10`. Zero GMP
  invocations of any size.**

**Verdict: OK.**

### Vector (3) — custom metaprogramming

**None.** `grep -nE '\b(macro|elab|syntax|notation|run_cmd|set_option)\b'` → **0 hits**;
`#eval` → 0; `native_decide` → 0; `axiom` → 0; `opaque` → 0; `unsafe` → 0; `partial` → 0;
`sorry` → 0. Attributes used: `@[simp]` only (81, 86, 90, 94, 98, 171, 457, 949). The 36
`omit [NormedAddCommGroup D] [NormedSpace ℝ D] in` lines are plain instance-binder management, not
metaprogramming. Consistent with the repo-wide finding the brief told me not to redo.

**Verdict: OK.**

### Overall kernel verdict

If the Lean 4 kernel has a bug that could fake a proof, **this file is not where it would be
exercised.** It contains no recursion, no numeral computation, no decision-procedure-by-evaluation,
and no metaprogramming. The entire trust surface is (a) structure projections, (b) `Fin 3` case
analysis, (c) `simp`/`rw` rewriting against Mathlib lemmas, and (d) `ring`/`abel`/`omega`/
`linear_combination` proof terms over commutative structures. **KERNEL-RISK: none found.**

## Escalations

**E1. Is any in-cone step of the headline chain gated on `HarmonicResidual.ExtractionRegular`
(global support disjointness) rather than `LocalResidualGrouping.ExtractionRegular` (local)?**

*Precise question.* `HarmonicResidual.ExtractionRegular` (`HarmonicResidual.lean:1461`, `disjoint`
field at `:1472-1473`, global `tsupport` separation) is never constructed anywhere in the artifact
except by the two transport lemmas `AxisymmetricResidualGrouping.extractionRegular_erase:137`
and `LocalResidualGrouping.ExtractionRegular.erase:238` (each of which needs one of the same
flavour as input). The only concrete suppliers —
`ActualInitialization.initial_extraction_regular:848`,
`ActualCycleResidualBounds.extraction_regular:263`, `.actual_extraction_regular:701` — all build
the *weaker* `LocalResidualGrouping.ExtractionRegular` (`LocalResidualGrouping.lean:210`,
`disjoint` field at `:220-222`, separation only inside `liftDomain U`). Does the dependency chain
of any headline theorem pass through the global-flavour tail
(`HarmonicResidual.stateFullResidual_reconstructed:1596`,
`AxisymmetricResidualGrouping.stateFullResidual_reconstructed:260`,
`CorrectionStep.fullResidual_reconstructed:9256`)? If yes, that chain is conditional on a
hypothesis with no supplier and the headline is not proved. If no, then three `in_cone == True`
rows of this file (1488, 1508, 1596) are false positives of the cone script and should be
demoted.

*What would settle it.* An **edge-level** (not name-level) dependency query: from each of the four
headline theorems, the actual `Environment` constant dependencies (e.g. via
`#print axioms` / `CollectAxioms`-style traversal, or `lake env lean` with a `getUsedConstants`
walk), checking whether `NavierStokes.HarmonicResidual.ExtractionRegular` appears. A one-line
decisive alternative: add `theorem probe (h : LocalResidualGrouping.ExtractionRegular U c s labels blocks g a n) : HarmonicResidual.ExtractionRegular U c s labels blocks g a n := by exact?`
in a scratch file — it should **fail**, since local disjointness does not imply global
disjointness, and that failure is the whole finding.

**E2. Where is the theorem that `stateFullResidual c s n x i = 0` implies the reconstructed field
solves incompressible Navier–Stokes in Cartesian coordinates?**

*Precise question.* `Frame` (`HarmonicResidual.lean:158-163`) and `Frame.Regular` (`:868-873`)
impose no orthonormality and no compatibility between `radius`, `radial`, `axial` and the
hard-coded `angularDirection := (0, 1)` (`:33`). The operators are formal expressions in
`along Vr/Vθ/Vz` with explicit `r⁻¹`, `r⁻²` weights, and `HarmonicCalculus.lean:328-329` says
outright that the identification with the Cartesian vector Laplacian *"belongs to the cylindrical
coordinate calculus"* — i.e. elsewhere. Separately, this file's residual is **momentum only**:
there is no divergence-free / continuity condition anywhere in it (pressure enters solely as
`gradient`, `:199`). So: which declaration certifies (i) that `contextFrame c n` is a genuine
orthonormal cylindrical frame with `radius` its cylindrical radius, and (ii) that the
divergence constraint is enforced on the reconstructed velocity?

*What would settle it.* Two named theorems: one of the shape
`cylindricalLaplacian R Vr Vθ Vz f x = (Cartesian Δ) f x` under an explicit orthonormal-frame
hypothesis instantiated at `contextFrame`, and one of the shape
`divergence (totalVelocity s c) = 0` (or a `DivFree` predicate) discharged for the assembled
state. If neither exists for `contextFrame`, then "residual = 0" is a statement about a formal
operator, not about Navier–Stokes, and the reader must be told so. (The audit tree already has a
`_sub-index-force-divfree.md` worker; this should be cross-checked against it rather than
re-litigated here.)

## Residue — what I could NOT check

1. **Nothing is machine-checked.** No Mathlib, no `lake build`, no `#print axioms`. Every verdict
   is a source reading. In particular I cannot confirm that `omega` closes line 1567, that the
   `simp only` sets at 243–247, 263, 281–284, 297–299, 314, 1140, 1290, 1410–1411, 1420,
   1432–1435, 1456–1458, 1516–1517 actually close their goals, or that the 16 `change`s (262, 265,
   280, 285, 313, 316, 338, 514, 531, 857, 958, 1052, 1080, 1257, 1370, 1589) are in fact
   definitional. All are
   **UNBUILT**. (Their *failure* mode is a compile error, not a false theorem, so this residue is
   about my confidence, not about soundness.)
2. **Upstream definitions taken on faith beyond one level.** I read `field`, `evaluate`'s
   signature, `period`, `angularMean`, `angularMean_field`, `field_angular_continuous`,
   `BandLimited`, `.mono`, `along`, `cylindricalLaplacian`, `cylindricalVectorLaplacian`,
   `angularGenerator`, `LinearWaveResidual.transport/gradient/linearResidual`,
   `ExcludedErrors.total`, `angularAverage`. I did **not** verify
   `HarmonicFields.differentiate`, `angularDifferentiate`, `derivativeCoefficient_contDiffOn`,
   `along_field_slow`, `field_hasDerivAt_angle`, `convolution_apply`, `evaluate_conjugateReverse`,
   `along_congr`, `contDiffOn_along`, `AddMonoidAlgebra.coeff_mul_single_apply`, or any
   `CorrectionState` field semantics. A wrong `differentiate` upstream would make this file's
   `field_*` bridges vacuous and I would not have seen it.
3. **Mathlib lemma names not grepped against a library copy.** `intervalIntegral.integral_add`,
   `intervalIntegral.integral_finsetSum`, `Complex.reCLM.intervalIntegral_comp_comm`,
   `Finsupp.erase_same`, `Finset.sum_eq_single`, `notMem_tsupport_iff_eventuallyEq` etc. are
   assumed to have the statements their names suggest.
4. **The cone flag.** I report `in_cone` values from `INVENTORY.csv` as given. I did not rebuild
   the cone, and E1 argues the flag is over-approximate for at least three rows of this file.
5. **The mathematics beyond formula-matching.** I verified the operators are the standard
   cylindrical ones and that the grouping identities are algebraically exact. I did **not** and
   cannot check whether the *estimates* that consume `residualBlock` (in
   `PhysicalResidualJetBounds`, `HarmonicWaveInteraction`, `ActualCycleResidualBounds`) are
   strong enough for the headline — that is where the brief's warning about "estimate mass" bites,
   and it is outside this file.
6. **`ofBlock_regular` (1383), `coefficients_unique` (520), `angularMean_nonconstant` (545),
   `nonconstant_support` (567), `field_neg` (90), `waveResidualCoefficients_values` (1163),
   `extract_residual` (1192), `residualBlock_smooth/values/stage_band/extract/mean_zero`
   (1542–1593)** are `in_cone == False`. I read them anyway, but a defect there cannot reach a
   headline theorem, so I did not chase their consumers.
