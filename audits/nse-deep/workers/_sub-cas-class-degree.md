# Sub-audit: does per-cycle `p`/`C` growth make the "+1/10 per cycle" gain vacuous?

Scope: READ-ONLY source audit of `openai/NavierStokesAndEuler` @ `f9e8bc5`
(clone at `/home/gsm/.openclaw/workspace/repos/NSE`). No build was run (no Mathlib on disk).
All paths below are relative to the NSE repo root. Nothing in NSE was modified.

## 0. The one-line answer

**NOT vacuous.** The class degree `p` never reaches the exponent. It is spent entirely in the
*constant*, and the exponent price for disposing of it is a **flat `+1`**, charged once, with no
`p` and no stage index `J` in it. The load-bearing lemma is

```lean
-- NavierStokes/PhysicalGraphBounds.lean:804-807
/-- Arbitrary fixed powers of the slow scale can be absorbed with one
fixed power loss; the constant may depend on the slow power. -/
theorem slow_power_absorption (a : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    ChartScales.S n ^ a ≤ C * ChartScales.Q n ^ (-1 : ℝ) := by
```

`a` is an arbitrary real; the exponent cost is exactly `-1` for every `a`; only `C = C(a)` moves.

---

## A. Where `s.growth n x ^ p` goes

The class bound is
```lean
-- NavierStokes/WeightedClasses.lean:78-79
def majorant (s : StripData D) (w : ℕ → D → ℝ) (α C : ℝ) (p n : ℕ) (x : D) : ℝ :=
  C * s.epsilon n ^ α * s.growth n x ^ p * w n x
-- NavierStokes/WeightedClasses.lean:50-51
def StripData.growth (s : StripData D) (n : ℕ) (x : D) : ℝ :=
  s.slow n * max 1 (s.delta x)⁻¹
-- NavierStokes/WeightedClasses.lean:111-113
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ...
```
`growth ^ p` is split into its two factors and each is disposed of separately. **Both go into the
constant.** Four steps, in order:

### A.1 `(max 1 (delta x)⁻¹) ^ p` -> constant `K(p,c)`, exponent untouched

```lean
-- NavierStokes/PhysicalClassBounds.lean:113-121  (inside UniformClass.edge_absorbed, :98-122)
    _ ≤ C * s.epsilon n ^ α * s.growth n x ^ p * s.zeta x ^ c := ...
    _ = (C * s.epsilon n ^ α * s.slow n ^ p) *
        ((max 1 (s.delta x)⁻¹) ^ p * s.zeta x ^ c) := by
      rw [StripData.growth, mul_pow]
      ring
    _ ≤ (C * s.epsilon n ^ α * s.slow n ^ p) * K :=
      mul_le_mul_of_nonneg_left (hKx x hx) (mul_nonneg (mul_nonneg hC he) hs)
```
`K` comes from `hg.uniform hc p` (`PhysicalClassBounds.lean:106`), i.e.
```lean
-- NavierStokes/PhysicalClassBounds.lean:67-70
theorem FlatGeometry.uniform ... (hc : 0 < c) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ s.domain,
      (max 1 (s.delta x)⁻¹) ^ m * s.zeta x ^ c ≤ K
```
**`delta` is NOT bounded below on the region.** `delta L x = min 1 (min x (L - x))`
(`NavierStokes/WeightedRadialPrimitive.lean:32`) goes to `0` at both edges. What saves the step is
that the class weight is *Gaussian-flat* there:
```lean
-- NavierStokes/FlatCutoff.lean:26-27
def edge (c x : ℝ) : ℝ := if x ≤ 0 then 0 else Real.exp (-c / x ^ 2)
-- NavierStokes/WeightedRadialPrimitive.lean:33
def zeta (cL cR L x : ℝ) : ℝ := edge cL x * edge cR (L - x)
```
so `delta⁻¹ ^ m * zeta ^ c` is bounded for **every** fixed `m` (`flat_edge_uniform`,
`PhysicalClassBounds.lean:53-65`, docstring: "Exponential flatness absorbs any fixed inverse-edge
power"), by compactness of `Icc 0 L` in `WeightedRadialPrimitive.weight_uniform_bound`
(`WeightedRadialPrimitive.lean:206-215`). **Verdict: constant, not exponent. `K = K(p,c)` may grow
with the cycle; nothing else does.**

### A.2 `s.slow n ^ p` -> `S n ^ (q*p)`, still a band power, still not an exponent charge

```lean
-- NavierStokes/PhysicalClassBounds.lean:169, 179, 185-189 (UniformClass.chart_bound, :165-189)
    (hslow : ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q)
  refine ⟨A * K ^ p, mul_nonneg hA (pow_nonneg (zero_le_one.trans hK) _), q * p, ?_⟩
    _ ≤ A * s.epsilon n ^ α * (K * ChartScales.S n ^ q) ^ p := ...
    _ = _ := by rw [he, mul_pow, ← pow_mul]; ring
```
Same shape at `NavierStokes/LocalPhysicalCopyBounds.lean:533-554` (`LocalSourceBounds.chart_bound`,
the version on the live residual path) with `slow_le` at `:528-529`.
The `epsilon` power becomes the physical `Q` power exactly, with **no loss**:
`s.epsilon n ^ α = ChartScales.Q n ^ (h * α)` (`PhysicalClassBounds.lean:181-182`).

**Is `slow n` polynomial in the band index? YES, it is `max 1 n²`:**
```lean
-- NavierStokes/ChartScales.lean:28
def S (n : ℕ) : ℝ := (n : ℝ) ^ 2
-- NavierStokes/BaseContextAssembly.lean:31
noncomputable def slowScale (n : ℕ) : ℝ := max 1 (ChartScales.S n)
-- NavierStokes/ActualInitialization.lean:641-651   ("All stages use one moving strip ...")
noncomputable def geometry : SignedMeanGain.Geometry where
  ...
  epsilon := ChartScales.epsilon ActualPrimary.h
  slow := BaseContextAssembly.slowScale
-- NavierStokes/ActualMeanPhysicalData.lean:246-247  (so K = 1, q = 1)
theorem slowScale_le_S {n : ℕ} (hn : 1 ≤ n) :
    BaseContextAssembly.slowScale n ≤ ChartScales.S n := by
```
and `Q n = 2 ^ (-n)` (`PhysicalMeanJetBounds.lean:77-80`, `Q_eq_half_pow`). So the slow scale is
polynomial while the physical scale is exponential in `n`. That gap is the whole mechanism.

### A.3 THE DISPOSAL STEP: `S n ^ e` -> constant, at a flat exponent cost of `1`

```lean
-- NavierStokes/PhysicalGraphBounds.lean:822-837, 842-848 (stripped_class_physical_bound)
/-- A stripped coefficient class with arbitrary stage-dependent slow powers
has a fixed physical loss `graphLoss m + 1` on dyadic active supports. -/
theorem stripped_class_physical_bound ... (m : ℕ) (g d A : ℝ) (hA : 0 ≤ A) : ∃ C : ℝ, 0 ≤ C ∧ ...
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (physicalLift h n p)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ d) →
      ‖iteratedFDeriv ℝ m (F ∘ physicalLift h n) p‖ ≤
        C * q ^ (g - (graphLoss m + 1)) := by
  obtain ⟨C, hC, hbound⟩ := graphRestriction_jet_bound (E := E) (b := b) hh hh1 ha m
  obtain ⟨D, hD, hslow⟩ := slow_power_absorption d          -- <<< D = D(d) is the price
  refine ⟨C * A * D * 2 ^ |g - (graphLoss m + 1)|, by positivity, ?_⟩
  ...
    _ ≤ C * (A * ChartScales.Q n ^ g * (D * ChartScales.Q n ^ (-1 : ℝ))) *
        ChartScales.Q n ^ (-graphLoss m) := by
      apply hb.trans
      gcongr
      exact hslow n
```
The slow power `d` appears **only** inside the constant `D`. The conclusion's exponent is
`g - (graphLoss m + 1)`: `d`-free. `slow_power_absorption` itself rests on the proved
polynomial-beats-exponential fact
```lean
-- NavierStokes/ChartScales.lean:273-281
/-- Every fixed real power of the slow scale is dominated by every positive
power of the actual small-viscosity scale, provided `h>0`. -/
theorem slow_power_epsilon_tendsto_zero (h : ℝ) (hh : 0 < h) (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => S n ^ a * epsilon h n ^ b) atTop (𝓝 0)
```
(reduced to `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*a) (h*b*log 2)`).

### A.4 The residual path actually uses it, and drops `e` from the exponent

```lean
-- NavierStokes/ActualCycleResidualBounds.lean:926-928  (selected_residual_jet_bound, :915-954)
  obtain ⟨A, hA, e, hb⟩ := hf.bounds m
  obtain ⟨C, hC, hCbound⟩ := cartesianPull_jet_bound (b := b) hh.le hh1.le ha Δ m
    (gain - β * m) (residualDegree h) e A hA
-- ... and the exponent identity that closes the proof, :951-954
  have hexp : gain - β * m - PhysicalMeanJetBounds.loss (residualDegree h) m = gain - physicalLoss h β m := by
    unfold physicalLoss
    ring
  simpa only [hexp] using he
```
`e` is the class degree of *this* cycle (from `NativeBounds.bounds`, itself fed by the `p` of
`MemClass`). It is passed as a parameter of the constant-producing lemma
```lean
-- NavierStokes/PhysicalResidualJetBounds.lean:275-284 (cartesianPull_jet_bound)
theorem cartesianPull_jet_bound ... (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ... (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (polarGraph a h j n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (cartesianPull a h j n d degree F) w‖ ≤
        C * q ^ (gain - PhysicalMeanJetBounds.loss degree m)
```
— note `C` is existentially quantified **after** `e`, and `e` does not occur in the conclusion's
exponent. `loss` charges the `+1` once:
```lean
-- NavierStokes/PhysicalMeanJetBounds.lean:132-133
noncomputable def loss (degree : ℝ) (m : ℕ) : ℝ :=
  PhysicalGraphBounds.graphLoss m + 1 + degree
-- NavierStokes/PhysicalResidualJetBounds.lean:740-743
/-- The loss contains the actual physical residual degree, graph derivative
loss, one polynomial-in-band absorption, and the fixed phase loss. -/
noncomputable def physicalLoss (h β : ℝ) (m : ℕ) : ℝ :=
  PhysicalMeanJetBounds.loss (residualDegree h) m + β * m
```

**ANSWER A. `s.growth n x ^ p` is absorbed into the JetRate constant, in three constant-only steps
(edge power -> `K(p,c)`; slow power -> `K^p`; band power -> `D(e)`), and the exponent is charged a
single fixed `+1` that contains no `p`. `delta` is not bounded below on the region; the
exponentially flat weight `zeta = exp(-cL/x²)·exp(-cR/(L-x)²)` is what absorbs the inverse-edge
power. `slow n = max 1 n²` is polynomial in the band index (`K = 1, q = 1`).**

---

## B. Is the charged loss `J`-independent, and is the slack real?

### B.1 Definitions: no `J`, no `p`

```lean
-- NavierStokes/ActualCycleResidualBounds.lean:1145-1148
noncomputable def fixedLoss (m : ℕ) : ℝ := physicalLoss ActualPrimary.h (2 * ActualPrimary.h) m

theorem fixedLoss_eq_ledger (m : ℕ) :
    fixedLoss m = ActualIterationLedger.residualLoss ActualPrimary.h (2 * ActualPrimary.h) m := rfl
-- NavierStokes/ActualIterationLedger.lean:284-287
/-- The full-phase derivative cost is a fixed parameter `beta`, not a
stage-dependent loss. -/
noncomputable def residualLoss (h beta : ℝ) (m : ℕ) : ℝ :=
  PhysicalGraphBounds.graphLoss m + 1 + (2 * CoordinateAlgebra.A h + 1 / 2) + beta * m
```
Unfolded: `fixedLoss m = m(m+2) + 1 + (2·A h + 1/2) + 2h·m`. Arguments: `m` only. `p`/`e` absent,
`J`/`σ` absent. `beta = 2h` is fixed, not `σ`-dependent — see `native_residual`, whose loss slot is
the literal `fun m => (2 * ActualPrimary.h) * m`:
```lean
-- NavierStokes/ActualCycleResidualBounds.lean:843-849
/-- Every term of the literal state residual has the required native gain.
The phase loss is fixed once, independently of the cycle index. -/
theorem native_residual (hN : ...) (hbase : ...) :
    NativeBounds 4 (HarmonicResidual.liftDomain ActualInitialization.geometry.strip.domain)
      (ActualPrimary.h * (1/2 + σ)) (fun m => (2 * ActualPrimary.h) * m)
      (fun (_ : Unit) => LiftedMeanResidual.fullResidual (ActualPrimary.commonContext B) x.state)
```
and the transfer structure itself states the discipline:
```lean
-- NavierStokes/PhysicalResidualJetBounds.lean:373-380
/-- Constants are chosen before the label and band. `loss` is allowed to
depend on the derivative order; it never depends on the correction stage. -/
structure NativeBounds ... (N : ℕ) (U : Set D) (gain : ℝ) (loss : ℕ → ℝ) (f : ι → ℕ → D → E) : Prop where
  ...
  bounds : ∀ m, ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n, N ≤ n → ∀ x ∈ U, ∀ j ≤ m,
    ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ A * ChartScales.Q n ^ (gain - loss m) * ChartScales.S n ^ p
```
`loss : ℕ → ℝ` — **the type forbids a stage argument.** `A` and `p` are per-`m` existentials, so
they may (and do) change from cycle to cycle.

The consumer statement:
```lean
-- NavierStokes/ActualCycleResidualBounds.lean:1187-1206
/-- The finite-residual input of the mixed diagonal assembly. `J` is the
number of completed correction cycles ... The derivative loss is fixed before `J` is chosen. -/
theorem finite_residual_rates ... :
    ∀ J m, DiagonalResidual.JetRate GlobalBaseError.originPast (physicalQ ActualPrimary.h)
      (fun w => navierStokesResidual (u J) (P J) w.1 w.2) m
      (ActualIterationLedger.gain ActualPrimary.h J - fixedLoss m) := by
  intro J m
  have he := (H J).residual_jetRate hGeom hN (actual_iterate_base_error p J) (d J) m
  have hgain := ActualIterationLedger.gain_le_residualWave ActualPrimary.outgoing.data.h_pos.le J
  ...
  exact he.weaken origin_positive_small (sub_le_sub_right hgain _)
```
Rate `= h·J/10 - fixedLoss m` -> `+∞` in `J` for each fixed `m`
(`gain_tendsto_atTop`, `ActualIterationLedger.lean:107-108`). **The `+1/10` per cycle survives the
conversion intact.**

### B.2 The slack: real, exactly `7h/10`, and used only for the gain/accuracy bookkeeping

```lean
-- NavierStokes/ActualIterationLedger.lean:29, 36, 231, 252-256
noncomputable def gain (h : ℝ) (j : ℕ) : ℝ := h * (j : ℝ) / 10
theorem sigma_formula (J : ℕ) : sigma J = 1 / 5 + (J : ℝ) / 10 := rfl
theorem residualWave_formula (J : ℕ) : residualWave J = (J : ℝ) / 10 + 7 / 10
theorem residual_physical_gap (h : ℝ) (J : ℕ) :
    h * residualWave J = gain h J + 7 * h / 10
```
The invariant delivers exponent `h * (1/2 + σ J) = h * (7/10 + J/10) = h * residualWave J`
(`Invariant.residual_jetRate`, `ActualCycleResidualBounds.lean:1158-1163`); the ledger claims only
`gain h J = h·J/10`. Slack `= 7h/10`, **fixed, `J`-independent**, and it is used exactly once, at
`ActualCycleResidualBounds.lean:1203-1206`, via `gain_le_residualWave` + `JetRate.weaken`
(`DiagonalResidual.lean:41-48`).

**Is a fixed exponent slack enough to swallow `slow n ^ p`?** For each fixed `p`: yes, and much less
than a fixed slack is needed — `n^{2p} ≤ C(p) · Q_n^{-δ}` holds for **every** `δ > 0`
(`ChartScales.slow_power_epsilon_tendsto_zero`, `ChartScales.lean:275`). The formalization does not
even take a small `δ`: it spends a full `1` (`slow_power_absorption`, `δ = 1`), coarser than needed,
and pays it inside `fixedLoss`, **not** out of the `7h/10` slack. So the two are independent:
the `7h/10` slack is spare margin between accuracy and claimed gain; the `+1` is a one-off
`J`-free exponent charge. **No `J`-uniform `p` is required anywhere** (see C).

Caveat worth naming loudly: the flat `+1` charge is only enough because `slow` is **sub-exponential**
in `n`. Had the strip's `slow` been an exponential band factor (e.g. `Lambda ^ nativeIndex h n`, cf.
`ChartScales.lean:33-34`), `slow_power_absorption` would be false and `p` *would* leak into the
exponent, making the claim `p`- hence `J`-dependent. The live geometry uses
`slow := BaseContextAssembly.slowScale = max 1 n²` (`ActualInitialization.lean:651`,
`BaseContextAssembly.lean:31`), so the hypothesis holds. This is the single fact the whole
non-vacuity rests on, and it is proved.

---

## C. Every place a bound must be uniform in the stage index `J` (live path)

| # | Site | What must be `J`-uniform | Proved? |
|---|------|--------------------------|---------|
| 1 | `NavierStokes/PhysicalResidualJetBounds.lean:377` `NativeBounds` field `loss : ℕ → ℝ` | the loss function (type-level: no stage argument) | yes, by type; instantiated `fun m => (2*h)*m` at `ActualCycleResidualBounds.lean:848` |
| 2 | `NavierStokes/ActualCycleResidualBounds.lean:1145` `fixedLoss : ℕ → ℝ` | one loss for all `J` | yes (definition has no `J`) |
| 3 | `NavierStokes/CutStageEstimates.lean:199-203` `RawStageBounds q A g L C p S`: `∀ j, 1 ≤ j → ∀ m x, ... ≤ C j m * (1+|log q x|)^(p j m) * q x ^ (g j - L m)` | a single `L : ℕ → ℝ` for all stages `j` (constants `C j m`, log powers `p j m` may vary with `j`) | yes: `ActualPhysicalStageBounds.lean:449-472` supplies `PhysicalStageBounds.potentialLoss h h 0` / `directLoss h 0` / `pressureLoss h (2*A h) 0` (all `J`-free, `PhysicalStageBounds.lean:296-305`) with `CA CB CP : ℕ → ℕ → ℝ` |
| 4 | `NavierStokes/DiagonalJetBounds.lean:196-200` `CutStageBounds`: `≤ (1/2)^j * q x ^ (g j - L m)` | per-stage constant must be beaten by `(1/2)^j`, with one `L` | yes: `CutStageEstimates.exists_diagonal_cut_bounds:349-368`; the cutoff schedule `a` is chosen **after** the per-stage constants via `DiagonalScale.exists_diagonal_scales K (cutLog p) g hg lower` (`:364`). Price: `g j / 2` and `cutLoss L m = finiteBound L m + m` (`:192`) |
| 5 | `NavierStokes/MixedCandidateAssembly.lean:39-47` `StageEstimates`: `potentialLoss directLoss pressureLoss backgroundLoss residualLoss : ℕ → ℝ` vs `potentialConstant … : ℕ → ℕ → ℝ` | losses uniform in `J`; constants explicitly **not** | yes, by type; instantiated `ActualStageEstimates.lean:369-387` |
| 6 | `NavierStokes/MixedDiagonalResidual.lean:180-185` `hbg`/`hres` hypotheses `∀ J m, JetRate … (g J - Lres m)` | `Lres` uniform in `J`; `g J → ∞` | yes; discharged by `finite_residual_rates` (`ActualStageEstimates.lean:399`) |
| 7 | `NavierStokes/ActualInitialization.lean:641-651` one `geometry` (hence one `epsilon`, `slow`, `delta`, `zeta`) for all stages; preserved by the step: `CorrectionAnalyticStep.lean:266 -> :301` (`G` in, `G` out, `σ -> σ+1/10`) | the strip data must not drift with `J` | yes |
| 8 | `NavierStokes/WeightedClasses.lean:111` `MemClass.bounds` `∃ C, ∃ p`; `:125-127` `StageClasses` | **nothing** — explicitly non-uniform: "Stage constants are deliberately not uniform in the stage index." | n/a (design) |

I found **no** live-path site that needs a `J`-uniform constant `C` or a `J`-uniform degree `p`.
The mechanism that makes per-`J` constants harmless is row 4: the diagonal cutoff schedule is
selected after the constants, at the cost of halving the gain (`g j / 2`) plus an `m`-only loss —
and `g j / 2 = h·j/20 → ∞` still.

---

## D. VERDICT (loud)

**The "+1/10 per cycle" gain is NOT rendered vacuous by per-cycle `p`/`C` growth. The claim is
substantive as formalized.** What settles it, exactly:

1. **`p` is charged to the CONSTANT, not the exponent.** `slow_power_absorption`
   (`PhysicalGraphBounds.lean:806-820`): `S n ^ a ≤ C(a) · Q n ^ (-1)` for *every real* `a`. Used in
   `stripped_class_physical_bound` (`:824-861`), whose conclusion exponent is `g - (graphLoss m + 1)`
   — no `a`. The edge factor `(max 1 delta⁻¹)^p` is likewise absorbed into `K(p,c)` by exponential
   flatness of `zeta` (`PhysicalClassBounds.lean:55-74`, `FlatCutoff.lean:26-27`).
2. **The exponent loss is `J`-free by type and by definition.** `NativeBounds`'s
   `loss : ℕ → ℝ` (`PhysicalResidualJetBounds.lean:377`), `RawStageBounds`'s `L : ℕ → ℝ`
   (`CutStageEstimates.lean:199`), `StageEstimates`'s five loss fields
   (`MixedCandidateAssembly.lean:39-58`), and the concrete
   `fixedLoss m = m(m+2) + 1 + (2·A h + 1/2) + 2h·m` (`ActualCycleResidualBounds.lean:1145`,
   `ActualIterationLedger.lean:286-287`) all lack a stage argument, and `selected_residual_jet_bound`
   discharges the `S n ^ e` factor into `C` while keeping the exponent
   `gain - physicalLoss h β m` (`ActualCycleResidualBounds.lean:926-954`).
3. **Per-`J` constants are absorbed by a schedule chosen after them.**
   `CutStageEstimates.exists_diagonal_cut_bounds:349-368` picks the cutoff scales `a j` from
   `K j m`, converting arbitrary stage constants into the summable `(1/2)^j` at the price of
   `g j / 2` and an `m`-only `cutLoss`.

Net: for each fixed derivative order `m`, the residual jet rate is
`h·J/10 - fixedLoss m → +∞` as `J → ∞` (`finite_residual_rates`,
`ActualCycleResidualBounds.lean:1190-1206`), with a fresh constant per `(J,m)` — which is exactly
what the diagonal argument consumes.

**The single fact the non-vacuity rests on** (and which a reader should re-check before trusting
the ledger): the strip's slow scale is polynomial in the band index,
`slow = max 1 n²` (`ActualInitialization.lean:651` + `BaseContextAssembly.lean:31` +
`ChartScales.lean:28`, with `slowScale_le_S` at `ActualMeanPhysicalData.lean:246`), while
`Q n = 2^{-n}` (`PhysicalMeanJetBounds.lean:77`). Polynomial-vs-exponential is what makes a flat
`+1` enough for arbitrary `p`. It is proved: `ChartScales.slow_power_epsilon_tendsto_zero`
(`ChartScales.lean:275-281`).

**Residual risk of this sub-audit (stated plainly):** source-only, no `lake build`, so I certify the
*statements and proof scripts as written*, not their kernel-checked correctness. The one worry that
source reading cannot fully close is whether some intermediate class on the live residual path is
instantiated with a strip whose `slow` is *not* `slowScale` (which would break step A.3's premise
`slow n ≤ K · S n ^ q`). Every `slow :=` occurrence I found is either `s.slow` (inherited, so the
strip is passed through unchanged: `ActualReferenceRebase.lean:187`, `LocalSignedRequest.lean:43`,
`CorrectionInitialization.lean:1596`, `ActualWaveRegularity.lean:33`,
`HarmonicWaveInteraction.lean:30`, `CartesianCopySource.lean:40`,
`CorrectionInitializationNoOptions.lean:1607`) or the two live roots
`BaseContextAssembly.slowScale` (`ActualInitialization.lean:651`, `ActualCycleGeometry.lean:40`).
No exponential `slow` instantiation exists in `NavierStokes/`.
