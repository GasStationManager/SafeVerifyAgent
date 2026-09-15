# Task B — the `SameCarrier` recursion invariant of the correction iteration

## Scope

Source-level audit (no `lake build`; no Mathlib on disk) of the representation invariant of the
correction iteration and of the `SameCarrier` hypothesis it is conditional on.
Read in full: `NavierStokes/CorrectionStep.lean:6780-7000`, `:2018-2065`, `:4836-4875`, `:5040-5115`;
`NavierStokes/ActualCandidateConstruction.lean:1-180`; `NavierStokes/ActualCycleParameters.lean:318-518`;
`NavierStokes/ActualInitialization.lean:27-60,130-235,830-850`;
`NavierStokes/CycleStateCoherence.lean:595-660`; `NavierStokes/CorrectionState.lean:160-210`;
`NavierStokes/LabelSumBounds.lean:810-840`; `NavierStokes/HarmonicWaveInteraction.lean:428-455`;
`NavierStokes/CorrectionInitialization.lean:113-130,310-320,5179-5305`;
`NavierStokes/ActualSignedStageControls.lean:97-109`; `NavierStokes/ActualCandidateAssembly.lean:1059-1100`.
Cone status read from `audits/nse-deep/CONE.csv` (columns `file,line,kind,name,in_cone,in_import_closure`;
52516 rows, 38369 in cone).

**Headline answer: `hc` IS discharged unconditionally.** The `∀ n l, SameCarrier …` hypothesis of
`CycleState.iterate_representation` is supplied at `ActualCandidateConstruction.lean:85` by the closed
term `cycle_signed_carrier B N0`, and the enclosing theorem `cycle_representation (B N0 j : ℕ)`
(`:80`) has **no hypotheses at all**. No re-assumption, no `hc`-shaped side condition anywhere on the
path to `ActualCandidateAssembly.physicalData`. The discharge is uniform in `n` (induction over `n`).

## Per-declaration findings

### 1. `NavierStokes.CorrectionStep.SameCarrier` — `CorrectionStep.lean:2027` — [OK]

```lean
structure SameCarrier (a b : HarmonicBlock D) : Prop where
  frequency : b.frequency = a.frequency
  phase : b.phase = a.phase
  angular : b.angularFrequency = a.angularFrequency
```
`HarmonicBlock` (`CorrectionState.lean:170-175`) has fields
`velocity : ℕ → Fin 3 → HarmonicFields.Coefficients D`, `pressure : ℕ → HarmonicFields.Coefficients D`,
`frequency : ℕ → ℝ`, `phase : ℕ → D → ℝ`, `angularFrequency : ℕ → ℤ`.

So `SameCarrier a b` is a triple of **function equalities** on the three carrier fields — a genuine
`Prop` with content (for two arbitrary blocks it is generally false and not `rfl`-able: it equates
functions `ℕ → ℝ`, `ℕ → D → ℝ`, `ℕ → ℤ`). It says nothing about `velocity`/`pressure`; it is exactly
"same phase carrier / same angular mode", which is precisely the condition needed for coefficient
addition to be field addition. **Statement matches its name.** No junk-value or empty-domain issue in
the definition itself. NOTE: a byte-identical duplicate lives at `LabelSumBounds.lean:813` (same three
fields), and both are in cone — a name clash, not a soundness issue.

### 2. `NavierStokes.CorrectionStep.addBlock` — `CorrectionStep.lean:2023` — [OK, but silent-carrier-drop by design]

```lean
/-- Add coefficient families on the same fixed label carrier. -/
noncomputable def addBlock (a b : HarmonicBlock D) : HarmonicBlock D :=
  { a with velocity := fun n i => a.velocity n i + b.velocity n i
           pressure := fun n => a.pressure n + b.pressure n }
```
`{ a with … }`: `frequency`, `phase`, `angularFrequency` are copied **from `a` only**. `b`'s carrier is
silently discarded. (`LabelSumBounds.lean:818` is the same; `HarmonicWaveInteraction.lean:431-437`
spells the same thing out field-by-field.)

`HarmonicBlock.oscillation` (`CorrectionState.lean:179-181`):
```lean
noncomputable def oscillation (b : HarmonicBlock D) : Oscillation D :=
  fun n p i => (HarmonicFields.field (b.velocity n i) (b.frequency n)
    (b.phase n) (b.angularFrequency n) p).re
```

### 3. `NavierStokes.CorrectionStep.addBlock_oscillation` — `CorrectionStep.lean:2033` — [OK]

```lean
theorem addBlock_oscillation (a b : HarmonicBlock D) (h : SameCarrier a b) :
    (addBlock a b).oscillation = a.oscillation + b.oscillation := by
  funext n x i
  simp only [addBlock, HarmonicBlock.oscillation, HarmonicFields.field, HarmonicFields.evaluate_add,
    Complex.add_re, Pi.add_apply, h.frequency, h.phase, h.angular]
```
The hypothesis is **used**: `h.frequency, h.phase, h.angular` are the rewrite rules that turn `a`'s
carrier (inherited by `addBlock`) into `b`'s carrier so `evaluate_add` applies. Companion
`addBlock_pressure` at `:2040`, same shape.

### 4. `NavierStokes.CorrectionStep.CycleParameters.finalBlock_oscillation` — `CorrectionStep.lean:6838` — [OK]

```lean
theorem finalBlock_oscillation
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) (l : ι) :
    (p.finalBlock v c u l).oscillation = (v.blocks l).oscillation +
      (p.particularBlock v c u l).oscillation + (p.signedBlock v c u l).oscillation := by
  have hs : SameCarrier (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l) :=
    ⟨(hc l).frequency,(hc l).phase,(hc l).angular⟩
  rw [finalBlock, addBlock_oscillation _ _ hs, addBlock_oscillation _ _ (p.particular_carrier v c u l)]
```
with `finalBlock` (`:5087`):
`addBlock (addBlock (v.blocks l) (p.particularBlock v c u l)) (p.signedBlock v c u l)`.
The `⟨(hc l).frequency, …⟩` step is the defeq transport `(addBlock x y).frequency ≡ x.frequency`
supplied by `{ a with … }`. The particular leg needs no hypothesis:
`particular_carrier` (`:6816`) is `⟨rfl,rfl,rfl⟩`.

**What breaks when `SameCarrier` fails: WRONG VALUE, not vacuity.** Direct source evidence at
`HarmonicWaveInteraction.lean:440-445`, which states the *unconditional* version:
```lean
theorem addBlock_oscillation (a b : CorrectionState.HarmonicBlock D) (n : ℕ)
    (p : D × ℝ) (i : Fin 3) :
    (addBlock a b).oscillation n p i = a.oscillation n p i +
      (withCarrier a b).oscillation n p i := by
```
i.e. without `SameCarrier` the sum block's field is `a.oscillation + (b's coefficients evaluated on
A's carrier)` — `b`'s own wave is *substituted*, not dropped and not made meaningless.
Consequently: `addBlock_oscillation` (`:2033`) would be **plainly false** without `hc`, and
`CycleRepresentation.velocity` (`:6800`) — an equation between actual state fields and the sum of the
stored blocks — would be **unprovable/false**, not vacuously true. The hypothesis is a genuine
necessary side condition, honestly placed. It is *not* a vacuity device.

### 5. `NavierStokes.CorrectionStep.CycleParameters.next_representation` — `CorrectionStep.lean:6871` — [OK]

Takes `hrep : CycleRepresentation v u axis` and the same
`hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)`; builds the 4 fields of
`CycleRepresentation` by `rw`/`simp only` with `finalBlock_oscillation`, `finalBlock_pressure`,
`nextCoefficients_gaussian_field` (`:6854`, also `hc`-conditional) and `Finset.sum_add_distrib`.
`hc` is used in three of the four fields; the alias-error field (`:6891-6896`) is closed by
`simp only [...] ; ring` with no `hc`.

### 6. `NavierStokes.CorrectionStep.CycleState.iterate_representation` — `CorrectionStep.lean:6963` — [OK]

```lean
theorem iterate_representation (p : ℕ → CycleParameters ι) (c : Context CyclePoint) (seed : CycleState ι)
    (hseed : CycleRepresentation seed.coefficients seed.state seed.axisymmetricAlias)
    (hc : ∀ n l, let v := iterate p c seed n
      SameCarrier (v.coefficients.blocks l) ((p n).signedBlock v.coefficients c v.state l)) :
    ∀ n, let v := iterate p c seed n
      CycleRepresentation v.coefficients v.state v.axisymmetricAlias := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    exact (p n).next_representation (iterate p c seed n).coefficients c (iterate p c seed n).state ih (hc n)
```
Mechanism: plain `Nat` structural induction (motive = the `let`-bound `CycleRepresentation` at `n`),
base = `hseed`, step = `next_representation … ih (hc n)`. `iterate` (`:6952-6955`) is structural
recursion on `ℕ` (`iterate_zero`/`iterate_succ` are `rfl`, `:6958`/`:6961` — so it compiles to
`Nat.rec`, not `WellFounded.fix`). Nothing hidden.

### 7. `NavierStokes.ActualCandidateConstruction.cycle_representation` — `ActualCandidateConstruction.lean:80` — [OK] — THE DISCHARGE SITE

```lean
theorem cycle_representation (B N0 j : ℕ) :
    CycleRepresentation (cycle B N0 j).coefficients (cycle B N0 j).state
      (cycle B N0 j).axisymmetricAlias :=
  CycleState.iterate_representation (parameterSequence B N0) (commonContext B)
    (ActualInitialization.initialCycleState B N0) (ActualInitialization.initialCycleState_represents B N0)
    (cycle_signed_carrier B N0) j
```
**The term passed as `hc` is `(cycle_signed_carrier B N0)`.** The enclosing theorem takes only
`(B N0 j : ℕ)` — no `SameCarrier` hypothesis, no invariant bundle, no `CycleAnalyticInvariant`.
`hseed` is `initialCycleState_represents B N0` (`ActualInitialization.lean:208`), also hypothesis-free.
Typechecks up to defeq because `cycle B N0 j` (`:40-42`) is literally
`CycleState.iterate (parameterSequence B N0) (commonContext B) (initialCycleState B N0) j`
and `parameterSequence B N0 = fun _ => parameters B N0` (`:37-38`),
`parameters B N0 = ActualCycleParameters.fixedParameters B N0` (`:34-35`).

### 8. `NavierStokes.ActualCandidateConstruction.cycle_signed_carrier` — `ActualCandidateConstruction.lean:74` — [OK]

```lean
theorem cycle_signed_carrier (B N0 j : ℕ) (l : Index B N0) :
    SameCarrier ((cycle B N0 j).coefficients.blocks l)
      ((parameters B N0).signedBlock (cycle B N0 j).coefficients (commonContext B)
        (cycle B N0 j).state l) :=
  ActualCycleParameters.fixedParameters_signed_carrier _ _ l (cycle_carrier B N0 j l)
```
No hypotheses. Reduces the problem to "block carrier = the *fixed initial* tangent carrier".

### 9. `NavierStokes.ActualCandidateConstruction.cycle_carrier` — `ActualCandidateConstruction.lean:62` — [OK] — the induction

```lean
theorem cycle_carrier (B N0 j : ℕ) (l : Index B N0) :
    SameCarrier ((cycle B N0 j).coefficients.blocks l) (ActualInitialization.tangentBlock l) := by
  induction j with
  | zero => exact ActualInitialization.primary_tangent_carrier l
  | succ j ih => exact ⟨ih.frequency, ih.phase, ih.angular⟩
```
* Motive: `fun j => SameCarrier ((cycle B N0 j).coefficients.blocks l) (tangentBlock l)`, i.e. "at
  cycle `j`, label `l`'s stored block still carries the *initial* frequency/phase/angular mode".
* Base `j = 0`: `(cycle B N0 0).coefficients = ActualInitialization.coefficients B N0` whose
  `blocks := primaryBlock` (`ActualInitialization.lean:130-135`), and
  `primary_tangent_carrier` (`ActualInitialization.lean:843-844`) is
  `SameCarrier (primaryBlock l) (tangentBlock l) := ⟨rfl, rfl, rfl⟩`
  (both blocks are built from the same `primaryPiece l` with the same `phase l`/`angularMode l`,
  `:40-44`), so this is a defeq leaf.
* Step: `⟨ih.frequency, ih.phase, ih.angular⟩` — a pure defeq transport. `(cycle B N0 (j+1)).coefficients
  = nextCoefficients …` whose `blocks := p.finalBlock …` = two nested `addBlock`s, and `addBlock` copies
  the carrier fields from its first argument, so
  `((cycle B N0 (j+1)).coefficients.blocks l).frequency ≡ ((cycle B N0 j).coefficients.blocks l).frequency`
  by unfolding only (`cycle_succ` is `rfl`, `:47-48`). CLOSED LEAF: `Nat.rec` + `rfl`.

**So the invariant is definitionally preserved: the iteration never touches the carrier fields.** That
is not a defect — it is why the invariant is provable at all — but it means `cycle_carrier` carries no
analytic content, and the *entire* `SameCarrier` chain is `rfl`/defeq plus one `Nat.rec`.

### 10. `NavierStokes.ActualCycleParameters.fixedParameters_signed_carrier` — `ActualCycleParameters.lean:499` — [OK]

```lean
theorem fixedParameters_signed_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    SameCarrier (x.coefficients.blocks l)
      ((fixedParameters B N0).signedBlock x.coefficients c x.state l) := by
  have hs := signed_tangent_carrier l (fixedParameters B N0).strip
    ((fixedParameters B N0).signedRequest x.coefficients c x.state)
  exact ⟨hs.frequency.trans H.frequency, hs.phase.trans H.phase, hs.angular.trans H.angular⟩
```
Its only hypothesis `H` is exactly what `cycle_carrier` provides. Note it is **uniform in `c` and in
`x`** — no restriction to `n = 0`, to a column, or to a finite prefix.

### 11. `NavierStokes.ActualCycleParameters.signed_tangent_carrier` / `signed_primary_carrier` — `:367` / `:351` — [OK]

`:351-365` proves `SameCarrier (primaryBlock l) ((ActualSignedStageControls.parameters l).exactBlock s request)`
from three `rfl` lemmas:
```lean
theorem signed_frequency … : (p.exactBlock s request).frequency = p.base.frequency := rfl      -- :327
theorem signed_phase     … : (p.exactBlock s request).phase = fun n z => p.base.phase n (z, 0) := rfl -- :332
theorem signed_angular   … : (p.exactBlock s request).angularFrequency = p.angularFrequency := rfl    -- :337
```
plus `primaryPiece_frequency/phase/angular` (`:339-349`, all `rfl`). The chain closes because the
signed stage's base literally *is* the primary chart data:
`ActualSignedStageControls.parameters l` has `base := ActualPrimary.chartCoefficients l.2 l.1`
(`ActualSignedStageControls.lean:97-98`), and
`ActualPrimary.piece U j L` has `coefficients := chartCoefficients j L`
(`CorrectionInitialization.lean:5298-5303`), with
`primaryPiece l := ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1`
(`ActualInitialization.lean:31-32`). `:367-375` transports this to `tangentBlock` via
`primary_tangent_carrier`. Verdict: the "same carrier" fact is true **by construction of the signed
parameters**, i.e. the signed correction was defined to reuse the primary phase/frequency/angular mode.
Legitimate, and honestly labelled ("The signed update uses the initialized primary carrier", `:322`).

### 12. `NavierStokes.CycleStateCoherence.iterate_block_fields` — `CycleStateCoherence.lean:601` — [UNCLEAR / mislabelled in the brief]

`:609-610` is **not** a per-`j` discharge of `hc`; it is a second *consumer* with the same shape:
```lean
    (hc : ∀ j l, let x := CycleState.iterate p c seed j
      SameCarrier (x.coefficients.blocks l) ((p j).signedBlock x.coefficients c x.state l)) :
```
closed by the same `Nat.rec` (`:617-619`, `| zero => exact Hseed`, `| succ j ih => … block_fields_next (HW j) (hc j) l (ih l)`).
CONE: `in_cone=False`, `in_import_closure=True` — this consumer is **not** used by the headline
theorems, so it is dead weight for the audit.

### 13. downstream consumer `NavierStokes.ActualCandidateAssembly.physicalData` — `ActualCandidateAssembly.lean:1079-1088` — [OK]

The only use of `cycle_representation` in the whole repo (`grep -rn cycle_representation` gives exactly
two hits: the declaration and this call site) is
```lean
  ActualPhysicalPrefixFields.physicalFields_all (stageRealizations B N0 hN) (exteriorStages B N0 hN)
    (ActualCandidateConstruction.twice_residual_scale B N0).le
    (stages_smooth B N0 hN).1 (stages_smooth B N0 hN).2.1 (stages_smooth B N0 hN).2.2
    (ActualCandidateConstruction.cycle_representation B N0)
```
inside `physicalData (B N0) (hN : geometricThreshold ≤ N0)`, which feeds `estimates` (`:1090`) and
`endpoints` (`:1100`). The only extra hypothesis introduced on this path is `hN` (a numeric threshold),
**not** a carrier condition.

## Verdict on the discharge

1. **`hc` is closed unconditionally: YES.** Chain, every step hypothesis-free except where the next
   step supplies the hypothesis:
   `cycle_representation` (ACC:80, no hyps) → `hc := cycle_signed_carrier B N0` (ACC:74, no hyps) →
   `fixedParameters_signed_carrier` (ACP:499, needs `H`) → `cycle_carrier B N0 j l` (ACC:62, no hyps) →
   `Nat.rec`: base `primary_tangent_carrier = ⟨rfl,rfl,rfl⟩` (AI:843), step `⟨ih.frequency, ih.phase, ih.angular⟩`
   (defeq through `addBlock`'s `{ a with … }`), and the signed leg
   `signed_tangent_carrier`/`signed_primary_carrier` (ACP:367/351) built from three `rfl`s (ACP:327/332/337).
2. **Nothing is re-assumed.** I looked specifically for an enclosing theorem that reintroduces the
   carrier property. There *are* such theorems in the repo — `ActualCycleParameters.invariant_signed_carrier`
   (`:398`), `invariant_fixedParameters_signed_carrier` (`:508`), `invariant_parameters_eq_fixed` (`:488`),
   all taking a `CycleAnalyticInvariant … x` bundle whose `.carrier` field re-supplies it, used by
   `ActualCyclePreservation.lean:640,698` and `ActualCycleAssembly.lean:1029` — but the path used by
   `cycle_representation` does **not** go through them. It uses the non-`invariant_` version with the
   inductively proved `cycle_carrier`. No loud escalation here.
3. **Uniform in `n`: YES.** `cycle_carrier`/`cycle_signed_carrier` are proved for all `j : ℕ` by
   structural induction; `fixedParameters_signed_carrier` is stated for an arbitrary state `x` and
   context `c`. There is no `n = 0`, no "primary column", no finite prefix restriction anywhere in the
   chain. (The parameter sequence *is* constant — `parameterSequence B N0 = fun _ => parameters B N0` —
   which is what makes the uniform statement cheap, but the statement is still uniform.)
4. **`SameCarrier` is real content but the discharge is definitional.** Honest, not vacuous, and the
   failure mode it guards against is a *wrong value* (carrier substitution, see
   `HarmonicWaveInteraction.lean:440`), not vacuity. `iterate_representation` being stated
   conditionally is correct engineering, not a hole.
5. **Cone status:** `iterate_representation` (CS:6963) `in_cone=True`; `next_representation` (CS:6871)
   True; `finalBlock_oscillation` (CS:6838) True; `finalBlock_pressure` (CS:6846) True;
   `nextCoefficients_gaussian_field` (CS:6854) True; `addBlock`/`addBlock_oscillation`/`SameCarrier`
   (CS:2023/2033/2027) True; `CycleRepresentation` (CS:6798) True; discharge site
   `cycle_representation` (ACC:80) True; `cycle_signed_carrier` (ACC:74) True; `cycle_carrier` (ACC:62)
   True; `fixedParameters_signed_carrier` (ACP:499) True; `signed_tangent_carrier` (ACP:367) True;
   `signed_primary_carrier` (ACP:351) True; `primary_tangent_carrier` (AI:843) True;
   `parameters_eq_fixed` (ACP:478) True. Only `CycleStateCoherence.iterate_block_fields` (:601) is
   `in_cone=False`.

Verdict counts over the 13 rows above: **OK 11, UNCLEAR 1 (`iterate_block_fields`, out of cone),
KERNEL-RISK 0, SUSPICIOUS 0**, plus one flagged-but-benign design note (silent carrier drop in
`addBlock`, item 2) and one vacuity escalation about the `∀ l` quantifier (below).

## Escalations

* **E1 (to whoever owns vacuity / label nonemptiness) — the `∀ l : Index B N0` quantifier.**
  `hc` and `cycle_carrier` quantify over `l : ActualInitialization.Index B N0 = ActualPrimary.Label B N0 × Fin 2`
  (`ActualInitialization.lean:27`, `CorrectionInitialization.lean:3931`). If that type were empty, all
  three carrier theorems would be *vacuously* true. That does NOT by itself make
  `CycleRepresentation` vacuous — its fields are equations `u.oscillation n x i = ∑ l ∈ v.labels n, …`
  (CS:6800-6805), which for an empty `labels n` assert `u.oscillation = 0`, i.e. a *stronger*, degenerate
  claim (no oscillation at all). Worth checking separately: is `activeLabels standardRegion B N0 n`
  (`CorrectionInitialization.lean:5179-5183`, a `Finset.preimage … |>.product Finset.univ`) nonempty for
  the `n` used by the headline theorems? I did not resolve this and it is outside task B.
* **E2 (naming / duplication).** Two distinct in-cone `SameCarrier` structures with identical fields
  (`CorrectionStep.lean:2027`, `LabelSumBounds.lean:813`) and three distinct in-cone `addBlock`s
  (`CorrectionStep.lean:2023`, `LabelSumBounds.lean:818`, `HarmonicWaveInteraction.lean:431`), one of
  which has a *different* `addBlock_oscillation` statement (the unconditional `withCarrier` form,
  `HarmonicWaveInteraction.lean:440`). Any cross-file audit that matches these by short name will
  conflate them. Match by full name.
* **E3 (out of cone).** `CycleStateCoherence.iterate_block_fields` (:601) carries the same `hc` and is
  `in_cone=False`; the brief described it as "a per-j version" of the discharge — it is a *consumer*,
  not a discharge. Do not spend cycles on it.

## Kernel-risk pass

Mechanical scan of exactly the line ranges I read (13 ranges across 8 files, ~800 lines):

| pattern | count | sites |
|---|---|---|
| explicit `.rec` / `rec_` | **0** | — |
| `Acc.rec` / `WellFounded.fix` | **0** | — |
| `decide` / `native_decide` | **0** | — |
| `termination_by` / `decreasing_by` | **0** | — |
| `macro`/`elab`/`syntax`/`set_option`/`axiom`/`unsafe`/`partial`/`sorry` | **0** | — |
| numeral with ≥5 digits | **0** | — |
| `induction`/`| zero`/`| succ` (structural `Nat.rec`) | 29 | CS:6970-6972, CS:6979-6981; ACC:52-54, 58-60, 64-66, 94-101, 105-111, 116-121; ACP (none in range); CSC:617-619 |
| `:= rfl` / `⟨rfl` leaves | 28 | CS:6817, 6820, 6958, 6961, 4837, 4864; ACC:45, 48; ACP:320, 327, 332, 337, 341, 345, 349, and the `@[simp] … := rfl` block :421-450; AI:844 |

Notes:
* `CycleState.iterate` (`CorrectionStep.lean:6952-6955`) is defined by pattern match on `ℕ`
  (`| 0 => seed`, `| n + 1 => (iterate p c seed n).step (p n) c`) and `iterate_zero`/`iterate_succ`
  are proved `:= rfl` (`:6958`/`:6961`) — so it compiles to structural `Nat.rec`, **not**
  `WellFounded.fix`, and needs no `termination_by`. No `Acc.rec` exposure on this path.
* The only numerals in the read ranges are tiny: `2`, `2 ^ (j + 1)` (ACC:93-101), `residualBand := 2`
  (AI:135), `Fin 3`, `Fin 2`. No GMP bignum exposure; no `decide`.
* Structure-eta is used heavily and deliberately: `{ a with … }` in `addBlock` plus anonymous-constructor
  `⟨ih.frequency, ih.phase, ih.angular⟩` transports. This is standard Lean 4 defeq (eta for structures),
  not a weak spot, but it *is* the reason the whole invariant is `rfl`-cheap.

**Kernel-risk verdict for task B's scope: clean. 0 findings.**

## Residue

* No Mathlib build available, so I could **not** kernel-check that the `:= rfl` and `⟨rfl,rfl,rfl⟩`
  leaves actually elaborate (in particular `ACP:327/332/337` need
  `(exactBlock s request).phase ≡ fun n z => base.phase n (z,0)` through
  `SignedWaveUpdate.blockOfCoefficients` and `copyData.commonCorrected`, which I read only at the
  definition level, `CorrectionStep.lean:4839-4843`). I traced the *definitional* path
  (`chartCoefficients` = signed `base` = `primaryPiece.coefficients`) and it is consistent, but the
  final word is the kernel's.
* I did not audit `CycleRepresentation`'s fourth field (`aliasError`, CS:6803-6805) or
  `nextAxisymmetricAlias` (CS:6832) for content — they are `hc`-free and belong to the alias/gauge task.
* I did not check whether `next_representation`'s `simp only … ; ring` step (CS:6891-6896) is
  load-bearing for anything beyond the alias bookkeeping.
* `ActualPrimary.Label`/`activeLabels` nonemptiness left open (E1).
