# ns-index-nonempty — worker A (independent re-derivation), NSE @ f9e8bc5

READ-ONLY audit. No file in /home/gsm/.openclaw/workspace/repos/NSE was modified. No `lake build`
attempted (0 .olean, pinned toolchain v4.34.0-rc2 vs box Mathlib v4.33.0). All claims are
source-read + grep, with file:line. Every Lean statement quoted below is verbatim from the artifact.

## VERDICT

**DERIVABLE-BUT-UNPROVED.** The artifact contains no proof that its wave-label type is inhabited
(grep: `Nonempty (Label|Index|SignedLabel` returns nothing; the only `Nonempty` about the strip is
`ActualSignedMeanBinding.lean:54`). The 0 = 1 derivation W25 sketched is **sound** and every input
theorem it needs exists and is hypothesis-clean. So the artifact's wave index set is NOT proved
inhabited in-repo, but IS derivable.

Cost, honestly: **~6 lines for the core contradiction** (W25's "five lines" is right for that step,
given a strip point in scope) **+ ~10-14 lines to relocate the strip witness**, because
`actual_strip_nonempty` is **import-unreachable from 3 of the 4 split sites** (details in §5).
Total realistic in-repo closure ≈ 20 lines in `ActualPrimaryCovariance.lean` + 1 new import.

W25's *conclusion* survives hostile testing. W25's *"closes all four split sites in five lines"*
**overreaches on the import DAG**, not on the type transfer. The parent's suspected type-mismatch
gap **does not exist** (§2): all four sites split on the *same* type `ActualPrimary.Label B N0 × Fin 2`.

## 1. `partitionFactor` really is a bare `Finset.sum` — empty labels force 0

Verbatim, `NavierStokes/ActualPrimaryCovariance.lean:381-382`:

```lean
noncomputable def partitionFactor (B N0 n : ℕ) (x : Point) : ℝ :=
  ∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2
```

- It is `Finset.sum` over `unsignedLabels B N0 n : Finset (Label B N0)`
  (`ActualPrimaryCovariance.lean:216-220`), **not** a `finsum`/`tsum` over a type.
- **No normalisation, no division, no `if`**: the summand is `spatialMask ... ^ 2`. Nothing can
  rescue `0 = 1`.
- With `IsEmpty (Label B N0)`, any `Finset (Label B N0)` is `∅`, so
  `Finset.sum_eq_zero (fun L _ => isEmptyElim L)` gives `partitionFactor B N0 n x = 0`.
- The "= 1" side, `ActualPrimaryCovariance.lean:508-513`:

```lean
theorem partitionFactor_eq_one (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (hq : physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N) :
    partitionFactor B N0 n x = 1 := by
  rw [partitionFactor_eq_tail B N0 n hx]
  exact physical_mask_tail_sum_sq _ _ (physicalScale_pos n hx) hq _
```

  Only two hypotheses: a strip point and the scale bound. **No `Nonempty` hypothesis**, no instance
  arguments (the file's only `variable` is `{B N0 : ℕ}` at `ActualPrimaryCovariance.lean:92`;
  `B N0 n` are explicit in the statement).
- The "= 1" engine is unconditional and genuine, `PartitionedCovariance.lean:766-768`:
  `physical_mask_tail_sum_sq (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x)`
  `: (∑ᶠ U : UnsignedLabel, mask D (tailLabel N U) q x ^ 2) = 1`. `UnsignedLabel := ℕ × SlotColoring.Grid`
  (`PartitionedCovariance.lean:580`) — an obviously inhabited *index type*, unrelated to `Label B N0`.
  So the sum-to-one is not itself vacuous when `Label B N0` is empty; that is exactly why the
  contradiction bites.
- The bridge `partitionFactor = finsum over UnsignedLabel` is `partitionFactor_eq_tail`
  (`ActualPrimaryCovariance.lean:464-506`); its content is `PrimaryGeometryAssembly.physicalMask_has_index`
  (`PrimaryGeometryAssembly.lean:198-205`, concludes `∃ i : Index W N, label W i = L`) — i.e. the
  artifact already owns a label-*construction* lemma. That is an alternative, even more direct route
  to `Nonempty`, at the price of exhibiting one nonzero mask.
- Hygiene: `grep -rn 'sorry\|admit' NavierStokes/*.lean` → empty; `grep -rn '^axiom' NavierStokes/*.lean` → empty.
  `chosen_threshold_four` (`ActualPrimaryCovariance.lean:404`) is proved, not assumed.

**§1 result: CONFIRMED.** Empty `Label B N0` forces `partitionFactor = 0`, contradicting `= 1`.

## 2. TYPE-TRANSFER (parent's suspected hole): NO GAP. All four sites are the same type.

- `ActualPrimaryCovariance` derives `Nonempty (Label B N0)` where `Label` comes from
  `open CorrectionInitialization.ActualPrimary` (`ActualPrimaryCovariance.lean:18`), i.e.
  `abbrev Label (B N0 : ℕ) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N`
  (`CorrectionInitialization.lean:3931`).
- Site 1: `ActualInitialMean.lean:25` — `abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2`.
- Site 4: `ActualSignedStageControls.lean:35` — `abbrev SignedLabel (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2`.
- Sites 2-3: `ActualSignedUnmaskedBounds.lean:23` — `abbrev Label (B N0 : ℕ) := ActualSignedStageControls.SignedLabel B N0`,
  which by `ActualSignedStageControls.lean:35` is again `ActualPrimary.Label B N0 × Fin 2`.

All four are *reducible `abbrev`s* for `ActualPrimary.Label B N0 × Fin 2`, with the same `B N0`, and
`nominal`/`choice`/`h`/`standardRegion` are **global, parameter-free** defs
(`CorrectionInitialization.lean:3886-3891`, `:3929`, `:5169`), so there is no instance-drift.
Transfer is a one-term coercion: from `⟨L⟩ : Nonempty (ActualPrimary.Label B N0)` produce
`⟨(L, (0 : Fin 2))⟩` (no typeclass search needed). **`Nonempty Label` transfers to all four sites.**
W25 does not overreach here.

Cross-check on component order: `ActualSignedUnmaskedBounds.lean:168` and
`ActualSignedStageControls.lean:1139` both write `ActualPrimaryBounds.fullEnvelope_nonneg (l.2, l.1)`
against `ActualPrimaryBounds.SignedLabel := Fin 2 × ActualPrimary.Label B N0`
(`ActualPrimaryBounds.lean:33`) — consistent with `l.1 : Label`, `l.2 : Fin 2`.

The four sites (exactly four; `grep isEmpty_or_nonempty NavierStokes/` returns 4 hits, and
`isEmptyElim` appears only in those branches: `ActualInitialMean.lean:321`,
`ActualSignedUnmaskedBounds.lean:164,199`, `ActualSignedStageControls.lean:1135`):

| # | file:line | type split | branch content |
|---|---|---|---|
| 1 | ActualInitialMean.lean:318 (in `covariance_bounds_of_curl`, :309) | `Index B N0` | empty ⇒ `activeLabels = ∅`, seed oscillation `= 0`, classes via `MemClass.zero` (:320-339) |
| 2 | ActualSignedUnmaskedBounds.lean:161 (`raw_jets`, :150) | `Label B N0` | empty ⇒ trivial `⟨fun l => isEmptyElim l, …⟩` (:164) |
| 3 | ActualSignedUnmaskedBounds.lean:196 (`localized_jets`, :185) | `Label B N0` | same (:199) |
| 4 | ActualSignedStageControls.lean:1132 (`raw_coefficients_jets`, :1121) | `SignedLabel B N0` | same (:1135) |

Why the splits exist at all: the general machinery needs `[Nonempty ι]`
(e.g. `UniformPrimaryWeights.lean:327, 596, 675`). The empty branches are **defensive, and proved** —
they are not soundness holes. Proving inhabitedness would let all four be deleted; it changes no
`inr` branch. So the real payoff is anti-vacuity, not repair.

## 3. STRIP-DOMAIN BRIDGE: sound, and it needs *less* than the one `rfl`

Chain, all verbatim:
- `ActualSignedMeanBinding.lean:54-67`: `actual_strip_nonempty : ActualInitialization.geometry.strip.domain.Nonempty`,
  witness `((G.patch.a + G.patch.b) / 2, ((1, 0), (0, 0)))`, hypothesis-free, via
  `LocalSignedRequest.movingStrip_domain` (`LocalSignedRequest.lean:191-198`) and
  `normalized_axis_scale : SimilarityCoordinates.coordinateQ (2 * h) (1, 0) = 1` (`ActualSignedMeanBinding.lean:48`).
- `ActualInitialization.lean:665`: `theorem geometry_strip : geometry.strip = strip := rfl`.
- `ActualInitialization.lean:383-384`: `noncomputable def strip : StripData Point :=
  BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion` —
  **literally the target expression** of `partitionFactor_eq_one`'s `hx`
  (`ActualPrimaryCovariance.lean:509`, where `nominal`/`standardRegion` are the same globals via the
  `open` at :18). Same instances. `ActualInitialMean.lean:27-28` defines its own `strip` by the
  identical expression, so site 1's `strip` is that strip too.
- Defeq check of `geometry_strip` (why the `rfl` is honest): `SignedMeanGain.Geometry.strip`
  (`SignedMeanGain.lean:560-563`) = `LocalSignedRequest.movingStripData G.region G.patch.a G.patch.b
  G.leftWeight G.rightWeight …`; `BaseContextAssembly.nativeStrip` (`BaseContextAssembly.lean:231-234`)
  = `movingStrip … U (leftRadius W) (rightRadius W) (edgeExponent W / 4) 1 …`; and `geometry`'s fields
  are exactly those (`ActualInitialization.lean:644` `region := ActualPrimary.standardRegion`,
  `:645` `patch := patch` with `patch.a/b := leftRadius/rightRadius ActualPrimary.nominal`
  (`:631-633`), `:646-647` `leftWeight := edgeExponent nominal / 4`, `rightWeight := 1`,
  `:650-651` `epsilon := ChartScales.epsilon ActualPrimary.h`, `slow := BaseContextAssembly.slowScale`).
  Proof-side arguments differ only up to Prop-proof irrelevance. **Nothing extra is missing.**

**§3 result: the bridge is exact, one `rfl` plus definitional unfolding of `strip`.**
No `nominal`/`standardRegion` mismatch.

## 4. Threshold instantiation: `n` is free — CONFIRMED

`ActualPrimaryCovariance.lean:527-529`:
```lean
theorem physicalScale_tail (B N0 : ℕ) {n : ℕ} (hn : (choice B N0).prepared.N + 1 ≤ n)
    {x : Point} (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N
```
`partitionFactor_eq_one` quantifies `n` explicitly and universally (`:508`). Take
`n := (choice B N0).prepared.N + 1` and `hn := le_refl _`. No extra hypothesis, no side condition,
and the conclusion `Nonempty (Label B N0)` does not mention `n`. Supporting facts are proved, not
assumed: `physicalScale_pos` (`:407-411`) needs only `hx`; `Q_antitone`/`Q_succ` (`:515`, `:521`).

## 5. THE REAL GAP IN W25's "five lines": IMPORT REACHABILITY

Computed from the `import NavierStokes.*` graph of all files in `NavierStokes/`:

| site file | reaches `ActualPrimaryCovariance`? | reaches `ActualSignedMeanBinding`? | reachable *from* `ActualSignedMeanBinding`? |
|---|---|---|---|
| ActualInitialMean | yes (`ActualInitialMean.lean:4`) | no | **YES** ⇒ importing the witness would be a **CYCLE** |
| ActualSignedUnmaskedBounds | yes (transitively) | no | no ⇒ new import legal |
| ActualSignedStageControls | **NO** | no | **YES** ⇒ **CYCLE** |

Consequences, stated loudly:
1. `actual_strip_nonempty` (`ActualSignedMeanBinding.lean:54`) **cannot be cited at site 1 or site 4**:
   `ActualSignedMeanBinding` transitively imports both `ActualInitialMean` and
   `ActualSignedStageControls`. Any 5-line patch that says "`obtain ⟨x, hx⟩ := actual_strip_nonempty`"
   at those two sites **does not compile**.
2. Site 4's file does not even see `partitionFactor_eq_one`: `ActualSignedStageControls.lean:1-8`
   imports `CorrectionInitialization, CorrectionStep, ActualSignedControl, ActualSignedGeometry,
   ActualPhaseDefect, ActualPrimaryDynamics, ActualPrimaryBounds, ActualSignedDynamics` — no
   `ActualPrimaryCovariance`. Adding that import is acyclic (`ActualPrimaryCovariance.lean:1-2`
   imports only `CorrectionInitialization` and `BaseStressClasses`), but it is an extra edit W25 did
   not count.
3. `ActualInitialMean` cannot reach `ActualInitialization` either, so `geometry` is unavailable there;
   the witness must be restated for `BaseContextAssembly.nativeStrip nominal standardRegion` directly.

**Correct placement: put both lemmas in `ActualPrimaryCovariance.lean` itself** (it already reaches
`LocalSignedRequest`, `BaseContextAssembly`, `ActualSignedGeometry`, `SignedMeanGain` transitively,
and defines all four sites' `Label`). Ingredients for the relocated witness are all in scope:
- `BaseContextAssembly.nativeStrip_mem` (`BaseContextAssembly.lean:236-239`): membership iff
  `x.2.1 ∈ U.carrier ∧ profileRadius h (slowCoordinates x) ∈ Ioo (leftRadius W) (rightRadius W)`.
- `standardRegion.carrier = {z | 0 < z.1 ∧ coordinateQ (2*h) z ∈ Ioo (1/2) 2}`
  (`ActualSignedGeometry.lean:30-32`, via `CorrectionInitialization.lean:5169-5170`), so `(1,0)` is in
  the carrier once `coordinateQ (2*h) (1,0) = 1` — provable exactly as `ActualSignedMeanBinding.lean:48-52`
  (uses only `SimilarityCoordinates.eq_coordinateQ`, `outgoing.data.h_pos`, `h_lt_half`).
- `PrimaryTargetBounds.radii_ordered : leftRadius W < rightRadius W` (`PrimaryTargetBounds.lean:676`)
  and `leftRadius_pos` (used at `ActualPrimaryCovariance.lean:202`) give the midpoint in `Ioo a b`.

Sketch of the closure (my own, ~6 lines given the witness):
```lean
theorem label_nonempty (B N0 : ℕ) : Nonempty (Label B N0) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  obtain ⟨x, hx⟩ := nativeStrip_nonempty            -- relocated witness, §5
  have h0 : partitionFactor B N0 ((choice B N0).prepared.N + 1) x = 0 :=
    Finset.sum_eq_zero (fun L _ => isEmptyElim L)
  exact absurd (h0.symm.trans (partitionFactor_eq_one B N0 _ hx
    (physicalScale_tail B N0 le_rfl hx))) (by norm_num)
```
Then `Nonempty (Index B N0) := ⟨(Classical.choice (label_nonempty B N0), 0)⟩` etc. for all four sites.

## 6. Residual, unremovable caveat

No compilation was possible (see header), so "these ~20 lines typecheck" is a source-level judgement,
not a machine check. Everything I *did* check — the statements, their hypothesis lists, the section
`variable` context, the abbrev chains, the import DAG, absence of `sorry`/`axiom` — is verbatim above.
The one step I could not test mechanically is Lean's acceptance of `geometry_strip`'s `rfl`
(`ActualInitialization.lean:665`); its two sides match field-by-field, and the closure I recommend in
§5 does not use it at all.
