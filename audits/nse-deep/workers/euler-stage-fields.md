# Worker report — `euler-stage-fields`: what `forwardNext` and `joinedNext` actually prove

Scope owner: read-only auditor. Repo under audit: `/home/gsm/.openclaw/workspace/repos/NSE`
(openai/NavierStokesAndEuler @ `f9e8bc5`). **No Mathlib build on this box: source-level reading only.**
Nothing under the audit path was modified. Every claim below carries `file:line` and is re-checkable
by reading that line.

Assignment: the item `euler-packet` left open — the ~26 fields of `structure Stage`
(`Euler/PacketInductionStage.lean:23-55`) are discharged by `forwardNext`
(`Euler/PacketForwardSuccessor.lean:92`) and `joinedNext` (`Euler/PacketJoinedSuccessor.lean:97`),
which nobody had read.

## Verdict in one line

**No degenerate/junk stage field found, and the anti-degeneracy is *structural*, not rhetorical.**
The two successors are `Classical.choice` on `Nonempty (Geometry{Forward,Joined}Choice …)` records
whose existence is *proved* (`ParentGeometryForwardChoice.lean:96`, `ParentGeometryJoinedChoice.lean:46`)
from a genuine PDE construction (`LabelData.forward_uniform_child`, `ParentUniformForwardChild.lean:36`);
the 26 `Stage` fields are then discharged either (a) by definitional identities that I checked term by
term, or (b) by real inequalities whose only inputs are the *current* stage's invariants plus the
`Scales` budget — never the next stage's. The zero-amplitude escape is closed by a hard identity chain:
`frame_shear` forces the renewed frame's `primaryShear` to equal `shear J X n = exp(...)`, and
`ParentFrame.remainder_bound` (`PacketSourceGeometryData.lean:45-47`) ties that number to the **actual**
strain field of the constructed child, with slack `error = k^(-1/4) ≤ 1`. That number is realised by a
genuine `arctan` packet whose derivative at the centre is `δ⁻¹` (`EulerProof.lean:11818`,
`profile_deriv_zero`) — which is exactly why `0 < δ` appears as a hypothesis everywhere. Kernel exposure
in this scope is nil: **0 `decide`, 0 `native_decide`, 0 `norm_num` on big numerals, 0 `termination_by`,
0 `Acc.rec`, 0 metaprogramming, 0 `sorry`**; the only reductions the kernel performs are single iota
steps on `Nat`-indexed sequence definitions at *symbolic* `n`.
The `attribute [local irreducible]` sites are **elaborator performance only** and the repo itself
documents why, in a checkable way (`ParentGeometryForwardChoiceNoOptions.lean:6-32`).

## Scope

### Read line by line, in full (every declaration)

| file | lines | decls (CONE.csv) |
|---|---|---|
| `PacketForwardSuccessor.lean` | 177 | 11 |
| `PacketJoinedSuccessor.lean` | 196 | 13 |
| `PacketInfiniteConstruction.lean` | 78 | 12 |
| `ParentGeometryForwardChoice.lean` | 137 | 14 |
| `ParentGeometryJoinedChoice.lean` | 93 | 6 |
| `BaseInductionStage.lean` | 105 | 4 |
| `PacketStageRestriction.lean` | 136 | 40 |
| `PacketStageGeometry.lean` | 207 | 38 |
| `PacketStageGuards.lean` | 155 | 20 |
| `PacketStageInputs.lean` | 170 | 24 |
| `PacketStageEstimates.lean` | 144 | 11 |
| `PacketStageLowPropagation.lean` | 138 | 8 |
| `ParentGeometryChoiceLow.lean` | 141 | 6 |
| `ParentGeometryChoiceRenewal.lean` | 145 | 12 |
| `ParentGeometryChoiceInitial.lean` | 162 | 15 |
| `PacketStagePhysicalBounds.lean` | 33 | 3 |
| `StageInitialSupport.lean` | 80 | 7 |
| `PacketStageGrowth.lean` | 96 | 5 |
| `ParentUniformForwardChild.lean` | 82 | 1 |
| `PacketInductionStage.lean` | 146 | 19 |

**20 files, 269 declarations, all read line by line.**

### Read in part (the specific declarations named in this report)

`ParentStateGeometry.lean` (:19-89, 6 decls), `ParentTargetRenewal.lean` (:1-100 + grep of the joined
half, 16 decls in file), `ParentRenewalScaleApplication.lean` (:1-109, 5), `ParentRenewalParameters.lean`
(:98-190, 34 in file), `PacketSourceGeometryData.lean` (:19-120, 22), `PacketForwardGeometryData.lean`
(:23-68, 19), `PhysicalChildParent.lean` (:1-100, 9), `BaseEulerState.lean` (:1-90, 26),
`ParentForwardGeometryGuards.lean` (:95-131, 2), `PacketSourceScaleSequence.lean` (:1-80, 21),
`ParentUniformJoinedChild.lean` (signature only, 1), `PacketAmplitudeBounds.lean` (:13-21),
`EulerProof.lean` (:11758-11818, the `profile`/`profile_deriv_zero` block only),
`ParentPacketPrimaryCenter.lean` (:1-70, 4).
Also skimmed: `PacketFirstStageSupport.lean`, `StageDisplacementConfinement.lean`,
and the 5 dead `*NoOptions.lean` / `*Investigation.lean` copies (see §C).
Prior reports skimmed first: `workers/euler-packet.md` (its `_scratch-packet-*.md` files do not exist
under that name in the tree; the packet worker's sub-reports are `_scratch-packet-contradiction.md`,
`_scratch-packet-horizon.md`, `_scratch-packet-series.md` and I used their conclusions only as
cross-checks, re-deriving each claim I repeat).

## A. What `forwardNext` and `joinedNext` construct

The two are structurally identical (line-for-line parallel, `earlyRatio` ↔ `badRatio`, `Stage S 1` ↔
`Stage S (n+1)`, and the joined branch additionally carries the history `historyTime := P.time`).
Pipeline, forward branch (joined identical, cited in parentheses):

1. **Shrink the current parent strictly**: `restrictedParent := P.parent.restrictTime P.nextHorizon …`
   (`PacketStageRestriction.lean:82`), where `nextHorizon = nextTime + 2·timeWidth (n+1)`
   (`:23`) and `nextTime = time + step` (`:21`), `step = stepLength …` (`:18`).
   Non-degenerate *because proved*: `step_pos` (`:31`), `nextHorizon_lt : nextHorizon < parent.T`
   (`:47`, from `source_stage.next_width`), `nextHorizon_common : baseHorizon/12 < nextHorizon` (`:72`).
2. **Build the geometric input record** `forwardInput : GeometryForwardInput …`
   (`PacketStageInputs.lean:112`) (`joinedInput`, `:41`) from the restricted state/low/frame.
3. **Build the guards** `forwardGuards : ForwardGuards P.forwardFrame` (`PacketStageGuards.lean:115`)
   (`joinedGuards`, `:48`) via `forwardGeometryGuardsOfStage` — this is where `δ := spike J X n`,
   `hchild := shear J X n`, `y := (scaleSequence J X (n+1))⁻¹`, `radius := 1` are pinned
   (`:127-130`, all `rfl`).
4. **Choose the packet**: `chooseForward := Classical.choice (exists_geometryForwardChoice …)`
   (`PacketForwardSuccessor.lean:32`) (`chooseJoined`, `PacketJoinedSuccessor.lean:36`).
5. From that one choice `F`: `forwardParent := F.parent = I.parent.child F.flow k I.normal F.graph …`
   (`:40` → `ParentGeometryForwardChoice.lean:125` → `PhysicalChildParent.lean:29`),
   `forwardState := F.state …` (`:42`), `forwardLow := F.lowBounds …` (`:63`),
   `forwardRenewal := F.renewal …` (`:68`), `forwardNextFrame := forwardRenewal.changeActivation …` (`:89`).
6. `forwardNext : Stage S 1` (`:92-172`) assembles the record.

**The existence theorem is where the work is.** `exists_geometryForwardChoice`
(`ParentGeometryForwardChoice.lean:96-119`) is *not* an axiom and *not* a choice on a subclass: it
`obtain`s `⟨hn,Q,G,hgraph,hG,herror,hdisplacement,LC,hLC⟩` from
`I.label.forward_uniform_child` (`ParentUniformForwardChild.lean:36-79`), which itself unpacks
`forward_uniform_child_label_bounds` (the deep PDE construction, out of my depth budget — see §Residue)
and returns, for the *actual* corrected velocity/pressure:
`‖fderiv (exact physical velocity) x − (α·profile'(k⟪m,·⟫))•rankOne(canonicalVelocity, normal)‖ ≤ k^(-1/4)`
(`:46-59`) plus `∃ LC : LabelData (A.child …), LC.K = k^80` (`:62`). So the *choice* is over a record of
already-constructed objects, and every `Stage` field below is proved from those.

### The 26 fields, one by one (forward branch line numbers; joined branch in brackets)

| Stage field | how discharged | mechanism | verdict |
|---|---|---|---|
| `parent` | `:108` [`:113`] | `F.parent = I.parent.child F.flow …`, a real `Parent` record: `T := A.T`, `ell := nextEll`, displacement/velocity/acceleration composed from the flow, with `determinant = 1` *proved* (`PhysicalChildParent.lean:48-51`) | OK |
| `state` | `:109` [`:114`] | `S.forwardChild …`, the corrected Euler state for that flow | OK |
| `low` | `:110` [`:115`] | `F.lowBounds` needs the smallness side condition `forward_smallness` (`:45-61`), proved from `next_localized` — *not* assumed | OK |
| `time` | `:111` `:= P.nextTime` | `time + step`, `step > 0` proved | OK |
| `time_nonneg` | `:112` | `P.nextTime_pos.le` | OK |
| `time_zero` | `:113` `fun h => by omega` | the hypothesis is `1 = 0` (resp. `n+1 = 0`) — vacuous *by design*, the field is index-guarded | OK |
| `time_lower` | `:114` | `P.nextTime_lower` (`Restriction:62`), a real bound `baseHorizon/12 ≤ nextTime` | OK |
| `horizon_eq` | `:115` `rfl` | `child.T = A.T = restrictedParent.T = nextHorizon ≡ nextTime + 2·timeWidth(n+1)`; pure δ-unfolding, needs `Parent.child` reducible — it is, in *this* file (§C) | OK |
| `horizon_le` | `:116` | `P.nextHorizon_le_base` | OK |
| `scale_eq` | `:117` `rfl` | `child.ell := nextEll ≡ supportScale J X (n+1)` (the `local notation "ell"`, `:28`) | OK |
| `label_eq` | `:118` | `F.label_constant : labels.K = k^80` with `k = frequency J X n ≡ previousFrequency J D X (n+1)` by one iota step | OK |
| `gradient_bound` | `:134-136` [`:139-141`] | `F.physical_bounds …).1` gives `≤ CM + hchild·(goodRatio+earlyRatio) + k^(-1/4)`; `ratio_absorption.1` (`LowPropagation:50`) absorbs that into `gradientConstant·shear J X n = gradientConstant·previousShear J X (n+1)`. Uses `S.shear_separation n` — the scale gap does the absorbing | OK |
| `hessian_bound` | `:137-143` [`:142-150`] | same route, `ratio_absorption.2`, with an explicit `change` + `nlinarith only` | OK |
| `exterior_bound` | `:144` | `initial_step_bound.1` = `rw [sum_range_succ]; linarith` — the `range n` sum grows by exactly one term `initialIncrement J X n`, and the new cost is `≤` it by `forward_initial_cost` (`Estimates:111`) | OK |
| `core_bound` | `:145` | `initial_step_bound.2`, same | OK |
| `pressure_bound` | `:146-149` | `pressure_step_bound` + `forward_pressure_cost` (`Estimates:122`) | OK |
| `boundary_eq` | `:124` `rfl` | `lowBounds_values.5` shows `.L = boundaryLocalizationC1·.Bc + 1` holds by `rfl` (`ChoiceLow.lean:52-54`) | OK |
| `radius_eq` | `:125` `P.radius_eq` | legitimate only because `lowBounds_values.4 : (F.lowBounds …).r = I.low.r` is `rfl` (`ChoiceLow.lean:51`); the child inherits the radius | OK |
| `frame` | `:126` | `forwardRenewal.changeActivation` (a transport along `targetTime = nextTime`, `PacketStageGeometry.lean:40`) | OK |
| `frame_shear` | `:150-151` | `renewal_matches.shear_eq (I).delta_pos` → `Pnew.shear = G.hchild = shear J X n`. **The load-bearing field.** Needs `0 < δ` | OK |
| `frame_bound` | `:152-154` `le_rfl` | `renewal_costs : Pnew.G = K` (`ChoiceRenewal:66`, `⟨rfl,rfl⟩`) with `K := frameConstant·(1+previousShear J X n)`, and the goal wants `≤ frameConstant·(1+olderShear J X (n+1))`; `olderShear J X (n+1) ≡ previousShear J X n` by one iota step (`SourceScaleSequence.lean:38-40`). Definitional, **not** vacuous: the burden moved into `ParentFrame.B_bound` inside `renewal` | OK |
| `frame_error` | `:155-157` `le_rfl` | `Pnew.error = k^(-1/4)` and `priorError J D X (n+1) = previousFrequency J D X (n+1)^(-1/4) ≡ (frequency J X n)^(-1/4) = k^(-1/4)` (`PacketSourceScaleActual.lean:22`). Again definitional, with the real content in `ParentFrame.remainder_bound` | OK |
| `coupling_error` | `:158-159` | `coupling_step` (`LowPropagation:102`): triangle inequality on `|a−1| ≤ |a−P.frame.a| + |P.frame.a−1|` plus `P.coupling_error` and `sum_range_succ`; the relative step error comes from `literal_step.1` | OK |
| `tilt_lower` | `:160-161` | `literal_step` (`ParentRenewalScaleApplication.lean:25-39`): `RenewalAtTarget.tilt_interval` gives `\|y⁻²σ²−1\| ≤ tiltError ≤ 1/2`, then `nlinarith` → `1/2 ≤ σ²·scaleSequence(n+1)²`. `y = scaleSequence(n+1)⁻¹` is supplied by `rfl` (`:101`) | OK |
| `tilt_upper` | `:162-163` | same, `≤ 2` | OK |
| `compression` | `:164-172` | `renewal_matches.background_compression_of_error_le_one (priorError J D X (n+1)) (S.priorError_one (n+1))` → `⟪B(unit m),unit m⟫ + priorError < 0`, from `Geo.compression_margin` + `Geo.nextCompression_le` (`LowPropagation:127-135`) | OK |

Base case for comparison: `firstStage` (`BaseInductionStage.lean:22-94`) sets `time := 0`, leaves
`time_lower` and `compression` vacuous by `fun h => (h rfl).elim` (`:42`, `:61`) — legitimate, both are
`n ≠ 0`-guarded — and proves `frame_bound` as a concrete numeric comparison
(`P.G = 1 + initialCoefficientCost ≤ frameConstant·(1+1)`, `:78-84`), `frame_error := le_of_eq hcost.2`
(`:85`), `coupling_error` from `P.a = 1` (`:86-88`), `tilt` from `σ²X² = 1` (`:30-34`, `:89-94`).
**The vacuous-at-0 fields are re-established for real at index 1** by `forwardNext`: `compression` comes
from `ForwardGuards.compression_guard`
(`PacketForwardGeometryData.lean:42`), itself *proved* at
`ParentForwardGeometryGuards.lean:126-128` from the smallness budget `hplain` (`:107-111`) and
`P.G_lower : 1 ≤ G`. So the guard is never carried as an unmet promise.

## B. The degeneracy / circularity hunt — concrete results

### B1. Could a stage field be satisfied by a zero-amplitude or empty-support choice? **No.**

The chain that forbids it, quoting the Lean:

* `frame_shear : frame.shear = previousShear S.J S.X n` (`PacketInductionStage.lean:48`) and
  `ParentFrame.shear := primaryShear P.c P.m P.v τ` (`PacketSourceGeometryData.lean:55`), where
  `primaryShear c m v t = c*(‖m t‖*‖v t‖)` (used as such at `ParentRenewalParameters.lean:140`).
* `ParentFrame` forces `ray_nonzero`, `velocity_nonzero`, `tangent : ⟪m t,v t⟫ = 0`
  (`PacketSourceGeometryData.lean:40-42`), so in `gradient_lower` the rank-one operator has
  `‖shear • rankOne (unit v) (unit m)‖ = |shear|` exactly (`PacketStageGrowth.lean:57-61`).
* `remainder_bound : ‖D.M.field (D.clamp t) 0 − B t − primaryShear c m v t • rankOne (unit v) (unit m)‖ ≤ error`
  (`PacketSourceGeometryData.lean:45-47`) — `D.M` is the **actual** parent strain field
  (`ParentTargetRenewal.lean:67-69` proves `A.centerStrain t = D.M.field (D.clamp t) 0`).
* Therefore `previousShear J X n ≤ ‖M‖ + G + error` (`PacketStageGrowth.lean:67-73`), and with
  `frame_bound` + `frame_error` + `S.activation_small` giving `G + error ≤ previousShear/2` (`:74-77`),
  the **actual** velocity gradient at the origin satisfies
  `previousShear J X n / 2 ≤ P.activationGradient` (`gradient_lower`, `:52`), while
  `previousShear_ge_index : (n:ℝ)+1 ≤ previousShear J X n` (`:25-34`).

So an empty-support / zero-amplitude / zero-`fderiv` stage is *impossible*: it would contradict
`gradient_lower`. That also closes the "support ⊆ ball 2 is satisfied by ∅" loophole in
`stages_initial_support` (`StageInitialSupport.lean:51`): the upper bound on support is compatible with
the empty set, but `gradient_lower` forbids the field being 0.

### B2. Is the huge shear *realisable*, or is it a number nobody has to earn? It is realisable, and I found the exact identity that earns it.

`primaryAmplitude δ hchild r w t = δ*hchild/(‖r t‖*‖w t‖)` (`PacketAmplitudeBounds.lean:13-14`);
`RenewalAtTarget.coefficient_eq : P.c = G.amplitude/G.δ` (`ParentRenewalParameters.lean:123`);
`target_shear_normalization (hδ : 0 < G.δ) : (G.amplitude/G.δ)*G.targetSize = G.hchild` (`:98-104`).
The renewed frame's `c` is therefore `hchild/(‖r‖‖w‖)` and `shear = hchild` (`shear_eq`, `:139-142`).
Meanwhile the actual field's increment at the centre is
`(α·deriv (profile δ) (k⟪m,Y 0⟫))•rankOne(canonicalVelocity, normal)` with `Y 0 = 0`
(`SmoothState.normalized_inverse_zero`, `ParentStateGeometry.lean:35`), and
`forward_primary_center_term` rewrites it to `(α/δ)•rankOne(sourceVelocity, sourceNormal)`
(`ParentPacketPrimaryCenter.lean:23-34`) using
**`profile_deriv_zero (δ) (hδ : 0 < δ) : deriv (profile δ) 0 = δ⁻¹`** (`EulerProof.lean:11818`) with
`profile δ t = arctan (sin t/(1+δ−cos t))` (`:11758`).
So `α/δ` is exactly the `c` the frame claims, and the claimed shear is the honest derivative of a real
`arctan` packet. **This is where the junk-value risk really lives and it is closed:** if `δ = 0` were
allowed, `profile 0` is singular at `0`, `deriv` would fall back to the junk value `0`, and the whole
construction would become vacuous while still type-checking. That is precisely why `0 < δ` is a *field*
of the inputs (`GeometryForwardInput.delta_pos`, `ParentGeometryForwardChoice.lean:38`) and is
discharged by `S.spike_pos n` with `δ = spike J X n = exp(−…) > 0`
(`PacketStageInputs.lean:131`, `:64`). **Direction of the junk value is against the claimant** — a
degenerate profile would kill the divergence, not fake it.

### B3. Does the inductive step re-use the invariant it must establish? **No — I checked the signatures.**

`joinedNext` has hypotheses `(P : Stage S n) (hn : n ≠ 0) (hq) (hB)` only
(`PacketJoinedSuccessor.lean:23-25`); there is no `Stage S (n+1)` argument anywhere in the file, and no
`Stage S (n+1)` appears in the hypotheses of any lemma it calls. What the step *does* use is the
current stage's fields: `P.coupling_bounds`, `P.tilt_upper`, `P.frame_bound`, `P.frame_error`,
`P.label_eq`, `P.compression hn`, `P.exterior_bound`, `P.core_bound`, `P.pressure_bound`,
`P.scale_eq`, `P.source_stage` (see `PacketStageGuards.lean:59-69` and
`PacketStageEstimates.lean:42-47`, `:82-86`). That is ordinary induction, not circularity.
The cumulative fields are honest: `exterior_bound` is `≤ … + ∑ i ∈ range n, initialIncrement i`
(`PacketInductionStage.lean:41`) and the step adds *one* term via `sum_range_succ`
(`PacketStageLowPropagation.lean:21`); the `Scales` record's `SmallSeries` fields cap the whole sum, so
the bound cannot drift to `∞`.

### B4. Two places where the *smallness* side conditions could have been smuggled in as hypotheses — they were not

`F.lowBounds` requires `hsmall` (`ParentGeometryChoiceLow.lean:25-29`) and it is discharged by
`forward_smallness` (`PacketForwardSuccessor.lean:45-61`), whose engine is `next_localized`
(`PacketStageLowPropagation.lean:30-48`) — that lemma consumes `S.localized_guard` and the *partial-sum*
bounds `S.initial_partial_sum (n+1)`, `S.pressure_partial_sum (n+1)`, i.e. the `Scales` series budget,
not an assumption about the new stage. Same for `joined_smallness` (`PacketJoinedSuccessor.lean:50-67`).

### B5. One transport (`Eq.rec`) that I want on the record

`ParentFrame.changeActivation P h := h ▸ P` (`PacketStageGeometry.lean:40`) transports a frame along an
equality of **real** activation times, and its 9 projection lemmas are `by cases h; rfl` (`:42-50`).
This is sound (motive is a plain `ParentFrame D t`, `t` a variable, so `cases h` is legal) and the
kernel does not reduce it (the equality is opaque, so the `Eq.rec` is stuck and merely type-checked).
No structure-eta or large-elimination subtlety is invoked. Verdict OK, flagged only because
dependent casts are where kernel bugs historically bite.

## C. `attribute [local irreducible] Parent.child` / `initialParent` — answered

**What they unfold to.** `Parent.child` (`PhysicalChildParent.lean:29-51`) is a 12-field `Parent`
record instance: `T := A.T`, `ell := nextEll`, three composed `SmoothTimeField`s
(`EulerChildParticleTime.displacement/velocity/acceleration`), two time-derivative proofs, `initial`,
and a `determinant` proof by tactic. `initialParent` (`BaseEulerState.lean:35-36`) is
`(solutionParent β hβ ell …).restrictTime initialTime …`, i.e. another full `Parent` record built over
the concrete base solution.

**Why a proof would want them opaque — and this is not my speculation, the repo says so and the claim
is checkable.** `Euler/ParentGeometryForwardChoiceNoOptions.lean:6-32` is an independent copy of the
live file that documents the experiment: the expensive step is Lean's automatic generation of
`GeometryForwardChoice.mk.inj`, which compares `LabelData (I.parent.child flow …)` for two distinct
`flow` variables; definitional equality unfolds `Parent.child` and its large displacement/velocity/
acceleration constructions before noticing the types differ. Measured on Lean 4.34.0-rc2:
**353857 heartbeats for the original structure declaration vs 3224 with `Parent.child` locally
irreducible (~110×)**, and "constructor injectivity generation stays enabled". That is why the section
around the structure is literally named `section ConstructorInjectivity`
(`ParentGeometryForwardChoice.lean:73-94`, `ParentGeometryJoinedChoice.lean:22-44`).
`BaseInductionStageNoOptions.lean:7-31` gives the analogous story for `initialParent` (418992 → 164890
heartbeats), and states that the two `firstStage` definitions were checked equal by `rfl` and that only
`propext`, `Classical.choice`, `Quot.sound` appear in the axiom dependencies. I verified by `diff` that
`BaseInductionStageNoOptions.lean` and `BaseInductionStage.lean` differ **only** in the docstring, the
namespace, and a `_noOptions` name suffix — i.e. the fix really was applied to the live file.

**Does any theorem depend on them NOT being unfolded? No — and the proof is that the opposite is
required elsewhere.** All 12 attribute sites are `local` (`ParentGeometryForwardChoice.lean:75`,
`ParentGeometryJoinedChoice.lean:24`, `BaseInductionStage.lean:18`, `BaseFirstPacketChoice.lean:25`,
`BaseFirstPacketEvolution.lean:61`, plus 7 in dead copies / `EulerProof.lean:5916`, `:6074` for
`sobolevNorm embeddingConstant`), and the successors' `horizon_eq := rfl` and `scale_eq := rfl`
(`PacketForwardSuccessor.lean:115,117`; `PacketJoinedSuccessor.lean:120,122`) **need** `Parent.child`
transparent — they hold precisely because `child.T := A.T` and `child.ell := nextEll`. Those `rfl`s live
in a different file where the attribute is not in force. Since reducibility is elaborator-only, the
kernel re-checks those `rfl`s by full δ-unfolding anyway; the attribute changes nothing the kernel sees.
Verdict: **OK, not a soundness lever.** The only residual smell is process, not logic: `Parent.child`
being expensive means the elaborator's defeq engine did explore a large term, and the repo ships 13 dead
`*NoOptions.lean`/`*Investigation.lean` files (all with `in_import_closure = False` in CONE.csv, so they
are not part of the proof) as evidence of that tuning.

## D. Is the stage recursion structural, and is the kernel ever asked to reduce it at a concrete index?

* `stages : (n : ℕ) → Stage S n | 0 => S.firstStage | n+1 => (stages n).successor hq hB`
  (`PacketInfiniteConstruction.lean:39-41`). **No `termination_by`, no `decreasing_by`, no
  `WellFounded`, no `Acc.rec` in the file** (verified by scan over the whole 21-file scope: zero hits).
  `stages_zero := rfl` (`:43`) and `stages_succ … := rfl` (`:45-46`) type-check, which only happens for
  equation lemmas produced by structural recursion (`Nat.rec`), not for `WellFounded.fix`.
* `Stage.successor` (`:21-25`) is `cases n` → `Nat.casesOn`, one iota step, dispatching to `forwardNext`
  / `joinedNext`.
* **Concrete-index reductions, complete list in my scope (4 sites, all one iota step, no arithmetic):**
  `stages_zero` `:= rfl` at literal `0` (`:43`, `in_cone=False`);
  `stages_succ` `:= rfl` at symbolic `n+1` (`:45`, `in_cone=False`);
  `stages ... 0` inside the base case of an induction at `StageDisplacementConfinement.lean:105,112,113`
  and `particleDisplacementCap` (`:119`); `firstStage_time`/`firstStage_horizon` `:= rfl`
  (`BaseInductionStage.lean:96,98`) which reduce projections of a record, not the recursion.
  Nothing forces reduction at a *large* literal; there is no `stages … 7` anywhere.
* Other iota steps the kernel must do, all at symbolic `n`: `olderShear J X (n+1) → previousShear J X n`
  and `previousFrequency J D X (n+1) → frequency J X n`
  (`PacketSourceScaleSequence.lean:34-40`), used by the `le_rfl` proofs of `frame_bound`/`frame_error`.
* `omega` at `PacketForwardSuccessor.lean:113` / `PacketJoinedSuccessor.lean:118` proves
  `1 = 0 → …` / `n+1 = 0 → …`; the certificate is a few `Nat` literals.

## Kernel-risk assessment

**(1) Recursive inductive types / recursor reduction.**
Present but minimal. `Nat.rec`/`Nat.casesOn` on `stages`, `successor`, `previousShear`, `olderShear`,
`previousFrequency` — all at symbolic index except the four literal-`0` sites in §D. Structures are
plain non-recursive records (`Parent`, `Stage`, `ParentFrame`, `Guards`, `LowBounds`,
`GeometryForwardChoice`, `GeometryJoinedChoice`); no nested/indexed families, no large elimination, no
`Acc.rec`. One `Eq.rec` transport (`changeActivation`, §B5) which is stuck, not reduced.
`GeometryForwardChoice.mk.inj` is auto-generated and, per the repo's own measurement, forced a large
defeq exploration of `Parent.child` in the *elaborator*; the kernel re-checks the resulting term but
does not need to search. **Does the kernel have to do the risky computation? Essentially no.**

**(2) Nat/GMP numeral arithmetic.**
**Zero exposure in this scope.** Scan of the 21 files: `decide` 0×, `native_decide` 0×, `Nat.pow/div/
mod/gcd/beq/ble` 0×. `norm_num` appears 20× and every instance I read is on a tiny rational goal
(`(0:ℝ) < 12`, `1/2 ≤ 1`, `2000 ≤ …` style) or on `rpow_ofNat`. The big-looking exponents are real
`Monoid.npow`/`rpow` on symbolic reals — `k^80` (`ParentGeometryForwardChoice.lean:86`),
`X^1000` (`PacketInductionStage.lean:42`), `horizon^40` (`ParentForwardGeometryGuards.lean:97`),
`X^(-498:ℝ)` — none of which the kernel can or must evaluate, because `X` and `k` are opaque reals
coming from `Classical.choice`. There is no `norm_num` certificate over a large numeral here.

**(3) Custom metaprogramming.**
**Zero.** No `macro`/`elab`/`syntax`/`notation`-with-elab/`set_option`/`axiom`/`unsafe`/`partial`/
`sorry` in the 21 files. Only `local notation` abbreviations (`PacketForwardSuccessor.lean:24-28`) and
`attribute [local irreducible]` (§C), both ordinary features that the kernel ignores.

**Extra vector actually worth naming:** `Classical.choice` is used twice per stage
(`chooseForward`/`chooseJoined`), i.e. once per index, plus once for `constructionScales`. All are on
`Nonempty` of a *proved* type. Axioms used are the standard three (the repo's own `NoOptions` note
claims `propext`, `Classical.choice`, `Quot.sound` only, for `firstStage`; I could not re-run
`#print axioms` without a build).

## Escalations

1. **`forward_uniform_child_label_bounds` / `joined_uniform_child_label_bounds` are the single
   unexamined load-bearing existence proofs.** `Euler/ParentUniformForwardChild.lean:63-73` (and
   `ParentUniformJoinedChild.lean:60-64`) consume them; everything in §A rests on their conclusion
   `‖fderiv(actual velocity) − α·profile'(k⟪m,·⟫)•rankOne(…)‖ ≤ k^(-1/4)`.
   *Question for an expert:* is that estimate proved for the actual nonlinear Euler evolution of the
   corrected datum, or for a linearised/ansatz field that is then *asserted* to be the evolution?
   *What would settle it:* read `PacketForwardUniformChild.lean` +
   `ParentPacketForwardChildChoice.lean` and check that the `Evolution` supplied to `A.child` satisfies
   the Euler equation fields, not just the bounds.
2. **`ParentFrame.remainder_bound` inside `A.forwardGeometryFrame` / `A.joinedGeometryFrame`**
   (consumed at `ParentStateGeometry.lean:62`, `:81`). This is the one step that converts
   "the increment's centre gradient is ≈ `(α/δ)•rankOne`" into "the *new* frame's `shear` is `hchild`
   up to `error`". *Question:* does the proof there use `hsource` at the **target time**
   `tNext` (which is inside the new horizon) or only at `t = 0`?
   *What would settle it:* check the `Icc τ N.T` quantifier ranges at
   `ParentPacketPrimaryCenter.lean:65-70` against `PhysicalGeometryData.target_time_mem`.
3. **`S.activation_small hn`** (`PacketInductionScaleBounds.lean:102-109`) is what makes
   `G + error ≤ previousShear/2` in `gradient_lower`. It is a `Scales`-derived inequality
   `frameConstant·(1+olderShear n) + priorError n ≤ activationMargin·previousShear n`.
   *Question:* is `activationMargin` independent of `n`, so that this survives all `n`?
   *What would settle it:* `activationMargin` is a closed constant
   (`PacketStageGrowth.lean:12-19` bounds it by `1/2`) — confirm the inequality's proof uses only
   `shear_separation`, which is a `Scales` field, and not a per-`n` choice.
4. **`in_cone=False` on definitional-identity lemmas that this report leans on**:
   `GeometryForwardChoice.renewal_costs` (`ParentGeometryChoiceRenewal.lean:66`, `False`),
   `lowBounds_values` (`ParentGeometryChoiceLow.lean:39`, `False`),
   `renewal_parameters` (`:68`, `False`), `tilt_step` (`PacketStageLowPropagation.lean:112`, `False`),
   `joinedNext_initial_increment` (`PacketJoinedSuccessor.lean:183`, `False`).
   These are `⟨rfl,rfl⟩`-style *witnesses* that the `le_rfl` proofs in the successors are honest; their
   being outside the cone is expected (the successors use the defeq directly, not the lemma), but a
   reviewer should not mistake `in_cone=False` for "unused idea". *What would settle it:* nothing to
   fix in the artifact; it is a note about reading CONE.csv.
5. **13 dead `*NoOptions.lean` / `*Investigation.lean` files ship in the repo**, all with
   `in_import_closure=False` (e.g. `ParentGeometryForwardChoiceNoOptions.lean`,
   `NavierStokes/CorrectionInitializationNoOptions.lean` with 393 decls).
   *Question:* are they byte-equivalent to the live files modulo names? For the two I diffed
   (`BaseInductionStage`, `ParentGeometryForwardChoice`) yes. *What would settle it:* diff the
   remaining 11; any *semantic* divergence would mean the shipped file differs from the one the
   heartbeat measurements were taken on.

## Residue — what I could not check

* **No build.** Nothing here is a claim that the files compile, that the `rfl`/`le_rfl`/`change` steps
  actually close their goals, or that `nlinarith only [...]` succeeds. I checked that each proof step is
  *the kind of step that could* close the stated goal, and that the definitional identities the `rfl`s
  need really hold by unfolding the cited definitions.
* **Depth cut at the PDE layer.** `forward_uniform_child_label_bounds`,
  `S.forwardChild`/`joinedChild`, `forwardChildLowBounds`, `exactForwardPacket_whole_horizon_low_bounds`,
  and `A.forwardGeometryFrame` were read only at their *interfaces* (statement + which hypotheses the
  callers discharge). Escalations 1-2 are exactly this gap.
* **Axiom census.** I could not run `#print axioms` for `forwardNext`/`joinedNext`. The `NoOptions`
  docstring asserts the standard three for `firstStage`; unverified by me.
* **`Guards`/`ForwardGuards` field-by-field derivation.** I read the structures
  (`PacketSourceGeometryData.lean:82-118`, `PacketForwardGeometryData.lean:23-44`) and the two
  constructor sites, but I traced only `compression_guard` and `small` back to their scale inequalities;
  the other ~15 guard fields (`history_layer`, `history_strain`, `activation_error`, `short_extension`,
  `target_le_horizon`, …) I confirmed are *supplied as arguments* by `geometryGuardsOfStage`
  (`PacketStageGuards.lean:49-69`) from named stage facts, without re-deriving each one.
* **Numerical plausibility.** Whether `shear_separation`, `activation_small` and the six `SmallSeries`
  bounds are *simultaneously* satisfiable at the chosen `J, D, X, δ` is an arithmetic question about
  `exists_scales`, already covered by `workers/euler-packet.md` §B; I did not re-audit it.
