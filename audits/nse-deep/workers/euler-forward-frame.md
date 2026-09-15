# Worker report — `euler-forward-frame`: the two unread parent-geometry declarations

Repo under audit: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ `f9e8bc5`).
Read-only; nothing under that path was modified. **No Mathlib build on this box — source-level reading
only.** Every claim carries `file:line`.

Assignment: close the two declarations `euler-stage-fields` left unread —
`forward_uniform_child_label_bounds` and `forwardGeometryFrame` — plus their dependency cone.

## Verdict in one line

Both declarations are honest and both are **structurally** protected against the `δ = 0` /
zero-amplitude degeneracy — but the protection sits in **different places**, and one of them is *not*
inside `forwardGeometryFrame`. `forward_uniform_child_label_bounds` carries `hδ : 0 < δ` **as data**
(it is an explicit term argument to `forwardInitializedCorrectionData`), so `δ = 0` is unreachable
there. `forwardGeometryFrame` (`Euler/ParentPacketPrimaryCenter.lean:73`) carries `hδ : 0 < δ` and
`hη : η ≠ 0` but **no `0 < α`** — so *as a def in isolation* it admits `α = 0`, producing a
`ParentFrame` with `c = 0` and hence `shear = 0`, whose `remainder_bound` then degenerates to the
content-free "the strain increment is ≤ error". That escape is closed one layer up, and closed
**more sharply than by `0 < α`**, by `Guards.shear_pos : 0 < P.shear`
(`Euler/PacketSourceGeometryData.lean:98`): since `shear = primaryShear c m v τ = c*(‖m τ‖*‖v τ‖)`
(`Euler/PacketFrameCoefficients.lean:122`), `0 < P.shear` simultaneously forces `α ≠ 0`, `δ > 0`
(sign), `sourceNormal m τ ≠ 0` and `sourceVelocity … τ ≠ 0`. See §B.
Kernel exposure in this scope is **nil**: 0 `decide`, 0 `native_decide`, 0 `Nat.pow/div/mod/gcd`,
0 `termination_by`, 0 `WellFounded`/`Acc.`, 0 `.rec`, 0 `sorry`, 0 metaprogramming, 0 `attribute`.
The only Nat numeral the kernel must touch is `10*(6+2) ⇒ 80` (§D).

## Scope

| file | lines | decls (CONE.csv) | in_cone | read |
|---|---|---|---|---|
| `Euler/PacketForwardUniformChild.lean` | 122 | 1 | 1 | full, line by line |
| `Euler/ParentPacketPrimaryCenter.lean` | 111 | 4 | 4 | full, line by line |
| `Euler/ParentPacketPhysicalFrame.lean` | 85 | 3 | 3 | full, line by line |
| `Euler/ParentPacketGeometryFrame.lean` | 177 | 13 | 13 | full, line by line |
| `Euler/PacketForwardUniformFlow.lean` | 235 | 1 | 1 | full, line by line |
| `Euler/PhysicalChildSourceBound.lean` | 81 | 2 | 2 | full, line by line |
| `Euler/ParentPacketLabelData.lean` | 115 | 8 | 8 | full, line by line |
| `Euler/ParentUniformForwardChild.lean` | 81 | 1 | 1 | full, line by line |
| `Euler/ParentStateGeometry.lean` | 89 | 6 | 6 | full (consumer) |
| `Euler/PacketSourceGeometryData.lean` | — | 22 | 22 | `:19-120` only (structures `ParentFrame`, `Guards`) |

**10 files, 61 declarations in CONE.csv, all `in_cone=True` and `in_import_closure=True`.**
9 of the 10 read line by line in full; `PacketSourceGeometryData.lean` read only through `:120`
(the two structures + `ParentFrame` namespace), because `euler-stage-fields` already covered it.

Also read at their statements only (interface reads, cited below):
`Euler/EulerProof.lean:11751-11835` (`profile`, `profile_deriv`, `profile_deriv_zero`),
`Euler/PacketPrimaryShearIdentity.lean:62-70` (`rankOne_normalized`),
`Euler/PacketFrameCoefficients.lean:122` (`primaryShear`),
`Euler/PacketNormalizedPrimary.lean:19` (`unit`),
`Euler/MeanClassicalWordBounds.lean:130-140` (`classicalBlockSize`),
`Euler/PacketParentLabelBudgets.lean:20-22` (`HasLabelBound`),
`Euler/SmoothL2Gevrey.lean:19-38` (`HasJetBound`, `.mono`),
`Euler/SmoothL2GevreyCalculus.lean:20-28` (`HasSupBound`, `.mono`),
`Euler/PacketUniversalFrequency.lean` (all, 3 decls),
`Euler/SobolevSourceExponent.lean:14` (`fixedCost`), `Euler/PacketSourceFrequency.lean:13` (`theta`),
`Euler/PacketForwardExactFields.lean:20-60` (`forwardInitializedExactPhysicalVelocity` + `_eq`).
Prior report read first: `workers/euler-stage-fields.md` (40 kB, in full).

## A. What each declaration states and what its proof establishes

### A.1 `forward_uniform_child_label_bounds` — `Euler/PacketForwardUniformChild.lean:57`

**Statement (paraphrase).** Given a mean-packet provider `M`, a transverse packet `D` with `M.T = D.T`,
a spike width `δ` with `0 < δ ≤ 1`, an amplitude `α > 0`, a label direction `ξ`, budgets
`L / NB / LM`, a radius primitive `W`, a frequency `k` satisfying nine explicit thresholds
(`4 ≤ k`, `69 ≤ k`, `64 ≤ expansion k`, `1 ≤ log k`, `16 ≤ k^(1/4)`, `delta (expansion k) ≤ k^(-3)`,
`max 71 √(2/period+2·period) ≤ k^(1/24)`, `2+45·embeddingCost ≤ k`, `fixedCost q ≤ k`), the parent's
flow/inverse pair `X, Y` with `fderiv (X t) = D.F.field t`, `det = 1`, and parent label data
`Dp, Vp, Wp` with a single Gevrey constant `K` (`1 ≤ K ≤ k`) and `ell⁻¹ ≤ k^(3/4)` — **there exist**
a truncation witness `hn`, a drift-correction budget `Q`, graph-flow data `G` and a per-time child
particle-field record `E` such that:

1. `Q.delta` and `Q.initialRadius` are *pinned* to the externally defined `delta (expansion k)` and
   `initialRadius …` (`:65-70`);
2. `G.A`, `G.A₁` are *pinned* to `Q.liftedPacketCoefficient …` / `…DerivativeCoefficient …` (`:71-77`);
3. the graph constraint holds identically: `∀ t z, graphConstraint k D.m₀ (G.A.field t z) = 0` (`:78`);
4. the three Gevrey towers satisfy `weightedNorm … ≤ weightSize W * delta (expansion k)` for all
   `s, n` with `n+6 ≤ s` and all `t` (`:79-83`);
5. **the shear/pressure error**: for *all* `t ∈ Icc 0 D.T` and *all* `x : Space`,
   ```
   ‖fderiv ℝ (forwardInitializedExactPhysicalVelocity … Q t (Y t)) x −
     (α*deriv (profile δ) (k*⟪D.m₀, Y t x⟫)) • rankOne ℝ (canonicalVelocity D ξ t (Y t x))
                                                           (D.normal.field t (Y t x))‖ ≤ k^(-(1/4:ℝ))
   ```
   plus the matching Hessian bound for the pressure gradient (`:84-95`);
6. `E t`'s seven fields are *pinned* by equations to `Dp t, Vp t, Wp t`,
   `G.displacementField k D.m₀ ell hell t`, `G.velocityField …`, `G.accelerationFieldL2 …`, and
   `(flowData … ).forward t` (`:96-98` region, `:96`→`:98`);
7. **the child label bound**: `∀ t n`,
   `blockSize(childDisplacement) + blockSize(childVelocity) + blockSize(childAcceleration)
    ≤ (k^(10*(q+2)))^(n+1) * (n!)^2` (`:99-103`);
8. `∀ t x, ‖(G.displacementField k D.m₀ ell hell t).field x‖ ≤ k^(-(1/4:ℝ))` (`:104-105`).

**What the proof does (`:106-121`).** It is a two-step composition, not a construction:
* `obtain ⟨hn,Q,G,hδQ,hρQ,hA,hA1,hgraph,hweighted,herror,hfields⟩ := forward_uniform_flow_and_shear …`
  (`:106-108` → `Euler/PacketForwardUniformFlow.lean:50`). Items 1-5 are *literally* the first seven
  conjuncts of that theorem, handed through unchanged (`refine ⟨hn,Q,G,E,hδQ,hρQ,hA,hA1,hgraph,
  hweighted,herror,hmatch,hlabel,?_⟩`, `:117`). So this declaration does **not** prove the PDE
  estimate; it *transports* it and adds only items 6-8.
* `hcoarse` (`:109-116`): from `hfields` (the `HasJetBound`/`HasSupBound` block of
  `forward_uniform_flow_and_shear`, `PacketForwardUniformFlow.lean:83-93`, constants
  `k^(-(1/4:ℝ))`, `k^(1/4:ℝ)`, `ell⁻¹*k^(5/4:ℝ)`) it derives the coarser
  `HasJetBound k (k^2)` / `HasSupBound k (k^2)` via
  `EulerPhysicalChildFields.coarsen_graph_bounds` (`Euler/PhysicalChildSourceBound.lean:18`).
  The five `by convert … using 1 <;> norm_num` steps are pure exponent renaming
  (`-(1/2)+1/4 = -(1/4)`, `1+1/4 = 5/4`); note the third is `using 1; norm_num` (one goal) exactly
  because `coarsen_graph_bounds`'s third hypothesis already reads `k^(1/4:ℝ)` — an internal
  consistency check that passes.
* `obtain ⟨E,hmatch,hlabel⟩ := EulerPhysicalChildFields.exists_source_child_fields …` (`:115-116`),
  which is itself a thin wrapper: it `let E := data G k m hgraph …` and returns
  `⟨rfl,rfl,rfl,rfl,rfl,rfl,inner_eq_forward …⟩` for item 6 and
  `(E t).source_physical_label_bound q k hk hbig hcost hKk le_rfl le_rfl n` for item 7
  (`PhysicalChildSourceBound.lean:72-79`). So the label bound is proved in
  `Euler/ChildParticleSourceBound.lean` (**not read** — see §Residue).
* item 8 (`:118-121`): `simpa only [norm_iteratedFDeriv_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,
  one_pow,mul_one] using (hfields ell hell hell1 t).2.2.2.1 0 x`. I checked this is honest:
  `HasSupBound f C R := ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*R^n*(n!)^2`
  (`SmoothL2GevreyCalculus.lean:20`), so at `n = 0` it is `‖f x‖ ≤ C*1*1`, and
  `norm_iteratedFDeriv_zero` is the Mathlib identity `‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖`. No
  differentiability is needed at `n = 0`, so there is **no junk-value exposure** in this step.

**Verdict: OK** for what it claims, with the load-bearing content imported. Two honesty notes:
* The name says "label bounds", and item 7 *is* the label bound; but items 1-5 (the whole PDE
  content) are also in the statement and are entirely inherited. A reader who audits this file
  believing it proves the shear error would be misled by the *file*, not by the theorem.
* The coarsening at `:109-116` **throws away the smallness** `k^(-1/4)` and replaces it with `k`
  before the child estimate, so the child's Gevrey constant is `k^(10(q+2))` — at `q = 6`, `k^80`.
  This is not a cheat: the smallness the geometry actually needs is retained separately as item 8
  (`‖displacementField‖ ≤ k^(-1/4)`). It *is* the reason the frequency must grow like `k ↦ k^80`
  per stage, which is exactly the `hKk : L.K ≤ k` requirement in the consumer.

### A.2 `forwardGeometryFrame` — `Euler/ParentPacketPrimaryCenter.lean:73`

**Statement.** A `def`, not a theorem: it builds
`ParentFrame (N.transverseData mNew hmNew RNew SNew hSNew) τ` from an old parent `G`, a new parent
`N` with `hTime : N.T = G.T`, the two velocity laws
`hGvelocity : G.velocity.field t x = u t (G.position t x)` and
`hNvelocity : N.velocity.field t x = u t (N.position t x) + w t (N.position t x)`
(`:57-59`), oddness of both displacement fields (`:60-61`), differentiability of `u` and `w`
(`:55-56`), a label vector `η ≠ 0`, quantitative parent inputs
`CM, CH, K, error` with `0 ≤ CM`, `1 ≤ K`, `0 ≤ error`, `CM ≤ K`, `CM^2+CH ≤ K^2`,
`‖G.centerStrain t‖ ≤ CM` and `‖G.centerCurvature t‖ ≤ CH` on `Icc τ N.T` (`:67-70`), a family
`Y` with `hY : ∀ t, Y t 0 = 0` (`:71`), `δ` with `0 < δ`, and the **one** genuinely new input:
```lean
(hsource20 : ∀ t : Icc (0 : ℝ) G.T, τ ≤ (t : ℝ) →
    ‖fderiv ℝ (w t) 0-(α*deriv (profile δ) (k*⟪m,Y t 0⟫_ℝ)) •
      rankOne ℝ (…canonicalVelocity (G.transverseData m hm R S hS) η t (Y t 0))
        ((G.transverseData m hm R S hS).normal.field t (Y t 0))‖ ≤ error)
```
i.e. *at the spatial centre 0, at every time `t ≥ τ`*, the velocity increment's centre gradient is
within `error` of the packet's primary rank-one term. This is exactly conjunct 5 of §A.1 specialised
to `x = 0`.

**What the proof does (`:78-84`).**
```lean
  apply G.geometryFrameOfPhysicalUpdate N hTime u w hu hw hGvelocity hNvelocity hGodd hNodd
    m hm R S hS mNew hmNew RNew SNew hSNew τ hτ η hη (α/δ) CM CH K error hCM hK he hMK hHK hM hH
  intro t ht
  have htG : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,by simpa only [hTime] using ht.2⟩
  have h := hsource20 ⟨t,htG⟩ ht.1
  rw [G.forward_primary_center_term m hm R S hS η δ hδ α k ⟨t,htG⟩ (Y ⟨t,htG⟩) (hY _)] at h
  exact h
```
Three things happen and I checked each:
1. **`c := α/δ`.** The abstract factory
   `geometryFrameOfPhysicalUpdate` (`Euler/ParentPacketPhysicalFrame.lean:70`) wants a scalar `c` and
   `hpacket : ∀ t ∈ Icc τ N.T, ‖fderiv (w t) 0 − c • rankOne (G.sourceVelocity …) (G.sourceNormal m t)‖
   ≤ error`. `forwardGeometryFrame` supplies `c = α/δ`.
2. **`forward_primary_center_term` (`:23`) converts `hsource20`'s packet form into `hpacket`'s
   source form**, and this is where `0 < δ` is spent:
   ```lean
   rw [hY]
   simp only [inner_zero_right,mul_zero,profile_deriv_zero δ hδ,
     …canonicalVelocity,innerCutoff_zero,one_smul,div_eq_mul_inv]
   rw [G.source_normal_eq m hm R S hS]
   rfl
   ```
   `Y 0 = 0 ⇒ ⟪m,0⟫ = 0 ⇒ k*0 = 0`, then `profile_deriv_zero δ hδ : deriv (profile δ) 0 = δ⁻¹`
   (`Euler/EulerProof.lean:11818`, proved from `profile_deriv` at `t=0`:
   `((1+δ)·cos 0 − 1)/denominator δ 0 = δ/δ² = δ⁻¹`, `denominator δ 0 = δ²` at `:11820`).
   So the packet coefficient `α·deriv (profile δ) 0` becomes literally `α·δ⁻¹ = α/δ`;
   `innerCutoff_zero` kills the cutoff (value `1` at the centre) and `source_normal_eq`
   (`Euler/ParentPacketGeometryFrame.lean:65`) identifies the transverse normal at `0` with
   `G.sourceNormal m t`. The final `rfl` is `uncutVelocity … 0 ≡ G.sourceVelocity …`, true by the
   definition at `ParentPacketGeometryFrame.lean:61`.
3. **The quantifier bridge is in the safe direction.** `hsource20` is over `Icc 0 G.T ∩ {t ≥ τ}`;
   `hpacket` is needed on `Icc τ N.T`. With `hτ : 0 ≤ τ` and `hTime : N.T = G.T` the latter is a
   *subset* of the former, and the `htG` line is exactly that inclusion. **This answers escalation 2
   of `euler-stage-fields` in the good direction:** the estimate is consumed at *every* time in
   `Icc τ N.T`, not only at `t = 0`. The `0` in `fderiv ℝ (w t) 0` is the *spatial* centre, not a
   time. `hY : ∀ t, Y t 0 = 0` is likewise uniform in `t`, and its consumer
   `ParentStateGeometry.lean:68` discharges it with `S.normalized_inverse_zero` (`:35`), proved from
   oddness of the inverse, not assumed.

**What the resulting record actually asserts.** All the `ParentFrame` fields
(`Euler/PacketSourceGeometryData.lean:25-47`) are discharged in
`geometryFrameOfCenterExpansion` (`Euler/ParentPacketGeometryFrame.lean:130-179`) from *proved*
lemmas about the old parent's own trajectories: `ray_equation` ← `sourceNormal_equation` (`:31`),
`velocity_equation` ← `sourceVelocity_equation` (`:78`), `ray_nonzero` ← `sourceNormal_ne_zero`
(`:44`, from `inverse_left`), `velocity_nonzero` ← `sourceVelocity_ne_zero` (`:88`, needs `hη`),
`tangent` ← `sourceVelocity_tangent` (`:92`), `B_bound`/`B₁_bound` ← `hM`/`hH` +
`centerStrainDerivative_bound`. The single interesting field is
```lean
remainder_bound : ∀ t ∈ Icc τ D.T,
  ‖D.M.field (D.clamp t) 0-B t-primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t))‖ ≤ error
```
proved at `:167-179` by: `hupdate ⟨t,htD⟩` (= `center_update_of_odd`,
`ParentPacketPhysicalFrame.lean:44`, `N.strain.field t 0 = G.centerStrain t + fderiv (w t) 0`,
itself proved from the two `strain_physical` identities at `x = 0` and `position_zero_of_odd`, with
`fderiv_fun_add (hu tg 0) (hw t 0)` — **both differentiability hypotheses genuinely supplied, so no
`fderiv` junk-value exploitation**), then `add_sub_cancel_left`, then
`rankOne_normalized c v m hv hn` (`Euler/PacketPrimaryShearIdentity.lean:62`,
`c • rankOne v m = (c*(‖m‖*‖v‖)) • rankOne (unit v) (unit m)`, needing `v ≠ 0`, `m ≠ 0` — supplied),
reducing the goal exactly to `hpacket t ht`. **No slack is invented and none is lost.**

**Verdict: OK** as a def, with the caveat in §B.

### A.3 supporting declarations examined

| declaration | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `forward_primary_center_term` | `ParentPacketPrimaryCenter.lean:23` | packet rank-one term at centre `= (α/δ) • rankOne(sourceVelocity, sourceNormal)` | `profile_deriv_zero` + `innerCutoff_zero` + `source_normal_eq` + `rfl` | OK |
| `joined_primary_center_term` | `:36` | same for the joined branch, with `η := B.coefficients.labelCoordinate 0 ξ …` | same, plus `erw [canonicalVelocity_eq_cutoff_uncut]` and `joined_sourceVelocity` | OK |
| `joinedGeometryFrame` | `:89` | joined analogue of `forwardGeometryFrame` | line-for-line parallel; non-zeroness from `joined_initialCoordinate_ne_zero` instead of `hη` | OK |
| `geometryFrameOfPhysicalUpdate` | `ParentPacketPhysicalFrame.lean:70` | abstract old/new-parent frame factory from `hpacket` in *source* form | delegates to `geometryFrameOfCenterExpansion`, supplying `center_update_of_odd` as `hupdate` | OK |
| `center_update_of_odd` | `:44` | `N.strain.field t 0 = G.centerStrain t + fderiv (w t) 0` | two `strain_physical` at `x = 0`, `position_zero_of_odd`, `fderiv_fun_add` with both diff. hyps | OK |
| `position_zero_of_odd` | `:22` | odd displacement ⇒ `G.position t 0 = 0` | coordinatewise `f 0 = -f 0 ⇒ f 0 = 0` by `linarith` | OK |
| `geometryFrameOfCenterExpansion` | `ParentPacketGeometryFrame.lean:130` | the `ParentFrame` record itself | 15 fields, each from a named proved lemma; see §A.2 | OK |
| `sourceNormal_ne_zero` | `:44` | `m ≠ 0 ⇒ sourceNormal m t ≠ 0` | `inverse_left` gives `inverse ∘ frame = id`, adjoint it | OK |
| `joined_initialCoordinate_ne_zero` | `:103` | `ξ ≠ 0 ⇒ labelCoordinate 0 ξ ≠ 0` | contrapositive via `uncutVelocity_ne_zero` and `uncutVelocity_initial` (`0 ↦ 0`) | OK |
| `joined_sourceVelocity` | `:98` | forward and joined propagators coincide after inserting the coordinate | `rfl` — the two `uncutVelocity`s are the *same* definition | OK |
| `forward_uniform_flow_and_shear` | `PacketForwardUniformFlow.lean:50` | the real PDE estimate (see §A.1 items 1-5 + the Jet/Sup block) | 140 lines of budget plumbing ending in `forwardInitializedExactPhysicalVelocity_global_gradient_error` + `physical_gradient_hessian_of_weighted` + `physical_error_le_inverse_quarter`; also `graphConstraint_transport` for the constraint | UNCLEAR (depth) |
| `coarsen_graph_bounds` | `PhysicalChildSourceBound.lean:18` | weakens Jet/Sup bounds `(k^(-1/4), ell⁻¹k^(5/4)) → (k, k^2)` | `rpow_le_rpow_of_exponent_le` + `hi : ell⁻¹ ≤ k^(3/4)` and `3/4+5/4 = 2`; `.mono` | OK |
| `exists_source_child_fields` | `:53` | ∃ child field record with the seven pinnings + label bound `(k^(10(q+2)))^(n+1)(n!)^2` | `let E := data G …`; pinnings are `rfl`; bound is `(E t).source_physical_label_bound` | OK (delegates) |
| `LabelData.child` | `ParentPacketLabelData.lean:81` | build the child's `LabelData` with constant `K` | splits the *sum* bound into three per-field bounds using `block_nonneg` + `linarith`; matches via `child_fields_match` | OK |
| `block_nonneg` | `:65` | `0 ≤ classicalBlockSize …` | `unfold; positivity` (sum of norms) | OK |
| `LabelData.forward_uniform_child` | `ParentUniformForwardChild.lean:36` | the consumer: ∃ next parent + `LC : LabelData (A.child …)` with `LC.K = k^80` | instantiates §A.1 at `q := 6`, feeds `hlabel` into `LabelData.child (k^80)` | OK |
| `SmoothState.forwardRenewal` | `ParentStateGeometry.lean:53` | the consumer of `forwardGeometryFrame` on two actual Euler states | supplies `u := S.evolution.velocity`, `w := S.velocityIncrement T`, smoothness from `velocity_smooth`, `hY` from `normalized_inverse_zero` | OK |
| `UniversalFrequency` + `universal_frequency_eventually` | `PacketUniversalFrequency.lean:15,25` | the nine `k`-thresholds hold eventually | `filter_upwards` / `eventually_ge_atTop` — **no numeral is ever evaluated** | OK |

## B. Does either declaration admit a degenerate instance?

Checked four escapes.

| escape | `forward_uniform_child_label_bounds` | `forwardGeometryFrame` |
|---|---|---|
| `δ = 0` | **No.** `hδ : 0 < δ` is a *term* argument threaded into `forwardInitializedCorrectionData M D hTime δ hδ ξ hs α …` (`:62`, `:73`, `:87`) and into `forwardInitializedNormalizedField … δ hδ …`. It is not merely `include`d; the statement does not even typecheck without it. | **No.** `hδ` is consumed by `forward_primary_center_term … δ hδ …` (`:82`), which needs `profile_deriv_zero δ hδ`. |
| zero amplitude `α = 0` | **No.** `hα : 0 < α` is in the variable block (`:29`) and `include`d (`:54`). | **YES — the def alone allows `α = 0`.** `ParentPacketPrimaryCenter.lean:71` declares `(δ : ℝ) (hδ : 0 < δ) (α k : ℝ)` — no `0 < α`. Then `c = α/δ = 0`, `shear = primaryShear 0 m v τ = 0*(‖m τ‖‖v τ‖) = 0`, and `remainder_bound` degenerates to `‖new centre strain − old centre strain‖ ≤ error`, which says nothing about amplification. **Closed one layer up** by `Guards.shear_pos : 0 < P.shear` (`PacketSourceGeometryData.lean:98`) — see below. |
| empty label set / `η = 0` | **No.** the label data is `Dp, Vp, Wp` with `1 ≤ K` and `HasLabelBound K` for each, and the conclusion's bound is over `∀ n` including `n = 0`; there is no index set that can be empty. | **No.** `hη : η ≠ 0` (`:73`) is required and is spent on `velocity_nonzero` via `sourceVelocity_ne_zero` (`ParentPacketGeometryFrame.lean:88`) and on `rankOne_normalized`'s `hv`. |
| child = parent | **No.** the child fields are pinned to `G.displacementField k m ell hell t` etc., built from the *new* graph-flow data `G`, and `G.A` is pinned to `Q.liftedPacketCoefficient …` — a new packet, not `Dp/Vp/Wp`. | **No.** `N` and `G` are separate `Parent`s and `hNvelocity` forces `N.velocity = u∘N.position + w∘N.position`; taking `w = 0` would force `error ≥ ‖(α/δ)•rankOne(v,m)‖ > 0`, i.e. it is *excluded by* `hsource20`, not permitted by it (given `α ≠ 0`). |

**The precise anti-degeneracy statement.** `shear = P.c*(‖P.m τ‖*‖P.v τ‖)` with
`P.c = α/δ`, `P.m = G.sourceNormal m`, `P.v = G.sourceVelocity m hm R S hS η`
(`PacketFrameCoefficients.lean:122`, `ParentPacketGeometryFrame.lean:130-136`,
`PacketSourceGeometryData.lean:55`). Hence `Guards.shear_pos : 0 < P.shear`
(`PacketSourceGeometryData.lean:98`) **is strictly stronger than `0 < α`**: it forces
`α ≠ 0`, forces `α/δ > 0` (so `δ > 0` in the sign sense too), and forces
`sourceNormal m τ ≠ 0` and `sourceVelocity … τ ≠ 0`. Three further `Guards` fields spend it:
`history_layer : 1 ≤ P.shear*τ` (`:113`), `activation_error : P.G+P.error ≤ ζ*P.shear` (`:118`),
`terminalBound _ = 8*(…)/P.shear` (`:62`). So the whole geometric induction is quantitatively
divided by `shear`, and a `shear = 0` frame cannot be fed into it.

**Conclusion for B.** The `0 < δ` protection identified by `euler-stage-fields` is preserved by both
declarations. `forward_uniform_child_label_bounds` additionally carries `0 < α`.
`forwardGeometryFrame` does **not** carry `0 < α`, and therefore *can* be instantiated to build a
degenerate `shear = 0` frame — but such a frame is unusable, because every consumer path goes through
`Guards`, whose `shear_pos` field rejects it. I record this as **SUSPICIOUS-but-benign / API hygiene**:
the def's type is weaker than its intended contract, so the non-degeneracy claim must be re-verified
at every call site rather than read off the frame's type. Both call sites I found
(`ParentStateGeometry.lean:62`, `:81`) inherit `α` from a caller that does carry `0 < α`
(via `ForwardGuards`/`Guards`, `euler-stage-fields` §A step 3), so nothing is actually broken here.

## C. Are the label bounds "uniform"? Quantifier order and consumers

**What is uniform.** `HasLabelBound K A := ∀ n, classicalBlockSize direction 6 A.toLp _ n
≤ K^(n+1)*(n!)^2` (`Euler/PacketParentLabelBudgets.lean:20`). The conclusion of
`forward_uniform_child_label_bounds` item 7 is
`∀ t n, (three block sizes summed) ≤ (k^(10*(q+2)))^(n+1)*(n!)^2`. The constant
`k^(10*(q+2))` is:
* **uniform in time** `t ∈ Icc 0 D.T` — genuinely; `t` is bound *inside* the `∃ E`, and the bound's
  right-hand side does not mention `t`. Since `E` is chosen before `t` and the bound is `t`-free,
  this is a single constant valid on the whole horizon. ✓
* **uniform in the block index `n`** — the RHS is one closed formula in `n` with a single base. ✓
* **uniform in the three fields** — one bound for `displacement + velocity + acceleration` *summed*,
  which `LabelData.child` (`ParentPacketLabelData.lean:101-112`) then splits into three separate
  `HasLabelBound K` facts using `block_nonneg` and `linarith`. Sound (nonneg summands). ✓
* **NOT uniform over children / stages.** There is exactly *one* child here: one `k`, one `m`, one
  `ell`, one `nextEll`. The name's "uniform" does **not** mean "one constant for all children". Read
  in context (docstrings at `PacketForwardUniformChild.lean:3-4`,
  `PacketForwardUniformFlow.lean:5-7`) and against the hypothesis
  `hfrequency : uniformConstant * W^uniformPower ≤ smallPower k`, "uniform" qualifies the *source
  cost comparison*: a single parent-independent constant/power `uniformConstant`, `uniformPower`
  absorbs all the frequency losses. That is a different and weaker claim than cross-child
  uniformity. **Verdict: the name is defensible but easy to over-read — UNCLEAR (naming).**
  Cross-stage control is *not* uniformity: it is the per-stage hypothesis
  `hKk : L.K ≤ k` (`ParentUniformForwardChild.lean:32`), i.e. the *previous* stage's constant must be
  below the *new* frequency, together with `LC.K = k^80`. So the constants grow like
  `k ↦ k^80` and the frequencies must outrun them — the opposite of a uniform bound.

**Quantifier order vs what consumers need.**
1. `LabelData.forward_uniform_child` (`Euler/ParentUniformForwardChild.lean:36`, called at `:63-73`
   with `q := 6`) needs `hb : ∀ t n, … ≤ K^(n+1)*(n!)^2` for `LabelData.child`
   (`ParentPacketLabelData.lean:82`). Order `∀ t n` — **exact match, no reordering, no `choice`**. ✓
2. `LabelData` itself (`ParentPacketLabelData.lean:26-28`) needs
   `∀ t, HasLabelBound K (displacement t)` = `∀ t, ∀ n, …`. Same order. ✓
3. `LabelData.normalBudget` / `meanBudget` (`:46`, `:56`) consume `L.displacement_bound` etc. with
   the same `∀ t` outer, `∀ n` inner shape. ✓
4. The downstream consumer of `LC.K = k^80` is `exists_geometryForwardChoice`
   (`Euler/ParentGeometryForwardChoice.lean:96`, per `euler-stage-fields` §A step 4) and then the
   next stage's `hKk`. ✓
5. Consumers of `forwardGeometryFrame`: `SmoothState.forwardRenewal`
   (`Euler/ParentStateGeometry.lean:53`, only call site) → then the geometry-choice layer
   (`ParentGeometryChoiceRenewal.lean`, `ParentGeometryForwardChoice.lean`) → `Stage.forwardNextFrame`.
   Its `hsource` (`:54-60`) has exactly `forwardGeometryFrame`'s `∀ t, τ ≤ t → …` order. ✓

**No quantifier-order defect found.** In particular the `error` in `forwardGeometryFrame` is chosen
*before* `t` (it is a plain variable at `ParentPacketPrimaryCenter.lean:69`), which is the strong
reading and the one the `Guards.activation_error : P.G+P.error ≤ ζ*P.shear` inequality needs.

## D. Kernel-risk assessment

Grep over all 10 scope files (`grep -c -E` per pattern, counts are per-file matches):

| vector | pattern | count | note |
|---|---|---|---|
| (2) | `decide` | **0** | — |
| (2) | `native_decide` | **0** | — |
| (2) | `Nat.pow` / `Nat.div` / `Nat.mod` / `Nat.gcd` | **0** | — |
| (2) | `norm_num` | **9** | all tiny: `PacketForwardUniformChild.lean:110-114` (exponent renaming `-(1/2)+1/4`, `1+1/4`), `PhysicalChildSourceBound.lean:30,32,37` (`-(1/2)+1/4 ≤ 1`, `1/4 ≤ 1`, `3/4+(1+1/4) = 2`), `PacketForwardUniformFlow.lean:149` (`norm_num [theta]`, `theta = 1/1000000`, `PacketSourceFrequency.lean:13`). Largest numeral seen: `1000000`. No certificate the kernel must recompute over a big literal. |
| (1) | `.rec` / `Acc.` / `WellFounded` / `termination_by` | **0** each | no recursor reduction, no well-founded unfolding in scope |
| (1) | `rfl` | **33** (lines: 3+6+10+2+7+5) | see below |
| (1) | `simp only` | 18 | all with explicit lemma lists (`simp only`); no bare `simp` closing a main goal except `by simp` for `(∞ : ℕ∞)`-style side goals at `ParentStateGeometry.lean:64-65` |
| (3) | `macro`/`elab`/`syntax`/`set_option`/`axiom`/`unsafe`/`partial`/`sorry`/`attribute` | **0** each | **no metaprogramming, and no `attribute [local irreducible]` in this scope** (unlike the stage files) |
| — | `classical` | 1 | `PacketForwardUniformFlow.lean:94` — the tactic, i.e. `Classical.propDecidable` as a local instance; used only for `let`-definitions, not for a `decide` |

**Does the kernel have to perform a risky computation? Concretely, no.**

* **(2) numerals.** The *only* Nat arithmetic the kernel must actually perform in this scope is
  `10*(6+2) ⇒ 80`: `forward_uniform_child_label_bounds` concludes with base `k^(10*(q+2))`
  (`PacketForwardUniformChild.lean:101`), the consumer instantiates `q := 6`
  (`ParentUniformForwardChild.lean:72`) and passes the resulting `hlabel` where
  `K := k^80` is expected (`:78`). Unifying `k^(10*(6+2))` with `k^80` needs
  `Nat.add 6 2` then `Nat.mul 10 8` on one- and two-digit literals. GMP is invoked; the operands are
  ≤ 80. Zero risk.
  Also: `Nat.factorial_zero` (`0! = 1`) and `pow_zero` are used as rewrite lemmas at
  `PacketForwardUniformChild.lean:119-120`, i.e. proof terms, not iota chains.
  Everything that *looks* big is symbolic: `k^80`, `k^2`, `(n.factorial : ℝ)^2`, `k^(-(1/4:ℝ))`,
  `k^(3/4:ℝ)`, `expansion k`, `truncation k` all sit over an **opaque real `k`** or a **variable
  `n : ℕ`**, and `fixedCost 6 = (2:ℝ)^6*∑ j ∈ range 7, (j!)^2` (`SobolevSourceExponent.lean:14`,
  numerically ≈ 3.4·10^7) is **never evaluated** — it appears only on the left of the hypothesis
  `derivative_bound : fixedCost 6 ≤ k` (`PacketUniversalFrequency.lean:24`), discharged by
  `eventually_ge_atTop (fixedCost 6)` (`:29`). This large-`k`-asymptotics pattern is what keeps the
  bignum exposure at zero, and I checked it is used consistently: none of the nine
  `UniversalFrequency` fields is proved by computation.
* **(1) recursors / inductives.** No `.rec`, no `Acc.rec`, no `termination_by`, no `WellFounded` in
  scope. The `rfl`/`erw` steps that the kernel must check are **structure-projection and
  `Subtype`/`Icc` coercion reductions**, not recursor reductions on recursive data:
  `ParentPacketGeometryFrame.lean:70` (`source_normal_eq`, `(transverseData …).normal.field t 0 ≡
  (inverse.field t 0).adjoint m`), `:78` (`source_strain_eq`), `:98` (`joined_sourceVelocity`, two
  syntactically distinct `uncutVelocity` applications that are the same head symbol),
  `ParentPacketPrimaryCenter.lean:34` (final `rfl` of `forward_primary_center_term`),
  `PhysicalChildSourceBound.lean:77` (six `rfl`s for the field pinnings — these hold because
  `E := data G k m …` is a `let`, so the projections reduce by one iota step on a
  **non-recursive structure**), `ParentUniformForwardChild.lean:79` (`rfl` for `LC.K = k^80`).
  The deepest of these is `source_normal_eq`; it unfolds `transverseData`, a plain (non-recursive)
  structure constructor. Structure-eta is used implicitly; no large elimination, no indexed family.
* **(3) metaprogramming.** Zero, in all 10 files. Consistent with the repo-wide scan. `local notation`
  does not even appear in this scope.

**Cone status (CONE.csv, mark 4).** All **61** declarations in the 10 scope files have
`in_cone=True` **and** `in_import_closure=True`. In particular
`EulerPacketTerminalDatum.forward_uniform_child_label_bounds`
(`Euler/PacketForwardUniformChild.lean:57`, kind `theorem`) and
`EulerParentPacketFrames.Parent.forwardGeometryFrame`
(`Euler/ParentPacketPrimaryCenter.lean:73`, kind `def`) are both in the cone — so both are genuinely
load-bearing for the top-level claim, and neither is dead code. I did **not** write to
`audits/nse-deep/CONE.csv` (it is a shared aggregator that other workers append to); this section is
the mark.

## Escalations

Ranked. Escalation 2 of `euler-stage-fields` is **closed** by §A.2 item 3 (the estimate is used at
every `t ∈ Icc τ N.T`, and the `0` is the spatial centre) — I do not re-raise it.

1. **`(E t).source_physical_label_bound` — the child Gevrey label bound is still unread.**
   `Euler/PhysicalChildSourceBound.lean:79` discharges the whole label conclusion with one call to
   `(E t).source_physical_label_bound q k hk hbig hcost hKk le_rfl le_rfl n`, defined in
   `Euler/ChildParticleSourceBound.lean` (not in my scope).
   *Question for an expert:* does that lemma prove the composition estimate
   `parent labels (constant K) ∘ child graph flow (Jet/Sup bound (k,k²)) ⇒ (k^{10(q+2)})^{n+1}(n!)²`,
   with the two `le_rfl` arguments being `k ≤ k` and `k^2 ≤ k^2` — i.e. is the exponent `10(q+2)`
   *derived* from a Faà di Bruno / word-composition count, or *chosen* to make the arithmetic close?
   *What would settle it:* read `Euler/ChildParticleSourceBound.lean`'s `source_physical_label_bound`
   and check that the `10` and the `+2` come out of an inequality chain, and that the `(n!)^2`
   Gevrey-2 index is not silently upgraded.
2. **`forward_uniform_flow_and_shear` is still the only place the PDE estimate is proved**
   (`Euler/PacketForwardUniformFlow.lean:50`, 140 lines). I read it line by line and it is *budget
   plumbing*: the actual gradient error comes from
   `forwardInitializedExactPhysicalVelocity_global_gradient_error` (`:223`),
   `Q.physical_gradient_hessian_of_weighted` (`:210`) and
   `physical_error_le_inverse_quarter` (`:214-215`). Partial progress on
   `euler-stage-fields` escalation 1: `forwardInitializedExactPhysicalVelocity`
   (`Euler/PacketForwardExactFields.lean:34`) is **not** a bare ansatz — it is
   `k⁻¹ • D.F.field t (Y x) ((forwardInitializedExactPacket …).velocity.pointField t (cylinderGraph …))`,
   i.e. the Piola pushforward of `exactPacketOfResidual period Q (…ApproximationResidual…)`
   (`:44-52`), a residual-corrected object produced by the `AllOrderDriftCorrection.Budget Q`.
   *Question:* is `exactPacketOfResidual` the solution of a *contraction/Duhamel fixed point* for the
   Euler residual, or a formal series whose convergence is asserted?
   *What would settle it:* read `exactPacketOfResidual` and
   `EulerAllOrderDriftCorrection.Budget`'s fields, and check that the residual is driven to zero by a
   proved estimate rather than by a definitional truncation.
3. **`forwardGeometryFrame` has no `0 < α` in its type** (`Euler/ParentPacketPrimaryCenter.lean:71`,
   `:73`; same for `joinedGeometryFrame` at `:89`). See §B. This is not a hole in the current proof,
   but it means the frame's *type* does not certify non-degeneracy, and a reviewer must chase every
   call site.
   *Question:* is there any construction path that reaches a `ParentFrame` *without* passing through
   `Guards` (so without `shear_pos`)?
   *What would settle it:* enumerate every consumer of `ParentFrame` (grep `ParentFrame` in the Euler
   tree) and verify each one either builds a `Guards` or is itself only used to build one.
4. **`Guards.shear_pos` is where all the non-degeneracy actually lives**
   (`Euler/PacketSourceGeometryData.lean:98`), together with `coupling_lower : 1/2 ≤ P.a` (`:97`) and
   `compression_guard` (`:109`).
   *Question for an expert:* are `shear_pos`, `coupling_lower`, `sigma_small ≤ 1/4`,
   `epsilon_small ≤ 1`, `target_le_horizon`, `short_extension`, `small` and `compression_guard`
   *simultaneously* satisfiable for the realised `shear = (α/δ)·‖m‖·‖v‖`, given
   `a = normalizedCoupling`, `epsilon = √(a/shear)`, `horizon = a(T−τ)/epsilon`? Note
   `epsilon_small ≤ 1` plus `coupling_lower ≥ 1/2` forces `shear ≥ a ≥ 1/2`, while
   `horizon^40` appears in `small` — the margins are tight.
   *What would settle it:* the `exists_scales` arithmetic already audited in
   `workers/euler-packet.md` §B, re-instantiated at the *realised* `shear` rather than at a free
   variable.

## Residue — what I could not check

* **No build.** Nothing here asserts the files compile, that the six `rfl`s at
  `PhysicalChildSourceBound.lean:77` or the `rfl` at `ParentUniformForwardChild.lean:79` really close,
  or that the `convert … using 1 <;> norm_num` steps succeed. I checked each is *the kind of step that
  could* close the stated goal and that the definitional identities the `rfl`s need do hold by
  unfolding the cited definitions.
* **`Euler/ChildParticleSourceBound.lean` unread** (escalation 1) — the label-bound arithmetic and
  `EulerChildParticleFieldBounds.Data`'s `childDisplacement/childVelocity/childAcceleration` fields.
* **`Euler/PacketForwardInitializedFlowAndShear.lean` and the ~15 cost/budget lemmas** named inside
  `forward_uniform_flow_and_shear` (`forwardInitializedRadius_guards`, `forward_output_costs`,
  `forward_five_costs_bound`, `liftedAmplitude_small_of_costs`, `tailBase_frequency`,
  `data_field_bounds_explicit`, `data_sup_bounds_explicit`, …) read only as names + the inequality
  they are `.trans`'d into. Each is a place a wrong constant could hide; I verified only that the
  chains are type-plausible (`_ ≤ smallPower k` composed with `hout`/`hcomparison`).
* **`Icc τ N.T` non-emptiness.** I did not check that `τ < N.T` at the call sites, so I cannot rule
  out an instance where `Icc τ N.T = ∅` and `hM`/`hH`/`hpacket`/`remainder_bound` are all vacuous.
  `Guards` requires `hτ : 0 < τ` and `hτT : τ < D.T` (`PacketSourceGeometryData.lean:64`, `:77`) which
  would close it, but `forwardGeometryFrame` itself only has `hτ : 0 ≤ τ` and **no `τ < N.T`**. This
  is the same shape of gap as escalation 3 and is worth one grep by whoever picks that up.
* **Axiom census.** `#print axioms forward_uniform_child_label_bounds` not runnable.
