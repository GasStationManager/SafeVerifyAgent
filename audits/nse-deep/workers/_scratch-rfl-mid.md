# Bare-`rfl` audit, ranks 9-17 by statement length (worker: rfl-mid)

Repo audited READ-ONLY: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5).
No Mathlib build on this box: this is source-level reading (grep/python) only. All line numbers are
from the checked-out files; every claim below is re-checkable by `sed -n 'Np' <file>`.

## Global result for my 9 sites

**No kernel-risk site.** All 9 are *definitional restatements*: after delta-unfolding non-recursive
`def`s and taking projections of explicit structure literals (`where` / `{ x with ... }` / `⟨...⟩`),
the two sides become the *same term*. In particular, in my whole set I found:

* **zero** iota chains at closed numerals (no `f 7`-style forced unfolding, class (iv) never fires);
* **zero** recursive definitions on the reduction path (no `Nat.rec`, `Acc.rec`, `WellFounded.fix`);
* **zero** `decide` / `Nat.pow|div|mod|beq|ble` / big literals on the reduction path;
* **zero** `Fin`/`Matrix.cons`/`List.get` *literal index resolution* (class (v)): `![a,b,c]` vectors
  do appear (`HarmonicResidual.stateMean`, `contextBase`, `contextVirtual`, `pressureAliasState`,
  `temporalAliasState`), but they always appear *identically on both sides* and are only ever applied
  to **variable** indices `i : Fin 3`, so no kernel `Nat` literal comparison is forced;
* **zero** macro/elab/`set_option`/`native_decide`/`axiom`/`unsafe`/`partial` in any file I opened.
* Kernel **proof irrelevance** is load-bearing at 3 sites (2, 3, 5, 9): duplicated `by omega` /
  `by norm_num` / `length_pos` proof arguments are compared as Props, not as terms. That is a
  standard, sound kernel feature; the only cost is that the kernel typechecks small `omega`
  certificates over the literals 6 and 7.

**Length is argument lists, not computation.** Sites 1, 2, 3, 4, 8 have long statements purely
because the constructions carry 10-20 explicit parameters (`m hm J support hSupport δ hδ ξ hs α N hN
k hk Q I`, `g r h index axial c labels pieces baseError`, ...). Those arguments are *carried along*
by the kernel unchanged; they cost nothing. I say this explicitly per site.

Step estimates below count **head reductions** (delta of a `def` + one projection + one beta each
count as one step); they are order-of-magnitude, not exact.

---

## Site 1 — `Euler/ParentForwardInitialSupport.lean:49` `normalizedPacketPressure_forwardInitialized`

Statement (49-56, verbatim):

```lean
theorem normalizedPacketPressure_forwardInitialized (t : Icc (0 : ℝ) A.T) :
    A.normalizedPacketPressure m hm J support hSupport Q
      (forwardInitializedApproximationResidual (A.meanData H) (A.transverseData m hm J support hSupport) rfl
        δ hδ ξ hs α
        (A.sourceAgreement m hm J support hSupport H) N hN k hk) k I t =
    forwardInitializedExactPhysicalPressure (A.meanData H) (A.transverseData m hm J support hSupport) rfl
      δ hδ ξ hs α
      (A.sourceAgreement m hm J support hSupport H) N hN k hk Q t (I.normalized t) := rfl
```

**Two sides.** LHS head `EulerParentPacketFrames.Parent.normalizedPacketPressure`
(`Euler/PacketChildFieldMatch.lean:84`):
`= (exactPacketOfResidual P B residual).graphPotential k t ∘ I.normalized t`.
RHS head `forwardInitializedExactPhysicalPressure` (`Euler/PacketForwardExactFields.lean:86`):
`= (forwardInitializedExactPacket M D hTime δ hδ ξ hs α Cagree N hN k hk Q).graphPotential k t ∘ Y`,
with `Y := I.normalized t`.

**Defs followed.**
* `Euler/PacketChildFieldMatch.lean:84-85` — `normalizedPacketPressure`, non-recursive, 1 line body.
* `Euler/PacketForwardExactFields.lean:86-87` — `forwardInitializedExactPhysicalPressure`, ditto.
* `Euler/PacketForwardInitializedExactLifted.lean:23-30` — `forwardInitializedExactPacket M D ... Q
  := exactPacketOfResidual period Q (forwardInitializedApproximationResidual M D ... )`. **This is
  the whole content of the lemma**: the two packets are the *same* `exactPacketOfResidual`
  application.
* `Euler/PacketInitializedExactLifted.lean:42-50` — `exactPacketOfResidual` is a `where` literal
  (7 fields, 4 of them Props). Not unfolded here; both sides share it.
* `Euler/ExactLiftedGraphPressure.lean:36` — `graphPotential`; not unfolded (identical both sides).

**Kernel work.** 3 delta steps (`normalizedPacketPressure`, `forwardInitializedExactPhysicalPressure`,
`forwardInitializedExactPacket`) and then syntactic identity. Extra: the *statement* only typechecks
because the implicit `{P κ hκ Z R}` of `normalizedPacketPressure` were unified against
`forwardInitializedCorrectionData` — resolved by
`Euler/PacketForwardInitializedCorrectionData.lean:31-38` -> `correctionDataOfFields`
(`Euler/PacketCorrectionSourceData.lean:33-35`) -> `correctionData`
(`Euler/PacketCorrectionSourceData.lean:17`), so the kernel re-checks ~5-15 further deltas of *types*.
Note the `hTime` argument is passed as literal `rfl` (line 51), i.e. `(A.meanData H).T` and
`(A.transverseData ...).T` are definitionally equal — also cheap delta, no computation.

**Classification.** (ii) beta/delta of non-recursive defs (~3 steps + ~10 in type checking);
(i) marginal. No (iii)-(vi).

**Long statement = long argument list.** Yes: 15 carried arguments; zero computation.

**Verdict: OK.** Content is real but trivial: the child's normalized packet pressure is *by
definition* the forward-initialized exact packet's graph potential precomposed with the inverse flow.
Reason another auditor can check: `forwardInitializedExactPacket` (PacketForwardInitializedExactLifted.lean:29-30)
literally *is* `exactPacketOfResidual period Q (forwardInitializedApproximationResidual ...)`.

---

## Site 2 — `NavierStokes/ActualParticularStageControls.lean:813` `selected_data_amplitude`
## Site 3 — `NavierStokes/ActualParticularStageControls.lean:821` `selected_data_pressure`

Statement (813-819; site 3 is the same with `.pressure`):

```lean
theorem selected_data_amplitude (e : ℕ → ActivePair B N0)
    (x : CycleState (Label B N0)) (j : ℤ) (u : Unit) (q : ℕ) (k : Frequency) :
    (data x (selectedLabel e q) j).amplitude (selectedBand e q) k =
      (ParticularWaveBounds.complexCopyCoefficients (selectedBackground e x j u)
        (selectedTangent e x j u) (selectedSource e x j u) (selectedGeometry e u) (fun _ => k)
        (selectedLength e u) (fun n => ScaledActualParticularControl.length_pos
          (selectedConstruction e) (selectedClock e) u n)).amplitude q := rfl
```

**Two sides.** This is a **reindexing-coherence** identity, and note the *index mismatch*: LHS reads
the coefficient family at band index `selectedBand e q`, RHS at the enumeration index `q`.

* LHS: `data` (`:788-790`) = `(parameters x l).copyData (assembly x l).context ... j` with
  `l := selectedLabel e q`. `ParticularParameters.copyData` is a `where` literal at
  `NavierStokes/CorrectionStep.lean:4908-4922`; its `amplitude` field (`:4913-4916`) is
  `amplitude n k := (complexCopyCoefficients (actualCarrier p.background b j)
  (fun n => angleTangent (p.tangent j n)) (sourceFamily c u b G A j) p.geometry (fun _ => k)
  p.length p.length_pos).amplitude n`. So LHS = that, at `n := selectedBand e q`.
* RHS: the same `complexCopyCoefficients`, but fed the *reindexed* families.

**Why the index shift is harmless.** `ParticularWaveBounds.complexCopyCoefficients`
(`NavierStokes/ParticularWaveBounds.lean:1606-1612`) is
`{ base with amplitude := fun n => complexCopyVelocity (t n) (source n) (g n) (hL n).le (copy n),
pressure := fun n => complexCopyPressure (t n) (source n) (g n) (hL n).le (copy n) (base.frequency n) }`
— **strictly component-wise in `n`, no recursion on `n`**. So the equation reduces to a per-component
comparison at the single index `selectedBand e q`.

**Component-wise defs followed (all non-recursive one-liners).**
* `selectedLabel`/`selectedBand` = `(e n).val.1` / `(e n).val.2` (`:451`, `:453`) — projections of a
  subtype value, so `ActivePair`'s proof component is discarded.
* `selectedTangent e x j u n = (parameters x (selectedLabel e n)).nativeTangent j (selectedBand e n)`
  (`:725-726`), and `ParticularParameters.nativeTangent`
  (`NavierStokes/CorrectionStep.lean:5688-5689`) `= fun n => angleTangent (p.tangent j n)`
  — matches LHS's `fun n => angleTangent (p.tangent j n)` at `n := selectedBand e q`. ✔
* `selectedSource e x j u n = currentSource x j (selectedLabel e n) (selectedBand e n)` (`:722-723`)
  and `currentSource` (`:555-558`) `= sourceFamily (assembly x l).context (assembly x l).state
  (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput j` — the exact
  family LHS uses. ✔
* `selectedGeometry e u q` (`:480-483`) = `ScaledActualParticularControl.geometry (slotReference slots
  vectors_det (selectedSlot e)) (selectedGap e) (selectedClock e) u q`
  = `transportGeometry (slotReference ... u q) (selectedGap e u q) 0 ((selectedClock e).value u q) _`
  (`NavierStokes/ScaledActualParticularControl.lean:59-62`), to be identified with
  `(parameters x l).geometry (selectedBand e q)` = `fromReference (assembly x l) h (gap l)`'s
  `geometry` field = `transportGeometry (assembly x l).reference.geometry (gap l n) 0 (clockWeight ...)`
  (`NavierStokes/CorrectionStep.lean:7945-7948`). The repo asserts exactly this as a separate `rfl`
  at `:491-492` (`selected_geometry_eq`) and `:494-495` (`selected_length_eq`).
* `selectedLength` (`:485-486`) -> `ScaledActualParticularControl.length F clock l n = F.L (l,n)/clock.value l n`
  (`ScaledActualParticularControl.lean:42-43`) vs `fromReference`'s `length n := D.reference.length /
  clockWeight ...` (`CorrectionStep.lean:7949-7950`).
* `selectedBackground` (`:728-732`) = `ParticularCopyBounds.reindexedBase (fun l => (... .copyData ...).background)
  (fun n => (selectedBand e n, selectedLabel e n))`; `reindexedBase`
  (`NavierStokes/ParticularCopyBounds.lean:467-476`) is a `where` literal with every field
  `field n := (base (e n).2).field (e n).1` — a pure projection reindex. Needed only for site 3
  (`pressure` uses `base.frequency n`); site 2's `amplitude` does **not** read `base` at all.
* `hL` argument: LHS carries `p.length_pos`, RHS carries `fun n => ScaledActualParticularControl.length_pos ...`
  (`ScaledActualParticularControl.lean:45-47`). Different *terms*, same *Prop* — identified by kernel
  **proof irrelevance** once `(parameters x l).length (band q) ≡ selectedLength e u q` (see `:494-495`).

**Classification.** (i) projection of `where` literals (`copyData`, `complexCopyCoefficients`'s
`{base with ...}`, `reindexedBase`, `fromReference`) + (ii) delta of ~10 non-recursive one-line defs.
No (iii)/(iv)/(v)/(vi). **Step estimate ~20-35 head reductions for site 2, ~30-45 for site 3**
(site 3 additionally reduces `base.frequency` through `reindexedBase` and `actualCarrier`).

**Nat/Fin exposure:** none. Every index (`q`, `selectedBand e q`, `k`) is a **variable**; `ChartScales.Q n`
etc. are applied to symbolic `n`, so nothing computes.

**Verdict: OK (both).** The claims are genuine coherence facts (the "selected" enumeration of
(label, band) pairs sees exactly the per-band data of the labeled construction) that happen to hold
definitionally because every layer is a component-wise `where` literal. Mild honest-naming note: the
`u : Unit` argument is unused on both sides (`selected*` take `_ : Unit`), so the lemma is trivially
uniform in `u`; and the RHS deliberately re-derives the same numbers, so this is *not* vacuous.

---

## Site 4 — `Euler/PacketResidualTailFields.lean:51` `PrefixFields.tailGradeField_path`

Statement (51-58):

```lean
theorem PrefixFields.tailGradeField_path (F : PrefixFields P T (N+1) a) ... (n : ℕ) (hn : N+1 ≤ n) :
    (F.tailGradeField C hT Ct hCt pressure ha n hn).path =
      (F.tailLinearField C hT Ct hCt pressure n).path + (F.tailNonlinearField C n).path := rfl
```

**Two sides.** LHS is the `path` field of `tailGradeField` (`:41-49`), defined as
`((F.tailLinearField ... n).add (F.tailNonlinearField C n)).congr (fun _ _ _ => recursiveGrade_tail ...)`.
RHS is the sum of the two summands' `path`s.

**Defs followed.**
* `Euler/PacketCylinderField.lean:21-25` — `structure Field` with fields `path : C(Icc 0 T, LiftL2 P)`,
  `orbit` (Prop), `raw_eq` (Prop).
* `Euler/PacketCylinderFieldAlgebra.lean:29-34` — `Field.congr` is a `where` literal with
  `path := G.path`. **1 projection.** (Crucially it is *not* `h ▸ G`, so no `Eq.mpr`/cast to reduce.
  Contrast `Euler/PacketProfileRegularity.lean:50` and `Euler/PacketPressureWitness.lean:77`, where
  `congr` *is* `h ▸ G`; those would have been transport-through-cast, not a projection.)
* `Euler/PacketCylinderFieldAlgebra.lean:42-51` — `Field.add G H := ofLifted (G.path+H.path) ...`;
  `ofLifted` (`:16-26`) is a `where` literal with `path := p`. **2 steps.**

**Kernel work.** delta `tailGradeField` -> proj `congr` -> delta `add` -> delta `ofLifted` -> proj
`path` = `G.path + H.path`, then syntactic identity with RHS. **~5-6 head reductions.**
The `Field.add` proof fields (`orbit`, `raw_eq`) are Props and are never forced.

**Not forced (worth stating):** `tailLinearField` (`:27-39`) is defined by a **tactic** body that
does `by_cases hn : n=N+1`, i.e. its data content sits under a `Decidable (n = N+1)` case split
(`Nat.decEq`), and `tailNonlinearField` (`:14-25`) is a `let`-heavy tactic body. **Neither is
unfolded by this `rfl`** — both occur syntactically identically on the two sides. If a later lemma
ever forces `tailLinearField` at a *closed* `n`, that WOULD hand the kernel a `Nat.decEq` literal
comparison; that is not this site's problem, but it is the nearest thing to a threat-vector-2 hook I
saw in this file. Also `recursiveGrade` appears only inside the *type*, never reduced.

**Classification.** (i) + (ii), ~5-6 steps. No (iii)-(vi).

**Verdict: OK.** Reason: `Field.congr` copies `path` (`PacketCylinderFieldAlgebra.lean:32`) and
`Field.add` builds `path := G.path + H.path` via `ofLifted` (`:43` with `:22`).

---

## Site 5 — `Euler/SobolevTransportCommutator.lean:34` `externalCommutator_apply`

Statement (34-41):

```lean
theorem externalCommutator_apply {s : ℕ} (hs : 6 ≤ s) (n : ℕ) (w : Fin n → Fin 4) (hn : n+6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (u v : SobolevSpace period (s+1)) :
    externalCommutator period hs n w hn L hL u v =
      wordAtLevel period 6 n w hn (transportBilinear period hs L hL u v) -
      transportBilinear period (by norm_num : 6 ≤ 6) L hL
        (restrictOperator period (by omega : 7 ≤ s+1) u)
        (wordAtLevel period 7 n w (by omega : n+7 ≤ s+1) v) := rfl
```

**Two sides.** LHS is the operator `externalCommutator` (`:25-31`) applied to `u` then `v`; the
operator is `((compL ℝ _ _ _ (wordAtLevel period 6 n w hn)).comp (transportBilinear period hs L hL))
- (transportBilinear period _ L hL).bilinearComp (restrictOperator period _) (wordAtLevel period 7 n w _)`.
RHS is the elementwise value.

**What the kernel must do.** Unfold `externalCommutator` (1 delta), then push the application
through four *Mathlib* coercion layers, each of which is a `rfl`-lemma in Mathlib (I could not open
Mathlib source — no build on this box — so I name the lemmas the reduction corresponds to):
`ContinuousLinearMap.sub_apply` twice (outer in `E →L (F →L G)`, inner in `F →L G`),
`ContinuousLinearMap.comp_apply`, `ContinuousLinearMap.compL_apply`,
`ContinuousLinearMap.bilinearComp_apply`. Mechanically these are projections of `⟨⟨⟨_,_⟩,_⟩,_⟩`
bundled-morphism literals plus `Pi`/`DFunLike.coe` instance unfolding.
`wordAtLevel` (`Euler/SobolevWordLevel.lean:18-20`) and `transportBilinear` are **not** unfolded
(identical on both sides).

**Duplicated proof arguments.** `(by norm_num : 6 ≤ 6)` and `(by omega : 7 ≤ s+1)`,
`(by omega : n+7 ≤ s+1)` are re-elaborated at the theorem site (lines 39-41) and are almost certainly
different *terms* from those in the def (lines 30-31). They are identified by **kernel proof
irrelevance**; the kernel does typecheck the omega/norm_num certificates, which involve only the
literals 6 and 7 (tiny `Nat.le` terms), so threat-vector-2 exposure is negligible.

**Classification.** (i) projections of bundled-CLM structure literals + (ii) delta of instance /
`compL` / `comp` / `bilinearComp` definitions. **Step estimate ~20-40 head reductions.** No (iii)-(v).
Possibly a trace of (vi): `DFunLike` coercions of bundled morphisms may need structure eta on the
`ContinuousLinearMap`/`LinearMap` records — cheap and standard.

**Long statement = long argument list + explicit proof terms.** Yes.

**Verdict: OK.** Reason: `externalCommutator` (`:28-31`) is *literally* the difference of the two
composites the RHS spells out; the only kernel content is Mathlib's `*_apply` rfl-lemmas.

---

## Site 6 — `Euler/ChildParticleFieldBounds.lean:243` `childAcceleration_apply`

Statement (243-248):

```lean
theorem childAcceleration_apply (x : Space) :
    G.childAcceleration.field x = G.parentAcceleration.field (G.inner x)+
      fderiv ℝ G.parentVelocity.field (G.inner x) (G.velocity.field x)+
      fderiv ℝ G.parentVelocity.field (G.inner x) (G.velocity.field x)+
      fderiv ℝ (fderiv ℝ G.parentDisplacement.field) (G.inner x) (G.velocity.field x) (G.velocity.field x)+
      G.acceleration.field x+fderiv ℝ G.parentDisplacement.field (G.inner x) (G.acceleration.field x) := rfl
```

**Two sides.** LHS: `field` of `childAcceleration` (`:201-205`), a left-nested 5-fold `addField` of
six summands. RHS: the six chain-rule terms, left-associated by `+` — the same association.

**Defs followed (all non-recursive `where` literals or one-liners).**
* `Euler/LpSmoothField.lean:31-34` — `structure SmoothL2Field` (`field`, `smooth` Prop, `integrable` Prop).
* `Euler/LpSmoothFieldAlgebra.lean:47-52` — `addField A B` is a `where` literal, `field := A.field+B.field`
  (`Pi.add`, so one more beta after projection). The repo itself states the one-step version as
  `addField_field ... := rfl` at `:54-55`.
* `Euler/SmoothL2GevreyCalculus.lean:98-101` — `composeField`, `field := A.field ∘ f`; used by
  `parentComposed` (`ChildParticleFieldBounds.lean:90-93`) with `f := G.inner`; `Function.comp`
  unfold + beta gives `U.field (G.inner x)`. ✔ = RHS summand 1.
* `Euler/SmoothL2GevreyCalculus.lean:110-120` — `productField`, `field x := g x (A.field x)`; used by
  `firstTerm` (`:146-149`) with `g := G.firstCoefficient U` = `fderiv ℝ U.field (G.inner x)` (`:103-104`)
  -> summands 2 and 3 (`U := G.parentVelocity`, appearing **twice** because `childAcceleration`
  lists `firstTerm parentVelocity` twice at `:204-205`), and by `accelerationTerm` (`:185-188`)
  -> summand 6, and by `quadraticTerm` (`:169-173`) with `g := G.quadraticCoefficient`
  = `G.secondCoefficient G.parentDisplacement x (G.velocity.field x)` (`:157-158`),
  `secondCoefficient` = `fderiv ℝ (fderiv ℝ U.field) (G.inner x)` (`:105-106`) -> summand 4.
* Summand 5, `G.acceleration.field x`, is a projection of the `Data` parameter `G` — irreducible,
  identical both sides.

**Classification.** (i) + (ii). Steps: 5 x (delta `addField` + proj + `Pi.add` delta + beta) ≈ 20,
plus ~3 steps per leaf x 6 leaves ≈ 15. **Estimate ~30-40 head reductions.** No recursion, no
literals, no (iii)-(vi).

**Mathematical sanity check (not just kernel).** The six terms are exactly
`X_tt + 2·(∇X_t)Y_t + (∇²X)(Y_t,Y_t) + Y_tt + (∇X)Y_tt` for `child = X(t, Y(t,·))` — the doubled
`fderiv ℝ G.parentVelocity.field (G.inner x) (G.velocity.field x)` (lines 245-246) is the genuine
`2·∇X_t·Y_t` cross term, not a copy-paste artifact (it is duplicated on purpose at `:204-205`, and
`childAcceleration_bound` at `:224-234` prices it twice: `3*firstAmplitude*amp` appears twice at
`:229`). No junk-value or vacuity smell.

**Verdict: OK.**

---

## Site 7 — `NavierStokes/AxisymmetricResidualGrouping.lean:152` `stateMeanCoefficientValue_erase`

Statement (152-158):

```lean
@[simp] theorem stateMeanCoefficientValue_erase {ι : Type*} (labels : ℕ → Finset ι)
    (blocks : ι → HarmonicBlock D) (gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D)
    (c : Context D) (s : State D) (axis : MeanVector D) :
    HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c
      (eraseAxisymmetricAlias s axis) =
      HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c s := rfl
```

**Two sides.** Equality of two *partially applied* functions (`n x i` are not given), so the kernel
delta-unfolds both to `fun n x i => meanResidualValue ...` and compares bodies (function eta/η is
trivially available; no structure eta needed).

**Defs followed.**
* `NavierStokes/HarmonicResidual.lean:1500-1505` — `stateMeanCoefficientValue ... c s n x i :=
  meanResidualValue (labels n) (fun l => ofBlock (blocks l) (gaussian l) (aliasError l) n)
  (contextFrame c n) (contextBase c n) (stateMean s n) (fun y => (s.pressure n y : ℂ))
  (contextVirtual c n) x i`. **`s` enters only via `stateMean s n` and `s.pressure`.**
* `NavierStokes/HarmonicResidual.lean:1307-1308` — `stateMean s n x := ![(s.mean.radial n x : ℂ), ...]`
  — only `s.mean`.
* `NavierStokes/AxisymmetricResidualGrouping.lean:32-33` — `eraseAxisymmetricAlias s a :=
  { s with errors := { s.errors with aliasError := s.errors.aliasError - axisymmetricLift a } }`
  — a `State.mk` literal that changes **only** `errors.aliasError`.
* `NavierStokes/CorrectionState.lean:65-70` — `structure State` (`mean`, `pressure`, `oscillation`,
  `oscillatoryPressure`, `errors`).

**Kernel work.** 2 deltas of `stateMeanCoefficientValue`, 1 delta of `eraseAxisymmetricAlias`, then
`(mk ...).mean -> s.mean` and `(mk ...).pressure -> s.pressure` (2 projections of a constructor
application). **~6-10 head reductions.** `![...]` occurs identically on both sides and is applied only
to the *variable* `i`, so **no `Matrix.cons`/`Fin` literal resolution** (class (v) does not fire).

**Classification.** (i) + (ii), ~6-10 steps.

**Sharp observation (name vs statement).** The same `rfl` would prove invariance of
`stateMeanCoefficientValue` under **any** change to `s.errors` (all three components) and under any
change to `s.oscillation`/`s.oscillatoryPressure` — because the value is built from the *label
families* plus `s.mean`/`s.pressure` only. Contrast the neighbouring, non-`rfl` facts in the same
file: `stateGoodResidual_eraseAxisymmetricAlias` (`:65-73`) needs a real proof and shows the good
residual **does** move, `= ... + a n x.1 i`; and `stateGoodWaveResidual_addAxisymmetricAlias`
(`:90-102`) needs an integrability hypothesis. So the "mean coefficient value" is only the angular
mean of the good residual *given* a `BlockRepresentation` (`HarmonicResidual.lean:1508-1520`), and the
alias bookkeeping is reconciled by `Representation.erase` (`:121-135`), which is *not* `rfl`
(`aliasError` needs `add_sub_cancel_right`). Nothing false here, but the `rfl` is much weaker than
"the mean coefficient is alias-covariant".

**Verdict: OK** (with the naming/scope note above).

---

## Site 8 — `NavierStokes/CorrectionInitialization.lean:1327` `GaugeInitialization.initialized_reconstructed`

Statement (1327-1332):

```lean
theorem initialized_reconstructed (g : GaugeData S) (r : RankData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × PressureStream.Plane) (c : Context (PressureStream.Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (PressureStream.Lift S × ℝ))
    (baseError : Oscillation (PressureStream.Lift S)) :
    reconstructState g c (initialized g r h index axial c labels pieces baseError) =
      initialized g r h index axial c labels pieces baseError := rfl
```

This is an **idempotence / fixed-point** claim proved by `rfl`, so it is the most structurally
interesting site I was given.

**Two sides.** LHS = `reconstructState g c I`, RHS = `I`, where
`I := initialized g r h index axial c labels pieces baseError`.

**Defs followed.**
* `NavierStokes/VariableGaugeMean.lean:517-523` — `reconstructState g c u :=
  { u with pressure := fun n => meanPressure ... g.radial.radialDirection (u.gr c n) }`.
  It rewrites **only** the `pressure` field, from `u.gr c n`.
* `NavierStokes/CorrectionState.lean:117-118` — `State.gr s c :=
  MeanIncrementBounds.gr c.operators c.base s.mean s.covariance`. **`gr` does not read `s.pressure`
  and does not read `s.errors`.**
* `NavierStokes/MeanIncrementBounds.lean:338-342` — `MeanIncrementBounds.gr o b m W` uses only
  `o`, `b`, `m` and `W`; `State.covariance` (`CorrectionState.lean:98-99`) is built from
  `s.oscillation` only.
* `NavierStokes/CorrectionInitialization.lean:1286-1290` — `initialized := retainPressureAlias g c
  (afterRank ...)`; `retainPressureAlias` (`:1281-1284`) changes **only** `errors.aliasError`.
* `:1275-1279` `afterRank := rankStageState g r axial c (afterTemporal ...)` and
  `VariableGaugeMean.lean:580-583` `rankStageState ... := reconstructState g c (u.addIncrement ...)`
  — i.e. every stage already **ends** with `reconstructState` (same for `temporalStageState`,
  `VariableGaugeMean.lean:559-563`, and `primaryStage`, `CorrectionInitialization.lean:1264-1267`).

**Why `rfl` works (the mechanism).** Write `X := (afterTemporal ...).addIncrement (rankIncrementState ...) ...`.
Then `afterRank = { X with pressure := fun n => meanPressure ... (X.gr c n) }` and
`I = { afterRank with errors := ⟨...⟩ }`. Because neither `reconstructState` nor
`retainPressureAlias` touches `mean` or `oscillation`, `I.mean ≡ X.mean` and `I.oscillation ≡ X.oscillation`
after projections, hence `I.gr c n ≡ X.gr c n` **syntactically after reduction**; and
`I.pressure ≡ fun n => meanPressure ... (X.gr c n)`. So the new pressure the LHS installs is the one
already there. Both sides reduce to `State.mk` applications whose five arguments are pairwise
identical after projection chains. **`reconstructState g c` is definitionally idempotent for *every*
state**, not just this one.

**Classification.** (i) projections of `{ _ with _ }` / `mk` literals + (ii) delta of ~8 non-recursive
defs (`initialized`, `retainPressureAlias`, `afterRank`, `rankStageState`, `reconstructState` x2,
`State.gr` x2, `State.covariance`). **Step estimate ~30-60 head reductions.** No (iii)-(v). Mild (vi):
`{ u with ... }` on a non-constructor `u` is elaborated with projections, so record eta is in play in
the usual harmless way. `meanPressure` (an integral transform) is never *evaluated* — it is a carried
head symbol.

**Mathematical read (be loud).** The fixed-point property is real but it is a consequence of a
**deliberate definitional blindness**: the gauge-reconstructed mean pressure is computed from `gr`,
which by construction (MeanIncrementBounds.lean:338-342) is the radial-momentum defect built from
`c.operators`, `c.base`, `s.mean`, `s.covariance` and carries **no pressure feedback**; pressure
enters the residual only additively elsewhere (`State.radialResidual := c.operators.dr s.pressure -
s.gr c`, `CorrectionState.lean:120-121`). That is the physically right structure for `∂_r p = gr`,
so I do **not** call it junk — but the theorem name "initialized_reconstructed" would equally be
provable for any state, and a reader could mistake it for "the initialization solved the gauge
equation". It did not; it only says "the pressure slot already holds the value the gauge map would
install".

**Verdict: OK** (loud structural note above; nothing false, nothing kernel-heavy).

---

## Site 9 — `Euler/SobolevBaseCommutator.lean:33` `baseCommutator_apply`

Statement (33-38):

```lean
theorem baseCommutator_apply (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) (u v : SobolevSpace period 7) :
    baseCommutator period r hr w L hL u v =
      value period (wordAtLevel period 0 r w (by omega : r+0 ≤ 6) (transportBilinear period (by norm_num : 6 ≤ 6) L hL u v)) -
        transportL2Bilinear period (by norm_num : 3 ≤ 7) L u (wordAtLevel period 1 r w (by omega : r+1 ≤ 7) v) := rfl
```

Same shape as site 5 (`baseCommutator` at `:23-30` is a difference of a `compL`-composite and a
`bilinearComp`), with **two extra reductions**:

1. `ContinuousLinearMap.id ℝ (SobolevSpace period 7)` applied to `u` must reduce to `u`
   (`id_apply`, a projection + beta).
2. LHS carries `(valueOperator period 0).comp (wordAtLevel period 0 r w _)` (`:27`) while the RHS
   writes `value period (wordAtLevel period 0 r w _ ...)` (`:37`). So the kernel must see
   `valueOperator period 0 y ≡ value period y`:
   `valueOperator` (`Euler/CylinderSobolevOperators.lean:20-21`) `= (ContinuousLinearMap.proj (emptyWord q)).comp
   (arrayOperator period q)`, `arrayOperator` (`:16-17`) `= (sobolevSubspace period q).toSubmodule.subtypeL`,
   and `value` (`Euler/CylinderSobolevSpace.lean:63`) `= u.val (emptyWord q)`. Reduction:
   `proj_apply` + `subtypeL_apply` + 2 deltas -> `y.val (emptyWord 0)` on both sides.
   `emptyWord q := ⟨⟨0, Nat.zero_lt_succ q⟩, Fin.elim0⟩` (`CylinderSobolevSpace.lean:21`) appears
   **identically** on both sides — it is used as a *function argument*, never as an index into a
   `Matrix.cons` literal, so again **no class-(v) Nat/Fin literal resolution**.

**Duplicated proof terms** `(by omega : r+0 ≤ 6)`, `(by omega : r+1 ≤ 7)`, `(by norm_num : 6 ≤ 6)`,
`(by norm_num : 3 ≤ 7)` are re-elaborated at the theorem (lines 37-38) vs the def (lines 27-30) and
are identified by **proof irrelevance**; certificates involve only 0,1,3,6,7.

**Classification.** (i) + (ii), **~30-50 head reductions**; a trace of (vi) via bundled-morphism
coercions. No (iii)/(iv)/(v).

**Verdict: OK.** Reason: `baseCommutator` (`:26-30`) is literally the difference of the two composites
the RHS spells out, plus `valueOperator 0 = value` (both are `_.val (emptyWord 0)`).

---

## Summary table

| # | site | classification | est. steps | verdict |
|---|------|----------------|-----------|---------|
| 1 | ParentForwardInitialSupport.lean:49 | (ii) [+ type-level deltas] | ~3 (+10) | OK |
| 2 | ActualParticularStageControls.lean:813 | (i)+(ii), proof irrelevance | ~20-35 | OK |
| 3 | ActualParticularStageControls.lean:821 | (i)+(ii), proof irrelevance | ~30-45 | OK |
| 4 | PacketResidualTailFields.lean:51 | (i)+(ii) | ~5-6 | OK |
| 5 | SobolevTransportCommutator.lean:34 | (i)+(ii)+trace(vi), proof irrelevance | ~20-40 | OK |
| 6 | ChildParticleFieldBounds.lean:243 | (i)+(ii) | ~30-40 | OK |
| 7 | AxisymmetricResidualGrouping.lean:152 | (i)+(ii) | ~6-10 | OK (scope note) |
| 8 | CorrectionInitialization.lean:1327 | (i)+(ii)+trace(vi) | ~30-60 | OK (structural note) |
| 9 | SobolevBaseCommutator.lean:33 | (i)+(ii)+trace(vi), proof irrelevance | ~30-50 | OK |

## Follow-ups another auditor may want

1. `Euler/PacketResidualTailFields.lean:27-39` — `PrefixFields.tailLinearField` is a **data**
   definition whose body is `by_cases hn : n=N+1`. Any later `rfl`/`decide` that forces it at a
   *closed* `n` hands the kernel a `Nat.decEq` literal comparison. Worth grepping for uses at
   literal grade indices.
2. Two `congr` helpers in the Euler tree are `h ▸ G` transports, not field copies
   (`Euler/PacketProfileRegularity.lean:50`, `Euler/PacketPressureWitness.lean:77`). A bare `rfl`
   over *those* would be a cast-reduction obligation, unlike site 4's `Field.congr`
   (`Euler/PacketCylinderFieldAlgebra.lean:29-34`). Worth checking whether any bare-`rfl` theorem
   crosses them.
3. `NavierStokes/VariableGaugeMean.lean:517-523` + `CorrectionState.lean:117` establish that
   `reconstructState` is idempotent for *every* state. Any lemma whose name suggests the
   initialization "solves" the gauge equation should be re-read against this.
