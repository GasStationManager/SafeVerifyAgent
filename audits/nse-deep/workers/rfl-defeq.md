# Worker report: bare-`rfl` sites and the artifact's kernel defeq exposure

Auditor: `rfl-defeq` worker. Subject: `/home/gsm/.openclaw/workspace/repos/NSE`
(clone of `openai/NavierStokesAndEuler` @ `f9e8bc5`), READ-ONLY, source-level reading only
(no `lake build`; no Mathlib on this box).

Threat model for this worker: a proof that is exactly `rfl` / `by rfl` hands the **kernel** a
definitional-equality obligation. The kernel may use delta (unfold `def`), beta, zeta (`let`/`have`),
iota (recursor / match reduction), structure projection, structure eta, and **proof irrelevance**.
The question is not "does it elaborate" (Comparator settled that) but "what does the kernel have to
COMPUTE, and is any of it on a kernel weak spot".

## Scope

* **Inventory re-derived independently** (I did not trust `RFL_SITES.csv`; see
  "Is the 529 count right?" below): I re-parsed all **2659** `.lean` files under the clone,
  segmented **51008** declaration blocks by column-0 declaration starts, stripped comments
  (nested `/- -/` and `--`), located the **first bracket-depth-0 `:=`** of each declaration and
  required the remaining text to be exactly `rfl` or `by rfl`.
  Result: **1358** bare-`rfl` `theorem`s repo-wide; **541** of them in-cone
  (`CONE.csv in_cone = True`, matched with tolerance for `@[simp]`-on-its-own-line offsets).
  541 / 27753 in-cone theorem+lemma declarations = **1.9 %** of the in-cone theorem population,
  spread over **291** files. Statement length: median 135, mean 160, max 657 chars.
  218 of the 541 are named `*_apply`.
* **Read line-by-line by me**: the top 8 by statement length (ranks 1-8 below), all 7
  "names a recursive construct" sites (task B), the 2 `Matrix`-literal sites, the 4 other
  `Matrix`-mentioning sites, the 19 sites that mention any recursive definition
  (systematic scan, below), `SlowRecursion.lean:128,974`. For each I also read the `def`s of both
  sides' head symbols (34 supporting `def`s / `structure`s, all cited with file:line).
* **Read by delegated read-only children on the same taxonomy** (their sections are appended
  verbatim below / cross-linked): ranks 9-17 (`_scratch-rfl-mid.md`), ranks 18-25
  (`_scratch-rfl-tail.md`), and the 28 `SlowRecursion.lean` + `GlobalSlowProfiles.lean` sites
  (`_scratch-rfl-wf.md`, task C).
* **Skimmed only**: the remaining ~490 in-cone sites were not opened individually; instead they
  were subjected to three *systematic* text tests (recursive-definition mention, numeral size,
  `Matrix`/`![`/`Fin.cons`/`decide` mention) whose results are reported under
  "Kernel-risk assessment". Those tests are cheap to re-run and are stated so that a reviewer can
  falsify them.

## Classification taxonomy used

* (i) projection of a **structure literal** (`where`-style / `⟨…⟩` / `{ … }` term) — cheap, safe.
* (ii) beta/delta unfolding of **non-recursive** `def`s — cheap.
* (iii) exactly **ONE iota step on a symbolic constructor** (`f (n+1)` vs `| n+1 =>`) — safe.
* (iv) an iota **CHAIN** over a recursive definition at a **closed** argument — the dangerous case.
* (v) `Matrix.cons` / `Fin` / `List` **literal index resolution** (routes through kernel `Nat`
  literal comparison = threat vector 2).
* (vi) structure/function **eta**.
* (pi) **proof irrelevance**: the two sides carry different proof terms in `Prop` positions.

## Per-declaration findings

### Task A — the top 8 by statement length (my ranks; see count section for why they differ from the parent list)

| # | name | file:line | statement (my words) | what the kernel does | class | est. steps | verdict |
|---|------|-----------|----------------------|----------------------|-------|-----------|---------|
| 1 | `potential_eq` | `NavierStokes/ActualParticularPotentialCoherence.lean:106` | the *potential* of the current common coefficient equals `CurlClassBounds.vectorPotential` applied to 7 explicitly spelled arguments | delta `potential` (:80) → `(actualCoefficients x l j).curlPotential strip dirs n`; delta `curlPotential` (`LinearWaveBounds.lean:253`) → the same `vectorPotential` head with args `a.frequency n`, `a.radius n`, …; then the kernel must identify `a.frequency n ≡ (j:ℝ)*(x.coefficients.blocks l).frequency n` and `a.radius n ≡ fun y : WaveSpace => y.1.1.1` by unfolding `actualCoefficients` (`ActualReferenceRebase.lean:868`) `= (….copyData …).common` and projecting the `where` literal (`CorrectionStep.lean:4908`). `phase`/`amplitude` args are syntactically identical on both sides and are never reduced. | (i)+(ii) | ~10-40 head reductions per differing argument, ~10² total | OK |
| 2 | `nativePotential_eq` | `NavierStokes/ActualCurrentParticularPhysical.lean:112` | same shape, one layer shallower: the *native* potential equals `vectorPotential` of `(copyData x l j).background.…` fields | same mechanism; `copyData` (`CorrectionStep.lean:4908`) is a `where` literal, `background := ParticularWaveAssembly.actualCarrier …`, so each argument is one delta + one projection | (i)+(ii) | ~10² | OK |
| 3 | `initializedDriftBudget_growth` | `Euler/PacketInitializedSpatialBudget.lean:115` | the `combinedConstant` of the initialized drift budget and its metric budget equals `growthCoefficient` at two explicit real arguments | delta `combinedConstant` (`Euler/CorrectionEnergyMajorants.lean:109`) → `energyConstant period (K.growth0 …) (K.growth1 …) (K.multiplier …) S.B S.M S.B0 S.B1 S.A0 S.A2 K.c`; delta `growthCoefficient` (`Euler/PacketCorrectionGrowth.lean:20`, plus 3 zeta steps for its `let`s) → `energyConstant P (growthBudgetBase c … + …) … Kc.B Kc.M B0 B1 Kc.A0 Kc.A2 c`. Kernel then matches argument-by-argument through **five** layers of structure literals: `.full` → `initializedSpatialBudget` (`:57`, fields `B := Kc.B`, `B0 := 2*velocity L.R S.H0 BC.multiplierCost`, `B1 := 12*velocity …*(4*L.R)`, `:61-67`), `Data.metricBudget` (`Euler/AllOrderCorrectionData.lean:100`, every field `:= K.<same>`), `initializedMetricBudget` (`:26`) → `sourceMetricBudgetOfFields` (`Euler/PacketCorrectionMetricBudget.lean:115`) → `sourceMetricBudget` (`:93`, `c := D.inverseBound⁻¹`, `first := inverseMetricFirstBound D`, `time := inverseMetricTimeBound D`, `bound := inverseMetricBound D`), and the derived `MetricBudget.growth0/growth1/multiplier` defs (`Euler/CorrectionEnergyData.lean:147/152/157`). Every step is delta or projection-of-literal. | (i)+(ii) | ~1-3 × 10² | OK. Note the statement is *long because the argument lists are long* (21 named hypotheses threaded through), not because anything is computed. |
| 4 | `forwardInitializedDriftBudget_growth` | `Euler/PacketForwardInitializedSpatialBudget.lean:113` | same theorem for the "forward" variant | same chain, `forward*` twins of the same defs | (i)+(ii) | ~1-3 × 10² | OK |
| 5 | `forcingWordPath_apply` | `Euler/RegularizedForcingWord.lean:29` | the forcing path evaluated at time `t` is source + transport + pressure, spelled out | delta `forcingWordPath` (`:19`) → `(f₁ + f₂ + f₃) t`; `ContinuousMap` `+`/`⟨fun t => …, _⟩` projections give `f₁ t + f₂ t + f₃ t`; then `sourceWordPath` (`Euler/RegularizedWordTime.lean:32`) = `((valueOperator …).comp (regularizedWordBlock …)).compLeftContinuous … f` and `timePathApply` (`Euler/TimePathApply.lean:17`) `= ⟨fun t => A t (u t), _⟩` reduce to the RHS by CLM/`ContinuousMap` projections. **The recursive `wordBlock` (`Euler/SobolevWordBlocks.lean:17`, structural on the word length) sits inside `regularizedWordBlock` at the SYMBOLIC length `m` and appears identically on both sides — the kernel never reduces it.** | (i)+(ii); recursive subterm neutral | ~40-80 | OK |
| 6 | `sourcePair_matrix` | `NavierStokes/CorrectionInitialization.lean:1012` | the `sourceMatrix` of a `sourcePair` equals `PrimaryPulseBounds.phaseCovariance` of an explicit prefactor family | `sourceMatrix` (`NavierStokes/PrimaryFieldAssembly.lean:519`) = `primaryCovariance (fun j (_ : Unit) => …) … () A.point`; `phaseCovariance` (`NavierStokes/PrimaryPulseBounds.lean:1647`) = `primaryCovariance … n q`. **The two sides instantiate `primaryCovariance`'s index type `ι` differently (`Unit` vs `ℕ`)**; both fully applied results are `Mat2`, and after delta to `covarianceMatrix` (`PrimaryPulseBounds.lean:782`, body `fun r c => pref c n * ∫ …`) + beta, the index argument disappears and both sides become the same term, given the `sourcePair` `where` literal (`:988`, `frame j := (F j).frame n`, `length j := (F j).L n`, `stretch := stretch`, `point := q`). `Mat2 = Matrix (Fin 2) (Fin 2) ℝ` (`SmoothCovariance.lean:27`) is here a plain **lambda**, not a `!![…]` literal, so no `Fin` index is ever resolved. | (i)+(ii)+beta | ~20-50 | OK, but see Escalation E2: this is defeq *across two different instantiations of a polymorphic index type*, cheap for the kernel and near-unreviewable by hand. |
| 7 | `preparedCovariance_eq_construction` | `NavierStokes/PrimaryTargetBounds.lean:631` | the prepared covariance equals `primaryCovariance` built from the `construction` data | delta `preparedCovariance` (`:628`) → `familyCovariance vr vt (family H v a)` → (`:464`) `primaryCovariance (fun j i => nativePrefactor … * timeCoefficient h ((a' j).band i) * (a' j).length i) (fun j => (a' j).frame) …`. RHS uses `(construction H v a hr0 j).frame/.lam/.u/.L`, and `construction` (`NavierStokes/PrimaryGeometryAssembly.lean:356`) `= (family H v a c).construction …`, whose body (`NavierStokes/BasePhaseGeometry.lean:985-1010`) is a **tactic-built** (`by have …; refine { … }`) structure literal with `lam := a.lam`, `L := a.length`, `u := fun _ => u`. `family` itself (`PrimaryGeometryAssembly.lean:302`) is likewise `by have hlow := …; refine { band := BaseChartJets.cellBand, … }`. So the kernel must zeta-reduce the `have`s and project. **The RHS carries an extra `hr0 : 0 < r0` argument the LHS does not; the sides are identified only because the kernel is proof-irrelevant in `Prop`.** | (i)+(ii)+zeta+(pi) | ~10² | OK (mechanism is sound), but this is the one where "read the proof" is least possible: both sides' witnesses are produced by tactics. |
| 8 | `normalizedPacketVelocity_forwardInitialized` | `Euler/ParentForwardInitialSupport.lean:40` | the parent's normalized packet velocity, fed the forward-initialized residual, equals the forward-initialized exact physical velocity at the normalized time | argument-threading equality of two `def`s; note the statement itself passes `rfl` as a *proof argument* (`… hSupport) rfl δ hδ …`), i.e. a `Prop`-valued equality hypothesis discharged by defeq at elaboration time — inside the `rfl` proof this again lands on proof irrelevance | (i)+(ii)+(pi) | ~10² | OK |

Rank 9 (`normalizedPacketPressure_forwardInitialized`, `Euler/ParentForwardInitialSupport.lean:49`)
is the pressure twin of rank 8 and was assigned to the `rfl-mid` child.

### Task B — the 7 sites whose statement names a recursive construct

The parent's `touches_rec` column is a **name-substring** heuristic (`truncate`, `word`). Four of the
seven names do not denote a recursive function at all. Per site:

| site | name | is the named construct actually recursive? | argument | class | verdict |
|------|------|------------------------------------------|----------|-------|---------|
| `Euler/CorrectionOperators.lean:60` | `coordinateProduct_apply` | **No.** `truncateOperator` (`Euler/CylinderSobolevDerivatives.lean:23`) is `ContinuousLinearMap.pi … |>.comp (arrayOperator …) |>.codRestrict …` — non-recursive | n/a | (i)+(ii): unfold `coordinateProduct` (`:55`) and Mathlib's `bilinearComp`, then CLM projections | OK |
| `Euler/CylinderSobolevDerivatives.lean:77` | `value_truncateOperator` | **No** (same as above) | n/a | LHS → `u.val (truncateIndex (emptyWord q))`, RHS → `u.val (emptyWord (q+1))`; `truncateIndex` (`:13`) and `emptyWord` (`Euler/CylinderSobolevSpace.lean:21`) are `⟨⟨…⟩, Fin.elim0⟩` literals, so the kernel needs Subtype/`Fin` projections **plus proof irrelevance** for the two different `0 < q+1` proofs | (i)+(pi), ~10 steps | OK |
| `Euler/OrdinarySmoothWords.lean:35` | `wordField_zero` | **Yes.** `wordField` (`:31`) is a genuine equation-compiler recursion on the word length (`| 0, _ => A`, `| _+1, w => (wordField A (Fin.tail w)).directionalField …`) | applied at the **closed literal `0`**, which is exactly the base case | (iv) with **chain length 1** (one `Nat` literal→`Nat.zero` conversion + one iota step) | OK |
| `Euler/RegularizedForcingWord.lean:29` | `forcingWordPath_apply` | **Yes**, `wordBlock` (`Euler/SobolevWordBlocks.lean:17`) is structural on the length | **symbolic** `m`; identical on both sides, never reduced | (i)+(ii), 0 iota steps | OK |
| `Euler/SobolevWordConstraints.lean:25` | `sobolevGradientProjection_word` | **No.** `word` (`Euler/CylinderSobolevSpace.lean:66`) is `u.val ⟨⟨n, _⟩, w⟩` — a subtype projection, not a recursion | n/a | delta `sobolevGradientProjection` (`:15`) → `liftOperator` (`Euler/CylinderSobolevOperators.lean:68`) → `pi`/`proj`/`codRestrict` projections give `gradientProjection … (u.val ⟨⟨n,_⟩,w⟩)` | (i)+(ii), ~10-20 | OK |
| `NavierStokes/R3/SchwartzCompactApproximation.lean:30` | `truncate_apply` | **No.** local `truncate` (`:25`) is `CompactSchwartz.ofCompactSupport (fun x => cutoff R x • ψ x) …` | n/a | one `SchwartzMap` coercion/projection of a literal | (i), ~5 | OK |
| `NavierStokes/SlowRecursion.lean:974` | `sequence_profile` | **Yes and this is the interesting one**: `hierarchy` (`:942`) is literally `Nat.lt_wfRel.wf.fix (recursionStep …) n` | **symbolic** `n`. `WellFounded.fix` at a variable `n` has no `Acc.intro` in head position, so the kernel cannot iota-reduce it; the term is neutral and appears on both sides. The residual obligation is `profile (restrict h X) ≡ profile X`, and `restrict` (`:120`) is `⟨F, { … }⟩` keeping the same underlying function while `profile` (`:278`) is `(F (…)).re` — one Subtype projection of an explicit literal | (i), ~5 steps, **0 `Acc.rec` steps** | OK |

### Systematic screen of the other ~490 in-cone sites

Three text tests over the 541 statements (all re-runnable):

1. **Recursive-definition mention.** I first collected every `def`/`instance` in the repo whose body
   is an equation-compiler recursion (`| 0` / `| n+1` patterns), or carries
   `termination_by`/`decreasing_by`, or names `WellFounded.fix`/`.wf.fix`/`Nat.rec`/`strongRecOn`:
   **87** such definitions. Only **19 of 541** bare-`rfl` statements mention any of them:
   `Euler/EulerProof.lean:6555,6558`; `Euler/OrdinarySmoothWords.lean:35`;
   `Euler/PacketSourceScaleChoice.lean:230,232`; `Euler/PacketStageGuards.lean:72,128`;
   `Euler/SobolevWordConstraints.lean:25`; `NavierStokes/EvenSmoothDescent.lean:243`;
   `NavierStokes/ExtendedHeatDebts.lean:121`; `NavierStokes/PhysicalParticularWave.lean:214,777`;
   `NavierStokes/PhysicalResidualNaturality.lean:634`;
   `NavierStokes/R3/SchwartzCompactApproximation.lean:30`;
   `NavierStokes/SlowExpansionResidual.lean:56`; `NavierStokes/SlowRecursion.lean:128,974`;
   `NavierStokes/WeightedODEJets.lean:33,35`.
   I read all 19. Every one is either a **base-case unfolding lemma at a closed `0`/`[]`**
   (`iteratedFieldDerivative_zero`, `wordField_zero`, `scaleSequence_zero`, `radialIterate_zero`,
   `correctionJet_zero`, `jet_nil`) = **one** iota step, or a **successor/cons unfolding lemma at a
   symbolic argument** (`iteratedFieldDerivative_succ` at `Fin (n+1)`, `scaleSequence_succ` at `n+1`,
   `previous_succ` at `n+1`, `jet_cons` at `v :: l`) = **one** iota step on a symbolic constructor,
   or the recursive term is **neutral and identical on both sides** (`coverPower gap …` at symbolic
   `gap` in `chartChange_apply`/`associatedChart_apply`, `scaleSequence S.J S.X (n+1)` inside a
   structure-literal projection in `PacketStageGuards.lean:72,128`, `hierarchy … n` in
   `sequence_profile`).
   **No bare-`rfl` site in the in-cone artifact applies a recursive definition to a closed numeral
   greater than 0.** There is therefore no iota chain of length > 1 anywhere in this proof style.
2. **Numeral size.** Only **3 of 541** statements contain any integer literal ≥ 10
   (`Euler/PacketInitializedSpatialBudget.lean:115` and
   `Euler/PacketForwardInitializedSpatialBudget.lean:113`, both the real coefficient `12`;
   `NavierStokes/ActualIterationLedger.lean:36`, the real constant `10`). These are `ℝ`
   coefficients inside `energyConstant`-style expressions, never `Nat` arguments to a computation.
   **Zero** statements contain `decide`, `Nat.pow`, `Nat.gcd`, `Nat.mod`, or `Nat.div`.
3. **Matrix / `Fin` literals.** `![` appears in exactly **2** statements
   (`NavierStokes/AngularMomentReset.lean:200` and `NavierStokes/TerminalCompensation.lean:270`,
   both `quadraticCLM_apply`): both compare a `Matrix.vecCons` literal against the `def`'s own
   `![…]` body **structurally, without ever applying an index**, so no `Fin`/`Nat` literal
   comparison is forced. `Matrix` is mentioned in 4 further statements; the sharpest,
   `NavierStokes/TerminalCompensation.lean:220` `linearMatrix_entry`, indexes at **symbolic**
   `i j : Fin 3` and is only provable by `rfl` because `LocalizedMomentRepair.matrix` is a lambda
   (`fun i j => …`), not a `!![…]` literal. `AngularMomentReset.lean:114`'s `linearMatrix` **is**
   a `!![…]` literal, but the two `rfl` theorems about it (`:197,198`) never apply an index to it.
   `Fin.cons`/`Fin.snoc`/`List.get` appear in **0** statements.

## Kernel-risk assessment

**(1) Recursors / recursive inductives / `Acc.rec` / structure eta.**
Does the kernel have to reduce a recursor to accept these files? Essentially no.
Across all 541 in-cone bare-`rfl` sites the total iota work is **at most one step per site, at 19
sites only** (item 1 above). Not a single site presents a recursive function at a closed argument
`> 0`, so there is no unfolding chain whose length the kernel must walk. The wf-recursion files are
the sharpest test and they pass: `SlowRecursion.lean:974` is a `rfl` *about* a `WellFounded.fix`
term, and precisely because the recursion index is the symbolic variable `n`, the kernel keeps
`Nat.lt_wfRel.wf.fix (recursionStep …) n` as a **neutral** subterm on both sides and performs **zero
`Acc.rec` steps**; the real obligation is one Subtype projection (`restrict`, `SlowRecursion.lean:120`
vs `profile`, `:278`). Note also that the artifact's own unfolding lemmas for the wf recursion
(`hierarchy_zero`, `:948`; `hierarchy_succ`, `:956`) are **not** bare `rfl` — they go through
`rw [WellFounded.fix_eq]` first, i.e. the author routed around kernel wf reduction propositionally.
Structure **eta** is used pervasively but only in its cheap form: comparing a partially applied
`def` against a lambda (rank 7) and comparing `⟨…⟩`/`where` literals field-by-field. What the
kernel *does* do heavily is **projection of structure literals** and **proof irrelevance**; both are
O(1) per use and are not on any known kernel-bug list. Depth: the deepest projection chain I
measured is 5-6 nested structure literals (rank 3), i.e. low hundreds of head reductions.

**(2) Kernel GMP `Nat` arithmetic.**
Absent from this proof style. No `decide`, no `Nat.pow/div/mod/gcd/beq/ble` in any of the 541
statements; the largest literal is `12`, and it is a real coefficient. The only place `Nat`
comparison *could* have been forced — `Fin`/`Matrix.cons` literal index resolution — does not occur
(item 3): every index application in the set is at a symbolic `Fin` variable or at a variable
function. `Fin`-valued proofs like `Nat.lt_succ_of_le hn` inside `emptyWord`/`truncateIndex`
(`CylinderSobolevSpace.lean:21`, `CylinderSobolevDerivatives.lean:13`) are `Prop` and are discharged
by proof irrelevance, not by arithmetic.

**(3) Custom metaprogramming.** None found in anything I read. No `macro`, `elab`, `syntax`,
`set_option`, `native_decide`, `axiom`, `unsafe`, `partial`, `@[implemented_by]`, `attribute
[instance]` tricks appear in the bare-`rfl` blocks or in the ~34 supporting `def`s I opened.
Two stylistic items worth naming, neither being metaprogramming: `local instance` re-derivations
of the Sobolev norm (`Euler/CorrectionOperators.lean:49-52`) and `omit …in` / `include …in`
modifiers before several `rfl` theorems (e.g. `NavierStokes/CompactSmoothFamily.lean:85-88`,
`Euler/SmallCorrectionParity.lean:31`).

**Total defeq exposure, in one paragraph.**
The artifact's bare-`rfl` proofs are almost entirely *bookkeeping identities between two names for
the same term*: a `where`-style structure literal is built in one file, and a `rfl` lemma in another
file records that some projection of it equals the expression that was written into that field.
The kernel work is dominated by (a) delta-unfolding non-recursive `def`s, (b) projecting structure
literals, (c) beta, (d) zeta for tactic-built `have`/`let` wrappers, and (e) proof irrelevance for
`Prop`-valued arguments that differ between the two sides. Statement *length* in this corpus is a
proxy for the number of threaded arguments (rank 3 threads 21 hypotheses), not for computation:
the 657-character champion costs the kernel on the order of 10² head reductions, and the whole
541-site set costs, generously, 10⁴-10⁵ head reductions with **≤19 iota steps in total** and **zero
`Nat` literal arithmetic**. On the kernel-bug threat model this is the *benign* end of the
spectrum — far cheaper and far less exotic than a single `decide` on a 4-digit numeral would be.
The real cost of this style is epistemic, not computational: 218 `*_apply` lemmas plus tactic-built
structure literals mean a human reviewer cannot see *why* two sides agree without re-running the
elaborator, which is exactly the situation in which a mis-stated field would go unnoticed.

(Task A ranks 9-25 and Task C are in the delegated sections further below; the verdict counts and
bottom line are at the end of this file.)

## Escalations

Ranked. None of these is a kernel-soundness alarm; they are the places where an expert's answer
would change my confidence.

* **E1 — `NavierStokes/PrimaryTargetBounds.lean:631` (`preparedCovariance_eq_construction`).**
  Both sides' witnesses (`family`, `PrimaryGeometryAssembly.lean:302`; `FamilyData.construction`,
  `BasePhaseGeometry.lean:985`) are **built by tactic blocks** (`by have …; refine { … }`) with
  `?_` holes filled later, and the equality additionally relies on **proof irrelevance** for the
  `hr0 : 0 < r0` argument that appears on the RHS only.
  *Question for an expert:* is every field the `rfl` silently identifies (`frame`, `lam`, `u`, `L`,
  `band`, `length`) the field the surrounding mathematics *intends*, given that the two sides were
  produced by different tactic scripts? *What would settle it:* `#print` / `set_option pp.all` of
  both sides after `whnf`, or a `simp`-free `example` restating each of the 5 argument equalities
  separately.
* **E2 — `NavierStokes/CorrectionInitialization.lean:1012` (`sourcePair_matrix`).** The `rfl`
  identifies `primaryCovariance` at index type `Unit` (via `PrimaryFieldAssembly.sourceMatrix`,
  `:519`, applied at `()`) with `primaryCovariance` at index type `ℕ` (via `phaseCovariance`,
  `PrimaryPulseBounds.lean:1647`, applied at `n`).
  *Question:* is the `Unit`-indexed instantiation really carrying the same per-band data as the
  `ℕ`-indexed one for every `n`, or does the collapse to `Unit` discard an index dependence that
  the downstream bound assumes? *What would settle it:* state the lemma with the `Unit` side
  replaced by an explicit `ℕ`-indexed family and check it still holds by `rfl`.
* **E3 — the inventory itself.** `RFL_SITES.csv` misses 15 in-cone bare-`rfl` theorems and contains
  3 non-`rfl` entries (details below). Two of the misses are the **two longest statements in the
  whole corpus** (ranks 1-2 above). *Question:* were other `audits/nse-deep` censuses built with the
  same regex family (statements containing `:=` inside named arguments such as `(B := B)`, or
  declarations preceded by `omit … in`)? *What would settle it:* re-run the sibling censuses
  (`SITES_decide.md`, `SITES_wf_fix.md`, `BIGNUM_SITES.md`) with a bracket-depth-aware parser.
* **E5 — `NavierStokes/LocalSignedRequest.lean:523` (`physicalBarSigma_profile`).** The only site in
  the whole audited set whose acceptance needs **structure eta** (`x.2.1 ≡ (x.2.1.1, x.2.1.2)` for a
  `Prod`, through `chartQ`/`qCoord`/`chartInput`, `NavierStokes/MeanRankUpdate.lean:775` and
  `NavierStokes/PhysicalCoordinateBounds.lean:35`). *Question:* is eta-for-structures the feature the
  earlier escalation A3 was about, and is it being relied on anywhere in a form stronger than
  `Prod` eta? *What would settle it:* a `set_option pp.all true` `#check` of both sides plus a scan
  of the whole in-cone set for `rfl` lemmas whose two sides differ by a projection/pair pattern.
* **E4 — `Euler/CylinderSobolevDerivatives.lean:77` (`value_truncateOperator`).** The `rfl` holds
  because `truncateIndex (emptyWord q)` and `emptyWord (q+1)` are the same `⟨⟨0, _⟩, Fin.elim0⟩`
  literal up to a `Prop` component. *Question:* is `Fin.elim0` the *same* term on both sides, or is
  one side's word component an eta-expanded/`absurd`-based function? (The kernel has eta but not
  funext, so if they differed structurally the `rfl` would fail — the fact that it typechecks is
  itself the evidence; I could not run the kernel to confirm.) *What would settle it:* one
  `#reduce`/`whnf` on each side, or `example … := rfl` after `unfold`.

## Residue — what I could not check and why

* **No kernel execution.** With no built Mathlib I could not run `lake env lean` on a single file,
  so every "the kernel does X" statement here is a *reading* of the definitions, not an observation.
  In particular I cannot report actual `maxRecDepth`/`whnf` step counts; my step estimates are
  hand counts of delta/proj/beta opportunities and should be read as order-of-magnitude only.
* **Mathlib-side definitional content.** Several sites bottom out in Mathlib definitions I did not
  open (`ContinuousLinearMap.bilinearComp`, `codRestrict`, `compLeftContinuous`,
  `LinearMap.toContinuousLinearMap`, `Matrix.mulVec`, `SchwartzMap` coercions,
  `ClosedSubmodule`/`Submodule.subtypeL`). If any of those is *not* the simple structure literal I
  assumed, the step counts grow (they are still non-recursive, so the classification would not
  change).
* **The ~490 unopened sites** were only screened by the three text tests. A site whose statement
  mentions no recursive name and no numeral could still, in principle, unfold into a recursive
  definition *not named in the statement*. I did not compute the transitive delta-closure of every
  right-hand side; that is the natural next instrument (a whnf-free static "does the delta closure
  of this statement reach any of the 87 recursive defs" pass).
* **`RFL_SITES.csv`'s `touches_rec` column** is a name-substring heuristic and I treated it as such;
  I did not reconstruct how the parent generated it.
* Structure **eta** in its subtle form (two `Prop`-carrying structures identified only by eta) would
  not be visible to source reading; I found no site that appears to need it, but I cannot exclude it.

## Is the parent's 529 count right?

**No — 529 undercounts, and it contains 3 false positives. My independent count is 541.**

* **15 in-cone bare-`rfl` theorems missing from `RFL_SITES.csv`** (with the likely cause: a `:=`
  inside a *named argument* or an inline `(by … : …)` in the statement, or a leading
  `omit … in` / `include … in` modifier, which a "first `:=` splits statement from proof" regex
  mis-parses):
  `Euler/EnergyWordCoordinates.lean:27` (`(by omega : n+q ≤ s)`),
  `Euler/LpSmoothJetField.lean:29,34` (`mapField (V := V) (W := …)`),
  `Euler/PacketResidualTailFields.lean:51`,
  `Euler/RegularizedMildEquation.lean:96`,
  `Euler/SobolevBaseCommutator.lean:33`,
  `Euler/SobolevTransportCommutator.lean:34`,
  `NavierStokes/ActualCurrentParticularPhysical.lean:112`,
  `NavierStokes/ActualParticularPotentialCoherence.lean:94,106`,
  `NavierStokes/ActualParticularStageControls.lean:509` (`(B := B) (N0 := N0)`),
  `NavierStokes/CompactSmoothFamily.lean:86` (`omit [NormedSpace ℝ Z] in`),
  `NavierStokes/InitialPhysicalData.lean:276` (`(h := ActualPrimary.h)`),
  `NavierStokes/PhysicalResidualTZ.lean:259` (`(D := Lift)`),
  `NavierStokes/SmoothPathFamily.lean:87`.
  **Two of these are the longest statements in the entire corpus** (657 and 593 chars), i.e. the
  parent's "top 25 by `stmt_len`" list was missing its true rank 1 and rank 2.
* **3 entries in `RFL_SITES.csv` that are not bare-`rfl` theorems** but structure-instance
  (`where`-style) proofs in which *some* field is `rfl`:
  `Euler/PacketCylinderSpatialInvariance.lean:21` (`AngleIndependentJet.zero`, all three fields are
  `rfl`), `Euler/SmallCorrectionParity.lean:32` (`parityData`: `metric`/`linear` are `rfl`,
  `quadratic`/`approximation` are tactic proofs), `NavierStokes/BasePhaseGeometry.lean:934`
  (`coefficientControl`: only `eigenvalue` is `rfl`).
* **4 line-number offsets**: where `@[simp]` sits on its own line, `RFL_SITES.csv` records the
  attribute line and `CONE.csv` agrees, while the declaration keyword is on the next line
  (`Euler/CylinderSobolevDerivatives.lean:76/77`, `Euler/DivergenceFreeHeat.lean:46/47`,
  `Euler/SobolevHeat.lean:33/34`, `Euler/SobolevPressureResolvent.lean:20/21`). Not an error, but
  worth knowing when joining the two CSVs.
* Repo-wide (not restricted to the cone) I count **1358** bare-`rfl` theorems, of which 541 are
  in-cone; `stmt_len` statistics on my 541 (median 135, mean 160, max 657) are close to the
  parent's (median 139, mean 164, max 629), so the parent's *distributional* claims stand.


## Task C — the 28 bare-`rfl` sites in the two well-founded-recursion files

Delegated to a read-only child on the same taxonomy; its full table is in
`_scratch-rfl-wf.md`. I re-derived the central facts myself (see Task B, `SlowRecursion.lean:974`)
and I agree with its answer.

**Central question — does any of these 28 `rfl`s force the kernel through `WellFounded.fix` /
`Acc.rec` at a canonical `Acc.intro`? Answer: NO, for all 28.** Evidence:

* `NavierStokes/SlowRecursion.lean` (16 in-cone sites: 89, 91, 93, 95, 97, 99, 128, 435, 437, 439,
  441, 443, 447, 449, 451, 974) and `NavierStokes/GlobalSlowProfiles.lean` (12: 76, 78, 80, 82, 84,
  85, 97, 213, 1201, 1203, 1205, 1207).
* Neither file contains `termination_by` or `decreasing_by`. `WellFounded.fix` appears only at
  `SlowRecursion.lean:946` (the definition of `hierarchy`) and inside three **tactic** proofs that
  rewrite with `WellFounded.fix_eq` (`SlowRecursion.lean:953, 964`; `GlobalSlowProfiles.lean:910`) —
  and those three theorems are *not* bare `rfl`, so the author deliberately discharged the wf
  unfolding **propositionally**, never definitionally.
* Only 1 of the 28 statements mentions a wf-recursive function at all
  (`SlowRecursion.lean:974 sequence_profile`). Its recursion index is the **symbolic variable `n`**,
  so `Nat.lt_wfRel.wf.apply n` is stuck, `Acc.rec` cannot fire, and the `hierarchy … n i` subterm is
  a neutral atom appearing identically on both sides. The residual obligation is one Subtype
  projection (`restrict`, `:120`, keeps the same underlying function; `profile`, `:278`, takes `.re`
  of an application). ~4-6 head reductions, **zero** `Acc.rec` steps.
* The other 27 are algebra-instance `*_apply` lemmas on the `AxisFunction`/profile subalgebra
  (`(F + G) p = F p + G p`, `complexProfile (F * G) p = …`, `xProfile_add`, …). Mechanism:
  projection of Subtype/Prod literals plus delta of non-recursive instance/coercion definitions
  (Subalgebra → Pi → ℝ/ℂ instance chain, each Mathlib `coe_*` step itself a `rfl`). 4-60 steps each.
  `complexProfile_pow` (`:443`) carries a symbolic exponent `k : ℕ` **unreduced on both sides**
  (`npowRec` is never entered) and `GlobalSlowProfiles.lean:213` merely carries the literal `2`;
  no `Nat`/GMP arithmetic is forced.
* Child verdict counts for its 28 (+2, see next bullet): OK 30, UNCLEAR 0, KERNEL-RISK 0,
  SUSPICIOUS 0; no vacuity, junk-value or over-claiming found.

**One correction to the child's report.** It flagged the site list as incomplete, naming
`SlowRecursion.lean:86` (`realConstant_apply`) and `:445` (`complexProfile_zero`) as additional
bare-`rfl` theorems. They *are* bare `rfl`, but `CONE.csv` marks both `in_cone = False`
(`realConstant_apply`, `complexProfile_zero`), so they are correctly outside the in-cone census of
16 + 12 = 28. Its audit of them (both OK) is a free bonus, not a gap in the parent's inventory.

## Task A continued — ranks 9-17 (delegated read-only child `rfl-mid`; full text in `_scratch-rfl-mid.md`)

All 9 verdicts **OK**; no KERNEL-RISK, no SUSPICIOUS. Mechanism at every site: delta of
non-recursive `def`s plus projection of `where` / `{ x with … }` structure literals. Estimated head
reductions in brackets.

| # | name | file:line | mechanism | class | est. | verdict |
|---|------|-----------|-----------|-------|------|---------|
| 9 | `normalizedPacketPressure_forwardInitialized` | `Euler/ParentForwardInitialSupport.lean:49` | pressure twin of rank 8; pure argument threading | (ii) | ~3 | OK |
| 10 | `selected_data_amplitude` | `NavierStokes/ActualParticularStageControls.lean:813` | projections of the selected-construction literal | (i)+(ii)+(pi) | ~25 | OK |
| 11 | `selected_data_pressure` | `…:821` | same | (i)+(ii)+(pi) | ~35 | OK |
| 12 | `PrefixFields.tailGradeField_path` | `Euler/PacketResidualTailFields.lean:51` | `.path` of a `ContinuousMap`-literal sum | (i)+(ii) | ~6 | OK |
| 13 | `externalCommutator_apply` | `Euler/SobolevTransportCommutator.lean:34` | CLM `comp`/`sub` projections | (i)+(ii)+(pi) | ~30 | OK |
| 14 | `childAcceleration_apply` | `Euler/ChildParticleFieldBounds.lean:243` | projections through the child-data literal | (i)+(ii) | ~35 | OK |
| 15 | `stateMeanCoefficientValue_erase` | `NavierStokes/AxisymmetricResidualGrouping.lean:152` | the erased alias is *definitionally not read* by the value function | (i)+(ii) | ~8 | OK + scope note (see below) |
| 16 | `GaugeInitialization.initialized_reconstructed` | `NavierStokes/CorrectionInitialization.lean:1327` | idempotence/fixed-point claim; see below | (i)+(ii), mild (vi) | ~30-60 | OK + name/scope note |
| 17 | `baseCommutator_apply` | `Euler/SobolevBaseCommutator.lean:33` | CLM projections | (i)+(ii)+(pi) | ~40 | OK |

Child's cross-checks, matching mine independently: zero iota chains at closed numerals, zero
`Nat.rec`/`Acc.rec`, zero `decide`/`Nat.pow`, zero `Fin`/`Matrix.cons` literal index resolution
(the `![…]` occurrences are identical on both sides and all indices are variables), and proof
irrelevance is load-bearing at 4 of the 9 sites (duplicated `omega`/`norm_num`/`length_pos`
arguments). Long statements are long **argument lists**, not computation.

**Most interesting finding of the mid slice (worth an escalation-level note).**
`NavierStokes/CorrectionInitialization.lean:1327` states
`reconstructState g c (initialized …) = initialized …` by `rfl` — a **fixed-point / idempotence**
claim. The child traced why it is definitional: `reconstructState`
(`NavierStokes/VariableGaugeMean.lean:517-523`) is `{ u with pressure := fun n => meanPressure …
(u.gr c n) }`, i.e. it rewrites **only** `pressure`, from `u.gr`; and `State.gr`
(`NavierStokes/CorrectionState.lean:117-118` → `MeanIncrementBounds.lean:338-342`) reads only
`c.operators`, `c.base`, `s.mean`, `s.covariance` — **no pressure and no error feedback**. Every
stage constructor already ends in `reconstructState` (`VariableGaugeMean.lean:559-563, 580-583`;
`CorrectionInitialization.lean:1264-1267, 1275-1290`), so the pressure slot already holds the value
being reinstalled. Consequence: **`reconstructState g c` is definitionally idempotent for *every*
state**, so the theorem carries no information about the initialization in particular, even though
its name ("initialized_reconstructed") invites the reading "the initialization solved the gauge
equation". The same definitional blindness underlies rank 15
(`AxisymmetricResidualGrouping.lean:152`: erasing an axisymmetric alias does not change the mean
coefficient value because the value function never reads that field). This is *not* junk-value abuse
and it is the right structure for `∂_r p = gr`, but it is the clearest example in my scope of a
`rfl` lemma whose **name claims more than its statement**.

## Task A continued — ranks 18-25 (delegated read-only child `rfl-tail`; full text in `_scratch-rfl-tail.md`)

All 8 verdicts **OK**; no KERNEL-RISK, UNCLEAR or SUSPICIOUS.

| # | name | file:line | mechanism | class | est. | verdict |
|---|------|-----------|-----------|-------|------|---------|
| 18 | `parameters_raw` | `NavierStokes/ActualSignedStageControls.lean:111` | projections of the parameter literal; the only `Fin` is the **variable** column `l.2` | (i)+(ii) | ~24 | OK |
| 19 | `fullCopy_slot` | `NavierStokes/ActualPrimaryBounds.lean:1128` | 3 delta + one `Prod.snd`; the `-` is `Nat` subtraction of **open** terms, never computed | (i)+(ii) | 4 | OK |
| 20 | `complexCopyPressure_eq_parts` | `NavierStokes/ParticularWaveBounds.lean:1592` | 1 delta + 8 beta | (ii) | 9 | OK |
| 21 | `physicalBarSigma_profile` | `NavierStokes/LocalSignedRequest.lean:523` | needs kernel **Prod structure eta** (`x.2.1 ≡ (x.2.1.1, x.2.1.2)` through `chartQ`→`qCoord`→`chartInput`, `MeanRankUpdate.lean:775`, `PhysicalCoordinateBounds.lean:35`) plus a CLM/`DFunLike` coercion walk; `Real.sqrt`, `*`, `/` are compared symbolically and never evaluated | (i)+(ii)+**(vi)** | ~50-90 | OK |
| 22 | `initialized_reconstructed` | `NavierStokes/CorrectionInitialization.lean:1193` | same idempotence pattern as rank 16 | (i)+(ii) | ~40 | OK (same name/scope note) |
| 23 | `growthCoefficient_eq` | `Euler/PacketCorrectionGrowth.lean:29` | **not** an arithmetic identity: same head `energyConstant`, 11 arguments matched pairwise after delta + zeta (`MetricBudget.growth0/growth1/multiplier`, `Euler/CorrectionEnergyData.lean:147-158`, against the `let`-bound body at `PacketCorrectionGrowth.lean:20-27`) | (i)+(ii)+zeta | ~15 | OK, but note the hypotheses `κ hκ Z G q` are **dead parameters** of the statement |
| 24 | `afterParticular_pressure` | `NavierStokes/ActualCycleCoherence.lean:492` | projections of the stage literal | (i)+(ii) | ~27 | OK |
| 25 | `stateDebt_eq_sourceDebt` | `NavierStokes/MeanChartCompatibility.lean:1258` | projections + a `Pi`/`SMul` instance-unfolding chain | (i)+(ii) | ~25-60 | OK |

Two additions this slice makes to the global picture:

* **Structure eta is genuinely load-bearing at least once** (rank 21): the kernel must accept
  `x.2.1 ≡ (x.2.1.1, x.2.1.2)` for a `Prod`. This is exactly the kernel feature the audit's earlier
  escalation A3 came down to. It is a standard, specified Lean 4 kernel feature (eta for structures),
  it is used here in its simplest form on `Prod`, and it is *cheap*; but it is the one place in my
  scope where acceptance depends on a kernel feature beyond delta/beta/proj/iota/proof-irrelevance.
* **Dead hypotheses** (rank 23): `growthCoefficient_eq` binds `κ hκ Z G q` which do not occur in the
  equation's two sides after unfolding (they only pick out *which* `sourceMetricBudget` is named on
  the RHS, and every choice gives the same constant). Harmless, but it is the signature of a lemma
  that was generalized past what it needs, and such statements are where a reader over-reads scope.

## Verdict counts (declarations examined individually)

| verdict | count |
|---------|-------|
| OK | **78** (in-cone; + 2 out-of-cone bonus sites from the wf child) |
| UNCLEAR | 0 |
| KERNEL-RISK | 0 |
| SUSPICIOUS | 0 |
| of which "OK + name-claims-more-than-statement note" | 3 (`CorrectionInitialization.lean:1193,1327`; `AxisymmetricResidualGrouping.lean:152`) |
| of which "OK + escalation question" | 4 (E1-E4) |

Breakdown of the 78: my ranks 1-8 (8) + the 7 task-B sites (6 new) + the 19 recursive-mention
screen (14 new) + the 5 `Matrix`/`![` sites (5) + `SlowRecursion.lean:128` and `:974` (in the task-B
and wf sets) + mid child ranks 9-17 (9) + tail child ranks 18-25 (8) + wf child's 28. The remaining
~463 in-cone sites were covered only by the three systematic text screens.

## Bottom line

On this worker's slice of the threat model the artifact is **clean and, more importantly, cheap**:
541 in-cone bare-`rfl` theorems whose combined kernel obligation is projection of structure
literals, delta of non-recursive definitions, beta/zeta, proof irrelevance, one `Prod` eta, **≤19
single iota steps in total**, and **no `Nat` literal arithmetic whatsoever**. There is no place where
a kernel bug in recursor reduction, `Acc.rec` unfolding, or GMP `Nat` arithmetic could be doing work
for the author, because that work is never requested. The residual concerns are epistemic
(tactic-built structure literals, index-type-collapsing defeq, names that promise more than the
statements deliver) and one inventory-quality concern (E3).
