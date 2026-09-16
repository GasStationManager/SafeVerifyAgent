# Audit: openai/NavierStokesAndEuler — the kernel-trust pass

**Artifact:** `github.com/openai/NavierStokesAndEuler` @ `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`
**Auditor:** SafeVerifyAgent, coherence rung, 20 read-only worker threads + parent verification
**Date:** 2026-09-16 — **DRAFT: one thread still open** (§Open)
**Companion:** [`2026-09-15-openai-NavierStokesAndEuler.md`](2026-09-15-openai-NavierStokesAndEuler.md)
audited the two challenge *statements*. This pass audits the *proofs*.

> **Verdict so far: no defect found.** No refutation, and the specific kernel-unsoundness exposure
> this pass was commissioned to find is **small and now enumerated**. Four threads are open, one of
> which (§Open 1) is a real question about whether a per-cycle gain chains.

The question is not "does it compile" — Comparator already answered that. It is:

> the artifact already passed a mechanical checker. **Which of its proofs could a bug in the Lean
> kernel turn into a fake?**

Three fragile families were named up front: (1) recursive inductive types, (2) `Nat` arithmetic
delegated to GMP, (3) custom metaprogramming.

---

## Summary

| | |
|---|---|
| Lean files / lines / declarations | 2,659 / 641,332 / **52,516** |
| theorems | 38,503 (+ 10,827 `def`, 1,578 `instance`, 899 `abbrev`, 667 `structure`, 28 `lemma`, **14 `inductive`**) |
| declarations in the **cone** of the 4 headline theorems | **38,369** — theorems: **27,725** |
| declarations that cannot reach a headline theorem at all (outside the import closure) | 3,616 in 216 files |
| **vector (3)** metaprogramming: `macro`/`elab`/`syntax`/`notation`-decl/`run_cmd`/`#eval`/`set_option` | **0** |
| `axiom` / `opaque` / `unsafe` / `@[extern]` / `implemented_by` / `partial def` / `native_decide` | **0** |
| `sorry` | 4 — both challenge files' intentional placeholders |
| **vector (2)** `decide` sites | 210 (177 in-cone), **every literal ≤ 1000**, 208 of 210 ≤ 40 |
| largest closed `Nat` the kernel evaluates **anywhere** | **2.0×10¹⁸ — 61 bits, one machine word, never multi-limb GMP**; MEASURED in the emitted proof term, and contingent on the certificate's *degree* (see below) |
| **vector (1)** recursive inductives, well-founded defs, explicit recursors | 14 (10 in-cone) / 12 `termination_by`, 0 `decreasing_by` / 5 |
| defeq workload: in-cone theorems whose proof involves a `rfl` | **1,717** — **541** proved by `rfl` *alone* (bounded: ≤ 19 iota steps, zero chains) + **1,176** whose tactic block is *closed* by `rfl` (not bounded — the goal is not in the source) |
| worker threads / reports | 25 / 69 |
| in-cone theorems in files some report has read or cited | 11,511 of 27,753 (**41.5%**, a generous upper bound) |

---

## The three vectors, measured

### (3) Metaprogramming: empty

Not "small" — **zero**, across 52,516 declarations. No `macro`, `macro_rules`, `syntax`, `elab`,
`notation` declaration, `run_cmd`, `#eval`, `#reduce`, `MetaM`/`TacticM`, and **no `set_option` of any
kind** (so no `maxHeartbeats`, no `maxRecDepth`, and in particular no `debug.skipKernelTC`). The only
elaboration-affecting declarations in the repository are **25 `attribute` lines, all `local`**: 11
`local instance`, 10 `local irreducible`, 2 `local gcongr`, of which 4 instances are
`Classical.propDecidable`. Reducibility is elaborator-only — the kernel ignores it — and the ten
`local irreducible Parent.child` sites turned out to be an elaboration-cost device whose measurement
the repo itself documents (353,857 → 3,224 heartbeats, `Euler/ParentGeometryForwardChoiceNoOptions.lean:6-32`).

There is therefore **no custom metaprogramming to audit**. The residue is Mathlib's own, which this
artifact does not control.

### (2) `Nat`/GMP: present, and far below the GMP path

All 210 `decide` sites were classified. The entire surface is `Nat.ble`/`beq`/`mod` on **1-4 digit**
literals; the largest numeral in any `decide` goal is **1000**
(`Euler/ParentHistoryFrequencyGuard.lean:81`), and 208 of 210 are ≤ 40. No `Nat.pow`/`div`/`mod`/`gcd`
appears explicitly anywhere, no custom `Decidable` instance exists, and `native_decide` is absent.

The largest closed `Nat` the kernel is ever asked to evaluate in the whole artifact is
**2,000,979,990,000,000,000 = 2.0×10¹⁸** — the `nlinarith` certificate of
`NavierStokes/PulseCone.lean:1017`. That is 61 bits: **one machine word**, inside Lean's tagged-scalar
`Nat` path (`< 2⁶³ = 9.223×10¹⁸`), and it does not reach multi-limb GMP arithmetic. The margin is a
factor of **4.6**.

This number is **measured, not estimated**: the artifact's heavy sites were re-elaborated against a
built Mathlib (Lean 4.33.0) and the `Nat` literals in the proof terms `linarith`/`nlinarith`/`norm_num`
actually emitted were counted with an `Expr`-walking `#litcensus` command
(`audits/nse-deep/workers/cert-numerals.md`; reproduced independently by a second reader). An earlier
generation of this report said ≈5.0×10¹⁷ here — that value *is* in the term (it is the product
`200097999 × 2499900001`) but it is 59 bits and it is not the maximum, so the sentence paired a 59-bit
number with a 61-bit label.

**The reason matters more than the number, and it is weaker than "the constants are small."** Width is
set by the **degree** of the certificate Mathlib's oracle happens to find, not by the size of the
source literals — the largest integer literal anywhere in 641,332 lines is only 10⁹. `cancelDenoms` is
the *last* preprocessor (`Mathlib/Tactic/Linarith/Preprocessing.lean:384-386`) and `nlinarithExtras`
runs *after* it (`:326-333`), so degree-2 products multiply **already-denominator-cleared integers**:
degree-1 costs `lcm × numerators`, degree-2 costs that **squared**. A control run on this artifact's
own literals — a degree-2 route through `sq_nonneg (x² − (49999/100000)²)` — emits **10²⁰ (67 bits) and
541 literals above 2⁶⁴**. So "never multi-limb" is a true statement about *these* certificates under
*this* Mathlib, not a property of the artifact's numbers, and it is one certificate-degree away from
being false.

The one large power, `9^729` (`Euler/ConstantCorrectionData.lean:146`, verbatim
`def pressureBound : ℝ := 9^729`), is **never normalised** — it is consumed at `:149` by
`one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)`, whose `norm_num` goal is `1 ≤ 9`. Confirmed by elaboration:
the `positivity`, `one_le_pow₀` and `norm_num` routes all emit `729` as their widest literal, and
`norm_num` asked for `(2:ℝ)^40 ≤ 9^729` *fails* rather than expanding the 2,311-bit numeral. Of 711
sites with an exponent literal ≥ 8, only 3 have closed bases and one of those is a parse artifact;
`Θ^40`, `k^80` and `6^m` all have symbolic bases, and a `Monoid.npow` over `ℝ` with a `ℕ` literal
exponent is not integer arithmetic at all.

`Nat.choose`/factorial are essentially never computed: of **368** `Nat.choose` applications, **zero**
have a closed numeral in either slot, and the sole kernel-forced factorial is `4! = 24`
(`Euler/EulerProof.lean:12153-12154`, `norm_num only [Nat.factorial, …]`). An earlier generation of
this report also listed `0!` and `C(0,0)` here; **`C(0,0)` does not occur anywhere in the artifact**.
The largest closed factorial *expression* is `fixedCost 6 = 2⁶·Σ_{j≤6}(j!)² = 34,138,752`
(`Euler/SobolevSourceExponent.lean:14`), a `Finset.sum` over `ℝ` that is filtered on by
`eventually_ge_atTop` and never normalised.

`Classical.propDecidable` as a local instance (4 files) **cannot** corrupt a `decide`:
`Classical.choice` is irreducible, so such a `decide` fails to *elaborate* rather than computing
something false.

### (1) Recursive inductives: present, and used in the weak mode

14 `inductive` declarations, 10 in the cone. The four hand-rolled **recursive syntax trees**
(`PolynomialExpression`, `Expression`, `Expr`-in-`GenericDifferentialPolynomial`, `FieldFactor`/
`FactorSupportAt`) — the scariest-looking constructs for this vector — are **out of the cone**:
`PaperResults`-only, not on the Comparator deliverable path, confirmed both by the name graph and by
import closure. Where they *are* used, every theorem about them is `induction … with` yielding
propositional equalities, so the kernel checks a `rec`-shaped **term** and never **reduces** a
recursor over a closed tree. The only concrete-tree reflection site in the repository
(`NavierStokes/SeedHandbackJets.lean:94`) has **zero referencing declarations** and is not in the
deliverable import closure; its total cost would have been 186 single iota steps with all `Nat`
literals ≤ 18.

The load-bearing recursive types are the two **`Type`-valued, doubly indexed jet families**
`SpatialJet`/`CoefficientJet` (`Euler/EulerProof.lean:3064,3073`), with a higher-order recursive
argument (`lower : ∀ i, SpatialJet … n (derivatives i)`); not nested, not mutual, no large
elimination. Being `Type`-valued is *forced*: `sobolevNorm`, `word` and `levelNorm` recurse into `ℝ`.
The kernel does iota-reduce them, but always **one step on symbolic constructors** — there is no
concrete jet literal in the file — plus `FlatKernelBounds.Expr` and five finite enumerations.

Non-structural recursion: **12 `termination_by`, 0 `decreasing_by`**, all measures genuine, all
consumed through generated **equation lemmas**. The two hand-rolled `WellFounded.fix_eq` sites
(`NavierStokes/SlowRecursion.lean:948-965`, `GlobalSlowProfiles.lean:907-911`) use the safe idiom
`unfold; rw [WellFounded.fix_eq]; rfl`, where `fix` sits in identical positions on both sides, so the
kernel never reduces `Acc.rec` on a canonical `Acc.intro`. `Nat.rec` into `Type u`
(`Euler/LpSmoothJetField.lean:17`) is an ordinary elimination, needed because the space changes each
step, and its two unfolding lemmas are one iota step at symbolic `n`.

### The vector nobody named: definitional equality

Every measurement above concerns *computation*. A `rfl` proof is a different obligation — the kernel
must decide a **defeq**, which is where structure eta lives (the previous audit's E2 reduced to
exactly that), where `Fin`/`Matrix.cons` literal indices run through `Nat` comparison, and where an
iota chain at a closed argument would appear. So it was measured: **541 in-cone theorems are proved
by a bare `rfl`** (1,358 across the whole artifact), max statement 709 characters. Classified: only 19
touch a recursive definition and each is **≤ 1 iota step at a symbolic or base-case argument**, so the
total iota exposure of those proofs is **≤ 19 steps with zero chains**; no `Fin`/`Matrix.cons` literal
index is ever resolved; exactly one site needs structure eta (a second, needing `Prop` proof
irrelevance, was later found at `NavierStokes/VariableGaugeMean.lean:624`).

**That bound covers 541 of 1,717, and the report previously implied it covered the surface.** A later
worker noticed the census saw 1 of 19 proof-closing `rfl`s in the file it was reading, and the
distinction it exposed is sharper than the miscount: a *bare* `rfl`'s statement displays exactly what
the kernel must decide, so a statement-level screen can bound its iota depth — whereas a `rfl` that
**closes a tactic block** faces a goal `simp`/`rw`/`unfold` already rewrote, which is **not in the
source**, so no statement-level screen bounds it at all. There are **1,176 further in-cone theorems**
of that second kind (1,523 repo-wide; `SITES_closing_rfl.md`). They remain the largest *unbounded*
kernel surface in the artifact, and bounding them needs elaboration rather than reading — which
`cert-numerals` has since shown is possible on this box.

---

## What the proofs actually do (the part a checker cannot see)

- **The solution's private copies of the challenge structures are exact.** Both
  `Euler/SolutionDefinitions.lean` and `NavierStokes/ComparatorDefinitions.lean` are
  character-identical to their challenge modules modulo the deleted `sorry` placeholders, in an
  identical `import Mathlib` / `open` / notation context. Nothing was added to or removed from a
  solution structure. *(Closes a residue item of the previous audit.)*
- **The Navier-Stokes force is *defined* as the candidate's own residual**
  (`NavierStokes/CandidateFromLimits.lean:82`), so the PDE field of the solution structure is
  *definitionally* true. This is the standard shape for a forced blowup, and it moves the entire
  burden elsewhere.
- **What the NS theorem says:** the exhibited initial velocity is **identically zero** and the force
  is **compactly supported in space and time** (`NavierStokes/R3/ComparatorBridge.lean:85-86`). So
  what is proved is *breakdown from rest under a compactly supported force* — Fefferman's alternative
  (C)/(D), which permits exactly that — **not** blowup of unforced Navier-Stokes. The decay conditions
  are consequently cheap; the content is in the construction and the uniqueness.
- **Neither non-existence claim is a subclass claim.** On the NS side,
  `globalSolutionOfComparator` (`NavierStokes/R3/ComparatorBridge.lean:48-74`) builds the competitor
  record from the challenge structure's own fields, adding no support, decay, mildness or
  energy-inequality hypothesis. On the Euler side the contradicted class *is* stronger, but
  `exists_evolution_of_commonCompactCurl` (`Euler/ComparatorLocalEvolution.lean:64-97`) builds it
  **from an arbitrary challenge solution** — the L² jets from Caccioppoli + Fatou with a
  field-independent constant, the time continuity by interpolation, `time_law` from the challenge's
  own `h.euler` — and the competitor's pressure is *discarded and rebuilt*, so no pressure regularity
  is demanded. Every bridge lemma runs challenge ⇒ Evolution; the only converse is an honest `iff`
  used solely for the positive half.
- **The gluing that makes the force smooth through the blowup time is honest:** a real Borel series
  and a genuine one-sided Whitney theorem, no assumed jet growth and no all-jets-vanish shortcut. The
  blowup itself is closed-form, `‖u(t,0)‖ = (1-t)^{-(1/2+h)}·j` with `j > 0` proved.
- **Junk values run the safe direction, repeatedly.** `fderiv`-collapses are fenced by supplied
  `ContDiffOn` hypotheses; out-of-range jet words are zero only where guarded lemmas carry the guard;
  and in the Euler packet construction the junk value points **against** the claimant — the stage
  invariant is only realisable because `deriv (profile δ) 0 = δ⁻¹`, so `0 < δ` must be a *field*.
- **The Euler energy estimates are non-circular and their constants are solution-independent**; the
  `6^m` growth in the derivative order is harmless because the quantifier order is `∀ q, ∃ C`
  everywhere and the top-level claim has no analyticity conjunct.
- **The NS residual-jet predicates are discharged by a real `Nat` induction over cycles**, with no
  limit interchange and with the `tsum`'s summability proved rather than assumed.

## Escalations

**E-A4 — the NavierStokes library is built without `autoImplicit := false`.** `lakefile.toml` gives
the `Euler` library `leanOptions = { autoImplicit = false, warningAsError = true }`; the
`NavierStokes` library (816 files) and `ComparatorChallenges` get **no options**, so they build with
Lean's defaults. A mistyped identifier in a *statement* is then silently bound as a fresh implicit
rather than erroring. This cannot manufacture a proof of a false statement (auto-binding
generalises), but it can leave an intermediate lemma quietly about a fresh variable. The authors know
the check — 11 `…NoOptions.lean` modules document `-DautoImplicit=false -DwarningAsError=true` — they
applied it per-file, not per-library. *Settled by: building the NS library once with those flags.*

**E-A3 — closed, benign, with the line range pinned.** `attribute [local instance]
CompletePartialOrder.toSupSet` (`Euler/Solution.lean:41`) governs lines **43-56 only** — not
`euler_breakdown_R3` — and Mathlib's only `CompletePartialOrder ℝ≥0∞` route is
`CompleteLattice.toCompletePartialOrder` with `sSup := sSup`, so both instance paths denote
`ENNReal`'s own `sSup`. The residual risk is precisely *kernel structure eta*, which is a much
smaller target than an unknown instance diamond.

**E-A7 — non-degeneracy that lives outside the type that needs it.**
`forwardGeometryFrame` (`Euler/ParentPacketPrimaryCenter.lean:73`) admits `α = 0` at the definition
level, which would collapse the shear to 0 and make its remainder bound a statement about nothing; it
is ruled out one layer up by `Guards.shear_pos` (`Euler/PacketSourceGeometryData.lean:98`). Benign
today, but the *type* does not certify it. Two analogous cases are open (§Open 2).

**E-E3 — inherited scope limit, now confirmed at source.** The periodic alternative (D) excludes only
solutions whose **pressure** is 1-periodic: `cubeIntegral_pressure_energy_zero`
(`NavierStokes/PeriodicUniqueness.lean:435-441`) takes that periodicity as a hypothesis and the energy
identity at `:533` discharges it for both pressures. Inherited verbatim from the independently
authored upstream, and (C) is a full Clay alternative by itself.

**Near-tautological in-cone theorems.** `NavierStokes/TerminalEdgeFactor.lean:1467,1562,1659` hold
because `Tz` is flat-zero; in `NavierStokes/InitialPhysicalData.lean` **all 177 theorems survive if
`cartesianPotential = 0`**. Not defects — but a reader should know which in-cone theorems carry no
information.

## Open

1. ~~Does the `+1/10` per cycle chain?~~ **CLOSED — it is earned.** `signed_tensor_bounds`
   (`NavierStokes/SignedMeanGain.lean:462`) spends `17/100` of a **`σ`-free** cap
   `δ - α = 17/25 - 1/2 = 18/100`; the binding branch gives `κ ≤ 1/200` against `κ ≤ 1e-5`, and the
   nonlinear self-interaction branch `17/100 + 3κ ≤ σ` holds with slack `3/100` and *improves* as `σ`
   grows. The `+1/10` in the ledger is a round-down. The invariant carries only three `σ`-dependent
   fields and rebuilds the `σ`-free requirement each cycle with a margin that grows; the induction
   closes at `ActualCyclePreservation.lean:826`; and the `MemClass` degree worry is answered by
   `slow_power_absorption` charging a **fixed `+1`** with losses `J`-free by type. Arithmetic
   re-derived by hand by the parent.
2. ~~Two collapse checks.~~ **CLOSED, and my premise was wrong.** `zeta = 0` makes `MemClass`
   *stronger*, not vacuous (the majorant becomes 0 and forces all jets to vanish); the real
   non-degeneracy is `actual_strip_nonempty` (`NavierStokes/ActualSignedMeanBinding.lean:54`) with an
   explicit witness, and every strip in the tower is a pullback of it. `SameCarrier` is
   unconditional, by `Nat.rec`, discharged at `NavierStokes/ActualCandidateConstruction.lean:80`.
   **But a new one replaces them:** `Index B N0` (`NavierStokes/BaseChartJets.lean:825`) — the wave
   tower's index set — is **never proved nonempty**; the artifact case-splits on emptiness and the
   empty branch gives `oscillation = 0`, so every wave estimate could hold because there are no waves.
   Sound, but it would make the wave tower decoration: the blowup is carried by the base field
   (`NavierStokes/BaseResidual.lean:104-114`).
   **CLOSED too — the tower IS inhabited.** The artifact never *records* it, but emptiness contradicts
   its own in-cone `partitionFactor_eq_one` (`NavierStokes/ActualPrimaryCovariance.lean:508`), which
   makes a `Finset.sum` over the label set equal `1` at every native-strip point above a threshold; an
   empty type forces that `Finset` to `∅` and the sum to `0`, and the strip point is supplied
   explicitly by `actual_strip_nonempty`. So the four `isEmpty` branches are **dead code that is
   nevertheless shipped in-cone**, and the gap is bookkeeping rather than vacuity. Separately, the
   headline does not need inhabitedness at all: all 12 `CandidateProperties` fields are discharged
   without a label, and the artifact *proves* the whole correction tower is identically zero on a
   neighbourhood of every axis point — exactly where the blow-up is measured. HIGH-CONFIDENCE, and the
   five-line derivation is still UNBUILT.
3. ~~The 529 `rfl` sites.~~ **CLOSED, and the count was 541.** Of the 541 in-cone bare-`rfl`
   theorems, only 19 mention any of the artifact's 87 recursive definitions, and each of those is a
   base case at a closed `0`/`[]` or a `succ`/`cons` lemma at a **symbolic** argument: **≤ 1 iota step
   each, ≤ 19 in total, zero iota chains**. Three statements contain a literal ≥ 10 (real
   coefficients); `![…]` appears twice and both are compared structurally with **no index applied**, so
   the `Fin`/`Matrix.cons` route into vector (2) is never taken. Zero `Acc.rec` steps, including in the
   well-founded files. Exactly **one** site requires `Prod` structure eta
   (`NavierStokes/LocalSignedRequest.lean:523`) — the kernel feature E-A3 reduces to, now with a named
   witness. Everything else is projection of structure literals, delta of non-recursive definitions,
   beta/zeta, and proof irrelevance; the long statements are long *argument lists*, not computation.
4. ~~A quoted vs proved exponent.~~ **CLOSED.** The packet label bound's `k^80` is **chosen, not
   derived** — the ledger adds to `6q+8` (= 44 at `q = 6`), and the jump to `10(q+2) = 80` is one
   `pow_le_pow_right₀` step (`Euler/SobolevSourceExponent.lean:73`) needing only `1 ≤ k`. That
   *weakens* an upper bound, so the direction is safe, and there is no site quoting a different
   exponent — `10*(6+2)` and the literal `80` reconcile by defeq, so a mismatch would be a type error.
   Residue: `80` is hand-copied into `requiredExponent := 80*degree+1` and into the only size check in
   the layer, `80 ≤ 320` (`Euler/NormalPacketFrequencyGuards.lean:24`), whose `320` is unaudited; with
   36 powers of slack below it this cannot break the argument, only a future edit.
   One documentation overclaim: `Euler/PhysicalChildSourceBound.lean:6` says "exactly `10(s+2)`" for
   what is a rounded-up envelope.
5. **The other 1,176 `rfl`s.** Item 3's ≤19-iota bound holds for the 541 in-cone theorems proved by
   `rfl` *alone*, where the statement displays the obligation. A further **1,176 in-cone theorems close
   a tactic block with `rfl`**, and the goal that `rfl` faces has already been rewritten by
   `simp`/`rw`/`unfold`, so it is not in the source and no statement-level screen bounds it. This is
   now the largest **unbounded** kernel surface in the artifact. Bounding it needs elaboration, not
   reading — and item 6 shows that is available.
6. **"Never multi-limb" is a claim about certificate *degree*, not about constants.** The 61-bit
   maximum is measured in emitted proof terms, but `nlinarith` forms its degree-2 products *after*
   `cancelDenoms`, so a degree-2 certificate over the artifact's **own** literals reaches 10²⁰ and 541
   literals above 2⁶⁴ (demonstrated). The artifact sits 4.6× below Lean's `2⁶³` single-word threshold
   because Mathlib's oracle found degree-1 certificates for these goals. Question for an expert: is
   that a property worth relying on across Mathlib versions, and should an artifact this size pin the
   Mathlib revision for that reason as well as the usual ones?
7. **The five-line `index_nonempty` build.** The cheapest open check in the pass: add the derivation
   of item 2 to the artifact and build it. A built Mathlib (Lean 4.33.0) exists on the audit box, so
   the only obstacle was never looking for one.

## What this does not cover

- **No build, therefore no execution.** Disk on the audit machine is at 99%; there is no compiled
  Mathlib. So `lake build`, `#print axioms`, Comparator, `lean4lean`, and nanoda were **not run**, and
  every claim about kernel *behaviour* here is inference from source plus knowledge of how Lean 4
  compiles `match`/`termination_by` — not observation. The two cheapest measurements that would
  upgrade this audit are `#print axioms` on the four headline theorems and
  `set_option diagnostics true` on the seven well-founded definitions.
- **75.5% of in-cone theorems have not been read by anybody**, and "read" above is generously defined
  (see `nse-deep/COVERAGE.md` for the ledger and the ranked work queue). The unread mass is the
  Navier-Stokes estimate/assembly layer, which is the *lowest*-risk mass for kernel trust and a
  plausible hiding place for an off-by-one in a constant.
- **The cone is an over-approximation with a known blind spot**: instance synthesis and the ambient
  `@[simp]` set are invisible to it (611 out-of-cone declarations carry an implicit-use attribute).
  "Out of cone" is triage, not proven dead code.
- **Mathlib itself is out of scope.** Every proof here rests on it, and its trust surface is not this
  artifact's to control.

## Reproduce

```bash
git clone https://github.com/openai/NavierStokesAndEuler /tmp/nse && cd /tmp/nse && git checkout f9e8bc5

# the kernel-risk census (§"The three vectors") + the per-declaration ledger
python3 audits/scan_kernel_risk.py /tmp/nse -o /tmp/out

# the cone: which declarations a headline theorem can possibly depend on
python3 audits/cone.py /tmp/nse \
  --seed Euler.euler_breakdown_R3 \
  --seed Euler.exists_compact_smooth_euler_singularity \
  --seed NavierStokes.Comparator.navier_stokes_breakdown_R3 \
  --seed NavierStokes.Comparator.navier_stokes_breakdown_periodic \
  -o /tmp/out/CONE.csv
```

Worker reports, per-marker site lists, the coverage ledger and the running findings log are in
[`nse-deep/`](nse-deep/). Every `file:line` in this report was read in the original file before being
cited — the first generation of these lists was measured on comment-stripped text and drifted by the
height of the comments above each site, which is why `safeverifyagent/extract.py` now has
`blank_comments`.
