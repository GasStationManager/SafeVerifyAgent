# NSE deep audit — running findings

Artifact: `github.com/openai/NavierStokesAndEuler` @ `f9e8bc5` (clone at
`/home/gsm/.openclaw/workspace/repos/NSE`, read-only).
Pass: **kernel-trust**, not specification. The 2026-09-15 audit read the two challenge
*statements*; this pass reads *proofs*, and asks which of them a bug in the Lean kernel
could turn into a fake. Threat vectors, in the order we were told they matter:
(1) recursive inductive types, (2) `Nat` arithmetic delegated to GMP, (3) custom
metaprogramming.

Verdict tags: **OK** (understood and benign), **NOTE** (true but only hygiene),
**ESCALATE** (an expert should answer a specific question), **REFUTED** (a defect).
Nothing is REFUTED so far.

---

## P0 — measurement corrections to our own instrument (not artifact findings)

- `safeverifyagent/extract.py:strip_comments` deletes block comments outright, so every
  `file:line` computed on stripped text drifts by the height of preceding comments —
  on `Euler/EulerProof.lean` an `inductive` reported at 3015 actually lives at **3064**.
  Fixed by adding `blank_comments` (comment content removed, newlines kept) and
  switching the new scanner to it. All site lists in this directory are 2nd generation
  and verified against the original files. Six in-flight workers were sent the
  correction. *Lesson: a citation that lands 49 lines away is worse than no citation,
  because it looks checkable.*

## A1 — vector (3) is empty at source level — OK

`python3 audits/scan_kernel_risk.py <repo> -o audits/nse-deep` over 2,659 files /
641,332 lines / **52,516 declarations** (38,503 `theorem`, 10,827 `def`, 1,578
`instance`, 899 `abbrev`, 667 `structure`, 28 `lemma`, 14 `inductive`):

`macro`/`macro_rules`/`syntax`/`elab`/`notation`-declaration = **0**;
`run_cmd`/`#eval`/`#reduce`/`MetaM`/`TacticM` = **0**; `set_option` (any, incl.
`maxHeartbeats`, `maxRecDepth`, `debug.skipKernelTC`) = **0**; `axiom` = **0**;
`opaque` = **0**; `native_decide` = **0**; `unsafe`/`@[extern]`/`implemented_by`/
`partial def` = **0**; `sorry` = 4, all of them the two challenge files' placeholders.
The only elaboration-affecting declarations are 25 `attribute` lines, **all `local`**
(11 `local instance`, 10 `local irreducible`, 2 `local gcongr`, 4 of the instances being
`Classical.propDecidable`). So there is no custom metaprogramming to audit: the artifact
is written in plain Lean + Mathlib tactics. The residue is Mathlib's own trust surface,
which this artifact does not control.

## A2 — the solution's private copies of the challenge structures are exact — OK
*(closes a residue item of the previous audit)*

Comparator requires the solution not to import the challenge, so the solution restates
the challenge's definitions. Both copies exist:

| challenge | solution-side copy |
|---|---|
| `ComparatorChallenges/Euler.lean` | `Euler/SolutionDefinitions.lean` |
| `ComparatorChallenges/NavierStokes.lean` | `NavierStokes/ComparatorDefinitions.lean` |

Normalized diff (comments blanked, attributes/imports/`namespace`/`open`/`section`/
`local notation`/`#print` lines dropped, whitespace collapsed) over each pair: the
**only** difference is the deletion of the placeholder theorems (`euler_breakdown_R3`,
`exists_compact_smooth_euler_singularity`; `navier_stokes_breakdown_R3`,
`navier_stokes_breakdown_periodic`) with their `sorry`s. **Every definition and every
structure field is character-identical.** Field lists, `extends` chains, and the junk-prone
`toL2` are identical, so nothing was silently added to or dropped from a solution
structure.

The elaboration *context* is identical too, which is the part that a text diff does not
by itself establish: both members of each pair are the only 4 files in the repo that do
`import Mathlib` wholesale (and nothing else), and their `open`/`local notation` lists
match line for line (`open ContDiff Set InnerProductSpace MeasureTheory`,
`open scoped Laplacian`/`ENNReal Topology`, `ℝ³`, `ℝ^n`, `∇⬝`).

## A3 — ESCALATE (refines the previous audit's E2, with a mechanism)

`Euler/Solution.lean:41`: `attribute [local instance] CompletePartialOrder.toSupSet`,
commented "Match the reference's elaboration of ENNReal suprema independently of import
order", placed between `euler_breakdown_R3` and `exists_compact_smooth_euler_singularity`.

What we can now say precisely:

- The `⨆ t ∈ Icc (0:ℝ) T, velocityC1Norm (v · t)` and `⨆`-in-`velocityC1Norm`/
  `vorticityNorm` occurrences are `ℝ≥0∞`-valued suprema, and the ones in the *theorem
  statement* are elaborated **in `Euler/Solution.lean`**, not in the definitions file.
- `Euler/SolutionDefinitions.lean` (the copy) elaborates its `⨆` with an import set of
  exactly `Mathlib`. `Euler/Solution.lean` elaborates its own `⨆` sitting on top of
  **1,829 modules** (measured on the import graph), exactly one of which pulls in
  Mathlib wholesale. Instance resolution among same-priority instances depends on
  declaration order, hence on module order — which is what the author's comment says.
- So the acceptance of the Euler headline rests on the kernel deciding that the
  challenge's `SupSet ℝ≥0∞` and `CompletePartialOrder.toSupSet` denote the same
  function. That is a defeq between two paths through Mathlib's `CompleteLattice`
  hierarchy, i.e. **structure-projection unfolding and structure eta** — the same
  machinery listed under threat vector (1).

**Question for an expert (checkable in ~10 lines of Lean):** in an environment with the
solution's import set, do
`(inferInstance : SupSet ℝ≥0∞)` and `CompletePartialOrder.toSupSet` elaborate to terms
that are equal by `rfl` *and* print identically under `set_option pp.all true`? And is
Comparator's declaration comparison sensitive to the difference if they are not? A
positive `rfl` answer that relies on a long projection-unfolding chain is exactly the
kind of judgement a kernel bug could get wrong, and it sits on the deliverable path.

## A4 — ESCALATE (build-option asymmetry: the NS half is elaborated with `autoImplicit`)

`lakefile.toml` gives the `Euler` library `leanOptions = { autoImplicit = false,
warningAsError = true }`. The `NavierStokes` library (816 files) and
`ComparatorChallenges` get **no `leanOptions` at all**, so they build with Lean's
defaults: `autoImplicit := true`, `relaxedAutoImplicit := true`, warnings not errors.
With `autoImplicit` on, a mistyped identifier in a *statement* is silently bound as a
fresh implicit argument instead of being an error, so the theorem that gets proved is
not the theorem that was written down.

This is a specification-drift vector, not a kernel one, and it cannot manufacture a
proof of a false statement (auto-binding generalizes, which makes a statement harder,
not easier). It does mean an intermediate NS lemma can quietly be about a fresh
variable while its name says otherwise.

Mitigating and interesting: the authors clearly know the check — 11 `…NoOptions.lean`
modules document `lake env lean -DautoImplicit=false -DwarningAsError=true <file>` as
their verification command. They applied it to selected files, not to the library.

**Suggested:** build the `NavierStokes` library once with `-DautoImplicit=false
-DwarningAsError=true` and report the diff. We cannot run it here (no Mathlib build:
7.4 GB free disk), so this is escalated rather than measured.

## A5 — NOTE: the 11 `NoOptions` siblings do not re-verify their namesakes

The `…NoOptions.lean` modules exist to reprove something without a resource-limit
override, but **`set_option` occurs 0 times in the repo**, so whatever override they
were built against is gone from the source. Nine of the eleven are near-copies
(e.g. `NavierStokes/CorrectionInitializationNoOptions.lean` vs
`CorrectionInitialization.lean`: 5,573 vs 5,562 lines, `difflib` ratio 0.999 — the only
substantive change is the namespace and a docstring paragraph). Two are **not** copies:

- `Euler/TransversePacketCorrectorNoOptions.lean` — 39 lines vs 160: it reproves exactly
  one theorem (`potentialCoefficientPath_time`) and says the original's `simpa only`
  "exceeds the default recursion depth in an isolated reproduction".
- `NavierStokes/ActualParticularDynamicsNoOptions.lean` — 143 lines vs 1,633.

Nothing wrong with that, but the name invites the reading "this module is also checked
under strict options", and for these two the strict-option check covers a fragment.

---

## Coverage ledger

`INVENTORY.csv` — 52,516 rows, one per declaration, with per-body counts of
`decide, norm_num, omega, simp, rfl, native, rec, induction, termination_by, wf, bignum,
pow, choose_fact, finset, nat_prim`. An audited theorem is a row signed off here.
Parent-read so far: the two challenge files, both definition copies, `Euler/Solution.lean`,
`Euler/EulerSingularity.lean` (head), `Euler/EulerProof.lean:3040-3130`, the 25
`attribute` sites, the 14 `inductive` headers, all 12 `termination_by` and 5 explicit
recursor sites (locations verified, bodies delegated).
**Six workers in flight** (see `workers/`): `jet-inductives`, `expr-inductives`,
`decide-bignum`, `wf-recursion`, `euler-spine`, `ns-spine`.

---

## W1 `expr-inductives` — the four recursive syntax trees in the NS half — OK (0 kernel-risk)

Report: `workers/expr-inductives.md` (36 KB). Scope: `ClosedIntervalJetAlgebra.lean` (293 l),
`GenericDifferentialPolynomial.lean` (283 l), `FlatKernelBounds.lean` (442 l),
`GenericFactorSupport.lean` (139 l) — **1,157 lines / 103 declarations, all read
line-by-line**. Verdicts: 102 OK, 1 UNCLEAR-then-OK, **0 KERNEL-RISK, 0 SUSPICIOUS**.

**The load-bearing negative: no proof by reflection.** All four trees
(`PolynomialExpression` :244, `Expression` :185, `Expr` :76, `FieldFactor` :14) are plain,
direct-recursive, **non-nested, non-indexed, non-mutual**; every theorem about them is
`induction … with` yielding *propositional* (in)equalities. The kernel therefore checks a
`rec`-shaped *term* and never has to *reduce* a recursor applied to a closed tree. The only
`rfl`s are single-iota-step unfoldings at variable-argument nodes
(`GenericFactorSupport.lean:42,54,58`). Zero `decide`, zero `deriving`/`DecidableEq`, zero
`termination_by`, hence no `Acc.rec` anywhere in scope; **the largest numeral the kernel must
evaluate in these 1,157 lines is `3`** (`Expr.pow 3` at `FlatKernelBounds.lean:111,112,334`).
All four files are `noncomputable section`, so no compiled evaluator exists either.

Parent spot-checks (independent, on the original files): `decide` = 0, ≥7-digit numerals = 0,
`termination_by` = 0, `deriving` = 0 in all four files; `FactorSupportAt`
(`GenericFactorSupport.lean:106-114`) is exactly as described — an indexed **`Prop`** family
with 2 constructors (so small elimination only, and its one use at `:133` has a `Prop` goal),
whose `mul` constructor demands the property of **both** factors, i.e. **conservative, not
over-strong**, and non-vacuous via `factor_of_tsupport` :116. Confirmed.

Architecturally this is the *right* way to use a syntax tree in a proof: the symbolic
operations (`Expr.diff` :106, `Expr.jetOrder` :219) are **validated against real analysis**
(`Expr.hasDerivAt_eval` :116, `jetOrder_diff_le` :306), never trusted. The worker re-derived
the three kernel derivative formulas and the `2^k` constant chain in `Bound.mul` :58 by hand
and they agree.

### New escalations from W1

- **W1-E1 — `NavierStokes/SeedHandbackJets.lean:94-108` `stocks_formulas`** *(the only
  reflection-shaped site in the cone)*. The one consumer that builds **concrete** trees
  (~42 constructor nodes, 34 `input` leaves, `ι = Fin 19`, `Matrix.cons` vectors of length 19
  and 12) and closes four closed-form identities with
  `simp […, PolynomialExpression.eval, …]` → `repeat' constructor <;> ring_nf` → a bare `simp`.
  Magnitude is still small (tens of iota steps, `Nat` literals ≤ 19), and the worker
  hand-derived the four formulas and says the trees encode exactly the stated ones. Open:
  tactic robustness, and lines 110-393 (the `Fin 19` index bookkeeping) were not read.
  **Dispatched:** worker `seedhandback`.
- **W1-E2/E3/E5 — the consumer side.** `Expression.eval`'s `directional` node
  (`GenericDifferentialPolynomial.lean:202`) is `fderiv`, junk-`0` off differentiability;
  `polynomial_jetRate_of_stages` :247 concludes a rate for **every real `n`** and imports all
  its strength from its hypothesis `hres` :261; `approximation_eval` :217 is a `def` built by
  tactic `induction` (i.e. `Expression.rec` into `Type`) whose only current consumer applies it
  to a *variable* tree. In-scope the smoothness side conditions are always supplied, but the
  call sites (`GenericSupportLocalCoefficients.lean:151-214`, `GenericTupleSupport.lean`,
  `GenericSupportLocalSummation.lean`, `GenericSummationRealization.lean`) were out of scope.
  **Dispatched:** worker `jetrate-callsites`, also asked to check that `JetRate`'s filter never
  escapes the open set `U` on which smoothness is assumed.
- **W1-E4 (low)** `ClosedIntervalJetAlgebra.lean:204-209` uses `iteratedDerivWithin_succ'`
  with no `UniqueDiffOn` argument while every neighbour passes one — a one-`#check` question,
  and the file elaborates, so it is a formality.
- **W1-E6 (low, docs)** `GenericFactorSupport.lean:103-105`'s docstring oversells the `mul`
  constructor (claims support need not be shared; the constructor requires both factors to be
  tracked). Conservative direction — cannot create unsoundness.

---

## The cone: a denominator for "theorem by theorem"

New framework tool `audits/cone.py`. It builds a **name-level dependency graph** over the whole
repository (declarations fully qualified through a `namespace`/`section` stack; a reference is
any identifier token in a body that resolves to a declared name, exactly or by suffix) and
computes what the four headline theorems reach:

| | in cone | out |
|---|---|---|
| theorem | **22,643** | 15,860 |
| def | 8,990 | 1,837 |
| abbrev / structure / inductive / lemma | 864 / 623 / 14 / 28 | 35 / 44 / 0 / 0 |
| instance | 1 | 1,577 |
| **total** | **33,163** | 19,353 |

Both error directions, because a reachability number is quotable: suffix matching
**over**-approximates (`add` resolves to every `*.add`), which is the safe direction; and it
**under**-approximates uses that are never written down — instance synthesis (hence the absurd
1-of-1,578 instance count), the ambient `@[simp]` set, `gcongr`, `positivity`. 702 out-of-cone
declarations carry an implicit-use attribute, and that number is the blind spot's size. So
*out of cone* = *no named reference chain from the headline theorems*: strong triage, never a
proof of dead code. Ledger: `CONE.csv`; `INVENTORY.csv` gains `fullname` + `onpath`.

This is what makes "audited N theorems" meaningful: the denominator is 22,643, not 38,503.

## W2 `jet-inductives` — `Euler/EulerProof.lean`, the two `Type`-valued jet families — 0 kernel-risk

Report: `workers/jet-inductives.md`. 1,227 declarations in the file; **119 read line-by-line**
(all of the jet block 3061-3480). OK 116, UNCLEAR 3, KERNEL-RISK 0, SUSPICIOUS 0.

- `SpatialJet` :3064 and `CoefficientJet` :3073 are recursive and **doubly indexed** (both the
  order `n` *and* the field/coefficient change at `succ`), with a **higher-order recursive
  argument** (`lower : ∀ i, SpatialJet … n (derivatives i)`). Not nested, not mutual. Being
  `Type`-valued is **forced, not gratuitous**: `sobolevNorm` :3093, `word` :3393 and
  `levelNorm` :4697 recurse *into `ℝ`*, which a `Prop`-valued family could not support. No
  large elimination (`Prop → Type`) anywhere.
- The kernel *does* iota-reduce these recursors (:3212, 3265, 3374, 3403, 4722, 4880, 7943) but
  always **one step on symbolic constructors** — there is no concrete jet literal in the file,
  so no reduction chain of depth > 1.
- All 7 `termination_by` measures are genuine (`word`/`levelNorm`/`boundLevel` measure the jet
  order `s`; `n` would fail), and their bodies enter proofs only through the generated
  **equation lemmas**, so the kernel never unfolds `Acc.rec` at closed arguments — the one
  claim source reading cannot close (**W2-E1**, needs a build: `set_option diagnostics true`
  and look for `WellFounded.fix`/`Acc.rec` in the unfolded-constant counters).
- The junk convention `word = 0` past the jet order (:3397) is **fenced**: the lemmas with
  mathematical content carry the guard (`word_hasDerivAt` :3413 needs `n < s`, `word_unique`
  :4549 needs `n ≤ s`), and `sobolevNorm_eq_sum_words` :3458 plus `compactSmoothJet_sobolevNorm`
  :7957 pin the jet norm to the classical Sobolev norm. Two *unguarded* conclusions
  (`pressure_gevrey_majorant` :5120, `pressure_word_sum_majorant` :5170 conclude `∀ n` from
  `∀ n ≤ s`) are **W2-E2**: harmless in-file, cross-file instantiation unchecked.
- All 40 `decide` in the file are tiny (`m ≤ n ≤ 40`, `2 < 3`, `Even 6`); largest literal in
  the file is 320,000,000. **W2-E3**: `productConstant` :3196 sums an `i`-independent term
  inside `∑ i : Fin 4`, so the constant is silently 4× — cannot cause unsoundness (upper bound
  only) but downstream budgets may quote a tighter constant than the definition supports.
- Correction it made to my own summary: "0 `set_option`" is right but 25 `attribute` lines
  exist; the two `attribute [local irreducible]` in this file hit `EulerSobolev.sobolevNorm`
  :5472 (Schwartz), **not** the jet norm — and reducibility is elaborator-only, the kernel
  ignores it. **W2-E4** asks the same of `attribute [local irreducible] Parent.child
  initialParent` in 10 packet files.

## W3 `decide-bignum` — vector (2) repo-wide — 210/210 classified, all OK

Report: `workers/decide-bignum.md` (+ two child reports). **Vector (2) exposure is ~nil:**

- The entire `decide` surface is `Nat.ble`/`beq`/`mod` on **1-4 digit** literals; the largest
  numeral in any `decide` goal is **1000** (`Euler/ParentHistoryFrequencyGuard.lean:81`) and
  208 of 210 are ≤ 40. No `Nat.pow`/`gcd`/`div`, no custom `Decidable` instance, no
  `native_decide`.
- The largest closed `Nat` the kernel evaluates **anywhere in the repo** is `5.0e17` — 61 bits,
  **one machine word, never multi-limb GMP** — an `nlinarith` certificate at
  `NavierStokes/PulseCone.lean:1017`. The one big power, `9^729`
  (`Euler/ConstantCorrectionData.lean:146`), is **never normalised**: it is consumed by
  `one_le_pow₀` with a symbolic exponent.
- `Nat.choose`/factorial are never computed by the kernel; the only closed values are `0!`,
  `C(0,0)` and `4! = 24` (`Euler/EulerProof.lean:12153-54`).
- The only *load-bearing* `decide` is `sum_knownTerm` / `card_knownTerm`
  (`Euler/PacketKnownDecomposition.lean:31,33`, `decide` at :36-41) over the 5-constructor
  `deriving DecidableEq, Fintype` enum `KnownTerm` — hand-verified true (2+3·3+4 = 15; list
  complete, no duplicates), so a recursor/`Finset` kernel bug **cannot** make them false.
  *Parent addition:* my cone graph puts both of them **out of the cone with zero referencing
  declarations**, so even that one is not load-bearing.
- `Classical.propDecidable` as a local instance (4 files) **cannot** corrupt a `decide`:
  `Classical.choice` is irreducible, so `decide` would fail to elaborate rather than compute.
  The real risk in those files is a degenerate `else 0` branch on `if 0 < x.1.1`
  (`NavierStokes/InitialPhysicalData.lean:368,376`) — a semantics question, not a kernel one.

## W4 `wf-recursion` — vector (1), the non-structural half — 0 kernel-exploit

Report: `workers/wf-recursion.md`. 7 files, 590 declarations, **241 read line-by-line**.
OK 232, KERNEL-RISK 3 (all "theoretical, one iota step"), UNCLEAR 2, SUSPICIOUS 0.

- Both hand-rolled well-founded sites use the **safe idiom**: `unfold; rw [WellFounded.fix_eq];
  rfl` (`NavierStokes/SlowRecursion.lean:948-965`, `GlobalSlowProfiles.lean:907-911`). After the
  rewrite `fix` sits in identical positions on both sides, so the `rfl` is one `Nat`-matcher
  iota step **with `fix` opaque** — the kernel never reduces `Acc.rec`/`fixF` on a canonical
  `Acc.intro`. `Nat.lt_wfRel` is core, not repo-defined.
- The genuine risk in this vector was the **course-of-values junk default**, and it is
  discharged: histories are padded with `0` (`SlowRecursion.lean:918-923`,
  `GlobalSlowProfiles.lean:778-780`) or with the order-`n` seed (:770-776), every index the step
  reads is `j ≤ n` (`SlowRecursion.lean:549-616`), and five prefix-congruence lemmas
  (:946, 966, 976, 986, 993, 995) prove the padding is unread. No "future coefficient = 0" cheat.
- `Euler/LpSmoothJetField.lean:17`'s `Nat.rec (motive := fun n => ∀ V, …)` into `Type u` is not
  a dangerous large elimination (`Nat` is `Type`-valued); the explicit recursor is needed because
  the space changes each step (`V ↦ Space →L V`). `jetField_zero/succ` (:32, :39) are `:= rfl`,
  i.e. exactly one iota step at symbolic `n`, and `jetField_field` :57 anchors the construction
  to `iteratedFDeriv`. Same shape for `List.rec` (`WeightedODEJets.lean:177,187`) and
  `HistoryRow.rec` (`ActivationContinuation.lean:517,520`, a non-recursive 5-constructor enum).
- Largest kernel numeral in scope: 4 digits. **W4-E1**: `GlobalSlowProfiles.lean:600-692`
  `exists_repaired_order` — everything after `sequence` is `Classical.choose` of that one
  existence claim, so a defect there is invisible downstream.

## W5 `ns-spine` — the Navier-Stokes deliverable path — 1 SUSPICIOUS (structural), 0 kernel-risk

Report: `workers/ns-spine.md` (19 files read in full, 167 declarations, plus two delegated
children). Confirms my A2 independently ("0-hunk `difflib` diff" of the private copy) and adds:

- **Scope split worth recording:** `ComparatorSolution`'s import closure is **609 modules** —
  that is the deliverable path; `PaperResults` adds 143 more; the root sees 753. Vectors (1)
  and (2) *are* on the deliverable path (all 4 explicit `.rec`, all 5 well-founded sites, all 3
  `propDecidable` files, 86 of 90 `decide`, 5 of 9 NS inductives, max numeral 1,000,000 at
  `Euler/ExponentLedger.lean:276`); the four recursive syntax trees of W1 are
  `PaperResults`-only, i.e. **not** on the Comparator deliverable path.
- **The structural finding (SUSPICIOUS, and I verified it myself at
  `NavierStokes/CandidateFromLimits.lean:82-87`):** the force is *defined* as the smooth
  extension of the candidate's own residual —
  `def force := SpacetimeGluing.smoothExtension 1 (tracedResidual u p L) (…)`. So the PDE field
  of the solution structure is **definitionally true**, not verified content. For a *forced*
  blowup (Fefferman's (C)/(D) permit a force satisfying condition (5)) this is the standard and
  legitimate shape — but it means the whole mathematical burden moves to three places:
  `ForceConditionDecay`'s spatial decay for **every** derivative order and **every** rate
  (challenge `:185-191`), smoothness of the glued force **through** `t = 1`
  (`force_smooth` :86 ← `tracedResidual_boundary_jets` :57 ← the `hlim` jet-convergence
  hypothesis), and the blowup itself. **Dispatched:** worker `ns-force-and-blowup`.
- **All R3 non-existence reduces to one lemma:** `WholeSpaceUniqueness.candidate_global_agrees_before_one`
  (`NavierStokes/R3/CandidateBreakdown.lean:43,49`); the rest is compactness. That is where a
  non-existence claim could silently become non-existence-*in-a-subclass*.
  **Dispatched:** worker `ns-uniqueness`.
- Periodic E3 (previous audit) **pinned**: the competitor's `pressure_periodic` field is
  consumed in the **energy balance** (`PeriodicUniqueness.lean:533,435`), so competitors with
  non-periodic pressure genuinely escape the periodic claim.

## W6 `euler-spine` — the Euler deliverable path — A3/E2 SETTLED BENIGN

Report: `workers/euler-spine.md` (58 declarations; OK 54, UNCLEAR 4, KERNEL-RISK 0).

- **A3/E2 settled.** `Euler/Solution.lean:41`'s forced instance affects **exactly one**
  supremum: the `⨆ t ∈ Icc 0 T, velocityC1Norm` at `Solution.lean:51` (= challenge `:181`).
  Mathlib's only `CompletePartialOrder ℝ≥0∞` route is `CompleteLattice.toCompletePartialOrder`
  with `sSup := sSup`, so **both instance paths yield `ENNReal`'s own `sSup`**, equal by
  structure eta; `limsup` uses `InfSet` and `∫⁻` needs no `SupSet`; the `⨆` inside
  `velocityC1Norm`/`vorticityNorm` was elaborated in `SolutionDefinitions.lean`, which imports
  only Mathlib. So the meaning cannot differ. Residual risk is now precisely *kernel structure
  eta*, not an unknown instance diamond — a much smaller target.
- No junk-value hole on the spine: `lifespan` is `Exists.choose` of a proved existence
  (`OrdinaryEulerLifespan.lean:35`), `duration` is `sSup` of a set proved nonempty and bounded,
  `SmoothL2Field` (`LpSmoothField.lean:31`) carries `ContDiff ∞` so `fderiv` is never junk,
  `u₀ ≠ 0` is *derived* (`OrdinaryEulerNontriviality.lean:47`), and the `T = T*` exclusion is a
  real continuation theorem (`OrdinaryEulerContinuation.lean:53`).
- BKM sub-chain cleared by a delegated child (`workers/euler-spine-bkm.md`): the vorticity
  integral is an honest `∫⁻` of a *bundled* `BoundedContinuousFunction` sup-norm
  (`OrdinaryEulerVorticity.lean:30,63`) — stated as a lower Lebesgue integral so the
  Bochner-`0` convention cannot be exploited — and the logarithmic/BKM estimate is **proved**,
  not assumed (`OrdinaryEulerBKM.lean:22-24` ← `OrdinaryLogarithmicGradient.lean:63` ←
  `WholeSpaceGaussianElliptic.lean:91`).
- **New top Euler question, dispatched** (worker `euler-cauchy`): is the PDE field of the
  *limit* evolution built by `limitEvolutionOfH3` (`Euler/OrdinaryEulerCauchy.lean:97`, used by
  `exists_smooth_endpoint`, `OrdinaryEulerEndpoint.lean:39`) actually **proved**, or inherited?
  It is load-bearing three times over (deliverable clauses 8 and 3, and the BKM contradiction).
  If that construction can manufacture an `Evolution` that need not satisfy the PDE, the BKM
  theorem is false rather than vacuous — the first candidate refutation path in this audit.

---

## The cone, mark 2: cut back by the module system (sound, not heuristic)

Worker `seedhandback` made a point worth building into the instrument: **a Lean file can only
cite declarations from modules it imports**. That is not a heuristic, it is the module system,
and it separates "nobody names it" from "it is not even in scope". `audits/cone.py` now
resolves a token in file `F` only against names declared in `F` or in `F`'s import closure.

| | mark 1 (suffix only) | **mark 2 (import-scoped)** |
|---|---|---|
| declarations in cone | 33,163 | **28,145** (53.6%) |
| theorems in cone | 22,643 | **19,214** of 38,503 |
| instances in cone | 1 | 0 (the blind spot, unchanged) |
| inductives in cone | 14 | **10** of 14 |

The 5,018 removed declarations were reachable only through last-component ambiguity. The
worker's own counterexample reproduces: `FieldFactor.zero` and the whole `FactorSupportAt`
cluster were in mark 1 because a bare `.zero` token matched them; in mark 2 they are out, which
independently agrees with `ns-spine`'s import-closure finding that those four recursive syntax
trees are **`PaperResults`-only, not on the Comparator deliverable path**. Mark 2 is a strict
subset of mark 1 (0 declarations gained), as it must be.

Also computed and now a column in `CONE.csv`: `in_import_closure` — is the declaration's module
in the import closure of the two solution files at all? **48,900 of 52,516 are; 3,616 are not**,
i.e. 216 files (all 11 `…NoOptions` siblings, both `…Investigation` files, both challenge
files, and 200 more) **cannot** contribute to the headline theorems no matter what they contain.
27 declarations are in the cone while their file is outside the closure — that is the
name-collision artifact of collapsing two same-named declarations into one node, and it is the
instrument's remaining known imprecision.

**Which of the 14 inductives are load-bearing:** in cone — `SpatialJet` and `CoefficientJet`
(`Euler/EulerProof.lean:3064,3073`), `KnownTerm` :21, `KnownPiece` :14, `SourceCost` :76,
`FlatKernelBounds.Expr` :76, `NaturalAxisCoefficients.Field` :116, `ReservedPatches.Slot` :22,
`StressActivation.HistoryRow` :539, `TorusInverse.Direction` :190. Out of cone —
`PolynomialExpression`, `Expression`, `FieldFactor`, `FactorSupportAt`. So the four *recursive
syntax trees* audited by W1 are exactly the ones that are **not** load-bearing, and the
load-bearing recursive types are the two indexed jet families (W2, clean) plus
`FlatKernelBounds.Expr` and five finite enumerations.

## W7 `seedhandback` — the only concrete-tree reflection site — NOT load-bearing

Report: `workers/seedhandback.md`. All 40 declarations of `NavierStokes/SeedHandbackJets.lean`
read line-by-line, plus the 28 of `ClosedIntervalJetAlgebra.lean`.

- **Decisively not load-bearing**, by the module argument rather than by my name graph:
  `NavierStokes.SeedHandbackJets` is **not in the 609-module import closure of
  `ComparatorSolution.lean`**; `stocks_formulas` has exactly one occurrence repo-wide (its own
  declaration line); the only route from the root is `PaperAdditionalResults.lean:16`, a
  zero-declaration aggregator; and the file carries no `@[simp]`, so the instance/simp blind
  spot does not apply either.
- The reflection is real but tiny: the expanded closed trees are **186 nodes**, `eval` is
  structural (no `termination_by`/`WellFounded`/`Acc.rec`), so `simp` uses its 5 equation lemmas
  and the kernel checks a propositional rewrite chain, worst case 186 single iota steps. `Nat`
  work: 75 `Fin 19` `Matrix.cons` lookups, Σ(idx+1) = 877 steps, every literal ≤ 18. The final
  term is **not** a large `Eq.refl`.
- All four formulas independently re-derived (numeric transliteration, residual 4.4e-16, a
  12-mutation battery, and a code-disjoint `sympy` child at residual 0) — they match, no index
  or sign differs from the sibling's hand derivation. All three index alignments in lines
  110-392 are correct and exhaustive (12/12, 19/19, 7/7).
- Two non-kernel findings, both inside this non-load-bearing file: (a) `stocks_formulas` cannot
  detect a 15↔16 index swap, because :76 uses those two slots only inside the product
  `v14·v15·v16` (mutation residual exactly 0); (b) **SUSPICIOUS**: `Profile.history` :249 is
  defined as a Lebesgue integral that **no theorem uses** (both comparison theorems consume it
  only through hypotheses — substitute any function and the proofs are unchanged), and
  `density 4 = E²/(2x)` :247 is integrated from 0 with no integrability hypothesis, so `Cp` may
  be junk `0`.

## W8 `jetrate-callsites` — the consumers — 44/44 OK, and an instrument correction

Report: `workers/jetrate-callsites.md`. 5 files, 1,001 lines, 44 declarations, 100% read.

- W1-E3 (circularity) **dissolved and generalized**: `polynomial_jetRate_of_stages` has one
  occurrence repo-wide (its own definition). But its **live twin**
  `TailRates.flat_of_residuals` (`GenericSupportedPolynomial.lean:130`) also takes `hres` as a
  *leaf hypothesis*, and the worker traced 5 hops
  (`GenericSupportLocalSummation.lean:105→:67→:21` → `GenericSupportLocalCoefficients.lean:183→:130`)
  to find that **nobody in the repo proves `hres`**. No circularity and no `J→∞`/order
  interchange (the loss and threshold depend on `m` only; `J` is chosen after `m` and `n`), but
  the whole cluster is a *conditional* result with an unsupplied hypothesis — consistent with it
  being out of the cone.
- W1-E2 (junk `fderiv`) and the filter question **clean**: no `directional`-eval conclusion is
  drawn without `IsOpen U` *and* `ContDiffOn ℝ ∞` (and `IsOpen` is load-bearing), and every
  filter is `scaleApproach U q = comap q (𝓝[>] 0) ⊓ 𝓟 U` (`GenericRealization.lean:23-28`),
  which cannot escape `U`. Zero recursors reduced on a closed tree; max numeral in scope 2.
- **Correction to my instrument, which I have now fixed** (see mark 2 above): the worker
  demonstrated that `FieldFactor.zero` was flagged in-cone purely by last-component matching.
  Its observation that the bias only ever marks declarations wrongly *in* — so out-of-cone
  verdicts stay trustworthy — is right, and mark 2 removes the class of error it found.

---

## The cone, mark 3: a worker caught it under-approximating, which is the dangerous direction

Worker `euler-cauchy` reported that `CONE.csv` had **systematic false negatives for
dot-notation callees** — `SmoothLimitData.toEvolution` was in the cone while
`SmoothLimitData.field_integral_equation`, which its proof calls, was not. Cause: Lean's dot
notation writes the callee against a *local*, so the source token is `hx.field_integral_equation`,
which resolves to no declared name; mark 2 tried the whole token only. Fixed by resolving a
dotted token against **every suffix of itself**.

| | mark 1 | mark 2 | **mark 3** |
|---|---|---|---|
| declarations in cone | 33,163 | 28,145 | **38,076** (72.5%) |
| theorems in cone | 22,643 | 19,214 | **27,456** of 38,503 |
| out-of-cone decls carrying `@[simp]`-style attributes (blind spot) | 702 | 799 | **613** |

**One dismissal is hereby retracted.** With the fix, `EulerPacketCylinderField.sum_knownTerm`
and `card_knownTerm` (`Euler/PacketKnownDecomposition.lean:31,33`) are **in the cone** after all,
so W3's "only load-bearing `decide`" *is* load-bearing. It remains fine — the worker
hand-verified both facts (2+3·3+4 = 15; the constructor list is complete with no duplicates), so
a recursor or `Finset` kernel bug cannot make them false — but the earlier note in this file
that even that one was unreachable was wrong, and this is the correction.

Still out of cone after the fix: `stocks_formulas`, `polynomial_jetRate_of_stages`, and the
four recursive syntax trees (`PolynomialExpression`, `Expression`, `FieldFactor`,
`FactorSupportAt`) — so those conclusions stand.

**Kernel-computation surface, restricted to the cone:** 177 of 210 `decide` sites and 96 of 121
≥7-digit numerals sit inside in-cone declarations. Those are the numbers that matter for
vector (2), and W3's magnitude findings (all `decide` literals ≤ 1000, largest closed `Nat`
61 bits) apply to them.

*Lesson for the framework, recorded because it cost a retraction:* a reachability instrument
must be biased to **over**-approximate. Mark 2's import scoping was sound, but combining it with
whole-token-only resolution silently made the cone too small, and "too small" means an audit
walks away from live code. Mark 3 keeps the sound scoping and restores the over-approximation.

## W9 `euler-cauchy` — the limit evolution's PDE field is PROVED — no refutation

Report: `workers/euler-cauchy-endpoint.md` (both files read in full; 15 in-scope declarations OK,
0 KERNEL-RISK, 0 SUSPICIOUS; two read-only children added 26 + 27 OK).

This was the audit's first candidate **refutation** path: if `limitEvolutionOfH3` could
manufacture an `Evolution` that need not satisfy the Euler equation, the BKM theorem would be
*false*, not merely vacuous. It does not.

- The PDE field is `time_law` (`Evolution`, `Euler/OrdinaryEulerDifference.lean:21-32`, 7 fields).
  `limitEvolutionOfH3` (`OrdinaryEulerCauchy.lean:97`) is a one-line wrapper; all 7 fields are
  discharged in `SmoothLimitData.toEvolution` (`Euler/OrdinaryEulerLimit.lean:55-73`).
- Mechanism, verified: each member's Duhamel equation plus convergence of the **nonlinear** term
  (`projectedRhsPath_convergence`, `AdvectionLimit.lean:135` — Leray projection composed with a
  product estimate, checked real) → `tendsto_nhds_unique` → the limit integral equation (:27) →
  FTC (:43) → an `L²` derivative → pointwise via an injective-embedding integral equation and
  bounded Sobolev evaluation (`StrongTime.lean:48`). That is a genuine passage to the limit, **not**
  a pullback of derivatives along an embedding.
- The pressure is **reconstructed** by Helmholtz (:58), and each member's own pressure is proved
  determined by its velocity (`HelmholtzField.lean:110,125`).
- `exists_smooth_endpoint` (`OrdinaryEulerEndpoint.lean:39`) OK; the rescaling
  `u_c = c·u(ct,x)`, `P_c = c²·P(ct)` is the exact Euler symmetry, re-derived by hand.
- **It corrected the brief I gave it:** my chain claim was wrong. `exists_smooth_endpoint` does
  *not* feed `no_endpoint` or `initial_nonzero`; it feeds only the BKM route
  (`maximalC1Norm_limsup`, `vorticity_integral`), which are still deliverable clauses, so the
  target was right for the wrong reason. Recorded because a brief that misstates a chain can
  make a worker audit the wrong file and report a clean result about it.
- Risk moved one level down to two **unaudited** files: `SmoothFieldSobolevTime.lean:96` (the
  `Icc`-endpoint upgrade of `time_law`) and `SobolevCauchyInterpolation.lean:78` (an
  interpolation step standing in for Rellich compactness).

---

## A6 — SCOPE OF THE ACCEPTED NAVIER-STOKES CLAIM: `u₀ = 0`, and a compactly supported force

Verified by the parent directly at `NavierStokes/ComparatorR3Theorem.lean:33-35`
(`option_C_of_compact_candidate`):

```lean
  refine ⟨fun _ => 0, toComparator (rescaledForce ν f),
    zero_initial_condition_decay, hFd, ?_⟩
```

So the exhibited initial velocity is **identically zero**, and the exhibited force is
**compactly supported in space and in time** (`h.force_support`, `h.force_time_support`, :29-32),
from which `ForceConditionDecay` is discharged by
`CompactSpatialForceDecay.forceConditionDecay` (:30).

This is not a defect: the challenge is Fefferman's alternative **(C)/(D)**, which explicitly
permits an external force satisfying condition (5), and the previous audit already recorded that
the two *existence* alternatives (A)/(B) were deleted from the copied statement because OpenAI
does not claim them. But it is the single most quotable scope fact in the artifact and it belongs
in any summary:

> what is proved is **breakdown from rest under a compactly supported external force**, not
> blowup of unforced Navier-Stokes.

It also relocates the mathematical weight. Two of the three obligations I had flagged as the
"real content" after the force-is-the-residual discovery are cheap: the force's polynomial decay
follows from compact support, and `u₀`'s decay is `zero_initial_condition_decay`. What remains
load-bearing is (i) smoothness of the glued force **through** `t = 1`, (ii) the construction of
the candidate flow whose response blows up, and (iii) uniqueness. Worker `ns-force-and-blowup`
has been redirected accordingly.

## W10 `ns-uniqueness` — the non-existence is NOT a subclass claim — 224 OK, 0 kernel-risk

Report: `workers/ns-uniqueness.md` (+ three children: pressure, flux, estimates). 67 files /
13,049 lines surveyed; OK 224, UNCLEAR 2 (cosmetic), SUSPICIOUS 0, KERNEL-RISK 0.

This was the other place a non-existence claim could quietly shrink, and it does not:

- `candidate_global_agrees_before_one` (`NavierStokes/R3/WholeSpaceUniqueness.lean:104`) takes
  **only** `CandidateProperties ν u p f K` plus **one** `GlobalFiniteEnergySolution ν f`, and
  yields agreement on **all** of `[0,1)`.
- That competitor class is the challenge's, with nothing added. **Parent-verified independently**
  at `NavierStokes/R3/ProblemStatement.lean:125-135` and
  `NavierStokes/R3/ComparatorBridge.lean:48-74`: `globalSolutionOfComparator` builds every field
  of `GlobalFiniteEnergySolution` from the challenge structure's own fields — `energy_bounded`
  from the challenge's `integrable` + `globally_bounded_energy`, the PDE from
  `comparator_equation_Rn`, the divergence from `h.div_free` — and the structure's docstring
  states, truthfully, "there are no support, periodicity, pressure-growth, derivative-growth, or
  energy inequality assumptions on a competitor".
- General `ν` reduces to `ν = 1` by a **space-only** rescale with an exact energy factor
  (`ViscosityScaling.lean:182,141,24`, `SpatialEnergyScaling.lean:27`).
- The comparison is a Gronwall estimate on a **closed** `[0,T]` with `T = t < 1`, never at
  `t = 1`; dissipation is absorbed with `δ = 1/2`; the pressure flux is killed by `∇χ_R`
  (`LocalizedTransport.lean:83-89`) rather than by assuming decay of the competitor's pressure —
  which matters, because a competitor's pressure is only determined up to a function of `t`.
- Kernel risk across those 67 files: **zero** `inductive`/`.rec`/`termination_by`/`WellFounded`/
  metaprogramming, largest numeral 40, 6 trivial `decide`.
- This worker **independently found and patched the same dot-notation gap** in my cone instrument
  that `euler-cauchy` reported (their patch, without import scoping, gives 40,414/52,516; my
  mark 3, with scoping, gives 38,076). Two workers finding the same instrument bug from
  different directions is the strongest evidence in this audit that the fix was necessary.

---

## The cone, mark 4 — and the instrument's honest history

A third worker (`euler-packet`) found the **mirror** of the mark-3 bug: a **trailing** projection,
`initialDatum_finite_lifespan.choose` (`Euler/PacketFiniteLifespan.lean:54`), which my
suffix-only resolver also dropped. Consequence, and it is exactly the failure mode that matters:
the **entire Euler finiteness spine** read as out-of-cone (`initialDataLimit_no_euler`,
`false_of_evolution`, `PacketFiniteLifespan:31/46/56`, `gradient_lower`, `gradient_atTop`,
`previousShear_ge_index`) while `lifespan` itself read as in-cone. The worker measured the two
fixes separately (+241 for trailing alone, +9,004 for both directions) and kept its probes at
`workers/_probe/cone_{base,tail,both}.py`.

`cone.py` now resolves a token against **every contiguous run** of its components.

| mark | resolution rule | decls in cone | theorems in cone |
|---|---|---|---|
| 1 | whole token or its suffixes, no scoping | 33,163 | 22,643 |
| 2 | + import scoping (sound) | 28,145 | 19,214 |
| 3 | + leading-receiver dot notation | 38,076 | 27,456 |
| **4** | + trailing projections (every contiguous run) | **38,369** | **27,725** |

Verified after the fix: the recovered spine is in-cone, and the three declarations this audit
found genuinely dead — `stocks_formulas`, `polynomial_jetRate_of_stages`, `FactorSupportAt` and
its cluster — are still out. **Denominator for coverage claims: 27,725 in-cone theorems.**

Three workers found this class of bug independently, from three different files, and each of them
was right. That is the strongest argument in this audit for making workers re-derive with their
own instrument and telling them to disagree loudly: a shared instrument's blind spot is a
common-mode failure, and the only thing that caught it was disagreement.

## W11 `euler-packet` — packet finiteness is earned analysis, not a trick

Report: `workers/euler-packet.md` (+ 3 scratch files). 16 files / 199 declarations, 91 read
line-by-line. OK 63, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0.

- `initialDataLimit_no_euler` (`Euler/PacketStageInitialLimit.lean:106`) is a genuine
  contradiction between a **proved divergence** (`previousShear ≥ n+1`, `gradient ≥ shear/2`) and
  a **proved no-escape bound** (H³ stability + Sobolev embedding + compact trajectory). Not a
  `Classical.choose` of the conclusion.
- `constructionScales` (`Euler/PacketInfiniteConstruction.lean:68`) is a `Classical.choice` on a
  **proved `Nonempty`** record of numbers plus 6 `SmallSeries` fields, each carrying real
  `0 ≤ ·`, `Summable`, and `tsum ≤ d` bounds — i.e. actual convergence, not an assumed one.
- `stages` is **structural** recursion (`rfl` unfolding, no `termination_by`, no `Acc.rec`), and
  `Tstar ∈ [baseHorizon/12, baseHorizon] ≤ 1` comes from real `rpow` asymptotics, not from a
  numeral computation. Kernel numerals in scope: three `decide : 2 ≠ 0`.
- Open items it handed on, now dispatched: **P2** — is the bundled `Evolution` class *stronger*
  than the challenge's notion of an Euler solution, and if so is every extra field *proved* from
  challenge data (worker `euler-evolution-class`)? **P4** — 28 `Stage` fields still rest on
  unread `forwardNext`/`joinedNext` (worker `euler-stage-fields`, also asked what the ten
  `attribute [local irreducible] Parent.child initialParent` sites are hiding from `simp`).
  Its P1 was already settled benign by `euler-spine` and I told it so.

---

## W12 `ns-force-and-blowup` — the gluing is honest, the blowup is closed-form, and A6 needs one correction

Report: `workers/ns-force-and-blowup.md` (+3 children). Mine 41 declarations (OK 35, UNCLEAR 6),
children 151/48/73 declarations, **0 KERNEL-RISK** throughout; in its 21 files: no `inductive`,
no `.rec`, no `WellFounded`, no metaprogramming, one `decide` (`2 ≠ 0`), no literal above 2 digits.

**Correction to A6, from this worker, verified by the parent at
`NavierStokes/R3/ComparatorBridge.lean:85-86`.** The live route for option (C) is
`comparator_of_breakdown`, not `option_C_of_compact_candidate`, and it passes the force
**unrescaled** at the **same** `ν`:

```lean
  refine ⟨fun _ => 0, toComparator f, zero_initial_condition_decay,
    forceConditionDecay_of_compact h.force_smooth h.force_support.1, ?_⟩
```

So A6's substance is unchanged and now doubly confirmed on the live path — **`u₀ ≡ 0`, force
compactly supported, decay discharged from compact support** — but the `rescaledForce ν` route I
quoted is dead code. The scope sentence stands: *breakdown from rest under a compactly supported
force*.

**The smoothness-through-`t = 1` plumbing is honest.** The glue is `if t ≤ 1 then residual else`
a **real Borel series** (`SpacetimeGluing.lean:192,235`) — no assumed jet growth, and none of the
"all jets are zero so the extension is trivial" shortcut. The one-sided Whitney theorem
(`SpacetimeEndpoint.lean:250,277`) is genuine: an MVT lemma, `UniqueDiffOn` actually true, and the
local uniformity hypothesis actually used. `ForceConditionDecay`'s quantifier order is right —
`C` is fixed before `x` and `t` — and the support is `tsupport ⊆ Icc (1/16) (21/16) ×ˢ compact`
(`PositiveTimeForce.lean:61-80`).

**The blowup is closed-form and not vacuous:** `‖u(t,0)‖ = (1-t)^{-(1/2+h)} · j` with `j > 0`
(`BaseResidual.lean:90-100`, `FinalSlowBase.lean:372-378` via `W.axis.small.j_pos`), and the
corrections vanish near the axis (`GermCandidateAssembly.lean:109-144`), so the blowup is the bare
self-similar base rather than an artifact of the correction series.

**All remaining NS content reduces to two predicates**, `VanishingJointJets` and `AwayExtensions`
(`JointResidualLimits.lean:84,81`), discharged from `StageEstimates.finite_residual`
(`MixedCandidateAssembly.lean:62-65`) at `ActualCandidateAssembly.lean:1090,1100`.
**Dispatched:** worker `ns-stage-estimates`, told explicitly to check whether this cluster's
stagewise estimate is proved by construction or is another never-proved `hres`-style hypothesis
like the one `jetrate-callsites` found, and to hunt an asserted `J → ∞` / `t → 1⁻` interchange.

---

## W13 `euler-interpolation` — both remaining Euler limit steps are proved — no gap

Report: `workers/euler-interpolation.md`. 18 in-scope declarations read line-by-line (10 in
`SmoothFieldSobolevTime.lean`, 8 in `SobolevCauchyInterpolation.lean`): 16 OK, 2 OK-with-remark,
**0 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS**; two children added 13 + 33 OK. Both key lines are
in-cone, and the 4 out-of-cone rows it checked are genuinely unused.

- The **endpoint upgrade** (`SmoothFieldSobolevTime.lean:96` via `:86`) involves no one-sided
  derivative gymnastics: it delegates to `SeparatingTimeDerivative.lean:49`, which (a) proves
  `f t = f 0 + ∫₀ᵗ g` on the **closed** `Icc` by Mathlib's FTC-2
  (`integral_eq_sub_of_hasDerivAt_of_le`, needing only an `Ioo` derivative plus closed-interval
  continuity), (b) differentiates the integral by FTC-1 (`integral_hasDerivAt_right`, two-sided at
  every real `t`), (c) transfers by `congr_of_mem`. Integrability and `CompleteSpace` are proved.
  This also resolves a predecessor's escalation: the `Ico`-including-`0` derivative that the
  Gronwall step needs **is** supplied.
- The **interpolation** (`SobolevCauchyInterpolation.lean:78`) is **not** compactness and is not
  used as such — no Rellich-Kondrachov anywhere. It is Landau/Kolmogorov
  `|∂f|² ≤ |f|·|∂²f|` (`word_square_le_parent`, `SobolevInterpolation.lean:17`) by genuine
  integration by parts plus Cauchy-Schwarz, with `n + 2 ≤ s` tight. It converts an **L²-Cauchy**
  input into full-sequence Cauchy at every order, which is exactly what the consumer
  (`OrdinarySmoothLimit.lean:31`) wants. Shape matches.
- Kernel surface in scope: **zero** `decide`, `.rec`, `termination_by`, metaprogramming, or
  4-digit numerals.
- Burden moved again, and this is now the Euler half's last analytic frontier: the route is
  Cauchy-based, so the weight sits on the **energy/Gronwall estimates**
  (`Euler/OrdinaryEulerL2Stability.lean:136`, `Euler/HigherEnergy.lean:101`).
  **Dispatched:** worker `euler-gronwall`, told specifically to hunt a constant that secretly
  depends on the solution being estimated — which would turn an a-priori estimate into a tautology.

## Coverage, stated honestly — `COVERAGE.md`

New ledger. Restricting to files containing at least one in-cone theorem: **2,306 files, 27,753
in-cone theorems**. After 13 worker threads and 40 reports, **395 files are cited by some report,
holding 6,808 in-cone theorems = 24.5%** — and "cited" is a deliberately generous upper bound,
since some reports name a file to say they read three lines of it.

What that 24.5% contains is the part that matters most: both deliverable spines end to end, all
14 inductives, all 12 `termination_by`, all 5 explicit recursors, all 210 `decide` sites and all
121 large numerals. What it does **not** contain is the Navier-Stokes **estimate mass** — the
long `nlinarith`/`calc` files. For kernel trust those are the lowest-risk declarations in the
artifact (no inductives, no recursors, no `decide`, numerals of a few digits); for mathematical
correctness they are exactly where an off-by-one in a constant would hide.
**Dispatched:** worker `ns-correction-step` on the top of that queue
(`CorrectionStep.lean`, 9,849 lines / 264 in-cone theorems; then `InitialPhysicalData.lean`, 167),
with instructions to sample by *proof pattern* rather than by prefix and to state exactly what was
read versus sampled.

---

## W14 `euler-evolution-class` — the Euler refutation really does cover the challenge class

Report: `workers/euler-evolution-class.md` (+3 sub-notes). 30 declarations OK, **0 UNCLEAR,
0 KERNEL-RISK, 0 SUSPICIOUS**. 139 of 157 audited rows in-cone; the 18 out-of-cone rows are unused
alternative routes.

Answering `euler-packet`'s P2: **`Evolution` (`Euler/OrdinaryEulerDifference.lean:21-32`) IS
stronger** than the challenge's Euler-solution class — it carries all-order L² jets, their time
continuity, and a gradient-packaged pressure. That is exactly the shape in which "no solution
exists" could quietly become "no *nice* solution exists". It does **not**, because the missing
bridge exists and is discharged from an arbitrary challenge solution:

**Parent-verified at `Euler/ComparatorLocalEvolution.lean:64-97`.**
`exists_evolution_of_commonCompactCurl` takes `h : EulerExistenceAndSmoothnessR3 u₀ v p` — the
challenge structure verbatim — plus a compact-vorticity support hypothesis, and returns an
`Evolution` whose velocity **is** `v` (`recoveredVelocity_field` :45 is `rfl`). And
`compactCurlLocalUpgrade` :91 derives that support hypothesis from `h` itself together with
compact initial vorticity of the *constructed* datum, not of the competitor. So nothing is assumed
on the competitor and the refuted object is literally `v`.

Every extra field is earned rather than assumed:
- the L² jets come from Caccioppoli + Fatou div-curl recovery (`DivCurlTensorRecovery.lean:79`,
  `DivCurlRecovery.lean:53-150,174`) with a **field-independent** constant;
- their time continuity from an L²-Lipschitz bound plus real interpolation
  (`CompactVorticityTimeUpgrade.lean:83-108`, log-convexity by integration by parts,
  `OrdinaryWordInterpolation.lean:31`);
- `time_law` from the challenge's own `h.euler` through `ClassicalBridge.lean:33`
  (`derivWithin (Ici 0) → HasDerivAt` only at `t > 0` — no junk-value trick) plus
  `pointwise_derivative_of_l2` (`OrdinaryStrongTime.lean:48`);
- the competitor's **pressure is discarded and rebuilt** by Helmholtz
  (`OrdinaryHelmholtzField.lean:60`), so no pressure regularity beyond the challenge's
  `pressure_smooth` is ever demanded.

**Direction check, which is the whole point:** every bridge lemma goes *challenge ⇒ Evolution*. The
only converse is an honest `iff` (`ComparatorSobolevEvolution.lean:151`,
`OrdinaryEulerClassicalClass.lean:271`) and it is used **only for the positive half** of the
headline (the singular solution that must exist), never for the refutation. The `toL2` junk branch
never fires (`toL2_field :15` via `dite_eq_left` on `A.memLp`).

Kernel surface in its 22 files: **zero** `decide`/`axiom`/`sorry`/`macro`/`elab`/`set_option`/
`native_decide`/`unsafe`/`partial`/`termination_by`/`WellFounded`/`.rec`; all structures
non-recursive and non-indexed (recursors used only as projections); largest numerals 3600, 39, 13,
and the only 5+-digit numeral in scope is a URL commit hash.

It also sharpened `euler-packet`'s P1: the `attribute [local instance] CompletePartialOrder.toSupSet`
at `Euler/Solution.lean:41` is in force for lines **43-56 only**, i.e. for
`exists_compact_smooth_euler_singularity` — **not** for `euler_breakdown_R3` at :33. Combined with
`euler-spine`'s mechanism (Mathlib's only `CompletePartialOrder ℝ≥0∞` route yields `ENNReal`'s own
`sSup`), A3/E2 is now closed as benign with the affected line range pinned.

---

## W15 `euler-stage-fields` — all 26 `Stage` fields earned; the junk value points AGAINST the claimant

Report: `workers/euler-stage-fields.md`. 269 declarations read line-by-line across 20 files.
**26 of 26 `Stage` fields OK**; 48 supporting declarations = 46 OK + 2 UNCLEAR; **0 KERNEL-RISK,
0 SUSPICIOUS**. No circularity: `joinedNext` carries no `Stage (n+1)` hypothesis.

- **Degeneracy is closed by an identity chain, not by rhetoric.** `frame_shear` forces the new
  frame's `primaryShear` to be `shear J X n`, and `ParentFrame.remainder_bound`
  (`Euler/PacketSourceGeometryData.lean:45`) ties that number to the **actual strain field** with
  slack `k^(-1/4)`. It is realisable because `deriv (profile δ) 0 = δ⁻¹`
  (`Euler/EulerProof.lean:11818`, with `profile δ t = arctan (sin t / (1 + δ - cos t))`).
- **The junk value here runs against the claimant, which is the direction we want.** If `δ = 0`
  were admissible, `deriv` would collapse to junk `0` and the stage invariant would be vacuous —
  so `0 < δ` is a **field** of the geometry record (`Euler/ParentGeometryForwardChoice.lean:38`),
  obtained from `spike J X n > 0`. A construction that *needs* non-degeneracy to state its own
  invariant cannot be satisfied by the degenerate object.
- Two fields are literally `le_rfl` (`Euler/PacketForwardSuccessor.lean:154,157`) and are
  nonetheless honest: `renewal_costs` supplies `G = K` and `error = k^(-1/4)` by `⟨rfl, rfl⟩`
  (`Euler/ParentGeometryChoiceRenewal.lean:66`), and `olderShear (n+1) ≡ previousShear n`,
  `previousFrequency (n+1) ≡ frequency n` hold by iota. The real burden sits in `B_bound` and
  `remainder_bound`, which are proved.
- **The `attribute [local irreducible] Parent.child initialParent` question (W2-E4) is answered:
  it is an elaboration-cost device, not a semantic one.** The repo documents the measurement
  itself — 353,857 → 3,224 heartbeats for `GeometryForwardChoice.mk.inj`
  (`Euler/ParentGeometryForwardChoiceNoOptions.lean:6-32`). Nothing *needs* the opacity; in fact
  `horizon_eq := rfl` requires `child` to be **transparent**. And reducibility is elaborator-only,
  so the kernel ignores it entirely.
- Kernel surface: zero `decide`, zero large numerals, zero metaprogramming, structural recursion,
  symbolic iota only.
- Two declarations left unread (`forward_uniform_child_label_bounds`, `forwardGeometryFrame`).
  **Dispatched:** worker `euler-forward-frame` to close the thread, with the specific instruction
  to check they cannot admit a degenerate instance.
