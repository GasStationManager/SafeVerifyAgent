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

---

## A7 — the artifact's real defeq workload: 529 in-cone theorems proved by a bare `rfl`

Parent-produced, mechanically, over the in-cone theorem set (`RFL_SITES.csv`). Every measurement
so far said the same thing — the *computational* surface is tiny (`decide` on ≤4-digit literals,
one-machine-word numerals, one-iota-step recursors). That left a question nobody had asked
systematically: **where does the kernel have to decide a definitional equality?** A `rfl` proof is
exactly that obligation, and unlike `decide` it is invisible to a search for computation.

Measured over the 27,753 in-cone theorems/lemmas:

| | |
|---|---|
| proved by exactly `:= rfl` / `:= by rfl` | **529** |
| statement length: median / max | 139 / **629** characters |
| whose statement names a recursive construct | **7** |
| proof head containing `decide` | 4 |
| bare `by simp` (relies on the ambient simp set) | 2 |

The largest: `Euler/PacketInitializedSpatialBudget.lean:115` (629),
`Euler/PacketForwardInitializedSpatialBudget.lean:113` (622),
`Euler/RegularizedForcingWord.lean:29` (614),
`NavierStokes/CorrectionInitialization.lean:1012` (591),
`NavierStokes/PrimaryTargetBounds.lean:631` (566),
`Euler/ParentForwardInitialSupport.lean:40,49` (541 each),
`NavierStokes/ActualParticularStageControls.lean:813,821` (531/528).
Files with the most: `NavierStokes/SlowRecursion.lean` (16), `PhysicalResidualTZ.lean` (14),
`GlobalSlowProfiles.lean` (12), `Euler/EulerProof.lean` (10), `Euler/PacketStageGuards.lean` (10).

Why this is the right thing to look at next, in the threat model we were given: a defeq check is
where **structure eta** lives (escalation A3 came down to exactly that), where **`Matrix.cons`/`Fin`
literal index resolution** runs through `Nat` literal comparison (vector 2), and where an **iota
chain over a recursive definition at a closed argument** would appear (vector 1, the dangerous
mode). Note the encouraging prior: the 7 sites whose statement names a recursive construct are the
only ones where an iota chain is even possible, and two of them sit in the course-of-values
well-founded files that `wf-recursion` already found use the safe `WellFounded.fix_eq` idiom.

**Dispatched:** worker `rfl-defeq`, to classify the top 25 by statement size plus all 7
recursion-touching sites into (i) structure-literal projection, (ii) beta/delta of non-recursive
`def`s, (iii) one iota step on a symbolic constructor, (iv) an iota chain at a closed argument,
(v) `Fin`/`Matrix.cons` literal index resolution, (vi) structure eta — and to re-derive the 529
count independently.

---

## W16 `ns-stage-estimates` — the NS residual-jet predicates are discharged by a real induction

Report: `workers/ns-stage-estimates.md`. ~160 declarations tabled: OK 148, UNCLEAR 5 (all
delegated), **0 KERNEL-RISK, 0 SUSPICIOUS**.

This was the last structural doubt on the NS side, and it is **not** the dangling-hypothesis pattern
that `jetrate-callsites` found elsewhere in this repo:

- `StageEstimates.finite_residual` (`MixedCandidateAssembly.lean:62`) *is* a hypothesis field, but
  on the **live** path it is discharged by a real theorem: `GluedStageEstimates.lean:436` →
  `ActualCycleResidualBounds.finite_residual_rates:1190` → `Invariant.residual_jetRate:1158` +
  `native_residual:845`, fed by a genuine **`Nat` induction** (`ActualCyclePreservation.state_runInvariant:826`,
  base `:773`, step `:817`). With `gain h j = h·j/10` (`ActualIterationLedger.lean:29`),
  `σ 0 = 1/5`, `σ (J+1) = σ J + 1/10`, the divergence `gain → ∞` is then pure arithmetic.
- `VanishingJointJets` (`JointResidualLimits.lean:84`) is the **strong** form — jets tend to
  **zero**, and **jointly**, along `𝓝[openPast 1] (1,0) = 𝓝[<] 1 ×ˢ 𝓝 0`. `boundaryLimits:120` is
  *defined* to be `0` at `x = 0`, which would be the junk-value shortcut, but `boundaryLimits_joint:130`
  **re-proves** the limit from `hzero`, so the definition is not what carries it.
- **No interchange of limits and no assumed summability**: `J` is chosen *after* `(m,r)`
  (`DiagonalResidual.residual_jetRate_of_stages:196`) with an exact `abel` identity and the losses
  are `J`-free; `potentialSum` is a `tsum` (`SolenoidalDiagonal.lean:37`) whose summability is
  **proved** (`summable_cutStage:69`) and which is locally a **finite** sum wherever `q > 0`
  (`eventually_zero_tail:46`). The worker's own words: "I disagree loudly in the negative here: I
  expected a hole and found none."
- It also corrected my brief: the consumer I cited
  (`MixedCandidateAssembly.candidate_of_finite_stages:130`) is **out of cone / dead**; the live twin
  is `GermCandidateAssembly.lean:164`. Both call sites `:1090/:1100` are in-cone with all hypotheses
  available, and `hq := le_rfl` is genuine (`qbig := Q (firstBand)`, `qbig > 0`).
- Kernel surface in its files: **zero** `decide`/`native_decide`/`termination_by`/`WellFounded`/
  `.rec`/`inductive`/metaprogramming/`axiom`/`sorry`; 4 structural `Nat` inductions, exactly one
  1-step recursor `whnf` (`ActualCyclePreservation.lean:153-163`); largest literal 100,000.

**Dispatched:** worker `ns-analytic-step` on its top escalation — `CorrectionAnalyticStep.step`'s
**+1/10 per cycle**, which is unread and on which the entire quantitative NS claim rests, with the
specific instruction to check that cycle `n`'s *output* meets cycle `n+1`'s *input* field by field
(the way an induction like this fails is by not chaining).

---

## W17 `euler-gronwall` — the Euler energy estimates are uniform and non-circular

Report: `workers/euler-gronwall.md` (+2 sub-auditors). **55 declarations OK, 0 UNCLEAR,
0 KERNEL-RISK, 0 SUSPICIOUS.**

The specific failure mode I sent it to hunt — a constant that secretly depends on the solution being
estimated, which would turn an a-priori estimate into a tautology — is **absent**:

- `tameEnergyConstant m = 6 · h3ProductConstant · Σ_{n ≤ m} 6ⁿ` (`Euler/TameEnergy.lean:86`) is
  closed-form **in `m` alone**, built from fixed embedding constants (`Euler/H3Products.lean:16`).
- In the L² chain, `K` bounds only the **reference** evolution `U` (`OrdinaryEulerL2Stability.lean:18,27`),
  and the estimate is linear in the estimated norm.
- The nonlinear term is an exact **commutator**: the pressure contribution dies because solenoidal =
  `gradientᗮ` (`SobolevWordConstraints.lean:49`), the transport term by integration by parts with
  `div = 0` (`TransportCancellation.lean:42`).
- Gronwall runs on a **closed** `Icc 0 T` of a *given* `Evolution`; the blowup time never enters
  (`time_law` lives on `Ioo 0 T`, `OrdinaryEulerDifference.lean:28`).
- Uniqueness (`OrdinaryEulerUniqueness.lean:24`) uses the **hypothesis-free**
  `l2_stability_gradientIntegral` (`GradientStability.lean:54`) in the right direction on the full
  bundled class, and `gradientNormPath` is genuinely finite through a proved H³→L^∞ bounded-continuous
  bound with an **unconditional** `finiteField_apply` (`MeanSobolevBoundedField.lean:104,108`) — no junk
  fallback.
- It closed two predecessor escalations: the interpolation constants **are** `k`-uniform
  (`Euler/OrdinaryEulerCauchy.lean:54,78`), and the endpoint derivative is **not** an MVT argument —
  the Bochner primitive is reconstructed by separating point-evaluations plus FTC
  (`SeparatingTimeDerivative.lean:24,49`).
- Kernel surface in this layer: **empty**. Zero `decide`/metaprogramming/`termination_by`/
  `WellFounded`/`.rec`/`deriving`; the only real `Nat` work is `3⁰..3³ → 40`
  (`H3Norms.lean:31,47`).
- Its escalation (2), "`Evolution` assumes all-jet time continuity", is **already answered** by
  W14: the bridge *derives* that continuity from an arbitrary challenge solution
  (`CompactVorticityTimeUpgrade.lean:83-108`). Cross-closed.
- Its escalation (1) — the constant grows like `6^m` in the derivative order — is dispatched as
  worker `euler-gevrey`: harmless if every consumer fixes `m` first, and it matters only if some
  Gevrey/analyticity consumer needs order-uniformity.

## W18 `euler-forward-frame` — Euler packet thread closed, with one type-level note

Report: `workers/euler-forward-frame.md`. 10 files, 61 declarations, all in-cone: 16 OK,
2 UNCLEAR (naming/depth), **1 SUSPICIOUS-benign**, 0 KERNEL-RISK.

- **The note worth keeping:** `forwardGeometryFrame` (`Euler/ParentPacketPrimaryCenter.lean:73`) has
  `hδ : 0 < δ` and `hη : η ≠ 0` but **no `0 < α`**, so the definition *alone* admits `α = 0`, whence
  `c = α/δ = 0`, `shear = 0`, and `remainder_bound` degenerates to "strain increment ≤ error" — a
  statement about nothing. It is **closed one layer up** by `Guards.shear_pos : 0 < P.shear`
  (`Euler/PacketSourceGeometryData.lean:98`), which is strictly stronger than `0 < α`. Benign today;
  the *type* does not certify it. Same shape for `hτ : 0 ≤ τ` without `τ < N.T`, so `Icc τ N.T` could
  be empty at the definition level and is again closed by the guards.
- The `0 < δ` field is spent exactly at `profile_deriv_zero` (`Euler/EulerProof.lean:11818`) inside
  `forward_primary_center_term`, giving the amplification coefficient `α·δ⁻¹`. No `fderiv` junk:
  `center_update_of_odd` uses `fderiv_fun_add` with both differentiability hypotheses supplied.
- The `0` in `fderiv (w t) 0` is the **spatial centre**, not a time — so the estimate is consumed at
  every time in `Icc τ N.T ⊆ Icc 0 G.T`, closing a predecessor's worry.
- `forward_uniform_child_label_bounds` inherits all PDE content from `forward_uniform_flow_and_shear`
  and adds only coarsening plus the label bound. "Uniform" in the name means the
  `uniformConstant`/`uniformPower` source-cost comparison, **not** one bound for all children — it is
  uniform in `t` and `n`, and the quantifier order matches all four consumers exactly.
- Kernel: zero `decide`/`.rec`/`Acc.`/`WellFounded`/`termination_by`/metaprogramming; 9 tiny
  `norm_num`; the only genuine kernel numeral is `10·(6+2) ⇒ 80` unifying `k^(10(q+2))` with `k^80`.
  `fixedCost 6 ≈ 3.4e7` is **never evaluated** — only `eventually_ge_atTop` is used.
- Open (recorded, not yet dispatched): `Euler/ChildParticleSourceBound.lean`
  `source_physical_label_bound` is unread — is the exponent `10(q+2)` **derived** or **chosen**?

## E3 (the previous audit's periodic-pressure item) — confirmed at source by the parent

`ns-spine` reported that the competitor's `pressure_periodic` field is genuinely *used*. Verified
directly: `NavierStokes/PeriodicUniqueness.lean:435-441` `cubeIntegral_pressure_energy_zero` takes
`hpp : UnitPeriods (fun x => p (t, x))` as a hypothesis, and the energy identity at `:533` discharges
it with `unitPeriods_sub hpp hpq` — i.e. the periodicity of **both** pressures. So the periodic
argument really does need the competitor's pressure to be 1-periodic, and alternative (D) as
formalized upstream (and therefore as proved here) excludes only periodic-pressure solutions.
This is inherited from the independently authored upstream, not introduced by the claimant, and
alternative (C) is a full Clay alternative by itself — so the headline does not rest on it. But it is
a scope fact, and it is now confirmed by reading the Lean rather than by trusting a docstring.

---

## W19 `ns-correction-step` — the largest unread NS file, and the sharpest open question so far

Report: `workers/ns-correction-step.md` (+2 sub-reports). `NavierStokes/CorrectionStep.lean`:
9,849 lines, 559 declarations, 264 in-cone theorems — **110 declarations read line-by-line** (93 of
them in-cone) plus all imported predicate definitions; the rest scanned. OK 104, UNCLEAR 4,
**0 KERNEL-RISK, 0 SUSPICIOUS**.

**It corrected my brief, usefully.** I called this an "estimate/assembly file with long
`nlinarith`/`calc` chains". It has **0 `nlinarith`, 0 `calc`, 1 `norm_num`**, and **374 of 418
proofs contain no arithmetic tactic at all**. It is a *transport* file — definitional plumbing that
moves data between records. That is worth recording because it changes where the arithmetic risk in
the NS half actually lives, and because a brief built on a guess sends a worker looking for the
wrong thing.

**The sharpest open question in the audit right now.** The `σ → σ + 1/10` per-cycle gain that the
whole scheme lives on reduces to **one imported inequality** at `CorrectionStep.lean:8103` (= `:5495`),
which hands `1 + (s + 1/10) ≤ (1 + s - 2k) + 9/10 - 2k  by linarith` to
`MovingMomentBounds.rankStage_defectBounds`; `:8021` and `:8471` are bookkeeping around it. And:

> `MemClass` permits a **new degree `p` (and constant `C`) at each application**. So "+1/10 per
> cycle over many cycles" is **empty** if `p` or `C` may grow with the cycle index — the exponent
> improves while the class it improves in gets weaker.

Partial counter-evidence from the same worker: `slow = max 1 n²` against `eps = Q^h`, so a
`growth^p` factor cannot eat the gain; and the `MemClass`/`UniformClass` quantifier order is sound;
and the sign flip at `:76` is exactly right given `gr`'s negation
(`MeanIncrementBounds.lean:338`). But it could not close the question at its own level.
**Relayed to worker `ns-analytic-step`**, which is reading `CorrectionAnalyticStep.step` right now,
with the instruction to determine whether `p` and `C` are fixed across cycles or re-chosen per cycle,
and to say so loudly if they may grow unboundedly while the ledger only sums the `1/10`s.

Other findings:
- `fullResidual:396` = residual + virtualDivergence + `errors.base`, while the *controlled*
  `fullGoodResidual:402` subtracts `errors.total` as well; `:414` is `simp [def]`, content-free.
- `iterate_representation:6963` (the recursion invariant) is conditional on `SameCarrier` for **all**
  `n`; otherwise `addBlock` is not field addition (`:6838`). Discharge claimed at
  `ActualCandidateConstruction.lean:83`.
- **A collapse check nobody had done:** `StripData` permits `domain = ∅` and `zeta = 0`, which would
  make every class membership vacuous; the question is settled (or not) at
  `ActualInitialization.lean:651`.
- Sub-reports: `TerminalEdgeFactor.lean` (OK 233 / UNCLEAR 1) — its three headline in-cone theorems
  `:1467/:1562/:1659` are **near-tautological**, holding because `Tz` is flat-zero;
  `InitialPhysicalData.lean` (OK 230) — the `else 0` branches at `:368,376` have a provably `t < 1`
  gate so they are not live, but the potential is identically `0` for `t ≥ 1` and **all 177 theorems
  survive if `cartesianPotential = 0`**.
- Kernel: nil. The only recursion is `CycleState.iterate:6952` with 3 iota steps; all 20 large
  numerals are `1/100000`.

**Dispatched:** worker `ns-nondegeneracy` on the two collapse checks (`StripData` non-degeneracy at
`ActualInitialization.lean:651`, and `SameCarrier` for all `n` at `ActualCandidateConstruction.lean:83`)
plus the `cartesianPotential = 0` survivability question.

## W20 `euler-gevrey` — the `6^m` growth is harmless: no consumer needs order-uniformity

Report: `workers/euler-gevrey-uniformity.md`. 44 declarations: **OK 44**, 0 UNCLEAR, 0 KERNEL-RISK,
0 SUSPICIOUS. Closes `euler-gronwall`'s escalation (1).

- The quantifier order is `∀ q, ∃ C` **everywhere**, never `∃ C, ∀ q`, and there is no series in the
  order: `all_order_bounds_of_h3` (`Euler/OrdinaryEulerCauchy.lean:70-78`) introduces `q` *before* the
  witness that contains `tameEnergyConstant q`, and its interface
  (`OrdinaryEulerLimit.lean:86`, `∀ q, ∃ M, ∀ k t, …`) is instantiated only at `hb 3` (`:88`).
  `regularized_all_order` (`OrdinaryRegularizedEnergy.lean:153`) keeps `q` as a binder and its
  consumer (`OrdinaryEulerLocalExistence.lean:118-122`) uses only `q = 4`. So `6^m` is a **per-order
  amplitude**, not a constant anyone needs uniformly.
- The **lifespan is order-free**:
  `regularizedTime A = (2·(1 + tameEnergyConstant 3)·(1 + wordEnergy 3 A))⁻¹`
  (`OrdinaryRegularizedEnergy.lean:125`) — order 3 only.
- The Gevrey layer **cannot** consume it: zero grep contact (no Gevrey file mentions
  `tameEnergyConstant`/`wordEnergy`/`EulerOrdinarySobolev`, none imports `Euler.Ordinary*`), and the
  import DAG runs the other way. Decisively, the top-level Euler claim
  (`Euler/EulerSingularity.lean:115,133`) has **no analyticity/Gevrey/radius conjunct at all** — only
  `C^∞`, `C¹`-limsup `= ⊤`, and vorticity `∫ = ⊤`. So even a weak Gevrey index would not touch the
  headline.
- Also confirmed dead: `l2_stability_of_h3` (`OrdinaryEulerL2Stability.lean:148`, one grep hit — its
  own declaration) and `GradientControl.lean:119,132`. Correct, non-vacuous, unused.
- Kernel: zero `decide`, no numeral above 2 digits, zero `termination_by`/`.rec`/metaprogramming;
  `tameEnergyConstant 3` is **never evaluated** (its embedding constants are opaque).

**Dispatched:** worker `euler-label-bound` on the final Euler item —
`Euler/ChildParticleSourceBound.lean` `source_physical_label_bound`: is the exponent `10(q+2)`
(i.e. `k^80`) **derived** from the estimates or **chosen** with slack, and does any other packet file
quote a different exponent for the same quantity? A mismatch between a proved exponent and a quoted
one is exactly the defect class that survives a mechanical checker, because both statements are
individually true.

---

## W21 `ns-analytic-step` — the `+1/10` per cycle IS earned. Open question 1 closes.

Report: `workers/ns-correction-analytic-step.md` (+2 children). 45 declarations read
statement-and-proof: OK 44, UNCLEAR 1, **0 KERNEL-RISK, 0 SUSPICIOUS**.

**Parent re-derived the arithmetic by hand at `NavierStokes/SignedMeanGain.lean:426,462`, and it
checks out.** This is the inequality the entire Navier-Stokes half balances on, so it is worth
writing out. `remainderTensor_mem` :426 requires
`γ ≤ δ + β`, `γ ≤ α + η`, `γ ≤ 2β` (plus `β ≤ η`); `signed_tensor_bounds` :462 instantiates

    α = 1/2,  δ = 17/25,  β = 1/2 + σ - κ,  η = 1 + σ - 2κ,  κ ≤ 1/100000,  σ ≥ 1/5

and concludes `TensorClass s (1 + σ + 17/100 + κ)` for the remainder. Checking the three branches:

| branch | requirement | reduces to | at `σ ≥ 1/5`, `κ ≤ 1e-5` |
|---|---|---|---|
| `δ + β` | `1+σ+17/100+κ ≤ 1+σ+18/100-κ` | **`κ ≤ 1/200`** | holds, with 4 orders of magnitude to spare |
| `α + η` | `1+σ+17/100+κ ≤ 3/2+σ-2κ` | `17/100+3κ ≤ 1/2` | holds easily |
| `2β` (the **nonlinear self-interaction**) | `1+σ+17/100+κ ≤ 1+2σ-2κ` | `17/100+3κ ≤ σ` | holds with slack `3/100`, and **improves as `σ` grows** |

So the per-application gain in the exponent is `17/100`, the structural cap is
`δ - α = 17/25 - 1/2 = 9/50 = 18/100`, and **the cap is `σ`-free** — it does not shrink as the
exponent improves, which is exactly what my open question 1 asked. The ledger's `+1/10` is a
conservative **round-down** of `17/100`. The nonlinear self-interaction branch is genuinely present
and genuinely checked.

**And it chains.** The cycle invariant (`CorrectionStep.lean:9408`) carries only three `σ`-dependent
fields (residual `1/2+σ` :9440, mean :9443, debt :9445); the `σ`-free `17/25` `difference` requirement
is rebuilt each cycle at `CorrectionStep.lean:8632`, needing `17/25 ≤ 1/2 + σ - κ`, i.e. margin
`1/50` at `σ = 1/5` that **grows** with `σ`. The live induction is closed at
`ActualCyclePreservation.lean:826` with its `StepData` built at `:730`. There is **no upper bound on
`σ` anywhere**, which is the point.

**The `MemClass` degree worry that `ns-correction-step` raised is closed:**
`PhysicalGraphBounds.lean:806` `slow_power_absorption` charges a **fixed `+1`** for any slow power, and
the losses are `J`-free **by type** (`ActualCycleResidualBounds.lean:1145`, degree dropped at `:926`);
`δ` is not bounded below but is absorbed by the Gaussian `zeta`. So the class does not weaken as the
exponent improves. Residue: no `sup_J C_J` is proved, hence no *stage-uniform* statement exists — but
nothing in the claim needs one.

Kernel surface in scope: zero `decide`/`sorry`/`axiom`/`macro`/`termination_by`/`inductive`; one
`Nat` induction (off-cone); max numeral `1e5`. Dead code flagged: `ExponentLedger.lean:46,53` and
`CorrectionAnalyticStep:632,657,674` are off-cone.

---

## W22 `euler-label-bound` — the `k^80` exponent is CHOSEN, not derived — safe direction. Euler thread closed.

Report: `workers/euler-source-label-bound.md`. 21 declarations: OK 18, UNCLEAR 2, **1 SUSPICIOUS
(documentation overclaim)**, 0 KERNEL-RISK; all in-cone.

- **The exponent is chosen with large slack, and the slack is measured.** The ledger actually adds up
  to `6q + 8`, not `10q + 20`: amplitude `≤ k^6` (degree-5 `K³·amp²` plus 1 for the constant),
  radius `≤ k^5`, `radiusCoef ≤ k^6`, `ampCoef ≤ k^(6q+7)`, product `→ k^(6q+8)`. The jump to
  `10(q+2)` happens in **one step**, `pow_le_pow_right₀ hk1 (by omega)`
  (`Euler/SobolevSourceExponent.lean:73`). At `q = 6`: **derived 44 versus quoted 80 — 36 powers of
  slack** (with `k ≥ 69`). The direction is safe: it *weakens* an upper bound and needs only `1 ≤ k`.
  Individual constants are genuinely tight (`45 = 9 + 36`, `69 = 68 + 1`, `12 = 4·card (Fin 3)`).
- **No mismatch anywhere.** Every site uses `^80`, and `10*(6+2)` versus the literal `k^80`
  (`Euler/ParentUniformForwardChild.lean:72,78`) reconcile by **defeq**, so a mismatch there would be
  a type error rather than a silent difference. This was the defect class I sent it to hunt — a proved
  exponent and a quoted exponent differing while both statements are individually true — and it is
  absent.
- Uniform in `t` and `n`, quantifier order matches all consumers, `direction = EuclideanSpace.single`
  is non-degenerate, and `k^80` is realised by `exists_firstPacketChoice`.
- **The SUSPICIOUS item is a documentation overclaim:** `Euler/PhysicalChildSourceBound.lean:6` says
  "exactly `10(s+2)`" when the derivation gives `6s+8` and `10(s+2)` is a rounded-up envelope. Harmless
  for correctness; it is the sort of sentence that makes a later reader believe a bound is tight.
- **New residue, low priority:** `80` is hand-copied into `requiredExponent := 80*degree + 1`
  (`Euler/ParentNeighborThreshold.lean:23`) and into the test `80 ≤ 320`
  (`Euler/NormalPacketFrequencyGuards.lean:24,75-77`), which is the **only size check in the layer**
  and carries 4× headroom. Whether `320` is itself derived is unaudited. Given the 36 powers of slack
  below it and the safe direction, this cannot break the argument — it could only make a future edit
  that raises the true exponent silently invalid.
- Kernel: benign — zero `decide`/`inductive`/well-founded recursion in the three primary files; the
  heaviest obligation is the defeq `10*(6+2) = 80` (two-digit), plus 8 `omega` and small `linarith`
  certificates. `fixedCost 6 = 34,138,752` is **never evaluated**.

**The Euler thread is closed.** Every load-bearing declaration on the Euler deliverable path has been
read by at least one worker, and the parent independently re-verified the challenge-to-`Evolution`
bridge, the forced-instance question, and the finiteness spine.

---

## W23 `ns-nondegeneracy` — both collapse checks close negative, and the worker was right to disagree with my brief

Report: `workers/ns-nondegeneracy.md` (+2 children). 41 declarations line-by-line, 26 files /
2,227 declarations scanned: OK 39, **SUSPICIOUS 2**, UNCLEAR 0, KERNEL-RISK 0.

- **It refuted the premise of my own brief, correctly.** I asked it to check whether `StripData`
  admitting `zeta = 0` makes every class membership vacuous. It does not: `zeta = 0` makes `MemClass`
  **stronger**, because the majorant becomes `0` and forces all jets to vanish
  (`WeightedClasses.lean:78,115`). And the settlement site I was given (`ActualInitialization.lean:651`)
  is just `slow := slowScale` — it settles nothing. The real non-degeneracy is
  `actual_strip_nonempty` (`NavierStokes/ActualSignedMeanBinding.lean:54`) with an **explicit witness**
  `((a+b)/2, ((1,0),(0,0)))`, and every strip in the tower is a pullback of it
  (`geometry_strip := rfl`, `:665`). `zeta` is strictly positive in-cone
  (`ActualSignedStageControls.lean:764`, `NativeBandExtension.lean:372`) and used as a **lower** bound
  (`:777`).
- **The "everything survives if the field is 0" worry is false.** `speed_unbounded` is a **mandatory
  field** (`NavierStokes/R3/ProblemStatement.lean:109`, `ProblemStatement.lean:94-96`), and the in-cone
  H³ blowup of the **actual** field sits at `ActualCandidateAssembly.lean:1142` (`Witness:1121`,
  `witness:1153`), rooted in `BaseResidual.lean:104-114`:
  `|u(t,0)| = (1-t)^{-A·h} · d.axial 0 (0,0)` with `h₀ > 0` from `W.axis.small.j_pos`.
- **New escalation, and the last open structural question in the NS half (E1):** `Index B N0`
  (`NavierStokes/BaseChartJets.lean:825`, `PrimaryRepresentatives.lean:91`) — the wave tower's index
  set — is **never proved nonempty**. The artifact case-splits on emptiness
  (`ActualInitialMean.lean:318`, `ActualSignedUnmaskedBounds.lean:161,196`,
  `ActualSignedStageControls.lean:1132`) and the empty branch yields `oscillation = 0`. That is *sound*
  — but it means every wave estimate could be true because there are no waves. The worker's own
  formulation is the right one: **ask for one label.** Note the likely outcome, which the same report
  supports: the blowup is carried by the *base* field, so an empty index would make the wave tower
  decoration rather than falsify anything. **Dispatched:** worker `ns-index-nonempty`, told to say
  loudly if instead some in-cone theorem *needs* a nonempty index.
- `SameCarrier` (my item B) is **unconditional** (`hc`), by `Nat.rec` on `j`, discharged at
  `ActualCandidateConstruction.lean:80` → `ActualCycleParameters.lean:499,62`.
- Item C: the `t ≥ 1` regime is dead for the potential; the only object that crosses `t = 1` is the
  **force**, through `SpacetimeGluing.smoothExtension` (`CandidateFromLimits.lean:82-136`) — which this
  worker flagged as unaudited but which **W12 already audited** (a real Borel series plus a genuine
  one-sided Whitney theorem). Cross-closed.
- Kernel: zero metaprogramming/`inductive`/`Acc.rec`/`termination_by`; three one-digit `decide`; the
  largest literal (100,000) is a **real**, not a `Nat` (`SignedMeanGain.lean:463`).

---

## W24 `rfl-defeq` — the defeq workload is benign and BOUNDED; and my census was wrong by 12

Report: `workers/rfl-defeq.md` (+3 children). 78 declarations examined: **OK 78, 0 UNCLEAR,
0 KERNEL-RISK, 0 SUSPICIOUS**. This closes open thread 3, and it is the strongest single result of the
pass, because it bounds the one kernel surface that no computation marker can see.

**The bound.** Screening all in-cone bare-`rfl` statements against the repository's **87 recursive
definitions**: only **19 mention any of them**, and every one of those is either a base-case lemma at a
closed `0`/`[]` or a `succ`/`cons` lemma at a **symbolic** argument. So each is **≤ 1 iota step**,
**≤ 19 in total, and there are ZERO iota chains** anywhere in the artifact's `rfl` proofs. Further:

- only **3** statements contain a literal ≥ 10, and those are real coefficients (12, 10) — no `decide`,
  no `Nat.pow`/`div`/`mod`;
- `![…]` appears in **2** statements and both are compared **structurally with no index applied**, so
  there is **no `Fin`/`Nat` literal index resolution anywhere** — the `Matrix.cons` route into vector
  (2) is simply not taken;
- the mechanism everywhere else is projection of `where`/`{x with}` literals, delta of
  **non-recursive** defs, beta/zeta, and **proof irrelevance**. The long statements are long
  *argument lists*, not computation: the 657-char champion costs on the order of 10² head reductions.
- Task C answered **no** for all 28 `rfl`s in the well-founded files:
  `NavierStokes/SlowRecursion.lean:974` is a `rfl` *about* `WellFounded.fix`, but `n` is symbolic so
  `Nat.lt_wfRel.wf.fix … n` stays neutral on both sides and the real obligation is one `Subtype`
  projection. **Zero `Acc.rec` steps.**
- Only **one** site needs `Prod` structure **eta** (`NavierStokes/LocalSignedRequest.lean:523`) — which
  is the exact kernel feature escalation A3 reduced to, now with a single named witness instead of a
  general worry.

**And it corrected my instrument, for the sixth time this session.** My census said 529; the true count
is **541**. My splitter took the first `:=` in the body, which mis-reads a **named argument**
(`(B := B)`, `(h := …)`) as the start of the proof and mis-reads a **structure-instance proof**
(`theorem zero : P where` with fields `value _ := rfl`) as a `rfl` proof — 15 false negatives
(including the true rank 1 and 2 by statement length,
`NavierStokes/ActualParticularPotentialCoherence.lean:106` at 709 chars and
`ActualCurrentParticularPhysical.lean:112` at 639) and 3 false positives.

Fixed: `audits/scan_kernel_risk.py` now carries a bracket-depth-aware `split_decl` that splits at the
first **top-level** `:=` / standalone `by` / standalone `where`, and the scanner reports the defeq
workload as a first-class measurement (`bare_rfl_proof`, with `SITES_bare_rfl_proof.md`, plus
`stmt_chars`/`proof_kind`/`bare_rfl` columns in `INVENTORY.csv`). Re-derived independently after the
fix: **541 in-cone — exact agreement with the worker** — and 1,358 across the whole artifact.
`RFL_SITES.csv` regenerated; the count of recursion-touching statements rises 7 → 12 with the fix.

Its remaining escalations, all low: `PrimaryTargetBounds.lean:631` (both sides tactic-built structure
literals plus proof irrelevance), `CorrectionInitialization.lean:1012` (defeq across index types
`Unit` vs `ℕ`), `CylinderSobolevDerivatives.lean:77`, and two name-overclaims
(`CorrectionInitialization.lean:1193,1327` — `reconstructState` is definitionally idempotent for
*every* state, so the lemma says less than its name).

## W25 `ns-index-nonempty` — the wave tower IS inhabited; the gap is bookkeeping, not vacuity

Report: `workers/ns-index-nonempty.md` (+2 children: `_sub-index-headline`, `_sub-index-force-divfree`).
11 files / 1,246 declarations in scope, ~46 read line-by-line plus full greps; 30 declarations signed off:
**OK 30, 0 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS.** This closes E1/E2 of `ns-nondegeneracy` (W23).

The question was the last live vacuity worry in the NS half: the artifact case-splits on
`isEmpty_or_nonempty (Index B N0)` at four sites and **never proves its own wave-label set is
inhabited** — so were the wave estimates true only because there are no waves?

- **The literal claim is confirmed:** a full grep finds no `Nonempty (Index/Label/SignedLabel/
  ActiveLabel/CellIndex …)` conclusion anywhere; the five `[Nonempty Label]` occurrences
  (`ParticularCopyBounds.lean:453,480`, `ActualGaussianCoverage.lean:730,801,1251`) are all
  *hypotheses*. The existence lemmas that do exist (`physicalMask_active`
  `PrimaryRepresentatives.lean:159`, → `:542` → `PositiveRepresentatives.lean:61` →
  `physicalMask_has_index` `PrimaryGeometryAssembly.lean:198`) are **conditional**: each needs a point
  with `mask ≠ 0` handed in.
- **And the worry is refuted, from the artifact's own in-cone theorems, in five lines.**
  `partitionFactor_eq_one` (`ActualPrimaryCovariance.lean:508`, in-cone) says a `Finset.sum` over
  `unsignedLabels B N0 n : Finset (Label B N0)` **equals 1** at every native-strip point for
  `n ≥ (choice B N0).prepared.N + 1` (threshold from `physicalScale_tail`, `:527`; partition of unity
  from `PartitionedCovariance.physical_mask_tail_sum_sq`, `:766`). An empty label type forces that
  Finset to `∅` and the sum to `0`. The strip point is supplied *explicitly, with no choice and no
  hypothesis*, by `actual_strip_nonempty` (`ActualSignedMeanBinding.lean:54-67`, witness
  `((a+b)/2, ((1,0),(0,0)))`), and `ActualInitialization.lean:665` is a `rfl` bridging its set to the
  one `partitionFactor_eq_one` quantifies over. So `0 = 1` — hence `Nonempty (ActualPrimary.Label B N0)`,
  hence all four split sites' empty branches are **dead code that is nevertheless shipped in-cone**
  (`covariance_bounds_of_curl`, `ActualInitialMean.lean:309`, is `in_cone = True`).
  The worker checked its own argument for circularity and it is not: `partitionFactor_eq_tail`
  (`:464-506`) goes through the *unrestricted* `finsum` over the full label type, whose emptiness is
  not at issue, and that is where `physicalMask_has_index` is consumed (`:484-495`) — the artifact
  already proves "nonzero mask ⇒ active label" and simply never runs it backwards.
  **Status: HIGH-CONFIDENCE, UNBUILT** (no Mathlib on the box), and it is the audit's cheapest
  remaining check — five lines and a `lake build`.
- **Belt and braces, from the `index-headline` child: the headline does not need it anyway.** All 12
  `CandidateProperties` fields are discharged without an inhabitant; `navier_stokes` is *definitional*
  (the force **is** the traced residual, `CandidateFromLimits.lean:82` vs `:181-182`); and
  `speed_unbounded` rests on one index-free positive constant, `W.axis.small.j_pos`
  (`NaturalAxisData.lean:41-45`) via `FinalSlowBase.axis_tendsto:372` and
  `BaseResidual.baseVelocity_axis_tendsto_atTop:104`. The loudest fact is the artifact's own theorem
  that the **entire correction tower is identically zero on a neighbourhood of every axis point**
  (`AxisZeroOn`, `GermCandidateAssembly.lean:24`; `positivePotential_axisZeroOn`,
  `ActualCandidateAssembly.lean:680-686`; `axis_not_active`, `:642-647`) — i.e. exactly where the
  blow-up is measured. No `Nonempty` obligation propagates up to `witness`/`selected_witness`/
  `theorem_1_1`.
  *I record one disagreement with that child:* it calls the tower "decoration". Accurate for the
  **blow-up**; wrong for the **smoothness of the force**, which is what the tower's residual ladder
  buys (W12, W16). Its own §5 says so, and the parent's E4 keeps it.
- **The `index-force-divfree` child:** both remaining clauses are wave-independent. Force compact
  support is *imposed* by two multiplicative cutoffs (`R3/PositiveTimeForce.lean:46`,
  `R3CompactCandidate.lean:88`, wired at `R3/ActualCandidate.lean:88-89,109-110`) and divergence-freeness
  is structural (`div (curl …) = 0`, `SpatialLocalization.lean:258-262`, plus a termwise
  `Finset.sum_eq_zero`, `DirectAngularDiagonal.lean:291-313`). Its blunt summary, which the parent
  endorses: **`f ≡ 0` satisfies both clauses verbatim**, so neither can detect an empty tower. Force
  non-triviality is never assumed — it is *derived* from `speed_unbounded`
  (`MaximalLifespan.lean:275-290`, `R3/CandidateBreakdown.lean:53-62`).
- **Kernel risk in these 11 files: zero.** No `inductive`, no `.rec`/`Acc.rec`, no `termination_by`,
  no `deriving`, no metaprogramming. The label types are `Subtype`/`Prod`/`Fin 2` chains, and
  `Countable (Index W N)` is obtained by *delta-unfolding to `Subtype`* and `infer_instance`
  (`PrimaryGeometryAssembly.lean:141-144`) — no recursor reduction is asked of the kernel.
  Vector (2) is two occurrences of `zero_pow (by decide : (2:ℕ) ≠ 0)`
  (`ActualPrimaryCovariance.lean:330`, `ActualSignedMeanBinding.lean:295`); the `^ 2` exponents are
  `Monoid.npow` over `ℝ`, never integer arithmetic. The real non-kernel risk in scope is
  `Classical.choice`: `(choice B N0).prepared.N` is choice-selected
  (`CorrectionInitialization.lean:3929`), which is *why* no explicit label witness can be written —
  the innocent explanation of the whole gap. Note the author does prove `Nonempty` when a
  `Classical.choice` forces it (`choice_nonempty`, `:3920-3927`).

**Net effect on the ledger:** W23's E1/E2 downgrade from SUSPICIOUS to **OK (unrecorded)**. New E4
(rank 3, structural): the residual-decay ladder (`MixedCandidateAssembly.lean:29-65` →
`ActualCandidateAssembly.lean:1090-1098,1152` → `ActualCycleResidualBounds.lean:1158-1172,1190-1206`)
is index-*uniform* and never case-splits on emptiness, so it is the one place where an empty tower
would have had to be checked rather than shrugged at — moot for soundness given the above.

---

## P1 — three more corrections to our own instrument (found by workers, verified by the parent)

The census has now been wrong six times, and the pattern is always the same: a regex that reports a
*count* gets read as if it reported a *surface*.

- **`choose_fact` was blind and polluted at once.** `ns-variable-gauge-mean` noticed
  `SITES_choose_fact.md` says **6** sites while `INVENTORY.csv`'s `choose_fact` column says **534**;
  `kernel-choose-pow` diagnosed both halves. The marker regex
  `\bNat\.(?:choose|factorial|ascFactorial|descFactorial)\b` cannot see **dot notation**, and
  `j.factorial` is how the artifact actually writes it — 892 factorial terms, of which the marker saw
  6. The *feature* column's extra alternative `\bchoose\b` then counted `Classical.choose`,
  `h.choose_spec` and the `choose` **tactic**. So one number was simultaneously 150× too low and
  polluted by three unrelated things.
  **Fixed:** the marker now matches dot notation (**6 → 881 sites in 194 files**), and the feature
  column is split into three — `nat_choose`, `factorial`, and `dot_choose`, the last named ambiguous
  on purpose because `n.choose k` (Nat) and `h.choose` (Classical) are the same token and only a
  reader can separate them. Worker's manual split of the old 534: 368 `X.choose` applications,
  100 `choose` *tactic*, 56 `Classical.choose`, 6 `Nat.factorial`, 4 other.
- **`bare_rfl_proof` measured the easy half of the defeq surface.** `ns-transition-ramp` reported
  that the census sees **1 of 19** proof-closing `rfl`s in `TransitionRamp.lean`. That is not a bug in
  `_BARE_RFL` — it correctly matches "the whole proof is `rfl`" — it is a **scope** error in how W24's
  bound was then read. The distinction matters more than the count:
  *a bare `rfl`'s statement displays exactly what the kernel must decide, so a statement-level screen
  can bound its iota depth. A `rfl` closing a tactic block faces a goal `simp`/`rw`/`unfold` already
  rewrote, which is **not in the source**, so no statement-level screen bounds it at all.*
  **Fixed:** new `closing_rfl` measurement and `SITES_closing_rfl.md`. Repo-wide it is
  **1,523 further theorems** (parent-measured **1,176 of them in-cone**) on top of the 1,358 bare ones
  (541 in-cone). So the in-cone defeq surface is **1,717 theorems, not 541**, and W24's bound —
  ≤ 19 iota steps, zero chains — is proved for **541 of them**. That is still the strongest bound in
  the pass, and it now has an honest denominator. Reopened as open thread 5.
- **`in_cone` counts in my briefs were theorem-only.** `ns-variable-gauge-mean` and
  `ns-transition-ramp` both flagged it: my "138 in-cone declarations" for `VariableGaugeMean.lean` is
  138 in-cone *theorems* (169 in-cone declarations: 138 theorem + 30 def + 1 structure); same for
  `TransitionRamp` 127/168 and `OutgoingHistories` 114/209. Harmless but it made two workers
  reconcile a number that never disagreed.

---

## W26 `cert-numerals` — the published 61-bit sentence is right in its label, wrong in its number, and too strong in its reason

Report: `workers/cert-numerals.md` (+3 children). **OK 13, NOTE 2, REFUTED 2, ESCALATE 3,
KERNEL-RISK 0.** This is the first thread in the pass that is **not** source-level: the worker found a
**built Mathlib** on the box (`lean-eval-house-with-two-rooms/.lake/packages/mathlib`, Lean 4.33.0),
re-elaborated faithful ports of 14 artifact sites plus 2 adversarial controls, and **counted the `Nat`
literals in the proof terms `linarith`/`nlinarith`/`norm_num` actually emitted**
(`#litcensus`, an `Expr`-walking `elab`; `/tmp/certprobe/Probe{2,4,5,6}.lean`).

**The parent re-ran Probe2 and Probe6 independently and reproduces every number below.**

- The published report says the largest closed `Nat` the kernel evaluates anywhere is
  **≈5.0×10¹⁷ — 61 bits**, at an `nlinarith` certificate in `NavierStokes/PulseCone.lean:1017`.
  The **site is right**; the **number is not**. The emitted term's widest literal is
  **2,000,979,990,000,000,000 = 2.0×10¹⁸ = 61 bits** (`= 200097999 × 10¹⁰`).
  `500,224,987,900,197,999` *is* in the term — it is the product `200097999 × 2499900001` a previous
  worker computed by hand — but it is **59** bits and it is not the maximum. So the published sentence
  pairs a 59-bit number with a 61-bit label. Measured census (parent-reproduced):
  `max=2000979990000000000 bits=61 over64=0`.
- **My own rank-1 lead was wrong, and the worker refuted it with a measurement.** I had put
  `NavierStokes/MatchingConeBounds.lean:31` `shape_axis_lower` above the PulseCone site on a
  lcm-of-denominators proxy (37.9 vs 33.2 proxy bits) and warned that a degree-2 `nlinarith` product
  there would reach 87 bits. Measured: **4,501,000 — 23 bits** (parent-reproduced:
  `max=4501000 bits=23`), because the step that carries `4501/500000` is proved by `linarith` at
  `:53` and then used **linearly**, and the final step at `:80` is **degree-1 `linarith`** whose own
  census is 1,000,000 (20 bits). *My proxy ranked the source; the kernel checks the certificate, and
  the certificate's degree is what sets the width.* Lesson for the instrument, not the artifact.
- **The mechanism, named from Mathlib source, is the real result.** `defaultPreprocessors` ends with
  `cancelDenoms` (`Mathlib/Tactic/Linarith/Preprocessing.lean:384-386`), and `nlinarithExtras` runs
  **after** it (`:326-333`), forming all pairwise products via `mapDiagM` (`:303-317`) on comparisons
  whose denominators are **already cleared**. So a degree-2 product's coefficients are products of the
  *cleared integers* — the width-doubling step. The oracle returns natural-number multipliers
  (`Verification.lean:216`) and the leaf is closed by the default discharger `ring1`
  (`Frontend.lean:159`, used at `Verification.lean:246`). Hence the rule:
  **degree-1 ⇒ lcm × numerators; degree-2 ⇒ that squared.** Also: `linarith`'s default
  `transparency := .reducible` (`Frontend.lean:168`) means a plain `def` such as `decay`
  (`PulseLag.lean:165`) is *not* unfolded, so `decay d.core ^ 2` is one monomial — which is why the
  atom count stays small.
- **And therefore the published *reason* is too strong.** "Never multi-limb" is not a property of the
  artifact's numerals; it is a property of the certificate the simplex happened to pick. The worker
  proved this with a control on the artifact's **own** literals: `ADV_pulse_deg2`, a degree-2
  `nlinarith` route through `sq_nonneg (x^2 - (49999/100000)^2)`, emits **10²⁰ = 67 bits and 541
  literals above 2⁶⁴**. So the correct claim is a **degree-1-certificate fact**, not a
  small-literal fact — and it is contingent on Mathlib's oracle continuing to find degree-1
  certificates for these goals.
- **Headroom, which nobody had stated.** Lean's `Nat` is a tagged scalar below **2⁶³ = 9.223×10¹⁸**
  and an mpz above it. The artifact's measured maximum is 2.0×10¹⁸, so the margin to the multi-limb
  path is a factor of **4.6** — one degree-2 certificate away, not orders of magnitude away.
- Runners-up, all measured: `Euler/PacketNeighborControlled.lean:221` and
  `PacketGeometryGuards.lean:99` at 10¹⁵ (50 bits); `AxisProfile.lean:92` and `AxisModelBounds.lean:24`
  at 1,327,104,000,000 = 1152000² (41 bits); `PulseCone.lean:1031` at 20,010,000,000,000 (45 bits).
  Only **13 declarations in the whole artifact** combine an lcm of denominators ≥ 10⁵ with any
  square or `nlinarith`, and 9 of them are in `PulseCone.lean`.

**Replacement sentence for the published report** (mine, from the worker's measurement):
*The widest closed `Nat` the kernel is asked to evaluate is `2.0×10¹⁸` (61 bits) — the `nlinarith`
certificate of `NavierStokes/PulseCone.lean:1017`, measured in the emitted proof term, not estimated
from source. That is inside Lean's single-word `Nat` path (< 2⁶³) with a factor-4.6 margin, and the
artifact reaches multi-limb GMP nowhere. But that is a fact about the **degree** of the certificates
Mathlib's oracle found, not about the size of the artifact's constants: a degree-2 route through the
same literals emits 10²⁰ and 541 literals above 2⁶⁴.*

---

## W27 `kernel-choose-pow` — `9^729` is inert (parent-reproduced), and the published `C(0,0)` does not exist

Report: `workers/kernel-choose-pow.md`. **OK 6, NOTE 1, REFUTED 4, ESCALATE 3, KERNEL-RISK 0.**

- **`9^729` confirmed inert, and by a stronger mechanism than we claimed.**
  `Euler/ConstantCorrectionData.lean:146` is verbatim `def pressureBound : ℝ := 9^729`
  (parent-verified), consumed at `:149` by `one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)` — the `norm_num`
  goal is `1 ≤ 9`, not the power. Its only other unfold is `:165`
  `simpa only [mul_one, pressureBound]`, a syntactic match against `(9*L)^729` at `L := 1`.
  **Parent-reproduced by elaboration** (Probe6): `positivity`, `one_le_pow₀` and `norm_num` routes all
  census at `max=729 bits=10 over64=0` — the exponent literal itself is the widest thing in the term.
  Better still, `norm_num` *refuses*: asked for `(2:ℝ)^40 ≤ 9^729` it expands `2^40 = 1099511627776`
  and reports `unsolved goals` rather than expanding `9^729`. So the 2,311-bit numeral is unreachable
  by the tactics the artifact uses **and** by the obvious one it does not.
- **REFUTED, a published claim:** the report says "the only closed values are `0!`, `C(0,0)`, and
  `4! = 24`". There is **no `C(0,0)` anywhere** — parent-verified, `grep -E 'choose 0 0|Nat\.choose
  [0-9]+ [0-9]+'` over all 2,659 files returns **nothing**. Of **368** `Nat.choose` applications,
  **zero** have a closed numeral in either slot.
- **`4! = 24` confirmed as the sole kernel-forced factorial**, and the mechanism is visible:
  `Euler/EulerProof.lean:12153-12154` does `have h := factorial_decay 4 z hz0.le` then
  `norm_num only [Nat.factorial, Nat.cast_ofNat] at h` — that `norm_num only [Nat.factorial]` is
  exactly the instruction to unfold it. 5 bits.
- **A value we had missed:** `fixedCost 6` = `2^6 * Σ_{j ≤ 6} (j!)²` = **34,138,752** (26 bits),
  defined at `Euler/SobolevSourceExponent.lean:14` (parent-verified verbatim:
  `def fixedCost (q : ℕ) : ℝ := (2 : ℝ)^q*∑ j ∈ range (q+1), (j.factorial : ℝ)^2`) and used at
  `Euler/PacketUniversalFrequency.lean:24` as the structure field `derivative_bound : fixedCost 6 ≤ k`.
  It is a `Finset.sum` over **ℝ** and is never normalised — it is filtered on by
  `eventually_ge_atTop`, so `k` is chosen above it rather than it being computed. OK, but it is a
  closed factorial expression the census did not report, which is why the `choose_fact` fix above
  matters.
- Of **711** sites with an exponent literal ≥ 8, only **3** have closed bases, and
  `Euler/PacketSourceScaleActual.lean:33`'s `0^60` is a **parse artifact**. `Θ^40`, `k^80`, `6^m`
  all have symbolic bases — a `Monoid.npow` over ℝ with a ℕ literal exponent is not integer
  arithmetic and the kernel never computes it. Widest closed integer the kernel reduces in this
  thread's scope: **1,146,880** (21 bits), from `ring` on `1120*(2*Cθ)^10`.
  Jet/Taylor files (`AxisWeightEstimates`, `JetBounds`, `EdgeWeightJets`, `FiveProfileMoments`):
  **zero** closed orders, so no `m!` is ever at a literal `m`.

---

## W28 `ns-transition-ramp` — the ramp is honestly glued, and it is NOT the file I said it was

Report: `workers/ns-transition-ramp.md`. **OK 46, NOTE 2, REFUTED 1, ESCALATE 3, KERNEL-RISK 0.**
All 2,253 + 1,278 lines read. Queue ranks 1 and 2 of `COVERAGE.md` — first reader in the pass.

- **REFUTED, my brief:** I called `OutgoingHistories.lean` "the ramp's likely consumer side". It is
  not related to `TransitionRamp.lean` at all — **zero** cross-references either way
  (parent-verified: `grep -c` gives 0 and 0), disjoint imports (parent-verified:
  `TransitionRamp` imports `ActivationStocks` + `ReferenceJetBounds`; `OutgoingHistories` imports
  `CorrectedPulseAmplitude` + `SchedulePressure` + `ProfileHistories`), and the only shared ancestor
  is `OutgoingSchedule`. A brief that invents a dependency makes a worker audit a relationship that
  is not there; recorded for the same reason as the `euler-cauchy` correction.
- **The piecewise definition is real but the junction is interior, so no one-sided matching is
  needed.** `TransitionRamp.lean:702` is `if p.1 ≤ R.radius0`, and `:959` `physicalF_eq_log` proves
  **both branches agree on all `0 < p.1`** — so `:999` `physicalF_smooth` is two
  `congr_of_eventuallyEq` applications on two **open** sets that cover the domain. That is the
  honest construction, not an assertion that one-sided derivatives match. Same shape at `:1024`.
- **`C^∞` is earned by the standard flat-cutoff route, uniformly in `k`.**
  `σ = edge/(edge+edge)` (`OutgoingSchedule.lean:26-27`) with
  `edge = if x ≤ 0 then 0 else exp(-c/x^2)` (`FlatCutoff.lean:26-27`), smooth by **induction on the
  inverse-polynomial family** (`FlatCutoff.lean:118-128`), and the smoothness statement is uniform
  (`OutgoingSchedule.lean:37`) — **no per-`k` constant**, which is the failure mode I asked it to hunt.
  The side condition `δ ≤ bigTime` is **proved** (`ActivationContinuation.lean:1699-1704`), not assumed.
- **The narrow-interval worry is real and the artifact does not widen it.** `:1281` `log_value` holds
  only on `Icc 0 (bigTime+w1+w2)` while its siblings `:1277`/`:1279` hold on `Icc 0 finalTime`
  (strictly larger, `:1276`). The consumer never uses it outside its interval: `:1852` switches to a
  one-sided `normalizedLog ≤ B+1` via `hold` (`:1826`) and `sub_le_self` (`:1883`), and the consumer
  at `:1784` needs only the upper side. **OK.**
- Kernel risk: largest numeral **1000** (`:747`); recursion is **one structural `Nat` def**
  (`parameterJet`, `:327`); no `inductive`/`.rec`/`termination_by`/`decide`. UNBUILT.

---

## W29 `ns-variable-gauge-mean` — clean, and it refuted two premises of its own brief

Report: `workers/ns-variable-gauge-mean.md`. **OK 17, NOTE 4, REFUTED 2, ESCALATE 4, KERNEL-RISK 0.**
110 of 190 declarations read line-by-line, 25 partial, 55 grep-only (2,088 of 3,004 lines); 41 cited
`file:line`s re-verified by the worker.

- **REFUTED: this is not "estimate mass".** I dispatched it as a long-`nlinarith` estimate file. It
  contains **17 `nlinarith` lines total**, each a one-line `lt_div_iff₀` juggle (e.g. `:1320`), and
  10 `calc` blocks of at most 4 steps. The mass is **fiber localisation and germ rewriting**. My
  classification of the NS remainder as uniformly estimate-shaped is wrong for at least this file,
  which matters because it is how the work queue is prioritised.
- **REFUTED: the limit-interchange hunt was vacuous here** — **zero** occurrences of
  `Tendsto`/`atTop`/`iSup`/`limUnder` in 3,004 lines. There is no limit to interchange.
- **The quantifier order is right, and it is the good pattern.** `:1288` `let K := leftK+rightK+midK`,
  `:1297` `refine ⟨K, hKK, ?_⟩`, `:1298` `intro U hU ell … A B … z … j` — `K` is fixed **before**
  `ell`, `M`, `v`, `f`, `A`, `B`, `z`, `j`. And the ambient class is honestly `m`-only:
  `WeightedClasses.lean:111` `bounds : ∀ m, ∃ C, 0 ≤ C ∧ ∃ p, ∀ n x`.
- **The leaf hypothesis HAS a supplier here** — the shape `jetrate-callsites` found unsupplied
  elsewhere does not recur: `hell` is discharged by `CorrectionInitialization.lean:3960`
  `gauge.length n = VariableGaugeMean.qLength (2*h) := rfl`, and the coordinate `2h` is forced by
  `ActualSignedGeometry.lean:31` `SlowRegion (2*h)` with `h < 1/2`.
- Largest closed numeral in scope: **5** (`:2471` `hclass.bounds (m+5)`, matching
  `UniformFourierAlias.lean:614` `j ≤ m+5`). No `inductive`/`.rec`/`termination_by`/`decide`/`Nat.pow`.
  The only exotic defeq in the file: `:624` `subst; rfl` needs **`Prop` proof irrelevance** — the
  fourth witness for A3's kernel feature after `rfl-defeq`'s single `Prod` eta site.

---

## Open threads after this cycle

1. ~~The defeq workload~~ — **reopened as thread 5**: W24's ≤19-iota bound covers 541 of the
   **1,717** in-cone theorems whose proof involves a `rfl`; the other 1,176 close a tactic block and
   their goals are not in the source.
2. **The degree of the certificates.** W26 makes "never multi-limb" contingent on Mathlib's oracle
   finding degree-1 certificates, with 4.6× headroom. An expert question: is that a property anyone
   should rely on across Mathlib versions?
3. **Coverage.** 11,511 of 27,753 in-cone theorems live in a file some report has read or cited
   (41.5%, a generous upper bound). Queue in `COVERAGE.md`, ranks 1-2 now closed by W28.
4. **The five-line `index_nonempty` build** (W25 E1) — still the cheapest open check in the pass, and
   **still NOT runnable here. I overclaimed this and am correcting it in the same cycle.** On seeing
   W26 elaborate Lean successfully I wrote that the check was "now clearly buildable". It is not, for
   two measured reasons:
   * The artifact has **0 built `.olean` files** (`find NSE/.lake -name '*.olean'` → 0). `index_nonempty`
     cites the artifact's *own* declarations (`ActualPrimaryCovariance.partitionFactor_eq_one`,
     `ActualSignedMeanBinding.actual_strip_nonempty`), so it needs NSE's 641,332 lines compiled first.
   * The toolchains differ. NSE pins `leanprover/lean4:v4.34.0-rc2` with mathlib `85e3a25e006c`
     (`lean-toolchain`, `lake-manifest.json`); the built Mathlib on this box is **v4.33.0**.
   **The distinction this exposes is worth more than the correction.** W26 could measure real Lean
   behaviour without the artifact because its probes were **faithful ports** — self-contained
   restatements over Mathlib alone. Measuring what a *tactic* emits is portable across a minor Lean
   version. Checking a *theorem about the artifact's own definitions* is not. So the elaboration
   instrument W26 built generalises to every tactic-behaviour question in this audit (including open
   thread 5, the 1,176 unbounded `rfl`s, if their goals can be reconstructed as ports) and to **none**
   of the artifact-specific ones. What would settle item 4 is unchanged from W25: a full
   `lake build` of NSE at its pinned toolchain.
   **RE-PRICED by W31 (and the name "five-line" retired).** The figure conflated two jobs:
   proving `Nonempty (ActualPrimary.Label B N0)` as a *standalone* theorem is indeed ~5 lines inside
   `ActualSignedMeanBinding.lean` (all citations in scope there, as the file already does at `:463-472`),
   but *deleting the empty branches* needs the lemma re-homed low in the import DAG in
   `ActualPrimaryCovariance` with its own strip witness — **~20 lines + 1 import** — because
   `actual_strip_nonempty` (`ActualSignedMeanBinding.lean:54`) is import-unreachable from the split sites
   and `ActualSignedStageControls` does not import `ActualPrimaryCovariance` at all.
   **And there are SIX split sites, not four** (`ActualParticularStageControls.lean:941,1214` use
   `by_cases Nonempty (ActivePair B N0)`, which our `isEmpty_or_nonempty` grep could not see).
   **Priority drops.** W31 established that emptiness would make *non-split in-cone* theorems FALSE
   (`ActualPrimaryCovariance.lean:508` → `0 = 1`; `ActualSignedMeanBinding.lean:463-472`), so
   non-emptiness is already *entailed* by proved in-cone theorems. This item is now **documentation-grade
   tidying, not a soundness risk**.

## W30 `ns-harmonic-residual` — the `hres` shape recurs: a strong `ExtractionRegular` nobody constructs

Report: `workers/ns-harmonic-residual.md` (child of `ns-variable-gauge-mean`, whose parent then
re-verified and *enlarged* the finding). **OK 54, NOTE 4, UNCLEAR 1, ESCALATE 2, KERNEL-RISK 0**,
173 of 173 declarations.

`jetrate-callsites` (W8) found one cluster resting on a hypothesis `hres` that **nobody in the
repository proves**. This is the second instance of exactly that shape, and it is bigger:

- `NavierStokes/HarmonicResidual.lean:1461` `structure ExtractionRegular` demands **global**
  separation — `:1472-1473` `Disjoint (tsupport ((blockFamily l).oscillation n)) (tsupport …)`, with
  no localising set. **Parent-verified by exhaustive grep: every single occurrence of
  `HarmonicResidual.ExtractionRegular` is a hypothesis binder.** The one conclusion-position use,
  `AxisymmetricResidualGrouping.lean:142`, already assumes one at `:140`. There is **no constructor
  anywhere in 2,659 files.**
- Its **weaker same-named twin** `LocalResidualGrouping.lean:210` asks only
  `Disjoint (liftDomain U ∩ tsupport …) (…)` (`:220-222`) — and **is** produced:
  `ActualInitialization.lean:849` `initial_extraction_regular` (parent-verified), consumed at
  `ActualCycleResidualBounds.lean:269,311,702`. So the **live** chain runs on the local version.
- The child said the strong one had 3 in-file consumers; the parent found **21 hypothesis sites in 5
  other files**: `AxisymmetricResidualGrouping.lean:140,167,196,218,238,266`;
  `CorrectionStep.lean:1410,1424,1520,1533,3122,9250,9258`;
  `PhysicalResidualJetBounds.lean:129,694`; `HarmonicWaveInteraction.lean:1123,1124`;
  `HarmonicMeanInteraction.lean:619,620`.
- **Verdict: SAFE, and a cone false positive.** A weaker hypothesis makes a *stronger* theorem, so
  nothing is overclaimed; `CorrectionStep.lean:9250,9258` sit directly beside `:9268,9276`, which is
  what an **incomplete migration** from the global predicate to the local one looks like. But
  `in_cone = True` on that whole cluster is **wrong**: those theorems cannot be reached, because their
  hypothesis cannot be supplied. That is 21+ declarations the cone counts as live and are not — the
  same over-approximation direction the cone was designed to have, now with a named 21-site witness.
- Kernel risk nil; largest numeral **3** (`Fin 3`); the only integer arithmetic in 1,620 lines is
  `:1567` `2^stage + 2^stage = 2^(stage+1) := by omega`.

**Pattern worth naming, since it is now 2 for 2 in the files we look at closely:** this artifact
contains predicate clusters whose hypothesis has no supplier, sitting next to a weaker twin that
does. Both times the direction was safe. Both times the *cone* was fooled. A third instance would
make "count the declarations whose hypotheses have no constructor" a cheap and worthwhile pass in its
own right — and it is mechanisable: for every `structure`/`def` used only in hypothesis position,
check whether any declaration has it in conclusion position without also assuming it.

---

## W31 `ns-index-nonempty` (re-audit) — non-emptiness is **entailed in-cone**; the ledger's cost and site count were both wrong

Three read-only workers (`_sub-index-rederive`, `_sub-index-vacuity`, `_sub-index-incone`) re-ran W25's
argument against the artifact @ `f9e8bc5` with instructions to disagree. Every claim below is
**parent-verified at file:line**. The check does **not** close as buildable — the artifact still has
**0 `.olean` files** and pins `leanprover/lean4:v4.34.0-rc2` (box Mathlib is `v4.33.0`) — but its
*status* changes, and two of our own numbers were wrong.

**1. The whole question is one type, and the derivation closes all sites.** My suspected type-mismatch
hole (`partitionFactor` sums over `Label`, the headline splits on `Index`) is **not** a hole. All the
split types are reducible abbrevs of a single type:
`CorrectionInitialization.lean:3931` `ActualPrimary.Label B N0 := PrimaryGeometryAssembly.Index nominal
(choice B N0).prepared.N`; `ActualInitialMean.lean:25` `Index B N0 := ActualPrimary.Label B N0 × Fin 2`;
`ActualSignedStageControls.lean:35` `SignedLabel B N0 := ActualPrimary.Label B N0 × Fin 2`;
`ActualSignedUnmaskedBounds.lean:23` `Label B N0 := ActualSignedStageControls.SignedLabel B N0`.
`Fin 2` is inhabited, so transfer is `⟨(L, 0)⟩` and **one** `Nonempty (ActualPrimary.Label B N0)`
discharges every site.

**2. `0 = 1` is sound.** `partitionFactor` is a bare `Finset.sum` of `spatialMask ^ 2` over
`unsignedLabels` with **no division or normalisation** (`ActualPrimaryCovariance.lean:381-382`), so an
empty label type forces it to `0`. The `= 1` side (`:508-513`) takes only `hx` and `hq` — no hidden
`Nonempty` instance argument (the file's only `variable` is `{B N0}` at `:92`) — and its engine
(`PartitionedCovariance.lean:766`) is unconditional over `UnsignedLabel = ℕ × Grid`, so the `1` is not
itself vacuous. `n` is free: `physicalScale_tail` (`:527`) with `n := N+1` by `le_rfl`.
The strip bridge is **exact, nothing missing**: `ActualInitialization.lean:383-384` defines
`strip := BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion`, literally
the `hx` of `:509`.

**3. NEW (W31a) — the "five-line" cost conflated two different jobs.** `actual_strip_nonempty` lives in
`ActualSignedMeanBinding.lean:54`, which **imports** `ActualSignedStageControls` *and*
`ActualPrimaryCovariance` (`:1-6`), so it is **import-unreachable from the split sites**; and
`ActualSignedStageControls.lean:1-8` does not import `ActualPrimaryCovariance` at all, so
`partitionFactor_eq_one` is not even in scope there. Therefore:
  * **Proving `Nonempty` as a standalone theorem: 5 lines**, inside `ActualSignedMeanBinding.lean`,
    where all three citations are already in scope — exactly as the file itself does at `:463-472`.
    **W25's figure is correct for this job.**
  * **Making the split branches deletable: ~20 lines + 1 import**, with the lemma re-homed low in the
    DAG in `ActualPrimaryCovariance` (imports only `CorrectionInitialization` + `BaseStressClasses`,
    `:1-2`) and carrying **its own** strip witness. `ActualInitialMean` already imports that file
    (`:1-5`), so site 1 comes free.
  The ledger charged one price for two jobs. Corrected in open item 4.

**4. NEW (W31c) — there are SIX split sites, not four.** Our census grepped `isEmpty_or_nonempty` and
missed `by_cases`: `ActualParticularStageControls.lean:941` and `:1214` both do
`by_cases hne : Nonempty (ActivePair B N0)`. Both empty branches are proven (`:983-994`, `:1245-1248`).
In the non-empty branch inhabitance is used only to build a surjection `e : ℕ → ActivePair` via
`Classical.choose (exists_surjective_nat …)` — i.e. **inhabitance buys enumeration, never an estimate**.
That is census miss #7, same shape as the six in P1: a marker regex read as a surface.

**5. What is actually vacuous if the tower is empty.** Sharpen W25's "dead code":
  * `covariance_bounds_of_curl` (`ActualInitialMean.lean:309`, split `:318`) — **still true but empty**:
    the empty branch proves `activeLabels = ∅`, `(seed B N0).oscillation = 0`, then discharges both
    `MeanClass` goals for the zero field (`:319-338`). Its `errors.baseError` content survives.
  * `ActualSignedUnmaskedBounds.lean:161,196` and `ActualSignedStageControls.lean:1132` — **fully
    vacuous**: `UniformLocalJets` is a bare `∀ l`, closed by `isEmptyElim` with `C = 0, p = 0`.
  * **No split branch is FALSE.**

**6. The real conclusion: emptiness is REFUTED in-cone, not tolerated.** The load-bearing point, which
W25 understated. Emptiness would make **non-split, in-cone theorems false**:
`partitionFactor_eq_one` (`ActualPrimaryCovariance.lean:508`) becomes `0 = 1`, and
`requested_cross_tail` (`ActualSignedMeanBinding.lean:463-472`) would equate `0` with an arbitrary
`requestedStress` **for every `u`** — parent-read: its proof rewrites with `partitionFactor_eq_one` and
`physicalScale_tail`, and its `hx` is satisfiable from `:54`. So **non-emptiness is an implicit
consequence of theorems the artifact already proves in-cone.** It is not an open assumption. No in-cone
theorem *depends* on an inhabitant; several *entail* one.

**7. Census confirmations (and one worker overreach rejected).**
  * **CONFIRMED, exhaustive grep:** no declaration anywhere states
    `Nonempty (Label/Index/SignedLabel/ActiveLabel/CellIndex)`. The only inhabitance conclusion in the
    repo is `ActualParticularPhysicalData.lean:615` `Nonempty (SourceIndex N)` — a different,
    activity-free type, `in_cone = False`.
  * The record's **"five `[Nonempty Label]` occurrences" is exact** (`ParticularCopyBounds.lean:453,480`;
    `ActualGaussianCoverage.lean:730,801,1251`). W31c's "37, not 5" counts *all* `[Nonempty _]` binders
    across all type variables (13 on `ι`, 5 on `Label`, 6 on `Λ`, 1 on `ActivePair`, …). Both numbers are
    right about different questions; **the ledger was not wrong here.** All 37 are hypotheses.
  * In-cone `[Nonempty …]` hypotheses are discharged **only from a case hypothesis**
    (`ASUB:167,204`; `ASSC:1138`; `APSC:942,1215`) — never by proof.
  * **REJECTED — W31b's 2-line shortcut.** It claimed `physicalMask_has_index`
    (`PrimaryGeometryAssembly.lean:198-209`) already gives `∃ i : Index W N` outright. Parent-read: it
    carries **eight** hypotheses, including `hm : PartitionedCovariance.mask … ≠ 0`. The conclusion is
    real but **conditional**, and supplying a nonzero-mask point is the entire difficulty — which is
    precisely what the partition-of-unity reductio buys for free. **W25's "conditional" reading stands.**

**8. Headline independence re-confirmed.** No inhabitance obligation reaches the top:
`ActualCandidateAssembly.lean:1123-1158,1177` names no label type, the blow-up is label-free
(`FinalSlowBase.lean:372-379`, `NaturalAxisData.lean:44` `axis.j > 0`), and the correction tower is
identically zero near every axis point (`ActualCandidateAssembly.lean:643-648`).

**9. W25's E4 counter-witness DISSOLVES (W31c follow-up, parent-verified).** W25 raised the
residual-decay ladder as "the one place where an empty tower would have had to be checked rather than
shrugged at". It would not. `StageEstimates.finite_residual` (`MixedCandidateAssembly.lean:62-65`)
quantifies **only** `∀ J m` — there is no index quantifier to be uniform over — and its payload
`JetRate` is a pure **upper** bound, `∃ C, 0 ≤ C ∧ ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r`
(`DiagonalResidual.lean:33-34`), which `C = 0` satisfies outright for the zero field. The gain is
label-free arithmetic (`ActualIterationLedger.lean:29` `gain h j = h * j / 10`). So E4 is **not** an
index-uniform counter-witness and is **withdrawn**; consistent with
`ActualCycleResidualBounds.lean:1158,1190`.

**10. The headline, named.** `NavierStokes.Comparator.navier_stokes_breakdown_R3`
(`ComparatorSolution.lean:16-20`), spine → `ComparatorR3Theorem:43` → `R3/Theorem:46,26` →
`R3/ActualCandidate:143` → `ActualCandidateAssembly:1177` → witness `:1153` → estimates `:1090`. The
statement is **closed and label-free** (`∃ u₀ f, InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f
∧ ¬ ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p`), so no inhabitance obligation can reach it.
The only `Nonempty` facts on the spine concern *solution* types (`R3/ProblemStatement:125,153`) and the
**parameter record** `Choice` (`CorrectionInitialization.lean:3923`), which *defines* the label type at
`:3931` and never populates it.

**Ledger effect.** W25's E1 is **upgraded**: from "HIGH-CONFIDENCE, UNBUILT vacuity refutation" to
**non-emptiness is entailed by proved in-cone theorems; the four (now six) empty branches are
unreachable code**. The residual is documentation-grade, not soundness-grade: 0 declarations assert
inhabitance, and the reductio only bites for `n ≥ N+1`. Open item 4 is **re-priced, not closed** — it
still needs a `lake build` at the pinned toolchain, which this box cannot do.

---

## W32 — the "hypothesis with no supplier" pass is MECHANISED, and it found the bug in itself first

New instrument: `audits/nosupplier.py`. Motivation was the pattern named at the end of W30: this
artifact contains predicate clusters whose hypothesis has no supplier, it happened twice, it fooled the
cone twice, and finding it cost a worker each time. It is now one command. Four subagents
(`openrouter/openai/gpt-5.6-luna`) verified the top candidates by reading; each was given a **planted
control** (`LocalResidualGrouping.ExtractionRegular`, known supplied) and **both that answered passed it**.

**The instrument was validated against known ground truth BEFORE any number was quoted, and failed
twice on the way.** Both failures are recorded because both are the audit's signature error:

1. **Bare-suffix masking.** `cone.py` resolves a token to every contiguous run of its components,
   which over-approximates — correct for reachability. Here that direction is *fatal*: the fully
   qualified supplier at `ActualInitialization.lean:849` also matched the bare suffix
   `ExtractionRegular`, so the strong twin looked supplied and **the one known-real finding vanished**.
   Resolving most-specifically (with `namespace`/`open` context to break ties) **added 23 candidates** —
   the naive version hid 21% of its own output.
2. **The declaration's own name was read as its own hypothesis.** `theorem SourceBounds.of_wave … :
   SourceBounds …` tokenised its header into the binder region, so the `conclusion − binders` rule
   discarded it. That silently hid **the single most idiomatic way a Lean structure is ever supplied**,
   the namespaced smart constructor `P.of_foo`/`P.mk`. Caught not by me but by worker
   `nosupplier-1`, which found `PhysicalClassBounds.SourceBounds` supplied at `:251-262` and `:264-273`
   while my script called it unsupplied. Fixed by `strip_header`; the case is now a regression test.

**Measured output, after both fixes: 104 candidates from 976 Prop-valued structure/class/def
declarations.** A refinement the first run did not make: these are two different shapes, and only the
first is the W30 defect.
  * **PREDICATE** (declared `: Prop`) — a proposition nobody ever proves. **70 candidates, 48 of them
    in-cone, 390 hypothesis sites.**
  * **BUNDLE** (a data record: `MeanData` carries `firstBand : ℕ`, `region : Set …`) — 34 candidates,
    26 in-cone. Stating lemmas over an abstract bundle and instantiating it once is **normal practice**,
    so a BUNDLE hit is only interesting if the headline chain needs an instance and none exists.
    Reporting all 104 as one number would repeat the count-for-surface error.

**Verified by reading: 17 of the top in-cone candidates → 12 CONFIRMED UNSUPPLIED, 5 false positives.
Precision 71% at the top**, and the honest reason is that 4 of the 5 misses are routes this instrument
*cannot* see without elaboration (anonymous constructor against an expected type; a field of a parent
structure that is itself constructed). The 5th was the header bug and is now fixed.
The four extra false positives are worth naming, because they are what the instrument will always miss:
`ParticularWaveAssembly.BandCharts` (route 2, `ActualReferenceRebase.lean:246-250`),
`SignedMeanGain.MovingField` (route 4, `MeanStateRegularity.lean:454-470`),
`MovingMomentBounds.Support` (route 4, `:337-350`), and `NavierStokesR3.PressureRecovery.Hypotheses`
(route 2, parent-verified: `R3/PressureRecovery.lean:436` builds it with
`let H : Hypotheses T u v p q := ⟨hT, hu, hv, hp, hq, hdivu, hdivv, hNS, heu, hev⟩` — a *bundling*
convenience, so its consumers are reachable exactly when those ten components are).
Two reliability signals from the cheap workers, both unprompted: one distinguished
`PhysicalWaveSum.RegularFamily` from the twin `PhysicalCopyBounds.RegularFamily` supplied at
`PhysicalCopyBounds.lean:586` (the masking trap, caught in the right direction), and one rejected
`AngularPeriodic.direction/.mul/.add/total_periodic` as suppliers because each takes an `AngularPeriodic`
hypothesis.

**The 12 confirmed, carrying 271 in-cone hypothesis sites** (worker file:line detail in
`workers/_sub-nosupplier-{1,2,3}.md`). Beyond the eight tabulated below, `nosupplier-2b` confirmed
`CorrectionStep.ParticularParameters.NativeDynamics` (`:6124`, 23 sites — so **both** `NativeDynamics`
twins are unsupplied), `GaussianTailFlat.FlatEdges` (`:446`, 28), `PhysicalWaveSum.RegularFamily`
(`:745`, 19) and `MeanResidual.AngularPeriodic` (`:56`, 16):

| predicate | declared | sites | note |
|---|---|---|---|
| `PhysicalStageBounds.MeanData` | `:154` | 49 | BUNDLE; support/init branch looks dead against its live `MeanInput` twin (`ActualPhysicalStageBounds.lean:30-67`) |
| `PhysicalParticularWave.ReferenceODE` | `:810` | 27 | 31 occurrences examined, all binders |
| `CorrectionStep.PeriodizedSignedParameters.NativeDynamics` | `:6000` | 23 | twin at `:6124`; neither supplied |
| `HarmonicResidual.ExtractionRegular` | `:1461` | 22 | **the W30 finding, reproduced mechanically** |
| `ValidBandGluing.Compatible` | `:22` | 19 | `ValidDyadicBandCover.lean:73` is a wrapper RHS, not a proof |
| `PeriodicIntegration.UnitPeriods` | `:40` | 17 | conditional energy chain `PeriodicUniqueness.lean:414-447` |
| `DefectIncrementBounds.ShellTriple` | `:109` | 15 | `.updated` (`:115`) concludes `P` from **two** `P` binders — supplies nothing |
| `PhysicalResidualNaturality.BandCoherence` | `:678` | 13 | worker found **4** using files where the nomination said 3 |

**Verdict, and it is the same direction as W30, at scale.** None of this makes a theorem false — an
unsatisfiable hypothesis yields an unreachable theorem, never a wrong one. What it does is falsify
`in_cone = True` on a large block: W30's witness was 21 sites, and there are now **12 confirmed
predicates totalling 271 in-cone sites**, with 48 in-cone PREDICATE candidates (390 sites) nominated
and mostly unread. The pattern named at the end of W30 is confirmed as **systemic, not anecdotal**.

**One shape this instrument cannot see, stated so its output is not mistaken for completeness.**
W8's `hres` (`GenericSupportedPolynomial.lean:130`) is `∀ J m, JetRate l q (fs J) m (rho J - Lres m)` —
a **supplied** predicate used at **arguments nobody establishes**. The script is correctly silent on it.
So there are two defects of this family and only the first is mechanised; the second needs a
per-callsite argument match, i.e. real elaboration.

---

## W33 — the unread remainder is NOT "all estimates": ~31% is structural, and my own triage was wrong twice

`audits/nse-deep/UNREAD_TRIAGE.csv`. First, a coverage correction. `COVERAGE.md`'s 41.5% was computed
over **65 worker reports**; at today's **78** the same definition gives **55.2%** (710 files, 15,310 of
27,753 in-cone theorems). Counting the synthesis documents too gives 81.7%, which is too generous to
quote. I also nearly published an 18% figure from a basename match that let `Solution.lean` match
inside `ComparatorSolution.lean`; boundary-fixing moved it by only 7 files, so that was *not* the
cause — the cause was the report-set definition. Both numbers are now stated with their denominators.

**The sharp target: 964 files that NO audit document has ever named, holding 5,067 in-cone theorems
(18.3%).** Mechanical classification, then hostile-tested by a worker with sampled error rates:

| class | files | in-cone thms | worker's sampled error rate |
|---|---|---|---|
| STRUCTURAL (declares a structure/class/inductive or Prop-def) | 73 | 843 | — (read directly) |
| ESTIMATE (estimate-signal ≥ 0.5) | 761 | 3,486 | **4 of 12 files misclassified** |
| PLUMBING (below that) | 130 | 738 | **5 of 8 are actually proof-spine/construction** |

**Answer to the question: no, it is not basically all estimate material. ~1,581 of 5,067 in-cone
theorems (~31%) are not estimates.** But the two error rates mean opposite things and the distinction
is the finding:
  * My **ESTIMATE** class is right where it matters. The 4 misclassified files
    (`ParentParticleRegularity`, `MeanPacketContract`, `PacketPhysicalCorrectionPotential`,
    `SmoothFlowJacobian`) hold **15 in-cone theorems between them** — 0.4% of that bucket's 3,486. By
    theorem mass the big bucket is ~99.6% correct.
  * My **PLUMBING** label was wrong in *character*, not at the margin. Those files contain real `def`
    constructions — parent-verified at `Euler/TransverseInitialCoordinates.lean:31-47`
    (`initialCoordinates`, `initialCoordinateField`, `initialCoordinateDerivative`, then theorems about
    them). Calling 738 in-cone theorems "plumbing" invited exactly the wrong triage. **Renamed
    CONSTRUCTION in the ledger.**

**Ranked read-first list** (worker's, with in-cone counts from `UNREAD_TRIAGE.csv`):
`ActualPhysicalPrefixFields:340-343,438-475` (34) · `ModulatedExterior:333-368,489-520` (24) ·
`ParametricModulation:304-316,577-608` (29) · `BasePrefixIdentity:217-224,278-311` (24) ·
`PeriodicPhaseAssembly:667-680,805-831` (25) · `IntegratedMeanBalances:638-645,674-740` (53) ·
`TransversePacketPrimaryPressure:118-151,172-200` · `SmoothFlowJacobian:25-27,37-38,82-118`.

**The two passes point at the same place.** The 73 untouched STRUCTURAL files are where new predicates
are declared, and unsupplied predicates are what W32 hunts — 5 of the 104 candidates are declared in
files no report has ever named. Reading the list above therefore buys coverage *and* feeds W32.

---

## W34 — two false-positive routes mechanised, and the instrument overturned a worker

Follow-up to W32, on the parent's own instrument. Verification of the first 17 candidates produced 5
false positives, and 4 were one of exactly **two shapes**, both now detected by `audits/nosupplier.py`:

* **route 4 — supplied parent.** `P` is a *field* of structure `S`, and `S` is constructed somewhere, so
  building `S` builds `P`. Mechanised by parsing `structure … where` field blocks and resolving each
  field type, then walking the field relation transitively to any supplied ancestor.
* **route 2 — in-proof type ascription.** `P` is built inside a proof under
  `have h : P … := by … exact ⟨…⟩`. Mechanised by scanning proof regions for
  `have`/`let`/`show`/`suffices` ascriptions.

**They are reported as HINTS and never remove a candidate.** Auto-excluding on them needs a wide text
window around the ascription, and a wide window starts calling things supplied that are not — which
*hides* findings, the one direction this instrument must not fail in.

**Measured on the known set: hints cover 4 of 4 remaining false positives, and 9 of the 11 confirmed
true findings carry no hint.** So of 104 candidates, **24 carry a hint and 80 do not**, and the 80 are
the higher-confidence set to read next. The hint is imprecise in a *known* way, and the two cases are
worth distinguishing because only reading separates them:
  * a **base construction** — `PressureRecovery.Hypotheses` is built at `R3/PressureRecovery.lean:436`
    by `let H : Hypotheses T u v p q := ⟨hT, hu, hv, hp, hq, hdivu, hdivv, hNS, heu, hev⟩` from ten
    separate binders. A real supplier.
  * mere **closure under an operation** — `have hp : UnitPeriods (fun x => f x * g x) := by … rw [hpf x k,
    hpg x k]` (`PeriodicIntegration.lean:185`) builds a `UnitPeriods` *only from two existing ones*.
    Supplies nothing, and the UNSUPPLIED verdict on `UnitPeriods` stands.

**The instrument then overturned one of its own verifiers, which is the point of building it.**
`nosupplier-2b` ruled `PhysicalWaveSum.RegularFamily` UNSUPPLIED, reasoning that
`PhysicalCopyBounds.regular_of_native` "concludes the distinct twin … not this predicate". The types
*are* distinct — and that is the trap. `PhysicalCopyBounds.lean:95-97` declares
`structure RegularFamily … copy : ∀ k, PhysicalWaveSum.RegularFamily (f.copy k) a b h r0 Z Δ`, so the
outer record **contains** the candidate as a field; and `regular_of_native` (`:568`, parent-read) proves
the outer one with `refine ⟨fun k => ⟨hgap_le, hgap_native, hamp k, hF k, hG k, hint k, ?_, hmask k⟩⟩`,
whose inner `⟨…⟩` *is* a `PhysicalWaveSum.RegularFamily`. **Reclassified SUPPLIED (route 4).**

Lesson worth naming, since it is the mirror of the twin-masking trap the workers were warned about:
**being right that two same-named predicates are distinct says nothing about whether one CONTAINS the
other.** Identity and containment are different questions, and route 4 is exactly the second one.

**Revised tally: 17 verified → 11 CONFIRMED UNSUPPLIED carrying 252 in-cone hypothesis sites, 6 false
positives. Precision 65%.** Every one of the 6 is now covered by a mechanised hint or a fixed bug, so
the next tranche should be read from the 80 hint-free candidates first.

---

### W34 addendum — first reading results, and a delegation failure worth recording

**Reading, first result.** `NavierStokes/CopyAngularInvariance.lean` (37 in-cone theorems, never
previously named by any audit document): **56 declarations read, OK 56, no NOTE/UNCLEAR/ESCALATE, zero
kernel risk.** Its two Prop-valued defs are direct translation predicates (`Invariant` `:23-24`,
`AffinePhase` `:26-27`), `TangentInvariant` is a five-field conjunction (`:201-206`) and — relevant to
W32 — it **is** constructed, by `angleTangent_invariant` (`:669-680`), consumed at
`ParticularWaveAssembly.lean:619-640`. No vacuity shortcut, no unsupplied hypothesis, no large
arithmetic, no recursor. First untouched structural file read: clean.

**One more candidate verified.** `ErrorHarmonics.GaussianData` (`:446`, 13 sites) — **UNSUPPLIED**, all
occurrences binders or fields. It is a BUNDLE and reads as a deliberately abstract primitive-data
interface consumed by the block/error definitions, which is the benign reading of an unsupplied bundle.

**Delegation failure, recorded because it cost a cycle.** Six concurrent OpenRouter children were
spawned; **four returned empty assistant turns and went to `needs_input` having done nothing** (32
session records, 0 text parts, `basedOnMessageCount: 2`). The earlier batch of four concurrent children
all succeeded. So the practical ceiling here is about **four concurrent children per provider**, and the
failure is silent — a child reports `completed` while having produced nothing. Two mitigations now in
use: cap concurrency at three, and spread across providers (`prime-inference/…` alongside
`openrouter/…`). The append-after-each-item protocol again limited the damage: the two children that
did run had their partial work on disk, which is why the two results above survive at all.
