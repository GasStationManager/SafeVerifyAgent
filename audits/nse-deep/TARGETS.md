# NSE deep audit — kernel-risk target inventory

Commit `f9e8bc5` (= the commit of the 2026-09-15 specification audit).
Census over comment-stripped source: **2,659 files / 641,332 lines / 52,516 declarations**
(38,503 `theorem`, 10,827 `def`, 1,578 `instance`, 899 `abbrev`, 667 `structure`,
28 `lemma`, **14 `inductive`**).

Threat model for this pass (given: comparator already ACCEPTed, so we are hunting
*kernel* trust, not elaborator agreement):

1. recursive inductive types (kernel recursor/reduction),
2. `Nat` operations delegated to GMP (kernel-level numeral computation),
3. any custom metaprogramming.

## Global negatives (comment-stripped, whole repo)

| marker | count |
|---|---|
| `native_decide` | 0 |
| `macro` / `macro_rules` / `syntax` / `elab` / `notation`-decl / `run_cmd` / `#eval` | 0 |
| `set_option` (any) | 0 |
| `axiom` declarations | 0 |
| `opaque` | 0 |
| `unsafe`, `@[extern]`, `implemented_by`, `partial def` | 0 |
| `sorry` | 4 — both challenge files only (intentional Comparator placeholders) |
| explicit `Nat.pow/div/mod/gcd/shiftLeft/…` | 0 |

So there is no metaprogramming surface at all (vector 3 is empty at source level;
the residue is Mathlib's own, which is out of scope for this artifact).

> CORRECTED 2nd generation: line numbers are against the ORIGINAL file (the first generation counted lines on comment-stripped text and drifted by the height of preceding block comments — e.g. an `inductive` reported at 3015 actually lives at 3064).

## A. Inductive types (14) — vector 1

- `Euler/EulerProof.lean:3064` — `inductive SpatialJet (directions : Fin 4 → LiftTangent) : ℕ → LiftL2 period → Type`
- `Euler/EulerProof.lean:3073` — `inductive CoefficientJet (directions : Fin 4 → LiftTangent) : ℕ → SmoothCoefficient period → Type`
- `Euler/PacketKnownDecomposition.lean:21` — `inductive KnownTerm where`
- `Euler/PacketKnownPieces.lean:14` — `inductive KnownPiece where`
- `Euler/PacketSourceScaleChoice.lean:76` — `inductive SourceCost`
- `NavierStokes/ClosedIntervalJetAlgebra.lean:244` — `inductive PolynomialExpression (ι : Type)`
- `NavierStokes/FlatKernelBounds.lean:76` — `inductive Expr where`
- `NavierStokes/GenericDifferentialPolynomial.lean:185` — `inductive Expression (D ι κ : Type*) where`
- `NavierStokes/GenericFactorSupport.lean:14` — `inductive FieldFactor (D ι : Type*) where`
- `NavierStokes/GenericFactorSupport.lean:106` — `inductive FactorSupportAt (base : ι → D → ℝ) (inc : ℕ → ι → D → ℝ) (x : D) :`
- `NavierStokes/NaturalAxisCoefficients.lean:116` — `inductive Field`
- `NavierStokes/ReservedPatches.lean:22` — `inductive Slot where`
- `NavierStokes/StressActivation.lean:539` — `inductive HistoryRow`
- `NavierStokes/TorusInverse.lean:190` — `inductive Direction`

Recursive / indexed-family ones (the kernel-relevant subset) are
`SpatialJet`, `CoefficientJet`, `PolynomialExpression`, `Expr`, `Expression`,
`FactorSupportAt`; the rest are finite enumerations with `deriving DecidableEq`
(and `Fintype` for `KnownTerm`).

## B. Well-founded / non-structural recursion — vector 1

- `Euler/EulerProof.lean:3202` — `termination_by n`
- `Euler/EulerProof.lean:3233` — `termination_by n`
- `Euler/EulerProof.lean:3291` — `termination_by n`
- `Euler/EulerProof.lean:3331` — `termination_by n`
- `Euler/EulerProof.lean:3399` — `termination_by s`
- `Euler/EulerProof.lean:4703` — `termination_by s`
- `Euler/EulerProof.lean:4712` — `termination_by s`
- `Euler/H6Pressure.lean:28` — `termination_by s`
- `Euler/H6Pressure.lean:53` — `termination_by n`
- `Euler/H6Pressure.lean:93` — `termination_by s`
- `NavierStokes/VolterraAnalyticBounds.lean:164` — `termination_by w.length`
- `NavierStokes/VolterraAnalyticBounds.lean:184` — `termination_by w.length`

`WellFounded.fix_eq` rewrites (the unfolding lemma, i.e. proofs that *depend on*
`Acc.rec` reduction):

- `NavierStokes/GlobalSlowProfiles.lean:910` — `rw [WellFounded.fix_eq]`
- `NavierStokes/SlowRecursion.lean:953` — `rw [WellFounded.fix_eq]`
- `NavierStokes/SlowRecursion.lean:964` — `rw [WellFounded.fix_eq]`

## C. Explicit recursor applications (motive supplied by hand) — vector 1

- `Euler/LpSmoothJetField.lean:17` — `Nat.rec (motive := fun n => ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V],`
- `NavierStokes/ActivationContinuation.lean:517` — `HistoryRow.rec (motive := fun _ => Fin 10) 0 2 4 6 8 r`
- `NavierStokes/ActivationContinuation.lean:520` — `HistoryRow.rec (motive := fun _ => Fin 10) 1 3 5 7 9 r`
- `NavierStokes/WeightedODEJets.lean:177` — `(List.rec`
- `NavierStokes/WeightedODEJets.lean:187` — `(List.rec`

## D. `decide` sites — vector 2 (kernel must evaluate a `Decidable` instance)

204 in `theorem` bodies, 6 in `def` bodies, 85 files. Full list: `DECIDE_SITES.md`.

## E. Large numerals (≥ 7 digits) — vector 2

121 sites in 30 files. Full list: `BIGNUM_SITES.md`.

## F. Declaration-level feature table

`INVENTORY.csv` — one row per declaration (`file,kind,name,line,bodylen,lines`)
plus per-body counts of `decide, norm_num, omega, simp, rfl, native, rec,
induction, termination_by, wf, bignum, pow, choose_fact, Fintype_sum, nat_ops`.
This is the coverage ledger: 52,516 rows, and an audited theorem is one whose row
has been signed off in `FINDINGS.md`.

## G. `attribute` sites (25) — vector 3 residue, meaning-changing but not kernel-changing

All 25 are `local`. 11 `local instance`, 10 `local irreducible`, 2 `local gcongr`,
plus 4 × `attribute [local instance] Classical.propDecidable`
(`NavierStokes/ActualParticularPhysicalData.lean:24`, `ActualSignedPhysicalData.lean:22`,
`InitialPhysicalData.lean:28`, `PositiveTimeSignedData.lean:24`). Full list:
`SITES_attribute.md`. `Classical.propDecidable` as a local instance is worth a look
for the opposite reason to `decide`: it makes `if h : P` and `Decidable` arguments
noncomputable, so a definition can *look* like it computes and not, and two files can
disagree about which instance a definition was elaborated with. `Euler/Solution.lean:41`
(`CompletePartialOrder.toSupSet`) is the previous audit's escalation E2 and is the one
site positioned inside the deliverable spine.
