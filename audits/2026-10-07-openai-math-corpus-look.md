# openai/math `lean/` — corpus look: statement rung on four challenges, trust surface, big numbers, checker replay

Status: **concluded 2026-10-08** at the scope below. This is a LOOK at a 405-statement corpus,
not an audit of any one result: four challenge statements paired against their papers, a
corpus-wide trust-surface and metaprogramming scan, a big-number and `decide +kernel`
inventory, and an export-and-replay of the built headline theorems through the four
external checkers. 401 of the 405 statements were not read.

Artifact: `openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (2026-10-06), the
`lean/` directory only (sparse checkout); Lean `v4.34.1`, Mathlib `d13f23b7`; 121,734 `.lean`
files, 25,910,542 lines under `OAI/`; 405 `ComparatorChallenges/<Name>.{lean,json}`; 235
`docs/NNN.md` scope notes (every challenge file is linked from one); 30 `require`s in
`lakefile.lean` (Mathlib plus TauCeti, PrimeCert, leancert, PrimeNumberTheoremAnd,
ClassFieldTheory, carleson, iut, …) with 23 `patches/*-lean4341.patch` (160 k lines) applied
by `lake update`. `formalization.yaml` (v0.4): `status.scope: "Partial progress."`,
`review.status: unchecked`, 178 `main_results` entries. Intake: `oaimath-intake/`.

## 1. Verdict

**No defect found at this scope.** The four statements read are **PAIRED, EXACT**
(DimensionTenPair 16/16 clauses, LaughlinGap 11/11, FourRowPermanent 9/9, PlaneColoring 5/5).
The trust surface is as clean as any corpus scanned so far: no `native_decide`, `bv_decide`,
`ofReduceBool`, `implemented_by`, `extern`, `unsafe`, `sorry`, `set_option`, `simproc`,
`addDecl` or `#eval` anywhere in 25.9 M lines; one real `axiom` (in a challenge file, §3.3).
All 405 challenge files import only `Mathlib`, so no statement depends on a patched
third-party library. The four headline theorems built here are ACCEPTED by con-leche (`--verified`) and con-ron,
and three of the four by leanchecker and nanoda as well (the fourth, LaughlinGap, exceeded
leanchecker's 101-minute budget and nanoda was not run) — §4, including the 634-digit
literals. So the answer to "would con-leche behave differently here" is measured: no
decline anywhere, at a cost set by the kernel-decision count, not the export size.

Two things to keep in view, neither a defect: the docs notes formalise a SUBSET of each
paper's claims and say so (§3.1), and 227 of the 405 challenges are not listed in the yaml's
`main_results` (§3.2).

## 2. Was con-leche tried on this corpus?

No evidence that it was, and some that it was not:

- The repo mentions Comparator and lean4export (`formalization.yaml` acknowledgements,
  `COMPARATOR.md`) and nothing else: no `con-leche`, `con-ron`, `nanoda`, `leanchecker`,
  `lean4lean` string anywhere in the checkout (`.md`, `.yaml`, `.json`, `.lean`, `.py`, `.sh`).
- 402 of 405 comparator configs set `enable_nanoda: false`, two omit the key, and one
  (`ArtinParabolicIntersections.json`) sets it true. So even the comparator's built-in second checker was
  switched off for the published runs.
- `review.status: unchecked` (yaml).

**Expected behaviour.** con-leche and con-ron decline for exactly three reasons measured in
`checkers/DECLINE-CORPUS.md` — a used `sorryAx`, a user axiom, or the per-proof axioms
`native_decide`/`bv_decide` add — plus a toolchain whose well-founded `Nat` definitions
match none of the binary's pins (v4.33.0, v4.34.0-rc2, nightly-2026-09-10 in the bundled
v4.35.0-rc2 build). This corpus has none of the first three anywhere, and the pin question is
answered by the replay: v4.34.1 oleans export and check with no pin complaint (§4). So on a
proof the Lean kernel accepts, con-leche is expected to ACCEPT, not decline, everywhere
here. What it cannot do is anything about the statement rung (§3), and what it has not been
asked to do is the whole corpus: 1,354,379 `decide +kernel` sites and 1,246 files carrying
40-digit-or-longer literals (§3.4) are a kernel-replay COST question, not a decline question.

## 3. Statement rung

### 3.1 The four statements read (`oaimath-intake/statements/`)

Method as always: the reference statement was written from the paper BEFORE the Lean was
read, then paired clause by clause; two denominators (which of the paper's claims are
formalised at all; which of the Lean clauses match).

| challenge | theorem | paper claim | clauses | formalised share of the paper | verdict |
|---|---|---|---|---|---|
| DimensionTenPair | `OAI.DimensionTen.main_pair` | Thm 1.2: PPT Φ₁, Φ₂ on M₁₀ with Z = J(Φ₂∘Φ₁) ≠ 0, no nonzero product vector in range Z, Φ₂∘Φ₁ not entanglement breaking | 16/16 EXACT | Thm 1.2 only (Thm 1.1 zero-secret-key out of scope; Thm 1.3 is `DimensionTenChannel`) | PAIRED EXACT |
| LaughlinGap | `OAI.LaughlinGap.thm_main` | Fock-space paper Cor 1.2: ∃ N₀ ≥ 2, ∀ N ≥ N₀, Q = 3(N−1): H_{N,Q} ≥ (1/25)(I − P_L) | 11/11 EXACT | the unperturbed gap only; the stability paper's Thm 1.1 (disorder) not formalised, docs say so | PAIRED EXACT |
| FourRowPermanent | `OAI.FourRow.robust_permanent` | Thm 1.1 of a THIRD preprint linked from `docs/238.md`: ∃ p₀ ∈ (4/3, 2), ε > 0, ∀ ν on S₄ with TV < ε and uniform marginals, E_ν ∏ fᵢ(π(i)) ≤ ∏ ‖fᵢ‖_{p₀} | 9/9 EXACT | Thm 1.1 only | PAIRED EXACT |
| PlaneColoring | `OAI.Problem160.properColoring_seven` | χ(ℝ²) ≤ 7 (Isbell colouring, pp. 2–3) | 5/5 EXACT | the minor half; the headline "not 5-colourable" is `EuclideanFiveColor` (a definition-hole config, §3.2) | PAIRED EXACT |

Checks worth recording: the DimensionTen construction was rebuilt numerically from the Lean
definitions (`dimensionten_check.py`): Z is PSD of rank 80, its partial transpose PSD, and
Z[(0,0),(0,0)] = 10,077,696 = 6·36⁴, the value the paper states on p. 32, so the Lean builds
the paper's own Z; `separable` admits r = 0 (0 is separable, which only makes ¬EB harder);
the `0 < k` guards are vacuous at k = 0. The Laughlin `pairCoefficient` simplifies to the
paper's spin-(Q−1) basis with Z_{Q,b} = Q·C(2Q−2, b−1), and the Lean-mirrored spectrum for
N = 2, 3 has a one-dimensional kernel containing `laughlinVector`. The four-row theorem is not
vacuous: the uniform law satisfies every hypothesis and the identity-matrix example fails
below p ≈ 1.744, so a genuine p₀ < 2 is required (the solution uses p₀ = 2 − 10⁻⁵, ε = 10⁻⁵).

Pattern across all four: the docs note names the subset it formalises and names what it
leaves out. Read the note's "Scope" paragraph before the challenge; the challenge NAME is not
the paper's headline (PlaneColoring is the upper bound; LaughlinGap is the unperturbed input
to the stability paper).

### 3.2 Corpus-level observations

- **Definition holes.** Nine configs list `definition_names` (bodies compared by name and
  type only, playbook lesson 18): Brenier (12 defs), DefocusingNLS (3), ElementaryPositivity
  (1 def, **0** `theorem_names`), EuclideanFiveColor (1), KServer (9), Naimark (7),
  OccupiedOverlap (5), Rokhlin (4), SpinAngle (3). A comparator "okay" on these covers the
  scaffolding, not the hole bodies. DONE 2026-10-08 (`oaimath-intake/holes/RESULTS.md`): each
  pair built, both sides exported, every hole's type and value compared as de Bruijn terms up
  to alpha-equivalence. Eight of nine close with no body difference (OccupiedOverlap differs
  in one auxiliary proof constant of the same `Nat.AtLeastTwo` type — proof irrelevance);
  DefocusingNLS (2,415-module closure, not built) matches textually in its data components,
  its holes being subtype elements whose membership proofs the challenge leaves as `sorry`.
  ElementaryPositivity's hole IS its statement (inhabit a Σ-type), so the config checks the
  hole's type, which is the content; its binder info differs between the two sides, which
  the comparator cannot see. No statement-level discrepancy.
- **Coverage record.** `formalization.yaml` `main_results` lists 178 configs; 227 challenge
  configs (with scope notes) are unreferenced there. The yaml's own `scope` is "Partial
  progress."; nothing says which 178 were selected or why.
- **`axiom` in a challenge file.** `ComparatorChallenges/HarmonicGrowth.lean:100` declares
  `axiom mainStatement : MainClaim` and `theorem main : MainClaim := mainStatement`, where
  every other challenge ends in `sorry`. The solution (`OAI/Geometry/HarmonicGrowth/Main.lean:
  475`) proves `main` by a proof and imports only `OAI.Geometry.HarmonicGrowth.Growth`, and the
  config's `permitted_axioms` are the standard three, so a solution that leaned on the
  challenge's axiom would fail the comparator. Harmless; worth a grep in any corpus because
  the pattern "challenge supplies an axiom the solution may import" is exactly what the
  permitted-axioms gate exists for.
- **Challenge imports.** Every one of the 405 challenge files imports `Mathlib` only. The 23
  dependency patches therefore touch solutions, never statements.

### 3.3 Trust surface and metaprogramming (comment-stripped scan, `scan_repo.py`)

| marker | count |
|---|---|
| `native_decide`, `bv_decide`, `ofReduceBool/Nat`, `implemented_by`, `@[extern`, `unsafe`, `sorry`, `set_option`, `simproc`, `addDecl`, `#eval`, `initialize` | 0 |
| `axiom` (real) | 1 (§3.2; three more are the word in docstrings) |
| `run_cmd` | 11 — `Lean.LibrarySuggestions.nameDenyListExt.addEntry` (10, hiding the file's own lemmas from `exact?`-style suggestion) and one `auxLemmasExt.setState env {}` |
| `elab` | 7 — tactic elaborators (`poly_bound`, `poly_auto`, `pts_pl`, `direct_decidable_heq`, …) that build a term with `mkAppM`/`mkAuxTheorem` and `goal.assign` it; every term so built is kernel-checked when the enclosing declaration is added |
| `macro` / `macro_rules` / `syntax` | 6 / 13 / 14 — tactic and notation sugar |
| `partial def` | 1 file (`Computability/TypeSystem/Logic.lean`: `reify`, `Node.syntax`, `atomFunction` — meta-level, `MetaM`) |
| `opaque` | 20 declarations in 20 files, ALL with bodies: subtype-with-proof wrappers (`opaque degreeData : {n // sizeFactor ≤ 2^n} := ⟨…⟩`, `opaque pWrapped : Subtype (Eq pDefinition) := ⟨_, rfl⟩`) used to stop the kernel unfolding a large definition; no body-less `opaque` (which would be an `Inhabited`-chosen constant) |
| `notation` / `attribute` | 23,404 / 19,244 (ordinary) |

Nothing here reaches past the kernel. The `run_cmd` sites edit elaborator-side environment
extensions (suggestion deny lists), not declarations.

### 3.4 Big numbers and `decide +kernel`

| item | measure |
|---|---|
| files with a ≥ 40-digit literal | 1,246 (Analysis 713, NumberTheory 281, MathematicalPhysics 211) |
| longest literal | 634 digits, `OAI/Analysis/Quantum/DimensionTen/{IntegerPolynomials,PolynomialData}.lean` |
| shape | `lemma coef_41_k : ((N : ℤ) : ZMod 41) = r := by decide +kernel` — an `Int` cast into `ZMod p` evaluated by the kernel |
| `decide +kernel` sites | 1,354,379 in 5,848 files (Analysis 700,928; Combinatorics 360,146; MathematicalPhysics 193,119) |
| in the modules replayed in §4 | DimensionTen 441 big literals / 266 sites; PPTSquare (its dependency) 1,438 / 1,959; LaughlinGap 440 / 2,297 |

For con-leche the literal arithmetic is the TRUSTED GMP fast path (the Lean runtime's
`Nat`); for con-ron it is the verified `ron::Nat` (`checkers/CON-RON` notes). A replay that
accepts the DimensionTen theorem therefore exercises both routes on 600-digit operands.

## 4. Build and checker replay

Built here from the sparse checkout (`lake update` with the repo's 23 patches, Mathlib cache
restored; 16 GB container, 4 cores). The four-way default build of `DimensionTen.Main` was
killed by the memory cgroup after 29 min (exit 137, one Lean process per file at 4–7 GB RSS);
`LEAN_NUM_THREADS=2` finished the remainder in 404 s. That is a property of this container,
not of the artifact.

| solution module | OAI modules | build | headline |
|---|---|---|---|
| `OAI.Combinatorics.Permanent.Main` | 5 | 1 m 43 s | `OAI.FourRow.robust_permanent` |
| `OAI.Geometry.PlaneColoring.Main` | 9 | 1 m 08 s | `OAI.Problem160.properColoring_seven` |
| `OAI.Analysis.Quantum.DimensionTen.Main` | 129 | 29 m (OOM) + 6 m 44 s | `OAI.DimensionTen.main_pair` |
| `OAI.Analysis.LaughlinGap.Main` | 106 | 44 m 50 s | `OAI.LaughlinGap.thm_main` |

Export: lean4export at tag v4.34.0 built under toolchain v4.34.1 (the v4.34.1 toolchain
bundles `leanchecker` but no exporter), one headline theorem per file with the usual
`Quot`/`Nat`/`String` targets, so each export is the theorem's whole Mathlib closure.
Checkers: the v4.35.0-rc2 toolchain's bundled `leanchecker`, `con-leche --verified`,
`con-ron --verified`, `nanoda_bin` (standard three axioms permitted), as in
`checkers/DECLINE-CORPUS.md`. Control: the `sorry`-carrying PlaneColoring CHALLENGE module
exported and replayed first — leanchecker accepted it (it accepts `sorryAx`), con-leche and
con-ron declined it ("1 via sorryAx; first skipped: `OAI.Problem160.properColoring_seven`",
15,631 Mathlib declarations checked with no toolchain-pin complaint), nanoda panicked
(exit 101, "declaration not found in infer_const, sorryAx") — the decline corpus's
behaviour, reproduced on v4.34.1 oleans.

| theorem | export | leanchecker | con-leche `--verified` | con-ron | nanoda |
|---|---|---|---|---|---|
| `OAI.FourRow.robust_permanent` | 80.9 MB, 1,526,030 lines, 35 s | rc 0, 17 s | **accepted** 16,819 decls, 15 s | accepted 16,819, 20 s | rc 0, 4 s |
| `OAI.Problem160.properColoring_seven` | 81.3 MB, 1,528,020 lines, 25 s | rc 0, 18 s | **accepted** 17,456 decls, 19 s | accepted 17,456, 25 s | rc 0, 7 s |
| `OAI.DimensionTen.main_pair` (634-digit literals) | 1.85 GB, 35,164,592 lines, 5 m 07 s | rc 0, 15 m 30 s | **accepted** 78,634 decls, 5 m 57 s | accepted 78,634, 6 m 59 s | rc 0, 3 m 27 s |
| `OAI.LaughlinGap.thm_main` (2,297 `decide +kernel`) | 610 MB, 11,405,089 lines | NOT FINISHED in 101 min (stopped at the task budget) | **accepted** 76,294 decls, 62 m 36 s with `--jobs=2` (check 61.9 min, parse 10 s, install 32 s) | accepted 76,294, 77 m 36 s with `--jobs=2` | unmeasured (budget) |


## 5. What this look does not say

401 of 405 statements unread; no route walk on any result; DefocusingNLS's three holes
compared only textually; the 23 dependency patches unread (they cannot touch a
statement, §3.2, but they are compiled into every solution that imports the patched
library); no whole-corpus replay (the cost of 1.35 M kernel decisions through an external
checker is unmeasured); con-leche's own four accept-more-than-Lean cases
(`checkers/DECLINE-CORPUS.md`) not probed against this corpus; the scanner's "implicit-use
def" rows (230) not classified. The four statement checks were done by four independent
readers from the same brief (`statements/BRIEF.md`) and not cross-read.

## 6. Reproduce

```
git clone --filter=blob:none --sparse https://github.com/openai/math && cd math && git checkout adc7f124
git sparse-checkout set lean && cd lean && lake update && (cd .lake/packages/mathlib && lake exe cache get)
python3 <SafeVerifyAgent>/audits/scan_repo.py --sites .            # trust surface, §3.3
lake build OAI.Analysis.Quantum.DimensionTen.Main OAI.Analysis.LaughlinGap.Main \
           OAI.Combinatorics.Permanent.Main OAI.Geometry.PlaneColoring.Main
# lean4export at tag v4.34.0 built under toolchain v4.34.1, then
<SafeVerifyAgent>/audits/oaimath-intake/controls/check.sh DimensionTenPair OAI.Analysis.Quantum.DimensionTen.Main OAI.DimensionTen.main_pair
```
