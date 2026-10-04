# openai/ten-proofs `GapCVP.lean` — statement rung, route walk, trust surface

Status: **concluded 2026-10-04** at the scope below: statement rung (PAIRED, same author),
route walk at three places plus a no-supplier pass over the whole route, and the
metaprogramming / trust-surface read. Nothing built, no `#print axioms`, no comparator or
independent checker run here (disk).

Artifact: `openai/ten-proofs` at `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6` (2026-08-01), Lean
v4.32.0, Mathlib v4.32.0; the formalization is the single file `GapCVP.lean` (130,430 lines,
3,683 theorems, 461 namespaces, no comments). Headline, comparator-checked by the authors
against `ComparatorChallenges/H_GapCVP.lean`: `GapCVP.Comparator.gapCVP400IsNPHard :
IsNPHardPromise gapCVP400Promise` and three siblings (binary nearest codeword, binary
syndrome decoding, ℓ_p CVP for every rational p ≥ 1). Informal claim (paper Chapter 7,
"n^{1/400}-Hardness of the Euclidean Closest Vector Problem", Theorem 1, Corollaries 15–16):
a deterministic polynomial-time reduction from 3SAT, hence NP-hardness of GapCVP^(2) within
n^{1/400} under Karp reductions; n^{1/200} for the coding problems; n^{1/(200p)} for ℓ_p.
Provenance: authored by OpenAI, model "Astra (OpenAI)" per `formalization.yaml`; selected
from the 2026-09-30 survey as the only remaining target with a tactic-macro layer. Intake:
`gapcvp-intake/` (`REFERENCE-gapcvp.md`, `STATEMENT.md`, `ROUTE-MAP.md`, `ROUTE-WALK.md`,
`TRUST.md`, `cone-gapcvp.py`).

## 1. Verdict

**No defect found.** The statement is EXACT against the paper on every clause that carries
the claim, with three deviations that make the formal statements STRONGER (§2). The route is
EXACT at the three places reconstructed (Cook–Levin over Mathlib's TM2 model, the gap core,
the coding and ℓ_p transfers), and every assumption-shaped object on the route is supplied
by a construction in the file. The trust surface is 23 simp-based tactic macros and classical
`Decidable` packaging, nothing else.

**Two caveats on the pairing itself**, which are the audit's main observations:

- **P1. The comparator did not compare what the four problems ARE.** `H_GapCVP.json` lists
  the four `*Promise` definitions under `definition_names`, which makes them comparator
  "definition holes": for a hole the comparator checks name, type, universe levels and
  safety and walks only the hole's TYPE (comparator `Compare.lean:49–50, 61–63, 102`; its
  README says hole values "must always be checked with an additional (potentially human)
  verifier"). The holes exist because the challenge's `disjoint` fields are `by sorry`. So
  the authors' comparator pass certifies the scaffolding (`IsNPHardPromise`,
  `PromiseReduction`, `IsNP`, `BitTM`, `VerifierTM`, the encodings) and says nothing about
  the YES/NO languages, the instance encodings, the distance or the gap factors. This audit
  did that check BY TEXT: every `yes`/`no` field and every definition they reach is
  byte-identical after whitespace normalisation between `H_GapCVP.lean` and
  `GapCVP.lean:129737–130428`, three definitions differ only in bound-variable names, the
  promises differ only in `disjoint` (real proofs in `GapCVP.lean`), and no identifier
  resolves differently. Text-level, not elaborated terms; and the challenge and the proof
  have the same author.
- **P2. `IsNP` is satisfiable, but the artifact never shows it.** Every NP-hardness claim is
  "for every language in NP there is a reduction"; if nothing were in NP the claims would be
  vacuous. The statement agent built, by hand against the pinned Mathlib's `TM2.stepAux`,
  `haltList` and `TM2OutputsInTime`, a verifier machine accepting everything, which gives
  `IsNP (fun _ => true)`, so the statements are not vacuous. But all 539 occurrences of
  `VerifierTM` in `GapCVP.lean` are hypotheses, no value of that type is ever constructed, and
  no `IsNP L` is proved for any concrete `L`. A one-line positive control (`IsNP (fun _ =>
  true)` or 3SAT ∈ NP, elaborated) is the cheapest thing that would close this; it needs the
  build.

## 2. Statement rung (`gapcvp-intake/STATEMENT.md`, `REFERENCE-gapcvp.md`)

Reference written from the paper's §1.1, Theorem 1, Corollaries 15–16 and Arora–Barak before
the challenge file was opened (the brief had named the challenge's identifiers; disclosed).
Pairing, every clause exact except:

| deviation | Lean | direction |
|---|---|---|
| D1 `hasIntegerTarget` in both YES and NO (H:120, 127) | GapCVP restricted to t ∈ ℤ^n | STRONGER: a reduction into the restriction is a reduction into the ℚ-target problem; it is the form Theorem 1 proves. The ℚ-target Euclidean problem is also the p = 2 case of `finitePNormGapCVPIsNPHard` |
| D2 syndrome-decoding NO requires `∃ word, H·word = b` (H:259–260) | inconsistent systems in neither language | STRONGER (smaller NO set); the paper's inconsistent-branch output is consistent, so its proof is compatible |
| D3 generator matrix `Fin blockLength → Fin generatorRank → ZMod 2`, codewords `G·c` (H:159, 173–178) | columns generate; paper uses rows | transpose convention; same codes (k = 0 allowed, which the paper's {00} output needs) |

Checked and exact: NP via a polynomial-time Mathlib `TM2ComputableInPolyTime` verifier on
`encodingProd` pairs with certificates of length ≤ `bound.eval |x|`; reductions
`TM2ComputableInPolyTime bitEncoding bitEncoding map` with `bitEncoding = id`, time bounded by
`time.eval` of the input length for ALL inputs; the distance is squared Euclidean against r²
and (γr)²; γ evaluated at `dimension` / `blockLength` as in the paper; `encodeInstance`
injective (prefix-free atoms, dimension first; proved in `GapCVP.lean:129806`), so YES and NO
are disjoint given γ ≥ 1 and r > 0; `wellFormed` (0 < n, det ≠ 0, 0 < r) inhabited; the
`@decide P (Classical.propDecidable _)` Bool languages equal `true` exactly when P holds.
`PolynomialTimeClosedUnderComposition` is a theorem, not a hypothesis (§3).

## 3. Route walk and no-supplier pass (`ROUTE-MAP.md`, `ROUTE-WALK.md`)

Chain: `gapCVP400IsNPHard` (130398) ← `isNPHardPromise_of_original` (130374, copies fields)
← `paperVariableArityPhysicalIntegerTargetNPHardPromise` (126152) ←
`nphardPromise_of_nphard_of_promiseReduction` (1772) applied to
`paperOriginalThreeSATIsNPHard` (88642, Cook–Levin), the 3SAT→GapCVP reduction, and
`polynomialTimeClosedUnderComposition` (1736, a THEOREM: an explicit two-phase composed TM2
machine, time `first.time + second.time ∘ (X + maxPush·first.time)`).

- **Cook–Levin, EXACT.** Arbitrary `L ∈ IsNP` → nondeterministic guess of ≤ `bound(|x|)`
  certificate bits, then the verifier; tableau with one-hot cells, fixed first row, accept
  clause, forbidden 2×3 windows; Tseitin 3-CNF translation; `tableau_completeness` (1970) /
  `tableau_soundness` (2226); size T = |x| + bound + g·maxPush + g + 1. Handles Mathlib's
  generality (only the input alphabet is required finite) by tagging work-stack symbols with
  their push site (`CLBoundedStates`, 3842). `paperOriginalThreeSATLanguage` (88578) is 3SAT
  with three literal slots, repeats allowed.
- **Gap core, EXACT in exponent, n, radius and parameters.** n = dimension, factor
  dim^{1/400}; radius ⌈√((ℓ+1)|P|)⌉, N = 100+s+m+ℓ, q = 2^{⌈log₂ N^200⌉}, T = N^30,
  M ≤ 40N^401, constraint families C1–C4 as in the paper. Intermediate constants differ
  (Markov slack q/10 vs the paper's q/20; Proposition 14's hypothesis stated as 10‖z‖² ≤ qN⁴);
  the bridge at 74221 uses r² ≤ 8qN, M^{1/200} ≤ N^{2.01} and 80^100 < 100^99 (recomputed
  independently: true).
- **Coding and ℓ_p transfers, EXACT.** Lemma 7's parity-lift lattice; Corollary 16 with
  A = ⌈4p⌉ and r_p^p < 2R; all three routes feed one core through a 2·n^{1/200}·R threshold.
- **No-supplier pass: clean.** Every structure that looks like a hypothesis
  (`LocalTableauCompiler`, `TableauSimulation`, the matrix-shape and cell-computer records,
  `BinaryGaussianExactSourceInitializer`, `PackedMatrixSourceComputer`,
  `ShiftedTupleRankComputers`) is constructed by a `def`/`theorem` in the file; the 42
  `variable` lines are implicit types and instances discharged where used. Cone of the
  headline: at most 7,019 of 8,029 declarations (name-level, upper bound; 47 ambiguous short
  names).

## 4. Trust surface (`TRUST.md`)

Zero each: `axiom`, `sorry`, `opaque`, `native_decide`, `ofReduceBool`, `unsafe`,
`implemented_by`, `extern`, `elab`, `syntax`, `macro_rules`, `run_cmd`, `initialize`,
`set_option`, any `Lean.` meta API. 23 `macro "<name>_step_tac" : tactic`, each `simp
[<machine defs>, Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
<;> try { congr 2; funext stack; fin_cases stack <;> simp [Function.update] } <;> try rfl`,
proving single steps of concrete TM2 programs, used 439 times. 11 `attribute [local instance]
Classical.propDecidable` and 2 `[-instance]` removals; 112 `@decide … (Classical.propDecidable
_)` Bool definitions in 101 declarations, unpacked by the instance-generic
`decide_eq_true_eq`. 34 `decide` tactic uses, all on small finite goals; the largest numeral
in the file is 2000 (an instance priority). Nothing is kernel-computation-heavy.

## 5. What this audit does not say

- Nothing was built; the authors' comparator pass, `sorry_count: 0` and the three-axiom list
  are taken from `formalization.yaml`. The build needs full Mathlib (~8 GB of disk this box
  did not have).
- Two blocks carry most of the proof's mass and were read only at their interfaces: the
  algebraic reconstruction (paper §§4–5, Lean ≈ 66,000–74,400) and the TM2 machine layer
  (the `BitTM` constructions, ≈ 17,000–62,000 and 93,000–126,000; only the kernel can
  certify that one). Denominators: ~6,600 of 130,430 lines read with `sed`; ~120 of 3,683
  theorem statements, ~45 proof bodies.
- Mathlib's computability files were read at the pinned commit `81a5d257` for the statement
  rung (identical to v4.33.1 apart from `set_option` lines); the route walk read them at
  v4.33.1 and asks for a diff (E1, low).
- The positive control for P2 (`IsNP` inhabited inside the artifact) was done by hand against
  the Mathlib definitions, not elaborated.

## 6. Reproduce

```
git clone https://github.com/openai/ten-proofs && cd ten-proofs && git checkout 94bc0feb
python3 <SafeVerifyAgent>/audits/scan_repo.py GapCVP.lean          # single-file mode, added 2026-10-04
python3 <SafeVerifyAgent>/audits/gapcvp-intake/cone-gapcvp.py       # name-level cone of the headline
lake exe cache get && lake build GapCVP ComparatorChallenges        # then the comparator per ComparatorChallenges/README.md
```
