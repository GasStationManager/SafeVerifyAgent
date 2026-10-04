# openai/ten-proofs `GapCVP.lean` — statement rung, route walk, trust surface

Status: **concluded 2026-10-04.** Plain-language summary:
`SUMMARY-openai-ten-proofs-GapCVP.md`. Statement rung (PAIRED, same author), route walk at three
places plus a no-supplier pass over the whole route, the metaprogramming / trust-surface
read, and — after freeing disk — the build-side rungs: the module built here, `#print
axioms` on the headline, an elaborated positive control that `IsNP` is inhabited, the
authors' comparator configuration re-run, and the export replayed by leanchecker,
con-leche, con-ron and nanoda (§3.2).

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
  the YES/NO languages, the instance encodings, the distance or the gap factors. **Shown
  live (negative control):** a scratch challenge identical to `H_GapCVP.lean` except for the
  gap exponent (`dimension ^ (1/4)` in place of `dimension ^ (1/400)`), run through the same
  comparator configuration, is also "Your solution is okay!" (`controls/H_GapCVP_mut.json`,
  `controls/comparator-mut.log`). So a comparator pass on this configuration certifies the
  hardness scaffolding and says nothing about the approximation factor the theorem is about.
  This audit did the missing check at the level of ELABORATED TERMS: `#print` with
  `pp.all` of the four promises and the 30 definitions they reach, from the challenge module
  and from the solution module, is identical after normalising auxiliary `_proof_n` names,
  the challenge's hidden `sorry`s and four bound-variable names (`controls/PP.lean`,
  `controls/pp_Challenge.txt`, `controls/pp_Solution.txt`). The remaining caveat is that the
  challenge and the proof have the same author.
- **P2. `IsNP` is satisfiable, and the artifact never shows it — closed by an elaborated
  control.** Every NP-hardness claim is "for every language in NP there is a reduction"; if
  nothing were in NP the claims would be vacuous. All 539 occurrences of `VerifierTM` in
  `GapCVP.lean` are hypotheses, no value of that type is ever constructed, and no `IsNP L` is
  proved for any concrete `L`. `gapcvp-intake/controls/NPControl.lean` builds the verifier
  machine that accepts everything against Mathlib's `FinTM2` (one input stack over `Bool ⊕
  Bool`, one output stack over `Bool`, pop until empty, push `true`, halt; time `X + 1`) and
  proves `NPControl.isNP_true : GapCVP.IsNP (fun _ => true) = true`, axioms `[propext,
  Classical.choice, Quot.sound]`, elaborated against the built artifact. So the hypothesis of
  every `IsNPHardPromise` theorem is inhabited, and the theorems are not vacuous.

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

### 3.2 Build-side rungs (run 2026-10-04 after freeing 17 GB of disk)

| rung | result |
|---|---|
| `lake build GapCVP` (Lean v4.32.0, Mathlib cache 8,275 oleans) | 11 min 38 s wall, peak lean RSS ≈ 8.7 GB, 120 MB olean |
| `#print axioms` on the four headline theorems and `polynomialTimeClosedUnderComposition` | each exactly `[propext, Classical.choice, Quot.sound]` (`controls/Axioms.lean`) |
| `ComparatorChallenges.H_GapCVP` | builds; its only warnings are the eight deliberate `sorry` placeholders |
| the authors' comparator (`H_GapCVP.json`), comparator at its own `v4.32.0` tag, lean4export from the artifact's manifest, nanoda from the v4.35.0-rc2 toolchain | "Nanoda kernel accepts the solution. Lean default kernel accepts the solution. Your solution is okay!" in 6 min 17 s (`controls/comparator-run.log`). Caveats: run through `lake env` with the comparator's development `fake-landrun` shim (patched to keep `--env`; no sandboxing, which is irrelevant to the verdict on our own box), and the pinned `Lean4Checker` dependency in the artifact's manifest does not compile against v4.32.0 (`Replay.lean:66` type mismatch), so the comparator could not be built from inside the artifact |
| `lean4export GapCVP -- <33 Palomar targets> <4 theorems>` | 42 s, 449 MB, 57,683 declaration records, 3 axiom records |
| `leanchecker --from-export` (v4.35.0-rc2 binary; the v4.32.0 one lacks the flag) | "Lean default kernel accepts the solution", 3 min 20 s |
| `con-leche --verified` | "accepted 57683 declarations", 2 min 55 s |
| `con-ron` | "accepted 57683 declarations", 3 min 20 s |
| `nanoda_bin` (Palomar config, 4 threads) | rc 0, 33 s |
| `NPControl.isNP_true` | elaborates; 3 axioms (§1, P2) |
| negative control: challenge with gap exponent 1/4 instead of 1/400, same `definition_names` | comparator: "Your solution is okay!" (P1 demonstrated) |
| elaborated-term diff of the four promises and the 30 definitions they reach (challenge vs solution, `pp.all`) | identical up to auxiliary proof names, hidden `sorry`s and binder names |

The comparator pass still has the P1 limitation (holes), which is a property of the
configuration, not of the run, and the mutant run above shows it concretely; the
elaborated-term diff of the hole bodies is the complement.

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

- The comparator was run with the development landrun shim, not the real sandbox; the
  sandbox guards a hostile `Solution.lean` on a shared runner and does not bear on the
  kernel verdicts here.
- Two blocks carry most of the proof's mass and were read only at their interfaces: the
  algebraic reconstruction (paper §§4–5, Lean ≈ 66,000–74,400) and the TM2 machine layer
  (the `BitTM` constructions, ≈ 17,000–62,000 and 93,000–126,000; only the kernel can
  certify that one). Denominators: ~6,600 of 130,430 lines read with `sed`; ~120 of 3,683
  theorem statements, ~45 proof bodies.
- Mathlib's computability files were read at the pinned commit `81a5d257` for the statement
  rung (identical to v4.33.1 apart from `set_option` lines); the route walk read them at
  v4.33.1 and asks for a diff (E1, low).

## 6. Reproduce

```
git clone https://github.com/openai/ten-proofs && cd ten-proofs && git checkout 94bc0feb
python3 <SafeVerifyAgent>/audits/scan_repo.py GapCVP.lean          # single-file mode, added 2026-10-04
python3 <SafeVerifyAgent>/audits/gapcvp-intake/cone-gapcvp.py       # name-level cone of the headline
lake exe cache get && lake build GapCVP ComparatorChallenges.H_GapCVP
lake env lean <SafeVerifyAgent>/audits/gapcvp-intake/controls/Axioms.lean
lake env lean <SafeVerifyAgent>/audits/gapcvp-intake/controls/NPControl.lean   # IsNP inhabited
bash <SafeVerifyAgent>/audits/gapcvp-intake/controls/check.sh                  # export + 4 checkers (edit paths)
# comparator: clone leanprover/comparator at v4.32.0, lake build, then from the artifact root
#   PATH=<lean4export>:<nanoda_bin>:<landrun> lake env <comparator> ComparatorChallenges/H_GapCVP.json
```
