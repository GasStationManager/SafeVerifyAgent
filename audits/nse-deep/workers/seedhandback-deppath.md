# NSE audit: is NavierStokes/SeedHandbackJets.lean load-bearing?

Repo: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5). READ-ONLY, no `lake build`.
Method: source-level parse of all 2659 `.lean` files with python (namespace-aware declaration index,
51061 declaration names), plus module import graph, plus grep.

## VERDICT: DEAD-WEIGHT (imported only, never used)

`NavierStokes/SeedHandbackJets.lean` is a 393-line, 0-`sorry` leaf module. Nothing in the repo
references any of its 40 declarations. It is not even in the import closure of the headline theorems.

## 1. Headline theorems

* `NavierStokes/ComparatorSolution.lean:16` `theorem navier_stokes_breakdown_R3 (nu) (hnu) : ∃ u₀ f, InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧ ¬ ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p`
  proof body (line 20): `exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu`
* `NavierStokes/ComparatorSolution.lean:23` `theorem navier_stokes_breakdown_periodic ...`
  proof body (line 27): `exact ComparatorBridge.navier_stokes_breakdown_periodic nu hnu`
* (`ComparatorChallenges/NavierStokes.lean:273,280` are the challenge-side `sorry` statements, not the proofs.)

Shortest real chains:
* R3: ComparatorSolution.lean:20 -> `ComparatorBridge.navier_stokes_breakdown_R3` (NavierStokes/ComparatorR3Theorem.lean:38) -> `NavierStokesR3.theorem_1_1` + `NavierStokesR3.comparator_of_breakdown` (lines 43-44).
* Periodic: ComparatorSolution.lean:27 -> `ComparatorBridge.navier_stokes_breakdown_periodic` (NavierStokes/ComparatorTheorem.lean:47) -> `PeriodicPaper.periodic_corollary` + `option_D_of_paper_candidate` (lines 52-53).

## 2. Import-level proof of absence (decisive)

A Lean proof term can only mention declarations from transitively imported modules.
Transitive repo-module import closure of `NavierStokes.ComparatorSolution` = 609 modules.
`NavierStokes.SeedHandbackJets` is NOT one of them (`'NavierStokes.SeedHandbackJets' in ti == False`).
Hence no SeedHandbackJets declaration can occur in either headline proof, at any depth.

The module only enters the build via the umbrella root:
`NavierStokes.lean:1-2` imports `ComparatorSolution` and `PaperResults`;
`PaperResults` -> `PaperAdditionalResults` -> `NavierStokes/PaperAdditionalResults.lean:16 import NavierStokes.SeedHandbackJets`.
`NavierStokes.PaperAdditionalResults` is a pure 31-line import aggregator: it contains ZERO declarations
(verified: no non-import, non-comment lines). So even that path is import-only.
Transitive closure of the root `NavierStokes` = 753 modules and does contain SeedHandbackJets - i.e. it is
compiled, but only as a leaf.

## 3. Name-level transitive closure (independent confirmation)

Roots: the two `NavierStokes.Comparator.*` theorems. Resolution: exact name, enclosing-namespace prefixes,
`open`ed namespaces, then unique/suffix base-name match; restricted to the 609-module import closure
(32612 candidate declarations). Depth limit 40; BFS terminated on its own at depth 30.
Result: 21392 reachable declarations. Intersection with the 40 `NavierStokes.SeedHandbackJets.*` names: EMPTY.
No file of the closure is `NavierStokes/SeedHandbackJets.lean`.

## 4. Reverse direction (who consumes it)

`grep -rn 'SeedHandbackJets' NSE --include=*.lean` -> exactly 3 hits:
* SeedHandbackJets.lean:15 `namespace NavierStokes.SeedHandbackJets`
* SeedHandbackJets.lean:392 `end NavierStokes.SeedHandbackJets`
* PaperAdditionalResults.lean:16 `import NavierStokes.SeedHandbackJets`
No `SeedHandbackJets.` qualified use, and no `open ... SeedHandbackJets` anywhere (also 0 hits in md/json/toml/yml/py).

Bare-name word-grep outside the file:
* 0 other files for the distinctive names: SmoothOnBand, angularExpression, axialExpression, basis_pairBound, differenceBounds, fieldDifference, fixed_L_bound, fixed_d_bound, jetValues, jetValues_bddAbove, jetValues_nonempty, massExpression, outputDifference, outputExpression, packet_pairBound, parameterNorm, parameterNorm_bounds, parameterNorm_le, profile_comparison, profile_comparison_norm, stocks_comparison, stocks_formulas
* other-file hits exist only for generic names, in unrelated namespaces of files that do not import
  SeedHandbackJets: Expr (2 files), JetBound (3 files), L_lower (15 files), basis (42 files), historyDifference (3 files), inputBounds (2 files), packet (257 files), stocks (11 files)

## 5. Caveats

* Source-regex analysis, no kernel check (`lake build` forbidden here). Statement-level and proof-level
  identifiers are both scanned (whole declaration block), so the closure over-approximates real proof use.
* The import-closure argument (section 2) does not depend on the regex resolution quality; it only needs
  the `import` lines, and it alone settles the question.
* Not audited here: whether SeedHandbackJets itself is sound/non-vacuous. It has 0 `sorry`.
