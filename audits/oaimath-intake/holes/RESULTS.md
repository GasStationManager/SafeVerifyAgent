# Definition-hole diff — the nine `definition_names` configs in openai/math

Method: the comparator matches a `definition_names` entry by name, universe parameters,
type and safety only (`Comparator/Compare.lean`, `definitionHoleMatches`), never by body,
and its walker follows only the constants of the hole's TYPE. So the solution may supply any
body of the right type and still pass. Here each pair (challenge module, solution module)
was built, both exported with lean4export (tag v4.34.0 under v4.34.1) naming the holes and
the theorems, and every hole's type and value compared as de Bruijn terms up to
alpha-equivalence (`holediff.py`: binder names ignored, binder info reported separately,
`mdata` dropped). Theorem types were compared the same way; theorem values differ by
construction (challenge `sorryAx`, solution proof). `sorryAx` references were counted in
every export: each challenge export has exactly one (its own placeholder), every solution
export has zero.

| config | holes | type | value | theorem type | note |
|---|---|---|---|---|---|
| EuclideanFiveColor | 1 (`ProperColoring`) | alpha-equal | alpha-equal | alpha-equal | the paper's headline (not 5-colourable); hole closed |
| SpinAngle | 3 (`row`, `column`, `phi`) | all alpha-equal | all alpha-equal | alpha-equal | |
| ElementaryPositivity | 1 (`elementaryPositivityWitness`) | alpha-equal, binder info differs (`(n : ℕ)` vs `{n : ℕ}`) | challenge is `sorryAx` BY DESIGN; solution is `PermutationWitness.mk …` | no theorem | the hole IS the statement (inhabit a Σ-type); the comparator checks its type, which is the content; binder-info difference invisible to it (Lean's `Expr` equality ignores binder annotations) |
| Naimark | 7 | all alpha-equal | all alpha-equal | alpha-equal | |
| KServer | 9 (incl. `MainStatement`) | all alpha-equal | all alpha-equal | alpha-equal | solution `main_theorem := fully_quantified_main` |
| Brenier | 12 (incl. `wasserstein2`, `cube`, `HasExactlyThreeAtoms`) | all alpha-equal | all alpha-equal | both alpha-equal | |
| Rokhlin | 4 (incl. `IsMixing`, `MixingOfOrder`) | all alpha-equal | all alpha-equal | alpha-equal | |
| OccupiedOverlap | 5 | all alpha-equal | 4 alpha-equal; `OccupiedOverlapEndpoint` differs in ONE subterm | alpha-equal | the subterm is an auxiliary proof constant (`Specht.hilbertEquiv._proof_1` vs `OccupiedOverlapEndpoint._proof_4`), both of type `Nat.AtLeastTwo (1 + 1)`; renaming it makes the values identical — proof irrelevance, closed |
| DefocusingNLS | 3 (`sobolevProduct`, `schrodingerFlow`, `sobolevOddPower`) | — | TEXTUAL only | — | solution closure is 2,415 modules (≈ 80 modules/hour here; not built). Source comparison: the challenge's `sobolevProduct` has `by sorry` INSIDE the definition (the ℓ²-membership proof of the subtype element) and the data component `fun n => weight * coefficient` is identical to the solution's; `sobolevOddPower` is textually identical; `schrodingerFlow` has the same `toFun` with a different membership-proof script and the structure's proof fields. These holes exist because the challenge cannot discharge membership proofs without the theory; by proof irrelevance the subtype elements agree when the data agree. Unverified at the elaborated level |

Outcome: eight of nine configs closed at the elaborated-term level with no body difference
beyond an auxiliary proof name; the ninth matches textually in its data components. No
statement-level discrepancy found. The one thing the comparator cannot see and this diff
can is binder info (ElementaryPositivity) — harmless there.
