# nasqret/semibase-order6 — statement rung and trust-surface scan

Status: **concluded 2026-10-04** at the scope below. Statement rung and metaprogramming /
trust-surface scan done; nothing built, no axiom listing, no independent checker, no route
walk (the artifact needs ~220 GB of RAM to build; this box has 16 GB and 2 GB of disk).

Artifact: `nasqret/semibase-order6` at `6f75ceacff8f54d0db1f0ab286c05f0f5301f90d`
(Zenodo DOI 10.5281/zenodo.23109225), Lean `v4.28.0`, no Mathlib; 7,398 Lean files,
5,853,308 lines. Headline: `SemiBase.order6_classification : ∀ e ∈ Catalogue.order6,
Classified e` (`SemiBase/Classification.lean:233`), with corollaries `order6_finitelyBased`,
`order6_nonfinitelyBased`, `Catalogue.order6_length`, `Catalogue.order6_ids`. Informal claim:
every semigroup of order six is finitely based except exactly four, `L`, `B₂¹`, `A₂ᵍ`, `A₂¹`
(Smallsemi [6,3843], [6,8564], [6,8878], [6,13747]), which are nonfinitely based (Lee–Li–Zhang
2012; Lee–Zhang 2015). Provenance per the README: all Lean code written by language-model
agents (Codex workers, a Claude referee) in a June–September 2026 campaign; people chose
targets and approved changes, wrote no proofs. BARE claim: no comparator, no independently
authored statement file. Intake: `semibase-intake/` (`REFERENCE-finite-basis.md`,
`STATEMENT.md`, `tools/`).

## 1. Verdict

**Statement: BARE, EXACT.** The formal statement says each of the 15,973 listed 6×6 tables
is the table of a semigroup, and every semigroup on `Fin 6` with that table is nonfinitely
based iff its id is one of the four, finitely based otherwise, with the textbook notions of
word, identity, satisfaction, derivation, basis and finite basability. No clause is weaker,
none stronger, nothing vacuous. Three deviations are recorded, none changing the result
(§3). **Trust surface: nothing to audit** beyond the kernel itself: one tactic macro, three
notations, one local simp attribute, 228 build-time `#eval IO.println` audit markers, and
36,588 `set_option`s of exactly three names (`maxHeartbeats`, `maxRecDepth`,
`linter.unusedSimpArgs`). No `elab`, `syntax`, `run_cmd`, `simproc`, `unsafe`,
`implemented_by`, `extern`, `native_decide`, `axiom`, `opaque`, `partial`, `sorry` or
`addDecl` anywhere, including the `research` library. **No defect found** at this scope.

## 2. What was checked

| item | how | result |
|---|---|---|
| Reference statement | written from Volkov 2001 / Lee–Zhang 2015 before the Lean was opened (`REFERENCE-finite-basis.md`; after the README, which quotes four Lean definitions — disclosed) | O1–O10, two catalogue facts K1–K2, hypothesis H1, claim C1–C3, twelve weakening modes W1–W12 |
| `Derives` (`SemigroupBasis/Equational.lean:31–43`) | every constructor read | seven: `fromBasis`, `refl`, `symm`, `trans`, `prepend`, `appendRight`, `subst` (any `σ : α → Word α`, all variables at once via `Word.bind`); exactly equational logic for semigroup words; `Derives.sound` (:50–67) proves soundness, so nothing extra is admitted |
| `Word`, `Semigroup`, `eval`, `Identity`, `SatisfiedBy`, `Models`, `BasisFor`, `FinitelyBased(Over)`, `NonfinitelyBased(Over)` | read in full | words are nonempty (`head` mandatory); `Semigroup` carries `assoc` as a field; `eval` is the left-bracketed product; `SatisfiedBy` is ∀ over every valuation `α → S`; `BasisFor` has both halves (models + derives every valid identity); alphabet `Nat` for both FB and NFB, NFB the negation of the same predicate |
| `Entry`, `entry`, `HasTable`, `Classified`, `AllClassified`, `nonfinitelyBasedIds` (`SemiBase/Statement.lean:1–80`) | read in full | `Classified e := (∃ G, HasTable G e.rows) ∧ ∀ G, HasTable G e.rows → (id ∈ ids → NFB G) ∧ (id ∉ ids → FB G)`; `eq_of_hasTable` shows ∃ and ∀ range over one structure; the four ids literal |
| The five theorems (`Classification.lean`) | read | main theorem keeps the existence conjunct; the two corollaries drop it (D2) and are derived from the main theorem |
| Catalogue data (`SemiBase/Catalogue/Order6/Part001..107.lean`) | **independent parse and computation** (`tools/indep_catalogue.py`): shape, entries, order, associativity, pairwise iso/anti-iso canonical form over 720 relabellings × {T, Tᵀ}, self-duality | all 15,973 tables exactly 6×6 with entries 0..5; lists exactly `S6_1..S6_15973` in order; all associative; pairwise non-isomorphic and non-anti-isomorphic; 3,312 self-dual (= the repo's `catalogue.json`); SHA-256 of `catalogue.json` matches `check_catalogue.py`'s pin |
| The four exceptional ids | semigroups built from presentations and located in the catalogue | `B₂¹` → 8564, `A₂¹` → 13747, `L` → 3843 independently; `A₂ᵍ` → 8878 only as a consistency check (built from the repo's own table) |
| Positive controls (`tools/controls.py`) | a relabelled transpose; a non-associative table | both flagged; the first non-associativity control was itself associative and was replaced (instrument note) |
| Trust surface | `scan_repo.py --sites` over all 7,398 files; keyword greps per library | table in §1; `decide +kernel` 31,975 (31,956 in the `SemiBase` census shards), plain `decide` 155,150, `rfl` ~100,000, concentrated in the generated adapters (`Order6FinalL5TransferV3`, 69,144 `rfl`) that the lakefile gives a 2 GB thread stack |
| Repository's own checks | `scripts/verify.sh` read; `check_catalogue.py` run (passes, 0.8 s) | provenance diff against the certified campaign commit, catalogue check, import-closure check, build, `#print axioms` on five theorems rejecting anything beyond the three standard axioms |

## 3. Deviations recorded

- **D1, inert.** `entry rows a b := (rows.getD a []).getD b 0`: Lean alone would zero-pad a
  short or missing row and ignore extra cells, and `check_catalogue.py` does not test shape.
  Not hit: every table is exactly 6×6 with entries in 0..5 (independent parse). An entry ≥ 6
  would make `HasTable` unsatisfiable rather than silently accepted.
- **D2.** The corollaries drop the existence conjunct; they are non-vacuous because they are
  derived from `order6_classification`, which keeps it.
- **D3.** "Every semigroup of order six" also needs the catalogue to be complete and the
  property to be invariant under isomorphism and anti-isomorphism; neither is in the Lean
  statement, and the README says so. The invariance is standard (a basis read backwards is a
  basis of the opposite semigroup; `Opposite.lean` is used in the proofs, not the statement);
  completeness follows from the recomputed pairwise inequivalence plus the published count
  15,973 (OEIS A001423), taken on trust.
- Row/column convention: rows are the left factor, matching GAP's `MultiplicationTable`
  (from the GAP manual, not run here). A transposition would be harmless, the property being
  anti-isomorphism invariant.

## 4. What this audit does not say

- Nothing was built, elaborated or `#print axioms`-ed here. `order6_length`, `order6_ids` and
  every census `decide +kernel` are taken as stated; the README's axiom claim and
  `provenance/FINAL-AUDIT.md`'s "PASS, 15,973 of 15,973" are not re-checked.
- No independent checker ran. The kernel-computation load is the largest we have seen
  (generated files needing tens of gigabytes each in Lean's own kernel, the largest ~50 GB);
  whether nanoda, con-ron or con-leche can replay those endpoints is an open question of
  resources, not of the artifact.
- No route walk. The nonfinitely-based endpoints may rest on literature inputs
  (`SemigroupBasis/Nonfinite/A2One/TrahtmanCriterion.lean:844`: "sole external input is
  Trahtman's exact one-step occurrence-order statement"); the headline has no hypotheses, so
  any such input must be proved inside Lean, and the axiom rung is what would show a gap.
- GAP was not run; `catalogue.json` was not regenerated.
- Lean core was read at v4.33.1, not the pinned v4.28.0, for `List.getD`/`List.range'`.
- Coverage: about ten of 7,398 files read; the trusted base in full except
  `Nonfinite.lean:121–243` (declaration list only).

## 5. Reproduce

```
git clone https://github.com/nasqret/semibase-order6 && cd semibase-order6
python3 scripts/check_catalogue.py
python3 <SafeVerifyAgent>/audits/scan_repo.py --sites .
python3 <SafeVerifyAgent>/audits/semibase-intake/tools/indep_catalogue.py   # ROOT at the top
python3 <SafeVerifyAgent>/audits/semibase-intake/tools/controls.py
./scripts/verify.sh      # the full build and axiom check: ~220 GB RAM, 20 h on 24 cores
```
