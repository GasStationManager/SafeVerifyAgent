# alpo.ge `lean.tar.gz` — claimed Lean proof of RH and GRH for Dirichlet L-functions

Status: **ESCALATE, 2026-11-20. The claim is neither confirmed nor refuted.** The rung
that decides it did not run: the headline was **not built**, so there is no
`#print axioms` for it and no independent checker saw it. Every one of the 175,187
project files is in the import closure of `Main.lean`; a build is at least ~12 CPU-days
and this box has 4 cores and 16 GB. What ran (statement rung, trust-surface scans over
all source, dependency cone, a 174-module compile sample) found **no defect**.

Not run, in order of what they would settle: full build; `#print axioms` on the five
headline theorems; `lean4export` + leanchecker / con-leche / con-ron / nanoda; route
walk beyond the top three levels; no-supplier and junk-value passes; any reading of the
mathematics. The argument was not reconstructed, so nothing here says *why* the
theorem would be true.

A second pass on metaprogramming, big integers and kernel computation is in
[`2026-11-20-alpo-ge-riemann-hypothesis-kernel-surface.md`](2026-11-20-alpo-ge-riemann-hypothesis-kernel-surface.md).

Artifact: `https://alpo.ge/lean.tar.gz.part01 … part14`, linked from footnote 1 of
`https://alpo.ge/remark.pdf`, fetched 2026-11-20. Concatenated archive SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (per-part sums in
`rh-intake/SHA256SUMS`). 239 MB compressed, 1.03 GB unpacked: 175,187 `.lean` files,
17,374,215 lines, 1,066,087 declarations (784,092 `theorem`, 212,819 `def`), plus
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`. Lean `v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. No README, no git history, no docstring and
no comment in any file, all mtimes zeroed. Provenance per the PDF: written with an AI
model; the PDF supplies a 20-item timeline and no written proof. BARE claim: no
comparator config and no independently authored statement file. Intake: `rh-intake/`.

## 1. Verdict

**Statement: BARE, EXACT.** `Main.lean` (12 lines) states five theorems.
`riemannHypothesis : RiemannHypothesis` uses Mathlib's own definition
(`Mathlib.NumberTheory.LSeries.RiemannZeta`, confirmed by module lookup in the built
environment, not by name). The other four are typed by `Statements.lean` (16 lines,
imports only `Mathlib`, root namespace), so no project definition can sit inside them:

| theorem | says | reading |
|---|---|---|
| `riemannZeta_eq_zero_re` | `RiemannZetaZerosOnLine` | definitionally Mathlib's `RiemannHypothesis` (`rfl` checked) |
| `LFunction_ne_zero_of_half_lt_re` | ∀ N≠0, χ mod N, Re s > 1/2, (χ ≠ 1 ∨ s ≠ 1) → L(χ,s) ≠ 0 | GRH in half-plane form, all characters incl. imprimitive; the one excluded point is the pole of the trivial character, where `LFunction` is a junk value |
| `LFunction_eq_zero_re` | zeros of L(χ,·) in 0 < Re s < 1 have Re s = 1/2, all χ | correct for imprimitive χ too: the extra Euler factors vanish only on Re s = 0 |
| `LFunction_eq_zero_re_of_isPrimitive` | same, primitive χ | implied by the previous |

No clause is weakened and nothing is vacuous. The reference was not written before
opening the Lean (the statement is standard and the comparison is against Mathlib's
own); disclosed. Scope note: the PDF says "Generalized Riemann Hypothesis"; what is
stated is GRH for **Dirichlet** L-functions, not Dedekind zeta or automorphic
L-functions.

**Trust surface: small and read in full; nothing found.** Over comment-stripped
source: zero `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`,
`implemented_by`, `extern`, `skipKernelTC`, `debug.*`, `#eval`, `initialize`,
`simproc`, `syntax`. What exists:

- 5 `run_cmd` (`BuildAid/D1–D5`), each adding a name prefix to
  `LibrarySuggestions.nameDenyListExt`. Affects premise selection, adds no declaration.
- 4 `elab`: `kexactB` (assigns the goal an elaborated term without a type check),
  `kcopy` / `#kcopy_probe` (rebuilds a term structure-field by field using
  `Expr.proj`), and `cpt_copy_thms` (copies a cone of definitions and theorems under
  renamed constants through `addDecl`). `addDecl` is kernel-checked and the tactic
  ones produce terms the kernel checks when the enclosing theorem is added, so none
  of them can admit anything a sound kernel would refuse; all three are places an
  elaborator/kernel disagreement would surface first. Used in 56 files.
- 87 tactic/term `macro`s in 64 files, all expanding to ordinary tactics; 44 inline
  `run_tac` blocks (`revertAll`, a goal assigned from a named hypothesis).
- 88,139 `set_option`s; none disables checking. Notable: `maxHeartbeats` up to
  8,000,000, `backward.isDefEq.respectTransparency false` (1,844),
  `allowUnsafeReducibility true` (36), one `Elab.async`.
- No project declaration shadows `RiemannHypothesis`, `riemannZeta` or
  `DirichletCharacter.LFunction` at root; two namespaced `LFunction` defs exist and
  cannot reach `Statements.lean`.

**Supply chain: clean.** The pinned Mathlib commit carries upstream tag `v4.33.1`
("chore: bump toolchain to v4.33.1"), so it is not a fork-only object fetched by
hash; the other eight packages in the manifest equal Mathlib's own manifest at that
commit; `lake` did not rewrite the manifest; the toolchain came from
`releases.lean-lang.org`.

**Compile sample: 174 of 174 built.** With the Mathlib cache, `lake build` on a
seeded random sample (60 of the 5,927 leaf modules, and 12 non-leaf targets with
closure ≤ 40) built all 60 leaves and 6 of the 12 targets with their closures before
a 25-minute limit: 174 modules, zero errors, warnings only (linters, deprecations).
Median 6.0 s per module, maximum 183 s. This is 0.1% of the modules, all near the
bottom of a graph of depth 203; it shows the source is real Lean against the pinned
Mathlib and bounds the *leaf* failure rate below ~5% (95%), and says nothing about
the 126,000 modules at depth ≥ 10.

## 2. What the top of the route looks like

Read with `sed -n`, three levels down:

- `Main.riemannHypothesis := rhOfAll`; `rhOfAll := Formalism.VW.rh_of_every allChi`
  (`Supplements/Kernels/MainTheorems.lean`); `allChi :=
  UpperTheory.FinalTheorems.everyCharacter`.
- `UpperTheory.EveryCharacter` is the half-plane statement above, word for word.
  `rh_of_every`, `critLine`, `Claim.strip`, `Claim.zeta` derive the other four from
  it by the functional equation, non-vanishing of the gamma factor on Re s > 0, and
  reduction to the primitive character. These are short, standard, and read correct.
- `everyCharacter` is `everyCharacter_of_row` applied to
  `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`, through
  `every_character_of_literature_of_vWin`, which takes a structure
  `OpenLiteratureStatements` (three fields: two of the same type `One.M.Row`, both
  filled with the same term, and `RecTExists`, a local Langlands correspondence for
  GL_n with its laws) and derives some sixty named "literature" inputs from it
  (Kawamata–Viehweg, arithmetic Hilbert–Samuel, toroidal compactification,
  Deligne–Ribet, …).

The artifact carries results as named `Prop`s passed as hypotheses, the convention
of playbook lesson 4. The headline itself takes none, so if it compiles axiom-free
every such input is supplied on the route; whether intermediate theorems off the
route are vacuous was not examined.

## 3. Denominators

| | whole artifact | cone of `riemannHypothesis` |
|---|---|---|
| files | 175,187 | 175,187 (import closure, `tools/closure.py`) |
| declarations | 1,066,087 | 905,410 (84.9%, `cone.py`, name-level) |
| read line by line | — | ~10 files (top of route, the three `elab` files, `BuildAid`) |
| compiled here | 174 modules | 174 modules |
| kernel-checked headline | no | no |

Kernel-exposure census (`rh-intake/KERNEL-RISK-summary.txt`), unexamined: 20,029
theorems proved by bare `rfl`, 65,833 more closed by `rfl`, 8,185 `decide` sites, 34
files with `decide +kernel`, 120 `inductive`s.

## 4. Escalations

- **E1 (decisive).** Build the artifact on adequate hardware, run `#print axioms` on
  the five theorems in `Main.lean`, export and replay through con-leche `--verified`,
  con-ron and nanoda. Until that is done by someone other than the author, the claim
  rests on the author's word that it compiles.
- **E2.** If E1 passes: a proof of this theorem with no human-readable argument is
  exactly the case the README describes, the ensemble says true and nobody can say
  why. The three custom elaborators, the 85,862 `rfl`-closed theorems and the
  `decide +kernel` sites are where a checker bug would be exploited; they should go
  to the independent kernels first.
- **E3.** The route passes through formal proofs of local Langlands for GL_n,
  local–global compatibility and a long list of deep published theorems, none of
  which exist in Mathlib. Each is an independently checkable intermediate claim and
  a natural place to start reading; a statement that is weaker than its name would
  not make the headline false, but it would show where the argument's weight is not.

## 5. Instrument notes

- `cone.py` reported two orphan files, `HypothesesZ'.lean` and `HypothesesZ''.lean`;
  both are imported (`FinOrderOfKills.lean:3`, `BirthTop.lean:62`). Its import
  pattern does not match module names ending in `'`. `tools/closure.py` handles
  them and finds no orphan but `Main`. Not fixed in this pass.
- `scan_repo.py` took 8 min and `scan_kernel_risk.py` 14 min on 17.4 M lines;
  `cone.py` 25 min and several GB of RAM.
- Auditor: one Claude-family agent, one pass, no cross-model reading.

## 6. Reproduce

```bash
cat lean.tar.gz.part* > lean.tar.gz && sha256sum lean.tar.gz   # 9631b4f0…
tar -xzf lean.tar.gz && R=lean
python3 audits/scan_repo.py $R --md SCAN.md
python3 audits/scan_kernel_risk.py $R -o kr
python3 audits/cone.py $R/src --seed riemannHypothesis -o CONE.csv
python3 audits/rh-intake/tools/closure.py $R/src closure.txt
python3 audits/rh-intake/tools/graph.py $R/src sample.json      # seed 20261120
cd $R && lake exe cache get && lake build Statements
lake env lean ../audits/rh-intake/tools/stmt_probe.lean
LEAN_NUM_THREADS=1 lake build $(python3 -c "import json;d=json.load(open('../sample.json'));print(' '.join(d['leaves']+d['small'][:12]))")
```
