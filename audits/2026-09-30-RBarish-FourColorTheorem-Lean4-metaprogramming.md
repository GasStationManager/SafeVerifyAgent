# RBarish-UTokyo/FourColorTheorem-Lean4 — metaprogramming and kernel-computation audit

Status: **concluded 2026-10-01.** Scope as stated below (statement rung, metaprogramming layer,
kernel controls, independent checkers on two certificates); the route walk and the remaining
631 certificates were not in scope and are listed in §5. Plain-language summary:
`SUMMARY-RBarish-FourColorTheorem-Lean4.md`.

Artifact: `RBarish-UTokyo/FourColorTheorem-Lean4` at `20fa34599f5189dd569d96dd22f306c94ab1c446`
(Palomar PALOMAR-2026-09-27-000005, trust `high`), Lean `v4.35.0-rc2`. Headline:
`FourColor.RealPlane.four_color : ∀ (m : Map), SimpleMap m → ColorableWith 4 m`, a port of
Gonthier's Coq `four_color` with `Challenge.lean` transcribing `realplane.v`. Written, per its
README, "essentially all of it" by an AI agent; "no human has reviewed the mathematics yet".

Scope of THIS report: the artifact's metaprogramming layer and its kernel-computation
surface, chosen from the 2026-09-30 target survey as the only AI-written formalization
found with a nontrivial elaboration-time engine. It is not a full audit: the statement rung is
done (`fct-intake/STATEMENT.md`, PAIRED and EXACT up to the declared specialisation to
Mathlib's `ℝ`); the route walk (compactness, discretization, unavoidability, Birkhoff) was
not. Intake files: `fct-intake/METAPROGRAMMING.md` (the read-through),
`fct-intake/CHECKERS.md` (what con-leche's and con-ron's proofs cover),
`fct-intake/controls/Controls.lean` (the kernel controls).

## 1. Verdict

**No defect. The engine's trust claim holds as stated and as run.** Every declaration the
meta code adds goes through `Lean.addDecl`, which only skips the kernel under
`debug.skipKernelTC`, and nothing in the artifact sets it. The compiled code produces data
only; every theorem about the data is `Eq.refl true`, `Eq.trans` with a kernel evaluation,
or an application of theorems proved in ordinary source. Corrupting a checkpoint or a
network literal was rejected by the kernel on this box (§3). Two certificates, one at ring
size 6 and one at ring size 14, were exported and accepted by all four checkers bundled in
the toolchain: `leanchecker`, con-leche (`--verified`), con-ron and nanoda.

## 2. What was read

| item | result |
|---|---|
| `FourColor/Engine/Gen.lean` (958 lines), end to end | 3 helpers add declarations, all through `addDecl` under `Elab.async=false`, `maxHeartbeats=0`, `maxRecDepth=100000`; data as `defnDecl` (`safe`, `abbrev` hints) built from raw literals ≤ 8 Kbit chunked with `Nat.lor`/`Nat.shiftLeft`; theorems as `thmDecl` (table in `METAPROGRAMMING.md` §2.3); the one `unsafe` is `evalExpr` for the native run; IO only for timings/verbosity; the three development commands (`#engine_def_natlist`, `#engine_def_net`, `#engine_load_net`) unused in proof modules |
| `FourColor/QuizData/Lit.lean` (233 lines) | constructor-only `Expr`s added with `addDecl`; the equalities to their definitions are `decide +kernel` theorems in ordinary source (`Quizzes1..4.lean`, `theQuizTree_eq`, `theDruleFork_eq`) |
| `ConfigSyntax`, `PartSyntax`, seven local/scoped tactic and term macros | constructor terms or ordinary tactic scripts; `hygiene false` only to name local hypotheses |
| `FourColor/Fast/PruneGen.lean` (README calls it meta) | ordinary computable code run by generators; no proof mentions it |
| absent in `FourColor/`, `Solution.lean`, `FourColor.lean` | `native_decide`, `implemented_by`, `extern`, `axiom`, `addDeclWithoutChecking`, `setEnv`, `skipKernelTC`, `ofReduceBool`; `sorry` only in `Challenge.lean` as Palomar requires |
| kernel-computation surface | 16,948 `decide +kernel` + 470 `decide`, nearly all in the generated presentation case trees (`Present/P5..P11`); `Nat` GMP extensions on ≤ 8 Kbit literals; the port avoids `pow`, `/`, `%`, `testBit`, big right shifts and keeps declarations ≤ ~1 GB / 30 s for the independent checkers |
| `Lean/AddDecl.lean` at v4.33.1 and v4.35.0-rc2 | `Kernel.Environment.addDecl` gates on `debug.skipKernelTC` and otherwise calls `addDeclCore` (the kernel) |
| `lakefile.toml`, `scripts/*.sh` | no `-D` options; only `pp.unicode.fun` and `autoImplicit=false` |

## 3. What was run

Built here: the engine closure (53 modules over a 962-olean Mathlib slice), `Nets6`, `Cf001`,
`Nets14`, `Cf110`. Engine logs: cf001 ring 6, 4 rounds, kernel 245 ms in all; Nets14
1,195,743 positions, 41+41 layers, 20.4 MB of masks in 2,500 chunks, routing 179 s, kernel
27 s in 31 parts; cf110 ring 14, 13 rounds, 7 checkpoint steps, 8 checkpoints (598 KB),
kernel 18.4 s, peak lean RSS ≈ 2.2 GB.

Controls, from `run_cmd` through the engine's own `addThm`/`addDataDef`:

| control | verdict |
|---|---|
| `cf001_init` rebuilt by hand under a new name, same literal | accepted |
| same theorem, `cf001_H0` with one bit flipped | rejected: `(kernel) application type mismatch` (the kernel evaluated `checkInitB` on the bad literal to `false`) |
| `tauNetC6` with one layer dropped, six position checks | rejected 6 of 6 |

Independent checkers (all four bundled in `leanprover/lean4:v4.35.0-rc2`, Palomar's 33 fixed
export targets added):

| export | records | leanchecker | con-leche `--verified` | con-ron | nanoda |
|---|---|---|---|---|---|
| `cf001_reducible` (83.1 MB) | 11,765 (3 axioms) | accepts, 22.6 s | accepted 11,761, 18.4 s | accepted 11,761, 21.9 s | rc 0, 5.0 s |
| `cf110_reducible` (122.9 MB) | 11,790 accepted (3 axioms) | accepts, 87.6 s, 1.1 GB | accepted 11,790, 720 s, 3.0 GB | accepted 11,790, 130 s, ≤ 3.6 GB | rc 0, 59 s, ≤ 3.6 GB |

`#print axioms` on both certificates: `[propext, Classical.choice, Quot.sound]`.

## 3.1 Why `addDecl`, and malformed `Nat`s

The commands add only `defnDecl` data (4 per ring size, `n + 2` per configuration) and
`thmDecl`s (`2r + 5` per ring size, `n + 6` per configuration): no `opaque`, `axiom` or
inductive, so the two 2026 `addDecl`-path kernel bugs (#14484, #14576) are out of shape as
well as out of version. The alternative, literals in source, was measured: a 4 Mbit decimal
numeral takes 651 s to elaborate on this box, so the engine's reason holds, though chunked
`nat_lit`s in generated source (the export's own shape) would have worked at the price of a
~50 MB file per ring size. Malformed `Nat` objects: the emitted values come from safe
arithmetic, the tree has no `unsafeCast`/`ptrAddrUnsafe`/`implemented_by`/`extern`, and
`leanexport` serialises every literal as a decimal string the external checkers reparse, so
only a literal's VALUE reaches them. Details in `fct-intake/METAPROGRAMMING.md` §7–8.

## 4. On "is con-ron also guaranteed consistent?"

Same headline theorem as con-leche (`model_exists`, `no_False_declaration`), one more
translation layer: a Lean twin of con-ron's data structures refines con-leche's pure checker
(Theorem 1), and the Aeneas-generated model of the Rust refines the twin (Theorem 2). Its own
bignum is inside the proof, unlike con-leche's reliance on GMP. Outside both proofs: the
driver and thread pool, the input reader's file handle; outside con-ron's additionally:
`rustc`, the Rust standard library, the allocator, and Aeneas/Charon, which the authors call
"not a high assurance verification effort". con-ron may decline where con-leche accepts,
never the reverse. Neither checks the statement. Table in `fct-intake/CHECKERS.md`.

## 5. Not done, and what would close it

- **Statement rung**: DONE. All 20 definitions and the theorem match Coq's one for one; the
  only deviation is Coq's `∀ Rmodel : Real.model` becoming `ℝ`, a specialisation the
  statement only uses through `<`. The synced block is byte-identical between
  `Challenge.lean` and the proof's `RealPlane.lean` (my diff).
- **Route walk**: `compactness_extension`, `discretize_to_hypermap`, `unavoidability`, the
  Birkhoff replay, `cReducible_of_checks`. Unread here; these are ordinary Lean proofs the
  kernel checks, so they concern faithfulness to Gonthier, not soundness.
- **Full closure through the checkers**: Palomar's pipeline did it (`leanchecker` 4,700 s,
  nanoda 1,300 s, con-ron 860 s per the README's final run); here two of 633 certificates.
  The full build is ~2.6 h CPU of certificates plus the presentations; disk on this box is
  the constraint (2.2 GB free after the slice).
- Whether the 633 configurations and the discharge rules are Gonthier's (generated by
  `scripts/gen_configurations.py` from `configurations.v`; docstrings quote the Coq text).

## 6. Reproduce

```
elan toolchain install leanprover/lean4:v4.35.0-rc2
cd FourColorTheorem-Lean4 && lake exe cache get   # or the 14-file slice in METAPROGRAMMING.md §6
lake build FourColor.Reducibility.Nets6 FourColor.Reducibility.Cf001
lake env lean audits/fct-intake/controls/Controls.lean
scripts/palomar_check.sh --jobs 4 FourColor.Reducibility.Cf001 FourColor.cf001_reducible
```
