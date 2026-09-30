# Four Color Theorem port: metaprogramming read-through

Artifact: `RBarish-UTokyo/FourColorTheorem-Lean4` at `20fa345` (Palomar entry
PALOMAR-2026-09-27-000005, trust `high`), Lean `v4.35.0-rc2`, Mathlib `v4.35.0-rc2`.
Question asked: does any elaboration-time code let a value into the proof that the
kernel does not check? The README's own claim is the thing under test: "Nothing in this
file is trusted ... a wrong literal only makes a kernel check fail."

Verdict: **the claim holds.** Every declaration the meta code creates goes through
`Lean.addDecl`, which is kernel checking unless `debug.skipKernelTC` is set, and nothing in
the repository sets it. The compiled code only produces DATA (Nat literals, constructor
terms); every theorem about that data is a `thmDecl` whose proof is `Eq.refl true`,
`Eq.trans` of a proved equation with `Eq.refl true`, or an application of ordinary theorems
proved in ordinary source. Details and the checks that support each point follow.

## 1. Inventory

Comment-stripped grep for `elab|macro|macro_rules|syntax|run_cmd|initialize|simproc|unsafe|
implemented_by|extern|addDecl|native_decide|ofReduceBool` over `FourColor/`, `Challenge.lean`,
`Solution.lean`, `FourColor.lean`:

| file | what | lines |
|---|---|---|
| `FourColor/Engine/Gen.lean` | `#engine_nets`, `#engine_certify`, three development commands; `addDecl`, `unsafe evalExpr` | 958 |
| `FourColor/QuizData/Lit.lean` | `#quizdata_quizzes/_blocks/_tree/_drules`, `#quizdata_print_checks`; `addDecl` | 233 |
| `FourColor/CfMap/Prog.lean` | `ConfigSyntax`: `Cprog`/`Config`/`Config*` term macros over a `cpitem` syntax category | ~60 |
| `FourColor/Part/Basic.lean` | `PartSyntax`: `fcprange`/`fcpart` categories and their expansions | ~130 |
| `FourColor/RedPart/Zipper.lean` | scoped tactic macros `hnorm`, `wrap_tac`, `arity_tac`, `arity_wrap_tac` | ~50 |
| `FourColor/Chromogram.lean` | local tactic macros `bal_tac`, `pg_color_tac` | ~25 |
| `FourColor/Fast/{Hubcap,Part,RedPart}.lean`, `Present/Tree.lean` | local term macros `bif%`, `mp%` | 4 × 3 |

Only `Gen.lean` imports `Lean`; the other three elab-monad files reach `Lean.Elab` through
Mathlib. `FourColor/Fast/PruneGen.lean`, which the README lists with the meta modules, is
ordinary computable code run natively by the generators (`#eval`, `lean --run`); it adds
nothing to the environment and no proof mentions it.

Absent everywhere (grep over the same files): `native_decide`, `implemented_by`, `extern`,
`axiom`, `addDeclWithoutChecking`, `Environment.add`, `setEnv`, `skipKernelTC`,
`ofReduceBool`, `opaque` declarations from meta code, `unsafe` outside the one `evalExpr`
wrapper. `set_option` values in the whole tree: `maxRecDepth 8000` (20), `8192` (1),
`hygiene false` (4, the tactic macros that name local hypotheses), `linter.dupNamespace
false` (1). `lakefile.toml` sets only `pp.unicode.fun` and `autoImplicit=false`; no script
passes `-D` options to `lean`.

## 2. `Engine/Gen.lean`, read end to end

### 2.1 The one door into the environment

Three helpers add declarations, and all three call `addDeclK`, which is
`withOptions kernelOpts (addDecl decl)`:

- `addDataDef name type value`: `Declaration.defnDecl` with `safety := .safe`,
  `hints := .abbrev`, then `modifyEnv (addNoncomputable · name)`. The value is a literal
  expression (§2.2). `addNoncomputable` is an environment-extension marker that stops the
  compiler from compiling it; it does not touch the kernel environment.
- `addLitDef`: the same `defnDecl` plus `compileDecl` (used only by the development
  commands, §2.5).
- `addThm name type value`: `Declaration.thmDecl`.

`kernelOpts` sets `Elab.async := false`, `maxHeartbeats := 0`, `maxRecDepth := 100000`. None
of the three weakens checking: async only moves the same kernel check to a task, the
heartbeat limit is a cancellation budget, and `maxRecDepth` is passed to the kernel as its
stack budget. In the toolchain's own `Lean/AddDecl.lean` (checked at v4.33.1 and v4.35.0-rc2,
identical gate):

```
def Kernel.Environment.addDecl (env : Environment) (opts : Options) (decl : Declaration) ... :=
  if debug.skipKernelTC.get opts then addDeclWithoutChecking env decl
  else addDeclCore env (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize decl cancelTk?
```

`debug.skipKernelTC` appears nowhere in the artifact (sources, `lakefile.toml`, `scripts/`,
README).

### 2.2 What the data definitions contain

`mkChunkedNat n`: a raw `Nat` literal when `n < 2^8192`, otherwise a balanced tree of
`Nat.lor`/`Nat.shiftLeft` applications over raw literals of at most 8192 bits. `mkNatListLit`,
`mkNetLit`, `mkNetCLit`, `mkCpstepLit`, `mkCprogLit` build `List.cons`/`List.nil`/`Prod.mk`/
constructor terms over those. So a data definition's value is a closed term of constructors,
`Nat.lor`, `Nat.shiftLeft` and literals; the kernel type-checks it against the declared type
(`NetC`, `Net`, `Cprog`, `List Nat`) when the definition is added.

`natOfExpr?`/`netOfConst` read such values BACK from the environment for the next command
(`#engine_certify` reads `tauNet<r>`/`cnvNet<r>` this way). This is the only flow from the
environment into the generator, and it only decides which literals the generator emits next;
the kernel checks those against the theorems below regardless.

### 2.3 What the theorems say and how they are proved

`#engine_nets r` adds, per kind ∈ {tau, cnv}:

| declaration | type | proof term |
|---|---|---|
| `<kind>NetOK<r>` | `netCOK 16 <kind>NetC<r> = true` | `Eq.refl true` (kernel evaluation) |
| `<kind>Layers<r>` | `<kind>Net<r>.all layerOK = true` | `Eq.refl true` |
| `<kind>Part<r>_<p>` | `<kind>CheckAt r <kind>Net<r> p = true` | `Eq.refl true` |
| `<kind>Spec<r>` | `TauSpec r tauNet<r>` / `CnvSpec r cnvNet<r>` | `<kind>Spec_of_check r net hr (<kind>Check_of_parts r net Layers (allFrom_cons ... allFrom_nil))`, with `hr : 1 ≤ r` (resp. `2 ≤ r`) by `mkDecideProof` |

`#engine_certify cfNNN` adds:

| declaration | type | proof term |
|---|---|---|
| `cfNNN_ctr` | `contractProg cfNNN = some cfNNN_cpc` | `Eq.refl (some cfNNN_cpc)` |
| `cfNNN_rc` | `cprsize cfNNN_cpc = r` | `Eq.refl r` |
| `cfNNN_init` | `checkInit r cnvNet<r> cfNNN.cfprog cfNNN_H0 = true` | `Eq.trans (checkInit_eq_checkInitB ...) (Eq.refl true)` |
| `cfNNN_step<i>` | `checkStep r tauNet<r> k H<i> H<i+1> = true` | `Eq.trans (checkStep_eq_checkStepB ...) (Eq.refl true)` |
| `cfNNN_final` | `checkFinal r cnvNet<r> cfNNN_cpc H<n> = true` | `Eq.trans (checkFinal_eq_checkFinalB ...) (Eq.refl true)` |
| `cfNNN_reach` | `ReachN r tauNet<r> (expand r H0) (expand r Hn)` | `ReachN.trans`/`ReachN.refl` over `reachN_of_checkStep` applied to the step theorems |
| `cfNNN_reducible` | the conclusion of `cfreducible_of_engine` instantiated | `cfreducible_of_engine` applied by binder name; `hr` by `Eq.refl`, `hr2` by `mkDecideProof` |

Every proof term is therefore either a kernel evaluation (`Eq.refl`, `decide`) or an
application of a theorem that lives in ordinary Lean source (`Engine/NetSplit.lean`,
`Engine/CheckChunk.lean`, `Engine/Check.lean`, `CfReducible.lean`), which the kernel checked
when that module was compiled. The generator never constructs a proof of anything by hand
beyond these applications, so a bug in it can only produce a term the kernel rejects.

Two name-resolution details, because they are where a generator could silently prove the
wrong thing:

- The configuration is resolved with `realizeGlobalConstNoOverloadWithInfo cfId`, so
  `cf001_reducible` is about the constant `FourColor.cf001`, not a string.
- The final theorem's TYPE is read off `cfreducible_of_engine` (`applyByName` returns the
  instantiated conclusion `CfReducible cfNNN`), and `cfreducible_of_engine` is an ordinary
  `theorem` in `CfReducible.lean` (`CfReducible cf := (cfmap cf).pointee.CReducible (cfring cf)
  (cfcontract cf)`, proved from `cReducible_of_checks` and `contractProg_spec`). If the binder
  names drifted, `applyByName` throws; if a hypothesis type drifted, the kernel rejects the
  application.

The aggregator `FourColor/Reducibility.lean` imports the 633 `CfNNN` modules and proves
`theReducibility` from the `cfNNN_reducible` constants by name, again kernel-checked.

### 2.4 Compiled code, `unsafe`, IO, determinism

`evalClosed` is the single `unsafe` site: `unsafe evalExpr α ty e`, used to run
`Config.cfprog cfNNN` and `contractProg cfNNN` natively and to obtain `Cprog` values. The
results only feed `mkCprogLit`/the round iteration; the theorems `cfNNN_ctr`/`cfNNN_rc` then
have the kernel recompute `contractProg cfNNN` and `cprsize` itself. The Beneš routing and
the Kempe rounds (`ringNets`, `dpP1`, `round`, `covered`) run in the interpreter/compiled
code; their outputs are the literals the kernel checks.

IO in the commands: `IO.monoMsNow` (timings), `IO.getEnv "ENGINE_GEN_VERBOSE"` (log
verbosity). Neither affects a declaration. The docstring's determinism claim ("the output
depends only on the ring size and on the configuration") is consistent with the code: no
randomness, no file reads in the two proof commands.

### 2.5 The development commands

`#engine_def_natlist`, `#engine_def_net` (evaluate a term, define its literal) and
`#engine_load_net` (read a network from a text file) would let a file's contents into the
environment as a DEFINITION, still kernel-typed and still only data. They are used in no
proof module: grep for them outside `Gen.lean` finds only docstring mentions. The 13
`Reducibility/Nets<r>.lean` files contain exactly `#engine_nets r` and the 633
`Reducibility/CfNNN.lean` files exactly `#engine_certify cfNNN` (both generated by
`scripts/build_reducibility.sh gen`).

## 3. `QuizData/Lit.lean`

Same shape, simpler. `addLiteralDef` builds a `defnDecl` (`safety := .safe`, regular
hints) from constructor-only `Expr`s (`quizExpr`, `quizTreeExpr`, `partExpr`, `listExpr`),
calls `addDecl`, then `enableRealizationsForConst`, `addDocStringCore`, `compileDecls`.
The values are computed natively (`cfquiz cf`, `cfquizTree theConfigs`, `pickSourceDrules`),
and the theorems relating them to their definitions are in ordinary source:
`cfquiz_cfNNN : cfquiz cfNNN = qzNNN := cfquiz_eq_of_cfquizCheck (i := c) (by decide +kernel)`
in `Quizzes1..4.lean` (written once by `#quizdata_print_checks`, which only prints), and
`theQuizTree_eq`, `theDruleFork_eq`. `register_simp_attr quizdata_cfquiz` is a simp set.

## 4. The macros

- `ConfigSyntax` (`Cprog`, `Config`, `Config*`) and `PartSyntax` (`$[...]`, ranges) expand
  to constructor terms (`Cpstep.R n`, `Prange.pr67`, `Part.cons ...`) through `MacroM`, with
  hard errors on anything unexpected. They define how the 633 configurations and the
  discharge-rule parts are WRITTEN; a wrong expansion would make the port prove reducibility
  of a different configuration set, which is a route question (are these Gonthier's 633?),
  not a soundness one. `scripts/gen_configurations.py` translates Coq's `configurations.v`
  into explicit structure literals and the README says each docstring quotes the Coq text.
- `bif%` (three copies) and `mp%` expand to `Bool.rec`/`PartRel.rec` so the kernel-fast
  checks avoid `ite`; each file proves the corresponding equation (`bool_rec_eq_ite`,
  `bool_rec_false_eq_and`) beside it.
- The tactic macros (`bal_tac`, `pg_color_tac`, `hnorm`, `wrap_tac`, `arity_tac`,
  `arity_wrap_tac`) expand to `simp only`/`rw`/`cases`/`refine` scripts. `hygiene false` lets
  them name `h1`, `h2`, `geoG` from the calling context. Whatever they produce is elaborated
  and kernel-checked like a hand-written proof.

## 5. What the kernel itself is trusted for here

- `Nat` GMP extensions: `Nat.lor`, `Nat.land`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`,
  `Nat.add/sub/mul`, `Nat.decEq/ble` on literals up to 8 Kbit each. The port avoids `Nat.pow`,
  `/`, `%`, `Nat.testBit` and big right shifts on big operands, and keeps each declaration
  under ~1 GB / 30 s, for the independent checkers' sake (README §Kernel time).
- `decide +kernel` (16,948 sites, 470 plain `decide`), almost all in the generated
  presentation case trees `Present/P5..P11/*.lean` (P9/C07 alone 846). These are
  `Decidable.decide` reductions of the `check*Fast` functions on literal parts and pruned
  quiz trees, proved equal to the faithful checks in `FourColor/Fast/`.

Palomar's pipeline replays the export with `leanchecker`, nanoda and con-ron (README
§Building), so the kernel-extension trust is spread over three implementations; con-leche is
also bundled in the `v4.35.0-rc2` toolchain (`~/.elan/toolchains/.../bin`: `con-leche`,
`con-ron`, `nanoda_bin`, `leanchecker`, `leanchecker-paranoid`, `lean4lean`, `leanexport`).

## 6. Live check: the engine on this box

Built here (16 GB box, Lean `v4.35.0-rc2`, Mathlib cache restricted to the 962 oleans the
engine closure imports): `FourColor.Engine.Gen`, `CfReducible`, `Reducibility.Nets6` and
`Reducibility.Cf001` in 1 m 40 s wall (1,277 lake jobs). The engine's own log for the
certificate:

```
FourColor.cf001: ring 6, 4 rounds, 1 checkpoint steps of ≤ 1000 rounds, 2 checkpoints (25 bytes)
FourColor.cf001: native 33 ms; kernel (ms): ctr 27 init 115 step0 58 final 44 reducible 1
```

`#print axioms FourColor.cf001_reducible` → `[propext, Classical.choice, Quot.sound]`;
`#check` → `cf001_reducible : CfReducible cf001`.

### 6.1 Controls (`fct-intake/controls/Controls.lean`)

Run with `lake env lean` against the built `Cf001` module, calling the engine's own
`addThm`/`addDataDef` from `run_cmd`:

| control | what was added | kernel verdict |
|---|---|---|
| positive | `cf001_init`'s statement and proof term rebuilt by hand under a new name, same literal `cf001_H0` | accepted |
| negative 1 | the same theorem about `H0bad`, `cf001_H0` with bit 0 of its last nonzero entry flipped | **rejected**: `(kernel) application type mismatch` — `Eq.refl true : true = true` offered where `checkInitB 6 16 11 cnvNetC6 cf001.cfprog H0bad = true` was required, i.e. the kernel evaluated the check on the bad literal to `false` |
| negative 2 | `tauNetC6` with its last layer dropped (14 of 15), then the six `tauCheckAt 6 net p = true` position theorems by `Eq.refl true` | **rejected, 6 of 6** |

So "a wrong literal only makes a kernel check fail" is what happens, not just what the
docstring says, on both literal kinds the engine emits (checkpoints and network masks).

### 6.2 Independent checkers on the certificate

`leanexport FourColor.Reducibility.Cf001 -- <Palomar's 33 fixed targets> FourColor.cf001_reducible`
(9.7 s) → 83.1 MB NDJSON, 11,765 declaration records (7,736 `thm`, 3,635 `def`, 4 `quot`,
2 `opaque`, 3 `axiom`: `propext`, `Quot.sound`, `Classical.choice`). Replayed with the four
checkers bundled in the toolchain:

| checker | mode | verdict | wall |
|---|---|---|---|
| `leanchecker` | `--from-export` | "Lean default kernel accepts the solution", rc 0 | 22.6 s |
| `con-leche` | `--verified` | "accepted 11761 declarations (--verified)", rc 0 | 18.4 s |
| `con-ron` | default (`--verified`) | "accepted 11761 declarations (--verified)", rc 0 | 21.9 s |
| `nanoda_bin` | Palomar's config (nat + string extensions, 4 threads) | rc 0 | 5.0 s |

(11,761 = 11,765 records minus the 4 `quot` records, which con-leche/con-ron install as
their own quotient block; the Lean.Syntax inductive is "modelled in-process".)
This is the evidence-ceiling kernel half for ONE certificate of 633. It is the ring-6 case;
§6.3 is the ring-14 case, the one the README prices at 3.5 GB of kernel memory before the
per-position split.

### 6.3 Ring 14

`lake build FourColor.Reducibility.Nets14 FourColor.Reducibility.Cf110` (ENGINE_GEN_VERBOSE=1):

```
ring 14: 1195743 positions; tauNet14: 41 layers, cnvNet14: 41 layers; 20415771 bytes of masks, in 2500 chunks of 65536 bits
ring 14: routing 179092 ms; kernel (ms): tauNetOK14 259 cnvNetOK14 195 tauSpec14 (in 15 parts) 16679 cnvSpec14 (in 14 parts) 10102
FourColor.cf110: ring 14, 13 rounds, 7 checkpoint steps of ≤ 2 rounds, 8 checkpoints (597867 bytes)
FourColor.cf110: native 1849 ms; kernel (ms): ctr 73 init 1253 step0 6340 step1 1822 step2 2001 step3 1908 step4 1744 step5 1804 step6 945 final 520 reducible 2
```

Nets14 209 s wall (routing dominates; peak lean RSS 2.2 GB), Cf110 22 s. Export of
`FourColor.cf110_reducible` with the same targets: 46.9 s, 122.9 MB.

| checker | verdict | wall | peak RSS |
|---|---|---|---|
| `leanchecker --from-export` | "Lean default kernel accepts the solution", rc 0 | 87.6 s | 1.1 GB |
| `con-leche --verified` | "accepted 11790 declarations (--verified)", rc 0 | 720 s | 3.0 GB |
| `con-ron` | "accepted 11790 declarations (--verified)", rc 0 | 130 s | ≤ 3.6 GB |
| `nanoda_bin` (4 threads) | rc 0 | 59 s | ≤ 3.6 GB |

(Peak RSS was read from `RUSAGE_CHILDREN`, which is the maximum over all children run so
far, so the last two are upper bounds.)

`#print axioms FourColor.cf110_reducible` was not printed separately; the export's axiom
records are the same three. con-leche is the slow one on the big-literal declarations (a
4-core box; Palomar does not run it), and its 720 s here against con-ron's is the price
difference the README's design rules were written around.

Files: `scratchpad/fct/cf001/`, `scratchpad/fct/cf110/` (exports not kept in the repo;
checker logs are one line each and are quoted above).
