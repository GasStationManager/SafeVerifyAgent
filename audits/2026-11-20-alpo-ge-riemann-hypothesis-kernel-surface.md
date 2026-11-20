# alpo.ge `lean.tar.gz` — metaprogramming, big integers and kernel computation

Second pass on the artifact of
[`2026-11-20-alpo-ge-riemann-hypothesis.md`](2026-11-20-alpo-ge-riemann-hypothesis.md)
(same archive, SHA-256 `9631b4f0…49c7fc`). Compilation is left to others; this pass reads
the parts where a compile would tell a reader nothing: custom elaborators, kernel-evaluated
computations and large literals. Source reading plus independent recomputation; **nothing
here was elaborated**, so "the kernel is asked to decide X" means the source asks it to.

Status: **no defect found at this scope.** Every arithmetic fact the artifact hands to
the kernel that this pass located was recomputed outside Lean and holds. The custom
metaprogramming cannot add an unchecked declaration. One escalation opened and closed
(§4). The overall verdict of the first report is unchanged: ESCALATE, headline not built.

Not done: 5 of 34 `decide +kernel` files were skimmed and not recomputed (§2.4); the
8,185 plain `decide` sites and 85,862 `rfl`-closed theorems were not ranked by workload;
`norm_num` certificates were not re-derived.

## 1. Metaprogramming

Complete inventory, each site read: 5 `run_cmd`, 4 `elab`, 87 `macro`, 32 inline `run_tac`,
220 `open private`. No `syntax`, `macro_rules`, `elab_rules`, `initialize`, `simproc`,
`#eval`, attribute handlers, or environment extensions of the artifact's own. Attributes
used are Mathlib's (`instance`, `simp`, `reducible`, `reassoc`, `ext`, `irreducible`,
`simps`, `to_additive`, `fun_prop`, `elab_as_elim`, …); none of `implemented_by`,
`extern`, `csimp`, `export`, `computed_field`.

| site | what it does | can it admit something unchecked? |
|---|---|---|
| `BuildAid/D1–D5` `run_cmd modifyEnv` | adds five name prefixes to `LibrarySuggestions.nameDenyListExt` | no: touches a premise-selection extension, adds no constant |
| `kexactB e` (`…/HeckeNonvanishing/Imports.lean`), 234 uses in 50 files, mostly through local term macros `kc%`, `kq%`, `kd%` | elaborates `e` with no expected type and assigns it to the goal **without** `isDefEq` against the goal type | no: a mismatch is an ill-typed proof term, refused when the enclosing declaration reaches the kernel. It moves the whole type check from the elaborator to the kernel |
| `kcopy t` (`…/NumberFieldFamilies/OwnStruct.lean`), 5 uses | rebuilds `t` at the goal type by recursion on Π-types and on structures in namespace `Formalism` (plus `And`, `Prod`, `PProd`, `Sigma`, `PSigma`, `Subtype`, `Iff`), field by field with raw `Expr.proj S i e`, `S` taken from the *target* | no: same reason. The kernel's projection rule must find `e`'s type to be an application of `S` |
| `#kcopy_probe` | diagnostic twin of `kcopy` using `Kernel.isDefEq`; logs, adds nothing | no |
| `cpt_copy_thms` (`…/CutCptCopy.lean`, run once at `CutMainCpt.lean:945` under `maxHeartbeats 0`) | walks the dependency cone of six named theorems, and re-adds every definition and theorem that depends on three "special" constants with those constants replaced by three others and `Cpt` appended to the name | no: uses `addDecl`, which type-checks each copy; no `debug.skipKernelTC` exists anywhere. The copies never appear in source, so they exist only in the built `.olean` |
| 32 `run_tac` | 28 are `g.revertAll` before an `exact`; `ExistsGIs.lean:82` assigns the goal the hypothesis named `h`; `FramesTildeGammaValues.lean:71–82` builds a `Subsingleton.elim` rewrite | no |
| 87 `macro`s | tactic abbreviations; none shadows a built-in keyword or term | no |
| `open private` | reaches private Mathlib lemmas | no |

**What `kexactB` is for.** Read at its heaviest users (`ExistsRow.lean`, 74 uses;
`StandardReadingTransportAndExtensionTrans.lean`, 62): the artifact carries the same
data in several structurally identical records and moves between them with
`HEq.trans y.H x.H`, `eq_of_heq (kc% hF)`, `kc% (HEq.refl kKs)`. The two types are
expected to be definitionally equal but the elaborator cannot show it in budget, so the
term is passed through unverified and the kernel is left to unfold both sides. Leaf files
also re-declare shared definitions locally as `@[reducible] noncomputable def`, which is
where the duplicate records come from.

**Consequence for an auditor.** These ~240 sites are where the artifact *relies on the
kernel deciding a definitional equality the elaborator did not confirm*, mostly between
large dependent records and under `HEq`. They are the first declarations to give an
independent kernel: a divergence between kernels on structure eta, proof irrelevance or
projection reduction would show here before anywhere else. The file list is in
`rh-intake/KEXACT-SITES.txt`.

## 2. Big integers and kernel computation

547 lines in 21 files carry a literal of ten or more digits (after removing
`set_option`); the longest are 459, 186 and 185 digits, and 315 are the same 116-digit
prime repeated. The kernel's accelerated `Nat` operations the source reaches through
`decide`: `pow`, `mod`, `div`, `mul`, `sub`, `gcd`, `ble`, `blt`, `beq`, `log2`. No
bitwise operation, no `UInt`/`BitVec`/`Float`, no string or character computation.

Every item below was recomputed in Python from the Lean definitions
(`rh-intake/tools/`), with Lean's truncated subtraction and `x / 0 = 0`.

### 2.1 Lucas certificates by windowed exponentiation (`…/SpanPowerMembership/Primes.lean`)

Three primes, 413718278401, 603339156001 and a 116-digit one, each by
`lucas_primality` with an explicit factorisation of `p − 1`. Each power `a^E % p` is
proved by a chain of `r^(2^8) · a^w % p = s` steps closed by plain `decide`.

- 21 statements `a ^ E % n = s`: all hold (`pow`).
- 393 chain links (`e' = 256·e + w`, `s = r^256·a^w mod n`, and `a^e' ≡ s`): all hold.
- The gcd fact `gcd(∏(gA^i−1), ∏(gB^i−1)) ∣ (2·3·5·7·11·13·37·571·599)^52` and the
  9 × 9 valuation table closed by `decide +kernel` at `:561–565` were **not**
  recomputed (they need `Exc`'s definition read; skipped for time).

### 2.2 The explicit example parameters (`…/Columns/CyclotomicIsCyclotomicExtension.lean`, `ChainInst.lean`)

The artifact instantiates its general machinery at one concrete host (`Examples₂.H0`:
q = 571, d = 599, e = 2, conductor 16·571·599) and four primes of the form
`1 + 599·(c·N)^2`, of 19, 23, 185 and 186 digits, with a 459-digit level `nd2N`.
Primality is by `lucas_primality_test` with the artifact's own fuelled modular power
`ndPowMod`, evaluated by `decide +kernel`.

| claim | recomputed |
|---|---|
| four Lucas tests: bases prime, `∏ qᵏ = p − 1`, `p − 1 < 2^f`, `5^(p−1) ≡ 1`, `5^((p−1)/q) ≢ 1` for each q | all hold; `ndPowMod` agrees with `pow` |
| four norm forms `1 + d·(…)² = p` | hold |
| four identities `−((p−1)/2)·2 + p = 1` | hold |
| `p ≡ 1 (mod condN)` ×4, `≡ 1 (mod 4)` ×2, pairwise distinct, `> 16` | hold |
| `t₁, t₂, t₁−1, t₂−1, nd2T, columnDegreeBound ∣ nd2N` | hold; `nd2N` is 3534093725929145747030016 times their lcm with `condN` |
| `¬ t₁ ∣ condN·18`, `¬ t₂ ∣ condN·768` | hold |
| `siteGood_prime_torsion` (`FoundationsPrimeFact.lean`): a 94-digit prime by `prime_of_cert _ 5 320 8 […]` | all five side conditions hold |

13 further literals asserted prime across the tree (four digits and up) are prime.

### 2.3 Boolean programs run by the kernel

| theorem | what the kernel runs | recomputed |
|---|---|---|
| `PI.PC.loop_run : loop 362 131070 2 0 1 = true` | 131,070 iterations; each a `gcd` against a running product and `n^256 < 2^⌊(3225600000000·n − 1)/(c·6931471808)⌋` — a Chebyshev-type upper bound on π(n) to n = 131,071 | true |
| `PI.PrimesDyadicRS.K.run1…run4` | four runs of 32,766–32,768 steps with `Q = 362!`, each checking `2^(…+257) ≤ h^256` and threading a prime count to an exact final value (1612, 3030, 4388, 5709) | all true |
| `factorial_ladder_thirteen`, `_thirty_one`, `_one_forty_one` | `∑ ⌊10⁹/p⌋` over primes in (N/2, N−3], ≥ 10⁹/20, on a geometric ladder to N = 20,000 | all true |
| `table_ok : okAll 100 table 16900 = true` | 12 intervals, 878 listed primes, trial division to 130, sortedness, a counting inequality | true |
| `Nat.lcmUpto n ≤ 3^n` (n < 30), `≤ 4^n` (n ≤ 100) | | true |

Both loops wrap their arguments in `force x f := match x with | 0 => f 0 | k+1 => f (k+1)`,
which makes the kernel reduce the argument to a literal before continuing; it is an
evaluation-order device, proved equal to `f x` by `force_eq`, and changes nothing
logically. Its presence shows the computations were tuned to the kernel's reduction
strategy, so their cost on a different kernel may differ sharply (playbook lesson 21).

Controls (`tools/controls.py`): eleven mutated inputs, each must make the port say
false (a wrong final prime count, a composite table entry, a dropped table row, a
shortened fuel, a wrong witness list, …). All eleven fire. Three first-draft controls did
not fire because the mutated statements were themselves true; they were replaced, and
the incident is recorded here rather than dropped.

### 2.4 Not recomputed

`decide +kernel` goals read and judged small but not ported: `SepticCharacterInjective`
(a cocycle identity on a 27-element group), `StrictInterlaceIffDescEnum` and
`UnitarySixTwoHarishChandraParameter` (finite interlacing examples over ℚ),
`RedList`/`EpDimb`/`SquareEqDiagOfQuadraticEven`/`SL2BinomialLattices` (exhaustive
checks over `Bool⁸`, `Fin 3 → ZMod 2`, `Fin 3 → ZMod 3`), Bernoulli values
`B₄ = −1/30`, `B₆ = 1/42` (correct), `Nat.primeFactors n` for n ≤ 10. Constants such
as `10^88·(10^421·Q^99)^(1−σ)` and `2^130` appear in real-number inequalities proved
by `norm_num`, not by kernel evaluation.

## 3. Inductive types

120 `inductive` declarations, headers all read. They are enumerations, inductive
predicates and a dozen small data types (`Tower`, `Dat`, `Tr`, `Path`, `Ex`, …); none is
nested through a container, none has a universe argument beyond `Type 1`, and one block
is `mutual` (§4). `Quot` is used through Mathlib's API only. One explicit
`WellFounded.fix_eq` rewrite; 20 `termination_by`.

## 4. Escalation E4, opened and closed: a certificate with a free constructor

`Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/PrincipalizationCertificate.lean`
defines mutual inductive predicates `PrincipalizationCertificate` and `OrderCertificate`
with a constructor `large : 2 ≤ m → PrincipalizationCertificate W p I m Mem Z` — any
ideal, any locus, certified as soon as `m ≥ 2`. On a route that claims Hironaka's
resolution of singularities in characteristic zero (`ResolutionCharZero`,
`PrincipalisationCharZero`, a 499-file development), a certificate that is free to
construct looked like a vacuous hypothesis.

Trace: the certificate is eliminated in
`StrictTransformIsolation/RestrictionToOpens.lean:526` by the mutual recursor into
`OrderOneCentersIsolated V W p I m Mem Z`, whose definition (`:106`) begins
`∀ C, m = 1 → …`. The `large` case is discharged by `omega` from `2 ≤ m` and `m = 1`.
So the predicate records how an order-one configuration was reached, the property drawn
from it is only ever about `m = 1`, and the free constructor carries no content. **Not a
finding.** The statements `ResolutionCharZero` and `PrincipalisationCharZero` themselves
read as the standard ones (blow-up sequence, smooth total space, isomorphism over the
smooth locus, SNC exceptional locus); whether `IsBlowupSeq` and `Snc` mean what their
names say was not checked.

## 5. What this adds for whoever builds it

1. The independent-kernel replay should start with the 50 `kexactB` files, `CutMainCpt`
   (the `addDecl` copies), and the four files of §2.3; the last will dominate the clock.
2. If a kernel rejects or times out on §2.3, that is a cost or reduction-strategy
   difference before it is a soundness signal: the facts themselves are true.
3. A reader looking for where the argument's weight sits should not start with the
   numerics. They are explicit prime bounds below 131,072 and primality of one fixed
   parameter set; everything recomputed is correct and none of it is where a proof of
   GRH could be wrong.

## 6. Reproduce

```bash
R=lean/src
python3 -I audits/rh-intake/tools/recompute_primes.py  $R   # 21 powers, 393 links, 13 primes
python3 -I audits/rh-intake/tools/recompute_example.py $R   # §2.2
python3 -I audits/rh-intake/tools/recompute_loops.py   $R   # §2.3
python3 -I audits/rh-intake/tools/controls.py          $R   # eleven negative controls
rg -n 'kexactB|kc%|kq%|kd%|kcopy|cpt_copy_thms' $R
rg -n 'decide \+kernel' $R
```

Auditor: one Claude-family agent, one pass.
