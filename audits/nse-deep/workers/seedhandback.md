# Deep audit — `NavierStokes/SeedHandbackJets.lean` (NSE @ f9e8bc5)

## TL;DR (written after the parent's triage update)

1. **NOT LOAD-BEARING.** A defect anywhere in this file cannot affect
   `navier_stokes_breakdown_R3` / `navier_stokes_breakdown_periodic`. Three independent proofs:
   (i) the headline theorems live in `NavierStokes/ComparatorSolution.lean`, whose transitive
   *import* closure (609 modules) does not contain `NavierStokes.SeedHandbackJets` — a Lean proof
   can only cite transitively imported modules, so this is decisive and heuristic-free;
   (ii) parent's name-level cone excludes it; (iii) my own greps, full output below.

```
$ grep -rn "stocks_formulas" .            # whole NSE repo
./NavierStokes/SeedHandbackJets.lean:94:theorem stocks_formulas (h X : ℝ) (P₀ : ℝ → ℝ) (f : Curves) (η : ℝ) :
                                          # ^ its own declaration line, and nothing else

$ grep -rn "outputExpression" .           # whole NSE repo
./NavierStokes/SeedHandbackJets.lean:85:def outputExpression (h : ℝ) : Fin 4 → Expr :=
./NavierStokes/SeedHandbackJets.lean:91:  (outputExpression h i).eval (basis h X (packet P₀ f))
./NavierStokes/SeedHandbackJets.lean:105:  simp [stocks, outputExpression, angularExpression, axialExpression, massExpression,
./NavierStokes/SeedHandbackJets.lean:224:  let C := ∑ i : Fin 4, ((outputExpression h i).bounds k BB CC).2
./NavierStokes/SeedHandbackJets.lean:225:  have hCn (i : Fin 4) : 0 ≤ ((outputExpression h i).bounds k BB CC).2 :=
./NavierStokes/SeedHandbackJets.lean:231:  have hresult := PolynomialExpression.eval_pairBound hbas (outputExpression h i)
```
   `stocks_formulas` is referenced by nothing at all; `outputExpression` never leaves its own
   file. The only route from the root is `NavierStokes.lean:1-2` → `PaperResults.lean:4` →
   `PaperAdditionalResults.lean:16` (`import NavierStokes.SeedHandbackJets`), and
   `PaperAdditionalResults.lean` is a 31-line pure import aggregator with **zero declarations**.
   No `@[simp]`/attribute anywhere in the file (grep: 0 hits), so the instance/simp blind spot
   does not apply.

2. **The reflection mechanism, sized (the pattern to care about if it ever became
   load-bearing).** `stocks_formulas` (:94-108) is the repo's only place where the kernel meets
   *closed* `PolynomialExpression` trees. Expanded (because `simp` unfolds `massExpression`,
   `angularExpression`, `axialExpression`, `outputExpression`): **186 nodes = 91 internal
   `add`/`sub`/`mul` + 75 `input` leaves + 20 `constant` leaves** over the four conjuncts
   (41/47/45/53 nodes). `eval` (`ClosedIntervalJetAlgebra.lean:255`) is *structural* recursion —
   grep for `termination_by|decreasing_by|WellFounded|Acc.rec` over both files: **0 hits** — so
   `simp` rewrites with its 5 equation lemmas and the kernel checks a **propositional rewrite
   chain** (`Eq.mpr`/congruence), *not* a `PolynomialExpression.rec` iota cascade; the worst case
   (defeq delta) is 186 single iota steps on a 5-constructor type. The final term is **not** a
   giant `Eq.refl` and **not** `of_decide_eq_true`. Nat-literal work: 75 `Fin 19` lookups through
   a 19-long `Matrix.cons` chain, `Σ(index+1) = 877` `cons_val_succ`-style steps worst case, all
   literals **≤ 18**; the `Fin 12` `packet` vector is never resolved (`packet` is deliberately
   absent from the simp list at :105-106, so `p i η` stays opaque on both sides). No `decide`,
   no `native_decide`, no `Nat.pow/div/mod/gcd`, no big-numeral `norm_num`; the `(2:ℝ)^k` bound
   constants are symbolic in `k`. **Conclusion: real reflection, but three orders of magnitude
   too small and too shallow to reach any known kernel weak spot.**

3. **What I found in the unread part (:110-392).** All three index alignments — the only places
   an off-by-one could hide — are **correct, exhaustively checked**: `packet` (:25-29) ↔
   `packet_pairBound` branches (:44-55), 12/12, each `derivWithin` branch citing the same curve
   index as the value branch above it; `basis` (:57-61) ↔ `inputBounds`/`differenceBounds`
   (:110-114) ↔ `basis_pairBound` branches (:153-192), 19/19, including slot 16 correctly using
   `(hpq 0).inverse` for `(p 0)⁻¹` with a difference constant syntactically identical to
   `PairBound.inverse`'s output; `Profile.curves` (:252-254) ↔ `profile_comparison` branches
   (:294-300), 7/7 with correct `.mono` directions. One blind spot (A-1): `stocks_formulas`
   cannot detect a `15 ↔ 16` index swap, because :76 uses them only inside the product
   `v14*v15*v16` (my mutation test: residual exactly 0.0). One SUSPICIOUS item (S1):
   `Profile.history` (:249) is defined as a Lebesgue integral whose integral nature is used by
   **no** theorem in the file — both comparison theorems consume it only through hypotheses, so
   replacing `history` by an arbitrary function leaves them true with identical proofs. And
   `Profile.density 4 = E²/(2x)` (:247) is integrated from `0` with no integrability hypothesis,
   so `Cp` may be Mathlib's junk `0` (E2). Verdict counts: **OK 37, OK-modulo-build 1, UNCLEAR 1,
   SUSPICIOUS 1, KERNEL-RISK 0.**

4. **Formulas: re-derived, all four MATCH** (kept because it was already done: my numeric
   transliteration, max residual 4.4e-16 with a 12-mutation sensitivity battery, plus a
   code-disjoint sympy child, `simplify(lhs-rhs)=0`). No index or sign differs from the sibling's
   map. Details in §A below.

---

Auditor: worker `seedhandback` (read-only). No file under `repos/NSE` was modified.
No `lake build` was run (no built Mathlib on this box); this is source-level reading plus
independent numeric/symbolic re-derivation done outside Lean.

## Scope

Primary: `NavierStokes/SeedHandbackJets.lean` — 392 lines (the file ends with a trailing
newline; "393" in the tasking is the line count including the final empty line).

Declaration census in the primary file (regex over `^\s*(private )?(theorem|def|abbrev|structure|inductive)`):
**40 declarations** = 4 `abbrev` (`Curves` :20, `Packet` :21, `Basis` :22, `Expr` :63),
1 `structure` (`Profile` :237), 0 `inductive`, 18 `def`, 17 `theorem`
(of which 7 `private`: `v` :65, `c` :66, `inputBounds` :110, `differenceBounds` :113,
`L_lower` :116, `fixed_L_bound` :122, `fixed_d_bound` :132, `basis_pairBound` :141,
`jetValues_nonempty` :314, `jetValues_bddAbove` :317 — count of `private` markers is 10
across defs+theorems).
**All 40 were read line-by-line. Nothing in this file was skimmed.**

Supporting files read line-by-line where they carry the semantics I had to check:
- `NavierStokes/ClosedIntervalJetAlgebra.lean` (294 lines): read `J` :11, `Bound` :15,
  `Bound.mono/nonneg/value/const/add/sub/congr/mul` :18-79, `inverse_bound` :82-118,
  `PairBound` :121-126, `PairBound.mono/same/const/add/sub/mul/inverse` :134-200,
  `Bound.derivWithin` :204, `PairBound.derivWithin` :211, `Bound.id` :225, `*.of_le` :234-241,
  `PolynomialExpression` :244, `eval` :255, `bounds` :262, `bounds_nonneg` :271,
  `eval_pairBound` :281. (28 decls, read in full.)
- `NavierStokes/NaturalAxisData.lean`: read only the definitions used here —
  `D` :27, `A` :28, `d` :29, `L` :30. Rest of that file skimmed by decl list only (49 decls),
  because `SeedHandbackJets` uses nothing else from it.
- Import graph: `NavierStokes.lean` :1-2, `PaperResults.lean` :1-4,
  `PaperAdditionalResults.lean` :16 (see §D).

Corroboration: two independent re-derivations of the four formulas were obtained
(mine, numeric float transliteration + mutation battery; sibling child `formula-recheck`,
sympy symbolic). Dependency-path question answered independently by child `deppath`.
Their raw work: `seedhandback-formula-recheck.md`, `seedhandback-deppath.md` (same dir).

---

## A. Independent re-derivation of `stocks_formulas` (:94-108) — the four closed formulas

**Index map of `basis h X p` (:57-61), read off the `Matrix.cons` literal:**
`0..11 ↦ p 0 .. p 11`, `12 ↦ (fun η => η)`, `13 ↦ (fun _ => X)`, `14 ↦ (fun _ => X⁻¹)`,
`15 ↦ (fun _ => (√(2X))⁻¹)`, `16 ↦ (fun η => (p 0 η)⁻¹)`, `17 ↦ (fun η => (L h η)⁻¹)`,
`18 ↦ NaturalAxisData.d`. 19 entries, matches `Basis = Fin 19 → ℝ → ℝ` (:22). The sibling's
map is **correct**; the `formula-recheck` child re-derived the same map twice, once from
`basis` :57 and once from the `fin_cases` branch order of `basis_pairBound` :153-192
cross-checked against `inputBounds` :110-111.

**Transliteration of the trees, term by term (source text, not paraphrase):**

- `massExpression h` (:67-69) = `((v13 - ((2*D h)*v12)*v2) - (v18*v3)) * v14`
  → `(X - 2*D h*η*p 2 η - d η*p 3 η) * X⁻¹` = the statement's `W` (:96). **MATCH**
  (Lean `a/X` is `a*X⁻¹` by `div_eq_mul_inv`, which is in the simp list :106.)
- `angularExpression h` (:71-76) = `(c 0 - mass) + ((((c(1-h)*v4 - (c(D h)*v12)*v5) - v18*v7) + (c(2*(h-D h))*v12)*v6) * v14) * v15) * v16`
  → `-W + ((1-h)p4 - D h·η·p5 - d·p7 + 2(h-D h)·η·p6)·X⁻¹·(√(2X))⁻¹·(p0)⁻¹`
  = RHS of conjunct 1 (:97-99). **MATCH**
- `axialExpression h` (:78-82) = `(((c 0 - mass*v1) + ((c(D h)*(v2 - v12*v3) + (c(4h)*v12)*v8) - v18*v9)*v14) + (c(4*A h)*v12)*v10) - v18*v11`
  → `-W·p1 + (D h·(p2 - η·p3) + 4h·η·p8 - d·p9)·X⁻¹ + 4·A h·η·p10 - d·p11`
  = RHS of conjunct 2 (:100-102). **MATCH**
- `outputExpression h` (:85-88) = `![angular, axial, (v13*v17)*angular, ((v13*v17)*v16)*axial]`
  → `stocks 2 = X·L⁻¹·angular = X/L·stocks 0` (:103) and
    `stocks 3 = X·L⁻¹·(p0)⁻¹·axial = X/(L·p0)·stocks 1` (:104). **MATCH**

**Machine confirmation (mine, independent of the child):** I transliterated the four trees
into Python floats with the `basis` index map applied, and the four claimed right-hand sides
separately, with `D=1/2-h, A=1/2+h, d=1-η², L=1-2hη²` (`NaturalAxisData` :27-30). Over 6
random parameter draws the max absolute residual was **4.44e-16** on quantities of size up
to 1.1e2 — i.e. exact to double rounding. The `formula-recheck` child got symbolic
`simplify(expand(lhs-rhs)) == 0` for all four. **No index or sign differs. I do not disagree
with the sibling on any of the four formulas.**

**The test is not vacuous** — mutation battery (mine), residual of conjunct 1 / conjunct 2:
`shift all indices +1` → 0.121 / 9.54; `-1` → 5.12 / 7.65; `swap p2↔p3` → 0.032/0.037;
`p4↔p5` → 0.233/0; `p6↔p7` → 0.083/0; `p8↔p9` → 0/0.169; `p10↔p11` → 0/1.29;
`p0↔p1` → 0/0.137; `b13↔b14 (X↔X⁻¹)` → 3.42/2.50; `b16↔b17 (p0⁻¹↔L⁻¹)` → 8.1e-4/0;
`b12↔b18 (η↔d)` → 5.4e-3/0.509. Every single-index confusion I could think of is detected
by at least one conjunct — **except one**, reported below as finding A-1.

### A-1 [UNCLEAR, blind spot, not an error] `stocks_formulas` cannot detect a `15 ↔ 16` index swap
`angularExpression` (:76) uses indices 14, 15, 16 only as the product `v14*v15*v16`, and
15 (`(√(2X))⁻¹`) and 16 (`(p 0 η)⁻¹`) occur there **only inside that product**. Swapping
them in the tree leaves both the tree value and the claimed RHS unchanged (my mutation
`swap(15,16)` → residual exactly 0.0 for both conjuncts). Index 15 appears nowhere else;
index 16 appears once more (`outputExpression 3`, :88). So neither `stocks_formulas` nor
`basis_pairBound` pins which of 15/16 the manuscript's angular lag intends at :76 — only the
paper does. Harmless for the algebra (the product is what matters), but it is the one place
where an index mix-up in this file is provably invisible to the Lean file itself.

### A-2 [OK, but content-free] `stocks_formulas` is a definitional unfolding, not a fact
Both sides of all four conjuncts are built from the *same* definitions; the theorem says
"the tree I wrote evaluates to the formula I wrote". Two consequences:
- It is **unconditional**: no `0 < X`, `p 0 η ≠ 0`, `L h η ≠ 0`. It holds at `X = 0` too,
  because `basis` supplies `X⁻¹`, `(√(2X))⁻¹`, `(p 0 η)⁻¹` and the RHS writes `/X`,
  `/(X*√(2X)*p 0 η)`; Lean's `x/0 = 0` and `0⁻¹ = 0` on both sides. It must not be read as
  any non-degeneracy or well-posedness statement.
- Conjuncts 3 and 4 (:103-104) are near-tautologies: `outputExpression 2` and `3` are
  *defined* (:87-88) as `(v13*v17)*angular` and `((v13*v17)*v16)*axial`, so those conjuncts
  only restate `X*L⁻¹ = X/L`. Only conjuncts 1 and 2 carry (definitional) information.
- Therefore a *wrong tree* cannot be caught here: the tree is a definition, and the formula
  it is compared against was written by the same hand. See Escalation E1.

---

## B. What the kernel must actually do to accept `stocks_formulas`

Proof script (:105-108): `simp [stocks, outputExpression, angularExpression, axialExpression,
massExpression, PolynomialExpression.eval, v, c, basis, div_eq_mul_inv, mul_inv_rev]` then
`repeat' constructor <;> ring_nf` then a bare `simp`.

**Tree size (expanded, mine, counted programmatically over the transliterated trees;
`massExpression` is inlined twice and `angular`/`axial` once more each by `outputExpression`):**

| component | nodes | `input` leaves | `constant` leaves | internal (`add`/`sub`/`mul`) |
|---|---|---|---|---|
| `outputExpression 0` (angular) | 41 | 16 | 5 | 20 |
| `outputExpression 1` (axial) | 47 | 19 | 5 | 23 |
| `outputExpression 2` | 45 | 18 | 5 | 22 |
| `outputExpression 3` | 53 | 22 | 5 | 26 |
| **total for the 4 conjuncts** | **186** | **75** | **20** | **91** |

(Unexpanded/shared: `mass` 13 nodes, `angular` 41, `axial` 47 — the sibling's "~42 constructor
nodes / 34 input / 9 constant" counts the *source text as written*, i.e. with `mass`,
`angular`, `axial` shared. Both counts are right; the kernel sees the expanded one, because
`simp` unfolds all four defs.)

**(2) Nat/GMP exposure.** `simp [basis]` rewrites `basis h X (packet P₀ f) i` for each of the
75 `input` leaves; each lookup is a literal `Fin 19` index into a 19-long `Matrix.cons`
chain, i.e. up to `index+1` `Matrix.cons_val_succ`-style steps. Sum over the 75 leaves of
`index+1` = **877** such steps (worst case; Mathlib's `Matrix.cons_val'`/`Fin.isValue`
numeral lemmas shortcut many of them). Index-leaf multiset:
`{1:2, 2:6, 3:6, 4:2, 5:2, 6:2, 7:2, 8:2, 9:2, 10:2, 11:2, 12:14, 13:6, 14:8, 15:2, 16:3, 17:2, 18:10}`.
Every literal involved is `≤ 18`. The `Fin 12` `packet` vector is **not** resolved at all:
`packet` is deliberately *absent* from the simp list (:105-106), so `basis` unfolding produces
`packet P₀ f 0 η … packet P₀ f 11 η`, which is syntactically the same as the statement's
`p 0 η … p 11 η` (`p` is the `let` at :95). The 15 `p i η` occurrences in the statement
(:96-104, `Σ(index+1) = 86`) therefore stay opaque. **Kernel numeral work: a few hundred
single-digit `Nat.beq`/`Nat.ble`/`Nat.succ` matchings. No `Nat.pow`, `div`, `mod`, `gcd`,
no literal above 18, no `decide`, no `norm_num` certificate over a big numeral, no
`native_decide` (grep for `native_decide|decide|axiom|unsafe|partial|sorry|set_option` over
both files: ZERO hits).** The `(2:ℝ)^k` factors that dominate the bound arithmetic are
symbolic in `k`, so they are never evaluated. Verdict: **threat vector 2 is untouched in any
meaningful sense** — GMP kernel bugs need large literals or `pow/div/mod/gcd`; none appear.

**(1) Recursor exposure.** `eval` (`ClosedIntervalJetAlgebra` :255) is *structural* recursion
over a plain (non-nested, non-indexed, non-mutual) inductive — grep for
`termination_by|decreasing_by|WellFounded|Acc.rec` over both files: **ZERO hits**, so there
is no well-founded/`Acc.rec` unfolding anywhere on this path. `simp [PolynomialExpression.eval]`
rewrites with the five generated equation lemmas (`eval.eq_1 … eq_5`), which were proved once,
generically in `ι`, at the definition site; each of the 91 internal nodes plus 75 leaf nodes
is then **one propositional rewrite**, checked by the kernel as a congruence/`Eq.mpr` step —
not as an iota-reduction of `PolynomialExpression.rec`. Even in the worst case where a defeq
check delta-unfolds `eval` instead, each step is a *single* iota step on a closed constructor
application, at most 186 of them, all on a 5-constructor non-recursive-parameter type. There
is **no large elimination** (`PolynomialExpression` eliminates into `Sort` but is only used at
`ℝ → ℝ` and at `Prop`), and the only recursor *uses* in the whole path are
`induction p` in `bounds_nonneg` (:274) and `eval_pairBound` (:284), both applied to a *variable*
`p`, so nothing reduces there. Structure eta is exercised by `PairBound` (a 5-field `Prop`
structure, :121) via the many `⟨…⟩`/projection rebuilds (e.g. :36-38, :192, :240) — `Prop`
structure eta, no large elimination. `Profile` (:237) is a 2-field `Type` structure used only
through projections.

**Shape of the final proof term.** `simp` + `ring_nf` produce an `Eq.mpr`/`congrArg`/`Eq.trans`
**rewrite chain**, plus `Mathlib.Tactic.Ring`'s certificate terms for the four `ring_nf`
closes. It is **not** a giant `Eq.refl` and **not** an `of_decide_eq_true`. Exponents inside
the `ring_nf` normal forms are ≤ 1 in the visible variables (`d η` and `L h η` are *not*
unfolded here, so the `η^2` inside `NaturalAxisData.d/L` never enters), so the ring
normalizer's own `Nat` exponent arithmetic is trivial. `repeat' constructor` splits the
4-fold `And` (3 `And.intro`s) and `<;> ring_nf` runs on each; the trailing bare `simp` (:108)
closes whatever `ring_nf` left syntactically unequal — that trailing `simp` is the only step
whose success I cannot predict from source, see Residue R2.

**(3) Custom metaprogramming.** grep over `SeedHandbackJets.lean` and
`ClosedIntervalJetAlgebra.lean` for `macro|elab|syntax|set_option|native_decide|axiom|unsafe|
partial|sorry|@[simp]`: **ZERO hits**. Not even a local `@[simp]` attribute, so the `simp`
calls use the ambient Mathlib set only. `noncomputable section` (:13) is not
metaprogramming and has no kernel consequence. Nothing to report under vector 3.

---

## C. Lines 110-392 — the `basis`/input-bound bookkeeping (read in full)

The question "does every bound actually cover the index it claims to" reduces to three index
alignments. I checked all three exhaustively, branch by branch.

**C-1 `packet` (:25-29) ↔ `packet_pairBound` (:31-55) branches (:44-55): ALIGNED, 12/12.**
`packet = ![f0, f1, f2, deriv f2, f3, deriv f3, f4, deriv f4, f5, deriv f5, P₀+f6, deriv(P₀+f6)]`.
Branch list in order: `(hm 0)`, `(hm 1)`, `(hm 2)`, `(hm 2).derivWithin`, `(hm 3)`,
`(hm 3).derivWithin`, `(hm 4)`, `(hm 4).derivWithin`, `(hm 5)`, `(hm 5).derivWithin`, `hp'`,
`hp'.derivWithin`. Each derivative branch cites the **same** curve index as the value branch
immediately above it — this is exactly where an off-by-one would live, and there is none.
The `(k+1) → k` order drop is carried by `PairBound.of_le … (by omega)` on value branches and
by `PairBound.derivWithin` (`ClosedIntervalJetAlgebra` :211) on derivative branches. `hm`
widens the jet bound `B → B+B₀` with `le_add_of_nonneg_right hb.nonneg` and *keeps* the
difference constant at `1` (:36-38) — correct, widening the difference constant is not needed.
`hp'` (:39-41) is `PairBound.same hP hb ε |>.add (h 6)`, giving bound `B₀+B` and difference
`0+1`, renormalised to `B+B₀` and `1` by `simpa only [zero_add, add_comm B₀ B]`. All 7
components of `Curves = Fin 7 → ℝ → ℝ` are used, none twice with different meanings. **[OK]**

**C-2 `basis` (:57-61) ↔ `inputBounds`/`differenceBounds` (:110-114) ↔ `basis_pairBound`
branches (:153-192): ALIGNED, 19/19.** Table (index : `basis` entry : `inputBounds` : `differenceBounds` : branch : justification):

| i | `basis` entry | `inputBounds` | `differenceBounds` | branch (:line) | check |
|---|---|---|---|---|---|
| 0-11 | `p i` | `D` | `1` | `hpq i` (:155-166) | hypothesis is `PairBound k (p i) (q i) D 1 ε` — exact |
| 12 | `fun η => η` | `1` | `0` | `PairBound.same contDiffOn_id (Bound.id k) ε` (:167) | `Bound.id k : Bound k (fun η => η) 1` (alg :225); bound `1` is only true because `J = [-1,1]` (alg :11) — and `Bound.id`'s proof does use `hη` (alg :230). `same` gives difference `0` |
| 13 | `fun _ => X` | `X₁` | `0` | `PairBound.same contDiffOn_const hXs ε` (:168) | `hXs` (:147-148) = `Bound.const k X` monotoned by `|X| ≤ X₁`, using `abs_of_pos hXp` and `hX.2` — needs `0 < X`, obtained at :145 from `hX₀.trans_le hX.1` |
| 14 | `fun _ => X⁻¹` | `X₀⁻¹` | `0` | `PairBound.same contDiffOn_const hXi ε` (:169) | `hXi` (:149-151): `inv_anti₀ hX₀ hX.1` gives `X⁻¹ ≤ X₀⁻¹`; correct direction (`X₀ ≤ X`) |
| 15 | `fun _ => (√(2X))⁻¹` | `(√(2X₀))⁻¹` | `0` | `PairBound.same contDiffOn_const hXsroot ε` (:170) | `hXsroot` (:153-156): `inv_anti₀ hroot0 (Real.sqrt_le_sqrt …)` with `hroot0 : 0 < √(2X₀)`; correct direction |
| 16 | `fun η => (p 0 η)⁻¹` | `T` | `CI` | `(hpq 0).inverse hμ hp hq hT` (:171) | **index 0, matching `basis 16 = (p 0)⁻¹`** — the right curve. `PairBound.inverse` (alg :180-185) outputs bound `T` and difference `(2:ℝ)^k*((2:ℝ)^k*C*T)*T` with `C = 1` here, and the theorem's `CI` argument is literally `(2:ℝ)^k*((2:ℝ)^k*1*T)*T` (:144) — **syntactically identical**, no `ring` gap |
| 17 | `fun η => (L h η)⁻¹` | `L` | `0` | `PairBound.same (hLs.inv hLp) hL ε` (:172) | `hL` is the **hypothesis** `Bound k (fun η => (L h η)⁻¹) L` (:141 sig) — an inverse bound, matching the inverse entry; `hLp` (:163-164) `L h η ≠ 0` from `L_lower` and `0 < 1-2h` |
| 18 | `NaturalAxisData.d` | `1+(2:ℝ)^k` | `0` | `PairBound.same hds (fixed_d_bound k) ε` (:173) | `fixed_d_bound k : Bound k d (1+(2:ℝ)^k)` (:132) — **same expression** as `inputBounds` slot 18 (:111) |

No slot is proved for a different index than the one it is used at. The 19 `fin_cases`
branches are in increasing index order and there are exactly 19 of them.

**C-3 supporting bound lemmas.**
- `L_lower` (:116-120) claims `1-2h ≤ L h η` for `0 ≤ h`, `η ∈ J`. `L h η = 1-2hη²`
  (`NaturalAxisData` :30), so the claim is `2hη² ≤ 2h`, true from `h ≥ 0` and `η² ≤ 1`; the
  script derives `hs : η^2 ≤ 1` by `nlinarith [hη.1, hη.2]` then `nlinarith`, which needs the
  product `h·(1-η²) ≥ 0` — within `nlinarith`'s pairwise-product search. **[OK modulo build]**
- `fixed_L_bound` (:122-130) claims `Bound k (L h) (1+(2:ℝ)^k*(|2*h|*(2:ℝ)^k))`. Built as
  `const 1 − const(2h)·(id·id)`: `Bound.mul` (alg :58) contributes `2^k·A·B`, so the chain
  gives `|1| + 2^k·|2h|·(2^k·1·1)`; `convert … using 1` then discharges the function equality
  (`1-2hη² = 1-2h(η·η)`, by `ext; simp only [L, id_eq]; ring`) and the constant equality
  (`simp only [abs_one, mul_one]; ring`). Both are genuine `ring` identities. The resulting
  constant is **literally the `LB` used at :218** (`let LB := 1+(2:ℝ)^k*(|2*h| *((2:ℝ)^k))`),
  so `hLb := hL (L h) hLs (…) (fixed_L_bound k h)` (:223) type-checks with no slack. **[OK]**
- `fixed_d_bound` (:132-137) claims `Bound k d (1+(2:ℝ)^k)`; same construction with `|1| + 2^k·1·1`
  and `convert … using 1` closing `1-η² = 1-η·η` and `|1|+2^k*1*1 = 1+2^k` (`simp`). Sanity:
  on `J`, `|d| ≤ 1`, `|d'| = |2η| ≤ 2`, `|d''| = 2`, so `1+2^k ≥ 2` is a true (loose) bound for
  every `k`, including `k = 0` where it equals 2. **[OK]**
- `hBB`/`hCC` nonnegativity (:222-229... i.e. :225-232 in file terms, `fin_cases i <;> norm_num
  [BB, inputBounds]` / `[CC, differenceBounds]` then `first | exact hD | exact hT0 | exact hL0 |
  exact hX₀.le.trans hXX | positivity`): needed because `bounds_nonneg` (alg :271) and
  `Finset.single_le_sum` both need nonnegativity. `X₁ ≥ 0` comes from `hX₀.le.trans hXX`, i.e.
  from `0 < X₀ ≤ X₁` — correct; `1+2^k ≥ 0` and `(√(2X₀))⁻¹ ≥ 0` by `positivity`. **[OK]**

**C-4 `stocks_comparison` (:196-235) — the load of the file. [OK, and genuinely uniform.]**
`C := ∑ i : Fin 4, ((outputExpression h i).bounds k BB CC).2` is fixed **before** `X`, `P₀`,
`f`, `g`, `ε` are introduced (:230-231), and depends only on `k, h, B, B₀, X₀, X₁, μ` through
`D = B+B₀`, `T` (from `inverse_bound k μ D`), `L` (from `inverse_bound k (1-2h) LB`) — so the
docstring's "C precedes both profiles and the radius" is **true of the actual statement**, not
just of the prose. The final step is `hresult.difference.mono` + `mul_le_mul_of_nonneg_right
(Finset.single_le_sum hCn (mem_univ i)) hε` (:233-235): bounding one summand by the sum needs
all four summands `≥ 0`, supplied by `hCn` via `bounds_nonneg` — correct, no gap.
Orientation check (the other classic off-by-one): the goal bounds
`stocks … g i η - stocks … f i η`; `PairBound.difference` (alg :126) bounds `g η - f η` with
`left = f`-side; `hpacket` is built from `hfg : ∀ i, PairBound (k+1) (f i) (g i) …`, so
`left = f`, `right = g` throughout, and `hp/hq` are fed `hf` (about `f 0`) and `hg` (about
`g 0`) in that order (:232). **Orientation is consistent; the difference is `g − f` as
required.** Non-vacuous: the hypotheses are satisfiable (e.g. `f = g` constant with
`f 0 ≡ μ`, `ε` arbitrary).

**C-5 `Profile` block (:237-267) and `profile_comparison` (:269-304). [OK on logic, see S1.]**
The `fin_cases j` mapping at :294-300 is the third place an off-by-one could hide:
`curves = ![E, U, history 0, history 1, history 2, history 3, history 4]` (:252-254), and the
branches are, in order, `(hfields …).1`, `(hfields …).2`, `hhist … 0`, `1`, `2`, `3`, `4`.
**Aligned, 7/7.** The `.mono` directions are right: fields use `le_add_of_nonneg_right`
(`εf ≤ εf+εm`), histories use `le_add_of_nonneg_left` (`εm ≤ εf+εm`). `rw [one_mul]` (:293)
is needed because `PairBound.difference` carries `C*ε` with `C = 1`.

**C-6 `parameterNorm` block (:306-342). [OK — and specifically NOT junk-value exploitation.]**
`jetValues` (:306-309) is `{0} ∪ {jet norms}`, so `Nonempty` is free (:314) and
`parameterNorm = sSup` is `≥ 0`. The two directions are handled correctly and this matters:
`parameterNorm_le` (:326) uses `csSup_le jetValues_nonempty` — valid without `BddAbove`; the
*upper*-bound direction (`le_csSup`, :335-342) is the one that needs `BddAbove`, and
`jetValues_bddAbove` (:317-324) is supplied from the `JetBound` hypotheses. So the
`sSup`-of-unbounded-set junk value (`= 0` in Mathlib) is **not** being used to make anything
true for free: in `profile_comparison_norm` (:354) the LHS `parameterNorm` is bounded via
`csSup_le` (elementwise, honest) and the two RHS `parameterNorm`s are used as upper bounds via
`le_csSup` with a proven `BddAbove`. `m` arities line up: `outputDifference : Fin 4 → …`,
`fieldDifference : Fin 2 → …`, `historyDifference : Fin 5 → …` (:344-352). `hd` (:369-371) is
`Bound.sub` under dot-notation with `hQb` landing in the first `Bound` slot, giving
`Q.curves − P.curves` with constant `B+B` — matching the `(B+B)` fed to `parameterNorm_bounds`
(:385-386). **[OK]**

### Per-declaration verdicts (all 40)

| # | name | file:line | statement, in my words | mechanism | verdict |
|---|---|---|---|---|---|
| 1 | `Curves` | :20 | abbrev `Fin 7 → ℝ → ℝ` | — | OK |
| 2 | `Packet` | :21 | abbrev `Fin 12 → ℝ → ℝ` | — | OK |
| 3 | `Basis` | :22 | abbrev `Fin 19 → ℝ → ℝ` | — | OK |
| 4 | `packet` | :25 | 12-vector: 6 curves + 4 `derivWithin`s + pressure `P₀+f 6` and its derivative | `Matrix.cons` literal | OK |
| 5 | `packet_pairBound` | :31 | if all 7 curves are `(k+1)`-pair-bounded by `B` with difference `ε`, all 12 packet slots are `k`-pair-bounded by `B+B₀` | `fin_cases` + 12 explicit branches, `of_le`/`derivWithin` | OK (C-1) |
| 6 | `basis` | :57 | 19-vector: 12 packet slots + `η`, `X`, `X⁻¹`, `(√2X)⁻¹`, `(p 0)⁻¹`, `(L h)⁻¹`, `d` | `Matrix.cons` literal | OK |
| 7 | `Expr` | :63 | abbrev `PolynomialExpression (Fin 19)` | — | OK |
| 8 | `v` | :65 | `input i` | — | OK |
| 9 | `c` | :66 | `constant x` | — | OK |
| 10 | `massExpression` | :67 | tree for `(X − 2D(h)ηp₂ − d p₃)·X⁻¹` | definition | OK (A) |
| 11 | `angularExpression` | :71 | tree for `−W + (…)·X⁻¹(√2X)⁻¹p₀⁻¹` | definition | OK (A); see A-1 |
| 12 | `axialExpression` | :78 | tree for `−W p₁ + (…)X⁻¹ + 4A(h)ηp₁₀ − d p₁₁` | definition | OK (A) |
| 13 | `outputExpression` | :85 | 4-vector `[angular, axial, X L⁻¹·angular, X L⁻¹p₀⁻¹·axial]` | `Matrix.cons` literal | OK |
| 14 | `stocks` | :90 | `eval` of the tree at the basis | definition | OK |
| 15 | `stocks_formulas` | :94 | the four closed formulas | `simp`+`ring_nf`+`simp`; 186-node rewrite chain | OK but content-free (A-2) |
| 16 | `inputBounds` | :110 | 19-vector of jet bounds | literal | OK (C-2) |
| 17 | `differenceBounds` | :113 | 19-vector of difference coefficients (only slots 0-11 and 16 nonzero) | literal | OK (C-2) |
| 18 | `L_lower` | :116 | `1−2h ≤ L h η` on `J` for `h ≥ 0` | `nlinarith` twice | OK modulo build (C-3) |
| 19 | `fixed_L_bound` | :122 | `Bound k (L h) (1+2^k(|2h|2^k))` | `const`/`mul`/`sub` chain + `convert using 1` | OK (C-3) |
| 20 | `fixed_d_bound` | :132 | `Bound k d (1+2^k)` | same | OK (C-3) |
| 21 | `basis_pairBound` | :141 | all 19 basis slots pair-bounded by `inputBounds`/`differenceBounds` | `fin_cases` + 19 branches | OK (C-2) |
| 22 | `stocks_comparison` | :196 | ∃ uniform `C ≥ 0` bounding the `k`-jet of each output difference by `C·ε` | `eval_pairBound` on the closed tree + `single_le_sum` | OK (C-4) |
| 23 | `Profile` | :237 | structure with fields `E, U : ℝ×ℝ → ℝ` | — | OK |
| 24 | `Profile.density` | :243 | 5-vector `[U, √(2x)E, U√(2x)E, U²−E²/2, E²/(2x)]` | literal | see S1/E2 |
| 25 | `Profile.history` | :249 | `∫ x in 0..X, density i x η` | definition | see E2 |
| 26 | `Profile.curves` | :252 | `[E(X,·), U(X,·), history 0..4]` | literal | OK |
| 27 | `Profile.outputs` | :256 | `stocks h X P₀ (curves X)` | definition | OK |
| 28 | `Profile.SmoothOnBand` | :259 | all curves `C^∞` on `J` for `X ∈ [X₀,X₁]` | definition | OK |
| 29 | `Profile.JetBound` | :262 | all curves `k`-bounded by `B` | definition | OK |
| 30 | `profile_comparison` | :269 | ∃ uniform `C` : output jet differences ≤ `C(εf+εm)` given field/history difference bounds | reduces to `stocks_comparison` via 7 aligned branches | OK (C-5) |
| 31 | `jetValues` | :306 | `{0} ∪ {‖iterated derivs‖}` | definition | OK |
| 32 | `parameterNorm` | :311 | `sSup jetValues` | definition | OK (C-6) |
| 33 | `jetValues_nonempty` | :314 | nonempty | `⟨0, Or.inl rfl⟩` | OK |
| 34 | `jetValues_bddAbove` | :317 | bounded by `B` given `Bound k` for all `i, X` | case split on the union | OK |
| 35 | `parameterNorm_le` | :326 | `parameterNorm ≤ B` | `csSup_le` (no `BddAbove` needed) | OK |
| 36 | `parameterNorm_bounds` | :335 | `0 ≤ parameterNorm` and it *is* a bound | `le_csSup` with `BddAbove` | OK (C-6) |
| 37 | `fieldDifference` | :344 | 2-vector of `Q−P` field differences | literal | OK |
| 38 | `historyDifference` | :347 | `Q.history i − P.history i` | definition | OK |
| 39 | `outputDifference` | :350 | `Q.outputs i − P.outputs i` | definition | OK |
| 40 | `profile_comparison_norm` | :354 | sup-norm form: `‖output diff‖ ≤ C(‖field diff‖+‖history diff‖)` | `profile_comparison` + `parameterNorm_le`/`_bounds` | OK (C-6) |

Verdict counts: **OK 37, OK-modulo-build 1 (`L_lower`), UNCLEAR 1 (A-1, blind spot in
`stocks_formulas`), SUSPICIOUS 1 (S1, `Profile.density`/`history` — naming vs use).
KERNEL-RISK 0.**

### S1 [SUSPICIOUS — rhetorical, not unsound] `history` is defined as a Lebesgue integral that no theorem in the file ever uses
`Profile.history` (:249-250) is `∫ x in (0:ℝ)..X, P.density i x η`, docstring "The manuscript's
actual cumulative Lebesgue integrals `M,I,J,S,Cp`" (:248). But `profile_comparison` (:269) and
`profile_comparison_norm` (:354) only ever consume `history` through the *hypotheses*
`∀ X ∈ Icc X₀ X₁, ∀ i, Bound (k+1) (fun η => Q.history i X η − P.history i X η) εm` (:283-284)
and `SmoothOnBand`/`JetBound`. **No integral property (linearity, FTC, integrability,
differentiation in `η`) is ever invoked.** Replace `history` by any function `ℝ → ℝ → ℝ`
whatsoever and both theorems remain true with identical proofs. So the word "actual" in the
docstring is doing work the Lean is not: this file proves a Lipschitz-in-jets estimate for a
*syntactic* functional of seven abstract curves, and the identification of those curves with
cumulative integrals of a Navier-Stokes profile is asserted by definition and used nowhere.

---

## D. Is this file load-bearing for the headline theorems? **NO — dead weight.**

Verified independently by child `deppath` and consistent with my own greps:
- `SeedHandbackJets` appears in the whole repo exactly 3 times: `namespace` (:15), `end` (:392),
  and `import NavierStokes.SeedHandbackJets` at `PaperAdditionalResults.lean:16`.
  `PaperAdditionalResults.lean` is a 31-line pure import aggregator with **zero declarations**.
- `navier_stokes_breakdown_R3` and `navier_stokes_breakdown_periodic` both live in
  `NavierStokes/ComparatorSolution.lean` (:16/:20 and :23/:27), whose transitive **import**
  closure is 609 modules and **does not contain** `NavierStokes.SeedHandbackJets`. A Lean proof
  can only cite declarations from transitively imported modules, so this is decisive regardless
  of name-resolution heuristics: no declaration of this file can appear in either proof term.
- Reverse check: none of the 40 names above (`stocks`, `stocks_formulas`, `stocks_comparison`,
  `profile_comparison`, `profile_comparison_norm`, `parameterNorm`, `packet`, `basis`, …) is
  referenced from any other file; only generic name collisions in unrelated, non-importing
  namespaces.

**Plainly: a defect anywhere in `SeedHandbackJets.lean` — a wrong index, a wrong sign, a
wrong tree, even an inconsistency — would not affect `navier_stokes_breakdown_R3` or
`navier_stokes_breakdown_periodic` at all.** 392 lines, 0 `sorry`, consumed by nothing. Its
only function is to be *countable* as formalized paper content (it is reachable from the root
`NavierStokes.lean` by imports, so `lake build` compiles it and a reader who checks "is it in
the build?" gets yes).

---

## Kernel-risk assessment (summary by vector)

| vector | present in scope? | does the kernel have to do the risky computation? |
|---|---|---|
| (1) recursive inductives / recursor reduction / `Acc.rec` / large elim / structure eta | `PolynomialExpression` (`alg` :244) + closed trees here | **Marginally.** `eval` is structural (no `termination_by`/`WellFounded`/`Acc.rec` anywhere on this path — 0 grep hits). `simp` unfolds it by its 5 equation lemmas, so the 186-node expansion is a **propositional rewrite chain**, not recursor iota. Worst case (defeq delta) = 186 single iota steps on a 5-constructor type. No nested/indexed families, no large elimination. `PairBound` `Prop`-structure eta is used freely; `Profile` `Type`-structure projections only. **No exploitable magnitude.** |
| (2) Nat/GMP numeral arithmetic | `Fin 19`/`Fin 12` literal indices through `Matrix.cons`; `fin_cases` on `Fin 19` (twice) and `Fin 12`/`Fin 7`/`Fin 4` | **Yes but trivially.** ≤ ~877 `cons_val_succ`-style steps for `stocks_formulas`, all literals ≤ 18; `fin_cases` enumerations of length ≤ 19. **No** `decide`, `native_decide`, `Nat.pow/div/mod/gcd`, no `norm_num` certificate over a large numeral, no literal above 18. The `(2:ℝ)^k` bound constants are symbolic in `k` and never evaluated. GMP-path bugs need large operands; there are none. |
| (3) custom metaprogramming | **absent** | grep over both files for `macro|elab|syntax|set_option|native_decide|axiom|unsafe|partial|sorry|@[simp]`: **0 hits**. Nothing to report; the repo-wide finding holds here. |

Bottom line for this file: **no kernel-exploitation surface worth the name.** If this file is
wrong, it is wrong mathematically or rhetorically, not because the kernel was tricked.

---

## Escalations (ranked)

**E1. Does `outputExpression`/`angularExpression`/`axialExpression` (:71-88) actually encode the
manuscript's angular/axial lag functionals?**
Question for an expert: with the paper's equations for `Q_s, N_s, p_{s,1}, p_{s,2}` in hand,
are the trees at :67-88 term-for-term the paper's lags — in particular is index 15 (`(√2X)⁻¹`)
vs 16 (`(p 0 η)⁻¹`) placed as the paper wants at :76 (see A-1: the file itself cannot tell),
and are `p 4 … p 11` (packet slots = `M, M', I, I', J, J', Cp, Cp'`, :26-29) attached to the
coefficients the paper attaches them to? What would settle it: a line-by-line diff of :67-88
against the manuscript's displayed lag equations. Nothing inside Lean can settle it, because
the trees are definitions and `stocks_formulas` compares them only to a restatement by the same
author (A-2). **Note E1 is only worth an expert's time if the paper's *claim* is that this file
formalizes those lags — it is provably irrelevant to the two headline theorems (§D).**

**E2. `Profile.density 4 = E²/(2x)` (:247) is integrated from `0` on (:249-250) with no
integrability hypothesis anywhere.**
Question: for the profiles the paper cares about, is `x ↦ E(x,η)²/(2x)` interval-integrable at
`0`? If not, `history 4` (`Cp`) is Mathlib's junk value `0` for exactly those profiles, and the
"pressure history" in `curves` (:254) is identically zero — the theorems stay true (they only
use hypotheses about `history`, see S1) but the object named `Cp` is not the paper's `Cp`.
What would settle it: either an added integrability hypothesis/lemma, or the paper's decay
assumption on `E` near the axis.

**E3. S1: the file's estimate is about abstract curves, not about solutions.**
Question: does the manuscript rely on `profile_comparison_norm` (:354) as a statement about
Navier-Stokes profiles? If yes, the missing link (that `Profile.curves` of an actual solution
satisfies `SmoothOnBand`/`JetBound`, and that `stocks` of it equals the paper's lags) is
unformalized and lives entirely in E1/E2. What would settle it: a single instantiation of
`profile_comparison_norm` at a concrete `Profile` produced by the rest of the development —
which, per §D, does not exist anywhere in the repo.

**E4. `L_lower` (:116-120), `fixed_L_bound` (:122), `fixed_d_bound` (:132) are `nlinarith`/
`convert`-closed and unbuildable here.**
Question: do they actually compile at this Mathlib pin? What would settle it: `lake build
NavierStokes.SeedHandbackJets` on a machine with the pinned Mathlib. Low priority: the
statements are mathematically true as written (I checked each by hand above), so a failure
would be a build failure, not a soundness issue.

---

## Residue (what I could not check, and why)

- **R1. Nothing in this file was checked by the Lean elaborator or kernel.** No built Mathlib on
  this box (disk full), per tasking. Every "OK" above means: the statement says what I say it
  says, and the cited mechanism is the right mechanism for it. Tactic *success* (`nlinarith` at
  :118/:120, `positivity` at :229/:232, `fun_prop` at :157/:160, `field_simp; ring` inside
  `PairBound.inverse`) is asserted by the artifact's own CI, not by me.
- **R2. The trailing bare `simp` at :108.** I cannot predict what goal `repeat' constructor <;>
  ring_nf` leaves for it. This is the one step in `stocks_formulas` whose content is opaque from
  source. It cannot make a false statement true (the four conjuncts are algebraic identities I
  verified numerically and symbolically), but if it closes a goal, that goal was left open by
  `ring_nf`, which mildly suggests a normal-form mismatch (e.g. `mul_inv_rev` orientation)
  rather than a mathematical gap.
- **R3. Correspondence to the manuscript.** I have no access to the paper text, so E1/E2/E3 are
  posed, not answered. Nothing in Lean can answer them.
- **R4. `NaturalAxisData.lean` beyond `D/A/d/L` (:27-30)** was only skimmed by declaration list;
  `SeedHandbackJets` uses nothing else from it, and I confirmed that by grep, but I did not read
  the other 45 declarations of that file.
- **R5. `WeightedQuotients.coeffBound` / `rpow_jet_bound`** used by `inverse_bound`
  (`ClosedIntervalJetAlgebra` :88-108) were not read. They only affect *how large* the constant
  `T` is, never whether an index matches, so they are outside the questions I was asked; a
  vacuous/junk `coeffBound` would weaken `stocks_comparison` (bigger `C`), not falsify it.
- **R6. `Matrix.cons` simp-lemma shortcutting.** My 877-step figure is the worst case
  (`cons_val_succ` chains). Mathlib's numeral lemmas make the real number smaller; I could not
  measure it without a build. The conclusion (all literals ≤ 18, no GMP-relevant operation) is
  unaffected.
