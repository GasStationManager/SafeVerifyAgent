# Worker report (task C slice): bare-`rfl` theorems in the two course-of-values WF-recursion files

Subject: every theorem whose ENTIRE proof is `rfl` / `by rfl` in
`NavierStokes/SlowRecursion.lean` and `NavierStokes/GlobalSlowProfiles.lean`
of `/home/gsm/.openclaw/workspace/repos/NSE` (clone of `openai/NavierStokesAndEuler` @ `f9e8bc5`).
Nothing under that path was read-write; no `lake build` was run (no Mathlib build on this box).
Method: source reading (python/grep) of the two NSE files, plus reading the *Mathlib source* of every
instance the kernel must unfold. Mathlib reference copy used: `/tmp/junk_packages_w4/mathlib`
and `/tmp/stray_packages_r12325x1w3/mathlib`, both at commit `8a178386ff` (toolchain v4.29.0).
**Caveat:** NSE pins `mathlib v4.34.0-rc2` (`lakefile.toml:8-11`), so my Mathlib citations are from a
*nearby* version. Every instance I cite is a stable, long-lived definition, and in each case Mathlib
itself proves the corresponding `coe_*` lemma by `rfl`, which is the fact I actually rely on.
Sibling report `audits/nse-deep/workers/wf-recursion.md` was read first; its facts on
`hierarchy`/`sequence`/`recursionStep` are reused, not re-derived, and I confirmed its line numbers.

## ANSWER TO THE CENTRAL QUESTION: **NO — for all 28 assigned sites (and for the 2 extra sites the
## assignment missed). Zero of them force the kernel to unfold `WellFounded.fix` / `Acc.rec`.**

Evidence, in the order another auditor can re-check it:

1. **Only ONE of the 28 sites even mentions a WF-recursive function.** `grep -n
   'termination_by\|decreasing_by\|WellFounded.fix\|Nat.rec\|Nat.strongRecOn\|Nat.le_induction\|Acc.rec'`
   over both files returns exactly three hits, all inside *tactic* proofs:
   `SlowRecursion.lean:953`, `SlowRecursion.lean:964`, `GlobalSlowProfiles.lean:910` — each is the
   `rw [WellFounded.fix_eq]` line of `hierarchy_zero` / `hierarchy_succ` / `sequence_succ`.
   **There is no `termination_by` and no `decreasing_by` in either file.** The two WF definitions are
   hand-rolled: `hierarchy` (`SlowRecursion.lean:942-946`, `Nat.lt_wfRel.wf.fix (recursionStep …) n`)
   and `sequence` (`GlobalSlowProfiles.lean:901-902`, same idiom). Neither `hierarchy_zero` (:948-954),
   `hierarchy_succ` (:956-965) nor `sequence_succ` (GSP:907-911) is a bare-`rfl` theorem — each is
   `unfold; rw [WellFounded.fix_eq]; rfl`, so they are **out of my subject** (and the sibling report
   already classifies their trailing `rfl` as a `Nat`-matcher iota step with `fix` as an opaque atom).
2. The single site whose statement contains a WF-recursive function is
   `SlowRecursion.sequence_profile` (**:974-977**):
   `profile (sequence c hcore hbuffer C base n i) = profile (hierarchy c hcore hbuffer C base n i)`.
   Here `sequence` (:969-972) is **not recursive**: `sequence … n = fun i => restrict (core_lt_radius
   hbuffer n).le (hierarchy … n i)`. The term `hierarchy … n i` occurs on **both** sides, at the same
   *symbolic variable* `n`, so after 1 delta + 1 beta + 1 `Subtype` projection the two sides are the
   *same* term and the kernel stops. Mechanism (i)+(ii), ~4-6 steps. See the per-site row below.
3. Independently: **a `WellFounded.fix` at a symbolic argument cannot iota-reduce at all.**
   `WellFounded.fix` is `WellFounded.fixF … (wf.apply x)`, and `Acc.rec` only reduces on a *canonical*
   `Acc.intro`. `Nat.lt_wfRel.wf.apply n` with `n` a free variable is a stuck application of an opaque
   proof term. So even a kernel that *tried* to whnf `hierarchy … n` would get stuck immediately
   rather than unfolding the recursion. **No site applies `hierarchy` or `sequence` at a closed
   numeral** (I checked every one of the 28 statements: the only numerals in any of them are the `0`
   in the *type* `Domain (radius core buffer 0) U h` at :974-976, `radius` being the non-recursive
   `core + buffer / ((n : ℝ) + 1)` at :886-887, and it occurs identically on both sides / only in
   hypothesis types).
4. `Admissible` (GSP:758-768) is a *Type*-valued structure, so `GlobalSlowProfiles.profiles s 0`
   (:904-905, `(sequence s 0).data`) *is* a projection applied to a `fix` at the closed numeral `0` —
   but that is a projection in a **statement/term**, not a defeq obligation: type-checking
   `(sequence s 0).zero_data rfl` (:913-914) needs only the *type* `Admissible s 0`, never the value.
   And GSP:913 is not a bare-`rfl` theorem (the `rfl` there is the argument `(0 : ℕ) = 0`).
   I flag it only to show I looked for the closed-numeral case.

Verdict counts over my 28 assigned sites: **OK 28, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0.**
(The 2 extra bare-`rfl` sites found below, `SlowRecursion.lean:86` and `:445`, are also OK.)

## Completeness check of the assignment (a finding in itself)

I re-scanned both files for *every* declaration whose whole proof is `rfl` (regex over the original,
non-comment-stripped text, requiring the body to end in `:= rfl` / `:= by rfl`):

* `SlowRecursion.lean`: **86**, 89, 91, 93, 95, 97, 99, 128, 435, 437, 439, 441, 443, **445**, 447,
  449, 451, 974 → **18** sites; the assignment listed 16, omitting **:86 `realConstant_apply`** and
  **:445 `complexProfile_zero`**. I audited both (rows below); they are the exact twins of :449 and
  :447 and are OK. No new mechanism.
* `GlobalSlowProfiles.lean`: 76, 78, 80, 82, 84, 85, 97, 213, 1201, 1203, 1205, 1207 → **12** sites,
  exactly the assigned list. Nothing missing.

## The four mechanism families (analysed once, cited once, applied to all 30 rows)

Both files build the same gadget: a `Subalgebra ℝ (function type)` of "regular" functions, and then
`abbrev`-hide the subtype.

* `SlowRecursion.lean:20` `abbrev Raw := ℝ × ℂ → ℂ`; `:23-27` `structure Regular … : Prop`;
  `:56-62` `def regularAlgebra : Subalgebra ℝ Raw` (a `where`-style structure literal);
  `:64` `abbrev AxisFunction R U := ↥(regularAlgebra R U)`; `:66`
  `instance : CoeFun (AxisFunction R U) (fun _ => Raw) := ⟨fun F => F.1⟩`.
* `GlobalSlowProfiles.lean:26` `abbrev Field := ℝ × ℝ → ℝ`; `:33-35` `structure Regular … : Prop`;
  `:54-60` `def regularAlgebra : Subalgebra ℝ Field`; `:62` `abbrev EvenProfile S := ↥(regularAlgebra S)`;
  `:64` the same `CoeFun … := ⟨fun f => f.1⟩`.

**(A) `⋯_apply` lemmas for the algebra operations** (SR:89,91,93,95,97,99; GSP:76,78,80,82,84,85).
Shape `(F ⊕ G) p = F p ⊕ G p`. `F p` is *notation for* `F.1 p` (the `CoeFun` above). So the kernel must
show `(F ⊕ G).1 p ≡ F.1 p ⊕ G.1 p`, i.e. exactly two facts:
1. `(F ⊕ G).1 ≡ F.1 ⊕ G.1` — a **projection of a structure literal**, because every subtype algebra
   operation in Mathlib is defined structurally as `⟨op x.1 y.1, op_mem …⟩`:
   `Subsemigroup/Defs.lean:266-267` `MulMemClass.mul := ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩`
   (`to_additive` gives the `Add` version; `coe_mul := rfl` at :271-272);
   `Submonoid/Defs.lean:337-338` `OneMemClass.one := ⟨⟨1, one_mem S'⟩⟩` (`to_additive`: zero;
   `coe_one := rfl` at :341-342, `one_def := rfl` at :353-354);
   `Submonoid/Defs.lean:364-365` `instPow := ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩`;
   `Subgroup/Defs.lean:190-191` `div := ⟨fun a b => ⟨a / b, div_mem a.2 b.2⟩⟩` (`to_additive`-ised to
   subtraction — this is the instance behind `sub_apply`); `Subgroup/Defs.lean:164` `InvMemClass.inv`
   (→ `Neg`, behind `neg_apply`). Mathlib *itself* proves these coe-lemmas by `rfl`
   (`Subgroup/Defs.lean:199-200 coe_div := rfl`, `Submonoid/Defs.lean:368-370 coe_pow := rfl`,
   `Subsemiring/Defs.lean:319-320 coe_pow := rfl`), which is exactly the obligation here.
   The `Monoid`/`Ring` bundles are assembled with `fast_instance%`
   (`Submonoid/Defs.lean:391-393`, `Subgroup/Defs.lean:207-209`), i.e. **flattened** structure
   literals, so each field is reached in one projection, not by walking `Injective.monoid`.
2. `(F.1 ⊕ G.1) p ≡ F.1 p ⊕ G.1 p` — the **Pi instance**, which is pointwise by construction:
   `Algebra/Group/Pi/Basic.lean:64-67` `Pi.monoid … npow := fun n x i => x i ^ n`, and likewise
   `divInvMonoid`/`subNegMonoid`. One beta step.
   Classification: **(i) + (ii)**, no recursion, no numerals, no `Fin`, no eta needed.
   Estimated kernel work per site: **~6-15** delta/projection/beta steps (a few more for `0`/`1`,
   which additionally go through `ZeroMemClass`/`OneMemClass` and `Pi.instZero/instOne`).

**(B) `⋯_apply` lemmas for the two "evaluate at a reparametrised point" wrappers**
(SR:435,437,439,441,443,445,447,449,451; GSP:1201,1203,1205,1207).
`SlowRecursion.lean:281-282` `def complexProfile F p : ℂ := F (Real.sqrt p.1, p.2)` and
`GlobalSlowProfiles.lean:1134-1135` `def xProfile f w : ℝ := f (Real.sqrt (2 * w.1), w.2)`. Both are
**non-recursive one-liners**. Each lemma is family (A) with one extra delta of `complexProfile`/`xProfile`
on each side and the *same* argument `(Real.sqrt …, …)` on both sides.
**`Real.sqrt` is never evaluated**: it is a noncomputable atom applied to a variable, carried along
unchanged; likewise `2 * w.1` at type ℝ. No real arithmetic happens in the kernel.
Estimated work: **~8-20** steps per site.

**(C) the constant/parameter/inverse sites, i.e. the ones that walk `algebraMap`**
(SR:86,449; GSP:97,213,1207). `realConstant R U c := algebraMap ℝ (AxisFunction R U) c` (SR:83-84),
`constant S c := algebraMap ℝ (EvenProfile S) c` (GSP:94-95). The kernel path is:
`Subalgebra.algebra` (`Algebra/Algebra/Subalgebra/Basic.lean:477-484`,
`algebraMap := { toFun r := ⟨algebraMap R A r, algebraMap_mem s r⟩ … }`, and Mathlib proves
`coe_algebraMap := rfl` at :487) → `Pi.algebra`
(`Algebra/Algebra/Pi.lean:38-45`, `algebraMap := Pi.ringHom fun i ↦ algebraMap R (A i)`, with
`algebraMap_def := rfl` at :44-45) → for GSP the base case `Algebra.id ℝ`
(`Algebra/Algebra/Defs.lean:391-396`, which deliberately **overrides `toFun x := x`**, so it reduces
without needing `RingHom.id` to be reducible) → for SR the base case `Complex.instAlgebraOfReal`
(`LinearAlgebra/Complex/Module.lean:100-101`, `algebraMap := Complex.ofRealHom.comp (algebraMap R ℝ)`,
with `coe_algebraMap : (algebraMap ℝ ℂ : ℝ → ℂ) = ((↑) : ℝ → ℂ) := rfl` at :109-110), which is exactly
what SR:449/:86 need to hit the `(b : ℂ)` on the right. All of this is **projection of structure
literals + delta of non-recursive defs**; nothing is recursive and reducibility hints do not bind the
kernel. Estimated work: **~15-40** steps; GSP:213 is the largest single obligation
(see its row). Classification **(i)+(ii)**.

**(D) the `restrict` / `sequence` sites** (SR:128, SR:974). `restrict` (SR:120-126) returns
`⟨F, {smooth := …, holomorphic := …, even := …, real := …}⟩`: a `Subtype.mk` whose first component is
the coercion of `F` and whose second is a `Prop` structure literal (**kernel proof irrelevance**
disposes of the second component). Reducing `(restrict hSR F).1` is one projection.
One honest uncertainty: I cannot see, without elaborating, whether the elaborator inserted
`Subtype.val F` or its eta-expansion `fun x => F.1 x` for that first component. In the first case the
check is 1 projection; in the second it is 1 projection + 1 beta (family **(vi)**-flavoured, harmless).
Both cost ≤3 steps and neither touches `hierarchy`.

**Mechanisms that do NOT occur in any of the 30 sites** (stated explicitly, since the task asks):
* **(iv) iota chain over a recursive def at a closed argument: ZERO occurrences.** No site applies a
  recursive function to a numeral. `radius` (SR:886-887) is a division formula, `recursionStep`
  (SR:931-938, GSP:884-897) is a `Nat` matcher but is never *reduced* by any of these `rfl`s.
* **(v) `Matrix.cons`/`Fin`/`List.get` literal index resolution: ZERO occurrences in the 30 sites.**
  The files do contain `![…]` vectors (SR:622, :782, :1210; GSP:1808, :1810 `localIndex := ![0,1,4,3] i`)
  and `Coefficient R U := Fin 5 → AxisFunction R U` (SR:722), but none of them appears in either side
  of any bare-`rfl` theorem: the only `Fin 5` in my sites is the *symbolic* variable `i` at SR:974-976.
  The single `Matrix.cons_val_zero` in these files (GSP:840) is inside a `simpa`, not a `rfl`.
* **kernel GMP `Nat` arithmetic: ZERO.** The only `ℕ` in my sites is the *symbolic* exponent `k` of
  `complexProfile_pow` (SR:443-444). Because `Pi.monoid.npow` is the pointwise
  `fun n x i => x i ^ n` and the subtype `Pow` is `⟨fun a n => ⟨a.1 ^ n, _⟩⟩`, `k` is **carried as an
  argument on both sides and never recursed on**; `npowRec` is never entered, and no `Nat.beq/ble/
  pow/div/mod` and no `decide` is reachable. GSP:213 contains the literal `2` twice (`parameter S ^ 2`
  vs `eta ^ 2` inside `ell`) but on both sides it is the same `(2 : ℕ)` exponent argument of the same
  ℝ-`Monoid.npow`, again only carried.
* **custom metaprogramming: ZERO** in these two files (re-confirmed:
  `grep -n 'macro\|elab\|syntax\|notation\|set_option\|native_decide\|axiom\|unsafe\|partial'` gives no
  declaration-position hit; this matches the sibling report's repo-wide census).
* **long statements**: several of these statements are long, and in every case the length is a long
  **argument list** (`{core buffer : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain …) (hcore …) (hbuffer …) (C : ℝ)
  (base : Coefficient …) (n : ℕ) (i : Fin 5)` at SR:974-976), i.e. terms the kernel merely *carries*,
  not deep computation. Explicitly: **no site is expensive because it is long.**

## Per-site table (28 assigned + 2 missed-by-assignment, marked ★)

Line = first line of the declaration; the `:= rfl` sits on that line or the next.

### `NavierStokes/SlowRecursion.lean`

| line | name | what it says | two sides / head symbols | mechanism | ~steps | verdict |
|---|---|---|---|---|---|---|
| ★86 | `realConstant_apply` | `realConstant R U c p = (c : ℂ)` | LHS head `realConstant` (:83-84, `algebraMap`); RHS `Complex.ofReal` | family (C): `Subalgebra.algebra` → `Pi.algebra` → `Complex.instAlgebraOfReal` (`coe_algebraMap := rfl`), then beta; (i)+(ii) | 15-30 | OK |
| 89 | `add_apply` | `(F + G) p = F p + G p` | both sides `HAdd.hAdd`; LHS at `↥(regularAlgebra)`, RHS at ℂ | family (A): `AddMemClass` `⟨a+b, add_mem⟩` proj + `Pi` add beta; (i)+(ii) | 6-12 | OK |
| 91 | `mul_apply` | `(F * G) p = F p * G p` | as above with `Mul` | family (A) (`MulMemClass`) | 6-12 | OK |
| 93 | `sub_apply` | `(F - G) p = F p - G p` | as above with `Sub` | family (A); the subtype `Sub` is **structural** (`Subgroup/Defs.lean:190-191` `to_additive`; `coe_sub := rfl` at :199) so no `a + -b` detour is needed — the ℂ side is never re-derived | 6-14 | OK |
| 95 | `neg_apply` | `(-F) p = -F p` | `Neg` | family (A) (`NegMemClass`, `Subgroup/Defs.lean:73-74, 164`) | 6-12 | OK |
| 97 | `zero_apply` | `(0 : AxisFunction R U) p = 0` | LHS `ZeroMemClass` zero → `Pi.instZero` `fun _ => 0`; RHS `(0 : ℂ)` | (i)+(ii); the argument `p` is **discarded** by the constant function | 5-12 | OK |
| 99 | `one_apply` | `(1 : AxisFunction R U) p = 1` | `OneMemClass` + `Pi.instOne` | as :97 | 5-12 | OK |
| 128 | `restrict_apply` | `restrict hSR F p = F p` | LHS `restrict` (:120-126) is a `Subtype.mk` literal | family (D): 1 delta + 1 projection (+1 beta if the coe was eta-expanded); `Prop` second field killed by proof irrelevance | 3-5 | OK |
| 435 | `complexProfile_add` | `complexProfile (F+G) p = complexProfile F p + complexProfile G p` | `complexProfile` (:281-282), non-recursive | family (B)+(A); `Real.sqrt p.1` identical atom on both sides, never evaluated | 8-16 | OK |
| 437 | `complexProfile_sub` | same with `-` | as :435 / :93 | family (B)+(A) | 8-18 | OK |
| 439 | `complexProfile_mul` | same with `*` | as :435 | family (B)+(A) | 8-16 | OK |
| 441 | `complexProfile_neg` | `complexProfile (-F) p = -complexProfile F p` | as :435 / :95 | family (B)+(A) | 8-16 | OK |
| 443 | `complexProfile_pow` | `complexProfile (F ^ k) p = complexProfile F p ^ k` | `Monoid.npow` on the subtype vs on ℂ | family (B)+(A); **`k` stays symbolic**: subtype `Pow` = `⟨fun a n => ⟨a.1^n, _⟩⟩` (`Submonoid/Defs.lean:364-365`), `Pi.monoid.npow = fun n x i => x i ^ n`, so `k` is only *carried*; `npowRec` is NOT entered and there is no `Nat` recursion | 8-18 | OK |
| ★445 | `complexProfile_zero` | `complexProfile (0 : AxisFunction R U) p = 0` | as :97 through `complexProfile` | family (B)+(A) | 6-14 | OK |
| 447 | `complexProfile_one` | `complexProfile (1 : AxisFunction R U) p = 1` | as :99 through `complexProfile` | family (B)+(A) | 6-14 | OK |
| 449 | `complexProfile_realConstant` | `complexProfile (realConstant R U b) p = (b : ℂ)` | LHS `algebraMap` chain; RHS `Complex.ofReal b` | family (C): the load-bearing Mathlib fact is `algebraMap ℝ ℂ = ((↑) : ℝ → ℂ)`, itself `rfl` (`LinearAlgebra/Complex/Module.lean:109-110`) | 15-35 | OK |
| 451 | `complexProfile_parameter` | `complexProfile (parameter R U) p = p.2` | LHS `parameter` (:109-114) is `⟨Prod.snd, …⟩`; so LHS ⟶ `Prod.snd (Real.sqrt p.1, p.2)` | (i): **projection of an explicit `Prod.mk`** ⟶ `p.2`; the discarded first component means `Real.sqrt` is not even looked at | 4-8 | OK |
| 974 | `sequence_profile` | `profile (sequence … n i) = profile (hierarchy … n i)` — "restriction to the common core radius does not change the profile" | LHS head `profile` (:278-279) then `sequence` (:969-972, **non-recursive**: `fun i => restrict … (hierarchy … n i)`); RHS `profile` then `hierarchy` (:942-946, `WellFounded.fix`) | delta `profile` (both sides), delta+beta `sequence`, 1 `Subtype` projection through `restrict` ⟶ both sides are literally `((hierarchy … n i).1 (Real.sqrt p.1, ↑p.2)).re`. **`hierarchy … n i` is an OPAQUE ATOM occurring identically on both sides: no `WellFounded.fix`/`Acc.rec` step, and none is possible since `n` is a variable.** Long statement = long argument list only | 4-6 | OK |

### `NavierStokes/GlobalSlowProfiles.lean`

| line | name | what it says | two sides / head symbols | mechanism | ~steps | verdict |
|---|---|---|---|---|---|---|
| 76 | `add_apply` | `(f + g) w = f w + g w` | `EvenProfile` = `↥(regularAlgebra S)` (:62), `Field = ℝ × ℝ → ℝ` (:26) | family (A) | 6-12 | OK |
| 78 | `mul_apply` | `(f * g) w = f w * g w` | as :76 | family (A) | 6-12 | OK |
| 80 | `sub_apply` | `(f - g) w = f w - g w` | as :76 | family (A), structural subtype `Sub` | 6-14 | OK |
| 82 | `neg_apply` | `(-f) w = -f w` | as :76 | family (A) | 6-12 | OK |
| 84 | `zero_apply` | `(0 : EvenProfile S) w = 0` | `ZeroMemClass` + `Pi.instZero` | (i)+(ii), `w` discarded | 5-12 | OK |
| 85 | `one_apply` | `(1 : EvenProfile S) w = 1` | `OneMemClass` + `Pi.instOne` | as :84 | 5-12 | OK |
| 97 | `constant_apply` | `constant S c w = c` | LHS `constant` (:94-95, `algebraMap ℝ (EvenProfile S) c`); RHS the variable `c` | family (C) with base case `Algebra.id ℝ` whose `toFun x := x` is overridden on purpose (`Algebra/Algebra/Defs.lean:391-396`) | 15-30 | OK |
| 213 | `inverseDenominator_apply` | `inverseDenominator d w = (PositiveAxisSystem.ell h w.2)⁻¹` | LHS `inverseDenominator` (:209-211) = `inverse (1 - constant S (2*h) * parameter S ^ 2) …`, `inverse` (:106-108) = `⟨fun w => (f w)⁻¹, …⟩`; RHS `ell` (`PositiveAxisSystem.lean:54`) = `1 - 2*h*eta^2` | **the heaviest site**: 1 proj through `inverse`, then families (A)+(C) on `1`, `-`, `*`, `^2`, `constant`, `parameter` (`⟨Prod.snd,…⟩`, :103-104), then 1 delta of `ell`. Both sides end as `(1 - 2*h*w.2^2)⁻¹` at ℝ with the *same* ℝ instances; the exponent `2` and the numeral `2` are only carried (no `npowRec`, no `Nat` arithmetic). Still purely (i)+(ii) — non-recursive, terminating | 30-60 | OK |
| 1201 | `xProfile_add` | `xProfile (f+g) w = xProfile f w + xProfile g w` | `xProfile` (:1134-1135), non-recursive | family (B)+(A); `Real.sqrt (2*w.1)` identical atom on both sides, never evaluated | 8-16 | OK |
| 1203 | `xProfile_sub` | same with `-` | as :1201 | family (B)+(A) | 8-18 | OK |
| 1205 | `xProfile_mul` | same with `*` | as :1201 | family (B)+(A) | 8-16 | OK |
| 1207 | `xProfile_constant` | `xProfile (constant S c) w = c` | as :97 through `xProfile` | family (B)+(C); the `Real.sqrt (2*w.1)` argument is **discarded** by the constant function | 15-32 | OK |

## Ordinary mathematical suspicion (the non-kernel half of the brief)

* **None of the 30 statements is vacuous**: every one is a universally quantified equation with no
  hypothesis that could be false. The only hypotheses present are `hSR : S ≤ R` (SR:128),
  `hcore/hbuffer` positivity (SR:974) and `d : Domain S h` (GSP:213); none of them is used to make the
  claim trivial, and none of them is unsatisfiable (`Domain` is inhabited — see the sibling report's
  `LocalHierarchy`/`exists_local_slow_hierarchy` row, `SlowRecursion.lean:1256-1287`).
* **No name overclaims.** Each name is `<thing>_<op>`/`<thing>_apply` and the statement is exactly the
  corresponding pointwise identity. The one name worth reading twice is `sequence_profile` (SR:974):
  it does **not** claim anything about the recursion, only that `restrict` is value-preserving. That is
  the honest content, and it is the same fact as `restrict_apply` (:128).
* **No junk-value exploitation in these sites.** The two junk-default definitions in these files
  (`lowerHistory`'s `else 0`, SR:918-923; `previousAxial/previousPhi/previousBeta`'s defaults,
  GSP:770-780) are *not* the subject of any bare-`rfl` theorem — their `dite` is discharged by
  `dite_eq_left` in tactic proofs (`lowerHistory_apply`, SR:925-929) and their unread-ness is proved
  by the congruence lemmas the sibling report lists (SR:993-1018; GSP:946-1006). Nothing in my subject
  silently reads a junk branch.
* One stylistic remark, not a finding: SR:89-100, :435-452 and GSP:76-85, :1201-1208 are `@[simp]`
  boilerplate written without blank lines between declarations, which is why an automatic line-based
  site list can miss neighbours (as happened for :86 and :445 above).

## Residue — what I could not check, and why

1. **No elaboration.** I could not run Lean, so I cannot exhibit the *actual* proof terms nor the
   coercion the elaborator inserted at `SlowRecursion.lean:122` (`Subtype.val F` vs its eta-expansion).
   Both possibilities are ≤3 kernel steps, so the verdicts do not depend on it.
2. **Mathlib version skew.** My instance citations are from Mathlib `8a178386ff` (v4.29.0) while NSE
   pins `v4.34.0-rc2`. Each cited definition is accompanied by a Mathlib `… := rfl` lemma of exactly
   the shape my argument needs, so a re-auditor with the pinned Mathlib can re-check the five
   load-bearing citations quickly: `Submonoid/Defs.lean` `instPow`/`coe_pow`,
   `Subgroup/Defs.lean` `div`/`coe_div` (+`to_additive` sub), `Algebra/Group/Pi/Basic.lean`
   `Pi.monoid.npow`, `Subalgebra/Basic.lean` `Subalgebra.algebra`/`coe_algebraMap`,
   `LinearAlgebra/Complex/Module.lean` `instAlgebraOfReal`/`coe_algebraMap`.
3. **Step counts are estimates**, given as ranges, and only for the instance-projection chains; they
   are all O(size of the Mathlib algebraic hierarchy), i.e. constant per site, with **no** dependence
   on any numeral or on the recursion depth. That is the only property that matters for threat
   vectors (1) and (2), and it holds for all 30 sites.
