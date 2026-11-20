# NODE-LANDAU: the analytic endgame (`zeroFreeAll_of_topG` -> `zeroFreeOn_of_tiedWin_cyc` -> `formB`)

Abbreviations: `TGC/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`,
`DL/` = `Development/AutomorphicArithmetic/DedekindLFunctions/`, `LT/` = `DL/LandauTheorems/`,
`PC/` = `Development/AutomorphicArithmetic/PrimitiveCosets/`, `CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`.

## 1. Statement

### 1a. The function Gm (question a)

Lean says (`TGC/ExplicitFormulaErrorOfHostConditions.lean:8-38`, `Formalism/StatementOC.lean:11-13`,
`TGC/Analytic.lean:11-24`, `TGC/PrimePairSizeCondition.lean:39-45`):

- A `Level` is a `KSet` (a `Finset` `KEPT` of primitive characters with `1 ∈ KEPT`, closed under inverse, an optional
  distinguished odd real character `psK`) plus a natural number `o`.
- `wt ψ = 1` if `psK = some ψ`, otherwise `(3o+1)^{-1}`. `Nt = KEPT \ {1}`.
- **Gm(y) = Gz(y) + Σ_{ψ ∈ Nt} wt(ψ) · Re gχ_ψ(y)**, where
  - Gz(y) = Σ_{1≤n≤y} Λ(n)(y/n − 1) − y log y + (1+γ) y,
  - gχ_ψ(y) = Σ_{1≤n≤y} Λ(n) ψ(n) (y/n − 1) + y · L'(1,ψ)/L(1,ψ) (for ψ ≠ 1; for ψ = 1 it is Gz).
- `Level.cyc ψ` (`:105-121`): KEPT = { primitive character inducing ξ : ξ ∈ ⟨ψ⟩ }, `psK = none`, `o = |⟨ψ⟩|`. So for
  the cyclic level, **Gm(y) = Gz(y) + (3o+1)^{-1} Σ_{ξ ∈ ⟨ψ⟩, ξ* ≠ 1} Re gχ_{ξ*}(y)** with ξ* primitive.

Mellin/Laplace picture (Lean: `LT/poleData.lean:137-143, 248-...`). With g(u) = Gm(e^u),
Φ(s) = ∫_0^∞ g(u) e^{-su} du = ∫_1^∞ Gm(y) y^{-s-1} dy. For each character the ramp sum has transform
−(L'/L)(s,χ)/(s(s−1)) (I infer the exact shape; the Lean records only the outcome): the main terms
`y L'/L(1,χ)`, resp. `−y log y + (1+γ) y`, cancel the pole at s = 1 exactly, so Φ continues meromorphically to Re s > 0
with poles only at zeros ρ of L(s,χ_i) or of L(s, χ̄_i), and `poleData_char` (`LT/poleData.lean:137-143`) says the
principal part of the single-character transform at ρ ≠ 0 is **m_ρ · (−1/(ρ(ρ−1))) / (s−ρ)**, m_ρ = order of the zero.
Re is taken by averaging χ and χ^{-1} (`poleData.lean:248`: Φ = Σ_i a_i/2 (Φ_{χ_i} + Φ_{χ_i^{-1}})).

### 1b. formB (question b)

`UpperTheory.Comparison₂.formB : ∀ Λ : Level, Λ.FormB` (`PC/Imports.lean:8-19`), with
(`TGC/Window.lean:7-8, 30-33`)
```
HasWindows S la := ∀ y, ∃ Y ≥ y, ∀ x, Y ≤ x → x ≤ Y^la → x ∈ S
FormBAt la := ∀ θ, 0 < θ → θ < 1 → HasWindows {x | Λ.Gm x ≤ x^θ} la → Λ.ZeroFreeAbove θ
FormB := ∀ la > 1, FormBAt la
```
In words: **for every Level Λ, every la > 1 and every θ ∈ (0,1): if there are arbitrarily large Y such that
Gm(x) ≤ x^θ for all x ∈ [Y, Y^la], then L(s,ψ) ≠ 0 for every ψ ∈ KEPT and every Re s > θ.**
The bound is one-sided (upper only), required only on a sequence of windows, constant 1, nothing uniform (Λ, θ, la
fixed). Λ is arbitrary: the weights and the group structure are not used, only that every weight is > 0.

It is a corollary of the general theorem (`LT/ZeroFreeOfRpowWindow.lean:11-14`, `DL/CharFamily.lean:68-89`):
`Deduction.zeroFree_of_rpow_window`: for any finite family of Dirichlet characters χ_i (mod N_i, with N_i = 1 or
χ_i ≠ 1) and weights a_i > 0, with Gm_F(y) = Σ a_i Re Gchi(χ_i, y), if 0<θ<1, δ>0 and for all Y0 there is Y ≥ Y0 with
Gm_F(y) ≤ C y^θ on [Y, Y^{1+δ}], then L(s,χ_i) ≠ 0 for all i and Re s > θ. `level_family` (`PC/LevelFamily.lean:41-52`)
identifies Level.Gm with Gm_F (weight 1 on ψ = 1) and the two zero-free predicates.

### 1c. `zeroFreeOn_of_tiedWin_cyc` (`TGC/TopWin.lean:90-93`)

For a predicate Q on primitive characters and la > 1: if for every ψ with Q ψ, writing Λ = Level.cyc ψ,
1. `ChebyshevInequalityOnWindows Λ` (`TopWin.lean:26-28`): for all reals eD, eL, all ε > 0 and every family Fm with
   `EFamC Λ (core Fm)` and `Tied Fm eD eL K cHH eK CL x` for all x ≥ x0 in Win, there is x1 with
   Gm(x) ≤ x^{1/2 + (eD+eL+7)ε} for all x ≥ x1 in Win;
2. `Λ.FormB`;
3. `ChebyshevInequalityAtWindowScale la Λ` (`TopWin.lean:30-32`): ∃ eD, eL, ε1 > 0 such that for every ε ∈ (0, ε1)
   some family Fm satisfies EFamC Λ, has la-windows (`HasWindows Win la`), and is Tied on its windows beyond some x0,

then ZeroFreeOn Q: L(s,ψ) ≠ 0 for Re s > 1/2.

`zeroFreeAll_of_topG` (`CB/ZeroFreeAllOfTopG.lean:26-34`) instantiates Q = True, Fam = FamP, Tied = ChainTied,
item 1 := `level_gm_le_on_family_scales`, item 2 := `formB`, item 3 from `TopG` applied to `GChi ψ` and `hS ψ`.

## 2. Argument

### 2a. Glue (`level_of_tiedWin`, `TopWin.lean:68-81`)
Fix ψ' ∈ KEPT and s with Re s > 1/2. Put m = min(Re s − 1/2, 1/2), θ = 1/2 + m/2. Choose ε < ε1 with
(eD+eL+7)ε ≤ m/2 (`exists_small_eps`, `:59-66`). Item 3 gives a family whose Win contains windows [Y, Y^la] for
arbitrarily large Y; item 1 gives Gm(x) ≤ x^{1/2+(eD+eL+7)ε} ≤ x^θ there (x ≥ 1). FormB gives no zero with Re > θ,
and θ < Re s. Correct.

### 2b. Proof of the windowed Landau theorem (`lemmaL`, `LT/lemmaL.lean:13-24`; `landau_window`, `LT/landauWindow.lean:83-166`)
Reconstructed from the Lean, and in my judgement a correct theorem with a correct proof. Work in u = log y; the window
is [U, (1+δ)U] (`windowHypU_of_windowHyp`). Write a_k(z) = (−1)^k Φ^{(k)}(z)/k! = ∫_0^∞ g(u) K_k(u) e^{−i Im z·u} du,
K_k(u) = u^k e^{−σu}/k! ≥ 0, z = σ + iγ, σ > 2 (`landau_coeff`). These are the Taylor coefficients of Φ at z.

1. **Upper bound from the one-sided hypothesis (positivity of the kernel, not of coefficients).** On the window put
   R = C e^{θu} ≥ g. Then |∫_W g K e^{−iγu}| ≤ ∫_W R K + ∫_W (R−g) K = 2∫_W R K − ∫_W g K, i.e.
   |a_k(σ+iγ)| + Re a_k(σ) ≤ 2∫_W R K + tails. Since sup_u u^k e^{−(σ−θ)u}/k! ≤ (σ−θ)^{−k},
   2∫_W R K ≤ 2 (σ−θ)^{−k} ∫_W R e^{−θu} ≤ 2 (σ−θ)^{−k} e^{ηU} (`landau_window_ineq`, `landau_window_key:40-73`).
   Tails: |g(u)| ≤ C0 e^{2u} (`Gchi_growth`), and a Chernoff bound (`landau_tails`) chooses σ = σ(δ) large and k ≥ U
   with the kernel's mass concentrated in [U,(1+δ)U], so the tail is ≤ C/σ^k. Result: for every η > 0 there are
   arbitrarily large U and k ≥ U with |a_k(σ+iγ)| + Re a_k(σ) ≤ C' e^{ηU} (σ−θ)^{−k} for all γ.
2. **Lower bound from a zero.** Suppose ρ0 is a zero with Re ρ0 > θ. `landau_dichotomy` (`LT/LandauDichotomy.lean:24`):
   either (i) the disc B(σ, D), some D ≤ σ−θ, is pole-free but some pole has σ − Re ρ1 < D; or (ii) there is a real
   pole β > θ that is the only pole in B(σ, r), r ≤ σ−θ.
   - Case (ii): residue at real β is −m/(β(β−1)) · Σ a_i(...)/2 > 0 (`PoleData.pole`, `LandauZeroFreeCriterion.lean:22`:
     real poles have positive real residue). So Re a_k(σ) ≥ c/(σ−β)^{k+1} − M/e^k with e > σ−β, while
     |a_k(σ)| ≥ 0. Since σ−β < σ−θ this beats C' e^{ηU}(σ−θ)^{−k} for small η and large k ≥ U (`landau_window_contra`).
   - Case (i): `landau_nearest` picks γ so that one pole ρ is the unique nearest singularity to z = σ+iγ, at distance
     d < D ≤ σ−θ. Then |a_k(z)| ≥ |c|/d^{k+1} − M/e^k (`landau_pole_asym`), and Re a_k(σ) ≥ −M'/e^k by Cauchy on the
     pole-free disc (`landau_cauchy`). Same contradiction. Here c ≠ 0 needs non-cancellation: the residue at ρ is
     −(1/(ρ(ρ−1))) Σ_i (a_i/2)(m(ρ,χ_i) + m(ρ,χ_i^{-1})), a sum of same-sign terms since a_i > 0.
3. Re s ≥ 1 is handled by Mathlib's non-vanishing (`charFamily_LFunction_ne_zero_of_one_le_re`).

So the positivity used is: (A) the kernel u^k e^{−σu} ≥ 0 together with the one-sided bound, (B) a_i > 0 so residues
at a common zero do not cancel, and (C) real zeros produce positive residues (a real zero β pushes Gm *up*, by
+y^β/(β(1−β))). **Positivity of the averaged coefficients Λ(n)(1 + (3o+1)^{-1}Σ Re ξ(n)) is NOT used**; the parent's
inference is wrong on this point. The windowed form works because the k-th derivative kernel localises the Laplace
integral to a log-window [U, (1+δ)U] for any fixed δ, provided σ is taken large in terms of δ. I could not check the
interior of `landau_tails`, `landau_nearest` and `poleData_char` line by line (budget), but their statements are exactly
what the argument needs and are standard.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `level_gm_le_on_family_scales` | `PC/LevelGmLeOnFamilyScales.lean:28` | item 1: EFamC + Tied on windows ⇒ Gm(x) ≤ x^{1/2+(eD+eL+7)ε} | all RH-strength content | core |
| `TopG` (hypothesis) + `hS : ∀ψ, HostExW la (GChi ψ).req` | `CB/ZeroFreeAllOfTopG.lean:12-14, 26` | item 3: families with la-windows meeting ChainTied exist for every small ε | existence of the input | core |
| `formB` / `zeroFree_of_rpow_window` / `lemmaL` / `landau_window` | `PC/Imports.lean:8`; `LT/ZeroFreeOfRpowWindow.lean:11`; `LT/lemmaL.lean:13`; `LT/landauWindow.lean:83` | windowed one-sided Landau, 2b | deduction | standard (Landau's theorem via Taylor coefficients; windowed variant, reconstructed above, correct) |
| `poleData` / `poleData_char` | `LT/poleData.lean:248, 137` | Laplace transform of Gm(e^u) meromorphic in Re s>0, poles = zeros, residue m·(−1/(ρ(ρ−1))) | explicit-formula input | standard |
| `landau_tails`, `landau_window_ineq`, `landau_coeff` | `LT/landauTails.lean:80`; `LT/landauWindowIneq.lean:27`; `LT/LandauCoeff.lean:10` | Chernoff tail for gamma kernel; positivity inequality; Taylor coeff = Laplace moment | technical | standard |
| `landau_dichotomy`, `landau_nearest`, `landau_pole_asym`, `landau_cauchy` | `LT/LandauDichotomy.lean:24`; `LT/LandauNearest.lean:36` | geometry of nearest singularity; Taylor-coefficient asymptotics | technical | glue |
| `level_family` | `PC/LevelFamily.lean:41` | Level.Gm = CharFamily Gm, zero-free predicates agree | identification | glue |
| `level_of_tiedWin`, `exists_small_eps` | `TGC/TopWin.lean:68, 59` | 2a | glue | glue |

Target for the next node: the caller must supply, for each primitive ψ and Λ = Level.cyc ψ, (1)
`ChebyshevInequalityOnWindows FamP.toFamCore ChainTied Λ` and (3) `ChebyshevInequalityAtWindowScale ... (3/2) Λ`
(from TopG). FormB is discharged unconditionally.

## 4. Oddities

- `ChebyshevInequalityOnWindows` (`TopWin.lean:26-28`) quantifies over **all real eD, eL**. Unconditionally Gm is not
  ≤ x^θ on windows for any θ < 1/2 (by formB itself, since ζ has zeros on Re s = 1/2 and ζ is always in KEPT with
  weight 1). So if ChainTied can hold with eD + eL + 7 < 0, item 1 would be false; the next node must check that
  ChainTied forces eD + eL + 7 > 0 (or is otherwise unsatisfiable there).
- ζ (ψ = 1) is always in the level with weight 1, so item 1 alone (on any la-windows) implies RH for ζ through formB.
  The level/group averaging and the weight (3o+1)^{-1} play no role in formB; they can only matter in item 1.
- `CharFamily` does not require primitivity, so `ZeroFree` would include only extra zeros on Re s = 0; harmless.
- formB is stronger than "for all large x": it only needs a sequence of windows [Y, Y^{la}], which is what the families
  provide. I found it a correct theorem.
- No `sorry`/`axiom` in `LT/` (searched).

## 5. Coverage
Read: `CB/ZeroFreeAllOfTopG.lean:1-38`; `TGC/TopWin.lean:1-140`; `TGC/Window.lean:1-50`;
`TGC/ExplicitFormulaErrorOfHostConditions.lean:1-140`; `TGC/Analytic.lean:1-40`; `TGC/PrimePairSizeCondition.lean:39-46`;
`Formalism/StatementOC.lean:1-30`; `PC/Imports.lean:1-19`; `PC/LevelFamily.lean:1-52`; `DL/CharFamily.lean:1-49`;
`DL/LandauZeroFreeCriterion.lean:1-66`; `LT/ZeroFreeOfRpowWindow.lean`, `LT/lemmaL.lean` (whole);
`LT/landauWindow.lean:1-170`; `LT/poleData.lean:137-175, 241-330`; `LT/LandauDichotomy.lean:1-30`;
`LT/LandauNearest.lean:1-30`; `LT/landauTails.lean:1-25`; declaration lists of the other `LT/` files.
Not opened: bodies of `landau_tails`, `landau_nearest`, `landau_pole_asym`, `landau_cauchy`, `landau_growth_contra`,
`poleData_char` past line 175, `Gchi_growth`, `windowHyp_of_rpow`, `level_gm_le_on_family_scales`.
