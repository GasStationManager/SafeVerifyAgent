# NODE-SERVED: which inert primes carry divisibility, what the rest cost, and the supplier of `ThinScales`

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
`IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`, `SKB` = `Formalism/SizeWindowBrackets/SecondKindBucket.lean`,
`WSS` = `Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean`, `PCL` = `Formalism/SizeWindowBrackets/PrimeClassLossHypothesesSatisfiable.lean`,
`SS` = `Formalism/LocalToGlobal/GlobalTheory/SuppSat.lean`, `P4` = `Formalism/LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean`,
`PC` = `Formalism/SharpRestriction/ParConsts.lean`, `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`,
`DH` = `Formalism/LocalRingCardinality/DataHost.lean`, `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`,
`ZG` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean`,
`AN` = `.../TotientGaloisClasses/Analytic.lean`, `TSI` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean`,
`PG` = `Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean`, `MSB/` = `Development/AutomorphicArithmetic/MeanSquareBounds/`.

## 0. Summary

**Part 1 (non-served inert primes): closes, with numbers.** The caller's conjecture is right in substance, but the
Lean's classification is finer than "served or not".

- Gal(E/ℚ) = G0 × A, with G0 = {±1}². A is an abelian group with a cyclic subgroup A0 = ⟨a0⟩ and a surjection
  h : A ↠ HGrp e = (ℤ/2^{e+2})^×/±1 ≅ ℤ/2^e (`ZG:15-23,55-62`).
- The inert-in-K primes fall into two G0-classes:
  - *signal*: (−d/p) = −1 and (p/q)-sign +1, so Frob = ((1,−1), h);
  - *inertClass*: inert in both K and ℚ(√−q), so Frob = c0·h (`DH:24-37`).
- The hermitian form at p is split iff c ∉ ⟨Frob_p⟩:
  - for signal p this always holds;
  - for inertClass p it holds iff ord(hP) is even.

  The anisotropic inert primes are therefore exactly the inertClass primes with ord(hP) odd. That is `hP = 0` together
  with `IsCs` (`IRZ:155-170`).
- Their Chebotarev density inside the inertClass coset is 1/|A₂| ≤ 2^{−e} ≤ x^{−2}. Among all primes it is 1/(4|A₂|).
- The Lean does **not** charge them by Chebotarev. It drops every inertClass prime with ord(hP) < x^{ε/4}, which
  includes all odd-order ones. It then bounds Σ log p/p over those primes by elementary counting in ≤ 2J residue classes
  mod 2^{e+2}. This uses Frob ↦ p mod 2^{e+2}/±1 (`pc_ord'`).
- The resulting charge is ≤ 4K·x^{−1+11ε/12}·U with U = |TT|·m·b. That is inside the explicit budget sg·U = 100K·x^{−1+4ε}·U.
  Every other dropped class (band, second-kind, high, bad orbits, d) is likewise ≤ x^{−1+O(ε)}·U.
- **But** "not dropped" is much larger than "kernel-served". The Lean also credits a **Hecke-free gain g0⁺**, which is a
  copy of the ASK summand, at:
  - every signal prime p ≤ X″;
  - every even-order inertClass prime between X′ and X″;
  - the bad orbits of Cand primes.

  These have total mass ≈ m·|TT|·a·log X″, far above the budget. It is delivered not by the GIdx kernel
  but by `OrbitsWithoutOperator` (WJS:184-189). That clause is the real open child of this node.

**Part 2 (`ThinScales`): closes.**
- The supplier is `QH.thinH` (`MSB/GaussSumFunctionEq.lean:55`). Its proof chain is:
  - `thin` (`MSB/Thin.lean:10`);
  - `psi_thin` (de la Vallée Poussin: |ψ(u,χ)| ≪ u(log u+λ)²·exp(−c log u/(λ+√log u)), with λ ≥ log N);
  - the project's own proved zero-free region with Landau exceptional zero (`zFRDirichlet`,
    `Formalism/LandauZeroFreeBounds/NoZeroComplex.lean:32`);
  - `small_zeros` / `RealBox` for the real characters.
- The parameters work: log y/λ ≥ x^{ε/3}/(2x^{ε/5}log²x) = x^{2ε/15}/(2 log² x) ≫ x^{ε/8}.
- No truncation height is needed. G is written as a tail integral of ψ, and the ψ-bound is integrated from y to ∞.
- ell(ψ) is pinned **exactly** to L′/L(1, χ_ψ) by `HostAddCharCompatible` (`PrimitiveCosets/CoreAtH.lean:18-20`), not merely
  implicitly. gChi itself uses the true L′/L(1) (`AN:23-24`).

## 1. Statement

### 1.1 Prime classes and "served"

- `primeClass` (`DH:34-39`) sends p to one of:
  - ram2 if p ∈ small;
  - ramQ if p = q;
  - ramD if p = d;
  - splitK if (−d/p) = 1;
  - signal if psAt p = 1;
  - inertClass otherwise.
- ASK runs over `PsAt` = primes p < bndP with cls ∈ {signal, inertClass} (`SS:30-32`). Here bndP = max(a(1+…), X″)+1.
- **`GIdx`** (`Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:68-69`) requires all of: p prime, p ≥ 5,
  cls p = inertClass, HNeZero, p ∉ levelPrimes, p ∤ T. This is only the domain on which local kernels are built. It
  does **not** contain the evenness condition.
- **hP** (`IRZ:146-147`) is the A-component of a Frobenius.
- `HEv` means ord hP is even. `IsCs` means inertClass ∧ ord hP odd ∧ hP ≠ 0. Then `class_zero_trichotomy` gives
  HEv ∨ hP = 0 ∨ IsCs (`IRZ:149-163`).
- **`Cand`** (`IRZ:279-281`) is: p < X′, inertClass, ord hP ≥ x^{ε/4}, and (p ≥ p0 ⇒ p ∉ band).
  - VV = goodReps if Cand ∧ Sig ≤ x^{−ε}, and ∅ otherwise (`IRZ:291-292`).
  - Kernel-served, i.e. Hecke gain gU, means VV ≠ ∅.
- **`NoGain` = `L.drop`** (`PC:24-29`, `SS:97`). p is dropped iff one of the following holds:
  - (A) p < X′(1+Cr·ρ), p is inertClass, and [ord hP < x^{ε/4}, or p^i lies in the band around X′, or (Cand ∧ Sig > x^{−ε})];
  - (B) p > X″;
  - (C) p is not inert;
  - (D) IsCs.
- **`clAt`** (`SS:43-47`): served iff p ∉ drop. Otherwise high (p > X″), second (Cand ∧ Sig > x^{−ε}), or first (the rest).
- `gainQ` = 0 on drop and gainP otherwise. **`gainP`** (`IRZ:355-359`) is
  - 0 if (inertClass ∧ hP = 0) or p > X″;
  - otherwise Σ_{t0∈VV} max(gU − Pr, g0⁺) + Σ_{t0∈reps∖VV} g0⁺.

### 1.2 The loss inequality used (`SecondKindLoss`, SKB:261-297; `SplitClasses` SKB:73-85)

ASK − GaW is bounded by:
- Σ_served 2 log p·servedLoss (SizeData₂ on TTp, plus the whole ask on TT∖TTp);
- the whole ask on first, second and high primes;
- the d-term.

Each whole ask is bounded by `TopLoss`: 2 log p·ask ≤ 4a log p/p (SKB:110-113).
The hypotheses are bundled in `PrimeClassLossHypotheses` (PCL:86-95):
- lhsW ≤ x^{−9};
- badPrimeLogWeightedCount ≤ |TT|·x^{−2+ε};
- `FirstHyp` (WSS:297-301): a first-kind p either has p ≤ max(Y, X″) and ord(hOf e p) < x^{ε/4}, or has p^i in the band.

### 1.3 `ThinScales` (`Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:55-56`)
```lean
def ThinScales (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (X' θ : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, ∀ y : ℝ, X' / 3 ≤ y → ‖GPsi D ell ψ y‖ ≤ y * θ
```
- On the host it is `ThinOK s c H` (TSI:61-63): for every primitive χ factoring through Gal(E/ℚ) and every y ≥ e^{x^{ε/3}}/3,
  ‖gChi χ y‖ ≤ y·e^{−c x^{ε/8}}.
- Here gChi χ y = Σ_{n≤y} Λ(n)χ(n)(y/n−1) + y·L′/L(1,χ) for χ ≠ 1, and G(y) = ψ₁(y) − y log y + (1+γ)y for χ = 1 (AN:18-24).
- `thinScales_iff_hostBound` (TSI:65) identifies it with `ChebyshevCharacterBound` (AN:146-148). It is a clause of `HostGood` (TSI:103).

## 2. Argument

### Part 1(a): classification of inert primes, with densities

Write Frob_p = (g0, h) ∈ G0 × A, with c = cc = ((−1,−1), 1).

| class | Frob | c ∈ ⟨Frob⟩? | partners of a top t | Lean treatment | density among primes |
|---|---|---|---|---|---|
| signal | ((1,−1),h) | never (the first coordinate of Frob^k is 1) | thick (e odd, t+e·h ∈ T2+u0) or thin | **not dropped** for p ≤ X″; VV = ∅; gain = Σ g0⁺; TTP = TT | 1/4 |
| inertClass, ord h even, ≥ x^{ε/4}, p < X′, Sig ≤ x^{−ε}, not band | c0·h | no | top or thin | **kernel-served**: gU on goodReps, g0⁺ on bad reps; bad tops charged as BAD | ≈ 1/4 |
| inertClass, ord h even, ≥ x^{ε/4}, X′(1+Crρ) ≤ p ≤ X″ | c0·h | no | top (ask 0, since a/p < b′) or thin | not dropped; VV = ∅; gain = Σ g0⁺ | — |
| inertClass, ord h even, < x^{ε/4} | c0·h | no (split, but short orbit) | | dropped (first) | ≤ ¼·#{ord(h(·)) < x^{ε/4}}/2^e ≤ ¼·2x^{ε/4}/2^e |
| inertClass, h = 0 or ord h odd (anisotropic) | c0·h | **yes** | t+e·h | dropped (first if p < X′(1+Crρ); IsCs at any p ≤ X″; h = 0 above X′ has ask 0 since its partner is the top itself) | 1/(4\|A₂\|) ≤ ¼·2^{−e} ≤ ¼x^{−2} |
| inertClass, p^i in band around X′ (p ≥ p0) | | | | dropped (first) | log X′ bands of relative width ρ ≤ x^{−2} |
| Cand ∧ Sig > x^{−ε} | | | | dropped (second) | Markov from mean Sig ≤ x^{−12} |
| p > X″ | | | | high | ask ≈ 0 |

The conjecture "non-served ⇔ z = Frob·c has odd order" holds for the *anisotropy* condition: z = ((1,1),h) for
inertClass, so ord z = ord h (NUMTEST4 §A). Its density is 1/|A₂| relative to the inertClass coset. A₂ ⊇ a lift of
HGrp e, since h is surjective onto a 2-group, so |A₂| ≥ 2^e ≥ x² (Windows: x² ≤ 2^{e₂}, WSS:105).

Signal primes never have this problem, and the Lean never drops them. The Lean's own cut is coarser: it drops all
orders < x^{ε/4}, which avoids orbits too short for the window machinery.

**How the Lean bounds the dropped first-kind primes.** It does not use Chebotarev in E. It uses three facts:
1. `pc_ord'` (used at P4:868-870) gives h(hP) = hOf e p, the class of p in (ℤ/2^{e+2})^×/±1, and ord(hOf) | ord hP. So
   ord hP < J implies ord(hOf e p) < J. For IsCs, h(hP) = 0 by `even_addOrderOf_hP_of_pow_le` (P4:893).
2. `OrdersBound` (`RandomSubsetCounterexample.lean:18-20`, proved at `FourNotDvdOddSqAddOne.lean:140`): ord(hOf l) ≤ J
   implies l ≥ 4·2^e/J − 1.
3. `OrdersSumY` (`:28-32`, proved from `OrdersIff` at `PmModulusFacts.lean:252`):
   Σ_{l≤Y, ord(hOf l)≤J} log l/l ≤ C·J·log²(2^eY)/2^e.

This is elementary counting of integers in the ≤ 2J residue classes ±a mod 2^{e+2} of order ≤ J. It is
unconditional.

### Part 1(b): charges and sizes

Every number below is from `WSS:130-161`, with U = unitU = T·m·b, a = x·b, and the WindowsSat parameters (WSS:117-128):
2^{e₂} ≥ x², J = Jo = ⌊x^{ε/4}⌋, Y ≈ X′ = e^{x^{ε/3}}, X″ = x·n·X′, ρ ≤ x^{−2}, p0 ≥ x^{4}, th = 1/(k x^{13}),
d ≥ x², s₀ = x^{−9}, θ = x^{−ε}. The budget is (2 log 4·C + 13·sg)·U with sg = 100K·x^{4ε}/x.

| bucket | Lean term | size / U |
|---|---|---|
| first, small order (includes all anisotropic inertClass, h = 0, IsCs up to X″) | tOrders = 4mTa·Cord·Jo·log²(2^e·max(Y,X″))/2^e | 4K·x·x^{ε/4}·(x^{ε/3}+O(log x))²/x² ≈ 4K·x^{−1+11ε/12} |
| first, band | tBand = 4mTa·Ib·(4ρ+1/p0)·log(2X′) | ≈ 16·x^{−1+2ε/3} |
| second (Sig > x^{−ε}) | tSecondD = 2amT·x^{−9} | 2x^{−8} |
| bad orbits at kernel-served primes | tOutD = 4amT·x^{−2+ε} (from ChBadp_at = `BadOK`, TSI:41-47) | 4x^{−1+ε} |
| high (p > X″) | tHigh = mT·2log(2X″)(a·th² + w″·th) | ≲ x^{−25} |
| p = d | tD = mT·2a log d/d | ≤ 2x^{−1}log x |

All are ≤ sg·U ≈ x^{−1+4ε}·U. The caller's estimate (density × m|TT|·a·log X′ ≈ x^{−1−8ε+ε/3}·U) agrees up to the
Lean's crude J·log² factor. **The non-served inert primes are a vanishing fraction, and their whole ASK is paid from the
budget. No positive proportion of primes is counted without divisibility.** The charge is the full ask (TopLoss bound
4a log p/p), and the gain there is set to 0 (`nonserved_zero`, P4:684-697).

**What the slope side is still asked to deliver.** These are *not* dropped, and Ga contains gainP = Σ g0⁺ ≈ ASK there:
- signal primes ≤ X″;
- even-order inertClass primes in [X′(1+Crρ), X″];
- the non-good orbits of kernel-served primes.

Their ASK mass is ≈ 2a·log(X″/X′)·(1/4 + 1/4) per top per lift ≈ m·|TT|·a·log x, i.e. ≈ x log x·U. It is **not**
small. It is delivered:
- at GIdx (inertClass) places, by `UAt` (WJS:206-215), whose Σ over reps∖VVs is the g0 term;
- at signal places, which are not GIdx, and at VV = ∅ places generally, by **`OrbitsWithoutOperator`**
  (WJS:184-189 = `NoOperatorOrbitBound`, `Formalism/SharpRestriction/Divisibility/OrbitPlaces.lean:455`):
  for (inertClass ∧ hP ≠ 0) ∨ signal, ¬Exc, p ≤ X″, every x ∈ Sram satisfies ColGe(Σ_j g0S + low).
  `InNP` (WJS:61-63) lets VV = ∅ places use Sram vectors.

Signal places have c ∉ D_p, so the hermitian form is split there and the Gaussian-class mechanism is plausible. But
NUMTEST3/4 tested only inertClass served primes. The non-served control (h = 0, slope 1/(p²−1)) is correctly given gain 0.

### Part 1(c): the remaining small or special primes

- **p = 2**: ram2 (`small`), so not in PsAt (`two_not_inert`, used at `GT/LossRequirementsOfSmallShares.lean:57`).
- **Odd p ≤ splitBound**: split in K (`split_small`, DH:63-64). splitBound ≥ ⌊x^{ez/5}⌋ (`split_tie`, DP2:136). So
  p = 3, and every inert prime < x^{ε/(5J)}, is absent. GIdx's "p ≥ 5" is automatic on PsAt.
- **QS primes**: 4l ≤ splitBound (`small_le`), so they are split.
- **Level primes**:
  - g_i = ππ̄ with π ∈ K, so g_i splits.
  - pde, pde′ and q0 are ≡ 1 mod QS·q·d (HostGood, TSI:108-110). With d ≡ 3 mod 4 this gives (−d/p) = (p/d) = 1, so
    they split. *Inferred* via reciprocity; not a Lean lemma I read.
  - So no level prime is in ASK. `gain_g` (DP2:94) and `Exc` (WJS:37) zero them anyway.
- **T**: `hT : ¬InertK D T` (P4:722), so T is not counted.
- **q**: (−d/q) = 1 (ramQ, split-in-K). It contributes 0 (NODE-CHBALANCE §2a).
- **d**: the askD term with weight log d, bounded by tD.

## 3. Part 2(d,e): `ThinScales` supplier

**Live path.** `hostOfFieldOf` (`Development/AutomorphicArithmetic/ShortNorms/hostOfFieldOf.lean:159-171`) takes
`QH.thinH`. Its inputs are:
- odd part of QS ≤ C0, from QS | lcm(2^{e+2}, M) with M ≤ C0;
- log(QS·q·d) ≤ 2x^{ε/5}log²x (`hN`, from PairWin);
- RealBox, from `BoxW`/`BoxH`, i.e. PairGood.boxes and GoodFor. This means no real zero in β > 1−1/400 for real χ
  with q | N or d | N (TSI:84-97).

A second, alternative route, `thin_choice_of_zero_density` from Published ExplZeta/ExplChi/ZeroCount
(`.../ThinChoiceOfZeroDensityStatement.lean:23`), is not the one hostOfFieldOf uses.

**`thinH` proof** (`MSB/GaussSumFunctionEq.lean:55-108`):
1. gChi = G0 (definitional).
2. Every χ of E has conductor N | condN | QS·q·d (`level_dvd`).
3. Real χ: by `real_cond`, N | 8·odd(QS)·q·d. If q ∤ N and d ∤ N, then N ≤ 8B, and `small_zeros` (finitely many moduli)
   gives NoExc. Otherwise RealBox gives NoExc.
4. `thin` (`MSB/Thin.lean:10-13`) is then applied. Its parts are:
   - `psi_thin` (`MSB/PsiThin.lean:385-388`): |ψ0(u,χ)| ≤ C u(log u+λ)² exp(−c log u/(λ+√log u)), with λ ≥ log N.
     It comes from `pt_zero_free` (PsiThin:353-356: zeros satisfy β ≤ 1 − c/(λ + log(|γ|+3))), built on `zFRDirichlet`,
     a project theorem assembled from proved lemmas, plus `explicitFormula_closed`.
   - `int_thin` (`MSB/IntThin.lean:169-173`): y·∫_y^∞ φ(u)/u² du ≤ y e^{−c′x^{ε/8}} for y ≥ e^{x^{ε/3}}/3 and
     λ ≤ A x^{ε/5} log²x.

**Check of exponents.** With v = log u ≥ x^{ε/3}:
- v/(λ+√v) ≥ min(v/(2λ), √v/2) ≥ min(x^{2ε/15}/(2A log²x), x^{ε/6}/2);
- both exceed x^{ε/8}, since 2/15 > 1/8 and 1/6 > 1/8;
- the (v+λ)² factor and the ∫dv are absorbed.

So the caller's 2/15 vs 1/8 check is right. There is **no truncation height T**: G(y) = −y∫_y^∞ ψ(u,χ)/u² du (the
y·L′/L(1) term is exactly the completed integral), so a pointwise ψ-bound for all u ≥ y suffices.

**Which characters.** Every character of G0 × A, including:
- the trivial one (G, PNT Riesz main term x log x − (1+γ)x);
- χ_{−d} = chC;
- (·/q) = psC;
- all characters of A, with conductor | 2^{e+2}·M·q·d.

The ones that reach MAIN are ψ = 0 (Gz) and chC: MAIN carries a·ell(chC) (NODE-CHBALANCE §2b).

**(e) ell.** `HostAddCharCompatible` (`PrimitiveCosets/CoreAtH.lean:18-20`) requires ell ψ = L′/L(1, χ) for the
primitive χ with χ(n) = primVal ψ n. So ell is pinned *exactly*, and ThinScales then bounds the true gChi. The true
values are bounded in three places:
- |L′/L(1,χ_{−d})| ≤ x^ε (`HostGood`, TSI:103);
- `LogDerivativeBound` (AN:150-153): chC ≤ x^ε, and the bounded twists ≤ C log X;
- PairGood.bounds: ≤ 4 log y for the twists (PG:21-24).

In SizeData₂, `logDerivativeAtOne = dlogL D 1` (DP2:132-133) is the same true value of L′/L(1, χ_{−d}), and IdentU ties
Dd.LpL to it (`TieGlobal.lean:56`).

## 4. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `OrbitsWithoutOperator` = `NoOperatorOrbitBound` | WJS:184-189; `Divisibility/OrbitPlaces.lean:455` | at signal and inertClass hP ≠ 0 places, p ≤ X″, ¬Exc: Sram vectors get ColGe(Σ g0S + low) | delivers the Hecke-free gain ≈ ASK at all non-kernel-served, non-dropped inert primes (mass ≈ x log x·U) | **core, unread** |
| 2 | `UAt` (reps∖VVs term) | WJS:206-215 | g0⁺ at bad and non-served orbits of GIdx places | same, at inertClass places | core (NODE-PAIRING/LOCALDIV) |
| 3 | `pc_ord'` | used at P4:868, 890 | h(hP) = hOf e p (Frobenius ↦ p mod 2^{e+2}/±1), ord divides | links the A-class to a residue class | glue/host compatibility, body not read |
| 4 | `orders_bucket_bound`, `ordersSumY_of`, `leOfOrderOfLe_holds` | `ChainSlopeWindows/AdmissibleSchurLemma.lean:620`; `PmModulusFacts.lean:252`; `FourNotDvdOddSqAddOne.lean:140` | Σ_{ord(hOf p) ≤ J} log p/p ≤ C J log²(2^eY)/2^e | density of small-order classes | standard (elementary counting) |
| 5 | `BadOK` / `ChBadp_at` | TSI:41-47; `WeightVectorSmallSharesSeven.lean:17` | bad tops at Cand primes have log-weighted count ≤ \|TT\|x^{−2+ε} | bad orbits | core-ish host property (supplier `topsChoiceH`, not read) |
| 6 | `QH.thinH` ← `thin`, `psi_thin`, `int_thin`, `zFRDirichlet`, `small_zeros`, `real_cond` | `MSB/GaussSumFunctionEq.lean:55`; `MSB/Thin.lean:10`; `MSB/PsiThin.lean:353,385`; `MSB/IntThin.lean:169`; `LandauZeroFreeBounds/NoZeroComplex.lean:32` | effective PNT for characters, no exceptional zero | ThinScales | standard (de la Vallée Poussin + Landau; bodies not read) |
| 7 | `BoxW`/`BoxH`/`PairGood.boxes` | TSI:84-97; PG:25-27 | no real zero > 1−1/400 for real twists by q, d | RealBox | core upstream (PAIRGOOD) |
| 8 | `HostAddCharCompatible` | `CoreAtH.lean:18` | ell = L′/L(1) exactly | pins ell | glue |

Ranked: (1) ≫ (5) > (3) > the rest.

## 5. Oddities

1. **"Served" means three different things.**
   - Kernel-served: VV ≠ ∅, with Hecke gain.
   - `clAt = served`: not dropped.
   - The Gaussian-split condition: c ∉ D_p.

   Signal primes are split, never dropped, and never kernel-served, yet they carry gain g0⁺. Readers of SUMMARY §10
   item (6) should note that the open question is not "are non-served primes charged". They are, at ≤ x^{−1+O(ε)}·U.
   It is "is the Hecke-free gain at signal / VV = ∅ primes actually delivered" (child 1).
2. h = 0 inertClass primes above X′(1+Crρ) are not in `drop` (clause A needs p < X′(1+Crρ)), but gainP = 0 for them and
   their ask is 0, since the partner is the top itself with w ≥ b′ > a/p. This is harmless.
3. IsCs primes up to X″ are dropped and charged. Their thin partners give ask ≈ a/p up to X″, and the bound uses
   Y = max(Y, X″). Fine.
4. The small-order bucket uses J = x^{ε/4} and a log² loss. This is crude but has ample room: x^{−1+11ε/12} vs x^{−1+4ε}.
5. ThinScales has no upper limit on y, and holds for all characters including the trivial one. That is legitimate
   because of the integral representation.
6. The pde/q0 splitting in K is inferred from congruences, not from a lemma I read.

Nothing false-looking.

## 6. Coverage

Read:
- `RhoDetPrimeEqMuTildeMulChiPow.lean:40-110`; IRZ:1-420; SS:1-140; PC:20-40;
- SKB:1-297; WSS:11-170, 280-330; PCL:1-160; `RandomSubsetCounterexample.lean:1-40`;
- `GT/LossRequirementsOfSmallShares.lean:1-90`; P4:615-760, 843-900; DP2:1-140; DH:1-120;
- `ZG:15-140`; `AN:60-170`; WJS:25-215; `OrbitPlaces.lean` (declaration list only); TSI:1-130;
- PG (all); `MSB/GaussSumFunctionEq.lean` (all); `CharacterBoxes/ThinChoice.lean:1-80`; `LogCondLeThree.lean:55-90`;
- `hostOfFieldOf.lean:155-215`; `MSB/Thin.lean:10-24`; `MSB/SmallZeros.lean:25-46`;
- `MSB/PsiThin.lean:353-391` (statements); `MSB/IntThin.lean:169-175` (statement); `NoZeroComplex.lean` (all);
- `CoreAtH.lean:10-30`; `WeightVectorSmallSharesSeven.lean:17-42`.

Not opened:
- bodies of `pc_ord'`, `orders_bucket_bound`, `ordersSumY_of`, `psi_thin`, `int_thin`, `explicitFormula_closed`;
- `OrbitsWithoutOperator`'s supplier; `topsChoiceH`; `size_core`; the `TwoGroup` usage.
