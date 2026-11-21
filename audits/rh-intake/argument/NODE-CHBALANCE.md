# NODE-CHBALANCE: the bridge from the prime count ASK to Gm(ψ) (`ch_balance`, `ch_core` steps 1–5)

Abbreviations (paths relative to `src/`): `LT/` = `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`,
`SI` = `Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean`, `PC/` = `Development/AutomorphicArithmetic/PrimitiveCosets/`,
`FPN` = `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean`, `PFA` = `Formalism/ThickAverageLoss/PartnersToFactorsAt.lean`,
`GB` = `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean`, `STI` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean`,
`TGC/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`.

## 0. Summary

The bridge is a correct exact computation. `ch_balance` is the finite-group orthogonality identity
ASK − MAIN = De, which holds for any weights w and any constants ell(ψ). `ch_core` then keeps only the "thick"
Frobenius classes, replaces their caps by b, and averages over u0 ∈ A0 = ⟨a0⟩. That leaves exactly the characters of
E0 × A/A0, which are 4o characters: (·/d)^α (·/q)^β ψ^j. After summing over the tops t ∈ TT, the trivial character has
coefficient 1 and each ψ^j (j ≠ 0) has coefficient c = (3o+1)^{-1}. **The target character enters through a 4 : 3
over-weighting of thick primes with ψ(p) = 1**: TT puts mass 4/(3o+1) on the trivial coset of A0 and 3/(3o+1) on each
other coset. The 3o non-kept characters, the quadratic twists, are bounded two-sidedly by `bdG`. The coefficient of Gm
is exactly U = |TT|·m·b·δ/2, which is positive. The directions are right for Landau. Every replacement error is at most
about x^{1/4+ε}·U, far below x^{1/2}·U. The analytic content the bridge imports is `ThinScales`, an effective PNT for
every character of Gal(E/ℚ) at y ≥ X′/3 with saving θ = e^{−c x^{ε/8}}. It also pins ell(ψ) ≈ L′/L(1, χ_ψ).

## 1. Statement

### `ch_balance` (`LT/ChBalance.lean:200-202`)
```lean
theorem ch_balance (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S)
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 < a) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) : (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w
```
Unfolded:
- G = E0 × H with E0 = (ℤ/2)², H = A (`PFA:13`). Φ = {g : g.1.1 = 0}, so |Φ| = 2|H| (`PFA:21,31`; `phiSet_card`).
  The first E0 coordinate is the (−d/·) sign: inertia at d is {0, sgc0}, sgc0 = ((1,0),0) (`SI:22`, `FPN:17`). So Φ is
  Gal(E/K), K = ℚ(√−d), and ¬Φ means inert in K. The second coordinate is (·/q): it is `psC`, and `TGC/Analytic.lean:86`
  has psC = chQ. cconj = ((1,1),0), topPl t = ((0,0),t), thickPl t = ((0,1),t) (`PFA:23-26`).
- partner(t,g) = cconj + g + topPl t (`FPN:21`). This is a bijection G∖Φ → Φ (`STI:47`).
- primVal ψ n = ∏_{p|n} mean of ψ over v_p(n)·Frob_p + I_p (`FPN:57-62`). This is the Artin value. `prim_read`
  (`PC/PrimRead.lean:48`) shows it equals the primitive Dirichlet character of ψ at every n ≠ 0.
- **GPsi ψ y** = Σ_{n≤y} Λ(n) primVal ψ(n)(y/n − 1) + y·ell(ψ) for ψ ≠ 0, and Gz(y) for ψ = 0 (`FPN:64-66`).
- **ASK** = Σ_{p inert, p ≠ 2,q,d} 2 log p · Σ_{i ≤ N, i·Frob_p ∉ Φ} (a/p^i − w(partner(t, i·Frob_p)))₊
  + log d · Σ_i Σ_{g ∈ i·Frob_d + I_d, g ∉ Φ} (a/d^i − w(partner(t,g)))₊ (`FPN:71-87`).
- **MAIN** = a(log a − 1 − γ + ell(chC) − |Φ|^{-1} Σ_{ρ∈Φ} log w(ρ)) (`FPN:89-91`).
- **De** = |Φ|^{-1} Σ_{g∉Φ} Σ_{ψ∈Ĝ} ψ̄(g)·w(partner(t,g))·GPsi_ψ(a/w(partner(t,g))) (`FPN:93-96`).

### `ch_core` averaging (`LT/ChCore.lean:16-338`; main theorem `:343-442`; statement quoted in NODE-COREGM)
- Th(u0,t) = |Φ|^{-1} Σ_{s∈T2} Σ_ψ ψ(−e1(s+u0−t))·b·GPsi_ψ(y), with e1(h) = ((1,0),h) (`ChCore:18-22`).
- `sum_Th` (`:56-73`): for T2 ⊆ A0, Σ_{u0∈A0} Th(u0,t) = |A0|·b·(δ/2)·Σ_{ψ∈PsiA A0} ψ(e1 t)·GPsi_ψ(y), with δ = |T2|/|H|
  (`GB:41`) and PsiA A0 = {ψ : ψ(0,s) = 1 ∀ s ∈ A0} (`SI:28`).
- `th_le` (`:75-152`): Re Th(u0,t) at y = a_t/b ≤ Re De(a_t, t, w_{u0,j}) + 2|Φ|(3(x+1)(η+1) + (x+1)bθ).
- `one_char` (`:202-281`): Σ_t Re ψ(e1 t) G_ψ(y_t) ≥ |TT|(vv_ψ − R), where vv_ψ = wtA(ψ)·Re G_ψ(x) for ψ ∈ Kp and
  −|G_ψ(x)| otherwise (`:180-184`).
- `core` (`:283-338`): |TT|·m·b·(δ/2)·Y ≤ Err + 2|TT|mb/x.
- Final step: Y = GmA − SigA − 4x^{1/2+ε}, and `proposition_size_bound` gives the exponent.

## 2. Argument (paper derivation)

### (a) What is counted, and the character expansion

**Lean says.** For an unramified p and i ≥ 1, the summand of ASK is nonzero only if i·Frob_p ∉ Φ, that is, p is inert
in K and i is odd. It is then 2 log p·(a/p^i − w_ρ)₊, at the place ρ = partner(t, i·Frob_p). Split p, even powers, and
p ∈ S = {2, q, primes of QS} contribute 0. Those p have Frob and inertia in Φ (`SI:14-22`), and
(−d/2) = (−d/q) = 1 by HostHyp. The prime d contributes log d per power. So, *as a function of n*,
ASK = Σ_n Λ(n)(1 − χ_{−d}(n))(a/n − w(partner(t, Frob_n)))₊. The Frobenius class beyond inertness enters **only through the cap
w at the partner place**.

The caps (`SizesA`, `SI:42-48`; `IsThickAt`, `PFA:97`):
- ρ thick, i.e. ρ = thickPl(s+u0) with s ∈ T2: b ≤ w ≤ b+η+1. The Riesz length is y = a/w ≈ x.
- Every other ρ ∈ Φ (top or thin): w ≤ 2b′. The length is a/w ≥ X′/2, which is enormous (X′ = e^{x^{ε/3}}).

partner(t,g) = thickPl(s+u0) exactly when **g = e1(s+u0−t) = ((1,0), s+u0−t)**. So the primes counted at the
x-scale have:
- (−d/p) = −1;
- psC-coordinate 0, i.e. (p/q) on the chQ sign = +1;
- A-coordinate h ∈ T2 + u0 − t ⊂ A0 − t.

Equivalently Frob_p = c·thickPl(h): Frob·c = ((0,1),h) has even order. This is consistent with "served" in
NUMTEST3 / HidaSetting.

Fix j and sum the thick weight over u0 ∈ A0 and t ∈ TT. A class ((1,0),h) receives
|T2|·#{t ∈ TT : t ≡ −h mod A0}, which is ≈ |T2||TT|·λ(−h). Here `Frame.lam` (`TGC/ExplicitFormulaErrorOfHostConditions.lean:132`)
is λ = 4/(3o+1) on A0 and 3/(3o+1) off A0, and `Shares` holds to relative x^{−1+ε} (EAtH.shares). Since
1_{A0}(h) = o^{-1} Σ_{j} ψ^j(h) on A/A0 (A/A0 has order o and its dual is ⟨ψ⟩ by `TwistForm`, see `BoundedTw.lean:5-30`):

  λ(h) = (3 + 1_{A0}(h))/(3o+1) = o^{-1}·[1 + (3o+1)^{-1} Σ_{j≠0} ψ^j(h)].

The E0-condition is [g.1 = (1,0)] = ¼(1 − chC + psC − chC·psC)(g). So the thick-class indicator is a combination
of the 4o characters (·/d)^α(·/q)^β ψ^j of E0 × A/A0, with these coefficients:
- 1 on the trivial character and c = (3o+1)^{-1} on ψ^j, both times a common ¼o^{-1};
- ∓1 and ∓c on the twists by chC, psC, chC·psC.

`ch_core` reaches exactly this through `sum_A`/`sum_Th`. The averaging over u0 ∈ A0 kills every character that is
nontrivial on A0. The sum over t then gives Σ_t ψ(0,t) ≈ c|TT| for kept ψ nontrivial on A (`tops_sum`, `PC/TopsSum.lean:75`:
|Σ_t ψ(0,t) − (3o+1)^{-1}|TT|| ≤ o·δ_sh·|TT|). The source of 3o+1: it is the normalising constant of the positive
measure 4 : 3 : 3 : … on A/A0. Any c ∈ (0,1] would do for Landau. 3o+1 is just a choice that keeps the shares positive.

**Remark.** `GB:43` defines `ThickPartTranslateMean`, an average over *all* u0 ∈ H. It would leave only the four
E0-characters (output "Gsig"), and ψ would disappear. It is defined and never used (single hit in the tree). The live
path averages over A0 only, and that is precisely what lets ψ survive.

### (b) The identity and the coefficient of Gm

**`ch_balance` on paper.**
1. Orthogonality on G: |Φ|^{-1} Σ_ψ ψ̄(g)·primVal ψ(p^i) = 2·[i·Frob_p = g] for unramified p (`ounram`, `ChBalance:41-51`).
   For the coset form at ramified p see `orthogonality_ramified` (`STI:311`). The ramified-at-d case gives weight 1
   (`ld`, `cardI`). So |Φ|^{-1} Σ_{g∉Φ} Σ_ψ ψ̄(g) Σ_n Λ(n) primVal ψ(n)(a/n − w_{partner g})₊ = ASK (`askExp`, `:136-198`).
2. For each g and ψ: Σ_n Λ χ_ψ(n)(a/n − w)₊ = w·G_ψ(a/w) − a·ell(ψ) for ψ ≠ 0, and
   = w·Gz(a/w) + a log a − a log w − (1+γ)a for ψ = 0 (`sum_cut` `STI:619`, `inner_eq` `STI:654`).
3. The main terms then sum as follows. Σ_{g∉Φ} ψ̄(g) equals |Φ| for ψ = 0, −|Φ| for ψ = chC, and 0 otherwise
   (`colour_sum`, `STI:171`). So the ell-terms leave only +a·ell(chC). Σ_{g∉Φ} log w(partner g) = Σ_{ρ∈Φ} log w(ρ)
   (`sum_partner`). The result is MAIN.

The identity is exact and correct. It holds **for every function ell and every w**. On the count side, −L′/L(1,χ)
enters only as ell(chC) = L′/L(1, χ_{−d}) in MAIN. That is the y·L′/L(1,χ_d) term of the explicit formula for
Σ Λ(1−χ_d)(y/n−1), and IdentU sets Dd.LpL = Re ell(chC), the Chowla–Selberg match. For the other characters,
ell(ψ) cancels out of De exactly and reappears only when De is split into thick and thin classes.

**`ch_core` on paper.** Write G_ψ for GPsi. Then De = Thick + Thin:
- Thick = |Φ|^{-1} Σ_{g thick} Σ_ψ ψ̄(g)·w_g·G_ψ(a/w_g).
- Thin = the same sum over the other g ∉ Φ.

The following hold:
- Thick − Th = O(|G|·3(x+1)(η+1)), by `LipW`: |w G(A/w) − b G(A/b)| ≤ 3A/b·|w−b|, i.e.
  d/dw[wG(A/w)] = −ψ_χ(A/w) (+ A/w for ψ = 0). This is Chebyshev, standard.
- |Thin| ≤ |G|·(x+1)bθ by `ThinScales` (`GB:55`).
- CostWindows (`SChain.lean:50-51`) makes the sum of the two ≤ 2b/x.

Next average over u0 ∈ A0 and sum over t ∈ TT and j < m. With the gap hypothesis gapA(u0) ≤ Err:

  |TT|·m·b·(δ/2) · (1/|TT|) Σ_t Re Σ_{ψ∈PsiA A0} ψ(e1 t) G_ψ(a_t/b) ≤ Err + 2|TT|mb/x.

`one_char` turns the inner average into the following:
- ψ = 0 gives Gz(x).
- Kept ψ ≠ 0 have ψ(sgc0) = 1, so ψ(e1 t) = ψ(0,t). They give c·Re G_ψ(x).
- Non-kept ψ give ≥ −|G_ψ(x)|.
- The total error is ≤ R.

By `gmA_eq` (`PC/GmAEq.lean:61-149`, read) Σ_{Kp} wtA·Re G_ψ(x) = Λ.Gm(x) = Gz(x) + (3o+1)^{-1}Σ_{ξ∈⟨ψ⟩,ξ≠1} Re g_ξ(x).
This is a genuine bijection keptA ↔ KEPT: G_ψ = gChi via `prim_read`, and psC is not kept for Level.cyc
(`ExceptionalCharacterKept`). The trivial character's part is exactly Gz = Σ Λ(n)(x/n−1) − x log x + (1+γ)x,
the PNT Riesz main term. Hence:

  **ASK − MAIN (summed over t, j, averaged over u0) ≥ U·[Gm(x) − SigA(x) − 4x^{1/2+ε}] − 2|TT|mb/x,
  where U = |TT|·m·b·δ/2.**

The coefficient is exactly U: it is positive, and it is the signal unit of ACCOUNT. SigA = Σ_{ψ∈PsiA A0∖Kp} |G_ψ(x)|
runs over 3o characters. By `TwistForm`/`boundedTw_key` (`CharacterBoxes/BoundedTw.lean:5-34`) these are exactly the
twists ξ·(·/q)^i(·/d)^j with ξ ∈ ⟨ψ⟩ and (i,j) ≠ (0,0). Characters with (i,j) = (0,0) are either kept or in Xm, and
Xm is impossible for them. `card_PsiA` = 4o (used in `charsA`, `PC/charsA.lean:96`).

### (c) The scales

- All tops t have |a_t/b − x| ≤ 1 (SizesA; with a_t ∈ [a, a(1+x^{−17.5})] the deviation is actually ≪ x^{−16}). The
  move to the single point x costs |G_ψ(y_t) − G_ψ(x)| ≤ log(x+1) + Cd + |ell ψ| per t (`move`, `DerivInt` =
  `derivative_integral_all`, `LipschitzWeightAndMinimum.lean:966`). This is Mertens: G′(y) = Σ_{n≤y}Λχ/n + ell, and
  Gz′ = O(1). It is O(log x), not x^{1/2}.
- Equidistribution error: o·x^{−1+ε}·|G_ψ(x)| ≲ o·x^{ε}·log x.
- Cap replacement w → b at thick places: 2b/x per (t,j), i.e. relative 4/(xδ) ≤ 4x^{−1+ε} of U.
- Thin and top places (length ≥ X′/3): ≤ (x+1)bθ per class, with θ = e^{−cx^{ε/8}}.
- `ch_core` absorbs everything into a crude 4x^{1/2+ε} using x^{1/4} as a log envelope (`:381-417`). The actual errors
  are ≲ x^{ε}·log x. **No error in the bridge is comparable to x^{1/2}.** The x^{1/2} comes only from Err/U (NODE-COREGM §2).

### (d) One-sidedness

From `core` and `hY`: U·(GmA − SigA − 4x^{1/2+ε}) ≤ Err + 2|TT|mb/x. This is an **upper** bound on GmA = Gm(x). It
needs only:
- the *upper* bound gapA ≤ Err on ASK − MAIN;
- U > 0;
- a lower bound on the non-kept part, which comes from −|G_ψ|.

The bound on SigA is then taken *two-sidedly* from bdG (|gχ(x)| ≤ x^{1/2+ε}, `sigA_le`). LANDAU needs Gm ≤ x^θ on
windows. The weights there are 1 and (3o+1)^{-1}, both > 0. A real zero β of some L(s, ψ^j) contributes
+x^β/(β(1−β))·weight, which pushes Gm up. Complex zeros are caught by the nearest-pole argument. The signs match:
G_ψ = ΣΛχ(y/n−1) + yL′/L(1,χ) is the explicit-formula remainder Σ_ρ −y^ρ/(ρ(ρ−1)) + O(log), and it enters
ASK − MAIN with coefficient +U·(weight). Correct direction.

### (e) Judgement

The bridge is a correct exact computation as reconstructed. ψ genuinely enters. The counting weight on thick classes is
3 + 1[ψ(Frob) = 1], and the kept characters are exactly ⟨ψ⟩, by an injective identification with the true primitive
characters (`gmA_eq`, `prim_read`). The bridge proves nothing deep by itself. Given the windows, gapA ≤ x^{Cε}·Err is
equivalent to GmA − SigA ≲ x^{1/2+O(ε)}. The arithmetic inputs it imports are `ThinScales`, `bdG`, `Shares`
and `TwistForm`.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `ThinScales` (supplied by host `ThinOK` / `ChebyshevCharacterBound`) | `GB:55`; `TGC/Analytic.lean:146-148` | for every character ψ of Gal(E/ℚ), including the trivial one, and every y ≥ X′/3 (X′ = e^{x^{ε/3}}): \|G_ψ(y)\| ≤ y·e^{−c x^{ε/8}} | drops all non-thick classes; pins ell(ψ) to L′/L(1,χ_ψ) within θ | core. Effective PNT for ≈ 4\|A\| ≈ x^{2+8ε} characters of conductor up to e^{x^{ε/5}}. It needs no exceptional zero for the real characters involving q, d (GoodFor in HostGood). Check in HOSTS. |
| gap hypothesis (`ch_top` ← SizeData₂) | `LT/ChTop.lean:37` | ASK − MAIN ≤ Err per u0 | the whole RH-strength content | core (upstream) |
| `bdG` / `boundedTw` / `PairGood.bounds` | `TGC/Analytic.lean:154`; `CharacterBoxes/BoundedTw.lean:45` | \|gχ(x)\| ≤ x^{1/2+ε} for the 3o twists (i,j) ≠ 0 | bounds SigA two-sidedly | core (upstream; PAIRGOOD) |
| `TwistForm` | `CharacterBoxes/BoundedTw.lean:15` (use) | every character of Gal(E/ℚ) trivial on A0 is ξ·tw(q,d,i,j) with ξ ∈ ⟨ψ⟩ | the dual of A/A0 is ⟨ψ⟩, so the kept set is exactly ⟨ψ⟩ | glue (host property; definition not opened) |
| `Shares` / `lam` / `tops_sum` | `TGC/ExplicitFormulaErrorOfHostConditions.lean:132-138`; `PC/TopsSum.lean:75` | TT has mass 4/(3o+1) on each A0-coset representative class 0 and 3/(3o+1) on the others, to relative x^{−1+ε}; hence Σ_t ψ(t) = (3o+1)^{-1}\|TT\| + O(o x^{−1+ε}\|TT\|) | makes ψ enter with weight c | standard (finite Fourier). Existence of such TT is a host-construction question. |
| `ch_balance` helpers `askExp`, `ounram`, `lunram`, `lsplit`, `ld`, `orthogonality_ramified`, `colour_sum`, `sum_partner`, `sum_cut`, `inner_eq` | `LT/ChBalance.lean:19-198`; `STI:47,171,311,619,654` | orthogonality and Riesz bookkeeping | exact identity | glue (bodies read) |
| `sum_A`, `sum_Th`, `th_le`, `one_char`, `core` | `LT/ChCore.lean:28-338` | §2(b) | averaging and replacements | glue (read) |
| `lipschitz_weight_all`, `derivative_integral_all` | `LipschitzWeightAndMinimum.lean:957,966` | LipW, DerivInt (Chebyshev / Mertens) | replacements | standard (bodies not read) |
| `gmA_eq`, `prim_read`, `charsA` | `PC/GmAEq.lean:61`; `PC/PrimRead.lean:48`; `PC/charsA.lean:80` | GmA = Level.Gm; GPsi = gChi of the primitive character; CharsA from EAtH | identification of ψ | glue (gmA_eq and charsA read; prim_read statement read) |
| `proposition_size_bound` | `LipschitzWeightAndMinimum.lean:507` | exponent arithmetic | glue | glue (not read) |

Ranked for expansion: (1) ThinScales supplier, (2) the gap hypothesis (already the SLOPE/LOSS chain), (3) PairGood,
(4) the existence of TT with exact 4 : 3 shares.

## 4. Oddities

1. **The identity is ell- and w-free.** `ch_balance` is true for an arbitrary ell. Nothing in the bridge ties ell(ψ)
   for ψ ≠ chC to L′/L(1) except two things: HostAddCharCompatible (`PC/CoreAtH.lean:18`), and ThinScales, which forces
   it implicitly. This is harmless because both are present on the live path. But it means the "−L′/L(1,χ) on the
   count side" is a definition, not something derived from the count.
2. **ASK counts every inert class, not only served ones.** Non-thick inert classes (top or thin partners, caps ≤ 2b′)
   are counted at almost full Chebyshev weight. In the bridge their excess over MAIN is harmless (ThinScales). The slope
   side must nonetheless *gain* at all of them, or charge them as loss. That is the ACCOUNT (iv) / ADMB2
   "non-served classes charged their whole ask" bookkeeping, which needs the bad classes to have tiny density. The
   bridge is not where this is decided, but the reader should know the ASK being bounded is not a "served-only" count.
3. **ψ enters weakly but genuinely.** It enters with relative weight c = (3o+1)^{-1} per power, through a 4 : 3
   over-weighting. That suffices for Landau, which needs only positive weights. If TT's shares were uniform (3 : 3),
   c = 0 and the argument would prove nothing about ψ (only RH for ζ via Gz). So the exactness of `Shares` is load-bearing.
4. `ThickPartTranslateMean` (`GB:43`): a defined but unused Prop. Averaging over all of H would erase ψ. Dead code,
   not on the live path.
5. The R absorption in `ch_core` is crude (4x^{1/2+ε} for errors of size x^ε log x). It is harmless.
6. `ThinScales` is quantified over **all** characters of G, including chC, psC, and the trivial character, and over
   all y ≥ X′/3, with no upper limit. For the trivial character this is PNT with error e^{−cx^{ε/8}} at
   y ≥ e^{x^{ε/3}}/3. For real characters of conductor about e^{x^{ε/5}} it is Siegel-sensitive. The required region
   log y/log Q ≈ x^{2ε/15} > x^{ε/8} works out with a classical zero-free region *provided* no exceptional zero
   exists. That is what `GoodFor` in HostGood buys. I did not trace the supplier.

None of these is a defect in the bridge.

## 5. Coverage

Read: `LT/ChBalance.lean:1-264` (all); `LT/ChCore.lean:1-446` (all); `SI:1-90`; `FPN:1-110`; `PFA:1-100`;
`GB:36-70`; `STI:40-60,150-180,300-320,615-660`; `SChain.lean:48-60`; `PC/CoreGm.lean:16-74`;
`PC/CoreAtH.lean:1-30`; `PC/GmAEq.lean:10-149`; `PC/charsA.lean:80-130`; `PC/PrimRead.lean:48-60`;
`PC/TopsSum.lean:75-85`; `TGC/ExplicitFormulaErrorOfHostConditions.lean:100-152`; `TGC/Analytic.lean:60-160`;
`TGC/ZsmulGeneratorEqZeroOfProjection.lean:10-130` (declaration lines); `CharacterBoxes/BoundedTw.lean:1-56`;
`PC/SigALe.lean:1-40` (declaration lines).
Not opened: bodies of `lipschitz_weight_all`, `derivative_integral_all`, `proposition_size_bound`, `ortho_coset`,
`primitive_value_primitive`, `tops_sum_gen`, `sigA_le`; the `TwistForm` definition; the suppliers of ThinScales,
Shares and TT.
