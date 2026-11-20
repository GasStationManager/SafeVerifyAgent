# NODE-PAIRGOOD: `UpperTheory.Top.PairGood` / `PairEx` and its proof `QH.pairEx`

Source root `.../scratchpad/art/lean/src`. Abbreviations: `CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`,
`MSB/` = `Development/AutomorphicArithmetic/MeanSquareBounds/`, `GL3/` = `Formalism/GL3MeanSquares/`,
`JCS/` = `GL3/GenusMeanAsymptotics/JacobiCharacterSums/`, `LZF/` = `Formalism/LandauZeroFreeBounds/`,
`TSI` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean`.
Nothing was compiled. A grep of the whole tree for `^axiom` and for `sorry` found nothing.

## 0. Summary (answer to the circularity question)

There is **no circularity**, and the square-root bound for the twists is **not** GRH for them.
- `PairEx` is proved as a closed theorem, `QH.pairEx : UpperTheory.Top.PairEx` (`MSB/pairEx.lean:112-113`), with no hypotheses.
  Its proof is an averaging argument over the family of quadratic characters, case (i) of the question. It combines:
  a mean-square (large-sieve-type) bound over primes q; Markov's inequality; a zero-density estimate in a box
  (`zero_density_box`); Gallagher-type PNT in progressions; and Siegel's theorem. All of these are proved in the tree.
- The bound |gχ(y)| ≤ y^{1/2+ε/2} is claimed only for **y ∈ [Y, Y^A]** with A fixed. The characters have conductor
  about **exp(Y^{ε/5})** (q) and **exp(Y^{ε/5} log²Y)** (d). So y ≤ (log q)^{5A/ε}: the range lies far below the conductor.
  The pair (q, d) is chosen anew for every Y. This is a statement about short sums of one character from a varying family.
  It is not a statement as y → ∞ for a fixed character, so it is not GRH. Under GRH it would hold for every q, because
  log q ≤ y^{ε/5}. Unconditionally the tree proves it only for all but a proportion η of the q (and of the d).
- Nothing in the dependency cone of `pairEx` mentions `ZeroFreeAll`, `ZeroFreeOn`, `TopG` or `everyCharacter`. A grep of
  `MSB/`, `GL3/` and `LZF/` for these names finds nothing. Since `pairEx` has no hypotheses and Lean imports are acyclic,
  no statement-level circularity is possible here.

## 1. Statement

### `PairGood M ε Y X q d` (`CB/PairGood.lean:18-26`)
```lean
structure PairGood (M : ℕ) (eps Y X : ℝ) (q d : ℕ) : Prop where
  pair : WinPair eps Y q d
  coprime : Nat.Coprime M (q * d)
  bounds : ∀ (ξ : DirichletCharacter ℂ M) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw (fun a => ξ (a : ZMod M)) q d i j) (2 * M * q * d) →
      ∀ y : ℝ, Y ≤ y → y ≤ X → ‖An.gChi χ y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) ∧ ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log y
  boxes : ∀ ρ : PChar, ρ.IsReal → ρ.N ∣ 8 * M → ∀ i j : Fin 2, (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw ρ.val q d i j) (2 * M * q * d) →
      ZeroBox (height M eps Y j) χ
```
`tw ξ q d i j (a) = ξ(a)·(a/q)^i·(a/d)^j` (`:9-10`). `ZeroBox Q χ`: L(s,χ) ≠ 0 for Re s > 1 − 1/400 and |Im s| ≤ Q (`:12-13`).
`height M ε Y j = 8M·exp(Y^{ε/5})·exp(Y^{ε/5} log²Y)^j` (`:15-16`).

In words: (q, d) is a WinPair. For every character ξ mod M and every (i, j) ≠ (0, 0), the primitive χ that induces
ξ·(·/q)^i·(·/d)^j satisfies, **for every y in [Y, X]**:
- |gχ(y)| ≤ y^{1/2+ε/2}, where gχ(y) = Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L′/L(1,χ);
- |L′/L(1,χ)| ≤ 4 log y.

In addition, every twist of a real character ρ with ρ.N | 8M has no zero in Re s > 1 − 1/400, |Im s| ≤ height. That
height is at least the conductor.

### `WinPair ε Y q d` (`CB/ExistsPageN.lean:27-37`)
q is prime with q ≡ 3 (mod 8) and Y^{ε/5}/2 < log q ≤ Y^{ε/5}. d is prime with d ≡ 7 (mod 16) and
Y^{ε/5}log²Y/2 < log d ≤ Y^{ε/5}log²Y. Also q | d+1, and every odd prime p ≤ Y^{ε/5} divides d+1.

### `PairEx` (`CB/PairGood.lean:28-30`)
For every M > 0, every 0 < ε < 1/52 and every A ≥ 1, there is Y₁ such that for all Y ≥ Y₁ some (q, d) has
`PairGood M ε Y (Y^A) q d`.

### Neighbours
- **`RealBox H`** (`CB/PairGood.lean:32-34`): the host's real characters ψ with q | N_ψ or d | N_ψ have no real zero β > 1 − 1/400.
- **`HostGood s C8 C5 c6 Cb H q0`** (`TSI:102-112`) is a conjunction. Its clauses: HostVal, HostArith, a lower bound on #T2;
  `QDq` (BoundsAtX for (·/q), (·/d) and (·/qd) at the point x, `Formalism/SharpRestriction/InertJacobiLevels/AsmIface.lean:166-168`);
  **`BoxW`**; |dlogH| ≤ x^ε; **`ThinOK`**; BadOK; the disjoint BB sets; the norm forms of the level primes; pde, pde′ ≡ 1;
  q0 prime with q0 ≡ 1 and q0 ≤ (QS·q·d)^{C8}; and the list of level primes.
- **`BoxW s H`** (`TSI:73-74`): there is a Y with
  - `PairWin s Y`, i.e. x^{1/J} ≤ Y ≤ x (`PairRowIffQdRows.lean:66`);
  - `PairRow`;
  - `Boxq` (zero-free boxes of height 8·exp(Y^{ε/5}) for (·/q) and χ₈(·/q), `AsmIface.lean:170-172`);
  - `BoxH` (`TSI:68-71`): every real host character χ with d | N is `GoodFor(8·QS_odd·X1·X2)`, and every one with q | N but
    d ∤ N is `GoodFor(8·QS_odd·X1)`. `GoodFor Q` means primitive, real, N ≤ Q, and `ZeroFreeBox Q`
    (`GL3/SecondEstimateOfIntervalHypothesis.lean:44-48`).

  BoxW therefore asks for zero-freeness only in the box Re s > 1 − 1/400, |Im s| ≤ Q, where Q is about the conductor.
  It does not ask for zero-freeness to the right of 1/2.
- **`ThinOK s c H`** (`TSI:61-63`): for all y ≥ exp(x^{ε/3})/3, |gχ(y)| ≤ y·exp(−c x^{ε/8}). This is a de la Vallée Poussin
  quality bound for y far above the conductor (log y = x^{ε/3} against log cond ≈ x^{ε/5}log²x). It is fed by `ThinH`
  (`CB/PairGood.lean:36-39`) together with RealBox. That route is the sibling node NODE-HOSTS, and I did not open it.
- **`HostExW la P`** (`TSI:116-120`): for every ε in (0, 1/52) there are constants and an la-scale family S such that every
  scale s ∈ S with s.eps = ε and s.x ≥ x0 has R, H and q0 with RankVal, CT2, HostGood and P.

### How `bounds` reaches EAtH.bdG
`boundedTw` (`CB/BoundedTw.lean:45-56`) applies `PairGood ψ.N ε Y x H.q H.d` **at the single point y = x** (with Y ≤ x). It
gives BoundedCharsPointwise and |L′/L(1,χ)| ≤ 4 log x for every Bounded host character θ. The Bounded characters are exactly
the twists ξ(·/q)^i(·/d)^j with (i, j) ≠ 0 (`boundedTw_key`, `:5-43`). `winPairs` (`CB/WinPairs.lean:5-8`) applies
`PairEx` with A = J at Y = X^{1/J}. That gives PairGood on [X^{1/J}, X] ⊇ [Z, Z^{3/2}], and VWinAt (the Sha bound) is
then applied to the **same** (q, d), since VWinAt is quantified over every WinPair.

## 2. Argument (how `pairEx` is proved)

1. **Choice of q, d by density** (`pair_exists`, `MSB/PairExists.lean:9-50`, from `pair_share`, `MSB/PairShare.lean:26-50`).
   The set of q is P₁ = {q prime, q ≡ 3 (mod 8), e^{z/2} < q ≤ e^z}, with z = Y^{ε/5} (`PPset`, `GL3/SecondEstimate…:50-51`).
   - `stage1` (`MSB/Stage1Succ.lean:36-39`): the q in P₁ that are not GoodQ form at most a proportion η of P₁.
     GoodQ means that for every ξ mod 8M, the primitive χ inducing ξ·(·/q) satisfies `Box` (`MSB/PrimeSetTwoBounds.lean:32-36, 48-49`):
     χ ≠ 1, cond ≤ Q, ZeroFreeBox Q, |L′/L(1,χ)| ≤ C log Y, and |Gchi χ y| ≤ y^{1/2+τ} on [Y, Y^K].
   - `stage2` (`MSB/CharOf.lean:61`) does the same for each good q over P₂(q) = {d prime, d ≡ 7 (mod 16), oddM(z,q) | d+1,
     log d ≍ z'} (`MSB/PrimeSetTwoBounds.lean:44-46`), and gives GoodD.
   - Since η < 1, a good q and then a good d exist (`PairExists.lean:33-44`). `Rows` becomes `WinPair` in `pairEx.lean:139-142`.
2. **One modulus family: the engine `stage`** (`MSB/StagePow.lean:41-46`). Fix admitted (m₀, a₀, U) (`PrimeSetTwoBounds.lean:18-24`):
   8 | m₀, Y^{ε/6} ≤ log U ≤ Y^{ε/5}log²Y, and log U ≥ ¼·log²Y·log m₀. Fix also a list Ξ of at most R characters of conductor
   ≤ F ≤ U^{1/2}. Then for all but a proportion η of the primes q ≡ a₀ (mod m₀) in (U^{1/2}, U], every ξ ∈ Ξ gives
   BoxAll for ξ·(·/q). The proof has four parts:
   - (a) **Zero-free box**: `count_bad` (`MSB/CountBad.lean:9-18`) rests on `zero_density_box` (`JCS/CountZAll.lean:13-16`,
     statement `GL3/ZeroDensityBox.lean:8-12`). At most C·Q^{1/4} primitive characters of conductor ≤ Q have a zero with
     Re s > 1 − 1/400 and |Im s| ≤ Q. Distinct q give distinct characters (`count_bad_core`, injectivity at `MSB/CountBadCore.lean:39-55`).
     So at most C(FU)^{1/4} ≤ CU^{3/8} of the ≈ U^{1−o(1)} primes q are bad.
   - (b) **Splitting** (`box_of_S`, `MSB/BoxOfS.lean:34-62`). With Z = (Y^K)^{400}, we have Gchi(y) = −S(Z, y) − y·tail(Z).
     Here S(Z, y) = Σ_{n≤Z} Λ(n)·min(1, y/n)·κ(n)·(n/q), and tail(Z) = −L′/L(1) − Σ_{n≤Z} Λχ(n)/n. This is the exact identity
     `finite_splitting_of_group`. Inside the zero-free box, `tailK` (`MSB/TailKExp.lean:92-95`) gives |Y^K·tail| ≤ Y^ε, and
     `kappaC`/`kappa4` give |L′/L(1,χ)| ≤ C log Y, resp. ≤ 1000·log log Q + C ≤ 4 log Y (`MSB/Kappa4Loglog.lean:44-45, 126-128`).
   - (c) **Mean square over q** (`meanSqK`, `MSB/meanSqK.lean:51-54`). Σ_{q∈P} |S(Z, y, q, κ)|² ≤ C·y log y·|P| for every
     y ∈ [Y, Y^K] and every |κ| ≤ 1. The diagonal is Σ Λ(n)² min(1, y/n)² ≍ y log y. The off-diagonal terms need
     `twistK` (`MSB/twistK.lean:148-151`): |Σ_{q∈P} (q/s)| ≤ Y^{−B}|P| for every odd squarefree s ≤ Y^A coprime to m₀, except
     **one** exceptional s = n*. `twistK` follows from `PNTAPRelW` (`JCS/MeanSquareHypWIff.lean:38-45`, proved in `JCS/PNTFinal.lean:22-24`).
     PNTAPRelW is Gallagher's theorem: π(X; M, b) = main·(1 + O(e^{−c log X/log M} + e^{−√(c log X)})) for log X ≥ C₀ log M·log log M,
     with the main term corrected for an exceptional real zero. `twistK` also uses `zFRDirichlet` (de la Vallée Poussin–Landau–Page,
     `LZF/Statement.lean:15-20`) and `excBound` (Siegel, `LZF/LogDerivRegionChiOf.lean:50-52`, proved from `siegelLower`,
     `LZF/SiegelWalfiszAPOfSiegelLower.lean:26-32`). The condition log U ≥ ¼·log²Y·log m₀ puts X = U far enough beyond the
     modulus M = m₀·s that e^{−c log X/log M} ≤ Y^{−B}. That is the reason for the shape of `admitted`.
   - (d) **From mean square to "all y in the window"** (`bad_share`, `MSB/BadShare.lean:251-254`). This combines Markov's
     inequality with a Sobolev-type block bound in y (`bs_block`, `bs_normSq_S_le`, using ∂S/∂y). The proportion of q with
     |S(y)| > y^{1/2+τ}/2 for **some** y ∈ [Y, Y^K] is ≲ (C/τ)·Y^{−τ} → 0.
3. **Assembly** (`pairEx`, `MSB/pairEx.lean:112-169`). Take τ = ε/2, K = A and N₀ = 8M. `pairEx_box` (`:16-63`) reduces the twist by
   (i, j) to GoodQ or GoodD. For j = 0 it drops d with `ind_drop`. `pairEx_g` (`:65-82`) identifies An.gChi with QH.Gchi for χ ≠ 1.
   `log_exp_product_bounds` (`:84-110`) checks that log height lies between Y^{ε/6} and 3Y^{ε/5}log²Y, which `kappa4` needs.

**Compatibility of window and box.** y ≤ Y^K ≤ Z = Y^{400K}, Z is far smaller than the conductor, and Z is far smaller
than Q ≈ exp(Y^{ε/5}). The box (Re s > 1 − 1/400, |Im s| ≤ Q) is used only for the tail Σ_{n>Z} Λχ(n)/n ≪ Z^{−1/400+δ}·(log Q)^{O(1)}
≈ Y^{−K+O(ε)}. It is not used to bound S. The y^{1/2} quality of S comes from the mean square (random-sign heuristic,
made rigorous by orthogonality over q). *I infer* that the scales fit: the zero-density count (Q^{1/4}) is negligible
against #P ≈ U^{1−o(1)}. The constant 1/52 makes 1000·log log Q ≈ 200ε·log Y < 4 log Y. That explains the ubiquitous
ε < 1/52, which NODE-ROOT left untraced.

## 3. Children

| # | Name | file:line | Statement (math) | Role | Weight |
|---|---|---|---|---|---|
| 1 | `zero_density_box` | `JCS/CountZAll.lean:13`; def `GL3/ZeroDensityBox.lean:8` | #{primitive χ, cond ≤ Q, zero in Re s > 1−1/400, \|Im s\| ≤ Q} ≤ C Q^{1/4} | makes most twists zero-free in the box | standard (zero-density estimate; true with much room, e.g. Montgomery/Huxley give Q^{O(1/400)}); proof via mollifier + duality + Pólya–Vinogradov (`zero_detection`, `duality_inequality`, `pair_sum_bound`), not read |
| 2 | `pnt_progressions_relative_weak_holds` (`PNTAPRelW`) | `JCS/PNTFinal.lean:22`; def `JCS/MeanSquareHypWIff.lean:38` | Gallagher's PNT in progressions with relative error, exceptional zero included in the main term | off-diagonal of the mean square (`twistK`) | standard (Gallagher 1970); proof chain (`deuring_heilbronn_lossy`, `zero_sum_bound_lossy`, …) not read |
| 3 | `excBound` / `siegelLower` | `LZF/SiegelWalfiszAPOfSiegelLower.lean:32`; `LZF/FinalSiegel.lean:17` | Siegel: real zero β ≤ 1 − c(ε)q^{−ε} | at most one exceptional s in `twistK` | standard (Siegel, ineffective) |
| 4 | `zFRDirichlet` | `LZF/NoZeroComplex.lean:32`; def `LZF/Statement.lean:15` | classical zero-free region with at most one (real, simple) exceptional zero | `twistK` | standard (dlVP–Landau–Page) |
| 5 | `meanSqK` + `twistK` | `MSB/meanSqK.lean:51`; `MSB/twistK.lean:148` | Σ_q \|Σ_{n≤Z} Λ(n)min(1,y/n)κ(n)(n/q)\|² ≤ C y log y·#P, uniformly for admitted (m₀, a₀, U) | source of the y^{1/2} | core (an averaged, large-sieve-type statement; true by the above. I did not check the handling of the exceptional s = n*, `RRLe`/`SPsqLe`) |
| 6 | `bad_share` | `MSB/BadShare.lean:251` | Markov + block/derivative argument: few q have \|S(y)\| > y^{1/2+τ}/2 for some y ∈ [Y, X] | pointwise-in-y from mean square | glue (routine but delicate; skimmed) |
| 7 | `tailK`, `kappaC`, `kappa4` (← `tail_contour`, `tail_mertens`) | `MSB/TailKExp.lean:92`; `MSB/kappaC.lean:9`; `MSB/Kappa4Loglog.lean:44,126` | under ZeroFreeBox Q with log Q ≍ Y^{ε/5}: \|Y^K tail(Y^{400K})\| ≤ Y^ε, \|L′/L(1)\| ≤ 1000 log log Q + C | turns the truncated sum into gχ; the 4 log y bound | standard (contour shift in a zero-free rectangle); bodies not read |
| 8 | `finite_splitting_of_group` | `GL3/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean:52` | Gchi(y) = −Sz(y, Z) − y·tail(Z) for y ≤ Z | exact identity | glue |
| 9 | `pair_share`, `stage`, `stage1`, `stage2`, `count_bad(_core)`, `pairEx_box`, `ind_drop` | `MSB/PairShare.lean:26`; `StagePow.lean:41`; `Stage1Succ.lean:36`; `CharOf.lean:61`; `CountBad.lean:9`; `pairEx.lean:16` | the bookkeeping in §2 | assembly | glue (stage1 and the count_bad files read; `stage` body and `stage2` body skimmed or not read) |

## 4. Oddities

1. **The premise "bound for all large y = GRH" does not apply.** `PairGood.bounds` holds only on [Y, X] with X = Y^A, and on the
   live path it is used only at one point y = x ≤ Y^J (`BoundedTw.lean:52`). The characters depend on Y, and their conductors are
   ≈ exp(Y^{ε/5}) and ≈ exp(Y^{ε/5}log²Y). This is a "typical member of a family, short range" statement. It can be proved by
   averaging, and the tree does so.
2. **No circularity found.** `pairEx` is hypothesis-free (`MSB/pairEx.lean:112-113`), and the tree has no `axiom` or `sorry`.
   Its analytic inputs are the classical zero-free region, Siegel's theorem, Gallagher's PNT in progressions and a box
   zero-density estimate. None of them refers to the GRH-level predicates.
3. **Consistency with VWinAt.** `winPairs` takes the (q, d) supplied by `PairEx` and then invokes VWinAt for that same pair. This is
   legitimate because VWinAt is quantified over **every** WinPair (`CB/ExistsPageN.lean:44-49`). The "most q are good" choice and
   the Sha bound therefore do not conflict.
4. **Ineffectivity.** Siegel (`excBound`) enters through `twistK`, so Y₀ in PairEx is ineffective. That is harmless for an
   existence proof.
5. **Constants.** The constants 400, 1/52 and Q^{1/4} are loose but consistent. 1/52 is forced by 1000·log log Q ≤ 4 log Y with
   log Q ≤ 3Y^{ε/5}log²Y (`Kappa4Loglog.lean`, `pairEx.lean:84-110`). The "4" in |L′/L(1,χ)| ≤ 4 log y is also the source of the
   reviewer's HostGood "4 log x".
6. Two definitions named `ZeroDensityBox` exist, in different namespaces (`GL3/ZeroDensityBox.lean:8`, `JCS/CountSt.lean:7`).
   They are textually identical, and `count_bad_core` uses the `Ext.PrimitiveCharacterCasts` one. They are named alike but
   are not shared.
7. I did not verify that the bodies of `zero_density_box`, `PNTAPRelW`, `meanSqK` and `twistK` prove exactly these statements. As
   stated, each is a true theorem of the literature (rows 1–5) with generous constants. If one of them were false as literally
   stated, the whole node would collapse. They are the places for an expert spot check, `twistK`'s exceptional-s handling and
   `zero_density_box` first.

## 5. Coverage

Read: `CB/PairGood.lean` (all); `CB/ExistsPageN.lean:1-60`; `CB/WinPairs.lean:1-60`; `CB/BoundedTw.lean:1-56`;
`MSB/pairEx.lean` (all); `MSB/PairExists.lean` (all); `MSB/PairShare.lean` (all); `MSB/PrimeSetTwoBounds.lean` (all);
`MSB/BoxOfS.lean` (all); `MSB/CountBad.lean`, `MSB/CountBadCore.lean` (all); `MSB/Stage1Succ.lean:36-97`; `MSB/StagePow.lean:41-60`;
statement lines of `meanSqK`, `twistK` (`:148-160`), `bad_share`, `kappa4`, `kappa4_loglog`, `kappaC`, `tailK`;
`GL3/SecondEstimateOfIntervalHypothesis.lean:1-60`; `GL3/ZeroDensityBox.lean`; `JCS/CountSt.lean:1-12`; `JCS/CountZAll.lean`;
`JCS/MeanSquareHypWIff.lean:30-45`; `JCS/PNTFinal.lean:15-24`; `LZF/LogDerivRegionChiOf.lean:45-55`; `LZF/Statement.lean:10-20`;
`LZF/SiegelWalfiszAPOfSiegelLower.lean:1-32`; `TSI:55-127`; `AsmIface.lean:166-172`; NODE-HOSTS.md (for HostGood context).
Not opened: the bodies of `stage`, `stage2`, `meanSqK`, `twistK`, `bad_share` (skimmed names only), `tailK`, `kappaC`,
`zero_density_box`'s components, the PNTAPRelW chain, `siegelLower`, `thinH`, `PairRow`, and `hostOfFieldOf`.
