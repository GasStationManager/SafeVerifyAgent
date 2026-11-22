# NODE-HOSTSEL: host selection and the twist bound (`PairGood.bounds` → `bdG`), step 2 of the main argument

Source root `.../scratchpad/art/lean/src`. Abbreviations: `CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`,
`MSB/` = `Development/AutomorphicArithmetic/MeanSquareBounds/`, `JCS/` = `Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/`,
`TSI` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean`,
`An/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean`,
`SN/` = `Development/AutomorphicArithmetic/ShortNorms/`. Nothing was compiled or run.

## 0. Verdict

**No ESCALATE.** The averaging proof is a correct, classical argument, and its sizes fit with a huge margin.
- The family is primes q (then primes d). log q ≍ Y^{ε/5} and log d ≍ Y^{ε/5}log²Y, so the family has size ≥ e^{0.9·Y^{ε/5}/2}.
  The sums have length y ≤ Y^J, truncated at Z = y-range^{400}, and every modulus in the family exceeds Z².
- The off-diagonal is therefore handled by **elementary orthogonality**: quadratic reciprocity turns (nn′/q) into (q/s), and
  PNT in progressions mod 8s or m₀s does the rest (Gallagher-type, with the exceptional zero in the main term). The proof
  does **not** use Heath-Brown's quadratic large sieve or any other Published input.
- The Siegel case is handled in two ways. (i) The one exceptional modulus s = n* is removed, and its pairs are bounded
  trivially. (ii) Any d (or q) whose twist has a zero in Re s > 1 − 1/400, |Im s| ≤ Q is removed by a zero-density count. This is
  also what bounds L′/L(1, χ_{−d}) ≤ 4 log x.
- Simultaneity is not proved by counting. **Every** structural host condition is constructed deterministically for **every**
  (q, d) that satisfies `PairGood`. Only the analytic clauses are averaged.
- Range: the bound is *proved* for all y ∈ [Y, X] = [X^{1/J}, X], for one (q, d) per window. It is *consumed* only at the
  single point y = x of each x in the window, plus |y − x| ≤ 1 by a Lipschitz step. Both earlier phrasings were partly right.

## 1. Statement

**`tw`, `PairGood`, `PairEx`** (`CB/PairGood.lean:9-30`, read). tw ξ q d i j (a) = ξ(a)(a/q)^i(a/d)^j (Jacobi symbols).
`PairGood M ε Y X q d` has four clauses:
- `pair`: `WinPair ε Y q d` (`CB/ExistsPageN.lean:27-37`, read). q is prime with q ≡ 3 mod 8 and Y^{ε/5}/2 < log q ≤ Y^{ε/5}.
  d is prime with d ≡ 7 mod 16 and Y^{ε/5}log²Y/2 < log d ≤ Y^{ε/5}log²Y. Also q | d+1, and every odd prime p ≤ Y^{ε/5} divides d+1.
- `coprime`: (M, qd) = 1.
- `bounds`: take **every** Dirichlet character ξ mod M (not only ξ ∈ ⟨ψ⟩) and every (i, j) ∈ {0,1}² \ {(0,0)}. Let χ be the
  primitive character inducing tw ξ q d i j. Then for **every y ∈ [Y, X]**: ‖g_χ(y)‖ ≤ y^{1/2+ε/2} and ‖L′/L(1, χ)‖ ≤ 4 log y.
- `boxes`: for every real ρ with ρ.N | 8M, each twist has no zero with Re s > 1 − 1/400 and |Im s| ≤ height = 8M·e^{Y^{ε/5}}·(e^{Y^{ε/5}log²Y})^j.

`PairEx`: ∀ M > 0, 0 < ε < 1/52, A ≥ 1, ∃ Y₁ ∀ Y ≥ Y₁ ∃ q, d with `PairGood M ε Y (Y^A) q d`.

**Weight.** g_χ(y) = Σ_{n≤y} Λ(n)χ(n)·max(y/n − 1, 0) + y·L′/L(1, χ) for χ ≠ 1 (`An/Analytic.lean:11-24`, read). This is the
Riesz weight (y/n − 1)₊. The averaging itself works with S(Z, y, q, κ) = Σ_{n≤Z} cN(y, n)κ(n)(n/q)
(`MSB/PrimeSetTwoBounds.lean:13-14`), where cN(y, n) = Λ(n)·min(1, y/n) (`JCS/MSqMain.lean:19-21`). The two are tied exactly
by g_χ(y) = −S(Z, y) − y·tail(Z) (`MSB/BoxOfS.lean:45`, `finite_splitting_of_group`). The tail is ≤ Y^ε inside the zero-free box (`tailK`).

**Families and sizes.**
- `admitted ε Y U m₀ a₀` (`MSB/PrimeSetTwoBounds.lean:18-24`): 8 | m₀; (a₀, m₀) = 1; ¼log²Y·log m₀ ≤ log U; Y^{ε/6} ≤ log U ≤ Y^{ε/5}log²Y.
- `MeanSq C Z P A` (`:26-27`): ∀ y ∈ A, ∀ |κ| ≤ 1, Σ_{q∈P} |S(Z, y, q, κ)|² ≤ C·y log y·#P.
- q-family: P₁ = PPset 8 3 (e^z), z = Y^{ε/5} (`:41`).
- d-family (for fixed q): primes d ≡ 7 mod 16 with oddM(z, q) | d+1 and e^{z′/2} < d ≤ e^{z′} (`:45-46`), z′ = Y^{ε/5}log²Y.
  Here oddM(z, q) = q·∏_{3≤p≤z} p (`Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:53`). The modulus is m₀ = 16·oddM, with
  log m₀ ≤ 4z (`MSB/CharOf.lean:140`).

**`meanSqK`** (`MSB/meanSqK.lean:51-54`, read in full). There is C > 0 such that for 0 < ε ≤ 1 and K ≥ 1, eventually in Y: for
admitted (U, m₀, a₀) all of whose prime factors are either ≤ Y^{ε/5} or > Y^{400K},
`MeanSq C (Y^{400K}) (PPset m₀ a₀ U) [Y, Y^K]`.

**`twistK`** (`MSB/twistK.lean:148-151`, read in full). For ε, A, B > 0, eventually in Y: for admitted (U, m₀, a₀) **there is one n\***
such that every odd squarefree s > 1 with (s, m₀) = 1, s ≤ Y^A and s ≠ n\* satisfies |Σ_{q∈PPset m₀ a₀ U}(q/s)| ≤ Y^{−B}·#PPset.

**Host existence.** `HostExW la P` (`TSI:120-123`, read): for each ε there are constants and a la-window family S of scales. Every
s ∈ S with s.x ≥ x₀ has R, H, q₀ with RankVal, H.CT2 = CT2, `HostGood` and P. `HostGood` (`TSI:101-109`, read) includes:
- `QDq s.x ε C5 q d`, i.e. BoundsAtX for (·/q), (·/d) and (·/qd) at the point x (`Formalism/SharpRestriction/InertJacobiLevels/AsmIface.lean:166-168`;
  `BoundsAtX`, `Formalism/SharpRestriction/GlobalSchurBounds/Chosen.lean:38-40`: ‖g_χ(x)‖ ≤ x^{1/2+ε} and ‖L′/L(1)‖ ≤ C log x);
- `BoxW`;
- |dlogH| ≤ x^ε, where dlogH = Re L′/L(1, (·/d)) (`TSI:24-28`);
- `ThinOK`, `BadOK`, and the level-prime and q₀ clauses.

The live P is `EAtH (Level.cyc ψ) H TT x ε 4 ∧ VVle …` (`SN/supplyOfAdmOf.lean:23`). `EAtH` (`ExplicitFormulaErrorOfHostConditions.lean:144-151`,
read) contains **`bdG`**: ‖g_χ(x)‖ ≤ x^{1/2+ε} for every χ that is primitive for a θ ∈ `Bounded`, and **`bdL`**: ‖L′/L(1, χ)‖ ≤ C log x for the same χ.
`Bounded` = (X⁺ \ Kept) ∪ X⁻ (`An/Analytic.lean:136`). By `TwistForm` (`CB/TwistForm.lean:14-17`) and `boundedTw_key`
(`CB/BoundedTw.lean:5-43`), these are exactly the twists ξ(·/q)^i(·/d)^j, ξ ∈ ⟨ψ⟩, (i, j) ≠ 0: that is 3o characters.

**Range resolved.** `winPairs` (`CB/WinPairs.lean:5-81`, read) works as follows:
- It takes Y = X^{1/J} with X ≥ M^J and gets (q, d) from `PairEx` with A = J (`:34`), **before** quantifying over x (`:52`).
- It returns Z′ = kW such that every x ∈ [Z′, Z′^{3/2}] has `WinDatum` with that same (q, d) and `PairGood ψ.N ε Y x q d`, by `mono` from [Y, X] (`:68`).

So one host pair serves a whole Landau window, and the bound holds on all of [x^{1/J}, x]. `boundedTw` then evaluates it at
y = x only (`CB/BoundedTw.lean:53,56`).

## 2. Argument

**(a) The mean square, by orthogonality** (`meanSqK` ← `meanSq_abs`, `MSB/MeanSqAbs.lean:8-58`, read).
1. Expand |S|² as a double sum over n, n′ ≤ Z of cN(y,n)cN(y,n′)κ(n)κ̄(n′)·Σ_q (nn′/q).
2. Every q in the family satisfies q > ⌊Z⌋² (`meanSqK.lean:91-106`, from Z² = Y^{800K} ≤ U^{1/2} < q, using log U ≥ Y^{ε/6} ≫ 1600K log Y).
   Since 8 | m₀ and q ≡ a₀ mod m₀, quadratic reciprocity gives |Σ_q (nn′/q)| = |Σ_q (q/s)| with s = soutPart(m₀, nn′), the product
   of the primes p ∤ m₀ that divide nn′ to an odd power (`abs_pair_sum_eq`, `JCS/MSqMain.lean:38-53`; `soutPart`, `JCS/MeanSquareHypWIff.lean:48-49`).
3. The pairs fall into three classes:
   - **s = 1 (diagonal).** n, n′ are powers of one prime with the same parity, or both are supported on primes dividing m₀
     (`pairs_one`). They contribute Σ_p sP(p)² + RR², where sP(p) = Σ_{p^a≤Z} cN(p^a) and RR = Σ over even prime powers and m₀-primes
     (`JCS/MeanSquareHypWIff.lean:51-55`). Then Σ_p sP² ≤ C₃ y log y (`sPsq_le`) and RR ≤ C₁(√y + w log y) with w = Y^{ε/5} ≤ y^{1/5}
     (`RR_le`), so RR² ≤ 25C₁² y log y (`meanSqK.lean:157-170`).
   - **s = n\*.** Bounded trivially by |Σ_q| ≤ #P. These pairs number few: since n, n′ are prime powers, n\* must be a prime or a
     product of two primes, giving ≤ 2B² + 2B·RR with B = max_p sP(p) ≤ C₂ log y (`pairs_r`, `JCS/MSqPairs.lean:307-324`, read).
   - **Other s ≤ Z².** `twistK` gives η = Y^{−(K+1)}, so these contribute η(Σ_n cN)²·#P ≤ Y^{−K−1}·C₄²y²(400K log Y)²·#P ≤ C₄²y·#P, using y ≤ Y^K
     (`meanSqK.lean:193-215`).
4. Total: Σ_q |S|² ≤ (C₃ + 25C₁² + 4C₂² + 20C₁C₂ + C₄²)·y log y·#P (`:219-221`). I checked this arithmetic line by line. It is the
   expected diagonal y log y.

**(b) `twistK`** (`MSB/twistK.lean:148-354`, read).
1. Write Σ_{q≡a₀ (m₀)} (q/s) through π(X; m₀s, b), with X = U.
2. Apply `PNTAPRelW` (`JCS/MeanSquareHypWIff.lean:38-46`, read): for 8 | M and log X ≥ C₀ log M·log log M,
   π(X; M, b) = mainAP·(1 + O(e^{−c₃ log X/log M} + e^{−√(c₃ log X)})), where mainAP subtracts χ₁(b)li(X^{β₁}) when M has an exceptional pair.
3. The ratio log X/log M ≥ ¼log²Y follows from `admitted.log_m` and log s ≤ A log Y. It makes the relative error ≤ Y^{−B}.
4. **Exceptional zero.** Call s *bad* if the exceptional character of m₀s has 1 − β < c₀/log Z and restricts to (·/s) on
   u ≡ 1 mod m₀ (`:249-251`). `page_across`, Landau–Page across moduli ≤ Z (`:258-274`), shows there is at most one bad s.
   That s is n\*.
5. For any other s, an exceptional zero either has β ≤ 1 − c₀/log Z, which gives li(X^β) ≤ r·li X with r = 4 log X·e^{−c₀ log X/log Z}
   (`:315-328`), or does not correlate with (·/s). The second case is handled by `twist_one`, which I did not read.
6. #PPset ≥ X^{9/10} comes from `count_a` (`:330`).

**(c) From mean square to all y in the window** (`bad_share`, `MSB/BadShare.lean:251-320`, assembly read).
1. Split [Y, X] into dyadic blocks [2^iY, 2^{i+1}Y].
2. In each block, a Sobolev bound with ∂S/∂y (`bs_block`, `bs_markov`) and Markov show that the proportion of q with
   |S(y)| > y^{1/2+τ}/2 somewhere in the block is ≤ (32C/τ)(2^iY)^{−τ}.
3. Summing the geometric series, the bad proportion over all of [Y, X] is ≤ (32C/τ)Y^{−τ}(1 − 2^{−τ})^{−1} → 0.

The single κ is fixed and independent of q: in `stage` it is κ = ξ.2 (`MSB/StagePow.lean:103`). So a uniform-in-y bound is
obtained from the mean square, and there is no union bound over y.

**(d) One family** (`stage`, `MSB/StagePow.lean:41-170`, read in full). Let Ξ be the list of primitive κ, of size ≤ R and conductor ≤ F ≤ U^{1/2}.
1. Put into B₁ the q for which some twist ξ·(·/q) has a zero in the box. `count_bad` bounds #B₁ ≤ C_b(FU)^{1/4} ≤ C_b·U^{3/8} ≤ (η/2)·U^{9/10} ≤ (η/2)#P (`:141-154`).
2. Put into B₂(ξ) the q that fail the window bound. `bad_share` with η/(2(R+1)) bounds each (`:155-167`).
3. Every other q has `BoxAll` by `box_of_S` (`MSB/BoxOfS.lean:28-60`, read): GoodC, |L′/L(1)| ≤ C log Y, and |g_χ(y)| ≤ y^{1/2+τ} on [Y, Y^K].

`stage2` (`MSB/CharOf.lean:61-…`, read to :152) applies `stage` to the d-family with m₀ = 16·oddM(z, q), using ε′ = 6ε/5:
- `admitted` holds because ¼log²Y·4z = z log²Y ≤ z′ (`:125-149`);
- every prime of m₀ is ≤ z, or equals q, and q > Y^{400K} (`:112-119`);
- κ ranges over ξ·(·/q)^a with a ≤ 1, so R = 2φ(N₀).

`pair_exists` (`MSB/PairExists.lean:9-49`, read) takes η = ½ in `pair_share`, picks a good q and then a good d, and assembles them.
`pairEx` (`MSB/pairEx.lean:112-169`, read) applies this with τ = ε/2, K = A and N₀ = 8M, and obtains the 4 log y bound from `kappa4`.

**(e) Simultaneity with the structural requirements.** `supplyOfAdmOf` (`SN/supplyOfAdmOf.lean:13-135`, read in full) takes the
(q, d) from `winPairs` (`:29`, `:57`). It then uses three hypotheses, each quantified over **all** inputs of the relevant kind:
- `fieldChi` (`:93-94`), applied to any WinPair. Its side conditions (−d/p) = 1 for odd p ≤ Y^{ε/5} follow from p | d+1 (`pairHyp`, `:68`, `:91-92`).
  It builds E, the frame and `KerChi`.
- `hAdm` (`:95`), for every HostAx with KerChi. It gives ranks and `admitted`.
- `hSup` = `hostOfField` (`CB/HostOfField.lean:8-15`), for every (q, d) with `PairGood`, FieldRows and admitted.

`hostOfFieldOf` (`SN/hostOfFieldOf.lean:159-255`, read lines 17-46, 159-255) then builds everything else from `PairGood` alone:
- the level primes, p, p′ and q₀ come from `levelData`, with size ≤ (QS·q·d)^{C1};
- TT comes from `topsChoiceH`, and T2 from `hof_thick`;
- QDq and Boxq come from `pairRows` (`CB/PairRows.lean:334-347`, read), built from `bounds` at y = x and from `boxes`;
- BoxH and RealBox come from `hof_box`;
- ThinOK comes from `QH.thinH` together with RealBox;
- |dlogH| ≤ 4 log x ≤ x^ε comes from `hof_abs_dlogH_le` (`:38-45`), via QDq applied to (·/d).

**So no density argument is needed.** The averaging excludes a proportion ≤ ½ of q, and then ≤ ½ of d. Every remaining pair is
structurally admissible (*inferred* from the hypotheses being ∀-quantified; the bodies of `levelData`, `topsChoiceH`, `fieldChi`
and the supplier of `hAdm` were not read).

**(f) Consumers of the twist bound.**
1. **`bdG`** → `sigA_le` (`Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean:38-60`, read). It gives SigA ≤ #PsiA·x^{1/2+ε} = 4o·x^{1/2+ε},
   summing over PsiA \ kept. This is the only use of `.bdG` found.
2. **`bdL`** → `charsA.lean:125` (read 105-125). It bounds ell(ψ) ≤ C log x for the bounded characters in the bridge.
3. **QDq → ValuesAtX** (`Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:67-69`, read) covers (·/q), (·/d) and (·/qd) at x. It enters:
   - De, through −G_chC and G_chpsC (LEDGER row "split");
   - `three_bound`/`signal_term` (`Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:262-300`, read). These pass from x to y with
     |y − x| ≤ 1 through `DerivInt`, at a cost of O(log x). No second square-root point is needed.
4. **dlogH = L′/L(1, χ_{−d})** ≤ 4 log x, as in (e).
5. **`boxes`** → BoxH and RealBox → ThinOK/ThinScales. ThinScales uses the zero-free boxes, not the y^{1/2} bound.

## 3. Children

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `meanSqK` / `meanSq_abs` | `MSB/meanSqK.lean:51`; `MSB/MeanSqAbs.lean:8` | Σ_{q∈P}\|S(Z,y,q,κ)\|² ≤ C y log y·#P for y ∈ [Y, Y^K], q > Z² | source of y^{1/2} | core (read; arithmetic checked) |
| 2 | `twistK` | `MSB/twistK.lean:148` | \|Σ_q (q/s)\| ≤ Y^{−B}#P for s ≤ Y^A, s ≠ n\* | off-diagonal | core (read; `page_across`, `twist_one` and `final_ineqK` statements not read) |
| 3 | `PNTAPRelW` | `JCS/MeanSquareHypWIff.lean:38`; proof `JCS/PNTFinal.lean:22` (per PAIRGOOD) | Gallagher-type PNT in APs, exceptional zero in main term | twistK | standard (Gallagher); proof not read |
| 4 | `page_across`, `excBound`, `zFRDirichlet` | used at `twistK.lean:156-158` | Landau–Page uniqueness across moduli; Siegel; classical zero-free region | exceptional s | standard; not read |
| 5 | `pairs_one`, `pairs_r`, `sPsq_le`, `RR_le`, `sum_cN_le` | `JCS/MSqPairs.lean:255,307` | diagonal and n\* pair counts | mean square | standard elementary; `pairs_r` read, others statement-level |
| 6 | `bad_share` | `MSB/BadShare.lean:251` | Markov + dyadic Sobolev: few q fail anywhere on [Y, X] | uniform in y | glue (assembly read; `bs_block` not read) |
| 7 | `count_bad` ← `zero_density_box` | `MSB/StagePow.lean:142` | ≤ C Q^{1/4} characters with a box zero | removes Siegel-type q, d | standard (zero density); not re-read |
| 8 | `box_of_S`, `tailK`, `kappaC`, `kappa4` | `MSB/BoxOfS.lean:28` | g_χ = −S − y·tail, \|y·tail\| ≤ Y^ε, \|L′/L(1)\| ≤ 1000 log log Q + C ≤ 4 log y | S → g_χ, L′/L bound | standard; BoxOfS read, rest per PAIRGOOD |
| 9 | `stage`, `stage2`, `pair_exists`, `pairEx` | `MSB/StagePow.lean:41`; `MSB/CharOf.lean:61`; `MSB/PairExists.lean:9`; `MSB/pairEx.lean:112` | bookkeeping of (d) | assembly | glue (read) |
| 10 | `winPairs`, `supplyOfAdmOf`, `hostOfFieldOf`, `pairRows`, `boundedTw` | `CB/WinPairs.lean:5`; `SN/supplyOfAdmOf.lean:13`; `SN/hostOfFieldOf.lean:159`; `CB/PairRows.lean:334`; `CB/BoundedTw.lean:45` | one (q, d) per window → host → EAtH, QDq, BoxW, dlogH | host selection | glue/core (read) |
| 11 | `levelData`, `topsChoiceH`, `fieldChi`, `hAdm` supplier | `SN/hostOfFieldOf.lean:167,171`; `SN/supplyOfAdmOf.lean:28` | structural host data for every WinPair | simultaneity | definitions to unfold (not read) |

## 4. Oddities

1. **Not the large sieve.** The family of moduli is enormously larger than Z² (log q ≍ Y^{ε/5} against log Z² = 800K log Y). So plain
   orthogonality via reciprocity and PNT in APs suffices. This is easier than Heath-Brown's quadratic large sieve and is classical.
   The y-range [Y, Y^J] is polylogarithmic in the conductor (y ≤ (log q)^{5J/ε}).
2. **Range versus point.** The bound is proved on [X^{1/J}, X] for one (q, d). It is used at y = x for each x of a window [Z′, Z′^{3/2}] ⊆ [X^{1/J}, X],
   plus a Lipschitz step to |y − x| ≤ 1. The averaging supplies all of this at once, so the "at more points than the average gives" worry does not arise.
3. `PairGood.bounds` covers **all** φ(M) characters ξ mod M = ψ.N, not just ⟨ψ⟩. `stage` also takes all ξ mod 8M, which is finite and fixed.
   It is stronger than needed and harmless.
4. **Siegel and L′/L(1, χ_{−d}).** No a-priori unconditional bound is used. The bound |L′/L(1, χ_{−d})| ≤ 4 log x comes from selecting d:
   d is admitted only if every twist (including (·/d) itself, GoodD with a = 0 and ξ = 1, `MSB/PrimeSetTwoBounds.lean:51-53`) is zero-free in the box,
   and the zero-density count makes such d all but ≤ CU^{3/8}/U^{9/10} of the family. Siegel (`excBound`) enters only inside `twistK`, which makes Y₀ ineffective.
5. The exceptional s = n\* is handled correctly: its pairs are bounded trivially, and since n, n′ are prime powers they are few.
   This answers PAIRGOOD's unchecked row 5.
6. Two other `BoundedCharsPointwise` definitions, with a "MeanSquare" alternative clause, exist in
   `Development/AutomorphicArithmetic/QuadraticCharacters/ExceptionalCharacterCondition.lean:41,63` and `A0InfStabilizerTrivial.lean:133,145`.
   I did not check whether they are on the live path. The live one is `An/Analytic.lean:154-156`.
7. `sigA_le` sums over PsiA \ kept, so the 4o in its bound counts all of PsiA, not just the 3o twists. This is loose and harmless.

## 5. Coverage

Read:
- `CB/PairGood.lean` (all), `CB/BoundedTw.lean` (all), `CB/WinPairs.lean` (all), `CB/TwistForm.lean:1-30`, `CB/ExistsPageN.lean:1-60`, `CB/HostOfField.lean` (all), `CB/PairRows.lean:334-387`;
- `An/Analytic.lean:1-30, 125-176`;
- `MSB/meanSqK.lean` (all), `MSB/MeanSqAbs.lean` (all), `MSB/PrimeSetTwoBounds.lean` (all), `MSB/twistK.lean:140-355`, `MSB/BadShare.lean:240-320` (and its lemma index),
  `MSB/BoxOfS.lean` (all), `MSB/StagePow.lean` (all), `MSB/CharOf.lean:61-152`, `MSB/PairExists.lean` (all), `MSB/pairEx.lean:112-171`;
- `JCS/MeanSquareHypWIff.lean` (all), `JCS/MSqMain.lean:1-60`, `JCS/MSqPairs.lean:300-326`;
- `TSI:20-28, 55-127`; `SN/supplyOfAdmOf.lean` (all); `SN/hostOfFieldOf.lean:17-46, 159-255`;
- `AsmIface.lean:160-175`, `Chosen.lean:36-44`, `ExplicitFormulaErrorOfHostConditions.lean:135-165`, `SigALe.lean:1-60`, `charsA.lean:105-125`,
  `GrowthBoundGivesRiemannHypothesis.lean:60-72`, `LipschitzWeightAndMinimum.lean:258-300`.

Greps run: `\.bdG\b|bdG :` (two hits: definition and `SigALe.lean:50`); `BoundedCharsPointwise` (five files); `ValuesAtX`;
`boundedTw\b|winPairs\b|WinDatum`; `def dlogH|def QDq|supplyOfAdmOf`; `dlogH` in `Development/AutomorphicArithmetic`.

Not opened:
- `twist_one`, `page_across`, `final_ineqK` (statement only), `count_a`, `bs_block`, `sPsq_le`, `RR_le`, `sum_cN_le`, `tailK`, `kappa4`;
- the PNTAPRelW proof chain, `zero_density_box`;
- `levelData`, `topsChoiceH`, `fieldChi`, `hof_thick`, `qdBig`, the `hAdm` supplier;
- `ThinH` and `thinH` bodies.
