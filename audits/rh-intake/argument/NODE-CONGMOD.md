# NODE-CONGMOD: where the Selmer / congruence-module bound enters the slope chain

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations: `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`,
`LL` = `Formalism/LocalToGlobal/Divisibility/`, `RL` = `LL/RowLat.lean`, `TPE` = `LL/TwistedPlaceEtaSumLeExtended.lean`,
`SO` = `Formalism/DivisorInequality/StatementObj.lean`, `DHB` = `LL/DivisionHeightBoundStatement.lean`,
`DN` = `Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean`, `DR` = `Formalism/LocalRingCardinality/DataRows.lean`,
`DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`, `IE` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`.
"The Lean says" means I read the line. *(inferred)* means my reading. Nothing was compiled. Chain line numbers (1)–(12) are NODE-WRITEUP's.

## 0. Answer in brief

- **The consuming line is WRITEUP (7), piece (A).** This is the upper bound on the target slope μ(RR^∨) by the covolumes of the
  layer lattices M_j (`BoundsMu`, `SO:17-79`). It is not an error term of the slope inequality (5). It is not the colength (2). It is
  not the height of B_u. The congruence modules sit in the error E2 of (A). (A) feeds the DIV clause, whose error is
  C·m·(B0+Nc)·x^{Cabs·ε}. They also sit in the passage constant Q (`deQ: 3·de·Q ≤ 1`).
- **Mechanism.** RR is glued place by place from *different type parts*. At a place y the Lean takes RR_y = ι(μ(y))·(projection of the
  integral lattice onto the type-μ(y) part) (`SO:47`; `RRset`, `DR:196-199`). At "twisted" places, μ(y) ≠ μ0. There the projected
  lattice T_j of each lift layer is not self-dual. Its dual-index jw(T_j) is bounded by the **congruence module**
  η_j(y) = len_y[Pr_Z(L) : L ∩ Z] plus small terms (`jw_le`; `etaU`, `LiftLat.lean:118`). Your guess is right: the cost is
  "forms congruent mod l to forms outside the type part". The bound needed is an **upper** bound.
- **From congruence to Selmer.** `GlobalCongruenceCountOfRootDifferenceUnit.main` runs Ribet's direction: congruence ideal ⇒
  extension classes. It bounds each eigen-system's congruence ideal by local Selmer + Σ_{0<e<t} len Ш¹(E, ℚ_l/ℤ_l(−e)) + v_l(h_E)
  + tame terms. Then `EtaBound` gives etaLoc ≤ Σ_π mult·(that bound). Summing over the places w | l with weights lw·e_w gives
  exactly log l·len Ш. That is why VWin carries the weight log l.
- **Size.** VWin's Ш sum is **not** at the budget. LinkN adds it to C·f·m·b·L² per dimension. The proof needs only Σ ≤ b, and VWin
  gives √b. What sits at the budget is the allowance η_j ≤ D0·C·x^ε(B0+Nc). Summed over j ≤ m this is ≈ x^{3+O(ε)}·b, the
  "m-family" of NODE-ACCOUNT.
- **The dependence is real.** It holds on the route as built. Twisted places include every prime below X″ = a/w″, which is the
  whole range where the gain lives. If Ш exceeded about x^{2.5}·b, DIVinN would fail, the error of (7) would grow by about
  m·Σ log l·len Ш, and the final inequality would no longer close. VWin is not a host-existence convenience. The host requirement
  is just where the bound is stored.

## 1. Statement(s)

### 1a. The quantities (Lean, unfolded)

- **Type parts.** `BlockDat` (`RL:52-73`) is a space of forms with Hecke operators `op` and a G-action. `Z` is a Hecke-stable
  subspace, the "type part" (`ZStable`, `RL:124`). There is a level idempotent (P, ψ) and a hermitian form `HV` on its good part.
  - `Tl` = matLat(lPr, lvlNab) (`RL:153`): the image of the integral level lattice under the **orthogonal projection** Pq onto Z
    (`orthPr` = (EᴴHE)⁻¹EᴴH, `GoodPartHermitianSpec.lean:61`).
  - `cutZ` = cutLat(fE, nabLat) (`RL:155`; `cutLat` = comap, `ClassSumDualLe.lean:15`): Z ∩ the integral lattice.
  - **etaW(w) = len_{O_w}(Tl/cutZ)** (`LiftLat.lean:116`; `lenW`, `AlgebraMapMemMaximalIdealPowIff.lean:91`), and etaU = etaW/e_w.
    This is Hida's **congruence module** of the type part Z in the integral lattice, localised at w.
  - `DefFam.etaJ j t w` = etaU of lift layer j for tuple t (`LiftLat.lean:147`).
- **At a local index i** (`DN:150-221`), with residue prime l_i, coefficient DVR O_i, Hecke algebra T_i acting on a free O_i-module Mt_i
  of eigen-systems X_i, and the good set Zgood_i:
  - MtUp = (Zgood-eigenpart) ∩ (Mt + complementary eigenpart), i.e. the projection of Mt onto the Zgood-part;
  - MtLow = Mt ∩ (Zgood-part);
  - **etaLoc i = len(MtUp/MtLow)** (`DN:219-220`), the same congruence module;
  - **vcc i π = len O_i/cc(π)** (`DN:225-226`), the congruence ideal of the single eigen-system π against the cut.
  - The Lean ties these together: `etaJ_tie`: etaJ j w = Σ_{i ∈ locs j w} etaLoc i (`RhoDetPrimeEqMuTildeMulChiPow.lean:283`).
- **Twisted places.**
  - Tuples ("types") form a set `Tup` with a base point mu0, and each place has muAt w ∈ {mu0, muTw w} (`DR:51-60`).
  - The family records `untwisted`: muAt w = mu0 ⇒ A_j(w) = 0 and F_j(w) = 0 (`DP2:110` region, read).
  - The host constructor ties the twisted places to residue characteristic: muAt w ≠ mu0 **iff** resChar w ≤ X″(n) or
    resChar w ∈ {d, g0, g1} (`InertJacobiLevels/ExtraFinal.lean:25`, the `hmt` iff; one direction is also in `AsmTie.lean:30`).
  - X″ = a/w″ (`DP2:39`) ≈ x·n·e^{x^{ε/3}} (ACCOUNT table).
- **η_j** = etaSum L j = Σ_{w∈supp, μ_w≠μ0} lw(w)·e_w·etaJ(j,w) (`GTI:37-40`).
- **LinkN_at** (`GTI:42-45`): if Σ_l vvTerm(l) converges, then
  η_j ≤ dZ0(j)·( C(f·m·b·L² + log²x·Nc) + Σ_l log l·Σ_{1≤e<t} len Ш_l(e) ).
  Here dZ0 j = dim Z_j(μ0) (`DP2:194`) and vvTerm l = log l·Σ_{e<t} shaLen (`GTI:32-33`).
- **DIVinN_at** (`GTI:59-60`): η_j ≤ D0·C·x^ε·(B0 + Nc), where:
  - B0 = f·m·b·x^ε (`DataArith.lean:200`);
  - Nc = #T2·k·b·x^ε/(n·n·x^{−ε}) (`DataArith.lean:204-205`);
  - b = e^{x^ε}.
- **divinN_of_hypV** (`CharacterBoxes/DivinNOfHypV.lean:117-130`): HypV (= VVle E t √b) + LinkN + dZ0 = D0 ⇒ DIVinN. It uses VVle only
  through Σ' vvTerm ≤ √b ≤ b ≤ B0 (`:122-128`, `divinN_at :70-112`).

### 1b. `GlobalTheory.CutCoreUnit.main` (`IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`)

The Lean says (paraphrased literally). Assume:
- global Artin reciprocity;
- D7, a local index i (residue prime l = l_i), families r(x) : G_E → GL_{nV}(O_i) and ρ(x) : G_E → GL_r(O_i) over the
  eigen-systems x ∈ X_i, and π ∈ Z_i;
- an orthogonal idempotent decomposition S of the GMA of r into a ρ-block and t character blocks;
- `GoodR`, `NoChiOff`, `UnrOut` (unramified outside the listed places);
- at v ∈ S_i (places over g0, g1 and pde) a quadratic relation with ζ_v − 1 a unit, or a polynomial condition;
- at the tame set Q_i a quadratic relation with ζ_q ≠ 1;
- at each w | l: the ρ-block satisfies LocBound with exponent 0, cut cocycles in χ-blocks c ≥ 2 lie in the local lattice BD, and the
  c = 1 block is unramified (Z1ur);
- finiteness of the local Selmer term of ρ (`sFin`) and of Ш_l(e) for 0 < e < t.

Then

  **vcc_i(π) ≤ sPi(ρ_π) + Σ_{0<e<t} len Ш¹(G_{E,S_l}, ℚ_l/ℤ_l(−e)) + v_l(h_E) + t·Σ_{q∈Q_i} len O_i/(ζ_q − 1).**

E = D.host.E, the **host field**. The character blocks are fixed by `chi_def` (`DN:126-129`): χ_c = χ_1·ε_cyc^{−(c−1)} for 1 ≤ c ≤ t.
`chiRatO c` = χ_c/χ_1 = ε^{−(c−1)} (`QuotientHomNonvanishingBound.lean:283-284`).

`StepsNoCut.GlobalStatement` (`TPS/StepsNoCut.lean:18-32`) is the same bound with a cut set Xs and extra local exponents eρ, eχ.
`LocalCongruenceBound` (`LocalCongruenceBound.lean:12-20`) adds a polynomial term f·2(2r+2t)·CT·(N r′ + (η+t+1)(N+r′)) and 4nV·vdel.
`EtaBound` (`CongruenceSingleEndomorphism.lean:87-92`): etaLoc i ≤ Σ_{π∈Zgood} mult(π)·(c_π + v_{g_k}|G|), with each c_π satisfying
LocalCongruenceBound.

## 2. Argument

### 2a. Where η is consumed: WRITEUP (7)(A)

1. **The glued lattice.** `BoundsMu` (`SO:17-79`, proved as `slope_bounds`) takes the target lattice R with
   R_y = ι(μ(y))·abelian₂(μ(y)) locally at every finite y (`SO:47`). abelian₂ t is the projection Pq of the integral lattice onto
   the type-t part (`RL:151`). So **RR's integral structure is glued across types (Hecke characters)**. This is the author's item 15,
   *(inferred)* visible as a hypothesis.
2. **Comparison with the lift layers.** At y ∈ Tw it compares R with the layer lattices M_j through the theta maps θ_j(μ(y)).
   - The indices are idx(M_j, θ·T_j) + idx at the conjugate place, bounded by (2F_y + err)·D. The 2F part is the Fo that cancels in
     WRITEUP (9).
   - The **dual index** jw(H_j, y, T_j) = lidx(T_j, T_j^∨) (`jIdx`, `HermitianLattices/StatementLat.lean:98`) is assumed to satisfy
     jw ≤ J_y·D + η_y (`SO:69`).
   - Away from Tw all these indices vanish (`SO:54-58`).
   - Conclusion (`SO:75-77`): μ(R^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + 2ΣF + LG + Σ_j(E1_j + **E2_j**) + E3, with
     Σ_{y∈Tw} lw·η_y/D ≤ E2_j.
3. **Dual index ≤ congruence module.** The instance is `lift_index_bound_extended` (`TPE:30-60`) ← `jw_le` (`LiftLatLemmas.lean:663`):
   jw(T_j) ≤ etaW + d·(JJW + v(DG) + v(s)). *(inferred)* If the ambient lattice were unimodular, T^∨ = L ∩ Z, so jw = len(T/(L∩Z)) is
   exactly the congruence module. JJW measures how far the ambient lattice is from self-dual (cutZ vs delZ).
4. **Assembly.**
   - `twisted_place_eta_sum_le_extended` (`TPE:62-104`) turns InEta (Σ_y lw·etaJW ≤ bd_j·D) into E2_j = bd_j + log dg + log s.
   - `inEta_num` (`SumLeEtaSumNum.lean:60-76`) gets InEta from DIVinN with bd_j = divSize = C x^ε(B0+Nc) (`TPE:315`).
     The bridge `sum_le_etaSum_num` identifies the place sum with etaSum.
   - `inpAt_of` (`InpAtOf.lean:22,46`) consumes DIVinN there.
   - In `DivClauses` (`DHB:779-813`), E2 enters hB (BoundsMu) and then hM:
     mu0 ≤ Σ pq·w·logΩ + 2Fo + (El3 + LG + Σ_j(E1_j + E2_j) + E3).
   - It is closed by `RecNums.divIneq` (`DHB:131-160`) with Eb ≤ errB. errB has the shape ce·m·x^ε(B0+Nc) (`errB_of_units`,
     `DHB:846-865`; `errB_rec` ≤ 2ce·szPol⁵·b, `EigenvalueSumLeClosedOf.lean:1845`).
   - E2 also enters Qb ≤ Q with 3·de·Q ≤ 1. That is the passage from base to columns (`DHB:798-805`).
   - Result: LinkDIV_at clause (vii): μ(RR^∨) + h − Fo ≤ MAIN + C|TT|aLa + **C·m(B0+Nc)x^{Cabs ε}** (`GTI:84-86`).
5. **Why the twisted places matter.** The twisted places include every place of residue characteristic ≤ X″. The gain is
   Σ_e(a/p^e − w)₊ with w ≥ w″, so it vanishes for p ≥ X″ *(inferred from the count shape, NODE-ACCOUNT)*. So the twisted places
   contain every served prime.
   - At those places the source side uses twisted-tuple periods (`TwistedPeriodAdmissible`, `AdmissibleAtGeneratorPlaces.lean:14-19`:
     periods for μ ≠ mu0 are integral up to −ur·v(DG)). The F_j shift is supported there (`untwisted`).
   - *(inferred)* The twist is what makes integrality (4) hold at the served primes. The F part nets to zero (Fo). The congruence
     module η is the uncancelled price of using a type-part lattice rather than a self-dual one.

### 2b. From congruence modules to Ш (the proof of `main`, `IE/…:56-118`)

- Fix the GMA decomposition S of r over the local Hecke algebra (Bellaïche–Chenevier style). The congruence ideal of π is controlled
  by the module of reducibility cocycles. Those split into a ρ-block `cocRho` and character blocks `cocChi c`, c = 0..t−1, where
  block c lives in H¹(G_E, ℚ_l/ℤ_l(−c)) (via chiRatO).
  - **ρ-block:** bounded by local Selmer, via `length_global_cocycles_le_sum_places_over` and
    `length_cocycles_le_coboundaries_add_selmer`. The coboundary module is 0 because del51 is a unit.
  - **c = 0:** unramified homomorphisms that are locally trivial in the cut at l, so ≤ v_l(h_E)·len(O/l)
    (`UnramHom.length_le_classNumber`, which needs Artin reciprocity).
  - **c ≥ 1:** unramified outside l after peeling off Q (`Cut.Peel.main`; each q ∈ Q costs len O/(ζ_q−1)). At S the restrictions
    vanish by the quadratic or polynomial relations. At w | l they lie in BD. So they lie in Ш¹(ℚ_l/ℤ_l(−c))
    (`length_cyclotomic_block_cocycles_le_sha`).
  - This is the safe Ribet/Mazur direction (congruence ⇒ class) that ONECHARU noted.
- **Which twists, and why up to x^{401}.** e = c − 1 ranges over 1..t−1, where t = R.t is the number of character blocks in r (r has
  dimension nV; *inferred* nV = r + t).
  - The bound 1 ≤ t ≤ x^{Ct} is the field `t_win` (`DP2`, read). NODE-ACCOUNT gives t ≈ x^{398.5}.
  - The host requirement uses VVle at ⌊x^{400}⌋ and weakens it to R.t (`VVle.mono`, NODE-HOSTS).
  - VWin is stated with ⌊x^{401}⌋ for slack.
  - So the twists are the Hodge–Tate gaps between the t consecutive cyclotomic characters in the residually reducible part of the
    lifted forms' Galois representations.
- **Which field.** Ш is over the host E (`D.what₂.shaLen`, `D.nd.ldat`; VVle H.E in `(GChi ψ).req`). E has degree ≈ x^{2+8ε}.
  - Reconciliation with "conductor chosen tiny": log cond E ≈ Y^{ε/5}log²Y, which is tiny relative to x^ε, not small.
  - The degree enters only through the number of Dirichlet-character components ψ′. In VWin's proof (NODE-VWIN §2) each component is
    bounded over ℚ (minus part) or via U(3) over an imaginary quadratic K (plus part).
  - So there is one large field, split into many small (ℚ, ψ′) problems.
- **Weights.** Σ_{w|l} 2·lw·e_w = 2 log l (`FactUnitNormalisation`). So η_j = Σ_w lw·e_w·Σ_{i∈locs} etaLoc_i ≤ D0·Σ_l log l·(Ш_l + …).
  The log l in VVle is exactly the place weight. The factor D0 counts eigen-systems (Σ mult ≤ rank).

## 3. Size check (task c)

The scales are from NODE-ACCOUNT: f = 2n ≈ 2x^{2+8ε}, m ≈ x^{1/2−ε/16}, k ≈ x^{9/2+10ε}, #T2 ≥ x^{−ε}n.
- B0 = f·m·b·x^ε ≈ x^{2.5+O(ε)}·b.
- Nc ≈ k·b·x^{2ε}/n ≈ x^{2.5+O(ε)}·b.

| quantity | size | vs budget x^{3+O(ε)}·b |
|---|---|---|
| per-lift allowance bd_j = C x^ε(B0+Nc) (DIVinN, per dimension) | x^{2.5+O(ε)}·b | ×m: **at the budget**, coefficient x^{O(ε)} |
| Σ_j E2_j ≤ errB = ce·m·x^ε(B0+Nc) | x^{3+O(ε)}·b | = the "m-family" (EComp5, QSB, DIV's m(B0+Nc)) |
| Ш contribution per dimension, Σ_l log l·len Ш (VWin) | ≤ √b | ×m ≈ x^{1/2}√b: **negligible**, by a factor x^{2.5}√b |
| C·f·m·b·L² in LinkN (non-Ш congruence terms) | x^{2.5+O(ε)}·b | this, not Ш, fills the allowance |

Comparison point: ASK − MAIN ≈ U·Gm, U = |TT|·m·b·δ/2 ≈ x^{2.5−O(ε)}·b (NODE-CHBALANCE). So an error of x^{3+O(ε)}·b costs
x^{1/2+O(ε)} in Gm. That is admissible and is the √x balance (x/m + m).

**Coefficient in powers of x.**
- The per-dimension congruence cost enters with coefficient 1/D (BoundsMu divides by D) and is summed over m lifts.
- With Ш ≤ √b the Ш part is far inside the budget. The true constraint is Σ log l·len Ш ≲ x^{O(ε)}·B0 ≈ x^{2.5}·b.
- The Lean uses only Σ ≤ b (`divinN_at`, hypothesis hb).

## 4. Is the dependence real? (task d)

- **What fails without VWin.**
  - LinkN remains true, since it carries Ш additively. DIVinN fails, then InEta, so E2_j grows by Σ_l log l·len Ш.
  - The DIV error (7) then grows by about m·x^{O(ε)}·Σ log l·len Ш, and the conclusion (12) becomes
    ASK ≤ Main + budget + m·VV.
  - If VV ≫ x^{2.5+O(ε)}·b, Gm ≤ x^{1/2+O(ε)} no longer follows.
  - No other line of the chain uses VV. The only consumer is `divinN_of_hypV` (grep: DIVinN appears only in `GTI`, `InpAtOf`,
    `IndefiniteRealisationChoice`/`ClassOfRecordOfChoice` (as `pkg`/`hh` hypotheses), `SumLeEtaSumNum`).
- **Could it be avoided?**
  1. **Untwisted gluing (μ = μ0 everywhere).** This would make A_j = 0, so η would vanish. But then the twisted-period integrality at
     the served primes would be gone. *(inferred)* That integrality is the divisibility the gain needs. The Lean offers no untwisted
     alternative.
  2. **A weaker Selmer bound.** Anything ≤ b suffices. `LinkV_at` (`GTI:16-23`, unused) has the quasi-polynomial
     Vbound = C·exp(C·log²(n·t·cond E)) ≈ exp(O(Y^{2ε/5}·polylog)). That is also < √b. It is still a nontrivial Selmer bound.
  3. **A crude bound.** This fails. Soulé/LemmaK gives exp((2kn)^C log disc) (NODE-ONECHARU §2a.4).
- **Verdict.** Some bound of order ≤ b on Σ_l log l·len Ш(E, −e) for e < t ≈ x^{398.5} is genuinely needed on the route as built. The
  slack is enormous: about √b times x^{2.5}. Exponential-in-x^{ε}-scale bounds suffice; polynomial ones are not needed.

## 5. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `CutCoreUnit.main` | `IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44` | vcc(π) ≤ sPi + Σ_e len Ш(−e) + v_l(h_E) + t·Σ_Q len O/(ζ_q−1) | congruence ⇒ classes | standard direction (Ribet; Bellaïche–Chenevier GMA); sub-lemmas named, bodies not opened |
| 2 | `GalC.final_alt_alt` (supplier of LinkN, via EtaBound/LocalCongruenceBound) | `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:47` (NODE-THETA) | per-lift η_j ≤ D0·(C f m b L² + log²x·Nc + Σ vvTerm) | where the f·m·b-sized congruence terms come from | **core, unread**: in particular, why the non-Ш terms are ≈ f·m·b and not larger |
| 3 | `BoundsMu`/`slope_bounds` | `SO:17`; `BaseLevelBoundsWithCovolume.lean:7` | μ(R^∨) ≤ meanLog κ + Σ lcv(M_j)/D + 2ΣF + LG + Σ(E1+E2) + E3 for a lattice glued from type-part projections | consumer (WRITEUP 7A) | core; statement read, proof not |
| 4 | `jw_le` ← `local_bounds_from_exponent` | `LiftLatLemmas.lean:663` | dual-index of the projected lattice ≤ congruence module + d·(J + v(DG) + v(s)) | turns η into a covolume cost | standard (*inferred*: disc(Pr L) vs disc(L∩Z) = congruence module); body not read |
| 5 | `EtaBound`, `CongruenceSingleEndomorphism` | `CongruenceSingleEndomorphism.lean:87,95` | congruence module ≤ Σ_π mult·len O/(a_π) for a Hecke-commuting α killing the complement | module ⇐ ideals | standard |
| 6 | `twisted_place_eta_sum_le_extended`, `inEta_num`, `divinN_of_hypV`, `errB_of_units`, `RecNums.divIneq` | `TPE:62`; `SumLeEtaSumNum.lean:60`; `DivinNOfHypV.lean:117`; `DHB:846,131` | bookkeeping | glue | glue (read) |
| 7 | the twisted-tuple choice (`hmt` iff; `TwistedPeriodAdmissible`) | `ExtraFinal.lean:25`; `AdmissibleAtGeneratorPlaces.lean:14` | twisted ⇔ resChar ≤ X″ or ∈ {d, g0, g1}; twisted periods integral | why twisting is needed at all | core, *inferred* role; not traced |

## 6. Oddities

1. **Ш is not what fills the allowance.** VWin's √b is negligible next to the C·f·m·b·L² congruence term in LinkN.
   - The load-bearing quantity is the non-Ш part of the congruence bound, which is ≈ f·m·b. That part is the polynomial term of
     LocalCongruenceBound times weights, plus sPi.
   - Why it is ≈ b and not, say, the weight a = x·b or (r+t)·b is decided in child 2, which I did not open.
   - The question "why exactly f·m·b" is where a mis-sized local Selmer term (sPi, the Bloch–Kato term of the r-dimensional ρ
     at l < weight) would show.
2. **sPi is uncontrolled in this node.** The ρ-block term sPi(ρ_π) is the local-at-l Selmer of a large-weight representation, with
   l possibly far below the weight. It is bounded somewhere inside child 2, not by VWin.
3. **Twisted places are almost all relevant places.** Every residue characteristic ≤ X″ ≈ x^{3+8ε}e^{x^{ε/3}} counts. "Twisted" does
   not mean "few exceptional places". The congruence cost is paid at every served prime, every lift, every dimension, and is
   still within budget.
4. **The F gain cancels exactly (Fo), but η does not.** At the Lean's level twisting has net cost +η and net gain 0. So it must be
   qualitatively necessary, presumably for integrality (4). That role is *(inferred)*; I did not find a statement saying the
   untwisted structure fails.
5. **Factor D0 on Ш.** Ш is charged once per eigen-system (Σ mult ≤ D0) and per lift. This is natural (each eigen-system can be
   congruent through the same class), not a double count.
6. **VWin weight vs Lean weight.** VVle sums over *all* primes l. The Lean consumes only odd-l finiteness (ShaFinOdd in LinkN)
   but the full sum including l = 2. This is consistent.

## 7. Coverage

Read:
- PROTOCOL; SUMMARY; NODE-ONECHARU; NODE-WRITEUP; NODE-VWIN (all); NODE-THETA:36-75, 128-190; NODE-HOSTS, NODE-FAMILY,
  NODE-CHBALANCE (grep); NODE-ACCOUNT:15-80.
- `GTI:1-100`; `CharacterBoxes/DivinNOfHypV.lean` (all).
- `LL/LiftLat.lean:100-175, 240-256`; `RL:1-260`; `LL/LinkDefN.lean:1-60, 100-175`; `LL/LinkDef.lean:80-110`; `TPE:1-320`;
  `LL/SumLeEtaSumNum.lean:28-90`; `LL/InpAtOf.lean` (all); `LL/LiftLatLemmas.lean:640-700`.
- `DHB:120-165, 760-880`; `LL/EigenvalueSumLeClosedOf.lean:1840-1870`; `SO:1-80`.
- `QuotientMetricDivisors/ClassSumDualLe.lean:10-30`; `QuotientMetricDivisors/Statement.lean:78-95`;
  `HermitianLattices/StatementLat.lean:88-100`; `Columns/AlgebraMapMemMaximalIdealPowIff.lean:85-100`;
  `GoodPartHermitianSpec.lean:55-75, 110-130`.
- `DN:100-240`; `RhoDetPrimeEqMuTildeMulChiPow.lean:265-300`; `DR:40-135, 190-240`; `DP2:85-240`; `DataArith.lean:198-206`;
  `DataForced.lean:100-140`.
- `InertJacobiLevels/AsmTie.lean:25-45`; `InertJacobiLevels/ExtraFinal.lean:15-30`.
- `IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:1-125`; `LevelLetterCocycles/LocalCongruenceBound.lean`;
  `TPS/StepsNoCut.lean:1-40`; `CongruenceSingleEndomorphism.lean:80-135`; `QuotientHomNonvanishingBound.lean:278-290`.
- `AdmissibleAtGeneratorPlaces.lean:11-25`; `WeightDegreeSizes.lean:1465-1500`; `AbsolutelyIrreducibleSpan.lean:705-730`.

Not opened:
- the proofs of `slope_bounds`, `local_bounds_from_exponent` and `GalC.final_alt_alt` (the LinkN supplier);
- the sub-lemmas of `main` (`length_cyclotomic_block_cocycles_le_sha`, `UnramHom.length_le_classNumber`, `Cut.Peel.main`);
- `sPi`'s bound, and the definition of `ccAt` beyond `ccOff_univ`;
- the source-side role of twisted tuples in integrality (4).
