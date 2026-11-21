# NODE-CHAININD: the induction over the m theta lifts (`main_ind`)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `MV/` = `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/`
- `DG` = `Formalism/SharpRestriction/GrowthBounds/DataG.lean`, `DGC` = `.../GrowthBounds/DataGChain.lean`
- `GG/` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/`
- `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`

## 0. Verdict (short)

1. **The iteration re-normalises and re-applies.** The induction hypothesis of `main_ind` is: after m′ steps, the
   image is ϖ^{(gains so far)}·G′ with **G′ an arbitrary element of the level-m′ integral lattice Int_{m′}**. The
   next step is then bounded by a single-step lemma (`ZL_bound`) that holds for *every* G′ ∈ Int_{m′}. Nothing about
   G′ lying in the image of the chain is used. Source and target lattices at each level are the same Lean object
   `X.Int j`, built by the same recipe at every level (Weyl-module-valued Γ-equivariant functions). So the composite
   bound is formally the sum of single-step bounds. In the Hecke-free case it is literally the composition of
   `Conclusion2`: Kz_j(Int_j) ⊆ p^{Σ_v gA_{j+1} − dG_j}·Int_{j+1}.
2. **The derivative order is not split along the chain.** Every gain formula (gB, gA) uses
   al_s = λ_{s,1} − λ_{s,2}. This is computed from the **level-0** weight lam0 and does not depend on j (`FGS:33-35`).
   At every level the weight keeps the same top gap a_s, and the level-j kernel is differentiated by an operator of
   order a_s in a single column direction. So
   Σ_j gain_j = Σ_{j=1}^m Σ_v max(gB_j − Pr_j, gA_j) − Σ_{j<m} dG_j ≈ m·Σ_{s∈TT} Σ_{e odd}(a_s/p^e − w_j)₊.
   That is m times the one-step gain, not γ_p·a once.
3. **The Hecke operators are not needed to iterate.** The Hecke-free iteration already gives m·gA. The Hecke
   commutation is needed to move one level-0 operator T_r up to level j+1 at each step. There it unlocks the larger
   jet bound gB, which includes the even-position tops and the dSet-excluded e. The price is p^{−Pr} per step.
4. **No intermediate integrality is assumed.** It is carried by the induction. The only inputs are the 13 clauses of
   `admitted` (for every level j < m) and `adm8` (T_r preserves Int_0). They enter through `SiteAdm` (`GG/IsPlaceCofactorValuationLowerBound.lean:10-14`).
5. **Judgement.** As an induction, the argument is honest and elementary. All the weight is in the single-step
   statement at *every* level j ≤ m, in rank up to N(m) ≈ x^{399}: every integral form, not only theta images, is
   mapped into p^{≈ Σ(a/p^e − w)₊}·Int_{j+1}. This is E-TWU-1 for one lift, then multiplied by m ≈ √x, and that m is
   the source of the exponent 1/2. A normalisation error in one step would be multiplied by m, and nothing in the
   iteration would catch it.

## 1. Statement

### 1.1 The objects (the Lean says)

**Levels and weights.**
- For j = 0..m, Fm_j = functions (component c, lattice tuple L) ↦ weight space Xsp of `Fl.Pj j` (`DGC:70`).
- Int_j = Π_c (lev j c).M (`DGC:72`). Here M = `funMod HtupW` (`DG:131-141`): the Γ-equivariant (character χ)
  functions L ↦ HtupW(L), vanishing off lattice tuples.
- HtupW is a tensor product of `Dl0` = `deltaLTw` lattices (`DG:22-31`), i.e. the **Weyl-module (Δ)** integral form
  of the weight representation.
- The other lattice, Mna = funMod Htup, uses the **dual-Weyl (∇)** form `nablaLTw` (`UnramifiedQuadraticSetting.lean:70-79`).
  `Sandwich e` (`DG:183-184`): p^e·Mna ⊆ M ⊆ Mna.
- **The recipe is the same at every level.** Only the rank and the weight change.

**Weight at level j** (`liftWt`, `DGC:24-25`; `Pj`, `DGC:44-47`).
- Rank: N(j) = m₀ + 1 + j(t+1) (in FGS, `NN k1 t j`, `FGS:27`).
- Weight at position s: (λ_{s,0}, …, λ_{s,m₀}, −w_1(s)^{×(t+1)}, …, −w_j(s)^{×(t+1)}).
- At a top s ∈ TT, `IsBaseWeight` (`UnramifiedQuadraticSetting.lean:59-63`) gives λ_{s,0} = a_s, λ_{s,last} = −b_s, and
  |λ_{s,i}| ≤ c in between.
- So **every level carries (a_s, small, …, small, −b_s, −w_1, …, −w_j)**, the same a_s at every j.
- FGS works with the det^{w_j} twist ν_j = liftWt + w_j (`FGS:29-32`). The gap ν_j(s,1) − ν_j(s,2) = λ_{s,1} − λ_{s,2} = al_s
  is unchanged.

**Chain.** Kz_j : Fm_j → Fm_{j+1} is K_f-linear, and chainK_m = Kz_{m−1}∘…∘Kz_0 (`DGC:78-87`).

**Valuation.** vGe(j, F, g) :⇔ F ∈ ϖ^{⌈g·eO⌉}·Int_j, with p ~ ϖ^{eO} (`FGS:301-303`).

**Hecke operators.**
- yv_v at level 0: p^{ArV}·Σ over neighbours at distance r (`DG:146-149`).
- Tt v i j = p^{Nprime(j,i)}·T_i at level j (`FGS:313-314`).
- Zop_v at level j = Σ_l (−1)^l cl_l·Ttu(r−l) (`FGS:331-332`). The cl_l are complete symmetric functions h_l of the
  j(t+1) "new" Satake parameters m_l·p^{(n′/2)(t−2x)} (`FGS:320-326`).

**Numbers** (`FGS:33-81`).
- gB_j = γ_p Σ_{TT} al − Σ_{odd s∈TT} Σ_{e odd} min(al_s/p^e, cap_j(s+e)) − de_j
- gA_j = Σ_{TT} Σ_{e odd, e∉dSet(s)} (al_s/p^e − cap_j(s+e))₊ − de_j
- cap_j(z) = ν_j(z,2) if z ∈ TT, else ν_j(z,1). This is the "w" at the partner place, and it is non-decreasing in j by `w_mono`.
- Pr_j = Σ_{odd s}(r·w_j(s) + Σ_{lowest r} λ_s) + n′·r·j(t+1)/2
- de_j = Σ_s(N(j)·lgp(al) + N(j−1)N(j)·lgp(lsz)) + Σ_{TT} lgp(al)²

### 1.2 `main_ind` (`MV/YEPEComm.lean:131-185`)

Hypotheses:
- FormB, EntCondition (§1.3);
- Conclusion4's pieces:
  - hu: u_l are units;
  - hc0: v(cl_l) ≥ 0;
  - hcr: v(cl_r) ≥ alEven;
  - **hCi (commutation)**: for all F ∈ FQ_0 = K_f·Int_0,
      Zop_v^{(j+1)}(chainK_{j+1} F) = p^{PrZ_{j+1}}·chainK_{j+1}(yv_v F);
- hy: yv_v(Int_0) ⊆ Int_0;
- a duplicate-free list Lv of places, budgets Gn, G0n, and a choice function Q;
- h1: Gn_{v,j+1} ≤ gB_{v,j+1} on Lv;
- h2: LowAt(j, v, G0n_{v,j+1}) for every v.

Claim (`:153-154`). For all m′ ≤ m and all F1 ∈ Int_0:

  chainK_{m′}((∏_{v∈Lv} yv_v)^{m′}·F1) ∈ ϖ^{⌈Σ_{j<m′} bbJ_j·eO⌉}·Int_{m′},

where
  bbJ_j = Σ_{v∈B_j} Gn_{v,j+1} + Σ_{v∉B_j} G0n_{v,j+1} − dG_j − Σ_{v∈B_j} PrZ_{v,j+1},
with B_j = {v ∈ Lv : Q(j, v)} (`bbJ`, `:127-129`).

**Induction hypothesis**, stated exactly:
- *for every* F1 ∈ Int_0, the image after m′ steps of (Hecke)^{m′}F1 is ϖ^{(Σ_{j<m′} bbJ_j)}·G′ with G′ ∈ Int_{m′}.
- Nothing more is assumed about G′.

### 1.3 The single-step lemmas it consumes

- **`ZL_bound`** (`MV/AofUpdate.lean:172-211`). Let j < m, vs a duplicate-free list, gP ≤ gB on vs and LowAt(j, v, gP_v) off vs.
  Then for **every G ∈ Int_j**:
    (∏_{v∈vs} Zop_v^{(j+1)})(Kz_j G) ∈ ϖ^{Σ_v gP_v − dG_j}·Int_{j+1}.
  - Proof: ∏Zop(Kz_j G) lies in the O-span of the generators a·TtL(i0)(Kz_j G′) with v(a) ≥ Aof (`ZL_mem`, `Gen`, `:51-53`).
  - Each generator is bounded by `form_of_place`, i.e. FormB with EntCondition at the budget gP − [i0=0]·alEven.
    The missing alEven is supplied by v(a) ≥ alEven, which comes from cl_r.
- **`FormB`** (`MV/PlaceB.lean:22-25`). EntB(j, i0, g) ⇒ ∀ G ∈ Int_j: TtL_{i0}(Kz_j G) ∈ ϖ^{g − dG_j}·Int_{j+1}.
  - EntB (`:14-17`) is a statement about the **kernel alone**: every coefficient of applyD(PI_j(I, i0), ThZA(ThA_j(La, La′))) has valuation ≥ g.
  - FormB is proved from ExpansionEquality/Decomposition + adm7 + the stabiliser bound dG_spec (`formB`, LOCALDIV §3.2 D).
- **`EntCondition`** (`MV/RamifiedLatticeOfChainEstimates.lean:15-17`). For any per-place budgets satisfying
  PlaceB (`PlaceB.lean:27-28`), EntB holds with their sum. It is proved by `restEnt_of` from the Dwork/LT jet bounds.
- **`Conclusion2`** (`FGS:633-634`; proved as `slopeEstimate_of_lemmaB_slopeLine`). The Hecke-free step:
  ∀ G ∈ Int_j, Kz_j G ∈ ϖ^{Σ_v gA_{v,j+1} − dG_j}·Int_{j+1}.

### 1.4 The other named statements

- **`LowTermBound`** (`FGS:705-713`). Let Gn ≤ gB on VV, LowAt(G0n) everywhere, PRn ≥ Pr on VV, and
  S_v ≥ Σ_j(Gn − PRn − G0n)₊. Then for every F in
    Iprod(S, VV) = span_O{(∏_{BB} yv^m)(ϖ^{Σ_{VV∖BB}⌈S_v eO⌉}·F0) : BB ⊆ VV, F0 ∈ Int_0}:
    chainK_m F ∈ ϖ^{Σ_{j=1}^m [Σ_{VV} max(Gn − PRn, G0n) + Σ_{∉VV} G0n] − Σ_{j<m} dG_j}·Int_m.
  - It is proved by `lift_bound_of_integrality` (`MV/LiftBoundOfIntegrality.lean:103-174`): `main_ind` with Lv = BB,
    F1 = F0, and Q(j, v) := [G0n ≤ Gn − PRn].
  - `basic₂` (`:22-87`) shows the explicit ϖ^{S_v} pays max(…) − G0n at the places VV∖BB, where no Hecke operator is present.
- **`ExpansionEquality`** (`FGS:566-571`). There is a unit cK with
  Kz_j F(c′, L′) = Σ_{La∈Rep_j} (cK/|Stab La|)·ker_j(La, (c′, L′))(F(La)) for all F ∈ FQ_j.
  The last step uses `ExpansionDecomposition` (`:573-588`): the same identity with class weights wt (v_p(wt) ≤ dG_j)
  plus Hecke equivariance of the edge sums.
- **`adm5`** (`FGS:590-595`). ThF_j(La, La′) = u^{len}·u′^{len′}·p^{−(n′/2)·volE}·Xi(aw)(1[x·L ⊂ L′]), with u, u′ units.
  The kernel is the Schrödinger-model lattice indicator.
- **`adm6`** (`FGS:603-611`). Mass-weighted up/down edge-sum adjointness. It is proved generically.
- **`adm7`** (`FGS:613-622`). If every PI_j(I, i0)-jet of f has valuation ≥ g, then for G ∈ HtupW(La) (level j),
  ∏_v p^{Nprime(j+1, i0_v)}·kerF(linSub f)(G) lies in the level-(j+1) lattice HtupW(L′) scaled by g.
  This is the jet-to-lattice transfer, from the level-j integral structure to the level-(j+1) one.
- **`heckeCondition_of_adm`** (`MV/HeckeConditionOfAdm.lean:75`). admitted + `countLoc` + `restTmFQ` ⇒ `RestHecke`
  (`MV/HeckeValueEstimateOfRecordValue.lean:277-282`):
    ecal_i^{(j+1)}(Kz_j F) = u_{j+1}^i·Kz_j(Σ_l e_l(m_{j+1}q_x)_{x≤t}·ecal_{i−l}^{(j)}F).
  - This is the Eichler/Rallis relation: one lift adds t+1 Satake parameters.
  - `alternate_expansion_of_relations` and `theorem_of_alternate_form` invert it (h_l against e_l) and iterate it
    down the chain to get Conclusion4's hCi, together with v(cl_r) ≥ alEven and the Zop bound
    (`MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:83-96`).
- **`UAt`** (`WJS:161-170`, family form). For VV′ ⊆ VVs ⊆ reps and F ∈ M:
  chain(yProd(VV′)F) ≥ Σ_j[Σ_{VV′} max(gU − Pr, g0⁺) + Σ_{rest} g0⁺] + low.
  - With VV′ = ∅ it is the iterated `Conclusion2`, transported to the family's numbers. It needs
    `SmallResidueCharComparison` (`FGS:741-754`: gU ≤ gB, g0 ≤ gA, Pr_FGS ≤ Pr_fam).

### 1.5 Answer to (a): what is claimed about K_j∘…∘K_1(F)

For F ∈ Int_0 (no Hecke operator), for each j ≤ m:

  chainK_j(F) ∈ p^{Σ_{l=1}^{j}(Σ_v gA_{v,l} − dG_{l−1})}·Int_j.

With Hecke operators: chainK_j((∏_{Lv} T_r)^j F) ∈ p^{Σ_{l≤j} bbJ_{l−1}}·Int_j.
- The places in B_l receive gB_l − Pr_l at step l; the others receive gA_l.
- Int_j is the honest level-j Weyl-lattice-valued form space. By NODE-GLOBALCHAIN `latS`/`intS` it equals the
  completion of the global lattice (fm u).lat j.

## 2. Argument

**Step m′ → m′+1** (`YEPEComm.lean:162-185`).
1. Split Lv = B ⊔ C, with B = {Q(m′, ·)}. Because the yv commute (`PE_comm`),
   (∏_{Lv} yv)^{m′+1} = (∏_B yv)·(∏_{Lv} yv)^{m′}·(∏_C yv).
2. Put W := (∏_{Lv} yv)^{m′}·(∏_C yv)F1. Since yv(Int_0) ⊆ Int_0 (adm8), ∏_C yv F1 ∈ Int_0.
   - **The C-places' Hecke operator at this step is simply absorbed into the input.** It gains nothing: it is only an integral endomorphism.
3. Commutation (`ZL_chain`, `:111-123`, iterating hCi over B):
   chainK_{m′+1}((∏_B yv)W) = p^{−Σ_B PrZ_{m′+1}}·(∏_B Zop^{(m′+1)})(chainK_{m′+1} W).
   - **So the B-places' level-0 Hecke operator has been carried up through all m′+1 lifts to level m′+1.**
4. IH applied to ∏_C yv F1 ∈ Int_0: chainK_{m′}W = ϖ^{prev}·G′ with G′ ∈ Int_{m′}. Hence
   chainK_{m′+1}W = ϖ^{prev}·Kz_{m′}G′.
5. `ZL_bound` at level m′ for this arbitrary G′ ∈ Int_{m′}, with gP = Gn on B and G0n off B:
   (∏_B Zop)(Kz_{m′}G′) ∈ ϖ^{Σ_B Gn + Σ_{∉B} G0n − dG_{m′}}·Int_{m′+1}.
6. Multiply out: prev + bbJ_{m′}. ∎

**(b) Re-normalise and re-apply? Yes.**
- Step 4 is exactly "divide by ϖ^{prev} and land in Int_{m′}".
- Step 5 is a fresh single-step bound, valid on the whole of Int_{m′}.
- The fresh gain comes from the **level-m′ kernel's** jets (EntB at j = m′), not from the earlier steps.

**Where the fresh a-type divisibility comes from at step j** (the Lean says, plus *I infer* where marked).
- EntB at level j concerns applyD(PI_j(I, i0), Θ_j), where
  PI_j = ∏_{v,s} ∏_{c < ν_{j+1}(s,1)} p^{colExp}·det(column-c minor of height colHt_{j+1}(s,c)) (`FGS:396-412`).
- The columns c ≥ ν_{j+1}(s,2) have height 1. There are ν_{j+1}(s,1) − ν_{j+1}(s,2) = al_s of them.
  So PI_j contains a degree-al_s product of linear forms in one row direction, i.e. ∂^{a_s} in one vector variable.
- applyD multiplies the coefficient by ∏ n_x! (`FGS:255-258`). Through the Dwork factorisation this is the
  v_p(a!) − a/(p²−1) − #(Gaussian factors) mechanism of NODE-LOCALDIV.
- So **each lift K_j is a derivative pairing of order ≈ a_s against its own kernel Θ_j** (the level-j → level-(j+1)
  theta kernel, adm2/adm5). The weight of the form does not decrease along the chain; it only gains the blocks −w_l.
- *I infer*: the input form's own a does not need to "survive". What recurs is the target weight's top gap, which is
  fixed by construction (`liftWt`). The divisibility is a property of the kernel, uniformly over all integral inputs.

**Σ_j gain_j as a formula.**
- Hecke-free: Σ_{j=1}^m [Σ_s Σ_{e odd, ∉dSet}(a_s/p^e − cap_j(s+e))₊ − de_j] − Σ_{j<m} dG_j.
- Hecke-assisted at served v: replace that place's term by max(gB_j − Pr_j, gA_j).
- On the family, cap_j ≈ fill_j, which is constant in j up to O(η + kaJ) (PAIRING §1). So
  **total ≈ m·Σ_s Σ_{e odd}(a_s/p^e − w)₊**.
- This is consistent with ACCOUNT's m·|TT|·a scale and with NODE-HEIGHT's "m copies of ph(a_t) − a_t·logΩ".
  Each lift is an order-a derivative on both sides. (*I infer* the consistency; HEIGHT was not reread here.)

**(c) Why the Hecke commutation.**
- Iteration does not need it: Conclusion2 composes to m·gA.
- The Hecke operator is needed because the stronger jet bound gB, which gives full γ_p·al at even-position (V) tops
  and covers the dSet-excluded distances, holds only for TtL_{i0}(Kz_j G) with i0 ≥ 1: the B-branch of PlaceB, where
  PI_j carries p^{colExp}.
- A level-(j+1) Hecke operator applied after Kz_j is not available on the level-0 input. Conclusion4 hCi converts one
  level-0 T_r into Zop^{(j+1)} = Σ(−1)^l cl_l·T_{r−l}, at the price p^{PrZ}.
- The l = r term is the identity (T_0 = id) with coefficient cl_r. Its plain jets reach only gB − alEven (`ea_A2U`),
  and v(cl_r) ≥ alEven pays the rest.
- *What goes wrong without it:* nothing, for the iteration. Without it the V-top surplus is lost. PAIRING and
  REVIEW-TWU show that this surplus is exactly what pays the colength τ of the Hecke image NP. The net delivered per
  prime is ASK either way.

**dG.**
- dG_j ≥ v_p(|Stab|) for every level-j lattice tuple (`FGS:281-282`). SiteAdm forces dG_0 = 0 and dG_j ≤ v_p(DGam).
- DGam = lcm |Aut| over unimodular hermitian lattices of ranks ≤ N(m) (`Formalism/LocalToGlobal/Columns/DGamAut.lean:126-129,165`).
  It divides minkM(2f·N(m)), Minkowski's bound ∏_p p^{Σ_i⌊N/(p^i(p−1))⌋} (`:185-188`;
  `…/CuspSpanNormBounds/CongruenceAtSplitFrobeniusHolds.lean:820-821`).
- So dG_j ≤ 2fN(m)/(p−1)·(1 + O(1/p)), and dG_j = 0 for p > 2fN(m)+1.
- **It is charged honestly, once per lift:** `Eval` (`Formalism/LocalRingCardinality/DataErr.lean:159-169`), the
  per-lift per-place error E_{j,w}, begins with v_p(DGam). lowS adds one more vDG (`WJS:73-74`).
- Sizes (ACCOUNT): f ≈ 2x^{2+8ε}, N(m) ≈ x^{399}. Per lift and per inert p, dG ≈ x^{401}/p against gain ≈
  |TT|·a/p ≈ x^{3+8ε}·e^{x^ε}/p. Summed: m·log DGam ≲ m·2fN(m)·log(fN(m)) ≈ x^{402} against a budget x^{3+O(ε)}·e^{x^ε}.
- **Confirmed: this closes only because a ∝ b = e^{x^ε} is exponential in a power of x.**
- The same holds for the log-loss de_j, which contains N(j−1)N(j)·lgp ≈ x^{798}·log a per position per lift
  (`FGS:47-50`; mirrored in `EatI`, `DataErr.lean:147-155`).

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `Conclusion2` / `FormB` / `EntCondition` (single step, every level j) | `FGS:633`; `MV/PlaceB.lean:22`; `MV/RamifiedLatticeOfChainEstimates.lean:15` | for all G ∈ Int_j, Kz_j G ∈ p^{Σ gA − dG}·Int_{j+1}; kernel jet bounds | **core** (E-TWU-1 at each level) |
| 2 | `ExpansionEquality` / `ExpansionDecomposition` for the family's chain (via `AdmAtEnt2`, `TiesAt`) | `FGS:566-588` | Kz_j = unit·Σ Stab⁻¹·theta-kernel pairing | **core** |
| 3 | `adm7` (`pending_tuple_admissible`) | `FGS:613` | jets ≥ g ⇒ image in g-scaled level-(j+1) Weyl lattice | core (proved; LOCALDIV) |
| 4 | `heckeCondition_of_adm` → `theorem_of_alternate_form` | `MV/HeckeConditionOfAdm.lean:75`; `MV/TheoremOfAlternateForm.lean:561` | Eichler/Rallis commutation, inverted to Zop∘chain = p^{PrZ}·chain∘T_r | standard (Rallis; Kudla–Rallis), proved |
| 5 | `ZL_bound`, `ZL_chain`, `main_ind`, `lift_bound_of_integrality`, `basic₂` | read | — | glue (read in full) |
| 6 | `SmallResidueCharComparison` supplier (`NumCmp`) | `FGS:722-754` | family gU, g0, Pr against gB, gA, Pr_FGS | glue, supplier not traced |
| 7 | `dGamAut_dvd_minkM` | `DGamAut.lean:185` | Minkowski bound for stabilisers | standard (Minkowski) |

## 4. Oddities

1. **The single step is a worst-case statement over the whole lattice at every level.** ZL_bound/Conclusion2 are
   used for arbitrary G′ ∈ Int_j, up to rank N(m) ≈ x^{399}. The iteration therefore needs the single-step
   divisibility on *all* integral forms, not only on theta images. If E-TWU-1 holds at m = 1 uniformly in rank and
   level, the composite is formal. If it fails by δ per step, the composite fails by mδ.
2. **The lattice convention does not change along the chain.** Int_j is Δ-type (Weyl-module, `deltaLTw`) at every
   level, and the same object `X.Int j` is the target of step j−1 and the source of step j. A Δ-at-source/∇-at-target
   mismatch would manufacture a free factor at each step, and it is excluded by construction. (The Δ/∇ index per
   vector is only O(log_p a) in any case, `Sandwich`.)
   - Cross-check for an expert (*I infer*): Δ and ∇ are dual under the invariant pairing. The adjoint of Kz_j
     therefore maps ∇-lattices, and the Rallis identity Kz_j*Kz_j = λ_j does not trivially force v_p(λ_j) ≥ 2·gain_j.
     Comparing v_p(λ_j) (L6's hook product) with gain_j at one inert p would be an independent test of one step.
3. **Pr_j grows linearly in j**: n′r·j(t+1)/2 ≈ n′·x^{403.5} at j = m. On the B-branch it must be offset by r·w_j
   and must be ≤ the family's Pr (SmallResidueCharComparison). PAIRING says the off returned by Pr's first sum
   matches exactly. The supplier of the FGS-to-family comparison is still untraced.
4. **`hCi` is quantified over FQ_0 (rational span), not over Int_0.** That is correct for an identity of linear maps.
   The integrality burden then sits entirely in ZL_bound.
5. **eO = 0.** If p were a unit in O, vsc ≡ 1 and every bound would be vacuous. `stmt_proved` has a separate branch
   for this (`low_term_bound_of_eO_eq_zero_of_aux0`, `MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:91-92`). I did
   not check that the live O = completion at w has eO ≥ 1, though `eO_spec` and inertness make it expected.
6. **The C-places' Hecke operators** (Q false) are applied and wasted at each step. This is harmless.
7. Size closure in m, dG and de is polynomial (x^{≈800}) against exponential (e^{x^ε}). It is logically fine, but
   asymptotic only.

## 5. Coverage

Read:
- `MV/YEPEComm.lean` (all); `MV/LiftBoundOfIntegrality.lean` (all); `MV/AofUpdate.lean:1-60,160-211`;
  `MV/PlaceB.lean` (all); `MV/RamifiedLatticeOfChainEstimates.lean:1-60`;
  `MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:75-113`; `MV/HeckeConditionOfAdm.lean:60-100`;
  `MV/HeckeValueEstimateOfRecordValue.lean:277-290`;
- `FGS:1-110, 255-800`; `DGC` (all); `DG:22-31, 79-200`; `UnramifiedQuadraticSetting.lean:59-86`;
- `GG/ModelsOK.lean` (all); `GG/IsPlaceCofactorValuationLowerBound.lean:1-30`;
  `GG/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:130-145`;
- `WJS:19-31, 60-125, 156-170`; `DGamAut.lean:124-192`; minkM definition; `DataErr.lean:140-200`.
- Context nodes as listed in the brief, plus ACCOUNT §sizes.

Not opened: bodies of `formB`, `form_of_place`, `ZL_mem`/`Zop_gen`, `restEnt_of`, `slopeEstimate_of_lemmaB_slopeLine`,
`theorem_of_alternate_form`, `countLoc`; the `NumCmp` supplier; `deltaLTw`/`nablaLTw` definitions; NODE-HEIGHT.
