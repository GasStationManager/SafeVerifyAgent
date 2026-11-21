# NODE-TWSET: the twisted-place set Tw and the index of θ_jT_j in M_j off Tw (hole H3)

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* means my reading. Nothing was compiled.
Abbreviations (new ones; SO, IS, ONL, JOIN etc. as in NODE-JOIN):
- `CT2` = `Formalism/LocalToGlobal/IndefiniteReal/CutTuples2.lean`
- `EF` = `Formalism/SharpRestriction/InertJacobiLevels/ExtraFinal.lean`; `AT` = `…/InertJacobiLevels/AsmTie.lean`; `TA` = `…/InertJacobiLevels/TiesAsm.lean`
- `LC` = `Formalism/LocalToGlobal/IndefiniteReal/LinksChar.lean`; `CPS` = `Formalism/LocalToGlobal/IndefiniteReal/ConcretePkgSpec.lean`; `RR` = `Formalism/LocalToGlobal/IndefiniteReal/RealRec.lean`
- `RPI` = `TPS/RealPins3Iff.lean`; `RPT` = `TPS/RealPins3RealTOf.lean`; `TTR` = `TPS/TieTwRecOf.lean`; `RHT` = `TPS/RowHTwOfTie.lean`; `RTL` = `TPS/RealTwLe.lean`; `FLS` = `TPS/FiniteLevelAndSecond.lean`
- `CSC` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConstructionStartingChoicesOfFineAdelicData.lean`
- `CSI` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ComplexSidePlacesIffMemNonzeroIndexPlaces.lean`
- `LDN` = `Formalism/LocalToGlobal/Divisibility/LinkDefN.lean`; `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`
- `HIB` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasIndexBoundOfRuns.lean`; `RHO` = `…/DivisorProofs/RunsHoldOfTies.lean`; `IDO` = `Development/AbelianVarietyTheory/Definitions/Divisors/IsDeltaDelAtOwnAt.lean`
- `WA` = `Formalism/SharpRestriction/Divisibility/WeightAlgebra.lean`; `ETR` = `Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsThresholdRunHolds.lean`; `ECI` = `…/HeightProofs/ExistsConstantsIndexBoundHypothesesLiftWeights.lean`
- `CI4` = `Development/AbelianVarietyTheory/Definitions/HeightFunctions/ConclOfInputs4.lean`
- `GPB` = `Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/`; `MMT` = `Formalism/MirabolicMackeyTheory/StatementT.lean`

## 0. Verdicts

| Question | Verdict |
|---|---|
| Q1: the hypothesis | **There are two, and the one earlier nodes quoted is dead code.** `hmt` (EF:24-25: muAt w ≠ mu0 ⇔ resChar w ≤ X″ ∨ resChar w ∈ {d, g₀, g₁}) is an argument of `recF_more` (EF:23). Neither `recF_more` nor its target structure `RecMore` (AT:22) has a consumer anywhere in the tree. The live hypothesis is `MuDef` (CT2:196-198): twist **exactly** at the places W1 where the *untwisted* layer index, dual index or F is nonzero, and set Tw := W1. |
| Q2: supplier | **There is no unimodularity theorem, and none is needed.** On the live route Tw = W1 is *constructed* (CSC:195-199, `P.Wt = z.W1`; RPT:20-29). "idx = 0 off Tw" is then true by construction. The content moves to the bound **at** every w ∈ Tw (`ON`, IS:318-323). That bound is proved by `on_of_leaves` (ONL:873) for an arbitrary finite Tw, with no residue-characteristic restriction. Its per-place input `LatticeIndexBoundAtPairs` comes from a global remainder r(v) with Σ_v lw(v)·r(v) ≤ rank·f·m·b·de2 over **all** places (HIB:139-141). That remainder is proved in-tree, down to `theorem_zero_of_refined_inputs` (read; its inputs were not opened). |
| Q3: mathematical reason | **None of (i)–(iii) as stated. Large primes, congruence primes included, may divide the untwisted index. They are paid for globally.** A prime p dividing idx(M_j : θ_jT_j) at μ0 joins Tw and is twisted. The twisted index is then bounded by (2F + err + 2/p²)·D, and for p > Y the depth and the err-polynomial vanish (ONL:310-312; MMT:68-71). What remains is the remainder r(w), and its sum over all places is bounded by a height-type ("Heights") inequality (GPB `LiftIndexPowFourLeDegree.lean:405-422`). X″ plays no role in this bound. |
| Q4: bookkeeping | The cost at Tw goes into E1 = CE·x^ε·(B0 + Nc), B0 = f·m·b·L (ONL:184, 357), plus E2 and E3 = Σ lw·2/ℓ². These enter BoundsMu as Σ_j(E1_j + E2_j) + E3 (SO:72-74), and from there DIV's error 60ce·m·x^ε(B0+Nc) (NODE-DIV §1–2). That is the **x^{O(ε)}·m·(B0+Nc)** error term, not x/m, m or k/n². The 2F part cancels against Fo. Places outside Tw contribute exactly 0, by construction. |

## 1. Statement

**MuDef** (CT2:188-198, read). Let W1(w) be: for some layer j, at w or at its conjugate w̄, the *untwisted* signed index Iw_j(μ0, w) = idx_w(M_j, θ_j(μ0)T_j(μ0)) is nonzero, or the dual index jw(T_j(μ0)) is nonzero, or F0(w, j) is nonzero. Then MuDef(tw) says four things:
- tw(w) ≠ μ0 on W1;
- tw is conjugation-invariant on W1;
- μ(w) = tw(w) if W1(w), and μ(w) = μ0 otherwise;
- **w ∈ Tw ⇔ W1(w)**.

**Untwisted** (IS:328-330, read): off Tw, Aw_j(w) = 0 and F0(w, j) = 0. `CPS.untw` (CPS:140-152, read) proves it from `IsTup.tw` (LC:385-386, read: W1 ⊆ twPl) by unfolding Aw and rewriting with the negated W1 clauses. It is pure definition-chasing.

**ON** (IS:318-323, read), for every w ∈ Tw:

  Σ_j (Iw_j(μ(w), w) + Iw_j(μ(w), w̄)) ≤ (Σ_j (2·ramw·F0 + ramw·err0) + ramw·2/p_w²)·D,

with err0 ≥ 0 and Σ_{w∈Tw} lw·ramw·(err0 + J0) ≤ E1_j. This bounds the index of the **twisted** lift, at tuple μ(w).

**The dead `hmt`.** `rg 'recF_more|recF_ex\b|RecMore\b'` finds only EF:23, 27, 35 and AT:22, and `rg '\.mu_0\b'` finds only EF:32 and AT:30. So the iff "twisted ⇔ resChar ≤ X″ or bad", which NODE-CONGMOD §2a and NODE-JOIN §2c attribute to the live record, is not on the route. The live analogue, `TieHyp.htw` (TA:45-46), is only an implication, and it has a third disjunct: twisted ⇒ resChar ≤ X″ ∨ bad ∨ **w ∈ L0.supp**. `tw_supp` (TA:83-84) only places twisted places inside the enlarged support, and that is all `TieTwRec` (LDN:36-37) asks (consumed via TTR:45-48, RHT:22).

## 2. Argument

**(a) How Tw is built on the live route.**
1. `exists_pre2_of_fine_of_resChar_mem` (CSC:195-199, read) takes adelic data z. It assumes W1(z) ⊆ {v : resChar v ∈ T.pl} (`hsub`) and that the twist character T.psi is trivial off W1. It restricts z to W1 (z′, CSC:209-212), and outputs P with **P.Wt = z.W1**.
2. `twisted_places_eq_complex_side_of_eq_nonzero_index` (CSI:115-121, read) turns Wt = W1 into twPl ⇔ W1. `realPins3_realTOf_alt` (RPT:20-29, read) uses it to prove `MuDef` via `realPins3_iff_twPl_iff_W1` (RPI:26-41, read).
3. `RealRec.tw_iff` (RR:125-134, read) gives twPl ⇔ D.muAt ≠ D.mu0. So "muAt ≠ mu0" on the live D means exactly "nonzero untwisted index, dual index or F", not "resChar ≤ X″".
4. The residue-characteristic set T.pl is enlarged to cover W1. In FLS:85-93 (read, statement level), `exists_twisted_cohomology_class_lift_alt` produces B′, f′, T′ with a twisted class at the needed places. *(inferred)* The twist data are constructed after W1 is known. Not opened.

**(b) Why off-Tw costs nothing.** By (a), Tw ⊇ W1, so off Tw the untwisted index, dual index and F vanish by definition. The tuple there is μ0, so these are exactly the quantities in BoundsMu's off-Tw clauses (SO:52-55, 58).

**(c) Why on-Tw costs little, at any residue characteristic.** `on_of_leaves` (ONL:873ff; the proof core is ONL:605-870, read in part) works as follows.
- `local_bound` (ONL:623-636) gives, at w ∈ Tw: idx ≤ ramw·[(e0 + vU0)·dW + (r/ramw + nZ·vU0)/|P:U| + ε0].
- e0 = (E − v(σ))/ramw (ONL:172) is the derivative-content depth. `LeafDepthGood` (ONL:305-312) puts it at ≤ F0 + aE + 1 for p ≤ Y and **= 0 for p > Y**, where Y = C·DF (ONL:188).
- `LeafSizes` (ONL:334-339) only requires 1 < Y ≤ m·b and log Y ≤ 2L.
- errl at a good place is `errGood` (ONL:215-219), which is **0 for p > Y** (MMT:68-71).
- ε0 terms are ≤ 2/p² per place (ONL:288-291).
- So for good p > Y, the per-place cost is only (r(w) + r(w̄))/(|P:U|·D) + 2/p².
- **The r-budget.** `LatticeIndexBoundAtPairs` (ONL:262-270) requires Σ_{v∈S′} lw·r_i(v) ≤ nZ·f·m·b·de2 for **every** finite S′. With nZ/|P:U| ≤ 3D (ONL:640), Σ_{w∈Tw} lw·r/(|P:U|D) ≤ O(f·m·b), absorbed in CE·x^ε·B0 (ONL:851-864, read).

**(d) Where r comes from.** `hasIndexBound_of_runs` (HIB:129-190, read) builds r from `exists_rem_of_tie` (HIB:95-113) and `exists_rem_of_concl` (HIB:51-87, read). These come from `WeightAlgebra.Concl` (WA:424-434, read):
- there is r ≥ 0 with Σ' r(λ)·log N(λ) ≤ β = rk·f·m·b·de2;
- at every place λ and for every K_λ-subspace V′, the length of (M_sup ∩ V′)/(Θ ∩ V′) is ≤ ⌈T·nus(λ)⌉·dim V′ + r(λ), where Θ is the span of explicit theta-type test forms;
- nus is finitely supported (WA:395).

The supplier chain, each step read at statement level:
1. `RunsHold` (IDO:40-48) has Concl as a conjunct.
2. It is supplied by `runsHold_of_ties` (RHO:20-34), from `exists_constants_indexBound_hypotheses_liftWeights` (ECI-Statement:8) = `hyp_concl_at_run` (ECI:13-21), from `runHolds_of_parOK` (ETR:58-71).
3. That uses `inputs4_of_net` (ETR:33-53), whose proof uses `concl_of_inputs4` (CI4:91-99), which is `theorem_zero_of_refined_inputs` (`GPB/TheoremZeroOfRefinedInputs.lean:8-31`, read).
4. There r(λ) = `rLa` (`GPB/PublishedIntClosHolds.lean:371-376`, read). This is a binomial factor times a local intersection length Ila (plus a Net term), plus the Gauss content of M_j at λ, plus the local length of Qm/⟨th_i⟩.
5. Its total is bounded by `sumGC4` (`GPB/LiftIndexPowFourLeDegree.lean:405-422`, statement read) from `Heights` (`PublishedIntClosHolds.lean:378-380`): twice Σ' Ila·log N(λ) is bounded by height-type constants.

*(inferred)* This is the classical mechanism. The local index of a span of explicit small sections inside the integral lattice is bounded by the valuation of a global quantity (intersection numbers / a Gauss content). Summed over all places with weights log N(λ), the product formula turns that into an archimedean height bound. A congruence prime is therefore allowed to divide the index, but it is charged to a fixed global budget.

**(e) Answer to the size question.** X″ = a/w″ = x·n·X′ ≈ x^{3+8ε}·e^{x^{ε/3}} (NODE-ACCOUNT table, DP2:39). It is the support length of the gain/F (the gain at p ≥ X″ vanishes), not a unimodularity threshold. The layer weights are ≈ b = e^{x^ε} ≫ X″, so "p > weight" could not hold at p ≈ X″, and the Lean does not claim it. The only "large p" input is depth e0 = 0 for p > Y, where Y ≤ m·b. That is a statement about the p-content of derivative functionals of bounded order (JOIN §2c: from chart theorems AvFSt/HTFSt/UpFSt; proofs not read). It is not about L-values.

## 3. Children

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `exists_pre2_of_fine_of_resChar_mem` | CSC:195-237 | Given W1(z) ⊆ T.pl-places, build the realisation with Wt = W1 | defines Tw | glue (read); hypothesis `hsub` is discharged by the twisted-class lift (#7) |
| 2 | `twisted_places_eq_…`, `realPins3_realTOf_alt`, `muDef_iff_alt` | CSI:115; RPT:20; RPI:26 | twPl ⇔ W1, hence MuDef | definitional | glue (read) |
| 3 | `on_of_leaves` / `ONwith` proof | ONL:605-880 | ON at every w ∈ Tw, for any finite Tw | the on-Tw bound | core; proof read in part |
| 4 | `LeafDepthGood` ← `leafDepth_all_record` | ONL:305-312; `DivisorProofs/LeafDepthAllRecord.lean` (not opened here) | e0 = 0 for good p > Y; ≤ F0 + aE + 1 below | removes depth at large p | core; statement read, proof per NODE-JOIN |
| 5 | `hasIndexBound_of_runs` → `Concl` | HIB:129; WA:424 | local index ≤ depth·dim + r(λ), Σ r·log Nλ ≤ rk·f·m·b·de2 | **global budget for all primes** | core (read at statement level) |
| 6 | `theorem_zero_of_refined_inputs`, `rLa`, `sumGC4`, `Heights` | GPB/TheoremZeroOfRefinedInputs.lean:8; PublishedIntClosHolds.lean:371; LiftIndexPowFourLeDegree.lean:405 | r(λ) = local intersection and Gauss-content lengths; their weighted sum ≤ height constants | **the real content of H3** | core; top level read, inputs (`Heights`, `PolyDom4`, `localBound`) **not opened** |
| 7 | `exists_twisted_cohomology_class_lift_alt` | used at FLS:88 | twist data at every residue characteristic needed by W1 | makes μ(w) ≠ μ0 possible at every W1 place | core, **not opened** |

## 4. Oddities

1. **The record H3 rests on dead code.** The iff Tw = {resChar ≤ X″} ∪ {d, g₀, g₁} (EF:24-25) has no consumer. On the live route Tw is the nonzero-index set W1. That set is finite, but its residue characteristics are unbounded a priori. MAIN-ARGUMENT §9.4 H3 should be restated (§5).
2. **Twisted-place inputs must hold at arbitrary congruence primes.** Every prime dividing an untwisted layer index lies in Tw. So the twisted-place hypotheses must hold there as well, however large the prime: `mu_on` (LC:400-402: a character ψ_w with `IsPsi` at that place), KillAt/`GoodTw` (Selmer vanishing, residual absolute irreducibility at every twisted l, NODE-KILLAT), `PlacesCondition` (RTL:28-40) and the `LeafDepth*` clauses. NODE-KILLAT oddity 2 phrased this as "every twisted l ≤ X″". On the live route it is every l in W1, with no upper bound. The statements quantify over all twisted indices, so this is no logical gap. The satisfiability burden is larger than recorded.
3. **The signed index is bounded only above** (as NODE-JOIN noted). Denominators of θ_j are not penalised. This favours the covolume and is no soundness risk.
4. `ON` bounds the **twisted** index Iw(μ(w)), but membership in Tw is decided by the **untwisted** index Iw(μ0). Twisting at a congruence prime is therefore asserted to *reduce* the index to the r-budget. *(inferred)* This works because ON's bound comes from the twisted test forms spanning M_j up to depth plus r. Coherent as read.
5. The r-budget β = rk·f·m·b·de2 holds uniformly over every finite set of places (WA:426-427; ONL:268-270). It is a genuine global (product-formula) statement, and its satisfiability rests on `Heights`/`PolyDom4`, which I did not read.

No ESCALATE: no assumed-without-supplier or false-looking statement was found on this path. The open item is to read child 6's inputs.

## 5. Proposed restatement of H3

H3 is not a unimodularity statement. It is the global index bound Concl: there is a remainder r ≥ 0 on all finite places, with Σ_λ r(λ)·log Nλ ≤ rk(M_j)·f·m·b·de2, such that at every place the theta-type test forms span the integral forms M_j up to depth ⌈T·nus(λ)⌉ per dimension plus r(λ). Here nus is finitely supported, and the depth is 0 above Y. It is proved in-tree via `theorem_zero_of_refined_inputs`. The next node should open `Heights`, `PolyDom4` and `localBound` (GPB) to check that the height constants do not secretly carry an a-sized or L-value-sized term.

## 6. Coverage

Read:
- CT2:1-228; EF:1-85; AT:1-51; TA:1-140; IS:290-345; CPS:100-175; LC:330-440; RR:110-135;
- RPI:1-54; TTR:1-54; RPT:1-31 (TPS copy); RHT:1-24; RTL:1-150;
- CSC:185-240; CSI:112-130; FLS:55-110; LDN:25-60; DP2:80-110;
- SO:17-80; ONL:140-370, 605-640, 785-880;
- MMT:60-80; HIB:51-194; IDO:30-70; RHO:1-36; ECI-Statement:1-9; ECI:13-22; ETR:20-73; CI4:91-115;
- `GPB/TheoremZeroOfRefinedInputs.lean:1-33`; `GPB/PublishedIntClosHolds.lean:360-380`; `GPB/LiftIndexPowFourLeDegree.lean:405-424`; WA:395-450;
- earlier nodes CONGMOD, LINKN, VWIN, TWU, SLOPE, ARCH, SEESAW, JOIN, DIV §1-2, ACCOUNT table, MAIN-ARGUMENT §5, §9.4.

Greps run:
- `recF_more|recF_ex\b|RecMore\b`; `\.mu_0\b`; `\bUntwisted\b`; `MuDef`;
- `twPl`; `tie_tw_rec_of_real_rec`; `tw_supp`; `htw`;
- `X'' .*↔ .*muAt` and variants (found only EF:25, `LocPl` iff at `NormalizedHeckeFactors/HeckeStdTwOfStd.lean:147-149`, and the RR/TPS `tw_iff`s);
- `exists_pre2_of_fine_of_resChar_mem`; `constructionStartingChoices_of_fine_adelicData`;
- `WeightAlgebra.Concl`; `hyp_concl_at_run`; `concl_of_inputs4`; `rLa`; `sumGC4`.

Not opened:
- the proofs of `localBound`, `sumGP4`, `Heights`/`PolyDom4` suppliers, `leafDepth_all_record`;
- `exists_twisted_cohomology_class_lift_alt`;
- `restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces`.
