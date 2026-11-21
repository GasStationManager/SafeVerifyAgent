# NODE-TWIST: hypotheses at every twisted l (Q1) and uniformity in the twist ψ_w (Q2)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `IRP` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsRhoPtOfSplitting.lean`
- `BKP` = `Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean`
- `IHF` = `Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean`
- `DN` = `Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean`
- `RIT` = `Formalism/SharpRestriction/LevelLetterCocycles/JointConditionsZpowers/ResidualIrreducibleOfTheorem.lean`
- `RI3` = `Formalism/SharpRestriction/LevelLetterCocycles/ResidualIrreducibleOfTheoremThreePrime.lean`
- `CNT` = `Formalism/CyclotomicNorms/StatementT.lean`, `CNI` = `Formalism/CyclotomicNorms/StatementI.lean`
- `ETC` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTiedChoiceOfReads.lean`
- `NCh` = `Formalism/LocalRingCardinality/DataNChoice.lean`, `NCT` = `Formalism/LocalRingCardinality/DataNChTie.lean`
- `AM/` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/`

"The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.

## 0. Answers in brief

**Q1. Hypotheses at every l: option (ii), in a different form than the one the brief proposed. Closed in the statements I read. Two children are unread.**
- ρ_s is not one fixed representation, and the source does not change with the place either. ρ_s = `D.ntw.rhoS i s`.
  - It is an r-dimensional representation G_E → GL_r(O0_i), one for each twist index i (each has its own prime l_i) and each signature s (a lift layer jS and a side). Field at `DN:337`.
  - `IsTriple` (`TorsionBlocks/LatticeConditions.lean:156-166`) ties it to the automorphic side: the Frobenius charpolys of ρ_s are those of the rank-r cuspidal parameter Sg of the lift's A-parameter, for almost all split w.
  - So ρ_s is the l_i-adic realisation of the GL_r source parameter of the theta lift.
  - It is unramified outside {l, g₀, g₁} (`BKP:351-353`). So its level is supported at the two auxiliary primes g₀, g₁.
- **Residual absolute irreducibility at every l, l = 2 included, comes from prescribed depth-zero local types at the two auxiliary primes g₀, g₁. It is not a big-image theorem.**
  - The tool is a "good tuple" criterion (`CNT:36-62`, proved as `irreducibility_of_good_tuple`). At each place v over g_k, the tame-inertia generator has charpoly equal to the reduction of the roots of a squarefree polynomial f_v over F_{g_k}. Two conditions on degrees are imposed:
    - for each a ≤ r/2, some v where f_v has no factor of degree a;
    - some v where f_v has an irreducible factor of prime degree q, with r/2 < q ≤ r − 3.
  - Under these conditions ρ̄ is absolutely irreducible for every l outside BB(r, g_k).
  - BB(r, g) = {g} ∪ {l : g^d < l^{4·v_l(g^d − 1)} for some d ≤ r} (`CNI:10-12`).
  - The datum requires BB(r, g₀) ∩ BB(r, g₁) = ∅ (`ntypes.BB_disj`). So every prime, including l = 2, 3 and l = g_k, is covered by one of the two g's.
  - This is the classical device of a supercuspidal type at an auxiliary prime forcing irreducibility. It is legitimate.
- The condition is "absolutely irreducible", and it is genuine: `IrredOn` over F̄_l, and `ValuationStabilityAtRing` (the span of ρ̄_s is M_r, by Burnside).
- **Crystallinity at l is required only for l ∉ {g₀, g₁}.** At l = g_k only de Rham plus potentially crystalline is required (`BKP:354-358`). So "crystalline at l | level" is not asserted.
- No `True` is involved, beyond the harmless leading `True ∧` in `SetHyp`. No quantifier is vacuous: `ResidualIrreducibleRankR` ranges over every local index that has HG (Zgood ≠ ∅).
- Still unread:
  - the suppliers of the datum conditions that every Zgood eigensystem has the prescribed g_k-type and that its residual representation realises it (`LabelDegreeHypotheses`, `GlobalDatumResidualRepCondition`, `GlobalDatumDepthZeroCondition`);
  - the supplier of NoJump / SelfDual (`TwistedPairSettingHyps`).

**Q2. Uniformity in the twist: the archimedean objects are ψ-independent by construction. A consistency question remains open.**
- The types are fixed. muTw(w) = muStar, or muStar′ when resChar w = pde (`AM/NontrivialReferenceForms.lean:252`).
  - These form a finite family of Hecke-character tuples fixed in `Cols`.
  - muStar has character ξ = δ, which is ramified above pde only (`AM/TwistedLevelExtension.lean:272-293`).
  - μ(y) varies only between twisted and untwisted, and between pde and the other places. It never varies with l or with ψ.
- In `Stages` (`AM/AssembleLattice.lean:188-197`) the order is B → C (types) → W (`what₂`: MtL, MtLat, etaJ) → V (`DivStage`: RR, Nu, norms), S (`SStage`: the Theorem-S data), G, and N (`NStage`: nd, ntw, nexp).
  - V, S and G do not take N as a parameter.
  - The choice NChoice (Q, k′, ψ′) is not in `Stages` at all.
- Every place where ψ appears in `GoodTw` is l-adic (§2b): PsiOk, IdxAt, partA/AT, partC, partD. IdxAt in particular compares two O′-lattices in the ψ-independent space O′⊗Fm.
- **Open point (possible defect).** The N-stage ties seem to require the forms of the fixed global type part Mt(muTw w_i, j_i) to carry ramification at the auxiliary set Q_i, which is chosen afterwards. The relevant fields:
  - `Mt_i` is defined as MtLat(mu i, j i) ⊗ O_i (`prMt_lat`, `DN:117`);
  - `chi_ram_Q`: χ₁ is ramified at every v ∈ Q_i (`DN:154`);
  - `NChTie.Q_eq`: nd.Q = C.Q (`NCT:19`);
  - `locV_unr` (`DN:635`).
- The rebuild step after the choice guarantees only `SameExport` (ntw/nexp) and `SameField` (`ETC:649-660`). It does not guarantee the same `what₂`/RR.
- So either the global data are rebuilt after ψ, and Q-uniformity must sit in the kit-existence bounds (`RecOK`/`LedOK`, constants in (s, C, cD) only; unread), or I misread the ties.

## 1. Statements

### 1a. What `SignatureChoiceCondition` needs (`IE/PsiAtPsiAt.lean:22-37`, read)
`JointSix.main : Cheb → PtFam → NChTie → TriplesGood → SameTwist → GoodPtRow → ResAbsIrr → SignatureChoiceCondition ρ C`.
- `PtFam` (`IRP:337-345`) is glue. It asks for GoodR at each i, continuity, and that ρ_iπ be the r-block complement of r_iπ for π ∈ Z_i. There is no l-local content.
- `ResAbsIrr` (`IRP:144-146`) says: ∀ a, ∀ π ∈ Zgood a, ∀ ρ with `IsRhoPt`, `AbsIrrSub (redRep ρ) ⊤`.
- `SameTwist` (`IRP:162-163`) says: twOf a = C.twI(w_a), and the datum's l-power character `ntw.psiL a` equals the chosen ψ_w via `SameChar`.
- `TriplesGood`/`GoodPtRow` (`IRP:128-137`): every π ∈ Zgood has a source row σ with an A-parameter Sg, and a good signature s with `IsTriple a s Sg`.

### 1b. Residual irreducibility chain (all read)
1. `ResAbsIrr` ← `residualAbsIrredGoodPoint_of_residualIrred` (`IE/ResidualAbsIrredGoodPointOfResidualIrred.lean:105-128`), from `ResidualIrreducibleRankR`. This is glue: redRep ρ is an `IsRhoBar`.
2. `ResidualIrreducibleRankR D` (`JointConditionsZpowers/ResidualIrreducibleRankR.lean:109-114`) says: ∀ a with HG, ∀ residual rb of the localisation:
   - `IrredOn rb ⊤` over F̄_l;
   - for l ≠ g_k and v | g_k, χ̄₁(γ0_v) is not a root of charpoly(rb(γ0_v)).
3. It is supplied by `residual_irreducible_of_theorem_three_prime D ⟨tieLab, g3⟩ a5 litBNIrr R.c.rho R.c.dz` (`Proofs/SatakeParameters/FullConclusionOfInputs.lean:41-42`, inside `CoreFacts.main`), which goes to `residual_irreducible_of_theorem` (`RIT:85-…`).
   - `hBB := D.ntypes.BB_disj`.
   - `GlobalDatumResidualRepCondition` (`RIT:13-19`): for x ∈ ZgoodN with good parameter Sig, there are ρ of type Sig and a character ξ, unramified at g_k (l ≠ g_k), with r_x-block ≅ ρ⊗ξ.
   - Brauer–Nesbitt transfers irreducibility to rb (`charpoly_eq_of_frob_on_split_places`).
4. `theorem_three_prime_holds` (`RI3:167-215`) applies `irreducibility_of_good_tuple` with k chosen so that l ∉ BB(r, g_k). The tame data come from `LabelDegreeHypotheses` (`AdmissibleThreePrime.lean:17-50`):
   - ρ̄(tg_v) has charpoly ∏(X − ι(primeToPart_l x)) over the roots x of the local-type polynomial `items₂ k v (isoLoc Sig v)`;
   - there is φ with φ·tg·φ⁻¹ ↦ (tg)^{g_k}.
   - `goodSig` (`DN:1281-1287`) is `IsGood r g_k f χ` for both χ and χ⁻¹.
5. `IsGood` (`CNT:19-29`) requires:
   - f_v monic, squarefree, of degree r, with f_v(0) ≠ 0;
   - injectivity on prime-to-l parts for l ∉ BB;
   - no root colliding with χ;
   - the two degree patterns described in §0.
6. `BB` and `Exc` (`CNI:10-12`). `BBCount` gives ≤ 3 primes per d, hence |BB(N, g)| ≤ 3N + 1. `ChoiceCount` (`CNI:24-27`, proved as `choice_count` in `FoundationProofs/DivLeRpowThreeQuarters.lean:221`) bounds the bad g in [Y, 2Y]. On the main route g₁ comes from `exists_modulus_bb_disjoint` (`AM/ExistsPreDataDyadicFrame.lean:72`). There is also a numeric instance for r = 9 (`Foundations/FoundationsPrimeFact.lean:78`).

### 1c. The twisted-index hypotheses on ρ_s (`BKP:327-392`, read)
- `SetHyp i` = True ∧ SelfDual(s) ∧ NoJump(s) for good s ∧ untwisted theta sums ≠ 0 ∧ SOk ∧ 100 ≤ r ∧ 2r ≤ g_k.
- `IsotypicValuationAtRing i s` (adm1) has these parts:
  - ρ_s is unramified at every v ∤ l·g₀g₁;
  - at v | l, ρ_s and Tgl are de Rham, crystalline **if l ∉ {g₀, g₁}**, and potentially crystalline;
  - H⁰ vanishes on every decomposition group, for T and T^∨;
  - a Hodge dimension identity holds at conjugate places.
- `ValuationStabilityAtRing i s` (adm2) has these parts:
  - span(ρ̄_s(G)) = M_r(k), i.e. absolute irreducibility;
  - at v | g_k with g_k ≠ l, wild inertia acts trivially and some inertia σ has det(ρ̄_s(σ) − χ̄_s(σ)) ≠ 0.
- adm2 is obtained by `admissible_at_of_irreducible_tame` (`FoundationProofs/GeneralAdmissibleOfIrreducibilityStmt.lean:254-300`, read): ρ̄_s ≅ η ⊗ `ntypes.rbar σ w` with `IrredOn (rbar σ w)`. This is the same g_k-type mechanism *(inferred: I did not trace `hirr` to the good-tuple theorem)*.

### 1d. The twist and where it lives
- `NChoice D` (`NCh:12-50`) consists of:
  - twI, sd;
  - Q(w), k′(w), and ψ′(w) : RCG(twI w, Q w) → ⟨ζ_{l^{k′}}⟩;
  - Oe, embW;
  - **eMt w j : MtL(muTw w, j) →ₛₗ[embW w] Frac(Oe)⊗MtV(twI w, j, sd, k′, Q, ψ)**, with `eMt_lat`: the image of the global lattice MtLat(muTw w, j) spans the base change of `nexp.MtLat(…, Q, ψ)`.
- `NChTie D C` (`NCT:11-36`) says:
  - twOf a = C.twI(w_a), twSide a = C.sd(w_a);
  - **nd.Q a = C.Q(w_a)**;
  - there is a conjugation-invariant ψ0_w with values in LL, read both as C.psi′ w and as `ntw.psiL a`.
- `GoodTw` (`IHF:219-231`) = PsiOk ∧ (∃ ε_B ≥ 0, Σ ε_B ≤ ε′, IdxAt for each j, b) ∧ (IsLatIn ∧ InclAt) ∧ partAT ∧ partC ∧ partD.
  - **IdxAt** (`IHF:201-211`): for every finite DVR O′ over O_k and every lattice M ⊂ O′⊗Fm(i, j, b), sIdx_l(M, span of the ψ-twisted theta vectors eThPsi) ≤ sIdx_l(M, eTh⊗O′) + e.
  - **partC** (`BKP:315-321`): every twisted theta value thEval(i, Q, λ, k′, ψ^{±}) is nonzero, with −N0 ≤ v_l(thEval) ≤ c0(λ) + ε′, where c0 is the valuation of the untwisted sum.
  - **partD** (`BKP:323-325`): t·Σ_{P∈Q} tameVal_l(ψ, P) ≤ ε′.
  - **PsiOk** (`BKP:290-298`): Q consists of split, degree-1, unramified places disjoint from S0 ∪ A; k′ ≥ 1; ψ is open-kernel, anticyclotomic, valued in ⟨ζ_{l^{k′}}⟩, ramified exactly at Q, and trivial above l.
- The choice is `exists_good_of_conditions` (`TwGood.lean:239-272`, read): Classical.epsilon over (Q, k′, ψ) with `GoodTw`, made consistent across places w with the same twI. **There is no size constraint on Q.**

## 2. Argument

### 2a. Q1
The killing argument needs ρ̄_s absolutely irreducible, together with tame and no-H⁰ conditions at g_k, for each twist index i (every twisted residue characteristic l, l = 2 included).

This holds because every relevant eigensystem has, at the places over g₀ and g₁, a depth-zero local type of the "good" shape. These are the Deligne–Lusztig-type cuspidal types that define the cut Zgood through G = ∏GL_r(F_{g_k}), as in NODE-LINKN.

Local–global compatibility at g_k turns that type into a statement about ρ̄|tame inertia. *(Inferred.)* The relevant compatibility is Row0b's tame, square-free, N = 0 clause, valid for p > 16a² (NODE-GALREP §1a).

The good-tuple lemma then gives irreducibility for every l ∉ BB(r, g_k), and BB-disjointness covers all primes.

So the theorem needed is not "big residual image of one fixed form at every prime". It is the following: every form in the localised type part has the prescribed supercuspidal-type local components at g₀ and g₁. That is a design condition on the level/type, which is where the content sits.

At l = g_k the crystallinity condition is replaced by potential crystallinity (`BKP:356`). The tame/H⁰ clause at g_k is dropped (`∀ k, g_k ≠ l`), and irreducibility uses the other auxiliary prime.

### 2b. Q2
- **Global and archimedean objects.** These are RR, Nu, the period maps, heights, Theorem S, the volumes and the dimensions. They live in the B/C/W/V/S/G stages of `Stages`, which do not depend on N or on NChoice.
  - The types μ(y) are drawn from {mu0, muStar, muStar′}, with fixed Hecke characters of fixed conductor.
  - Hence no archimedean statement inside one `Stages` object mentions Q.
- **l-adic side.** ψ appears in five places:
  - (a) the Bloch–Kato lengths sLen(ρ_s⊗χ_s⁻¹⊗ψ) (partA/AT);
  - (b) IdxAt, two lattices in O′⊗Fm(i, j, b): the space Fm is ψ-independent; only its spanning vectors are ψ-twisted;
  - (c) the l-adic valuations of twisted theta values (partC);
  - (d) the tame term (partD);
  - (e) the place-w embedding eMt, which compares the fixed global lattice MtLat(muTw w, j) with `nexp.MtLat(…, Q, ψ)`.
- **The open point.** At local index i the datum D has the following:
  - nd.Mt i = MtLat(mu i, j i)⊗O_i, with mu i = muTw(w i) (`DN:76-79, 107-120`);
  - Hecke algebra generated at split v ∉ S ∪ Q ∪ {l} (`DN:146-148`);
  - χ₁ (the Speh character in r_x) **ramified at each v ∈ Q_i** (`chi_ram_Q`);
  - nd.Q i = C.Q(w_i) (NChTie);
  - automorphic points P of Mt(mu i, j i) whose local components may be ramified exactly at Q_i (`locV_unr`, `pt_loc`, `DN:635-641`), and whose μ-block character `muC i` depends on i (`DN:610, 1291-1294`).
- *(Inferred.)* For a fixed finite-level type space, a χ₁ ramified at the Chebotarev set Q_i, with norms ≡ 1 mod 2l^M and M → ∞ as ε → 0, cannot be the Speh character of its forms.
  - Twisting the Hecke action globally by ψ∘det would move ρ_π and χ₁ together. It cannot produce the relative twist ρ_π⊗χ₁⁻¹ ↔ ρ_s⊗χ_s⁻¹⊗ψ that `sLen` and `LatticeConditions.Corr` (`…/LatticeConditions.lean:181-190`) express.
- There are two consistent readings, and I could not decide between them.
  - (i) **Rebuild.** `exists_madeFrom` (`ETC:756-797`) and `Rebuild`/`RebuildTied` (`ETC:649-660`) construct the final D after the packs are chosen. They require only `SameExport` (`TwistDataAgreeAcrossCoefficients.lean:205-210`: the same nd-Galois frame, ntw, nexp, ntwbr, avPrimes) and `SameField` (LL, places, LL0, embeddings, twisted set). `what₂`, the rows, RR and nd are **not** required to be unchanged.
    - If the type spaces are rebuilt with level at Q, every archimedean estimate must be uniform in Q.
    - The quantifier that would give this is in the kit statements `RecAtK`/`RecExP` (`GlobalTwisting/ValidForConstructedPointClassesEventuallyWorking.lean:90-92, 189-200`): ∃ D Y, Over D P Lv ∧ RecOK s C cD D ∧ LedOK … ∧ TWAt D Y.nch Y.xd.
    - The constants there depend only on (s, C, cD), and P and Lv (the level choice) are fixed before D. That is the right shape, but I did not read the proof.
  - (ii) The ties are satisfied in a way I did not see, for instance through the choice of `muC i`, or with Q_i empty in the instance. If Q_i = ∅, then PsiOk with RamExactly ∅ forces ψ to be unramified, and the Chebotarev killing degenerates.

## 3. Children (ranked)

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | kit existence with `TWAt` (`RecExP`/`RecAtK` suppliers; `exists_madeFrom` + a concrete `RebuildTied`) | `GlobalTwisting/ValidFor…Working.lean:189`; `ETC:756` | ∃ D over the fixed (P, Lv) with uniform RecOK/LedOK and good twists | decides Q2: are `what₂`/RR rebuilt after ψ, and are the bounds uniform? | **core, unread** |
| 2 | `PtSel.selCore` | used at `IE/PsiAtPsiAt.lean:30` | sPi(ρ_π) ≤ sLen(ρ_s⊗χ_s⁻¹⊗ψ) | identifies ρ_π⊗χ₁⁻¹ with ρ_s⊗χ_s⁻¹⊗ψ | **core, body unread** |
| 3 | `LabelDegreeHypotheses` (`AdmTame.main`), `GlobalDatumResidualRepCondition`, `GlobalDatumDepthZeroCondition` (`R.c.rho`, `R.c.dz` ← `rows_of_inputs_and_jumps`) | `AdmissibleThreePrime.lean:17`; `RIT:13,49` | Zgood forms have the good depth-zero type at g_k, realised on ρ̄(tame inertia) | the content of Q1 | core, statements read, suppliers unread |
| 4 | `irreducibility_of_good_tuple` | `CyclotomicNorms/IrreducibilityOfGoodTuple.lean:19`; statement `CNT:36` | tame type ⇒ ρ̄ absolutely irreducible for l ∉ BB | Q1 lemma | standard in kind (orbit/degree argument); body unread |
| 5 | `TwistedPairSettingHyps` (SetHyp: NoJump, SelfDual) and `admT4_of_rational_rows` | `ETC:13`; `IE/AdmT4OfRationalRowsStatement.lean:16` | HT gaps, self-duality, adm1/adm2 for ρ_s | twisted-index inputs | core, unread |
| 6 | `choice_count`, `exists_modulus_bb_disjoint` | `DivLeRpowThreeQuarters.lean:221`; `AM/ExistsPreDataDyadicFrame.lean:72` | g₀, g₁ with disjoint BB exist | covers every l | standard counting; bodies unread |
| 7 | `residual_irreducible_of_theorem(_three_prime)`, `residualAbsIrredGoodPoint_of_residualIrred`, `admissible_at_of_irreducible_tame` | `RIT:85`; `RI3:217`; `IE/ResidualAbsIrred…:105`; `GeneralAdmissible…:254` | glue (Brauer–Nesbitt, Burnside) | — | glue, read |

## 4. Oddities

1. **Small l is handled by a prescribed type, not a large-image theorem.** This is sound in kind. It places the weight on the requirement that every eigensystem of the localised type part has the good g_k-type (Zgood). That is a cut, so Zgood ≠ ∅ must come from the construction. Where it is used, Zgood is nonempty by HG.
2. **l = g_k is a twisted place** (resChar ∈ {d, g₀, g₁}, NODE-CONGMOD). There ρ_s is only potentially crystalline. The local Bloch–Kato condition `bk` is "finite (crystalline) cocycles", and I did not check how the lifting/length lemma treats a non-crystalline l = g_k.
3. **`SetHyp` begins with a literal `True ∧`** (`BKP:328`). It is harmless.
4. **`IsotypicValuationAtRing`'s ramification clause excludes only l and g_k.** So ρ_s is unramified at pD and Q; those are carried by χ and ψ. This is consistent.
5. **The Q2 tie.** `NChTie.Q_eq` + `chi_ram_Q` + `prMt_lat` + `locV_unr` seem to need the global type-part forms to be ramified at the later-chosen Q (§2b). `Rebuild` does not preserve `what₂`. This is the single point I would escalate.
6. **No `True`/`trivial`/vacuous quantifier** in `ResAbsIrr`, `PtFam`, `ResidualIrreducibleRankR` or the adm2 supplier. The `bb_disjoint` instance is numeric for r = 9, which is not the core rank *(inferred: a toy host)*.

## 5. Coverage

Read:
- PROTOCOL; SUMMARY §11; NODE-KILLAT, NODE-LINKN, NODE-CONGMOD (all); NODE-GALREP:1-235; grep of NODE-THETA/FAMILY/HEIGHT/THEOREMS/HOSTS.
- `IRP` (1-200, 300-395); `IE/PsiAtPsiAt.lean`; `CommutingEndomorphismCondition.lean:25-50`; `NCT` (all); `NCh:1-120`; `DN:55-160, 256-420, 600-660, 769-860, 1268-1300, 1371-1375`.
- `TwGood.lean:150-274`; `BKP:286-392`; `IHF:196-231`; `ResidualIrreducibleRankR.lean:80-125`; `RIT:1-140`; `RI3` (all to 220); `CNT:19-62`; `CNI:1-30`; `AdmissibleThreePrime.lean:17-66`.
- `IE/ResidualAbsIrredGoodPointOfResidualIrred.lean:60-128`; `GeneralAdmissibleOfIrreducibilityStmt.lean:240-300`; `ResidualIrreducibilityFormsEquivalent.lean`; `FullConclusionOfInputs.lean:30-60`; `FoundationsPrimeFact.lean` (grep 78, 248).
- `AM/NontrivialReferenceForms.lean:200-300`; `AM/TrueColumnChoicesHeckeCharReferenceEqOne.lean:170-260`; `AM/TwistedLevelExtension.lean:265-300`; `AM/AssembleLattice.lean:188-197`; `NStageTrivialCharacterCoeffEq.lean:15-37`; `NuInRange.lean:10-30`; `SCuIsom.lean:10-23`; `ResCharThetaJetPlaceDegOne.lean:10-30`.
- `ETC:400-500, 700-862` and its definition list; `TwistDataAgreeAcrossCoefficients.lean:205-260`; `RhoDetPrimeEqMuTildeMulChiPow.lean:240-300`; `LatticeConditions.lean:54-200`; `DisjointExceptional.lean:96-104, 195-216`; `CharacterBoxes/DesignS.lean:30-90`; `ValidFor…Working.lean:80-100, 185-215`; `SetUnipotentTranslate.lean:66-72`; `LocalQuadraticParts.lean:340-346`; `MvAll.lean` (glue sample).

Not opened:
- the bodies of `PtSel.selCore`, `irreducibility_of_good_tuple`, `admT4_of_rational_rows`, `AdmTame.main`, `rows_of_inputs_and_jumps`, `exists_modulus_bb_disjoint`;
- any concrete `RebuildTied`/kit constructor;
- the definitions of `Fo`/F-gain (taken from NODE-CONGMOD: F_j(w) = 0 at untwisted w and cancels as Fo), `thEval`, `eThPsi`, and `nexp.MtLat` in the core instance.
