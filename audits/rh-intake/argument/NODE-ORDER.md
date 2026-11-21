# NODE-ORDER: the order of choices for the twist (Item A) and BB-disjointness for the live family (Item B)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `NBC` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotBaseCondFalse.lean`
- `CQF` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CmQuadraticFormEqAlternatingForm.lean`
- `VFC` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ValidForConstructedPointClassesEventuallyWorking.lean`
- `ID/` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/`
- `TPS3/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `SN/` = `Development/AutomorphicArithmetic/ShortNorms/`

"The Lean says" means I read the line. *(inferred)* marks my own reading. Nothing was compiled.

## 0. Verdicts

- **Item A: closed, with reading R1 refined. There is no circular dependence.**
  - The construction has two passes over one fixed pre-chain P (host, ranks and level primes).
  - The first pass has untwisted twist data (Q = ∅, ψ = 1). The Chebotarev choice of (Q, k, ψ) is made from that pass's **export**: the l-adic block `ntw`/`nexp`, which holds ρ_s, χ_s and the theta/Bloch–Kato data.
  - The second pass rebuilds the whole automorphic datum. Its types at twisted places are **δ·ψ_w**, a Hecke character ramified at Q. Its export is required to be **identical (HEq)** to the first pass's.
  - GoodTw (the Selmer-killing conditions) depends only on the export, so it transfers verbatim.
  - The archimedean bounds RecOK/LedOK are proved for every Core over every twist datum T, under constants fixed beforehand. So they are uniform in Q.
- **Item B: closed. A supplier was found for the actual r = k+m−1 (≍ x^{9/2}) and g₀, g₁ ≍ (k·b)⁸.**
  - The supplier is a counting/pigeonhole lemma, `typePrimesN`, built on `choice_count` (a theorem).
  - It feeds `HostGood`, which goes to `PreCh.BB_disj` and then to `ntypes.BB_disj`.
  - The r = 9 numeric certificates belong to three separate toy hosts. None of them reaches the host/family supply.
  - Correction to NODE-TWIST §1b.6: `exists_modulus_bb_disjoint` / `ExistsPreDataDyadicFrame.lean:72` is **not** on the main route. `exists_preData_dyadicFrame` has no users.

## 1. Item A

### 1a. Statements (all read)

- `TwDat B` (`CQF:79-89`) has fields pl, Q(w), k(w) and psi(w) : HChar E, with these conditions:
  - `IsPsi (resChar w) (Q w) (psi w)`;
  - the order of ψ divides l^k;
  - `psi_tw`: ψ is a twist that is unramified on `offSet` (`CQF:75-77`: the primes dividing 30·condN, g_i, pde, pde′, T_u, q0 and the level primes);
  - Q avoids l;
  - ψ = 1 off pl;
  - conjugation invariance.
- **The type at w is `xiTw w = (δ or δ′) · T.psi w`** (`CQF:91-92`). The type set is {1, δ, δ′} ∪ range(xiTw) (`CQF:94-95`).
- `TwDat.untw` (`CQF:196`) sets Q = ∅, k = 0, ψ = 1.
- `Enl B B'` (`CQF:72-74`): **B'.toPre = B.toPre**, with the same Ks and LL0 images and a larger LL. The pre-chain (host, ranks, level primes) is fixed.
- `Core K X f T` includes `nch_Q : ∀ w ∈ Wt, O.nch.Q w = T.Q w ∧ O.nch.k' w = T.k w` (`AM/RationalRootsDef.lean:61`). The datum's NChoice is the twist datum T.
- `FirstG KP Q` (`NBC:53`): for large Ctx, and every B and f with KP, and **T = untw**, a full Stages+Core exists satisfying the slot Q.
- `ExportF` (`NBC:55-58`): every such first-pass core satisfies `ExportAt`.
- `Pass KP Q r` (`NBC:60-66`): for every first-pass core with ExportAt, and for every finite avoidance set A, there exist B′ with Enl B B′, f′ ≅ f and T′ : TwDat B′ with T′.pl = T.pl and T′ avoiding A, such that r K B′ f′ T′ holds.
- `SecondG` (`NBC:68-69`) = Pass with r = HasCore(Q ∧ TwAllAt ∧ Q′). The rebuilt Stages over (B′, T′) are new existentials.
- `RecAtG QL` (`CQF:180-182`) = EvG: ∃ D Y, Over D K.P K.Lv ∧ **RecOK K.s K.C K.cD D** ∧ LedOK ∧ TWAt ∧ QL.
- `RecExP` (`VFC:190-200`) quantifies as follows: ParEv κ (eps, C, cD, ch), then ∃ cs x0, then ∀ s P a b c with ChGood, then ∃ du Ds, then ∀ Lv, then ∃ D Y over P with RecOK s κ.C κ.cD D ∧ LedOK ∧ TWAt ∧ ….

### 1b. The live path (all read)

`memberTop_final_contextParameters` (`ID/MemberTopFinalContextParameters.lean:14-23`)
= `existsLayeredData_of_goodScaleContexts` (= `recExP_of_recAtG`) ∘ `layeredAutomorphicData_exists_of_twoPasses`
(= `recAtG_of_two_passes`, `ID/LayeredAutomorphicDataExistsOfTwoPasses.lean:22-45`). The proof does the following:
- `:34-36`: it takes a first-pass core c over (B, f, untw).
- `:37-38`: it applies `SecondG` (h3) with the export (h2), A = ∅ and S₂ = ∅, which yields (B′, f′, T′, c′) with TwAllAt.
- `:39`: it applies `lay_of_core` to the **second-pass** Stages ⟨B′, C′, W′, V′, S′, N′, G′⟩. The returned datum is the second-pass datum (`:45`).

The suppliers of FirstG, ExportF and SecondG:
- `memberE_of_steps2` (`ID/ExistsMemberOfConstructionStepsSecondPass.lean:38-61`) takes two slot systems 𝒮 and 𝒮′.
  - 𝒮′ comes from `GeometricNormExtension hL cDep` = extensionWithOrigin × **PLift (GoodO (w.D Z) nch xd)** (`TPS3/ExtensionWithOrigin.lean:28`). That is, the second-pass slot carries GoodO *of its own datum and its own nch*.
- It is called from `exists_baseLattice_of_prime_alt` (`TPS3/ExistsBaseLatticeOfPrime.lean:57-72`), with `second` taken from `sFino_and_secondNo_of_sFinl'`.
- The content of the second pass is `secondNo_of_sMt_sRat_sCusp_sFinl` (`TPS3/FiniteLevelAndSecond.lean:72-115`):
  1. `:83-87`: from the first-pass built core and its export e, `exists_pre_point_with_henselian_level` (`TPS3/ExistsSeed.lean:26-37`) gives a first-pass state x with D₁ = Dof x, and **∀ A, Nonempty (Seed D₁ A)**.
     - That is built by `nonempty_seed_of_kept … e`, which is the Chebotarev choice from the export.
     - `Seed` (`ID/ExistsUnlocalizedSaturatedState.lean:64-82`) records s, Q, k, ψ and the proposition `good : … GoodTw D.nexp (bk0 D) (twEOf xd) N0 (s v) … (A (s v)) (Q (s v)) (k (s v)) (ψ (s v)^a)`, together with `sep` (the Q's for different indices are disjoint).
  2. `:88`: `exists_twisted_cohomology_class_lift_alt` gives B′ (Enl), T′ with `TwFrom … σ h T'` (`ID/ExistsUnlocalizedSaturatedState.lean:89-98`):
     - at twisted v′, T′.Q = σ.Q, T′.k = σ.k, and T′.psi is a global Hecke character χ with `FrobPick` of σ.ψ;
     - otherwise T′.psi = 1.
  3. `:93-110`: the second-pass state is Start K B′ f′ T′ w′. Then the stages bare/sa/mt/rat, and `mv : MvB` (`…ExistsUnlocalizedSaturatedState.lean:111-114`) give x″ with **`Carried (Dof x) (Dof x'')`** (`:51-55`). Carried is SameExport plus agreement of the emb0 embeddings.
  4. `:113`, `has3_of_carried_levelB2` (`:52-71`): it proves GoodO for the final datum D₃ = (w′.st Z).toD7 by `goodO_of_alt_alt` (`:30-51`). That uses `goodTwist_of_seed_character_powers` (`ID/GoodTwistOfSeedCharacterPowers.lean:157-227`), whose argument is:
     - h13 : SameExport D₁ D₃ (`:163-164`);
     - the second-pass raw pack is a power ψ^a of the seed pack (`rigid_raw_packet_eq_pow_alt`, `TPS3/RigidRawPacketEqPow.lean:13-24`, via FrobPick and `pow_of_tied hc.cheb`);
     - **σ.good on D₁ is transported along h13 (`good_pack`, `SameExport.good`) to GoodTw on D₃.nexp** (`:193-208`).
- `SameExport D D′` (`Proofs/InertiaEigenvalues/TwistDataAgreeAcrossCoefficients.lean:205-210`) consists of:
  - `SameGalois nd`;
  - `TwistDataAgreeAcrossCoefficients ntw` (HEq of Tw, l, O0, O, Ok, chi1, Sig, jS, side, **rhoS**, S0, hEig, … `:23-48`);
  - `SameForms nexp`;
  - ntwbr;
  - avPrimes.

### 1c. What depends on what

| object | first pass | second (final) pass | why it is well-founded |
|---|---|---|---|
| pre-chain P (host, g₀, g₁, ranks, levelPrimes) | fixed | the same (`Enl`: B′.toPre = B.toPre) | chosen before both passes |
| types μ at twisted w | δ (or δ′) | **δ·ψ_w**, ψ_w ramified exactly at Q_w (`CQF:91`, TwFrom) | ψ_w comes from the seed of pass 1 |
| what₂, rows, RR, NuLat, Theorem-S data, nd (with nd.Q = T′.Q and the nd-level χ ramified at Q, `DataN.lean:154`) | built over untw | **rebuilt** over (B′, T′) | they are new existentials in HasCore |
| export ntw/nexp (ρ_s, χ_s = ntw.chi1, Sig, theta/BK data) | E₁ | **HEq E₁** (Carried) | the data killed by the Selmer argument are these; they do not depend on Q |
| GoodTw / GoodO | proved on E₁ by the seed | transported, since it is a predicate of nexp, bk0, xd, N0, S, Q, k and ψ only | no recomputation is needed |
| RecOK / LedOK / TupUsed | — | from `lay_of_core` (`ID/ExistsLayerParametersAdmissible.lean:105-111`): **Ev fun K => ∀ X f T c**, … RecOK K.s K.C K.cD | the constants (Ctx) are fixed before X and T, so the bounds are uniform in T and hence in Q |

- Answer to (i). The Selmer groups that are killed are those of the export. The export is literally the same object in both passes.
  - The source representation ρ_s is unramified outside l·g₀g₁ (NODE-TWIST) and is untouched.
  - Only the m-block character changes, χ₁ = χ_s·ψ (the type δψ_w).
  - This is exactly the "uniform statement" the brief anticipated. It also removes NODE-TWIST's inferred objection, "a global ψ∘det twist cannot produce the relative twist": in pass 2 the twist sits only in the μ-block type.
- Answer to (ii). The uniformity quantifier is `lay_of_core`'s `Ev fun K => ∀ … (T : TwDat X.B) …`, together with RecExP's order (constants before s, P, Lv, D).
  - Q is not bounded, but no archimedean clause mentions Q. Q enters only through TwDat/nch, and through the l-adic partD (t·Σ_{P∈Q} tameVal ≤ ε′, NODE-TWIST).

## 2. Item B

### 2a. Statement (`Formalism/CyclotomicNorms/StatementI.lean:10-12`, read)

```lean
def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))
def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}
```
- So ℓ is exceptional for g when the ℓ-part of g^d − 1 exceeds (g^d)^{1/4}.
- For ℓ ∉ BB(r, g), the prime-to-ℓ reductions of the tame-type roots (the roots of unity of order dividing g^d − 1, d ≤ r) stay injective. That is what `IsGood` needs. *(Inferred from NODE-TWIST §1b.5; I did not reread the body of `irreducibility_of_good_tuple`.)*
- `ChoiceCount` (`:24-27`) says: for fixed g₁ ∈ [Y, 2Y], the number of g ∈ [Y, 2Y] with BB(N, g) ∩ BB(N, g₁) ≠ ∅ is at most (3N+1)(1 + 2N²(Y^{3/4} + 1)).
- It is proved as `choice_count := choiceCount_of exceptional_set_count rootsOfUnityCount` (`Proofs/FoundationProofs/DivLeRpowThreeQuarters.lean:221`; both inputs are theorems, at `ExceptionalPrimesFiniteCardLe.lean:51` and `CardPowEqOneLeOfIsCyclicUnits.lean:78`).

### 2b. Supplier for the live family (all read)

- `typePrimesN` (`SN/typePrimesN.lean:78-129`): eventually in x, for all N, d, k, r with 1 ≤ r ≤ x⁵, there are g₀ ≠ g₁ prime in [Y, 2Y], with Y = (k·e^{x^ε})⁸, NormOne d N, and **Disjoint (BB r g₀) (BB r g₁)**. The proof has two steps:
  - `exists_pair_disjoint` (`:29-49`): if every pair met, choice_count would bound #G by (3r+1)(…) < Y^{9/10} (`excluded_lt`, using 20r³ < Y^{3/20}, `:108`);
  - the short-interval norm-prime count gives ≥ Y^{9/10} candidates (`:115`, from `normPrimesN`/ShortNorm).
- `levelData` (`SN/levelData.lean:37-…`) applies it with **r = R.r**. The bound R.r ≤ x⁵ comes from `rank_basic_bounds` (`GlobalInterpolation/ExplicitRanksBasicBoundsLargeScale.lean:22`).
- `hostOfFieldOf` (`SN/hostOfFieldOf.lean:159-…`, `:167` uses levelData) produces `HostGood`. `HostGood` contains `Disjoint (BB R.r (H.g 0)) (BB R.r (H.g 1))` (`GlobalTwisting/ThinScalesIffHostBound.lean:104`).
- `ChGood` (`GlobalTwisting/SetUnipotentTranslate.lean:61-64`) contains `host : HostGood …`. `PreCh`/`Pre` carry `BB_disj` (`AM/DuStarPos.lean:25`, `Foundations/RootOfUnityEightQMemCoeffGaloisSubfield.lean:83`). `ntypes.BB_disj` is built from `B.BB_disj` (`ID/ExistsTypesIdempotentCoefficients.lean:252,342`).
- So the live r is the full rank r = k+m−1, growing with x. It is not r = 9.

### 2c. Toy instances: classification

| constant | where | used by | class |
|---|---|---|---|
| `BB_disj0` (r = 9; 413718278401, 603339156001) | `LocalRingCardinality/SpanPowerMembership/Primes.lean:554` | only `SpanPowerMembership.lean:26` (exampleRecord, conditional on `LocalGap H0`) | sanity |
| `Examples₂.H0/R0`, `exampleRecord`, `gA_prime`, `prime_large` (toy) | ExampleLayerExistsGenerators, Primes | `Columns/ChainInst.lean` (toy chain), `StandardIntegralLatticeExists.lean:1228-1246` (IsEmpty lemmas) | sanity, no consumer found |
| `nd2N`, `toyPrimes`, `toyFirstParameter` | `Columns/CyclotomicIsCyclotomicExtension.lean`, ChainInst, `KernelLocalFactors/ColInst.lean:1216` | `DecoratedLatticeProofs/RanksFourToFrame.lean:115` `exists_closed_ok` → `LatticeFrames/IsGLExistsUnique.lean:348` `twData_closed` | **dead**: twData_closed has no users |
| `bb_disjoint` (r = 9; 10944929, 128860109809), `Explicit.pre` (571/599) | `Foundations/FoundationsPrimeFact.lean:78,237-307` | `Mem.exists_pre` → `exists_base_two_words`/`nonempty_base` (`Foundations/ExistsBaseTwoWords.lean:246-252`), `exists_sStage_unconditional` (`AM/ExistsSStageUnconditional.lean:318`) | Nonempty/∃ witnesses for record types |
| `HostFam.Rt s`, `exists_bb_disjoint` (congruence trick, e ≤ 9) | `Formalism/SharpRestriction/InertJacobiLevels/HostFam.lean:14,165,230` | `arith_nonempty` | sanity |
| `exists_host_congruence_primes` (via `exists_modulus_bb_disjoint`) at `Rt 0` | `ID/ExistsNatBoundPre.lean:36` `exists_pre_two_words` | `exists_pre_hasLetters` → `exists_stages`/`nonempty_record : Nonempty D7` (`ID/ExistsPreHasLetters.lean:95-105`), `exists_muIsW_proper`, `exists_hyp`, `exists_pre_sized` → `exists_colIn_jets`, `ExistsOkPins.exists_pre` | Nonempty/∃ witnesses |

- `nonempty_record` is consumed by "hypotheses_inhabited / data_inhabited / exists_field / exists_complMet" lemmas (`Divisors/ExistsField.lean:92`, `ExistsComplSpace.lean:146`, `SiegelWeil₂/ExistsNotEisContinues.lean:21`, `Divisors₂/IsModerateFormAdd.lean:23`). These are literature-hypothesis inhabitation checks.
- None of these witnesses reaches `HostExW`, `hEx`/`classSel`, `RecExP` or `memberTop_final_contextParameters`. Those take P, the host and the scale universally, and the family host comes from `hostOfFieldOf`.
- I did not walk every consumer of `nonempty_record` up to the root. *(Inferred:)* an ∃/Nonempty witness can discharge only an existential. It cannot instantiate a "for all families" statement, so it cannot make the live family the toy one.

## 3. Children (ranked)

| # | name | file:line | role | weight |
|---|---|---|---|---|
| 1 | `exists_levelB2_carried_of_levelB1`, `levelI_same_gal_transfer_to_levelB1_list` (= MvB, via `moveToBase_of_inputs_serN`) | `TPS3/MultiplicityBoundOfLocalComponents.lean:17-31` | rebuilds the datum over (B′, T′) with the **same export**, so that the new automorphic side (types δψ_w, level at Q) is still tied to the old ρ_s and nexp | **core, unread** |
| 2 | `nonempty_seed_of_kept` (Chebotarev from ExportAt) | `TPS3/ExistsSeed.lean:33` | chooses (Q, k, ψ) with GoodTw for the pass-1 export | core, unread |
| 3 | `exists_twisted_cohomology_class_lift_alt` | `TPS3/FiniteLevelAndSecond.lean:88` | a global Hecke character χ realising the seed ψ (FrobPick), with the base enlarged | core, unread |
| 4 | `goodTwist_of_seed_character_powers`, `rigid_raw_packet_eq_pow_alt` | `ID/GoodTwistOfSeedCharacterPowers.lean:157`; `TPS3/RigidRawPacketEqPow.lean:13` | transport of GoodTw along SameExport | read; glue plus `pow_of_tied` (Chebotarev) |
| 5 | `lay_of_core` (TamePow.tame_of_pow, c.col.mink/atT, c.gy.led) | `ID/ExistsLayerParametersAdmissible.lean:105` | RecOK/LedOK uniformly in T | read; its fields are proved in the Core constructors |
| 6 | `typePrimesN` ← `choice_count` ← `exceptional_set_count`, `rootsOfUnityCount`; `normPrimesN` (ShortNorm) | `SN/typePrimesN.lean:78`; `DivLeRpowThreeQuarters.lean:221` | BB-disjoint level primes for the live r | read (bodies of the two counts not read); standard counting plus the Hecke short-interval count |

## 4. Oddities

1. **The types are not fixed across passes.** NODE-TWIST's "μ(y) ∈ {mu0, muStar, muStar′} fixed" holds for pass 1 only. The final datum's twisted types are δ·ψ_w (`CQF:91`). This is what makes `chi_ram_Q`, `NChTie.Q_eq` and `prMt_lat` consistent.
2. The final datum's nd-level χ is ramified at Q, while `ntw.chi1` is HEq to that of pass 1. These are different objects (`DataN.lean:154` vs `:321`). The relation χ_nd = χ_s·ψ is a tie that child 1 must establish. I did not verify it.
3. `recAtG_of_two_passes` calls SecondG with A = ∅ and S₂ = ∅ (`:38`). The avoidance freedom in `Pass` is unused at this level.
4. `ExistsPreDataDyadicFrame.exists_preData_dyadicFrame` and `twData_closed` are dead code. NODE-TWIST's citation of the former as the main route is wrong.
5. The `Examples₂` namespace also hosts generic definitions used on the live path (`Examples₂.stdSpace` in `AM/DuStarPos.lean:15-18`; `Examples₂.lamOf`). These are definitions, not the toy host, so their use is harmless. It does make name-based greps for "the example" noisy.
6. The constraint r ≤ x⁵ (`typePrimesN`) is met because R.r ≍ x^{9/2+10ε} < x⁵ only for ε < 1/20. Here ε < 1/52 is assumed throughout, so it holds.

## 5. Coverage

Read:
- PROTOCOL Explainer; NODE-TWIST (all); NODE-HOSTS (all); greps of NODE-FAMILY, NODE-THEOREMS and the others; kernel-surface report §2.
- NBC:1-120; CQF:60-100, 165-200; VFC:80-100, 180-215; `AM/RationalRootsDef.lean:50-80`.
- ID/: LayeredAutomorphicDataExistsOfTwoPasses(+Statement), MemberTopFinalContextParameters, ExistsLayeredDataOfGoodScaleContextsStatement, ExistsMemberOfConstructionStepsSecondPass:1-65, ExistsUnlocalizedSaturatedState:40-120, GoodTwistOfSeedCharacterPowers:150-229, ExistsLayerParametersAdmissible:1-111, ExistsNatBoundPre:1-60, ExistsPreHasLetters:70-105.
- TPS3/: MemberEClosing, ExistsBaseLatticeOfPrime, FiniteLevelAndSecond (all), ExistsSeed:1-37, RigidRawPacketEqPow:13-24, MultiplicityBoundOfLocalComponents:1-35.
- `AM/DsigEq.lean:1-40`; `TwistDataAgreeAcrossCoefficients.lean:23-48, 205-215`; `DataN.lean:140-160`.
- StatementI:1-30; SN/typePrimesN (all), levelData:25-70, hostOfFieldOf:159-200; ThinScalesIffHostBound:98-110; SetUnipotentTranslate:55-80; DuStarPos:15-30; RootOfUnityEightQ…:70-90; ExistsHarishChandraWeights:1-40; ExistsPreDataDyadicFrame:60-100, 140-160; HostFam (definition list, 225-237); FoundationsPrimeFact (list, 235-310); RanksFourToFrame:100-140; IsGLExistsUnique:340-360; ExistsBaseTwoWords:240-252; ExistsSStageUnconditional:315-330; ExistsField:86-96 and the 3 sibling consumers.

Not opened:
- the bodies of children 1-3;
- `ExportAt`, `TwConjAt`, `GoodCl`;
- `irreducibility_of_good_tuple`, `exceptional_set_count`, `normPrimesN`;
- the full consumer trees of `nonempty_record` / `exists_pre_sized`.
