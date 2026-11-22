# NODE-G2A: crystallinity at w | l with automorphic HT weights (`G2a`, `CoreNormFacts.g2`): statement, constructor, guards

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my own reading. Nothing was compiled or run.

Abbreviations:
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `TC/` = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/`
- `DN` = `Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean`
- `DNL` = `Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean`
- `CCD` = `TC/ConstituentConditionAtDistinguishedPrime.lean`
- `D7F` = `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean` (the `D7` structure)

## 0. Verdict

**No ESCALATE.**

- **A constructor fills `g2`.** It is `UpperTheory.GalC.facts_of_galois_preconditions_of_cutRec` (`TPS/CFacts.lean:45-57`), with `g2 := de_rham_points_weight_jumps_alt …` (`TPS/DeRhamPointsWeightJumps.lean:15-37`). That theorem is proved, and I read it.
- **`G2a` has no explicit "unramified at l" guard, but the guard exists structurally.** For localisation i and l = l_i ∉ {g₀, g₁}, the datum's own fields force every point at localisation i to have an unramified local parameter at every w | l_i (`iso_unr_l`, CCD:43-55, read). So `G2a` is never asserted at a prime where the representation is ramified.
- **The obligation moves into the datum fields.** These are `NData.SQ_l`/`S_def`, `NAut.locV_unr`, and the inert clause of `IsBCV`. In the one live-looking `NAut` constructor I found, `locV_unr` is a proved theorem.
- **"Crystalline" is the real notion.** It means dim_{LL} (V ⊗ B)^{G_K} = [K₀ : ℚ_l] · dim V, with B tied to the in-tree `Per.Bcris` by a G_{ℚ_l}- and φ-equivariant ring isomorphism. `G2a` and `TopCore`/`admG2` use the same predicate `IsCrys` with the same period data `(D.loc l).PD K_w`.
- **The source of crystallinity is Row0b, not Faltings/Tsuji inside this node.**
  - Row0b's `nice` clause gives: de Rham, pst, and WD(D_pst) matching the local parameter when that parameter is Tor with N = 0.
  - From that, through `CarUAlt` → `AutomorphicGaloisAdmissible` (`adm2_alt`), crystallinity follows from Fontaine's criterion `CrysIffWD`: crystalline ⇔ de Rham and WD unramified.
  - That Row0b's proof establishes this clause for the theta-lift and trace-limit constructions (the Kisin / Chenevier–Harris interpolation step) was **not verified**. See §4.

| Q | Answer | Status |
|---|---|---|
| 1 | §1 | definitions read |
| 2 | §2: `CFacts` → `de_rham_points_weight_jumps_alt` → `crys_unram_of_lgc` + `lgc` + `iso_unr_l`; input `adm2_alt` ← `galClose_alt` ← `CarUAlt` ← Row0b (`One.M.Row`) | constructor proved and read; `ofDual_star_alt`/`carU_of_star_alt` statement only |
| 3 | Guarded structurally, not vacuous. `IsCrys` is real. §3 | read |
| 4 | χ₁ is ramified only at Q i, and Q i is not above l_i (`SQ_l`). η_T is unramified everywhere. §3d | read (μ_i via `muUnr` not opened) |

## 1. Statement (Q1)

**`CoreNormFacts.g2`** (`TPS/NormChoiceFacts.lean:24`):
`g2 : DeRhamFamilyAwayAlt D ∧ DeRhamJumpsDistinctCondition D`.

**`DeRhamFamilyAwayAlt D`** (`TPS/DeRhamFamilyAway.lean:26`):
`∀ i r, GoodR D.nd i r → G2a D.nd D.naut i r`.

**`G2a`** (`TC/TrivialLocalCondition.lean:81-84`):
```lean
∀ w ∈ placesOver H.E (N.l i), N.l i ≠ H.g 0 → N.l i ≠ H.g 1 → ∀ x,
  A.IsCrysW i (mapRep (iotaOQ N A i) (r x)) w ∧
  ∀ τ, InducesW N i τ w → A.jumpsW i (mapRep …(r x)) τ = A.locAutHodgeTateWeightsLevelZero i τ
```

In words:
- **Range.** It holds for every localisation index i ∈ `N.Loc`, with prime l = l_i (an `NData` field, DN:69-71), and for every place w | l of the host CM field E, provided l ≠ g₀, g₁.
- **Representation.** For every eigensystem x ∈ X_i, the Galois representation r_x : G_E → GL_{nV}(O_i) of a GoodR family is pushed to \bar{ℚ}_l.
- **Conclusion.** r_x|_{G_{E_w}} is crystalline. At every embedding τ inducing w, its HT jump multiset equals `locAutHodgeTateWeightsLevelZero i τ`. By `NAut.locAut_hodgeTateWeightsLevelZero_def` (DN:703-705) that multiset is {−z + (nV−1)/2 : z ∈ infWt_i(ι∘τ)}, i.e. the weights read off the infinity type.
- **Guards present.** Only l ≠ g₀, g₁.
- **Guards absent from the text.** There is no "level prime to l", no "l unramified in E", and no l > c.
- **Where demanded.** It is demanded at **every** i, not only where it is used. The only consumer (`GTwoTheta.main_alt_alt` via `AdmGTwoLarge`, TPS/ImportsExtraMore.lean:14-20) uses it for l > lStar, l ≠ g_k.

**Second conjunct.** `DeRhamJumpsDistinctCondition` is produced in the same proof (TPS/DeRhamPointsWeightJumps.lean:37) from `constituentCondition_of_hodgeJumps` (CCD:172-194). It is not opened further here.

**Definition of crystalline.**
- `NAut.IsCrysW` is an abstract field (DN:682).
- It is tied by the `D7` field `loc_tie : LocTie nd naut loc nbr` (D7F:275; `LocTie` DN:1376-1416) to `LocBridge.IsCrysW P r := IsCrys (P.PD Bw.Kw) (Bw.rep r)` (DNL:718-719).
- `IsCrys := finrank LL (Dcris PD ρ) = finrank Qp K₀ * finrank LL V`, with `Dcris = ⨅ g, ker(actVB g − id)` = (V ⊗ B)^{G} (`Formalism/WeaklyAdmissibleFiltrations/Statement.lean:131-132, 169`).
- The rings come from `D.loc l : LocPrime l` (DNL:527-562). These are abstract `LocRings`, but the `D7` field `locT : LocTied l (loc l) (locA l)` (D7F:239) gives:
  - ring isomorphisms `eB : B ≃ Per.Bcris l` and `eD : BdR ≃ Per.BdR l`;
  - compatibility with the Galois action, φ, filtration, t and A_inf (`Formalism/LocalRingCardinality/AdicCompletionLocal/LocTied.lean:11-36`).
- `Per.Bcris` is a concrete construction (`…/InstIsAdicCompleteOCSpanSingletonSetCast.lean:67`, `Reformulated.AutPerF.Bcris l (OC l)`; I did not unfold it).
- **So this is the standard B_cris-admissibility.** It is not a weakened notion (not Wach-lattice existence, not potentially crystalline; the latter is the separate field `IsPotCrysW`).

**Same predicate as `TopCore`.**
- `admG2` (`Formalism/SharpRestriction/LevelLetterCocycles/DecompositionData.lean:184-189`) and TopCore's hypothesis use `IsCrys (Br.PD D.loc D.nbr i w hw)`.
- `Br.PD := (L (N.l i)).PD (nbr i w hw).Kw` (`…/QuotientHomNonvanishingBound.lean:813-815`), which is the same period data.
- The bridge `DualTwistCrys.crys_bridge_alt_alt` (`TPS/CrysBridge.lean:40-45`, read) is exactly `(D.loc_tie i w hw).2.1 … |>.1.1` applied to `G2a`'s first clause.

## 2. Constructor and argument (Q2)

**Producer chain** (all read unless marked):

1. `NLinkE.main_alt_alt` (TPS/AdmissibleParameterEventually.lean:30) takes `NormChoiceFacts (Fm.D x i) nch` as a hypothesis.
2. That hypothesis comes from `FactsFAlt` (TPS/BoundAtTwoThreeFamilyFon.lean:23-24), a hypothesis of `NLinkClose.main_alt_alt` (TPS/ImportsFurtherTail.lean:22, 61, 73).
3. **The only constructor of `NormChoiceFacts` found** (grep below) is `facts_of_galois_preconditions_of_cutRec` (TPS/CFacts.lean:45-57).
4. It is reached via `exists_good_cut_facts_tie4` (CFacts:58-62). That is called at `TPS/CFinal.lean:21` (`final_of_alt`; I did not trace CFinal to the root).
5. Its line 50 is `g2 := de_rham_points_weight_jumps_alt D h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC`.

**`de_rham_points_weight_jumps_alt`** (TPS/DeRhamPointsWeightJumps.lean:15-37). Inputs:
- `tie0`;
- `adm1` (every point P has a base-change parameter Pa, `IsBCV`);
- `adm2_alt` = `AutomorphicGaloisAdmissible`;
- `adm5`;
- `CutRec`.

It returns `crys_unram_of_lgc D h0 h1 (lgc D h0 h2 h5) i r …`.

**`crys_unram_of_lgc`** (CCD:82-97) proves G2a. For x, w | l, l ≠ g₀, g₁:
1. Pick a point P over x (`pt_surj`) and its parameter Pa (`adm1`).
2. `iso_unr_l` (CCD:43-55) gives that `isoLoc Pa w` is unramified.
3. Hence it is `Nc` (`Nc.of_unr`).
4. `large₂` (from `lgc`, CCD:205-215) at w | l with `Nc` gives three things for r_x: `IsdRW`, `RelA(wdOf r_x w, isoLoc Pa w)`, and HT jumps = `locAutHodgeTateWeightsLevelZero`.
5. `RelA.unr` (`…/CuspidalSupport/GaloisStatementWeakOfFull.lean:39-42`) transfers unramifiedness to WD(r_x|_w).
6. `TieGal.1` = `CrysIffWD` (DN:1343-1346: IsCrysW ⇔ IsdRW ∧ unr(wdOf)) turns "de Rham + WD unramified" into `IsCrysW` (CCD:97).

**`lgc`** (CCD:205-215) takes ρ₀ from `isoRep D t0 a2 i P Pa` (the representation attached to the isobaric sum Pa), conjugates it to r_x (`heckeGaloisRepQbar_conjugate_unique` with `adm5`), and transports the local clauses.

**Mathematically.** π_x is unramified at w | l, so the attached ρ is de Rham with the infinity-type HT weights and has unramified WD representation at w. By Fontaine's criterion (with Berger's dR ⇒ pst), ρ is crystalline.

**Where the l-adic local–global input comes from.**

`AutomorphicGaloisAdmissible` (`TC/AutomorphicGaloisAdmissible.lean:133-151`, read) states, for every i and every csd regular-algebraic cuspidal π of GL_a/E, that some ρ exists with:
- **at w | l, under the guard `a = 1 ∨ Nc(locG π w)`:** de Rham, HT jumps = `jumpsInf`, and `CuspA(wdOf ρ w, locG π w)` (lines 140-142);
- **at w ∤ l:** `RelW`.

The guard **is** present at this level.

Its supplier chain:
1. `a_close_main` (TPS/SClose.lean:25-43): `ha2 := galClose_alt hP hL D P` (:39), and `tie0`'s `TieGal` := `tieGal_of_jumpsCard_of_deRhamPotSemistable hP.berger …` (:38; statement not opened).
2. `galClose_alt` (SClose:21-22) = `automorphic_galois_admissible_of_theta_local_inputs hP (mergeP'_alt … hP.car …)` (TPS/GalRepRankTwo.lean:133-147, read). Rank a ≥ 2 goes through `galRep_rankTwo_alt` (lines 100-132 read). There `CuspA` at w | l comes from `cuspA_of_ab` applied to the `Ab` clause of `CarUAlt` (WD(D_pst) of ρ|_w vs. rec(π_w) when NcW), and de Rham/HT come from `IsGalUAlt.above` (`LocalConditionsAbovePrime.deRham/jumps` under `NiceAlt`).
3. `CarUAlt` (TPS/WeightsConj.lean:55-66) is the field `ThetaLocalInputsAlt.car` (TPS/ThetaLocalInputs.lean:22). It is filled at `TPS/PublishedInputsCombined.lean:13` by `carU_of_finite_gl_recT hFin hLL (hCSD.1 hCLGD)` with `hCSD := bridgeStar_alt hGK` (TPS/SOneRow.lean:11-12, read) and `hCLGD : UpperTheory.One.M.Row`.
4. `UpperTheory.One.M.Row := UpperTheory.GalStar.Row0b (IsRecT)` (`Development/AutomorphicArithmetic/Foundations/UnitarySphericalFixing/SatakeParameters/RecT.lean:6`, read).
5. So the input is **Row0b, proved in-tree** (NODE-GALREP), through `ofDual_star_alt` = `carU_of_star_alt hGK H` (TPS/SOfStar.lean:54; body not opened).

A sibling route `HypothesesBridge.main` (`Development/AbelianVarietyTheory/Proofs/SatakeParameters/PublishedInputsCombined.lean:26-46`) builds the different bundle `Hypotheses₂`. Its `car := local_global_above_l hFin hLL (hCSD.1 hCLGD)` uses the Published `CaraianiLocalGlobal`/`CaraianiLocalGlobalDual`. I did not establish which bundle the root uses for `ThetaLocalInputsAlt`; the `_alt_alt` combiner at TPS/PublishedInputsCombined.lean:24 takes `One.M.Row`.

**Correction to the brief.** Row0b does carry crystalline content at l. NODE-GALREP §1a lists `AboveB.crys` (crystalline with HT jumps at spherical σ) and `AboveB.nice`. The G2a route uses `nice` (pst + WD) together with `CrysIffWD`, not `crys` directly.

**Which literature this matches** *(inferred)*:
- The statement used is Caraiani / BLGGT Thm 2.1.1-type local–global compatibility at l for π_w unramified, which gives crystalline.
- The `JumpsCard`/`TieGal` step is Berger (dR ⇒ pst, `Published.DeRhamPotSemistable`) plus Fontaine's crystalline ⇔ WD unramified.
- For geometric (GeoOne) representations this is Faltings/Tsuji. For theta-lift and trace-limit representations it needs Kisin / Chenevier–Harris-type interpolation of the pst/WD condition. Whether Row0b's proof contains that was **not checked here**, and NODE-GALREP did not open it.

## 3. Guards (Q3, Q4)

**3a. Why no explicit guard is needed** (`iso_unr_l`, CCD:43-55, and `iso_unr`, CCD:34-41, read). Take w | l_i with l_i ≠ g₀, g₁.

- **If w is split:** `IsBCV` (DN:1270-1277) gives isoLoc = `locV i P w`. `NAut.locV_unr` (DN:638-639) gives unramified provided all of the following hold:
  - w ∉ Q i, which follows from `NData.SQ_l : v ∈ S i ∨ v ∈ Q i → v ∉ placesOver (l i)` (DN:142);
  - w is not above g_k (l ≠ g_k);
  - w is not above `if l = pde then pde' else pde` (primes differ).
- **If w is nonsplit:** `IsBCV`'s clause `¬IsSplitPl w → unr (isoLoc Pa w)` (DN:1275) gives it directly.

So the level of every point at localisation i is supported on S i ∪ Q i (places over g₀, g₁, pde or pde′, and Q i), and that set avoids l_i by construction (`S_def`, DN:144-145, also removes places above l_i). **`G2a` is asserted only where π_x is unramified at w.** It is not vacuous: X_i is nonempty (`neX`, DN:102).

**3b. Who must honour these fields.** They are fields of `NData`/`NAut`/the `adm1` datum, so each `D7` constructor must prove them.
- In `TPS/ExistsAutSpec.lean:46`, `locV_unr := galois_family_irreducible_alt …`. That is `AutUnr.locV_unr_m_alt` (`TPS/MLocVUnr.lean`, lines 16-43 read). It derives unramifiedness from `HypOutside` (forms fixed by the maximal compact outside gPl ∪ qPl), and uses `Sp.Q_eq` to identify qPl with Q i.
- Other `NAut` constructors found use `isEmptyElim i` (empty Loc; e.g. `…/GaloisGeometry/NotIsobaricRigid.lean:136`). I did not determine whether ExistsAutSpec is the root's constructor.

**3c. The listed problem primes.**
- l ∈ Q (twist packs): excluded at that localisation by `SQ_l`.
- l | d, l ∈ small (incl. 2), l = q: `G2a` *is* asserted there, if such an i exists. It is consistent because π_x is required unramified at w | l.
- One residual point: when l is ramified in E/F (`primeClass` ram2/ramQ/ramD, `Formalism/LocalRingCardinality/DataHost.lean:28-34`), the places w | l are nonsplit and ramified in E/F. `IsBCV` then demands that the base change of a unitary-group point be unramified there. That is a claim of `adm1` (Labesse base change, NODE-GALREP), not of G2a. I did not check it at places ramified in E/F.
- In the live consumer, l ∉ {q, d, small} anyway (NODE-TOPCORE §5).

**3d. Twists (Q4).**
- χ_i = `chi i 1` is ramified at Q i (`chi_ram_Q`, DN:157), and Q i is not above l_i (`SQ_l`). So χ₁ is unramified at l_i.
- Crystallinity of χ₁^{−1} at w | l is derived, not assumed: `crys_chi` in `CrysFromGTwo.main_alt_alt` (`TPS/MainAltAlt.lean:12-17`, read) shows χ₁ is a constituent of r_π, which is crystalline (needs `FontaineBcris`). r ⊗ χ₁^{−1} is handled by `crys_tw`.
- η_T is unramified at every w (`etaT_unr`, DN:613).
- μ_i: field `muUnr` (not opened).

## 4. Children

| # | name | file:line | statement | role | weight / status |
|---|---|---|---|---|---|
| 1 | `facts_of_galois_preconditions_of_cutRec` | TPS/CFacts.lean:45 | GaloisPreconditions + CutRec ⇒ NormChoiceFacts | fills `g2` | glue; read |
| 2 | `de_rham_points_weight_jumps_alt` | TPS/DeRhamPointsWeightJumps.lean:15 | tie0, adm1, adm2_alt, adm5, CutRec ⇒ G2a ∀ GoodR ∧ distinct jumps | constructor | core; read |
| 3 | `iso_unr_l` / `iso_unr` | CCD:43 / 34 | point parameter unramified at w ∣ l_i, l_i ≠ g_k | the guard | core; read |
| 4 | `crys_unram_of_lgc`, `lgc`, `isoRep` | CCD:82, 205; `isoRep` not opened | LGC at w ∣ l for Nc ⇒ crystalline + HT | assembly | core; read (isoRep statement only) |
| 5 | `CrysIffWD` (in `TieGal`) ← `tieGal_of_jumpsCard_of_deRhamPotSemistable` | DN:1343; SClose:38 | crys ⇔ dR ∧ WD unramified | Fontaine criterion | standard (Fontaine, Berger); proof not opened |
| 6 | `AutomorphicGaloisAdmissible` ← `galClose_alt` ← `CarUAlt` ← Row0b | TC/AutomorphicGaloisAdmissible.lean:133; GalRepRankTwo:133; WeightsConj:55; RecT.lean:6 | Galois reps with dR/HT and WD(D_pst) matching at w ∣ l for Nc parameters | the l-adic input | standard (Caraiani/BLGGT); proved in-tree via Row0b; `carU_of_star_alt` not opened |
| 7 | `loc_tie`, `locT` (D7 fields) | D7F:275, 239; DN:1376; LocTied.lean:11 | abstract IsCrysW ⇔ IsCrys over B ≅ Per.Bcris | definition tie | structure obligation of each D7 constructor (not traced) |
| 8 | `NAut.locV_unr` ← `locV_unr_m_alt` | DN:638; TPS/ExistsAutSpec.lean:46; TPS/MLocVUnr.lean | split places outside Q, g_k, pde* unramified | guard input | proved; partly read |
| 9 | `adm1` / `IsBCV` inert clause | DN:1275 | nonsplit places unramified | guard input | from Labesse BC (NODE-GALREP); not checked at E/F-ramified places |

## 5. Oddities

1. **Implicit guard.** `G2a` is literally quantified over every localisation prime l_i ≠ g₀, g₁ with no unramifiedness hypothesis. It is satisfiable only because the datum fields (`SQ_l`, `S_def`, `locV_unr`, `IsBCV`) keep the level of the points away from l_i. A reader of the statement alone would think it is false at ramified primes. It is not, provided those fields hold.
2. **The level depends on the localisation prime** through `if l i = pde then pde' else pde` (DN:145, 639). So the auxiliary prime moves when l_i = pde. This is consistent, but it means "the same forms" at different localisations need not have the same level.
3. **E/F-ramified primes.** At l ∈ {q, d, small}, `IsBCV` demands an unramified base-change parameter at nonsplit, ramified w | l. That should be checked against Labesse at ramified places (`adm1`). It is not used by the live `TopCore` call.
4. **`g4p : CuspidalGaloisUnramified' D` is `∀ i, UnusedSlot55 …` = `True`**, filled by `trivial` (SClose:23-24, 42; TC/TrivialLocalCondition.lean:89; `TPS/CuspidalGaloisUnramified.lean:33`). It is not used on the G2a path. It is noted because the name suggests content.
5. **Crystallinity at l for the non-geometric constructions.** It rests on Row0b's `nice` clause, whose proof for the theta-lift and limit constructions (interpolation of pst/WD) has not been opened by any node.

## 6. Coverage

Read:
- PROTOCOL; NODE-TOPCORE (all); NODE-GALREP (all); NODE-LIVEPATH:1-80; greps of NODE-BEYONDFL and NODE-LARGETW for g2 / crys.
- TPS/NormChoiceFacts.lean (all); TPS/DeRhamFamilyAway.lean (all); TC/TrivialLocalCondition.lean (all).
- DN:55-164, 510-717, 1262-1300, 1340-1420; DNL:495-525, 527-600, 690-735; D7F:76-140, 230-300; LocTied.lean (all).
- `Formalism/WeaklyAdmissibleFiltrations/Statement.lean`:125-135, 150-175; `QuotientHomNonvanishingBound.lean`:805-816; `OneSubPhiOntoOfFilZero.lean`:1-40.
- TPS/ImportsExtraMoreStatement.lean; TPS/ImportsExtraMore.lean; TPS/MainAltAltTer.lean; TPS/MainAltAlt.lean; TPS/CrysBridge.lean; `DecompositionData.lean`:150-200 (file-relative numbering); TPS/AdmissibleParameterEventually.lean:1-58; its Statement file; TPS/ImportsFurtherTail.lean:1-90.
- TPS/CFacts.lean (all); TPS/DeRhamPointsWeightJumps.lean (all); CCD:1-240; TC/AutomorphicGaloisAdmissible.lean:1-170; `AdmissibleTemperedUnramified.lean`:18-40; `GaloisStatementWeakOfFull.lean`:10-45; SumRepresentations.lean:60-80.
- TPS/GaloisPreconditions.lean; TPS/PartsGive.lean:10-60; TPS/GaloisRepIsGeometricAtAllPlaces.lean:1-45; TPS/GaloisRepIsGeometricOfLocalConditions.lean; TPS/SClose.lean; TPS/GalRepRankTwo.lean:100-147; TPS/WeightsConj.lean:1-85; TPS/ThetaLocalInputs.lean; TPS/LocalRepresentationTheoryHypotheses.lean.
- `SatakeParameters/PublishedInputsCombined.lean`; TPS/PublishedInputsCombined.lean:18-45; TPS/SOneRow.lean; RecT.lean:6.
- TPS/ExistsAutSpec.lean:20-70; TPS/GaloisFamilyIrreducible.lean; TPS/MLocVUnr.lean:16-43; TPS/BoundAtTwoThreeFamilyFon.lean:23-30; TPS/CuspidalGaloisUnramified.lean:33-36; RhoBar.lean:12-15; DataHost.lean (grep lines).

Greps run:
- `def (UpperTheory\.GalS\.)?G2a\b|structure CoreNormFacts|def DeRhamFamilyAwayAlt|structure NormChoiceFacts`;
- `structure NData\b|structure NAut\b|IsCrysW|locAutHodgeTateWeightsLevelZero|jumpsW|DeRhamJumpsDistinctCondition|InducesW`;
- `admG2_of_isRankR_of_lStar_lt`; `def admG2`; `AdmGTwoLarge`; `main_alt_alt` (admG); `CrysFromGTwo`; `loc_tie :`; `structure D7`; `LocTie`;
- `LocTheory|LocBridge|LocPrime`; `def IsCrys`; `LocRings`; `FontaineBcris`; `LocTied|LocAinf`; `Bcris|Acris|BdR|Ainf` defs;
- `NLinkE.main_alt_alt`; `g2 :=`; `eventually_congBound_of_facts`; `NormChoiceFacts` (file list); `FactsFAlt`; `de_rham_points_weight_jumps_alt`;
- `iso_unr_l|crys_unram_of_lgc|lgc`; `compatR`; `AutomorphicGaloisAdmissible|adm2_alt|tie0|adm5|isoRep|Nc`; `GaloisPreconditions|PointConditions'|RowsAAlt`; `RelA|CuspA|TieGal`;
- `tieLab :=|: RowsAAlt`; `thetaLocal_a_conditions_of_jumpsCard`; `a_close_main`; `automorphic_galois_admissible_of_theta_local_inputs|mergeP'_alt|ThetaLocalInputsAlt`; `car :=`; `HypothesesBridge.main`; `local_global_above_l`;
- `carU_of_finite_gl_recT|bridgeStar_alt`; `One.M.Row`; `SQ_l :=|locV_unr :=`; `ofDual_star_alt`; `galois_family_irreducible_alt`; `locV_unr_m_alt`; `structure Host`; `def PD`; `def Dcris`; `CuspidalGaloisUnramified'`; `CutRec`;
- `facts_of_galois_preconditions_of_cutRec|exists_good_cut_facts_tie4`; `g2 := g2|toCore :=|CoreNormFacts.mk|NormChoiceFacts.mk`.

Not opened:
- `isoRep`, `heckeGaloisRepQbar_conjugate_unique`, `tieGal_of_jumpsCard_of_deRhamPotSemistable`, `carU_of_star_alt`, `crys_chi`/`crys_tw`/`crys_coef`, `constituentCondition` details, `muUnr`, `Per.Bcris` construction, `CFinal.final_of_alt` up to the root;
- which `D7`/`NAut` constructor the root uses;
- Row0b's proof of the `nice`/`crys` clauses for theta-lift and limit representations.
