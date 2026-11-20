# NODE-ROOT: `UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter`

Paths are relative to the source root `.../scratchpad/art/lean/src`. Abbreviations:
`TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`,
`CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`,
`TGC/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`.

## 1. Statement

The Lean says (`CB/EveryCharacter.lean:13-14`):

```lean
def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
    DirichletCharacter.LFunction χ s ≠ 0
```

In words: GRH for every Dirichlet L-function. For every modulus N ≥ 1 and every character χ mod N, L(s,χ) (the
Mathlib L-function: analytic continuation, with ζ for χ = 1) has no zero in Re s > 1/2, apart from the pole
s = 1, χ = 1. There are no project definitions to unfold here.

## 2. Argument (top three levels)

### Level 0: the wrapper
`everyCharacter_of_row h = every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)`
(`TPS/EveryCharacterOfLiteratureOfVWin.lean:810-814`). The structure `OpenLiteratureStatements`
(`:215-218`) has three fields: `caraianiLocalGlobalDual : One.M.Row`, `localLanglandsExists : Zero.LLC.RecTExists`
and `galoisRepOfPolarizedPairLit : One.M.Row`. Most of the "literature" theorems in this file, for example
`logDerivOne`, `heckeTateFunctionalEquation'` and `global_artin_reciprocity_of_literature` (`:219-260`), take `O`
and then ignore it: their bodies are closed terms proved elsewhere. So `O` is mostly a label, not a hypothesis.

`every_character_of_literature_of_vWin O hV` applies
`Lit.every_character_of_theta_integrals_local_matching P F hA hM hX hL hV` (`TPS/SiegelEisensteinSecondTermHypotheses.lean:69-74`). Its inputs:
- `P : UnitaryGroupThirdPlaceHypotheses`, from `published_results_eigen O` (`EveryCharacterOfLiteratureOfVWin.lean:666`);
- `F : ThetaLocalInputs`, from `published_results_first O` (`:727`);
- `hA : ThetaIntegralsAgree` and `hM : LocalMatching`, both from `theta_integrals_agree_and_local_matching_of_literature O`
  (`:565-566`), which is `PositivityTheory.ThKR.theoremK_head2 (eis_bl…) (siegel_weil_std…)`;
- `hX : CovolumeBoundOfX`, from `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` (about 15 arithmetic-geometry inputs);
- `hL : RecTExists`, the local Langlands parameter existence;
- `hV : VWin`.

### Level 1: three ingredients feeding the zero-free machine
`every_character_of_theta_integrals_local_matching` (`SiegelEisensteinSecondTermHypotheses.lean:69-74`) is
```
Top.every_character_of_green_v_win (green_of_regular P.greenRegularCharacters) hV
   (nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL (fun cDep => boundAtTwoThree_linked_of_recT …))
```
So its three ingredients are:
1. **Green** (`Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108-112`). For every prime g, every
   `LabelDatum g` and every d > 0 there is a map τ from polynomials over F_g to class functions on `Gn g d`, with
   these properties: it is injective on "prime labels" of degree d; each τ(P) is a cuspidal character of degree ∏_{i=1}^{d-1}(g^i − 1);
   and every cuspidal character is some τ(P). *I infer* that `Gn g d` is GL_d(F_g), so this is **Green's 1955
   parametrisation of the cuspidal characters of GL_d(F_q)**, a standard result. It is proved from
   `P.greenRegularCharacters`.
2. **VWin** (see (c) below).
3. **`Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)`**, produced by
   `nonempty_hyps_definite_side_of_closed_bound` (`SiegelEisensteinSecondTermHypotheses.lean:54-68`) from the theta and
   automorphic inputs. This is where `ThetaIntegralsAgree` and `LocalMatching` are used: they feed
   `test_vector_assembly_holds`, `fourier_coefficient_fit_of_join_alt` and `evaluation_grid_of_join`, which in turn give
   `RowRat`, the grid evaluation `EvLgG` and the open parameter statements, and then
   `hypotheses_nonempty_of_unramified_exponents_alt` builds the `HypsAlt` record.

### Level 2: from those three ingredients to a zero-free region (`TPS/TopPlug.lean:11-18`)
```
zero_free_all_of_green_v_win hG hV h :=
  h.elim fun h => zeroFreeAll_of_topG (la := 3/2) (by norm_num)
      (forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green hG) trivial trivial h)
      (fun ψ => supplyChi ψ (hV ψ))
every_character_of_green_v_win := imprimitive ∘ zero_free_all_of_green_v_win
```
This is the "Alt" twin of `plugAll`/`plugWin` (`CB/EveryCharacter.lean:8-19`). Those use `Hyps … DRS` and
`shapeWin`/`shape_of`, and the live chain does not use them.
- `shape_closed_link_n_of_green hG : TopShapeAlt True True N TopG` (`TPS/TopShape.lean:33-57`). `TopShapeAlt V NR N G`
  (`TPS/TopShapeAlt.lean:24ff`) is a long implication: for every family class 𝒜 with a twist selection and the ~45
  side conditions that are the fields of `HypsAlt`, together with V, NR and `N (D3 3 𝒜)`, G holds. `forall_goal_of_shape_of_hyps`
  (`TPS/ShapeOf.lean:31`) simply feeds the fields of `HypsAlt` (`TPS/Hyps.lean:22-90`) into it. So all of the content of
  `TopG` lives in `shape_closed_link_n_of_green`, which ends with `topDesWin`, and in the `HypsAlt` record.
- `topDesWin` (`CB/DesWin.lean:11-33`) says: if a family class has designs (`DesignExists`), satisfies `HypV`, and
  satisfies the nine "Link" closure properties (`LinkN, LinkEta, LinkIRR, SmallLevelRankEq, LinkDIVt, NuFull/MuRank,
  LinkG, LinkS, LinkGLOBAL`), then it is `FamilyClassConnected`.
- `supplyChi ψ : VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req` (`CB/SupplyChi.lean:8-16`, via `supplyOfAdm`,
  `CB/HostOfField.lean:20-27`, and `ShortNorms/supplyOfAdmOf.lean:13-135`).
- `imprimitive : ZeroFreeAll → EveryCharacter` (`CB/Imprimitive.lean:5-30`). This passes from χ to its primitive
  character: L(s,χ) = L(s,χ*) ∏_{p|N}(1 − χ*(p)p^{-s}), and each Euler factor is nonzero for Re s > 0. Routine glue.

### The definitions in mathematical terms
- **PChar** (`TGC/PrimePairSizeCondition.lean:7-11`): a *primitive* Dirichlet character (N, χ mod N, χ primitive).
  Note that the `PChar` at `Formalism/RealPlaceAnalysis/Complexify.lean:87` is an unrelated Prop with the same name.
- **ZeroFreeOn Q** (`TGC/ExplicitFormulaErrorOfHostConditions.lean:11-18`): every primitive ψ satisfying Q has
  L(s,ψ) ≠ 0 for Re s > 1/2. **ZeroFreeAll** = ZeroFreeOn (fun _ => True), i.e. GRH for all primitive characters,
  including ψ = 1 (ζ) at s = 1, where Mathlib's junk value ζ(1) = (γ − log 4π)/2 ≠ 0 makes the statement true.
- **Level, Level.cyc ψ, Gm** (`:7-41`, `:105-124`): a Level is a finite set of primitive characters closed under inverse,
  with a weight. `Level.cyc ψ` is the cyclic group ⟨ψ⟩ (made primitive), of order o, with weights 1/(3o+1). The
  function is Gm(y) = Gz(y) + Σ_{ξ∈⟨ψ⟩, ξ≠1} (3o+1)^{-1} Re gχ_ξ(y), where (`TGC/Analytic.lean:11-26`,
  `Formalism/StatementOC.lean:11-13`):
  - Gz(y) = Σ_{n≤y} Λ(n)(y/n − 1) − y log y + (1+γ)y;
  - gχ(y) = Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L'/L(1,χ).

  These are Riesz-smoothed Chebyshev functions with their main terms removed. *I infer*: the coefficients
  Λ(n)(1 + (3o+1)^{-1} Σ_{ξ≠1} Re ξ(n)) are ≥ 0, because the sum over the group is o or 0 for (n,N) = 1. That is the
  positivity Landau's theorem needs.
- **FormB / FormBAt la** (`TGC/Window.lean:30-33`): for θ ∈ (0,1), if Gm(x) ≤ x^θ on windows [Y, Y^la] for
  arbitrarily large Y, then no character in the level has a zero with Re s > θ. `Comparison₂.formB` proves this for every
  level (`PrimitiveCosets/Imports.lean:8-20`) via `Deduction.zeroFree_of_rpow_window`
  (`DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11-14`).
- **FamCore / FamP** (`Formalism/SharpRestriction/FamCore.lean:71-137`, `ParConsts.lean:31-70`): a "family". For each
  scale x in an unbounded set `Win` there is a nonempty index set `Ix x` and, for each index, a datum `D x i : D7`.
  *I infer* that a D7 is a number field E with a "host" (primes q, d, g_0, g_1, an abelian group A and a frame) plus
  size data `L x i`, many uniformity constants, and parameter choices.
- **FamClass / Closed 𝒞 P** (`ParamsHeightRankConstant.lean:157-161`): a FamClass is a predicate on families. `Closed 𝒞 P`
  says: for all sufficiently small ε there is a threshold K such that every family in 𝒞 that is `Large K CH` satisfies
  P. It is an "eventually for large families" quantifier.
- **LinkN Fm** (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:41-49`): eventually in x, for each datum with
  `ShaFinOdd`, a weighted η-sum over twisted places satisfies η ≤ dZ0·(C(f·m·b·L² + log²x·Nc) + Σ_l vvTerm(l)). Here
  vvTerm is the Sha-length term, the same quantity that VVle bounds.
- **HypV Fm** (`CB/DivinNOfHypV.lean:10-11`): eventually, each host field E = (D x i).host.E satisfies
  `VVle E t (√b)`, where t is the rank and b the scale parameter.
- **FamilyClassConnected ℰ** (`CB/DivinNOfHypV.lean:13-15`): there are eD, eL and ε₁ > 0 such that for every ε < ε₁ some
  family in ℰ satisfies `ChainTied Fm eD eL …` at every x ∈ Win beyond some x0.
- **ChainTied** (`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97-114`): a 16-clause existential. It gives
  a host datum at x with Frobenius/Artin data (`TieArith`, `Ident`), size data, error windows, `ErrWindows`, `BNBounds`,
  `GrowthInequalityRemainingHyps`, `CostWindows` and `RestSize`. These are the hypotheses of the Chebyshev bound.
- **FReq, GChi ψ** (`CB/Supply.lean:10-43`): a requirement on (scale, frame, host, TT, t). `GChi ψ` asks for
  `EAtH (Level.cyc ψ) H TT x ε 4` and `VVle H.E t (√b)`. `(GChi ψ).cls la` is the class of families with windows of
  exponent la all of whose members satisfy GChi ψ.
- **EAtH Λ H TT x ε C** (`TGC/ExplicitFormulaErrorOfHostConditions.lean:144-150`): the host is adapted to the level.
  The order matches, the level's characters are "kept", TT has equidistributed shares (error x^{-1+ε}), the character
  values are bounded pointwise, and |L'/L(1,χ)| ≤ C log x for the relevant primitive χ.
- **HostExW la P** (`Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:118-127`): for
  every ε ∈ (0,1/52) there are constants and a window system `S : Scales la` such that every large scale s in S
  admits ranks R, a host H and a prime q0 with `RankVal`, `HostGood` and P. `HostGood` (`:102-114`) is a long list.
  It includes `BoxW`, which gives the real-zero-free statement L(β,χ) ≠ 0 for β > 1 − 1/400 for the host's real
  characters (`:96-100`).
- **TopG** (`CB/ZeroFreeAllOfTopG.lean:13-15`): for every la > 1 and every requirement G, if HostExW la G.req holds
  and every family in `G.cls la` satisfies HypV, then `G.cls la` is FamilyClassConnected. In words: wherever good
  hosts exist on windows, one can build a family of them that satisfies the Chebyshev chain.
- **Hyps/HypsAlt** (`TPS/Hyps.lean:22-90`): a Type-valued record of about 45 fields. It holds a family class 𝒜, a raw
  selection σ, a design-existence function `hEx : MinkDiv → ExS 𝒜 cT`, and closure facts about rows, twists,
  indefinite realisations, class-number formula, `LitThin`, Wu decay, counting constants, Theorem S selections, genus
  mass `GenusMassAt D 2`, `MassRatioUnderVolume`, `RealPlaceSecondLayerConditions`, and finally `nRest : N (D3 3 𝒜)`,
  which here is `Closed (D3 3 𝒜) (LinkN)`. `DRS`/`DefiniteSideCondition` (`TPS/DefiniteSideCondition.lean:25-40`) is a
  definite-side row condition (DivTied3 ⇒ RowsU). It is too deep to unfold here.

## (b) Where the analytic number theory happens

`zeroFreeAll_of_topG` (`CB/ZeroFreeAllOfTopG.lean:26-36`) calls
`zeroFreeOn_of_tiedWin_cyc` (`TGC/TopWin.lean:90-94`) with `Fam := FamP` and `Tied := ChainTied`. For each primitive ψ
it uses the level `Level.cyc ψ` and three facts:
1. `ChebyshevInequalityOnWindows` (`TopWin.lean:25-27`): for any family that satisfies EFamC (the hosts are adapted to the
   level) and is ChainTied on its windows, eventually Gm(x) ≤ x^{1/2 + (eD+eL+7)ε} for x ∈ Win. This is supplied by
   `level_gm_le_on_family_scales` (`PrimitiveCosets/LevelGmLeOnFamilyScales.lean:28-30`), which goes through
   `windowInequality_of_artinInputs` (`PrimitiveCosets/WindowInequalityOfArtinInputs.lean:18-27`) to **`core_gm`**
   (`PrimitiveCosets/CoreGm.lean:12-15`): if a host satisfies EAtH and CoreAtH at x, then Gm(x) ≤ x^{1/2+(eD+eL+7)ε}.
   `core_gm` in turn rests on **`Deduction.ch_core`** (`DedekindLFunctions/LandauTheorems/ChCore.lean:343-351`). That
   lemma gives GmA ≤ x^{1/2+(C+3)ε} + SigA from host facts and a hypothesis of the form
   "`gapA … ≤ x^{Cε}·errorBracket`" for u ∈ A0.
2. `FormB` (Landau-type, above): one-sided windowed bound ⇒ zero-free half-plane.
3. `ChebyshevInequalityAtWindowScale la` (`TopWin.lean:29-31`): for every small ε there is a family that satisfies
   EFamC, has la-windows and is ChainTied. This comes from `TopG`, applied with G = GChi ψ, `hS = supplyChi ψ (hV ψ)`,
   and `HypV` read off the `VVle` component of GChi.

`level_of_tiedWin` (`TopWin.lean:68-82`) then puts these together. Fix s with Re s > 1/2 and choose ε so that
1/2 + (eD+eL+7)ε < (1/2 + Re s)/2. The family gives Gm(x) ≤ x^θ' on windows [Y, Y^{3/2}], and FormB gives no zeros
with Re > θ', in particular none at s. **So the mechanism is positivity plus Landau's theorem applied to a one-sided
Chebyshev bound with square-root error, not a contradiction derived from an assumed zero.** All of the RH-strength
content is the bound Gm(x) ≤ x^{1/2+O(ε)} on windows, which (1) produces from `CoreAtH`/`ChainTied` (ultimately from
the `gapA` hypothesis of `ch_core`), and the existence of families that meet those hypotheses, which (3) produces from TopG.

## (c) Heavy inputs, ranked

| # | Name | file:line | Statement (math) | Role | Weight |
|---|---|---|---|---|---|
| 1 | `UpperTheory.Comparison₂.core_gm` and `Deduction.ch_core` | `PrimitiveCosets/CoreGm.lean:12`; `DedekindLFunctions/LandauTheorems/ChCore.lean:343` | If a host field at scale x satisfies EAtH and CoreAtH (size/arith/thin-scale data plus a gap bound gapA ≤ x^{Cε}·err), then the smoothed, level-weighted Chebyshev remainder satisfies Gm(x) ≤ x^{1/2+O(ε)} | the square-root bound itself | core |
| 2 | `UpperTheory.Top.shape_closed_link_n_of_green` (→ `topDesWin`, `designExists_of_tuSize_aux4n_litThin`, `link_gl`, `closed_linkIRR_of_join_count` …) | `TPS/TopShape.lean:33`; `CB/DesWin.lean:11` | Given Green and any `HypsAlt` record, TopG holds: every class of good-host families on la-windows contains, for each small ε, a ChainTied family | builds the families whose hosts satisfy the hypotheses of (1) | core |
| 3 | `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` | `TPS/SiegelEisensteinSecondTermHypotheses.lean:54` | Theta/unitary-group inputs, ThetaIntegralsAgree, LocalMatching, CovolumeBoundOfX, RecTExists and a linked BoundAtTwoThree ⇒ a HypsAlt record (about 45 fields) exists | supplies the side conditions of (2) | core |
| 4 | `UpperTheory.One.vwin_of_row` → `automorphic_window_of_inputs` → `V.v_window_of_literal_automorphy_n` → `vwin_of_hypotheses_H_E_alt` | `…/DenseThresholdCases/VwinOfRow.lean:4`; `TopMainZj.lean:71`; `WindowBoundOfLiteratureLevel.lean:33,22` | Galois representations for polarized regular algebraic cuspidal π on CM fields (Row0b), base change and literature bundles ⇒ VWin | supplies the Sha bound | core |
| 5 | `UpperTheory.Top.supplyChi` / `UpperTheory.T3.supplyOfAdmOf` / `hostOfFieldOf` | `CB/SupplyChi.lean:8`; `ShortNorms/supplyOfAdmOf.lean:13` | VWinAt ψ 401 ⇒ on 3/2-windows there exist good hosts adapted to ⟨ψ⟩ that satisfy the Sha bound | host existence (HostExW) | core |
| 6 | `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree` / `LocalMatching` (via `PositivityTheory.ThKR.theoremK_head2`) | `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:581-598`; `EveryCharacterOfLiteratureOfVWin.lean:565` | LocalMatching: every unitary-pair triple (F, E, σ, Geo σ a a', chars X, ω, ω′) admits matched local data. ThetaIntegralsAgree: theta integrals decay; matched data have one constant and coinvariants; tower-step relations StepAlpha/StepBeta relate theta constants at (a, b+2) and (a, b) by a nonzero factor times a partial L-value charL(ν, S₀, (a−b−2)/2 + 1). *I infer*: Siegel–Weil / Rallis inner-product tower relations. | inputs to (3) | standard? (theta correspondence; needs check) |
| 7 | `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter : Row0b recT` | `Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6` (body: `galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK`) | Row0b (`TypeConditions/WeightsConjBis.lean:69-73`): for every CM field E, every prime l, every ι and every regular algebraic cuspidal π of GL_a(𝔸_E) in a polarized pair with χ, there is a continuous semisimple r : G_E → GL_a(Q̄_l) with local-global compatibility away from l (relative to recT), Hodge–Tate weights given by the infinity type, conjugate-self-duality of weights, and crystalline/de Rham/pst behaviour above l (PropsB) | the input of the VWin branch | standard (Harris–Taylor, Shin, Chenevier–Harris, Barnet-Lamb–Gee–Geraghty–Taylor, Caraiani). It is proved here *via a theta lift*, which is unusual. |
| 8 | `GlobalTheory.GreenBridge.green_of_regular` | `SiegelEisensteinSecondTermHypotheses.lean:73` (use site) | Green's parametrisation of cuspidal characters of GL_d(F_q) | input to (2) (LinkIRR) | standard (Green 1955) |
| 9 | `Comparison₂.formB` / `Deduction.zeroFree_of_rpow_window` / `lemmaL` | `PrimitiveCosets/Imports.lean:8`; `ZeroFreeOfRpowWindow.lean:11` | Landau: a windowed one-sided bound on the nonneg-coefficient Gm gives a zero-free half-plane | the deduction step | standard (Landau), verify the windowed form |
| 10 | `UpperTheory.Top.imprimitive`, `zeroFreeOn_of_tiedWin_cyc`, `level_of_tiedWin`, `forall_goal_of_shape_of_hyps` | as cited | glue | | glue |

**What VWin/VWinAt ψ 401 asserts** (`CB/ExistsPageN.lean:14-49`). Fix a primitive ψ, ε ∈ (0, 1/52) and any choice of
e(x) with x^{2+8ε} ≤ 2^{e(x)} ≤ 2x^{2+8ε}. Then there are J ≥ 1 and X0 such that for all X ≥ X0 and all prime pairs (q, d)
that are a `WinPair` at scale X^{1/J}, the following holds. (A WinPair means q ≡ 3 mod 8, d ≡ 7 mod 16, log q ≈ Y^{ε/5},
log d ≈ Y^{ε/5} log²Y, q | d+1, and every odd prime p ≤ Y^{ε/5} divides d+1.) There is Y ∈ [X^{1/J}, √X] such that for
all x ∈ [Y, Y²], every number field E with `IsChiField ψ e(x) q d E` satisfies `VVle E ⌊x^401⌋ √(exp(x^ε))`.
`IsChiField` means E embeds in a cyclotomic field Q(ζ_N) with 2^{e+2}, ψ.N, q, d | N as the fixed field of
{a : a ≡ ±1 mod 2^{e+2}, ψ(a) = 1, (a/q) = (a/d) = 1}. `VVle E t B` means: for all primes l and twists 0 < e < t,
Sha¹(G_{E,S_l}, Q_l/Z_l(−e)) has finite Z_l-length, and Σ_{l∈S} log l · Σ_{e<t} len Sha_l(e) ≤ B for every finite set S
of primes (`Formalism/GaloisCohomology/Statement.lean:54-78`).
*I infer*: this is a uniform upper bound exp(x^ε/2) on the total "Tate–Shafarevich size" of all Tate twists up to
x^401 of very large abelian fields of degree about 2^{e} ≈ x^{2+8ε}. By Lichtenbaum/Bloch–Kato-type formulas such sizes are
tied to special values ζ_E(1−e) and ζ_E(e). It is very strong.
`vwin_of_row` needs Row0b (Galois representations) and `BaseChangeIdentities.baseChangeN`, and through
`v_window_of_depth_zero_residual_bc_cm` the bundles LitLocAlt (Bernstein–Zelevinsky, Moy–Prasad, Green …),
LiteratureAutomorphyHypothesis (Jacquet–Shalika, Clozel purity, Artin reciprocity, …), Galois-cohomology literature
and the CM/abelian bundle. The actual proof is `vwin_of_hypotheses_H_E_alt`, which goes through Kato-type automorphy
counts (`count_i_of_printed_bound_k_kato_automorphy`, `countII_and_countIII…`, `count_v…unitary_lift`); I did not open these.

## (d) The constants 401 and 3/2

- **401**. VWinAt is used with Ct = 401 so that the Sha bound covers all twists e < ⌊x^401⌋. Inside
  `supplyOfAdmOf` (`ShortNorms/supplyOfAdmOf.lean:131-134`) the VVle bound from VWinAt is weakened with `VVle.mono` to the
  host's own rank t = R.t. This uses `eventually_rank_le_rpow_of_lt_one_div_fiftytwo`
  (`CB/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5-7`): R.t ≤ x^400 for large x. So 401 is simply "any exponent
  above the rank bound 400". The 400 comes from `RankVal` (not opened), and is unrelated as far as I can see to the
  1 − 1/400 in `BoxW.real_ne_zero`.
- **la = 3/2** is the window exponent. `winPairs` (`CB/WinPairs.lean:5-8`) turns VWinAt's ranges Y ≤ x ≤ Y² (with
  Y ≥ X^{1/J}) into windows Z ≤ x ≤ Z^{3/2}. `supplyOfAdmOf` therefore gives `HostExW (3/2)`, and `zeroFreeAll_of_topG`
  is called at la = 3/2 (with 1 < la). The value is not otherwise significant: FormB holds for every la > 1.
- **1/52** bounds ε everywhere (`HostExW`, `VWinAt`, `HType`). Its origin was not traced.

## 4. Oddities

1. The live chain uses the `Alt` variants (`HypsAlt`, `DefiniteSideCondition`, `TopShapeAlt`,
   `shape_closed_link_n_of_green`, `forall_goal_of_shape_of_hyps`). The `plugAll`/`plugWin`/`Hyps`/`DRS`/`shapeWin` route in
   `CB/EveryCharacter.lean` is parallel and not on the path from `everyCharacter`.
2. `OpenLiteratureStatements` holds three fields, two of them the same type `One.M.Row`, and is built as
   `⟨h, recTExists, h⟩`. Most theorems "of_literature O" ignore O (`EveryCharacterOfLiteratureOfVWin.lean:219-260`).
   The wrapper name "Open…Statements" suggests hypotheses, but everything is discharged.
3. In `zero_free_all_of_green_v_win`, V and NR in `TopShapeAlt True True …` are `True` and are discharged by `trivial`.
   A reviewer should check that these slots are not meant to carry real hypotheses.
4. The whole RH-strength content reduces to the per-host bound Gm(x) ≤ x^{1/2+O(ε)} (`core_gm`), that is, square-root
   cancellation in a smoothed ψ(x; ⟨ψ⟩), derived from host data. The key hypothesis of `ch_core` is a "gap" bound
   `gapA ≤ x^{Cε}·errorBracket`. Where that bound comes from (the `CoreAtH` fields / `ChainTied` clauses
   `ErrWindows`, `GrowthInequalityRemainingHyps`, `ThinScales`) is the decisive question.
5. VWin asks for finiteness of Sha¹(G_{E,S}, Q_l/Z_l(−e)) for all e up to x^401 and all l, with a uniform total bound. This
   is extremely strong for fields of degree about x^{2+8ε}, and it is supplied by an automorphy/Galois-representation route
   (Row0b proved via a theta lift). Worth expert scrutiny.
6. `ZeroFreeAll` covers ψ = 1 at s = 1. That case is true only because of Mathlib's convention for ζ(1); it is harmless.
7. There are two unrelated `PChar` definitions (`Formalism/RealPlaceAnalysis/Complexify.lean:87` is a Prop about
   matrices). The one used is `Formalism.HC.PChar`.
8. `Closed 𝒞 P` is only "for all large-enough families in 𝒞". If a class 𝒞 is empty for some ε, Closed is vacuous, while
   FamilyClassConnected requires existence (`DesignExists` in `topDesWin`). The existence side therefore carries weight.

## 5. Coverage

Read: `PROTOCOL.md`; `TPS/EveryCharacterOfLiteratureOfVWin.lean:200-260,565-568,790-814`;
`TPS/SiegelEisensteinSecondTermHypotheses.lean:1-77`; `TPS/TopPlug.lean` (all); `TPS/TopShape.lean:1-57`;
`TPS/Hyps.lean:1-90`; `TPS/ShapeOf.lean:1-33`; `TPS/TopShapeAlt.lean:20-40`; `TPS/DefiniteSideCondition.lean:20-40`;
`CB/EveryCharacter.lean`, `CB/ZeroFreeAllOfTopG.lean`, `CB/ExistsPageN.lean:1-80`, `CB/Supply.lean:1-46`,
`CB/DivinNOfHypV.lean:1-40`, `CB/SupplyChi.lean`, `CB/Imprimitive.lean:1-30`, `CB/HostOfField.lean:1-27`,
`CB/DesWin.lean:1-33`, `CB/WinPairs.lean:5-11`, `CB/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5-11`;
`TGC/ExplicitFormulaErrorOfHostConditions.lean:1-165`; `TGC/TopWin.lean:1-140`; `TGC/Window.lean:1-45`;
`TGC/Analytic.lean:1-40`; `TGC/PrimePairSizeCondition.lean:1-20,30-80`; `TGC/TopDefs.lean:1-30`; `TGC/Landau.lean:530-545`;
`Formalism/StatementOC.lean:1-25`; `Formalism/SharpRestriction/FamCore.lean:60-137`; `ParConsts.lean:25-70`;
`ParamsHeightRankConstant.lean:155-170`; `GlobalTheoremInputs.lean:35-60`; `GlobalSchurBounds/TieGlobal.lean:90-116`;
`PrimitiveCosets/{LevelGmLeOnFamilyScales.lean:1-38, Imports.lean:1-20, WindowInequalityOfArtinInputs.lean:1-40,
CoreAtH.lean:1-48, CoreGm.lean:1-40}`; `DedekindLFunctions/LandauTheorems/ChCore.lean:343-362`,
`ZeroFreeOfRpowWindow.lean:11-22`; `ThinScalesIffHostBound.lean:90-135`; `NonGaloisDescent/LabelDatum.lean:100-115`;
`Formalism/GaloisCohomology/Statement.lean:50-80`; `WeilTensorModels.lean:560-604`;
`TypeConditions/WeightsConjBis.lean:40-90`; `ShortNorms/supplyOfAdmOf.lean:13-135`;
`DenseThresholdCases/{VwinOfRow.lean, TopMainZj.lean:1-77, WindowBoundOfLiteratureLevel.lean:1-37,
TemperedProductOfSquareIntegrable.lean:205-215}`.

Not opened: the bodies of `ch_core` (beyond its statement), `lemmaL`, `formB`'s `level_family`, `topDesWin`'s
link lemmas, `designExists_of_tuSize_aux4n_litThin`, `nonempty_hyps_definite_side_of_closed_bound`'s callees,
`hypotheses_nonempty_of_unramified_exponents_alt`, `galoisRepresentations_of_thetaLift`/`tLiftK`, `theoremK_head2`,
`vwin_of_hypotheses_H_E_alt`'s callees, `UnitaryGroupThirdPlaceHypotheses`, `ThetaLocalInputs`, `CovolumeBoundOfX`,
`RankVal`, `HostGood` subclauses, `IsTriple`/`IsMatched`/`StepBeta` definitions, `Gn`/`IsCusp` in LabelDatum.
