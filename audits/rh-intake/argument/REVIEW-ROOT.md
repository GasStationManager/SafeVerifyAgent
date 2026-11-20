# REVIEW-ROOT (reviewer of NODE-ROOT.md)

Source root: `.../scratchpad/art/lean/src`. Abbreviations as in NODE-ROOT (`TPS/`, `CB/`, `TGC/`), plus
`DL/` = `Development/AutomorphicArithmetic/DedekindLFunctions/`, `PC/` = `Development/AutomorphicArithmetic/PrimitiveCosets/`.
Nothing was compiled. Every `file:line` below is one I read.

## Verdict: NEEDS-DETAIL

The top three levels compose as the node says. Taking the children's *Lean* statements as black boxes, I could
write `everyCharacter` from `imprimitive`, `zeroFreeOn_of_tiedWin_cyc`, `level_gm_le_on_family_scales` (that is,
`core_gm`), `formB`, `TopG` and `supplyChi`. Most renderings are faithful. One part of the stated mechanism is wrong:
the Landau step does **not** use non-negative Dirichlet coefficients. The deduction of ZeroFreeAll from TopG is short
and correct. All of the RH-strength content sits in children that have not been opened (`core_gm`'s CoreAtH/gap
hypothesis, and TopG's production of ChainTied families for an *arbitrary* requirement G). So the root is understood,
but the argument as a whole is not.

## Checks against the Lean

**(1) Live path, and how the pieces compose.**
- `FinalTheorems.everyCharacter` = `everyCharacter_of_row galoisLocalGlobalStrong_recParameter`, and
  `everyCharacter_of_row h = every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)`
  (`CB/MainConclusion.lean:7-11`). The node cites `TPS/EveryCharacterOfLiteratureOfVWin.lean:810-814` for this. That
  range holds `every_character_of_literature_of_vWin` (`:811-814`), not `everyCharacter_of_row`. The citation is
  wrong; the content is right.
- `every_character_of_theta_integrals_local_matching` calls `Top.every_character_of_green_v_win`
  (`TPS/SiegelEisensteinSecondTermHypotheses.lean:69-74`). That is the Alt route, so the node is right.
  `plugAll`/`plugWin` (`CB/EveryCharacter.lean:8-19`) are not on the path.
- `every_character_of_green_v_win = imprimitive (zero_free_all_of_green_v_win hG hV h)` (`TPS/TopPlug.lean:11-18`).
  `zero_free_all_of_green_v_win` calls `zeroFreeAll_of_topG (la := 3/2)` with two arguments:
  `TopG := forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green hG) trivial trivial h` and
  `hS := fun ψ => supplyChi ψ (hV ψ)`.
- `zeroFreeAll_of_topG` (`CB/ZeroFreeAllOfTopG.lean:26-36`) instantiates `zeroFreeOn_of_tiedWin_cyc` (`TGC/TopWin.lean:90-93`)
  with the following:
  - `h112 := level_gm_le_on_family_scales` (`PC/LevelGmLeOnFamilyScales.lean:28-30` → `windowInequality_of_artinInputs`,
    `PC/WindowInequalityOfArtinInputs.lean:17-25` → `core_gm`, `PC/CoreGm.lean:12-15`);
  - `hB := formB` (`PC/Imports.lean:8-19`);
  - the window-scale family from `TopG la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)`. EFamC is read off the EAtH
    component of GChi with constant C = 4 (`:20-24`).
  - `imprimitive` (`CB/Imprimitive.lean:5-30`) is the routine Euler-factor reduction, and the node describes it
    correctly.

**(2) Definitions.**
- `ZeroFreeOn Q` (`TGC/ExplicitFormulaErrorOfHostConditions.lean:14`): every primitive ψ with Q ψ has L(s,ψ) ≠ 0 on
  Re s > 1/2. `ZeroFreeAll` (`:18`) is this with Q = True. This is faithful, including the remark about ζ(1).
- TopG (`CB/ZeroFreeAllOfTopG.lean:13-15`): faithful.
- HostExW (`ThinScalesIffHostBound.lean:118-122`): faithful, except that the scale must also satisfy `s.eps = eps`.
- VWinAt (`CB/ExistsPageN.lean:44-49`, with `VAt` `:41-42`, `VVle` `:12-17`, `WinPair` `:27-37`): faithful.
- FormBAt (`TGC/Window.lean:30-33`, with `HasWindows` `:7-8`): faithful. The hypothesis is: for every y there is a
  Y ≥ y with Gm ≤ x^θ on all of [Y, Y^la].
- FamilyClassConnected (`CB/DivinNOfHypV.lean:13-15`): faithful. eD, eL and ε₁ are chosen **before** ε.

**(3) The mechanism.**

*(a) Is the root argument correct?* `level_of_tiedWin` (`TGC/TopWin.lean:68-81`) runs as follows. Fix ψ and s with
Re s > 1/2, and put m = min(Re s − 1/2, 1/2). Pick ε with (eD+eL+7)ε ≤ m/2. This works because eD and eL do not depend
on ε (`TopWin.lean:30-32`). There is then one family that is ChainTied on its la-windows, so
Gm(x) ≤ x^{1/2+m/2} = x^θ on windows [Y, Y^{3/2}] arbitrarily far out, with θ < Re s. FormBAt then gives no zero at s.

Gm depends only on the level ⟨ψ⟩ (`TGC/ExplicitFormulaErrorOfHostConditions.lean:36-38`). It does not depend on ε or
on the family, so a single ε per s is enough. No uniformity in ε or in the level is needed, because each ψ is handled
separately. `core_gm` forces eD + eL ≥ 0 (`PC/CoreGm.lean:46`), so negative exponents cannot sneak in.

*(b) Which Dirichlet series, and what "positivity" really is.* **Mismatch.**
- `formB` goes through `level_family` (`PC/LevelFamily.lean:41-56`) to a `Deduction.CharFamily`
  (`DL/CharFamily.lean:24-36`): a finite family of characters with weights **a_i > 0**, and Gm = Σ a_i Re Gχ_i.
- `zeroFree_of_rpow_window` and `lemmaL` (`DL/LandauTheorems/ZeroFreeOfRpowWindow.lean:11-14`, `lemmaL.lean:13-22`)
  hold for **every** such family.
- The abstract kernel `landau_window` (`landauWindow.lean:83-84`) needs only two things beyond the window hypothesis.
  `PoleData` (`DL/LandauZeroFreeCriterion.lean:15-23`) asks that the Laplace transform have simple poles with nonzero
  residues, and *positive real residue at real poles*. `WindowHypU` (`:25-29`) is the window hypothesis.
- Non-negativity of the Dirichlet coefficients is neither assumed nor used.
- The positivity that does matter is this. Weights a_i > 0 mean poles of different L'/L at the same ρ cannot cancel.
  A real zero β gives Laplace residue a·m/(β(1−β)) > 0, which a one-sided upper bound forbids.
- The node's sentence "That is the positivity Landau's theorem needs", and the phrase "nonneg-coefficient Gm" in row 9,
  should be removed. (The coefficients are in fact positive for a trivial reason: the weights 1/(3o+1) are small. This
  is irrelevant.)

*(c) Is the windowed statement true?*
- The Lean form is `WindowHyp` (`DL/CharFamily.lean:41-45`): for every η there are arbitrarily large Y and an R ≥ 0 with
  Gm ≤ R on [Y, Y^{1+δ}] and ∫ R y^{−θ−1} ≤ Y^η. `windowHyp_of_rpow` derives it from the pointwise windowed bound.
- The proof is Landau's Taylor-coefficient (Pringsheim) method: `landau_window_key` bounds Φ^{(k)}(σ+iγ)/k! with
  k ≥ U (`landauWindow.lean:40-45`). That kernel concentrates in the window once σ is large relative to 1/δ.
- As a theorem, "fixed la > 1, one-sided bound on windows ⇒ no zeros above θ" is plausible and has the correct sign.
  It is **not** the textbook Landau theorem, which assumes the bound for all large x, so "standard (Landau)" needs
  that qualification.
- I did not check `landau_tails`, which is the step where the e^{2u} growth outside the window has to be beaten.

**(4) `True` / `trivial`.**
- `TopShapeAlt True True …` takes V = NR = True, and these are discharged by `trivial` (`TPS/TopPlug.lean:15`).
- In `shape_closed_link_n_of_green` the corresponding binders are `hVC` (V) and `nR` (NR) (`TPS/TopShape.lean:34`;
  for the order see `TPS/ShapeOf.lean:25-30`). **Neither appears in the proof body (`:35-55`)**. So `True` removes no
  content that the proof uses. Node oddity 3 is resolved.
- `imprimitive` passes `trivial` for Q = True, which is correct.
- I saw no other `True` on the root path.

## Mismatches (summary)
1. The positivity mechanism (node §Definitions on Gm, and table row 9): non-negative coefficients play no role. The
   positive weights and the positive real residue do.
2. The node calls FormB "standard (Landau)". It is a windowed, integral-hypothesis variant with its own proof
   (`landauWindow.lean`), and it should be listed as non-standard.
3. Wrong file for `everyCharacter_of_row`: the node cites `TPS/EveryCharacterOfLiteratureOfVWin.lean:810-814`, but the
   theorem is at `CB/MainConclusion.lean:7-8`.
4. HostExW: the node omits the condition `s.eps = eps` (`ThinScalesIffHostBound.lean:121`). Minor.

## Gaps
- None at this node: every step follows from the children's Lean statements.
- The real content is wholly delegated. TopG is quantified over **every** requirement G : FReq. So for any predicate G
  that good hosts on windows can meet, TopG promises ChainTied families inside G. Through `tiedCore_of_chainTied` and
  `core_gm`, ChainTied plus EAtH then yields Gm(x) ≤ x^{1/2+O(ε)}. The square-root bound must therefore come from
  HostGood + VVle (Sha) + HypsAlt + Green. Nothing at this node explains how.

## Expand next (ranked)
1. **`core_gm` / `Deduction.ch_core` / `tiedCore_of_chainTied`.** What are `gapA` and `errorBracketSizeWindows`? Which
   ChainTied clause (ErrWindows, `ch_top`'s inputs) yields `gapA ≤ x^{Cε}·err`? Is this hypothesis already equivalent to
   a square-root bound on ψ(x; ⟨ψ⟩)?
2. **`shape_closed_link_n_of_green` → `topDesWin`, and `designExists_of_tuSize_aux4n_litThin`.** How is a ChainTied
   family built for an *arbitrary* G? Which of LinkN/HypV/HostGood supplies the gap bound, and is any link vacuous?
3. **`supplyChi` / `supplyOfAdmOf` / `HostGood` (BoxW, QDq, EAtH.bdL).** Can hosts with |L'/L(1,χ)| ≤ 4 log x, shares
   error x^{−1+ε}, and real-zero-freeness for β > 1 − 1/400 be produced without assuming zero-free regions? Do
   WinPairs exist, or is VWinAt vacuous?
4. **`nonempty_hyps_definite_side_of_closed_bound`.** Are the ~45 HypsAlt fields genuinely satisfied, or is some field,
   such as `nRest : Closed (D3 3 𝒜) LinkN`, vacuous because the class is empty or degenerate?
5. **`vwin_of_row` / `vwin_of_hypotheses_H_E_alt`.** Where does a uniform Sha bound exp(x^ε/2) over all twists below
   x^401 of fields of degree about x^{2+8ε} come from?
6. **`landau_window` / `landau_tails`.** Confirm that σ is chosen depending on δ so that the out-of-window tails are
   beaten. This is lower priority: it is a plausible theorem.

## Escalations (ten-minute checks for an expert)
- E1. TopG (`CB/ZeroFreeAllOfTopG.lean:13-15`) is universal in the requirement G, and with G = GChi ψ it is the whole
  of GRH. Since ChainTied ⇒ CoreAtH ⇒ Gm(x) ≤ x^{1/2+O(ε)} (`PC/CoreGm.lean:12-15`), any proof of TopG implicitly
  proves square-root cancellation for every level that hosts can be adapted to. An expert should look at what
  `ch_core`'s gap hypothesis (`DL/LandauTheorems/ChCore.lean:343-351`) means in terms of primes, to see whether it is a
  disguised form of the conclusion.
- E2. Note for the record: the Landau step is not the classical one. It is
  `landau_window` (`DL/LandauTheorems/landauWindow.lean:83`), for arbitrary positively weighted character families
  under a windowed one-sided bound. The statement looks true. No escalation unless `landau_tails` fails.
- Nothing rendered at the root is false as literally read.
