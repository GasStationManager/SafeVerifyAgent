# NODE-LOCALDIV: the local divisibility theorem at an inert prime (`stmt_proved`)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `MV/` = `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/`
- `UTS/` = `Formalism/ThetaLogCoordinates/UniformThetaSubstitution/`
- `PL/` = `Formalism/LocalToGlobal/GroupLattices/PendingLemmas/`
- `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`

The brief's line references are slightly off. `FGS:529` is `LowAt`, not `SysTw`; `SysTw` is in `GG/ModelsOK.lean` (see NODE-TWU).
The 13-clause package `admitted` is at `FGS:771`, `LowTermBound` at `FGS:708` and `KernelCommutationUpToUnits` at `FGS:683`.

## 0. Verdict (short)

`stmt_proved` (`MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:107`) is a coherent local theorem, and I can reconstruct its proof on paper.
It has three layers, and each layer is either proved in the tree or is a clearly stated hypothesis (`admitted`).

1. **Coefficient bound (where the arithmetic gain comes from).**
   - Setting: a power series in Lubin–Tate coordinates of the height-2 formal group. After the coordinates are rescaled by ϖ (ϖ^{p²−1} = p), the series lies in the ring
     O[[Z]][hh/p], where hh = Σ u_s·S_s^p·S_{s+1} is a fixed "Gaussian" form (Dwork-type factorisation, `RestGc`).
   - Its **derivatives** (n!·coefficient) along products of minors then have valuation
     ≥ v_p(a!) − a/(p²−1) − #(hh-factors) ≈ γ_p·a − #(hh-factors).
     Here γ_p = p/(p²−1) = 1/(p−1) − 1/(p²−1) (`GammaIdentity`, `GrowthSums/StatementA.lean`).
   - The number of hh-factors of degree p^e (e odd) is at most min(a/p^e, cap). This gives
     gain ≥ Σ_{e odd} max(0, a/p^e − cap) − (log loss).
   - **The exponent is a Legendre valuation v_p(a!) minus the convergence-radius cost a/(p²−1) of the height-2 Lubin–Tate coordinate.**
     The split into odd e comes from where the Gaussian's monomials sit: they have degree p^{2l+1}.
2. **Transfer.**
   - The family's chain map is a finite sum of such derivative pairings (`ExpansionEquality`). Integral forms pair into the integral lattice (`adm7`).
   - So one chain step applied after one Hecke operator gains that coefficient bound.
3. **Iteration.**
   - A Rallis-type commutation relation (Hecke at level j+1 ∘ chain = chain ∘ Hecke polynomial at level j) is derived from the explicit lattice shape of the kernel (`adm5`, `adm6`).
   - It lets each of the m steps contribute its own gain. Summing the gains gives `LowTermBound`.

My hand checks on toy kernels (§4) agree with the Lean inequality and are tight up to the logarithmic loss term `de`. The loss term is necessary: without it the inequality is false in the smallest case.
I did not find a normalisation that makes the bound cheap. Two normalisations remain unverified (§5, items 4–5).
The arithmetic weight of (P) is not in `stmt_proved`. It sits in the clauses that the instance must satisfy, chiefly:
- `adm2`/`adm2b`: the actual global theta series, expanded at the supersingular CM point, has the form exp(−Gaussian)·(LT-integral);
- `ExpansionEquality`: the family's own chain is that theta integral.

## 1. Setup (the local mathematics)

**Prime and field.**
- p ≥ 5 is prime (`Std.five_le`, `FGS:89`) and inert in an imaginary quadratic K = ℚ(√−d) (`GL3Theta.InertK`: (−d/p) = −1, `GlobalSchurBounds/GL3Theta.lean:115`).
- K0 = Frac W(F̄_p) (`FGS:113-118`), with Frobenius σ.
- The coefficient field Kc (ℂ_p on the live path) has an element ϖ with ϖ^{p²−1} = p, so v(ϖ) = ρ_p := 1/(p²−1).

**Formal group.**
- logF(X) = Σ_j X^{p^{2j}}/p^j (`FGS:126`). This is the logarithm of the height-2 Lubin–Tate (Honda) formal group over Z_{p²} with uniformiser p, i.e. the formal group of a supersingular elliptic curve.
- On the live path that curve is the CM curve g.W with good reduction (`IsModelU`, `GL3Theta.lean:46`). `LTIso g` identifies its formal group with this one (`PL/CoeffOneLNe.lean:123`).
- The twisted log series is sSer_s = Σ_l (−1)^l X_{s−2l}^{p^{2l}} (`FGS:200`), with positions s ∈ ℤ/n' (n' even, the Frobenius orbit).

**"Simeq" and the pairing.**
- f ≃ g means two things (`FGS:139`): f − g has no constant term, and exp((f−g)∘logF) has W-integral coefficients.
- `BeProp be` (`FGS:147`): be(X,Y) is biadditive up to ≃, and be(αX, Y) ≃ be(X, σ(α)Y) for α ∈ W(F_{p²}). This is a hermitian pairing of the formal group into Ĝ_m, written in log coordinates.

**`Sys p`, a formal-group system (`FGS:264`).** Its data:
- G (`GAtP`, `DataG.lean:166`): a DVR O ⊂ Kf with places v, local lattices and arithmetic groups. M = Γ-equivariant functions from lattice tuples to the weight-λ lattices (algebraic modular forms of weight λ = lam0).
- Fl (fills): the weights a, b, w, the tops TT, t, the number of steps mm = m.
- Lv: levels j = 0..m with spaces Fm_j, lattices Int_j and Hecke operators Tm.
- Ch: a chain Kz_j : Fm_j → Fm_{j+1}, with chainK_m = Kz_{m−1}∘…∘Kz_0.
- `std` (numerical standing hypotheses), a uniformiser vp with p ~ vp^{eO}, stabiliser bounds dG_j ≥ v_p(#Stab), and unitary bases om.

**`Pend X`, the pending theta datum (`FGS:447`).** Its data:
- Kc ⊇ Oc, a rank-1 valuation ring;
- the pairing be;
- representatives Rep_j of Γ-classes of lattices;
- the kernels ThA(La, La') ∈ Kc[[x_e, y_e]], with ThF = linear change of variables of ThA;
- a bilinear map DelF_j(G, f) ∈ Xsp_{j+1};
- lengths `len`, and an "indicator" map Xi.

From these:
- the kernel integral is ker_j(La, La')(G) = p^{Σ_v vm(len_j − len_{j+1})}·DelF_j(G, ThF) (`FGS:515-520`);
- `ExpansionEquality` (`FGS:566`) asks Kz_j F(c', L') = cK·Σ_{La∈Rep} Stab(La)^{−1}·ker_j(La,(c',L'))(F(La)), with cK a unit.

**What the "coefficients" are.**
- applyD(P, f) = Σ_n (∏ n_x!)·coeff_n(f)·P_n (`FGS:256`). This is the pairing ⟨P(∂), f⟩ at 0, i.e. **derivatives, not raw coefficients**.
- The operators P are products of column minors PI_j(I, i0) = ∏_{v,s,c} p^{colExp}·det(Σ_a Y·X) (`FGS:405-420`). This is the highest-weight (pluriharmonic) polynomial of the Young diagram ν_{j+1}.
- On the live path DelF is exactly such a pairing: DelF(G, f) = Σ_n derAt(n, f)·coeff_n(polDel G), with derAt = n!·coeff_n (`PL/DetYtMatNeZero.lean:100-170`).
- "Coefficient bound" therefore means a lower bound for v(D^λ Θ(0)), where Θ is the kernel and D^λ a determinantal differential operator.

**Hecke operators.**
- Level 0: yv v F(L) = p^{ArV_v}·Σ_{L'' at distance r} F(L with L_v replaced by L''), with ArV = Σ_s Σ_{i<r} λ_{s,i} (`DataG.lean:91,148`; `Ar`, `UnramifiedQuadraticSetting.lean:124`).
- Level j: Tt v i j = p^{Nprime(i)}·Tm (`FGS:331`), with Nprime(i) = Σ_{s even} Σ_{a≤i} λ_{s,a} + i·Σ_{s odd} w_j(s) (`FGS:72`).
- Zop = Σ_{l≤r} (−1)^l cl_l·Ttu(r−l) (`FGS:352`) is a Hecke polynomial at level j+1. Its coefficients cl_l are complete symmetric functions of the new Satake parameters m·p^{(n'/2)(t−2x)} (`FGS:339-350`).

**The numbers.** Write al_s = λ_{s,1} − λ_{s,2} for s ∈ TT (the weight gap, ≈ a on the live path) and cap_s = ν_{j,s,2 or 1} (`FGS:36-40`).
- gB = γ_p Σ_{TT} al − Σ_{s∈TT odd} Σ_{e odd} min(al_s/p^e, cap_{s+e}) − de (`FGS:57`)
- gA = Σ_{TT} Σ_{e odd, e∉dSet(s)} max(al_s/p^e − cap_{s+e}, 0) − de (`FGS:66`)
- Pr = Σ_{s odd}(r·w_j(s) + Σ_{lowest r} λ_s) + n'·r·j(t+1)/2 (`FGS:81`), which is ≥ 0 (`PrNonneg`)
- de = O(NN²·log_p(al, lsz)) (`FGS:47`)
- alEven = Σ_{s∈TT even} al_s (`FGS:355`)

## 2. The 13 clauses of `admitted` (`FGS:771`)

| # | clause (`FGS` line) | mathematical statement | tag |
|---|---|---|---|
| 1 | `adm1` :546, `DworkLemma` :225 | Dieudonné–Dwork criterion: exp(P) is W-integral ⇔ P^σ(X^p) − pP ∈ pW[[X]] (p ≠ 2). It does not depend on X, Y; proved in the tree (`positivity_condition_holds` → `sx_dwork`, `MV/PositivityConditionHolds.lean:115`) | standard (proved) |
| 2 | `adm2` :548 + `ExtensionLocalCondition` :162 | For each place v, the restriction ThV of the kernel is exp(−Ph)·U. Here (inParam U) is Oc-integral (U is integral as a function of the LT logarithm), Ph(−X) ≃ Ph, and Ph ≃ Σ_e be(x_e, y_e). **The kernel is a Gaussian in log coordinates times an integral series** | **substantive** |
| 3 | `adm2b` :552 | the same for the full ThA over all places | substantive |
| 4 | `adm2c` :556 | BeProp be | definition/routine (proved for beLT) |
| 5 | `adm3` :558 | all minor-jets applyD(PI_0)(ThZA ThA) are Oc-integral (geC ≥ 0) | substantive (integrality of jets) |
| 6 | `adm3b` :563 | Kz_j maps Kf·Int_j into Kf·Int_{j+1} | routine |
| 7 | `ArchimedeanSignatureMatching` :587 = `ExpansionEquality` :566 (j+1 < m) and `ExpansionDecomposition` :572 (j+1 = m) | the chain map **equals** the mass-weighted sum of kernel integrals. The last step also includes Hecke equivariance: the edge-sum of ker over neighbours of La equals ker applied to Tm F. The name is misleading: nothing archimedean is involved | **substantive** (ties the real chain to Θ) |
| 8 | `adm5` :590 | ThF(La, La') = u^{len}·u'^{len'}·p^{−(n'/2)·volE}·Xi(aw)(1[x L ⊂ L']), with u, u' units. This is the Schrödinger-model kernel as a function of the lattice pair | substantive / normalisation |
| 9 | `MinkowskiCounting` :597 | Γ-equivariance of ker (character χ_γ) | routine |
| 10 | `adm6` :603 | edge-sum adjointness: Σ_{La} Stab^{−1} Σ_{L1 ∼ La} φ = Σ_{La1} Stab^{−1} Σ_{L0 ∼ La1} φ. A mass-formula double count, proved generically (`up_down_adjoint`, `PL/OrbitSumStabilizer.lean:257`) | routine (proved for every Y) |
| 11 | `adm7` :613 | **jet-to-lattice transfer**: if every PI_{i0}-jet of f has valuation ≥ g, then p^{Σ Nprime(i0)}·kerF(linSub(bc) f)(G) lies in the level-(j+1) lattice scaled by g, for every G in the integral weight lattice. Proved for every kernel F on the live Pend (`pending_tuple_admissible`, `.../LatticeShapeMiddleHolds.lean:26`), from frame identities | substantive (proved) |
| 12 | `adm8` :624 | SelectionLemmas.adm3, and yv preserves M (the integral normalisation of T_r) | routine/normalisation |
| 13 | `adm11` :627 | LowAt j v 0: for **every** integral U, the jets of exp(−PhAt)·U have valuation ≥ 0 | substantive (integrality of the Gaussian's jets) |

## 3. The theorem and its proof

### 3.1 Statement

`Stmt D` (`FGS:779`) consists of two parts: ∀ p, X, Y, admitted ⇒ `Conclusion₂` (11 conclusions, `FGS:775`), and a numerical inequality `RelativePresentationLiterature`.
`stmt_proved` proves both (`MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:107`).
The consumer (`unit_bound_of_sum_over_primes`, `GrowthBounds/JointsTw.lean:243-270`) extracts three of the conclusions: VolumeRatio₂, adm11 and LowTermBound.

**LowTermBound** (`FGS:708`). Let VV be a set of places and Gn, G0n, PRn, S functions satisfying:
- Gn ≤ gB on VV;
- LowAt(j, v, G0n_{j+1}) everywhere, i.e. G0n is a valid jet bound for exp(−Ph)·U;
- PRn ≥ Pr;
- S_v ≥ Σ_j max(Gn − PRn − G0n, 0).

Then for every F in
Iprod(S, VV) = span_O{ ∏_{v∈BB} (yv_v)^m (ϖ^{Σ_{v∈VV∖BB} ⌈S_v eO⌉}·F0) : BB ⊆ VV, F0 ∈ Int_0 }
the following holds:

  v_ϖ(chainK_m F)/eO ≥ Σ_{j=1}^m [ Σ_{v∈VV} max(Gn_{v,j} − PRn_{v,j}, G0n_{v,j}) + Σ_{v∉VV} G0n_{v,j} ] − Σ_{j<m} dG_j.

With Gn = gB and G0n = gA, the per-step gain at v is max(gB − Pr, gA). Here gB − Pr ≈ γ_p·Σal − Σ_e min(al/p^e, cap) and gA = Σ_{e odd} max(al/p^e − cap, 0), each up to the log loss.
So the m-step gain is Σ_j Σ_{e odd} max(0, a/p^e − cap_j), the ASK shape of NODE-LOSS.

### 3.2 Proof as mathematics

**Step A: Dwork factorisation (`RestBeta`, `RestGc`; `MV/DworkExponentialRestrictions.lean:15-36`).** Both are proved: `restBeta`, `BiadditiveSecondVariable.lean:137`; `restGc` ← `gcCondition_of_twoSums`, `CommonEigenvectorThird.lean:21`.
- *RestBeta.* Any be with BeProp is ≃ a standard bilinear series Gser(c, σc), with c ∈ W(F_{p²}).
- *RestGc.* In the coordinates t = μ(ϖ·ω·Z) (μ the inverse of the LT parameter series lamF), the standard Gaussian factors as
    exp(−Gt) = exp(−(ϖ^{p+1}/p)·hh_u(Z))·V, with V integral over O[ϖ] and hh_u = Σ_s u_s S_s(Z)^p·S_{s+1}(Z).
- Here **π := ϖ^{p+1} satisfies π^{p−1} = p**: it is a Dwork π, with v(π) = 1/(p−1). The prefactor is π/p, with v(π/p) = 1/(p−1) − 1.
- The Dieudonné–Dwork criterion (clause 1) is the tool used to show V is integral.

**Step B: the class `InClass` (`Conclusion1`/`SConcl` `FGS:216`; `ExpansionsMultiply` `FGS:637`).** Since v(π^k/k!) ≥ 0, we have
  exp(−(π/p)hh) = Σ_k (hh/p)^k·(π^k/k!)·(−1)^k ∈ O[ϖ][[Z]][hh/p].
- Together with clauses 2 and 13, the rescaled kernel (variables Z ↦ ϖZ, `atPi`) is Σ_i p^{−i}·hh^i·g_i with g_i integral.
- This is proved as `theta_kernel_expansion` / `expansions_multiply` (`MV/CommonEigenvectorThird.lean:32-36`).

**Step C: jet bounds (`ea_A1U`, `ea_A2U`, `ea_BU`; `MV/EaGeCOfNorm.lean:198-237`).**
- These reduce, through `ea_BrJet`/`ea_BrClass`/`ea_BrScale`/`ea_BrNum` (all proved), to `kernel_a_one_generic`, `kernel_a_two_generic` and `kernel_b_generic` (`UTS/FrobeniusLiftNorms/EGaussK.lean:213-220`).
- Those rest on `EntryStar` (`UTS/StatementE.lean`), via `entry_a_one`, `entry_a_two` and `entryB` (`UTS/KOneConsequence.lean:43-45`).

The statement of `EntryStar`: let F = Σ p^{−i} hh^i g_i, and let the jet operator be (topForm)^e·(product of minors). The top degree is al_s = Σ_b e(s, b) and capN(s) is the number of minors at position s. Then the jet is 0, or
  v(jet of F) ≥ γ_p Σ_{TT} al − (#α + #β) − deLoss + ρ_p·Σ(al + ls).
- Here α counts the hh-monomials X_{s−2i}^{p^{2i+1}}·X_{s+1−2i'}^{p^{2i'}} used (both factors top) and β the monomials X^{p^{2i+1}}·(low linear) used.
- The +ρ_p(al + ls) term is the ϖ-rescaling. It is removed by `descend` (`EGaussK.lean:150`), which gives the bound for the **unrescaled** kernel:
  v(D^λ Θ(0)) ≥ γ_p Σ al − #factors − deLoss.
- **Why:**
  - a degree-n coefficient of hh^i g_i/p^i has valuation ≥ −i;
  - the jet multiplies by n! (applyD), worth v(al!) = (al − s_p(al))/(p−1) on the top part;
  - undoing the rescaling costs ρ_p per degree.
  - So v ≥ al/(p−1) − al/(p²−1) − i − O(log) = γ_p·al − i − O(log).
- **Why the caps and odd e.** Every hh-monomial has top degree p^{2l+1} at the first slot, because S^p raises the LT exponents p^{2l} to p^{2l+1}.
  A Hasse derivative in a fixed column direction kills a product of minors once it is taken more than capN times (`HitsCapPos`, `UTS/StatementE.lean:15`).
  So #factors of size p^e ≤ min(al/p^e, cap_{s+e}). This gives
  γ_p·al − Σ_{e odd} min(al/p^e, cap) = Σ_{e odd} max(0, al/p^e − cap),
  using Σ_{e odd} p^{−e} = γ_p and max + min = identity.
- So **the odd-e sum matches term by term**:
  - Legendre's v(a!) − a/(p²−1) ≈ Σ_{e odd} a/p^e;
  - each hh-factor of size p^e uses up one unit of the e-th term.

The three variants:
- A1 gives gA (excess form);
- A2, the jet with no Hecke factor, gives gB − alEven;
- B, with the Hecke operator T_i's factor p^{colExp}, gives the full gB. The even positions are paid for by the p-power in PI_{i0} (`ea_BrScale`, `EaApplyDScale.lean:98`).

**Step D: from jets to the chain (`FormB`, `MV/PlaceB.lean:22`; `formB`, `MV/SmulUpdate.lean:99`).**
- By ExpansionEquality, Kz_j G is a combination Σ Stab^{−1}·ker. Composing with Hecke operators at the target, adm7 bounds each term's lattice valuation by the jet bound.
- The stabiliser denominators cost dG_j. Hence:
  EntB(j, i0, g) ⇒ Tt_{i0}…(Kz_j G) ∈ p^{g − dG_j}·Int_{j+1}.
- `EntCondition` (`MV/RamifiedLatticeOfChainEstimates.lean:15`): given per-place budgets that satisfy `PlaceB` (`PlaceB.lean:27`), the jets have valuation ≥ Σ_v gP_v. It is proved by `restEnt_of` from A2U and BU.
- **The parent's oddity resolved.** The i = 0 branch "g ≤ gB − alEven" of `PlaceB` is not a free grant. EntCondition must hold for every PlaceB-admissible budget, so the branch is a *demand* that the plain jets reach gB − alEven, and ea_A2U meets it.
  The missing alEven is later supplied by the coefficient cl_r of Zop, which satisfies v(cl_r) ≥ alEven (`Conclusion4`, third conjunct).

**Step E: MassRatio₂ and PointsLemma** (`hecke_integral_of_forms` `:122`, `latticeChain_succ_of_partial` `:165`, in `RamifiedLatticeOfChainEstimates.lean`).
- MassRatio₂ (`FGS:661`): v(Kz_j G) ≥ gB_v − alEven_v + Σ_{v'≠v} gA_{v'} − dG_j for all G ∈ Int_j. It is the i0 = 0 case of D.
- PointsLemma (`FGS:665`):
  - Tt_{v,i}(Kz_j G) ≥ gB_v + Σ_{v'≠v} gA − dG for 1 ≤ i ≤ r (the B case of D);
  - Tt preserves Int_{j+1}.

**Step F: kernel commutation.**
- `heckeCondition_of_adm` (`MV/HeckeConditionOfAdm.lean:75`) uses clauses 6–10 and lattice counting (`CountLoc`) to derive `RestHecke` (`MV/HeckeValueEstimateOfRecordValue.lean:277`):
    ecal_i(Kz_j F) = u^i·Kz_j(Σ_l e_l(m·q^{(n'/2)(t−2x)})_{x≤t}·ecal_{i−l} F).
- This is the **Rallis/Eichler commutation relation**: a theta lift adds t+1 Satake parameters. It follows from the explicit indicator kernel (adm5).
- `alternate_expansion_of_relations` and `theorem_of_alternate_form` (`MV/TheoremOfAlternateForm.lean:561`) invert it with complete symmetric functions:
    Zop_v(chainK_{j+1} F) = p^{PrZ}·chainK_{j+1}(yv_v F),
  together with v(cl_l) ≥ 0, v(cl_r) ≥ alEven and v(Zop(Kz_j G)) ≥ gB + Σ′gA − dG (`Conclusion4`, `FGS:671`).

**Step G: iteration** (`main_ind`, `MV/YEPEComm.lean:131`; `lift_bound_of_integrality`, `MV/LiftBoundOfIntegrality.lean:103`).
- Claim, by induction on m′: chainK_{m′}((∏_{v∈Lv} yv_v)^{m′}F) has valuation ≥ Σ_{j<m′} bbJ_j. The step from m′ to m′+1:
  1. Split Lv into B, the places where gB − Pr ≥ gA, and C, the rest.
  2. Write (∏ yv)^{m′+1} = (∏_B yv)·(∏ yv)^{m′}·(∏_C yv). The Hecke operators commute, and they preserve Int_0 by adm8.
  3. Apply F to get chainK_{m′+1}(…) = p^{−Σ_B PrZ}·(∏_B Zop)(Kz_{m′} chainK_{m′} W).
  4. By induction, chainK_{m′} W = ϖ^{prev}·G′ with G′ ∈ Int_{m′}.
  5. `ZL_bound` (from D and E) gives (∏_B Zop)(Kz G′) ≥ Σ_B gB + Σ_{rest} gA − dG.
  6. So the step gains Σ_B (gB − Pr) + Σ_{v∉B} gA − dG = Σ_v max(gB − Pr, gA) − dG.
- **One application of the chain therefore converts one level-0 Hecke operator into a gain at level j+1, at the cost Pr.** Iterating m times gives the sum over j.
- For the generators of Iprod with BB ⊊ VV, the explicit factor ϖ^{⌈S eO⌉} pays for the max(…) at the places in VV∖BB (`basic₂`, `:22`).
- If eO = 0 there are no places, and the bound is trivial (`:51`).

## 4. Sanity checks by hand

I use toy kernels in the post-factorisation form of Step B, which is the hypothesis form of `EntryHyp` (`UTS/StatementE.lean:170`). Take n' = 2 with top position s = 1 ∈ TT, one variable per position, and ρ = 1/(p²−1).
1. **No Gaussian, cap 0, p = 7, al = 7.** Rescaled kernel V = Σ_n Z_1^n (integral).
   - Unrescaled jet: ∂^7 Θ(0) = 7!·ϖ^{−7}, with v = 1 − 7/48 = 41/48.
   - Formula: γ_7·7 − s_7(7)/6 = 49/48 − 1/6 = 41/48. Exactly v(a!) − ρa.
   - Lean bound (excessGain): Σ_{e odd} 7/7^e − deLoss = 49/48 − deLoss, with deLoss ≥ 2·NN.
   - Holds. **Without deLoss the bound would be false** (41/48 < 49/48), so the log loss is genuinely needed and is present.
2. **One Gaussian factor, cap 1, p = 7, al = 7.** Θ_resc ∋ −(π/p)·Z_1^7 Z_0, π = ϖ^8.
   - Rescaled jet ∂_1^7∂_0 = 7!·(−ϖ^8/7), with v = 1 + 8/48 − 1 = 1/6. Unrescaled: 1/6 − 8/48 = 0.
   - Lean (excessGain): max(0, 1 − 1) + Σ_{e≥3} 0 − deLoss = −deLoss ≤ 0. Holds and is tight up to the loss.
   - The `EntryStar` form claims 49/48 − 1 + 8/48 − deLoss = 9/48 − deLoss in rescaled terms, against the actual 8/48. It again holds only because of deLoss.
3. **Many factors, al = p·w, cap = w.** Unrescaled valuation = v(w!) ≥ 0. The claimed bound is Σ_{e odd} max(0, pw/p^e − w) − deLoss = −deLoss. Holds.
4. **Normalisation and sign.**
   - **Valuation direction.** The bound is a lower bound on the valuation (geC; `ea_geC_of_norm`, norm ≤ p^{−g}).
   - **Kernel p-power cancels.** The live kernel FrecG contains p^{Σ vm(len_{j+1} − len_j)} (`OrthogonalChartLevels/FdOfCharts.lean:42-55`). kerF multiplies by eS/eT = p^{Σ vm(len_j − len_{j+1})} (`FGS:510-516`). The two cancel in ker = (eS/eT)·DelF(·, ThF), so the chain sees the raw theta series.
     **But** the jet bounds of clauses 2/3/13 apply to ThA, which still carries the factor. So clause 2's "U integral" is a statement about p^{Σvm Δlen}·Θ, and adm7 takes the factor back. I did not check that these two uses are consistent.
   - **Hecke normalisation.**
     - yv carries p^{ArV}, with ArV = Σ_s Σ_{i<r} λ_{s,i}. This is the sum of the *top* weights, of size ≈ n'·a, i.e. larger than γ_p·a.
     - This is the integral normalisation of T_r on weight-λ forms. If it over-normalised, chainK(yv^m F) would be divisible for free.
     - Two checks guard against that:
       - the kernel-commutation identity is *derived* from adm5/adm6, not assumed, so PrZ must absorb exactly the normalisation;
       - the proved colength bound (NODE-TWU: length(Mram/NP) ≤ d(τ + io)) would fail if yv^m M ⊆ p^{k}M with k large.
     - So a cheap gain from over-normalisation is excluded **provided** the colength theorem is honest. That theorem is unopened by me.
5. **p = 3 is excluded** (`Std.five_le`), so the requested p = 3 check is impossible. The p = 7 checks above stand in for it.

## 5. Is it applied non-trivially on the live path? (e)

- **Y5 = pendG = pendT (FrecG …)** (`IKT/DelPolOfTies.lean:97`; `PL/InvarianceIffAdditiveMapsExist.lean:54`).
  ThA = linSub(c·subBG)(p^{…}·serP_λ(kerTh B χ …)) is the **global theta series kerTh** transported to ℂ_p and rewritten in frame coordinates. It is not 0 by construction. I did not check kerTh ≠ 0.
- **DelF** is the derivative pairing with polDel(G) = divD(numD·subD G). Here divD is a `Classical.choose` left inverse of multiplication by denD, or 0 if that multiplication is not injective (`PL/DetYtMatNeZero.lean:86-102`).
  So off the image of denD, polDel is an arbitrary fixed choice. adm7 and ExpansionEquality are proved for it.
  The file name suggests det ≠ 0 is proved; I did not read it.
- **be = beLT** = `if BeRat then choose else 0` (`PL/CoeffOneLNe.lean:117,123`).
  be = 0 would *strengthen* clause 2: the kernel would have to be nearly integral. So it gives no vacuity in the favourable direction.
- **Suppliers of the clauses** (`admissible_general_of_kernel_law`, `IKT/InertCoprimeLemmas/AdmissibleEntriesOfKernelLaw.lean:68-78`):

  | clause | supplier |
  |---|---|
  | adm1 | proved |
  | adm2, adm2b, adm3 | `first_kernel_law_global_small` (`IKT/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean:124`), from the CM data g (supersingular CM curve, `LTIso`, `ModelOverW`) and **[Fact CM2]** |
  | adm2c, adm11 | `admissible_*_inert` (`IKT/AdmissibleEleventhInert.lean`) |
  | adm3b | `admissible_third_instance` |
  | ArchimedeanSignatureMatching | `admissible_fourth_instance` / `coupled_compatibility_at_place` (local models tied to the family's chain) |
  | adm5 | hXi |
  | adm6 | proved for every Y |
  | adm7 | proved for every kernel |
  | adm8 | proved |
  | Minkowski | stabiliser law |

  None is `True`/`trivial`.
- **a ≠ 0.** The comparison `SmallResidueCharComparison` (`FGS:741`) requires the family's gU ≤ gB. On the live path gU ≈ ASK_p > 0, so gB > 0 is forced, and with it al ≈ a. Its supplier is not traced (NODE-TWU child 7).
- **`entStd`** (`SP/RowTwUHolds.lean:13`). Its four zero fields are Th, ep, be and one more field of an `OrbitPlaces.Ent` record. `Shape` (`SharpRestriction/Divisibility/OrbitPlaces.lean:249-260`) reads only the Young diagrams ν (`size`, `row`). **Harmless.**
- **The PlaceB i = 0 branch** is harmless: it is a demand, met by A2U (Step D).
- **The zero chain** is not on this branch (NODE-TWU).
- **The variable scaling.** c = ltC = (g.C.u·ep)^{−1} (`OrthogonalChartLevels/LtCNeZero.lean:11`), where u is the Weierstrass change of variables to the good-reduction model.
  - u ∈ ℂ_p^× need not be a unit. Its valuation is the p-adic period, fixed by minimality.
  - A wrong-valuation c would make every jet of degree d cheaply divisible by c^d. It is consistent only if ExpansionEquality's proof (h4) uses the same c.
  - **Open; flag for the expert.**

## 6. Judgement (f)

**A correct theorem? Yes, as far as I can reconstruct.** Taking the children's statements as black boxes, I can write the proof of `stmt_proved` myself (§3). Its mathematical heart is elementary:
- *derivatives of a series in O[[ϖZ]][hh/p] are divisible by p^{v(a!) − a/(p²−1) − #factors}*;
- *a Rallis commutation relation lets this gain repeat m times*.

This matches the expected phenomenon: Taylor expansions at a supersingular CM point in the height-2 LT logarithm, with v(D^a f) ≳ v(a!) − a/(p²−1) = γ_p·a − O(log a). It is the a!-type quantity in the inert setting, not a lattice-point count.

**Where I could not follow** (proofs not read):
1. `EntryStar`/`TermBound`: the combinatorics of the α/β monomials, `HitsCapPos`, and the dSet exclusion.
2. The `RestGc` proof via `TwoSumsCondition`.
3. Whether clause 2 truly holds for the global theta series at the CM point. This is a deep statement: in log coordinates the Taylor expansion is Gaussian × LT-integral, with the p-power normalisation noted in §4.4.
4. The identification Kz = Σ ker for the family's chain.
5. The consistency of c = ltC and of p^{Σvm Δlen} between clause 2 and adm7.

**Children, ranked:**

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `first_kernel_law_global_small` | `IKT/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean:124` | the CM theta kernel satisfies clauses 2, 2b, 3 | **core** |
| 2 | `admissible_fourth_instance` / `coupled_compatibility_at_place` | `…AdmissibleEntriesOfKernelLaw.lean:85-104` | ExpansionEquality/Decomposition for the family's chain | **core** |
| 3 | `entryStar` (→ `entry_a_one`/`entry_a_two`/`entryB`) | `UTS/KOneConsequence.lean:43-45` | jet bound of §3.2 C | core (elementary; proved) |
| 4 | `restGc`, `restBeta` | `MV/CommonEigenvectorThird.lean:21`; `MV/BiadditiveSecondVariable.lean:137` | Dwork-π factorisation | core (Dwork/Artin–Hasse-type; proved) |
| 5 | `pending_tuple_admissible` | `…/RowActionCoefficients/LatticeShapeMiddleHolds.lean:26` | adm7 | core-ish (proved) |
| 6 | `heckeCondition_of_adm` | `MV/HeckeConditionOfAdm.lean:75` | Rallis commutation from adm5 | standard (Rallis; Kudla–Rallis), proved |
| 7 | `main_ind`, `lift_bound_of_integrality`, `basic₂`, `form_of_place` | read | — | glue |
| 8 | supplier of `SmallResidueCharComparison`; `ltC` valuation; `divD` choice | — | — | definitions to unfold |

## 7. Coverage

Read:
- `FGS:1-856`;
- `MV/PrvAndKernelCommutationUpToUnitsOfRests.lean`, `DworkExponentialRestrictions.lean`, `CommonEigenvectorThird.lean`, `FirstTheoremPlaceBound.lean`, `PlaceB.lean`;
- `MV/RamifiedLatticeOfChainEstimates.lean:1-200`, `EaGeCOfNorm.lean:1-240`, `LiftBoundOfIntegrality.lean`, `YEPEComm.lean`, `SmulUpdate.lean:60-110`, `HeckeConditionOfAdm.lean:60-100`, `HeckeValueEstimateOfRecordValue.lean:270-300`;
- `UTS/FrobeniusLiftNorms/EGaussK.lean:1-240`, `UTS/StatementE.lean:1-260`;
- `GrowthSums/StatementA.lean:55-125`; `GaussJetBounds/StatementP.lean:1-80`;
- `…/AdmissibleEntriesOfKernelLaw.lean`; `IKT/DelPolOfTies.lean:60-200`; `IKT/TranslatesOfInertKernelAtPlace.lean`; `IKT/AdmissibleEleventhInert.lean`; `IKT/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean:100-140`;
- `PL/DetYtMatNeZero.lean:80-175`; `PL/CoeffOneLNe.lean:95-125`;
- `OrthogonalChartLevels/FdOfCharts.lean:10-80`; `…/LatticeShapeMiddleHolds.lean`;
- `DataG.lean:80-200`; `GlobalSchurBounds/GL3Theta.lean:30-115`;
- `GrowthBounds/JointsTw.lean:236-275`; `SP/RowTwUHolds.lean`; `SharpRestriction/Divisibility/OrbitPlaces.lean:34-140,249-261`.

Not opened:
- the proofs of `entryStar`, `TermBound`, `restGc`/`TwoSumsCondition`, `restBeta`, `formB_of`, `ZL_bound`, `Ci`/`Cii`/`Ciii` and `CountLoc`;
- `first_kernel_small_of_frame_twist`; the fourth/third instances;
- the `kerTh` definition; `ltC`'s valuation; `denD` ≠ 0; the `SmallResidueCharComparison` supplier.
