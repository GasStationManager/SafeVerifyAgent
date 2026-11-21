# NODE-HIGHERRANK: the higher-rank local statement and why the cap works

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `UTS/` = `Formalism/ThetaLogCoordinates/UniformThetaSubstitution/`; `FLN/` = `UTS/FrobeniusLiftNorms/`
- `SE` = `UTS/StatementE.lean`, `SAB` = `UTS/StatementAB.lean`
- `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`; `ICL/` = `IKT/InertCoprimeLemmas/`
- `DER` = `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DworkExponentialRestrictions.lean`

Script: `numtest/cap_minors.py` → `numtest/out_cap_minors.txt` (stdlib, exact integers, a few seconds).

## 0. Verdict (short)

- **(a) Confirmed.** In the position coordinates Z_{s,a,b} (s ∈ ℤ/n′ a Frobenius position, (a,b) a matrix entry), the
  Gaussian is exp(−(π/p)·hh), π = ϖ^{p+1}, with
  hh = Σ_s u_s Σ_{a,b} S_{s,a,b}^p·S_{s+1,a,b}, S_{s,a,b} = Σ_l (−1)^l Z_{s−2l,a,b}^{p^{2l}} (FGS:200-208).
  It is diagonal in the matrix entry (a,b). Mod p its "first-order" monomials are, for every odd e = 2l+1 and every t,
  (−1)^l u_{t+2l}·Z_{t,a,b}^{p^e}·Z_{t+e,a,b}. So a factor of level e couples position t to **position t+e**
  (the place Frob^e·t). When n′ = 2 (rank one over ℚ), t+e is the same conjugate position for every odd e. That
  explains NUMTEST2's "cap once": the weight b there is one shared budget, and the Lean's separate charge per e is
  valid but weaker. When n′ is large, the positions t+e for odd e < n′ are distinct, and each has its own weight.
- **(b) The cap is an honest, elementary algebraic lemma, and my hand and machine checks confirm it.** Multiplying the
  series by a linear form ℓ is adjoint, under the jet pairing, to the directional derivative ∂_ℓ of the operator
  polynomial. Each Gaussian factor's linear part Z_{t+e} therefore forces one derivative, in the fixed row-direction
  ξ_t^{p^e} at position t+e, onto the product of column minors. A column minor det((T·X)[·, I]) is linear in each column
  of X and alternating, and a ξ-derivative replaces a column by the fixed vector Tξ. So **two ξ-derivatives kill one
  minor**, and more than C = (#minors at that position) ξ-derivatives kill the product.
  - This is not pluriharmonicity (Δ P = 0).
  - The cap is per (position, direction). It fails for mixed directions, and the Lean uses it only per direction.
  - C = ν₂ at a top, because the first-row overhang has been peeled off into the top linear forms, and C = ν₁ elsewhere.
    This matches `cap` (FGS:36).
- **(c) The term-by-term valuation bound is right.** It is a multinomial expansion of (hh/p)^i·g_i, followed by an
  ultrametric max over terms.
  - The top-degree multi-factorial ∏_b e_{s,b}! is kept in full, giving al/(p−1) − r₁·lg.
  - Each Gaussian factor costs one p. The Dwork coefficients π^k/k! are exactly integral and are absorbed into g_i.
  - The ϖ-rescaling costs ρ per degree. Net: γ_p·al − #factors − deLoss.
- **(d) The reduction to rank one is honest, and it does not assume an orthogonal decomposition globally.** It has four
  steps:
  1. A unimodular hermitian lattice is locally (at p) isometric to the standard one (`unimodular_genus_unique`).
  2. Weak approximation gives a global unitary γ with L = γ·M and M = std at p.
  3. A prime-to-p coset average (`StdStep`) expresses θ_M through translates of θ_std.
  4. θ_std is a tensor power by definition, and the one-copy factor is handled by a 4-fold isometry.
- **(e)** I could reconstruct the higher-rank cap mechanism as correct mathematics. The open load is upstream, in the
  claim that the kernel *is* in InClass(hh) (adm2/RestGc). The cap combinatorics are sound.

## 1. Statement

### 1.1 The Gaussian (a)

**Variables.**
- `Eidx n′ r0 r1 = Fin(n′/2) × Fin r0 × Fin r1` (FGS:160) indexes the hermitian pairs e = (r, a, b), where r is the
  half-orbit index and (a,b) the matrix entry.
- The kernel lives in variables x_e = `Sum.inl e` (holomorphic) and y_e = `Sum.inr e` (dual).

**Clause 2.** `ExtensionLocalCondition` (FGS:162) asks for four things:
- Th = exp(−Ph)·U;
- U(logF) is integral;
- Ph is even;
- Ph ≃ Σ_e be(x_e, y_e). The "the Lean says" form is `sub2 be (X (inl e)) (X (inr e))`.

Here ≃ means "difference has no constant term and its exponential, in LT-log coordinates, is W-integral" (FGS:139).
`BeProp` (FGS:147) makes be biadditive mod ≃, with be(αX,Y) ≃ be(X,σα·Y) for α ∈ W(F_{p²}).

**Where clause 2 comes from (`k1gen_of_orth`, ICL/RepAsm.lean:17).** `OrthInt` (IKT/DefsRep.lean:26) assumes
exp(Σ_i ph(X_i))·Θ(log) is integral in an orthonormal basis, and that Th = Θ∘hypLin(f,f′) for a hyperbolic pair
(`IsHypPair`). Two facts then give Σ_i ph(X_i) ≃ Σ_e be(x_e,y_e) (`hyperbolic_of_orthogonal`):
- be is the polarisation of ph;
- ph(αT) ≃ ασ(α)·ph(T) (`NormRel`, a field of `CurveAt`, DefsRep.lean:17).

*I infer:* this is the identity "the hermitian norm form is Σ x_e ȳ_e in a hyperbolic basis", with the isotropic
self-terms ≃ 0.

**Normal form of be (`RestBeta`, DER:15).** For p ≥ 5, be ≃ Gser(c, σc) with σ²c = c. The series is
`Gser c c′ = c·Aser − c′·Aser′`, with Aser = Σ_{i≤j} X^{p^{2i}}Y^{p^{2j+1}}/p^{i+j+1} (UTS/OddLogRelation.lean:20-29).
Its leading term is (c·XY^p − σc·X^pY)/p.

**Positions (`coordZ`, FGS:181).** The pairs are spread over positions s ∈ ℤ/n′:
- x_{(r,a,b)} = ϖ·Σ_{s even} σ^s(ω*_r)·Z_{s,a,b};
- y_{(r,a,b)} = ϖ·Σ_{s odd} σ^s(ω_r)·Z_{s,a,b};
- `OmBasis` (FGS:172) requires the duality Σ_i σ^{2i}(ω_r ω*_{r′}) = δ_{rr′}.

**`RestGc` (DER:22).** After substituting the LT parameter t = μ(ϖ·coordZ),
exp(−Gt) = exp(−(ϖ^{p+1}/p)·hhS_u(Z))·V,
with V integral over Rp = W[ϖ] and the u_s in Rp. Here:
- `hhS u = Σ_s u_s Σ_{a,b} sSer_{s,a,b}^p·sSer_{s+1,a,b}` (FGS:205);
- `sSer_{e,a,b} = Σ_l (−1)^l Z_{posSub(e,2l),a,b}^{p^{2l}}` (FGS:200).

So hh is an explicit power series:

  hh = Σ_s u_s Σ_{a,b} (Σ_l (−1)^l Z_{s−2l,a,b}^{p^{2l}})^p·(Σ_{l′} (−1)^{l′} Z_{s+1−2l′,a,b}^{p^{2l′}}).

**Monomials mod p.** Write X = low + ξ·top at a top position (`zSub`, SE:88). Then
`HhDecomp` (SE:124, proved: `decomposition_of_hh`, FLN/EDecomp.lean:498) says that, up to degree D and modulo
Z + p·Y, hh equals:
- **β-terms** (`KapI`, `aBof`, `dBof`, `bBof`, SE:110-120): u_{t+2l}(−1)^l·top_{t,b}^{p^{2l+1}}·⟨ξ_t^{p^{2l+1}}, low_{t+2l+1,·,b}⟩.
  This is a top power at t times a **linear** form in the low variables at **t+e**, e = 2l+1, in the Frobenius-twisted
  row direction ξ_t^{p^e}.
- **α-terms** (`PhiI`, `aAof`, `dAof`, SE:93-108): top_{t}^{p^{2l+1}}·top_{t′}^{p^{2l′}}, with
  t = s−2l and t′ = s+1−2l′. Both are tops, at odd distance.
- **Z**: integral, with low degree ≥ p.
- **p·Y**: integral.

The cross terms of (Σ)^p are divisible by p, which is why they fall into p·Y. *I infer* this is why the decomposition
works: (u+v)^{p^e} ≡ u^{p^e} + v^{p^e} mod p.

**Answer to the brief's question.** Yes: for each odd e there is a leading monomial x^{p^e}·y. In rescaled coordinates
it is (π/p)·Z_t^{p^e}·Z_{t+e}, with π = ϖ^{p+1}, v(π/p) = 1/(p−1) − 1. Its y-variable sits at position t+e, the place
Frob^e·t, whose weight is PAIRING's W_{t,e}. Undone to LT coordinates, the e = 1 term is z_t^p·z_{t+1}/p (KERNELLAW).

**Rank one.** With n′ = 2, `posSub` gives s − 2l ≡ s, so S_s is a one-variable twisted log. Every partner t+e is the
other position, and all levels draw on the same derivative budget b in the conjugate variable. The Lean charges
Σ_e min(a/p^e, b), which is larger than the true joint count. That is NUMTEST2's "cap bites once", and the Lean is
weaker there, not wrong.

**Long orbits.** For n′ ≫ 1 the targets t+e (odd e < n′) are distinct places with distinct weights. For e > n′ they
wrap around; the Lean again charges them separately, which is valid and negligible (PAIRING: ≤ a/p^{n′+1}).

### 1.2 The jet operator and the cap (b)

**The operator.**
- `applyD P f = Σ_n (∏_x n_x!)·coeff_n(f)·P_n` (FGS:256), and `jetPair` is the same pairing over K
  (`Formalism/GaussJetBounds/StatementI.lean:13`, with `mfact` = ∏ n_x!).
- `PI j` (FGS:417) = ∏_{v,s} ∏_{c < ν_{j+1}(s,1)} p^{colExp}·colFac(c).
- colFac(c) (FGS:405) = det_{i,i′ < colHt(c)} (Σ_a T_{s,i,a}·Z_{s,a,I(c,i′)}): one column minor per column c of the
  Young diagram ν_{j+1}(s,·), of size colHt(c) = column length (FGS:398). The frame T consists of generic
  indeterminates (`FrI`).
- So the number of minors at position s is ν(s,1), the first-row length.

**EntryStar's split (SE:144-154).** EntryStar works with
entryOp = (∏_{(s,b)} topForm_ξ(s,b)^{e(s,b)})·∏_c minorAt(sf c, T c, I c),
where topForm_ξ(s,b) = Σ_a ξ_{s,a} Z_{s,a,b} is a height-1 column in the first-row direction.
- At a top s, the al_s = ν₁ − ν₂ overhang columns are these topForms.
- So capN(s) = #(remaining minors) = ν₂(s) at tops and ν₁ elsewhere. This is FGS:36 `cap`.
- *I infer* the conversion PI → entryOp from the `ea_Br*` chain named in LOCALDIV; I did not read it.

**`HitsCapPos` (SE:15).** Take a set S of directions k, all at the same position s₀ and with the **same** row vector ξ,
in arbitrary columns col k. If Σ_{k∈S} β_k > #{minors at s₀}, then the Hasse derivative of order β of
∏_c minorAt(…) is 0.

It is proved (`hitsCapPos`, UTS/KOneConsequence.lean:33) from two lemmas:
- **`MinorHits`** (SAB:58). A single minor is killed by any of: a repeated direction (β_k ≥ 2); two directions at the
  same position with equal ξ **or** equal column; a direction at another position or outside the minor's columns.
- **`HasseDerivProdVanish`** (SAB:42). This is Leibniz plus pigeonhole: if factor c dies under more than m_c
  derivatives from S, the product dies under more than Σ m_c.

`HitsColumnsPos` (SE:23) is the same with the cap replaced by Σ_c #(columns of minor c in J). It is used by `EntryB`.

**The mechanism.**
- `JetPairingHasseIdentity` (SAB:31): jetPair(Q, ∏_k ℓ_k^{β_k}·G) = (∏ β_k!)·jetPair(∂^β_ℓ Q, G).
  Multiplication by a linear form is adjoint to a directional (Hasse) derivative.
- So every β-type Gaussian factor in the expansion of the kernel moves one derivative ∂_{ξ_t^{p^e}, col b} at
  position t+e onto the minors.
- By MinorHits, a minor absorbs at most one such derivative per direction.
- Hence the number of β-factors of level e from top t is ≤ min(al_t/p^e, capN(t+e)). This is `iN_le_cap` /
  `iN_le_min`, FLN/EntryATwoAndB.lean:125,151; statements read, bodies not.

**Test on the smallest example: P = (x11x22 − x12x21)·x11, weight (2,1), frame rows e₁, e₂.** The results
(`out_cap_minors.txt`):
- ∂_{x11}∂_{x12}P = −x21 ≠ 0, but ∂_{x11}²∂_{x12}P = ∂_{x11}³P = 0. The maximum in direction e₁ is 2 = #minors.
- In direction e₂ the maximum is 1, so the bound holds but is not attained.
- The mixed directions ∂_{x11}²∂_{x22}P ≠ 0 give 3 > 2, so **the cap is per direction**.

The random-frame tests ((2,1), (2,2), (3,2,1), (1,1,1), 3×3 matrices) agree:
- in one generic direction the maximum order is exactly #minors and never exceeds it;
- with mixed directions it always exceeds it.

**Does the Lean ever need a joint cap across directions?** No.
- For a fixed (t,e) every β-factor has the same direction ξ_t^{p^e}. Only the column b varies, which HitsCapPos allows.
- Different (t,e) with the same target t+e have different directions. The Lean charges each (t,e) against
  capN(t+e) separately (gB/gA sum over (s,e) independently, FGS:57,66).
- So it never uses a cross-direction cap, which would be false.

**At a top partner q.** The ξ_q·top_q part of Z_q produces **α-terms**. These hit the top linear forms at q and are
limited only by top degree (≤ al_q), not by a cap. The Lean pays for them separately:
- gA excludes e ∈ dSet(s), the opposite-parity top distances, and charges those levels in full (FGS:63-70; SE:163);
- gB charges all of alEven (`EntryCappedBound`, SE:201);
- EntryB restores alEven through the Hecke p-power.

PAIRING's statement "cap = second row ν₂" is therefore exact for the β-cap at top partners.

### 1.3 The term bound (c)

**`TermBound` (SE:61; proved `TermBound_of`, FLN/NormNatCastLeOfDvd.lean:495).** Assume:
- g ∈ InClass(h), i.e. coeff g = Σ_i p^{−i}·coeff(h^i·U_i) with every U_i integral;
- h agrees up to degree D with Σ aA·(top monomials) + Σ aB·top^{dB}·ℓ_b + Z + pY, all coefficients ≤ 1;
- Z has low degree ≥ p everywhere;
- Q is integral and homogeneous of degree dQ, with |e| + dQ = D.

Then the jet is 0, or there are α, β, i₂ and n ∈ supp(∂^β_b Q) such that:
- α·dA + β·dB ≤ e;
- p·i₂ ≤ |n|;
- ‖jetPair(top^e·Q, g)‖ ≤ p^{Σα + Σβ + i₂}·|e!|·|(Σβ)!|·|n!|.

**Proof (read at top level).**
1. Expand (Σ pieces)^i with multinomial coefficients (`key`, :511).
2. Bound each term:
   - the 1/p^i is cancelled by one p for each pY-factor;
   - the top monomial pairs with full e! (|e!·coeff| ≤ |e!|, since the consumed top degree does not cancel e!);
   - the β linear forms become ∂^β with factor ∏β_k!, which times the multinomial gives (Σβ)!;
   - the Z-factors consume ≥ p low degree each.
3. The ultrametric `closure_sum` picks the worst term.

All steps are correct as stated.

**`EntryStar` (SE:176; proved `EntryStar_of`, FLN/NormLeOfDvd.lean:309).**
- Transport the jet through zSub by `JetPairLin` (the jet of P against F∘A equals the jet of Aᵀ·P against F).
- Apply TermBound.
- Close with `StarArith` (SAB:104):
  Σ_b v(e_{s,b}!) ≥ al/(p−1) − r₁·lgN (`FactorialLg`, SAB:95);
  the low factorials pay for their own ρ·ls and for i₂ (γ_p ≥ 1/p);
  the α/β losses are carried through.
- Result: rescaled v ≥ γ_p·Σal − #α − #β − deLoss + ρ·Σ(al + ls).
- Unrescaled (`descend`): v ≥ γ_p·Σal − #factors − deLoss.

**Bookkeeping checks (the brief's list).**
- **n!** is the multi-index ∏ n_x! in both `applyD` and `jetPair`.
- **The Dwork term π^k/k!** has v = k/(p−1) − v(k!) ≥ s_p(k)/(p−1) > 0. It is exactly integral, with no log loss, and
  is used only to place the kernel in InClass (LOCALDIV Step B). The bound itself holds for **any** integral u and
  U_i.
- **The 1/p per hh-factor** is exactly the 1/p^i.
- **The rescaling** costs ρ = 1/(p²−1) per degree, on top degree and low degree alike.
- **Worked example, one factor of level e = 3 in the unrescaled coordinates.** The coefficient has
  v = 1/(p−1) − 1 − (p³+1)/(p²−1) = −p − 1, and v((p³)!) = p² + p + 1. The jet therefore has v = p², against
  γ_p·p³ ≈ p² + 1 + O(1/p): one unit is lost per factor, as claimed.

### 1.4 Integrality of the Gaussian-free part (d)

**The statement (`IntInert`, IKT/StatementInt.lean:18; proved `kernels_integral_inert`, IKT/KernelsIntegralInert.lean:9).**
Let (L,L′) be **admitted**: even ranks, self-dual hermitian O_E-lattices (`admitted`,
`Formalism/LocalToGlobal/KernelLattices/ColumnData.lean:179`). Let F be a p-integral combination of prime-to-p torsion
translates of θ_{L,L′} (`IsComb`). Then, in every orthonormal local basis b, atLog(F)·∏ ePhi1⁻¹ is integral in the
good-model formal parameters. Here atLog(F) is F with z = u⁻¹·Σ b_i·log_W(T_i), and ePhi1 is σ*(u⁻¹log T)/(u⁻¹T). In
short, "Θ/∏σ\* is integral".

**The reduction (`integral_inert_of_weakApprox`, IKT/IntegralInertOfWeakApprox.lean:9-13).**
1. **General L to M = std at p.**
   - `wa_main` (ICL/IntWeak.lean:171) shows L is unimodular (`wa_unimod`).
   - `unimodular_genus_unique` makes it locally isometric to std at every P | p.
   - `WAPlaces` (IntWeak.lean:10; proved `weak_approximation_places`, ICL/IntWAPlaces.lean:465) then gives a global
     unitary γ with γ·std = L at every P | p.
   - `WeakApprox` (IKT/DefsInt.lean:48) states the result: L = γ·M with M admitted and M = std at p.
   - `PullFact`/`PullTors` move θ through γ (a linear change of the matrix variable), and `LocInv` changes orthonormal
     bases.
   - **No global orthogonal splitting is assumed.** Only the local p-adic fact is used: unimodular hermitian lattices
     over an unramified quadratic extension are unique up to isometry (Jacobowitz). That fact is standard.
2. **`StdStep` (DefsInt.lean:101; proved `pairs_standard_at_p`, ICL/IntStd.lean:302).** If M = std at p, then every
   prime-to-p translate of θ_M is Σ_k c_k·(translate of θ_std) with c_k algebraic and p-integral.
   *I infer:* this is coset averaging between commensurable lattices of prime-to-p index, which is honest.
3. **`TensFact` (DefsInt.lean:122; proved `tensor_matrix_units_fact`, ICL/IntTens.lean:640).** θ_std(N×N′) is a block
   product of 2×2 thetas, because thZero is a tensor power by definition (KERNELLAW).
4. **`FourProd` (DefsMM.lean:62; proved `four_products_from_one`, ICL/MMFour.lean:206).** The step 1×1 → 2×2, given
   one-copy integrality and algebraicity.
5. **`OneCopyLoc` (DefsMM.lean:40).** One-copy integrality, from `IsomONB` (the 4-fold isometry, KERNELLAW).

So the answer to "is it honest for lattices that are not orthogonal sums" is **yes**: the general case reaches the
standard lattice through the local structure at p plus weak approximation, not through a global decomposition.

## 2. Argument (assembled)

At one place, per step j:
1. The kernel in rescaled position coordinates lies in O[ϖ][[Z]][hh/p] (adm2 + RestGc + Dwork).
2. Paired against (top linear forms)^{al}·(column minors), each monomial term loses one p for each Gaussian factor and
   gains the full Legendre valuation of ∏ e_{s,b}!, less ρ per degree.
3. Gaussian factors of level e from top t either:
   - force a derivative in direction ξ_t^{p^e} at position t+e, which costs one minor there, so at most capN(t+e) of
     them occur; or
   - eat top degree at an opposite-parity top, which is paid for in full or through alEven.
4. Sum the counts: Σ_e min(al/p^e, cap) factors, so v ≥ Σ_e (al/p^e − cap)₊ − deLoss.

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `restGc` / `RestGc` | DER:22; proof `gcCondition_of_twoSums` (LOCALDIV) | exp(−Σ_e Gser(x_e,y_e)) in position LT coordinates = exp(−(π/p)hh_u)·(integral) | **core**, proved; body unread (the place where the Frobenius-adjacent coupling s ↔ s+1 and the twisted logs S_s originate) |
| 2 | `k1gen_of_orth` / `hyperbolic_of_orthogonal` | ICL/RepAsm.lean:17 | orthonormal Σph ⇒ hyperbolic Σbe | core-ish, proved; leaf unread |
| 3 | `decomposition_of_hh` (`HhDecomp`) | FLN/EDecomp.lean:498; SE:124 | hh∘zSub = α-terms + β-terms + Z(low deg ≥ p) + pY up to degree D | core, proved; body unread |
| 4 | `minor_hits`, `e_one_vanish_of` → `hitsCapPos` | UTS/KOneConsequence.lean:33; SAB:42,58 | the cap lemma | core; **true** (hand-checked and scripted) |
| 5 | `TermBound_of`, `EntryStar_of`, `gainFactorialInequality` (StarArith) | FLN/NormNatCastLeOfDvd.lean:495; FLN/NormLeOfDvd.lean:309 | term-by-term valuation | core, proved; top level read, correct |
| 6 | `iN_le_cap`, `iN_le_min`, `entryCappedBound_of`, `entryExcessBound_of`, `EntryB_of` | FLN/EntryATwoAndB.lean:125-268; FLN/EntryAOneParity.lean:177 | per-(t,e) β-count ≤ min(al/p^e, capN); the α/dSet/alEven accounting | core; statements read, bodies not |
| 7 | `unimodular_genus_unique`, `weak_approximation_places` | ICL/IntWeak.lean:180; ICL/IntWAPlaces.lean:465 | local uniqueness of unimodular hermitian lattices; weak approximation for U(n) | standard (Jacobowitz; weak approximation for rational groups), proved |
| 8 | `pairs_standard_at_p`, `tensor_matrix_units_fact`, `four_products_from_one`, `IsomONB` | see §1.4 | StdStep / TensFact / FourProd / one copy | core-ish, proved; bodies unread |
| 9 | the `ea_Br*` conversion PI ↦ entryOp (overhang → topForm) | LOCALDIV Step C | that capN = ν₂ at tops, ν₁ elsewhere | definition to unfold |

## 4. Oddities

1. **The cap is per direction, and the Lean respects this.** HitsCapPos requires equal ξ across S. A cross-direction
   cap would be false (script, mixed directions). The Lean charges each (t,e) separately, so it is never needed.
2. **The rank-one weakness is structural.** With n′ = 2, or whenever several (t,e) share a target, the per-e charge
   overcounts. That is a valid lower bound (NUMTEST2). The Lean never uses tightness on the delivered side; PAIRING's
   upper direction is about the count, not this bound.
3. **u in RestGc is existential (it could be 0).** The jet bound holds for any integral u, so this gives no vacuity in
   a favourable direction. All the arithmetic content is "kernel ∈ InClass(hh_u)" (adm2), which was not re-verified
   here.
4. **α-terms (top–top) have no cap**, only degree. They are paid in full via dSet (gA) or alEven (gB). This is
   consistent, but it is why the V-top surplus and τ bookkeeping of PAIRING are needed.
5. **The j-index.** `PI j` uses ν_{j+1} (FGS:398-421), while gB/gA use `cap … j`. I did not check that the instantiation
   shifts j by one consistently; LOCALDIV's Σ_{j=1}^m suggests it does. **Unchecked.**
6. Nothing false-looking found.

**Prediction.** In genuinely higher rank (n′ ≥ 4), the Lean's bound should be close to tight: distinct t+e have
distinct budgets. A numerical test would need a CM theta with an inert place of residue degree ≥ 4, or the
model kernel exp(−(π/p)hh)·(random integral) with n′ = 4 paired against minors. The second is feasible with
`kronecker_lib`-style exact arithmetic, but only as a test of combinatorics, since RestGc is the real claim.

## 5. Coverage

Read:
- context files;
- `SE` (all); `SAB:1-125`; FGS:20-81, 120-270, 395-445;
- DER:1-80; UTS/OddLogRelation.lean:1-60; UTS/KOneConsequence.lean (all);
- FLN/NormLeOfDvd.lean:300-420; FLN/NormNatCastLeOfDvd.lean:495-560 plus its lemma list;
- `Formalism/GrowthSums/StatementA.lean:95-125`; `GaussJetBounds/StatementI.lean:10-25`;
- IKT/StatementInt.lean; IKT/IntegralInertOfWeakApprox.lean; IKT/KernelsIntegralInert.lean; IKT/DefsMM.lean (all);
  IKT/DefsInt.lean:26-175;
- ICL/IntWeak.lean:10-17, 171-200; ICL/RepAsm.lean:1-60; IKT/DefsRep.lean:17-34;
- `KernelLattices/ColumnData.lean:150-200`; `PeriodIntegrals/HermLatFin.lean`.

Not opened:
- the bodies of `restGc`, `restBeta`, `decomposition_of_hh`, `minor_hits`, `iN_le_*`, `gainFactorialInequality`,
  `hyperbolic_of_orthogonal`, `unimodular_genus_unique`, `pairs_standard_at_p`, `tensFact_of`, `fourProd_main`,
  `IsomONB`;
- the ea_Br* PI → entryOp conversion; `ClassSubst`.
