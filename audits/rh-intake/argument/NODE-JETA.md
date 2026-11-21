# NODE-JETA: the per-monomial shape bound (`thmAJetA`) and the lattice tie on the OrbitPlaces route

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `GJ/` = `Formalism/GaussJetBounds/`, `GJP/` = `GJ/GaussJetProofs/`
- `IB` = `Formalism/IncomingBounds/IncomingBound.lean`
- `IW/` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/`
- `KEH` = `Formalism/LocalToGlobal/KernelLattices/ColumnData/KerEntHyp.lean`, `DKI` = `Formalism/LocalRingCardinality/DataKerI.lean`

Script: `numtest/jeta_lp.py` → `numtest/out_jeta_lp.txt` (stdlib, exact Fractions, a few seconds).

## 0. Verdict (short)

- **`thmAJetA` is correct mathematics, and the proof is an LP-duality argument, not a monomial-by-monomial count.**
  `thmAJetA := theorem_A_one_monomial_log_loss` (GJ/MonoShapeTop.lean:9). The body is `ThmAJetA_of`
  (GJP/TheoremAOneMonomialLogLoss.lean:15-236). Each frame coordinate gets a "radius" `rowRad`. Each Gaussian
  (bipower) factor of the exponential costs one p, and that cost is paid by a dual inequality
  l^α·r_i + l^β·r_j ≥ 1. The top budget A is **shared** across levels e (a level-e factor uses p^e top derivatives).
  The Lean charges Σ_e min(cap_e, A/p^e), which is at least the true LP maximum of the number of factors, so the
  bound is valid and weaker than optimal. I checked the assembly inequality by hand and exactly on 4000 random
  instances: 0 violations.
- **The generic frame reduction is honest.** It has three parts:
  1. The Gauss norm of a polynomial in the frame variables equals its value at a residually generic point, even
     after the Frobenius-power substitution on the top rows (`GaussPow`).
  2. Cauchy–Binet with an integral change of frame T moves to a frame with one dedicated partner row per
     (top, odd level, sign) and all other rows exactly orthogonal to the twisted top direction (`frameA_letter`).
     The Gram determinant is a unit by genericity (`generic_minor_norm`).
  3. The rank hypothesis exists only to have enough rows for these dedicated partners (`LabelsExist`).
- **Lattice tie: no Δ/∇ mismatch.**
  - Source and target lattices are both "forms with values in the **Weyl lattice Δ**". This is `delSq` = `weyl`,
    the span of divided-power row operators applied to the highest-weight vector.
  - Both are characterised by the **same** condition: the associated functional is integral on the products of
    minors ∇_J, which span ∇.
  - The duality Δ = ∇* used for this is the classical one, proved in-tree as `WeylLatticeDuality.Stmt`.
  - The jet polynomial lies in the ∇-span by Cauchy–Binet. Monomial-coefficient bounds convert to ∇-coefficient
    bounds without loss, because the ∇-span is saturated (`cutKW_holds`, standard-bideterminant leading terms).
  - No index [∇:Δ] is charged anywhere, and none is owed.
- Items 4 (`kerEnt_kform_true`) and 5 (`orbitIdentity…` body) are transport and reindexing. The arithmetic input of
  item 5 is the GAUSSCLASS theta expansion.

## 1. Statement

### 1.1 `ThmAJetA` (GJ/StatementG.lean:33-64)

**Data.**
- K is an ultrametric field of characteristic 0, l ≥ 3 prime, and d is even (the number of Frobenius positions).
- be ∈ K[[X_s : s ∈ ℤ/d]] satisfies `BHyp` (GJ/Statement.lean:85). BHyp has four parts:
  1. coefficients lie in an unramified subfield;
  2. torus invariance;
  3. `NoLowBidegree`;
  4. integrality of exp(de1 be) and exp(de2 be) in letter-log coordinates, i.e. the Dwork form.
- U is integral and g is the inverse of the entry log `entLog` (GJ/Statement.lean:120).
- The variables are ZV = ℤ/d × Fin N0 × Fin N1 = (position, frame row k, column b).
- x is an integral frame, x(s,k,a) with ‖x‖ ≤ 1.
- `frameM x` (GJ/StatementC.lean:63) expresses the matrix entry (s,a,b) as Σ_k x(s,k,a)·W(s,k,b), where W are the
  frame coordinates.

**The kernel.** In frame coordinates the kernel is

  Θ_x = U(g(entries(W))) · exp(ε·bSum(frameM x, be)), with bSum = Σ_{(a,b)} be(entries_{·,a,b}).

**Hypotheses on the monomial κ in W.**
- Tops TT: at each s ∈ TT, row 0 has total degree nu1 s, the number of minors.
- At each s, the non-top rows have total degree Dl(s) = size − nu1 (s ∈ TT) or size (IB:105).
- `spec` assigns to some rows (s,k) a label (s0, j). Here s0 ∈ TT, j is odd, s = s0 + j, the row is not a top row,
  and l^j ≤ nu1 s0 if j > 0, l^{|j|} ≤ size s if j < 0.
- **Cap**: for each (s0, j), Σ over rows labelled (s0, j) of the row degree is ≤ capL(s0+j). Here capL = nu2 at a top
  and nu1 elsewhere (IB:103).
- **Frame orthogonality**: every unlabelled non-top row (s,k) at odd distance j from a top s0, within the admissible
  range, satisfies ‖Σ_a x(s0,0,a)^{l^j}·x(s,k,a)‖ ≤ |l|. For j < 0 the condition is ‖Σ_a x(s0,0,a)·x(s,k,a)^{l^{|j|}}‖ ≤ |l|.

**Conclusion.**

  ‖κ!·coeff_κ(Θ_x)‖ ≤ |l|^{ Σ_{s∈TT}(topTerm_s − γ·Wcap_s) + Fnum(Dl) − d·N0·N1·(log_l a + 1) }.

The definitions:
- γ = l/(l²−1) (IB:10).
- topTerm (IB:113) = Σ_{odd e < dTop}(nu1/l^e − capL(s+e))₊ + Σ_{odd e > dTop} nu1/l^e. Here dTop is the least odd
  distance to another top (IB:107).
- Wcap (IB:109) = sup{capL(s−i) : i odd, l^i ≤ size(s−i)}.
- Fnum(D) = γ·ΣD − maxFlow(D) (IB:28) is the Gaussian-free base LP. It is ≥ ρ·ΣD, with ρ = 1/(l²−1).

### 1.2 The lattice-tie fields

**`KerEnt.lat_S` (DKI:100-104).** At a level-free place w and level i < m, for a class-indexed function φ the
following are equivalent:
- φ = emb(x) with x ∈ locW_w((Tw.fm u μ).lat i);
- φ ∈ Fi, and for each class c there is v with ev v = φ_c and |prS(v)(∇_J)| ≤ 1 for every column choice J.

Here `nablaX` (DKI:37) is ∇_J = ∏_s ∏_c det(X_{s,i,J(c,k)})_{i,k < colLen c}, a product of column minors of the
generic matrix X with rows 0..colLen−1 and strictly increasing column sets.

**`levelFree_lattice_condition` (latT, DKI:106-110).** The same statement at level i+1, with the condition |prT(v′)(I)| ≤ 1
for all I. On the live path prT = `onMin` ∘ `tgtPh` (KEH:118-120), i.e. again "the functional evaluated on ∇_I".

**`kform` (DKI:115-121).** If ev v′ = Kmap(ev v), then prT(v′)(I) = un · prS(v)(applyAt0(Th, Gxz I)). Here
Gxz I = ∇_I(X·Z) is the target ∇-element evaluated at X·Z, and applyAt0 is the factorial (Fischer) jet pairing in Z.

**`CutKW.KW` (`PeriodIntegrals/NablaSpans/ExpansionCoeffValuationGe.lean:50`).** KvalGe(B) ⇔ ExpansionCoeffValuationGe(B):
- KvalGe(B): all monomial coefficients of applyAt0(Th, Gxz I) are ≤ l^{−B}.
- ExpansionCoeffValuationGe(B): applyAt0(Th, Gxz I) = Σ_J c_J ∇_J with |c_J| ≤ l^{−B}.

It is proved as `cutKW_holds` from `MinorProdSpanHasCompl` (`…/MinorProdSpanHasCompl.lean:18`): for every
commutative ring R, the R-span of the products of minors has a complement in R[X].

## 2. Argument

### 2.1 `thmAJetA` as mathematics (the Lean says; read in full)

The proof is a dual-feasibility argument.

**Step 1: the radii (TheoremAOneMonomialLogLoss.lean:24-59).**
- Take an optimal dual sig of the base LP for Dl (`lemmaFa`, strong duality).
- Take radii eps on the tops from `rowRadiusAssembly` (`ThmAAssembly`, GJ/StatementA.lean:19).
- Define `rowRad` (GJ/StatementA.lean:10):
  - eps(s) on a top row;
  - max(sig, 1 − l^j·eps(s0)) on a row labelled (s0, j > 0);
  - max(sig, l^{−|j|}) on a row labelled (s0, j < 0);
  - sig on every other row.

**Step 2: LemmaRA (GJP/LemmaRA.lean:55-170).** Suppose every pure monomial W_i^{l^α}W_j^{l^β} ≤ κ that fails the good
weight 1/(l−1) in bSum satisfies l^α·r_i + l^β·r_j ≥ 1. Then ‖κ!·coeff_κ Θ‖ ≤ |l|^{Σκ_i(γ − r_i) − |ZV|(log a + 1)}.

Why this is true (I reconstruct):
- **Radius.** Use the radius ρ + r_i per degree. U∘g has weight ≥ −ρ·deg (`LemmaSt`).
- **Good monomials.** LemmaS gives be weight 1/(l−1) − ρ·deg on non-bipower monomials. In frame coordinates,
  non-pure monomials of a bipower term carry a multinomial coefficient divisible by l, so they are good too
  (`PureCross`).
- **Bad pure factors.** A bad pure factor has weight 1/(l−1) − 1 − ρ·deg ≥ 1/(l−1) − (ρ + r)·deg by the dual
  inequality.
- **exp.** exp preserves weight 1/(l−1): v(m!) ≤ (m−1)/(l−1).
- **Legendre.** v(κ_i!) ≥ κ_i/(l−1) − log_l a − 1. Since 1/(l−1) − ρ = γ, each degree nets γ − r_i, less one log per
  coordinate.

This is the brief's "term-by-term" bound, organised as weighted Newton polygons. It is correct.

**Step 3: dual feasibility for every bad pure monomial (:74-206).** `jet_bipower`/`jet_collapse` and LemmaS show that
a bad pure monomial joins two rows at positions s, s′ with s + α = s′ + β and α + β odd. The cases:
- **Top–partner, labelled (s0, j).**
  - j > 0: l^α·eps + l^β·(1 − l^j·eps) = l^β ≥ 1.
  - j < 0: l^α·eps + l^{α+|j|}·l^{−|j|} ≥ 1.
- **Top–unlabelled row.** Impossible. Frame orthogonality and `FramePure` (GJP/FrameCoeffMulLin.lean:179) give
  Σ_a x_top^{l^α}x_k^{l^β} ≡ (Σ_a x_top^{l^j}x_k)^{l^β} ≡ 0 mod l. The extra l makes the factor good. Mixed columns
  b ≠ b′ have coefficient 0, since be acts entry by entry.
- **Non-top–non-top.** IsDualAll gives l^α·sig_s + l^β·sig_{s′} ≥ l^β·(l^{α−β}·sig_s + sig_{s+α−β}) ≥ 1.
- **Top–top.** Here eps ≥ l^{−dTop} and α − β ≥ dTop (R.2.2.2).

I checked each case by hand.

**Step 4: assembly (`ThmAAssembly`, reconstructed and checked).**

  Σ_i κ_i(γ − rowRad_i) ≥ Σ_s Dl_s(γ − sig_s) [= Fnum(Dl)]
     + Σ_tops [A·γ − A·eps − Σ_{j>0} cap_j(1 − l^j·eps)₊]
     − Σ_tops Σ_{j<0} cap_{s0+j}·l^{−|j|} [≥ −γ·Wcap].

The top bracket ≥ topTerm by the one-variable LP. The primal is max Σ n_j subject to n_j ≤ cap_j and Σ_j l^j·n_j ≤ A,
i.e. **the shared top budget**. The dual is min_eps A·eps + Σ cap_j(1 − l^j·eps)₊. The primal maximum is
≤ Σ_j min(cap_j, A/l^j) = A·γ − Σ_j(A/l^j − cap_j)₊, using A·γ = Σ_{odd j} A/l^j.

With a top at odd distance dTop, eps ≥ l^{−dTop} is forced. Then level dTop is charged in full and levels beyond it
are free. That is exactly topTerm's shape (term 0 at e = dTop; full A/l^e for e > dTop).

### 2.2 The brief's checks

**(i) The optimisation.** The brief's inequality is, for one top of size a with caps cap_e:

  v_p(a!) − a/(p²−1) − Σ_e n_e ≥ a·γ − (log_p a + 1) − Σ_e n_e ≥ Σ_e (a/p^e − cap_e)₊ − (log_p a + 1),

with n_e ≤ min(cap_e, a/p^e).

Hand example (`out_jeta_lp.txt`): p = 5, a = 125, cap_1 = 3, cap_3 = 0.

| quantity | value |
|---|---|
| v(125!) | 31 |
| aρ | 5.21 |
| aγ | 26.04 |
| v(125!) − aρ − 3 factors | 22.79 |
| topTerm = (25−3)₊ + (1−0)₊ + 0.04 + … | 23.04 |
| Lean bound, topTerm − (log₅125 + 1) | 19.04 ≤ 22.79 ✓ |

Random exact check: 4000 instances with l ∈ {3,5,7,11}, A ≤ 3l⁴, random caps, and dTop ∈ {∞,1,3,5,7}. The checks
were the assembly inequality with the optimal eps, the bound charged ≥ LP primal, and every top–partner dual
constraint. Result: 0 violations.

**(ii) Interactions.**
- **Between levels.** The budget is shared, and the Lean is conservative (it sums mins).
- **Two tops.** Two tops at odd distance are paid through eps ≥ l^{−dTop}. At signal places tops sit at even
  positions and partners at odd ones, so dTop = ∞ (ORBIT). The two-tops NUMTEST is consistent with this.
- **Partners preceding a top (j < 0).** These are charged γ·Wcap per top, a genuine but small loss (≈ γ·b at signal
  places).

**(iii) The generic frame.**
1. `thmAGauss_of` (GJP/ThmAGaussOf.lean:13-56) passes to a residually generic Y (`IsGeneric`: every primitive
   integral polynomial has norm 1 at Y, GJ/StatementM.lean:12).
2. KvalGe is a statement about the Gauss norm of the jet as a polynomial in the frame variables.
3. `GaussPow` (GJ/FrameJetEval.lean:49): the coefficient norm is ≤ the value at Y^{k} for any positive exponents k.
   So it suffices to bound the jet at genFrame = Y^{l^m} on top rows and Y elsewhere (GJ/StatementM.lean:16). The
   twist l^m makes the negative-j partner directions Y_top^{l^{m+j}} polynomial.
4. `theorem_A_generic` (GJP/Generic.lean:133-226) assigns rows e(s,i) = i (+1 at a top) to the labels. It shows that
   the Gram matrix ⟨λ_i, Y_{s,e(i′)}⟩ has unit determinant by specialisation to a monomial determinant
   (`generic_minor_norm`).
5. `frameA_letter` (GJP/FrameA.lean:48) then writes the original rows as y = T·x with T integral. The new rows x are
   exactly orthogonal to every λ_i except their own.
6. The minors of rows of T·x are integral combinations of minors of x (Cauchy–Binet).
7. `op_prod_shape` (GJP/ThmAOp.lean:250-298) gives the row degrees: the top row has degree = #minors, and other rows
   at a top have degree ≤ #columns of height ≥ 2 = nu2. `thmAOp` (:312-406) feeds these to thmAJetA with the
   injective labelling (one row per label, `hinj`), so the cap sum is a single row degree ≤ capL.

**(iv) Errors and the rank hypothesis.**
- **d·N0·N1·(log a + 1)** is the Legendre digit-sum loss, one log per frame coordinate (`factValA`,
  GJP/LemmaRA.lean:13). It is not tied to the number of factors.
- **The rank lower bound** is `LabelsExist` (GJ/FrameJetEval.lean:39): 2·log_l a + 2 ≤ N0 − 1. It guarantees that
  every position has N0 ≥ #labels + [top] rows. The labels are one per odd j > 0 with l^j ≤ a and one per odd j < 0
  with l^{|j|} ≤ a, so ≈ log_l a + 1.
- Without enough rows one cannot dedicate a separate partner row to each (top, level), and the remaining rows could
  not all be made orthogonal. The cap would then have to be shared among levels in one row. The condition is about
  twice what is needed.

### 2.3 The lattice tie: which lattice is where (the Lean says)

**Source and target forms take values in Δ.**
- The global integral forms are `IntSpan`/`RatSpan` (`LocalToGlobal/Columns/TiedCF.lean:51-61`; identical copies in
  `HermitianForms/TiedStep.lean:47`, `GlobalSchurBounds/ProductFirstZerothParts.lean:427`, `FlipTwoThree.lean:392`).
  They are spans of r·⊗_τ f_τ with f_τ ∈ **`delSq ℤ n λ_τ`**.
- `delSq` (`LocalRingCardinality/DataCoeff.lean:52`) = `GradedWeylDivisibility.weyl` (`GradedWeylDivisibility/StatementA.lean:71`)
  = span of `applyWord` (iterated `rowDiv`, the k-th divided power of a row operation) applied to `hw`. Here
  hw = ∏ leading principal minors^{ν_s − ν_{s+1}} (StatementA.lean:63).
- So delSq is **Δ(λ) = U_ℤ·v_λ**, the small lattice. The same file defines `dualWeyl` (∇, :24) by column-unipotent
  invariance. It proves `BideterminantMem` (products of minors ∈ ∇, :80) and `WeylLeDual` (Δ ⊆ ∇).
- The source side: `latS_at_class` (IW/FormsLatticeAtClassIffTwistedPolynomial.lean:30-46) relates IntSpan (Δ) in a
  local basis Bm to `srcFun v ∈ DelW` in the adapted basis. `DelW` (`UnipotentAdelicQuotients/WeylLatDual.lean:54`)
  is again `weyl ℤ` = Δ.
- The target side: `kerEnt_latT` (IW/KernelDatumLatticeTargetSideTrueChains.lean) uses `latOf … delAtr` and
  `mem_localisedWeylLattice_iff_targetPairing_integral` (`delAtr`, the Δ lattice).

**Kernel entries are computed with the canonical pairing against ∇.**
- `prSC` = canInv ∘ srcFun (KEH:105). canM (KEH:72) sends a functional φ to y ↦ φ(DeX(y)), where
  DeX(y) = ∏ det(X·y)_{minor} (WeylLatDual.lean:46) is the reproducing element.
- `WeylLatticeDuality.Stmt` (WeylLatDual.lean:61) says: φ(∇_J) integral ∀J ⇔ φ(DeX(·)) ∈ DelW (Δ-valued). This is
  Δ = ∇*. It is proved by `stmt_holds` (IW/WeylLatticeDualityPadicMinors.lean:172) and `mainProof`
  (IW/MainProof.lean:15) from dual bases with integral transition matrices (`dualData`) and a Fock reproducing
  formula. I read the top level only.
- `prSC_int_iff` (FormsLatticeAtClassIffTwistedPolynomial.lean:20) applies it. Target: prTC = onMin ∘ tgtPh, the same
  functional evaluated on target ∇_I.

**Hand check of the duality, weight λ = (2), N = 2.**
- DeX(y) = (y₀X₀ + y₁X₁)² = y₀²X₀² + 2y₀y₁X₀X₁ + y₁²X₁².
- With φ integral on ∇ = {X₀², X₀X₁, X₁²}, the function is φ(DeX(y)) = c₀y₀² + 2c₁y₀y₁ + c₂y₁².
- That is exactly Δ(2) = span{y₀², 2y₀y₁, y₁²}, not ∇(2). So the statement is the correct duality, not the false
  Δ = ∇.

**The kernel step, end to end.**
1. Source x ∈ lat i means its functional φ_S is integral on all source ∇_J.
2. Cauchy–Binet gives ∇_I(XZ) = Σ_J ∇_J(X)·(minor of Z). So applyAt0(Th, ∇_I(XZ)) ∈ span ∇_J(X).
3. Its monomial coefficients are ≤ p^{−B} (ThmA).
4. `cutKW_holds` turns that into ∇_J-coefficients ≤ p^{−B}. The ∇-span is a direct summand
   (`minorSpanCompl`, `PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/RenameInitMinor.lean:77`: the
   semistandard bideterminants span it, with monic and pairwise distinct column-lex leading monomials; complement
   = the other monomials).
5. Therefore |φ_T(∇_I)| = |un·φ_S(Σ c_J ∇_J)| ≤ p^{−B}.
6. latT turns this into "target form ∈ p^{B}·Δ-lattice".

Δ appears on both sides and ∇ appears only as the test vectors on both sides, so **no [∇:Δ] index** is owed or
charged.

**The slope side.** `IntSpanAt` (`GlobalSchurBounds/FlipTwoThree.lean:392`) uses the same delSq. The adjacent Fock
normalisation `nfAll` (:388) divides by ⟨hw, hw⟩_Fock. The lattice in `ColGe`/`KGe` is (Tw.fm).lat, the object of
latS/latT (ORBIT). I did not open the covolume computation itself; as far as read, one integral structure (Δ) is
used throughout. The "M = Weyl, Mna = dual-Weyl" pair of NODE-COLENGTH belongs to the Hecke route and does not
occur here.

### 2.4 Items 4 and 5

**`kerEnt_kform_true`** (IW/KernelEntriesFormTrueChains.lean:229, outline read).
- It assembles:
  - canInv specs on both sides;
  - `jetMap_identity_transport_complex_to_padic`;
  - `kernelForm_complex_polynomial_identity`, the complex identity "Kmap = jet pairing of the theta kernel";
  - cancellation of the det(B)^{±sSharp} and ρ-character scalars into `unF`.
- This is **transport bookkeeping**. Its one content leaf is the complex polynomial identity, not opened.

**`orbitIdentity_all_of_integralClass_hostLog`** (SP/OrbitIdentityAllOfIntegralClassHostLog.lean:113-236, 173-236
read now).
- Lines 173-236 reindex orbits (`orb_bijective`, `πv`), compose substitutions, and factor exp over orbits
  (`expFactor_allOrbits_eq_prod_orbits`).
- **Bookkeeping**. The content is the Θ-expansion hZ/hR1 (GAUSSCLASS, `Th1.D.b0`).

## 3. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `lemmaS` | GJ/Statement.lean:98 (stmt) | be has weight 1/(l−1)−1 everywhere, 1/(l−1) off bipowers X_s^{l^α}X_{s′}^{l^β} (s+α=s′+β, even/odd) | where BHyp (Dwork, torus) becomes the Gaussian shape | core, not read here (LOCALDIV/GAUSSCLASS territory) |
| 2 | `lemma_R_log_loss` (LemmaRA) | GJP/LemmaRA.lean:55,170 | weighted-radius jet bound given dual inequalities on bad pure monomials | the valuation engine | core; top level read, correct |
| 3 | `rowRadiusAssembly` (ThmAAssembly) | GJP/CapacityLeReachCapacity.lean:278 | ∃ eps: Σκ(γ − rowRad) ≥ Σ(topTerm − γWcap) + Fnum(Dl) | the optimisation | core; body not read, statement re-derived and checked exactly (jeta_lp.py) |
| 4 | `frame_pure_weight` | GJP/FrameCoeffMulLin.lean:179 | orthogonal-mod-l rows give good weight; cross-column coefficient 0 | generic frame | core-ish, Frobenius in char l, true |
| 5 | `lemmaFa`, `dualRadiiInequalities` | IncomingBounds/WeightIdentities.lean:17; GJP/OneLetterRadiusIdentity.lean:124 | LP strong duality; radii inequalities | glue / standard (LP duality) |
| 6 | `theorem_A_generic`, `frameA_letter`, `GaussPow`, `LabelsExist` | GJP/Generic.lean:133; FrameA.lean:48; FrameJetEval.lean:39,49 | generic frame reduction | read | standard (Gauss norm = generic value), honest |
| 7 | `WeylLatticeDuality.Stmt` (`stmt_holds`/`mainProof`) | WeylLatDual.lean:61; IW/WeylLatticeDualityPadicMinors.lean:172 | φ integral on ∇ ⇔ φ∘DeX ∈ Δ | the Δ = ∇* duality | standard (Carter–Lusztig / DEP / Jantzen II.4), top level read |
| 8 | `minorSpanCompl` | …/RenameInitMinor.lean:77 | the span of products of minors is a direct summand of R[X] | `cutKW_holds` | standard (DEP standard bideterminants), read |
| 9 | `lattice_iff_integralWeyl_coordinates`, `hermitianChart_complex_rational_integral_forms` (`val_tied`), `dualLattice_localBasis_iff_unimodularCompanion` | IW/…Statement.lean | global lattice localised = Δ-valued in local bases; local bases of L^# = those of the companion at level-free w | latS leaves | core-ish, statements read, bodies not |
| 10 | `mem_localisedWeylLattice_iff_targetPairing_integral`, `localisation_formLattice_iff_classValues_weylLattice` | IW/…Statement.lean | target analogue (delAtr) | latT | core-ish, statements read |
| 11 | `kernelForm_complex_polynomial_identity` | inside KernelEntriesFormTrueChains | Kmap = jet pairing of the theta kernel over ℂ | kform | core, not opened |

Ranked: 1 (upstream), 3 (checked numerically), 9/10, 11, then the rest.

## 4. Oddities

1. **topTerm uses nu1 (all minors), while Cor uses the gap nu1 − nu2.**
   - At a top, row 0 has degree = #minors, because the overhang is not peeled in this library. Its factorial pays
     γ·nu1.
   - The other rows at a top (≤ nu2 each) are base-LP rows. This differs in form from NODE-HIGHERRANK's "topForm
     overhang", but it is consistent.
   - Cor ≤ ThmA via `base_term_le_top_term`.
2. **Partners before a top (j < 0)** are charged with the crude radius l^{−|j|}, giving the γ·Wcap loss. It is valid
   and could be sharpened. ORBIT oddity 1 (the budget of that loss) is unchanged by this node.
3. **The rank condition is twice what is needed** (2·log a + 3 vs ≈ log a + 2). Harmless, but it is a structural
   hypothesis that must hold at every level of the chain.
4. **`MinorProdSpanHasCompl` is stated for every commutative ring R.** That is true, by base change of the ℤ-basis,
   and it is proved that way (leading terms are monic over ℤ).
5. **The name `nablaX` is apt.** ∇_J are test vectors spanning ∇. The forms themselves are Δ-valued. A reader who
   expects "∇-valued forms" will misread latS. The duality makes the two consistent.
6. Nothing false-looking.

## 5. Coverage

Read:
- GJ/StatementG.lean (all), MonoShapeTop.lean (all), StatementA.lean (all), StatementC.lean (all), Statement.lean (all),
  StatementM.lean:12-24, FrameJetEval.lean:39-55;
- GJP/TheoremAOneMonomialLogLoss.lean (all), LemmaRA.lean:13-100, ThmAOp.lean:250-406, Generic.lean (all),
  FrameA.lean:48-75, 196-240, ThmAGaussOf.lean (all);
- IB:1-130;
- DKI:1-140; KEH (all);
- NablaSpans/ExpansionCoeffValuationGe.lean, MinorProdSpanHasCompl.lean (all); WeightFramesOfSubgroupFrames.lean,
  GenericFramesLetters.lean (all); PeriodIntegrals/MinorSpanCompl.lean; RenameInitMinor.lean (all);
- IW: TrueChainsKernelDatumSourceSideLattice.lean (all), three leaf statements, FormsLatticeAtClassIffTwistedPolynomial.lean
  (all), MainProof.lean (all), WeylLatticeDualityPadicMinors.lean:172-240, KernelDatumLatticeTargetSideTrueChains.lean
  (all), two target leaf statements, KernelEntriesFormTrueChains.lean (outline);
- WeylLatDual.lean (all); GradedWeylDivisibility/StatementA.lean:1-140; LocalRingCardinality/DataCoeff.lean:1-80;
  LocalToGlobal/Columns/TiedCF.lean:1-80; FirstKernelLawReading.lean:120-175; the IntSpan copies cited above;
- SP/OrbitIdentityAllOfIntegralClassHostLog.lean:173-236.

Not opened:
- the bodies of `rowRadiusAssembly`, `lemmaS`, `frame_pure_weight`, `PureCross`/`ExpWtLe`, `dualData`,
  `fock_reproducing_formula`, `sSBasis`;
- the latS/latT leaf bodies (`val_tied`, `isLocBasis_dual_iff_N`, `lattice_iff_integralWeyl_coordinates`,
  `mem_locW_iff_prTC_le_one`);
- `kernelForm_complex_polynomial_identity`; the covolume and height computation.
