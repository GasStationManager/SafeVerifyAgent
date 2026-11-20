# NODE-COLENGTH: the lattice index of Hecke images at an inert place

Paths are relative to `.../scratchpad/art/lean/src/Formalism`. Abbreviations:
- `UQS` = `SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean`
- `DG` = `SharpRestriction/GrowthBounds/DataG.lean`
- `FGS` = `SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `CGL` = `SharpRestriction/GrowthBounds/CornerGLContinuity.lean`
- `TCB` = `SharpRestriction/GrowthBounds/TopChoiceBounds.lean`
- `SC` = `SharpRestriction/GrowthBounds/MultisetValuation/StabilizerCount.lean`
- `LS` = `SharpRestriction/GrowthBounds/LatticeSystems.lean`
- `SL` = `SharpRestriction/GrowthBounds/SelectionLemmas.lean`
- `IRZ` = `LocalToGlobal/GlobalTheory/IsResidueClassZero.lean`
- `CSD/` = `SharpRestriction/GrowthBounds/ColumnSpanDensity/`
- `PLB` = `SharpRestriction/GrowthBounds/ProjectionLemmaBaseLevel.lean`

## 0. Verdict (short)

1. **The colength bound is proved, and it is half-tautological by design.** `LemmaVVolumeGeneral` (FGS:832-847) says
   length(Mram/NP) ≤ vUnit·d·(τ + io). It is proved from `LPprime` by a sound-looking local-to-global argument
   (`core`, SC:131; `restJAll`, LS:4410). In `LPprime(t, D, κ)` the "bad fraction" κ is **not bounded there**: it is
   *defined* to be the infimum of the κ for which `LPprime` holds (`kapISet`/`kapI := sInf`, IRZ:281-285 and
   `ins`, IRZ:300; DefsInst.lean:37-45; AsmKap.lean:18-30). So `OrbitLatticeBounds` (CGL:180-191) is true by
   definition. The infimum is attained, by monotonicity in κ (Joints.lean:405).
2. **κ is paid for elsewhere:**
   - A prime is "served" (VV ≠ ∅, τ > 0) only if Sig = m·Σ_{t0} κ_{t0} ≤ x^{−ε} (`VV`, IRZ:296-297).
   - Otherwise it is NoGain/dropped (`NoGain`, IRZ:246-252; the third disjunct is Cand ∧ x^{−ε} < Sig).
   - A dropped prime gets only the Hecke-free gain g0⁺.
   - So the substantive content is the theorem that κ is small **on average over the weight window**:
     `Conclusion2` (PLB:76-91), meanKap ≤ C·N·N1/Y. It is consumed by `sum_kapv_le`/`sum_Sig_le`
     (`LogarithmicSums/SlopeEstimateOfLemmaBSlopeLine.lean:319-345`), and it rests on the local rank bound
     `admB2` (PLB:138-156). E-PAIR-1 lives there, not in the colength theorem.
3. **The proposed Hodge comparison ("average slope ≈ a/2") is the wrong model.**
   - The colength of T_r(M) is not governed by the elementary divisors of *one* transport L″→L, which do range
     over [0, a+b].
   - It is governed by the span of the transports from all ≈ q^m neighbours, q = p^{n′}.
   - Hand and machine computation for the base case (§3) gives a mean cost ≈ k/(2(q+1)) and a maximum ≈ k/(q+1)
     per rank. That is the a/p scale the Lean uses, not a/2.
   - So the Lean's t ≈ min(b, a/p^d) + O(a/p²) is of the right order. Its exact shape (Frobenius-distance pairing)
     is consistent with the Lucas/Steinberg digit coupling, but I did not verify it.
4. **Judgement:**
   - Yes, as a correct and proved statement, conditional on the in-tree proofs I read only in skeleton.
   - Could-not-determine for the non-trivial part: `admB2` (← `ColumnSystems.Pf.extendedClosedForm`) and the
     dropped-prime budget. Both are unopened.

## 1. Statement (mathematics)

**Local setting** (`HidaSetting`/`UnramifiedQuadraticSetting`, UQS:13-40):
- W is the unramified extension of ℤ_p of degree n′. Its residue field is F_q with q = p^{n′}, n′ even, and σ is
  Frobenius of order n′.
- O ⊃ W is a complete DVR with a uniformiser w such that w² = p, and Kf = Frac O. Positions s ∈ ℤ/n′ index the
  embeddings ι∘σ^s.

**Local group** (I read this off the Lean; it is not named there).
- The lattices are arbitrary W-lattices L ⊂ Qq^{m+1}, with no hermitian condition. The group acting is
  GL_{m+1}(Qq) (`Level.act`, DG:117), and the building is that of GL_{m+1}(Qq).
- The odd positions carry the dual weight (`lamAt`, UQS:68-69). This is the shape of a unitary group at a place
  where the conjugation pairs the embedding σ^s with a dual. I could not confirm from the Lean that the global
  group is unitary and the place inert.
- The "hyperspecial" structure is implicit: functions are on all lattices (`funMod`, DG:136-142), and
  `TrivStab`/`FinClasses` (DG:152-158) make M ≅ ⊕_{Γ-classes of vertices} (coefficient lattice).

**Coefficients:**
- V_λ = ⊗_s V(lamAt λ s) (`Vsp`, UQS:79-81), with base weight λ_{s} = (a_s, small, …, small, −b_s) at tops
  (`IsBaseWeight`, UQS:59-63).
- Two integral structures per vertex L:
  - HL(L), the dual-Weyl (H0, ∇) lattice (`H0`/`Hten`/`HL`, UQS:70-91); Mna uses it (`Htup`, DG:73-74);
  - HtupW(L), the Weyl (Δ) lattice (`Dl0`, DG:23-28); M uses it.
- M = Γ-equivariant (with character χ) functions F on lattice tuples with F(L) ∈ HtupW(L) (`Level.M`, DG:146).
  d = rank M (DG:150).
- p^e·Mna ⊆ M ⊆ Mna (`Sandwich`, DG:154). The constant e = ep ≈ Ce·f·k²·log_p a enters τ (IRZ:300-301).

**Hecke operator** (`Level.yv`, DG:152-155):
- (y_v F)(L) = p^{ArV}·Σ_{L″} F(L with L_v ↦ L″), summed over L″ with pL_v ⊆ L″ ⊆ L_v and [L_v : L″] = q^r
  (`IsEdge`, UQS:97-99).
- So y_v is T_r, the r-th elementary Hecke operator of GL_{m+1}(Qq), with r = 1 on the live path (IRZ:285).
- ArV = Σ_s Σ_{i<r} lamAt(λ)_s(i) (`Ar`, UQS:124-125). For r = 1 this is Σ_{even tops} a_s + Σ_{odd tops} b_s + O(c).
  It is the minimal power making y_v preserve the lattice: a single transport has elementary divisors
  p^{λ_0 − μ_0}, μ ranging over the weights.

**`LPprime(t, D, κ, c*)`** (UQS:205-220). Here 4(D+1) ≤ c* (the live value is c* = 8(D+1)). For every vertex L
there are edges e_i into L and vectors F_i ∈ V_λ such that:
- (a) F_i ∈ w^{−t}·HL(src e_i) and F_i ∈ Re(e′) for every edge e′ out of src e_i. Here Re(e) = w^{−Ar}·HL(src + w·tgt)
  is the coefficient lattice at the **midpoint** of the edge (`LeAt`/`HLe`/`Re`, UQS:107-131).
- (b) F_i ∈ w^{c*}·Re(e′) for every *other* edge e′ ≠ e_i out of src e_i. So δ_{src}·F_i is almost a delta under
  T at e_i.tgt.
- (c) The pairing be(F_i, G) = G(p^{Ar}F_i), against G ∈ Ntgt(L) = w^{−t}·HL(L)^∨ ∩ ⋂_{e into L} Re′(e), has a
  rank-n block left-invertible up to p^D (`GoodRankK`, UQS:200-203). Here n ≥ (1−κ)·dim V_λ.

In words: the transports into L from its neighbours, enlarged by w^{t}, span V(L) up to p^D, except on a
κ-fraction.

**`OrbitLatticeBounds`** (CGL:180-191): `LPprime` with t = ⌈tv⌉, D = Dp, κ = kapv, at every served orbit.
- kapv = kapLoc (IRZ:139-140). For p ≥ p0 this is kapI = sInf{κ : LPprime holds for **all** settings and all base
  weights λ with these a, b}.
- So the content is nil once the infimum is attained.

**`LemmaVVolumeGeneral`** (FGS:832-847):
- Hypotheses: sandwich, m ≥ 1, injectivity of the orbit-to-place map, `OrbitLatticeBounds`, Mram saturated in M,
  and m·Σ kapv ≤ 1/2.
- Conclusion: NP ⊆ p^{⌈τ⌉}·Mram, and length(Mram/NP) ≤ vUnit·d·(τ + io). Here:
  - τ = ep + Σ_{t0∈VV} m(⌈tv⌉ + Dp + 1) (IRZ:338-342);
  - io = 2·Sig·max Sv (IRZ:346-350).
- Note that d is the rank of the **whole** M, not of Mram.

**Mram, Vram.**
- Vram = Kf-span of cmp(ramSub of the level-0 global family lattice) (`vramC`,
  `LocalToGlobal/GroupLattices/ComparisonMaps/ChainFirstChainK.lean:104-107`). That is the image in the local
  p-adic space of a specified global subspace of forms.
- It is **not** an ordinary/non-ordinary or slope decomposition.
- Mram = M ∩ Vram, assumed saturated (`RamifiedPartSaturated`, CGL:226-229).
- The colength theorem is generic in V′ (Conclusion6, FGS:810-826): any saturated M ∩ V′ works, at the price of
  using d = rank M.

## 2. Argument (proof skeleton)

**A. Local to global (proved; skeleton read).**
- `gluing_statement_holds` (TCB:1639-1648) feeds `OrbitLatticeBounds`, the sandwich, saturation and `bg_sig_le`
  (Sig ≤ x^{−ε} ≤ 1/2) into `LocalServiceStatement`.
- `LocalServiceStatement` = `stmt6Loc` (SC:212) → `core` (SC:131-203).
- `core` uses `SL.Conclusion1` (SL:41-55), which is proved as `theta_kernel_expansion` (LS:4417). Its chain is
  `instance_of_lemma_J` ← `restJAll` (LS:4410, all components theorems: jLocal, jStep1, jSmith, jRank, jDelta, jEquiv).
- Mathematically, in four steps:
  1. A system of lattices latSys(σ), σ ∈ {base, ball, dual}^{VV}, built per vertex from (`piLattice₂`, LS:709):
     - ball ≈ w^{−t}·base;
     - dual ≈ w^{t}·base;
     - T_v(ball) ⊆ dual (`RestWalk`, LS:197-211).
  2. `RestJ` (LS:725-733): for each nonempty B ⊆ VV, p^{D+1}·latSys(B) ⊆ Σ_{v∈B} T_v(latSys(ball at v)) + span(C),
     with #C ≤ (∏_{v∈B} κ_v)·dna.
     - This is `LPprime` globalised. The w^{c*}-small off-diagonal values from (b) are absorbed by Nakayama
       (`le_of_le_smul_of_le_jacobson_bot`, LS:4384).
     - This is where c* ≥ 4(D+1) is used.
  3. Walking from base to the product of T's gives `AllButLE`: outside a set of size dna·m^{β+1}·e_{β+1}(κ), every x
     has p^{τ+βS}·x ∈ prodIdeal (SL:50-52; `AllButLE`, `SubspaceCounting/Statement.lean:9-12`).
  4. `lengthFromAllBut` sums over β. Each extra power of the exceptional fraction Sig costs S = max Sv. This gives
     length ≤ d(τ + 2S·Sig) = d(τ + io), and the sandwich adds e.
- The structure is an explicit near-inverse at each vertex up to p^{t+D}, made global by a triangular/Nakayama
  argument plus inclusion–exclusion over the κ-exceptional parts. It is not lattice-point counting.

**B. Why κ is small (the real content; not opened to the bottom).**
- `Conclusion2` (PLB:76-91): there is κ(a, b) ≥ 0 with mean over the weight box ≤ C·N·N1/Y, such that `LPprime`
  holds at t ≥ tI(a, b) with that κ. Here tI (PLB:66-74) = Σ_{odd tops y} min(b_y, a_{yPrev}/p^{dPrev}) +
  C·N·N1(a/p² + b′/p + La·a/(pk) + La·b′/k) + ….
- It is proved through `SecondPartClosed` (PLB:260):
  - the chain is `theorem_I_closed_form_holds` (`HermitianTensor.lean:18`) → … → `second_estimate_of_restrictions`
    (`CSD/TheoremIOfLatticeFunctorComparison.lean:45-51`);
  - it uses `midLP_of` (`CSD/LatticeCountPrimeMonoLevel.lean:183`) and `midMean_of`.
- The bound is assembled in three steps:
  1. The weight (a, small…, −b) is compared to the "flat" weight (A, 0, …, 0, −B) (`CloudWeightLowerBound`,
     `ResidueClassCount`, `CSD/RhoLowerBoundLargeConductor.lean:189-210`).
  2. dim V(flatW A B) = ∏ dimHar(A,B), with Sym^A ⊗ Sym^B∨ = ⊕_j Har(A−j, B−j) (`RestDims`, `CSD/MeanDefs.lean:37-40`).
  3. Per edge, a rank ≥ (1−κ)·dim/gaussianNumber(q, m+1) is needed. The per-edge rank lower bound on
     Sym^A ⊗ Sym^B∨ is **`admB2`** (PLB:138-156), with t = t0I = Σ_seg min(b, a/p^d) + Ct·N(a/p² + …)
     (`t0G4`, `ObjSeg.lean:439-442`) and explicit densities kapPI + Σ kapTI. `keyIneq_of` consumes it
     (`CSD/FactorizationBoundMonoLattices.lean:169`, `hrho := hA.2.1`).
- `admB2` comes from `AdmBE` ← `first_theorem_admitted_closed` (`PlaneCountTheoremWithConstants.lean:1238`).
  Behind that is `extended_windows_theorem` = `h.p15` = `ColumnSystems.Pf.extendedClosedForm`
  (`LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean:65`). The instance is proved; I did not open the body.
- The weights are then chosen so that the average turns into a pointwise bound for most served primes
  (`sum_Sig_le`; `pf_sum_Sig_le`, `PowFourLtCeilThresholdPrime.lean:1783`).

## 3. Hand computation: the true colength of T_1(M) in M, base case

**Model.**
- GL₂ over Qq, V = Sym^k at one embedding, H0 (monomial) lattice. That is the Mna side, which is what `core` bounds.
- Normalisation p^{Ar} = p^k.
- T(Mna)(L) ⊆ W(L) := Σ_{q+1 neighbours L′} p^k·HL(L′). Since Mna ≅ ⊕_{classes} HL(L_i), this gives
  colength(Mna/T Mna) ≥ d·(mean elementary divisor of W(L) in HL(L)).
- Conversely, an LPprime-type near-inverse is exactly a statement that W(L) has small elementary divisors.

**Script.** `.../scratchpad/colen/gl2q.py` does exact rational arithmetic over ℤ_p[t]/(irreducible quadratic) and
reduces by p-adic valuations. The first script, `gl2.py`, had a bug (all neighbours equal) and is superseded.

| p | n′ | q | k | mean ED (colength/rank) | max ED | k/(2(q+1)) | k/(q+1) | Hodge mean k/2 (one transport) |
|---|---|---|---|---|---|---|---|---|
| 5 | 1 | 5 | 24 | 1.60 | 4 | 2.0 | 4.0 | 12 |
| 7 | 1 | 7 | 70 | 4.39 | — | 4.38 | 8.75 | 35 |
| 3 | 1 | 3 | 60 | 7.31 | — | 7.5 | 15 | 30 |
| 3 | 2 | 9 | 40 | 2.34 | — | 2.0 | 4.0 | 20 |

- The elementary divisors are 0, 1, …, ≈k/(q+1), each with multiplicity ≈ q+1, as in p=5, k=24:
  [0×6, 1×6, 2×6, 3×6, 4].
- So the true local cost per rank is ≈ k/(2(q+1)) on average and ≈ k/(q+1) at worst. That is the a/p (here a/q)
  scale.
- The a/2 picture is the elementary-divisor distribution of *one* transport. The sum over neighbours divides it by
  ≈ #neighbours: a quantile 1/N_e of the one-transport distribution, which is the dimension count in `RhoL`'s
  dL = dimV/gaussianNumber(q, m+1) (`CSD/RhoLowerBoundLargeConductor.lean:52`).
- The two-position Frobenius-coupled case is in `pair.py`, with V = Sym^{k0} ⊗ Sym^{k1}∘σ over Q_{9}:
  - k0=12, k1=2: mean 1.69, max 4;
  - k0=9, k1=3: mean 1.55, max 3;
  - for comparison, min(k1, k0/p) is 2 and 3, and (k0+p·k1)/(q+1) is 1.8 in both cases.
  - Lucas collapse is visible (k = 9 = p²: only 2 cost-0 directions).
  - These sizes are too small, and GL₂ is outside the Lean's m ≥ 2N1+2, so they do **not** test the min(b, a/p^d)
    formula. They only show that costs are coupled across Frobenius-related positions.
- **Conclusion of (b):** no Hodge lower bound contradicts colength ≤ d·(tv + Dp) with tv ≈ a/p. The necessary
  local cost has the same order. The Lean's correction term La·a/(p·k) matches the shape of the excess I get from
  the dimension count on harmonic polynomials in m+1 variables, (a/q)·((bq/a)^{1/(m+1)} − 1) ≈ (a/q)·log(·)/k.

## 4. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `admB2` (via `extended_windows_theorem` = `ColumnSystems.Pf.extendedClosedForm`) | PLB:138-156; `PlaneCountTheoremWithConstants.lean:1228`; `AdmissibleFamilyNoKernel.lean:65` | per-edge rank ≥ (1 − kapPI − Σ kapTI)·dim(Sym^A⊗Sym^B∨)/gauss(q, m+1) of the midpoint-normalised pairing at t = t0I ≈ Σ min(b, a/p^d) + O(a/p²) | **core, not opened**: the mathematical heart of the colength |
| 2 | `admB3` + `kappaMarginBound` | PLB:158-176; `ObjSeg.lean:434-435` | density kp ≤ Cs·N·N1/Y; κ ≈ N(e^{−La/8} + kQ(m+N1k)/b′ + 1/Y + kE0/a) | core (explicit; not checked) |
| 3 | `Conclusion2` ⇐ `SecondPartClosed` (`second_estimate_of_restrictions`, `midLP_of`, `midMean_of`, `keyIneq_of`) | PLB:76-91, 260; `CSD/TheoremIOfLatticeFunctorComparison.lean:45-51` | mean of κ over the weight box ≤ C·N·N1/Y | core (skeleton read) |
| 4 | `CloudWeightLowerBound`, `ResidueClassCount`, `RhoLowerBoundLargeConductor`, `RestDims` | `CSD/RhoLowerBoundLargeConductor.lean:172-210`; `CSD/MeanDefs.lean:37` | general weight ← flat weight ← harmonic pieces; per-edge rank to LPprime | standard-ish (branching Sym^A⊗Sym^B∨ = ⊕Har; proved, not read) |
| 5 | `core` / `restJAll` / `lengthFromAllBut` | SC:131-203; LS:4390-4417, 197-211, 725-733 | LPprime ⇒ AllButLE ⇒ length ≤ d(τ + 2S·Sig) | core-glue (proved; Nakayama + inclusion–exclusion; read in skeleton) |
| 6 | `kapISet`/`kapI := sInf`, `VV`, `NoGain` | IRZ:281-285, 296-297, 246-252, 300 | κ defined as optimal; served iff Sig ≤ x^{−ε} | definition (makes OrbitLatticeBounds tautological) |
| 7 | dropped-prime budget (`pf_sum_Sig_le`, `drop`, `NoGainBoundAtTypePrimes`) | `PowFourLtCeilThresholdPrime.lean:635-727, 1767-1797`; IRZ:388 | primes with Sig > x^{−ε} lose the served gain; their total must fit the budget | core, **not opened** |
| 8 | `Sandwich` / ep | DG:154; IRZ:300-301 | p^{ep}Mna ⊆ M ⊆ Mna, ep ≈ f·k²·log_p a | glue (Weyl vs dual-Weyl) |

## 5. Oddities

1. **κ is an infimum, not a bound** (IRZ:281-285, `KapIDef`). Every "LPprime with small κ" statement on the live
   path is true by definition. The number-theoretic content is only in the averaged `Conclusion2` and in the
   served/dropped bookkeeping. This is legitimate, but it means E-PAIR-1's "if the index were ≈ a/p per pair,
   `LemmaVVolumeGeneral` would be false" is mis-aimed. A wrong index would make κ ≈ 1, VV = ∅ and every prime
   dropped. The falsity would then sit in `admB2`/`Conclusion2`, not in `LemmaVVolumeGeneral`.
2. **Units of t.** LPprime enlarges by w^{−t} with w² = p, while τ counts ⌈tv⌉ in powers of p. With the midpoint
   lattice (src + w·tgt) this may be consistent (a half-step in w-units equals a full step in p-units). I did not
   settle whether the Lean over-charges or under-charges by a factor 2. If under-charging, `admB2` is asked for half
   the natural cost, which is the risky direction.
3. **d vs rank Mram.** The colength of NP in Mram is bounded with d = rank M (FGS:847). That is weaker than per-rank
   of Mram. It is handled downstream (REVIEW-TWU "rank mismatch").
4. **Vram is a global-image subspace**, not a slope/ordinary part (ChainFirstChainK.lean:104-107).
5. **Local group** is GL_{m+1}(Qq) on all lattices, with dualised odd positions. I saw no hermitian structure. The
   "unitary group at an inert place" reading is inferred from context, not from this code.
6. `kapLoc` for p < p0 is an explicit formula min(1, kII·N·rG²·k·x^{−A}) (`kapIIf`, IRZ:117-118), not an infimum,
   used with `LPprime` at r = rG (`SmallOrderPrimes.lean:146`). I did not check how that `LPprime` is supplied.
7. Nothing false-looking in what I read.

## 6. Coverage

Read:
- UQS:1-254 (all);
- DG:1-207 (all);
- FGS:800-850;
- CGL:170-240;
- TCB:1625-1648;
- SC:120-212;
- LS:197-211, 360-470, 709-733, 2360-2470, 4380-4417;
- SL:23-55;
- IRZ:100-140, 180-300;
- `GrowthBounds/DefsInst.lean:30-60`;
- `InertJacobiLevels/AsmKap.lean`;
- `CSD/RhoLowerBoundLargeConductor.lean` (all);
- `CSD/LatticeCountPrimeMonoLevel.lean:90-200`;
- `CSD/MeanDefs.lean`;
- `CSD/TheoremIOfLatticeFunctorComparison.lean`;
- `CSD/FactorizationBoundMonoLattices.lean:150-240`;
- PLB:1-262;
- `ObjSeg.lean:380-444`;
- `SlopeEstimateOfLemmaBSlopeLine.lean:300-350`;
- `AdmissibleParameterJoins/GandSm.lean`;
- `PlaneCountTheoremWithConstants.lean:1150-1270`;
- `AdmissibleFamilyNoKernel.lean:30-70`;
- `ComparisonMaps/ChainFirstChainK.lean:100-119`;
- `SubspaceCounting/Statement.lean:9-20`.

Grep only: `HermitianTensor.lean:18`, `ColumnSystems.Pf.extendedClosedForm`, `kapIIf`.

Not opened:
- `ColumnSystems.Pf.extendedClosedForm` (the body behind admB2);
- `jLocal`/`jSmith` bodies;
- `CloudWeightLowerBound`/`ResidueClassCount` proofs;
- the dropped-prime budget;
- the p < p0 `LPprime` supplier.

Scripts: `.../scratchpad/colen/gl2q.py`, `gl2q_lib.py`, `pair.py`.
