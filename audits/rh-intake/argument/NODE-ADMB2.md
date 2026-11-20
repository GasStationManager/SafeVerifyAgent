# NODE-ADMB2: the per-edge rank bound, its units, and the dropped-prime budget

Paths are relative to `.../scratchpad/art/lean/src/Formalism`. Abbreviations as in NODE-COLENGTH, plus:
- `OS` = `SharpRestriction/GrowthBounds/ObjSeg.lean`
- `CS` = `SharpRestriction/GrowthBounds/ColumnSystems.lean`
- `LS` = `SharpRestriction/GrowthBounds/LatticeSystems.lean`
- `IRZ` = `LocalToGlobal/GlobalTheory/IsResidueClassZero.lean`
- `IRZg` = `SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
- `P4` = `LocalToGlobal/GlobalTheory/PowFourLtCeilThresholdPrime.lean`
- `LRS` = `LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean`
- `WSS` = `SizeWindowBrackets/WindowSettingSatisfiable.lean`

## 0. Verdict

1. **E12 is closed: there is no factor 2.**
   - w is a genuine uniformiser of a *ramified* quadratic extension O/W. `HidaSetting.w_sq : w² = p` (UQS:30), and
     `Irreducible w` with #(O/w) = p^{2n′} (UQS:36). So v(w) = ½·v(p). The field Qq is unramified, but the
     coefficient ring O is not: e = 2 and f = 2 over W.
   - The enlargement w^{−t} is applied on **both** sides of the pairing: F ∈ w^{−t}·HL(src) and G ∈ w^{−t}·HL(L)^∨.
     So the pairing loses w^{−2t} = p^{−t}. Equivalently, the integral transport pairing must have elementary
     divisors ≤ p^{t+D}.
   - The global walk charges exactly this. `walk_allBut_bound` (LS:216-313) uses ball→base (w^t) and base→dual (w^t),
     counts the exponent 2·(τ + βS) in w-units, and rewrites it with `pow_mul, hw` to p^{τ+βS} (LS:296-311).
   - So t is effectively a p-exponent of the integral pairing, and τ = Σ m(⌈t⌉ + D + 1) is in p-units. The two agree.
   - The w-units appear only as bookkeeping halves. In `bbSpec` (OS:217-221) the Fock lattice scales monomials by
     p^{−v_p(μ!)/2} on each side, and the midpoint lattice src + w·tgt (UQS:107-111) is the other such half.
2. **`admB2` is a reduction theorem, not a final bound.**
   - Its κ is kapPI + Σ_j kapTI. Here kapTI = `badShare` of a model Fock pairing on "segment block lattices", and it
     is again *defined* as the optimal bad share (OS:259-268).
   - The real counting content is split three ways:
     - `ModelLatticeRank`/`admB3`: a block-dimension count;
     - `OrderBoundDigits`/`ColumnFamilyLowerSet`: every kept block has order ≤ t0I;
     - the flipOneThree counting statement: the mean of kapT over the weight window is ≤ C(t+1)N1/Y.
       It is proved trivially when Y is small, and otherwise reduced to `RemainingCountingStatement`
       (`CountingStatementReduction.lean:2423-2458`).
3. **The closed form is a Pieri/Lucas count, and its threshold is the right one.**
   - (b) below derives the cost min(b, a/p^d) as P·o, with P = p^{G−d} and o the number of Pieri contractions.
   - Exact GL₂ p-adic computation is consistent with it as an upper bound that is nearly sharp.
   - A GL_{m+1} dimension count shows that for large m almost all of the dimension sits at cost ≈ the full min. So
     the bound fails visibly below the threshold, and κ is small only within an O(log/m) relative margin. That margin
     is the La·b′/k, La·a/(pk) term of t0I.
4. **The dropped-prime budget is tiny.**
   - Mean Sig ≤ m·#TT·x^{−12} over the weight box (`pf_sum_Sig_le`, P4:1783).
   - Markov over weights and Mertens over p < X′ then choose a weight at which the dropped primes' total loss is
     ≤ (2/θ+4)·s0·2x^{ε/3}·4mTa, with θ = x^{−ε}. That is ≈ x^{−12+4ε/3}·m²·#TT·T·a, far inside x^{3+O(ε)}·b.
5. **Judgement.** Correct and proved, as far as read. The remaining unread content is `RemainingCountingStatement`
   and the block-lattice realisation inside `extendedClosedForm`. Nothing false-looking.

## 1. Statements (Lean, unfolded)

**Setting** (`UnramifiedQuadraticSetting`, UQS:34-37; `HidaSetting` UQS:13-31):
- W is an unramified DVR with uniformiser p and residue field of size q = p^{n′}, n′ even, p ≥ 5. σ lifts Frobenius
  and has order n′.
- O ⊃ W is a DVR with **irreducible w, w² = p**, #(O/w) = p^{2n′}, and every integer a square in O.
- `vO`/`vK` normalise by ramE = v_O(p) = 2, so they are **p-units** (ObjPol.lean:27-40).

**Edge** (`IsEdge`, UQS:97-100): src ⊆ tgt, p·tgt ⊆ src, [tgt : src] = q^r. Live r = 1. A vertex has
gauss(q, m+1) = (q^{m+1}−1)/(q−1) edges into it (OS:432).

**`LPprime(p, n′, ι, σ, w, r, λ, t, D, κ, c*)`** (UQS:205-220, read):
- 4(D+1) ≤ c*.
- For every lattice L there are edges e_i (tgt e_i = L) and vectors F_i such that:
  1. F_i ∈ Nsrc = w^{−t}·HL(src e_i) ∩ ⋂_{e′ out of src} Re(e′);
  2. F_i ∈ w^{c*}·Re(e′) for each other edge e′ out of src e_i;
  3. the pairing be(F_i, G) = G(p^{Ar}F_i) has a block that is left-invertible up to **p^D**, of size
     n ≥ (1−κ)·dim V_λ (`GoodRankK` with π = p, UQS:200-203). This is tested against
     G ∈ Ntgt = w^{−t}·HL(L)^∨ ∩ ⋂_{e into L} Re′(e).

**`admB2`** (PLB:138-156). For all settings, under `HypI`, `WinX`, `CBoundI` and 4·totalDegreeBudget < c, for every
edge e:

> RhoGE p beHH (CCe t c e) (CCe′ t c e) D X, with t = ⌊t0I⌋, D = totalDegreeBudget, and
> X = (1 − kapPI − Σ_j kapTI_j)·dimHH / gauss(q, m+1).

The pieces:
- **VHH** = ⊗_{s∈TT} Sym^{A_s} ⊗ (Sym^{B_s})^∨ (OS:344-362). (A_s, B_s) is (a_s, b_s) at even s and (b_s, a_s) at
  odd s, each factor σ^s-twisted. So at an odd "top" y the *vector* degree is b_y.
- **CCe** (OS:390-394) = w^{−t}·HHL(src) ∩ ReHH(e) ∩ ⋂_{e′≠e, same src} w^{c}·ReHH(e′). CCe′ is the dual analogue at
  tgt.
- **beHH**(F, G) = G(p^{AHH}F), with AHH = Σ vector degrees (OS:386-388).
- **RhoGE** (OS:410-418) asks for n ≥ X vectors x_i ∈ CCe and y_l ∈ CCe′, z with v_p(z) ≤ D, and an O-matrix M with
  Σ_l be(x_i, y_l)·M_{lj} = z·δ_ij.
- In words: from **one** edge, a near-inverse pairing of rank ≥ (1−κ)/gauss of the whole dimension, at enlargement t.

**`t0I` = `t0G4`** (OS:439-442):

> Σ_{segments j} Σ_{odd y in j} min(b_y, a_{segStart}/p^{d_y}) + Ct·N·(a/p² + b′/p + La·a/(pk) + La·b′/k + kQ + Qc),

with k = m+1, Q = p^{G′} and La = C0·N1²·log a.

**`kapPI`** = `kappaMarginBound` (OS:430): Ckap·N·(e^{−La/8} + kQ(m0 + N1k)/b′ + 1/Y + kE0/a).

**`kapTI_j`** = `kapT` = `badShare`(segForm, segLat_j, DjI) (PLB:105-108; OS:259-268). This is 1 − (max rank of a
saturated sublattice whose primitive vectors each pair to valuation ≤ D)/rank. It is the **optimum**, not a bound.

**`admB3`** (PLB:158-176): (1 − kp)·dimHH ≤ gauss·∏_j segRank_j and kp ≤ Cs·N·N1/Y, for every margin mm ≤ b′/(kQY).

**`ColumnFamilyLowerSet`** (PLB:178-189) = `OrderBoundDigits` (CS:169-173): Σ_j blockOrd(b_j) ≤ t0I for every kept
block.

**`Conclusion2`** (PLB:76-91): under `HypI` there is κ(a, b) ≥ 0 with meanKap over the box IaZ^TT × IbZ^TT
≤ C·N·N1/Y, such that LPprime(t, Dp, κ(a, b), c*) holds for all t ≥ tI and every base weight in the window.

**`extendedClosedForm`** (`StandardPolynomials.lean:23`): `ExtendedClosedForm D` = admitted D → Closed
(ExtendedAllConclusions D) (CS:511). That is the conjunction (CS:425-430) of:
- `HerrExtensionClass` (the admB2 shape, `aux₃` CS:94-106);
- `ExtendedKappaBound`, `PointsLemma`, `Conclusion4` (rank on digits ≤ dimMM);
- `ExtendedDichotomy`, `ExtendedModelRank` (≈ admB3), `ExtendedOrderBound` (≈ ColumnFamilyLowerSet);
- `RootMultiplicityTwo`, `FreeTopRankBound`.

It is proved via `stmtEExt_of_15c` ← `restRawTail1_of` (key3Ord, loc4Res) and `RestCols ∧ RestPre ∧ RestTCore`
(`CoarseMultiplicity.lean:30-34`). I did not open those bodies.

**Sig / served / dropped** (IRZ:220-235, 246-252):
- Sig = m·Σ_{t0 ∈ goodReps} kapv(t0).
- VV = goodReps if Cand ∧ Sig ≤ x^{−ε}, and ∅ otherwise. The prime is *served* iff VV ≠ ∅.
- *Second-class (dropped)* = Cand ∧ x^{−ε} < Sig (`SuppSat.lean:46`; `second_spec` P4:659).
- If VV = ∅ then τ = 0 (`tauP`), and the local gain is Σ_reps g0⁺, the Hecke-free part (`gainP`).
- In the global accounting, *all* non-served classes are charged their whole ask: gain 0 and τ 0 (`SplitClasses`,
  `SecondKindBucket.lean:68-80`).

**`pf_sum_Sig_le`** (P4:1783-1790): for each Cand prime p,

> Σ_{a∈box(winA)} Σ_{b∈box(winB)} Sig(a, b, p) ≤ #box_A·#box_B·(m·#TT·x^{−12}).

It follows from `MeanKappaBound` (IRZg:330-334): mean over the box of κ ≤ Nv·x^{−12}, and pointwise for p < p0.

## 2. Units (E12) — one inequality tracked end to end

1. `admB2`/`LPprime` at a vertex L give F_i = w^{−t}f_i and G = w^{−t}g, with f_i, g integral. So
   be(F_i, G) = p^{−t}·g(p^{Ar}f_i). Requiring this block invertible up to p^D means the integral matrix
   g(p^{Ar}f_i) has elementary divisors ≤ p^{t+D} on a (1−κ)-share.
2. `RestLocChain` (LS:722-727) gives base ⊆ ball, dual ⊆ base, w^t·ball ⊆ base and w^t·base ⊆ dual. So
   w^{2t}·ball ⊆ dual, while RestJ gives p^{D+1}·dual ⊆ T(ball) + C.
3. `walk_allBut_bound` (LS:296-311) sums per vertex t + t + (m−1)·2t + m·2(D+1) = 2m(t+D+1) in w-units, and rewrites
   w^{2(τ+βS)} = p^{τ+βS}. This gives `tau` = Σ m(t+D+1) (SL:27), in p-units.
4. `tauP` (IRZ:338-342) uses the same ⌈tv⌉, and `LemmaVVolumeGeneral` concludes NP ⊆ p^{⌈τ⌉}·Mram (FGS:832-847).

So the t of admB2 is an elementary-divisor bound in **p-units**, and is charged once, in p-units. The exact
computation (§3) confirms that the EDs of the integral transport pairing sit at the t0I scale in p-units. Had t been
an ED bound in w-units, the GL₂ data would sit at twice the Lean's scale; they sit below it.

## 3. Mathematics of the closed form, and computations

**What blockOrd counts** (OS:132-170, 282-284; my reading). Take one segment: an even top s0 with vector Sym^a,
followed by odd tops y_i at Frobenius distance d_i < G (G = distance to the next even top).
- Write b_i = Σ_c rz_{i,c} + P_i·coarseA_i in base P_i = p^{G−d_i}, with digits rz < P_i (`DigitsOK`).
- The coarse part (Sym^{b_i} of a σ^{d_i}-twist ≈ Sym^{coarseA_i} of a σ^{G}-twist, by Lucas/Steinberg) lands at the
  same Frobenius position as Sym^{A0}, with A0 = ⌊(a − E0)/p^G⌋.
- A block records, for each i, the number o_i of Pieri contractions between position i and what has accumulated.
  Their caps are o_i ≤ coarseA_i and o_i ≤ cap_i = A0 + Σ_{l<i}(coarseA_l − o_l) (+ margin La·coarseA/(r+1)).
- Each contraction costs P_i in p-adic order: blockOrd = Σ_i P_i·oEff_i + low digits.
- Hence the maximum order is Σ_i P_i·min(b_i/P_i, a/p^G) = Σ_i min(b_i, a/p^{d_i}). That is t0I's main term.
- For "near" positions (p^{d} < a/b′, i < σ) the cap is never binding and the cost is the full b_i (·(1+4/p²)).

**Expected κ (my derivation).** Model the coarse factor as Sym^A ⊗ Sym^B = ⊕_o V_{(A+B−o, o)} for GL_{m+1}, where
cost(o) = P·o.
- At threshold t, κ ≈ the dimension share of pieces with P·o > t, plus the digit/boundary/window terms.
- For m+1 = n large, the hook-content dimension of V_{(A+B−o, o)} increases steeply in o. So the mass concentrates
  at o ≈ min(A, B)·(1 − O(1/(n·|A/B − 1|))).
- The hypothesis excluding p^d ∈ (a/b′)(1 ± 2de) for odd d (HypI) removes exactly the balanced case A ≈ B, where the
  concentration is slow.
- So κ is small at t = Σ min(b, a/p^d)·(1 + O(La/k)), and close to 1 at t = (1−δ)·Σ min for fixed δ.

`colen/pieri.py` (exact hook-content dimensions) gives, for A = 1000, B = 100, the share of dim with o ≤ (1−δ)·min:

| n = m+1 | δ = 0.5 | 0.25 | 0.1 | 0.05 | mean deficiency (min−o)/min |
|---|---|---|---|---|---|
| 2 | 0.53 | 0.77 | 0.91 | 0.96 | 0.52 |
| 10 | 4.6e−3 | 0.11 | 0.44 | 0.67 | 0.11 |
| 50 | 7.8e−11 | 4.9e−5 | 0.026 | 0.17 | 0.023 |
| 200 | 2.8e−25 | 1.2e−11 | 7.8e−5 | 9.7e−3 | 0.0066 |

- For A = 400, B = 200 the mean deficiency at n = 200 is 0.0145. For A = B = 200 it is 0.086, which is slow, as
  predicted.
- With m ≈ x^{1/2}, a threshold 10% below the Lean's main term leaves only ≲ 10^{−4} of the dimension servable
  (κ ≈ 1). The Lean's threshold is necessary at the leading order, not just sufficient.

**Exact p-adic GL₂ test** (`colen/pairfast.py`, the same model as the parent's `pair.py` but mod p^N; reproduces it
on (12,2) and (9,3)).
- V = Sym^a ⊗ (Sym^b)^σ over Q_{p²} (n′ = 2, G = 2, d = 1), and W(L) = Σ_{q+1 neighbours} p^{a+b}·HL(L′).
- EDs are in p-units. "base" is the max ED for b = 0. The Lean prediction is ≤ base + min(b, a/p) + O(a/p² + b/p).

| p | a | b | dim | mean | q90 | max | max − base | min(b, a/p) | share ED > min(b, a/p) | share ED > ½·min |
|---|---|---|---|---|---|---|---|---|---|---|
| 3 | 18 | 3 | 76 | 2.11 | 4 | 4 | 2 | 3 | — | — |
| 3 | 18 | 6 | 133 | 2.92 | 5 | 6 | 4 | 6 | — | — |
| 3 | 18 | 9 | 190 | 3.55 | 6 | 7 | 5 | 6 | 0.021 | 0.58 |
| 3 | 27 | 3 | 112 | 2.74 | 4 | 5 | 3 | 3 | — | — |
| 3 | 27 | 6 | 196 | 3.79 | 6 | 7 | 5 | 6 | 0.051 | 0.59 |
| 3 | 27 | 9 | 280 | 4.58 | 7 | 9 | 7 | 9 | — | — |
| 3 | 27 | 12 | 364 | 5.18 | 8 | 10 | 8 | 9 (cap a/p) | — | — |
| 5 | 25 | 5 | 156 | 2.40 | — | 5 | 4 | 5 | 0.000 | 0.45 |
| 5 | 30 | 4 | 155 | 2.74 | — | 6 | 5 | 4 | 0.17 | 0.61 |

Raw ED histograms are in `colen/out_p3.txt`, `out_p5.txt` and `out_scan2_p3.txt`.
- The growth in b has slope ≈ ⅔ below the cap a/p and ≈ ⅓ above it (a = 27: max 3, 5, 7, 9, 10 at b = 1, 3, 6, 9,
  12). That is the min(b, a/p) shape plus a b/p-size term, inside the Lean's bound.
- For (5, 30, 4), max − base = 5 > min = 4, but < 4 + a/p² + b/p = 6. The O(·) terms are needed and suffice.
- GL₂ (m = 1) has no concentration, so failure below the threshold is gradual: about 45-60% of directions exceed
  ½·min. For large m, `pieri.py` predicts a sharp failure.
- Caveat: this is a vertex-sum ED computation, which tests only the *necessary* condition
  #{ED ≤ t+D} ≥ (1−κ)·dim. It does not test the per-edge near-delta condition (CCe's w^c-smallness at other edges),
  and it is outside HypI (m ≥ 2N1+2, p ≥ (m+1)²Y²).

## 4. Dropped-prime budget (c)

- Which primes are dropped: Cand primes (p < X′, residue class zero, ord h ≥ x^{ε/4}, not in band) with
  Sig > θ = x^{−ε}. For them τ = 0, the local gain is the Hecke-free Σ g0⁺, and the global accounting charges their
  whole ask, 4·m·T·a·log p/p (`SecondLe`, `second_term_le`, OneLeThresholdMulPowers.lean:944-954). So they are lost
  into LoP, conservatively.
- `MeanKappaBound`: Y = x^{A/2} = x^{13} is the window parameter (winA width a/(k·x^{13}), IRZg:305-306), and
  p0 = k²x^{26} (DataParams₂:43-45), which matches HypI's (m+1)²Y² ≤ p.
  - For p ≥ p0: mean κ ≤ C·N·N1·x^{−13} ≤ Nv·x^{−12}, from Conclusion2 via kapI = sInf ≤ κ.
  - For p < p0: kapIIf = min(1, kII·N·rG²·k·x^{−26}) pointwise.
  - It enters as hypothesis `(hG x eG i0).2.2.2.2` of `LinkG` (LRS:263). I did not trace that supplier.
- `pf_sum_Sig_le` → `mean_SigO` (P4:1943) gives mean Sig ≤ s0 = m·#TT·x^{−12}. `chosenW_of` (LRS:251-320) then gives:
  - Σ_o π(o)·Σ_{p<X′} (log p/p)·1[Sig_p(o) > θ] ≤ (2/θ + 4)·s0·Σ log p/p;
  - Mertens gives Σ_{p<X′} log p/p ≤ 2x^{ε/3};
  - so some weight o has a dropped-prime log-density ≤ (2x^{ε}+4)·m·#TT·x^{−12}·2x^{ε/3};
  - `LossChoiceU`/`WindowSettingHypotheses` (WSS:303-358) also bound io (= 2·Sig·max Sv) the same way.
- Total second-kind loss ≈ 16·m²·#TT·T·a·x^{−12+4ε/3}. With m ≈ x^{1/2} and a = x·b this is ≈ x^{−10+O(ε)}·#TT·T·b,
  negligible against x^{3+O(ε)}·b unless #TT·T exceeded x^{13}. It does not: TT is a set of tops, of size ≤ n ≈ x^{2+8ε}.
- So **no main-term loss**. The dropped set is the Markov tail of an x^{−12}-small mean.

## 5. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `RemainingCountingStatement` (flipOneThree `Conclusion1`) | `CountingStatementReduction.lean:2427-2458` | mean over the window of badShare of segment block lattices ≤ C(t+1)N1/Y, via explicit good sublattices L₂ | **core, not opened** (this is where κ is actually small) |
| 2 | block-lattice realisation inside `extendedClosedForm` (`HerrExtensionClass`/`aux₃`, `RestCols`, `RestPre`, `RestTCore`, key3Ord, loc4Res) | CS:94-106; `CoarseMultiplicity.lean:30-34`; `StandardPolynomials.lean:13-23` | the kept blocks give vectors in CCe/CCe′ whose pairing matches segForm up to p^{D}; the per-edge rank ≥ (1−kapP−Σ badShare)·dim/gauss | **core, not opened** |
| 3 | `ModelLatticeRank`/`admB3` | CS:159-167; PLB:158-176 | (1−kp)·dimHH ≤ gauss·∏ segRank: kept blocks fill all but kp of the dimension | core-combinatorial (Pieri/Lucas count; consistent with `pieri.py`) |
| 4 | `OrderBoundDigits` | CS:169-173 | Σ blockOrd ≤ t0I for kept blocks | glue-arithmetic (follows from the `Kept` caps; my §3 derivation) |
| 5 | `LinkG` supplying `MeanKappaBound` | LRS:251-263 | Conclusion2 ⇒ mean κ ≤ Nv·x^{−12} for p ≥ p0; kapIIf for p < p0 | core-glue, not traced |
| 6 | `walk_allBut_bound` | LS:216-313 | the w-unit to p-unit bookkeeping | glue (read; correct) |
| 7 | `chosenW_of`, `LossChoiceU`, `SecondLe`, Mertens | LRS:251-320; WSS:303-322; OneLeThresholdMulPowers.lean:944-954 | Markov choice of weight; dropped-prime loss | standard (Markov + Mertens) |

## 6. Oddities

1. **Second "defined-as-optimum" quantity.** kapTI = `badShare` is an sSup-defined optimum, like kapI. So `admB2`
   alone is again a comparison theorem (true rank ≥ model rank), not a smallness statement. The smallness lives only
   in child 1. This is legitimate, but a reviewer must open child 1 before calling κ small.
2. **Existential constants.** `ClosedA` (PLB:226-231) lets Ct, Ckap, CA and Cs be chosen *after* C0, CE·, Cm and CH,
   but before p, a, m. So the O(·) part of t0I has an arbitrary but uniform constant. The main term
   Σ min(b, a/p^d) has coefficient exactly 1. That is the honest part.
3. **tIf vs tI.** IRZ:160-168 drops the b′/p and La·b′/k terms of tI. They are absorbed because Cand primes have
   p < X′ = a/b′. The constant bridge was not checked.
4. **w and "unramified".** The name `UnramifiedQuadraticSetting` refers to Qq/Q_p. O is ramified (e = 2) and also has
   residue degree 2 over W. The extra clause "every integer is a square in O" is strong but satisfiable after a finite
   extension.
5. **Accounting is conservative.** Served-but-Hecke-free information for dropped primes (g0⁺) is discarded in
   `SplitClasses` (gain 0). This is harmless.
6. Nothing false-looking seen.

## 7. Coverage

Read:
- PLB:1-262 (all);
- OS:106-170, 196-444;
- UQS:1-135, 195-222;
- ObjPol.lean:15-45;
- LS:180-316, 680-735;
- SL:23-56;
- CS:15-175, 425-515;
- `CoarseMultiplicity.lean:1-34`;
- `StandardPolynomials.lean` (all);
- `AdmissibleFamilyNoKernel.lean:30-70`;
- FlipOneThree.lean:95-135;
- `CountingStatementReduction.lean:2400-2470`;
- IRZ:100-360;
- IRZg:295-345;
- P4:600-680, 1767-1800, 1935-1960;
- LRS:240-320;
- WSS:300-380;
- OneLeThresholdMulPowers.lean:930-960;
- SecondKindBucket.lean:60-95;
- DataParams₂.lean:30-60.

Not opened:
- the bodies of `restCols`/`restPre`/`restTCore`/key3Ord/loc4Res;
- `RemainingCountingStatement`'s proof;
- the `LinkG` supplier;
- `keyIneq_of`/`midLP_of` (parent read them).

Scripts, all in `audits/rh-intake/argument/colen/`:
- `pairfast.py` (exact GL₂ two-position EDs mod p^N);
- `scan2.py` (quantile scan);
- `pieri.py` (GL_{m+1} Pieri concentration);
- outputs `out_p3.txt`, `out_p5.txt`.
