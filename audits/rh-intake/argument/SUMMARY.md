# The argument, as reconstructed from the Lean source (checkpoint 2)

Artifact: alpo.ge `lean.tar.gz`, SHA-256 `9631b4f0…49c7fc`. Method: `PROTOCOL.md`.
Twenty-seven explainer nodes and two reviewers (`REVIEW-ROOT`, `REVIEW-TWU`), each a
separate agent reading source; nothing compiled. Every statement is "the Lean says, as
read by one agent" unless marked *(inferred)*. "Proved" means a proof term exists in the
tree, not that it was checked to compile. Corrections between nodes are in §5.

**Status: no defect found in any node. The argument is a coherent slope-method proof
whose mechanism has been identified and whose normalisations match on both sides. Its
correctness now rests on a short list of in-tree theorems (§4), three of which are
stronger than anything in the literature known to the readers, and whose decisive
estimates have not been read.**

## 1. The mechanism in one paragraph *(synthesis)*

Take high-order Taylor derivatives of CM theta functions (reduced sigma functions σ* of
a lattice with Δ = 1, CM by ℚ(√−d)). At a prime p inert in ℚ(√−d) the curve is
supersingular; in the height-2 Lubin–Tate coordinate the kernel is an integral series
times Dwork-type Gaussian factors, so a derivative of order a is divisible by
v_p(a!) − a/(p²−1) − (#Gaussian factors), and the number of Gaussian factors is capped by
the weight w available in the conjugate variables. That gives γ_p·a − Σ_{e odd}
min(a/p^e, w), γ_p = p/(p²−1) = Σ_{e odd} p^{−e}. (Checked numerically in the two extreme
one-variable cases, NODE-NUMTEST: for ℘, no Gaussian factor, the slope is γ_p to three
decimals at inert p and 0 at split p; for σ itself, all factors present, the gain is only
a/(p²−1). An earlier version of this paragraph wrongly attributed γ_p·a to σ*.) Summed
over inert primes the uncapped part is the inert half of Chebyshev's log a! = Σ Λ(n)⌊a/n⌋. At infinity,
Cauchy estimates in Fock space bound the derivative by ph(a) − a·logΩ, with
logΩ = γ + log(π/v) − L′/L(1,χ_d) the (averaged) Chowla–Selberg period, which already
contains the limit of the split half. Caps coming from pluriharmonic column minors turn
the count into Σ Λ(n)(1−χ(n))(a/n − w)₊, a Riesz mean localised at n ≈ x. The comparison
is made not for one number but for lattices of forms, through Bost's slope inequality,
along a chain of m ≈ √x theta lifts; the error has the shape x/m + m. The resulting
one-sided bound Gm(x) ≤ x^{1/2+O(ε)} on windows gives zero-freeness by a windowed
Landau theorem.

## 2. The chain, node by node

| # | step | node(s) | reading |
|---|---|---|---|
| 1 | Windowed one-sided Landau ⇒ no zeros Re s > 1/2 | LANDAU, REVIEW-ROOT | correct theorem (reader's judgement); four sub-lemma bodies unread |
| 2 | Gm ≤ x^{1/2+} ⇔ ASK ≤ MAIN + err; ASK = Σ Λ(n)(1−χ(n))(a/n−w)₊ | COREGM, ACCOUNT | bookkeeping; `ch_balance` body unread |
| 3 | Hosts E (abelian CM, degree x^{2+8ε}) with q, d by zero-density + mean square | HOSTS, PAIRGOOD | unconditional; no circularity |
| 4 | gain := count shape; N_u := 𝔭^{−gain}·NuLat_u; 11 clauses of `SizeData₂` | LOSS, FAMILY, SLOPESN, SLOPE | by definition / linear arithmetic |
| 5 | \|gain − count\| ≤ slack | PAIRING | lower direction in Lean; upper direction by hand; worked at p = 7, 101 |
| 6 | Slope inequality (Harder–Narasimhan layer cake + Bost) | RANK | correct theorem; no rank/degree error term, genuinely |
| 7 | Period divisibility at inert places for the m-fold chain | ROWSU, TWU, REVIEW-TWU, LOCALDIV | correct local theorem; tight (hand check p = 7); Hecke part nets to zero |
| 8 | σ* in LT coordinate = integral × Dwork exponential; scaling constant a unit | KERNELLAW | proved from recognisable mathematics |
| 9 | Local chain = global chain completed at w; lattices preserved exactly | GLOBALCHAIN | by construction; no free scalar |
| 10 | Same Θ, same Δ = 1 lattice, same period on p-adic and archimedean sides; no net power of p | SAMETHETA | yes, at the level of definitions and statements |
| 11 | Archimedean height of the chain | HEIGHT | proved; polynomial losses; averaged Chowla–Selberg exact |
| 12 | Theta-lift scalars λ_j ≥ hook product − small (Rallis; L-value in convergent range) | L6 | proved; exact hook term; seven premises discharged in-tree |
| 13 | Degree clause DIV; two x^7·b terms cancel; needs (11) and (14) to relative x^{−4} | DIV, ACCOUNT | closes exactly at x^{1/2+O(ε)}; m-independent error is a parameter choice |
| 14 | Covolume of cusp-form lattices: (p−q)·logΩ exact from flat sections, error ∝ q ≤ m | COVOL, HS, VOLUME | weak-but-sufficient lower slope bound; Zhang + Chowla–Selberg + Chow forms |
| 15 | Hecke-image colength | COLENGTH | proved; half by definition (κ is an infimum); hand computation agrees on the a/p scale |
| 16 | Near-tight frame of Bessel periods ("Theorem S") | THEOREMS, SLEAVES | every hypothesis discharged by a named theorem; decisive estimates unread |
| 17 | Selmer-size bound `VWin` for host admissibility | VWIN | plausible statement; plus part via U(3) Eisenstein congruences |
| 18 | Automorphic input record; theta second-term identity | THETA | consumed while building the record; not matched to one published theorem |

## 3. Sizes (ACCOUNT)

b = e^{x^ε}; n ≈ x^{2+8ε}; m ≈ x^{1/2−ε/16}; k ≈ x^{9/2+10ε}; t ≈ x^{398}; weight a = x·b.
Budget ≈ x^{3+O(ε)}·b. Two error families sit at the budget and balance at m ≈ √x; all
other errors are inside it. √x enters only as the number of lifts.

## 4. What the proof rests on that has not been read, ranked

| # | statement | why it is load-bearing | status |
|---|---|---|---|
| 1 | **Limit multiplicity with exponential precision**: dim of the level/character part of L²(U(k+r,r+1)) for a very regular discrete series equals formal degree × covolume to relative e^{−n f log n/16}, uniformly in rank (`CountingTheorem`; `DecGap`, `NonzeroFlagBound`) | gives near-surjectivity, hence that the comparison is not about a vanishing quantity | beyond the literature known to the readers; method standard (pre-trace formula); estimates unread; whether the family meets the required parameter gap n¹⁹·log b unchecked |
| 2 | **Near-orthogonality of Bessel periods** to relative b⁻⁶ (`PairBound`; local saving `NGAt`; `NormBound`; `loopRowBounds_along_family_largeGaps`) | same | decisive lemmas unread |
| 3 | **Per-edge rank bound** on Sym^A⊗Sym^{B∨} (`admB2`, `extendedClosedForm`) and the dropped-prime budget | the colength bound is true by construction; this is where a wrong local index would show | unopened; a factor-2 question on units (powers of √p vs p) unsettled |
| 4 | **Selmer upper bound from Eisenstein congruences on U(3)**, uniform in l and k < x^401 (`OneCharU`, `CongruenceNumberRankThree`) | host admissibility | needs residually reducible R = T for U(3); unread |
| 5 | `ThmB` (intersection numbers = vol × flag-variety height polynomial + linear form) and point-height bounds (`cusp_height_upper`); tie of the abstract tower to the Shimura variety | the lower slope bound (V) | unread |
| 6 | Site identities `serAt_all`, `thetaSeries_scalar_bounded_of_pos_pair` (pays a negative p-power), `Dec.ScalAt` | kernel = Taylor(Θ) at each inert place | statements read, bodies not |
| 7 | `first_kernel_law` leaves (`FourProd`, `StdStep`), `coboundary_exact`/`RestBeta` | integrality of Θ/∏σ* in higher rank | top level read |
| 8 | Rallis inner product supplier, `fockVector_matrixCoefficient_formula`, Galois transport of λ to other places | exact hook main term | unread |
| 9 | In-tree Siegel–Weil, doubling method, global Artin reciprocity, Chebotarev, resolution of singularities | standard, but each is a large formalisation in its own right | not opened |

## 5. Corrections made between nodes (kept, not smoothed)

- ROOT: Landau uses non-negative coefficients. LANDAU, REVIEW-ROOT: no; kernel and weights.
- LOSS: the only divisibility clause is instantiated with the zero map. SLOPESN, TWU: that
  is the colength branch; the divisibility branch uses the family's chain.
- COREGM/THETA/HOSTS: family data may be free witnesses. FAMILY: built over the host;
  but `SizeData₂` alone is empty (`exists_data_completion`).
- SLOPESN: `twU` never constructed. ROWSU, TWU: supplier traced.
- TWU: chain at w is the family's own. REVIEW-TWU: it is an existential model.
  GLOBALCHAIN: the model is the global chain completed at w, lattices preserved.
- TWU: τ small. REVIEW-TWU, PAIRING: τ is the size of the gain; paired off exactly.
- GLOBALCHAIN: groups totally definite. THEOREMS, VOLUME: U(k+r, r+1) at real places;
  definite only for the Bessel subgroup and the top layer.
- THEOREMS: weight plays no part in Theorem S. SLEAVES: true for kernel bounds, false for
  the dimension count, which needs a large Harish-Chandra gap.
- COVOL: lower slope bound is an induction over layers. HS, VOLUME: per layer.
- HS: `VolumeTheoremX` is a uniform volume formula. VOLUME: it has no main term; it is a
  uniform lower bound, weak but sufficient.
- VOLUME: signal looks smaller than DIV's error. ACCOUNT: closes once normalisations are
  followed.
- ACCOUNT: gain − count may be unbounded above. PAIRING: bounded by the slack.
- ACCOUNT guess that √x comes from caps (it was the brief's): no, only from m.
- LOCALDIV vs KERNELLAW on p^{expG}. SAMETHETA: cancels exactly; no uncharged division.
- PAIRING E-PAIR-1 (a wrong index would falsify the colength lemma). COLENGTH: mis-aimed;
  κ is an infimum, a wrong index would instead drop primes via `admB2`/`Conclusion2`.
- Three first-draft briefs were wrong and were corrected by the nodes: the "Hodge
  average a/2" model (COLENGTH: a/q after summing over neighbours), the "class-set"
  model of Theorem S (SLEAVES), and the caps guess above.

## 6. Escalations for an expert, in order

- **E10.** §4 row 1: is an exponentially precise, rank-uniform limit-multiplicity
  statement for U(p,q) with q² ≤ n and Harish-Chandra gap ≥ C·n¹⁹f⁵·log(b·rd) true, and
  does the constructed family have that gap?
- **E11.** §4 row 2, in particular the local lemma giving q_p^{−(k−2r−5)} at non-generic
  places.
- **E-TWU-1.** The bare claim: m theta-lift steps send every integral weight-a form to
  periods divisible by Σ_{e odd} max(0, a/p^e − w). One-variable extremes tested and
  confirmed (NODE-NUMTEST and its addendum); the capped two-variable rank-one case
  confirmed as a lower bound, not tight (NODE-NUMTEST2). Higher rank untested.
- **E8.** `OneCharU`.
- **E12.** The colength units question (t in powers of √p, τ in powers of p).
- **E6 (closed).** `VolumeTheoremX` is weaker than it sounded. **E7 (closed).** No rank
  term in the slope inequality is correct. **E5 (closed conditionally).** B_u = 0 is
  excluded by the frame hypothesis, i.e. by rows 1–2. **E9 (closed).** Sizes close.
- Nonvanishing of the iterated lift is nowhere asserted directly; it follows only from
  rows 1–2. L6 gives λ_j > 0 only on non-empty type parts.

## 7. What this pass does not show

That the source compiles; that any unread proof body is what its statement suggests;
that the readers' judgements of "recognisable" and "plausible" are right. Not located
from the author's note: "Behrend", the pigeonhole Iwasawa tower, the sixfold cover of
GL₅. Scripts from COLENGTH's hand computation are in `colen/`.

## 8. Round 4 (after checkpoint 2)

| node | result |
|---|---|
| NUMTEST (+ addendum) | First non-reading evidence. Exact computation to order 6000: for ℘ (no Gaussian factor) v_p of the a-th Laurent derivative has slope γ_p = p/(p²−1) to three decimals at inert p, O(log a) defect, no gain at split/ordinary p. For σ (all Gaussian factors) the gain is only a/(p²−1). Both extremes of the Lean's formula confirmed; the summary's earlier wording was wrong (fixed in §1). Capped two-variable case: NUMTEST2, next row. |
| NUMTEST2 | Kronecker theta function σ(z+w)/(σ(z)σ(w)) for both CM curves, exact p-adic arithmetic, a < 2000, b ≤ 40, validated against brute force. At supersingular p: v_p(∂_w^a∂_z^{b−1}) ≈ max(γ_p(a+b) − b, (a+b)/(p²−1)), error in [−3.3, +6.1] not growing with a; no gain at split/ordinary p. The bound the proof uses, gain ≥ Σ_{e odd}(a/p^e − w)₊ − O(1), **holds at every grid point**, cap constant 1. It is not tight: the truth exceeds it by ≈ γ_p·b + Σ_{e≥3 odd} min(a/p^e, b) (the cap bites once, at e = 1). Hand estimate of the excess summed over primes: O(w(x^{1/3} + log x)), below the x^{1/2} scale. Control: replacing each Hurwitz number by a random unit of the same valuation leaves the law intact, so in rank one this follows formally from the ℘ result and is not independent evidence. |
| COUNT | Dimension count is limit multiplicity on a non-compact quotient via an exact projection onto cusp forms (Schur orthogonality for integrable discrete series), not a trace formula over classes. The family meets the Harish-Chandra gap (needs ≈ x^110, has ≈ x^1300; only opposite-sign pairs count). New expert item: the "compression formula" for lowest-K-type coefficients of non-holomorphic discrete series (`FormulaGap`), not located in the literature; check on U(2,1). |
| PAIRB | Near-orthogonality is a double unfolding of Poincaré series (no spectral decomposition). Savings are counting (sublattice counts; level factor (2/g)^{(s−1)kf}); Gauss-sum clause is Gelfand–Graev multiplicity one. The tight comparison 2^{−k/2}·e^{C m⁵ f log b} ≤ b^{−14} closes by x^{21ε/16}/128; this fixes k ≈ x^{9/2+10ε}. Unread: local defect-mass counts, `EnergyAbs`, `IdZero` supplier. |
| ADMB2 | E12 closed: w is a uniformiser of a ramified extension, v(w) = ½v(p), bookkeeping consistent. `admB2` compares true rank with a model rank; `badShare` is an optimum by definition; smallness is in `RemainingCountingStatement` (unopened). Hook-content and exact GL₂ computations agree with the threshold Σ min(b, a/p^d) up to the Lean's O(·) terms. Dropped primes cost ≈ x^{−10}·(budget unit): no main term lost. |

Further corrections: SLEAVES attributed the corank ≥ 2 saving to a Siegel mass ratio; PAIRB:
mostly the level. The brief to COUNT suspected an unsatisfiable gap hypothesis; it is
satisfied. The brief to PAIRB had the direction of P_u reversed.

Updated ranking of what is unread and load-bearing: (1) the capped divisibility in
higher rank with harmonic minors (rank one now confirmed as a lower bound); (2) `FormulaGap` and the bodies of the count's near/far/deep/flag
lemmas; (3) `RemainingCountingStatement` and the block-lattice realisation in
`extendedClosedForm`; (4) local defect-mass counts and `EnergyAbs`; (5) `OneCharU`
(Selmer bound); (6) `ThmB` and point heights; (7) site identities.

## 9. Round 5

| node | result |
|---|---|
| CHAININD | The iteration over the m lifts is an honest induction (`main_ind`, YEPEComm.lean:131): the hypothesis after j steps is only "ϖ^{prev}·(arbitrary element of Int_j)", the next step's bound holds for every integral form, Int_j is one Lean object at every level, and the derivative order a is NOT split among lifts (the level-j weight keeps a_s; each level's kernel differentiates to order a again). Total ≈ m × one-step gain. Hecke operators are not needed to iterate; automorphism denominators charged once per lift via Minkowski's bound; closes only because a ∝ e^{x^ε}. Everything reduces to the single-step statement for every integral form, uniformly in rank up to N(m) ≈ x^{399}. |
| HIGHERRANK | The Gaussian is exp(−(π/p)hh), hh = Σ_s u_s Σ_{entries} S_s^p S_{s+1}; mod p, one coupling x^{p^e}·y per odd e with y at position t+e. The cap is a genuine lemma: multiplication by a linear form is adjoint to a directional derivative of the operator; two derivatives in one direction kill a column minor. Term-by-term valuation bound and the reduction to rank one (unimodular at p ⇒ locally standard; weak approximation) check out. All arithmetic content is "the kernel lies in the Gaussian class". |
| WRITEUP | The slope chain written as one proof with the Lean statements; 17 sign/direction checks pass (μ = 2·(−log covol/rk)+const; superlattice raises μ; frame on the target; factor 2 consistent on both sides). Misfits, none a reversal: see file. |
| LOOSE | Five misfits closed: rescaling identity is proved from covol(𝔞L) = N(𝔞)^{rk}covol(L), slack only from floors; factor 2 in the covolume main term is `degW = rank·μ/2`; Mram index exact; eO ≥ 2, `NumCmp` proved, no off-by-one between operator weight and cap; integrality, height and frame clauses use the same B_u and bases. |
| FORMULAGAP | The compression formula for lowest-K-type coefficients (non-holomorphic discrete series on the live path) reproduces (cosh t)^{−m} on U(1,1), the classical value on holomorphic U(2,1), and on the middle series of U(2,1) has value 1 at 0, is ≤ 1, has the second derivative given by an independent Schmid/Clebsch–Gordan computation, and a decay rate matching Trombi–Varadarajan. Not Knapp–Wallach; not found published. Unread: `germ_jet_zero` (486 lines). |
| **NUMTEST3** | **The Lean's own kernel in its smallest instance, both sides computed for the same numbers.** Smallest host E = ℚ(√−d, √−q), n′ = 2; one matrix entry Θ(z₀,z₁) = th0(z₀+z₁)·th0(c(z₀−z₁)), th0 a 2-torsion translate of σ*, c·c^σ = −1 at p; jet J(a,w) = ∂_{z₀}^a∂_{z₁}^wΘ(0). At served inert primes: slope in a equals γ_p to 0.0003 for all w ≤ 30; at w = 0, v ≥ v_p(a!) − (a−1)/(p²−1) exactly; slope in w is γ_p − 1; the proof's bound Σ_{e odd}(a/p^e − w)₊ never short by more than 0.98. Archimedean Fock bound saturated to within 5.3 in log for the same numbers. Split primes: slope 0. Inert primes where the hermitian form is anisotropic (Frob_p = c): only 1/(p²−1). **Mechanism:** Θ(z₀,0) = th0(Az)·th0(Cz) with A·A^σ + C·C^σ = 0 at p but \|A\|² + \|C\|² = 1 at ∞, so the two Gaussians cancel p-adically while the function keeps Gaussian growth at ∞. Scrambling the jets to random units of the same valuation destroys the gain (slope 0.0185): unlike NUMTEST2 this is a genuine arithmetic cancellation. Not modelled: full matrices with minors, non-standard lattices, the chain. |

Consequences for §1: the entire theta kernel obtains the Gaussian-free gain because, in
the even-position direction at a place where the hermitian form is split, a product of
two σ*-type factors has cancelling p-adic Gaussians. "Inert" in the prime count means
inert in K with that splitting condition (the host's Frobenius classes), which is why
ASK carries (1 − χ_Φ) for the host's characters and MAIN contains the corresponding
L′/L(1,·) terms.

Further corrections: the brief to FORMULAGAP guessed Knapp–Wallach (no); the brief to
NUMTEST3 described the odd-position variable as possibly conjugate/dual (it is the other
CM-type coordinate, holomorphic); WRITEUP corrected SLOPESN (no injectivity hypothesis)
and the summary's "𝔭^{−gain}".

What is still unread and load-bearing, ranked: (1) `restGc`, `HhDecomp`, the kernel-law
leaves (`FourProd`, `StdStep`), i.e. that the full higher-rank kernel lies in the Gaussian
class; (2) `germ_jet_zero`; (3) `RemainingCountingStatement`; (4) local defect-mass counts,
`EnergyAbs`; (5) `ThmB`, point heights; (6) `OneCharU` (Selmer bound); (7) site
identities. Untested numerically: rank ≥ 2 with minors, long Frobenius orbits (n′ ≥ 4),
any composite of two lifts.

## 10. Round 6

| node | result |
|---|---|
| GAUSSCLASS | The full kernel lies in the Gaussian class by a six-link chain, each followed: (1) exp(Σ ph(X_i))·Θ integral in an orthonormal basis at every inert p (one copy → 2×2 → tensor → general lattice by prime-to-p coset averaging); (2) at a served place the position variables are a unimodular hyperbolic pair (the only use of "split at p"); (3) self-terms cancel by isotropy, leaving the polarisation Σ be(x_e, y_e); (4) Dieudonné/Honda classification of be; (5) trace duality of the unramified extension forces the s ↔ s+1 coupling (read in full); (6) Dwork. Nothing grows with rank or orbit length. Unread leaves: `joint_integrality` (integrality of translated σ*/σ*, i.e. Kronecker theta), `lamPos_of_posEmb`, the one-copy step. |
| CHBALANCE | The bridge ASK − MAIN ↔ Gm is an exact character computation. ψ enters through unequal shares of the index set TT (4/(3o+1) on the trivial A0-coset, 3/(3o+1) elsewhere; A/A0 dual to ⟨ψ⟩), giving coefficient (3o+1)⁻¹ on each ψ^j; with uniform shares only RH for ζ would follow. Coefficient of Gm is U = \|TT\|·m·b·δ/2 > 0; replacement errors logarithmic; direction right for Landau. ASK counts every prime inert in K; "thick" (informative) classes are the served ones. New untraced input: `ThinScales`, an effective PNT for all characters of Gal(E/ℚ) at y ≥ e^{x^{ε/3}}. |
| GERMJET | `germ_jet_zero` correct: jets as a 𝔨-map out of U(𝔤)⊗_{U(𝔨)}τ; reduction to Hom_K(S^m𝔭⊗τ/relations, τ) = 0; Casimir (Hotta–Parthasarathy/Schmid) inequality, constant hand-checked; ray-by-ray analyticity. Needs only gap > 2n. `mul_vminus_eq_zero` read in full. |
| COUNTS | `RemainingCountingStatement` has no open hypotheses; its content is a mean-value lemma for p-adic valuations of a polynomial determinant along an arithmetic progression (root counting + Markov), tested by exact Smith forms (0/24 violations, one case nearly sharp). Local mass bounds point the right way; the second-type saving is a character-sum cancellation, not counting; `EnergyAbs` is the formal-degree isometry; `IdZero` and `PointSumInput` suppliers found and proved. |
| ONECHARU | **The Selmer bound is on the core route**: it bounds Hecke congruence modules, which bound the divisibility exponents at twisted places (`LinkN`/`DIVinN`). Crude bounds do not suffice for twists k up to x^{401}. Proof is R = T-type on the deformation side: Ш ↪ first-order deformations of Ψ⊕1⊕Ψ⁻¹; a graded commutative-algebra lemma; every point automorphic or endoscopic by a Skinner–Wiles-style argument with a Hida ideal. Uniformity in l from one integer NN (a norm over all U(3) forms of the level and weight). Non-standard inputs: residually reducible ordinary automorphy for U(3) uniform in all odd l with no l > weight condition; regularity of the generic fibre at automorphic points; finiteness of a trace algebra. Would imply a polynomial bound on plus parts of K_{2k}(O_E). |
| **NUMTEST4** | n′ = 4 instance of the Lean kernel (E = K·ℚ(ζ₁₆)⁺, orthonormal basis found exactly, Θ = ∏_k th0(Σ_s σ^s(f_k)z_s)), jets computed exactly, 0/800 mismatches against brute force. **Per-position caps confirmed and close to tight** (p = 5, a ≤ 640): weight at position 1 costs ≈ 1 − γ per unit; weight at position 3 costs ≈ 1 per unit then flat at ≈ a/p³ (drop 4 for all n₃ ∈ [6,12], a/p³ = 5.12); position 2 costs nothing; mixed losses add. The shared-budget alternative is excluded (predicts 12, observed ≈ 5). **Minors:** det(Y)^m costs m (number of minors), not 2m; Y₁₁^{ν₁−ν₂}det^{ν₂} with the overhang row orthogonal to the top direction costs ν₂, tight. If the overhang row is the coupled direction the cost is ν₁ (the Lean charges that coupling separately; untested). Controls: split, non-served, scrambled jets, broken isotropy all collapse the gain. Correction: NUMTEST3's host identification was wrong (served p is inert in both ℚ(√−d) and ℚ(√−q)); its numbers stand. |

Updated ranking of what is unread, load-bearing and beyond established results:
(1) residually reducible R = T for U(3), uniform in l (ONECHARU) — on the core route;
(2) `ThmB`/`weighted_bound_rotated_uniform` (shared by the lower slope bound and
near-orthogonality); (3) the second-type character-sum cancellation;
(4) `joint_integrality` and the other kernel-law leaves; (5) the supplier of
`ThinScales`; (6) how non-served inert primes are excluded or charged in the count.
Untested numerically: the separate accounting of the coupled overhang direction; any
composite of two lifts; a genuine host with d ≡ 7 mod 16.

## 11. Round 7

| node | result |
|---|---|
| SERVED | Primes inert in K are "signal" (Frob = ((+1,−1),h): inert in K, split in ℚ(√−q); hermitian form always split) or "inertClass" (split iff ord h even; anisotropic density ≤ 2^{−e} ≤ x^{−2}). Dropped buckets (small order, band, second-kind, bad orbits, high, p = d) each ≤ x^{−1+O(ε)}·U, inside the budget; dropped primes are charged their whole ASK with gain 0. `ThinScales` is de la Vallée Poussin with a zero-free region proved in the tree plus host-selected boxes; ell is pinned to the true L′/L(1,χ). |
| SIGNAL | **The x-scale ("thick") part of ASK, the part that carries ψ, sits entirely on signal primes, and their gain is delivered by a different route from the one audited in rounds 2–6**: `NoOperatorOrbitBound` (OrbitPlaces.lean:423) ← `noOp_of` ← `sum_over_primes_service`, using no GIdx, local chain models, `SiteAdm`, Hecke operators or colength; it works on global kernel entries at every place: Gaussian class via `hostAt_inert` + `hyp_of_stdBases` ("inertClass ∨ signal") + `orbitIdentity_all…`; local Hecke-free orbit theorem `Loc.Cor` (`split_bound_eleven_one`); orbits summed; `kform_of_ker` ties entries to the chain. At signal places VV = ∅, τ = 0, no colength; gain = Σ g0⁺ exactly. NUMTEST3's instance WAS a signal place (NUMTEST4's "correction" was wrong); a new n′ = 4 two-tops check matches the Lean bound to −1.13 over 57 jets (`numtest/signal_twotops.py`). Unread: `split_bound_eleven_one`, `orbitIdentity_all_of_integralClass_hostLog_alt`, `orbit_entry_bounds_hold`, kernel entries/adapted bases at signal places and `kform_of_ker`. |
| CONGMOD | The Selmer/congruence cost enters the degree clause through the dual index of the target lattice RR, which at twisted places (almost all relevant places) is an orthogonal projection onto a type part; index ≤ Hida congruence module; error C·m(B0+Nc)x^{Cε}, at the budget. Ш part negligible (√b vs x^{2.5}b). |
| LINKN | The type part is a genuine Hecke-eigen subspace (theta image inside forms with a Speh block μ⊠S_t); Galois representation ρ ⊕ χ₁(1⊕ε⁻¹⊕…⊕ε^{−(t−1)}). Bound by a Wiles-style Fitting-ideal/determinant argument: congruence ≤ Selmer, the Ribet–Wiles half (right direction). Depth: `KillAt` (Bloch–Kato Selmer of ρ⊗χ₁⁻¹ killed by choosing the twist, at every twisted l), local-at-l exponents ≈ weight/l down to l = 2, `NoChiOff`, `GoodR`. Clean version only for l > t. |
| RT3 | The ring is a universal deformation ring (ordinary Kisin-style at l, minimal elsewhere, HT weights (e,0,−e)), not built from forms. `AutEnd3Alt`: residually reducible modularity for U(3), three characters, all odd l with l ∤ h_K·disc K, l−1 ∤ 2e; Skinner–Wiles scheme, no patching. LemmaM is a multiplicity inequality (Smith form + Rees algebra), right direction, toy cases checked. Look first at: the bridge between the ring's local condition and the theorem's (`exists_ordPt_of_point`), and finiteness of R/λ (`FinEnd`). |
| THMB | The "rotated uniform" bound feeds only the non-generic clause of `PairBound` (crude precision); block induction with a Paley–Wiener step and Poisson summation; local Bessel multiplicity one proved in-tree. Second-type cancellation is a Gauss sum on a hermitian quadric; model check agrees with margin ≈ q⁵. (Correction: not shared with the lower slope bound.) |
| LEAVES | `joint_integrality` = integrality of the Kronecker quotient at torsion translates (σ-addition formula, torsion integrality, N-th root, parallelogram law); `NormRel` = distribution relation + density; s₂ p-integral via α = √−d. Exact arithmetic to T^{260}: NormRel integral with the true s₂ and failing at T^{2p} with a wrong one; ph alone non-integral from T^{p+1}. Fourth-power trick confirmed. |

Risk map after round 7. Read down to classical statements and numerically confirmed where
computable: Landau, bridge to Gm, hosts, slope chain and its signs, Gaussian class and
its leaves, cap lemma, iteration on the Hecke route, nonvanishing chain. Read in outline
only, beyond established results, and on the core route: (1) the OrbitPlaces route that
delivers the gain at signal primes (the ψ-carrying part) — four unread children;
(2) residually reducible modularity for U(3) and finiteness of the deformation ring;
(3) `KillAt` and the local exponents at small l; (4) `NoChiOff`/`GoodR`.

**ORBIT (follow-up to round 7).** The second route bounds the m-fold chain, not single
entries: `NoOperatorOrbitBound` gives col(x) = a·z with z in the level-m global lattice
localised at w and v_w(a) ≥ e·(Σ_j g0S_j + lowS). The iteration `chain_ge` (OP:779) is
a plain induction of the same shape as `main_ind`: after n steps the image is a·z with z
arbitrary in the localised lattice; one-step bounds hold on the whole lattice; the
lattice at every level is the one Lean object (T.fm).lat j; no intermediate form is
assumed to be a theta image. Lattice tie: `KerEnt.lat_S` states the localised lattice
EQUALS the forms with integral ∇-minor pairings in the adapted bases (proved by
`kerEntHyp_latS`, leaves unopened), so no index is charged; only v_p(DGam) once per lift.
The local theorem (`split_bound_eleven_one`: generic frame, products of minors,
per-monomial shape bound with capped partner rows, Dwork) is the same architecture as the
Hecke route's, in separate code; at signal places baseTerm = Σ_{e odd}(gap/p^e − row0(s+e))₊
with row0 = number of minors at the w̄ partner ≤ fillG + cG, matching PAIRING, NUMTEST4
and the two-tops check. Orbit bounds add with no loss. Needs rank ≥ 2·log_p a + 3.
Unread: `thmAJetA`, the `latS`/`latT` leaves, `orbitIdentity…` body, `cutKW_holds`,
`kernelEntries_form_true_chains`. Budget check left open by the node: errF ≈
|TT|·m·b·log log X″ in total; against the budget U·x^{1/2+ε} with U = |TT|·m·b·δ/2 and
δ = x^{−O(ε)} (ACCOUNT) this is ≈ U·x^{O(ε)}, inside the budget (orchestrator's
arithmetic, not checked in the Lean).
