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

## 12. Round 8

| node | result |
|---|---|
| JETA | Orbit-route local theorem `thmAJetA` is an LP-duality valuation argument (row weights; each Gaussian factor x^{l^α}y^{l^β} costs one p, covered by l^α r_x + l^β r_y ≥ 1; Legendre); the Lean's charge Σ_e min(cap_e, A/p^e) is ≥ the true LP maximum (conservative; hand example 22.79 vs 19.04); exact random check 0/4000 violations. Generic-frame reduction honest (Gauss norm at a residually generic point; unit Gram determinant; Cauchy–Binet). **No Δ/∇ index:** source and target forms are both Weyl-lattice (Δ) valued, products of minors ∇_J are test vectors, tie is Δ = ∇* (proved in-tree); `cutKW_holds` loses nothing (∇-span a direct summand). |
| MODU3 | `AutEnd3Alt` is Skinner–Wiles extended to n = 3 WITH Taylor–Wiles patching at nice primes (corrects RT3). Chenevier determinant ring, ordinarity as a trace identity; ordinary Hecke algebra; **seed exists unconditionally** (n = 2: Eisenstein congruence at an auxiliary prime w ≡ 1 mod l; n = 3: adjoint lift, base-changed), so 𝕋_𝔪 ≠ 0. dim Λ = 1 + n[L⁺:ℚ]; reducible locus controlled by H¹ rank bounds from Ferrero–Washington (proved in-tree, unread). No l > 3 hypothesis. |
| PATCH | Patching at endoscopic (W⊕1 over K((t))) nice points rests on a DERIVED condition g² + e ≤ D0 (Greenberg–Wiles bound independent of g) and a new local model: quotient of OO[[X, M]]/(Y·M), Y a g×g matrix of independent linear forms, with exactly two big components, the reducible {M = 0} and an irreducible determinantal one containing every stable and thick prime (pure commutative algebra, proved, `CaDetCore`). `Choice` needs only l ≠ 2, ε̄ ≠ 1, finiteness, density of separable Frobenius; detection of dual Selmer classes is "trace determines the representation over K((t))". Connectedness in codimension 1 from the explicit presentation. Exceeds Thorne/ANT exactly at the determinantal model. Unread: `HasAut`, `claim1`/`linAlg`, `s6`, `absolute_irreducible_rank_four`. |
| FINEND | Bridge `It` ⊆ `CondT`: closed (generic distinct eigenvalues ⇒ flag; properness; residual distinctness). Finiteness: `FinEnd` quantifies over char-l DVRs only and yields finiteness of the torus-invariant subalgebra, not of R/λ; sibling of `AutEnd3Alt`, not circular (corrects RT3). Adjoint vanishing: Newton–Thorne-shaped, no enormous-image hypothesis; char-0 replacement `regDet` reads correct; finite-level step `core_o_of_literal_automorphy_n` unread. |
| GALREP | `Row0b` is weaker than Chenevier–Harris + Caraiani ("Strong" is a misnomer: WD matching away from l only for abelian-image, N = 0 parameters; no purity). Proved via descent, Eichler–Shimura-type construction in odd rank (Lefschetz proved in-tree), stable-range theta lift replacing the parity trick, trace limits, Arthur–Clozel base change. Not circular (import closure 66,168 files, no self-reference). `NoChiOff` is a Galois-side rank/weight counting argument, not the theta converse; that content is in `ConclusionZ` and `D7.Z_tie` (unread). Junk defaults `hop` = 0, `wdOf` = trivial noted. |
| KILLAT | Selmer of ρ_s⊗χ_s⁻¹⊗ψ killed by a finite multivariable tame tower O[(ℤ/l^M)^{2R}] with auxiliary primes: square presentation Φ, length = v(ψ(det Φ)), Chebotarev kills the residual Selmer group so det Φ has a unit coefficient in low degree; no weak Leopoldt. Local lengths from a Wach-module lifting theorem with Legendre-type exponent; budget passes with a factor L. |
| TWIST | Residual absolute irreducibility at every l comes from prescribed depth-zero types at g₀, g₁ (`irreducibility_of_good_tuple`), valid outside bad sets BB(r, g_k) required disjoint. Flagged a possible defect on the order of choices for the twist. |
| ORDER | **Both TWIST items closed; no defect.** Two-pass construction over one fixed pre-chain (`recAtG_of_two_passes`): pass 1 untwisted (Q = ∅); a `Seed` (Q, k, ψ) with proof of `GoodTw` is chosen from pass 1's export; pass 2 rebuilds with types δ·ψ and level at Q under `SameExport`, which keeps ρ_s, χ_s, the theta and Bloch–Kato data identical, so the Selmer groups killed are the same; only the character block is twisted. Archimedean constants are fixed before the twist datum (`lay_of_core`: `Ev fun K => ∀ X f (T : TwDat) c, … RecOK K.s K.C K.cD …`). BB-disjointness for the live family is supplied by pigeonhole (`typePrimesN`, `choice_count`): r ≤ x⁵, g ∈ [Y, 2Y], Y = (k·e^{x^ε})⁸, at most (3r+1)(1+2r²(Y^{3/4}+1)) < Y^{9/10} bad choices against ≥ Y^{9/10} candidates. The explicit toy hosts are sanity lemmas, dead code, or witnesses for ∃/Nonempty only; none reaches `HostExW`, `hEx`/`classSel` or `RecExP`. Unread: `exists_levelB2_carried_of_levelB1` (rebuild under `SameExport`), `nonempty_seed_of_kept` (the Chebotarev choice), the global Hecke character realising ψ. |

Risk map after round 8. No defect found; the one "possible defect" raised (TWIST) was closed
by tracing the live path (ORDER). The Galois-representation side has now been read to a
named new idea at each point where it exceeds the literature: the determinantal local model
for patching at reducible nice points; Selmer killing by a finite tame tower over a two-pass
construction; residual irreducibility from depth-zero types with pigeonholed level primes;
`regDet` in place of enormous image. Unread and load-bearing, ranked: (1) `HasAut` and the
derivation of g² + e ≤ D0; (2) `exists_levelB2_carried_of_levelB1`, `nonempty_seed_of_kept`;
(3) `ConclusionZ`/`Z_tie` (theta image = Speh-block forms); (4) `core_o_of_literal_automorphy_n`;
(5) the Wach-module lemmas; (6) Ferrero–Washington, Hida control, the Eichler–Shimura-type
construction, each a large in-tree formalisation taken at its statement. Purity is used in
`ConclusionG6` but is not a clause of `Row0b`: source untraced.

## 13. Round 9: synthesis

Aim changed from gap-hunting to understanding the main argument.

| node | result |
|---|---|
| ARCH | Three-tower dictionary. Column tower X₀ ⊂ … ⊂ X_m (totally definite; algebraic modular forms; jets of CM theta as step maps; all p-adic divisibility lives here). Row tower Y_m → … → Y₀ (Y₀ of signature (k+r_S, r_S+1), r_S = m/2 − 1; target lattice RR, Poincaré series, Theorem S, dimension count). Layers V_j → W_j (W_j of signature (k+j−1, m−j); covolumes, Rallis scalars, congruence modules). |
| WHYHALF | The balance is G_m ≲ x^{O(ε)}[x/m + m + k/n²]: one-off errors divided by m lifts, per-lift errors growing like m, and the non-vanishing precision. Stepanov analogy: the m ≈ √x chained lifts play the role of multiplicity. Lists which inputs are exact identities and which are one-sided. |
| SEESAW | The join of the towers is a genuine m-step seesaw (`MIid`/`MIstar2` ← `mainX_of_lawsX`); the `TieBm` scaffolding is unused. |
| JOIN | The live record is not a stand-in (nondegenerate); the layer lattice is geometric; the a-sized factorial is counted only in column steps. Did not reach the seesaw supplier from the root's producer (trace ran out below `miAt_of_truePack_alt_alt`). |

`MAIN-ARGUMENT.md` is a continuous exposition written from the nodes. A cold reviewer
(`REVIEW-MAIN-ARGUMENT.md`) judged it UNDERSTANDABLE WITH GAPS and gave a fifteen-step
logical skeleton. Holes it named, in the reconstruction, not established defects of the proof:

- H1. det ι = κ^D ∏ det θ_j is a hypothesis of `BoundsMu`; no derivation was read.
- H2. The seesaw supplier is not traced from the live path.
- H3. The set of twisted places (integral theta-unimodularity above X″) was not located.
- H4. The layer signatures (k+j−1, m−j) are stated, not derived; they give Σ(p_j − q_j) = mk.
- H5. ACCOUNT's satisfiability condition Ga − ASK ≤ budget was not seen proved.

Paper checks that closed in the review: Riesz main terms, the 4:3 identity, each bracket of
the balance (given |TT| ≈ n), rank and signature counts, the Mertens/Chowla–Selberg
leading-order match. By-product: non-vanishing forces n ≳ m⁴, matching n ≈ x^{2+8ε}.
Not checkable from the exposition: thin-cap / high-prime accounting; ThinScales (the draft
used Y for three scales).

Follow-up. `MAIN-ARGUMENT.md` was revised against the review (notation box; one-lift model
computation §4.6; hook-product cancellation §5.1; holes §9.4). The reviser disputed the
review on H5: PAIRING §0.1 settles Ga − ASK ≤ budget on paper for Hecke-route tops (τ
cancels the surplus), though not in the Lean. DETSIG read H1 and H4: the determinant
identity is supplied on the live route by a proved linear-algebra lemma (`SpecDet`) from
partwise similitudes (Rallis inner product with the same L-value on both sides) and equal
part dimensions; the layer signature is a definition forced by `arithAt`. Open below it:
`AForm`/`BForm` bodies, `MultEq` (equal multiplicities across inner forms; endoscopic case
to be checked), `GalD` (hypothesis, supplier untraced). Reader dispatched (MULTEQ).

MULTEQ (no escalation). `MultEq`: U(Y_0) and U(W_i) have the same odd rank and are
isomorphic at every finite place; "good" σ carries types with no vector fixed by the
unipotent radical of any P_{(a,r−a)}, which by depth-zero theory leaves only simple generic
parameters (multiplicity 1 on every inner form); proof is a simple-trace-formula comparison
on 14 Published leaves, with only E-irreducible elliptic tori surviving, so no κ-terms.
Oddity: `RealStable` drops (−1)^{pq}, correct only because the rank is odd. Row-step
L-value: use of the bottom parameter B is proved (`LFull`, hypothesis-free; the extra factor
H is a product of Hecke L-values independent of c and B); tuple-independence is `RUnif`.
`GalD` is supplied: Galois equivariance of the rational theta lift (`ConjRatLift5`, proved)
plus Rallis at the conjugate datum. Open: `WeilSiegelFormulaUnitary` is stated for
2·rank A < rank B, which fails for row steps k ≥ 1; the bridge `heckeForm_of_doubling₂`
and `SiegelWeilUnitaryConvergent` are unread. Reader dispatched (SWRANGE).

SWRANGE (no escalation). Siegel–Weil is used only in Weil's range (rank B − witt B > rank A);
`siegelWeilAll_of_hypotheses` splits: rank B > 2 rank A uses the absolutely convergent
identity (Weil 1965), otherwise `SiegelWeilUnitaryConvergent` (n < m ≤ 2n, m − r > n;
reader attributes to Ichino 2007, not checked against the paper). Row step 0→1 and layer
lifts are absolutely convergent; row steps j ≥ 1 are not, witt B ≤ ⌊(m−j−1)/2⌋ < t proved.
All four leaves are `Published` Props filled at the root by closed in-tree theorems, proofs
unread. Oddity: the root record fills `siegelEisensteinSimplePole` with `True`
(ECL:505-506, 718) and no conversion to `S0.HypothesesUE` was found, so the producer
MULTEQ followed (`member_bundles_large_ue`) may not be the root's live one. Untraced: the
caller-supplied L-value at (1+t)/2 and bad-place integrability.

TWSET (no escalation; corrects CONGMOD, JOIN, KILLAT). There is no "unimodular above X″"
statement. The `hmt` iff (`ExtraFinal.lean:24-25`) is dead code (`recF_more`, `RecMore`
unused). Live: `MuDef` (`CutTuples2.lean:188-198`) puts Tw := W1 = places where the
untwisted index, dual index or F is nonzero; off Tw the index is 0 by definition. Content
is `ON` at every place of Tw (`on_of_leaves`) with a global remainder budget
Σ log N(v)·r(v) ≤ rank·f·m·b·de2 (`WeightAlgebra.Concl`; inputs `Heights`/`sumGC4`
unread). X″ is only where gain and F stop. Cost enters E1 = CE·x^ε(B0+Nc). Consequence:
twisted-place inputs must hold at unbounded residue characteristic. Reader dispatched
(LARGETW).

LARGETW (no escalation; corrects ORDER's "single Seed"). W1 is finite (inside
{resChar ∈ T.pl}, P₁ fixed by the pre-chain) with no size bound, and none is used. Pass 2's
W1 equals pass 1's (`ExistsExtTwistedPlaces.lean:91-103`; inputs `DatExt`,
`nonzeroForcedContentPlaces_agree…` at statement level). No single ψ: `ExportAt` gives a
pack (Q, k′, ψ′) with `GoodTw` separately at each twist index, chosen inductively with
pairwise disjoint Q; per-index cost 1/l², summable. Local lengths: `point_bound` (proof
read) gives Σ_{l∈S} log l·lamG(l) ≤ 2000(C+1)³·f·m·b·L² for every finite S; lamG = 0 for
l > lStar outside Exc ∪ {g₀, g₁} (`CongBound_at`). Residual irreducibility
(`theorem_three_prime_holds`) has no restriction on l. Oddity for an expert: Hodge–Tate
weights ≈ b and lStar ≈ b/x^{O(1)}, so zero local defect is claimed for lStar < l < b,
outside the Fontaine–Laffaille range, via "position data" (weights in short windows not
divisible by l) and a Wach / prismatic comparison; `UseLoc.main`,
`exists_localPositionData_off_exceptional_primes` at statement level. Reader dispatched
(BEYONDFL).

LIVEPATH (no escalation; corrects DETSIG's consumer and MULTEQ's route). Top-down term
trace from ECL. (a) Seesaw: live `MIstar2` producer `miStar2_at_realisation_alt` ←
`joint_of_famAllQ_alt` ← `SeeSaw.mainX_of_lawsX` (20 steps; consumer side confirmed). H2
closed. (b) `BoundsMu`: live consumer `divClausesR_of`, same `IndefSide.boundsMu`; live
record from `base_lifts_package_of_primitive_links` (the producer DETSIG read); producers at
`LinksLemmas.lean:401`, `ConcretePkgSpec.lean:179` not live. Caveat: `PrimRows3` is read off
a bundle witness (`of_wit_alt`); the constructor storing it was not confirmed. (c) `MultEq`:
live producer `PsCo.Pc.multEq_of_sides` via `twisted_multiplicity_one`; MULTEQ's route
(`member_bundles_large_ue` … `multEq_of_trCusp`) is dead (only entry `EveryCharacterE.lean`,
uncalled). `siegelEisensteinSimplePole : UnusedSlot72`, a Prop defined as `True`; its only
live consumer `ResidueKilled.dm_of_two` ignores it, and the live
`DoublingMethodLocalZetaIntegrals` has a literal `True` conjunct where a pole clause was:
the pole statement is removed, not proved, and consumers are typed against the weaker
version. Other `True` slots: ECL:372 (unused), `TopShapeAlt True True` (unused). Script
check of 182 root field types: no other Prop defined as `True`. Reader dispatched (LIVEMULT).

BEYONDFL (no escalation; a new in-tree theorem, key link at statement level).
`CongBound_at`: congruence valuation ≤ Selmer + Ш + v_l(h_E) + epsQ, no local-at-l term.
Local defect = length of the span of Ribet/GMA cut cocycles at w | l modulo divisible
H¹_f; `UseLoc.main` proves it 0. Mechanism is a new integral comparison for widely spaced
weights, not a CM shape: `TopCore` (any crystalline ρ over unramified K) says a class cut
out by lattices in crystalline representations of the given weights lies in H¹_f, by a
dimension count (residual H⁰ = H² = 0; H¹_f a summand of rank dsum; a mod-l (φ,Γ)/Herr–Sen
count of residual admissible classes ≤ dsum). "Position data" is a residual genericity
condition on base-l digits of the weights (low window of length η with η+4σ+6 < l,
σ ≈ h/(l−1); cloud weights mod l avoid [−2σ−2, η+2σ+3]); l ∉ Exc gives it. Reader's toy
check (GL₂(Q_l), l = 101, not in the Lean): the excluded residues are exactly those where
Breuil–Mézard gives a crystalline lift; consistent. Inputs: `BhattScholzeIntegral` matches
the literature; `BlochKatoLocal` passed but discarded; no Fontaine–Laffaille. Non-literature
content, statement level only: `card_cocycles_independent_mod_coboundaries_le`, `realD`.
Exc budget confirmed (8b < lStar², |Exc| ≤ 388·Ub⁸, charge ≤ b).

LIVEMULT (no escalation). Live `MultEq` is the same predicate (only `def MultEq` is
FRA:118; same `IsGoodRep`/`NoFixed`) with gap condition `GapG` (consecutive HC gaps
≥ 100r⁴). Proof read (TEX:248-558): two simple trace formulas, no stabilisation;
pseudo-coefficients at ∞, e_τ·h·e_τ at type places, Iwahori coset of a strictly regular
torus element at an auxiliary split place; types kill elliptic tori with reducible
characteristic polynomial. (−1)^{pq} is present in `dsChar` and absorbed by an odd-rank
lemma; r = k+m−1 odd (`odd_r`). Non-tempered at ∞ killed by `LocalPC`, valid because of
`GapG`. Witness: constructor `bwit_exists_alt`; `Holds` tied to the bundle by definitional
equality and the field `eq`, transported in `twArgs_exists`; three links untraced
(transport proof; point record's `Holds` = output of `primRows3_of_parts`; `selB` = b.B).
`GalD` matches MULTEQ's description. Poles: the `True` conjunct is discarded; holomorphy at
s₀ = t/2 is part of the conclusion of `SiegelWeilUnitaryConvergent`. Unread bodies:
`nonFieldT`, `ellipticT`, `localPC_holds`, `SpecX.main`.

Round 10 status of the review's holes: H1 read to literature-shaped inputs; H2 closed; H3
restated and its consequences rechecked; H4 read; H5 on paper only. Corrections this round:
`hmt` iff is dead code (CONGMOD, JOIN, KILLAT); no single twist seed (ORDER); MULTEQ read a
dead route (conclusions survive on the live one). New in-tree mathematics met, at statement
level: `TopCore` and the cocycle count (BEYONDFL); global index budget `Concl` (TWSET).

## 14. Round 11

INDEXBUDGET (no escalation; corrects TWSET). `Concl` (WA:424) bounds, at every place, the
index in M_ka (integral cusp forms of weight ka on layer j) of a TEST lattice Θ spanned by
T-fold products of short weight-wL forms times short weight-wF forms; no theta lift is
involved. Index ≤ e·dim + r(λ), Σ r(λ) log Nλ ≤ rk·f·m·b·de2. Reason: determinant and
product formula. Local: twice the index of restricted forms on a generic curve ≤ ord_λ of
their discriminant plus a correction (HDA:20). Global: Σ ord_λ(Δ) log Nλ by the product
formula with Mahler-measure heights, Hadamard, sup norms of explicit forms, height of an
auxiliary section (HDB:24, NNF:86); sup-norm lower bound for nonzero integral forms by
evaluation at a CM point and Chowla–Selberg (`LAMwAt`). Not circular: `BoundsMu` takes
index bounds and lcv(M_j) as separate inputs; no lcv, slope or Rallis scalar on this path.
Size: per layer ≤ 12·f·m·b, total ≈ m·B0, the same tight "m" bucket; size·log(size) terms
are divided by T ≥ x^{Bx}·k·f/(m·de2); no factorial term. Literature: Krull–Akizuki,
Hadamard, Gauss's lemma, product formula, Chowla–Selberg; no arithmetic intersection
theory. Twisting buys the inclusion Θ ⊆ θ_j T_j (mirabolic chain; last link LeafTW1/TW2 is
a hypothesis at twisted places only), cost ≤ 2/p² per place. Unopened: suppliers of
LeafTW1/TW2, `QAt`, `ShareRd` (a dimension inequality the budget depends on); bodies
`localIdx`, `disc_product`, `heights_arith`, `deepCore`; top-layer inputs.

TOPCORE (no escalation). `TopCore` (TL2:193-212) is integral: K unramified, l ≥ 5, ρ
crystalline with labelled weights U, position hypotheses T1–T3; an extension of
O/λ^a(χ₁) by T₀⊗X is a subquotient of crystalline lattices of the prescribed weights iff
its class is in the image of H¹_f(T₀′)⊗X. Cocycle count (proof read in full): Herr cocycles
(b, g), g ∈ XN, b ∈ X^{−w}N, independent mod coboundaries, number ≤ dsum = Σ#{u < w}.
Mechanism: reduced Wach modules of any height h have φ-height bounded by X^h, (γ−1)N ⊆ XN,
Sen weights = HT weights mod l (`SenLat`); for h ≥ l the lattice is not unique but any two
are within X^σ, σ = Σ h_{i+j+1}/l^{j+1}; T2, T3 give no Sen weight in [0, σ+1] and exactly
d_i in the polar window [−w, −1]; a gauge step and the polar part of b give the bound.
Reader's test for K = Q_{l²} against Gee–Liu–Savitt weights (reader's computation, relies
on an unchecked lifting assumption): consistent; in the mixed case an extra admissible line
exists exactly when a base-l digit condition holds, which T2 forbids, so T2 is sharp. GL₃
test unfinished. Integral step (`adm_eq_H1fX`): induction on the power of λ with
admissibility at every level and saturation of H¹_f as an explicit clause; sound.
Crystallinity at w | l with automorphic HT weights is a clause `G2a` in `CoreNormFacts.g2`,
passed down; discharge not found; `G2a` has no "unramified at l" guard for l ≠ g₀, g₁.
Unread: integral `SenLat`, Herr-complex facts, `Gauge.main`, closeness lemma. Reader
dispatched (G2A).

MIRABOLIC (no escalation). Part (B) of the layer index does NOT run through
`CongBound_at`/KillAt/LinkN/VWin. All lattices sit in Zg_j, the (U,ψ)-eigenpart of the type
part for a product P of finite mirabolic groups at level primes. Chain in `local_bound`
(ONL:409): θT = Im ⊇ X₃ (LeafTW2: explicit theta series of the twisted tuple are lifts of
integral vectors; proved, read) ≈ eJ up to ε (LeafTW1, from the `IdxAt` part of GoodTw) ⊇
Th0 ⊇ |U|·ThK, then budget (A); Mackey property of the mirabolic pair divides r by |P:U|.
LeafTW1 mechanism: `ThURel` (twisted theta series = product of Hecke Euler-factor operators
at auxiliary primes applied to an untwisted one); determinant a unit mod l (Chebotarev
primes with Frobenius near tame inertia, plus `T3`: every residual eigensystem lifts to a
known signature, from `sig_all` and semisimplicity); Weierstrass-type evaluation, cost ≤ ε.
Integral surjectivity of theta is never proved: lift/non-lift congruences appear as index of
the base theta lattice and are paid by budget (A). Global object: one lattice R ⊆ K^D with
localisation ι(μ(y))·abelian₂(μ(y)), {μ ≠ μ0} finite; M_j, XE and the target are
tuple-independent. `ShareRd`: C(T−1, dimY)·del ≤ rk M_ka, proved (independent monomials).
`QAt` belongs to (A). Unread: `ThURel` supplier, `ExportTie` supplier, `sig_all`/`T3`.
Open question raised: where the congruence/Selmer machinery then enters the main chain.

G2A (no escalation; corrects GALREP on crystallinity). `CoreNormFacts.g2` =
`DeRhamFamilyAwayAlt ∧ DeRhamJumpsDistinctCondition`; `G2a`
(TrivialLocalCondition.lean:81-84): at every localisation i with l_i ≠ g₀, g₁, every w | l,
every r_x is crystalline with HT jumps the infinity-type weights; no explicit guard.
Constructor `facts_of_galois_preconditions_of_cutRec` (TPS/CFacts.lean:45-57) fills it by
`de_rham_points_weight_jumps_alt` (read): parameter unramified at w, local–global
compatibility at l gives de Rham + unramified WD + right jumps, `CrysIffWD` (Fontaine's
criterion) gives crystalline. l-adic input from `Row0b` via its `nice` clause (pst + WD
matching; `AboveB.crys`), so Row0b does carry crystalline content at l. Guard is
structural: `NData.SQ_l` (level and twist places not above l_i), `NAut.locV_unr`, the
`IsBCV` inert clause. Crystalline is the real notion: `IsCrysW` tied by `loc_tie` to
dim (V⊗B)^{G_K} = [K₀:ℚ_l]·dim V with B identified with in-tree `Per.Bcris`; same predicate
as in TopCore. Twists: χ₁ ramified only at Q_i, away from l_i. Oddities: `IsBCV` demands an
unramified base-change parameter at non-split w | l even for l ∈ {q, d, small} (claim of
`adm1`; live TopCore call excludes these l); `g4p` is `True` (not on this path); Row0b's
pst/WD clause for theta-lift and trace-limit representations not verified; sibling bundle
`HypothesesBridge.main` uses Published `CaraianiLocalGlobal` instead, live one undetermined.

WHERECONG (no escalation; corrects CONGMOD, MIRABOLIC, MAIN-ARGUMENT §5.2/§8). All of
`CongBound_at`, `KillAt`, `LinkN`, `VWin`, `OneCharU`, `AutEnd3Alt`, `Row0b` and residual
irreducibility are live and reach the slope chain through one scalar per lift, E2_j, the
dual index of the type-part projection T_j at twisted places (`jw_le`, TPE:48; SO:67, 70),
and through nothing else; E2 also sits in the base→column constant Q and DIV error `errB`.
Trunk: `divClausesR_of` → `IndefSide.boundsMu` → `toDivInputs0R` → `inpAt_of_alt` → DIVinN
(`topDesWin`, `divinN_of_hypV`). Ш part ≤ √b against ≈ x^{2.5}·b: the U(3) branch is
nearly idle numerically. `sig_all` is linear algebra on an explicit model, no deformation
ring. Open: fields carrying ON are typed `DIVinN → …`; `row_rRows_stage0_alt`, `ev_prem`
unopened. Dependency map added as MAIN-ARGUMENT §9.5.

Round 11 status. No defect. New in-tree mathematics now read to a mechanism: discriminant
index budget; mirabolic chain; `TopCore`. Unread beneath: integral `SenLat` and Herr facts;
`localIdx`, `disc_product`, `heights_arith`; `ThURel`, `ExportTie` suppliers; three witness
links (LIVEMULT); Row0b's pst/WD clause for trace-limit representations.

## 15. Round 12

SENLAT (no escalation; corrects TOPCORE §2e sign). `SenLat` (TL2:385-396) is proved
in-tree: for the Wach module N of any crystalline O-lattice, with E = q, the quotient
E^{−y}N^Δ/E^kN^Δ is O-free, γ is killed by ∏(γ − χ(γ)^{−x}), eigenspace ranks
Σ_{j∈[1−k,y]} mult_τ(x−j); exact in characteristic 0, no weight bound. Chain `stmtSen` →
`senLat_of_tie` → `lattice_at_level` → `lat_eq_fil` read; rests on `PerS.image` (Berger's
N⊗B_dR⁺ = Fil⁰; statement only). Mod-l step `senMultiset_base_lattice_eq_jumps_mod`
statement only. Closeness lemma read: a_{i−1} ≤ ⌊(a_i+h_i)/l⌋ iterates to σ; sharp in
rank 1. Herr/duality inputs standard (Tate duality, Euler characteristic Published and
passed down). `Gauge.main` read: ∇ has eigenvalue −a on X^aN/X^{a+1}N (window [0, σ+1]);
push g into X^{σ+3}N, then 1−φ bijective. Reader's tests: rank-1 label shift matches;
GL₃ with l = 101 found no allowed extra class (weight-swapped reducible lifts are excluded
by T2/T3). Not testable by hand: irreducible 3-dimensional lifts with weights ≫ l; that two
lifts of ρ̄₂ with the same weights reduce H¹_f to the same line (asserted via the largest
model).

ROWCRYS (no escalation; completes GALREP). Row0b l-adic clauses
(`WeightsConjBis.lean:39-73`): every CM field E, every l, every regular algebraic polarized
cuspidal π on GL_a, no weight bound. `crys`: where π_w is spherical at w | l, r|_w is
crystalline with HT weights (a−1)/2 − infinity type. `nice`: for abelian Weil image and
N = 0 (or tame with l > 16a²), de Rham, pst, WD(D_pst) = rc(π_w) Frobenius-semisimple.
Within BLGGT/Caraiani l = p. Proof is by l-adic limits for essentially every π
(`LimFinOdd`): geometric seeds U′ with the same weight as U at every embedding not over two
auxiliary places w₀, v′ (`SameWtOff`); crystallinity claimed only away from w₀, v′, by an
in-tree Kisin/Berger-type closure theorem `closedAtL` (limit of semistable representations
with fixed HT multiplicities; Breuil–Kisin frames with bound N = max|J|); all places above
l covered by three pairwise-apart choices identified by Chebotarev
(`JoinEndHolds.lean:19-62`). Even rank: two odd-rank theta lifts, peel characters. No
Published hypothesis on this path; C_cris, dR ⇒ pst and the closure theorem are in-tree
(statements read). Key unread: `CongUW4`/`wtLacEx_holds` (congruences with weight varying
only over w₀, v′). Root bundle: `⟨h, recTExists, h⟩`; the ECL field named
`caraianiLocalGlobalDual` has type `One.M.Row` (in-tree Row0b), misleading name;
`HypothesesBridge.main` not referenced. Purity in `ConclusionG6`: Jacquet–Shalika bound
plus half-integral exponents force |α| = 1 (`SixthWeightPurity.lean:18-86`); in-tree
Jacquet–Shalika; no Ramanujan input.

E1LOOSE (no escalation; corrects INDEXBUDGET, WHERECONG). A. The "generic curve" is a
generic 0-dimensional intersection Z = {s₁ = … = s_d = 0} in D(s₀), d = dimY, s_i generic
combinations of weight-wL forms over the Gauss-valuation DVR O_λ(T). A weight wF+T·wL form
maps to its Taylor jet of order < T−d along Z; Hasse derivatives in the generic
coefficients pick each of the C(T−1,d) coefficients integrally (`TaylorHasse`, `Column`).
Local: 2·Ila ≤ ord_λ Δ + 2·N_λ(ta′) − t. Global: exact product formula (`disc_product`)
then Hadamard. Sizes close with slack ≥ a power of x; CM lower bound is paid at weight
≈ k·f·b by only rz ≤ 44·dimY²·rk/T forms, T ≥ PPv⁴·dimY³·k·f/(m·de2). Live Bx = 0.
Tightness of E1 is in the 12·f·m·b allocation and the J0 term EJ ≤ 32·x^ε·f·m·b·L.
B. ON does not use the DIVinN premise (`onto_path_alt` binds it as `_`,
TPS/OntoPath.lean:23); producers of DIVinN never mention ON/BoundsMu; no circularity. E1
has Galois input through J0 (`ExponentStatement`: `CuspUAlt`, base change, Bhatt–Scholze,
Chebotarev), none from the congruence chain. C. Witness: κ kept literally; λ replaced by
`zeroLam` (differs only on zero eigenspaces), identities re-proved by congruence; `Holds`
originates in `primRows3_of_parts`; `selB` = (σ).B for the single σ from `classSel`.
Unread: SameGrp transports (statements only); whether L6/BoundsMu read λ on zero parts.

Round 12 status. No defect. Everything named load-bearing in rounds 10–11 has now been
read at least to a mechanism with a live supplier. Deepest unread inputs: `CongUW4` /
`wtLacEx_holds` (congruences with weight varying over two places); `PerS.image`; in-tree
C_cris and closure theorem bodies; `ThURel`/`ExportTie` suppliers; `J0`/`ExponentStatement`.

## 16. Round 13: the spine

ENDGAME (no escalation). Landau lemma `zeroFree_of_rpow_window`
(`LT/ZeroFreeOfRpowWindow.lean:11-14`): G(y) ≤ C·y^θ for every y in windows [Y, Y^{1+δ}],
Y arbitrarily large; off windows only |g| ≤ Cy²; conclusion: no zero of any L(s, χ_i) (ζ
included) with Re s > θ. All bodies read except `iteratedDeriv_laplace` (statement).
Mechanism: k-th Taylor coefficient at σ+iγ is a Laplace transform against u^k e^{−σu}/k!;
k ≈ (1+δ/2)σU concentrates it on [U, (1+δ)U] (Chernoff); σ ≈ 36/δ² (336 here) so tails with
the e^{2u} bound lose to σ^{−k}; nearest-singularity argument, real pole with positive
residue or γ chosen so one complex pole is uniquely nearest. e_D, e_L are error exponents of
the DIV bound and LossBounds (≥ 0); 7 = 3+3+1. Non-cancellation of zeros needs only
positive weights: residue at ρ is −1/(ρ(ρ−1)) times a nonnegative combination of
multiplicities (`poleData.lean:346-383`). c = (3o+1)^{−1} is the Fourier coefficient at ψ^j
of the share measure (3 + 1_{A₀})/(3o+1); any α ≥ 0, β > 0 would do; no reason found for 3.
ψ enters as the A/A₀ coordinate of Frobenius. ASK counts primes inert in ℚ(√−d); the pieces
twisted by χ_{−d}, (·/q), (·/qd) are bounded two-sidedly at the single point y = x by host
selection (`PairGood.bounds`), so L(ψχ_{−d}) never enters the Landau function. G_m is
host-independent. Order of choices: ψ; (e_D, e_L, ε₁); s; ε with
(e_D+e_L+7)ε ≤ (Re s − 1/2)/2; family with 3/2-windows; per x a host; Landau parameters.
ε → 0 pointwise in s. Inputs not rechecked here: `core_gm` at every x of each window;
`PairGood`.

LEDGER (no escalation; resolves the signal splitting type; H5 not in the Lean). Fifteen
lines L0–L15 plus D1–D5 for DIV, each a Lean statement, combined by proved linear
arithmetic. Slope side: Bost (MB:151) → DIV (MB:118) → Slopes, EComp5, Count5 →
`s_lower5` (LoC:50; the two Fo terms cancel). Main term: `key_identity5` (LoC:105), an
exact identity turning m·ph(a_t) − m·a_t·logΩ into Main; `Ga_bound5` (LoC:113). Closing:
LossBounds, ASK − Ga ≤ LoP (QSB:34) → ASK ≤ Main + ErrX5at (LoC:175) → `errX5at_le`
(PCh:613). Bridge: `ch_top`, `ch_balance`, `th_le`, `core`, `GrowthSizeBound`, `core_gm`
(CG:12-74). Live call has eD = 2, eL = 0 (TS:52): final statement G_m(x) ≤ x^{1/2+9ε}
(9 = 5 + 3 + 1); error/U ≤ 20·x^{1/2+2.625ε} from the live record. ε fixed per family
`FamP ε`; limit only in Landau. The gain Σ_p γ_p·a·log p never appears: the gain is an
abstract scalar Ga, bounded below by `Loss_at` and above by the slope chain; Main is matched
to the explicit-formula MAIN by definition (CT:11-35), L′/L constants tied by `Char_at`
(QLD:226). Precision: archimedean side relative x^{−1/2+O(ε)}; p-adic side
LoP = c·|TT|·m·b (eL = 0), i.e. relative ≈ x^{−1}, a hypothesis of `LossesSmallShares`,
producer untraced. Primes: signal = Frobenius ((1,0),h), inert in ℚ(√−d), split in ℚ(√−q)
(HCl:116-117, 178-179), thick partners, Riesz weight b·(x/p − 1)₊; inertClass =
((1,1),h), top/thin partners, removed in the bridge by ThinScales (NUMTEST4's "inert in
both" describes these); split primes not in ASK. H5 (Ga − ASK ≤ budget) is not in the
Lean; only `ga_le_at`, far too weak; `exists_data_completion` (PCh:306) shows the
SizeData₂ clauses are satisfiable from ASK ≤ Main + error alone with Ga := ASK − LoP, so
content lies in the ties to real lattices. Unread: `proposition_size_bound`, `core_ineq`,
`divIneqRecord`, `windowInequality_of_artinInputs`; hop TS:52 → `linkGLOBAL7_pk` inferred.

ENGINE (no escalation). One lift, one inert prime, as a paper proof. θ_{c,c′} (`kerTh` =
`thC`, KerTh.lean:26-31; XiIndCClass.lean:148-239): reduced theta function on
ℂ^{Tau×N′×N}, form H = area⁻¹·Σ z·w̄, lattice δ·Φ_Tau(AA0·Hom(N, N′)), a finite Heisenberg
sum of torsion translates of one vacuum theta built from th0 = U_t(σ*)/U_t(σ*)(0).
Variables are log coordinates z = ℓ(X), ℓ the height-2 Honda logarithm; integral means
integral in z/ϖ, ϖ^{p²−1} = p, so v(∂^n f(0)) ≥ v(n!) − |n|/(p²−1). Exponent per top s and
lift: v ≥ Σ_{e odd, e∉dSet(s)} (a_s/p^e − cap_{s+e})₊ − deLoss, for every jet (top linear
forms)^a × (column minors), i.e. on the whole integral lattice Int_j. cap = number of
minors at the partner position (ν₁, or ν₂ at a top; FGS:36-38, 398-419); at a non-top
partner this is λ_{s,1} + w_{j+1}(s). Read to the bottom, downstream of clause `adm2`
(kernel at a served place = exp(−Ph)·(LT-integral), Ph a hyperbolic cross Gaussian):
Gaussian class (adm2 + RestBeta + RestGc + Dwork); self-Gaussian cancellation (Frobenius
rotates positions by one, orbit length n′ even, `iso_fK`/`dual_fK`,
`hyperbolic_plane_split`); cap lemma (multiplication by a linear form is adjoint to a
directional derivative; shifted minors are a rank-one update, each absorbs at most one
derivative); Legendre (`TermBound`, `StarArith`); odd e (Legendre gives Σ_{e≥1} a/p^e, the
height-2 rescaling costs Σ_{e even} a/p^e; Gaussian monomials have degree p^{2l+1});
composition `main_ind` (each step for an arbitrary element of Int_j, gains add). Numerics:
NUMTEST3/4 tested the Lean's object; NUMTEST (σ alone keeps its self-Gaussian) and NUMTEST2
did not; ℘ is the Gaussian-free w = 0 case. Statements only: `adm2` for the live kernel
(`first_kernel_law_global_small`), `posOK`, `decomposition_of_hh`, generic-frame `reduce`,
`adm7`, `ZL_bound`, cap = ledger w via `LatTied`. deLoss ≈ r0·r1·log ≈ x^{798+ε} per prime
per lift: harmless only because b = e^{x^ε} — orchestrator's inference: this is the reason
b is exponential (π(X″)·x^{798} ≪ b). dSet exclusions not traced into the ledger.
