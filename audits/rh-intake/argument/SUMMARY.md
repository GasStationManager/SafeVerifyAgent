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
  confirmed (NODE-NUMTEST and its addendum); the capped two-variable case
  (Eisenstein–Kronecker numbers e*_{a,b}, b ≤ w ≪ a) is the test still to run.
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
