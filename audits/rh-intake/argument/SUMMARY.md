# The argument, as reconstructed from the Lean source (checkpoint 1)

Artifact: alpo.ge `lean.tar.gz`, SHA-256 `9631b4f0…49c7fc`. Method: `PROTOCOL.md`. Fifteen
explainer nodes and one reviewer, each a separate agent reading source; nothing compiled.
Every statement below is "the Lean says, as read by one agent" unless marked otherwise.
Only the root was put through a reviewer; the other nodes were cross-checked only where
sibling explainers overlapped (five corrections, listed in §4).

**Status: no defect found; the argument has a coherent architecture; its two
load-bearing theorems have been located and stated but not read to the bottom.**

## 1. Outline

Target: L(s, χ) ≠ 0 for Re s > 1/2, every Dirichlet χ (`EveryCharacter`).

1. **Landau on windows** (NODE-LANDAU). For primitive ψ let
   Gm(y) = Gz(y) + Σ_{χ ∈ ⟨ψ⟩, χ≠1} (3o+1)⁻¹ Re g_χ(y), with
   Gz(y) = Σ_{n≤y} Λ(n)(y/n − 1) − y log y + (1+γ)y and
   g_χ(y) = Σ_{n≤y} Λ(n)χ(n)(y/n − 1) + y·L′/L(1,χ).
   If Gm(x) ≤ x^θ on windows [Y, Y^{3/2}] for arbitrarily large Y, no character in the
   level has a zero with Re s > θ. One-sided, windowed, Taylor-coefficient form of
   Landau's theorem; positivity is of the kernel and of the weights, not of coefficients.
2. **Reduction to a prime count** (NODE-COREGM). An exact identity turns
   "Gm(x) ≤ x^{1/2+O(ε)}" into "ASK ≤ MAIN + error", ASK a weighted count of prime powers
   p^e (e odd) inert in a quadratic subfield of an auxiliary field. The exponent 1/2 is a
   parameter balance x/m + m at m ≈ √x, m the number of lifts.
3. **Host fields** (NODE-HOSTS, NODE-PAIRGOOD). For every large window there is an abelian
   CM field E ⊃ ℚ(√−q, √−d), degree ≍ x^{2+8ε}, with q, d enormous (log q ≈ Y^{ε/5}) chosen
   by zero-density, mean-square and Markov so that the twists of the level by (·/q), (·/d)
   satisfy a square-root bound at the single point y = x. Unconditional; no circularity.
4. **Slope method** (NODE-SLOPE, NODE-FAMILY, NODE-LOSS, NODE-SLOPESN, NODE-DIV). Over E:
   lattices M_u of p-adic/integral algebraic modular forms on unitary groups, a target
   lattice RR, Bessel-period pairings B_u. The "gain" at an inert p is *defined* as the
   prime count (Legendre-type exponent γ_p = p/(p²−1) = Σ_{e odd} p^{−e}); the lattice is
   *defined* as N_u = ∏ 𝔭^{−gain}·NuLat_u; so its slope is μ(M_u) + gain by construction.
   A proved slope inequality bounds the mean slope of the N_u by the slope of RR^∨ plus
   the height of B_u, provided **B_u(N_u) ⊆ RR^∨**. A degree computation bounds that by
   MAIN. Hence count ≤ MAIN + error.
5. **The two theorems that carry it.**
   - **(P) Period divisibility** (NODE-ROWSU, NODE-TWU). B_u(N_u) ⊆ RR^∨ unwinds to: every
     Bessel period of every form in NuLat_u is divisible by 𝔭^{⌊e·Σ gain⌋} at each inert
     place. Supplied by: the m-fold chain of theta-lift steps maps the Hecke-generated
     lattice into ϖ^{Σgain − τ}·Int, from (a) coefficient bounds for theta kernels via a
     Dwork exponential in a height-2 Lubin–Tate parameter, (b) "kernel commutation": the
     chain carries a Hecke operator to a Hecke polynomial one level down, each step gaining
     γ_p·Σa, (c) a proved colength bound showing the lattice is p^τ·M up to rank·x^{−ε}.
   - **(V) Uniform arithmetic volume** (NODE-COVOL, NODE-HS). (1/D)·log covol of integral
     cusp forms of given vector weight on unitary Shimura varieties of signature
     (k+i, m−i−1) is ≤ (p−q)·Σ w·logΩ + error, logΩ = γ + log(π/v) − L′/L(1,χ_d) the
     Chowla–Selberg period, uniformly over all hosts. Supplied by an in-tree *effective*
     slope bound at a single tensor power (not the asymptotic Hilbert–Samuel theorem,
     which is also in the tree but not used here) and a uniform volume theorem
     `VolumeTheoremX` with one constant for all CM fields, levels and towers.
6. **Host admissibility needs a Selmer bound** (NODE-VWIN). `VWin`: for the fields E,
   Σ_l Σ_{k < x^401} log #Ш¹(G_{E,S_l}, ℚ_l/ℤ_l(−k)) ≤ exp(x^ε/2). Minus part by a
   main-conjecture-shaped bound; plus part by Eisenstein–cusp congruences on U(3), using
   Galois representations for GL₃ over imaginary quadratic fields (constructed in the tree
   by a theta lift).

## 2. How this compares with the author's note

Matches: Stepanov-style multiplicity balance at √x; multiplicity won per theta lift
between definite unitary groups; Legendre-type divisibility at inert primes; Bessel
periods; a slope inequality; Chowla–Selberg; a Vandiver-flavoured cohomological input;
resolution of singularities and Hilbert–Samuel in the positivity package.
Not located: "Behrend", "Iwasawa tower by pigeonhole", "relative trace formula", the
"sixfold cover of GL₅". They may sit below the depth reached.

## 3. Open nodes, ranked by how much rests on them

| # | node | why it matters | read so far |
|---|---|---|---|
| 1 | `stmt_proved` and the 13-clause `admitted` package, incl. "the chain map is a sum of theta-kernel integrals" (`FormalGroupSystem.lean:566-771`, `PrvAndKernelCommutation…:107`) | the whole of (P) | skeleton only |
| 2 | `VolumeTheoremX` / `final_theorem_of_inputs_right` (`GoodTowerExistsX.lean:28`) | uniformity in (V); not a published theorem | statement only |
| 3 | `SlopeBound` / `slopeLowerBound_topLattice_offHypersurface` (`HermSysHypOneLeLambdaZero.lean:243`) | effective Hilbert–Samuel substitute in (V) | statement only |
| 4 | nonvanishing and near-full rank of B_u on N_u (`LinkS`, `LinkIRR`, `InputSG`) | (P) is satisfied by B_u = 0; the slope inequality must exclude it for the *same* pairing | not opened |
| 5 | `tuplesHaveLocalModels_of_standardColumnObjects` | ties local chain models to the global chain | not opened |
| 6 | `OneCharU`, `CongruenceNumberRankThree` | upper bound on Ш⁺ from congruences, uniform in l and k; needs residually reducible R = T for U(3) | statements only |
| 7 | `ThetaIntegralsAgree` / `theoremK_head2` | a twisted second-term identity with tower relations, not matched to one published theorem | statement only |
| 8 | `landau_tails`, `meanSqK`/`twistK`, `joint_a_ramified_holds`, `BoundsMu` | believed standard; bodies unread | statements only |

## 4. Corrections made between nodes (kept, not smoothed)

- ROOT said the Landau step uses non-negative averaged coefficients. LANDAU and
  REVIEW-ROOT: it does not; positivity is of the kernel and the weights.
- LOSS found the only named divisibility clause instantiated with the zero chain map.
  SLOPESN and TWU: that is the branch feeding the colength clause, where the chain is
  irrelevant; the divisibility branch uses the family's own chain.
- COREGM/THETA/HOSTS suspected the family's numerical data are free witnesses. FAMILY:
  the datum is built over the host; the selector's `True` predicate is glue. But the 11
  clauses of `SizeData₂` are empty on their own (`exists_data_completion`).
- SLOPESN said `twU` is never constructed. ROWSU and TWU traced its supplier
  (`hServ` ← `ServH` ← `RowTwU` ← `rowTwU_of_models`).
- COVOL said the lower slope bound is an induction over layers. HS: top layer by
  `LowDef`, every other layer by a single cover.

## 5. Escalations for an expert

- **E5.** (P) as stated holds for the zero pairing. Confirm that the slope inequality's
  rank/frame hypothesis is about the same B_u on the same N_u (open node 4).
- **E6.** `VolumeTheoremX`: one constant for all unitary Shimura varieties in the family.
  If true and proved here it is a major theorem in its own right; read its statement for
  a quantifier or normalisation that makes it weaker than it looks.
- **E7.** The slope inequality's error has no rank or field-degree term (NODE-SLOPE).
- **E8.** `OneCharU`: Selmer upper bounds from Eisenstein congruences, uniform in l.
- **E9.** Scales: b = exp(x^ε) and every "additive" error carries a factor b. All
  comparisons are relative to b; an expert should check one chain of inequalities end to
  end with actual magnitudes.
- Smaller: `flat_tensor_swap_isIso` ignores its three premises; `entStd` has four zero
  fields; `th : R.L.Sec := 0` in the geometric data; every `*_of_literature O` ignores `O`.
