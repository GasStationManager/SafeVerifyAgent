# NODE-WHYHALF: where the exponent 1/2 comes from

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `SC` = `Formalism/SizeWindowBrackets/SChain.lean`
- `GB` = `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean`
- `EW` = `Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean`
- `QSB` = `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`
- `RV` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean`
- `DA` = `Formalism/LocalRingCardinality/DataArith.lean`, `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`
- `PRM` = `Formalism/LocalRingCardinality/Params.lean`, `INP` = `Formalism/LocalToGlobal/Divisibility/Inputs.lean`
- `SLN` = `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SecondLabelsNonempty.lean`
- `BS` = `Formalism/BehrendSets/Statement.lean`

This is an explanation node, not a gap hunt. Lines marked **[Lean]** were read at the cited place in this pass.
Lines marked **[node]** are taken from the named node. Lines marked **[inf]** are my inference.

## 0. The answer in five sentences

1. One theta lift is one Chebyshev identity. On the p-adic side its period is divisible by the inert half of a!
   (Legendre plus Lubin–Tate). On the archimedean side its size is a!·Ω^{−a}, and the Chowla–Selberg period Ω already
   contains the average of the split half. The two sides agree to first order.
2. Composing m lifts multiplies **both** sides by m. Each lift is again an order-a derivative against its own kernel,
   and the divisibility recurs undiminished on every integral form (CHAININD). That is the "multiplicity".
3. The comparison also pays **boundary costs** that are paid once per chain: the slope of the source lattice, the
   normalisation of the last (Bessel) map, and the Harder–Narasimhan spread in Bost's inequality. Each is as large as
   **one whole copy** of the signal. So a single lift gives only the trivial bound Gm(x) ≲ x^{1+O(ε)}, which is
   Chebyshev quality. Amortised over m copies, the boundary costs give relative error 1/m.
4. Each lift also pays an **interior cost that grows with the length of the chain**. The target layer j lives on a
   unitary group of signature (k+j−1, m−j). Its covolume is exact only in the p−q flat directions, so the error is
   ∝ q ≤ m. The same holds for the residual of the logΩ cancellation and for the congruence modules. So the per-lift
   error is B0 = f·m·b·x^ε, proportional to m, and the total is m·B0 ∝ m². Relative to the signal this is m/x.
5. Relative error 1/m + m/x is minimised at m ≈ √x, giving relative x^{−1/2}, i.e. Gm(x) ≲ x^{1/2+O(ε)}. A larger
   m makes the m-family dominate. A per-lift cost independent of m would prove ψ(x) = x + O(x^{δ}) for every δ, which
   is false. So the growth of the per-lift cost is not a removable inefficiency: it is where Gz(x) = Ω±(x^{1/2})
   shows up in this argument. **[inf]**

## 1. The one-lift inequality and the two error families

### 1.1 Schematic, for one lift and one top place of weight a

Here ph(a) = a log a − a = log a! + O(log a), y = a/w is the Riesz length, and w ≈ b at thick partner places.

```
 Σ_{p inert} 2 log p · v_p(period)        ≤   [ph(a) − a·logΩ]                  archimedean height (Fock/Cauchy), HEIGHT
 ≥ Σ_n Λ(n)(1−χ_d(n))(a/n − w)₊ − O(1)/p        + [−μ(source)]                        source floor, Slopes
   (Legendre + LT, LOCALDIV, NUMTEST3/4)        + [μ(target)]  − [log T]               DIV (A)+(B); last map, Count5
                                                + [Bost loss: u·log(1+HH/u)]           SlopeIneq, RANK
```

with logΩ = γ + log(π/v) − L′/L(1,χ_d) (`DP2:224` **[node]** ACCOUNT, DIV). Writing the right side as a function of y,
ph(a) − a logΩ − a log w + (log T bookkeeping) = w·[y log y − (1+γ)y + y·L′/L(1,χ_d)] + (exactly cancelled terms)
(HEIGHT §2(b), `key_identity5` **[node]**). This is the explicit-formula main term of Σ Λ(n)(1−χ_d(n))(y/n − 1)₊. So the
inequality reads

  **Σ_{n} Λ(n)(1−χ_d(n))(y/n−1)₊ ≤ main term + (boundary errors) + (interior errors)**,

which is the statement Gm(x) ≤ x^θ once it is normalised and the character bookkeeping (§4) is done.

### 1.2 Orders of magnitude, from the Lean's own error term

The conclusion of the chain is `ASK ≤ Main + ErrX5at` (`QSB:45-54` **[Lean]**). The terms of ErrX5at:

| term in `ErrX5at` (`QSB:45-54`) | size | family | origin in plain terms |
|---|---|---|---|
| ΣA·cCount·(La + m²La/k) | \|TT\|·a·x^ε | one-off | `Count5` (`QSB:27-32` **[Lean]**): log T(u) for the prime T that scales the last map must match Σ_j mean log(wv/π) + m·lg to ±La. The precision of a single prime's position in a short window, paid once. |
| cDiv·nT·a·La | \|TT\|·a·x^ε | one-off | DIV's top-place boundary terms: the last-map Bessel functional (hA, logc, logxi ≲ Nn·b′·log 2a) and the top part of δ. They are m-independent only because b′ = a/X′ with `p32 : b′·Nn ≤ a` and `p33 : m·k·b′ ≤ a` (`INP:156,158` **[Lean]**; HEIGHT §2(d)). |
| cSlope·nT·a·La·(1+m/k) | \|TT\|·a·x^ε | one-off | `Slopes`: the floor μ(M_u) ≥ −c·nT·a·La on the slope of the level-0 source lattice of weight-a forms (WRITEUP (3)). |
| (1−δ̄)⁻¹·4 log(1+x^{cHH})·UBar5, with UBar5 ∋ cSlope·nT·a·La(2+m/k) (`QSB:41-43` **[Lean]**) | \|TT\|·a·x^ε·log x | one-off (its nT·a·La part) | Bost/HN: the mean-slope form of Bost's inequality loses u·log(1+HH/u), where u is the HN spread of the sources. That spread is one copy. |
| cDiv·m·(B0+Nc)·x^{eDiv ε} | m·f·m·b·x^{O(ε)} | per lift | DIV interior: per-layer covolume error C·B0·log log x (COVOL), the logΩ residual Σ_j(p_j−q_j−k)·w·logΩ with \|p_j−q_j−k\| ≤ m (ACCOUNT C2), and the congruence allowance η_j ≤ D0·C·x^ε(B0+Nc) (CONGMOD) |
| m·cE·B0 | m²·f·b·x^ε | per lift | `EComp5` (`QSB:24-25` **[Lean]**): the per-lift local error E_j (DIV-side automorphism denominators, local lengths) |
| UBar5 ∋ cSl1·m·B0 | m²·f·b·x^ε·log x | per lift | QSB upper bound on μ_max(N_u) (`QSB:21` **[Lean]**), which feeds the HN spread |
| log\|W\| ≤ (k−3) log 2, LoP, MLo5, (η̄+4√ē)x^{cHH}b | ≪ budget | — | polynomial in x, or x^{−1/2} of the budget (ACCOUNT §3(i)) |

B0 = `sizeBudget` = f·m·b·x^ε (`DA:200` **[Lean]**). **The per-lift error B0 itself contains the factor m.** That
is the whole point. Nc = T2·k·b·x^{2ε}/n² (`DA:204-210` **[Lean]**) is a third, subdominant per-lift term. I did not
trace where it comes from.

### 1.3 The balance, as the Lean writes it

`SizeWindows` (`GB:109-117` **[Lean]**) bounds the error by

  Err ≤ x^{Cε}·[ nT·aE·(1 + m²/k) + m·(2n·m·b·x^ε + nT2·k·b·x^{2ε}/n²) ]

(the bracket is `errorBracketSizeWindows`, `EW:133-135` **[Lean]**). `GrowthSizeBound` (`GB:119-122` **[Lean]**)
divides by the signal unit U = nT·m·b·δ/2, with δ = nT2/n. Using aE ≤ 2xb, nT ≥ x^{−ε/8}n/2, δ ≥ x^{−ε}
(`SC:53-58` **[Lean]**) and m²/k ≤ m/x ≤ 1 (from x·m ≤ k, `GB:114` **[Lean]**):

```
 Gm(x) ≲ x^{O(ε)} · [ 2aE/(m·b·δ)  +  4n·m/(nT·δ)  +  2k/(n·nT) ]
       ≲ x^{O(ε)} · [    x/m       +       m       +    k/n²    ] ,   minimised at m ≈ √x  ⇒  Gm(x) ≲ x^{1/2+O(ε)}.
```

The windows in the Lean are exactly what keep each bracket at √x:
- x^{1/2−ε} ≤ m (`RestSize`, `SC:57` **[Lean]**);
- m ≤ x^{1/2+ε/2} (`ErrWindows0`, `EW:32` **[Lean]**; `SizeWindows`, `GB:113`);
- k ≤ n²·x^{1/2−ε} (`SC:58`, `GB:114` **[Lean]**);
- m ≈ √(x·x^{−ε/8}) (`RankVal`, `RV:31` **[Lean]**).

In relative terms the signal is m copies of |TT|·a·(log), and the error is 1 copy·x^{O(ε)} + m·(m/x) copies.
So the relative error is ≈ 1/m + m/x. **The brief's reading is confirmed**, with two refinements:
1. The one-off family is not one boundary term but four (last map/T, top-place weights, source floor, HN spread).
   Only the second is m-independent "by parameter choice". The other three are m-independent because they concern the
   ends of the chain.
2. There is a third bracket, k/n², which is also at √x. It is held there by k ≤ n²x^{1/2−ε}.

### 1.4 What m = 1 would give **[inf]**

Formally, putting m = 1 in the bracket gives Gm ≲ x^{1+O(ε)}, the trivial bound. The Lean never instantiates m = 1
(HOSTS: m even, m ≥ 2; RestSize: m ≥ x^{1/2−ε}). The point is that the one-off errors are each of size
|TT|·a·x^ε, which is **at least one full copy** of the per-lift signal |TT|·a·(log x … x^{ε/3}) (ACCOUNT §2, the ASK
line). A single lift is therefore at best a Chebyshev-type statement, and the classical experience is reproduced
exactly. Everything better than trivial comes from amortising those copies over m lifts.

### 1.5 Why the interior layers cost only m/x each, not O(1)

The interior of the chain never meets the comparison as a free quantity:
- The lattice Int_j is the same Lean object as the target of lift j−1 and as the source of lift j (CHAININD §1.1,
  ORBIT item 2). Its slope never enters.
- Per layer, three quantities of size k·f·b·x^ε cancel down to one ph(a_t) − a_t·logΩ per top, with error O(B0):
  - the jet-step norm Σ ph(ν) − Σν·logΩ (proved Fock bound);
  - the theta scalar λ_j (hook product, L6, a premise);
  - the flat covolume (p_j−q_j)·w·logΩ (Chowla–Selberg).

  They cancel because Σ_j(p_j − q_j) = m·k exactly (`PRM:46` sigW (k+j−1, m−j) **[Lean]**; ACCOUNT C2; HEIGHT §2(d)).
- What survives per layer is ∝ q_j·w and ∝ (p_j − q_j − k)·w, both ≤ m·f·b·La ≈ B0.

The relative precision needed is x^{−4} (ACCOUNT C2). This is the "cancellation of order-m terms … via
Chowla–Selberg, Weyl, and Siegel mass" of the author's item 9 **[inf: matching]**.

## 2. The Stepanov analogy

Stepanov, schematically (standard): F(x) vanishes to order ℓ at each of N points and has degree D, so ℓ·N ≤ D. Here
D = ℓ·q + (one-off, ≈ q) + (cost of the derivatives, ≈ ℓ²), so N ≤ q + O(q/ℓ) + O(ℓ) and ℓ ≈ √q.

| Stepanov | here | node(s) |
|---|---|---|
| (a) the curve and its F_q-points | served (signal) inert primes p ≤ x: Frobenius in the class "inert in K, hermitian form split at p", weighted by the Riesz weight Λ(n)(y/n−1)₊ at scale y ≈ x. "Points" are primes; the "curve" is the CM structure (supersingular reduction at inert p) | SERVED, SIGNAL, NUMTEST3 |
| x^q = x at every point (Frobenius is a constant for d/dx) | the derivative of order a of the CM theta kernel is divisible at **every** served p simultaneously by p^{Σ_{e odd}(a/p^e − w)₊}. In the Lubin–Tate coordinate the kernel is integral × Dwork Gaussians, and at served places the Gaussians cancel (A·A^σ + C·C^σ = 0) | KERNELLAW, GAUSSCLASS, NUMTEST3 |
| (b) the auxiliary polynomial | the period map B_u: the m-fold iterated theta lift followed by the Bessel period, applied to the rescaled lattice N_u = 𝔭^{−sg}·NuLat_u of weight-a forms. It is a vector of algebraic numbers | WRITEUP (1),(4), SLOPESN |
| (c) vanishing order ℓ | p-adic divisibility Σ_{j≤m} gain_j ≈ m·Σ_{e odd}(a/p^e − w)₊. Each lift is again an order-a derivative of its own level-j kernel. The bound holds for every integral form at every level, so the same primes divide each of the m lifts. Multiplicity = m, not "a split into m parts" | CHAININD §0.2, ORBIT |
| (d) degree bound | product formula in slope form: Bost's slope inequality plus the archimedean height (Fock/Cauchy, ≈ m·(ph(a) − a logΩ)) plus target covolumes (flat part by Chowla–Selberg) | RANK, HEIGHT, COVOL, DIV |
| one-off degree ≈ q | the four boundary terms of §1.2: last map/T, top weights, source floor, HN spread | ACCOUNT, HEIGHT §2(d) |
| derivative overhead ≈ ℓ² | m lifts × per-lift error B0 ∝ m: the target layer j has signature (k+j−1, m−j), so a chain of m lifts forces q up to m−1, and only the p−q flat directions are computed exactly | `PRM:46`, `DA:200`, COVOL, VOLUME |
| (e) F ≢ 0: independence of monomials | Theorem S: near-orthogonality of Bessel periods (to b^{−6}) plus limit multiplicity (dimension count) give robust near-surjectivity of ⊕_u B_u onto RR^∨, which excludes B_u = 0 | RANK, THEOREMS, PAIRB, COUNT |

**Is the cap m ≲ √x forced by non-vanishing, as ℓ ≲ √q is in Stepanov?** No, not in the Lean. The constraints that
mention m are:

| constraint | file:line | binds m? |
|---|---|---|
| m ≥ x^{1/2−ε} | `SC:57` **[Lean]** | lower bound: the x/m family |
| m ≤ x^{1/2+ε/2} | `EW:32`, `GB:113` **[Lean]** | upper bound: the m family. **This is the cap.** |
| x·m ≤ k ≤ n²·x^{1/2−ε} | `EW:32`, `GB:114` **[Lean]** | m ≤ n²x^{−1/2−ε}: slack |
| x^{ε/2}·m⁵·f·x^ε ≤ k ≤ x⁵ (Theorem S, `RankNums.k_lo/k_hi`) | `SLN:38-39` **[Lean]** | m ≲ x^{5/9}: slack. **[inf]** With f ≈ 2n and k ≤ n²x^{1/2}, it needs m⁵ ≲ n·x^{1/2}. With n ≈ x^{2+8ε} that is again about √x, but enlarging n would relax it, so it is not the reason. |
| m⁴ ≤ f | `SLN:36` **[Lean]** | used for 2m ≤ 2^{…} (`two_m_le_two_pow`), i.e. the host has at least m positions; slack |
| m² ≤ k + m(t+1) (HOSTS) | **[node]** | slack (t ≈ x^{398}) |

So non-vanishing (Theorem S) costs a polynomial relation k ≳ m⁵·f·log b, which the parameters absorb. The cap is the
error growth: the per-lift cost grows linearly in the chain length, exactly like Stepanov's ℓ² overhead. It is not the
non-vanishing condition. In Stepanov these two coincide (the overhead is what makes the linear system solvable). Here
they have separated. **[inf]** Larger m would not help, because x/m + m ≥ 2√x: past √x the m-family dominates.

## 3. Why it is not Chebyshev: what is exact and what is only bounded

Chebyshev fails to give more than constants for three reasons:
- (i) the integer C(2n,n) is not supported only on the primes counted;
- (ii) there is no multiplicity;
- (iii) divisibility is bounded but not computed.

Here (ii) is supplied by m (§1), and (i) and (iii) are replaced by exact computations.

### Exact (the main term is computed, not bounded)

1. **Legendre and LT divisibility, to O(1) per prime.**
   - Per lift and per prime the gain is Σ_{e odd}(a/p^e − w)₊ minus at most ≈ 1. Measured: −0.98 (NUMTEST3), −1.54
     (NUMTEST4), −1.13 (SIGNAL two-tops).
   - Summed over p ≤ x with weight log p this is O(x) per top per lift, against a signal a = x·b per top per lift.
   - So digit-sum and floor losses are relatively 1/b = e^{−x^ε}, which is negligible. This is one reason the weight is
     a = x·b (`DP2:31` **[Lean]**).
2. **Caps localise exactly.** max(A−w, 0) + min(A, w) = A identically (`ask_add_Mn`, ACCOUNT §0.5).
   - The capped count is therefore the Riesz mean w·Σ Λ(n)(1−χ)(y/n − 1)₊ at y = a/w ≈ x on thick partners.
   - There are no floors and no lost fraction.
3. **The split half is computed, not bounded.**
   - log a! = Σ Λ(n)⌊a/n⌋. Its split part Σ Λ(n)χ_d(n)⌊a/n⌋ ≈ −a·L′/L(1,χ_d) is exactly the −L′/L(1,χ_d) inside
     logΩ.
   - That is the proved averaged Chowla–Selberg identity: mean over conjugates of log-period = γ + log(2π/√d) −
     L′/L(1,χ_d) (`mean_log_area`, HEIGHT §2(b), child 3).
4. **Flat covolumes are exact.** The flat sections on U(p,q) have arithmetic degree (p−q)/2·logΩ + q(…), by
   Chowla–Selberg for the CM curve (`FlatDegree`, COVOL §0, VOLUME item 4). The error is ∝ q ≤ m.
5. **The archimedean height is sharp.** The Fock/Cauchy jet bound has no slack in the coefficients of ph(ν) or of logΩ
   (HEIGHT §2(c)). NUMTEST3 found it saturated to within 5.3 in log for the actual kernel.
6. **The slope inequality is nearly an equality, for a rank reason, not a metric one.** *Correction to the brief:* RANK
   says the frame hypothesis carries **no metric content** (Y_u, Y′ are free invertible matrices). It yields only robust
   near-surjectivity of the joint period map.
   - Bost's inequality, applied in mean form through the HN layer cake, is rank-free (RANK).
   - The loss is the HN spread term u·log(1+HH/u) (one-off) plus (η+4√e)·HH ≤ 6b (negligible, `QLD:258-260`
     **[node]** ACCOUNT).
   - The "isometry" content sits in the height clause and in L6, not in the frame.
7. **Four cancellations are syntactic** (Fo, logΩ, log(π/v), m·lg; ACCOUNT §0.3).

### Only one-sided, and why that suffices

- Divisibility: only a **lower** bound, gain ≥ count − slack. The truth exceeds it in rank one (NUMTEST2), which only
  helps.
- Size: only **upper** bounds (htMap ≤ h; covolume lcv ≤ l3).
- L6: a **lower** bound on λ_j, which must nonetheless be sharp to relative x^{−4} (HEIGHT oddity 1).
- Bost: an inequality.
- The conclusion is one-sided: Gm(x) ≤ x^{1/2+O(ε)}, on windows [Y, Y^la] only.
- The windowed Landau theorem needs exactly this. With positive weights, the transform of Gm has a pole at a zero ρ
  with Re ρ > θ. A positive kernel turns a one-sided bound on windows into a bound on the Taylor coefficients, and that
  is incompatible with such a pole (LANDAU §1b, 2b).

### Not exact, and used two-sidedly (honest list)

- `ValuesAtX`/`bdG`: |G_ψ(x)| ≤ x^{1/2+ε} for (·/d), (·/q), (·/qd) and their level twists, at the single point y = x
  (ACCOUNT §3(vi)). This is RH strength for three quadratic characters, supplied by host selection (HOSTS, PAIRGOOD).
  The fluctuation of the split-prime sum is *not* cancelled by the method; it is placed here.
- `ThinScales`: effective PNT at y ≥ X′/3 (CHBALANCE, SERVED).

## 4. The role of ψ

The x-scale part of ASK counts primes with Frobenius ((1,0), h), h ∈ T2 + u0 − t (CHBALANCE §2(a)). Averaging over
u0 ∈ A0 and t ∈ TT weights the class h by the share λ(h) of TT on the coset of −h. The frame fixes
λ = 4/(3o+1) on A0 and 3/(3o+1) off A0 (`Frame.lam`, CHBALANCE). Since A/A0 is cyclic of order o with dual ⟨ψ⟩:

  **λ(h) = (3 + 1_{A0}(h))/(3o+1) = o⁻¹·[1 + (3o+1)⁻¹·Σ_{j≠0} ψ^j(h)].**

The bound on the thick count therefore becomes a bound on

  Gm(y) = Gz(y) + (3o+1)⁻¹·Σ_{ξ∈⟨ψ⟩, ξ≠1} Re g_{ξ*}(y),

a combination of every L(s, ψ^j) with strictly positive weights (LANDAU §1a). Landau then gives zero-freeness for each
of them. With uniform shares only Gz, and hence only ζ, would survive. The unequal 4:3 shares are a positive
perturbation of the uniform measure whose Fourier coefficients on ⟨ψ⟩ are all positive. Why "3" and not some other
c > 0 I did not determine. **[inf]**

## 5. A proof in ten lines

1. Take Taylor coefficients of order a = x·e^{x^ε} of CM theta kernels for ℚ(√−d), on hermitian lattices over a CM
   host E of degree ≈ x². *(HOSTS, THETA, KERNELLAW)*
2. At an inert prime where the hermitian form is split, the Lubin–Tate coordinate makes the kernel integral times
   cancelling Dwork Gaussians. Each coefficient is divisible by p^{Σ_{e odd}(a/p^e−w)₊}, where the caps w come from
   column minors. *(LOCALDIV, GAUSSCLASS, HIGHERRANK, NUMTEST3/4, SIGNAL)*
3. Pass this divisibility through a chain of m ≈ √x theta lifts U(X₀) → … → U(X_m). Every lift is an order-a
   derivative pairing against its own kernel, and the bound holds on every integral form. So the composite is divisible
   by the m-th power of the pattern. *(CHAININD, ORBIT, GLOBALCHAIN)*
4. Rescale the source lattice by that divisibility. The composite with the Bessel period at the top is then an
   integral map N_u → RR^∨. *(SLOPESN, WRITEUP (1)–(4))*
5. Bost's slope inequality, made rank-free by HN layer-cake and near-surjectivity (Theorem S: near-orthogonal Bessel
   periods plus limit multiplicity), gives: mean slope(source) − height ≤ slope(target) + one-off loss.
   *(RANK, THEOREMS, PAIRB, COUNT)*
6. The archimedean height of each lift is ≤ a!·Ω^{−a} by Cauchy estimates in Fock space. The theta scalars are bounded
   below by the Rallis inner product (hook products). *(HEIGHT, L6)*
7. The target is glued from cusp-form lattices on U(k+j−1, m−j). Their covolumes are (p−q)·logΩ per unit weight,
   from flat sections and Chowla–Selberg, with error ∝ q ≤ m. *(COVOL, VOLUME, HS, CONGMOD)*
8. Since Σ_j(p_j−q_j) = m·k, the large logΩ terms cancel. What remains says: m × [inert Riesz count] ≤
   m × [a log a − (1+γ)a + a·L′/L(1,χ_d)] + O(one copy) + O(m²/x copies). Ω = Chowla–Selberg period.
   *(DIV, ACCOUNT, WRITEUP)*
9. Average over tops and Frobenius cosets with 4:3 shares, and bound the three quadratic twists at y = x by host
   selection. This gives Gm(x) ≤ x^{1/2+O(ε)}, with Gm a positive combination over ⟨ψ⟩. *(CHBALANCE, COREGM, SERVED)*
10. The windowed one-sided Landau theorem gives L(s, ψ^j) ≠ 0 for Re s > 1/2. *(LANDAU, REVIEW-ROOT)*

## 6. What remains unclear to me (understanding, not correctness)

1. **Why the weight is exponential.** Partly clear. Every polynomial loss must be ≪ b:
   - Minkowski automorphism denominators, ≈ x^{402} per lift (CHAININD §2);
   - Δ/∇ log-losses, ≈ x^{798} (CHAININD);
   - Stirling, class numbers, log|W| ≤ k log 2;
   - floors and digit sums, ≈ x per copy.

   The ranks depend on log b only polynomially: nWv contains L² with L = x^ε = log b (`RV:21-22` **[Lean]**). That
   makes b = e^{L} the natural closure. I do not see why a large fixed power of x would not do, apart from the
   tree's habit of "eventually in x" absorption. **[inf]**
2. **Why two auxiliary quadratic fields.**
   - d supplies the CM, the supersingularity at inert p, and the L′/L(1,χ_d) inside Ω.
   - **[inf]** The second field supplies a hermitian structure that is definite at ∞ but hyperbolic at served p.
     NUMTEST3's mechanism needs N(C/A) = −1 locally.
   - The sources disagree on the splitting type of served p in ℚ(√−q): NUMTEST4 says "inert in both"; SERVED and
     CHBALANCE say "psC-coordinate 0", i.e. split. I did not resolve this.
3. **Residue degree and positions.** γ_p = Σ_{e odd} p^{−e} is reproduced by couplings between positions s and s+e
   along the Frobenius orbit, with a separate cap at each partner position. I understand the bookkeeping, not why the
   argument needs orbit length n′ > 2 at all, rather than only n′ = 2.
4. **Author's item 14 ("one would stop at 2/3 a priori").** **[inf]** That exponent is what a per-lift cost ∝ m²
   (total m³) gives: relative error 1/m + m²/x, balanced at m = x^{1/3}, so Gm ≲ x^{2/3}. Item 9's "cancellation of order-m terms"
   would then be what reduces the per-lift cost to ∝ m. I could not locate the a-priori version in the Lean.
5. **Item 16 (relative trace formula).** Located: it is Theorem S. The Gram kernel P_u*P_{u′} of the Bessel period
   maps is expanded as `tO u u′` (RANK) by a double unfolding of Poincaré series (PAIRB), and Cauchy–Schwarz bounds a
   projected Poincaré series. "Approximate orthogonality of the columns of the integral structure" is `PairBound`.
6. **Item 19 ("Behrend").** Located, but not traced to the live path. `Formalism/BehrendSets/Statement.lean` has:
   - `BehrendFree K T` (`BS:48`): no non-trivial solution of αx₁+βx₂+γx₃ = 0 with |α|,|β|,|γ| ≤ K;
   - `BehrendBound` and `ThickSet` (`BS:54,58`): density ≥ e^{−C√(log n·log L)};
   - `WindowTwo` (`BS:67`): every Frobenius-orbit window of length 2L meets the thick set thick(n,T,u) at most twice;
   - `OrbitOne` (`BS:72`): short orbits meet it at most once;
   - `TranslateMean` (`BS:78`).

   **[inf]** Behrend is used to choose the thick places T2 ⊂ A ≅ (ℤ/2^{s+2})^×/±1 with density x^{−o(1)}. That is
   compatible with δ = nT2/n ≥ x^{−ε} (`SC:56` **[Lean]**), so the signal unit loses only x^{O(ε)}. At the same time
   no prime's partner positions at small odd distance hit more than two thick (x-scale) caps. A random selection
   (`BadOrbit`, `Select`, same file) is an alternative there. This fits the author's footnote 7 ("intuitively …
   unnecessary").
7. **Why the per-lift interior error must grow with m.** I can say where it grows: the signatures (k+j−1, m−j). I
   cannot say why an m-fold Bessel period needs targets with q up to m. **[inf]** It may be the "up to m
   non-interlacing weights" of GGP (author's item 7). This is the conceptual heart of "why 1/2", and it is the
   piece I would most like an automorphic-forms expert to explain.

## 7. Coverage

Lean read this pass:
- `SC:45-62`; `RV:15-40`; `EW:26-50, 125-140`; `QSB:15-56`; `GB:109-122`;
- `DA:195-212`; `DP2:25-45`; `INP:156,158` (grep); `PRM:46,81-83` (grep);
- `SLN:30-45`; `BS:1-127`.

Nodes read: SUMMARY, PROTOCOL, ACCOUNT, WRITEUP, DIV, CHAININD, HEIGHT, COVOL (§0–2), COREGM (§0–1), CHBALANCE (§0–2a),
LANDAU (§1–2b), and the verdict sections of VOLUME, SLOPE, RANK, PAIRING, ORBIT, CONGMOD, NUMTEST3, NUMTEST4; grep of
PAIRB, HOSTS. The author's note was read in full.

Not done: the origin of Nc; whether `BehrendSets` is on the live path; the 4:3 constant; the a-priori 2/3 computation.
