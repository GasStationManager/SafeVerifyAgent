# NODE-NUMTEST3: the actual Lean theta kernel in its smallest instance, both sides

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations: `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`,
`LAT2` = `Formalism/LocalToGlobal/KernelLattices/LateralTheory.lean`, `SC` = `Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/SemiChar.lean`,
`DR` = `Formalism/LocalToGlobal/InertKernelTheory/DefsRep.lean`, `SZ` = `Formalism/LocalToGlobal/GroupLattices/PendingLemmas/SubstZOfXCoordZA.lean`,
`FDC` = `Formalism/LocalToGlobal/PairingIndexBounds/OrthogonalChartLevels/FdOfCharts.lean`, `SPM` = `Formalism/LocalToGlobal/GroupLattices/LevelGatherings/SecPsiMulPow.lean`.

Scripts (stdlib only, exact integer / exact p-adic arithmetic, `python3 -I`), in `numtest/`:

| script | output | time |
|---|---|---|
| `kernel3_lib.py` | engine | — |
| `kernel3_validate.py` | `out_kernel3_validate.txt` | 1 s |
| `kernel3_run.py 1000` | `out_kernel3_run.txt` | 97 s |
| `kernel3_shape.py 800` | `out_kernel3_shape.txt` | 41 s |
| `kernel3_global.py 400` | `out_kernel3_global.txt` | 0.3 s |
| `kernel3_controls.py` | `out_kernel3_controls.txt` | 11 s |

## 0. Verdict (short)

1. **The claim holds for the actual kernel.** Take the smallest instance, at an inert prime p that the host
   serves. A jet of order a in the even-position variable and order w in the odd-position variable has
   v_p ≈ γ_p(a+w) − w. It is never below the Lean's Σ_{e odd}(a/p^e − w)₊ by more than 0.98. At w = 0 it satisfies
   the Gaussian-free law v_p ≥ v_p(a!) − (a−1)/(p²−1) **exactly**: the minimum slack is 1/(p²−1), with no log defect.
   This holds for a ≤ 1000, for ℤ[i] at p = 7, 11, 19 and ℤ[ω] at p = 5, 11, 17. It is **not** the a/(p²−1) behaviour.
2. **The brief's model of the variables is right; its inference is wrong.** The odd-position variable is an
   independent holomorphic variable of one entire theta function: the other CM-type coordinate z_{τ·z}. But the
   kernel is not a function of one combined variable. In orthonormal coordinates it is **th0(u₁)·th0(u₂)**, with
   u = M*z and M unitary. The even-position direction is isotropic for the p-adic hermitian form:
   A·A^σ + C·C^σ = 0, while |A|² + |C|² = 1 at ∞. So Θ(z₀, 0) = th0(Az₀)·th0(Cz₀) is Gaussian-free at p. The two
   Gaussians cancel because N(C/A) = −1. This cancellation is arithmetic: scrambling the jets destroys it (§E).
3. **The tension dissolves.** The same numbers saturate the archimedean Fock bound:
   log|J|² = log(a!w!) + (a+w)·log(π/Area) − D, with |D| ≤ 5.3 up to a = 400. They also carry the full p-adic gain
   at served primes. This is possible because the hermitian form is definite at ∞ and split (hyperbolic) at served
   p. The full gain occurs only at **served** inert primes, Frob_p = c·g. At inert primes with Frob_p = c (p inert
   in K, split in F), the same function gives only a/(p²−1). At split primes it gives 0.
4. **Product formula, one global entry (E = ℚ(i, √−13)).** At a = 400, log N(J) = 2987.3. The served primes
   contribute 1010.8, against 986.8 predicted by the LT law. The other contributions are: non-served inert 111.7,
   split 0, 2-part 415.9, 13-part 513.0, and primes > a: 935.9. No contradiction arises, and none is expected: the
   served primes have density 1/4. The served share is 0.32–0.34 and rises slowly towards ½.

## A. Specification (the Lean says, with my inferences marked)

**Host, CM type, positions.**
- E is Galois CM of degree 4·ord over ℚ, and F is its real subfield of degree 2·ord (`ConjEMemHostFIff.lean:183-184`).
  Tau ≃ Psi = {σ : σ√−d = √−d} = Gal(E/K) (`TiedRec.lean:35`, `ConjEMemHostFIff.lean:209`). So **the CM type is lifted
  from K**, and |Tau| = 2·ord ≥ 2.
- Positions are `posG ⟨v,s⟩ = orbRep_v · z^s` with z = zPsi = (c0,h)·cc (`SPM:64-66, 148-151`), and
  n′ = orderOf z (`HostPlacesWeight.lean:40-47`).
- `HidaSetting` requires n′ even, σ^{n′} = 1 and residue field p^{n′} (`UnramifiedQuadraticSetting.lean:12-31`).
- *I infer* that (c0,h) is the Frobenius class, so z = Frob_p·c ∈ Gal(E/K).
- **E = K is impossible**, since |Tau| = 1 and n′ would be odd. The smallest host is E = ℚ(√−d, √−q), with
  Tau = {1, g} and z = g, so Frob_p = c·g. In that case p is inert in K and in F = ℚ(√dq), and split in ℚ(√−q); n′ = 2,
  with one place.
- Ranks are at least N(0) = k = 6 and N(1) = 20 (`Params.lean:6-22`: m = 2, k = 6, t = 13).

**Which complex variable is position s.**
- `FrecG` = linSub(c·subBG)(p^{expG}·serP(kerTh)) (`FDC:42-60`), with subBG block-diagonal in Tau (`FDC:31-40`, `if x.1 = y.1`).
- `thFOf` re-indexes Tau by positions through `pos` (`ConditionIffAdditiveMaps.lean:41-51`).
- `zOfX`/`thA` send even positions to `Sum.inl` (x_e) and odd positions to `Sum.inr` (y_e) (`SZ:76-88`, mirrored by
  `coordZ` FGS:181-196).
- So **Z_s is, after a frame change, the global variable z_{pos(s)}**: the CM-type coordinate τ = orbRep·z^s of
  ℂ^{Tau×N′×N}. It is neither a conjugate-embedding coordinate of the same vector nor a formal dual variable.
- `OrthInt` (DR:26-31) writes the kernel as Θ_orth∘hypLin(f,f′), with X_i = Σ_e f_{e,i}x_e + f′_{e,i}y_e
  (`FirstKernelGeneratorOfOrthogonal.lean:46-49`). Here f, f′ are isotropic and dual (`IsHypPair.lean:23-27`), and the
  X_i are coordinates in a global orthonormal basis b with entries in E (`thOrth` DR:46-50; `FrameHyp` DR:66-77).

**The function.**
- Θ = thC(…, area⁻¹, aaOf cc, eNat χ) (`KerTh.lean:26-30`), with eNat = chiFac·thMoved (LAT2:177). thMoved is two
  coset averages of thZero = tensPow(thMM) = ∏_{i,j} thMM(z_{·,i,j}) (LAT2:34-35, 157).
- thMM lies in the 1-dimensional theta space of H = area⁻¹·I on Λ⊗AA0, with tens4 thMM = κ·kernel4 (LAT2:19-29, 119, 155).
- kernel4 is a product of th0 = opU(ω₀/2)(σ*)/opU(ω₀/2)(σ*)(0) (SC:27-34), where σ* = σ·e^{−s₂z²/2} and s₂ is
  given by SC:20-21.
- So th0(z) = σ*(z+t)e^{−πzt̄/A}/σ*(t), with (log th0)″ = −℘(z+t) − s₂. It is even and entire, with th0(0) = 1, and
  th0² = σ²(℘ − e_t). This identity is verified exactly through z⁴⁴ (`out_kernel3_validate.txt`). For ℤ[i] and ℤ[ω]
  we have s₂ = 0 (homogeneity), and **all jets T_n = th0^{(n)}(0) are integers**.
- **Smallest instance, one matrix entry** (standard lattice; AA0 has an orthonormal O_K-basis a₁, a₂ for tr_{E/K}(xȳ)):

    Θ(z₀, z₁) = th0(u₁)·th0(u₂),  u = M*z,  M = (τ(a_k))_{τ∈Tau,k} unitary.

  Explicitly, take K = ℚ(i), β = √−13, a₁ = (1+i)/2, a₂ = (1+5i)β/26. Then Θ = th0(ā₁(z₀+z₁))·th0(−γ̄β(z₀−z₁)).
  After unit rescaling, at p this is **Θ = th0(z₀+z₁)·th0(c(z₀−z₁)) with c c^σ = −1** when Frob_p = c·g (served), and
  c c^σ = +1 when Frob_p = c.
- Isotropy is a one-line check: A A^σ + C C^σ = c[(MM*)₀₁] = 0 exactly when σ = c·g.
- **Jet entry.** jetC = c_D^{|m|}·∂^mΘ(0) (`ThDistC.lean:60-61`), and applyD = Σ n!·coeff (FGS:256). With one entry
  and no frames:

    J(a,w) = ∂_{z₀}^a ∂_{z₁}^w Θ(0) = Σ_k S(a,w,k)·T_k·T_{n−k}·c^{n−k},  where S = [x^k y^{n−k}](x+y)^a(x−y)^w.

**What the model loses.**
- The full N′×N = 6×20 matrix with frames and minors. Θ_std is a product over entries, and the minor and cap
  combinatorics were checked in NODE-HIGHERRANK.
- Non-standard AA0 and the Iop/StdStep prime-to-p translates.
- chiFac, c_D, ltC, the ω-basis and the Δ = 1 rescaling, all of which are units at p.
- The Lean's size constraints on d and q (`qd_big`). ℤ[i] (d = 1) is outside the host hypotheses; ℤ[ω] (d = 3) is
  inside them.

## B. Prediction

- **w = 0.** Clause 2 (`ExtensionLocalCondition`, FGS:162-170) gives Θ(z₀,0) = exp(−Ph(z₀,0))·U with Ph(x,0) ≃ 0. So
  Θ(z₀,0) is integral in the LT parameter, and **v_p(J(a,0)) ≥ v_p(a!) − (a−1)/(p²−1)** (exp_LT denominators) ≈ γ_p·a.
  Call this LT.
- **w > 0.** EntryStar/TermBound (SE:61,176) with one top at s = 0 and cap w at s = 1 give
  **v ≥ γ_p a − Σ_{e odd} min(a/p^e, w) − deLoss = Σ_{e odd}(a/p^e − w)₊ − deLoss**. Call this LEAN.
- **The alternative hypothesis** (one combined variable, σ-type): v ≈ (a+w)/(p²−1). Call this SIG.

## C. Results

**Slopes of v_p(J(a,w)) in a, for a ∈ (500, 1000]** (`out_kernel3_run.txt` SUMMARY):

| curve, p | configuration | w = 0 | w = 5 | w = 20 | γ_p | 1/(p²−1) | min_a [v − LT], w = 0 |
|---|---|---|---|---|---|---|---|
| ℤ[i], 7 | served (two c's) | 0.1459, 0.1458 | 0.1457 | 0.1458 | 0.1458 | 0.0208 | +0.02 |
| ℤ[i], 7 | Frob = c (anisotropic) | 0.0204 | 0.0204 | 0.0204 | | | −123.2 |
| ℤ[i], 11 | served | 0.0917 | 0.0919 | 0.0915 | 0.0917 | 0.0083 | +0.01 |
| ℤ[i], 19 | served | 0.0527 | 0.0528 | 0.0528 | 0.0528 | 0.0028 | +0.00 |
| ℤ[ω], 5 | served | 0.2086 | 0.2082 | 0.2072 | 0.2083 | 0.0417 | +0.04 |
| ℤ[ω], 5 | anisotropic | 0.0398 | 0.0397 | 0.0398 | | | −164.5 |
| ℤ[ω], 11 / 17 | served | 0.0916 / 0.0592 | | | 0.0917 / 0.0590 | | +0.01 / +0.00 |
| ℤ[i] 5, 13; ℤ[ω] 7, 13 | split in K | 0.0000 ± 0.0001 | | | | | — |

Each entry below is v / LT / LEAN / SIG.

ℤ[i], p = 7, served:

| a \ w | 0 | 2 | 5 | 12 | 20 | 30 |
|---|---|---|---|---|---|---|
| 300 | 43/41.8/42.9/6.2 | 42/41.7/40.9/6.3 | 39/42.6/38.0/6.4 | 33/42.5/30.9/6.5 | 26/43.4/22.9/6.7 | 18/45.1/12.9/6.9 |
| 1000 | 145/143.2/145.8/20.8 | 143/143.1/141.8/20.9 | 140/143.1/137.7/20.9 | 134/143.9/130.9/21.1 | 128/144.8/122.9/21.2 | 119/146.6/112.9/21.5 |

The anisotropic row at a = 1000 is 20 or 21 at every w.

ℤ[ω], p = 5, served, a = 1000:

| w = 0 | 2 | 5 | 12 | 20 | 30 |
|---|---|---|---|---|---|
| 212/207.4/208.0/41.7 | 206/207.3/204.0/41.8 | 203/205.2/197.8/41.8 | 198/208.9/188.0/42.2 | 192/210.5/180.0/42.5 | 184/213.1/170.0/42.9 |

The anisotropic row is 40–43.

**Shape in w** (`out_kernel3_shape.txt`, a ≤ 800, w ≤ 40, all six served pairs):
- min(v − LEAN) ∈ [−0.98, −0.91];
- v − EMP ∈ [−2.5, +5.7], where EMP = max(γ(a+w) − w, (a+w)/(p²−1));
- a fit v = αa + βw + c gives α = γ_p ± 0.0003 and β = γ_p − 1 ± 0.005.

This is the same law NUMTEST2 found for the Kronecker function. The cap bites once, at e = 1, and LEAN is a valid
lower bound that is not tight in w.

**Both sides of the same numbers** (`out_kernel3_global.txt`; E = ℚ(i, √−13), ℤ[i], e_t = 1, Area = 6.8752). D is
the Fock gap. v₇, v₁₁ and v₁₉ are at served primes; v₂₃ is at an anisotropic prime, with (a+w)/(p²−1) in brackets.

| a | w | log\|J\|² | Fock: log(a!w!) + n log(π/A) | D | v₇ / LT | v₁₁ / LT | v₁₉ / LT | v₂₃ |
|---|---|---|---|---|---|---|---|---|
| 100 | 0 | 286.0 | 285.4 | −0.6 | 14/13.9 | 9/8.2 | 5/4.7 | 0 (0.2) |
| 200 | 2 | 706.8 | 705.7 | −1.1 | 28/27.8 | 16/17.3 | 8/9.4 | 0 (0.4) |
| 400 | 0 | 1684.0 | 1687.2 | 3.2 | 59/57.7 | 36/35.7 | 21/20.9 | 1 (0.8) |
| 400 | 2 | 1688.7 | 1686.4 | −2.3 | 56/57.6 | 34/35.7 | 19/20.9 | 1 (0.8) |

Over all computed (a,w), the minimum of D is −2.32. The Fock bound is saturated to O(1) and holds within the Lean's
polynomial slack. **For the same number**, v_p is within 1–2 of the full LT/γ_p law at every served p.

**Product formula** (log N_{K/ℚ} of the integral normalisation J*; natural logs):

| a | log N | served p (actual / LT prediction) | anisotropic inert | split | 2 | 13 | primes > a+50 |
|---|---|---|---|---|---|---|---|
| 100 | 611.9 | 197.0 / 189.4 | 28.6 | 11.7 | 104.0 | 128.2 | 142.3 |
| 400 | 2987.3 | 1010.8 / 986.8 | 111.7 | 0.0 | 415.9 | 513.0 | 935.9 |

## D. Verdict

For the actual kernel in its smallest instance, the proof's claim is what one sees: **v_p ≈ γ_p·a − (cap terms)**
at the inert primes the host serves. The cap is ≈ (1 − γ_p) per unit of w, and the bound holds against LEAN everywhere
with defect below 1. It is not a/(p²−1)-type.

There is no discrepancy between the Lean object and the description, apart from one point of the description. The
odd-position variable is an independent CM-type coordinate, the Gaussian couples z₀^p with z₁, and the archimedean
jets are Fock-size. All of that is right. What the description missed is that the kernel's restriction to z₁ = 0 is
a product th0(Az)·th0(Cz) whose two Gaussians cancel p-adically, because N(C/A) = −1.

The γ_p gain is therefore a property of an entire Gaussian-growth function. It holds only at primes where the
hermitian form is split, which here means Frob_p = c·g, not at all inert primes. That restriction is in the Lean
through `HidaSetting` (n′ = orderOf(Frob·c) even). The global consequences of the restriction (the served density)
are not tested here.

## E. Controls

- **Split primes:** slope 0.0000.
- **Non-served inert primes** (anisotropic c, the same function): slope 1/(p²−1).
- **Exact second methods:**
  - th0² = σ²(℘ − e) to z⁴⁴;
  - brute-force bivariate expansion: 0/720 mismatches;
  - the global Gaussian-integer entries against the local engine: 59/59 identical v_p at p = 7, 11 and 19.
- **Perturbations** (`out_kernel3_controls.txt`, p = 7):
  - T₂₀ += 1: v(J(400,0)) drops from 58 to 13; 380 of 802 valuations change.
  - Wrong s₂ = 1 or 3: slope 0.085.
  - s₂ = p: no change, since it is p-adically small.
  - **Scrambled jets** (T_n → p^{v(T_n)}·random unit): slope 0.0185, the σ-level. This is unlike NUMTEST2, where the
    law survived scrambling, so the γ_p gain here is a genuine arithmetic cancellation, not a formal consequence of
    one-variable valuations.
- **Robustness:** N(c) = −1 + p^k (k = 1, 2, 3) keeps the full gain. Only isotropy mod p matters.
- **σ(z)σ(cz) instead of th0** gives the same result: γ_p with N(c) = −1, against 0.0184 for N(c) = +1 and 0.0183 for
  σ alone.
- **Exact zeros:** for c = 1 + √2 (a global unit of norm −1) some entries vanish identically. They are flagged and
  excluded.
