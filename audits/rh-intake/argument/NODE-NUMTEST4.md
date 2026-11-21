# NODE-NUMTEST4: long Frobenius orbits (n′ = 4) and column minors, on the Lean's own kernel

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations as in NODE-NUMTEST3, plus
`FOS` = `Formalism/FrobeniusOrbits/Statement.lean`, `DH` = `Formalism/LocalRingCardinality/DataHost.lean`,
`UQS` = `Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean`, `MMO` = `Formalism/LocalToGlobal/InertKernelTheory/DefsMMOnb.lean`.

Scripts are stdlib only and use exact integer / exact p-adic arithmetic. Run them with `python3 -I`. They live in
`numtest/`:

| script | output | time |
|---|---|---|
| `kernel4_lib.py` | engine (reuses `kernel3_lib.th0_jets`) | — |
| `kernel4_validate.py` | `out_kernel4_validate.txt` | 62 s |
| `kernel4_run.py Zw 5 640 Zw_p5 12` | `out_kernel4_run_Zw_p5.txt` (**decisive**) | 97 s |
| `kernel4_run.py` (other primes) | `out_kernel4_run_{Zw_p11,Zi_p11,Zi_p19,Zi_p7_nprime2,Zw_p23_nprime2,Zw_p17_aniso,Zw_p13_splitK,Zi_p5_splitK}.txt` | 2–25 s each |
| `kernel4_block.py 320` | `out_kernel4_block.txt` (T2) | 25 s |
| `kernel4_controls.py` | `out_kernel4_controls.txt` | 24 s |

## 0. Verdict

1. **(T1) Confirmed: the caps at different odd e are charged against different positions' weights, and they are nearly tight.**
   In the n′ = 4 instance (p = 5, top weight a ≤ 640, so a/p³ ≤ 5.1), a jet of order a at position 0 behaves as follows
   in the other positions:
   - **Position 1 (the e = 1 partner):** each unit costs ≈ 1 − γ_p, i.e. v ≈ γ_p(a+n₁) − n₁, the NUMTEST3 law. The cap
     a/p = 128 is never reached.
   - **Position 3 (the e = 3 partner):** the loss grows by about one unit per unit of n₃ and then **saturates at
     ≈ a/p³**. At a = 640 the loss is 4–5 for every n₃ from 5 to 12, against a/p³ = 5.12.
   - **Position 2 (even distance):** costs nothing. There is even a small γ-type gain.
   - **Mixed weights:** the losses add, as Σ_e min(a/p^e, w_{t+e}) says.

   The "one shared budget" alternative min(a/p, n₁+n₃) is excluded. At (n₁, n₃) = (0, 12), a = 576, it predicts a loss of
   12; the observed loss is 4.5–5.5. At p = 11 (a/p³ < 0.4), position 3 costs nothing up to n₃ = 10, while position 1
   costs ≈ 0.9 per unit, on both curves.
2. **No point lies below the Lean bound.** Over all ≈ 890 nonzero served-prime jets computed (six runs), the minimum of
   v − (γ_p·a − Σ_{e odd} min(a/p^e, w_{t+e})) is −1.54, at p = 5. That is the digit-sum slack between v_p(a!) and γ_p·a,
   which has the same size as NUMTEST3's −0.98. The bound is tight to within about 1–2 on every axis.
3. **(T2) Confirmed, with a specification note.** Take a 2×2 block of entries (the Lean kernel is ∏_{i,j} over
   entries, LateralTheory.lean:34,157):
   - **det(Y)^m at the partner:** the loss is m, the **number of minors**, not the weight 2m. The bound with cap m holds
     to within −0.67 and is tight.
   - **Y₁₁^{ν₁−ν₂}·det(Y)^{ν₂}, overhang row ⊥ top direction:** the loss is ν₂. That is the Lean's top cap
     (`cap`, FGS:36-38), and it is tight.
   - **Specification note.** If the overhang row is coupled (same row as the top direction, or both generic), the loss is
     ν₁. The cap ν₂ would then be exceeded by 2.3–3.7. Per NODE-HIGHERRANK §1.2 the Lean charges that coupling separately,
     as α-terms (dSet/alEven), and this test does not check that accounting.
4. **Controls are as expected:**
   - split-in-K primes: slope 0.0000;
   - non-served primes (Frob|_F = 1, n′ = 1): slope 0.0029 against 1/(p²−1) = 0.0035;
   - scrambled jets: the gain is lost (0.043, the σ-level), as in NUMTEST3;
   - broken isotropy: the gain is lost;
   - isotropy mod p only: the full gain is kept;
   - brute force: 0/800 mismatches;
   - other pairing of factors: 20/20 identical;
   - two precisions: 60/60 identical.

## A. Specification

**The Lean's host shape.**
- GG = G0 × HGrp e, with HGrp e = (ℤ/2^{e+2})^×/⟨−1⟩ (FOS:24-29), and the frame has A ↠ HGrp e (NODE-HOSTS).
- **c0 = (−1,−1)** and cc = (c0, 1) (FOS:35-37).
- The orbit generator is zPsi h = ((1,1), h) = (c0, h)·cc (SPM:148-151), with orderOf(zPsi h) = orderOf h (SPM:153-158).
- Positions are posG⟨v,s⟩ = orbRep_v·z^s (SPM:66).
- So **the served Frobenius class is (c0, h)**: p is inert in ℚ(√−d) and in ℚ(√−q), and n′ is the order of the A-component h.
- HidaSetting requires p ≥ 5, n′ even and residue field p^{n′} (UQS:12-31).

**Instance.**
- Take e = 2: A = HGrp 2 ≅ ℤ/4 = Gal(F/ℚ), with F = ℚ(ζ₁₆)⁺ = ℚ(η), η⁴ − 4η² + 2 = 0 and O_F = ℤ[η].
- E = K·F, with K = ℚ(√−3) (curve ℂ/ℤ[ω]) or ℚ(i).
- Then Tau = Gal(E/K) ≅ Gal(F/ℚ), and z acts as Frob_p|_F. This gives n′ = 4 for p ≡ ±3, ±5 (mod 16), n′ = 2 for
  p ≡ ±7, and no service for p ≡ ±1.
- **Deviations from the Lean host.**
  - The √−q factor is dropped. See (f) below: at one place it only multiplies the kernel by a second copy.
  - d ∈ {1, 3} instead of d ≡ 7 (mod 16) (FOS:13).
  - The 2-adic condition on 𝔟 (DH:65) is unmet. All of these are prime-to-p, so they are absorbed by StdStep.

**Lattice.**
- The Lean uses AA0 = 𝔟⁻¹ with D_{E/K} = 𝔟·𝔟̄ (DH:65,153), which is self-dual for tr_{E/K}(x ȳ).
- I use O_E = O_K ⊗ O_F with tr_{E/K}(λ x ȳ), λ = ε/η¹¹ ≫ 0 and λO_F = D_F⁻¹. This lattice is unimodular and
  positive-definite of rank 4, so it is I₄.
- Enumeration finds the orthonormal basis f = (−1,−1,1,1), (−1,0,1,−1), (−1,0,2,0), (−1,1,2,−1) in ℤ[η]. Its Gram matrix
  is I₄ exactly, which gives the p-unit orthonormal basis that OneCopyOrth / UnitVec require (MMO:9-30).

**Kernel.**
- Following NUMTEST3 §A (thZero = tensPow thMM, thMM = ∏_k th0(u_k), u = M*z):

    **Θ(z₀,…,z₃) = ∏_{k=1}^4 th0(Σ_s σ^s(f_k)·z_s)**,

  with σ = Frob_p on F. The unit rescaling by σ^s(λ) is dropped, since it does not change v_p.
- **Yes, the kernel for this host is a product of elliptic th0's of linear forms.** The coefficients lie in
  ℤ_p[η] = ℤ_{p⁴}.
- There is an exact global check: Σ_k f_k σ^j(f_k) = δ_{j0}/λ (`out_kernel4_validate.txt`). So the position-0 direction
  is isotropic against every other position. The p-adic distinction between positions 1, 2 and 3 comes only from Frobenius.
- **The Lean host with √−q (inferred).** z fixes √−q, so a place's four positions are (1_q, σ^s), and
  Θ_v = Ψ(ā₁z)·Ψ(ā₂z), with Ψ as above and ā_k ∈ ℤ_{p²}.
- **NUMTEST3 correction.** Its smallest instance used z = the √−q flip with A trivial. That is not of zPsi's form, since
  z never moves √−q. Its d = 3 is also outside HostHyp. Its order-2 isotropy mechanism is the same, so its numbers stand,
  but the host identification does not.

**Jet.** J(a; n₁,n₂,n₃) = ∂_{z₀}^a ∂_{z₁}^{n₁} ∂_{z₂}^{n₂} ∂_{z₃}^{n₃} Θ(0), exact mod p^K. The algorithm is:
- binomial pair products of factors (1,2) and (3,4);
- low-index splits;
- one final convolution at sampled a.

## B. Predictions

- **LEAN:** v ≥ γ_p·a − Σ_{e odd} min(a/p^e, w_{e mod 4}), with w₁ = n₁ and w₃ = n₃. Position 2 is never charged.
  This uses hh = Σ u_s S_s^p S_{s+1} (FGS:200-208) and the per-(t,e) charge.
- **SHARED:** v ≈ γ_p(a+|n|) − min(a/p, n₁+n₃).

## C. Results

**p = 5, ℤ[ω], served, n′ = 4.** The full tables are in `out_kernel4_run_Zw_p5.txt`.
- **Slope in a at n = 0:** 0.2094 (γ₅ = 0.2083).
- **Fit to the Gaussian-free law:** v − [v_p(a!) − (a−1)/24] ∈ [+0.6, +1.6].

Entries below are v(a,0) − v(a,n):

| a (a/p³) | n₁ = 4 / 8 / 12 | n₃ = 2 / 4 / 6 / 8 / 10 / 12 | n₂ = 4 / 8 |
|---|---|---|---|
| 320 (2.56) | 4 / 6 / 10 | 2 / 2 / 1 / 2 / 1 / 2 | −1 / −2 |
| 448 (3.58) | 4 / 7 / 10 | 2 / 3 / 2 / 3 / 2 / 2 | −2 / −2 |
| 512 (4.10) | 3 / 6 / 10 | 2 / 4 / 3 / 3 / 3 / 3 | 0 / −1 |
| 640 (5.12) | 1 / 6 / 8 | 0 / 2 / 4 / 4 / 4 / 4 | 0 / −1 |

- **Mixed weights:** at a = 576, (4,0,8) has loss 8.5 above the γ-law (Lean 8.61); (3,0,9) has 8.5 (Lean 7.61);
  (2,0,8) has 5.1 (Lean 6.61). SHARED predicts 10–12 for these.
- **p = 11, ℤ[ω] and ℤ[i], a ≤ 500:**
  - position 3: v(a,n₃) − v(a,0) ∈ {−1, 0, +1, +2, +3} for all n₃ ≤ 10;
  - position 1: loss of n₁ − 1 at n₁ = 10.
- **p = 19, ℤ[i]:** same pattern.
- **ℤ[i] exact zeros.** About half of the ℤ[i] jets vanish identically (a selection rule from the i-symmetry). They are
  flagged and excluded.

**Controls.**
- **n′ = 2 (p = 7 for ℤ[i], p = 23 for ℤ[ω]):** z₁ is the partner at the same place and costs 1 per unit. z₂ and z₃
  belong to the other place and cost 0.26 for n = 6. This is NUMTEST3's rank-one law.
- **Control slopes:** split-in-K (ℤ[ω] at 13, ℤ[i] at 5) 0.0000; non-served (ℤ[ω] at 17, a ≤ 600) 0.0029.

**T2** (`out_kernel4_block.txt`, p = 5, a = 320; entries give the value of v − (γa − Σ_e min(a/p^e, cap))):

| operator at the e = 1 partner | cap = #minors | cap = weight |
|---|---|---|
| det(Y)², det⁴, det⁶ (generic ξ) | −0.67, −0.67, +1.33 | +1.33, +3.33, +7.33 |
| Y₁₁^{ν₁−ν₂}det^{ν₂}, ξ = e₂, ν = (4,2), (6,2), (6,4), (8,4) | −0.67 for all, cap ν₂ | +3.3 … +7.3 |
| the same with ξ = e₁, or generic ξ and ζ | −1.7 … −3.7 with cap ν₂; −0.67 … +0.33 with cap ν₁ | |

- **Odd ν₂ or m:** these vanish identically by parity.
- **At the e = 3 partner:** everything saturates at a/p³ = 2.56, with values between −0.67 and +0.89.
- **(f) two copies (Ψ(z)Ψ(η²z)):** the valuations equal the one-copy valuations in 26 of 28 cases. In the other two
  (s = 3, a = 160) the two-copy value is lower by 1 and by 2. Both are still within 0.05 of the Lean bound.

## D. What is not tested

- The Lean host's actual d ≡ 7 (mod 16) curve, whose s₂ ≠ 0 needs non-rational jets.
- A non-standard AA0.
- The α-term (dSet/alEven) accounting at top partners.
- Chains of lifts.
- n′ ≥ 8. For e = 5 and 7 the targets wrap to positions 1 and 3, which is charged separately. That charge is valid; at
  these sizes a/p⁵ < 1 and it is negligible.
