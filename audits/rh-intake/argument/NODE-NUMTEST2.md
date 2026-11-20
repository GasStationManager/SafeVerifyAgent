# NODE-NUMTEST2: the capped two-variable regime (Kronecker theta function)

The scripts and raw output are in `numtest/`. They use the Python standard library only and exact arithmetic, and each
runs with `python3 -I`. `numtest/kronecker_all.sh` reruns everything in about 6 minutes on 4 cores; no single job takes
more than 140 s.

| file | what it does |
|---|---|
| `kronecker_lib.py` | the engine (method in §0) |
| `kronecker_validate.py` → `out_kronecker_validate.txt` | brute-force two-variable check, symmetry check, b = 1 slice check, perturbation control |
| `kronecker_run.py CURVE p L m` → `out_kron_CURVE_p<p>.txt` | v_p(N_{a,b}) for a < L and b ≤ m; fits; grid |
| `kronecker_controls.py` → `out_kronecker_controls.txt` | perturbation and scrambled-input controls |

## 0. Object and method

- Θ(z,w) = σ(z+w)/(σ(z)σ(w)) = 1/z + 1/w + Σ_{a≥0,b≥1} C_{a,b} z^{b−1}w^a.
- N_{a,b} := a!(b−1)!·C_{a,b}.

**Method.**
- Write σ(u) = u·e^{φ(u)}. Then φ(u) = −Σ_{n≥2} c_n u^{2n}/(2n(2n−1)), where ℘ = u^{−2} + Σ c_n u^{2n−2}.
- This gives Θ = (1/z + 1/w)·G, where G = exp(φ(z+w) − φ(z) − φ(w)) is a power series.
- Put Φ_m = m!·[u^m]φ. So Φ_{2n} = −(2n−2)!·c_n, which are exactly the Hurwitz-type numbers of NODE-NUMTEST's Addendum.
- Then log G = Σ_{i,k≥1} Φ_{i+k} z^i w^k/(i! k!). The equation ∂_zG = (∂_z log G)·G becomes an integral binomial-convolution recursion for N′_{i,k} = i!k!·[z^i w^k]G.
- Finally, N_{a,b} = N′_{b,a}/b + N′_{b−1,a+1}/(a+1).
- All arithmetic is exact in ℤ/p^K. Denominators prime to p are inverted. Split primes have a few p's in the denominators of the Hurwitz numbers; these are handled by a graded rescaling p^{h·(z-index)}. Every reported valuation is below K, so it is exact.

**Validation** (`out_kronecker_validate.txt`):
- The engine was compared with an independent brute force: σ from Weierstrass's a_{m,n} recursion (`sigma_lib`), and Θ·zw = σ(z+w)/(σ̃(z)σ̃(w)) as a two-variable `Fraction` series of total degree 40. There were 0 mismatches mod p^60 out of 455 coefficients, for each of the 3 curves and for p = 5, 7, 13.
- The symmetry N′_{i,k} = N′_{k,i} holds for i, k ≤ 14.
- The b = 1 slice equals ζ(w) − 1/w, computed from the ℘ recursion.
- Perturbing Φ_12 by +1 gives 64 to 168 mismatches. The symmetry check cannot detect this, as expected.

**Curves.**
- ℤ[i]: g₂ = 4, g₃ = 0. Inert p = 7, 11, 19, 23; split p = 5, 13, 17.
- ℤ[ω]: g₂ = 0, g₃ = 4. Inert p = 5, 11, 17, 23; split p = 7, 13, 19.
- Non-CM curve C from NODE-NUMTEST: g₂ = −10, g₃ = 7/2. Supersingular p = 5, 7, 13; ordinary p = 11, 17, 23.

**Ranges.**
- a < 2000 with b ≤ 32–40 for ℤ[i] at p = 7 and ℤ[ω] at p = 5.
- a < 1600 with b ≤ 30–40 for the other inert primes.
- a < 800 with b ≤ 16 for the split primes.
- a < 700 with b ≤ 16 for C.
- Every b ≤ m is computed at every a, not only the sampled ones.

**Notation.** γ = p/(p²−1) and ρ = 1/(p²−1). The laws compared are:
- **LEAN**(a,b) = Σ_{e odd} (a/p^e − b)₊. This is the capped gain with cap w = b, as in NODE-LOCALDIV/PAIRING.
- **EMP**(a,b) = max(γ(a+b) − b, ρ(a+b)).
- **LB**(a,b) = v_p(a!) + v_p((b−1)!) − ρ(a+b) − min(b, (a+b)/(p+1)).

## 1. The empirical law (supersingular primes)

**(i) Slope in a at fixed b is γ_p, for every b.**
- ℤ[i], p = 7: dv/da = 0.1459, 0.1457, 0.1457, 0.1456, 0.1455 at b = 1, 3, 8, 16, 32, against γ = 0.1458.
- ℤ[ω], p = 5: 0.2083 to 0.2088 at b = 1 to 40, against γ = 0.2083.
- The same holds at every inert or supersingular pair: the fitted α agrees with γ_p to within 0.0004.

**(ii) Dependence on b: one linear cap at level e = 1, with slope 1 − γ_p and no further caps.**

A least-squares fit of v = αa + βb + c over the region b ≤ a/(2p), a ≥ 100:

| curve, p | α | γ_p | β | γ_p − 1 | LEAN's slope in b |
|---|---|---|---|---|---|
| ℤ[i], 7 | 0.1458 | 0.1458 | −0.8575 | −0.8542 | −1 or −2 (−2 where p³ ≤ a/b) |
| ℤ[ω], 5 | 0.2084 | 0.2083 | −0.7933 | −0.7917 | −1, −2, or −3 |
| ℤ[i], 11 / ℤ[ω], 11 | 0.0921 | 0.0917 | −0.9115 | −0.9083 | |
| ℤ[i], 19 | 0.0528 | 0.0528 | −0.9494 | −0.9472 | |
| ℤ[ω], 17 | 0.0591 | 0.0590 | −0.9442 | −0.9410 | |
| ℤ[i], 23 / ℤ[ω], 23 | 0.0434 | 0.0436 | −0.958 | −0.956 | |
| C (non-CM), 5 / 7 / 13 | 0.2086 / 0.1460 / 0.0773 | | −0.7945 / −0.8617 / −0.9303 | −0.792 / −0.854 / −0.923 | |

So v ≈ γ_p(a+b) − b = v_p(a!) + v_p((b−1)!) − (a+b)/(p²−1) − b.
- The cap acts on the e = 1 term only, with constant c = 1, on a/p (not on a/p^{e±1}).
- The **b-side factorial does contribute** symmetrically: +γ_p·b.
- At e ≥ 3 there is **no cap**. Take ℤ[ω], p = 5, a = 1500, where a/p³ = 12. Going from b = 1 to b = 12, v falls from 312 to 302, which is 0.9 per unit of b. LEAN falls from 309.8 to 288.0, which is 2 per unit of b.
- The law flattens to the σ-like level ρ(a+b) = (a+b)/(p²−1) once b ≥ a/p. Over all points with b ≥ a/p + 2, v − ρ(a+b) lies in [−2.75, 5.5] with mean −0.7 to 0.

**(iii) Balanced corner, a ≈ b.**
- v ≈ (a+b)/(p²−1) − O(1), the same as σ.
- For example, ℤ[ω] at p = 5 with a = b = 36 gives v = 2, against (a+b)/(p²−1) = 3.0. Values are 0 to 3 at p = 7 and 0 at p ≥ 11 (where (a+b)/(p²−1) < 1).

**Fit quality and the lower bound.** Over all a ≥ 50 at all 11 supersingular pairs:
- v − EMP ∈ [−3.25, +6.1], and the mean is between −0.2 and +0.35. The error does not grow with a.
- **v ≥ LB held at every computed (a,b), with 0 violations.** The minimum slack is 0.05 to 0.25.
- **v ≥ LEAN − 1.59 held everywhere.** Not one point has v < LEAN − 3.

**Grids.** Each entry is v / LEAN / EMP.

ℤ[i], p = 7 (inert):

| a \ b | 1 | 2 | 3 | 5 | 8 | 12 | 16 | 20 | 30 |
|---|---|---|---|---|---|---|---|---|---|
| 100 | 14/13.1/13.6 | 14/12.0/12.6 | 12/10.9/11.6 | 11/9.1/10.2 | 8/6.3/7.8 | 5/2.3/4.3 | 2/0.0/2.4 | 2/0.0/2.5 | 5/0.0/2.7 |
| 300 | 43/41.7/42.8 | 42/40.6/41.8 | 42/39.4/40.8 | 40/37.7/39.3 | 37/34.9/36.9 | 34/30.9/33.5 | 30/26.9/30.1 | 27/22.9/26.7 | 17/12.6/17.8 |
| 600 | 87/85.3/86.5 | 86/83.4/85.5 | 84/82.3/84.5 | 84/80.6/83.1 | 81/77.7/80.7 | 79/73.7/77.2 | 74/69.7/73.8 | 71/65.7/70.4 | 61/55.4/61.6 |
| 1000 | 145/143.6/144.8 | 144/141.5/143.8 | 143/139.4/142.8 | 141/137.7/141.4 | 139/134.9/139.0 | 135/130.9/135.6 | 132/126.9/132.2 | 128/122.9/128.8 | 119/112.6/119.9 |
| 1500 | 218/216.5/217.8 | 217/214.4/216.8 | 217/212.2/215.8 | 215/209.1/214.3 | 212/206.3/211.9 | 209/202.3/208.5 | 205/198.3/205.1 | 202/194.3/201.7 | 193/184.0/192.8 |

ℤ[ω], p = 5 (inert):

| a \ b | 1 | 2 | 3 | 5 | 8 | 12 | 16 | 20 | 30 | 40 |
|---|---|---|---|---|---|---|---|---|---|---|
| 100 | 18/18.0/19.0 | 19/18.0/19.2 | 19/16.8/18.2 | 15/14.4/16.2 | 15/12.0/14.5 | 10/7.2/10.5 | 6/3.6/7.8 | 3/0.0/5.0 | 4/0.0/5.2 | 4/0.0/5.8 |
| 300 | 62/60.2/61.5 | 60/58.0/60.5 | 59/56.4/59.5 | 58/54.0/57.5 | 55/51.6/55.8 | 52/48.0/53.0 | 49/43.2/49.0 | 47/39.6/46.2 | 39/30.0/38.8 | 29/19.2/30.0 |
| 600 | 121/122.6/124.0 | 123/120.4/123.0 | 122/118.2/122.0 | 119/114.0/120.0 | 118/111.6/118.2 | 115/108.0/115.5 | 111/103.2/111.5 | 107/99.6/108.8 | 100/90.0/101.2 | 92/79.2/92.5 |
| 1000 | 207/205.0/206.5 | 207/204.0/206.8 | 205/201.8/205.8 | 204/197.4/203.8 | 201/192.0/202.0 | 198/187.2/198.0 | 196/183.6/195.2 | 193/180.0/192.5 | 184/169.2/183.8 | 177/159.6/176.2 |
| 1500 | 312/309.8/311.5 | 310/307.6/310.5 | 309/305.4/309.5 | 308/301.0/307.5 | 305/295.6/305.8 | 302/288.0/303.0 | 299/283.2/299.0 | 297/279.6/296.2 | 289/270.0/288.8 | 279/259.2/280.0 |

Read along a row: observed − LEAN grows like γb + Σ_{e≥3 odd} min(a/p^e, b). At a = 1500, b = 40 for ℤ[ω], p = 5 this
is 279 − 259.2 ≈ 20, made up of γb = 8.3 plus a/p³ ≈ 12. Observed − EMP stays within a few units.

## 2. Split and ordinary primes (iv)

There is no gain for any (a,b):
- At every split pair, and at the ordinary primes of C, v ∈ {−3, …, 3}.
- The fitted α is 0.0000 and the fitted β is ≈ 0.01–0.03.
- For example, ℤ[i] at p = 5 has v = 0 at (600, b) for all b ≥ 2, against LEAN = 120.
- In the region b ≥ a/p both laws are ≈ 0 anyway.

## 3. Controls (`out_kronecker_controls.txt`)

These use ℤ[i], p = 7, a < 600, b ≤ 16.

**Input perturbations.**
- Φ_200 += 1 drives v − EMP down to −82.5 and gives 1540/2200 violations of LB.
- Φ_400 += 1 gives 790/2200 violations; Φ_400 += 7^20 also gives 790.
- Φ_12 += 1 has no visible effect. That is expected, because v(Φ_12) is only ≈ 1.

**Scrambled input (important).**
- Replace every Φ_n by p^{v_p(Φ_n)}·(random p-adic unit). This keeps every one-variable valuation and destroys all arithmetic relations between the Hurwitz numbers.
- The two-variable law survives unchanged: v − EMP ∈ [−2.33, 3.25], with 0 violations of LB.
- For ℤ[ω] at p = 5 with b up to 40, plateau included, 1650 of 1964 valuations are identical to the unscrambled ones.
- So, in this rank-one case, **the capped two-variable law is a formal consequence of the one-variable ℘ law** (v(Φ_n) ≈ γ_p·n − O(1)) together with the integral binomial-convolution structure of exp. It is not independent evidence about cancellation in theta functions.

## 4. Verdict on what the proof uses (3)

**Lower bound: holds.**
- When the conjugate order is b ≤ w, v_p(N_{a,b}) ≥ Σ_{e odd}(a/p^e − w)₊ − 1.6 at every computed point, for both CM curves and for the non-CM supersingular controls.
- The defect is a digit-sum-size constant. It does not grow with a up to 2000 and is far inside the Lean's loss term de ≥ NN·lgp + lgp².
- The cap constant is c = 1 on a/p, as the proof uses. **No different constant appears, so the prime-count weights are not changed.**

**The truth is MORE divisible than LEAN, and the discrepancy is structural, not just O(log).**
- True − LEAN ≈ γ_p·b + Σ_{e≥3 odd} min(a/p^e, b) for b < a/p.
- For b ≥ a/p, true ≈ (a+b)/(p²−1), where LEAN gives 0.

The proof's #factors = Σ_e min(a/p^e, w) counts one Gaussian factor per odd level e. The data show #factors = min(b, (a+b)/(p+1)) in total: a single cap, not one per level. The Lean form v ≥ v(a!) + v((b−1)!) − ρ(a+b) − #factors holds with this count and no violations.

**Effect on a two-sided accounting.** This is a hand estimate, not tested. Summed over inert p with weight 2 log p, and in units of w:
- The γ_p·b term contributes O(log x).
- The uncapped e ≥ 3 terms contribute O(x^{1/3}).
- The plateau beyond p > x = a/w contributes O(1).
- All three are below x^{1/2}, so this rank-one discrepancy would not upset an ACCOUNT/PAIRING match at the x^{1/2+ε} scale. But "delivered = count" is false at the level of exact shape: the true local gain is not the ASK summand.

## 5. What is and is not tested

**Tested:** rank one, one (a,b) pair, m = 1. The object is the classical Kronecker theta function of two CM lattices, plus a non-CM control. These are its Taylor numbers ∂_w^a ∂_z^{b−1}, at inert, split and ordinary primes p ≤ 23. The tested range is a < 2000 and b ≤ 40.

**Not tested:**
- the Lean's actual kernel, which has harmonic polynomials, column minors, higher-rank Θ, and the Hecke normalisation p^{ArV};
- the higher-rank minors and the injective pairing of tops;
- the chain of m lifts, the colength τ, and anything global or archimedean.

The scrambled-input control shows that this rank-one test reduces to the already-confirmed one-variable ℘ law. It therefore adds shape information (the cap acts at e = 1 only, with constant 1), not independent evidence about the higher-rank kernel.
