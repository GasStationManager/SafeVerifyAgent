# NODE-NUMTEST: numerical test of the inert-prime divisibility of D^a σ(0)

Scripts and raw output: `numtest/` (Python standard library only, exact integer and `Fraction` arithmetic; run each
with `python3 -I <file>.py`; each finishes in under 90 s).

| file | what it does | time |
|---|---|---|
| `sigma_lib.py` | Weierstrass recursion, integer D^aσ(0), fast v_p | — |
| `verify_recursion.py` | checks the recursion against ℘'² = 4℘³ − g₂℘ − g₃ for generic rational g₂, g₃, and against the first coefficients; shows the brief's version of the recursion is wrong; includes a perturbation control | <1 s |
| `verify_highorder.py [M=800]` | second, independent algorithm (℘-coefficient recursion, then exp of a double integral, all in `Fraction`); agrees with the recursion for **every a ≤ 800** on curves A, B, C | 9 s |
| `run_valuations.py [N=6000]` | parts 2 and 4 → `out_valuations_N6000.txt` | 84 s |
| `product_formula.py [N=6000]` | part 3 → `out_product_N6000.txt` | 8 s |
| `controls.py` | code controls → `out_controls.txt` | 1 s |
| `formal_param.py [M=241]` | same test in the integral formal-group parameter t = −2x/y → `out_formal_param_M241.txt` | 27 s |

## 0. Setup and a correction to the brief

σ(z) = Σ a_{m,n}(g₂/2)^m(2g₃)^n z^{4m+6n+1}/(4m+6n+1)!, so **D^aσ(0) = Σ_{4m+6n+1=a} a_{m,n} h₂^m h₃^n**, where
h₂ = g₂/2 and h₃ = 2g₃. This is an integer whenever h₂ and h₃ are integers. The correct recursion is

  a_{m,n} = 3(m+1)a_{m+1,n−1} + (16/3)(n+1)a_**{m−2,n+1}** − (1/3)(2m+3n−1)(4m+6n−1)a_{m−1,n}.

The brief has a_{m−1,n+1} in the middle term. That form breaks homogeneity, and it gives a non-integer
a_{3,0} = −385/3. The corrected recursion reproduces z − g₂z⁵/240 − g₃z⁷/840 − g₂²z⁹/161280 and satisfies the ℘
differential equation through z³⁴. A second, independent algorithm gives the same D^aσ(0) for every a ≤ 800.

Curves (Δ is a p-unit for every p ≥ 5 tested, so no rescaling is needed; s₂ = 0 for A and B by symmetry, so σ* = σ):

- **A**: y² = 4x³ − 4x, CM by ℤ[i], Δ = 64. Inert p ≡ 3 (4).
- **B**: y² = 4x³ − 4, CM by ℤ[ω], Δ = −432. Inert p ≡ 2 (3).
- **C** (non-CM): g₂ = −10, g₃ = 7/2, Δ = −5323/4. Supersingular among the tested primes: 5, 7, 13.
- **C2** (non-CM): g₂ = −4, g₃ = 7/2, Δ = −1579/4. Supersingular: 7, 13, 23.

For C and C2, a_p was found by brute-force point counts. Neither curve has bad reduction at any tested prime.

N = 6000. The nonzero terms are a ≡ 1 mod 4 (1500 of them) for A, a ≡ 1 mod 6 (1000) for B, and every odd a ≥ 5
(2999) for C and C2.

## 1. Main result: the gain is a/(p²−1), not p·a/(p²−1)

v := v_p(D^aσ(0)) = v_p(a!·c_a). The claim is v ≥ γ_p·a − O(log a), with γ_p = p/(p²−1) = Σ_{e odd}p^{−e}. The
Lean-style form is v ≥ v_p(a!) − a/(p²−1) − de.

**Observed, at every supersingular pair (curve, p) and for all a ≤ 6000 without exception:**

  Σ_{k≥1} ⌊a/p^{2k}⌋ ≤ v_p(D^aσ(0)) ≤ Σ_{k≥1} ⌊a/p^{2k}⌋ + 7 (the excess is ≤ 2 for most pairs),

so v ≈ a/(p²−1) = Σ_{e **even**} a/p^e. In terms of the Taylor coefficients, v_p(c_a) ≈ −Σ_{e odd}⌊a/p^e⌋ ≈ −γ_p·a.
The radius of convergence is v(z) > p/(p²−1), not v(z) > 1/(p²−1). The claim swaps the odd and even halves, and so
overstates the gain by a factor of exactly p. The shortfall against the claim is ≈ a/(p+1), which is linear in a.

| curve | p | type | min[v − ⌊a/p²⌋−⌊a/p⁴⌋−…], a≤6000 | max of same | LSQ slope dv/da (a>3000) | 1/(p²−1) | claimed γ_p | min[v − γ_p a], a≤6000 | v − (v_p(a!) − a/(p²−1)) at the last a (≈6000) |
|---|---|---|---|---|---|---|---|---|---|
| A | 7 | inert | 0 | 2 | 0.0210 | 0.0208 | 0.1458 | −750.6 | −748.1 |
| A | 11 | inert | 0 | 2 | 0.0084 | 0.0083 | 0.0917 | −500.4 | −498.0 |
| A | 19 | inert | 0 | 1 | 0.0028 | 0.0028 | 0.0528 | −299.7 | −297.3 |
| A | 23 | inert | 0 | 2 | 0.0019 | 0.0019 | 0.0436 | −249.4 | −246.6 |
| A | 31 | inert | 0 | 1 | 0.0011 | 0.0010 | 0.0323 | −187.7 | −186.8 |
| B | 5 | inert | 0 | 3 | 0.0414 | 0.0417 | 0.2083 | −999.0 | −995.2 |
| B | 11 | inert | 0 | 2 | 0.0084 | 0.0083 | 0.0917 | −500.0 | −498.0 |
| B | 17 | inert | 0 | 2 | 0.0035 | 0.0035 | 0.0590 | −333.9 | −332.2 |
| B | 23 | inert | 0 | 2 | 0.0019 | 0.0019 | 0.0436 | −249.4 | −246.6 |
| B | 29 | inert | 0 | 1 | 0.0012 | 0.0012 | 0.0345 | −199.1 | −197.9 |
| C | 5, 7, 13 | supersingular | 0 | 7 | 0.0414, 0.0210, 0.0059 | 0.0417, 0.0208, 0.0060 | | −999.8, −750.6, −428.2 | |
| C2 | 7, 13, 23 | supersingular | 0 | 6, 4, 3 | 0.0210, 0.0059, 0.0019 | | | −750.6, −428.2, −249.4 | |

The minimum of v − γ_p a over a ≤ A decreases linearly in A. For A, p = 7 it is −13.1, −31.3, −62.3, −124.8, −250.7,
−500.3, −750.6 at A = 100, 250, 500, 1000, 2000, 4000, 6000, against −log₇A ≈ −2.4 to −4.5. **No constant C makes
the claim's bound with −C·log_p a hold.** The liminf of v/a over a ∈ (3000, 6000] is 0.0204 for (A, 7), 0.0080 for
(A, 11) and 0.0410 for (B, 5), against claimed values of 0.146, 0.092 and 0.208.

Explicit rows: (a: v_p(D^aσ(0)) | claimed γ_p a | a/(p²−1) | v_p(a!))

- A, p = 7: (1501: 32 | 218.9 | 31.3 | 248); (3001: 62 | 437.6 | 62.5 | 498); (5997: 124 | 874.6 | 124.9 | 997)
- A, p = 11: (1501: 12 | 137.6 | 12.5 | 149); (5997: 50 | 549.7 | 50.0 | 598)
- B, p = 5: (1501: 62 | 312.7 | 62.5 | 374); (5995: 250 | 1249.0 | 249.8 | 1495)
- C, p = 13 (non-CM, supersingular): (5999: 36 | 464.2 | 35.7 | 498)

**Lean loss term.** NODE-LOCALDIV gives de = O(NN²·log_p(al, lsz)), polynomial in the number of factors and
logarithmic in a. Here, with one variable and m = 1, the observed shortfall against v_p(a!) − a/(p²−1) is ≈ a/(p+1).
At p = 7, a = 5997 that is 748. It is linear in a, so no logarithmic de can absorb it.

**Split / ordinary primes (in z):** there is no gain. For CM curves A and B, v = 0 for every nonzero a at every split
prime, except (B, 31), where 200 of 1000 terms have v ∈ {1, 2}. The slope is 0. For the non-CM curves at ordinary
primes, v ∈ {0, …, 5} sporadically and the slope is 0. So the **dichotomy holds qualitatively**: a gain of size
≈ a/(p²−1) at supersingular primes and none at ordinary ones. It is the same at CM and non-CM supersingular primes;
the valuation sequences at p = 7 for A, C and C2 have identical statistics. **The constant does not hold**: the gain
is 1/(p²−1), not p/(p²−1).

## 2. No Gaussian correction can rescue the constant (for A and B)

Suppose σ*(z) = σ(z)e^{−κz²/2} had the claimed radius v(z) > 1/(p²−1) for some κ, in any extension of ℚ_p.
Because σ(iz) = iσ(z), we get σ*(z)σ*(iz)/i = σ(z)². So σ² would be analytic on that disc, with zeros of even order.
Then σ would be analytic there too. That contradicts the observed radius p/(p²−1). The argument for ℤ[ω] uses
σ*(z)σ*(ωz)σ*(ω²z) in the same way. **The failure therefore does not depend on which s₂ the Lean uses at p.** (This is
a hand argument resting on the numerically observed radius; it is not a proof.)

## 3. Product formula for one coefficient (`out_product_N6000.txt`)

Natural logarithms. "Claimed" is Σ_{p inert ≤ a} log p·Σ_{e odd} a/p^e.

| curve, a | log\|D^aσ(0)\| | ½ log a! | inert primes, actual Σ v_p log p | inert, claimed | inert, Σ_{e even}⌊a/p^e⌋log p | split primes | p = 2, 3 | cofactor (primes > a) |
|---|---|---|---|---|---|---|---|---|
| A, 1501 | 4152.9 | 4740.9 | 147.3 | 4106.1 | 108.6 | 5.4 | 466.5 | 3533.7 |
| A, 5997 | 20740.8 | 23088.1 | **578.2** | **20558.0** | 492.5 | 3.6 | 1863.0 | 18296.0 |
| B, 5995 | 21622.4 | 23079.4 | **746.4** | **21043.1** | 666.5 | 11.5 | 4414.4 | 16450.1 |

- If the claim held, the inert primes would account for 99% of log|D^aσ(0)|. That near-saturation is what the slope
  argument exploits.
- In fact they account for 2.8% (A) and 3.5% (B). This matches the even-e part, which is O(a), not of order a log a.
- About 88% (A) and 76% (B) of the size comes from primes larger than a.
- The order-2 growth is confirmed. (log|D^aσ(0)| − ½ log a!)/a settles to −0.391 for A and −0.243 for B, so
  |D^aσ(0)| ≈ (a!)^{1/2}·C^a with C = 0.68 and 0.78.

## 4. Same test in the formal-group parameter t (`formal_param.py`, curve A, a ≤ 241)

The integral parameter is t = −2x/y, and v_p is taken of a!·[t^a]σ(z(t)).

- At inert p = 7 and 11 the valuations equal the z-valuations at every sampled a. Example: a = 241, p = 7 gives 4,
  against the claim's 33.0.
- At split p = 5 and 13, σ(z(t)) is **p-integral in t**. Example: p = 5, a = 241 gives v = 59 ≥ v_p(241!) = 58.
  This is consistent with Katz's result that the p-adic E₂ at an ordinary CM point equals E₂* = 0, which makes σ the
  Mazur–Tate σ.
- exp_F(z) has v(T_k) ≥ −(k−1)/(p²−1) exactly, at p = 7 and 11. This is the height-2 radius.
- So the obstruction is not t = exp_F(z). σ is **not** "integral in t" at inert p. The Dwork/Gaussian-type factor
  costs ≈ a/(p+1).

## 5. Controls

- `vp()` agrees with naive division on 2000 random cases.
- Perturbing a_{3,0} by 3^{N//3} changes the p-adic valuations at many a: 26 to 221 per (curve, p). It also breaks the
  exact law v ≥ Σ⌊a/p^{2k}⌋ at supersingular primes: 17 violations for (A, 11) and 8 for (C, 13), against 0 before.
- A +1 perturbation makes the recursion non-integral.
- Perturbing a_{2,1} by +1 breaks the ℘ differential equation from order 14 on.

## 6. What this does and does not test

**Tests:**

- The one-variable, m = 1, no-cap, no-Hecke case of the local claim, i.e. the consequence of the "kernel law" that
  v_p(D^aσ*(0)) ≥ v_p(a!) − a/(p²−1) − O(log a) at an inert p.
- This covers the bare CM σ-function with Δ a p-unit and s₂ = 0. By §2 it covers any Gaussian correction.

**Does not test:**

- The theta lifts, the higher-rank Θ, the caps, the Hecke normalisation p^{ArV}, the rescalings ϖ in the Lean's
  `EntryHyp`/`excessGain`, the global slope inequality, or anything archimedean beyond §3.
- If the Lean's actual inequality applies to a differently normalised object (for instance one carrying an extra
  p-power such as the kernel factor p^{Σvm Δlen} flagged in NODE-LOCALDIV §4.4), this experiment does not refute that
  statement as such.
- It does show that **the classical claim, as written in SUMMARY §1 and the brief, is false**. The true inert gain is
  ≈ a/(p²−1) = Σ_{e even} a/p^e. Summed over inert primes this is O(a), not the inert half of Chebyshev's log a!.

## Addendum (orchestrator): the brief tested the wrong function; ℘ confirms γ_p exactly

The experiment above tests σ, because the brief said to. That was the brief's error, not
the Lean's claim. NODE-LOCALDIV's bound is

  v_p(P(∂)f) ≥ v_p(a!) − a/(p²−1) − #(Gaussian hh-factors) − O(log a),

and the count of Gaussian factors is capped only by the weight available in the
*conjugate* (odd-position, dual) variables. For σ in one variable nothing caps them:
up to ≈ γ_p·a factors occur, the bound degenerates to ≈ 0, and the true value a/(p²−1)
found above is consistent with it. The γ_p gain is claimed only for the Gaussian-free
part, i.e. for functions integral in the formal-group parameter. The simplest such
function is ℘ (x = ℘(z) is a coordinate of the integral model), so the right
one-variable test of the engine is the Laurent coefficients of ℘, i.e. Hurwitz-type
numbers (2n−2)!·c_n ∼ (2n−1)!·G_{2n}.

`numtest/wp_valuations.py` (exact `Fraction` arithmetic, recursion checked against
℘′² = 4℘³ − g₂℘ − g₃; output `out_wp_valuations.txt`), a = 2n−2 up to 1798:

| curve | p | type | v/a at a = 1798 | γ_p | min_a [v − γ_p·a] |
|---|---|---|---|---|---|
| ℤ[i] | 7 | inert | 0.1457 | 0.1458 | −2.7 |
| ℤ[i] | 11 | inert | 0.0907 | 0.0917 | −2.8 |
| ℤ[i] | 19 | inert | 0.0517 | 0.0528 | −1.9 |
| ℤ[i] | 23 | inert | 0.0434 | 0.0436 | −1.9 |
| ℤ[ω] | 5 | inert | 0.2063 | 0.2083 | −3.6 |
| ℤ[ω] | 11 | inert | 0.0907 | 0.0917 | −2.8 |
| ℤ[ω] | 17 | inert | 0.0590 | 0.0590 | −1.9 |
| ℤ[i] | 5, 13, 17 | split | −0.002 … 0.000 | — | min v = −4, −2, −2 |
| ℤ[ω] | 7, 13, 19 | split | −0.001 | — | min v = −3, −2, −2 |
| non-CM g₂ = g₃ = 4 | 5 … 23 (all ordinary: a_p = −2, 4, −2, −5, 4, 2, −1) | ordinary | −0.002 … 0.000 | — | min v = −4 … −2 |

So for the Gaussian-free function the inert-prime divisibility holds with the constant
γ_p = p/(p²−1) to three decimals and an O(log a) defect, and there is no gain at split
or ordinary primes. This is the classical supersingular divisibility of Hurwitz numbers
(Katz). Together with the σ result (gain only a/(p²−1) when every Gaussian factor is
present) the two extreme cases of the Lean's formula are both confirmed numerically:
#factors = 0 gives γ_p·a, #factors maximal gives ≈ a/(p²−1) ≥ 0.

What this corrects: SUMMARY §1 said "an a-th derivative [of σ*] is divisible by ≈ γ_p·a".
That is false for σ* itself. The correct statement is that derivatives of the theta
kernel *divided by its σ\* factors*, taken with a harmonic polynomial whose degree in the
conjugate variables is at most w, are divisible by γ_p·a − Σ_{e odd} min(a/p^e, w).

What remains untested numerically: the capped, two-variable case (the Kronecker theta
function / Eisenstein–Kronecker numbers e*_{a,b} with b ≤ w ≪ a), which is the case the
proof actually uses, and everything about chains of lifts.
