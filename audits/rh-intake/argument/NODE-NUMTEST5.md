# NODE-NUMTEST5: the capped signal-place law in the regime cap ≈ a/p, across the kink

Paths are relative to `.../scratchpad/art/lean/src`; abbreviations as in NODE-ENGINE2 (`PZF`, `OP`, …).
Scripts (stdlib only, exact integer / exact p-adic arithmetic, `python3 -I`) are in `numtest/`:

| script | output | wall time (4 cores) |
|---|---|---|
| `signal5_lib.py` | engine (reuses `kernel3_lib.th0_jets`, `kernel4_lib.Ring/coeffs`) | — |
| `signal5_validate.py` | `out_signal5_validate.txt` | 9 s |
| `signal5_run2.py` | `out_signal5_run2.txt` (n′ = 2, rank 1 and 2×2 block; **main**) | 102 s |
| `signal5_run4.py 320 100` | `out_signal5_run4.txt` (n′ = 4, e = 1 and e = 3 caps) | 367 s |
| `signal5_back4.py 64` | `out_signal5_back4.txt` (n′ = 4, the distance-1 backward partner) | 282 s |
| `signal5_controls.py` | `out_signal5_controls.txt` | 27 s |

## 0. Verdict

1. **The capped law holds in the cap ≈ a/p regime, including the kink, on real theta-kernel jets.** Over about 250 000 rank-one jets at n′ = 2 (ℤ[ω] at p = 5 with a ≤ 5p³ = 625; ℤ[i] at p = 7 with a ≤ 3p³ = 1029; ℤ[ω] and ℤ[i] at p = 11 with a ≤ 6p²), caps ν ≤ 220, the minimum of v − P1 is −1.00. Here P1 = Σ_{e odd}(a/p^e − ν_e)₊ is the law of ENGINE2, i.e. the Lean's `topTerm` with dTop = ∞ (PZF:166-171). Across the kink |ν − a/p| ≤ 2 the minimum is −0.80 to −0.91. For the 2×2 block with ν minors (det Y)^ν the minimum is −0.83. For the n′ = 4 orbit (16 300 jets, a ≤ 320) it is −1.83, at ν = 0, a = 124 = p³ − 1. The worst points are always at ν = 0 or 1 at Legendre-bad a. There is **no counterexample**, so no independent re-check was triggered. The engines were nevertheless validated by independent formulas (§D).
2. **The kink is real and sits exactly at ν = a/p (cap = number of minors).**
   - Below the kink, each unit of cap costs 1 − γ_p. The fit at n′ = 4 is v = 0.2093a − 0.8045ν (γ − 1 = −0.7917). So the slack over P1 grows like **+γ_p·ν**: the fit is v − P1 = 0.0082a + 0.2012ν − 0.46 (p = 5) and 0.0029a + 0.1416ν − 0.50 (p = 7).
   - **On the kink the slack is ≈ a/(p(p−1))**, which is linear in a and positive.
   - Past the kink P1 is ≈ 0 and v is governed by the backward constraint (item 3).
   - In the block, v is minimal at ν ≈ a/p and not at 2ν ≈ a/p. This confirms cap = #minors in the kink regime.
3. **A sharper model fits every point to O(log a).** That model is the exact dual LP of Lemma RA (forward and backward bipower constraints, no Lean simplifications). Data − LP lies in [−3.8, +7.3], with the lower end drifting like log a (−1.4 at a ≈ 30, −3.8 at a ≈ 600).
4. **The backward charge (ENGINE2 §2.5, errF ≈ γ_p·Wc) is not a pure artefact.** It is never needed for P1 itself. What it really pays for is the **partner row's own γ-gain**, and the data show that this gain is destroyed by a backward partner at distance 1:
   - **n′ = 2:** past the kink, v = 0.040a + 0.047ν, the σ-level 1/(p²−1). If the partner row were credited γν with no backward charge, the bound would fail at 32 682 of 42 010 points, by up to 33.
   - **n′ = 4, position 3** (forward e = 3 partner and distance-1 backward partner): past the e = 3 kink, dv/dn₃ = 0.002–0.03 against γ = 0.208. The forward-only bound fails at 298/390 points, by up to 14. The Lean's accounting (credit γ per unit, minus γ·Wc) holds with min −1.83 and max +4.2, so it is nearly sharp.
   - **n′ = 4, position 1** (backward distance 3): the cost is only ≈ ν(p−1)/(p⁴−1). Past the kink v = 0.0077a + 0.2014ν (LP prediction 0.0096a + 0.2019ν). Here γ·Wc overcharges by a factor ≈ 30.

   So γ·Wc is the right size whenever a position at backward distance 1 carries a cap ≈ b, which is the generic signal configuration, and it is crude only at larger backward distances. **No loss proportional to the cap ever appears against P1.**
5. **The controls have power.** Each of the following gives thousands of violations of P1 (P1 − v up to 18–62): split primes, the anisotropic (non-signal) inert direction, the wrong Gaussian s₂ = 1, non-CM curves (ordinary and supersingular), and scrambled jets. A p-adically small perturbation (s₂ = p) changes nothing.

## A. Statement tested and correspondence with the Lean object

**Claim** (ENGINE2 §1.2, PZF:157-178): at a signal place, with one top s₀ whose top row has degree A = ν₀(s₀) and dTop = ∞, every jet coefficient has

  v_p ≥ topTerm = Σ_{e odd} (A/p^e − cap(s₀+e))₊ − (loss),

where cap(z) = ν_{z,0} = the number of column minors at the partner z. The ledger uses this with cap ≈ b and A/p ≈ b, i.e. at the kink.

**Instance (I), the smallest signal place** (h = 0, n′ = nP = 2; NUMTEST3 §A, SIGNAL §5).
- One matrix entry of thZero is Θ(z₀, z₁) = th0(z₀+z₁)·th0(c(z₀−z₁)) with c c^σ = −1 in ℤ_{p²}.
- th0 is the Lean's co-sigma function. Its jets T_n are exact integers (kernel3_lib, validated there against σ²(℘ − e) to z⁴⁴).
- z₀ is the top position at w, and z₁ is the odd position at w̄ (the thick/thin partner).
- Every odd e lands on position 1, so the cap is ν at e = 1, 3, 5, ….

**Instance (II), n′ = 4** (`kernel4_lib`: E = ℚ(√−3)·ℚ(ζ₁₆)⁺, p = 5).
- Θ = ∏_k th0(Σ_s σ^s(f_k) z_s).
- e ≡ 1 (mod 4) lands on position 1 (cap n₁) and e ≡ 3 on position 3 (cap n₃).
- This host is GIdx-shaped. SIGNAL §5 records that its local object is the one at a signal orbit.

**Jet = the Lean's jet.** Following NUMTEST3/4 (jetC = c_D^{|m|}·∂^mΘ(0), ThDistC.lean:60-61; applyD FGS:256), the jet of a monomial is ∂^m Θ(0) in the log coordinates z, up to p-adic units.
- **Rank one:** top form^a × ν minors is ∂_{z₀}^a ∂_{z₁}^ν. The minors are 1×1, so the cap is ν = `cap` at a non-top.
- **2×2 block** (thZero is a product over entries, LateralTheory.lean:34,157): the operator is (ξ₁X₁₁ + ξ₂X₂₁)^a·det(Y)^ν, i.e. ν height-2 minors at the partner. Its cap is ν and its partner degree is 2ν. The minimum is taken over ξ ∈ {e₁, e₂, two generic units}.

**Not the Lean's object.** There are no frames or labels. HidaSetting's N₀ ≥ 2·log_p a + 3 fails (one or two rows). The forward and backward labels of n′ = 2 fall on the same row.

**Predictions printed:**
- **P1** (the claim, the full tsum over e);
- **LS** = P1 − γ·Wc − |coords|(log_p a + 1) (the Lean's stated form);
- **LP**, the exact dual of Lemma RA. This is max over ε, r ≥ 0 of γ(a+Σn) − aε − Σ n_i r_i, subject to p^d ε + r_i ≥ 1 (forward) and ε + p^{n′−d} r_i ≥ 1 (backward). The bad bipowers are those of `IsBiPower`, s + α ≡ s′ + β;
- **LPf** (the forward constraints only);
- **σ** = (a+ν)/(p²−1).

**Truncation.** None. Every jet is a finite Leibniz sum of exact integer jets T_n, n ≤ a + ν. The only approximation is reduction mod p^K, with K = γ(a+ν)_max + 40. Jets with v ≥ K are flagged and excluded: 209 ℤ[i] zeros from the i-symmetry selection rule, and 2 at n′ = 4 with a ≤ 3. Two precisions give identical valuations (§D).

## B. Results

### B.1 n′ = 2, rank one, ℤ[ω], p = 5 (`out_signal5_run2.txt`)

Region statistics over all a ≤ 625 and ν ≤ 200:

| region | #pts | min(v − P1) | min(v − LS) | v − LP min / max | min(v − P1 − γν) | #(v < P1 + γν − 3) |
|---|---|---|---|---|---|---|
| ν < a/p − 2 | 19 034 | −1.00 | +4.36 | −3.58 / +5.67 | −1.56 | 0 |
| \|ν − a/p\| ≤ 2 (kink) | 1 366 | −0.80 | +3.98 | −3.83 / +3.33 | −1.80 | 0 |
| ν > a/p + 2 | 42 010 | 0.00 | +5.06 | −3.08 / +7.25 | −33.46 | 32 682 |

ℤ[i] at p = 7 (a ≤ 1029, 113 814 pts) gives the same picture: min(v − P1) = −1.00, −0.86 and 0.00 in the three regions. ℤ[ω] and ℤ[i] at p = 11 give −1.00, −0.91 and 0.00.

**Slice A: fixed ν, a across the kink a = pν.** Entries are v / P1 / LP.

| ν | a = 0.5pν | 0.85pν | 0.95pν | pν | 1.05pν | 1.15pν | 1.3pν | 1.6pν |
|---|---|---|---|---|---|---|---|---|
| 16 | 4/0/2.3 | 3/0/3.5 | 3/0/3.8 | 3/0/4.0 | 3/0.8/4.8 | 5/2.4/6.5 | 8/4.8/9.0 | 14/9.6/14.0 |
| 40 | 7/0/5.8 | 9/0/8.7 | 9/0/9.6 | 9/0/10.0 | 11/2.0/12.1 | 15/6.0/16.2 | 22/12.0/22.5 | 34/24.0/35.0 |
| 60 | 10/0/8.7 | 13/0/13.2 | 14/0/14.4 | 14/0/15.0 | 19/3.2/18.3 | 23/9.2/24.6 | 33/18.0/33.8 | 51/36.0/52.5 |

**Slice B: fixed a, ν across ν = a/p.** Entries are v / P1 / LP.

| a | ν = 0 | a/4p | a/2p | 3a/4p | 0.9a/p | a/p | 1.1a/p | 1.25a/p | 1.5a/p |
|---|---|---|---|---|---|---|---|---|---|
| 125 = p³ | 25/25.8/25.8 | 22/18.8/21.1 | 16/12.8/16.3 | 10/6.8/11.6 | 6/2.8/8.4 | 6/0/6.2 | 6/0/6.3 | 7/0/6.5 | 8/0/6.7 |
| 500 = 4p³ | 104/104.2/104.2 | 83/74.8/84.2 | 64/50.0/64.6 | 43/24.8/44.6 | 32/10.0/32.9 | 24/0/25.0 | 26/0/25.4 | 26/0/26.0 | 29/0/27.1 |
| 625 = 5p³ | 129/130.0/130.0 | 106/94.0/105.7 | 81/62.8/80.9 | 58/32.0/56.6 | 40/12.8/41.3 | 31/0/31.2 | 33/0/31.8 | 32/0/32.5 | 36/0/33.8 |

**Slice C: on the kink line ν = a/p (+0/+1).** v − P1 is +1, +2, +4, +6, +12, +18, +24 at a = 25, 50, 100, 125, 250, 375, 500, which is a/(p(p−1)) = a/20. v − LP is −0.25 to −1.0 there.

**Fits (p = 5):**
- region ν ≤ a/p: v − P1 = 0.0082a + 0.2012ν − 0.46. The LP prediction is (γ − 1/p)a + γν = 0.0083a + 0.2083ν;
- region ν ≥ a/p: v = 0.0403a + 0.0470ν − 0.44. The LP (backward) prediction is 0.0417(a + ν); LPf (forward only) would be 0.0083a + 0.2083ν.

**2×2 block, a = 250, p = 5.** min_ξ v falls from 52 at ν = 0 to 22 at ν = 50 = a/p, i.e. 0.58 per minor = 1 − 2γ. It then rises: 22, 24, 26, 28 at ν = 54, 58, 62, 74. min(v − P1(cap = ν)) over all blocks is −0.83 (p = 5), −0.62 (p = 7) and −0.25 (p = 11). With cap = 2ν (the weight reading), P1 would be 0 already at ν = 26, but v is still 36 there.

### B.2 n′ = 4, ℤ[ω], p = 5 (`out_signal5_run4.txt`, `out_signal5_back4.txt`)

| region (n₃ = 0) | #pts | min(v − P1) | v − LP min / max | min(v − P1 − γn₁) |
|---|---|---|---|---|
| n₁ < a/p − 2 | 4 867 | −1.83 at (124, 0) | −3.00 / +4.25 | −2.92 |
| kink | 695 | −0.99 | −3.08 / +2.54 | −3.00 (1 pt < −3) |
| n₁ > a/p + 2 | 10 396 | −0.06 | −2.38 / +4.58 | −2.62 (0 pts < −3) |

**Slice B at n′ = 4.** Entries are n₁: v / P1 / LP.
- a = 160: 0: 33/33.3/33.3; 16: 20/17.3/20.7; 28: 11/5.3/11.2; 32: 7/1.3/8.0; 40: 9/1.3/9.6; 64: 13/1.3/14.5; 80: 18/1.3/17.7.
- a = 320: 0: 66/66.7; 32: 40/34.6/41.3; 57: 19/9.4/21.3; **64: 14/2.6/16.0**; 80: 19/2.6/19.2; 96: 21/2.6/22.5.

At full resolution along a = 320 (n₁ = 0…100), v − P1 rises from −1.4 to +20.4, roughly linearly (+0.2 per unit). v − LP stays in [−2.6, +2.4].

**Both caps (a ≈ 250, 320; n₃ = 0…4 around a/p³ = 2.0, 2.56; n₁ around a/p).** min(v − P1) is −1.87, at n₁ = 0.

**Backward distance 1 (position 3, n₃ = 0…64, a ∈ {125, 200, 320}, n₁ ∈ {0, 4}):**

| prediction | min(v − pred) | #(v < pred − 3) / 390 |
|---|---|---|
| P1 | −1.83 | 0 |
| LP (fwd + bwd) | −2.67 | 0 |
| LGc = γ(a+n₁+n₃) − Lean forward charge − γ·max(n₁, n₃) | −1.83 | 0 |
| LPf (partner rows keep γ, no backward cost) | **−14.17** | **298** |

dv/dn₃ past the e = 3 kink is +0.003 to +0.03. The LP predicts 0.0096, and LPf predicts γ = 0.208.

## C. Controls (`out_signal5_controls.txt`, a ≤ 300, ν ≤ 90)

| configuration | #(v < P1 − 1) | min(v − P1) | slope at ν = 0 |
|---|---|---|---|
| reference: ℤ[ω] p = 5 / ℤ[i] p = 7, served | 2 / 0 (both at exactly −1.00) | −1.00 | 0.2078 / 0.1457 (γ) |
| split p (ℤ[ω] 7, 13; ℤ[i] 5) | 3112, 1639, 4299 | −44, −23, −62 | 0.000 |
| inert, anisotropic N(c) = +1 (not signal) | 3352, 2617 | −50, −38 | 0.049, 0.018 (σ-level) |
| wrong Gaussian s₂ = 1 | 2554, 2149 | −25, −19 | 0.122, 0.081 |
| s₂ = p (p-adically small) | 2 | −1.00 | 0.2073 (unchanged) |
| non-CM, ordinary (p = 5: j = 11664/13; p = 7: j = 6912000/7267) | 4377, 3120 | −62, −44 | 0.00 |
| non-CM, supersingular (p = 5: j = 6912000/7267; p = 7: j = 23704704/25625) | 2602, 2200 | −26, −20 | 0.121, 0.080 |
| scrambled T_n | 3398, 2672 | −50, −38 | 0.048, 0.017 |

Past the kink (ν ≥ a/p) the served kernel and the anisotropic control have the same σ-level values. For example, at a = 250, ν = 50, 62, 75, served gives 12/14/13 and anisotropic gives 15/14/13. So **the entire signal-place gain is the (a/p − ν)₊-shaped piece**: it switches off at the kink, as the Riesz weight requires.

## D. Validation (`out_signal5_validate.txt`)

- **n′ = 2 engine against a direct double Leibniz sum:** 0/248 mismatches (exact ring equality).
- **n′ = 2, two precisions** (p^110 against p^135; p^83 against p^108): 0 of 17 922 valuations differ.
- **New n′ = 4 pair engine against `kernel4_lib`** (a different algorithm, itself checked against brute force in NUMTEST4): 0/630 mismatches.
- **The other factor pairing:** 0/630 mismatches.
- All jets are exact. No power series is truncated, so the wp_valuations-type truncation bug cannot occur.

## E. Limits (what this does not test)

- **Rank and frames.** Rank ≤ 2. There are no frames, no labels and no generic-frame/Cauchy–Binet step. HidaSetting (N₀ ≥ 2 log_p a + 3) is not met. At n′ = 2 the forward and backward labels share one row. Overhang shapes Y₁₁^{ν₁−ν₂}det^{ν₂}, and the α-term accounting, were not redone (see NUMTEST4 T2).
- **Tops and lattices.** There is one top. Several tops, the lattice-wide (every x ∈ lat) statement, adapted global entries, lat_S and chains of lifts are not tested.
- **Sizes.** a ≤ 5p³ (p = 5), 3p³ (p = 7), 0.55p³ (p = 11); caps ≤ 220. The real a ≈ x·b and caps ≈ b are astronomically larger, and the extrapolation is only by the observed linear laws. e ≥ 5 is never active (a/p⁵ < 1). The e = 3 kink was probed only with n₃ ≤ 4 (a/p³ ≤ 2.6) together with the backward test.
- **Host and primes.** The n′ = 4 instance is GIdx-shaped (SIGNAL says it is locally the same object). The Lean host's d ≡ 7 (mod 16) curve is not used, and ℤ[i] is outside the host hypotheses. Only p = 5, 7, 11.
- **Lean code.** The Lean is not executed. The jet = ∂^mΘ(0) reading is taken from NUMTEST3/4.

## F. Bearing on ENGINE2

The e = 1 term (a/p − cap)₊ with cap ≈ a/p, which carries the Riesz weight (x/p − 1)₊, is realised by the actual kernel:
- the bound holds through the kink with O(1) loss;
- the measured gain is P1 + γ·cap + O(a/p³) below the kink, a/(p(p−1)) at the kink, and σ-level beyond it.

ENGINE2 oddity 1 (the backward charge γ_p·Wc as a "crude artefact") is **only half right**:
- the charge is needed, at about its stated size, whenever the backward-distance-1 neighbour of a top carries a cap ≈ b (n′ = 2 data; n′ = 4 position 3);
- it is crude, by ≈ γp³, only for backward distances ≥ 3.

So booking it in E (errF/EatI) is mathematically necessary, not removable bookkeeping. Whether E stays below the main mass is the adm11/GATIE question, which is not numerical.
