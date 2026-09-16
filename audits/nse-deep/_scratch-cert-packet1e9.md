# packet-1e9 — widest closed kernel numeral at the Euler `Packet*` big-literal sites

Worker: `packet-1e9` (READ-ONLY). Repo: `openai/NavierStokesAndEuler` @ f9e8bc5, clone
`/home/gsm/.openclaw/workspace/repos/NSE` (not modified). **UNBUILT**: no Mathlib, no `lake build` in the
clone, so *nothing here is machine-checked*. Every width below is a source-level estimate from the
`linarith`/`nlinarith`/`norm_num` mechanism; every `file:line` was re-opened and quoted verbatim.

## Mechanism used (as given in the brief, refined by what the sites actually contain)

* `linarith` parses each hypothesis / negated goal into a linear form over **atoms** with rational
  coefficients (`Linarith/Parsing.lean`), `cancelDenoms` clears each comparison's denominators, a simplex
  oracle returns nonneg rational multipliers `c_i = p_i/q_i`, and `Verification.lean` emits the scaled sum,
  closing the final closed comparison with `norm_num`.
* Sharpening that matters for these sites: the widest emitted numeral is **not** `lcm x global-max-numerator`.
  It is `max_i ( p_i * L / q_i ) * maxnum(h_i)` with `L = lcm(q_i)`, i.e. **per-hypothesis**: a hypothesis
  with a huge coefficient that is used with a tiny multiplier stays cheap. This is what keeps the `1e15`
  hypotheses below 64 bits here (see F, E).
* `nlinarith` adds pairwise products (incl. squares) *before* the oracle. A product's numerals are the
  **product** of the two factors' numerals. But an unused product (multiplier 0) is dropped by
  `Verification` and costs the kernel nothing. So the degree-2 column below is a *worst case*, only realised
  if the oracle actually puts a nonzero multiplier on a product.
* Atoms are *not* delta-unfolded at reducible transparency: `D.error` (`def error`,
  `Euler/PacketGeometryData.lean:90: def error (D : PhysicalGeometryData α) : ℝ := 16*(D.ε*D.Θ*(4*D.G)^2+D.d)`)
  stays one atom after the `change ... at hs` steps, so `1000000*K*D.error*D.Θ^40` contributes `1e6*1e9`,
  not `1e6*1e9*256`. If it *were* unfolded the coefficient would be `2.56e17` (58 bits) — see NOTE-2.
* 64-bit line: `2^64 = 1.845e19`.

## Line verification (all 15 assigned sites re-opened; literals confirmed)

| site | verbatim line | enclosing decl (line) |
|---|---|---|
| PacketPhysicalFamily.lean:66 | `          \|scaledVelocity m v (w ξ) t₀ a ε τ 0+Z₁ τ\| ≤ 400000000*e*Θ^29*(1+lam)*F τ) ∧` | `theorem physical_family_amplification_and_size` (:19) |
| PacketPhysicalFamily.lean:90 | same text (inside `have hcommon`) | same (:19), `have hcommon (ξ : α)` at :81 |
| PacketPhysicalFamily.lean:118 | `  have hK : 1 ≤ neighborStabilityConstant := (by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge` | same (:19) |
| PacketNeighborControlled.lean:154 | `def neighborStabilityConstant : ℝ := 1000000000*exp 6` | itself (:154) |
| PacketNeighborControlled.lean:156 | `theorem neighborStabilityConstant_ge : 1000000000 ≤ neighborStabilityConstant := by` | itself (:156) |
| PacketNeighborControlled.lean:213 | `  let δ := 400000000*e*Θ^29` | `theorem controlled_neighbor_stage_references_within` (:161) |
| PacketGeometryGuards.lean:76 | `    ((by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge) D.error_nonneg` | `theorem ray_error_small` (:74) |
| PacketGeometryGuards.lean:83 | `  have hK : 0 ≤ neighborStabilityConstant := (by norm_num : (0:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge` | `theorem relative_error_small` (:82) |
| PacketGeometryGuards.lean:93 | `    (by norm_num : (0:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge` | `theorem scalar_error_small` (:90) |
| PacketGeometryAssembly.lean:35 | `    \|D.velocity ξ τ 1-Z τ\|+\|D.velocity ξ τ 0+Z₁ τ\| ≤ 400000000*D.error*D.Θ^29*(1+D.lam)*F τ` | field `state_error` (:34) of `structure PhysicalGeometryConclusion` (:21) — **no decl of its own** |
| PacketGeometryAssembly.lean:70 | `    (by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge` | `theorem PhysicalGeometryData.exists_geometry` (:67) |
| PacketGeometryAssembly.lean:126 | `    D.target_from_sigma D.slope_nonneg (show 0 ≤ 400000000*D.error*D.Θ^29 by positivity [D.error_nonneg, D.Theta_pos])` | same (:67) |
| PacketPhysicalNeighbor.lean:64 | `      (∀ t ∈ Icc 0 T, \|V t-Z t\|+\|U t+Z₁ t\| ≤ 400000000*e*Θ^29*(1+lam)*F t) ∧` | `theorem physical_neighbor_stage_references` (:19) |
| PacketWithinStage.lean:54 | `        160000000 * e * Θ ^ 29 * (1 + lam) * F t) ∧` | `theorem controlled_stage_references_within` (:21) |
| PacketPhysicalStage.lean:59 | `      (∀ t ∈ Icc 0 T, \|V t-Z t\|+\|U t+Z₁ t\| ≤ 160000000*e*Θ^29*(1+lam)*F t) ∧` | `theorem physical_stage_references` (:20) |

Two brief-level corrections (evidence, not manufactured disagreement):
* **`PacketWithinStage.lean:54` and `PacketPhysicalStage.lean:59` carry `160000000` (1.6e8), not 4e8.**
* The brief's site list contains **no** site where 4e8 is actually *computed*. The one real 4e8 arithmetic
  step in the Packet family is `Euler/PacketNeighborControlled.lean:139`
  (`  have hcoef : 20*e*Θ^8+800*(200000*e)*Θ^29*(1+lam+e) ≤ 400000000*e*Θ^29*(1+lam) := by`, closed by
  `nlinarith only [...]` at :144-145). I audited it anyway as row **G**; it is the row the brief was looking for.

## Findings table

`deg1` = widest closed numeral on the degree-1 (linarith) route; `deg2` = worst case if an nlinarith product
of the two widest hypotheses is used with a nonzero multiplier. Bits = ceil(log2).

| # | site | (c) closing tactic | (d) literal x atom? | (e) denominators in context | (f) deg1 | deg1 bits | (f) deg2 worst | deg2 bits | (g) |
|---|---|---|---|---|---|---|---|---|---|
| S1 | PacketPhysicalFamily.lean:66 | none — theorem **statement** conclusion; produced at :107-108 by `refine ⟨..., (fun ξ => (hcommon ξ).2.1), ...⟩` | literal x atoms (`e*Θ^29*(1+lam)*F τ`) | n/a | **0** (never normalised) | 0 | 0 | 0 | OK |
| S2 | PacketPhysicalFamily.lean:90 | none — `have hcommon` **statement**; proved at :103 `simpa only [(hFeq τ hτ.1).1, (hZeq τ hτ.1).1, (hZeq τ hτ.1).2] using herr τ hτ` (rewrite only) | literal x atoms | n/a | **0** | 0 | 0 | 0 | OK |
| S3 | PacketGeometryAssembly.lean:35 | none — `structure` field type | literal x atoms | n/a | **0** | 0 | 0 | 0 | OK |
| S4 | PacketPhysicalNeighbor.lean:64 | none — **statement**; discharged at :154 `· exact controlled_neighbor_stage_references_within hσ hσsmall hΘ hT0 hT he hε.le herr.1 hlam hsmall` (unification, no arith) | literal x atoms | n/a | **0** | 0 | 0 | 0 | OK |
| S5 | PacketWithinStage.lean:54 | none — **statement** (1.6e8); discharged at :105 `simpa only [hUeq ht, hVeq ht] using herr t ht` | literal x atoms | n/a | **0** | 0 | 0 | 0 | OK |
| S6 | PacketPhysicalStage.lean:59 | none — **statement** (1.6e8); discharged at :145 `exact controlled_stage_references_within ...` | literal x atoms | n/a | **0** | 0 | 0 | 0 | OK |
| S7 | PacketNeighborControlled.lean:154 | none — `def` body. Costs only where `unfold`ed (:158, :220, :229, :232, Guards:98) | `1000000000*exp 6`, literal x atom `exp 6` | none | 1e9 where unfolded | 30 | n/a | — | NOTE |
| A | PacketNeighborControlled.lean:156 | `linarith only [h]` (:159), after `unfold neighborStabilityConstant` (:158); `h : 1 ≤ exp (6:ℝ)` from `one_le_exp_iff.mpr (by norm_num)` (:157) | yes: `1e9 * exp 6`, one atom, coefficient 1e9 | none | **1e9** (multiplier 1e9 on `h`) | **30** | no products (`linarith`, not `nlinarith`) | — | OK |
| B | PacketPhysicalFamily.lean:118, PacketGeometryAssembly.lean:70, PacketGeometryGuards.lean:76, :83, :93 (and :54, same idiom) | `norm_num` on a closed goal `(1:ℝ) ≤ 1000000000` / `(0:ℝ) ≤ 1000000000` | **pure numeral**, no atom | none | **1e9** (one `Nat.ble`/`isNat_le_true` on 1e9) | **30** | n/a | — | OK |
| C | PacketGeometryGuards.lean:74-80 `ray_error_small` (uses site :76) | `nlinarith only [hp, hs]` (:80) | goal `800*D.error*D.Θ^5`; `hp` from `scaled_power_le` (EulerProof.lean:17904-17906) has **no** big numeral (`K` = `neighborStabilityConstant` stays an atom, **not** unfolded here); `hs` (:79) `1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1` | `1/2` in the goal (lcm 2); multipliers 800 and 1/1250 -> L=1250 | ~**1e6** | **20** | (1e6)^2 = 1e12 | 40 | OK |
| D | PacketGeometryGuards.lean:82-88 `relative_error_small` (site :83) | `nlinarith only [hp, hs]` (:88) | `K` atom kept (**no** `unfold` in this proof); numerals 1e6, 1/2 | `1/2` (lcm 2), multiplier 1e-6 -> L=1e6 | ~**1e6** | **20** | 1e12 | 40 | OK |
| E | PacketGeometryGuards.lean:90-99 `scalar_error_small` (site :93) | `nlinarith only [hp, hs, hr]` (:99) **after** `unfold neighborStabilityConstant at hp hs hr` (:98) | goal `4*exp 6*(4e8*D.error*D.Θ^29)` = coefficient **1.6e9** on the monomial `exp6*error*Θ^29`; `hr` 1e9 & `1/2`; `hp` 1e9; `hs` **1e15** | `1/2` from `hr`; cheapest multipliers `hr`=4/5 -> L=5 | **8e9** via `hr` alone; **8e15** if the oracle instead routes through `hp`+`hs` | **33** / **53** | `hs*hp` 1e24 (80) / `hs^2` 1e30 (100) | 80-100 | UNCLEAR (UNBUILT) |
| F | PacketNeighborControlled.lean:213-221 (site :213; arithmetic at :219-221) | `nlinarith only [hm, hn, hsmall]` (:221) after `dsimp [δ]` (:219) and `unfold neighborStabilityConstant at hm hn hsmall` (:220) | goal `4*exp 6*(4e8*e*Θ^29) ≤ 1` -> **1.6e9**; `hm` 1e9 (`K*e*Θ^29 ≤ K*e*Θ^40`); `hsmall` **1e15** (`1e6*1e9*exp6*e*Θ^40 ≤ 1`) | none in the hypotheses; the *multipliers* are `hm`=8/5, `hsmall`=8/5e6 -> **L=5e6** (forced: no `≤ 1/2` shortcut exists here, unlike E) | **8e15** = 5e6 x 1.6e9 = 8 x 1e15 | **53** | `hsmall*hm` 1e24 (80) / `hsmall^2` 1e30 (100) | 80-100 | NOTE + UNCLEAR |
| G | PacketNeighborControlled.lean:139-145 `hcoef` (the real 4e8 computation; **not** in the brief's list) | `nlinarith only [h1, h2, mul_nonneg (mul_nonneg he (pow_nonneg hΘ0 29)) hlam, mul_nonneg he (pow_nonneg hΘ0 29)]` (:144-145) | yes: 4e8 x `e*Θ^29*(1+lam)`; `800*(200000*e)` ring-normalises to **1.6e8**; `h2` (:142-143) carries 1.6e8 and, after `2*(1+lam)`, **3.2e8** | **none** (all integer literals; `1+lam+e ≤ 2*(1+lam)` is integral) | **4e8** (multipliers 1, L=1) | **29** | (4e8)^2 = 1.6e17 | **58** | OK |
| H | PacketGeometryAssembly.lean:126 (and :127) | `positivity [D.error_nonneg, D.Theta_pos]` inside `show 0 ≤ 400000000*D.error*D.Θ^29` | 4e8 x atoms; positivity discharges `0 < 400000000` by `norm_num` as a **pure numeral** | none | **4e8** | **29** | n/a (no products) | — | OK |

## Ranking by (f) and the 64-bit question

Degree-1 (what the kernel almost certainly sees):

1. **8e15 — 53 bits — `Euler/PacketNeighborControlled.lean:221`** (`nlinarith only [hm, hn, hsmall]`), driven by
   the forced multiplier `1.6e9/1e15 = 8/5000000`, i.e. `L = 5e6` times the 1e9 coefficient of `hm`.
2. 8e15 / 53 bits (worst branch) or 8e9 / 33 bits (cheap branch) — `Euler/PacketGeometryGuards.lean:99`.
3. 4e8 — 29 bits — `PacketNeighborControlled.lean:144` (`hcoef`) and `PacketGeometryAssembly.lean:126`.
4. 1e9 — 30 bits — `PacketNeighborControlled.lean:159` and every `by norm_num : (1:ℝ) ≤ 1000000000` (row B).
5. 1e6 — 20 bits — `PacketGeometryGuards.lean:80`, `:88`.
6. 0 bits — the six statement-only sites S1-S6.

**Does anything cross 64 bits (1.845e19)?**
* On the degree-1 route: **NO.** The maximum is 8e15 (53 bits), one machine word, 3.5 decimal orders *below*
  2^64 and also below the audit's headline 5.0e17 / 59 bits. So these sites do **not** refute the published
  claim; they sit under it.
* On the degree-2 route: **only conditionally, and only at two sites.** If the simplex puts a nonzero
  multiplier on an nlinarith product involving the `1e15` hypothesis (`hsmall` at :221, `hs` at :99), the
  emitted numeral is `1e15*1e9 = 1e24` (80 bits) up to `1e15^2 = 1e30` (100 bits) — multi-limb GMP.
  Both proofs admit a purely linear certificate, so a competent oracle should not need the product; but
  **that is an assumption I cannot machine-check here (UNBUILT)**. Everywhere else the degree-2 ceiling is
  1.6e17 (58 bits, row G) or 1e12 (40 bits, rows C/D) — comfortably inside one word.

## Notes / caveats

* **NOTE-1 (statement vs computation).** 6 of the 15 assigned sites (S1-S6) are *statements only*: theorem
  conclusions, a `have` type, and a `structure` field. They are transported by `refine`/`exact`/`simpa only`
  and cost the kernel **nothing** in numeral arithmetic. A 7th (S7, the `def` at :154) costs only at its
  `unfold` sites. So 7/15 of the brief's "largest source integer literals" are kernel-free.
* **NOTE-2 (the atom assumption is load-bearing).** If `D.error` were unfolded inside the `nlinarith` at
  Guards:99 / :80 / :88, `1000000 * 1000000000 * 16*(ε*Θ*(4*G)^2+d)` ring-normalises to a
  `2.56e17` coefficient (58 bits) on `exp6*ε*G^2*Θ^41`, and its square is 6.6e34 (116 bits). The `change`
  steps (`:79`, `:87`, `:97`) deliberately re-fold `D.error`, and `error` is a plain `def`
  (`PacketGeometryData.lean:90`), which linarith's parser treats as an atom. Verifying that this really
  blocks the expansion needs a build.
* **NOTE-3 (non-standard-looking syntax, unverifiable here).** `positivity [D.error_nonneg, D.Theta_pos]`
  (Assembly:126) and 20+ similar `positivity [...]` occurrences use a bracketed argument form I could not
  confirm against Mathlib v4.34.0-rc2 from this clone (no Mathlib source present). Not a numeral issue; flagged
  as UNBUILT/UNCLEAR only.
* **UNBUILT everywhere.** Simplex multiplier choice, `ring_nf` intermediate coefficients, and `norm_num`'s
  exact `Nat` operands are all elaboration-time facts. Every number above is a source-level upper/lower
  estimate, not a measurement.

## Verdict counts

OK 11 (S1-S6, A, B, C, D, G, H — counting rows) / NOTE 2 (S7, F) / UNCLEAR 2 (E, F's product branch;
plus NOTE-3) / ESCALATE 0 / KERNEL-RISK 0 / REFUTED 0.
Precisely: rows with tag OK = S1,S2,S3,S4,S5,S6,A,B,C,D,G,H (12); NOTE = S7 (1); NOTE+UNCLEAR = F (1);
UNCLEAR = E (1).
