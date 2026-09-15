# READ-ONLY recheck: `stocks_formulas` in NavierStokes/SeedHandbackJets.lean

Auditor: independent child. Nothing under repos/NSE was modified. No `lake build` run
(no built Mathlib / disk 99% full); the check is a *symbolic* re-derivation of the
`PolynomialExpression` trees against the claimed closed forms, plus a mutation battery
that proves the test is sensitive to exactly the off-by-one / sign errors it must catch.

Tooling: sympy 1.14.0 installed into a throwaway venv at /tmp/symv (NOT into the NSE repo
or its toolchain). Decision procedure: `simplify(expand(lhs - rhs)) == 0`.

## 1. Index map, re-derived from `basis` (SeedHandbackJets.lean:57-61)

```
def basis (h X : ℝ) (p : Packet) : Basis :=
  ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, p 10, p 11,   -- 0..11
    (fun η => η),                    -- 12
    (fun _ => X),                    -- 13
    (fun _ => X⁻¹),                  -- 14
    (fun _ => (Real.sqrt (2*X))⁻¹),  -- 15
    (fun η => (p 0 η)⁻¹),            -- 16
    (fun η => (NaturalAxisData.L h η)⁻¹),  -- 17
    NaturalAxisData.d]               -- 18
```
Counting the `Matrix.cons` entries positionally: 12 entries `p 0 .. p 11` occupy 0..11,
then id at 12, X at 13, X⁻¹ at 14, (√(2X))⁻¹ at 15, (p 0)⁻¹ at 16, (L h)⁻¹ at 17, d at 18.
**This is IDENTICAL to the map supplied in the brief. No off-by-one found.**
Corroborating independent evidence for the same map: `basis_pairBound` (:141-159) discharges
its 19 `fin_cases` goals in the order `hpq 0..hpq 11`, `Bound.id` (12), `hXs` (13), `hXi` (14),
`hXsroot` (15), `(hpq 0).inverse` (16), `hL` (17), `fixed_d_bound` (18) — same positions —
and `inputBounds` (:110-111) is `![D×12, 1, X₁, X₀⁻¹, (√(2X₀))⁻¹, T, L, 1+2^k]`, again same.

`eval` (ClosedIntervalJetAlgebra.lean:255-260) is the plain pointwise interpretation
(`input i => x i`, `constant c => fun _ => c`, add/sub/mul pointwise), so eval of `input 12`
at η is η and of `input 16` is (p 0 η)⁻¹, as assumed.
`NaturalAxisData`: `D h = 1/2-h`, `A h = 1/2+h`, `d η = 1-η²`, `L h η = 1-2*h*η²`.

## 2. Transliterated trees -> algebra

massExpression (:67-69) = ((X - 2·D·η·p2) - d·p3)·X⁻¹
angular (:71-76)  = (0 - mass) + ((((1-h)·p4 - D·η·p5) - d·p7 + 2·(h-D)·η·p6)·X⁻¹·(√(2X))⁻¹)·p0⁻¹
axial   (:78-82)  = ((0 - mass·p1) + ((D·(p2 - η·p3) + 4h·η·p8) - d·p9)·X⁻¹) + 4A·η·p10 - d·p11
out 2   (:87)     = (X·L⁻¹)·angular
out 3   (:88)     = ((X·L⁻¹)·p0⁻¹)·axial

Simplified forms produced by sympy:

stocks 0 =
 3/2                            √2⋅X⋅(D⋅η⋅p₅ + d⋅p₇ + 2⋅η⋅p₆⋅(D - h) + p₄⋅(h - ↪
X   ⋅p₀⋅(2⋅D⋅η⋅p₂ - X + d⋅p₃) - ────────────────────────────────────────────── ↪
                                                        2                      ↪
────────────────────────────────────────────────────────────────────────────── ↪
                                      5/2                                      ↪
                                     X   ⋅p₀                                   ↪

↪  1))
↪ ────
↪     
↪ ────
↪     
↪     

stocks 1 =
-D⋅(η⋅p₃ - p₂) + X⋅(4⋅A⋅η⋅p₁₀ - d⋅p₁₁) - d⋅p₉ + 4⋅η⋅h⋅p₈ + p₁⋅(2⋅D⋅η⋅p₂ - X +  ↪
────────────────────────────────────────────────────────────────────────────── ↪
                                         X                                     ↪

↪ d⋅p₃)
↪ ─────
↪      

## 3. Claimed RHS (transliterated verbatim from :96-104)

W    = (X - 2*D*η*p2 - d*p3)/X
RHS0 = -W + ((1-h)*p4 - D*η*p5 - d*p7 + 2*(h-D)*η*p6)/(X*√(2X)*p0)
RHS1 = -W*p1 + (D*(p2 - η*p3) + 4h*η*p8 - d*p9)/X + 4A*η*p10 - d*p11
RHS2 = X/L * stocks 0
RHS3 = X/(L*p0) * stocks 1

## 4. VERDICTS

| formula | verdict | residual |
|---|---|---|
| 0 (`Q_s`, angular)  | MATCH | 0 |
| 1 (`N_s`, axial)    | MATCH | 0 |
| 2 (`p_{s,1}`)       | MATCH | 0 |
| 3 (`p_{s,2}`)       | MATCH | 0 |

Also MATCH when RHS2/RHS3 are re-expanded from RHS0/RHS1 instead of from the LHS,
and MATCH after substituting the concrete `D=1/2-h, A=1/2+h, d=1-η², L=1-2hη²`.
Every sign and every packet index in the claim reproduces the tree, including the
`+2*(h-D)*η*p6` sign (a `.add` of the p6 block after two `.sub`s) and the trailing
`- d*p11` (the outermost `.sub`).

## 5. Sensitivity (mutation battery) — the test is NOT vacuous

Tail index map rotated by +1 and by -1: residual 0 and 1 both become nonzero.
Packet-index swaps (residual that actually uses the swapped pair is shown):
  swap p2/p3: (r0==0, r1==0) = (False, False)
  swap p4/p5: (r0==0, r1==0) = (False, True)
  swap p6/p7: (r0==0, r1==0) = (False, True)
  swap p8/p9: (r0==0, r1==0) = (True, False)
  swap p10/p11: (r0==0, r1==0) = (True, False)
  swap p0/p1: (r0==0, r1==0) = (True, False)
  swap p5/p6: (r0==0, r1==0) = (False, True)
  swap b13/b14: (r0==0, r1==0) = (False, False)
  swap b16/b17: (r0==0, r1==0) = (False, True)
  swap b12/b18: (r0==0, r1==0) = (False, False)
(`True` entries are pairs the *other* formula does not mention, e.g. angular uses
p4..p7 only, axial uses p1,p2,p3,p8..p11 only — so those are expected insensitivities,
not weak spots: each pair is caught by the formula that contains it.)
Sign flips of the p6 term (formula 0) and the p11 term (formula 1): both detected.

## 6. Notes / caveats worth the parent's attention (no mismatch, but read)

1. NO POSITIVITY NEEDED. The identity is unconditional in Lean, since `basis` supplies
   `X⁻¹`, `(√(2X))⁻¹`, `(p 0 η)⁻¹` and the RHS writes the same quantities as `/X`,
   `/(X*√(2X)*p 0 η)`; `mul_inv_rev` and `div_eq_mul_inv` hold with zeros too. So the
   proof's `simp [... div_eq_mul_inv, mul_inv_rev]` needs no `X ≠ 0` / `p 0 η ≠ 0`, and the
   theorem is equally true (both sides 0-ish) at X = 0 or p 0 η = 0. That means the theorem
   asserts nothing about non-degeneracy — do not read it as implying X > 0.
2. Formulas 2 and 3 are near-TAUTOLOGIES. `outputExpression 2/3` are *defined* as
   `(v 13 * v 17) * angular` and `((v 13 * v 17) * v 16) * axial`, and the claim states
   exactly `X/L * stocks 0` and `X/(L*p0) * stocks 1`. So conjuncts 3 and 4 carry no
   content beyond `X * L⁻¹ = X/L` and associativity. Only conjuncts 1 and 2 are informative.
3. `L h η` and `p 0 η` are NOT shown nonzero anywhere in the statement, consistent with (1).
4. The statement is about `stocks`, i.e. about `packet P₀ f`; it does not connect these
   symbols to any PDE. Reading `p 2 η` as an actual integrated mass history is a claim made
   elsewhere (`Profile.curves` / `Profile.history`), not by this theorem.
