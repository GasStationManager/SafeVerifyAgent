# Junk-value (silent-degeneracy) audit -- worker _sub-junkvalue-1
Repo: /home/gsm/.openclaw/workspace/repos/NSE @ f9e8bc5b38b6e212696e8a30e3e91517af887bbd (READ-ONLY, grep+read only; no lake build)
Categories: A=guarded in signature (false positive) | B=certified by type (false positive)
            C=guarded by callers only (benign, statement alone weaker than it looks) | D=genuinely unguarded

## 1. Euler/WholeSpaceGaussianKernel.lean -- 6 hits: ALL C (no A/B/D)

Degenerate value under test: `t = 0`. Base defs:
  Euler/WholeSpaceGaussian.lean:19  `def normalization (t) := (Real.pi*t)^(-(3:R)/2)`  -> at t=0 this is
    `(0:R)^(-3/2) = 0` (Mathlib `Real.rpow` junk value for zero base, nonzero exponent).
  Euler/WholeSpaceGaussian.lean:21-22 `def kernel t x := normalization t * Real.exp (-t^-1*||x||^2)`
    -> `kernel 0 = fun _ => 0` (the normalization factor alone kills it; the `t^-1 = 0` in the
       exponent additionally makes the Gaussian factor the constant `exp 0 = 1`).
  Euler/WholeSpaceGaussianKernel.lean:16-17 `firstKernel t a x := (-2*t^-1*<x,a>) * kernel t x` -> `firstKernel 0 = 0`.
  Euler/WholeSpaceGaussianKernel.lean:19-20 `secondKernel t a b x := (4*t^-1^2*<x,a>*<x,b> - 2*t^-1*<a,b>) * kernel t x`
    -> `secondKernel 0 a b = 0`.
So at t=0 all three kernels are literally the zero function and every statement about them is empty.
None of the four flagged theorems carries `0 < t` (all take a bare `(t : R)`):

* :22 `firstKernel_smooth (t : R) (a : Space) : ContDiff R INF (firstKernel t a)`
  CLAIMS: the first-derivative Gaussian kernel is smooth. At t=0 collapses to "the zero function is
  smooth" -- true, empty, and a *smoothness* claim, so low severity.
  Callers all carry `0 < t`: Euler/WholeSpaceGaussianKernel.lean:158-161 (`firstKernel_integrable {t} (ht : 0 < t)`),
  Euler/WholeSpaceGaussianLow.lean:39-45 (`firstKernel_memLp {t} (ht : 0 < t)`),
  Euler/WholeSpaceGaussianIntegration.lean:93+105 (`average_second_identity {t} (ht : 0 < t)`).  => C
* :26 `secondKernel_smooth (t : R) (a b : Space)`  CLAIMS: second-derivative kernel is smooth.
  Same collapse ("0 is smooth"). Sole caller Euler/WholeSpaceGaussianKernel.lean:164-167
  (`secondKernel_integrable {t} (ht : 0 < t)`).  => C
* :32 `kernel_fderiv (t : R) (a x : Space) : fderiv R (kernel t) x a = firstKernel t a x`
  CLAIMS: an EXACT derivative formula for the heat kernel. At t=0 both sides are 0, so it collapses to
  `0 = 0` -- an exact-identity collapse, the kind that matters. Two `t`-denominators flagged (`kernel`,
  `firstKernel`); both die together. Callers all carry `0 < t`:
  Euler/WholeSpaceGaussianIntegration.lean:63 and :64, both inside `average_first_identity {t} (ht : 0 < t)`
  (Euler/WholeSpaceGaussianIntegration.lean:57).  => C
* :42 `firstKernel_fderiv (t : R) (a b x : Space) : fderiv R (firstKernel t a) x b = secondKernel t a b x`
  CLAIMS: EXACT second-derivative formula. At t=0 collapses to `0 = 0`. Callers all carry `0 < t`:
  Euler/WholeSpaceGaussianIntegration.lean:104 and :107, inside `average_second_identity {t} (ht : 0 < t)`
  (Euler/WholeSpaceGaussianIntegration.lean:93).  => C
Cross-check: `grep -rn 'kernel_fderiv|firstKernel_fderiv|firstKernel_smooth|secondKernel_smooth'` over the
whole repo returns only the call sites listed above; there is no unguarded consumer.
Note for the instrument: the *other* 10 in-cone theorems in this file (:56,:59,:62,:75,:83,:104,:114,:129,:158,:164,:171)
all do bind `{t : R} (ht : 0 < t)` -- i.e. the file's author guards where it matters for analysis and
forgets only on the algebraic/smoothness lemmas.

## 2. Euler/PacketPhysicalSize.lean -- 5 hits: ALL FALSE POSITIVES (B-class, new sub-kind)

Degenerate value under test: `a = 0`. Definition:
  Euler/PacketScaledRay.lean:12  `def physicalTime (t0 a eps tau : R) : R := t0 + (eps/a)*tau`
  -> at a=0, `eps/0 = 0` and `physicalTime t0 0 eps tau = t0`.
Verified by reading the file: in ALL five flagged theorems `a` occurs ONLY inside the expression
`physicalTime t0 a eps tau`, and that expression occurs IDENTICALLY on both sides of the identity
(every one of m, v, r, w is evaluated at exactly that point, and `scaledRay`/`scaledVelocity`
themselves only carry `a` into the same `physicalTime` slot:
Euler/PacketScaledRay.lean:35-36 `scaledRay ... := movingRay m v r (physicalTime t0 a eps tau) i / (s0*rayScale eps i)`,
Euler/PacketScaledVelocity.lean:18-19 `scaledVelocity ... := movingVelocity m v w (physicalTime t0 a eps tau) i / velocityScale eps i`).
Therefore at a=0 NOTHING collapses: each theorem becomes the very same nontrivial identity evaluated at
the time `t0`. The real denominators of the two `scaledX` defs -- `s0*rayScale eps i` and
`velocityScale eps i` -- ARE guarded in every one of the five signatures (`hs0 : s0 != 0`, `heps : eps != 0`;
`rayScale_ne_zero` Euler/PacketScaledRay.lean:19, `velocityScale_ne_zero` used at Euler/PacketScaledVelocity.lean:31).

Per hit (all five: what they claim, and why a=0 is harmless):
* :50 `scaledRay_norm_sq` -- exact identity `||r(t)||^2 = s0^2 * rayDenominator eps (R 0) (R 1) (R 2)`.
  Guards present in signature: hs0, heps, hm, hv, hmv.  a=0 -> same identity at t = t0.  FALSE POSITIVE
* :60 `scaledRay_norm` -- same, un-squared (`||r(t)|| = |s0| * sqrt (rayDenominator ...)`).  FALSE POSITIVE
* :72 `scaledVelocity_norm_sq` -- exact identity `||w(t)||^2 = eps^2*V0^2+V1^2+eps^2*V2^2`. FALSE POSITIVE
* :84 `scaledVelocity_norm_ratio_sq` -- exact identity `||w(t)||^2 = V1^2 * velocityDenominator eps (V0/V1) (V2/V1)`;
  note the inner `/V1` IS guarded in-signature by `hV : scaledVelocity ... 1 != 0` (:87), and
  `velocityDenominator eps r w3 = 1+eps^2*(r^2+w3^2)` is positive by construction
  (Euler/PacketPhysicalSize.lean:17,19 `velocityDenominator_pos`) -- category B in the strict sense too. FALSE POSITIVE
* :96 `scaledVelocity_norm_ratio` -- same un-squared; hV at :99.  FALSE POSITIVE

INSTRUMENT NOTE (new false-positive kind, distinct from the two the brief already lists):
  a junk-valued division that sits inside a *shared evaluation-point argument* (here a TIME argument
  reached through `physicalTime`) degenerates BOTH sides simultaneously and leaves a still-meaningful
  statement. The rule that separates it from a real hit: the flagged variable must reach a channel that
  appears on only ONE side of the conclusion (or must scale the conclusion multiplicatively). If the
  denominator variable appears in the conclusion only via a subterm that is syntactically shared by
  both sides, the junk value is a re-specification, not a collapse.

## 3. NavierStokes/PulseCovariance.lean -- 4 hits: 4 x C (0 A/B/D), but ONE of them is worth your eye

Defs:  NavierStokes/PulseCovariance.lean:40-41 `def gaussian (b m r v) := Real.exp (-b * ((v-m)/r)^2)`
       -> at r=0, `(v-m)/0 = 0`, so `gaussian b m 0 v = Real.exp 0 = 1` (the Gaussian becomes the constant 1).
Structure that guards the consumers: `PulseBounds` NavierStokes/PulseCovariance.lean:130-142, fields
`radius_one_le : 1 <= r` (:131) and `decay_pos : 0 < b` (:134); `radius_pos : 0 < r` derived at :173.

* :46 `gaussian_pos (b m r v : R) : 0 < gaussian b m r v`  (proof `Real.exp_pos _`)
  CLAIMS: the pulse Gaussian is strictly positive. At r=0 the "Gaussian" is the constant 1 and the
  statement collapses to `0 < 1`. Severity NIL (a positivity claim about an `exp`, cannot lose an
  equality's worth of content). All uses sit under a `PulseBounds` hypothesis, hence r >= 1:
  NavierStokes/PulseCovariance.lean:176, :191, :209, :283.  => C (severity nil)
* :48 `gaussian_eq_length (b m r v : R) : gaussian b m r v = Real.exp (-b*(v-m)^2/r^2)`
  CLAIMS: a rewriting identity moving the length scale into the denominator (two hits: `r` direct and
  `r` via `gaussian` -- they are the same degeneracy). At r=0 BOTH sides become `Real.exp 0 = 1`, so it
  collapses to `1 = 1`. Callers all have 0 < r: NavierStokes/PulseCovariance.lean:68 (inside
  `reference_envelope_gaussian_bounds`, `hr : 0 < r` at :67) and
  NavierStokes/PrimaryCovarianceBounds.lean:596 (inside a proof with `hr : 1 <= r`, used at :587/:592).
  => C (severity low: a definitional restatement)
* :74 `integral_gaussian_scaled (b m r : R) (hr : 0 < r) : (INT v, gaussian b m r v) = r * Real.sqrt (Real.pi / b)`
  CLAIMS: the EXACT Gaussian mass of a slot, `r * sqrt(pi/b)` -- this is the quantitative heart of the
  "mass of order r" story in the file header (NavierStokes/PulseCovariance.lean:11-14).
  `r` IS guarded (`hr`), but the flagged denominator is `b`, and `b` is UNCONSTRAINED. At b = 0:
    LHS: `gaussian 0 m r = fun _ => 1`, which is not integrable on R, so Mathlib's Bochner integral is
         the junk value 0;
    RHS: `Real.pi / 0 = 0`, `Real.sqrt 0 = 0`, so `r * 0 = 0`.
    => collapses to `0 = 0`. The same happens for every b < 0 (LHS non-integrable -> 0; RHS
       `Real.sqrt (negative) = 0` -> 0). So this exact-mass identity is content-free on the whole
       half-line b <= 0, and it typechecks without `0 < b` only because TWO junk values conspire
       (`integral_undef` and `Real.sqrt` of a negative).
  Its single caller does exclude it: NavierStokes/PulseCovariance.lean:233 (`mass_upper`, :229) applies it
  with `b := 2*b` where `b` carries `PulseBounds.decay_pos : 0 < b` (:134, used via `h.decay_pos` at :231).
  => C, but the highest-value C in this file: the statement ALONE promises an exact mass and delivers
     nothing on b <= 0.
Cross-check: `grep -rn 'integral_gaussian_scaled'` -> only :74 (decl) and :233 (sole use). No other consumer.

## 4. Euler/PacketInitializedCorrectionData.lean -- 4 hits: ALL A (guarded IN SIGNATURE). Pure false positives.

Every one of the three in-cone theorems binds `hk : 4 <= k` in its own signature, which gives k >= 4 > 0:
* :57 `initializedNormalizedField_bound (N) (hN : 1 <= N) (k : R) (hk : 4 <= k) (hbase ...)`  -- hk at :57.
  CLAIMS: a Gevrey word bound for the k-normalized packet field. Denominator `k` reached via
  Euler/PacketInitializedCorrectionData.lean:23-24 (`initializedNormalizedField ... := (...N k^-1).smul k`).
  GUARDED IN SIGNATURE.  => A
* :64 `initializedNormalizedField_normal_bound ... (hk : 4 <= k)` -- hk at :64; the flagged `/k` is right in
  the conclusion at :67 (`normal L.R S.H0 BC.multiplierCost/k`). CLAIMS: the normal component obeys a word
  bound with amplitude divided by k. GUARDED IN SIGNATURE (both the direct `/k` hit and the
  `via initializedNormalizedField` hit).  => A x2
* :72 `initializedNormalizedResidualField_bound (Cagree) (N) (hN) (k X : R) (hk : 4 <= k) ...` -- hk at :73.
  CLAIMS: a residual word bound of size exp(-(7/10) X log k). Denominator via
  :26-30 `initializedNormalizedResidualField`, whose DEFINITION itself takes `(hk : 4 <= k)` as an argument
  (:27) and consumes it as `inv_ne_zero (by linarith)` (:30) -- the term cannot even be FORMED at k = 0.
  => A (arguably B: the guard is part of the definition's telescope)
INSTRUMENT NOTE: `hk : 4 <= k` (and `1 <= k`, `0 < k`, `4 <= k` inside a DEFINITION's telescope) must count
as a nonzero guard. All four hits here are of that shape.

## 5. Euler/PacketPhysicalNormBounds.lean -- 4 hits: ALL FALSE POSITIVES, identical mechanism to section 2.

Same `a = 0` / `physicalTime` story (Euler/PacketScaledRay.lean:12). Read all four: `a` appears ONLY inside
`physicalTime t0 a eps tau`, symmetrically on both sides of every (in)equality, and the genuine denominators
`s0*rayScale eps i` / `velocityScale eps i` are guarded in every signature.
* :31 `scaledRay_norm_le_norm3` -- CLAIMS `||r(t)|| <= s0 * norm3 (R 0) (R 1) (R 2)`. Guards `hs0 : 0 < s0`,
  `heps : 0 < eps`, `heps1 : eps <= 1` (:32). a=0 -> same bound at t = t0.  FALSE POSITIVE
* :51 `scaledVelocity_norm_le_norm3` -- CLAIMS `||w(t)|| <= norm3 (V 0) (V 1) (V 2)`; guards at :52. FALSE POSITIVE
* :71 `physical_size_ge_second` -- CLAIMS a LOWER bound `s0*V 1/2 <= ||r(t)||*||w(t)||`; guards
  `hs0 : 0 < s0`, `heps : eps != 0` (:72), `hN : 1/2 <= R 2` (:75), `hV : 0 <= V 1` (:76). FALSE POSITIVE
* :99 `physical_size_le_scaled_state` -- CLAIMS an UPPER bound `||r(t)||*||w(t)|| <= 49*s0*Theta^4*(|V 0|+|V 1|)`;
  guards at :101 (`hs0`, `heps : 0 < eps`, `heps1`). FALSE POSITIVE
(For all four, the a=0 instance is still a nonvacuous statement about the norms at time t0; the constant
`49*s0*Theta^4` and the `1/2` do not degenerate.)  => 4 x B-class FP (see the instrument note in section 2)

## 6. NavierStokes/FlatPrimitive.lean -- 3 hits: ALL B (false positives), and this is a THIRD FP kind.

Defs: NavierStokes/FlatCutoff.lean:26-27 `def edge (c x) := if x <= 0 then 0 else Real.exp (-c/x^2)`;
      NavierStokes/FlatCutoff.lean:66-67 `def polynomialEdge (c p x) := p.eval x^-1 * edge c x`;
      NavierStokes/FlatPrimitive.lean:25-26 `def integrand (c j b x) := (edge c x / x^j) * b x`.
The `x = 0` value here is the DELIBERATE smooth zero extension, and it is CERTIFIED by theorems, not left as
an accident: `edge_zero` (NavierStokes/FlatCutoff.lean:32), `polynomialEdge_zero` (:69),
`polynomialEdge_tendsto_zero` (:74, a genuine two-sided limit), `polynomialEdge_div_pow` (:161),
`edge_div_pow_contDiff` (:167, "The total quotient, with value zero at the origin, is genuinely smooth"),
and decisively `polynomialEdge_hasDerivAt` (:89) whose proof treats x = 0 as its OWN case
(NavierStokes/FlatCutoff.lean:97-100, `hasDerivAt_iff_tendsto_slope` + the limit lemma) -- i.e. the value the
junk convention produces at 0 is PROVED to be the true derivative, not assumed.
Also note the flagged variable `x` here is the POINT of the statement, universally quantified, not a
parameter guarding the theorem; the x = 0 instance is one true instance of a family, and it is the
interesting one (flatness at the origin).
* :112 `edge_hasDerivAt {c} (hc : 0 < c) (x : R) : HasDerivAt (edge c) (2*c*edge c x / x^3) x`
  (both flagged hits, `x` direct and `x` via `edge`, are the same point). CLAIMS: the exact derivative of the
  flat edge. At x=0 the RHS is `2*c*0/0 = 0` and the statement becomes `HasDerivAt (edge c) 0 0` -- TRUE,
  nontrivial (it IS the flatness statement), and proved at x=0 by NavierStokes/FlatCutoff.lean:97-100.
  => B (false positive)
* :45 `primitive_hasDerivAt {c} (hc : 0 < c) (j) {b} (hb : Continuous b) (x : R) :
        HasDerivAt (primitive c j b) (integrand c j b x) x`
  CLAIMS: FTC for the flat primitive. At x=0, `integrand c j b 0 = (0/0^j)*b 0 = 0`, and the statement
  `HasDerivAt (primitive c j b) 0 0` is true and meaningful (the primitive is flat at 0; cf.
  `primitive_of_nonpos` :69 and `primitive_iteratedDeriv_zero` :95). The integrand's continuity at 0 comes
  from `integrand_continuous` :41 / `edge_div_pow_contDiff`.  => B (false positive)
INSTRUMENT NOTE (third FP kind): a `f x / x^k` whose zero value is accompanied in the SAME file/import
closure by a `_zero`, `_tendsto_zero`, or `ContDiff`/`HasDerivAt`-at-the-junk-point lemma is a deliberate
smooth extension. Cheap detector: if the flagged variable is the statement's point of evaluation
(universally quantified, appearing on both sides) AND some lemma named `*_zero`/`*_contDiff` mentions the
same quotient, deprioritize.

## 7. Euler/MeanCutoffDifferenceBound.lean -- 3 hits: 3 x D, but ALL severity NIL (see the reasoning).

Def: Euler/MeanBoundaryDifference.lean:40-44 `Cutoff.differenceQuotient chi a h` with
`(chi.differenceQuotient a h).field x = h^-1 * (chi.field (x + h*a) - chi.field x)`.
At h = 0: `h^-1 = 0`, so `(chi.differenceQuotient a 0).field = 0` identically (the whole cutoff becomes the
zero cutoff). Nothing in this file or its consumers excludes h = 0; on the contrary the author ADMITS it
deliberately -- `norm_differenceQuotient_le` (Euler/MeanCutoffDifferenceBound.lean:39) proves the h = 0 case
by an explicit `by_cases hh : h = 0` at :43-45. So these are unguarded-by-design, and the degenerate
instances are true-but-empty rather than dangerous.
* :57 `differenceQuotient_fderiv (chi : Cutoff) (a : Space) (h : R) (x : Space) :
        fderiv R (chi.differenceQuotient a h).field x = h^-1 . (fderiv R chi.field (x+h.a) - fderiv R chi.field x)`
  (both flagged hits, `h` direct and `h` via `differenceQuotient`, are one degeneracy.)
  CLAIMS: an EXACT commutation of `fderiv` with the difference quotient. At h = 0: LHS `fderiv` of the zero
  field = 0; RHS `0 . (fderiv chi.field x - fderiv chi.field x)` = 0.  COLLAPSES TO `0 = 0`.
  Consumers do NOT re-guard at the first layer: Euler/MeanCutoffDifferenceBound.lean:118
  (`cutoffBound_differenceQuotient`, :100, has only `hstep : ||h.a|| <= 1`, which h = 0 satisfies) and
  Euler/MeanCutoffTaylor.lean:129 (`Cutoff.differenceError_fderiv`, :121, no h-hypothesis). Only the third
  layer re-guards: Euler/MeanCutoffTaylor.lean:137 `cutoffBound_differenceError` carries `hh : h != 0`.
  => D, severity NIL: the collapse is SYMMETRIC (both sides vanish together) and every downstream use is a
     BOUND that stays true (trivially) at h = 0.
* :69 `differenceQuotient_support (chi) (R) (hsupport) (a) (h : R) (hstep : ||h.a|| <= 1) :
        tsupport (chi.differenceQuotient a h).field SUBSET closedBall 0 (R+1)`
  CLAIMS: the difference quotient keeps compact support in a ball only 1 larger. At h = 0 the field is
  identically 0, `tsupport = EMPTY`, and the statement collapses to `EMPTY SUBSET closedBall 0 (R+1)`.
  Callers: Euler/MeanCutoffDifferenceBound.lean:110 and Euler/MeanCutoffTaylor.lean:115, neither of which
  requires h != 0 (the h != 0 appears only at Euler/MeanCutoffTaylor.lean:137).
  => D, severity NIL (a support-inclusion claim, collapsing to a trivially true inclusion).

## 8. Euler/PacketForwardInitializedBounds.lean -- 3 hits: ALL A (guarded in signature). One line, as instructed.
Each theorem binds `hk : 4 <= k` in its OWN signature, so k >= 4 > 0 and every `k^-1` / `/k` is guarded:
:47 `forwardInitializedPacket_normalized_bound` (hk at :47; claims a velocity word bound for the
k-normalized forward packet) => A; :57 `forwardInitializedPacket_normal_bound` (hk at :57; claims the normal
component obeys a word bound with amplitude `.../k`) => A; :67 `forwardInitializedResidual_normalized_bound`
(hk at :68; claims a residual bound `exp(-(7/10) X log k)`, and the `k^-1` it feeds is accompanied by
`inv_ne_zero (by linarith)` at :73, from hk) => A.
Same instrument fix as section 4: `4 <= k` is a nonzero guard.

## 9. Euler/PacketInitializedBounds.lean -- 3 hits: ALL A (guarded in signature). One line, as instructed.
`hk : 4 <= k` is bound in each signature: :57 `initializedPacket_normalized_bound` (velocity word bound for
the k-normalized packet) => A; :69 `initializedPacket_normal_bound` (normal-component word bound with
amplitude `.../k`, :73) => A; :81 `initializedResidual_normalized_bound` (residual bound
`exp(-(7/10) X log k)`; the `k^-1` is fed with `inv_ne_zero (by linarith)` at :87) => A.

## 10. Euler/PacketUniformFrequencyMargin.lean -- 3 hits: ALL A (guarded in signature). One line, as instructed.
Each binds `hk : 1 <= k` in its own signature and the proofs immediately derive `hk0 : 0 < k`:
:17 `cost_div_le_inverse_half (C k) (hk : 1 <= k) (hC : C <= smallPower k) : C/k <= k^(-1/2)` (hk0 at :19)
  -- claims the cost/frequency ratio beats k^(-1/2)  => A
:49 `physical_error_le_inverse_quarter (C E k) (hk : 1 <= k) ... : C/k + E*k*delta (expansion k) <= k^(-1/4)`
  (hk0 at :53) -- claims a physical-error margin  => A
:62 `liftedAmplitude_small_of_costs (C E R T k) (hk : 1 <= k) ...` (hk0 at :68); the `/k` enters via
  `liftedAmplitude C E k` -- claims `liftedAmplitude <= 2 k^(-1/2)` and `liftedAmplitude*R*T <= 1/8`  => A

## TOTALS (38 hits over 10 files, all read)
A = 13 (sections 4, 8, 9, 10)         -- `4 <= k` / `1 <= k` already in the signature
B = 12 (sections 2, 5, 6)             -- shared-evaluation-point `a`, and certified smooth zero extension
C = 10 (sections 1, 3)                -- guarded by callers only
D =  3 (section 7)                    -- genuinely unguarded, but all three of severity NIL
Highest-value items are two C's, not the D's: NavierStokes/PulseCovariance.lean:74 (exact slot-mass identity,
content-free for every b <= 0) and Euler/WholeSpaceGaussianKernel.lean:32/:42 (exact derivative formulas,
`0 = 0` at t = 0).
