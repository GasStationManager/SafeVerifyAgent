# Junk-value degeneration audit (worker sub-junkvalue-2), NSE @ f9e8bc5, READ-ONLY


## 1. NavierStokes/PhaseCalculus.lean -- 10 hits, ALL FALSE POSITIVES (B)

`phase` (:44-46): `phase ε p pz x0 F G q = p*θ + (pz/ε)*Z + x0*R - v*(p*F+pz*G)`.
Key structural fact: `pz/ε` enters ONLY as a *constant coefficient* of the `Z` slot. It is
never a hypothesis-bearing denominator: for any ε (incl. 0) `pz/ε` is just some real `c`, and
every theorem below is the corresponding statement for the phase with axial coefficient `c`.
So at ε=0 the theorems remain TRUE and NON-VACUOUS (they become the statements for the
Z-independent phase). Nothing collapses to `0 = 0`.

Evidence the author guards where a guard is actually needed (i.e. the tool's ε-detector is
firing on the wrong theorems): `hε : ε ≠ 0` IS present at :110 (`phaseNormal_formula`),
:149 (`signedMaterialOp_phase`), :167 (`backwardMaterialOp_phase`), :251
(`hasDerivAt_phaseNormal_slot`) -- exactly the places where `field_simp [hε]` is used
(:120, :161).

Per-hit:
- :49 `fderiv_phase_apply` -- CLAIMS: full Frechet differential of the phase. `(pz/ε)*w.1.2.1`
  appears on the RHS as literally the same subterm as in the def, so ε occurs on BOTH sides
  (one-side rule: symmetric -> harmless). At ε=0 it is the correct differential of the
  Z-independent phase. **B.**
- :70 `phase_dR` -- CLAIMS: `∂R Φ = x0 - v*(p F_R + pz G_R)`. ε-free RHS, and the R-derivative
  does not see the Z coefficient at all; true and nontrivial for every ε. **B.**
- :76 `phase_dTheta` -- CLAIMS: `∂θ Φ = p` (exact). ε-free, true for all ε. **B.**
- :83 `phase_dZ` -- CLAIMS: `∂Z Φ = pz/ε - v*(p G_Z ...)` (exact). ε appears on BOTH sides in the
  identical subterm `pz/ε`; at ε=0 both sides become `-v*(...)`, still an exact nontrivial
  derivative identity. FP kind (i) (shared subterm, not shared eval point). **B.**
- :89 `phase_dT`, :95 `phase_dV` -- CLAIMS: exact `∂T Φ`, `∂v Φ`. ε-free statements, true for
  all ε. **B.**
- :123 `contDiff_phase` -- CLAIMS: joint `C^n` smoothness. Not an identity; holds for all ε
  (proof :126-132 uses no ε fact). **B.**
- :180 `phase_angularShift` -- CLAIMS: `Φ(θ+h) = Φ(θ) + p*h` (exact). ε appears symmetrically
  (same `pz/ε` term on both sides); true for all ε. **B.**

VERDICT: file is entirely B. The detector should not treat a `/ε` that is a *coefficient
constant appearing identically on both sides* as a channel.


## 2. NavierStokes/SquaredPartition.lean -- 5 hits, ALL FALSE POSITIVES (B)

`gridMask δ k x = lineMask k (x / δ)` (:174). So δ enters ONLY as a **shared evaluation
point**: at δ=0 the mask becomes the constant function `x ↦ lineMask k 0`. This is exactly the
previous triage's FP kind (i). And `lineMask` itself is nondegenerate BY CONSTRUCTION: its
denominator is `Real.sqrt (denominatorSquared x)` with `denominatorSquared_pos` proved for
EVERY x (used at :120-121, :130, :144, :147), so no inner junk value ever appears.

Author does guard where δ=0 would break truth: `hδ : 0 < δ` at :185 `gridMask_support`,
:194 `gridMask_tsupport`, :198 `gridMask_compactSupport`, :248, :260, :330, :352. The 5 hits
are precisely the statements that stay TRUE at δ=0.

- :179 `gridMask_smooth` -- CLAIMS: `ContDiff ℝ ∞ (gridMask δ k)`. At δ=0 it is the constant
  function, still smooth. True, and the δ≠0 content is untouched. A smoothness claim, not an
  exact value, so a trivial instance costs nothing. **B.**
- :182 `gridMask_sum_sq` -- CLAIMS: exact partition identity `∑ᶠ k, gridMask δ k x ^ 2 = 1`.
  Proof (:183) is `lineMask_sum_sq (x / δ)`, and `lineMask_sum_sq` (:143) holds at EVERY real
  point, including 0. So at δ=0 the identity is `∑ᶠ k, lineMask k 0 ^ 2 = 1` -- exactly true,
  not a `0 = 0`. Shared evaluation point. **B.**
- :203 `gridMask_locallyFinite` -- CLAIMS: local finiteness of the support family. At δ=0 the
  family is `{ℝ for k = 0, ∅ otherwise}` (since `support (lineMask 0) = Ioo (-1) 1 ∋ 0`,
  :123-124), which is locally finite. True; proof (:205-208) uses no δ fact. **B.**
- :235 `productMask_support` -- CLAIMS: support of the product = intersection of coordinate
  preimages. δ occurs on BOTH sides inside `gridMask δ ...` (ONE-SIDE rule kills it), and the
  proof (:237-238) is pure `Finset.prod_ne_zero_iff`, valid for any δ. **B.**
- :343 `productMask_eq_rescale` -- CLAIMS: exact rescaling identity
  `productMask δ k x = productMask 1 0 (δ⁻¹ • x - k)`. This is the one hit where δ is truly
  one-sided (`δ` left, `δ⁻¹` right), i.e. the shape worth checking. Checked: at δ=0,
  LHS_j = `lineMask (k j) 0` and RHS_j = `lineMask 0 (-(k j))`, and these are EQUAL by the
  unconditional translate identity `lineMask_eq_translate` (:170, itself resting on
  `denominatorSquared_sub_int` :165, the 1-periodicity of the denominator). So the identity is
  genuinely true at δ=0, not a junk coincidence; the proof (:345-349) uses no `hδ`, confirming
  it is unconditional. **B.**

VERDICT: file is entirely B.


## 3. Euler/PhysicalL2Scaling.lean -- 3 hits (2 distinct theorems): 1 B, 1 C

`scale ell f = fun x => ell • f (ell⁻¹ • x)` (:48). At ell=0 BOTH the prefactor and the
evaluation point die (`(0:ℝ)⁻¹ = 0`), so `scale 0 f = 0` (the zero function) identically.

- :50 `scale_contDiff` -- CLAIMS: `ContDiff ℝ ∞ (scale ell f)`. At ell=0 this is "the zero
  function is smooth": true, trivially. Regularity claim, no exact value at stake; the ell≠0
  content is intact and the proof (:52) needs no `hell`. **B (harmless).**
- :54 `iteratedFDeriv_scale` -- CLAIMS: the EXACT jet formula
  `iteratedFDeriv ℝ n (scale ell f) x = (ell*(ell⁻¹)^n) • iteratedFDeriv ℝ n f (ell⁻¹ • x)`.
  At ell=0: LHS = jets of the zero function = 0; RHS prefactor `ell*(ell⁻¹)^n = 0*0^n = 0`
  (also 0 at n=0, where `(ell⁻¹)^0 = 1` and the surviving factor is `ell = 0`), so RHS = 0.
  The statement becomes `0 = 0` -- CONTENT-FREE at ell = 0, and it is an exact identity, the
  shape that matters. `ell` is one-sided in the tool's sense but degenerates on both sides.
  NOT guarded in its own signature (:54-55 has only `hf`, `n`, `x`).
  GUARDED BY CALLERS: every consumer carries `hell : 0 < ell` --
    * :64-66 `scale_jet_memLp (ell) (hell : 0 < ell) ...`, applies it at :69;
    * :73-76 `lpNorm_scale_jet (ell) (hell : 0 < ell) ...`, applies it at :79;
    * :86-90 `lpNorm_scale_jet_le (hell) (hell1 : ell ≤ 1) ...`, via :91.
  **C.** Benign in this file, but the lemma alone advertises an exact dilation jet law that
  says nothing at ell = 0.

(The two "hits" at :54 -- `ell` and `ell via scale` -- are one theorem.)

