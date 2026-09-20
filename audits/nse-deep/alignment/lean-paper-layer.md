################ NavierStokes/ProblemStatement.lean (168 lines)
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# OPEN target: the candidate forced Navier--Stokes construction

This module states the primary existential assertion of Candidate Theorem 1.1.
`candidateStatement` is a proposition, not an axiom or a proved theorem.
No witness satisfying it is constructed here.

The unit torus is represented by periodic functions on Euclidean three-space.
Time is the first coordinate in `SpaceTime`. Smoothness at time zero is relative
to the indicated closed half-domain. The PDE uses ordinary Frechet derivatives
and is imposed only at interior times `0 < t < 1`; the initial value is imposed
separately at `t = 0`. No arbitrary extension to negative time is differentiated
at the time-zero boundary.

The `ContDiff` scope's `∞` means all finite differentiability orders. In this
Mathlib version `⊤` would instead impose the stronger analytic order.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace NavierStokes.ProblemStatement

/-- Three-dimensional real Euclidean space with its Euclidean norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The first coordinate is time; the second is the lifted spatial coordinate. -/
abbrev SpaceTime := ℝ × Space

abbrev VelocityField := SpaceTime → Space
abbrev PressureField := SpaceTime → ℝ

/-- The standard unit coordinate vectors, fixing both the metric and periods. -/
def coordinateVector (i : Fin 3) : Space := EuclideanSpace.single i 1

/-- Physical spacetime before the proposed singular time, including initial time. -/
def preSingularDomain : Set SpaceTime := Ico 0 1 ×ˢ univ

/-- The physical domain on which the prescribed force must be smooth. -/
def futureDomain : Set SpaceTime := Ici 0 ×ˢ univ

/-- Invariance under each of the three unit coordinate shifts. Quantifying over
every spatial point also gives the corresponding negative shifts. -/
def UnitSpatialPeriodsOn {V : Type*} (times : Set ℝ) (g : SpaceTime → V) : Prop :=
  ∀ t ∈ times, ∀ x : Space, ∀ i : Fin 3,
    g (t, x + coordinateVector i) = g (t, x)

/-- Ordinary time derivative, evaluated on the positive unit time direction.
It is used in the PDE only for `0 < t < 1`. -/
def temporalDerivative (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun s : ℝ => u (s, x)) t 1

/-- Spatial Frechet derivative with time held fixed. -/
def spatialDerivative (u : VelocityField) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (fun y : Space => u (t, y)) x

/-- `(u · ∇)u`, the spatial derivative applied to the velocity vector. -/
def advection (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative u t x (u (t, x))

/-- Euclidean divergence `∑ᵢ ∂ᵢuᵢ`. -/
def spatialDivergence (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, (spatialDerivative u t x (coordinateVector i)) i

/-- Euclidean gradient `∑ᵢ (∂ᵢp)eᵢ`. -/
def pressureGradient (p : PressureField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    (fderiv ℝ (fun y : Space => p (t, y)) x (coordinateVector i)) • coordinateVector i

/-- Componentwise Euclidean Laplacian `∑ᵢ ∂ᵢ∂ᵢu`. -/
def spatialLaplacian (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y : Space => spatialDerivative u t y (coordinateVector i))
      x (coordinateVector i)

/-- The physical Navier--Stokes residual at viscosity exactly one. -/
def navierStokesResidual (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x + advection u t x - spatialLaplacian u t x +
    pressureGradient p t x

/-- A common finite upper endpoint for the force's future time support,
uniformly over space. Spatial support is not required to be compact in the lift. -/
def CompactFutureTimeSupport (f : VelocityField) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ x : Space, f (t, x) = 0

/-- Pointwise expression of unbounded speed arbitrarily near time one from
below. Both the threshold and the time-neighborhood radius are arbitrary. -/
def SpeedUnboundedAtOne (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖

/-- Every field in this proposition is an explicit regularity, periodicity,
support, equation, initial-value, or blow-up condition. No existence is asserted
by introducing the proposition. -/
structure CandidateProperties (u : VelocityField) (p : PressureField)
    (f : VelocityField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  force_smooth : ContDiffOn ℝ ∞ f futureDomain
  velocity_periodic : UnitSpatialPeriodsOn (Ico 0 1) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico 0 1) p
  force_periodic : UnitSpatialPeriodsOn (Ici 0) f
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  force_time_support : CompactFutureTimeSupport f
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    navierStokesResidual u p t x = f (t, x)
  speed_unbounded : SpeedUnboundedAtOne u

/-- OPEN: the primary existential content of Candidate Theorem 1.1.
There is no proof, witness, or axiom asserting this proposition in this module.
Maximal lifespan, Sobolev blow-up, and force derivative decay require additional
theorems and are not silently included as proved consequences. -/
def candidateStatement : Prop :=
  ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField,
    CandidateProperties u p f

/-- Relative smoothness gives ordinary smoothness at every interior spacetime
point, where the ordinary derivatives in the equation are evaluated. -/
theorem smooth_at_interior {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    ContDiffAt ℝ ∞ g (t, x) := by
  exact hg.contDiffAt (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) Filter.univ_mem)

/-- A unit-period identity also gives the negative unit shift. -/
theorem unit_period_negative {V : Type*} {times : Set ℝ} {g : SpaceTime → V}
    (hg : UnitSpatialPeriodsOn times g) {t : ℝ} (ht : t ∈ times)
    (x : Space) (i : Fin 3) :
    g (t, x - coordinateVector i) = g (t, x) := by
  have h := hg t ht (x - coordinateVector i) i
  simpa only [sub_add_cancel] using h.symm

/-- The residual definition reduces to zero for zero velocity and pressure. -/
@[simp] theorem zero_residual (t : ℝ) (x : Space) :
    navierStokesResidual (fun _ => 0) (fun _ => 0) t x = 0 := by
  simp [navierStokesResidual, temporalDerivative, advection, spatialLaplacian,
    spatialDerivative, pressureGradient]

/-- The zero force satisfies the explicit support condition. -/
theorem zero_force_time_support : CompactFutureTimeSupport (fun _ => 0) := by
  exact ⟨0, le_refl 0, fun _ _ _ => rfl⟩

/-- The blow-up condition excludes the zero velocity field. -/
theorem zero_velocity_not_unbounded : ¬ SpeedUnboundedAtOne (fun _ => 0) := by
  intro h
  obtain ⟨t, x, _, _, hlarge⟩ := h 1 zero_lt_one 1 zero_lt_one
  have hlt : (1 : ℝ) < 0 := by simpa only [norm_zero] using hlarge
  exact (not_lt_of_ge zero_le_one) hlt

/-- The quantified blow-up condition excludes every uniform finite bound on
the physical presingular domain. This does not assert that the condition holds. -/
theorem unbounded_speed_excludes_uniform_bound {u : VelocityField}
    (h : SpeedUnboundedAtOne u) :
    ¬ ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, ‖u (t, x)‖ ≤ C := by
  rintro ⟨C, hC⟩
  have hpositive : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  obtain ⟨t, x, ht, _, hlarge⟩ := h (max C 1) hpositive 1 zero_lt_one
  have hbound := (hC t ⟨ht.1.le, ht.2⟩ x).trans (le_max_left C 1)
  exact (not_lt_of_ge hbound) hlarge

end NavierStokes.ProblemStatement

################ NavierStokes/R3/ProblemStatement.lean (222 lines)
import NavierStokes.ProblemStatement
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Support

/-!
# The whole-space assertion of Part II, Theorem 1.1

This module states the R³ theorem, including its comparison claim, independently
of the existing periodic target. The coordinates, Euclidean norm, and differential
operators are those of `NavierStokes.ProblemStatement`; no periodicity assumption
is made here. Time is the first coordinate of spacetime.

The force is a globally smooth function whose topological support is compact and
contained in strictly positive time. This represents the zero extension of an
element of `C_c^∞(R³ × (0, ∞); R³)` and, in particular, requires support separated
from initial time as well as from spatial and future-time infinity.

Smoothness of velocity and pressure at time zero is relative to the physical
half-domain. The equation uses ordinary derivatives at positive times; zero
initial velocity is imposed separately. This avoids differentiating an arbitrary
extension to negative time at the boundary. `∞` in the `ContDiff` scope means
every finite differentiability order.

`breakdownStatement` is the full proposition to prove. Introducing it does not
assert that it has a proof or supply a witness.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3.ProblemStatement

/-- R³ with its ordinary Euclidean norm. -/
abbrev Space := NavierStokes.ProblemStatement.Space

/-- Spacetime, with time first. -/
abbrev SpaceTime := NavierStokes.ProblemStatement.SpaceTime

abbrev VelocityField := NavierStokes.ProblemStatement.VelocityField
abbrev PressureField := NavierStokes.ProblemStatement.PressureField

/-- The physical domain before the asserted singular time. -/
abbrev preSingularDomain := NavierStokes.ProblemStatement.preSingularDomain

/-- The physical domain for a global competing solution. -/
abbrev futureDomain := NavierStokes.ProblemStatement.futureDomain

/-- The open set in which the prescribed force must have compact support. -/
def positiveTimeDomain : Set SpaceTime := Ioi 0 ×ˢ univ

/-- The exact incompressible Navier--Stokes residual at viscosity `ν`.
The viscosity multiplies only the spatial Laplacian. -/
def navierStokesResidual (ν : ℝ) (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  NavierStokes.ProblemStatement.temporalDerivative u t x +
    NavierStokes.ProblemStatement.advection u t x -
    ν • NavierStokes.ProblemStatement.spatialLaplacian u t x +
    NavierStokes.ProblemStatement.pressureGradient p t x

/-- Compact spacetime support contained in `t > 0`, using the closure of the
nonzero set. Together with global smoothness this is the required force class. -/
def CompactPositiveTimeSupport (f : VelocityField) : Prop :=
  HasCompactSupport f ∧ tsupport f ⊆ positiveTimeDomain

/-- Square integrability with respect to ordinary Lebesgue volume on R³.
This condition is explicit because the real Bochner integral is totalized. -/
def SquareIntegrableAtTime (u : VelocityField) (t : ℝ) : Prop :=
  Integrable (fun x : Space => ‖u (t, x)‖ ^ 2) (volume : Measure Space)

/-- Kinetic energy at a time. It is used below only together with the explicit
integrability condition `SquareIntegrableAtTime`. -/
def kineticEnergy (u : VelocityField) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : Space, ‖u (t, x)‖ ^ 2 ∂(volume : Measure Space)

/-- One finite bound for the kinetic energy at every time in `times`, with
square integrability required at every such time. -/
def UniformFiniteEnergy (times : Set ℝ) (u : VelocityField) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ times,
    SquareIntegrableAtTime u t ∧ kineticEnergy u t ≤ E

/-- Pointwise unbounded speed in every left neighborhood of time one. For the
continuous, compactly supported spatial slices in `CandidateProperties`, this
expresses the L∞ blow-up assertion of Theorem 1.1. -/
abbrev SpeedUnboundedAtOne := NavierStokes.ProblemStatement.SpeedUnboundedAtOne

/-- The properties of the constructed fields in Theorem 1.1. The same single
compact set `K` contains both spatial supports for every `0 ≤ t < 1`. -/
structure CandidateProperties (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  support_compact : IsCompact K
  velocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => u (t, x)) ⊆ K
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => p (t, x)) ⊆ K
  force_smooth : ContDiff ℝ ∞ f
  force_support : CompactPositiveTimeSupport f
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    NavierStokes.ProblemStatement.spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    navierStokesResidual ν u p t x = f (t, x)
  energy_bounded : UniformFiniteEnergy (Ico 0 1) u
  speed_unbounded : SpeedUnboundedAtOne u

/-- Data realizing the primary existence assertion at one viscosity. -/
structure Candidate (ν : ℝ) where
  velocity : VelocityField
  pressure : PressureField
  force : VelocityField
  support : Set Space
  properties : CandidateProperties ν velocity pressure force support

/-- A global smooth solution with uniformly bounded kinetic energy for the
given viscosity and the given force, starting from the same zero datum.

There are no support, periodicity, pressure-growth, derivative-growth, or energy
inequality assumptions on a competitor. The square-integrability requirement
and its uniform energy bound use all of R³ and all nonnegative times. -/
structure GlobalFiniteEnergySolution (ν : ℝ) (f : VelocityField) where
  velocity : VelocityField
  pressure : PressureField
  velocity_smooth : ContDiffOn ℝ ∞ velocity futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ pressure futureDomain
  zero_initial_velocity : ∀ x : Space, velocity (0, x) = 0
  divergence_free : ∀ t ∈ Ici (0 : ℝ), ∀ x : Space,
    NavierStokes.ProblemStatement.spatialDivergence velocity t x = 0
  navier_stokes : ∀ t ∈ Ioi (0 : ℝ), ∀ x : Space,
    navierStokesResidual ν velocity pressure t x = f (t, x)
  energy_bounded : UniformFiniteEnergy (Ici 0) velocity

/-- The primary existence assertion at one fixed viscosity. -/
def candidateStatement (ν : ℝ) : Prop :=
  ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
    CandidateProperties ν u p f K

/-- The primary existence assertion for every positive viscosity. -/
def coreBreakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → candidateStatement ν

/-- The full assertion of Theorem 1.1: at every positive viscosity there is a
candidate whose same prescribed force and zero datum have no global smooth
solution with uniformly bounded kinetic energy. This is a target proposition,
not an asserted theorem. -/
def breakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalFiniteEnergySolution ν f)

/-- Bundling the witnesses in `Candidate` does not change any hypothesis of
the explicit primary existence assertion. -/
theorem candidateStatement_iff_nonempty (ν : ℝ) :
    candidateStatement ν ↔ Nonempty (Candidate ν) := by
  constructor
  · rintro ⟨u, p, f, K, h⟩
    exact ⟨⟨u, p, f, K, h⟩⟩
  · rintro ⟨c⟩
    exact ⟨c.velocity, c.pressure, c.force, c.support, c.properties⟩

/-- The unit-viscosity residual is exactly the existing differential expression. -/
@[simp] theorem residual_at_viscosity_one (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) :
    navierStokesResidual 1 u p t x =
      NavierStokes.ProblemStatement.navierStokesResidual u p t x := by
  simp [navierStokesResidual, NavierStokes.ProblemStatement.navierStokesResidual]

/-- The support convention really excludes forcing at every nonpositive time. -/
theorem CompactPositiveTimeSupport.eq_zero_of_nonpos {f : VelocityField}
    (hf : CompactPositiveTimeSupport f) {t : ℝ} (ht : t ≤ 0) (x : Space) :
    f (t, x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact (not_lt_of_ge ht) (hf.2 h).1

/-- Restricting the set of times preserves the same energy bound. -/
theorem UniformFiniteEnergy.mono {times shorter : Set ℝ} {u : VelocityField}
    (hu : UniformFiniteEnergy times u) (hsub : shorter ⊆ times) :
    UniformFiniteEnergy shorter u := by
  obtain ⟨E, hE, hu⟩ := hu
  exact ⟨E, hE, fun t ht => hu t (hsub ht)⟩

/-- Zero velocity and pressure solve the equation for zero force at any
viscosity. This checks that the competing-solution class is inhabited. -/
theorem zero_force_has_global_solution (ν : ℝ) :
    Nonempty (GlobalFiniteEnergySolution ν (fun _ => 0)) := by
  refine ⟨{
    velocity := fun _ => 0
    pressure := fun _ => 0
    velocity_smooth := contDiff_const.contDiffOn
    pressure_smooth := contDiff_const.contDiffOn
    zero_initial_velocity := fun _ => rfl
    divergence_free := ?_
    navier_stokes := ?_
    energy_bounded := ?_
  }⟩
  · intro t ht x
    simp [NavierStokes.ProblemStatement.spatialDivergence,
      NavierStokes.ProblemStatement.spatialDerivative]
  · intro t ht x
    simp [navierStokesResidual, NavierStokes.ProblemStatement.temporalDerivative,
      NavierStokes.ProblemStatement.advection,
      NavierStokes.ProblemStatement.spatialLaplacian,
      NavierStokes.ProblemStatement.spatialDerivative,
      NavierStokes.ProblemStatement.pressureGradient]
  · refine ⟨0, le_refl 0, ?_⟩
    intro t ht
    constructor
    · simp [SquareIntegrableAtTime]
    · simp [kineticEnergy]

/-- The full target contains the primary candidate-existence target. -/
theorem breakdown_implies_core (h : breakdownStatement) : coreBreakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, _⟩ := h ν hν
  exact ⟨u, p, f, K, hc⟩

end NavierStokesR3.ProblemStatement

################ NavierStokes/R3/Theorem.lean (81 lines)
import NavierStokes.R3.ActualCandidate
import NavierStokes.R3.CandidateBreakdown
import NavierStokes.R3.ViscosityScaling
import NavierStokes.R3.IntegratedDissipation

/-!
# Theorem 1.1: unconditional whole-space forced Navier–Stokes blowup

The actual selected construction supplies the viscosity-one fields. Spatial
rescaling gives every positive viscosity while retaining singular time one,
compact support in strictly positive time for the force, and one kinetic-energy
bound for all times before the singularity. Whole-space comparison excludes a
global smooth finite-energy solution with the same prescribed force and datum.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokesR3

open ProblemStatement ViscosityScaling

/-- The full paper conclusion, together with the initial time interval on
which the constructed velocity is at rest. No construction hypotheses remain. -/
theorem theorem_1_1_with_initial_rest (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space,
        u (t, x) = 0 ∧ p (t, x) = 0 := by
  obtain ⟨u, p, f, K, hc, hzero⟩ := ActualCandidate.selected_candidate_one_with_initial_rest
  refine ⟨scaledVelocity ν u, scaledPressure ν p, scaledVelocity ν f,
    (fun x : Space => Real.sqrt ν • x) '' K, candidate_at_viscosity hc hν, ?_, ?_⟩
  · rintro ⟨v⟩
    exact hc.no_global_solution_one ⟨normalized_global_solution hν v⟩
  · intro t ht x
    constructor
    · change Real.sqrt ν • u (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).1, smul_zero]
    · change ν • p (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).2, smul_zero]

/-- Theorem 1.1, with all properties of the same velocity, pressure, force,
and compact support witnessed simultaneously, for every positive viscosity. -/
theorem theorem_1_1 : ProblemStatement.breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hg, _⟩ := theorem_1_1_with_initial_rest ν hν
  exact ⟨u, p, f, K, hc, hg⟩

/-- The primary whole-space candidate-existence assertion at any positive viscosity. -/
theorem candidateStatement (ν : ℝ) (hν : 0 < ν) :
    ProblemStatement.candidateStatement ν := by
  obtain ⟨u, p, f, K, hc, _⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc⟩

/-- The candidate construction is unconditional for every positive viscosity. -/
theorem coreBreakdownStatement : ProblemStatement.coreBreakdownStatement :=
  candidateStatement

/-- The whole-space breakdown assertion is an unconditional theorem. -/
theorem breakdownStatement : ProblemStatement.breakdownStatement := theorem_1_1

/-- Theorem 1.1 and all energy conclusions of Lemma 10.4 hold for the same
constructed fields. Total dissipation is explicitly integrable up to time one. -/
theorem theorem_1_1_with_dissipation (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      IntervalIntegrable (CompactEnergy.l2Norm f) volume 0 1 ∧
      IntegrableOn (CompactEnergy.dissipation u) (Ico (0 : ℝ) 1) ∧
      (∀ T ∈ Ico (0 : ℝ) 1,
        CompactEnergy.l2Sq u T +
          2 * ν * (∫ t in (0 : ℝ)..T, CompactEnergy.dissipation u t) ≤
            (CompactEnergy.cumulativeForceNorm f T) ^ 2) ∧
      2 * ν * (∫ t in Ico (0 : ℝ) 1, CompactEnergy.dissipation u t) ≤
        (CompactEnergy.cumulativeForceNorm f 1) ^ 2 := by
  obtain ⟨u, p, f, K, hc, hg⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, CompactEnergy.candidate_energy_estimates hν hc⟩

end NavierStokesR3

################ NavierStokes/PeriodicPaperTheorem.lean (164 lines)
import NavierStokes.PeriodicPaperSupport
import NavierStokes.PeriodicPaperScalingSupport
import NavierStokes.R3.ParabolicScaling
import NavierStokes.R3.Theorem
import NavierStokes.PeriodizePDE
import NavierStokes.PeriodicViscosity
import NavierStokes.CandidateConsequences

/-!
# The full periodic corollary of the paper

The torus is represented by spatially periodic lifts to R³. The support
clauses intersect topological support with the closed fundamental cube:
they do not assert compact support of a nonzero periodic lift on all of R³.
-/

noncomputable section

namespace NavierStokes.PeriodicPaper

open ProblemStatement PeriodicLocalization Set
open scoped ContDiff

/-- The same velocity, pressure, and force satisfy every assertion of the
periodic corollary before its singular time, which is exactly one. -/
structure CandidateProperties (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  force_smooth : ContDiff ℝ ∞ f
  velocity_periodic : UnitSpatialPeriodsOn (Ico 0 1) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico 0 1) p
  force_periodic : UnitSpatialPeriodsOn (Ici 0) f
  support_compact : IsCompact K
  support_interior : K ⊆ fundamentalInterior
  velocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => u (t, x)) ∩ fundamentalCube ⊆ K
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => p (t, x)) ∩ fundamentalCube ⊆ K
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  force_time_support : CompactFutureTimeSupport f
  force_zero_nonpos : ∀ t ≤ (0 : ℝ), ∀ x : Space, f (t, x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)
  speed_unbounded : SpeedUnboundedAtOne u

/-- A global smooth periodic competitor for precisely the prescribed force
and zero initial datum. No energy or pressure normalization is required. -/
structure GlobalSmoothSolution (ν : ℝ) (f : VelocityField) where
  velocity : VelocityField
  pressure : PressureField
  velocity_smooth : ContDiffOn ℝ ∞ velocity futureDomain
  pressure_smooth : ContDiffOn ℝ ∞ pressure futureDomain
  velocity_periodic : UnitSpatialPeriodsOn (Ici 0) velocity
  pressure_periodic : UnitSpatialPeriodsOn (Ici 0) pressure
  zero_initial_velocity : ∀ x : Space, velocity (0, x) = 0
  divergence_free : ∀ t ∈ Ici (0 : ℝ), ∀ x : Space,
    spatialDivergence velocity t x = 0
  navier_stokes : ∀ t ∈ Ioi (0 : ℝ), ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)

/-- Every periodic candidate excludes a global smooth periodic competitor. -/
theorem CandidateProperties.no_global_solution {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (h : CandidateProperties ν u p f K)
    (hν : 0 < ν) : ¬ Nonempty (GlobalSmoothSolution ν f) := by
  rintro ⟨v⟩
  exact PeriodicViscosity.excludes_global_solution hν
    h.velocity_smooth h.pressure_smooth h.velocity_periodic h.pressure_periodic
    h.zero_initial_velocity h.divergence_free h.navier_stokes h.speed_unbounded
    v.velocity_smooth v.pressure_smooth v.velocity_periodic v.pressure_periodic
    v.zero_initial_velocity v.divergence_free v.navier_stokes

/-- Every order of the ordinary spacetime derivative of the prescribed force
has arbitrary polynomial decay, as asserted in the periodic corollary proof. -/
theorem CandidateProperties.force_derivative_decay {ν : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space} (h : CandidateProperties ν u p f K)
    (m : ℕ) (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ C * (1 + t) ^ (-N) := by
  obtain ⟨C, hC, hbound⟩ := CandidateConsequences.futureJet_decay
    h.force_smooth.contDiffOn h.force_periodic h.force_time_support m N hN
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [← CandidateConsequences.futureJet_eq_full ht x m h.force_smooth.contDiffAt]
  exact hbound t ht x

/-- Periodize a compact whole-space candidate after its supports have been
compressed into the central quarter cube. The arbitrary post-one extensions
are discarded before forming the lattice sum. -/
theorem of_compact_candidate {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (h : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hK : K ⊆ fundamentalInterior)
    (hu : ∀ t < (1 : ℝ), ∀ x : Space, u (t, x) ≠ 0 → ∀ i, |x i| ≤ 1 / 4)
    (hp : ∀ t < (1 : ℝ), ∀ x : Space, p (t, x) ≠ 0 → ∀ i, |x i| ≤ 1 / 4)
    (hf : SupportedInCube (1 / 4) f) :
    CandidateProperties ν (periodize (beforeOne u)) (periodize (beforeOne p))
      (periodize f) K := by
  have hsu := beforeOne_supported hu
  have hsp := beforeOne_supported hp
  have hr : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  refine {
    velocity_smooth := contDiffOn_periodize hsu (beforeOne_smooth h.velocity_smooth)
    pressure_smooth := contDiffOn_periodize hsp (beforeOne_smooth h.pressure_smooth)
    force_smooth := contDiff_periodize hf h.force_smooth
    velocity_periodic := unitSpatialPeriodsOn_periodize _ _
    pressure_periodic := unitSpatialPeriodsOn_periodize _ _
    force_periodic := unitSpatialPeriodsOn_periodize _ _
    support_compact := h.support_compact
    support_interior := hK
    velocity_support := ?_
    pressure_support := ?_
    zero_initial_velocity := ?_
    force_time_support := compactFutureTimeSupport_periodize
      (compactFutureTimeSupport_of_hasCompactSupport h.force_support.1)
    force_zero_nonpos := ?_
    divergence_free := ?_
    navier_stokes := ?_
    speed_unbounded := speedUnbounded_periodize hsu hr
      (speedUnbounded_beforeOne h.speed_unbounded)
  }
  · intro t ht
    apply periodize_tsupport_on_fundamentalCube hsu hr
    simpa only [beforeOne, ht.2, ite_eq_left] using h.velocity_support t ht
  · intro t ht
    apply periodize_tsupport_on_fundamentalCube hsp hr
    simpa only [beforeOne, ht.2, ite_eq_left] using h.pressure_support t ht
  · intro x
    apply periodize_eq_zero_of_timeSlice
    intro y
    rw [beforeOne_eq u (by norm_num : (0 : ℝ) < 1)]
    exact h.zero_initial_velocity y
  · intro t ht x
    exact periodize_eq_zero_of_timeSlice (h.force_support.eq_zero_of_nonpos ht) x
  · apply divergence_free_periodize hsu hr
    intro t ht x
    rw [spatialDivergence_congr (beforeOne_eventuallyEq u (z := (t, x)) ht.2)]
    exact h.divergence_free t ht x
  · apply navier_stokes_periodize hsu hsp hf hr
    intro t ht x
    rw [residual_viscosity_congr ν (beforeOne_eventuallyEq u (z := (t, x)) ht.2)
      (beforeOne_eventuallyEq p (z := (t, x)) ht.2)]
    exact h.navier_stokes t ht x

/-- The full quantified periodic corollary, including support in the interior
of the fundamental cube and absence of a global smooth periodic solution. -/
def breakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ u : VelocityField, ∃ p : PressureField,
    ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalSmoothSolution ν f)

/-- The full periodic corollary is unconditional for every positive
viscosity. The affine parabolic clock preserves singular time exactly one. -/
theorem periodic_corollary : breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, _, hrest⟩ :=
    NavierStokesR3.theorem_1_1_with_initial_rest ν hν
  obtain ⟨l, hl, hK, hu, hp, hf⟩ := exists_compression_scale hc
  have hcompressed := NavierStokesR3.ParabolicScaling.compressedCandidate hc hrest hl
  have hperiodic := of_compact_candidate hcompressed hK hu hp hf
  exact ⟨_, _, _, _, hperiodic, hperiodic.no_global_solution hν⟩

end NavierStokes.PeriodicPaper

################ NavierStokes/LocalAngularGrowth.lean (251 lines)
import NavierStokes.R3.ActualCandidate
import NavierStokes.ActualExteriorPrefix
import NavierStokes.BaseAngularGrowth

/-!
# Angular growth of the selected solution in the inner core

All correction stages vanish on the inner complement of the active annulus.
Consequently the actual diagonal solution retains the slow base's quantitative
angular asymptotic along an inward-moving radial ray.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.LocalAngularGrowth

open ProblemStatement CorrectionInitialization

def rawVelocity (A D : ℕ → VelocityField) (a : ℕ → ℝ) : VelocityField :=
  MixedPeriodicAssembly.velocity
    (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) A)
    (SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) D)

/-- On either component of the complement of the correction annulus, the
whole diagonal velocity agrees with the same actual slow base once the
zeroth cutoff is on its plateau. -/
theorem rawVelocity_eq_base {B Nr : ℕ} {A D : ℕ → VelocityField}
    {P : ℕ → PressureField} (H : ActualExteriorPrefix.ExteriorStages B Nr A D P)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain Nr)
    (hsmall : |a 0 * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    rawVelocity A D a w =
      FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B w := by
  have ht := hw.1.1
  have hq := (PhysicalWaveSum.physicalQ_smoothAt
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half ht).continuousAt
  have hpos := PhysicalWaveSum.physicalQ_pos
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half ht
  have hzero : ∀ j : ℕ, j ≠ 0 → A j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact ActualExteriorPrefix.eqOn_exterior_germ (H.potential_succ k) hw
  have hcurl := AxisPreservation.velocitySum_eq_first ha hq hpos hzero hsmall
  have hbase := SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq
    (ActualExteriorPrefix.eqOn_exterior_germ H.potential_zero hw)
  have hD : SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) D w = 0 := by
    have hz (j : ℕ) : D j w = 0 := H.direct_zero j hw
    simp only [SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage, hz,
      smul_zero, tsum_zero]
  change SolenoidalDiagonal.velocitySum a (PhysicalWaveSum.physicalQ ActualPrimary.h) A w +
    SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ ActualPrimary.h) D w = _
  rw [hD, add_zero, hcurl, hbase]
  exact TailGaugePotential.finalPotential_sameCurl ActualPrimary.certificate
    ActualPrimary.modulation ActualPrimary.upper B ht

theorem localized_eq_raw {A D : VelocityField} {t : ℝ} (ht : 3 / 4 ≤ t)
    {x : Space} (hx : x ∈ SpatialLocalization.plateau) :
    R3CompactCandidate.velocity A D (t, x) = MixedPeriodicAssembly.velocity A D (t, x) := by
  rw [R3CompactCandidate.velocity, TimeLocalization.activatedVelocity_eq_late _ ht]
  have hA := SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq
    (SpatialLocalization.cutPotential_eventuallyEq A (z := (t, x)) hx)
  have hD := (SpatialLocalization.cutPotential_eventuallyEq D (z := (t, x)) hx).self_of_nhds
  change SpatialCurl.spatialCurl (SpatialLocalization.cutPotential A) (t, x) +
    SpatialLocalization.cutPotential D (t, x) = SpatialCurl.spatialCurl A (t, x) + D (t, x)
  rw [hA, hD]

def innerRadius : ℝ := NominalConeAssembly.activeLeft ActualPrimary.nominal / 2

theorem innerRadius_pos : 0 < innerRadius :=
  half_pos (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal)

theorem innerRadius_lt_left : innerRadius < NominalConeAssembly.activeLeft ActualPrimary.nominal :=
  half_lt_self (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal)

/-- One positive time interval satisfies every cutoff and correction-support
condition needed along the fixed inner ray. -/
theorem exists_ray_interval (a : ℕ → ℝ) (Nr : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ < δ →
      (1 - τ, BaseAngularGrowth.ray innerRadius τ) ∈ ActualExteriorPrefix.exteriorDomain Nr ∧
      |a 0 * PhysicalWaveSum.physicalQ ActualPrimary.h
        (1 - τ, BaseAngularGrowth.ray innerRadius τ)| < 1 / 2 ∧
      3 / 4 ≤ 1 - τ ∧ BaseAngularGrowth.ray innerRadius τ ∈ SpatialLocalization.plateau := by
  let δ : ℝ := min (1 / 8) (min (ChartScales.Q Nr)
    (min ((1 / 2) / (|a 0| + 1)) ((1 / 32) / (2 * innerRadius + 1))))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by norm_num) (lt_min (ChartScales.Q_pos Nr)
      (lt_min (div_pos (by norm_num) (by positivity))
        (div_pos (by norm_num) (by linarith [innerRadius_pos]))))
  have hδt : δ ≤ 1 / 8 := min_le_left _ _
  have hδq : δ ≤ ChartScales.Q Nr := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ ≤ (1 / 2) / (|a 0| + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδx : δ ≤ (1 / 32) / (2 * innerRadius + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, hδt.trans (by norm_num), ?_⟩
  intro τ hτ hτδ
  have hq : PhysicalWaveSum.physicalQ ActualPrimary.h
      (1 - τ, BaseAngularGrowth.ray innerRadius τ) = τ :=
    BaseAngularGrowth.physicalQ_ray ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hτ
  have hchart := BaseAngularGrowth.cartesianChart_ray ActualPrimary.outgoing.data.h_pos
    ActualPrimary.outgoing.data.h_lt_half innerRadius_pos.le hτ
  have ht : τ < 1 / 8 := hτδ.trans_le hδt
  have haτ : τ * (|a 0| + 1) < 1 / 2 :=
    (lt_div_iff₀ (by positivity)).mp (hτδ.trans_le hδa)
  have hxτ : τ * (2 * innerRadius + 1) < 1 / 32 :=
    (lt_div_iff₀ (by linarith [innerRadius_pos])).mp (hτδ.trans_le hδx)
  refine ⟨?_, ?_, by linarith, ?_⟩
  · apply ActualExteriorPrefix.mem_exteriorDomain.mpr
    refine ⟨by change 1 - τ < 1; linarith, ?_, ?_⟩
    · rw [hq]
      exact hτδ.trans_le hδq
    · intro hactive
      change (SlowBorelBase.cartesianChart ActualPrimary.h
        (1 - τ, BaseAngularGrowth.ray innerRadius τ)).2.1 ∈
          Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
            (NominalConeAssembly.activeRight ActualPrimary.nominal) at hactive
      rw [hchart] at hactive
      exact (not_le_of_gt innerRadius_lt_left) hactive.1
  · rw [hq, abs_mul, abs_of_pos hτ]
    nlinarith
  · change SpatialLocalization.radialSquare (BaseAngularGrowth.ray innerRadius τ) < 1 / 32 ∧
      |BaseAngularGrowth.ray innerRadius τ 2| < 1 / 8
    constructor
    · simp only [SpatialLocalization.radialSquare, BaseAngularGrowth.ray_apply_zero,
        BaseAngularGrowth.ray_apply_one, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, add_zero]
      rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) innerRadius_pos.le) hτ.le)]
      nlinarith
    · simp only [BaseAngularGrowth.ray_apply_two, abs_zero]
      norm_num

def selectedPotential (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
    (PhysicalWaveSum.physicalQ ActualPrimary.h) ActualCandidateAssembly.selectedPotentialStages

def selectedDirect (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
    (PhysicalWaveSum.physicalQ ActualPrimary.h) ActualCandidateAssembly.selectedDirectStages

def selectedVelocity (a : ℕ → ℕ) : VelocityField :=
  R3CompactCandidate.velocity (selectedPotential a) (selectedDirect a)

theorem selectedVelocity_eq_base_on_ray {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ < δ →
      selectedVelocity a (1 - τ, BaseAngularGrowth.ray innerRadius τ) =
        FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper ActualCandidateConstruction.selectedBudget
          (1 - τ, BaseAngularGrowth.ray innerRadius τ) := by
  obtain ⟨δ, hδ, hδ1, hconditions⟩ := exists_ray_interval (fun j => (a j : ℝ))
    (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro τ hτ hτδ
  obtain ⟨hw, hsmall, ht, hx⟩ := hconditions τ hτ hτδ
  rw [selectedVelocity, localized_eq_raw ht hx]
  exact rawVelocity_eq_base
    (ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    ha hw hsmall

theorem innerRadius_le_boxRadius : innerRadius ≤
    FinalSlowBase.boxRadius ActualPrimary.nominal ActualPrimary.upper := by
  have hord : NominalConeAssembly.activeLeft ActualPrimary.nominal <
      NominalConeAssembly.activeRight ActualPrimary.nominal :=
    (Real.log_lt_log_iff (NominalConeAssembly.activeLeft_pos ActualPrimary.nominal)
      (FinalSlowBase.terminal_pos ActualPrimary.nominal)).mp
      (LeadingStressWeights.edges_ordered ActualPrimary.nominal)
  exact innerRadius_lt_left.le.trans (hord.le.trans (le_max_right _ _))

/-- The error form of `uθ = τ⁻ᴬ (e₀ + O(τ^(2h)))` at one fixed radius
in the inner core. The exponent, radius and coefficient are
the ones belonging to the actual selected profile. -/
def AngularGrowth (u : VelocityField) : Prop :=
  ∃ e₀ C δ : ℝ, 0 < e₀ ∧ 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧
    ∀ τ : ℝ, 0 < τ → τ < δ →
      |τ ^ CoordinateAlgebra.A ActualPrimary.h *
        u (1 - τ, BaseAngularGrowth.ray innerRadius τ) 1 - e₀| ≤
          C * τ ^ (2 * ActualPrimary.h)

/-- The selected local velocity before the spatial and initial-time cutoffs. -/
def selectedRawVelocity (a : ℕ → ℕ) : VelocityField :=
  MixedPeriodicAssembly.velocity (selectedPotential a) (selectedDirect a)

/-- The quantitative angular estimate already holds for the local fields. -/
theorem selectedRawVelocity_angularGrowth {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) :
    AngularGrowth (selectedRawVelocity a) := by
  obtain ⟨δ, hδ, hδ1, hconditions⟩ := exists_ray_interval (fun j => (a j : ℝ))
    (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
  obtain ⟨C, hC, hb⟩ := BaseAngularGrowth.normalized_velocity_ray_bound
    ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
    ActualCandidateConstruction.selectedBudget innerRadius_pos innerRadius_le_boxRadius
  refine ⟨BaseAngularGrowth.leadingAmplitude ActualPrimary.modulation innerRadius, C, δ,
    BaseAngularGrowth.leadingAmplitude_pos ActualPrimary.modulation innerRadius_pos,
    hC, hδ, hδ1, ?_⟩
  intro τ hτ hτδ
  obtain ⟨hw, hsmall, _, _⟩ := hconditions τ hτ hτδ
  have heq : selectedRawVelocity a (1 - τ, BaseAngularGrowth.ray innerRadius τ) =
      FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper ActualCandidateConstruction.selectedBudget
        (1 - τ, BaseAngularGrowth.ray innerRadius τ) :=
    rawVelocity_eq_base
      (ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
      ha hw hsmall
  rw [heq]
  exact hb τ hτ (hτδ.le.trans hδ1)

theorem selectedVelocity_angularGrowth {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) : AngularGrowth (selectedVelocity a) := by
  obtain ⟨δ, hδ, hδ1, heq⟩ := selectedVelocity_eq_base_on_ray ha
  obtain ⟨C, hC, hb⟩ := BaseAngularGrowth.normalized_velocity_ray_bound
    ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
    ActualCandidateConstruction.selectedBudget innerRadius_pos innerRadius_le_boxRadius
  refine ⟨BaseAngularGrowth.leadingAmplitude ActualPrimary.modulation innerRadius, C, δ,
    BaseAngularGrowth.leadingAmplitude_pos ActualPrimary.modulation innerRadius_pos,
    hC, hδ, hδ1, ?_⟩
  intro τ hτ hτδ
  rw [heq τ hτ hτδ]
  exact hb τ hτ (hτδ.le.trans hδ1)

theorem selected_exponent_small : 0 < ActualPrimary.h ∧ ActualPrimary.h < 1 / 100 := by
  refine ⟨ActualPrimary.outgoing.data.h_pos, ?_⟩
  have hsmall := ActualPrimary.nominal.axis.small.h_le
  linarith

/-- A single unconditional selected whole-space candidate has every
Theorem 1.1 property and the local theorem's quantitative angular growth.
Both velocity and pressure also retain their initial rest interval. -/
theorem selected_candidate_one_with_angular_growth :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      NavierStokesR3.ProblemStatement.CandidateProperties 1 u p f K ∧
      AngularGrowth u ∧
      (∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0) := by
  obtain ⟨a, hs, ea, eb, ep, forcing, hc, hf, _⟩ := ActualCandidateAssembly.selected_witness
  have ha : Tendsto (fun j => (a j : ℝ)) atTop atTop := hs.2.2.2.2.1
  refine ⟨_, _, _, _, NavierStokesR3.ActualCandidate.of_localized_fields hc hf,
    selectedVelocity_angularGrowth ha, ?_⟩
  intro t ht x
  exact ⟨TimeLocalization.activatedVelocity_zero_early _ ht x,
    TimeLocalization.activatedPressure_zero_early _ ht x⟩

end NavierStokes.LocalAngularGrowth

################ NavierStokes/LocalPaperHeat.lean (74 lines)
import NavierStokes.LocalPaperTheorem
import NavierStokes.LocalHeatFormula
import NavierStokes.LocalHeatPressure

/-!
# The local theorem's literal radial heat formulas

These consequences use the same fields and normalization as `local_theorem`.
They express the heat exterior in the manuscript's radius coordinate, including
the genuinely integrable pressure tail.
-/

noncomputable section

namespace NavierStokes.LocalPaper

open Set MeasureTheory ProblemStatement
open scoped ContDiff

variable {h qstar Xa Xext C : ℝ} {A D u : VelocityField} {p : PressureField}

theorem Properties.exterior_profile_smooth
    (hp : Properties h qstar Xa Xext C A D u p) :
    ContDiffOn ℝ ∞ (LocalHeatFormula.exteriorProfile C h) (Ici 0) :=
  LocalHeatFormula.exteriorProfile_smooth C hp.exponent_small.1

theorem Properties.exterior_profile_derivatives_bounded
    (hp : Properties h qstar Xa Xext C A D u p) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Ici (0 : ℝ),
      |iteratedDerivWithin n (LocalHeatFormula.exteriorProfile C h) (Ici 0) y| ≤ M :=
  LocalHeatFormula.exteriorProfile_all_derivatives_bounded C hp.exponent_small.1 n

/-- The exterior angular magnitude is exactly `r^(-1-2h) H_ext(τ/r²)`. -/
theorem Properties.exterior_amplitude_formula
    (_hp : Properties h qstar Xa Xext C A D u p) (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    LocalHeatFormula.amplitude C h τ r =
      r ^ (-1 - 2 * h) * LocalHeatFormula.exteriorProfile C h (τ / r ^ 2) :=
  LocalHeatFormula.amplitude_formula C h τ hr

theorem Properties.exterior_heat_equation
    (hp : Properties h qstar Xa Xext C A D u p) {τ r : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) :
    -deriv (fun τ => LocalHeatFormula.amplitude C h τ r) τ =
      iteratedDeriv 2 (LocalHeatFormula.amplitude C h τ) r +
        deriv (LocalHeatFormula.amplitude C h τ) r / r -
        LocalHeatFormula.amplitude C h τ r / r ^ 2 :=
  LocalHeatFormula.amplitude_heat_equation C hp.exponent_small.1 hτ hr

/-- The same exterior direct field is `K eθ`, and its pressure is the
literal radius integral `-∫ K²/ρ`; the integrability assertion is explicit. -/
theorem Properties.exterior_radial_form
    (hp : Properties h qstar Xa Xext C A D u p) {w : SpaceTime}
    (ht : w.1 < 1) (hq : PhysicalWaveSum.physicalQ h w < qstar)
    (hX : Xext ≤ AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w) :
    let r := Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2)
    0 < r ∧
      D w = (LocalHeatFormula.amplitude C h (1 - w.1) r / r) • BaseResidual.angularVector w ∧
      p w = -(∫ ρ in Ioi r, LocalHeatFormula.amplitude C h (1 - w.1) ρ ^ 2 / ρ) ∧
      IntegrableOn (fun ρ => LocalHeatFormula.amplitude C h (1 - w.1) ρ ^ 2 / ρ) (Ioi r) := by
  have hh1 : h < 1 / 2 := by linarith [hp.exponent_small.2]
  have hq0 := PhysicalWaveSum.physicalQ_pos hp.exponent_small.1 hh1 ht
  have hXe : 0 < Xext := hp.edges_ordered.1.trans hp.edges_ordered.2
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 :=
    (mul_pos hXe hq0).trans_le ((le_div_iff₀ hq0).mp hX)
  have hr : 0 < Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2) := by positivity
  obtain ⟨_, hD, hP, _⟩ := hp.exterior w ht hq hX
  refine ⟨hr, hD.trans (LocalHeatFormula.heatVelocity_formula C h hs), ?_, ?_⟩
  · rw [hP]
    have he := LocalHeatPressure.heatPressure_radius_integral C h w.1 (w.2 2) hr
    rw [TerminalStress.radiusPoint_profilePoint hs.le] at he
    exact he
  · exact LocalHeatPressure.heatAmplitude_sq_div_integrable C hp.exponent_small.1 hh1 ht hr

end NavierStokes.LocalPaper

################ NavierStokes/ComparatorSolution.lean (32 lines)
import NavierStokes.ComparatorR3Theorem
import NavierStokes.ComparatorTheorem

/-!
# Navier–Stokes Comparator submission: options (C) and (D)

Expose the project's proof adapters under the reference theorem names.
The adapters import `ComparatorDefinitions`, never the challenge module.
-/

namespace NavierStokes.Comparator

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu

/-- (D) Breakdown of Navier–Stokes solutions on ℝ³/ℤ³. -/
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_periodic nu hnu

end NavierStokes.Comparator

#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic

