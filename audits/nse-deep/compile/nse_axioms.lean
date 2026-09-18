import NavierStokes.ComparatorSolution
import Euler.Solution

/-! Axiom provenance probe for the NSE deep audit.
    Run with:  cd <NSE> && lake env lean /tmp/nse_axioms.lean
    Kept OUTSIDE the artifact tree so the repository stays byte-identical. -/

#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
#print axioms Euler.euler_breakdown_R3
