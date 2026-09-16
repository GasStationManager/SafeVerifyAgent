## 1. NavierStokes/CopyAngularInvariance.lean

- 56 declarations read. **OK 56 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.** The two Prop-valued definitions are direct translation predicates (`Invariant` at lines 23–24 and `AffinePhase` at lines 26–27), and `TangentInvariant` is a five-field conjunction at lines 201–206. No vacuous/empty-set shortcut or unsupplied structural hypothesis found. `TangentInvariant` is actually constructed by `angleTangent_invariant` at lines 669–680 (and used in `ParticularWaveAssembly.lean:619–640`); the downstream exact-conditions consumer is at lines 467–489 and 509–525. No large arithmetic, inductive/recursor, termination, or metaprogramming risk.

