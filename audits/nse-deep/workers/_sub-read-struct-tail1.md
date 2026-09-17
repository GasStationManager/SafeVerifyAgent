# Worker _sub-read-struct-tail1 -- structural tail (READ-ONLY, NSE @ f9e8bc5)

## 1. Euler/ParentParticleInverse.lean (100 lines, 13 decls) -- CLEAN
Declares `structure ParticleInverse (A : Parent)` (`:17-21`: field/left_inverse/right_inverse/continuous).
CLOSURE-WITH-BASE-CASE: the two closure defs `ParticleInverse.restrictTime` (`:82`) and
`ParticleInverse.child` (`:90`) both consume an `I : ParticleInverse A` and produce another, so alone they
supply nothing -- BUT genuine base constructors exist outside the file:
`Euler/BaseEulerInput.lean:37 solutionInverse` (from `(...).particleInverse`),
`Euler/BaseStaticEuler.lean:109 baseInverse`, `Euler/BaseEulerParent.lean:119`, and
`Euler/BaseEulerState.lean:41 initialInverse`. So NOT an unsupplied hypothesis.
Junk-value sweep: the only inverses are `A.ell⁻¹` (`:33,:36`) inside `packetPosition_contDiff`, a pure
rewrite of `A.packetPosition_apply` -- it is an equality of the *definition* to itself, and `Parent.ell` is
positive by the Parent structure anyway; no unguarded division in any statement.
KERNEL RISK: none -- no inductive/rec/termination_by/deriving/decide/Fin; largest numeral = `80` in the
adjacent `k^80` callers, in-file largest numeral is `1` (`:92 hnext1`). OK.
Note (minor, not a defect): `field_initial` (`:49`) is the only theorem here that is not `include I` because
`I` is in its statement.
VERDICT: 13 decls read, OK 13 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 2. Euler/TransversePacketForcing.lean (108 lines, 15 decls) -- OK, one NOTE
Declares `structure Forcing (D : Data U) (raw : VectorField)` (`:25-31`) and
`structure InitialData (D : Data U)` (`:33-36`), plus `InitialData.zero` (`:38`), 4 abbrevs (`:65-76`) and
5 theorems (`:78-104`) that only re-export `EulerSourceCylinderEquation` lemmas.
BOTH structures ARE constructed, and non-degenerately, so no unsupplied hypothesis and no
only-degenerate-witness problem:
 * `Forcing`: degenerate witness `Euler/TransversePacketPrimaryMatching.lean:25 zeroForcing` (raw = 0) BUT
   live non-degenerate ones exist: `Euler/PacketJoinedSourceProfiles.lean:31 joinedSource_meanForcing`,
   `Euler/PacketSourceProfiles.lean:30/35`, `Euler/PacketConstructedProfiles.lean:32/38`,
   `Euler/PacketProfilesRegularity.lean:49/58`, plus closure ops
   (`TransversePacketHomogeneity.lean:23 smul`, `TransversePacketIntervalForcing.lean:27 initial`).
 * `InitialData`: degenerate witness is the in-file `.zero` (`:38-43`, `value := 0`); non-degenerate
   alternatives `Euler/PacketTerminalInitialData.lean:20 initialData`,
   `Euler/TransversePacketEndpoint.lean:108 terminalInitial`,
   `Euler/TransversePacketPrimaryMatching.lean:36 endpointData` / `:41 forwardInitial`,
   `Euler/TransversePacketLocalHistory.lean:22`.
NOTE (`:29 raw_eq`): `Forcing` is an EXACT identification of the prescribed `raw` with `pointField ...`, so
`Forcing P D raw` is essentially a proposition about `raw`; downstream files therefore use
`Nonempty (Forcing P D raw)` (e.g. `Euler/PacketJoinedSourceEquations.lean:86,104`,
`Euler/TransversePacketProvider.lean:152`) and `TransversePacketJoinedProvider.lean:26 path_unique` shows the
witness is unique. Harmless, but it means these 5 theorems say nothing until a caller EXHIBITS the identity;
they do (see the meanForcing/highForcing defs above).
Junk-value sweep: ZERO `/` or `⁻¹` anywhere in the file. All positivity side-conditions the abbrevs feed
(`D.T_pos.le`, `D.frameLower_pos`, `D.normalLower_pos`) are FIELDS of `Data`, i.e. in-signature guards --
a useful positive control.
KERNEL RISK: none (no inductive/rec/termination_by/deriving/decide/Fin/metaprogramming). Largest numeral in
file: `2` (`:2`-side `hp : 2 ≤ p` is in callers; in-file max literal is `0`). OK.
VERDICT: 15 decls read, OK 14 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.
