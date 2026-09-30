# What we checked in qinz1yang/differential-geometry, and what we concluded

A plain-language summary of the audit of the Lean formalization published at
`github.com/qinz1yang/differential-geometry`, release v0.1.3 (commit `7a48598d`),
whose headline theorem is the Poincaré conjecture. The detailed report is
`2026-09-28-qinz1yang-differential-geometry.md` and its evidence is under
`dg-intake/`. The artifact was never modified.

The artifact is very large: 17,555 Lean files, 4.7 million lines, about
107,000 theorems, on Lean and Mathlib v4.33.1. Unlike the Navier–Stokes
audit, this is a bare claim: nobody else authored the statement, and no
Comparator run exists. That makes the statement check the first job, and it
means the community's own `#print axioms` and comparator runs remain the
final word on the kernel side.

## The headline

`poincare_conjecture`: a compact, Hausdorff, simply connected topological
3-manifold is homeomorphic to the 3-sphere. In Lean the manifold is a charted
space on ℝ³, which carries "without boundary" implicitly, and "connected" is
carried by simple connectivity. We wrote the reference statement before
reading the Lean and paired the two clause by clause: exact, with no
hypothesis stronger than the reference.

## What was checked

- **Trust surface.** Every one of the 28 `run_cmd` sites is an axiom
  tripwire that fails the build on a violation. There is no macro, elaborator
  or syntax extension, no `native_decide`, no unsafe or extern code. The 7,584
  option settings use six values, all elaboration-strength or cosmetic. No
  attribute, notation or instance can change what the kernel accepts, and none
  changes the meaning of anything in the headline statement.
- **The route, read as mathematics.** Five reading passes walked the proof
  from the headline to the analytic core: Moise's theorem that every compact
  topological 3-manifold is smoothable (the 1977 book proof, with the loop
  theorem tower and the §34 cell construction); the reduction of the smooth
  case to controlled extinction of Ricci flow with surgery; one surgery with
  its standard cap and volume debit; Hamilton–Ivey pinching through surgery,
  with the smallness of the surgery parameter traced to an explicit threshold;
  κ-noncollapsing through surgery by reduced volume, including the "barely
  avoiding surgery" argument; canonical neighbourhoods with constants
  quantified in the right order and proved by the standard compactness
  contradiction; extinction by Perelman's width argument with an explicit
  threshold; and the topological finish, where undoing surgeries gives a
  connected sum, Van Kampen gives a free product, and a trivial free product
  forces every summand to be S³. Every step read as the standard mathematics.
- **Named open results.** The repository's convention is to carry a missing
  result as a named hypothesis rather than a `sorry`. Since the headline takes
  no such hypotheses, that convention cannot hide a gap in it. On the route,
  every named predicate is discharged by a hypothesis-free theorem whose
  definition matches the literature statement. Four predicates are never
  discharged anywhere; all sit on a dead Cheeger–Gromov interface or an
  abandoned reduction and matter only to someone reusing them.
- **Vendored code.** Five of six vendored projects had statements changed,
  always by dropping hypotheses. The chain the route depends on, invariance of
  domain through Brouwer and sphere homology, was read natively and is the
  standard proof on Mathlib singular homology.
- **Junk values.** 290 scanner hits triaged; none is a reachable degenerate
  value a consumer relies on.
- **Independent checker.** con-leche, a checker written in Lean with its own
  term representation and a consistency theorem for its verified mode,
  accepted 50 of the artifact's theorems in 42 dependency-closed export
  streams: most of the README's advertised list and every proof the audit
  itself had leaned on, with the three standard axioms and nothing else. The
  headline itself was not among them because its full import closure could
  not be compiled here.

## Conclusions

**No defect found. No gap on the route. The statement is the Poincaré
conjecture, exactly.** Two things narrow the surgery theory as formalised
without affecting the headline: it is established only for simply connected
initial data, unlike Perelman's, and its constants are stated per initial
metric rather than uniformly. Both are recorded for anyone who wants to reuse
the intermediate theorems for geometrization. No docstrings exist on the
route, so the mapping to the literature rests on identifier names and on the
readers' reconstruction.

**What remains for the community.** `#print axioms` on the headline and a
comparator-style check, which need the whole closure compiled: about 14,200
modules whose compiled form is roughly 15 GB, more than the 16 GB machine used
here could hold in memory, so the last few hundred modules could not be
finished in reasonable time. A machine with 32 GB of RAM finishes it in a
day.

## Reports

| file | what |
|---|---|
| `2026-09-28-qinz1yang-differential-geometry.md` | the consolidated report |
| `dg-intake/STATEMENT.md`, `REFERENCE-poincare.md` | the statement rung |
| `dg-intake/TRUST.md` | trust surface and vendored modifications |
| `dg-intake/ROUTE-WALK*.md` | the five reading passes |
| `dg-intake/VENDORED-CHAIN.md` | the invariance-of-domain chain |
| `dg-intake/NOSUPPLIER.md`, `workers/nosupplier-verify-1.md` | named hypotheses |
| `dg-intake/JUNKVALUE-TRIAGE.md` | junk values |
| `dg-intake/CONLECHE.md` | the independent checker run |
