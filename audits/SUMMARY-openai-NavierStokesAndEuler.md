# What we checked in openai/NavierStokesAndEuler, and what we concluded

A plain-language summary of five audit passes (15–20 September 2026) over the
Lean formalization published at `github.com/openai/NavierStokesAndEuler`, commit
`f9e8bc5`. The detailed reports are in this directory; this page is for a reader
who wants the conclusions without the ledgers.

The artifact is large: 2,659 Lean files, about 641,000 lines, 38,503 theorems.
It was never modified by us. It had already passed Comparator, an independent
checker that re-verifies the headline theorem against a statement the claimant
did not write. Our job was not to repeat that. It was to ask what Comparator
cannot ask.

## The two headline results

The repository claims two things, each as a Lean theorem checked by the kernel:

1. **Navier–Stokes blow-up.** There is a smooth, compactly supported force such
   that the 3D Navier–Stokes equations, started from rest, have no global smooth
   finite-energy solution. In the language of the Clay problem, this is the
   negative answer to alternatives (C) and (D).
2. **Euler blow-up**, the companion result.

## What was checked, in five passes

**Pass 1 (15 Sept): the statements.** Is the theorem Lean proved the theorem the
community would recognise as the Clay problem? We compared the challenge file
line by line against the independently authored statement in
google-deepmind/formal-conjectures. The only difference is the deletion of the two
existence alternatives OpenAI does not claim. No solution file imports the
challenge file, so the proof could not have redefined what it was proving. A
trust-surface scan over comment-stripped source found zero uses of the usual
escape hatches: no `native_decide`, no custom metaprogramming, no `unsafe`, no
axioms, and only the four intentional `sorry` placeholders in the challenge
templates.

**Pass 2 (16 Sept): kernel exposure.** Comparator trusts the Lean kernel. If the
kernel has a bug, which proofs here could exploit it? We enumerated the fragile
families: recursive inductive types (14, all read), well-founded recursion (12),
explicit recursors (5), `decide` on large numbers (210 sites, every literal at
most 1000), and the largest natural number the kernel ever evaluates (61 bits,
one machine word, never big-integer arithmetic). Every one of those sites was
classified by a reader. One surface stays unbounded: 1,176 proofs closed by
`rfl`, whose definitional-equality workload is invisible without a traced
compile.

**Pass 3 (18 Sept): compile-backed checks and reachability.** With a toolchain
installed, the sharpest open question was settled by compiling: 662 of 816
Navier–Stokes modules build with auto-bound implicits disabled, so no misspelled
identifier was silently bound as a free variable. Three hand-derived findings
were confirmed against the kernel. The pass also built a dependency cone from
the two headline theorems, and audited what lies inside it for statements that
say less than they appear to: predicates nobody ever constructs (46, carrying
463 hypothesis sites), closure operations with no base case (7), junk values
from division by zero and the like (127 triaged, 6 genuinely unguarded, all
property claims rather than exact values), and a non-degeneracy that is proved
once and then only propagated.

**Pass 4 (20 Sept): the paper.** Does each numbered lemma and proposition in the
166-page manuscript have a Lean counterpart, and is it as strong? Four
independent readers covered all 78 numbered statements. Every one has a Lean
counterpart. The headline theorem matches the paper clause by clause. Where Lean
and the paper differ, Lean is more often stronger. The genuine weakenings are
listed and none is used downstream.

**Pass 5 (20 Sept): the join.** The paper pass had checked statement against
statement without asking whether the Lean statement it found is one the
headline proof uses. Joining it against the dependency cone: 64 of the 172
cited counterparts are outside the cone. Re-reading those against the theorem
that actually carries each paper claim changed 29 of 64 verdicts.

## Conclusion about the headline result

**No defect found that could make either headline theorem false.** Nothing in
five passes contradicts Comparator's accept. The statement proved is the
community's statement. The proof uses no escape hatches, no metaprogramming and
no big-number kernel evaluation. The only residual kernel-trust surface is the
unbounded `rfl` workload, and the only unrun measurement is an independent
proof checker (Lean4Lean or nanoda) over a complete build, which the disk
budget did not allow. Both are compute, not reading.

The proof is also a proof of exactly what it says: starting from rest, with a
force compactly supported in space and time. Those two clauses are in the
paper's own statement of Theorem 1.1, not specialisations introduced in Lean.

## Conclusion about the intermediate theorems

This is where a user of the repository needs care. Someone who wants to reuse
an intermediate Lean theorem should know three things.

**1. It is not guaranteed to be non-vacuous.** The artifact contains 46
predicates and structures that appear as hypotheses at 463 places and are never
constructed anywhere. A theorem taking one of them is true but unreachable: no
one can ever supply its hypotheses, so it proves nothing about any concrete
object. There is also a family of closure lemmas with no base case, and several
identities that hold only because Lean's division-by-zero and similar junk
values cancel. None of this can make the headline false, because the headline
does not pass through it. But a reader who picks a theorem by name and trusts
it because the file compiled can pick one of these. The confirmed list is in
`nse-deep/FINDINGS.md` and the worker verdicts under `nse-deep/workers/`.

**2. It may correspond to a paper claim only in a display layer.** The
repository has a paper-facing layer: roughly thirty modules of theorems that
restate the manuscript's numbered results, imported by the top-level file
beside the Comparator solution rather than beneath it. Those theorems compile
and are true, but the headline proof never depends on them. In several places
the paper's full clause lives only there, while the theorem on the actual
proof route proves something weaker. The clearest cases:

- The all-order flatness of the linear-wave error (paper Proposition 9.1) is
  proved only under a hypothesis that is never constructed. The theorem on the
  route proves the class bound and the decomposition, not the flatness.
- The exact curl identity (Lemma 7.7) is out of the cone; the route carries a
  bound.
- The uniform cone margin of Lemma 4.11 appears nowhere on the route; the
  carrier gives strict cone membership with no margin.
- The energy estimate of Lemma 10.4 sits above the headline, in a stronger
  wrapper theorem; on the route, only a bare finite-energy bound is used.
- The C^k repair bounds of Lemma A.2 are display-only; the route uses a C^0
  version.
- Several lemmas (B.3, B.7, 4.4(ii), the counting half of 6.2) have no located
  counterpart on the route at all.

The headline does not need any of these stronger clauses. But the paper's
argument as written is not the formal proof's argument at those points, and a
reader matching paper to Lean by statement will be reassured by exactly the
layer that carries no weight.

**3. Where it does correspond, the correspondence is usually good.** For the
108 paper counterparts that are on the route, and for the many display-layer
theorems that merely restate a construction the route performs definitionally,
Lean is as strong as the paper or stronger: explicit constants, larger domains,
a closed-form blow-up rate at the origin that the paper never states, moment
conditions proved as exact equations rather than smallness. The docstrings cite
a draft numbering that differs from the published PDF; the correspondence
tables in `nse-deep/alignment/` translate.

## What was not done

About 3,900 in-cone theorems of estimate material were screened by two
mechanical passes and never read line by line; a wrong constant there is
invisible to both screens and cannot affect the headline. The `rfl` workload
was not bounded. No independent checker was run over the full build. Every
reading agent is from one model family, so independence is between passes,
not between models. Carrier soundness in the cone join was not re-audited
beyond the earlier passes.

## Reports

| date | report | question |
|---|---|---|
| 15 Sept | `2026-09-15-openai-NavierStokesAndEuler.md` | Is the statement the right statement? |
| 16 Sept | `2026-09-16-openai-NavierStokesAndEuler-kernel-trust.md` | Which proofs could a kernel bug fake? |
| 18 Sept | `2026-09-18-openai-NavierStokesAndEuler-FINAL.md` | Compile-backed checks; what says less than it appears to? |
| 20 Sept | `2026-09-20-openai-NavierStokesAndEuler-paper-alignment.md` | Does the Lean match the paper, and on the route? |
