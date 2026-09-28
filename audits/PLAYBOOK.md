# Audit playbook

What the NavierStokesAndEuler series (15–20 September 2026, five passes) taught
about auditing a large claimed formalization, written down so the next audit
starts from it rather than re-learning it. Each rule names the incident that
produced it. `DESIGN.md` says what the agent is; this says how to run it at a
real artifact.

## 0. What reading is for

Reading a Lean proof has one purpose: **reconstruct the mathematical argument
the proof expresses, and escalate any discrepancy** between that argument and
the claim, the paper, or the reader's own mathematics. A reader who reports
"the proof compiles and looks fine" has not read it. A reader who reports "this
lemma proves X by Y; the paper claims X' by Y'; here is the difference" has.

Reading works for the parts of a proof that ARE an argument: decompositions,
case splits, estimates chained by hand, lemmas invoked by name. It does not
work for parts that are a computation: `rfl` and `decide` closing goals whose
definitional workload is not in the source, `norm_num`/`omega`/`simp`
certificates, large case splits, numerals the kernel evaluates, anything a
tactic did that the text does not show. For those the audit needs
**independent computation**: recompute the fact by other means (a script, a
CAS, a second elaboration with tracing) and compare. On NSE the 1,176 proofs
closed by `rfl` were left unbounded because this rung had no tool; build the
tool before the next audit needs it.

And for the kernel itself the audit needs **independently developed checkers**.
Comparator plus nanoda was the NSE plan and neither ran on the full build.
con-leche (`github.com/leanprover/con-leche`, ReadingGroup note
`papers/con-leche-repo/notes.md`) is now a third option: a checker written in
Lean with its own term representation, proven in Lean to accept no proof of
`False` in `--verified` mode, reading `lean4export` NDJSON, exit codes
0 accepted / 1 rejected / 2 declined / 3 error. Its scope caveats are in the
ReadingGroup note (the byte-level corollary covers one JSON template; the
runtime `Nat` path and the compiled binary are outside the theorem; other
axioms are rejected outright). It is independent of the C++ kernel and of
nanoda, which is what an ensemble wants. Wire it as a tier, parse its verdict
line, and record which mode ran.

## 1. Before reading anything

1. **Classify the claim: BARE or PAIRED.** PAIRED means an independently
   authored challenge statement exists and Comparator can run; the statement
   rung is then a diff. BARE means the statement rung is the whole first job
   and the evidence ceiling applies (`DESIGN.md` §4): no accept may claim more
   than the statement check supports. NSE was PAIRED for Navier–Stokes and
   effectively BARE for Euler; differential-geometry's Poincaré theorem is
   BARE.
2. **Compute the dependency cone from the headline first** (`cone.py`) and
   carry the in-cone column into every later table. The paper alignment was
   done without it; 29 of 64 verdicts changed when it was joined.
3. **Ask what could still make the headline false** given what has already
   been checked, and route budget by that. After the statement and axiom
   rungs, reading cannot find a kernel bug; an independent checker and a
   traced compile can. On NSE both were planned last and neither ran, for
   disk. Plan them first and record why if they cannot run.
4. **Read the repository's own conventions for carrying open results.** NSE
   had none. differential-geometry states one: a missing result is *named*
   as a hypothesis rather than `sorry`-ed. Under that convention a hypothesis
   never discharged on the headline route is a `sorry` that `#print axioms`
   cannot see, and the no-supplier pass is the audit.

## 2. While reading

5. **Separate the display layer from the route.** Expect wrapper theorems
   that restate the paper and are imported beside the solution rather than
   under it. For each paper counterpart record route / wrapper / dead /
   above-seed before comparing strength. NSE's paper-facing layer was about
   thirty modules and every statement-to-statement reader was reassured by it.
6. **"Not located" is a claim, not a null result.** Three first-pass gaps
   closed on a second grep. A searcher reports what it grepped, and greps for
   structures, hypotheses and consumers, never for paper notation.
7. **Follow consumers, not names.** The theorem that carries a paper claim on
   the route is found by asking what the wrapper's proof calls (`obtain … :=`
   is the fastest lead) and what in-cone theorem the same content flows
   through.
8. **Draft versus published numbering.** Docstrings may cite a draft; NSE's
   did, non-uniformly. Establish the map by content and tabulate it once.
9. **Every `file:line` cited was read with `sed -n`.** No citation from a
   name.

## 3. Instruments

10. **Instrument disagreements are bug reports.** Seven bugs in our own
    scripts, five found by a worker's number disagreeing with the script's,
    two of which hid findings. A rule that measured 41/41 was still wrong.
    Never average a disagreement away.
11. **Positive controls before a sweep.** Seed known findings (a vacuous
    predicate, a junk-value identity) and measure recall before trusting a
    cheap-model sweep over thousands of theorems.
12. **Scripts do what scripts do better.** Hypothesis inhabitability, cone
    membership, unguarded partial operations, consumer counts. Agents do
    vacuity, docstring-versus-statement drift, argument reconstruction.
13. **Two denominators, always.** Whole artifact versus cone; "named by some
    report" versus "read line by line". State coverage in tiers; a single
    percentage was quotable and misleading.

## 4. Reporting

14. **An escalation is not an accusation** and is recorded with its trace
    when it closes.
15. **What did not run is stated at the top.**
16. **Record the auditor's model family.** One family means independence is
    between passes, not between models; use the cross-model protocol for the
    coherence rung on a bare claim.
17. **Plain-language summary last**, for the reader who wants conclusions
    without ledgers, answering: is the headline sound, and can an
    intermediate theorem be reused (non-vacuous? on the route? matches the
    paper?).

## 5. Order of operations for a new artifact

1. Intake: commit, toolchain, size, BARE/PAIRED, conventions, authorship,
   vendored code.
2. Mechanical scans over comment-stripped source (`scan_repo.py`,
   `scan_kernel_risk.py`), metaprogramming listed by site, not counted.
3. Cone from the headline; route extraction; no-supplier over the route.
4. Statement rung: the headline rendered with its instance assumptions
   unfolded, diffed against a reference statement written before reading.
5. Independent checker over the full build if disk allows; `#print axioms`.
6. Reading, on the route, in cone order, reconstructing the argument;
   independent computation for the computational parts.
7. Paper alignment with the cone column from the start.
8. Coverage ledger in tiers; summary.
