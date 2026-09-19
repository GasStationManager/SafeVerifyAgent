# Audit: openai/NavierStokesAndEuler — final consolidated report

**Artifact:** `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5` — 2,659 Lean files,
641,332 lines, 52,516 declarations, 38,503 theorems.
Pinned `leanprover/lean4:v4.34.0-rc2`, mathlib `85e3a25e006c`.
**Auditor:** SafeVerifyAgent deep pass. **Artifact modified: never** — `git status` inside NSE verified
empty at every stage, including after the build.

---

## 1. Verdict

**No defect found that makes any theorem false.** Across a source audit of the whole spine, a
line-by-line read of every structural file, three mechanised defect passes, and — new in this final
cycle — **compile-backed verification**, every finding falls into one of two classes:

* **the statement says less than it appears to** (vacuity, junk values, unneeded guards), or
* **the theorem cannot be reached** (a hypothesis nobody ever supplies).

Neither class can produce a false theorem. The Navier-Stokes and Euler headline claims are untouched
by anything in this report.

**The audit's top genuinely-suspicious item, E-A4, is now CLOSED CLEAN by measurement.**

---

## 2. What this final cycle verified by compiling, not by reading

Every prior cycle recorded the same blocker — disk at 99-100%, no toolchain, zero `.olean`. All three
facts became false, and the checks below are the result.

| check | result | evidence |
|---|---|---|
| **E-A4** — does the missing `autoImplicit := false` on the 816-file NavierStokes library admit silently auto-bound identifiers? | **662/662 PASS, 0 FAIL** | `compile/03-ea4-sweep.log` |
| **P5b** — are the `field_simp` guards in `StressAlgebra` redundant? | **VERIFIED redundant** | `compile/p5b_check.lean` |
| **P8** — is `PowerFlat` vacuous at the bottom filter? | **VERIFIED vacuous** | `compile/p8_check.lean` |
| **Junk-value collapse** in `integral_gaussian_scaled` | **VERIFIED, and wider than claimed** | `compile/p8_check.lean` |
| `sorry` census | **4, all in challenge templates** | `--exclude-dir=.lake` re-run |

**E-A4 in detail, because it was the sharpest open question.** `lakefile.toml` gives the `Euler` library
`leanOptions = { autoImplicit = false, warningAsError = true }` and gives `NavierStokes`
(816 files) and `ComparatorChallenges` **nothing**. With `autoImplicit` on, a mistyped
identifier in a *statement* is silently bound as a fresh implicit instead of erroring. Source reading cannot
settle this; elaboration can. **All 662 built NavierStokes modules — 81% of the library —
compile with `-DautoImplicit=false -DwarningAsError=true`, exit 0, zero errors.** Not one auto-bound
identifier, and not one warning promoted to an error. The 71-file sampled pass (three Sonnet subagents,
including 11 audit-flagged files) agreed before the sweep confirmed it.

**P5b, verified against the kernel.** The audit had derived by hand that five nonvanishing guards were
unnecessary. `p5b_check.lean` restates two `StressAlgebra` identities with the guards **removed** and both
compile: one drops `hφ ≠ 0` entirely, the other drops **both** `hR` and `hL`. They are `field_simp`
artefacts — required by the tactic, not by the statement.

**P8, verified against the kernel.** `powerFlat_bot_any` proves `PowerFlat (⊥) q f` for **arbitrary** `q, f`,
discharged by `⟨0, le_refl 0, by simp⟩`. Every flatness claim is vacuously true at the bottom filter. It is
benign only because `[NeBot l]` sits exactly where the contradiction is derived
(`BlowupImplication.lean:78,95`) — which is correct design, not an oversight.

---

## 3. Source-level findings that stand

**Kernel trust — no exploit.** Zero metaprogramming, zero `axiom`/`opaque`/`unsafe`/`native_decide`/
`partial def`. **`Acc.rec`: zero occurrences**; `Nat.rec`: **one**, in 641,332 lines. All 210 `decide`
literals ≤ 40 (an adversarial re-check found 10⁹ numerals *adjacent* to `decide` goals, all belonging to
ℝ-valued `norm_num` goals that never touch the `Nat`/GMP path). Largest closed `Nat` the kernel evaluates:
**2.0×10¹⁸ — 61 bits, one machine word, never multi-limb**. Worst finite case split: `Fin 22`.
The census missed one class — `fin_cases`, 767 uses in 198 files — which this audit measured and cleared.

**P1 — 45 predicates nobody ever constructs**, carrying **444 in-cone hypothesis sites**,
confirmed by reading at 71% precision over 63 verified candidates. Theorems taking them are
**unreachable**, so the dependency cone over-counts. It **clusters**: `CorrectionStep.lean` holds 7,
`ActualWaveRegularity` 4, `ParticularWaveBounds` 3; 20 files hold exactly one. Largest dead chain:
`EulerAllOrderCorrectionBudget.Budget`, unconstructible, stranding a **7-file, ~540-line** chain that a live
twin superseded.

**P2 — closure without a base case**, 7 instances. A predicate with a full algebra (`.add`, `.mul`,
`.updated`) and no way to make the first one. `JetBounds.AllJetBound` has five conclusions and every one
assumes an `AllJetBound`.

**P4 — strong hypothesis beside a weaker twin that carries the live traffic**, 6 instances plus one with
reversed polarity. Always safe in direction; always misleading about reachability.

**P5 — Lean junk values.** 127 triaged rows over every in-cone hit in the 74 never-named files:
**A=23 B=67 C=31 D=6**. All 6 genuinely-unguarded cases are *property* claims
(`ContDiffAt ∞ 0`, `0 ≤ 0`), never exact values. The sharpest specimen is caller-guarded:
`integral_gaussian_scaled` is an exact identity surviving only because **two independent junk values
conspire** — now kernel-confirmed.

**P7/P7b — degenerate witnesses, with a mechanism.** Non-degeneracy is proved **once** at a base case and
thereafter only propagated: `lowBoundsFromPhysical` admits `r = 0`, `firstChildLowBounds` is the sole escape,
and every later step passes `H.r` unchanged. Four consequences traced, all confined to the base generation.
Same shape as `cartesianPotential = 0` (all 177 theorems of `InitialPhysicalData` survive it).

---

## 4. Coverage, stated in tiers rather than as one number

| tier | files | in-cone theorems |
|---|---|---|
| structural bucket, read line-by-line | **73/73** | **843/843 (100%)** |
| never-named files, read line-by-line | 41 | 737 |
| screened + adjudicated by a human | 47 | ~398 |
| screened clean by both instruments, no hit | 876 | 3,932 |

All 964 never-named files were **screened** for the two mechanised defect classes;
5,067 in-cone theorems live there. Calling the 876 "unaudited" is wrong — both passes walked them.
Calling them "audited" is equally wrong — those screens cover exactly two defect classes, and **a wrong
constant is invisible to both**.

---

## 5. Residual blockers

1. **`#print axioms` on the headline theorems was NOT run.** `NavierStokes/ComparatorSolution`,
   `Euler/Solution` and `NavierStokes/ComparatorR3Theorem` sit at the top of the import tree and are **not**
   among the 1,264 built modules; the full build was stopped by instruction at ~48% of the artifact.
   **Axiom provenance for the headline results is therefore unverified by this audit.** Albert reports the
   repository passed Comparator, which is good external evidence, but it is *reported*, not measured here.
2. **E-A4 is settled for 662/816 files (81%)**, not all 816. The unbuilt remainder sits higher in
   the import tree.
3. **~3,834 in-cone theorems of estimate material have been read by no human**, and rest on the two
   mechanical screens plus the authors' own consistency.
4. **Instrument negatives are bounded.** `nosupplier.py`'s positives are reliable; its *negatives* are
   reliable only for the 748 predicates with a unique short name. Seven bugs were found in it — **five by a
   worker or reader disagreeing with it, never by the tool itself.**
5. **GPT-5.6 Luna unavailable** on all three providers (429 / 402 / 403); superseded by the Sonnet
   authorization. No Opus subagent was spawned at any point after the restriction.

---

## 6. Next actions, in value order

1. **Targeted `lake build NavierStokes.ComparatorSolution Euler.Solution`** — their import closures only, not
   all three libraries. This is the single measurement that would close blocker 1, and the staged probe
   `compile/nse_axioms.lean` is ready to run against it.
2. **Finish E-A4** on the remaining 154 NavierStokes files once built.
3. **Delete or document the dead chains** — the ~540-line `AllOrderCorrectionBudget` branch and the
   45 unsupplied predicates. Nothing is wrong; the cone is simply larger than the live code.
4. **Treat the estimate mass as out of scope for reading** and gate it on a full build plus the mechanical
   screens, which is where a wrong constant would actually be caught.

---

## 7. Method note worth keeping

Seven bugs were found in this audit's own instruments, two of which failed in the dangerous direction of
*hiding* findings. Five were caught by a worker's number disagreeing with the script's. One rule generalises:
**treat every parent/worker numeric disagreement as a defect report against the instrument, not as noise to
average away** — and a corollary learned the hard way, **a rule that measured 41/41 was still wrong**, refuted
by a single counterexample that would have deleted the audit's sharpest junk-value finding.
