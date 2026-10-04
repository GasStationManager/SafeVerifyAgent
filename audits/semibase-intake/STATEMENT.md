# Statement rung: `SemiBase.order6_classification` against the reference finite-basis classification

Verdict: **BARE, EXACT** for what the formal statement claims ("each of the 15,973 listed 6×6 tables is the
table of a semigroup, and every semigroup on `Fin 6` with that table is nonfinitely based iff its id is one of
3843, 8564, 8878, 13747, finitely based otherwise"), with the textbook notions of identity, satisfaction,
derivation, basis, FB and NFB. `Derives` is exactly the equational calculus for semigroup words (no rule
missing, none added); the alphabet is `Nat`; satisfaction quantifies over every valuation; `Semigroup`
carries associativity; `Classified` is "∃ and ∀". No clause is weaker, none stronger, nothing vacuous.
Deviations, none of which changes the truth value or strength of the stated theorem:
(D1) `HasTable` reads entries with `getD … 0`, so Lean alone would silently zero-pad a short or missing row
and ignore extra entries — inert here because every one of the 15,973 tables is exactly 6×6 with entries in
0..5 (independent parse, §3); (D2) the two corollaries `order6_finitelyBased`/`order6_nonfinitelyBased` drop
the existence conjunct and are only non-vacuous through the main theorem; (D3) the informal headline "every
semigroup of order six" needs two things the Lean statement does not contain — completeness of the list and
iso/anti-iso invariance — and the README says so (§4).

Artifact: `nasqret/semibase-order6` @ `6f75ceacff8f54d0db1f0ab286c05f0f5301f90d`, read at
`/home/user/semibase-order6`, unmodified. Lean `v4.28.0`, core only (no Mathlib), no `options` in
`lakefile.toml` (so core defaults, `autoImplicit` on). Reference: `REFERENCE-finite-basis.md` in this
directory, written before any `.lean` file was opened (after the README; disclosed there).

## What did not run

- **No build, no elaboration, no `#print axioms`.** The full build needs ~220 GB RAM; nothing here was
  `#check`ed, unfolded or `decide`d by Lean. `order6_length`, `order6_ids` (`by decide +kernel`) and every
  census `decide +kernel` are taken as stated, not re-run. The axiom claim (README; `scripts/Axioms.lean`,
  `scripts/verify.sh`) and `provenance/FINAL-AUDIT.md`'s "PASS — 15,973 of 15,973" are NOT re-checked.
  Whether the census proofs typecheck is outside this rung.
- **No GAP.** `gap/export_order6_catalogue.g` was read, not run; `catalogue.json` was not regenerated; the
  `--gap` cross-check files of the bases-min repository are not in this checkout, so the README's
  "independently regenerated with GAP 4.15.1" link is unverified here.
- Lean core was read at **v4.33.1** (the pinned v4.28.0 source is not on this machine) for `List.getD` and
  `List.range'`; both are elementary and I know of no change between the versions, but that is not checked.
- What DID run (independent computation, scripts `tools/indep_catalogue.py`, `tools/controls.py` beside this file, not in the
  deliverable): the repository's own `scripts/check_catalogue.py` (passes, 0.8 s); an independent parser of
  all 107 `Part*.lean` files with associativity, shape, order, pairwise iso/anti-iso inequivalence and
  self-duality checks; independent constructions of `B₂¹`, `A₂¹`, `L` (and a non-independent one of `A₂ᵍ`)
  located in the catalogue; two positive controls (§3).

## 1. Clause-by-clause pairing

Reference ids (O1–O10, K1–K2, H1, C1–C3, W1–W12) are those of `REFERENCE-finite-basis.md`. Every line cited
was read.

| ref | Lean (verbatim) | match | why |
|---|---|---|---|
| O1 alphabet countably infinite | `def FinitelyBased (G : Semigroup S) : Prop := FinitelyBasedOver G Nat` (`SemigroupBasis/Nonfinite.lean:16–17`); `def NonfinitelyBased … := NonfinitelyBasedOver G Nat` (:20–21) | exact | Both halves fix α = `Nat`. See §2(b). |
| O2 words = X⁺, nonempty | `structure Word (α : Type u) where head : α  tail : List α` (`Word.lean:4–6`); `append u v := ⟨u.head, u.tail ++ v.head :: v.tail⟩` (:28–29) | exact | A head letter is mandatory, so no empty word; `toList w = w.head :: w.tail` (:11–12) is injective (:14) and `toList_append` (:55–57) shows `++` is concatenation. Free semigroup on α. |
| O3 semigroup = associative operation | `structure Semigroup (S : Type u) where mul : S → S → S  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)` (`Word.lean:99–101`) | exact | Associativity is a field, so every `G : Semigroup (Fin 6)` is a genuine semigroup. No other data fields (relevant to O8/W8, §2(f)). Core Lean declares no `Semigroup` (grepped `Init/`), so there is no name clash with `open SemigroupBasis`. |
| O4 evaluation φ̂ | `def eval (G) (valuation : α → S) (w : Word α) : S := w.tail.foldl (fun acc x => G.mul acc (valuation x)) (valuation w.head)` (`Word.lean:105–106`) | exact | Left-bracketed product φ(x₁)·…·φ(x_k); bracket-independence is by `assoc`, and `eval_append` (:123–130) proves φ̂(uv) = φ̂(u)φ̂(v), i.e. φ̂ is the homomorphism. |
| O5 identity = ordered pair of words | `structure Identity (α : Type u) where lhs : Word α  rhs : Word α` (`Equational.lean:5–7`) | exact | |
| O6 satisfaction, ∀ valuations | `def SatisfiedBy (e : Identity α) (G : Semigroup S) : Prop := ∀ valuation : α → S, G.eval valuation e.lhs = G.eval valuation e.rhs` (`Equational.lean:12–13`) | exact | ∀ over the full function type `Nat → Fin 6`; no restriction. §2(c). |
| O6 Σ ⊆ Id(S) | `def Models (G) (basis : List (Identity α)) : Prop := ∀ e, e ∈ basis → e.SatisfiedBy G` (`Equational.lean:27–28`) | exact | |
| O7 derivability | `inductive Derives (basis : List (Identity α)) : Word α → Word α → Prop` with seven constructors (`Equational.lean:31–43`) | exact | §2(a). |
| O8 basis | `def BasisFor (G) (basis) : Prop := Models G basis ∧ ∀ e : Identity α, e.SatisfiedBy G → Derives basis e.lhs e.rhs` (`Equational.lean:46–48`) | exact | Both halves present (soundness of Σ in S, and Id(S) ⊆ Th(Σ)); W3 excluded. A `List` is finite, so "∃ list" = "∃ finite set". |
| O9 FB | `def FinitelyBasedOver (G) (α) : Prop := ∃ basis : List (Identity α), BasisFor G basis` (`Nonfinite.lean:7–8`), `FinitelyBased G := FinitelyBasedOver G Nat` (:16–17) | exact | |
| O9 NFB | `def NonfinitelyBasedOver (G) (α) : Prop := ¬FinitelyBasedOver G α` (:11–12); `NonfinitelyBased G := NonfinitelyBasedOver G Nat` (:20–21) | exact | Negation of the same predicate over the same alphabet and calculus; W11 excluded. |
| O10 invariance | not in the statement; lemmas `finitelyBased_opposite`, `nonfinitelyBased_opposite` (`SemiBase/Statement.lean:91–102`), `finitelyBased_transport` (:149–153); `BasisFor.oppositeReversed` (`SemigroupBasis/Opposite.lean:138–146`) | n/a (proof route) | Used by the census to move an endpoint proved for the transposed table onto the catalogue table (`Census/Shard001.lean:30–33` pattern: `first \| … \| … finitelyBased_opposite …`). Not part of `Classified`; kernel-checked if the build is. Matches O10 by reading: `Derives.reverse` (:115–129) maps prepend↔appendRight and subst σ ↦ subst (reverse ∘ σ), exactly the argument in the reference. |
| — | `structure Entry where id : Nat  rows : List (List Nat)` (`Statement.lean:36–38`) | bookkeeping | Data carrier. |
| W7 table lookup | `def entry (rows) (a b : Nat) : Nat := (rows.getD a []).getD b 0` (`Statement.lean:41–42`) | **D1, inert** | `List.getD as i d := as[i]?.getD d` (core v4.33.1 `Init/Data/List/BasicAux.lean:43–44`): out-of-range → default. §2(d). |
| O3 + table | `def HasTable (G : Semigroup (Fin 6)) (rows) : Prop := ∀ a b : Fin 6, (G.mul a b).val = entry rows a.val b.val` (`Statement.lean:46–47`) | exact (given D1 inert) | Row a, column b holds a·b. §2(d),(e). The `Decidable` instance (:49–51) is `inferInstanceAs` the same proposition; affects proofs only. |
| K2 the four ids | `def nonfinitelyBasedIds : List Nat := [3843, 8564, 8878, 13747]` (`Statement.lean:55`) | exact (ids), corroborated | §2(g). |
| C1 + C2 per entry | `def Classified (e : Entry) : Prop := (∃ G : Semigroup (Fin 6), HasTable G e.rows) ∧ ∀ G : Semigroup (Fin 6), HasTable G e.rows → (e.id ∈ nonfinitelyBasedIds → NonfinitelyBased G) ∧ (e.id ∉ nonfinitelyBasedIds → FinitelyBased G)` (`Statement.lean:61–65`) | exact | ∃ (table is associative) AND ∀ (every structure with that table). §2(f). |
| — | `def AllClassified : List Entry → Prop \| [] => True \| e :: es => Classified e ∧ AllClassified es` (:68–70) | bookkeeping | Only used to build the proof; the headline is restated as `∀ e ∈ …` via `AllClassified.mem` (:169–175). |
| K1 catalogue | `def order6 : List Entry := Order6.part001 ++ (… ++ (Order6.part107)…)` (`SemiBase/Catalogue/Order6.lean:122–123`) | exact (data) | §2(g), §3. |
| K1 count | `theorem order6_length : order6.length = 15973 := by decide +kernel` (`Catalogue/Order6.lean:125`) | exact | 15,973 = A001423(6). |
| K1 ids | `theorem order6_ids : order6.map Entry.id = List.range' 1 15973 := by decide +kernel` (`Catalogue/Order6.lean:128`) | exact | `range' s (n+1) = s :: range' (s+1) n` (core v4.33.1 `Init/Data/List/Basic.lean:2125–2127`), so the ids are 1,…,15973 in order, no repeats, no gaps. |
| C1 headline | `theorem order6_classification : ∀ e ∈ Catalogue.order6, Classified e` (`SemiBase/Classification.lean:233`) | exact | H1: the only hypothesis is list membership, inhabited 15,973 times (§2(h)). |
| C1 FB half | `theorem order6_finitelyBased : ∀ e ∈ Catalogue.order6, e.id ∉ nonfinitelyBasedIds → ∀ G : SemigroupBasis.Semigroup (Fin 6), HasTable G e.rows → SemigroupBasis.FinitelyBased G` (:238–241) | **D2** (weaker alone) | Drops the ∃ conjunct: on its own it would be vacuous for a table no semigroup has. It is proved FROM `order6_classification`, which keeps the conjunct, so the pair says the full thing. |
| C1 NFB half | `theorem order6_nonfinitelyBased : … e.id ∈ nonfinitelyBasedIds → ∀ G …, HasTable G e.rows → SemigroupBasis.NonfinitelyBased G` (:244–247) | **D2** | Same remark; also it does not by itself say that entries with these ids exist — `order6_ids` does. |

Reference clauses with no Lean counterpart: C3 (completeness of the list) and O10 as a headline theorem (§4).
Lean clauses with no reference counterpart: `Entry`, `AllClassified`, the `Decidable` instance — bookkeeping.

## 2. The specific checks

**(a) `Derives` is exactly equational logic over semigroup words.** The constructors (`Equational.lean:32–43`):

```lean
  | fromBasis {e : Identity α} : e ∈ basis → Derives basis e.lhs e.rhs
  | refl (u : Word α) : Derives basis u u
  | symm {u v : Word α} : Derives basis u v → Derives basis v u
  | trans {u v w : Word α} :
      Derives basis u v → Derives basis v w → Derives basis u w
  | prepend (p : Word α) {u v : Word α} :
      Derives basis u v → Derives basis (p ++ u) (p ++ v)
  | appendRight {u v : Word α} :
      Derives basis u v → (q : Word α) → Derives basis (u ++ q) (v ++ q)
  | subst {u v : Word α} :
      Derives basis u v → (σ : α → Word α) →
        Derives basis (u.bind σ) (v.bind σ)
```

These are (Ax), (Refl), (Sym), (Trans), (Compat-left), (Compat-right), (Subst) of O7, one to one. `Ax` admits only
members of `basis` (not identities of S), so W2's "axioms not restricted to Σ" is excluded. `subst` takes an
arbitrary `σ : α → Word α`, i.e. every endomorphism of the free semigroup, applied SIMULTANEOUSLY: `bind`
(`Word.lean:76–77`) is a left fold appending `σ x` for each letter, and `toList_bind` (:89–94) proves
`(w.bind σ).toList = w.toList.flatMap (fun x => (σ x).toList)` — letter-by-letter replacement. Substituted
values are nonempty words, as semigroup substitution requires. Nothing is missing (W1), so the NFB half is no
weaker than textbook NFB; nothing beyond the seven rules exists (W2), so the FB half is no weaker than textbook
FB. Soundness — the precise sense in which no rule is too strong — is also proved in the trusted file,
`Derives.sound` (`Equational.lean:50–67`: `Models G basis → Derives basis u v → ∀ valuation, eval u = eval v`),
and I checked each case by reading: `prepend`/`appendRight` by `eval_append` + `congrArg`, `subst` by
`eval_bind` (`Word.lean:143–149`), which re-evaluates with `x ↦ eval (σ x)`. The calculus is therefore
between "contains O7" and "sound", i.e. by Birkhoff it derives exactly Th(Σ).

**(b) Alphabet.** `Nat`, for both `FinitelyBased` and `NonfinitelyBased` (`Nonfinite.lean:16–21`); the headline
and both corollaries use these two names, not the `…Over` forms (`Classification.lean:240, 246`;
`Statement.lean:64–65`). `FinitelyBasedOver G α` for other α appears in the file (`Nonfinite.lean:7`) with the
docstring "The intended use is with an infinite variable type, such as `Nat`" (:5–6) and does not enter the
statement, so W4 (a finite alphabet making FB trivial for finite S) is excluded. Substitution maps
`Nat → Word Nat`, so derivations stay over the same infinite alphabet, as in the textbook.

**(c) `SatisfiedBy`** is `∀ valuation : α → S, …` (`Equational.lean:12–13`): every function, no injectivity,
no subset, no existential (W5 excluded).

**(d) Associativity and table encoding.** `Semigroup` carries `assoc` (`Word.lean:101`), so `∃ G, HasTable G
e.rows` asserts the table is associative (W6 excluded). The table read: `entry rows a b =
(rows.getD a []).getD b 0` (`Statement.lean:41–42`) and `HasTable G rows := ∀ a b : Fin 6, (G.mul a b).val =
entry rows a.val b.val` (:46–47). Consequences, by case:
- an entry ≥ 6: `(G.mul a b).val < 6`, so `HasTable` is unsatisfiable, the ∃ conjunct of `Classified` is false,
  and the theorem could not be proved — Lean itself rejects this malformation;
- a missing row or short row: `getD` supplies `0`s, so `HasTable` describes the ZERO-PADDED table, and a proof
  would be about that table, not the one apparently written — Lean does NOT reject this (D1);
- extra rows or extra columns: ignored by `HasTable` (only indices 0..5 are read) — Lean does not reject this.
So "can a non-6×6 table be the table of a semigroup?": yes, its 0-padded / truncated 6×6 reading can. D1 is
inert in this artifact: my independent parse of all 107 part files (§3) found every one of the 15,973 tables
to be exactly 6 rows of 6 entries, all in 0..5, and associative. `check_catalogue.py` does not test the shape
directly (it compares with `catalogue.json` minus 1, `check_catalogue.py:77, 83`), so the shape guarantee here
comes from my parse plus GAP's export being square.

**(e) Row/column convention.** `Entry`'s docstring: "row `a` lists the products `a * 0, …, a * 5`"
(`Statement.lean:33–35`), and `HasTable` puts `G.mul a b` at `rows[a][b]` — rows are the LEFT factor. The GAP
exporter writes `MultiplicationTable(s)` row by row (`gap/export_order6_catalogue.g:72, 30–42`); GAP's
documented convention for `MultiplicationTable` is M[i][j] = k iff elms[i]·elms[j] = elms[k] (from GAP's
reference manual, not re-read here — no GAP on this machine), i.e. also left factor = row, and
`check_catalogue.py:77` only subtracts 1. So the conventions agree. Even if they did not, a transpose is the
opposite semigroup and FB status is anti-isomorphism-invariant (O10), and anti-isomorphic copies are the same
Smallsemi class by construction, so a swap could not change the truth of any `Classified e`. `Opposite.lean`'s
role is on the PROOF side only: `Classified` mentions no `opposite`; the census tries the endpoint for the
table and, failing that, `finitelyBased_opposite`/`nonfinitelyBased_opposite` of the endpoint for its
transpose (`Census/Shard001.lean:30–33`; 16,220 `opposite` occurrences across the 107 shards), and in both
alternatives the last argument is `HasTable _ e.rows` for the catalogue entry, `by decide +kernel`. So
whichever orientation an endpoint was proved in, what reaches `Classified` is about the catalogue rows.

**(f) Quantifier structure of `Classified`.** `(∃ G, HasTable G e.rows) ∧ ∀ G, HasTable G e.rows → …`
(`Statement.lean:61–65`) — "for EVERY semigroup structure with this table", plus existence so the ∀ is not
vacuous (W8 excluded). Since a `Semigroup (Fin 6)` is `mul` plus a proof, any two with the same table are
equal — the file proves it, `eq_of_hasTable` (:75–83, funext on `mul` then `cases`, proof irrelevance for
`assoc`) — so ∀ and ∃ coincide here; the statement nonetheless says both. The two implications are on
`e.id ∈ nonfinitelyBasedIds` and its negation, so each entry gets exactly one of FB / NFB, and the
`List Nat` membership is ordinary core `List.Mem` (no `Membership` instance on `List` is declared anywhere in
the repository: the only `Membership` instance is on `Ideal G`, `SemigroupBasis/Ideal.lean:14`; and the
repository declares no `notation`/`infix`/`macro`/`syntax`/`elab` at all — grepped all `.lean` files for those
commands at line start; the hits were prose and field names).

**(g) The ids and the count.** In Lean: `order6_length = 15973` and `order6_ids = List.range' 1 15973`
(`Catalogue/Order6.lean:125, 128`), both `decide +kernel` (not re-run). The four ids
`[3843, 8564, 8878, 13747]` (`Statement.lean:55`) match the README and, by `check_catalogue.py:95–98`, the
repository's `published_classification.json`. Independently of that file (§3): from presentations I wrote
down before matching, B₂¹ (0-Rees 2×2 over the trivial group, sandwich = identity, plus identity) lands in
class **8564**; A₂¹ (sandwich [[1,1],[1,0]], plus identity) in **13747**; L = ⟨a, b | a² = a, b² = b, aba =
0⟩ (Zhang–Luo 2011) in **3843**. A₂ᵍ (A₂ with its zero replaced by the 2-element group) lands in **8878**, but
that construction was read off the structure of the repository's published table, so it is a consistency
check, not an independent identification. Counts: 15,973 = A001423(6); `check_catalogue.py` passes (pinned
SHA-256 of `catalogue.json` matches, 15,973 tables equal to it, 3,312 self-dual).

**(h) Hypothesis inhabitability.** The headline has one hypothesis, `e ∈ Catalogue.order6`, inhabited by 15,973
entries (`order6_length`). The corollaries add `e.id ∉ nonfinitelyBasedIds` (e.g. `[6,1]`) or
`e.id ∈ nonfinitelyBasedIds` (the four, present by `order6_ids`), and `HasTable G e.rows`, inhabited per entry
by the ∃ conjunct of `Classified`. No named-hypothesis convention (PLAYBOOK §1.4) applies: there are no
`Prop`-valued parameters on any of the five theorems. `autoImplicit` is on (core default; `lakefile.toml` sets
no options) and the trusted files rely on it (`Word.lean` has no `universe` or `variable` lines), so I checked
every auto-bound name in the trusted definitions (`α β S T G H u`) for typos that would silently create a new
variable: none.

## 3. Independent computation over the catalogue

Parser reads every line of `SemiBase/Catalogue/Order6/Part*.lean` (not only `def` lines; any other line kind
would be reported: none), and each `partNNN` list body (names only; no inline `⟨…⟩` entries).

| check | result |
|---|---|
| part files / list entries / `def S6_k` | 107 / 15,973 / 15,973 |
| concatenated part lists = `S6_1 … S6_15973` in order, `id` field = k | yes |
| every table 6×6, entries in 0..5 | yes (D1 inert) |
| associative | 15,973 / 15,973 |
| pairwise non-isomorphic and non-anti-isomorphic (canonical form over 720 relabellings × {T, Tᵀ}) | 15,973 distinct classes, 0 duplicates |
| self-dual | 3,312 (= `catalogue.json`'s count) |
| B₂¹ / A₂¹ / L located at | 8564 / 13747 / 3843 |
| A₂ᵍ (non-independent) located at | 8878 |
| control: relabelled transpose of `[6,100]` | found as 100 |
| control: non-associative table | flagged (my first control table was in fact associative — a zero semigroup with one extra product — and was not flagged; replaced; recorded as an instrument note) |

Consequence: the 15,973 listed tables are semigroups and are pairwise inequivalent under isomorphism and
anti-isomorphism. Together with A001423(6) = 15,973 (an external enumeration, Plemmons 1967 / Smallsemi), the
list is therefore COMPLETE up to iso/anti-iso — the step the README correctly says Lean does not prove. This
takes the OEIS number on trust, and is a computation, not a Lean proof.

## 4. Informal claim vs formal statement

- **"Every semigroup of order six" is not what Lean states.** Lean states C1 for 15,973 tables on `Fin 6`.
  The bridge needs (i) completeness of the list — not in Lean, stated as such (README "Scope and limitations";
  `Catalogue/Order6.lean:113–116` docstring "does not prove that it lists every class"); §3 supplies it modulo
  the OEIS count — and (ii) invariance of FB/NFB under isomorphism and anti-isomorphism — standard (O10),
  present in Lean as lemmas for transposes and for permutations of `Fin 6` (`Statement.lean:91–102, 137–153`;
  NFB via `nonfinitelyBased_iff_of_sameIdentityTheory`, `Nonfinite.lean:139`), but not as a theorem about an
  arbitrary carrier of size six.
- **Pairwise non-isomorphism** is not proved in Lean and is not needed for the stated theorem (duplicates
  would only lose coverage); §3 checks it.
- **Orders 1–5** (1,309 classes) are not in this repository (README); 1,309 = 1+4+18+126+1160 = Σ A001423(1..5).
- **"Every finitely based class comes with an explicit basis"** (README): true of the proof route (the census
  passes `BasisFor.finitelyBased <representative_basis>`), not of the statement, which is the existential
  `FinitelyBased`. Not a defect.
- **The NFB literature.** The README attributes the four to Lee–Li–Zhang 2012 / Lee–Zhang 2015; the Lean
  NFB proofs are named `LeeL.s6_3843…`, `B2One.s6_8564…`, `AC2.s6_8878…`, `A2One.s6_13747…`
  (`Census/Shard026.lean:505`, `Shard058.lean:103`, `Shard060.lean:207`, `Shard092.lean:531`). Whether those
  proofs rest on any named external input (e.g. `A2One/TrahtmanCriterion.lean:844` mentions "whose sole
  external input is Trahtman's exact …") is a ROUTE question: the headline has no hypotheses, so any such
  input must be discharged in Lean, and the axiom rung (not run here) is what would show a gap. Flagged as the
  first lead for the route rung.
- The formal statement is nowhere stronger than the informal one, and is weaker only by (i)/(ii) above,
  which the README states.

## 5. Coverage, two denominators

- Statement surface: `Word.lean` 152/152 lines, `Equational.lean` 91/91, `Nonfinite.lean` 1–120 read and
  121–243 declaration list read (only lemmas and `UsesOnly`/`BasisUses*` defs, none in the statement),
  `Statement.lean` 177/177, `Classification.lean` 249/249, `Opposite.lean` 148/148,
  `Catalogue/Order6.lean` 105–130 + import list, `Part001.lean` head and tail by eye, all 107 parts by script,
  `Census/Shard001.lean` 1–60 and tail, the four NFB census theorems. `HomomorphicImage.lean` (imported by
  `Statement.lean`): imports only, used by proof lemmas, not read.
- Whole artifact: 7,398 files; about ten read. This rung says the statement is the right one. It says
  nothing about whether the proofs typecheck or which axioms they use.
