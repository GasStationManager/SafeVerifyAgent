# Statement rung: `ComparatorChallenges/H_GapCVP.lean` against the reference NP-hardness of GapCVP^(2)_{n^{1/400}}

Verdict: **PAIRED-same-author; EXACT on every clause that carries the paper's claim, with three deviations
that make the formal statements STRONGER, not weaker, and two pairing caveats.** Read clause by clause, the
four statements say: for every language with a polynomial-time Mathlib TM2 verifier and polynomially bounded
certificates, there is a polynomial-time TM2-computable map on bit strings sending members into YES and
non-members into NO, where YES/NO are (i) GapCVP^(2) with γ(n) = n^{1/400} at the lattice dimension,
nonsingular square integer basis, positive rational radius, **restricted to integer targets**; (ii) binary
nearest codeword, γ = n^{1/200} at block length; (iii) binary syndrome decoding, γ = n^{1/200}, **NO side
restricted to consistent systems**; (iv) ℓ_p CVP, every rational p ≥ 1, γ = n^{1/(200p)}, rational target.
That is Theorem 1, Corollary 15 and Corollary 16 of the paper.

Deviations (none weakens the claim):
- **D1** (`hasIntegerTarget` in both YES and NO, H:120, H:127): GapCVP restricted to t ∈ ℤ^n. A
  reduction into the restriction is verbatim a reduction into the ℚ^n problem, so this is the STRONGER
  statement, and it is the one Theorem 1 proves (t ∈ ℤ^n). The unrestricted ℚ-target Euclidean problem is
  in any case the p = 2 instance of `finitePNormGapCVPIsNPHard` (§2(h)).
- **D2** (syndrome-decoding NO requires `∃ word, H·word = b`, H:259–260): inconsistent systems are in
  NEITHER language, where the textbook objective (min over ∅ = +∞) puts them in NO. Smaller NO set ⇒
  stronger hardness. The paper's inconsistent-branch output (H = I₂, b = 11) is consistent, so its proof is
  compatible.
- **D3** (nearest-codeword generator is `Fin blockLength → Fin generatorRank → ZMod 2`, codewords `G·c`,
  H:159, H:173–178): generators are the COLUMNS of an n × k matrix; the paper says rows of a k × n matrix.
  Transpose convention only; same set of codes (any spanning family, k = 0 allowed, which the paper's {00}
  output needs).

Pairing caveats:
- **P1. The four `*Promise` definitions are comparator DEFINITION HOLES, so the comparator does not compare
  what the problems ARE.** `definition_names` (H_GapCVP.json) makes `gapCVP400Promise` etc. holes; for a
  hole the comparator checks name, type, universe levels and safety only, and walks only the hole's TYPE
  (comparator@07bc4ea `Comparator/Compare.lean:49–50, 61–63, 102`; its README: "all definition hole
  solutions **must** always be checked with an additional (potentially human) verifier", `README.md:91`).
  The theorem types `IsNPHardPromise gapCVP400Promise` mention the hole by NAME. So a comparator pass
  certifies the complexity scaffolding (`IsNPHardPromise`, `PromiseReduction`, `PromiseProblem`, `IsNP`,
  `BitTM`, `VerifierTM`, the encodings of pairs) and NOTHING about YES/NO, the instance encodings, the
  distance, the gap factors or the coding problems. The holes exist because the challenge's `disjoint`
  fields are `by sorry` (H:138, 210, 266, 305). This rung is the additional verifier for those values
  (§3): the solution's bodies are whitespace-identical to the challenge's in every `yes`/`no` field and in
  every definition they reach, the `disjoint` fields are filled with real proofs, and no name in those
  bodies resolves differently in the solution's environment. That check is TEXTUAL plus a name-resolution
  argument, not a comparison of elaborated terms.
- **P2. Same author.** The challenge and the solution are both by OpenAI ("Astra (OpenAI)",
  `formalization.yaml`); the challenge is not an independent rendering of the paper. Its fidelity to the
  paper is established here by reading (§1, §4), not by authorship.

V1 (is the NP hypothesis satisfiable?): **yes in principle, by a hand construction that was not
elaborated; NOT exhibited anywhere in the artifact.** Every one of the 539 occurrences of `VerifierTM` in
`GapCVP.lean` is a binder (a hypothesis consumed), and no theorem proves `IsNP L` for any concrete `L`
(§2(a)). `BitTM` IS constructed many times in the artifact (e.g. `structuralPrefixWriterComputable`,
G:17449), and Mathlib's `idComputableInPolyTime` gives `BitTM id`.

Artifact: `openai/ten-proofs` @ `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6` (sparse checkout at
`/home/user/ten-proofs`, unmodified). Lean v4.32.0; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`
(tag v4.32.0); comparator `07bc4ea40f2266dcb861820a2ec1fa3244ed307f` (lake-manifest). Citations: `H:` =
`ComparatorChallenges/H_GapCVP.lean`, `G:` = `GapCVP.lean`, `ML@81a5d257` = Mathlib at the pinned commit.
Reference: `REFERENCE-gapcvp.md` beside this file, written before `H_GapCVP.lean` was opened (its
disclosure: the task brief named the challenge's identifiers; V2 reworded afterwards for clarity).

## What did not run

- **No build, no elaboration, no comparator run, no `#print axioms`.** Disk (1.7 GB free) does not allow
  the build of a 130,430-line file against Mathlib. Every judgement below is reading of source text. The
  authors' comparator pass, the axiom list (`formalization.yaml`: propext, Classical.choice, Quot.sound)
  and `sorry_count: 0` are taken as stated, not re-run. nanoda was not run.
- **The constant-true verifier machine in §2(a) was checked by hand against `TM2.stepAux`, not
  elaborated.** It is the only evidence here that `IsNP` is satisfiable.
- **The diff of hole bodies (§3) is whitespace-normalised TEXT**, plus a check that no identifier in them
  is shadowed by a `GapCVP.*`/`GapCVP.Comparator.*`/`GapCVP.BinaryEncoding.*` declaration of the solution
  that does not exist in the challenge (script over a namespace-tracking scan of `G:`; it reads declaration
  headers, so a declaration produced by a macro would be missed). Name resolution read in Lean v4.33.1
  source (`Lean/ResolveName.lean:146–151`, innermost namespace wins), not at v4.32.0.
- Mathlib was read at the pinned commit for `Computable.lean`, `Encoding.lean`, `StateTransition.lean`,
  `StackTuringMachine.lean` (blobless fetch, files by `git show`); these are identical to v4.33.1 except
  `set_option` lines and one simp list (diffed). `Encodable ℚ`/`ℤ`, `hammingNorm` read at v4.33.1 only.
- The proof route (`isNPHardPromise_of_original` G:130374 and the original-namespace theorems it calls)
  is outside this rung; nothing here says the proof is right.

## 1. Clause-by-clause pairing

Reference ids (P1–P10, C1–C7, H1–H3, V1–V11) are those of `REFERENCE-gapcvp.md`. Every line cited was
read.

### 1.1 Encodings and the machine model

| ref | Lean (verbatim) | match | why |
|---|---|---|---|
| C1 atom | `def lengthPrefixedWord (word : List Bool) : List Bool := List.replicate word.length true ++ false :: word` (H:9–10); `def encodeAtomic … (value : α) : List Bool := lengthPrefixedWord (Computability.encodeNat (Encodable.encode value))` (H:12–13) | exact | Unary length, separator, binary word: prefix-free, length 2k+1 for a k-bit word. `encodeNat` is binary via `encodeNum`/`encodePosNum` (ML@81a5d257 `Encoding.lean:83–95`), injective (`decodeNat` inverse). `Encodable` is injective by definition; `Encodable ℚ` goes through `Σ n : ℤ, {d // …}` (`Data/Rat/Encodable.lean:23–27`), `ℤ` through `Equiv.intEquivNat` (`Logic/Encodable/Basic.lean:375–376`), pairs through `Nat.pair`, so the code length is linear in the binary size. V4. |
| C1 vectors, matrices | `encodeFinValues` (H:15–20), `encodeMatrixRows` (H:22–27) | exact | Concatenated prefix-free atoms, row-major; the counts come from the already-encoded dimension. |
| C1 instance, V4 | `def encodeInstance (I : Instance) : List Bool := encodeAtomic I.dimension ++ encodeAtomic I.radius ++ encodeFinValues I.dimension I.target ++ encodeMatrixRows I.dimension I.dimension I.basis` (H:74–78) | exact | Injective: dimension first, then fixed-count prefix-free fields. Not stated in the challenge; the solution proves `encodeInstance_injective` (G:129806) via a decoder; by reading it holds. Malformed strings are in neither language (C4, fine). |
| — | `abbrev BitLanguage := List Bool → Bool` (H:33); `abbrev bitEncoding : List Bool → List Bool := id` (H:35) | exact | Languages over {0,1}; V10. `bitEncoding` is the identity encoding of a bit string into alphabet `Bool`. |
| V11 pair | `def pairBitEncoding : … → List (Bool ⊕ Bool) := (Computability.encodingProd (Computability.encodingList Bool) (Computability.encodingList Bool)).encode` (H:37–40) | exact | `encodingList α` has `encode := id` (ML@81a5d257 `Encoding.lean:191–194`); `encodingProd`: `encode x := (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr` (:202–204). So (x, w) ↦ x tagged `inl` then w tagged `inr`: injective, length \|x\|+\|w\|, alphabet of 4 symbols. |
| C2 | `abbrev BitTM (map …) := Turing.TM2ComputableInPolyTime bitEncoding bitEncoding map` (H:42–43) | exact | `TM2ComputableInPolyTime ea eb f` extends `TM2ComputableAux αΓ βΓ` (`inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀`, `outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁`, ML@81a5d257 `Computable.lean:147–153`) with `time : Polynomial ℕ` and `outputsFun : ∀ a, TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a)) (Option.some ((List.map outputAlphabet.invFun) (eb (f a)))) (time.eval (ea a).length)` (:179–188). Deterministic (`step` is a function, `StackTuringMachine.lean:171–173`), total on all inputs, bound in the INPUT length. V3. |
| C3 verifier | `abbrev VerifierTM (verifier : List Bool × List Bool → Bool) := Turing.TM2ComputableInPolyTime pairBitEncoding Computability.encodeBool verifier` (H:45–47) | exact | Time polynomial in \|x\|+\|w\|; output one bit (`encodeBool := pure`, `Encoding.lean:163`). |
| C3 NP | `IsNP (language) := @decide (∃ (bound : Polynomial ℕ) (verifier …), Nonempty (VerifierTM verifier) ∧ ∀ input, language input ↔ ∃ certificate, certificate.length ≤ bound.eval input.length ∧ verifier (input, certificate) = true) (Classical.propDecidable _)` (H:49–57) | exact | Arora–Barak Def. 2.1 with "≤ q(\|x\|)". Certificate bounded in \|x\|; verifier time poly in \|x\|+\|w\| hence in \|x\| on bounded certificates. V2 does not arise. |
| C4 | `structure PromiseProblem where yes : BitLanguage; no : BitLanguage; disjoint : ∀ bits, yes bits → no bits → False` (H:130–133) | exact | §2(c) for `disjoint`. |
| C5 | `structure PromiseReduction (language) (problem) where map : List Bool → List Bool; polynomial_time : Nonempty (BitTM map); completeness : ∀ input, language input → problem.yes (map input); soundness : ∀ input, ¬ language input → problem.no (map input)` (H:140–145) | exact | Karp reduction for a promise problem; quantified over ALL strings. |
| C6 | `IsNPHardPromise (problem) := @decide (∀ language : BitLanguage, IsNP language → Nonempty (PromiseReduction language problem)) (Classical.propDecidable _)` (H:147–151) | exact | The ∀ L form (stronger, self-contained; no Cook–Levin left outside the statement). |

### 1.2 GapCVP^(2)_{n^{1/400}}

| ref | Lean (verbatim) | match | why |
|---|---|---|---|
| P3 instance | `structure Instance where dimension : ℕ; basis : Matrix (Fin dimension) (Fin dimension) ℤ; target : Fin dimension → ℚ; radius : ℚ` (H:63–67) | exact | Square integer basis, rational target and radius. |
| P3, V7 | `wellFormed record := @decide (0 < record.dimension ∧ record.basis.det ≠ 0 ∧ 0 < record.radius) …` (H:80–83) | exact | Nonsingular over ℤ (det ≠ 0), r > 0, n ≥ 1. Inhabited: n = 1, B = (1), r = 1. |
| P6, V8 | `hasIntegerTarget record := @decide (∀ index, ∃ value : ℤ, record.target index = (value : ℚ)) …` (H:85–89), conjoined in BOTH `yesLanguage` (H:120) and `noLanguage` (H:127) | **D1, stronger** | §2(d). |
| P1, P2, V9 | `distanceSquared I vector : ℝ := ∑ i, (((∑ j, (I.basis i j : ℝ) * (vector j : ℝ)) - (I.target i : ℝ)) ^ 2)` (H:91–96) | exact | ‖Bz − t‖₂² over ℝ; `(Bz)_i = Σ_j B_ij z_j`, so L(B) is spanned by the COLUMNS, as in the paper (l.41–43). |
| P5, V6 | `gapFactor400 I := (I.dimension : ℝ) ^ ((1 : ℝ) / 400)` (H:98–99) | exact | Real rpow at n = dimension, not encoding length. ≥ 1 for n ≥ 1. |
| P4 YES | `gapYES400 record := @decide (wellFormed record ∧ ∃ vector, distanceSquared record vector ≤ (record.radius : ℝ) ^ 2) …` (H:101–106) | exact | dist₂ ≤ r ⇔ ∃ z, ‖Bz − t‖² ≤ r² (min attained; r > 0). |
| P4 NO | `gapNO400 record := @decide (wellFormed record ∧ ∀ vector, (gapFactor400 record * (record.radius : ℝ)) ^ 2 < distanceSquared record vector) …` (H:108–114) | exact | dist₂ > γr ⇔ ∀ z, (γr)² < ‖Bz − t‖² (min attained, γr > 0). Squares on both sides: V9 clean. |
| C4 YES/NO languages | `yesLanguage bits := @decide (∃ record, encodeInstance record = bits ∧ hasIntegerTarget record ∧ gapYES400 record) …` (H:116–121); `noLanguage` same with `gapNO400` (H:123–128) | exact (given D1) | Defined on encodings by ∃; with injective encoding (V4) each string has at most one instance. |
| C4 | `def gapCVP400Promise : PromiseProblem where yes := yesLanguage; no := noLanguage; disjoint := by sorry` (H:135–138) | exact (yes/no); hole (P1) | §2(c). |
| H1 | `theorem gapCVP400IsNPHard : IsNPHardPromise gapCVP400Promise` (H:153–154) | exact (+D1) | Theorem 1's "Consequently … NP-hard", in the stronger integer-target form. |

### 1.3 Coding problems (Corollary 15)

| ref | Lean (verbatim) | match | why |
|---|---|---|---|
| P7 instance | `structure BinaryNearestCodewordInstance where blockLength : ℕ; generatorRank : ℕ; generator : Fin blockLength → Fin generatorRank → ZMod 2; target : Fin blockLength → ZMod 2; radius : ℕ` (H:156–161) | exact (D3) | `generatorRank` is the number of generators, not a rank assertion (no independence required; neither in the paper). |
| C1 | `encodeBinaryNearestCodewordInstance` (H:163–171): three atoms, target, generator rows, entries as `((x).val : ℤ)` | exact | `ZMod 2 = Fin 2`, `.val` injective. Injectivity proved in the solution (G:129985 `encodeBinaryNearestCodewordInstance_injective`), holds by reading. |
| P7 code | `binaryNearestCodeword record coefficients := fun index => ∑ column, record.generator index column * coefficients column` (H:173–178); `binaryNearestTarget := record.target` (H:180–182) | exact (D3) | C = column span of G over F₂. |
| P7, V6 | `binaryCodeGapFactor (blockLength : ℕ) : ℝ := (blockLength : ℝ) ^ ((1 : ℝ) / 200)` (H:184–185), applied to `record.blockLength` | exact | n = block length, as in Cor. 15 ("n denotes the output block length", l.1610–1612). |
| P7 YES | `0 < record.blockLength ∧ 0 < record.radius ∧ ∃ coefficients, hammingNorm (binaryNearestTarget record - binaryNearestCodeword record coefficients) ≤ record.radius` (H:192–196) | exact | `hammingNorm x := #{i \| x i ≠ 0}` (Mathlib `InformationTheory/Hamming.lean:138`, v4.33.1). wt(u − c) ≤ R, R a positive integer. |
| P7 NO | `… ∀ coefficients, binaryCodeGapFactor record.blockLength * (record.radius : ℝ) < (hammingNorm (…) : ℝ)` (H:202–208) | exact | d_H(u, C) > n^{1/200} R. |
| H2 | `theorem binaryNearestCodewordIsNPHard : IsNPHardPromise binaryNearestCodewordPromise` (H:212–214) | exact | |
| P8 instance | `structure BinarySyndromeDecodingInstance where checkCount; blockLength; parityCheck : Fin checkCount → Fin blockLength → ZMod 2; syndrome : Fin checkCount → ZMod 2; radius : ℕ` (H:216–221); `binarySyndromeProduct … := fun row => ∑ column, record.parityCheck row column * word column` (H:233–238) | exact | H·x over F₂, m × n parity-check matrix. |
| P8 YES | `… ∃ word, binarySyndromeProduct record word = binarySyndromeTarget record ∧ hammingNorm word ≤ record.radius` (H:250–252) | exact | W(H,b) ≤ R. |
| P8 NO | `… (∃ word, binarySyndromeProduct record word = binarySyndromeTarget record) ∧ ∀ word, binarySyndromeProduct record word = binarySyndromeTarget record → binaryCodeGapFactor record.blockLength * (record.radius : ℝ) < (hammingNorm word : ℝ)` (H:259–264) | **D2, stronger** | Consistency demanded on the NO side. |
| H2 | `theorem binarySyndromeDecodingIsNPHard : IsNPHardPromise binarySyndromeDecodingPromise` (H:268–270) | exact (+D2) | |

### 1.4 ℓ_p CVP (Corollary 16)

| ref | Lean (verbatim) | match | why |
|---|---|---|---|
| P9 norm | `finitePNorm (p : ℚ) {n} (vector : Fin n → ℝ) : ℝ := (∑ i, \|vector i\| ^ (p : ℝ)) ^ ((p : ℝ)⁻¹)` (H:272–273) | exact for p ≥ 1 | Real rpow of nonnegative bases; the ℓ_p norm. |
| P9 distance | `finitePLatticeDiscrepancy I vector := fun i => (I.target i : ℝ) - ∑ j, (I.basis i j : ℝ) * (vector j : ℝ)` (H:275–278); `finitePLatticeDistance p I vector := finitePNorm p (finitePLatticeDiscrepancy I vector)` (H:280–282) | exact | ‖t − Bz‖_p, columns as before. |
| P9, V6 | `finitePGapFactor p I := (I.dimension : ℝ) ^ (((200 : ℝ) * (p : ℝ))⁻¹)` (H:284–285) | exact | n^{1/(200p)}, n = rank. |
| P9 YES/NO | `finitePGapCVPPromise (p : ℚ) (hp : 1 ≤ p)`: yes `∃ I, encodeInstance I = bits ∧ wellFormed I ∧ ∃ vector, finitePLatticeDistance p I vector ≤ (I.radius : ℝ)`; no `… ∀ vector, finitePGapFactor p I * (I.radius : ℝ) < finitePLatticeDistance p I vector` (H:287–305) | exact | Rational target (no integer restriction), rational r > 0, nonsingular square integer B. `hp` is used only by the (sorried) `disjoint`. |
| H3 | `theorem finitePNormGapCVPIsNPHard (p : ℚ) (hp : 1 ≤ p) : IsNPHardPromise (finitePGapCVPPromise p hp)` (H:307–309) | exact | ∀ p, ∃ reductions per p: p fixed independently of the input, as in Cor. 16 (l.1635–1643). |

Reference clauses with no Lean counterpart: Theorem 1's explicit 3SAT form and its size bounds
(q = Θ(N^200), n ≤ 40N^401) — the formal statement is the ∀-L form, which subsumes the consequence the
paper draws and says nothing about sizes; P10 items (ℓ_∞, real p) are not claimed by the paper either.
Lean clauses with no reference counterpart: none beyond encoding bookkeeping.

## 2. The specific checks

**(a) V1 — is `IsNP` satisfiable?** The structures involved, at ML@81a5d257:
`FinTM2` requires `[Γk₀Fin : Fintype (Γ k₀)]` and finite `K`, `Λ`, `σ` (`Computable.lean:46–71`, :68);
`TM2OutputsInTime tm l l' m := EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m`
(:135–137); `haltList` demands label `none`, `var := tm.initialState`, every stack other than `k₁` empty
(:118–124); `EvalsToInTime` = `steps`, `(flip bind f)^[steps] a = b`, `steps ≤ m`
(`StateTransition.lean:255–267`). A `VerifierTM v` needs `tm.Γ tm.k₀ ≃ Bool ⊕ Bool` and
`tm.Γ tm.k₁ ≃ Bool`, hence `k₀ ≠ k₁` (4 ≠ 2 elements) — no obstruction.

Hand construction (not elaborated) of `VerifierTM (fun _ => true)`: `K := Bool`, `k₀ := false`,
`k₁ := true`, `Γ false := Bool ⊕ Bool`, `Γ true := Bool`, `Λ := Unit`, `σ := Bool`, `initialState := false`,
`m () := pop false (fun _ o => o.isSome) (branch id (goto fun _ => ()) (push true (fun _ => true) halt))`,
both alphabet equivalences `Equiv.refl`, `time := X + 1`. By `stepAux` (`StackTuringMachine.lean:161–168`)
each step pops one input symbol and loops while the pop succeeded; the step that pops from the empty stack
sets `var := false` (= `initialState`), pushes `true` on stack `true` and halts, leaving stack `false` empty —
exactly `haltList tm [true]` = `haltList tm (List.map outputAlphabet.invFun (encodeBool true))`, after
\|x\|+\|w\|+1 steps ≤ `(X+1).eval (pairBitEncoding (x,w)).length`. With `bound := 0` this gives
`IsNP (fun _ => true)`. So the hypothesis of `IsNPHardPromise` is satisfiable and the four theorems are
not vacuous in the degenerate sense. (Equality of the stack function `update …` with `haltList`'s `dite` is
by `funext` over `Bool`; that is the step a Lean check would have to discharge.)

What the artifact exhibits: **no `VerifierTM` value and no `IsNP L` proof for any concrete `L` (not
located).** Searched `GapCVP.lean` for `VerifierTM` (539 occurrences: 534 `(machine : VerifierTM …)`
binders, 2 `{machine …}` binders, 1 `variable`, the `abbrev` G:634 and the use G:641), for `IsNP`
(G:638, 662, 684, 1776, 88646, 129765, 130213, 130382, 130385 — definitions, binders and `simp`
unfoldings that CONSUME a membership hypothesis, e.g. `paperOriginalThreeSATIsNPHard` G:88642–88658
`obtain ⟨bound, verifier, ⟨machine⟩, correctness⟩ := membership`), and for `idComputableInPolyTime`
(only `bitEncoding` instances, G:17508, 41508, 51670, …). Mathlib has no `IsNP`; its only
`TM2ComputableInPolyTime` value is `idComputableInPolyTime` (`Computable.lean:221–230`, ea = eb, so not a
verifier). Note what the artifact does NOT claim either: no theorem that 3SAT (or any hard language) is in
`IsNP`. Non-vacuity in the meaningful sense (formal NP contains hard languages) rests on the standard
fact that Mathlib's TM2 model with polynomial time is a faithful machine model; the artifact's own
Cook–Levin tableau over an ARBITRARY `machine : VerifierTM verifier` (`structuralWholeCNFWord bound
machine`, G:88626–88640) is consistent with that, but it is a proof route, not a witness.

`BitTM` is constructed in the artifact (e.g. `structuralPrefixWriterComputable : Turing.TM2ComputableInPolyTime
GapCVP.bitEncoding GapCVP.bitEncoding (fun input => lengthPrefixedWord input)` with `inputAlphabet :=
Equiv.refl Bool`, `time := 3 * Polynomial.X + 3`, G:17449–17457), so the reductions' machine type is
inhabited by the artifact itself.

**(b) V3.** The bound is `time.eval (ea a).length` with `ea = bitEncoding = id`: the input string's
length, for every input string, with the polynomial chosen before the input (field of the structure). A
`Polynomial ℕ` has nonnegative coefficients, so `eval` is monotone in the argument; no monotonicity or
degree assumption is needed for the statement to mean polynomial time. No weakening.

**(c) V5 — `disjoint`.** In the challenge, `disjoint := by sorry` in all four promises (H:138, 210, 266,
305). It is a Prop field; the theorems mention the promise only through `.yes`/`.no` in
`PromiseReduction`, so the proof is irrelevant to what the theorems say. The comparator treats the four
promises as holes (caveat P1) and so never sees the sorry or the solution's proof. The solution fills each
with a real proof (G:129888–129898, via `encodeInstance_injective` G:129806 and `gapYES400_not_gapNO400`
G:129846; G:130066–130110; G:130111–130150; G:130166–130202), and by reading disjointness holds: injective
encoding ⇒ same record; YES gives ‖·‖² ≤ r² for some z, NO gives (γr)² < ‖·‖² for all z, and γ ≥ 1, r > 0.
The solution's axiom list (taken as stated) excludes `sorryAx`.

**(d) V8 — integer targets.** Π' := (YES ∩ ℤ-target, NO ∩ ℤ-target). Π'_YES ⊆ Π_YES and Π'_NO ⊆ Π_NO
(Π the ℚ-target problem of §1.1 of the paper), so any `PromiseReduction L Π'` is a `PromiseReduction L Π`
with the same `map`. Hardness of Π' therefore implies hardness of Π; the formal statement is the
stronger one. The predicate is on the decoded instance, not the string, so it cannot interact with
malformed encodings. Theorem 1 outputs t ∈ ℤ^n (paper l.73–76; §6 outputs t = u ∈ {0,1}^M or t = (1)).

**(e) V9.** `distanceSquared` is the squared Euclidean norm over ℝ of `Bz − t` (sign irrelevant under the
square); compared with `r ^ 2` and `(γ * r) ^ 2`, both nonnegative. Exact.

**(f) V7.** `wellFormed` is inhabited (§1.2); neither YES nor NO is empty (the paper's fixed instances
B = (1), t = (0), r = 1 and B = (2), t = (1), r = 1/2 are in YES and NO respectively; the latter: dist = 1,
γ(1) = 1, (1·½)² = ¼ < (2z − 1)² ≥ 1 for all z ∈ ℤ).

**(g) V10.** Every language is `@decide P (Classical.propDecidable P)`. `decide_eq_true_iff` holds for any
`Decidable` instance (and `Decidable P` is a subsingleton), so `lang bits = true ↔ P bits`. The
`noncomputable` only blocks evaluation; it does not change meaning. The TM model never computes these
languages; it computes `map` and `verifier`, which are arbitrary functions constrained by the machine.

**(h) p = 2 covers the unrestricted Euclidean problem.** `finitePGapFactor 2 I = n^{1/400}` and
`finitePNorm 2` is the Euclidean norm, with a rational target and no integer restriction; so
`finitePNormGapCVPIsNPHard 2 (by norm_num)` is NP-hardness of GapCVP^(2)_{n^{1/400}} exactly as defined in
the paper's §1.1 (t ∈ ℚ^n), and `gapCVP400IsNPHard` is its integer-target strengthening.

## 3. Challenge vs `GapCVP.lean`'s `GapCVP.Comparator` (task 3)

Whitespace-normalised diff of every declaration of the challenge against its namesake in the solution
(`GapCVP.lean` lines 1–700 for the `GapCVP`/`GapCVP.BinaryEncoding` part, 129737–130428 for
`GapCVP.Comparator`; theorems compared up to `:=`):

- **Identical:** `lengthPrefixedWord` (G:319), `encodeFinValues` (G:471), `encodeMatrixRows` (G:511),
  `BitLanguage` (G:621), `bitEncoding` (G:623), `pairBitEncoding` (G:625), `VerifierTM` (G:634), and in
  `GapCVP.Comparator`: `Instance` (G:129743), `encodeInstance` (G:129767), `wellFormed` (G:129810),
  `hasIntegerTarget` (G:129815), `distanceSquared` (G:129821), `gapFactor400` (G:129828), `gapYES400`
  (G:129831), `gapNO400` (G:129838), `yesLanguage` (G:129869), `noLanguage` (G:129876), `PromiseProblem`
  (G:129883), `BinaryNearestCodewordInstance` (G:129900), `BinarySyndromeDecodingInstance` (G:129907),
  both encoders (G:129914, 129924), `binaryNearestCodeword` (G:130041), `binaryNearestTarget` (G:130048),
  `binarySyndromeProduct` (G:130052), `binarySyndromeTarget` (G:130059), `binaryCodeGapFactor`
  (G:130063), `finitePNorm` (G:130151), `finitePLatticeDiscrepancy` (G:130154), `finitePLatticeDistance`
  (G:130159), `finitePGapFactor` (G:130163), `PromiseReduction` (G:130203), `IsNPHardPromise`
  (G:130210), and the four theorem statements (G:130398, 130402, 130409, 130416).
- **Alpha-renaming only:** `encodeAtomic` (binder `value` vs `a`, G:454), `BitTM` (`map` vs `f`, G:631),
  `IsNP` (`language`/`input` vs `L`/`x`, and the position of the parentheses around `@decide`'s argument,
  G:638–646). Same term up to bound-variable names; `GapCVP.lean`'s `IsNP` IS the challenge's.
- **Differ only in `disjoint`:** `gapCVP400Promise` (G:129888), `binaryNearestCodewordPromise`
  (G:130066), `binarySyndromeDecodingPromise` (G:130111), `finitePGapCVPPromise` (G:130166): `yes` and
  `no` identical, `disjoint` a proof instead of `sorry`.

Name resolution. The solution's Comparator block sits inside `namespace GapCVP` (G:15 … G:130428), with
`open StateTransition (EvalsToInTime)` (G:5) and `open GapCVP.TraceGolf (oneStep rebound)` (G:37) in
force; no non-local instance or notation between them that the hole bodies could pick up (the only global
instances in that scope are `instEncodableFinIntMatrix` G:285, for `Matrix (Fin n) (Fin n) ℤ`, which no
challenge body encodes, and two `BinaryBitCodec` instances G:444, 602, a class the challenge does not
use; every `attribute [local instance] Classical.propDecidable` sits in a namespace closed before
G:129737). Identifiers in the challenge that the solution ALSO declares as `GapCVP.X` — `distanceSquared`
(G:306), `gapFactor400`, `gapYES400`, `gapNO400`, `gapCVP400Promise` (G:62097–62138), `PromiseProblem`
(G:670), `PromiseReduction` (G:675) — are all also declared in `GapCVP.Comparator`, and Lean resolves an
identifier at the innermost namespace that has it (`ResolveName.lean:146–151`), so they bind to the
Comparator versions, as in the challenge. No other identifier in the challenge has a `GapCVP.*`,
`GapCVP.Comparator.*` or `GapCVP.BinaryEncoding.*` namesake in the solution (scan over all 153
identifiers, including first components of dotted names). The solution's own `NPHard`/`NPHardPromise`
(G:660–686) and the bridge `isNPHardPromise_of_original` (G:130374) are proof route; the bridge's
`have original_hnp : GapCVP.IsNP language := hnp` (G:130382) typechecks because the Comparator `IsNP` is
the exported `GapCVP.IsNP` itself.

## 4. Informal vs formal (task 4)

| paper | formal | relation |
|---|---|---|
| Thm 1: deterministic P-time map 3SAT → (B, t ∈ ℤ^n, r ∈ ℚ_{>0}), sat ⇒ dist ≤ r, unsat ⇒ dist > n^{1/400} r; "Consequently GapCVP^(2)_{n^{1/400}} is NP-hard under deterministic polynomial-time many-one reductions" | `gapCVP400IsNPHard` | The "Consequently" sentence, in the integer-target form (D1, stronger), as ∀ L ∈ NP. The explicit 3SAT map, n = M and the size bounds are not part of the statement. |
| §1.1 GapCVP^(2)_γ with t ∈ ℚ^n | `finitePNormGapCVPIsNPHard 2` | exact (§2(h)); also implied by D1 at the meta level. |
| Cor. 15, nearest codeword, n^{1/200}, n = block length, integer R > 0 | `binaryNearestCodewordIsNPHard` | exact (D3 convention). |
| Cor. 15, syndrome decoding, same | `binarySyndromeDecodingIsNPHard` | exact on YES; NO restricted to consistent systems (D2, stronger). |
| Cor. 16, every fixed rational p ≥ 1, n^{1/(200p)}, square integral basis, rational target and radius | `finitePNormGapCVPIsNPHard p hp` | exact. |
| Overview: "related consequences for binary decoding and other lattice norms" (paper.txt l.26–28) | the two above | Nothing beyond Cors. 15–16 is claimed; ℓ_∞ is neither claimed nor formalized. |
| "does not invoke the PCP theorem / Projection Games Conjecture" | — | a property of the proof, not of the statement; checkable only on the route (not this rung). |

## 5. Plain-language summary

The four Lean statements say what the paper says, in some places slightly more: GapCVP is shown hard even
when targets are integer vectors, and syndrome decoding is hard even when the NO instances are required to
be consistent systems. The machine model is Mathlib's: deterministic, polynomial time in the input length,
with the usual NP verifiers and polynomially bounded certificates. The main risk in a complexity statement,
an NP predicate nothing satisfies (which would make "NP-hard" automatic), does not arise: a verifier that
accepts everything can be built by hand. The artifact never builds one, though, and never proves that any
language is in its NP. The pairing is weaker than the word "comparator" suggests. The challenge and the
proof have the same author, and because the four problem definitions are comparator "holes", a comparator
pass checks only the NP and reduction scaffolding, not what the problems are. This rung checked the
problems by reading: their text in the proof file matches the challenge exactly, apart from proofs of
disjointness the challenge left as `sorry`. Building the file and comparing the elaborated definitions
would close that gap; it did not run here.
