# NODE-HOSTS: the host supplier (`supplyChi`) and the family supplier (`shape_closed_link_n_of_green` → `topDesWin`)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations as in NODE-ROOT, plus
`HC/` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/`,
`SN/` = `Development/AutomorphicArithmetic/ShortNorms/`, `MSB/` = `Development/AutomorphicArithmetic/MeanSquareBounds/`,
`TSI/` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ThinScalesIffHostBound.lean`.

## 1. Statement

### (1) `UpperTheory.Top.supplyChi` (`CB/SupplyChi.lean:8-9`)
```lean
theorem UpperTheory.Top.supplyChi : ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req
```
where (`CB/HostOfField.lean:33-38`) `(GChi ψ).req C5 s R H q0 = EAtH (Level.cyc ψ) H TT s.x s.eps 4 ∧ VVle H.E R.t (√ s.b)`.

### (2) `UpperTheory.Top.shape_closed_link_n_of_green` (`TPS/TopShape.lean:33`)
```lean
GlobalTheory.GLq.Green → TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG
```
It finishes with `topDesWin` (`CB/DesWin.lean:11-22`): from `DesignExists (WithTw (WithSm 𝒞')) C0`, inclusions 𝒞' ⊆ 𝒞 and 𝒞' ⊆ ℰ,
HypV on ℰ, and nine `Closed (Des 𝒞 C0) …` Link properties, it concludes `FamilyClassConnected ℰ`.

### (a) What a host is

**Frame** φ (`HC/ZsmulGeneratorEqZeroOfProjection.lean:15-23`, `:61-124`):
- `e : ℕ` is the 2-power exponent.
- `ord`: |A|, where A = `Idx ord` is a finite abelian group with an arbitrary group structure `grp`.
- `h0 : A ↠ HGrp e`, where HGrp e = (Z/2^{e+2})^×/⟨−1⟩, cyclic of order 2^e (`Formalism/FrobeniusOrbits/Statement.lean:24-25`).
  The map is surjective.
- `gen0 = a0 ∈ A`, with ⟨a0⟩ meeting ker h0 trivially. Also n0 = ord(a0) and **o = ord/n0** (`:68-70`). Here o is matched to
  |⟨ψ⟩| = `(Level.cyc ψ).o`.
- Derived: **GG = G0 × A** with G0 = {±1}×{±1}. The class cc = ((−1,−1),1) is complex conjugation, iod = ((1,−1),1), chQ and chD
  are the two sign projections, and Psi = ker chD, the "CM-type" subgroup of index 2.

**HostRaw φ** (`HC/ConjEMemHostFIff.lean:12-43`): a number field with its arithmetic, made explicit.
- `q, d`: primes with `HostHyp q d`: q ≡ 3 (mod 8), d ≡ 7 (mod 16), (−d/q) = 1 (`FrobeniusOrbits/Statement.lean:13-14`).
- `QS`: the "small" conductor part. 2^{e+2} | QS, gcd(QS, qd) = 1, and every odd ℓ | QS splits in Q(√−d).
- `E`: a Galois number field with Gal(E/Q) ≅ GG (`gal`). It contains √−d, and Galois acts on √−d by the chD sign.
- `cycEmb`: E ↪ Q(ζ_{QS·q·d}). `art`: (Z/QS·q·d)^× → GG, the Artin map. Its properties: it is compatible with the cyclotomic
  action (`art_spec`), art(−1) = cc, the A-part reduces mod 2^{e+2} to the class in HGrp, and there are ramification conditions at d and q.
- So E is an abelian, imaginary, conductor-QS·q·d field of degree 4·ord. It is cut out by an explicit Artin map.

**HostAx φ** = HostRaw + `HostDer` (`:142-176`). HostDer lists the derived facts: art is surjective; E is CM with maximal real
subfield F; [E:Q] = 4 ord and [F:Q] = 2 ord; there is a **CM type** `cmType = {ι : ι(√−d) = i√d}` of size 2·ord, stable exactly
under Psi; the Frobenius at p ∤ condN is art(p), with sign chQ equal to `psAt p` and chD equal to (−d/p); the inertia and
decomposition groups are described through art; ramification at d is via iod; and K = Q(√−d) has 2 primes above p iff p = 2 or (−d/p) = 1.
It also has discriminant support, root-discriminant bounds, and a norm condition on roots of unity.

**Ranks** (`Formalism/LocalRingCardinality/Params.lean:6-24`) extends Frame:
- integers k (even), m (even, ≥ 2), t (odd), with m+3 ≤ k, k+m+4 ≤ t, 3m < t, m ≤ 2·ord ≤ k and m² ≤ k+m(t+1);
- derived: n = ord, f = 2n, r = k+m−1, N(j) = k + j(t+1).

`RankVal s R` (`…/GlobalTwisting/PairRowIffQdRows.lean:28-32`) fixes the sizes at scale x:
n ≍ x^{2+8ε}, m ≍ √(x·x^{−ε/8}), k ≍ x^{9/2+10ε}, and r+t equals an explicit formula.

**Host R** (`Formalism/LocalRingCardinality/DataHost.lean:39-110`) extends HostAx R.toFrame. Its fields:
- `flPS`: the chQ sign is the Legendre symbol (·/q). `sqq`: √−q ∈ E with the Galois action by chQ.
  So E ⊇ Q(√−q, √−d).
- `QS_exact`: every ℓ | QS really ramifies. `QS_le : QS ≤ n²`. `o_pow : o^64 ≤ 2^e`. `q ≠ 3`. `qd_big : q, d > 4tr+1`.
- `splitBound`, with all odd p ≤ splitBound split in Q(√−d), and 4ℓ ≤ splitBound for odd ℓ | QS.
- `φ₀`: an embedding in the CM type.
- `𝔟`: an ideal of O_E with different(E/K) = 𝔟·𝔟̄ and 𝔟 + 𝔟̄ = 1, stable under Psi.
- **level primes** `levelPrimes : Finset ℕ`, containing g 0 ≠ g 1 (primes) and pde ≠ pde' (primes ≡ 1 mod 15), all distinct.
- `ccK`: a primitive ideal of O_K whose prime factors have prime norm split in K, coprime to 2,3,5,q,d, the level primes and QS.
  The level primes are coprime to QS.
- `TT ⊆ A` (the "top" set), `T2 : Finset ℕ` (the "second/thick" set), u0 ∈ A, Lw ≥ 2 with 4·Lw·s < n0 for s ∈ T2, a no-relation
  condition `NoRel T2 Lw`, and a real constant `CT2`.

**HostGood s C8 C5 c6 Cb H q0** (`TSI:102-112`) adds conditions at scale s:
- HostVal, HostArith, a lower bound on #T2, and 4·Lw·#T2 ≤ n0;
- `QDq` (sizes of q, d);
- **`BoxW`**: there is a Y with PairWin and PairRow, and for the host's real primitive characters χ with q | N or d | N, χ is
  `GoodFor Q`, i.e. N ≤ Q and L(s,χ) ≠ 0 on {Re s > 1 − 1/400, |Im s| ≤ Q}. Here Q ≈ 8·QS_odd·exp(Y^{ε/5}) (·exp(Y^{ε/5}log²Y)).
- |L′/L(1, (·/d))| ≤ x^ε;
- **`ThinOK`** (`TSI:59-61`): for every primitive χ that factors through Gal(E/Q) and every y ≥ exp(x^{ε/3})/3,
  |gχ(y)| ≤ y·exp(−c·x^{ε/8});
- `BadOK`, a weighted count of bad primes below X′;
- the two g-sets `BB r (g i)` are disjoint;
- each g_i = π·π̄ with π ∈ O_K and π ≡ 1 mod QS·q·d;
- pde, pde′ ≡ 1 mod lcm(15, QS q d);
- **q0** is prime, q0 ≡ 1 mod QS q d, q0 ≤ (QS q d)^{C8}, and q0 ∉ {pde, pde′};
- levelPrimes = {g0, g1, pde, pde′, q0}.

**`HostExW la P`** (`TSI:118-121`). For every ε ∈ (0, 1/52) there are constants CT2, C8 ≥ 1, C5, c6, Cb > 0 and x0, and a window
system S : `Scales la` (`PrimeDiscriminants/Scales.lean:9-19`: a J ≥ 1 and a set Win with arbitrarily large Y such that
[Y, Y^la] ⊆ Win), such that **every** scale s with s.ε = ε, s.x ≥ x0, s.J = S.J and s.x ∈ Win carries ranks R, a host
H : Host R and a prime q0 with RankVal s R, H.CT2 = CT2, HostGood, and P. So it asks for good hosts at every x in a union of
windows [Y, Y^{3/2}] that reaches arbitrarily far out. Their size grows with x: [E:Q] = 4n ≍ x^{2+8ε}, log q ≍ Y^{ε/5} and
log d ≍ Y^{ε/5} log²Y with Y ∈ [x^{1/J}, x].

`EAtH` (from NODE-ROOT) adapts the host to the level ⟨ψ⟩. `VVle` is the Sha bound.

### (b) `TopG`, `FamilyClassConnected`, `ChainTied`

`TopG` (`CB/ZeroFreeAllOfTopG.lean:13-15`): ∀ la > 1, ∀ G : FReq, HostExW la G.req → (HypV on G.cls la) → FamilyClassConnected (G.cls la).

`FamilyClassConnected ℰ` (`CB/DivinNOfHypV.lean:13-15`): there are eD, eL and ε₁ > 0 such that for every ε < ε₁ there is a family
Fm ∈ ℰ and constants K, cHH, eK, CL, x0 with ChainTied Fm eD eL K cHH eK CL x for all x ≥ x0 in Fm.Win.
In this chain (`TopShape.lean:52`) topDesWin is called with Cabs = 2, C0 = 3, **eD = 2, eL = 0**.

`ChainTied Fm eD eL K cHH eK CL x` (`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97-114`). There exist an index i0 at
x (host datum D = Fm.D x i0, group A = D.R.A), sizes m and f, a map pt : A → Ix x choosing a datum for each u0 ∈ A, integer
sequences av and bv, a chain record `Dd : Data A W Top m f`, constants C, Xpp, a function ell on characters of E0×A, N, TT, T2 ⊆ A,
weights a and w, bijections eT and eP, and reals η, X′, θ, such that the following 16 clauses hold.

| # | Clause | Kind | Meaning |
|---|---|---|---|
| 1 | `TiePts` (`:38-46`) | bookkeeping | all the data pt(u0) share D's frame, m, f, q, d; u0 is the host's u0; aT, bT come from av, bv |
| 2 | `TieGlobal` (`:50-61`) | bookkeeping | the scalars of Dd (a, b, b′, k, L, La, B0, Nc, γ, L′/L(1), v, log g0g1, log Γ, X″, η, X′) equal the family's values |
| 3 | `TieLocal` (`:63-80`) | bookkeeping | the local entries of Dd (division-kernel ranks, μ, μmax, h, lattice μ's, EeJ sums, Fo, Ga, Ta, IO, δ) equal the data's |
| 4 | `TieArith` (`:82-91`) | mostly bookkeeping | TT, T2 and a, w are read off the host. Last clause: for each nontrivial character ψ of E0×A and each primitive χ with χ(n) = primVal(ψ)(n), ell ψ = L′/L(1,χ). This is a definitional identification, not an estimate |
| 5–6 | Dd.x = x, Dd.ε = ε | identity | |
| 7–9 | C.eDiv ≤ eD, C.eLoss ≤ eL, C.cHH ≤ cHH | size | constant comparisons. With eL = 0 this forces C.eLoss ≤ 0 |
| 10 | `Ident` (`Formalism/SizeWindowBrackets/SChain.lean:26-31`) | bookkeeping | aT and w via eT, eP; γ; LpL = Re ell(chC); ASK equals an arithmetic sum built from the host's ArithData |
| 11 | `SizeData₂ Dd C Xpp` (`SChain.lean:18-20`) | **substantive (not unfolded)** | an 11-fold conjunction: HidaSetting, DIV, EComp5, HComp, Count5, Slopes, QuotientSlopeBoundsWith, LossBounds, SlopeIneq, HHBound, FParams |
| 12 | `ErrWindows` (`Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:43-45`) | size + **one substantive bound** | ErrWindows0: about 25 size inequalities (1 ≤ b, xb ≤ a, m ≤ x^{1/2+ε/2}, xm ≤ k ≤ x^{eK}, L, La ≤ 2x^ε, …, δ̄ ≤ 1/2, ConstsBound C K). Plus (η̄ + 4√ē)·x^{cHH}·b ≤ K·x^ε·nT·a. The sibling file name "…WeakWindowsFalse" suggests that the version without this last clause was shown false |
| 13 | `BNBounds` (`SChain.lean:33-36`) | size | B0 ≤ 2|A|·m·b·x^ε and Nc ≤ #T2·k·b·x^ε/(|A|²x^{−ε}) |
| 14 | `GrowthInequalityRemainingHyps` (`SChain.lean:44-48`) | size + **substantive** | GrowthInequalitySizes (positivity, b′X′ ≤ xb, \|a_t/b − x\| ≤ 1, node sizes, a_t/w ≤ N). Plus **ThinScales**: for every character ψ of E0×A and y ≥ X′/3, ‖GPsi ψ y‖ ≤ yθ (`GrowthBoundGivesRiemannHypothesis.lean:55-56`). Plus **ValuesAtX**: for the three quadratic characters psC, chC, chpsC, ‖GPsi ψ x‖ ≤ x^{1/2+ε} and ‖ell ψ‖ ≤ CL log x (`:67-69`) |
| 15 | `CostWindows` (`SChain.lean:50-51`) | size | 2f(x+1)θ ≤ 1/x and 6f(x+1)(η+1) ≤ b/x |
| 16 | `RestSize` (`SChain.lean:53-58`) | size | a ≤ 2xb, #TT ≥ x^{−ε/8}n/2, #T2/n ≥ x^{−ε}, m ≥ x^{1/2−ε}, k ≤ n²x^{1/2−ε} |

*I infer*: **ValuesAtX** is a square-root (RH-strength) bound at the single point x for the Chebyshev sums of the quadratic characters
(·/q), (·/d) and (·/qd). It is fed by `PairGood.bounds` (below). **ThinScales** is a zero-free-region bound far beyond the conductor,
fed by `ThinOK`. The actual analytic content of ChainTied beyond these sits in `SizeData₂` and in the last clause of `ErrWindows`.

## 2. Argument

### (c1) supplyChi / supplyOfAdmOf: **hosts are constructed for every large window, not taken from an example**

`supplyChi ψ hψ = supplyOfAdm ψ hψ (admissibleClassesTwistedChar …)` (`CB/SupplyChi.lean:10-16`).
`supplyOfAdm = supplyOfAdmOf hostOfField` (`CB/HostOfField.lean:33-39`), and `hostOfField = hostOfFieldOf shortNorm smallOne` (`:24-31`).
Proof of `supplyOfAdmOf` (`SN/supplyOfAdmOf.lean:24-135`), as mathematics:
1. `fieldChi ψ` (`CB/FieldChi.lean:20-50`) gives c, e0 such that **for every** e ≥ e0 and **every** prime pair (q, d) with HostHyp,
   q ≠ 3, gcd(ψ.N, qd) = 1, and small odd primes split in Q(√−d), there is an explicit frame φ with ord = c·2^e and o = |⟨ψ⟩|, and a
   HostAx with this q, d. The field is `AnyGrp.host (zpowers ψ.χ) e …`, a fixed field inside a cyclotomic field. It satisfies
   KerChi ψ: art(a) = 1 ⟺ a ≡ ±1 (mod 2^{e+2}), ψ(a) = 1, (a/q) = (a/d) = 1. It also satisfies QS | lcm(2^{e+2}, ψ.N), TwistForm, KeptInXp,
   FieldRows and so on. This is a general construction: E is the abelian field attached to the subgroup above, of conductor 2^{e+2}·N_ψ·q·d.
2. `winPairs` (`CB/WinPairs.lean:5-8`) takes VWinAt ψ 401 and `QH.pairEx`. It produces J such that for arbitrarily large Z, every x ∈ [Z, Z^{3/2}]
   has (Y, q, d, e) with `WinDatum`: x^{1/J} ≤ Y ≤ x, `PairGood ψ.N ε Y x q d`, c·2^e ≍ x^{2+8ε}, and the VVle bound for every
   `IsChiField ψ e q d` field E (`CB/TwistForm.lean:19-27`).
3. **Where (q, d) come from**: `QH.pairEx : PairEx` (`MSB/pairEx.lean:112-169`). For every M, ε, A and every large Y there are primes q, d
   with `PairGood M ε Y (Y^A) q d` (`CB/PairGood.lean:18-31`):
   - `WinPair`: q ≡ 3 (8), d ≡ 7 (16), log q ∈ (z/2, z] with z = Y^{ε/5}, log d ≍ z log²Y, q | d+1, and small odd p | d+1;
   - for every ξ mod M and (i, j) ≠ (0, 0), each primitive χ inducing ξ·(·/q)^i·(·/d)^j has
     **|gχ(y)| ≤ y^{1/2+ε/2} for all y ∈ [Y, Y^A]** and |L′/L(1,χ)| ≤ 4 log y;
   - each such χ twisted from real ρ | 8M has no zeros in Re s > 1 − 1/400, |Im s| ≤ height.

   It is proved from `pair_exists` (`MSB/PairExists.lean:9-12`). That comes from `pair_share` (`MSB/PairShare.lean:26-31`): **all but a
   proportion η of the primes q ≡ 3 (mod 8) in the range are GoodQ, and for each of them all but η of the d in the second range are
   GoodD** (proved from `stage1`, `stage2`). So the pair is produced by an *averaging/density argument over a family of quadratic
   characters*, not by Chebotarev or Linnik. *I infer*: this is a zero-density / large-sieve statement for quadratic twists. It
   gives GRH-quality Chebyshev bounds (exponent 1/2+ε/2) for most q and d with log q ≈ Y^{ε/5}, on the range y ∈ [Y, Y^A], which
   is far below the conductor.
4. `admissibleClassesTwistedChar` (`CoprimeRanks/AdmChi.lean:13`) chooses Ranks R on φ with RankVal s R and `admitted`.
5. `hostOfFieldOf` (`SN/hostOfFieldOf.lean:159-175`) extends HostAx to a full Host and proves HostGood. It uses:
   - `levelData shortNorm smallOne`, for the level primes g_i = ππ̄ (π ≡ 1 mod condN) and q0, pde, pde′.
     `ShortNorm` (`SN/ShortNorm.lean:8-11`) is a lower bound c′hX/((4dM²)^A log X) for primes in [X, X(1+h)] represented by the
     principal form of Q(√−d) in a class mod M, uniformly for log(4dM²) ≤ c√log X. `SmallOne` (`:13`) is Linnik:
     there is a prime p ≡ 1 (mod M) with p ≤ M^A. These are the only Linnik/Chebotarev-type prime-existence inputs, and they
     are used for the *auxiliary level primes*, not for q and d;
   - `QH.thinH`, for ThinOK (`CB/PairGood.lean:38-41`: bounded odd QS, log condN ≤ 2x^{ε/5}log²x, and RealBox ⇒ the Chebyshev bound);
   - `topsChoiceH`, for TT and BadOK; `pairRows`; `hof_thick`, for T2.
6. Lines 116-135 assemble the requirement. EAtH comes from the KerChi/kept/shares facts and `boundedTw`. VVle H.E R.t √b comes from
   `hW.bound` applied through `isChiField`, then `VVle.mono` from ⌊x^400⌋ down to R.t (rank ≤ x^400, from
   `eventually_rank_le_rpow_of_lt_one_div_fiftytwo`).

### (c2) The 571/599 example: a sanity/non-emptiness witness, not a base case
`Formalism/LocalRingCardinality/SpanPowerMembership/ExampleLayerExistsGenerators.lean:149-150,207-225` builds `Examples₂.H0 : Host R0`
with e = 2, q = 571, d = 599 (571 ≡ 3 mod 8, 599 ≡ 7 mod 16), splitBound = 2, QS = 16 and small ranks.
`SpanPowerMembership.lean:44-53` builds `exampleRecord G : D7` **conditional on** `G : LocalGap H0`. It proves
`Nonempty D7 ↔ Nonempty (LocalGap H0)`. That makes it a consistency/non-emptiness check of the D7 record type. Its only other users
that I found are `levelData_exampleRecord_isEmpty` and `Pend_exampleRecord_isEmpty`
(`GlobalSchurBounds/StandardIntegralLatticeExists.lean:1228-1233`), which show that some substructures are empty for that example.
Grep found no consumer of those two theorems. The 185-digit primes in `Columns/CyclotomicIsCyclotomicExtension.lean:395-434` are
toy level primes for the same H0 (each is 1 + d·(condN·c)², certified by Lucas tests). They feed the toy datum in `Columns/ChainInst.lean`.
Its terminal lemmas (`character_index_conditions`, `local_constants_conditions`, `ToyHeckeCondition`) have no users outside
`CyclotomicIsCyclotomicExtension`/`ChainInst`, as far as grep shows.
An import-closure scan shows that **neither file is imported by `CB/SupplyChi.lean` or by `CB/DesWin.lean`**. Both are in the import
closure of `TPS/TopShape.lean`, but I found no use there. The example's frame has fixed ord, so it cannot satisfy RankVal
(n ≍ x^{2+8ε}) for large x and cannot serve as a HostExW witness. Verdict: decoration/sanity, not a base case. A dependency-graph
query (`#print axioms`-style or a used-constants walk) would settle this definitively.

### (c3) shape_closed_link_n_of_green / topDesWin
`shape_closed_link_n_of_green` (`TopShape.lean:34-55`) unpacks the HypsAlt fields and the TopG hypotheses (la, G, hla, HostExW hH, HypV hV). Then:
- **Existence of a family** (DesignExists) comes from `designExists_of_tuSize_aux4n_litThin` (`TPS/LinkEx.lean:15-22`). Its key input is
  `hEx hM la G hla hH`, i.e. the HypsAlt field `hEx : MinkDiv → ExS 𝒜 cT`. ExS (`CB/ExS.lean:10-12`) says **for every la, G with
  HostExW la G.req, `DesignChoices (WithTw (𝒜 ∧ G.cls la)) 3 cT`**: a family in the class with ThickSet, ChosenTT/Bad/QD/Code,
  BoxesF, QDRowsF, DGamDvdF, … (`Formalism/SharpRestriction/DesignExistsOfChoices.lean:22-26`). In the HypsAlt producer
  (`TPS/NonemptyHypsOfAllRows.lean:59`) this comes from `UpperTheory.Top.classSel` (`CB/ClassSel.lean:14-28`, via `recS` and
  `memberTop_final_contextParameters`). **So turning hosts into families happens in the HypsAlt producer, not in this node.**
- The nine Link closures come from: `nRest` (LinkN, a HypsAlt field), `closed_linkEta_of_duty`, `closed_linkIRR_of_join_count hGreen`
  (the only use of Green), `link_alt_alt_alt` (SmallLevelRankEq), `closed_linkDIVt_of_closed_bridge_kernel`, `hgl.1` (NuFull/MuRank),
  `closed_linkG_of_duty`, `link_alt_alt_bis` (LinkS) and `hgl.2` (LinkGLOBAL), where `hgl = link_gl 𝒜 hduty tie hU hG`.
- `topDesWin` (`DesWin.lean:23-31`): combine the Closed properties with `Closed.and` to get a threshold K. Pick the family Fm from
  DesignExists with Fm `Large K CH`, then apply the conjunction. DIV is obtained by `divinN_of_hypV` from HypV, LinkN and
  SmallLevelRankEq. Mu comes from `linkMu_of_linkDIV`. **ChainTied is then the output of `LinkGLOBAL`** (`GlobalTheoremInputs.lean:162-…`:
  ChosenE → GlobalTheoremInputs → ∃ K cHH eK CL x0, ∀ x ≥ x0 in Win, ChainTied). So `topDesWin` is logical glue. The 16 clauses are
  established inside `link_gl` (and LinkGLOBAL7-type lemmas, `GlobalSchurBounds/LossesSmallShares.lean:464-472`).

## 3. Children

| # | Name | file:line | Statement (math) | Role | Weight |
|---|---|---|---|---|---|
| 1 | `GlobalTheory.Top.link_gl` (→ LinkGLOBAL, LinkGLOBAL7) | `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean:14`; `Formalism/SharpRestriction/GlobalTheoremInputs.lean:162` | for families in the class: ChosenE ∧ GlobalTheoremInputs ⇒ eventually ChainTied (all 16 clauses, including SizeData₂, ErrWindows, ThinScales, ValuesAtX) | produces ChainTied | core |
| 2 | `QH.pairEx` ← `pair_exists` ← `pair_share` (`stage1`, `stage2`) | `MSB/pairEx.lean:112`; `MSB/PairExists.lean:9`; `MSB/PairShare.lean:26` | for most primes q ≡ 3 (8), log q ≍ Y^{ε/5}, and most d ≡ 7 (16): all twists ξ(·/q)^i(·/d)^j have \|gχ(y)\| ≤ y^{1/2+τ} on [Y, Y^A], \|L′/L(1)\| ≪ log Y, and zero-free boxes Re > 1−1/400 | the RH-strength bounds for the q,d-twists (they feed ValuesAtX and BoxW) | core (*I infer*: zero-density for quadratic families; check the y-range against the conductor) |
| 3 | `UpperTheory.Top.classSel` (→ `recS`, `memberTop_final_contextParameters`) | `CB/ClassSel.lean:14` | builds the family class 𝒜 and, from HostExW, DesignChoices families (ExD/ExS) | turns hosts into families | core |
| 4 | `UpperTheory.T3.hostOfFieldOf` (`levelData`, `QH.thinH`, `topsChoiceH`, `pairRows`, `hof_thick`) | `SN/hostOfFieldOf.lean:159` | a HostAx plus PairGood plus RankVal ⇒ a full Host with HostGood (level primes, q0, ThinOK, BadOK, BoxW) | completes the host | core |
| 5 | `UpperTheory.Top.fieldChi` (`AnyGrp.host`, `kerChiAny`, `twistAny`) | `CB/FieldChi.lean:20` | explicit abelian CM field of degree 4c2^e for every large e and every admissible (q,d) | field construction | standard (class field theory over Q), large bookkeeping |
| 6 | `QH.thinH` (`ThinH`) | `CB/PairGood.lean:38` | no real zero > 1−1/400 and log conductor ≤ 2x^{ε/5}log²x ⇒ \|gχ(y)\| ≤ y·e^{−c x^{ε/8}} for y ≥ e^{x^{ε/3}} | ThinOK/ThinScales | standard (de la Vallée Poussin PNT in progressions, no Siegel zero) |
| 7 | `ShortNorm` (`normPrimesImagQuad_short_interval_lower_bound`), `SmallOne` (`primesInProgressions_relativeError`) | `SN/ShortNorm.lean:8,13`; `SN/Primes.lean:5,7` | primes of norm form x²+dy² in a class mod M in short intervals; Linnik p ≡ 1 (mod M), p ≤ M^A | auxiliary level primes | standard (Hecke/Fogels; Linnik) |
| 8 | `winPairs`, `admissibleClassesTwistedChar`, `boundedTw`, `isChiField`, `eventually_rank_le_rpow_of_lt_one_div_fiftytwo` | `CB/WinPairs.lean:5`; `CoprimeRanks/AdmChi.lean:13`; `CB/BoundedTw.lean:45`; `CB/IsChiField.lean:5` | windows from VWinAt, rank choice, EAtH components | assembly | glue |
| 9 | the other Link lemmas in TopShape (`closed_linkIRR_of_join_count`, `link_alt_alt_bis`, `closed_linkDIVt_of_closed_bridge_kernel`, `link_brest_alt`, `wire_sel_alt`, `designExists_of_tuSize_aux4n_litThin`) | `TPS/TopShape.lean:35-55`; `TPS/LinkEx.lean:15` | the closure properties consumed by topDesWin | inputs | core/unknown (not opened) |
| 10 | `topDesWin`, `divinN_of_hypV`, `linkMu_of_linkDIV` | `CB/DesWin.lean:11` | logic | glue | glue |

Definitions not unfolded: `SizeData₂` sub-predicates, `ErrWindows0`/`ConstsBound`, `GPsi`/`primVal`/`ArithData`, `HostVal`, `HostArith`,
`QDq`, `PairRow`, `DesignChoices` components, `GlobalTheoremInputs`, `IsChiField`, `admitted`.

## 4. Oddities

1. **The q,d twists are where the square-root bound comes from.** `PairGood.bounds` gives |gχ(y)| ≤ y^{1/2+ε/2} for the characters
   ξ(·/q)^i(·/d)^j with (i,j) ≠ (0,0). These are found by density over q and d (`pair_share`). The target character ψ itself (i = j = 0)
   is excluded. Whatever passes from these twists to Gm for ⟨ψ⟩ is the crux, and it lives in ChainTied (SizeData₂/ErrWindows) and
   `core_gm`/`ch_core`. A reviewer should check the claimed density statement in `stage1`/`stage2`. It holds uniformly for all
   y ∈ [Y, Y^A] at conductors of size exp(Y^{ε/5}), with explicit constant C in |L′/L(1)| ≤ C log Y.
2. `shape_closed_link_n_of_green` is stated with `TopShapeAlt True True …`, so the V and NR slots are `True` (see NODE-ROOT 3).
   `classSel` returns `IsSel Q' Lk (fun _ _ _ _ _ => True) 𝒜 σ` (`ClassSel.lean:14`), so the selection predicate is trivial. It
   imports `CharacterBoxes/ObjCTrue` (not opened).
3. FamilyClassConnected is used with eL = 0, so clause 8 requires C.eLoss ≤ 0. This is not necessarily wrong, but it should be checked
   that `Consts.eLoss` can be ≤ 0.
4. The existence of families (the step that could be vacuous) does not happen here. It is the HypsAlt field `hEx`, which comes from
   `classSel`. If ExS were provable for an empty or degenerate reason, TopG would still follow. That makes `classSel`/`recS` a priority.
5. The 571/599 example and the 185-digit primes are not on the host-supply path (not in the import closure of SupplyChi or DesWin).
   They witness Nonempty D7 only conditionally on `LocalGap H0`.
6. The requirement `(GChi ψ).req` ignores its C5 and q0 arguments, and HostGood is used with C5 = 4 fixed. This is harmless.
7. `Frame.grp` is an arbitrary group structure on Fin ord, so it is not canonical. It is pinned down only through `h0` and `gal`.

## 5. Coverage

Read: NODE-ROOT.md, the PROTOCOL Explainer section; `CB/SupplyChi.lean`, `CB/HostOfField.lean`, `SN/supplyOfAdmOf.lean` (all);
`HC/ZsmulGeneratorEqZeroOfProjection.lean:1-124` (definitions); `HC/ConjEMemHostFIff.lean:1-200`; `FrobeniusOrbits/Statement.lean:1-41`;
`LocalRingCardinality/Params.lean:1-60`, `DataHost.lean:1-140`, `DataParams₂.lean:1-60`; `TSI:1-127`; `PrimeDiscriminants/Scales.lean:1-30`;
`CB/TwistForm.lean`, `CB/PairGood.lean`, `CB/FieldChi.lean:1-50`, `CB/WinPairs.lean:1-40`; `PairRowIffQdRows.lean:20-45`;
`GlobalSchurBounds/FiltrationCocycleLiftCriterion.lean:40-55`; `MSB/pairEx.lean` (all), `MSB/PairExists.lean:9-34`, `MSB/PairShare.lean:26-38`,
`MSB/PrimeSetTwoBounds.lean:35-63`; `CB/DesWin.lean`, `TPS/TopShape.lean:1-57`, `TieGlobal.lean:1-116`, `SChain.lean:1-70`,
`ErrorFormsWeakWindowsFalse.lean:28-70`, `GrowthBoundGivesRiemannHypothesis.lean:55-75`, `CB/DivinNOfHypV.lean:1-20`,
`CB/ZeroFreeAllOfTopG.lean:10-16`, `CB/ExS.lean`, `DesignExistsOfChoices.lean:12-34`, `TPS/LinkEx.lean:15-30`,
`TPS/NonemptyHypsOfAllRows.lean:40-62`, `CB/ClassSel.lean` (all), `SN/ShortNorm.lean`, `SN/Primes.lean`, `SN/hostOfFieldOf.lean:159-175`
(plus a grep of its references); `ExampleLayerExistsGenerators.lean:149-225` (grep plus excerpt); `SpanPowerMembership.lean:1-60`;
`Columns/CyclotomicIsCyclotomicExtension.lean:395-434,694-766` (grep); `StandardIntegralLatticeExists.lean:1215-1260`; `LossesSmallShares.lean:464-472`;
`GlobalTheoremInputs.lean:162-163`. Ran an import-closure scan (a Python script over the `import` lines) from SupplyChi, DesWin, TopShape and
EveryCharacterOfLiteratureOfVWin.

Not opened: the bodies of `stage1`/`stage2`, `thinH`, `levelData`, `topsChoiceH`, `AnyGrp.host`, `admissibleClassesTwistedChar`,
`link_gl`, `recS`, `memberTop_final_contextParameters`, the Link lemmas, `working_classes_frozen`; the definitions of SizeData₂ components,
GPsi, ArithData, GlobalTheoremInputs, IsChiField, HostVal/HostArith.
