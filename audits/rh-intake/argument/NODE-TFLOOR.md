# NODE-TFLOOR: the level prime T — rigidity of log T* against Lam5, where T is paid, and why one T serves all lifts

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(mine)* = my own computation or inference. [NODE] = taken from that node and not re-read. Nothing was compiled or executed.

Abbreviations as in NODE-TU, NODE-LEDGER, NODE-SHARP (`QSB`, `QLD`, `GAL`, `T3E`, `DK`, `DE`, `WDS`, `MB`). New ones:
- `STL` = `Formalism/SharpRestriction/GlobalSchurBounds/StandardLattice.lean`
- `JL` = `Formalism/SharpRestriction/GlobalSchurBounds/JointsL.lean`
- `F23` = `Formalism/SharpRestriction/GlobalSchurBounds/FlipTwoThree.lean`
- `TD16` = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- `CGF` = `Formalism/SizeWindowBrackets/ClaimGaFree.lean`
- `PrkS` = `Formalism/LocalToGlobal/HermitianForms/PrkSmul.lean`

## 0. Verdict

**No ESCALATE on any of the three checks.**

- **A (rigidity).** The Lean has an exact closed form for logXu (`LemmaFiveOneIdentity`, T3E:126-138). I put the true formal degree into it (Harish-Chandra: dsig = dimV(rowLam) in the transferred normalisation) and used the shapes the Lean fixes in `DataB` (STL:500-516). That gives **logXu = Lam5₀ − θ with θ = O(L + log k + m²L/k)**, where Lam5₀ = Σ_j mean_ρ log(w_{jρ}v/π) + m·lg. So log T* − Lam5 = O(L). The leading terms cancel: the (v/π), lg, facProd(r) and Σ_j k·log w terms all drop out (§2.1).
  - **No matching upper bound is proved, and none is provable from the stated formal-degree bounds.** The upper half of `SigmaDegreeTwoSidedBoundOfGap` (T3E:76-81) is loose by a factor of about exp((km/2)·log(pq·b/w)) per place. In log T that is ≈ (m/2)·x^{ε/3}, the same order as log T itself.
  - Rigidity therefore rests on the true formal degree sitting at the lower end, not on anything the Lean proves.
- **B (where T is paid).**
  - **The source floor pays the exact Weyl-mean cost.** `flipTwoThree.Conclusion5` (F23:442-448) has −Σ_t (a_t/k)·log T. That equals the mean last-coordinate exponent |λ|/k of the level-0 weight (Weyl symmetry, *mine*). L3's "(1+m/k)" is exactly this term, after using log T ≤ Cc·m·La (JL:1413-1431, 1574-1586).
  - **Lo5 is a further m·nT·(a/k+b′)·log T.** It is the colength of NuLat_u inside Mram at the places above T (TD16:1516-1526; CGF:65-85).
  - **Same lattice.** Both concern (fm u).lat 0, which is integral in coordinates of level-T lattices (`ColVal.latT`, F23:420). N_u is built from that lattice.
  - **Why the mean-slope Bost step is valid without semistability.** It uses μ_min of the HN pieces together with *robust* rank. A single heavy functional would violate robust rank. What excludes it is Theorem S (NONVAN, RANK), not injectivity alone (§2.3).
- **C (one prime).** The record forces it:
  - one `ColumnsAtT.T` per word (DK:104-108);
  - level-T data at every level i ≤ m, built from that single `AtTTied u` (`LvTied u A i`, PrkS:65-81);
  - E_{u,j} = EatT for every j (DE:159-161).
  - Per-lift primes cannot be expressed in the Lean, and they would not reduce the loss either (§2.4).

## 1. Statement (what was read)

- **Count5** (QSB:27-32): Lam5 := Σ_j (1/f)Σ_ρ log(w_{jρ}v/π) + m·lg − cCount(La + m²La/k) ≤ log T(u) ≤ cCount·m·L.
- **D\*, d\*_u** (GAL:82-99):
  - d*_u = massI(k)·idxPi·∏_ρ dimV(uColR u ρ);
  - D* = volY0·idxSig·∏_ρ dsig ρ;
  - logXu = (1/(fk))·log(D*/d*_u);
  - dimV(x) = vand(x)/facProd(N), where vand(x) = ∏_{a<b}(x_a − x_b) is applied to the HC parameter and facProd(N) = ∏_{i<N} i! (GAL:26-30).
- **rowLam** (GAL:50-54): (v_0..v_{k−2}, −b_0..−b_{m−1}). The signs are + on the v's and alternating on the b's.
- **LemmaFiveOneIdentity** (T3E:126-138). With r = k+m−1:

  fk·logXu = f[(m−1)k + m(m−1)/2]·log(v/π) − f·((m−1)/2)·log(2v) + Σ_{M∈(k,r]} log lValEta(M) + f·(m(2k+m−1)/2)·lg + f·Σ_iΣ_{j∈(k,r]} log(1−g_i^{−j}) + Σ_ρ log(dsig_ρ·facProd(r)/vand(u_ρ)).

- **Formal-degree bounds** (T3E:76-81): (1−ε₀)·dimV(rowLam) ≤ dsig ≤ 4·dTau·(3pq·lamAbs)^{pq}. Here dTau keeps only same-sign pairs and divides by facProd(n₊)·facProd(n₋) (GAL:40-43).
- **Lower bound proved:** lowS = Lam5₀ − 11L ≤ logXu ≤ (15+3CY)·m·L (T3E:142-148).
- **Shapes** (`DataB`, STL:500-516):
  - v has step 4Δ and 0 ≤ v ≤ 4kΔ;
  - u_l = v_{l−1} − ½ (or −½−Δ) for 1 ≤ l ≤ k−2;
  - off tops: u_0 − v_0 ∈ [4kΔ, 8kΔ] and u_{k−1} = v_{k−2} − ½;
  - at tops (`RowsA`, T3E:115-121): u_0 − v_0 ≥ 4kΔ, u_{k−1} ≤ −4kΔ and u_0 − u_{k−1} ≤ 2a;
  - b_j < w_j ≤ b_j(1+1/x) and b_0 ≥ 4kΔx;
  - b_{j+1} − b_j ≥ r^{19}f^5L/C0, and w_{m−1} ≤ 2b.
- **L3** (`SlopesM_at`, QLD:173-175): −C·nT·a·La(1+m/k) ≤ μ((fm u).lat 0), and μmax(lat 0) ≤ C·nT·a·La.
  - Producer: `slopesM_at_of` (JL:1518-1594), from `flipTwoThree.Conclusion5/6` (F23:442-456) with `ColVal` (F23:403-439).
  - Conclusion5: −Σ_{tops}(a_t/k)·log T − C·nT·xb·log k − C·f·k(b′+Sc)·log k − C·f·Sc·log T − C·f·k²·L ≤ μ(lat 0).
  - Conclusion6: μmax(lat 0) ≤ C·nT·xb·log(kv) + C·f·(b′+Sc)·(k·log(kv) + log T) + C·f·k²·L.
- **ColVal** (F23:403-439):
  - lat 0 = co-image of the VV(λ₀)-valued functions on cls 0 (TSpan, F23:377-379);
  - integral iff, at each w, the γ⁻¹-transformed polynomial lies in IntSpanAt, where γ is a local basis of Q c τ = bc(clsLat u 0 c);
  - `latT`: clsLat has LatT index T^{2f};
  - metric `inf`: the Fock norm `nfAll` normalised by the extremal vector (F23:387-388), in the frames (Q c τ).X v.
- **Lo5 = LoU** (QSB:15-17; QLD:177-179).
  - Producer: `slopesN_at_of` (TD16:1529-1540) ← `Places_at` (TD16:1516-1526).
  - `HypLow` (CGF:65-72): μN = μMu + Sg(sg′) − BeSum(len). At the T-places WT, τ = 0 and Σ_{WT} 2·l_w·len_w/du ≤ PT ≤ LT ≤ C·nT·m(a/k+b′)·log T.
  - `HypLow2` (CGF:80-85): μMu = μ(lat 0) − f·log(T−1)/(T−2).
  - len = lenMN, the local colength of NuLat_u in Mram (grep: `ExistsLedPart.lean:190`).
- **Mu0** (`Mu0Tie`, STL:458-461): finrank Mu0 = #cls0·∏_ρ dimV(uColR), i.e. all VV(λ₀)-valued functions on the level-T class set. #cls0 = massI(k)·idxPi·(T^k−1)^f (STL:453-456).

## 2. Argument

### 2.1 Check A: logXu against Lam5 *(mine, on the Lean formulas above)*

Assume dsig_ρ = dimV(rowLam_ρ)(1+o(1)). That is Harish-Chandra's formula, with the same ρ-denominator facProd(r) for every inner form in the measure transferred from the compact form; the Lean's lower bound (1−ε₀)·fdegHC is that value. Then dsig·facProd(r)/vand(u) = vand(rowLam)/vand(u), and

 vand(rowLam) = vand(v)·∏_{a<k−1, j<m}(v_a + b_j)·∏_{j<j′}(b_{j′} − b_j).

So logXu − Lam5₀ = R1 + … + R5, where:

| piece | formula | size |
|---|---|---|
| R1 | −log(v/π) + (m(m−1)/2k)·(log(v/π) + lg) − ((m−1)/2k)·log 2v | O(L + m²L/k) |
| R2 | (1/fk)·Σ log lValEta + (1/k)·Σ log(1−g^{−j}) | ≈ 0 |
| R3 | (1/fk)·Σ_ρΣ_j[Σ_a log((v_a+b_j)/w_{jρ}) − log w_{jρ}] | ≤ m/x + 2mL/k, since v_a/b_j ≤ 1/x and w/b ∈ (1, 1+1/x] |
| R4 | (1/fk)·Σ_ρΣ_{j<j′} log(b_{j′}−b_j) | ∈ [0, m²(L+1)/2k] |
| R5 | (1/fk)·Σ_ρ[log vand(v) − log vand(u)] | ≈ −(1/f)·[nT·(log a + log(b′/kΔ)) + (f−nT)·log(c·kΔ)] + O(log k), with c ∈ [4,12]; so −2L − O(log k) ≲ R5 ≤ 0 |

For R5:
- vand(u) = vand(u_{1..k−1})·∏_{l≥1}(u_0 − u_l).
- The ±Δ shifts give only O(k·log k) per place, which is VandermondeVariation's k(1+log k)+2 (T3E:176-181).
- At a top there is an extra ∏(u_l − u_{k−1}) ≈ b′^{k−2}.

**Result.** logXu = Lam5₀ − θ with 0 ≤ θ ≲ 3L + O(log k) + O(m²L/k). The bound lowS = Lam5₀ − 11L is consistent with this.
- log T ∈ [logXu − 2logΓ/(fk), logXu + 1/(fk)]. Since 2logΓ/(fk) ≈ 2CGam·m⁵·x^ε/k → 0, we get **log T − Lam5 = cCount(La+…) − θ + o(1) = O(L)**.
- So the Count5 slack ΣA·(log T − Lam5) is the x/m-family term already budgeted (≤ 8cCount·x^{1/2+2.07ε}·U [LEDGER]). **SHARP's rigidity requirement is met in truth.**

**What is not provable from the stated hypotheses.** The upper formal-degree bound exceeds dimV(rowLam) by:
- the reciprocal of the opposite-sign product, ≈ ∏_{j odd} w_j^{k−1} times ∏ over opposite-parity b-pairs;
- times facProd(r)/(facProd(n₊)facProd(n₋)) ≈ exp((m/2)·k·log k);
- times (3pq·2b)^{pq}, with pq ≈ km/2.

In logXu that is ≈ (m/2)·[log(3pq) + log k + mean_ρ log(2b/w̄_ρ)], which is ≈ (m/2)·x^{ε/3} at thin places (log(b/w″) = x^{ε/3} + log n). So "logXu ≤ lowS + O(L)" would need fdeg ≤ (1+ε₀)·fdegHC. That is not among the Lean's hypotheses. The chain never needs it, because it uses only the lower bound and the crude upper bound.

**If the normalisation `D.s.cdScale` (not read) made fdeg exceed fdegHC by e^{Θ(km)}, then log T* − Lam5 ≈ m·x^{O(ε)}, and the proved chain would assert ASK ≤ Main − x^{1/2+c}·U. That would be false.**

### 2.2 Check B: the cost, in the model and in the Lean *(model mine)*

**Model.** Take V(λ) for GL_N, with the lattice changed by diag(1, …, 1, π) at one prime of K above T.
- The log-covolume (log‖·‖² units) shifts by Σ_μ μ_N·log T over the weights μ. By Weyl symmetry this equals dim·(|λ|/N)·log T.
- For Sym^a: Σ_{|α|=a} α_N = (a/N)·#α, exactly.
- Fock metric normalised so the extremal vector has norm 1 (as in `nfAll`): ‖z^α‖² = α!/a!. So μ = mean_α log(a!/α!) − (a/N)·log T ≈ a(H_N − 1) − (N/2)·log(a/N) − (a/N)·log T. That is ≈ +a·log k − (a/k)·log T at N = k.
- This matches Conclusion5 and Conclusion6 at the nT·a·log k scale, and the T-term coefficient matches exactly.
- Off tops, |λ|/k ≤ Sc gives the f·Sc·log T term. The −b′ entry gives Conclusion6's +f·b′·log T for μmax.
- The gain T^{−nBr} (squared norms) at a single π̄-place equals the rank-one cost: e·log N_{E/ℚ}(π̄)·2/[E:ℚ] = e·log T. So TDIV's rank-one "0 ≤ 0" holds.

**In the Lean.** The T-costs charged are:
- (a/k)·log T once, in lat 0 (L3);
- m·nT·(a/k+b′)·log T, the NuLat⊂Mram colength (Lo5);
- m·EatT·log T (Ee_T [SHARP]), where EatT excludes the top row (`Wtau`, DE:98-101).

Against these, the gain is Σ_t a_t·log T, once. Since m ≪ k and m·EatT/nT ≈ m·b·x^{O(ε)} ≪ a = xb, the gain dominates [TU oddity 1].

### 2.3 Why a mean-slope Bost step can use the T-gain *(reconstruction from RANK §1–2 and QLD:188-193)*

**L0** (`Frame_at`, QLD:188-193) is

 s − log|W| − (1−δ_p)⁻¹[4u_F·log(1+HH/u_F) + (η+4√e)·HH] ≤ μ(RR^∨),

where s = wmean_u(μ(N_u) − h(u)) and u_F = max_u(μmax(N_u) − h(u)) − s.

**Proof** [RANK]:
1. For each τ, take the HN piece Ñ_u(τ) with slopes ≥ s − τ + h(u).
2. Bost for a *nonzero* map gives μ_min(E′) ≤ μ_max(F) + h. No injectivity or semistability is needed. So B_u(Ñ_u(τ)) lies in the HN piece of RR^∨ with slopes ≥ s − τ.
3. Markov: the total codimension of the Ñ_u(τ) is ≤ u_F/(u_F+τ).
4. **Robust rank from the frame**: subspaces of small total codimension have joint image of small codimension.
5. Layer cake.

**Why a single heavy functional fails.** If B_u read only the heavy component (GL₁-weight e = nBr ≈ a on z0), it would kill the light pieces.
- Those are the *high*-slope pieces (slope −e·log T with e < a), and their codimension fraction is dimV(σ)/dimV(λ) ≪ ε.
- Robust rank would then be violated, so Theorem S's diagonal clause ‖K_uu − 1‖² ≤ e₀·d_u [RANK] would be false.
- So the T-gain is legitimate exactly because Theorem S makes every direction of N_u visible after the jet chain. At level 0 the source is all VV(λ₀)-valued functions (Mu0Tie). The heavy reading happens only at level m, after jets that must mix points.

**What the frame delivers.** Robust near-surjectivity, uniform over sub-collections of codimension ≤ ε·Σd_u, with overfill Σ duS ≥ x^{CH}·D* [RANK §4].
- NONVAN's "rank only" description suffices for the *mean*-slope inequality. The metric enters only through h(u) and μ, and the norm of B_u enters piecewise through Bost.
- But the statement has to be robust rank, not injectivity.

**u_F stays small.** μmax(N_u) ≤ μmax(lat 0) + Ga + Fo − Ee + C·m·B₀ (QLD:182), and μmax(lat 0) has no −a·log T. So u_F ≈ nT(a/k+b′)·log T + O(nT·a·La). The −a·log T sits in h(u), common to all of N_u, and does not widen the spread.

### 2.4 Check C: one T for all lifts

**The Lean forces a single T.**
- `ColumnsAtT` carries one T per word (DK:104-108).
- Mram is defined by the torus at the places over T at level 0 (DK:146-150). This is where the rank count d*_u(T^k−1)^f enters.
- `LvTied u A i hi` gives the level-T functionals fv, lk and te (with T·z) at **every** level i ≤ m, from the same `A : AtTTied u` (PrkS:65-81).
- At p = T_u, `Eval` sets E_{u,j}(w) = EatT for every j (DE:159-161). EatT is a level-independent sup over i ≤ m (DE:98-107). Hence sg = −m·EatT (WDS:887-901).
- So per-lift primes cannot be stated in the Lean.

**Mathematically** *(mine)*:
- The prime that fixes the source dimension (the mirabolic index at level 0) must be the prime whose π̄_T the last map divides by at level m. Heavy coefficients are π̄^{nBr}-divisible only at points that carry the π_T level datum.
- The jet chain must transport that datum through levels 1 … m−1. A prime T_j used at a level j < m would add a cost and give no gain, because there is only one last map.
- So per-lift primes do not lower the loss, and the method is not shown to prove too much.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `LemmaFiveOneIdentity` | T3E:126-138 | closed form of fk·logXu | check A | core (statement read; producer `LogWordScaleClosedFormOfIndexFormulas` T3E:140, body unread) |
| `SigmaDegreeTwoSidedBoundOfGap` | T3E:76-81 | (1−ε₀)·dimV ≤ dsig ≤ 4·dTau·(3pq·lamAbs)^{pq} | the upper half is loose | standard (Harish-Chandra) |
| `DataB`, `RowsA` | STL:500-516; T3E:115-121 | shapes of u, v, b, w | check A | definition |
| `flipTwoThree.Conclusion5/6`, `ColVal` | F23:403-456 | slope floor and ceiling of the level-T lattice lat 0 | L3 | **core, hypothesis** (producer `slopesMF_of_count_fam` not opened) |
| `slopesM_at_of`, `jnt_slope_low` | JL:1373-1594 | (a/k)·log T ↦ the m/k part of L3 | glue (read) | glue |
| `Places_at`, `slopesN_at_of`, `HypLow`/`HypLow2` | TD16:1516-1540; CGF:65-85 | the Lo5 colength at T | Lo5 | core input (`placesF_of`, PlacesP:638, not opened) |
| `LvTied`, `ColumnsAtT`, `Eval`, `sg_atT` | PrkS:65-81; DK:104-150; DE:159-172; WDS:887-901 | one T, at every level and every lift | check C | definition / glue |

## 4. Oddities

1. **The rigidity of log T* rests on an unstated equality** fdeg ≈ fdegHC. The proved upper bounds (T3E:148; T3E:79-81) are loose by ≈ m·x^{ε/3} in log T. The normalisation `cdScale`/`cdScaleTie` (T3E:85) was not read. *Ten-minute check:* is fdeg w.r.t. `D.s.cdScale` the Euler–Poincaré/compact-transferred measure, consistent with `BaseVolumeEqualsMass` (volY0 = massI(r), T3E:89)? If yes, §2.1 gives log T* − Lam5 = O(L).
2. **EatT is a max (sup over all levels and rows) charged m times.** Per dimension, the Weyl-mean cost of level j is only ≈ j(t+1)w/N(j). So the Lean's Ee_T, which SHARP identified as the barrier carrier, is a conservative booking. That is safe for validity. But SHARP's "does not prove too much" then requires that the *real* T-adic loss of the jet steps (the hypotheses `Conclusion5Sharp`/`TwistedColumnBoundAtT`) is genuinely ≈ EatT per lift. This is not established by the reading.
3. GapA (STL:496-498) forces b_{j+1} − b_j ≥ r^{19}f^5L/C0, so η ≥ m·r^{19}f^5L/C0. This is consistent with `etaSz` being free [LEDGER], but it is huge.
4. The prime above T at which lat 0 shrinks (π versus π̄) depends on the sesquilinear convention of `actAll`/`bc` (F23:381-385, 411-418). It must be the π̄-place used by `brC`. I did not trace it for lat 0; TDIV traced it for lat m.

## 5. Coverage

**Read:**
- PROTOCOL; MAIN-ARGUMENT §0, §5, §6; NODE-TDIV, TU, SHARP, LEDGER, RANK (full); NONVAN §0–1.2; SLOPESN §0; DIVKEY, GATIE and ADM11 (grep for T-related lines only).
- Lean: QSB:1-84; QLD:150-270; JL:1360-1620; F23:1-100, 370-470; TD16:1500-1560; CGF:1-106; GAL:1-101; T3E:1-210; STL:380-540; DE:95-172; WDS:885-902; DK:104-160; PrkS:60-95.

**Greps run:**
- `SlopesN_at|SlopesNF|SlopesM_at|SlopesMF`;
- `def HypLow2|def HypLow |def HypHigh|lower_bound_simplified`;
- `lenMN`; `def suppT`; `flipTwoThree`;
- `def Conclusion5 |def Conclusion6 `;
- `def DataB|def uN|def vN|def bN|def pY|def qY`;
- `ClsTie`; `structure ClsTied|structure LvTied`; `structure ColumnsAtT`; `Places_at|placesF_of`.

**Not opened:**
- `slopesMF_of_count_fam`; `placesF_of`; `LogWordScaleClosedFormOfIndexFormulas`'s proof; `cdScaleTie`;
- `Conclusion5Sharp` (PFZ) and `TwistedColumnBoundAtT` bodies;
- the jet steps' T-integrality; SHARP's `lcv` q-term.
